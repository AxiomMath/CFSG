module

public import CFSG.Walter.Cited.OddQuotient
public import CFSG.Walter.Cited.FourGroupCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.Walter.Suzuki

structure Hyp (M : Type*) [Group M] [Finite M] : Prop where
  klein : ∀ P : Sylow 2 M, IsKleinFour (P : Subgroup M)
  conj : ∀ x y : M, orderOf x = 2 → orderOf y = 2 → IsConj x y
  comm : ∀ x : M, orderOf x = 2 → IsMulCommutative (Subgroup.centralizer ({x} : Set M))

variable {M : Type*} [Group M] [Finite M]

theorem odd_card_pPrimeCore : Odd (Nat.card (CFSG.pPrimeCore 2 M)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := M))

omit [Finite M] in
theorem le_pPrimeCore {N : Subgroup M} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ CFSG.pPrimeCore 2 M :=
  le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩

theorem card_comap_mk' (O : Subgroup M) [O.Normal] (C : Subgroup (M ⧸ O)) :
    Nat.card (C.comap (QuotientGroup.mk' O)) = Nat.card C * Nat.card O := by
  have h1 := (C.comap (QuotientGroup.mk' O)).card_mul_index
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O),
    Subgroup.card_eq_card_quotient_mul_card_subgroup O, ← C.card_mul_index] at h1
  have hi : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1]
  ring

theorem eq_bot_of_odd_quotient {C : Subgroup (M ⧸ CFSG.pPrimeCore 2 M)} (hC : C.Normal)
    (hodd : Odd (Nat.card C)) : C = ⊥ := by
  set O := CFSG.pPrimeCore 2 M
  have hcomap : (C.comap (QuotientGroup.mk' O)).Normal := hC.comap _
  have hle := le_pPrimeCore hcomap (by rw [card_comap_mk']; exact hodd.mul odd_card_pPrimeCore)
  have hmap := Subgroup.map_mono (f := QuotientGroup.mk' O) hle
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
    QuotientGroup.map_mk'_self] at hmap
  exact le_bot_iff.mp hmap

theorem card_map_of_inf_ker_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (hK : K ⊓ f.ker = ⊥) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have : (x : G) ∈ K ⊓ f.ker := ⟨x.2, hx⟩
    rw [hK, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hrange : K.map f = (f.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_lift {x : M ⧸ CFSG.pPrimeCore 2 M} (hx : orderOf x = 2) :
    ∃ t : M, orderOf t = 2 ∧ (t : M ⧸ CFSG.pPrimeCore 2 M) = x :=
  exists_orderOf_eq_two_mk_eq _ odd_card_pPrimeCore hx

namespace Hyp

variable (h : Hyp M)
include h

theorem orderOf_eq_two {P : Sylow 2 M} {s : M} (hs : s ∈ P) (hs1 : s ≠ 1) : orderOf s = 2 := by
  have hss : s * s = 1 := congrArg Subtype.val ((h.klein P).mul_self ⟨s, hs⟩)
  exact orderOf_eq_prime (by rw [pow_two]; exact hss) hs1

theorem card_sylow (P : Sylow 2 M) : Nat.card (P : Subgroup M) = 4 := (h.klein P).card_four

theorem factorization_two : (Nat.card M).factorization 2 = 2 := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  have h4 := P.card_eq_multiplicity
  rw [h.card_sylow P, show (4 : ℕ) = 2 ^ 2 by norm_num] at h4
  exact (Nat.pow_right_injective le_rfl h4).symm

theorem le_centralizer_core (P : Sylow 2 M) :
    (P : Subgroup M) ≤ Subgroup.centralizer (CFSG.pPrimeCore 2 M : Set M) :=
  le_centralizer_of_isKleinFour (h.klein P) odd_card_pPrimeCore fun s hs hs1 =>
    h.comm s (h.orderOf_eq_two hs hs1)

theorem sylow_inf_core (P : Sylow 2 M) :
    (P : Subgroup M) ⊓ CFSG.pPrimeCore 2 M = ⊥ := by
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [h.card_sylow P, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr odd_card_pPrimeCore)

theorem card_map_sylow (P : Sylow 2 M) :
    Nat.card ((P : Subgroup M).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 M))) = 4 := by
  rw [card_map_of_inf_ker_eq_bot, h.card_sylow P]
  rw [QuotientGroup.ker_mk']
  exact h.sylow_inf_core P

theorem factorization_two_quotient :
    (Nat.card (M ⧸ CFSG.pPrimeCore 2 M)).factorization 2 = 2 := by
  have hM := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 M)
  have hodd := (odd_card_pPrimeCore (M := M))
  have h2 := h.factorization_two
  rw [hM, Nat.factorization_mul (Nat.pos_of_ne_zero (by
      intro h0; rw [h0, zero_mul] at hM; exact Nat.card_pos.ne' hM)).ne' hodd.pos.ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      (fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)), add_zero] at h2
  exact h2

theorem not_eight_dvd_card_quotient : ¬ 8 ∣ Nat.card (M ⧸ CFSG.pPrimeCore 2 M) := by
  intro h8
  have hpos : Nat.card (M ⧸ CFSG.pPrimeCore 2 M) ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp
    (show 2 ^ 3 ∣ Nat.card (M ⧸ CFSG.pPrimeCore 2 M) by norm_num; exact h8)
  rw [h.factorization_two_quotient] at this
  omega

theorem isConj_quotient {x y : M ⧸ CFSG.pPrimeCore 2 M} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨s, hs, rfl⟩ := exists_lift hx
  obtain ⟨t, ht, rfl⟩ := exists_lift hy
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.conj s t hs ht)
  refine isConj_iff.mpr ⟨(c : M ⧸ CFSG.pPrimeCore 2 M), ?_⟩
  rw [← hc]
  rfl

theorem isMulCommutative_centralizer_quotient {x : M ⧸ CFSG.pPrimeCore 2 M}
    (hx : orderOf x = 2) :
    IsMulCommutative (Subgroup.centralizer ({x} : Set (M ⧸ CFSG.pPrimeCore 2 M))) := by
  obtain ⟨t, ht, rfl⟩ := exists_lift hx
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hle := centralizer_mk_le_map _ odd_card_pPrimeCore htt
  have hC := h.comm t ht
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨a', ha', ha'eq⟩ := hle a.2
  obtain ⟨b', hb', hb'eq⟩ := hle b.2
  have := congrArg Subtype.val (hC.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  change (a : M ⧸ CFSG.pPrimeCore 2 M) * b = b * a
  rw [← ha'eq, ← hb'eq, ← map_mul, ← map_mul]
  exact congrArg _ this

theorem normal_of_quotient {T : Subgroup (M ⧸ CFSG.pPrimeCore 2 M)} (hT : T.Normal)
    (hT4 : Nat.card T = 4) (P : Sylow 2 M) : (P : Subgroup M).Normal := by
  set O := CFSG.pPrimeCore 2 M
  have h4 : Nat.card T = 2 ^ (Nat.card (M ⧸ O)).factorization 2 := by
    rw [h.factorization_two_quotient, hT4]; norm_num
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hPp : IsPGroup 2 ((P : Subgroup M).map (QuotientGroup.mk' O)) :=
    P.isPGroup'.map _
  obtain ⟨R, hR⟩ := hPp.exists_le_sylow
  have hTR : T ≤ R := hTp.le_sylow_of_normal R
  have hTReq : T = R := Subgroup.eq_of_le_of_card_ge hTR (by
    rw [R.card_eq_multiplicity, ← h4])
  have hmapT : (P : Subgroup M).map (QuotientGroup.mk' O) = T := by
    refine Subgroup.eq_of_le_of_card_ge (hTReq ▸ hR) ?_
    rw [hT4, h.card_map_sylow P]
  refine normal_of_normal_map O odd_card_pPrimeCore P.isPGroup' (h.le_centralizer_core P) ?_
  rw [hmapT]
  exact hT

end Hyp

end CFSG.Walter.Suzuki
