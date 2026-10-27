module

public import CFSG.Quasithin.H13.A6S1372L76B
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6L76F

theorem pRank_le_map_of_not_dvd {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    [hp : Fact p.Prime] (φ : A →* B) (hker : ¬ p ∣ Nat.card φ.ker) (X : Subgroup A) :
    CFSG.Open.pRank p X ≤ CFSG.Open.pRank p (X.map φ) := by
  set ψ := φ.domRestrict X with hψ
  have hkerψ : ¬ p ∣ Nat.card ψ.ker := by
    rw [hψ, MonoidHom.ker_domRestrict]
    have h1 : Nat.card (φ.ker.subgroupOf X) = Nat.card (φ.ker ⊓ X : Subgroup A) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective X.subtype_injective]
    rw [h1]
    exact fun h => hker (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have e : ↥X ⧸ ψ.ker ≃* ↥(X.map φ) :=
    (QuotientGroup.quotientKerEquivRange ψ).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range X φ))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (X.map φ),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup X,
    ← CFSG.SectionRank.pRank_quotient_eq ψ.ker hkerψ]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt e).le

@[expose] def stabE : Subgroup (Perm (Fin 6)) where
  carrier := {σ | act4f σ e0123 = e0123}
  one_mem' := act4f_one _ e0123_mem_W4
  mul_mem' := fun {a b} ha hb => by
    show act4f (a * b) e0123 = e0123
    rw [act4f_mul, show act4f b e0123 = e0123 from hb, show act4f a e0123 = e0123 from ha]
  inv_mem' := fun {a} ha => by
    show act4f a⁻¹ e0123 = e0123
    have h : act4f a e0123 = e0123 := ha
    conv_lhs => rw [← h]
    rw [← act4f_mul, inv_mul_cancel, act4f_one _ e0123_mem_W4]

instance : DecidablePred (· ∈ stabE) := fun σ =>
  decidable_of_iff (act4f σ e0123 = e0123) Iff.rfl

theorem card_stabE : Nat.card ↥stabE = 48 := by
  have : Fintype.card {σ : Perm (Fin 6) // act4f σ e0123 = e0123} = 48 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem pRank_three_le_one {X : Subgroup (Perm (Fin 6))} (hX : X ≤ stabE) :
    CFSG.Open.pRank 3 X ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEX hE => ?_
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hdvd : 3 ^ k ∣ 48 := by
    rw [← hk, ← card_stabE]
    exact Subgroup.card_dvd_of_le (hEX.trans hX)
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 3 ^ 2 ∣ 48 := (pow_dvd_pow 3 h).trans hdvd
    norm_num at h9
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk1

theorem center_alt6 : ∀ σ : Perm (Fin 6),
    σ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * σ →
    σ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * σ →
    σ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * σ →
    σ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * σ → σ = 1 := by
  decide +kernel

theorem conj_c012 : (swap (1 : Fin 6) 2 * swap 3 4) * (swap 0 1 * swap 1 2) *
      (swap (1 : Fin 6) 2 * swap 3 4)⁻¹ = (swap 0 1 * swap 1 2)⁻¹ ∧
    Perm.sign (swap (1 : Fin 6) 2 * swap 3 4) = 1 ∧ Perm.sign (swap (0 : Fin 6) 1 * swap 1 2) = 1 ∧
    (swap (0 : Fin 6) 1 * swap 1 2) ^ 3 = 1 ∧ (swap (0 : Fin 6) 1 * swap 1 2) ≠ 1 ∧
    (swap (0 : Fin 6) 1 * swap 1 2) * (swap (0 : Fin 6) 1 * swap 1 2) ≠ 1 ∧
    (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) 4 = 4 ∧
    (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) 5 = 5 := by
  decide

end A6L76F

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pRank_three_NV3_le_one (h13315 : Stmt13_3_15) (h1337 : Stmt13_3_7)
    (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz) :
    CFSG.Open.pRank 3 (H ⊓ Subgroup.normalizer (S.V3 : Set G)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : H ⊓ Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_inf_right _ hH.2.1).trans (S.G1_inf_G3_le h13315)
  set N := Subgroup.normalizer (V : Set G) with hN
  set X' := (H ⊓ Subgroup.normalizer (S.V3 : Set G)).subgroupOf N with hX'
  have h3V : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) :=
    (h1337 G T L V S.h13 S.irr S.a6).resolve_right fun h => hhat h.1
  have hker : ¬ 3 ∣ Nat.card S.frame.ρ.ker := by
    have e : S.frame.ρ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf N := by
      ext g
      rw [MonoidHom.mem_ker, S.rho_eq_one_iff, Subgroup.mem_subgroupOf]
    rw [e]
    intro h
    apply h3V
    refine h.trans ?_
    have h1 : Nat.card ((Subgroup.centralizer (V : Set G)).subgroupOf N) =
        Nat.card (Subgroup.centralizer (V : Set G) ⊓ N : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective N.subtype_injective]
    rw [h1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h1 := A6L76F.pRank_le_map_of_not_dvd S.frame.ρ hker X'
  have h2 : X'.map S.frame.ρ ≤ A6L76F.stabE := by
    rintro _ ⟨g, hg, rfl⟩
    have hgH : (g : G) ∈ H := (Subgroup.mem_subgroupOf.mp hg).1
    have hgz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
      have h1 : (g : G) ∈ S.G1 := hH.2.1 hgH
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    exact S.fix_e0123 g hgz
  have h3 := A6L76F.pRank_three_le_one h2
  have h4 : X'.map N.subtype = H ⊓ Subgroup.normalizer (S.V3 : Set G) := by
    rw [hX', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hX]
  have h5 := A6L76B.pRank_map_le N.subtype (p := 3) (by
    rw [(MonoidHom.ker_eq_bot_iff _).2 N.subtype_injective, Subgroup.card_bot]
    norm_num) X'
  rw [h4] at h5
  omega

theorem two_le_pRank_L1_of_hat (hhat : IsHatA6 L) :
    2 ≤ CFSG.Open.pRank 3 S.L1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp := S.perfect_Q
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L with hQ
  set f : ↥L →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hf
  obtain ⟨hcon, hs2, hs3, hs31, hs11, hs12, hs4, hs5⟩ := A6L76F.conj_c012
  have hZ3 : Nat.card ↥(Subgroup.center Q) = 3 := hhat.2.1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) 3 (by rw [hZ3])
  have hφζ : S.phiQ (ζ : Q) = 1 := by
    have hcomm : ∀ σ ∈ alternatingGroup (Fin 6), S.phiQ (ζ : Q) * σ = σ * S.phiQ (ζ : Q) := by
      intro σ hσ
      rw [← S.phiQ_range] at hσ
      obtain ⟨q, rfl⟩ := hσ
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ζ.2 q]
    exact A6L76F.center_alt6 _ (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
      (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
      (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
      (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) (ζ : Q)
  have hwC : (w : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [← S.rho_eq_one_iff ⟨w, S.frame.L_le w.2⟩, ← S.phiQ_mk]
    rw [← hw] at hφζ
    exact hφζ
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hw'm : (w ^ (2 ^ a)) ^ m = 1 := by rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hw'L1 : ((w ^ (2 ^ a) : ↥L) : G) ∈ S.L1 := by
    refine Subgroup.subset_closure ⟨⟨(w ^ (2 ^ a)).2, ?_⟩, m, hm, ?_⟩
    · show ((w ^ (2 ^ a) : ↥L) : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)
      rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
      have hwz : (w : G) * S.z = S.z * w :=
        (Subgroup.mem_centralizer_iff.mp hwC S.z S.z_mem_V).symm
      rw [Subgroup.coe_pow]
      exact (Commute.pow_left hwz _).eq
    · simpa using congrArg Subtype.val hw'm
  obtain ⟨c, hcL, hcρ⟩ := S.exists_L1_of_three hs3 hs4 hs5 hs31
  have hcLL : (c : G) ∈ L := S.L1_le_L hcL
  set cq : Q := f ⟨c, hcLL⟩ with hcq
  have hφc : S.phiQ cq = swap 0 1 * swap 1 2 := by
    rw [hcq, hf, QuotientGroup.mk'_apply, S.phiQ_mk, ← hcρ]
  have hc3Z : cq ^ 3 ∈ Subgroup.center Q :=
    S.phiQ_ker _ (by rw [map_pow, hφc, hs31])
  have hsA : swap (1 : Fin 6) 2 * swap 3 4 ∈ alternatingGroup (Fin 6) :=
    Perm.mem_alternatingGroup.2 hs2
  rw [← S.phiQ_range] at hsA
  obtain ⟨sq, hsq⟩ := hsA
  have hz : (sq * cq * sq⁻¹) * cq ∈ Subgroup.center Q :=
    S.phiQ_ker _ (by rw [map_mul, map_mul, map_mul, map_inv, hsq, hφc, hcon, inv_mul_cancel])
  set z := (sq * cq * sq⁻¹) * cq with hzdef
  have hz3 : z ^ 3 = 1 := cube_of_mem_center hhat hz
  have hscs : sq * cq * sq⁻¹ = z * cq⁻¹ := by rw [hzdef]; group
  have hc6 : cq ^ 3 = (cq ^ 3)⁻¹ := by
    have h1 : sq * cq ^ 3 * sq⁻¹ = cq ^ 3 := by
      rw [Subgroup.mem_center_iff.mp hc3Z sq, mul_inv_cancel_right]
    have h2 : sq * cq ^ 3 * sq⁻¹ = (sq * cq * sq⁻¹) ^ 3 := (conj_pow).symm
    rw [h2, hscs] at h1
    have h3 : (z * cq⁻¹) ^ 3 = z ^ 3 * (cq⁻¹) ^ 3 := by
      have hzc : Commute z cq⁻¹ := (Subgroup.mem_center_iff.mp hz cq⁻¹).symm
      exact hzc.mul_pow 3
    rw [h3, hz3, one_mul, inv_pow] at h1
    exact h1.symm
  have hcq3 : cq ^ 3 = 1 := by
    have h1 : (cq ^ 3) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hc6]
      exact inv_mul_cancel (cq ^ 3)
    have h2 : (cq ^ 3) ^ 3 = 1 := cube_of_mem_center hhat hc3Z
    have h3 : orderOf (cq ^ 3) ∣ Nat.gcd 2 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  set wq : Q := f (w ^ (2 ^ a)) with hwq
  have hwqζ : wq = (ζ : Q) ^ (2 ^ a) := by rw [hwq, map_pow, hf, hw]
  have hζ3 : (ζ : Q) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    simpa using congrArg Subtype.val this
  have hwqZ : wq ∈ Subgroup.center Q := by rw [hwqζ]; exact Subgroup.pow_mem _ ζ.2 _
  have hwq1 : wq ≠ 1 := by
    rw [hwqζ]
    intro h
    have h1 : orderOf (ζ : Q) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf (ζ : Q) = 3 := by
      rw [← hζ]
      exact Subgroup.orderOf_coe ζ
    rw [h2] at h1
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega
  have hφwq : S.phiQ wq = 1 := by
    rw [hwqζ, map_pow, hφζ, one_pow]
  have hE : A6L76B.E9Pair cq wq := by
    refine ⟨Subgroup.mem_center_iff.mp hwqZ cq, hcq3, ?_, ?_, hwq1, ?_, ?_⟩
    · rw [hwqζ, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
    · intro h
      have := congrArg S.phiQ h
      rw [hφc, map_one] at this
      exact hs11 this
    · intro h
      have := congrArg S.phiQ h
      rw [hφc, hφwq] at this
      exact hs11 this.symm
    · intro h
      have := congrArg S.phiQ h
      rw [map_mul, hφc, hφwq] at this
      exact hs12 this.symm
  set X : Subgroup ↥L := S.L1.subgroupOf L with hXdef
  have hcX : (⟨c, hcLL⟩ : ↥L) ∈ X := by rw [hXdef, Subgroup.mem_subgroupOf]; exact hcL
  have hwX : w ^ (2 ^ a) ∈ X := by rw [hXdef, Subgroup.mem_subgroupOf]; exact hw'L1
  have h1 : 2 ≤ CFSG.Open.pRank 3 (X.map f) :=
    A6L76B.two_le_pRank_of_e9 ⟨_, hcX, rfl⟩ ⟨_, hwX, rfl⟩ hE
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h2 := A6L76B.pRank_map_le f hker X
  have h3 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) L.subtype L.subtype_injective X
  have h4 : X.map L.subtype = S.L1 := by
    rw [hXdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 S.L1_le_L]
  rw [h4] at h3
  omega

end Setting4

end CFSG.Quasithin.H13.A6
