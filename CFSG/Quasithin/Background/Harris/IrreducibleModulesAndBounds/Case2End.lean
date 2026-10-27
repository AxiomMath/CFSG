module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_fixedSpace_zpowers_of_order_eleven {g : GLV V} (hg : orderOf g = 11)
    (hV : Nat.card V = 2 ^ 12) : Nat.card (fixedSpace (Subgroup.zpowers g)) = 4 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hpg : IsPGroup 11 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hpg.card_modEq_card_fixedPoints V
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) =
      Nat.card (fixedSpace (Subgroup.zpowers g)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun v => ?_
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h k hk
      exact h ⟨k, hk⟩
    · intro h k
      exact h k k.2
  rw [hfix, hV] at hmod
  have hdvd : Nat.card (fixedSpace (Subgroup.zpowers g)) ∣ 2 ^ 12 := by
    rw [← hV]
    exact AddSubgroup.card_addSubgroup_dvd_card (fixedSpace (Subgroup.zpowers g)).toAddSubgroup
  obtain ⟨c, hc, hcc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hcc] at hmod ⊢
  have hne : c ≠ 12 := by
    rintro rfl
    have htop : (fixedSpace (Subgroup.zpowers g)).toAddSubgroup = ⊤ := by
      rw [← AddSubgroup.card_eq_iff_eq_top]
      show Nat.card (fixedSpace (Subgroup.zpowers g)) = Nat.card V
      rw [hcc, hV]
    have hall : ∀ v, g v = v := fun v => by
      have : v ∈ (fixedSpace (Subgroup.zpowers g)).toAddSubgroup := by rw [htop]; trivial
      exact this g (Subgroup.mem_zpowers g)
    have : g = 1 := LinearEquiv.ext hall
    rw [this, orderOf_one] at hg
    omega
  interval_cases c <;> simp_all [Nat.ModEq]

theorem natCard_endCommutant_eq_four {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤) {g z : GLV V}
    (hg : g ∈ L) (hgo : orderOf g = 11) (hzc : ∀ l ∈ L, l * z = z * l) (hz1 : z ≠ 1)
    (hV : Nat.card V = 2 ^ 12) : Nat.card (endCommutant L) = 4 := by
  have hC := card_fixedSpace_zpowers_of_order_eleven hgo hV
  have hnt := endCommutant_nontrivial hirr
  have hfinE : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  have hCnt : 1 < Nat.card (fixedSpace (Subgroup.zpowers g)) := by rw [hC]; norm_num
  have : Nontrivial (fixedSpace (Subgroup.zpowers g)) := Finite.one_lt_card_iff_nontrivial.1 hCnt
  obtain ⟨⟨c, hcC⟩, hc0⟩ := exists_ne (0 : fixedSpace (Subgroup.zpowers g))
  have hc0' : c ≠ 0 := fun h => hc0 (Subtype.ext h)
  let ev : endCommutant L → fixedSpace (Subgroup.zpowers g) := fun T =>
    ⟨(T : Module.End (ZMod 2) V) c, fun k hk => by
      have hkL : k ∈ L := (Subgroup.zpowers_le.2 hg) hk
      have h1 := (endCommutant_apply_comm T.2 hkL c).symm
      rw [hcC k hk] at h1
      exact h1⟩
  have hev : Function.Injective ev := by
    intro T T' h
    have h1 : (T : Module.End (ZMod 2) V) c = (T' : Module.End (ZMod 2) V) c :=
      congrArg Subtype.val h
    by_contra hne
    have hsub : ((T - T' : endCommutant L) : Module.End (ZMod 2) V) ≠ 0 := by
      intro h0
      exact hne (sub_eq_zero.1 (Subtype.ext h0))
    have hinj := injective_of_mem_endCommutant hirr (T - T').2 hsub
    apply hc0'
    apply hinj
    have : ((T - T' : endCommutant L) : Module.End (ZMod 2) V) c = 0 := by
      show (T : Module.End (ZMod 2) V) c - (T' : Module.End (ZMod 2) V) c = 0
      rw [h1, sub_self]
    rw [this, map_zero]
  have hle : Nat.card (endCommutant L) ≤ 4 := hC ▸ Nat.card_le_card_of_injective ev hev
  have hVnt : Nontrivial V := by
    obtain ⟨v, -, hv⟩ := (Submodule.ne_bot_iff _).mp (ne_of_lt hirr.2.1).symm
    exact ⟨v, 0, hv⟩
  let z' : endCommutant L := ⟨(z : V →ₗ[ZMod 2] V), by
    rw [endCommutant, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    ext v
    have := congrArg (fun x : GLV V => x v) (hzc h hh)
    simpa using this⟩
  have hz0 : z' ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h1 : z v = 0 := by
      have := congrArg (fun T : endCommutant L => (T : Module.End (ZMod 2) V) v) h0
      simpa [z'] using this
    have := congrArg z.symm h1
    simpa using this
  have hz1' : z' ≠ 1 := by
    intro h1
    apply hz1
    apply LinearEquiv.ext
    intro v
    have := congrArg (fun T : endCommutant L => (T : Module.End (ZMod 2) V) v) h1
    simpa [z'] using this
  have h01 : (0 : endCommutant L) ≠ 1 := zero_ne_one
  have h3 : 3 ≤ Nat.card (endCommutant L) := by
    let _ := Fintype.ofFinite (endCommutant L)
    classical
    have hcard3 : ({0, 1, z'} : Finset (endCommutant L)).card = 3 :=
      Finset.card_eq_three.2 ⟨0, 1, z', h01, hz0.symm, hz1'.symm, rfl⟩
    rw [Nat.card_eq_fintype_card, ← hcard3]
    exact Finset.card_le_univ _
  have hpow : Nat.card (endCommutant L) = 2 ^ Module.finrank (ZMod 2) (endCommutant L) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := endCommutant L)
    rwa [Nat.card_zmod] at this
  rw [hpow] at hle h3 ⊢
  generalize Module.finrank (ZMod 2) (endCommutant L) = k at hle h3 ⊢
  have hk : k < 3 := by
    by_contra hk
    push Not at hk
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk
    omega
  interval_cases k <;> simp_all

theorem exists_algEquiv_galoisField_of_card (K : Type) [Ring K] [IsDomain K] [Finite K]
    [alg : Algebra (ZMod 2) K] {e : ℕ} (h : Nat.card K = 2 ^ e) :
    Nonempty (K ≃ₐ[ZMod 2] GaloisField 2 e) := by
  classical
  let _ : Field K := (Finite.isDomain_to_isField K).toField
  let _ : Algebra (ZMod 2) K := alg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField.algEquivGaloisField 2 _ h⟩

theorem endIsField_of_natCard {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤) {e : ℕ}
    (hcard : Nat.card (endCommutant L) = 2 ^ e) : EndIsField L e := by
  have := endCommutant_nontrivial hirr
  have := endCommutant_noZeroDivisors hirr
  have : IsDomain (endCommutant L) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  exact exists_algEquiv_galoisField_of_card (endCommutant L) hcard

theorem centralizer_eq_center_of_card {L : Subgroup (GLV V)}
    (hF : Nat.card (endCommutant L) = 4) (hZ : Nat.card (Subgroup.center ↥L) = 3) :
    Subgroup.centralizer (L : Set (GLV V)) = (Subgroup.center ↥L).map L.subtype := by
  have hfinE : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have hZle : (Subgroup.center ↥L).map L.subtype ≤ Subgroup.centralizer (L : Set (GLV V)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_center_iff.1 hl ⟨y, hy⟩
    have h2 := congrArg Subtype.val this
    exact h2
  have hZcard : Nat.card ((Subgroup.center ↥L).map L.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L), hZ]
  let φ : Subgroup.centralizer (L : Set (GLV V)) → endCommutant L := fun c =>
    ⟨((c : GLV V) : V →ₗ[ZMod 2] V), by
      rw [endCommutant, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      ext v
      have := congrArg (fun x : GLV V => x v) (Subgroup.mem_centralizer_iff.1 c.2 h hh)
      simpa using this⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun T : endCommutant L => (T : Module.End (ZMod 2) V) v) hab
  have hle4 : Nat.card (Subgroup.centralizer (L : Set (GLV V))) ≤ 4 :=
    hF ▸ Nat.card_le_card_of_injective φ hφ
  have hdvd : 3 ∣ Nat.card (Subgroup.centralizer (L : Set (GLV V))) := by
    rw [← hZcard]
    exact Subgroup.card_dvd_of_le hZle
  have hpos : 0 < Nat.card (Subgroup.centralizer (L : Set (GLV V))) := Nat.card_pos
  have hC3 : Nat.card (Subgroup.centralizer (L : Set (GLV V))) = 3 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [hC3, hZcard])).symm

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
