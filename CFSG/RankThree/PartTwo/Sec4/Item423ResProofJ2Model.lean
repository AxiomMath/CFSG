module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofJ2
import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLCore

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open Subgroup

namespace Res462J2Model

section Counting

variable {G : Type*} [Group G] [Finite G] {E : Subgroup G}

omit [Finite G] in
theorem coe_normalizer_smul (a : normalizer (E : Set G)) (x : E) :
    ((a • x : E) : G) = a * x * (a : G)⁻¹ := rfl

theorem card_modEq_card_centralizer_inf {p : ℕ} [Fact p.Prime] {g : G}
    (hg : g ∈ normalizer (E : Set G)) (hord : orderOf g = p) :
    Nat.card E ≡ Nat.card ↥(centralizer ({g} : Set G) ⊓ E) [MOD p] := by
  set a : normalizer (E : Set G) := ⟨g, hg⟩ with ha
  have hcard : Nat.card (zpowers a) = p ^ 1 := by
    rw [Nat.card_zpowers, ha, Subgroup.orderOf_mk, hord, pow_one]
  have hP : IsPGroup p (zpowers a) := IsPGroup.of_card hcard
  have key := hP.card_modEq_card_fixedPoints E
  have hfix : ∀ x : E, x ∈ MulAction.fixedPoints (zpowers a) E ↔
      (x : G) ∈ centralizer ({g} : Set G) := by
    intro x
    rw [mem_centralizer_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro h
      have h1 := congrArg Subtype.val (h ⟨a, mem_zpowers a⟩)
      rw [Subgroup.smul_def, coe_normalizer_smul, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    · intro hx k
      have hstab : a ∈ MulAction.stabilizer (normalizer (E : Set G)) x := by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        rw [coe_normalizer_smul, mul_inv_eq_iff_eq_mul]
        exact hx.symm
      rw [Subgroup.smul_def]
      exact MulAction.mem_stabilizer_iff.1 ((zpowers_le.2 hstab) k.2)
  have e : MulAction.fixedPoints (zpowers a) E ≃ ↥(centralizer ({g} : Set G) ⊓ E) :=
    { toFun := fun x => ⟨x.1, mem_inf.2 ⟨(hfix x.1).1 x.2, x.1.2⟩⟩
      invFun := fun y => ⟨⟨y, (mem_inf.1 y.2).2⟩, (hfix _).2 (mem_inf.1 y.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Nat.card_congr e] at key

end Counting

theorem card_normalizer_VJ :
    Nat.card (normalizer ((VJ : Subgroup GJ) : Set GJ)) = 720 := by
  rw [normalizer_V, card_subOf (by decide) enum45.2.2.2.2.2.2.1 gensNV_spec,
    enum45.2.2.2.2.2.2.2.1]

theorem card_normalizer_zpowers_conj {G : Type*} [Group G] (g w : G) :
    Nat.card (normalizer ((zpowers (g * w * g⁻¹) : Subgroup G) : Set G)) =
      Nat.card (normalizer ((zpowers w : Subgroup G) : Set G)) := by
  have h := Step462UAlphaM12.map_normalizer_zpowers (MulAut.conj g) w
  rw [MulAut.conj_apply] at h
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem not_mem_zpowers_zJ
    {w : GJ} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hN : Nat.card (normalizer ((zpowers w : Subgroup GJ) : Set GJ)) = 72) :
    w ∉ zpowers zJ := by
  intro h
  have heq : zpowers w = zpowers zJ := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr h) ?_
    rw [card_zpowers_z, Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have h2 := card_normalizer_Z
  rw [← heq, hN] at h2
  norm_num at h2

theorem exists_conj_zpowers_xJ
    {w : GJ} (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) (hN : Nat.card (normalizer ((zpowers w : Subgroup GJ) : Set GJ)) = 72) :
    ∃ g : GJ, zpowers (g * w * g⁻¹) = zpowers xJ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwp : IsPGroup 3 (zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1, pow_one])
  obtain ⟨Q, hwQ⟩ := hwp.exists_le_sylow
  have hP3 : Nat.card P3 = 3 ^ (Nat.card GJ).factorization 3 := by
    rw [card_P3, card_GJ, CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  set P3S : Sylow 3 GJ := Sylow.ofCard P3 hP3 with hP3S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GJ Q P3S
  have hw₁ : g * w * g⁻¹ ∈ P3 := by
    have h1 : g * w * g⁻¹ ∈ ((g • Q : Sylow 3 GJ) : Subgroup GJ) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hwQ (mem_zpowers w), by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hg] at h1
    exact h1
  set w₁ := g * w * g⁻¹ with hw₁def
  have hw₁3 : w₁ ^ 3 = 1 := by rw [hw₁def, conj_pow, hw3, mul_one, mul_inv_cancel]
  have hw₁1 : w₁ ≠ 1 := by
    rw [hw₁def]
    intro h
    apply hw1
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hN₁ : Nat.card (normalizer ((zpowers w₁ : Subgroup GJ) : Set GJ)) = 72 := by
    rw [hw₁def, card_normalizer_zpowers_conj, hN]
  have hw₁z := not_mem_zpowers_zJ hw₁3 hw₁1 hN₁
  have hzP : zJ ∈ P3 := by rw [z_eq]; exact z_mem_P3
  have hzC : zJ ∈ centralizer ((P3 : Subgroup GJ) : Set GJ) := by
    have h1 : zJ ∈ P3 ⊓ centralizer ((P3 : Subgroup GJ) : Set GJ) := by
      rw [inf_centralizer_P3, ← z_eq]
      exact mem_zpowers zJ
    exact h1.2
  set A := zpowers w₁ ⊔ zpowers zJ with hA
  have hAP : A ≤ P3 := sup_le (zpowers_le.mpr hw₁) (zpowers_le.mpr hzP)
  have hA9 : Nat.card A = 9 := by
    have hcomm : zpowers w₁ ≤ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) := by
      rw [zpowers_le]
      refine centralizer_le_normalizer_zpowers' zJ ?_
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hzC w₁ hw₁
    have h := Item4443SL.card_sup_mul_card_inf hcomm
    have hinf : zpowers w₁ ⊓ zpowers zJ = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      by_contra hu1
      apply hw₁z
      have hu3 : orderOf u = 3 :=
        orderOf_eq_prime (by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu.1
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw₁3, one_zpow])
          hu1
      have h1 : zpowers u = zpowers w₁ := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hu.1)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hu3, orderOf_eq_prime hw₁3 hw₁1])
      have h2 : zpowers u ≤ zpowers zJ := zpowers_le.mpr hu.2
      rw [h1] at h2
      exact h2 (mem_zpowers w₁)
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hw₁3 hw₁1,
      card_zpowers_z] at h
    exact h
  have hE0 : E0 ∈ {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9} := by
    rw [nine_eq]
    exact ⟨0, rfl⟩
  obtain ⟨n, -, hnA⟩ := delta_transitive A ⟨hAP, hA9⟩ E0 hE0
  set w₂ := n⁻¹ * w₁ * n⁻¹⁻¹ with hw₂def
  have hw₂E : w₂ ∈ E0 := by
    rw [hnA]
    exact ⟨w₁, le_sup_left (α := Subgroup GJ) (mem_zpowers w₁), rfl⟩
  have hw₂3 : w₂ ^ 3 = 1 := by rw [hw₂def, conj_pow, hw₁3, mul_one, mul_inv_cancel]
  have hw₂1 : w₂ ≠ 1 := by
    rw [hw₂def]
    intro h
    apply hw₁1
    calc w₁ = n * (n⁻¹ * w₁ * n⁻¹⁻¹) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hN₂ : Nat.card (normalizer ((zpowers w₂ : Subgroup GJ) : Set GJ)) = 72 := by
    rw [hw₂def, card_normalizer_zpowers_conj, hN₁]
  obtain ⟨k, hk⟩ := zpowers_eq_a hw₂E (not_mem_zpowers_zJ hw₂3 hw₂1 hN₂)
  refine ⟨(cJ k)⁻¹ * n⁻¹ * g, ?_⟩
  have e1 : (cJ k)⁻¹ * n⁻¹ * g * w * ((cJ k)⁻¹ * n⁻¹ * g)⁻¹ =
      (MulAut.conj (cJ k)⁻¹) w₂ := by
    rw [MulAut.conj_apply, hw₂def, hw₁def]
    group
  rw [e1]
  change zpowers ((MulAut.conj (cJ k)⁻¹).toMonoidHom w₂) = _
  rw [← MonoidHom.map_zpowers, hk, MonoidHom.map_zpowers]
  congr 1
  change (cJ k)⁻¹ * aJ k * (cJ k)⁻¹⁻¹ = xJ
  rw [inv_inv, conj_c_a]

theorem pCore_eq_and_card_normalizer
    {S : Type} [Group S]
    (φ₀ : S ≃* Blueprint.NativeSporadic.J2) {y : S} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (h72 : Nat.card (normalizer ((zpowers y : Subgroup S) : Set S)) = 72) :
    inSubgroup (CFSG.pCore 2) (centralizer ({y} : Set S)) =
        inSubgroup (CFSG.pCore 2) (normalizer ((zpowers y : Subgroup S) : Set S)) ∧
      Nat.card (normalizer ((inSubgroup (CFSG.pCore 2) (centralizer ({y} : Set S)) :
        Subgroup S) : Set S)) = 720 := by
  set ψ₀ : S ≃* GJ := φ₀.trans CFSG.ComponentClassification.J2Cover.nativeEquivP with hψ₀
  have hy'3 : ψ₀ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hy'1 : ψ₀ y ≠ 1 := by rwa [Ne, MulEquiv.map_eq_one_iff]
  have h72' : Nat.card (normalizer ((zpowers (ψ₀ y) : Subgroup GJ) : Set GJ)) = 72 := by
    rw [normalizer_zpowers_map, Subgroup.card_map_of_injective ψ₀.injective, h72]
  obtain ⟨g, hg⟩ := exists_conj_zpowers_xJ hy'3 hy'1 h72'
  set ψ : S ≃* GJ := ψ₀.trans (MulAut.conj g) with hψ
  have hψy : ψ y = g * ψ₀ y * g⁻¹ := rfl
  have hz : zpowers (ψ y) = zpowers xJ := by rw [hψy, hg]
  have hcz : ∀ a : GJ, centralizer ((zpowers a : Subgroup GJ) : Set GJ) =
      centralizer ({a} : Set GJ) := fun a => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hC : (centralizer ({y} : Set S)).map ψ.toMonoidHom = centralizer ({xJ} : Set GJ) := by
    rw [map_centralizer_singleton, ← hcz, hz, hcz]
  have hN : (normalizer ((zpowers y : Subgroup S) : Set S)).map ψ.toMonoidHom =
      normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) := by
    rw [← normalizer_zpowers_map, hz]
  have hVC : (inSubgroup (CFSG.pCore 2) (centralizer ({y} : Set S))).map ψ.toMonoidHom = VJ := by
    rw [inSubgroup_pCore_map, hC, pCore_centralizer_x]
  have hVN : (inSubgroup (CFSG.pCore 2) (normalizer ((zpowers y : Subgroup S) : Set S))).map
      ψ.toMonoidHom = VJ := by
    rw [inSubgroup_pCore_map, hN, pCore_normalizer_x]
  refine ⟨Subgroup.map_injective ψ.injective (hVC.trans hVN.symm), ?_⟩
  rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
    Subgroup.map_equiv_normalizer_eq, hVC, card_normalizer_VJ]

end Res462J2Model

open Res462J2Model

theorem k462J2Inner :
    K462J2Inner := by
  intro S _ hS y hy3 hy1 hNy W hW2 hWC hWN
  obtain ⟨φ₀⟩ := hS
  have : Finite S := Finite.of_equiv _ φ₀.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ny := normalizer ((zpowers y : Subgroup S) : Set S) with hNydef
  set V := inSubgroup (CFSG.pCore 2) (centralizer ({y} : Set S)) with hVdef
  have h72 : Nat.card Ny = 72 := by
    obtain ⟨e⟩ := hNy
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨hVN, h720⟩ := pCore_eq_and_card_normalizer φ₀ hy3 hy1 h72
  have hVN' : V = inSubgroup (CFSG.pCore 2) Ny := hVN
  have h720' : Nat.card (normalizer (V : Set S)) = 720 := h720
  have hV2 : IsPGroup 2 V := (CFSG.pCore_isPGroup (p := 2)).map _
  have hVC : V ≤ centralizer ({y} : Set S) := Subgroup.map_subtype_le _
  have hNyV : ∀ n ∈ Ny, n ∈ normalizer (V : Set S) := fun n hn =>
    Step462UAlphaProof.mem_normalizer_inSubgroup_pCore
      (Step462UAlphaProof.mem_normalizer_centralizer_singleton hn)
  have hWNV : W ≤ normalizer (V : Set S) := hWC.trans (centralizer_le_normalizer _)
  set W' := W ⊔ V with hW'def
  have hW'2 : IsPGroup 2 W' := IsPGroup.to_sup_of_normal_right' hW2 hV2 hWNV
  have hVW' : V ≤ W' := le_sup_right
  have hW'NV : W' ≤ normalizer (V : Set S) := sup_le hWNV (Subgroup.le_normalizer)
  have hNyW' : Ny ≤ normalizer (W' : Set S) := fun n hn =>
    Step462UAlphaM12.mem_normalizer_sup (hWN n hn) (hNyV n hn)
  have hinf : Ny ⊓ W' = V := by
    apply le_antisymm
    · rw [hVN']
      have hle : Ny ⊓ W' ≤ Ny := inf_le_left
      refine Sporadic.J2.le_inSubgroup_pCore hle ?_ (hW'2.to_le inf_le_right)
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
      intro n hn
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hn, hNyW' hn⟩
    · exact le_inf (hVC.trans (centralizer_le_normalizer_zpowers' y)) hVW'
  have hprod := Item4443SL.card_sup_mul_card_inf hNyW'
  rw [hinf, h72] at hprod
  have hdvd : Nat.card (Ny ⊔ W' : Subgroup S) ∣ 720 := by
    rw [← h720']
    exact Subgroup.card_dvd_of_le (sup_le (fun n hn => hNyV n hn) hW'NV)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hVW'
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hm10 : m ∣ 10 := by
    obtain ⟨r, hr⟩ := hdvd
    have h1 : Nat.card (Ny ⊔ W' : Subgroup S) = 72 * m := by
      have h2 : Nat.card (Ny ⊔ W' : Subgroup S) * Nat.card V = (72 * m) * Nat.card V := by
        rw [hprod, hm]; ring
      exact Nat.eq_of_mul_eq_mul_right hVpos h2
    rw [h1] at hr
    have h3 : m * r = 10 := by
      have h4 : 72 * (m * r) = 72 * 10 := by
        rw [← mul_assoc, ← hr]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
    exact ⟨r, h3.symm⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hW'2
  have hm2 : m ∣ 2 ^ a := ⟨Nat.card V, by rw [← ha, hm, mul_comm]⟩
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm2
  have hc1 : c ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 10 := (Nat.pow_dvd_pow 2 (by omega)).trans (hc ▸ hm10)
    norm_num at h4
  have hy3' : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hmod := card_modEq_card_centralizer_inf
    (hNyW' (Subgroup.le_normalizer (mem_zpowers y))) hy3'
  have hfix : centralizer ({y} : Set S) ⊓ W' = V := by
    apply le_antisymm
    · rw [← hinf]
      exact inf_le_inf_right _ (centralizer_le_normalizer_zpowers' y)
    · exact le_inf hVC hVW'
  rw [hfix, hm] at hmod
  interval_cases c
  ·
    rw [hc, pow_zero, mul_one] at hm
    have hWV : W' = V := (Subgroup.eq_of_le_of_card_ge hVW' (le_of_eq hm)).symm
    exact (le_sup_left : W ≤ W').trans hWV.le
  ·
    exfalso
    rw [hc, pow_one] at hmod
    have h3 : 3 ∣ Nat.card V := by
      have := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      have e : Nat.card V * 2 - Nat.card V = Nat.card V := by omega
      rwa [e] at this
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp hV2
    rw [hb] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

theorem step462UAlpha_holds :
    Step462UAlpha :=
  step462UAlpha_of_j2Inner k462J2Inner

end CFSG.RankThree.PartTwo.Sec4
