module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HNAE9
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Ree
public import CFSG.LieType.Steinberg.CentralExt.GriessReeF4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Tor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

open CFSG.LieType.Ree (ReeTag)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


section SU3

open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagUHom diagU_injective permGL)


variable {F : Type} [Field F]

theorem three_dvd_two_pow_odd_add_one (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
  have h4 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  rw [h2, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, h4]

theorem zpow_eq_zpow_emod_three {M : Type*} [Group M] {u : M} (hu : u ^ 3 = 1) (m : ℤ) :
    u ^ m = u ^ (m % 3) := by
  exact zpow_eq_zpow_emod' m hu

theorem rot_not_mem_zpowers {d : Fin 3 → Fˣ} (hd3 : ∀ i, d i ^ 3 = 1)
    (hnc : ¬ ∀ i j, d i = d j) (m : ℤ) : d ∘ (finRotate 3).symm ≠ d ^ m := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Function.comp_apply, Pi.pow_apply] at h0 h1 h2
  have e0 : (finRotate 3).symm 0 = 2 := by decide
  have e1 : (finRotate 3).symm 1 = 0 := by decide
  have e2 : (finRotate 3).symm 2 = 1 := by decide
  rw [e0, zpow_eq_zpow_emod_three (hd3 0)] at h0
  rw [e1, zpow_eq_zpow_emod_three (hd3 1)] at h1
  rw [e2, zpow_eq_zpow_emod_three (hd3 2)] at h2
  apply hnc
  have hall : d 0 = d 1 ∧ d 1 = d 2 := by
    rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with hm | hm | hm <;>
      rw [hm] at h0 h1 h2
    · simp only [zpow_zero] at h0 h1 h2
      exact ⟨h1.trans h2.symm, h2.trans h0.symm⟩
    · simp only [zpow_one] at h0 h1 h2
      exact ⟨h1, h2⟩
    · have h0' : d 2 = d 0 ^ 2 := by rw [h0]; norm_cast
      have h1' : d 0 = d 1 ^ 2 := by rw [h1]; norm_cast
      have h2' : d 1 = d 2 ^ 2 := by rw [h2]; norm_cast
      have hd2 : d 0 = d 2 := by
        calc d 0 = d 1 ^ 2 := h1'
          _ = (d 2 ^ 2) ^ 2 := by rw [h2']
          _ = d 2 ^ 3 * d 2 := by rw [← pow_mul, ← pow_succ]
          _ = d 2 := by rw [hd3 2, one_mul]
      have h2one : d 2 = 1 := by
        have h' : d 2 * 1 = d 2 * d 2 := by
          rw [mul_one]
          calc d 2 = d 0 ^ 2 := h0'
            _ = d 2 ^ 2 := by rw [hd2]
            _ = d 2 * d 2 := sq _
        exact (mul_left_cancel h').symm
      have h0one : d 0 = 1 := hd2.trans h2one
      have h1one : d 1 = 1 := by rw [h2', h2one, one_pow]
      exact ⟨h0one.trans h1one.symm, h1one.trans h2one.symm⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hall.1, hall.2]

theorem isElemAbelian_torusSU_three (F : Type) [Field F] :
    CFSG.Assembly.IsElemAbelian 3 (torusSU 3 3 F) := by
  refine isElemAbelian_map diagUHom ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun d hd => ?_⟩
  funext i
  rw [Pi.pow_apply, hd.1 i, Pi.one_apply]

theorem exists_e9_unitarySU {f : ℕ} (h : UnitaryFieldData 2 f F) (h3 : 3 ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (unitarySU 2 f F 3), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI := h.finite
  have hζ : ∃ ζ : Fˣ, IsPrimitiveRoot ζ 3 := by
    obtain ⟨z, hz⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h Nat.prime_three h3
    have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
    exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  have hle : torusSU 3 3 F ≤ unitarySU 2 f F 3 :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU h h3
  refine ⟨(torusSU 3 3 F).subgroupOf (unitarySU 2 f F 3),
    isElemAbelian_comap _ (unitarySU 2 f F 3).subtype_injective (isElemAbelian_torusSU_three F),
    ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    CFSG.RankThree.PartOne.KFU.torusSU, Subgroup.card_map_of_injective diagU_injective,
    CFSG.RankThree.PartOne.KFU.card_torusVec_eq (by norm_num) hζ 2]
  norm_num

end SU3

section Ree


open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagUHom diagU_injective permGL
  mem_torusSU_iff)


variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem e9Move_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    E9Move (ReeTag.F4.reeGamma K a) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro B hB hB9 c hcB hc1
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hBc : ∀ x ∈ B, ∀ z ∈ B, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  obtain ⟨y, hyB, hyc⟩ : ∃ y ∈ B, y ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have hle : B ≤ Subgroup.zpowers c := fun x hx => h x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers] at h1
    have h2 : orderOf c ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hc3
    omega
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hy1 : y ≠ 1 := fun h => hyc (h ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨eU⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hyo
  set Fq := GaloisField 2 (2 * (2 * a + 1)) with hFq
  have hU : UnitaryFieldData 2 (2 * a + 1) Fq :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  haveI := hU.finite
  have hpq := three_dvd_two_pow_odd_add_one a
  set C := Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) with hCdef
  have hBC : B ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hBc x hx y hyB)
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set B₁ : Subgroup C := B.subgroupOf C with hB₁
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso_le_of_iso hU Nat.prime_three hpq
    eU.symm B₁ (fun x hx => Subtype.ext (hB.2 _ hx))
    (fun x hx z hz => Subtype.ext (hBc _ hx _ hz))
  set T : Subgroup (unitarySU 2 (2 * a + 1) Fq 3) :=
    (torusSU 3 3 Fq).subgroupOf (unitarySU 2 (2 * a + 1) Fq 3) with hT
  have hTle : B₁.comap ψ.toMonoidHom ≤ T := fun g hg => hψ g hg
  have hTcard : Nat.card T ≤ 9 := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hU hpq)).toEquiv]
    exact CFSG.RankThree.PartOne.KFU.card_torusSU_le (by norm_num) 2
  have hB₁c : Nat.card (B₁.comap ψ.toMonoidHom) = 9 := by
    have hmap : (B₁.comap ψ.toMonoidHom).map ψ.toMonoidHom = B₁ :=
      Subgroup.map_comap_eq_self_of_surjective ψ.surjective _
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hmap, hB₁,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hB9]
  have hTeq : B₁.comap ψ.toMonoidHom = T := Subgroup.eq_of_le_of_card_ge hTle (by omega)
  have hmemT : ∀ g : unitarySU 2 (2 * a + 1) Fq 3,
      ψ g ∈ B₁ ↔ (g : GL (Fin 3) Fq) ∈ torusSU 3 3 Fq := by
    intro g
    have := SetLike.ext_iff.mp hTeq g
    exact this
  set c₁ : C := ⟨c, hBC hcB⟩ with hc₁
  set y₁ : C := ⟨y, hyC⟩ with hy₁
  have hc₁B : c₁ ∈ B₁ := hcB
  have hy₁B : y₁ ∈ B₁ := hyB
  have hgc : ((ψ.symm c₁ : unitarySU 2 (2 * a + 1) Fq 3) : GL (Fin 3) Fq) ∈ torusSU 3 3 Fq :=
    (hmemT _).mp (by rw [MulEquiv.apply_symm_apply]; exact hc₁B)
  have hgy : ((ψ.symm y₁ : unitarySU 2 (2 * a + 1) Fq 3) : GL (Fin 3) Fq) ∈ torusSU 3 3 Fq :=
    (hmemT _).mp (by rw [MulEquiv.apply_symm_apply]; exact hy₁B)
  obtain ⟨d, hd3, hdp, hdc⟩ := mem_torusSU_iff.mp hgc
  obtain ⟨e, he3, hep, hey⟩ := mem_torusSU_iff.mp hgy
  let P : Equiv.Perm (Fin 3) → unitarySU 2 (2 * a + 1) Fq 3 := fun σ =>
    ⟨permGL σ, CFSG.RankThree.PartOne.KFU.permGL_mem_unitarySU hU σ⟩
  have hPcoe : ∀ σ, ((P σ : unitarySU 2 (2 * a + 1) Fq 3) : GL (Fin 3) Fq) = permGL σ :=
    fun _ => rfl
  have hecomm : ∀ σ : Equiv.Perm (Fin 3), e ∘ σ.symm = e := by
    intro σ
    have hcy : ψ (P σ) * y₁ = y₁ * ψ (P σ) := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (ψ (P σ)).2
    have h1 : P σ * ψ.symm y₁ = ψ.symm y₁ * P σ := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcy]
    have h2 : permGL σ * diagU e * (permGL σ)⁻¹ = diagU e := by
      rw [hey]
      have := congrArg (fun x : unitarySU 2 (2 * a + 1) Fq 3 => (x : GL (Fin 3) Fq)) h1
      simp only [Subgroup.coe_mul, hPcoe] at this
      rw [this, mul_inv_cancel_right]
    rw [CFSG.RankThree.PartOne.KFU.permGL_conj_diagU] at h2
    exact diagU_injective h2
  have heconst : ∀ i, e i = e 0 := by
    intro i
    fin_cases i
    · rfl
    · have := congrFun (hecomm (Equiv.swap 0 1)) 0
      simpa using this
    · have := congrFun (hecomm (Equiv.swap 0 2)) 0
      simpa using this
  have hdnc : ¬ ∀ i j, d i = d j := by
    intro hdconst
    have he1 : e 0 ≠ 1 := by
      intro h1
      apply hy1
      have : e = 1 := funext fun i => by rw [heconst i, h1]; rfl
      have hgy1 : ψ.symm y₁ = 1 := by
        apply Subtype.ext
        rw [← hey, this, CFSG.RankThree.PartOne.KFU.diagU_one]
        rfl
      have : y₁ = 1 := by
        rw [← MulEquiv.apply_symm_apply ψ y₁, hgy1, map_one]
      exact congrArg Subtype.val this
    have hprim : IsPrimitiveRoot (e 0) 3 :=
      (IsPrimitiveRoot.iff_orderOf).mpr (orderOf_eq_prime (he3 0) he1)
    have hprim' : IsPrimitiveRoot ((e 0 : Fqˣ) : Fq) 3 := IsPrimitiveRoot.coe_units_iff.mpr hprim
    have hd0 : ((d 0 : Fqˣ) : Fq) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hd3 0, Units.val_one]
    obtain ⟨k, -, hk'⟩ := hprim'.eq_pow_of_pow_eq_one hd0
    have hk : e 0 ^ k = d 0 := Units.ext (by rw [Units.val_pow_eq_pow_val, hk'])
    have hde : d = e ^ k := funext fun i => by
      rw [Pi.pow_apply, heconst i, hdconst i 0, hk]
    have hcy : c₁ = y₁ ^ k := by
      apply ψ.symm.injective
      apply Subtype.ext
      rw [map_pow, SubgroupClass.coe_pow, ← hdc, ← hey, hde,
        CFSG.RankThree.PartOne.KFU.diagU_pow]
    apply hyc
    have hcy' : c = y ^ k := congrArg Subtype.val hcy
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers y := by
      rw [Subgroup.zpowers_le, hcy']
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k
    have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers c) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo,
        orderOf_eq_prime hc3 hc1]
    rw [Subgroup.eq_of_le_of_card_ge hle hcard]
    exact Subgroup.mem_zpowers y
  set ρ : Equiv.Perm (Fin 3) := finRotate 3 with hρ
  have hPconj : ∀ x : GL (Fin 3) Fq, x ∈ torusSU 3 3 Fq ↔
      permGL ρ * x * (permGL ρ)⁻¹ ∈ torusSU 3 3 Fq := by
    intro x
    constructor
    · exact (CFSG.RankThree.PartOne.KFU.normPerm_permGL (p := 3) ρ).1 x
    · intro hx
      have h := (CFSG.RankThree.PartOne.KFU.normPerm_permGL (p := 3) ρ⁻¹).1 _ hx
      have heq : (permGL ρ)⁻¹ * (permGL ρ * x * (permGL ρ)⁻¹) * ((permGL ρ)⁻¹)⁻¹ = x := by
        group
      rwa [map_inv, heq] at h
  set n : ReeTag.F4.reeGamma K a := ((ψ (P ρ) : C) : ReeTag.F4.reeGamma K a) with hn
  have hnC : n ∈ C := (ψ (P ρ)).2
  refine ⟨n, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ z : C, (z : ReeTag.F4.reeGamma K a) ∈ B ↔
        n * z * n⁻¹ ∈ B := by
      intro z
      have hz : ((ψ (P ρ) * z * (ψ (P ρ))⁻¹ : C) : ReeTag.F4.reeGamma K a) = n * z * n⁻¹ := rfl
      rw [← hz]
      change z ∈ B₁ ↔ ψ (P ρ) * z * (ψ (P ρ))⁻¹ ∈ B₁
      rw [← MulEquiv.apply_symm_apply ψ z, ← map_inv, ← map_mul, ← map_mul, hmemT, hmemT]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hPcoe]
      exact hPconj _
    constructor
    · intro hx
      exact (key ⟨x, hBC hx⟩).mp hx
    · intro hx
      have hxC : x ∈ C := by
        have h1 : n * x * n⁻¹ ∈ C := hBC hx
        have h2 : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem hnC) h1) hnC
      exact (key ⟨x, hxC⟩).mpr hx
  · intro hnZ
    have hs : n * c * n⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hnZ c).mp (Subgroup.mem_zpowers c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk₁ : c₁ ^ k = ψ (P ρ) * c₁ * (ψ (P ρ))⁻¹ := Subtype.ext (by
      rw [SubgroupClass.coe_zpow]
      exact hk)
    have hk₂ : (ψ.symm c₁) ^ k = P ρ * ψ.symm c₁ * (P ρ)⁻¹ := by
      apply ψ.injective
      rw [map_zpow, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hk₁]
    have hk₃ : (diagU d) ^ k = permGL ρ * diagU d * (permGL ρ)⁻¹ := by
      rw [hdc]
      have := congrArg (fun x : unitarySU 2 (2 * a + 1) Fq 3 => (x : GL (Fin 3) Fq)) hk₂
      simpa [hPcoe] using this
    rw [CFSG.RankThree.PartOne.KFU.permGL_conj_diagU] at hk₃
    have hdk : d ∘ ρ.symm = d ^ k := by
      apply diagU_injective
      rw [← hk₃]
      exact (map_zpow diagUHom d k).symm
    exact rot_not_mem_zpowers hd3 hdnc k hdk

theorem exists_e9_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ E : Subgroup (ReeTag.F4.reeGamma K a), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ReeTag.F4.reeGamma K a) := by
    haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
      CFSG.LieType.Chevalley.finite_modGL
    exact Subtype.finite
  have h3 : 3 ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
    rw [Sec8.Item86ResProof.card_of_mulEquiv_reeGamma a K hK (MulEquiv.refl _)]
    exact Ronan148L.three_dvd_ordTwistedF4 a
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨eU⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have hU : UnitaryFieldData 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  obtain ⟨E, hE, hE9⟩ := exists_e9_unitarySU hU (three_dvd_two_pow_odd_add_one a)
  refine ⟨(E.map eU.symm.toMonoidHom).map (Subgroup.centralizer ({y} : Set _)).subtype,
    isElemAbelian_map _ (isElemAbelian_map _ hE), ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Subgroup.card_map_of_injective eU.symm.injective, hE9]

theorem out_cube_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α β : MulAut (ReeTag.F4.reeGamma K a)) (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1)
    (hαo : ¬ IsInnerAut α) : ∃ k : ℕ, IsInnerAut (α ^ k * β) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hcyc, hcard, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK
  haveI : Finite (Outer (ReeTag.F4.reeGamma K a)) := Nat.finite_of_card_ne_zero (by omega)
  set abar : Outer (ReeTag.F4.reeGamma K a) := QuotientGroup.mk α with habar
  set bbar : Outer (ReeTag.F4.reeGamma K a) := QuotientGroup.mk β with hbbar
  have habar1 : abar ≠ 1 := fun h => hαo ((QuotientGroup.eq_one_iff α).mp h)
  have habar3 : abar ^ 3 = 1 := by rw [habar, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hbbar3 : bbar ^ 3 = 1 := by rw [hbbar, ← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  have habaro : orderOf abar = 3 := orderOf_eq_prime habar3 habar1
  have hle : Subgroup.zpowers bbar ≤ Subgroup.zpowers abar := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, habaro]
    exact orderOf_dvd_of_pow_eq_one hbbar3
  have hmem : bbar ∈ Submonoid.powers abar :=
    (isOfFinOrder_of_finite abar).mem_powers_iff_mem_zpowers.mpr (hle (Subgroup.mem_zpowers bbar))
  obtain ⟨j, hj⟩ := hmem
  dsimp only at hj
  refine ⟨2 * j, (QuotientGroup.eq_one_iff (α ^ (2 * j) * β)).mp ?_⟩
  have h1 : (QuotientGroup.mk (α ^ (2 * j) * β) : Outer (ReeTag.F4.reeGamma K a)) =
      abar ^ (2 * j) * bbar := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  refine h1.trans ?_
  rw [← hj, ← pow_add, show 2 * j + j = 3 * j by ring, pow_mul, habar3, one_pow]
  rfl

theorem fix_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (ReeTag.F4.reeGamma K a)) (hα : α ^ 3 = 1) (hαo : ¬ IsInnerAut α) :
    (∃ E : Subgroup (autFix α), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
      E9Move (autFix α) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαo ⟨1, map_one _⟩
  have hout : ∀ g : ReeTag.F4.reeGamma K a, α ≠ MulAut.conj g := fun g h => hαo ⟨g, h.symm⟩
  obtain ⟨g, β, hβ, hαeq⟩ := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeF4_stdDescent_odd
    ha hK Nat.prime_three α ⟨orderOf_eq_prime hα hα1, hout⟩
  obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_fieldAut_equiv hK
      Nat.prime_three (by norm_num) β hβ
  haveI := hchar
  haveI : Finite (CFSG.LieType.Chevalley.fixSubfield β) := Subtype.finite
  set δ := ReeTag.F4.reeGammaFieldAut K a β with hδ
  have hfix : autFix δ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ :=
    Subgroup.ext fun _ => Iff.rfl
  let eA : autFix α ≃* ReeTag.F4.reeGamma (CFSG.LieType.Chevalley.fixSubfield β) b :=
    (((MulEquiv.subgroupCongr (by rw [hαeq])).trans
      (RonanK429Lie.autFixConjEquiv (MulAut.conj g) δ)).trans
        (MulEquiv.subgroupCongr hfix)).trans eC
  obtain ⟨E, hE, hE9⟩ := exists_e9_reeGamma b (CFSG.LieType.Chevalley.fixSubfield β) hkcard
  refine ⟨⟨E.map eA.symm.toMonoidHom, isElemAbelian_map _ hE, by
    rw [Subgroup.card_map_of_injective eA.symm.injective, hE9]⟩, ?_⟩
  exact (e9Move_reeGamma b (CFSG.LieType.Chevalley.fixSubfield β) hkcard).of_mulEquiv eA

end Ree

section Row


theorem noThreeCover_reeF4 (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    NoThreeCover (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hm).1
  have hmodel : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
      .twistedF4 0 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
      Or.inr ⟨rfl, ⟨_, hm⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  exact Ronan148L.noThreeCover_of_table rfl rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedF4_row hmodel).2

theorem rowOf425_reeF4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  intro m hm S _ _ _ _ ⟨eS⟩
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hm eS
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  exact row425_of_e9Move_outer_of_mulEquiv e (NoThreeCover.of_mulEquiv eS (noThreeCover_reeF4 m hm))
    (e9Move_reeGamma a K hK)
    (Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK)
    (exists_e9_reeGamma a K hK) (out_cube_reeGamma a K ha hK) (fix_reeGamma a K ha hK)

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
