module

public import CFSG.RankThree.GF2n.Parrott.Section3RemarksV
import CFSG.GroupTheory.HyperplaneDecomposition

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem CJ_conj_eq_map (g : H z) (σ : G) :
    CJ z ((g : G) * σ * (g : G)⁻¹) = (CJ z σ).map (MulAut.conj (g : G)).toMonoidHom := by
  have hJn : (g : G) ∈ Subgroup.normalizer (J z : Set G) := J_le_normalizer_A (z := z) g.2
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    rw [mem_CJ] at hx
    refine ⟨(g : G)⁻¹ * x * (g : G), ?_, ?_⟩
    · rw [mem_CJ]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h := Subgroup.mem_centralizer_singleton_iff.mp hx.1
        calc (g : G)⁻¹ * x * (g : G) * σ
            = (g : G)⁻¹ * (x * ((g : G) * σ * (g : G)⁻¹)) * (g : G) := by group
          _ = (g : G)⁻¹ * (((g : G) * σ * (g : G)⁻¹) * x) * (g : G) := by rw [h]
          _ = σ * ((g : G)⁻¹ * x * (g : G)) := by group
      · have hinv : (g : G)⁻¹ ∈ Subgroup.normalizer (J z : Set G) := inv_mem hJn
        have := (Subgroup.mem_normalizer_iff.mp hinv x).mp hx.2
        simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨y, hy, rfl⟩
    rw [mem_CJ] at hy ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hJn y).mp hy.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp hy.1
    calc (g : G) * y * (g : G)⁻¹ * ((g : G) * σ * (g : G)⁻¹)
        = (g : G) * (y * σ) * (g : G)⁻¹ := by group
      _ = (g : G) * (σ * y) * (g : G)⁻¹ := by rw [h]
      _ = (g : G) * σ * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) := by group

theorem card_CJ_conj_eq (g : H z) (σ : G) :
    Nat.card (CJ z ((g : G) * σ * (g : G)⁻¹)) = Nat.card (CJ z σ) := by
  rw [CJ_conj_eq_map, Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]

theorem card_CJ_eq_eight_of_cube (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) {y σ : H z}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ) : Nat.card (CJ z (σ : G)) = 8 := by
  have hσ3 : orderOf σ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  rw [card_CJ_eq_two_mul hJ hcard hcomm hσ3, fixDimV_eq_two_of_cube hJ hcard hcomm hCHJ hy hyσ]
  norm_num

theorem zpowers_le_normalizer_J (σ : H z) :
    Subgroup.zpowers (σ : G) ≤ Subgroup.normalizer (J z : Set G) :=
  (Subgroup.zpowers_le (G := G) (H := Subgroup.normalizer (J z : Set G))).mpr
    (J_le_normalizer_A (z := z) σ.2)

theorem isExtraspecial2_CJ_of_card_eight (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ : H z} (hσ : orderOf σ = 3)
    (h8 : Nat.card (CJ z (σ : G)) = 8) : IsExtraspecial2 (CJ z (σ : G)) := by
  have hσG : orderOf (σ : G) = 3 := by rw [Subgroup.orderOf_coe, hσ]
  have hB3 : IsPGroup 3 (Subgroup.zpowers (σ : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσG, pow_one])
  have hBne : Subgroup.zpowers (σ : G) ≠ ⊥ := by
    intro hbot
    have hmem : (σ : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hσG
    norm_num at hσG
  have hprop := prop5_centralizer Nat.prime_three (by norm_num)
    (H := G) (J := J z) (P := Subgroup.zpowers (σ : G)) hJ hB3 hBne
    (zpowers_le_normalizer_J σ)
  have hCP : J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G) = CJ z (σ : G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm]
    rfl
  rcases hprop with hE | hE
  · rwa [hCP] at hE
  · exfalso
    rw [hCP] at hE
    have h2 : Nat.card (CJ z (σ : G)) = 2 := by
      rw [hE, Subgroup.card_map_of_injective (J z).subtype_injective, card_center_J hJ hcomm]
    rw [h8] at h2
    norm_num at h2

theorem mem_normalizer_CJ_of_commute {σ₁ σ₂ : H z} (hc : Commute σ₁ σ₂) :
    (σ₂ : G) ∈ Subgroup.normalizer (CJ z (σ₁ : G) : Set G) := by
  have hσ2cent : (σ₂ : G) ∈ Subgroup.centralizer ({(σ₁ : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc.eq).symm
  have hσ2normCent : (σ₂ : G) ∈
      Subgroup.normalizer (Subgroup.centralizer ({(σ₁ : G)} : Set G) : Set G) :=
    Subgroup.le_normalizer hσ2cent
  have hσ2normJ : (σ₂ : G) ∈ Subgroup.normalizer (J z : Set G) :=
    J_le_normalizer_A (z := z) σ₂.2
  rw [show CJ z (σ₁ : G) = Subgroup.centralizer ({(σ₁ : G)} : Set G) ⊓ J z from rfl]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp hσ2normCent x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp hσ2normJ x).mp hx.2⟩
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp hσ2normCent x).mpr hx.1,
      (Subgroup.mem_normalizer_iff.mp hσ2normJ x).mpr hx.2⟩

theorem nonempty_CJ_mulEquiv_quaternion (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ₁ σ₂ : H z} (h3₁ : orderOf σ₁ = 3)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (h8₁ : Nat.card (CJ z (σ₁ : G)) = 8)
    (h8₂ : Nat.card (CJ z (σ₂ : G)) = 8) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) :
    Nonempty (↥(CJ z (σ₁ : G)) ≃* QuaternionGroup 2) ∧
      ∀ r : ↥(CJ z (σ₁ : G)), r ∉ Subgroup.center ↥(CJ z (σ₁ : G)) → orderOf r = 4 := by
  have hact : ∃ e ∈ CJ z (σ₁ : G), (σ₂ : G) * e * (σ₂ : G)⁻¹ ≠ e := by
    have hnotfix := not_forall_conj_eq_of_ne (h8₁.trans h8₂.symm) hne
    push Not at hnotfix
    exact hnotfix
  exact centralizer_is_quaternion_of_three_action
    (isExtraspecial2_CJ_of_card_eight hJ hcomm h3₁ h8₁) h8₁
    (by rw [Subgroup.orderOf_coe, h3₂]) (mem_normalizer_CJ_of_commute hc) hact

theorem z_mem_CJ (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) (x : H z) : z ∈ CJ z (x : G) := by
  rw [mem_CJ]
  exact ⟨zpowers_le_centralizer x (Subgroup.mem_zpowers z), z_mem_J hcomm⟩

theorem card_CJ_modEq_card_CJ_inf {σ₁ σ₂ : H z} (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) :
    Nat.card ↥(CJ z (σ₁ : G)) ≡ Nat.card ↥(CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G)) [MOD 3] := by
  classical
  have : Fintype ↥(CJ z (σ₁ : G)) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := mem_normalizer_CJ_of_commute hc
  have h3 : (σ₂ : G) * (σ₂ : G) * (σ₂ : G) = 1 := by
    rw [← pow_three', ← Subgroup.coe_pow, ← h3₂, pow_orderOf_eq_one, Subgroup.coe_one]
  let f : Function.End ↥(CJ z (σ₁ : G)) := fun y =>
    ⟨(σ₂ : G) * (y : G) * (σ₂ : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hN y).mp y.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    show (σ₂ : G) * ((σ₂ : G) * ((σ₂ : G) * (y : G) * (σ₂ : G)⁻¹) * (σ₂ : G)⁻¹) *
      (σ₂ : G)⁻¹ = (y : G)
    calc (σ₂ : G) * ((σ₂ : G) * ((σ₂ : G) * (y : G) * (σ₂ : G)⁻¹) * (σ₂ : G)⁻¹) * (σ₂ : G)⁻¹
        = ((σ₂ : G) * (σ₂ : G) * (σ₂ : G)) * (y : G) *
            ((σ₂ : G) * (σ₂ : G) * (σ₂ : G))⁻¹ := by group
      _ = (y : G) := by rw [h3]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hcard : Nat.card ↑(Function.fixedPoints f) =
      Nat.card ↥(CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G)) :=
    Nat.card_congr
    { toFun := fun y => ⟨y.1, Subgroup.mem_inf.mpr ⟨y.1.2, by
          refine mem_CJ.mpr ⟨?_, (mem_CJ.mp y.1.2).2⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hy : (σ₂ : G) * (y.1 : G) * (σ₂ : G)⁻¹ = (y.1 : G) := congrArg Subtype.val y.2
          calc (y.1 : G) * (σ₂ : G) = (σ₂ : G) * (y.1 : G) * (σ₂ : G)⁻¹ * (σ₂ : G) := by
                rw [hy]
            _ = (σ₂ : G) * (y.1 : G) := by group⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, by
          apply Subtype.ext
          show (σ₂ : G) * (x.1 : G) * (σ₂ : G)⁻¹ = (x.1 : G)
          have hx := (Subgroup.mem_centralizer_singleton_iff.mp
            (mem_CJ.mp (Subgroup.mem_inf.mp x.2).2).1)
          rw [← hx]
          group⟩
      left_inv := fun y => rfl
      right_inv := fun x => rfl }
  rw [hcard] at hmod
  exact hmod

theorem CJ_inf_CJ_eq_zpowers (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ₁ σ₂ : H z} (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (h8₁ : Nat.card (CJ z (σ₁ : G)) = 8)
    (h8₂ : Nat.card (CJ z (σ₂ : G)) = 8) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) :
    CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) = Subgroup.zpowers z := by
  have hmod := card_CJ_modEq_card_CJ_inf h3₂ hc
  rw [h8₁] at hmod
  set S := CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) with hS
  have hZS : Subgroup.zpowers z ≤ S :=
    Subgroup.zpowers_le_of_mem ⟨z_mem_CJ hcomm σ₁, z_mem_CJ hcomm σ₂⟩
  have hS1 : S ≤ CJ z (σ₁ : G) := inf_le_left
  have hdvd8 : Nat.card S ∣ 8 := h8₁ ▸ Subgroup.card_dvd_of_le hS1
  have hcZ : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_z hJ hcomm]
  have hdvd2 : 2 ∣ Nat.card S := hcZ ▸ Subgroup.card_dvd_of_le hZS
  have hS8 : Nat.card S ≠ 8 := by
    intro h8
    have hEq : S = CJ z (σ₁ : G) := Subgroup.eq_of_le_of_card_ge hS1 (by rw [h8, h8₁])
    have hle : CJ z (σ₁ : G) ≤ CJ z (σ₂ : G) := hEq ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [h8₁, h8₂]))
  have hS2 : Nat.card S = 2 := by
    have hcases : Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 4 ∨ Nat.card S = 8 := by
      have h := Nat.le_of_dvd (by norm_num) hdvd8
      interval_cases (Nat.card S) <;> simp_all
    unfold Nat.ModEq at hmod
    omega
  exact (Subgroup.eq_of_le_of_card_ge hZS (by rw [hS2, hcZ])).symm

theorem mem_centralizerJ_of_conjVA_pi_eq (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ : ↥(H z)} (hσ3 : σ ^ 3 = 1) {j : J z}
    (hfix : conjVA z σ (QuotientV.pi z j) = QuotientV.pi z j) : j ∈ centralizerJ σ := by
  let ζJ : J z := conjJ' z σ j * j⁻¹
  have hζker : ζJ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker]
    change QuotientV.pi z (conjJ' z σ j * j⁻¹) = 1
    rw [map_mul, map_inv, ← conjVA_mk σ j, hfix, mul_inv_cancel]
  rw [QuotientV.pi_ker] at hζker
  let ζ : centerIn (J z) := ⟨(ζJ : G), Subgroup.mem_subgroupOf.mp hζker⟩
  have hζcoe : (ζJ : G) = (ζ : G) := rfl
  have hζzp : (ζ : G) ∈ Subgroup.zpowers z := by
    rw [← centerIn_J_eq_zpowers hJ hcomm]
    exact ζ.2
  have hfixζ : conjJ' z σ ζJ = ζJ := by
    apply Subtype.ext
    change (conjJ' z σ ζJ : G) = (ζ : G)
    rw [conjJ'_apply_coe, hζcoe]
    have hc : (ζ : G) * (σ : G) = (σ : G) * (ζ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (zpowers_le_centralizer σ hζzp)
    rw [← hc]
    group
  have hrel : conjJ' z σ j = ζJ * j := by
    rw [show ζJ = conjJ' z σ j * j⁻¹ from rfl]
    group
  have hpow : ∀ k : ℕ, ((conjJ' z σ : MulAut (J z)) ^ k) j = ζJ ^ k * j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc ((conjJ' z σ : MulAut (J z)) ^ (k + 1)) j
            = (conjJ' z σ) (((conjJ' z σ : MulAut (J z)) ^ k) j) := by
              rw [pow_succ']
              rfl
          _ = (conjJ' z σ) (ζJ ^ k * j) := by rw [ih]
          _ = (conjJ' z σ) (ζJ ^ k) * (conjJ' z σ) j := by rw [map_mul]
          _ = ζJ ^ k * (ζJ * j) := by rw [map_pow, hfixζ, hrel]
          _ = ζJ ^ (k + 1) * j := by group
  have h3 : (conjJ' z σ : MulAut (J z)) ^ 3 = 1 := by
    rw [← map_pow, hσ3, map_one]
  have hj3 : ((conjJ' z σ : MulAut (J z)) ^ 3) j = j := by rw [h3]; rfl
  have hζ3 : ζJ ^ 3 = 1 := by
    have h := hpow 3
    rw [hj3] at h
    exact mul_eq_right.mp h.symm
  have hζ2 : (ζ : G) * (ζ : G) = 1 := mul_self_eq_one_of_mem_zpowers hJ hcomm hζzp
  have hζ3G : (ζ : G) ^ 3 = 1 := by
    have h := congrArg Subtype.val hζ3
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hζeq : (ζ : G) = 1 := by
    rw [pow_three, hζ2, mul_one] at hζ3G
    exact hζ3G
  have hζJ_one : ζJ = 1 := by
    apply Subtype.ext
    exact hζeq
  have hconj : conjJ' z σ j = j := by rw [hrel, hζJ_one, one_mul]
  rw [mem_centralizerJ_iff]
  have hcoe := congrArg (fun y : J z => (y : G)) hconj
  rw [conjJ'_apply_coe] at hcoe
  have hσj : (σ : G) * (j : G) = (j : G) * (σ : G) := by
    calc (σ : G) * (j : G)
        = ((σ : G) * (j : G) * (σ : G)⁻¹) * (σ : G) := by group
      _ = (j : G) * (σ : G) := by rw [hcoe]
  exact hσj.symm

theorem fixSubmodule_inf_eq_bot (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ₁ σ₂ : ↥(H z)} (h3₁ : orderOf σ₁ = 3)
    (h3₂ : orderOf σ₂ = 3) (hCJ : CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) = Subgroup.zpowers z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    fixSubmodule hcomm hJ σ₁ ⊓ fixSubmodule hcomm hJ σ₂ = ⊥ := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [Submodule.mem_bot]
  have hfix1 : conjVA z σ₁ (Additive.toMul v) = Additive.toMul v :=
    mem_autFixedSubgroup.mp ((mem_fixSubmodule_iff hcomm hJ σ₁ v).mp hv.1)
  have hfix2 : conjVA z σ₂ (Additive.toMul v) = Additive.toMul v :=
    mem_autFixedSubgroup.mp ((mem_fixSubmodule_iff hcomm hJ σ₂ v).mp hv.2)
  obtain ⟨j, hj⟩ := QuotientV.pi_surjective z (Additive.toMul v)
  have hvj : v = Additive.ofMul (QuotientV.pi z j) := by
    rw [hj]
    rfl
  have hfix1' : conjVA z σ₁ (QuotientV.pi z j) = QuotientV.pi z j := by
    rw [hj]
    exact hfix1
  have hfix2' : conjVA z σ₂ (QuotientV.pi z j) = QuotientV.pi z j := by
    rw [hj]
    exact hfix2
  have hj1 : j ∈ centralizerJ σ₁ :=
    mem_centralizerJ_of_conjVA_pi_eq hJ hcomm (by rw [← h3₁]; exact pow_orderOf_eq_one σ₁)
      hfix1'
  have hj2 : j ∈ centralizerJ σ₂ :=
    mem_centralizerJ_of_conjVA_pi_eq hJ hcomm (by rw [← h3₂]; exact pow_orderOf_eq_one σ₂)
      hfix2'
  have hamb1 : (j : G) ∈ CJ z (σ₁ : G) :=
    mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (mem_centralizerJ_iff.mp hj1), j.2⟩
  have hamb2 : (j : G) ∈ CJ z (σ₂ : G) :=
    mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (mem_centralizerJ_iff.mp hj2), j.2⟩
  have hjZ : (j : G) ∈ centerIn (J z) := by
    rw [centerIn_J_eq_zpowers hJ hcomm, ← hCJ]
    exact Subgroup.mem_inf.mpr ⟨hamb1, hamb2⟩
  have hker : j ∈ (QuotientV.pi z).ker := by
    rw [QuotientV.pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hjZ
  have hpi : QuotientV.pi z j = 1 := MonoidHom.mem_ker.mp hker
  rw [hvj, hpi]
  rfl

theorem invariants_zpowers_sup_eq_bot (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ₁ σ₂ : ↥(H z)} (h3₁ : orderOf σ₁ = 3)
    (h3₂ : orderOf σ₂ = 3) (hCJ : CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) = Subgroup.zpowers z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    Representation.invariants
        ((conjVRepresentation hcomm hJ).comp
          (Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂).subtype) = ⊥ := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  rw [CFSG.SolvableHall.invariants_comp_subtype_sup]
  rw [invariants_zpowers_eq_fixSubmodule, invariants_zpowers_eq_fixSubmodule,
    fixSubmodule_inf_eq_bot hJ hcomm h3₁ h3₂ hCJ]

end CFSG.RankThree.GF2n.Parrott.Remarks
