module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Defs
public import CFSG.LocalAnalysis.StandardType.KGLangT3Bridge
public import CFSG.LocalAnalysis.StandardType.KGLangT3ModelDiag
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylOuter
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylStruct
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private lemma l02qj4_conj_injective_of_center_bot {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g h hgh
  have hmem : h⁻¹ * g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut G => φ z) hgh
    simp only [MulAut.conj_apply] at hz
    calc z * (h⁻¹ * g) = h⁻¹ * (h * z * h⁻¹) * g := by group
      _ = h⁻¹ * (g * z * g⁻¹) * g := by rw [← hz]
      _ = (h⁻¹ * g) * z := by group
  have h1 : h⁻¹ * g = 1 := Subgroup.mem_bot.mp (hZ ▸ hmem)
  calc g = h * (h⁻¹ * g) := by group
    _ = h * 1 := by rw [h1]
    _ = h := by rw [mul_one]

private lemma l02qj4_conj_mul_conj {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    MulAut.conj (φ y) = φ * MulAut.conj y * φ⁻¹ := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private lemma l02qj4_conj_cube {G : Type*} [Group G] (β : MulAut G) (hβ3 : β ^ 3 = 1)
    (x : G) : (MulAut.conj x * β) ^ 3 = MulAut.conj (x * β x * β (β x)) := by
  ext y
  simp only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply, map_mul,
    map_inv, mul_assoc]
  have h3y : β (β (β y)) = y := by
    have := congrArg (fun φ : MulAut G => φ y) hβ3
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [h3y]

private lemma l02qj4_alpha_mem_centralizer {n : ℕ} {K : Type} [Field K] {k : Type} [Field k]
    [Algebra k K] (D : TriD4LineKGXData n K k) (y : GGTriD4R n K)
    (hy : y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))) :
    D.α y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc D.α y * D.z₀ = D.α (y * D.z₀) := by rw [map_mul, D.α_z₀]
    _ = D.α (D.z₀ * y) := by rw [hy]
    _ = D.z₀ * D.α y := by rw [map_mul, D.α_z₀]

private lemma l02qj4_alpha_inv_mem_centralizer {n : ℕ} {K : Type} [Field K] {k : Type}
    [Field k] [Algebra k K] (D : TriD4LineKGXData n K k) (y : GGTriD4R n K)
    (hy : y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))) :
    D.α⁻¹ y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  apply D.α.injective
  rw [map_mul, map_mul, D.α_z₀]
  have hαinv : D.α (D.α⁻¹ y) = y := by simp [MulAut.inv_apply]
  rw [hαinv]
  exact hy

private lemma l02qj4_sigma_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) :
    triD4LineSigma k K σ⁻¹ = (triD4LineSigma k K σ)⁻¹ := by
  ext x
  change triD4LineSigma k K σ⁻¹ x = (triD4LineSigma k K σ).symm x
  apply (triD4LineSigma k K σ).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← triD4LineSigma_mul_apply k K σ σ⁻¹ x, mul_inv_cancel, triD4LineSigma_one_apply]

private lemma l02qj4_Theta_alpha_inv {n : ℕ} {K : Type} [Field K] {k : Type} [Field k]
    [Algebra k K] (D : TriD4LineKGXData n K k) (y : GGTriD4R n K)
    (hy : y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))) :
    D.Θ ⟨D.α⁻¹ y, l02qj4_alpha_inv_mem_centralizer D y hy⟩ =
      triD4LineSigma k K D.σ⁻¹ (D.Θ ⟨y, hy⟩) := by
  have hy' : D.α⁻¹ y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) :=
    l02qj4_alpha_inv_mem_centralizer D y hy
  have hαinv : D.α (D.α⁻¹ y) = y := by simp [MulAut.inv_apply]
  have hαy' : D.α (D.α⁻¹ y) ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
    rw [hαinv]; exact hy
  have h1 : D.Θ ⟨D.α (D.α⁻¹ y), hαy'⟩ =
      triD4LineSigma k K D.σ (D.Θ ⟨D.α⁻¹ y, hy'⟩) :=
    D.Θ_α ⟨D.α⁻¹ y, hy'⟩ hαy'
  have hsub : (⟨D.α (D.α⁻¹ y), hαy'⟩ :
      Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))) = ⟨y, hy⟩ :=
    Subtype.ext hαinv
  have h2 : D.Θ ⟨y, hy⟩ =
      triD4LineSigma k K D.σ (D.Θ ⟨D.α⁻¹ y, hy'⟩) := by
    rw [← hsub]
    exact h1
  rw [h2, l02qj4_sigma_inv]
  exact (MulEquiv.symm_apply_apply _ _).symm

private lemma l02qj4_lang_glue
    {n : ℕ} {K : Type} [Field K] {k : Type} [Field k] [Algebra k K] [Finite K]
    (D : TriD4LineKGXData n K k)
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A)
    (hz : MulAut.conj D.z₀ ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (α₀ : MulAut (GGTriD4R n K)) (hα₀A : α₀ ∈ A)
    (J₀ : Subgroup (GGTriD4R n K))
    (hJle : J₀ ≤ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))
    (hEJ : triD4LineE n K A ≤ J₀)
    (hcomp : ∀ (y : GGTriD4R n K)
        (hy : y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))),
        y ∈ J₀ ↔ (D.Θ ⟨y, hy⟩ : TriD4LineX k K) ∈ triD4LineN0 k K)
    (hdeg : Module.finrank k K = 3) (h3 : 3 ∣ Nat.card k - 1)
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (xR : GGTriD4R n K)
    (hxX₀ : xR ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))
    (β : MulAut (GGTriD4R n K)) (hβ3 : β ^ 3 = 1)
    (hβc : ∀ y : GGTriD4R n K,
        y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) →
        β y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))
    (σ' : K ≃ₐ[k] K) (hσ' : orderOf σ' = 3)
    (hβσ : ∀ y : ↥(Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))),
        D.Θ ⟨β y.val, hβc y.val y.2⟩ = triD4LineSigma k K σ' (D.Θ y))
    (hfx : α₀ = MulAut.conj xR * β) :
    ∃ k : GGTriD4R n K,
      (∀ α ∈ A, α ∈ kgLangT3Inn n K → α k = k) ∧ k * (α₀ k)⁻¹ = D.z₀ := by
  set X₀ : Subgroup (GGTriD4R n K) :=
    Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) with hX₀
  set EA : Subgroup (GGTriD4R n K) := triD4LineE n K A with hEA
  have hxX : xR ∈ X₀ := hxX₀
  have hEAmem : ∀ e : GGTriD4R n K, e ∈ EA ↔ MulAut.conj e ∈ A := by
    intro e; rw [hEA]; exact mem_triD4LineE
  have hEAea : IsElemAbelian 3 EA := by
    rw [hEA]; exact triD4Line_E_isElemAbelian K hZ A hA
  have hEAle : EA ≤ X₀ := by
    rw [hX₀, hEA]; exact le_trans hEJ hJle
  have hEAcard : Nat.card EA ≤ 9 := by
    have := CFSG.LocalAnalysis.GLTheoremA.triD4_m3_le hn K hK EA hEAea
    simpa using this
  have hzX₀ : D.z₀ ∈ X₀ := by
    rw [hX₀, Subgroup.mem_centralizer_singleton_iff]
  let zX : TriD4LineX k K := D.Θ ⟨D.z₀, hzX₀⟩
  let E : Subgroup (TriD4LineX k K) := (EA.subgroupOf X₀).map D.Θ.toMonoidHom
  haveI hEAab_sub : IsMulCommutative ↥(EA.subgroupOf X₀) := by
    haveI : IsMulCommutative ↥EA := hEAea.1
    refine IsMulCommutative.mk ⟨fun a b => Subtype.ext ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using
      Subgroup.mul_comm_of_mem_isMulCommutative EA (Subgroup.mem_subgroupOf.mp a.2)
        (Subgroup.mem_subgroupOf.mp b.2)
  have hEea : IsElemAbelian 3 E := by
    constructor
    · refine IsMulCommutative.mk ⟨fun u v => ?_⟩
      apply Subtype.ext
      change (u : TriD4LineX k K) * (v : TriD4LineX k K) =
        (v : TriD4LineX k K) * (u : TriD4LineX k K)
      obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
      obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      exact congrArg D.Θ
        (Subgroup.mul_comm_of_mem_isMulCommutative (EA.subgroupOf X₀) hu' hv')
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hy3 : y ^ 3 = 1 :=
        Subtype.ext (hEAea.2 y.val (Subgroup.mem_subgroupOf.mp hy))
      have := congrArg D.Θ hy3
      simpa [map_pow] using this
  have hEcard : Nat.card E ≤ 9 := by
    rw [show E = (EA.subgroupOf X₀).map D.Θ.toMonoidHom from rfl,
      Subgroup.card_map_of_injective D.Θ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEAle).toEquiv]
    exact hEAcard
  have hzX3 : orderOf zX = 3 := by
    rw [show zX = D.Θ ⟨D.z₀, hzX₀⟩ from rfl, MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe (⟨D.z₀, hzX₀⟩ : X₀)).symm.trans D.orderOf_z₀
  have hzXc : zX ∈ Subgroup.center (TriD4LineX k K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := D.Θ.surjective y
    have hcenter : (⟨D.z₀, hzX₀⟩ : X₀) ∈ Subgroup.center X₀ := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp u.2
    have := Subgroup.mem_center_iff.mp hcenter w
    simpa [zX] using congrArg D.Θ this
  have hzEA : D.z₀ ∈ EA := (hEAmem D.z₀).mpr hz
  have hzE : zX ∈ E := by
    refine Subgroup.mem_map.mpr ⟨⟨D.z₀, hzX₀⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hzEA
  have hEN : E ≤ triD4LineN0 k K := by
    intro e' he'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp he'
    have haEA : a.val ∈ EA := Subgroup.mem_subgroupOf.mp ha
    have haJ : a.val ∈ J₀ := hEJ (hEA ▸ haEA)
    exact (hcomp a.val a.2).mp haJ
  let xX : TriD4LineX k K := D.Θ ⟨xR, hxX⟩
  have hα₀X₀ : ∀ y : X₀, α₀ y.val ∈ X₀ := by
    intro y
    have hβy : β y.val ∈ X₀ := hβc y.val y.2
    rw [hfx, MulAut.mul_apply, MulAut.conj_apply]
    exact X₀.mul_mem (X₀.mul_mem hxX hβy) (X₀.inv_mem hxX)
  have hact : ∀ y : X₀, D.Θ ⟨α₀ y.val, hα₀X₀ y⟩ =
      xX * triD4LineSigma k K σ' (D.Θ y) * xX⁻¹ := by
    intro y
    have hval : α₀ y.val = xR * β y.val * xR⁻¹ := by
      rw [hfx, MulAut.mul_apply, MulAut.conj_apply]
    have hsub : (⟨α₀ y.val, hα₀X₀ y⟩ : X₀) =
        ⟨xR, hxX⟩ * ⟨β y.val, hβc y.val y.2⟩ * ⟨xR, hxX⟩⁻¹ := Subtype.ext hval
    rw [hsub, map_mul, map_mul, map_inv, hβσ y]
  have hfixEA : ∀ e ∈ EA, α₀ e = e := by
    intro e he
    have hce : MulAut.conj e ∈ A := (hEAmem e).mp he
    have hcomm' : α₀ * MulAut.conj e = MulAut.conj e * α₀ := hcomm α₀ hα₀A _ hce
    apply l02qj4_conj_injective_of_center_bot hZ
    calc MulAut.conj (α₀ e) = α₀ * MulAut.conj e * α₀⁻¹ := l02qj4_conj_mul_conj α₀ e
      _ = MulAut.conj e * α₀ * α₀⁻¹ := by rw [hcomm']
      _ = MulAut.conj e := by group
  have hx : ∀ e ∈ E, xX * triD4LineSigma k K σ' e * xX⁻¹ = e := by
    intro e he
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp he
    have haEA : a.val ∈ EA := Subgroup.mem_subgroupOf.mp ha
    have hfix : α₀ a.val = a.val := hfixEA a.val haEA
    rw [← hae]
    calc xX * triD4LineSigma k K σ' (D.Θ a) * xX⁻¹
        = D.Θ ⟨α₀ a.val, hα₀X₀ a⟩ := (hact a).symm
      _ = D.Θ a := by
        rw [show (⟨α₀ a.val, hα₀X₀ a⟩ : X₀) = a from Subtype.ext hfix]
  have hx3 : xX * triD4LineSigma k K σ' xX * triD4LineSigma k K (σ' ^ 2) xX = 1 := by
    have hcube : (MulAut.conj xR * β) ^ 3 = 1 := by rw [← hfx]; exact hA.2 α₀ hα₀A
    have h3R : xR * β xR * β (β xR) = 1 := by
      apply l02qj4_conj_injective_of_center_bot hZ
      rw [← l02qj4_conj_cube β hβ3 xR, hcube, map_one]
    have hmem : xR * β xR * β (β xR) ∈ X₀ :=
      X₀.mul_mem (X₀.mul_mem hxX (hβc xR hxX)) (hβc (β xR) (hβc xR hxX))
    have h1 : D.Θ ⟨xR * β xR * β (β xR), hmem⟩ = 1 := by
      rw [show (⟨xR * β xR * β (β xR), hmem⟩ : X₀) = ⟨1, X₀.one_mem⟩ from
        Subtype.ext h3R]
      exact map_one D.Θ
    have h2 : D.Θ ⟨xR * β xR * β (β xR), hmem⟩ =
        xX * triD4LineSigma k K σ' xX * triD4LineSigma k K (σ' ^ 2) xX := by
      have hsub : (⟨xR * β xR * β (β xR), hmem⟩ : X₀) =
          ⟨xR, hxX⟩ * ⟨β xR, hβc xR hxX⟩ *
            ⟨β (β xR), hβc (β xR) (hβc xR hxX)⟩ := Subtype.ext rfl
      rw [hsub, map_mul, map_mul, hβσ ⟨xR, hxX⟩, hβσ ⟨β xR, hβc xR hxX⟩]
      rw [hβσ ⟨xR, hxX⟩]
      rw [pow_two, triD4LineSigma_mul_apply]
    rw [← h2]
    exact h1
  obtain ⟨y, hycomm, hylang⟩ :=
    kgLangT3_model_lang k K hdeg h3 σ' hσ' zX hzX3 hzXc E hEea hEcard hEN hzE xX hx hx3
  let kR : X₀ := D.Θ.symm y
  have hkR : D.Θ kR = y := MulEquiv.apply_symm_apply D.Θ y
  refine ⟨kR.val, ?_, ?_⟩
  · intro α hαA hαinn
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hαinn
    have heA : MulAut.conj e ∈ A := by rw [he]; exact hαA
    have heEA : e ∈ triD4LineE n K A := mem_triD4LineE.mpr heA
    have heEA' : e ∈ EA := hEA.symm ▸ heEA
    have heX₀ : e ∈ X₀ := hEAle heEA'
    have heX : (D.Θ ⟨e, heX₀⟩ : TriD4LineX k K) ∈ E := by
      refine Subgroup.mem_map.mpr ⟨⟨e, heX₀⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact heEA'
    have hcomm_eX : D.Θ ⟨e, heX₀⟩ * y = y * D.Θ ⟨e, heX₀⟩ := (hycomm _ heX).symm
    have hαk : α kR.val = e * kR.val * e⁻¹ := by
      rw [← he, MulAut.conj_apply]
    have hmem1 : e * kR.val * e⁻¹ ∈ X₀ :=
      X₀.mul_mem (X₀.mul_mem heX₀ kR.2) (X₀.inv_mem heX₀)
    have hsub : (⟨e * kR.val * e⁻¹, hmem1⟩ : X₀) =
        ⟨e, heX₀⟩ * kR * ⟨e, heX₀⟩⁻¹ := Subtype.ext rfl
    have hΘ : D.Θ ⟨e * kR.val * e⁻¹, hmem1⟩ = D.Θ kR := by
      rw [hsub, map_mul, map_mul, map_inv, hkR]
      rw [hcomm_eX]
      group
    have heq : e * kR.val * e⁻¹ = kR.val :=
      congrArg Subtype.val (D.Θ.injective hΘ)
    rw [hαk, heq]
  · have hα₀k_mem : α₀ kR.val ∈ X₀ := hα₀X₀ kR
    have hmem2 : kR.val * (α₀ kR.val)⁻¹ ∈ X₀ :=
      X₀.mul_mem kR.2 (X₀.inv_mem hα₀k_mem)
    have hsub2 : (⟨kR.val * (α₀ kR.val)⁻¹, hmem2⟩ : X₀) =
        kR * ⟨α₀ kR.val, hα₀k_mem⟩⁻¹ := Subtype.ext rfl
    have hΘ2 : D.Θ ⟨kR.val * (α₀ kR.val)⁻¹, hmem2⟩ = D.Θ ⟨D.z₀, hzX₀⟩ := by
      rw [hsub2, map_mul, map_inv]
      rw [show D.Θ ⟨α₀ kR.val, hα₀k_mem⟩ =
          xX * triD4LineSigma k K σ' y * xX⁻¹ from by
        rw [← hkR]; exact hact kR]
      rw [hkR]
      exact hylang
    exact congrArg Subtype.val (D.Θ.injective hΘ2)

theorem kgLangT3_core_z0 {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n)
    (D : TriD4LineKGXData n K k)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A)
    (hz : MulAut.conj D.z₀ ∈ A) (α₀ : MulAut (GGTriD4R n K)) (hα₀A : α₀ ∈ A)
    (hα₀o : α₀ ∉ kgLangT3Inn n K) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) :
    triD4LineE n K A ≤ J₀ →
      ∃ k : GGTriD4R n K, (∀ α ∈ A, α ∈ kgLangT3Inn n K → α k = k) ∧ k * (α₀ k)⁻¹ = D.z₀ := by
  intro hEJ
  have hn1 : 1 ≤ n := by omega
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype K := Fintype.ofFinite K
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn1 K hK
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    haveI := hA.1
    intro a ha b hb
    exact Subgroup.mul_comm_of_mem_isMulCommutative A ha hb
  have hdeg : Module.finrank k K = 3 := by
    have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK] at hcard
    have h2n : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
    exact (Nat.pow_right_injective h2n hcard).symm
  have h3 : 3 ∣ Nat.card k - 1 := by
    rw [hk]
    obtain ⟨m, rfl⟩ := hev
    have h4 : 3 ∣ 4 ^ m - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 m
    have e : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
    rw [e]; exact h4
  have hα₀3 : α₀ ^ 3 = 1 := hA.2 α₀ hα₀A
  obtain ⟨xR, hxX₀, hcase⟩ :=
    triD4Line_outer_form hn1 K hK k D A hcomm hz α₀ hα₀A hα₀o hα₀3
  have hcomp := kgLangT3_component_eq K k D J₀ hJ
  rcases hcase with hfx | hfx
  · refine l02qj4_lang_glue D hZ A hA hz hcomm α₀ hα₀A J₀ hJ.1 hEJ hcomp hdeg h3 hn1 hK
      xR hxX₀ D.α (by simpa [D.orderOf_α] using pow_orderOf_eq_one D.α)
      (fun y hy => l02qj4_alpha_mem_centralizer D y hy) D.σ D.orderOf_σ
      (fun y => D.Θ_α y (l02qj4_alpha_mem_centralizer D y.val y.2)) hfx
  · have hα3 : D.α ^ 3 = 1 := by simpa [D.orderOf_α] using pow_orderOf_eq_one D.α
    refine l02qj4_lang_glue D hZ A hA hz hcomm α₀ hα₀A J₀ hJ.1 hEJ hcomp hdeg h3 hn1 hK
      xR hxX₀ D.α⁻¹ (by rw [inv_pow, hα3, inv_one])
      (fun y hy => l02qj4_alpha_inv_mem_centralizer D y hy) D.σ⁻¹
      (by rw [orderOf_inv]; exact D.orderOf_σ)
      (fun y => l02qj4_Theta_alpha_inv D y.val y.2) hfx

end CFSG.StandardType
