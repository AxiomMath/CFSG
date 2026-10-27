module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointTorusAct
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointQuot
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointAux
public import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomPrincipal

import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointModel

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open scoped MatrixGroups

section Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private theorem entry_zRadEquiv_symm_ptc (z : ↥(zRad h)) :
    ((Multiplicative.toAdd ((zRadEquiv h).symm z) : h.fixedField) : K) =
      ((((z : hypSU h 2 0)) : GL Ix K) : Matrix Ix Ix K) ie1 if1 := by
  obtain ⟨c, rfl⟩ := (zRadEquiv h).surjective z
  rw [MulEquiv.symm_apply_apply, coe_zRadEquiv, sMat_ie1_if1]

private theorem entry_conj_zRad_ptc {d z : hypSU h 2 0} (hd : d ∈ u4PtTorus h)
    (hz : z ∈ zRad h) :
    (((d * z * d⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 =
      h.norm (u4PtKappaVal h d) * ((z : GL Ix K) : Matrix Ix Ix K) ie1 if1 := by
  obtain ⟨c, -, hzc⟩ := hz
  rw [coe_conj_sMat_of_mem_u4PtTorus h hd hzc, sMat_ie1_if1, hzc, sMat_ie1_if1]

end Model

section Complement

variable {G : Type} [Group G] {L1 L2 S H₀ : Subgroup G} {f : ℕ}

private theorem conj_mem_centerOf_ptc {Q : Subgroup G} {p z : G}
    (hp : p ∈ Subgroup.normalizer (Q : Set G)) (hz : z ∈ centerOf Q) :
    p * z * p⁻¹ ∈ centerOf Q := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hp z).mp hz.1,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : p⁻¹ * y * p ∈ Q := by
    have e := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hp) y).mp hy
    rwa [inv_inv] at e
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hy'
  calc y * (p * z * p⁻¹) = p * ((p⁻¹ * y * p) * z) * p⁻¹ := by group
    _ = p * (z * (p⁻¹ * y * p)) * p⁻¹ := by rw [hc]
    _ = p * z * p⁻¹ * y := by group

private theorem inf_centralizer_comm_ptc {a b : G}
    (ha : a ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G)) (hb : b ∈ H₀) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm

theorem U4qTorusData.torusCompl_le_centralizer (hT : U4qTorusData L1 L2 S H₀ f) :
    L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀ ≤ Subgroup.centralizer (H₀ : Set G) :=
  sup_le inf_le_right fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => hT.comm a ha b hb

theorem U4qTorusData.torusCompl_le_normalizer (hT : U4qTorusData L1 L2 S H₀ f) :
    L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀ ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
  sup_le (inf_le_left.trans (le_normalizer_pCoreOf 2 L1)) hT.le_normalizer_pCoreOf_left

theorem U4qTorusData.torusCompl_conj_mem_centerOf (hT : U4qTorusData L1 L2 S H₀ f) :
    ∀ r ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀, ∀ z ∈ centerOf (pCoreOf 2 L1),
      r * z * r⁻¹ ∈ centerOf (pCoreOf 2 L1) :=
  fun _ hr _ hz => conj_mem_centerOf_ptc (hT.torusCompl_le_normalizer hr) hz

theorem U4qLocalData.disjoint_pCoreOf_torusCompl [Finite G] (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f) (hH₀ : H₀ ⊓ L1 = ⊥) :
    Disjoint (pCoreOf 2 L1) (L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀) := by
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxQ, hxR⟩
  obtain ⟨k, hk, h₀, hh, rfl⟩ :=
    KProd.exists_mul_of_mem_sup_of_comm (fun a ha b hb => inf_centralizer_comm_ptc ha hb) hxR
  have hh1 : h₀ = 1 := by
    have hL : h₀ ∈ L1 := by
      have e := L1.mul_mem (L1.inv_mem hk.1) (pCoreOf_le 2 L1 hxQ)
      rwa [inv_mul_cancel_left] at e
    have hm : h₀ ∈ H₀ ⊓ L1 := ⟨hh, hL⟩
    rwa [hH₀, Subgroup.mem_bot] at hm
  subst hh1
  rw [mul_one] at hxQ ⊢
  have hm : k ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊓ pCoreOf 2 L1 := ⟨hk, hxQ⟩
  rwa [hD.inf_centralizer_torus_inf_eq_bot hH hS hT hf] at hm

theorem U4qLocalData.pCoreOf_sup_torusCompl [Finite G] (hD : U4qLocalData L1 L2 S f)
    (hT : U4qTorusData L1 L2 S H₀ f) (hsup : L1 ⊔ bigB L1 L2 S = L1 ⊔ H₀) :
    pCoreOf 2 L1 ⊔ (L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀) = L1 ⊔ bigB L1 L2 S := by
  rw [← sup_assoc, hD.sup_inf_centralizer_torus hT, hsup]

theorem U4qCoordLeft.exists_pointComplEquiv [Finite G] {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f)
    (hH₀ : H₀ ⊓ L1 = ⊥) (hU : UnitaryFieldData 2 f K) (ρ : F ≃+* hU.fixedField)
    (κ : ↥H₀ ≃* Kˣ) :
    ∃ e : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀) ≃*
        ↥((levHom hU).range ⊔ u4PtTorus hU),
      ∀ (r : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀)) (k h₀ : G)
        (hk : k ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G)) (hh : h₀ ∈ H₀), (r : G) = k * h₀ →
        (e r : hypSU hU 2 0) =
          levHom hU (Matrix.SpecialLinearGroup.map ρ.toRingHom (c₁.α ⟨k, hk.1⟩)) *
            ((u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩) : hypSU hU 2 0) := by
  have hi : L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊓ H₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hx, -⟩, hxH⟩
    have hm : x ∈ H₀ ⊓ L1 := ⟨hxH, hx⟩
    rwa [hH₀] at hm
  let P := KProd.prodEquivSup _ _ (fun a ha b hb => inf_centralizer_comm_ptc ha hb) hi
  let slρ : SL(2, F) ≃* SL(2, hU.fixedField) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ρ.toRingHom)
      (Matrix.SpecialLinearGroup.map ρ.symm.toRingHom)
      (by ext A i j; simp) (by ext A i j; simp)
  refine ⟨P.symm.trans ((((c₁.torusComplEquiv hH hD hS hT hf).trans slρ).prodCongr κ).trans
    (u4PtLevTorusEquiv hU)), fun r k h₀ hk hh hr => ?_⟩
  have hPr : P.symm r = (⟨k, hk⟩, ⟨h₀, hh⟩) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hr
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hPr]
  rfl

theorem U4qCoordLeft.toAdd_pointPhi_torus [Finite G] {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) {φ : (Fin 2 → F) →+ K}
    (hφA : ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2),
      φ (Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1) = (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    {h₀ : G} (hh : h₀ ∈ H₀) {c : K}
    (hc : ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2) (hha : h₀ * a * h₀⁻¹ ∈ L2),
      (c₂.α ⟨h₀ * a * h₀⁻¹, hha⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
        c * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    (u w : ↥(pCoreOf 2 L1)) (hw : (w : G) = h₀ * u * h₀⁻¹) :
    Multiplicative.toAdd (c₁.pointPhi φ w) = c • Multiplicative.toAdd (c₁.pointPhi φ u) := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨w, hw'⟩ := w
  change w = h₀ * u * h₀⁻¹ at hw
  subst hw
  rw [c₁.toAdd_pointPhi, c₁.toAdd_pointPhi, Prod.smul_mk, smul_eq_mul, smul_eq_mul,
    hD.phi_conj_of_torus hH hS hT c₁ c₂ hφA hh hc u hu hw' 0,
    hD.phi_conj_of_torus hH hS hT c₁ c₂ hφA hh hc u hu hw' 1]

theorem U4qCoordLeft.pointPhi_conj_eq_radPhi [Finite G] {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) (hU : UnitaryFieldData 2 f K) (ρ : F ≃+* hU.fixedField)
    {φ : (Fin 2 → F) →+ K} (hρ : ∀ (τ : F) (v : Fin 2 → F), φ (τ • v) = (ρ τ : K) * φ v)
    (hφA : ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2),
      φ (Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1) = (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    (κ : ↥H₀ ≃* Kˣ)
    (hκ : ∀ (h : ↥H₀) (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2)
        (hha : (h : G) * a * (h : G)⁻¹ ∈ L2),
      (c₂.α ⟨(h : G) * a * (h : G)⁻¹, hha⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
        (κ h : K) * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    {k h₀ : G} (hk : k ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G)) (hh : h₀ ∈ H₀)
    (v w : ↥(pCoreOf 2 L1)) (v' w' : ↥(radQ hU)) (hw : (w : G) = k * h₀ * v * (k * h₀)⁻¹)
    (hw' : (w' : hypSU hU 2 0) =
      levHom hU (Matrix.SpecialLinearGroup.map ρ.toRingHom (c₁.α ⟨k, hk.1⟩)) *
          ((u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩) : hypSU hU 2 0) * v' *
        (levHom hU (Matrix.SpecialLinearGroup.map ρ.toRingHom (c₁.α ⟨k, hk.1⟩)) *
          ((u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩) : hypSU hU 2 0))⁻¹)
    (hvv : c₁.pointPhi φ v = radPhi hU v') : c₁.pointPhi φ w = radPhi hU w' := by
  set A := Matrix.SpecialLinearGroup.map ρ.toRingHom (c₁.α ⟨k, hk.1⟩)
  set d : ↥(u4PtTorus hU) := (u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩) with hd
  have hhu : h₀ * (v : G) * h₀⁻¹ ∈ pCoreOf 2 L1 :=
    (Subgroup.mem_normalizer_iff.mp (hT.le_normalizer_pCoreOf_left hh) v).mp v.2
  let u : ↥(pCoreOf 2 L1) := ⟨h₀ * v * h₀⁻¹, hhu⟩
  have hu := c₁.toAdd_pointPhi_torus c₂ hH hD hS hT hφA hh (hκ ⟨h₀, hh⟩) v u rfl
  have hwk : (w : G) = k * u * k⁻¹ := by
    rw [hw]
    show k * h₀ * v * (k * h₀)⁻¹ = k * (h₀ * v * h₀⁻¹) * k⁻¹
    group
  have hk' := c₁.toAdd_pointPhi_conj (ρ := hU.fixedField.subtype.comp ρ.toRingHom) hρ
    ⟨k, hk.1⟩ u w hwk
  obtain ⟨x, y, c, -, hv'⟩ := v'.2
  rw [radPhi_apply hU hv'] at hvv
  have hdv := coe_conj_sMat_of_mem_u4PtTorus hU d.2 hv'
  have hlev := coe_conj_levHom hU hdv A
  have hw'' : (w' : hypSU hU 2 0) = levHom hU A * ((d : hypSU hU 2 0) * v' *
      (d : hypSU hU 2 0)⁻¹) * (levHom hU A)⁻¹ := by
    rw [hw']
    group
  rw [← hw''] at hlev
  rw [radPhi_apply hU hlev]
  apply Multiplicative.toAdd.injective
  rw [hk', hu, hvv]
  simp only [toAdd_ofAdd, Prod.smul_mk, smul_eq_mul]
  rw [hd, u4PtKappaVal_symm]
  rfl

theorem U4qCoordLeft.crossedHomPrincipal_point [Finite G] {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) (hU : UnitaryFieldData 2 f K)
    {φ : (Fin 2 → F) →+ K} (hφ : Function.Bijective φ)
    (hφA : ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2),
      φ (Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1) = (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    (κ : ↥H₀ ≃* Kˣ)
    (hκ : ∀ (h : ↥H₀) (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2)
        (hha : (h : G) * a * (h : G)⁻¹ ∈ L2),
      (c₂.α ⟨(h : G) * a * (h : G)⁻¹, hha⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
        (κ h : K) * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    (e : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀) ≃*
      ↥((levHom hU).range ⊔ u4PtTorus hU))
    (he : ∀ (n : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀)) (hn : (n : G) ∈ H₀),
      (e n : hypSU hU 2 0) = ((u4PtKappaEquiv hU).symm (κ ⟨n, hn⟩) : hypSU hU 2 0)) :
    CrossedHomPrincipal (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1))
      (L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀) (zRad hU)
      ((levHom hU).range ⊔ u4PtTorus hU) e := by
  classical
  obtain ⟨hR'Q', -, -⟩ := radQ_semidirect_levHom_range_sup_u4PtTorus hU
  have hRQ := hT.torusCompl_le_normalizer
  have hRZ := hT.torusCompl_conj_mem_centerOf
  have hR'Z : ∀ r ∈ (levHom hU).range ⊔ u4PtTorus hU, ∀ z ∈ zRad hU, r * z * r⁻¹ ∈ zRad hU :=
    fun r hr z hz => conj_mem_zRad_of_mem_normalizer hU r (hR'Q' hr) z hz
  have hZc : ∀ a ∈ zRad hU, ∀ b ∈ zRad hU, a * b = b * a :=
    fun a ha b hb => zRad_comm_radQ hU a ha b (zRad_le_radQ hU hb)
  have hodd : Odd (Nat.card H₀) := by
    rw [hT.card]
    have h4 : Even (4 ^ f) :=
      (show Even 4 by norm_num).pow_of_ne_zero (by have := hD.one_le; omega)
    exact Nat.Even.sub_odd (Nat.one_le_pow f 4 (by norm_num)) h4 (by norm_num)
  refine crossedHomPrincipal_of_normal e hRQ hRZ hR'Z hZc le_sup_right (fun r hr n hn => ?_)
    (crossedHomPrincipalOn_of_odd e hRQ hRZ hR'Z hZc (zRad_sq_eq_one hU) le_sup_right hodd) ?_
  ·
    rw [← Subgroup.mem_centralizer_iff.mp (hT.torusCompl_le_centralizer hr) n hn,
      mul_inv_cancel_right]
    exact hn
  intro φ' hφZ hφN
  haveI := hU.charP
  have hker : (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1) ≤ φ'.ker := fun v hv =>
    MonoidHom.mem_ker.mpr (hφZ v (Subgroup.mem_subgroupOf.mp hv))
  let χ : Multiplicative (K × K) →* Multiplicative hU.fixedField :=
    (zRadEquiv hU).symm.toMonoidHom.comp
      ((QuotientGroup.lift _ φ' hker).comp (c₁.pointQuotK hφ).symm.toMonoidHom)
  let ϕ : K × K →+ K :=
    (hU.fixedField.subtype : hU.fixedField →+* K).toAddMonoidHom.comp
      (AddMonoidHom.toMultiplicative.symm χ)
  have hϕ : ∀ u : ↥(pCoreOf 2 L1), ϕ (Multiplicative.toAdd (c₁.pointPhi φ u)) =
      ((((φ' u : ↥(zRad hU)) : hypSU hU 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 := by
    intro u
    have e1 : (c₁.pointQuotK hφ).symm (c₁.pointPhi φ u) = QuotientGroup.mk u := by
      rw [MulEquiv.symm_apply_eq, c₁.pointQuotK_mk]
    rw [← entry_zRadEquiv_symm_ptc hU (φ' u), ← QuotientGroup.lift_mk' _ hker u, ← e1]
    rfl
  have key : ϕ = 0 := by
    obtain ⟨ω, hω⟩ := hU.exists_bar_ne
    refine eq_zero_of_map_smul_eq_norm_mul hU.bar hω ϕ fun c hc w => ?_
    obtain ⟨u, hu⟩ := c₁.pointPhi_surjective hφ (Multiplicative.ofAdd w)
    obtain ⟨n, hn⟩ : ∃ n : ↥H₀, (κ n : K) = c :=
      ⟨κ.symm (Units.mk0 c hc), by rw [MulEquiv.apply_symm_apply, Units.val_mk0]⟩
    have hnu : (n : G) * u * (n : G)⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (hT.le_normalizer_pCoreOf_left n.2) u).mp u.2
    let u' : ↥(pCoreOf 2 L1) := ⟨(n : G) * u * (n : G)⁻¹, hnu⟩
    have h1 := c₁.toAdd_pointPhi_torus c₂ hH hD hS hT hφA n.2 (hκ n) u u' rfl
    rw [hn, hu, toAdd_ofAdd] at h1
    have h2 := hφN ⟨n, Subgroup.mem_sup_right n.2⟩ n.2 u u' rfl
    rw [he _ n.2] at h2
    rw [← h1, hϕ u', h2, entry_conj_zRad_ptc hU ((u4PtKappaEquiv hU).symm _).2 (φ' u).2,
      u4PtKappaVal_symm, ← hϕ u, hu, toAdd_ofAdd]
    change hU.norm ((κ n : Kˣ) : K) * ϕ w = c * hU.bar c * ϕ w
    rw [hn]
    rfl
  refine MonoidHom.ext fun u => Subtype.ext ?_
  have h0 : ((((φ' u : ↥(zRad hU)) : hypSU hU 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 = 0 := by
    rw [← hϕ u, key]
    rfl
  obtain ⟨c, -, hc⟩ := (φ' u).2
  rw [hc, sMat_ie1_if1] at h0
  apply hypSU_ext hU
  rw [hc, h0, sMat_zero_u4]
  rfl

end Complement

end CFSG.Quasithin.F112R.St84

end
