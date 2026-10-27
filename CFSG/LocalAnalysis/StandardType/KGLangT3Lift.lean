module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Defs
public import CFSG.LocalAnalysis.StandardType.KGLangT3Bridge
public import CFSG.LocalAnalysis.StandardType.KGLangT3Comm
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylOuter
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylStruct
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTransfer
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

private lemma l02qj7b_conj_injective {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have h : ∀ z, x * z * x⁻¹ = y * z * y⁻¹ := fun z => by
    have := congrArg (fun e : MulAut G => e z) hxy
    simpa [MulAut.conj_apply] using this
  have hcomm : ∀ z, z * (y⁻¹ * x) = (y⁻¹ * x) * z := by
    intro z
    have hz := h z
    calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
      _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [← hz]
      _ = (y⁻¹ * x) * z := by group
  have hmem : y⁻¹ * x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    exact hcomm
  have h1 : y⁻¹ * x = 1 := by
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [h1, mul_one]

private lemma l02qj7b_conj_mul_conj {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    MulAut.conj (φ y) = φ * MulAut.conj y * φ⁻¹ := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private theorem l02qj7b_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (h : LargeEvenSLGroup (Fin d) K) :
    TypeA.slKerEquiv d K (MulAut.conjNormal A h) =
      slConjugation d K A (TypeA.slKerEquiv d K h) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hc : ∀ h : LargeEvenSLGroup (Fin d) K,
      Matrix.SpecialLinearGroup.toGL (TypeA.slKerEquiv d K h) = (h : GL (Fin d) K) :=
    fun h => Units.ext (TypeA.coe_slKerEquiv h)
  rw [toGL_slConjugation, hc, hc, MulAut.conjNormal_apply]

private theorem l02qj7b_recipeEquiv_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (x : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    TypeA.recipeEquiv d K (TableB.linConjAut (Fin d) K A x) =
      LinearFlag.conjAut d K A (TypeA.recipeEquiv d K x) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [TableB.linConjAut_mk]
  rw [show (TypeA.recipeEquiv d K) (↑(MulAut.conjNormal A h)) =
      LinearFlag.proj d K (TypeA.slKerEquiv d K (MulAut.conjNormal A h))
    from TypeA.recipeEquiv_mk (MulAut.conjNormal A h)]
  rw [show (TypeA.recipeEquiv d K) (↑h) = LinearFlag.proj d K (TypeA.slKerEquiv d K h)
    from TypeA.recipeEquiv_mk h]
  rw [LinearFlag.conjAut_proj, l02qj7b_slKerEquiv_conjNormal]

private theorem l02qj7b_commute_transfer {F₀ E : Type} [Field F₀] [Finite F₀] [Field E]
    [Finite E] (hcard : Nat.card E = Nat.card F₀)
    (ψ : LargeEvenProj (LargeEvenSLGroup (Fin 3) F₀) ≃*
         LargeEvenProj (LargeEvenSLGroup (Fin 3) E))
    {M N : GL (Fin 3) F₀} {g h : GL (Fin 3) E}
    (hM : ∀ x, ψ (TableB.linConjAut (Fin 3) F₀ M x) = TableB.linConjAut (Fin 3) E g (ψ x))
    (hN : ∀ x, ψ (TableB.linConjAut (Fin 3) F₀ N x) = TableB.linConjAut (Fin 3) E h (ψ x))
    (hgh : g * h = h * g) : M * N = N * M := by
  let τF : LargeEvenProj (LargeEvenSLGroup (Fin 3) F₀) ≃* LinearFlag.projectiveSL 3 F₀ :=
    TypeA.recipeEquiv 3 F₀
  let τE : LargeEvenProj (LargeEvenSLGroup (Fin 3) E) ≃* LinearFlag.projectiveSL 3 E :=
    TypeA.recipeEquiv 3 E
  let ψ' : LinearFlag.projectiveSL 3 F₀ ≃* LinearFlag.projectiveSL 3 E :=
    τF.symm.trans (ψ.trans τE)
  have hM' : ∀ x, ψ' (LinearFlag.conjAut 3 F₀ M x) = LinearFlag.conjAut 3 E g (ψ' x) := by
    intro x
    have h1 : τF.symm (LinearFlag.conjAut 3 F₀ M x) =
        TableB.linConjAut (Fin 3) F₀ M (τF.symm x) := by
      apply τF.injective
      rw [MulEquiv.apply_symm_apply, l02qj7b_recipeEquiv_linConjAut, MulEquiv.apply_symm_apply]
    change τE (ψ (τF.symm (LinearFlag.conjAut 3 F₀ M x))) =
      LinearFlag.conjAut 3 E g (τE (ψ (τF.symm x)))
    rw [h1, hM, l02qj7b_recipeEquiv_linConjAut]
  have hN' : ∀ x, ψ' (LinearFlag.conjAut 3 F₀ N x) = LinearFlag.conjAut 3 E h (ψ' x) := by
    intro x
    have h1 : τF.symm (LinearFlag.conjAut 3 F₀ N x) =
        TableB.linConjAut (Fin 3) F₀ N (τF.symm x) := by
      apply τF.injective
      rw [MulEquiv.apply_symm_apply, l02qj7b_recipeEquiv_linConjAut, MulEquiv.apply_symm_apply]
    change τE (ψ (τF.symm (LinearFlag.conjAut 3 F₀ N x))) =
      LinearFlag.conjAut 3 E h (τE (ψ (τF.symm x)))
    rw [h1, hN, l02qj7b_recipeEquiv_linConjAut]
  exact kgLangS1A_commute_transfer (d := 3) (by norm_num) hcard ψ' hM' hN' hgh

theorem kgLangT3_E_le_component {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n)
    (D : TriD4LineKGXData n K k)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A)
    (hz : MulAut.conj D.z₀ ∈ A) (α₀ : MulAut (GGTriD4R n K)) (hα₀A : α₀ ∈ A)
    (hα₀o : α₀ ∉ kgLangT3Inn n K) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))))
    (E : Type) [Field E] [Finite E]
    (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E))
    (hAt : ∃ At : Subgroup (GL (Fin 3) E), IsMulCommutative At ∧
      ∀ α ∈ A, ∃ g ∈ At, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : GGTriD4R n K) = α j ∧
        θ₀ (QuotientGroup.mk j') = TableB.linConjAut (Fin 3) E g (θ₀ (QuotientGroup.mk j))) :
    triD4LineE n K A ≤ J₀ := by
  intro e₁ he₁
  have hn1 : 1 ≤ n := by omega
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype K := Fintype.ofFinite K
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn1 K hK
  have hdeg : Module.finrank k K = 3 := by
    have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK] at hcard
    have h2n : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
    exact (Nat.pow_right_injective h2n hcard).symm
  have hocomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    haveI := hA.1
    exact Subgroup.mul_comm_of_mem_isMulCommutative A ha hb
  have hEA : IsElemAbelian 3 (triD4LineE n K A) := triD4Line_E_isElemAbelian K hZ A hA
  have hzEA : D.z₀ ∈ triD4LineE n K A := mem_triD4LineE.mpr hz
  have he₁C : e₁ ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    haveI := hEA.1
    exact Subgroup.mul_comm_of_mem_isMulCommutative (triD4LineE n K A) he₁ hzEA
  have he₁comm : e₁ * D.z₀ = D.z₀ * e₁ := Subgroup.mem_centralizer_singleton_iff.mp he₁C
  by_contra hnotJ
  let y₁ : TriD4LineX k K := D.Θ ⟨e₁, he₁C⟩
  have hynot : y₁ ∉ triD4LineN0 k K := by
    intro hy
    exact hnotJ ((kgLangT3_component_eq K k D J₀ hJ e₁ he₁C).mpr hy)
  obtain ⟨g₁, c₁, h₁, hy₁⟩ := triD4LineMk_surjective k K y₁
  have hc₁ : ¬ ∃ μ : kˣ, c₁ = Units.map (algebraMap k K).toMonoidHom μ := by
    intro hμ
    exact hynot (by rw [← hy₁]; exact (triD4LineMk_mem_N0_iff k K hdeg g₁ c₁ h₁).mpr hμ)
  have hα₀o' : α₀ ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) := by
    simpa only [kgLangT3Inn, MonoidHom.mem_range, Set.mem_range] using hα₀o
  have hα₀3 : α₀ ^ 3 = 1 := hA.2 α₀ hα₀A
  obtain ⟨x₀, hx₀C, houter⟩ :=
    triD4Line_outer_form hn1 K hK k D A hocomm hz α₀ hα₀A hα₀o' hα₀3
  have houter' := houter
  let x : TriD4LineX k K := D.Θ ⟨x₀, hx₀C⟩
  obtain ⟨gx, cx, hx, hx_eq⟩ := triD4LineMk_surjective k K x
  have hα₀e₁ : α₀ e₁ = e₁ := by
    apply l02qj7b_conj_injective hZ
    have hcommA : α₀ * MulAut.conj e₁ = MulAut.conj e₁ * α₀ :=
      hocomm α₀ hα₀A (MulAut.conj e₁) (mem_triD4LineE.mp he₁)
    rw [l02qj7b_conj_mul_conj α₀ e₁, hcommA, mul_assoc, mul_inv_cancel, mul_one]
  have hα₀J : ∀ j : ↥J₀, (α₀ j : GGTriD4R n K) = x₀ * (j : GGTriD4R n K) * x₀⁻¹ := by
    intro j
    rcases houter' with hout | hout
    · rw [hout]
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      rw [kgLangT3_alpha_fix_component K k D J₀ hJ j j.2]
    · rw [hout]
      have hfixα : D.α⁻¹ (j : GGTriD4R n K) = (j : GGTriD4R n K) :=
        D.α.injective (by
          have h := kgLangT3_alpha_fix_component K k D J₀ hJ j j.2
          simp [MulAut.inv_apply, h])
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      rw [hfixα]
  obtain ⟨At, hAtcomm, hAtprop⟩ := hAt
  obtain ⟨g_e, hg_e_mem, hg_e_prop⟩ := hAtprop (MulAut.conj e₁) (mem_triD4LineE.mp he₁)
  obtain ⟨g', hg'_mem, hg'_prop⟩ := hAtprop α₀ hα₀A
  obtain ⟨ι, hι⟩ := kgLangT3_component_equiv (n := n) K k D J₀ hJ
  let ψ : LargeEvenProj (LargeEvenSLGroup (Fin 3) k) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 3) E) := ι.symm.trans θ₀
  have hψι : ∀ z : ↥J₀ ⧸ Subgroup.center ↥J₀, ψ (ι z) = θ₀ z := by
    intro z
    simp only [ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hM : ∀ p, ψ (TableB.linConjAut (Fin 3) k g₁ p) =
      TableB.linConjAut (Fin 3) E g_e (ψ p) := by
    intro p
    obtain ⟨q, rfl⟩ := ι.surjective p
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j', hj'spec, hj'θ⟩ := hg_e_prop j
    have hιj' : ι (QuotientGroup.mk j') =
        TableB.linConjAut (Fin 3) k g₁ (ι (QuotientGroup.mk j)) :=
      hι e₁ he₁C g₁ c₁ h₁ hy₁.symm j j' (by simpa [MulAut.conj_apply] using hj'spec)
    calc ψ (TableB.linConjAut (Fin 3) k g₁ (ι (QuotientGroup.mk j)))
        = ψ (ι (QuotientGroup.mk j')) := by rw [← hιj']
      _ = θ₀ (QuotientGroup.mk j') := hψι (QuotientGroup.mk j')
      _ = TableB.linConjAut (Fin 3) E g_e (θ₀ (QuotientGroup.mk j)) := hj'θ
      _ = TableB.linConjAut (Fin 3) E g_e (ψ (ι (QuotientGroup.mk j))) := by
            rw [hψι (QuotientGroup.mk j)]
  have hN : ∀ p, ψ (TableB.linConjAut (Fin 3) k gx p) =
      TableB.linConjAut (Fin 3) E g' (ψ p) := by
    intro p
    obtain ⟨q, rfl⟩ := ι.surjective p
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j', hj'spec, hj'θ⟩ := hg'_prop j
    have hrel : (j' : GGTriD4R n K) = x₀ * (j : GGTriD4R n K) * x₀⁻¹ := by
      rw [hj'spec, hα₀J j]
    have hιj' : ι (QuotientGroup.mk j') =
        TableB.linConjAut (Fin 3) k gx (ι (QuotientGroup.mk j)) :=
      hι x₀ hx₀C gx cx hx hx_eq.symm j j' hrel
    calc ψ (TableB.linConjAut (Fin 3) k gx (ι (QuotientGroup.mk j)))
        = ψ (ι (QuotientGroup.mk j')) := by rw [← hιj']
      _ = θ₀ (QuotientGroup.mk j') := hψι (QuotientGroup.mk j')
      _ = TableB.linConjAut (Fin 3) E g' (θ₀ (QuotientGroup.mk j)) := hj'θ
      _ = TableB.linConjAut (Fin 3) E g' (ψ (ι (QuotientGroup.mk j))) := by
            rw [hψι (QuotientGroup.mk j)]
  have hcard : Nat.card E = Nat.card k := by
    have htd := kgLangS1A_psl_typeDet (d := 3) (d₁ := 3) (m := n) (F₀ := k) (E := E)
      (by norm_num) hn (by rw [hk]) ((TypeA.recipeEquiv 3 k).symm.trans ψ)
    exact htd.2
  have hgeg' : g_e * g' = g' * g_e := by
    haveI := hAtcomm
    exact Subgroup.mul_comm_of_mem_isMulCommutative At hg_e_mem hg'_mem
  have hcomm_transfer : g₁ * gx = gx * g₁ :=
    l02qj7b_commute_transfer hcard ψ hM hN hgeg'
  rcases houter with hout | hout
  ·
    have hDαe₁C : D.α e₁ ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc D.α e₁ * D.z₀ = D.α e₁ * D.α D.z₀ := by conv_lhs => rw [← D.α_z₀]
        _ = D.α (e₁ * D.z₀) := by rw [← map_mul]
        _ = D.α (D.z₀ * e₁) := by rw [he₁comm]
        _ = D.α D.z₀ * D.α e₁ := by rw [map_mul]
        _ = D.z₀ * D.α e₁ := by rw [D.α_z₀]
    have hα₀e₁' : MulAut.conj x₀ (D.α e₁) = e₁ := by
      have h : (MulAut.conj x₀ * D.α) e₁ = e₁ := by rw [← hout]; exact hα₀e₁
      simpa [MulAut.mul_apply] using h
    have hsub : (⟨x₀, hx₀C⟩ : ↥(Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) *
        ⟨D.α e₁, hDαe₁C⟩ *
        (⟨x₀, hx₀C⟩ : ↥(Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))))⁻¹ =
        ⟨e₁, he₁C⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [MulAut.conj_apply] at hα₀e₁'
      exact hα₀e₁'
    have hfixpre : D.Θ ⟨x₀, hx₀C⟩ * D.Θ ⟨D.α e₁, hDαe₁C⟩ * (D.Θ ⟨x₀, hx₀C⟩)⁻¹ =
        D.Θ ⟨e₁, he₁C⟩ := by
      simpa only [map_mul, map_inv] using congrArg D.Θ hsub
    have hΘα : D.Θ ⟨D.α e₁, hDαe₁C⟩ = triD4LineSigma k K D.σ y₁ :=
      D.Θ_α ⟨e₁, he₁C⟩ hDαe₁C
    have hfix' : x * triD4LineSigma k K D.σ y₁ * x⁻¹ = y₁ := by
      have := hfixpre
      rw [hΘα] at this
      exact this
    have hfix_model : triD4LineMk k K gx cx hx *
        triD4LineSigma k K D.σ (triD4LineMk k K g₁ c₁ h₁) *
        (triD4LineMk k K gx cx hx)⁻¹ = triD4LineMk k K g₁ c₁ h₁ := by
      rw [hx_eq, hy₁]
      exact hfix'
    exact (kgLangT3_model_comm_ne_one k K hdeg D.σ D.orderOf_σ g₁ gx c₁ cx h₁ hx hc₁
      hfix_model) hcomm_transfer.symm
  ·
    have hz' : D.α⁻¹ D.z₀ = D.z₀ := by
      conv_lhs => rw [← D.α_z₀]
      exact MulAut.inv_apply_self (GGTriD4R n K) D.α D.z₀
    have hDαinv_e₁C : D.α⁻¹ e₁ ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc D.α⁻¹ e₁ * D.z₀ = D.α⁻¹ e₁ * D.α⁻¹ D.z₀ := by conv_lhs => rw [← hz']
        _ = D.α⁻¹ (e₁ * D.z₀) := by rw [← map_mul]
        _ = D.α⁻¹ (D.z₀ * e₁) := by rw [he₁comm]
        _ = D.α⁻¹ D.z₀ * D.α⁻¹ e₁ := by rw [map_mul]
        _ = D.z₀ * D.α⁻¹ e₁ := by rw [hz']
    have hα₀e₁' : MulAut.conj x₀ (D.α⁻¹ e₁) = e₁ := by
      have h : (MulAut.conj x₀ * D.α⁻¹) e₁ = e₁ := by rw [← hout]; exact hα₀e₁
      simpa [MulAut.mul_apply] using h
    have hsub : (⟨x₀, hx₀C⟩ : ↥(Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) *
        ⟨D.α⁻¹ e₁, hDαinv_e₁C⟩ *
        (⟨x₀, hx₀C⟩ : ↥(Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))))⁻¹ =
        ⟨e₁, he₁C⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [MulAut.conj_apply] at hα₀e₁'
      exact hα₀e₁'
    have hfixpre : D.Θ ⟨x₀, hx₀C⟩ * D.Θ ⟨D.α⁻¹ e₁, hDαinv_e₁C⟩ * (D.Θ ⟨x₀, hx₀C⟩)⁻¹ =
        D.Θ ⟨e₁, he₁C⟩ := by
      simpa only [map_mul, map_inv] using congrArg D.Θ hsub
    have hmemDα : D.α (D.α⁻¹ e₁) ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
      have hval : D.α (D.α⁻¹ e₁) = e₁ := by
        rw [MulAut.inv_apply]
        exact MulEquiv.apply_symm_apply D.α e₁
      rw [hval]
      exact he₁C
    have hΘα : D.Θ ⟨D.α (D.α⁻¹ e₁), hmemDα⟩ =
        triD4LineSigma k K D.σ (D.Θ ⟨D.α⁻¹ e₁, hDαinv_e₁C⟩) :=
      D.Θ_α ⟨D.α⁻¹ e₁, hDαinv_e₁C⟩ hmemDα
    have hσz : triD4LineSigma k K D.σ (D.Θ ⟨D.α⁻¹ e₁, hDαinv_e₁C⟩) = y₁ := by
      have hL : D.Θ ⟨D.α (D.α⁻¹ e₁), hmemDα⟩ = y₁ := by
        have hval : D.α (D.α⁻¹ e₁) = e₁ := by
          rw [MulAut.inv_apply]
          exact MulEquiv.apply_symm_apply D.α e₁
        have hsub_eq : (⟨D.α (D.α⁻¹ e₁), hmemDα⟩ :
            ↥(Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) = ⟨e₁, he₁C⟩ :=
          Subtype.ext hval
        rw [hsub_eq]
      exact hΘα.symm.trans hL
    have hσinv : triD4LineSigma k K D.σ⁻¹ = (triD4LineSigma k K D.σ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      apply MulEquiv.ext
      intro y
      simp only [MulAut.mul_apply, MulAut.one_apply, ← triD4LineSigma_mul_apply, mul_inv_cancel,
        triD4LineSigma_one_apply]
    have hz : D.Θ ⟨D.α⁻¹ e₁, hDαinv_e₁C⟩ = (triD4LineSigma k K D.σ)⁻¹ y₁ := by
      rw [← hσz, MulAut.inv_apply_self]
    have hfix' : x * triD4LineSigma k K D.σ⁻¹ y₁ * x⁻¹ = y₁ := by
      have h1 : x * (triD4LineSigma k K D.σ)⁻¹ y₁ * x⁻¹ = y₁ := by
        have := hfixpre
        rw [hz] at this
        exact this
      rw [hσinv]
      exact h1
    have hfix_model : triD4LineMk k K gx cx hx *
        triD4LineSigma k K D.σ⁻¹ (triD4LineMk k K g₁ c₁ h₁) *
        (triD4LineMk k K gx cx hx)⁻¹ = triD4LineMk k K g₁ c₁ h₁ := by
      rw [hx_eq, hy₁]
      exact hfix'
    exact (kgLangT3_model_comm_ne_one k K hdeg D.σ⁻¹ (by rw [orderOf_inv, D.orderOf_σ]) g₁ gx c₁ cx
      h₁ hx hc₁ hfix_model) hcomm_transfer.symm

end CFSG.StandardType
