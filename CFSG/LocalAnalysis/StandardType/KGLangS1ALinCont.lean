module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033

import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.KGLangTorALinLift
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinCore
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTransfer
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinComp
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
import CFSG.Walter.Bender1970.S2.Inner
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

private theorem kgLangS1ALinContAux_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (h : LargeEvenSLGroup (Fin d) K) :
    TypeA.slKerEquiv d K (MulAut.conjNormal A h) =
      slConjugation d K A (TypeA.slKerEquiv d K h) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hc : ∀ h : LargeEvenSLGroup (Fin d) K,
      Matrix.SpecialLinearGroup.toGL (TypeA.slKerEquiv d K h) = (h : GL (Fin d) K) :=
    fun h => Units.ext (TypeA.coe_slKerEquiv h)
  rw [toGL_slConjugation, hc, hc, MulAut.conjNormal_apply]

private theorem kgLangS1ALinContAux_recipeEquiv_linConjAut {d : ℕ} {K : Type} [Field K]
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
  rw [LinearFlag.conjAut_proj, kgLangS1ALinContAux_slKerEquiv_conjNormal]

private theorem kgLangS1ALinContAux_two_le_div {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (h3 : p = 3 ∨ p = 5) (hsplit : p ∣ 2 ^ n - 1) (hpn : p ∣ n) : 2 ≤ n / p := by
  have hnne : n ≠ p := by
    rintro hn'
    rcases h3 with h3 | h5
    · subst h3; subst hn'; norm_num at hsplit
    · subst h5; subst hn'; norm_num at hsplit
  obtain ⟨k, hk⟩ := hpn
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hk; omega)
  have hkne : k ≠ 1 := fun h => hnne (by rw [hk, h, mul_one])
  rw [Nat.le_div_iff_mul_le hp.pos]
  calc 2 * p = p * 2 := by ring
    _ ≤ p * k := Nat.mul_le_mul_left p (by omega)
    _ = n := hk.symm

theorem kgLangS1A_lin_cont
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : GGNbrLangS1LinLabel p lab) (hn : 1 ≤ lab.n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ lab.n) :
    KGLangAxisS1LinCont p (LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) F))
        Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) F))) := by
  classical
  let d : ℕ := lab.rank + 1
  let R : Type := LargeEvenProj (LargeEvenSLGroup (Fin d) F)
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ
  let Fd : Set (MulAut R) :=
    LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))
  change KGLangAxisS1LinCont p R I Fd
  rw [KGLangAxisS1LinCont]
  intro K _ _ θ hK A hA hAIF α₀ hα₀ hα₀I hcard2 ξ hξ hξI J₀ hJ₀ d₁ Ef _ _ θ₀ hAt
  obtain ⟨hsix, hsplit, hpn, htag⟩ := hlab
  have hpr : (p = 3 ∧ (lab.rank = 2 ∨ lab.rank = 5)) ∨ (p = 5 ∧ lab.rank = 4) := hsix.2
  have hsplitA : p ∣ 2 ^ lab.n - 1 := by
    rcases hsplit with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rw [htag] at h; cases h
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; omega
  have hd : 3 ≤ d := by
    rcases hpr with ⟨rfl, h | h⟩ | ⟨rfl, h⟩ <;> simp [d] <;> omega
  have hd2 : 2 ≤ d := by omega
  have hdp : d = p ∨ d = 2 * p := by
    rcases hpr with ⟨rfl, h | h⟩ | ⟨rfl, h⟩ <;> simp [d] <;> omega
  have hp35 : p = 3 ∨ p = 5 := by
    rcases hpr with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
  have hm : 2 ≤ lab.n / p := kgLangS1ALinContAux_two_le_div hp hn hp35 hsplitA hpn
  have hsimple : IsSimpleGroup R := LinearFieldFix.isSimpleGroup_proj hd F
  have hna : ∃ a b : R, a * b ≠ b * a := LinearFieldFix.exists_noncomm_proj hd F
  have hinn : GGRawInnField p R I Fd :=
    RecipeFieldLinear.ggRawInnField_linear (d := d) (K := F) hd2 (Or.inl hd) hp.ne_one
  have hPC : GGRawPCyclic p R I Fd :=
    RecipeFieldLinear.ggRawPCyclic_linear (d := d) (K := F) hd2 (hp.odd_of_ne_two hp2)
  have hFC : GGRawFieldConj p R I Fd :=
    RecipeFieldLang.ggRawFieldConj_linear (d := d) (K := F) hd2 (Or.inl hd) hp
  obtain ⟨B₀, X, u₀, f₀, hmem, hdec, hXcard, hu₀, hf₀, hf₀ord, hξeq, hXab, hXI, hXf, hXβ⟩ :=
    kgLangTorA_setup hp hsimple hna hinn hPC hFC θ hK hA hAIF hξ hξI
  let E : MulAut R ≃* MulAut (LinearFlag.projectiveSL d F) :=
    MulAut.congr (TypeA.recipeEquiv d F)
  obtain ⟨σ, hσord, hσE, hX'ab, hX'c, hX'σ, hX'card⟩ :=
    kgLangTorA_lin_transport (d := d) (p := p) hp hd hXab hXI hf₀ hf₀ord hXf
  let X' : Subgroup (MulAut (LinearFlag.projectiveSL d F)) :=
    X.map (MulAut.congr (TypeA.recipeEquiv d F)).toMonoidHom
  have hn3 : 3 ≤ lab.n := le_trans hp3 (Nat.le_of_dvd (by omega) hpn)
  have hF8 : 8 ≤ Nat.card F := by
    rw [hF]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
  have hF2 : Nat.card F ≠ 2 := by omega
  have hF3 : Nat.card F ≠ 3 := by omega
  have hF4 : ¬(d = 3 ∧ Nat.card F = 4) := by rintro ⟨-, h⟩; omega
  let θ' : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL d F :=
    θ.trans (TypeA.recipeEquiv d F)
  obtain ⟨κ, hκ⟩ := kgLangTorA_lin_lift (d := d) (F := F) hd hF2 hF4 hF3 hK θ'
  let g₀ : GL (Fin d) F := Classical.choose (TypeA.congr_recipeEquiv_mem hu₀)
  have hEu' : E u₀ = LinearFlag.conjAut d F g₀ :=
    (Classical.choose_spec (TypeA.congr_recipeEquiv_mem hu₀)).symm
  let κ' : Matrix.SpecialLinearGroup (Fin d) F →* K :=
    κ.comp (slConjugation d F g₀).toMonoidHom
  have hκ' : ∀ h, θ' (QuotientGroup.mk (κ' h)) =
      LinearFlag.conjAut d F g₀ (LinearFlag.proj d F h) := by
    intro h
    change θ' (QuotientGroup.mk (κ (slConjugation d F g₀ h))) = _
    rw [hκ]
    exact LinearFlag.conjAut_proj g₀ h
  haveI hSLperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hd
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin d) F) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have hact : ∀ (β : MulAut K) (Y : MulAut (LinearFlag.projectiveSL d F))
      (f : Matrix.SpecialLinearGroup (Fin d) F →* Matrix.SpecialLinearGroup (Fin d) F),
      E (kgInducedAut θ β) = LinearFlag.conjAut d F g₀ * Y * (LinearFlag.conjAut d F g₀)⁻¹ →
      (∀ h, Y (LinearFlag.proj d F h) = LinearFlag.proj d F (f h)) →
      ∀ h, kgInducedAut θ' β (θ' (QuotientGroup.mk (κ' h))) =
        θ' (QuotientGroup.mk (κ' (f h))) := by
    intro β Y f hE hY h
    rw [kgLangTorA_inducedAut_trans θ (TypeA.recipeEquiv d F) β, hκ' h, hE, hκ' (f h), ← hY h]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  have hξeq' : E (kgInducedAut θ ξ) = LinearFlag.conjAut d F g₀ * LinearFlag.fieldAut d F σ *
      (LinearFlag.conjAut d F g₀)⁻¹ := by
    rw [hξeq, map_mul, map_mul, map_inv, hσE, hEu']
  have hξψ : ∀ h, kgInducedAut θ' ξ (θ' (QuotientGroup.mk (κ' h))) =
      θ' (QuotientGroup.mk (κ' (Matrix.SpecialLinearGroup.map σ.toRingHom h))) :=
    hact ξ _ (Matrix.SpecialLinearGroup.map σ.toRingHom) hξeq' (LinearFlag.fieldAut_proj σ)
  have hξact : ∀ h, ξ (κ' h) = κ' (Matrix.SpecialLinearGroup.map σ.toRingHom h) :=
    kgLangTorA_act hSL θ' κ' ξ (Matrix.SpecialLinearGroup.map σ.toRingHom) hξψ
  have hκsurj : Function.Surjective κ' := by
    have hmk : Function.Surjective ((QuotientGroup.mk' (Subgroup.center K)).comp κ') := by
      intro q
      obtain ⟨x, hx⟩ := (LinearFlag.conjAut d F g₀).surjective (θ' q)
      obtain ⟨h, rfl⟩ := LinearFlag.proj_surjective d F x
      exact ⟨h, θ'.injective (by rw [← hx]; exact hκ' h)⟩
    have hrange : κ'.range ⊔ Subgroup.center K = ⊤ := by
      have h1 : κ'.range.map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
        rw [← MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hmk]
      have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center K))) h1
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
    exact MonoidHom.range_eq_top.mp (CFSG.Walter.eq_top_of_sup_center_eq_top hK hrange)
  have hκker : κ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro h hh
    rw [← LinearFlag.scalars_eq_center, ← LinearFlag.proj_eq_one_iff]
    apply (LinearFlag.conjAut d F g₀).injective
    have h1 : θ' (QuotientGroup.mk (κ' h)) = 1 := by
      rw [MonoidHom.mem_ker.mp hh, QuotientGroup.mk_one, map_one]
    rw [hκ' h] at h1
    simpa using h1
  obtain ⟨ρ, hρ⟩ := kgLangS1A_lin_component (d := d) (F := F) hd (σ := σ) (K := K)
    κ' hκsurj hκker hξact hJ₀
  let ψ : LinearFlag.projectiveSL d (semilinearFixedSubfield σ) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d₁) Ef) := ρ.symm.trans θ₀
  have hF₀card : Nat.card (semilinearFixedSubfield σ) = 2 ^ (lab.n / p) :=
    (kgLangTorA_card_fixed_linear (F := F) (n := lab.n) (p := p) hn hF hσord).2
  obtain ⟨hd1, hEcard⟩ := kgLangS1A_psl_typeDet hd hm hF₀card ψ
  subst d₁
  let ψ' : LinearFlag.projectiveSL d (semilinearFixedSubfield σ) ≃*
      LinearFlag.projectiveSL d Ef := ψ.trans (TypeA.recipeEquiv d Ef)
  obtain ⟨At, hAtcomm, hAtdata⟩ := hAt
  let φ : MulAut K →* MulAut R := (MulAut.conj u₀⁻¹).toMonoidHom.comp (kgInducedAut θ)
  have hφβ : ∀ β : MulAut K, φ β = u₀⁻¹ * kgInducedAut θ β * u₀ := fun β => by
    change (MulAut.conj u₀⁻¹) (kgInducedAut θ β) = _; rw [MulAut.conj_apply, inv_inv]
  have hXβ' : ∀ β ∈ B₀, φ β ∈ X := fun β hβ => by rw [hφβ]; exact hXβ β hβ
  have hinjθ : Function.Injective (kgInducedAut θ) := ggInducedAut_injective_of_perfect hK θ
  have hinjφ : Function.Injective φ := (MulAut.conj u₀⁻¹).injective.comp hinjθ
  have hA₀sub : {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I} ⊆ (B₀ : Set (MulAut K)) :=
    fun α hα => hmem α hα.1 hα.2
  have hle1 : Nat.card ↥B₀ ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} := by
    rw [← hXcard]
    exact Nat.card_le_card_of_injective
      (fun β : ↥B₀ => (⟨φ (β : MulAut K), hXβ' (β : MulAut K) β.2⟩ : ↥X))
      (fun β γ h => Subtype.ext (hinjφ (congrArg Subtype.val h)))
  have hle2 : Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} ≤ Nat.card ↥B₀ :=
    Nat.card_le_card_of_injective (fun a : {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} =>
      (⟨a.1, hA₀sub a.2⟩ : ↥B₀))
      (fun a b h => Subtype.ext (congrArg (fun x : ↥B₀ => (x : MulAut K)) h))
  have hcardeq : Nat.card ↥B₀ =
      Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} := le_antisymm hle1 hle2
  have hcardeq' : (B₀ : Set (MulAut K)).ncard =
      {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I}.ncard := by
    rw [← Nat.card_coe_set_eq (B₀ : Set (MulAut K)),
      ← Nat.card_coe_set_eq {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I}]
    exact hcardeq
  have hseteq : {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I} = (B₀ : Set (MulAut K)) :=
    Set.eq_of_subset_of_ncard_le hA₀sub (le_of_eq hcardeq') (Set.toFinite _)
  have hB₀AI : ∀ β ∈ B₀, β ∈ A ∧ kgInducedAut θ β ∈ I := fun β hβ =>
    (show β ∈ {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I} from by rw [hseteq]; exact hβ)
  have hB₀A : B₀ ≤ A := fun β hβ => (hB₀AI β hβ).1
  have hXeq : X = B₀.map φ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      exact fun β hβ => hXβ' β hβ
    · rw [Subgroup.card_map_of_injective hinjφ, hcardeq, hXcard]
  let gof : (β : MulAut K) → β ∈ B₀ → GL (Fin d) Ef := fun β hβ =>
    Classical.choose (hAtdata β (hB₀A hβ))
  have hgof_act : ∀ (β : MulAut K) (hβ : β ∈ B₀), ∀ j : ↥J₀, ∃ j' : ↥J₀,
      (j' : K) = β j ∧ θ₀ (QuotientGroup.mk j') =
        TableB.linConjAut (Fin d) Ef (gof β hβ) (θ₀ (QuotientGroup.mk j)) := fun β hβ =>
    (Classical.choose_spec (hAtdata β (hB₀A hβ))).2
  let Cof : (β : MulAut K) → β ∈ B₀ → GL (Fin d) F := fun β hβ =>
    Classical.choose (TypeA.congr_recipeEquiv_mem (hXI _ (hXβ β hβ)))
  have hCof_spec : ∀ (β : MulAut K) (hβ : β ∈ B₀),
      LinearFlag.conjAut d F (Cof β hβ) = E (u₀⁻¹ * kgInducedAut θ β * u₀) := fun β hβ =>
    Classical.choose_spec (TypeA.congr_recipeEquiv_mem (hXI _ (hXβ β hβ)))
  have hCofX' : ∀ (β : MulAut K) (hβ : β ∈ B₀), LinearFlag.conjAut d F (Cof β hβ) ∈ X' := by
    intro β hβ
    rw [hCof_spec β hβ]
    exact Subgroup.mem_map.mpr ⟨_, hXβ β hβ, rfl⟩
  have hCofσ : ∀ (β : MulAut K) (hβ : β ∈ B₀),
      LinearFlag.fieldAut d F σ * LinearFlag.conjAut d F (Cof β hβ) =
        LinearFlag.conjAut d F (Cof β hβ) * LinearFlag.fieldAut d F σ := by
    intro β hβ
    rw [hCof_spec β hβ, ← hσE, ← map_mul, ← map_mul, hXf _ (hXβ β hβ)]
  have hCof_hact : ∀ (β : MulAut K) (hβ : β ∈ B₀), ∀ h,
      kgInducedAut θ' β (θ' (QuotientGroup.mk (κ' h))) =
        θ' (QuotientGroup.mk (κ' (slConjugation d F (Cof β hβ) h))) := by
    intro β hβ
    refine hact β (LinearFlag.conjAut d F (Cof β hβ)) (slConjugation d F (Cof β hβ)).toMonoidHom
      ?_ (fun h => LinearFlag.conjAut_proj (Cof β hβ) h)
    rw [hCof_spec β hβ, map_mul, map_mul, map_inv, hEu']
    group
  have hCof_act : ∀ (β : MulAut K) (hβ : β ∈ B₀), ∀ h,
      β (κ' h) = κ' (slConjugation d F (Cof β hβ) h) := fun β hβ =>
    kgLangTorA_act hSL θ' κ' β (slConjugation d F (Cof β hβ)).toMonoidHom (hCof_hact β hβ)
  let Mof : (β : MulAut K) → β ∈ B₀ → GL (Fin d) (semilinearFixedSubfield σ) := fun β hβ =>
    Classical.choose (Classical.choose_spec
      (kgLangTorA_lin_descend_lift hp (d := d) (by omega) hσord (Cof β hβ) (hCofσ β hβ)))
  have hMof_spec : ∀ (β : MulAut K) (hβ : β ∈ B₀), ∃ c : Fˣ,
      Cof β hβ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype (Mof β hβ) :=
    fun β hβ => ⟨Classical.choose (kgLangTorA_lin_descend_lift hp (d := d) (by omega) hσord
        (Cof β hβ) (hCofσ β hβ)),
      Classical.choose_spec (Classical.choose_spec
        (kgLangTorA_lin_descend_lift hp (d := d) (by omega) hσord (Cof β hβ) (hCofσ β hβ)))⟩
  have hMψ' : ∀ (β : MulAut K) (hβ : β ∈ B₀) x,
      ψ' (LinearFlag.conjAut d (semilinearFixedSubfield σ) (Mof β hβ) x) =
        LinearFlag.conjAut d Ef (gof β hβ) (ψ' x) := by
    intro β hβ x
    obtain ⟨c, hc⟩ := hMof_spec β hβ
    obtain ⟨y, rfl⟩ := ρ.surjective x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨j₁, hj₁K, hj₁ρ⟩ :=
      hρ β c (Mof β hβ) (by intro h; rw [← hc]; exact hCof_act β hβ h) j
    obtain ⟨j₂, hj₂K, hj₂θ⟩ := hgof_act β hβ j
    have hjj : j₁ = j₂ := Subtype.ext (by rw [hj₁K, hj₂K])
    rw [← hj₁ρ, hjj]
    dsimp only [ψ', ψ]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hj₂θ, kgLangS1ALinContAux_recipeEquiv_linConjAut]
  have hMof_comm : ∀ (β : MulAut K) (hβ : β ∈ B₀) (β' : MulAut K) (hβ' : β' ∈ B₀),
      Commute (Mof β hβ) (Mof β' hβ') := fun β hβ β' hβ' =>
    kgLangS1A_commute_transfer hd hEcard ψ' (hMψ' β hβ) (hMψ' β' hβ')
      (congrArg Subtype.val (hAtcomm.is_comm.comm
        ⟨gof β hβ, (Classical.choose_spec (hAtdata β (hB₀A hβ))).1⟩
        ⟨gof β' hβ', (Classical.choose_spec (hAtdata β' (hB₀A hβ'))).1⟩))
  have hdesc : ∀ M ∈ X'.comap ((LinearFlag.conjAut d F).comp
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)),
      ∃ (β : MulAut K) (hβ : β ∈ B₀) (u : Fˣ),
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M =
          Matrix.GeneralLinearGroup.scalar (Fin d) u *
            Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype (Mof β hβ) := by
    intro M hM
    have hMχ : (LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype) M ∈ X' := hM
    obtain ⟨y, hyX, hyE⟩ := Subgroup.mem_map.mp hMχ
    obtain ⟨β, hβ, hβy⟩ := Subgroup.mem_map.mp (hXeq ▸ hyX)
    have hconjM : LinearFlag.conjAut d F
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M) =
        E (u₀⁻¹ * kgInducedAut θ β * u₀) := by
      rw [← hφβ, hβy]
      exact hyE.symm
    have hconjMof : LinearFlag.conjAut d F
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype (Mof β hβ)) =
        E (u₀⁻¹ * kgInducedAut θ β * u₀) := by
      obtain ⟨c, hc⟩ := hMof_spec β hβ
      rw [← hCof_spec β hβ, hc, map_mul, LinearFlag.conjAut_scalar, one_mul]
    have hconj : LinearFlag.conjAut d F
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
          (M * (Mof β hβ)⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hconjM, hconjMof, mul_inv_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one (K := F) hconj
    obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar (by omega) hc
    exact ⟨β, hβ, u, by rw [← hu, map_mul, map_inv]; group⟩
  have hab : ∀ M ∈ X'.comap ((LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)),
      ∀ N ∈ X'.comap ((LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)), M * N = N * M := by
    intro M hM N hN
    obtain ⟨β, hβ, u, hu⟩ := hdesc M hM
    obtain ⟨β', hβ', u', hu'⟩ := hdesc N hN
    apply Matrix.GeneralLinearGroup.map_injective (semilinearFixedSubfield σ).subtype_injective
    rw [map_mul, map_mul, hu, hu']
    exact (Commute.mul_left (TypeA.commute_scalar_GL u _) (Commute.mul_right
      (TypeA.commute_scalar_GL u' _).symm ((hMof_comm β hβ β' hβ').map _))).eq
  have hcard' : p ^ 2 ≤ Nat.card X' := by rw [hX'card, hXcard]; exact hcard2
  obtain ⟨e, s, he_fixed, hep, he_notcenter, hs_fixed, hcomm⟩ :=
    kgLangS1A_lin_core (d := d) (n := lab.n) (p := p) hp hp2 hn hF hdp hσord
      hX'ab hX'c hX'σ hsplitA hcard' hab
  have heKne : κ' e ≠ 1 := fun h => he_notcenter (hκker (MonoidHom.mem_ker.mpr h))
  have hfixC : ∀ (C : GL (Fin d) F) (x : Matrix.SpecialLinearGroup (Fin d) F),
      C * Matrix.SpecialLinearGroup.toGL x = Matrix.SpecialLinearGroup.toGL x * C →
      slConjugation d F C x = x := by
    intro C x hCx
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_slConjugation, hCx]
    group
  have hBψ : ∀ β ∈ B₀, ∃ ψ₀ : Matrix.SpecialLinearGroup (Fin d) F →*
      Matrix.SpecialLinearGroup (Fin d) F, ψ₀ e = e ∧ ψ₀ s = s ∧
      ∀ h, kgInducedAut θ' β (θ' (QuotientGroup.mk (κ' h))) =
        θ' (QuotientGroup.mk (κ' (ψ₀ h))) := fun β hβ =>
    ⟨(slConjugation d F (Cof β hβ)).toMonoidHom, hfixC _ _ (hcomm _ (hCofX' β hβ)).1,
      hfixC _ _ (hcomm _ (hCofX' β hβ)).2, hCof_hact β hβ⟩
  obtain ⟨k, eK, heKne, heKp, hAe, hBk, hke⟩ :=
    kgLangTorA_concl_of_lift (H := Matrix.SpecialLinearGroup (Fin d) F) (K := K)
      (R := LinearFlag.projectiveSL d F) (α₀ := ξ) hSL θ' A B₀ hdec κ'
      (Matrix.SpecialLinearGroup.map σ.toRingHom) hξψ heKne hep he_fixed hs_fixed hBψ
  obtain ⟨β₀, hβ₀, j, hα₀dec⟩ := hdec α₀ hα₀
  have hjp : ¬ p ∣ j := by
    intro hpj
    have hξj : ξ ^ j = 1 := by
      obtain ⟨t, rfl⟩ := hpj
      rw [pow_mul, hA.2 ξ hξ, one_pow]
    apply hα₀I
    rw [hα₀dec, map_mul, hξj, map_one, mul_one]
    exact (hB₀AI β₀ hβ₀).2
  have hkξ : ξ k = eK⁻¹ * k := by
    have h2 : k = eK * ξ k := mul_inv_eq_iff_eq_mul.mp hke
    conv_rhs => rw [h2]
    group
  have heKfix : ∀ m : ℕ, (ξ ^ m) eK = eK := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hAe ξ hξ, ih]
  have hpowk : ∀ m : ℕ, (ξ ^ m) k = (eK ^ m)⁻¹ * k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, MulAut.mul_apply, hkξ, map_mul, map_inv, ih, heKfix m, pow_succ, mul_inv_rev]
      group
  have hα₀k : α₀ k = (ξ ^ j) k := by
    rw [hα₀dec, MulAut.mul_apply, hpowk j]
    simp only [map_mul, map_inv, map_pow, hAe β₀ (hB₀A hβ₀), hBk β₀ hβ₀]
  refine ⟨k, eK ^ j, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    haveI : Fact p.Prime := ⟨hp⟩
    have horder : orderOf eK = p := orderOf_eq_prime heKp heKne
    exact hjp (by rw [← horder, orderOf_dvd_iff_pow_eq_one]; exact h)
  · rw [← pow_mul, mul_comm, pow_mul, heKp, one_pow]
  · intro α hα
    rw [map_pow, hAe α hα]
  · intro α hα hαI
    exact hBk α (hmem α hα hαI)
  · rw [hα₀k, hpowk j]
    group

end CFSG.StandardType
