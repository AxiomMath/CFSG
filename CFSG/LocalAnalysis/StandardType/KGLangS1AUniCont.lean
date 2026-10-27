module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniFrame
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniFixed
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniCore
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTransfer
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniComp
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniCover
import CFSG.LocalAnalysis.StandardType.KGLangS1AGlue
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
import CFSG.LocalAnalysis.StandardType.GGL45TGSU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
@[reducible] private noncomputable def kgLangS1AUniContAux_F0 {F : Type} [Field F] (σ : F ≃+* F) :
    Subfield F :=
  CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ

private theorem kgLangS1AUniContAux_inducedAut_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) =
    θ (QuotientGroup.mk (α k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerQuotAut_mk]
private theorem kgLangS1AUniContAux_scalar_descend {d : ℕ} {F : Type} [Field F]
    {σ : F ≃+* F} (hd : 0 < d) {M : GL (Fin d) (kgLangS1AUniContAux_F0 σ)}
    (h : Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M ∈
      LargeEvenScalars (Fin d) F) :
    M ∈ LargeEvenScalars (Fin d) (kgLangS1AUniContAux_F0 σ) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨c, hc⟩ := h
  have hentry : ∀ i j : Fin d,
      (kgLangS1AUniContAux_F0 σ).subtype
        ((M : Matrix (Fin d) (Fin d) (kgLangS1AUniContAux_F0 σ)) i j) =
        (if i = j then (c : F) else 0) := by
    intro i j
    have h1 := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F) i j) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.GeneralLinearGroup.map_apply] at h1
    exact h1.symm
  let a : kgLangS1AUniContAux_F0 σ :=
    (M : Matrix (Fin d) (Fin d) (kgLangS1AUniContAux_F0 σ)) ⟨0, hd⟩ ⟨0, hd⟩
  have hdiag : (kgLangS1AUniContAux_F0 σ).subtype a = (c : F) :=
    (by simpa [a] using hentry ⟨0, hd⟩ ⟨0, hd⟩)
  have ha0 : a ≠ 0 := fun h0 => c.ne_zero (by rw [← hdiag, h0]; rfl)
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_mk0]
    exact (kgLangS1AUniContAux_F0 σ).subtype_injective (by rw [hentry i i, if_pos rfl, hdiag])
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij]
    exact (kgLangS1AUniContAux_F0 σ).subtype_injective (by
      rw [hentry i j, if_neg hij, map_zero])
private theorem kgLangS1AUniContAux_scalar_mul_comm {d : ℕ} {K : Type} [Field K]
    {c c' : Kˣ} {X Y : GL (Fin d) K} (h : X * Y = Y * X) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) =
      (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin d) c *
      Matrix.GeneralLinearGroup.scalar (Fin d) c' =
      Matrix.GeneralLinearGroup.scalar (Fin d) c' *
        Matrix.GeneralLinearGroup.scalar (Fin d) c :=
    Matrix.GeneralLinearGroup.scalar_commute c _
  calc (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y)
      = Matrix.GeneralLinearGroup.scalar (Fin d) c *
          (X * Matrix.GeneralLinearGroup.scalar (Fin d) c') * Y := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c' * X) * Y := by
          rw [Matrix.GeneralLinearGroup.scalar_commute c' X]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c *
          Matrix.GeneralLinearGroup.scalar (Fin d) c') * (X * Y) := by group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c' *
          Matrix.GeneralLinearGroup.scalar (Fin d) c) * (Y * X) := by rw [hc, h]
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c' *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c * (Y * X)) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c' *
          ((Matrix.GeneralLinearGroup.scalar (Fin d) c * Y) * X) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c' *
          ((Y * Matrix.GeneralLinearGroup.scalar (Fin d) c) * X) := by
          rw [Matrix.GeneralLinearGroup.scalar_commute c Y]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) := by group
theorem kgLangS1A_uni_cont
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : GGNbrLangS1UniLabel p lab) (hn : 1 ≤ lab.n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ lab.n) ^ 2) :
    KGLangAxisS1UniCont p
      (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) F (2 ^ lab.n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) F (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) F (2 ^ lab.n)))
      (LargeEvenMatFieldImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) F (2 ^ lab.n)))) := by
  classical
  let d : ℕ := lab.rank + 1
  let SU : Subgroup (GL (Fin d) F) := LargeEvenSUGroup (Fin d) F (2 ^ lab.n)
  let R : Type := LargeEvenProj SU
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk SU) (LargeEvenGUSet (Fin d) F (2 ^ lab.n))
  let Fd : Set (MulAut R) := LargeEvenMatFieldImage (LargeEvenProjMk SU)
  change KGLangAxisS1UniCont p R I Fd
  rw [KGLangAxisS1UniCont]
  intro K _ _ θ hK A hA hAIF α₀ hα₀ hα₀I hcard2 ξ hξ hξI J₀ hJ₀ d₁ m E _ hE θ₀ hAt
  obtain ⟨hsix, hsplit, hpn, htag⟩ := hlab
  have hpr : (p = 3 ∧ (lab.rank = 2 ∨ lab.rank = 5)) ∨ (p = 5 ∧ lab.rank = 4) := hsix.2
  have hsplitU : p ∣ 2 ^ lab.n + 1 := by
    rcases hsplit with ⟨hA, -⟩ | ⟨-, h⟩
    · rw [htag] at hA; cases hA
    · exact h
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; omega
  have hd : 3 ≤ d := by
    rcases hpr with ⟨rfl, h | h⟩ | ⟨rfl, h⟩ <;> simp [d] <;> omega
  have hdp : d = p ∨ d = 2 * p := by
    rcases hpr with ⟨rfl, h | h⟩ | ⟨rfl, h⟩ <;> simp [d] <;> omega
  have hn3 : 3 ≤ lab.n := le_trans hp3 (Nat.le_of_dvd (by omega) hpn)
  have hn2 : 2 ≤ lab.n := by omega
  have h2n : 2 ^ lab.n ≠ 2 := by
    intro h
    have h' : 2 ^ lab.n = 2 ^ 1 := by simpa using h
    have := Nat.pow_right_injective (le_refl 2) h'
    omega
  have hdq : ¬(d = 3 ∧ 2 ^ lab.n = 2) := by rintro ⟨-, h⟩; exact h2n h
  have hdq' : (d, 2 ^ lab.n) ≠ (3, 2) := fun h =>
    hdq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  have hm : 1 ≤ lab.n / p := by
    obtain ⟨k, hk⟩ := hpn
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0'] at hk
      omega
    rw [hk, Nat.mul_div_right k hp.pos]
    exact hk1
  have hsimple : IsSimpleGroup R :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 lab.n hF d hd hdq'
  have hI1 : (1 : MulAut R) ∈ I := by
    refine ⟨1, ?_, ?_⟩
    · rw [LargeEvenGUSet]
      exact ⟨1, one_ne_zero, by simp, by simp⟩
    · intro h h' hh
      have hh' : h' = h := Subtype.ext (by simpa using hh)
      rw [hh']
      simp
  have hna : ∃ a b : R, a * b ≠ b * a := kgLangTorA_nonabelian θ hK hI1 hξI
  have hdata : UnitaryFieldData 2 lab.n F := unitaryFieldData_of_card hn hF
  have hinn : GGRawInnField p R I Fd :=
    RecipeFieldSU.ggRawInnField_unitary hdata hF hd hdq hp.ne_one
  have hPC : GGRawPCyclic p R I Fd :=
    RecipeFieldSU.ggRawPCyclic_unitary hdata hF hd hdq
  have hFC : GGRawFieldConj p R I Fd :=
    RecipeFieldSpU.ggRawFieldConj_unitary hdata hF hd hdq hp hp2
  obtain ⟨B₀, X, u₀, f₀, hmem, hdec, hXcard, hu₀, hf₀, hf₀ord, hξeq, hXab, hXI, hXf, hXβ⟩ :=
    kgLangTorA_setup hp hsimple hna hinn hPC hFC θ hK hA hAIF hξ hξI
  obtain ⟨hB₀AI, hXeq⟩ := kgLangS1A_setup_eq θ hK hmem hXcard hXβ
  have hB₀A : B₀ ≤ A := fun β hβ => (hB₀AI β hβ).1
  have hα₀B₀ : α₀ ∉ B₀ := fun h => hα₀I (hB₀AI α₀ h).2
  obtain ⟨σ, hσord, hσE⟩ := kgLangTorA_uni_field hF hn hd hdq hf₀ hf₀ord
  obtain ⟨-, hF₀card⟩ := kgLangTorA_card_fixed_unitary hn hp hp2 hF hσord
  have hF₀data : UnitaryFieldData 2 (lab.n / p) (kgLangS1AUniContAux_F0 σ) :=
    unitaryFieldData_of_card hm hF₀card
  have hN : LargeEvenGUSet (Fin d) F (2 ^ lab.n) ⊆
      Subgroup.normalizer (SU : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer hdata
  have hN₀ : LargeEvenGUSet (Fin d) (kgLangS1AUniContAux_F0 σ) (2 ^ (lab.n / p)) ⊆
      Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) (kgLangS1AUniContAux_F0 σ) (2 ^ (lab.n / p)) :
          Set (GL (Fin d) (kgLangS1AUniContAux_F0 σ))) :=
    TableBUE.gu_subset_normalizer hF₀data
  obtain ⟨κ', hκ'surj, hκ'ker, hκ'u₀, hκ'conj, hκ'field⟩ :=
    kgLangS1A_uni_cover hdata hd hn2 θ hK hu₀
  let ψ₀ : SU →* SU :=
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F),
        GGL45TG.SU.map_mem_su hdata σ g.2⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (Matrix.GeneralLinearGroup.map (σ : F →+* F))
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (Matrix.GeneralLinearGroup.map (σ : F →+* F)) _ _ }
  have hψ₀coe : ∀ g : SU, ((ψ₀ g : SU) : GL (Fin d) F) =
      Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F) := fun g => rfl
  have hξ' : ∀ g : SU, ξ (κ' g) = κ' (ψ₀ g) :=
    hκ'field ξ σ f₀ ψ₀ hψ₀coe hσE hξeq
  rcases em (d = 3 ∧ 2 ^ (lab.n / p) = 2) with hcase | hdq₀
  ·
    exfalso
    obtain ⟨hd3, hq0⟩ := hcase
    have hrank : lab.rank = 2 := by
      dsimp only [d] at hd3
      omega
    cases lab with
    | mk tag rank n =>
      have hr : rank = 2 := hrank
      subst rank
      exact (kgLangS1A_uni_not_component hF hn hp hp2 hσord hq0 κ' hκ'surj hκ'ker ψ₀
        hψ₀coe hξ' J₀) hJ₀
  ·
    obtain ⟨ρ, hρ⟩ :=
      kgLangS1A_uni_component hF hn hd hp hp2 hσord hdq₀ κ' hκ'surj hκ'ker ψ₀
        hψ₀coe hξ' hJ₀
    let ψ : LargeEvenProj (LargeEvenSUGroup (Fin d) (kgLangS1AUniContAux_F0 σ)
          (2 ^ (lab.n / p))) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d₁) E (2 ^ m)) := ρ.symm.trans θ₀
    obtain ⟨hd1, hm_eq⟩ := kgLangS1A_psu_typeDet hd hm hF₀card hdq₀ hE ψ
    subst d₁
    subst m
    obtain ⟨At, hAtcomm, hAtdata⟩ := hAt
    let gof : (β : MulAut K) → β ∈ B₀ → ↥(TableB.unitGroup (ι := Fin d) hE.bar) :=
      fun β hβ => Classical.choose (hAtdata β (hB₀A hβ))
    have hgof_unit : ∀ β hβ, gof β hβ ∈ At := fun β hβ =>
      (Classical.choose_spec (hAtdata β (hB₀A hβ))).1
    have hgof_act : ∀ β hβ j, ∃ j' : ↥J₀, (j' : K) = β j ∧
        θ₀ (QuotientGroup.mk j') =
          CFSG.HardMathSupport.C14Cl.uniConj hE d (gof β hβ)
            (θ₀ (QuotientGroup.mk j)) :=
      fun β hβ => (Classical.choose_spec (hAtdata β (hB₀A hβ))).2
    let Cof : (β : MulAut K) → β ∈ B₀ → GL (Fin d) F := fun β hβ =>
      Classical.choose (TableB.exists_eq_projConj hN (hXI _ (hXβ β hβ)))
    have hCofGU : ∀ β hβ, Cof β hβ ∈ LargeEvenGUSet (Fin d) F (2 ^ lab.n) := fun β hβ =>
      Classical.choose (Classical.choose_spec
        (TableB.exists_eq_projConj hN (hXI _ (hXβ β hβ))))
    have hCofeq : ∀ β hβ, u₀⁻¹ * kgInducedAut θ β * u₀ =
        TableB.projConj SU ⟨Cof β hβ, hN (hCofGU β hβ)⟩ := fun β hβ =>
      (Classical.choose_spec (Classical.choose_spec
        (TableB.exists_eq_projConj hN (hXI _ (hXβ β hβ)))))
    have hgraphCof : ∀ β hβ, LargeEvenGraphAut (LargeEvenProjMk SU)
        (fun g g' => (g' : GL (Fin d) F) = Cof β hβ * g * (Cof β hβ)⁻¹)
        (u₀⁻¹ * kgInducedAut θ β * u₀) := by
      intro β hβ g g' hgg'
      rw [hCofeq β hβ]
      change TableB.projConj SU ⟨Cof β hβ, hN (hCofGU β hβ)⟩ (g : LargeEvenProj SU) =
        LargeEvenProjMk SU g'
      rw [TableB.projConj_mk]
      have hrep : ((SU.normalizerMonoidHom ⟨Cof β hβ, hN (hCofGU β hβ)⟩) g : SU) = g' := by
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_coe, hgg']
      rw [hrep]
      rfl
    obtain ⟨S, hmemS, hprojS, hcardS, hSgu, hdecomp⟩ :=
      kgLangS1A_uni_fixed_group hF hn hd hdq' hp hp2 hσord hXab hXI hσE hXf
    have hdecβ : ∀ β hβ, ∃ (c : Fˣ) (M : GL (Fin d) (kgLangS1AUniContAux_F0 σ)),
        M ∈ S ∧ Cof β hβ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
          Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M := fun β hβ =>
      hdecomp (Cof β hβ) (hCofGU β hβ) (u₀⁻¹ * kgInducedAut θ β * u₀) (hXβ β hβ)
        (hgraphCof β hβ)
    let cβ : (β : MulAut K) → β ∈ B₀ → Fˣ := fun β hβ => Classical.choose (hdecβ β hβ)
    let Mof : (β : MulAut K) → β ∈ B₀ → GL (Fin d) (kgLangS1AUniContAux_F0 σ) :=
      fun β hβ => Classical.choose (Classical.choose_spec (hdecβ β hβ))
    have hMof_S : ∀ β hβ, Mof β hβ ∈ S := fun β hβ =>
      (Classical.choose_spec (Classical.choose_spec (hdecβ β hβ))).1
    have hMof_spec : ∀ β hβ, Cof β hβ =
        Matrix.GeneralLinearGroup.scalar (Fin d) (cβ β hβ) *
          Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ) :=
      fun β hβ => (Classical.choose_spec (Classical.choose_spec (hdecβ β hβ))).2
    have hMof_norm : ∀ β hβ, Mof β hβ ∈
        Subgroup.normalizer
          (LargeEvenSUGroup (Fin d) (kgLangS1AUniContAux_F0 σ) (2 ^ (lab.n / p)) :
            Set (GL (Fin d) (kgLangS1AUniContAux_F0 σ))) :=
      fun β hβ => hN₀ (hSgu _ (hMof_S β hβ))
    have hρβ : ∀ (β : MulAut K) (hβ : β ∈ B₀) (j : ↥J₀), ∃ j' : ↥J₀, (j' : K) = β j ∧
        ρ (QuotientGroup.mk j') =
          TableB.projConj (LargeEvenSUGroup (Fin d) (kgLangS1AUniContAux_F0 σ)
              (2 ^ (lab.n / p)))
            ⟨Mof β hβ, hMof_norm β hβ⟩ (ρ (QuotientGroup.mk j)) := fun β hβ j =>
      hρ β ⟨Cof β hβ, hN (hCofGU β hβ)⟩ (cβ β hβ)
        ⟨Mof β hβ, hMof_norm β hβ⟩ (hMof_spec β hβ)
        (hκ'conj β ⟨Cof β hβ, hN (hCofGU β hβ)⟩ (hCofeq β hβ)) j
    have hMψ' : ∀ β hβ x,
        ψ (TableB.projConj (LargeEvenSUGroup (Fin d) (kgLangS1AUniContAux_F0 σ)
              (2 ^ (lab.n / p)))
            ⟨Mof β hβ, hMof_norm β hβ⟩ x) =
          TableB.projConj (LargeEvenSUGroup (Fin d) E (2 ^ (lab.n / p)))
            ⟨(gof β hβ : GL (Fin d) E),
              CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hE (gof β hβ).2⟩
            (ψ x) := by
      intro β hβ x
      obtain ⟨y, rfl⟩ := ρ.surjective x
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨j₁, hj₁K, hj₁ρ⟩ := hρβ β hβ j
      obtain ⟨j₂, hj₂K, hj₂θ⟩ := hgof_act β hβ j
      have hjj : j₁ = j₂ := Subtype.ext (by rw [hj₁K, hj₂K])
      rw [← hj₁ρ, hjj]
      dsimp only [ψ]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hj₂θ]
      rfl
    have hEcard : Nat.card E = (2 ^ (lab.n / p)) ^ 2 := by
      rw [hE.card, mul_comm, ← pow_mul]
    haveI : Finite E := hE.finite
    have hMof_comm : ∀ β hβ β' hβ',
        Mof β hβ * Mof β' hβ' = Mof β' hβ' * Mof β hβ := by
      intro β hβ β' hβ'
      refine kgLangS1A_uni_commute_transfer hd hm hF₀card hEcard hdq₀ ψ
        (hMψ' β hβ) (hMψ' β' hβ') ?_
      have h := hAtcomm.is_comm.comm ⟨gof β hβ, hgof_unit β hβ⟩
        ⟨gof β' hβ', hgof_unit β' hβ'⟩
      exact congrArg (fun z : ↥At => ((z : ↥(TableB.unitGroup (ι := Fin d) hE.bar)) :
        GL (Fin d) E)) h
    have hdesc : ∀ M ∈ S, ∃ (β : MulAut K) (hβ : β ∈ B₀)
        (u : (kgLangS1AUniContAux_F0 σ)ˣ),
        M = Matrix.GeneralLinearGroup.scalar (Fin d) u * Mof β hβ := by
      intro M hMS
      obtain ⟨hMn, hMX⟩ := (hmemS M).mp hMS
      rw [hXeq] at hMX
      obtain ⟨β, hβ, hβeq⟩ := Subgroup.mem_map.mp hMX
      have hφβ : ((MulAut.conj u₀⁻¹).toMonoidHom.comp (kgInducedAut θ)) β =
          u₀⁻¹ * kgInducedAut θ β * u₀ := by
        change (MulAut.conj u₀⁻¹) (kgInducedAut θ β) = _
        rw [MulAut.conj_apply, inv_inv]
      have hβeq' : u₀⁻¹ * kgInducedAut θ β * u₀ =
          TableB.projConj SU ⟨Matrix.GeneralLinearGroup.map
            (kgLangS1AUniContAux_F0 σ).subtype M, hMn⟩ := by
        rw [← hφβ]
        exact hβeq
      have hconj : TableB.projConj SU ⟨Matrix.GeneralLinearGroup.map
            (kgLangS1AUniContAux_F0 σ).subtype M, hMn⟩ =
          TableB.projConj SU ⟨Cof β hβ, hN (hCofGU β hβ)⟩ :=
        hβeq'.symm.trans (hCofeq β hβ)
      have hZproj : TableB.projConj SU
          (⟨Cof β hβ, hN (hCofGU β hβ)⟩⁻¹ *
            ⟨Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M, hMn⟩) = 1 := by
        rw [map_mul, map_inv, hconj, inv_mul_cancel]
      have hZscal : (Cof β hβ)⁻¹ *
          Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M ∈
          LargeEvenScalars (Fin d) F :=
        kgLangTorA_uni_scalar hF hn hd hdq' hZproj
      obtain ⟨w, hw⟩ := hZscal
      have hmapM : Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M =
          Matrix.GeneralLinearGroup.scalar (Fin d) (cβ β hβ * w) *
            Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ) := by
        calc Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M
            = Cof β hβ * ((Cof β hβ)⁻¹ *
                Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype M) := by group
          _ = Cof β hβ * Matrix.GeneralLinearGroup.scalar (Fin d) w := by rw [hw]
          _ = (Matrix.GeneralLinearGroup.scalar (Fin d) (cβ β hβ) *
                Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ)) *
                Matrix.GeneralLinearGroup.scalar (Fin d) w := by rw [hMof_spec β hβ]
          _ = Matrix.GeneralLinearGroup.scalar (Fin d) (cβ β hβ) *
                (Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ) *
                Matrix.GeneralLinearGroup.scalar (Fin d) w) := by group
          _ = Matrix.GeneralLinearGroup.scalar (Fin d) (cβ β hβ) *
                (Matrix.GeneralLinearGroup.scalar (Fin d) w *
                Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ)) := by
                rw [Matrix.GeneralLinearGroup.scalar_commute w
                  (Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ))]
          _ = Matrix.GeneralLinearGroup.scalar (Fin d) (cβ β hβ * w) *
                Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype (Mof β hβ) := by
                rw [map_mul (Matrix.GeneralLinearGroup.scalar (Fin d)) (cβ β hβ) w]
                group
      have hιmem : Matrix.GeneralLinearGroup.map (kgLangS1AUniContAux_F0 σ).subtype
          (M * (Mof β hβ)⁻¹) ∈ LargeEvenScalars (Fin d) F := by
        refine ⟨cβ β hβ * w, ?_⟩
        rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_inv, hmapM]
        group
      obtain ⟨u, hu⟩ := kgLangS1AUniContAux_scalar_descend (d := d) (by omega) hιmem
      refine ⟨β, hβ, u, ?_⟩
      rw [hu]
      group
    have hcommS : ∀ M ∈ S, ∀ N ∈ S, M * N = N * M := by
      intro M hMS N hNS
      obtain ⟨β, hβ, u, hu⟩ := hdesc M hMS
      obtain ⟨β', hβ', u', hu'⟩ := hdesc N hNS
      rw [hu, hu']
      exact kgLangS1AUniContAux_scalar_mul_comm (hMof_comm β hβ β' hβ')
    have hab : ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ lab.n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk SU)
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        ∀ B' ∈ LargeEvenGUSet (Fin d) F (2 ^ lab.n), ∀ x' ∈ X,
          LargeEvenGraphAut (LargeEvenProjMk SU)
            (fun g g' => (g' : GL (Fin d) F) = B' * g * B'⁻¹) x' → B * B' = B' * B := by
      intro B hBgu x hxX hBgraph B' hB'gu x' hx'X hB'graph
      obtain ⟨c, M, hMS, hBeq⟩ := hdecomp B hBgu x hxX hBgraph
      obtain ⟨c', M', hM'S, hB'eq⟩ := hdecomp B' hB'gu x' hx'X hB'graph
      rw [hBeq, hB'eq]
      exact kgLangS1AUniContAux_scalar_mul_comm
        (by
          rw [← Matrix.GeneralLinearGroup.map_mul, ← Matrix.GeneralLinearGroup.map_mul,
            hcommS M hMS M' hM'S])
    have hcardX : p ^ 2 ≤ Nat.card X := by rw [hXcard]; exact hcard2
    obtain ⟨U, a, hUσ, hU, hdiag, hsum, hne⟩ :=
      kgLangS1A_uni_frame hdata hdp hdq' hp hp2 hσord hXab hXI hσE hXf hsplitU hcardX hab
    obtain ⟨e, s, heSU, hsSU, heσ, hep, he_notscalar, hsσ, hcomm⟩ :=
      kgLangS1A_uni_core hdata hp hp2 hσord hsplitU hUσ hU hsum hne
    have hep' : (⟨e, heSU⟩ : SU) ^ p = 1 := by
      apply Subtype.ext
      exact hep
    have heσ' : ψ₀ ⟨e, heSU⟩ = ⟨e, heSU⟩ := by
      apply Subtype.ext
      exact heσ
    have hsσ' : ψ₀ ⟨s, hsSU⟩ = ⟨s, hsSU⟩ * ⟨e, heSU⟩ := by
      apply Subtype.ext
      exact hsσ
    have heKne : κ' ⟨e, heSU⟩ ≠ 1 := by
      intro h
      have h1 : θ (QuotientGroup.mk (κ' ⟨e, heSU⟩)) = 1 := by
        rw [h, QuotientGroup.mk_one, map_one]
      rw [hκ'u₀ ⟨e, heSU⟩] at h1
      have hproj : LargeEvenProjMk SU ⟨e, heSU⟩ = 1 :=
        u₀.injective (by rw [h1, map_one])
      have hscal : e ∈ LargeEvenScalars (Fin d) F := by
        have h4 : (⟨e, heSU⟩ : SU) ∈ (LargeEvenScalars (Fin d) F).subgroupOf SU := by
          rw [← QuotientGroup.eq_one_iff]
          exact hproj
        exact Subgroup.mem_subgroupOf.mp h4
      exact he_notscalar hscal
    haveI hSUperf : Group.IsPerfect SU :=
      Subgroup.isPerfect_iff.mpr (GGL45TG.SU.commutator_su hdata hd hn2)
    have hSU : commutator SU = ⊤ := Group.IsPerfect.commutator_eq_top
    have hψ₀ : ∀ h : SU, kgInducedAut θ ξ (θ (QuotientGroup.mk (κ' h))) =
        θ (QuotientGroup.mk (κ' (ψ₀ h))) := by
      intro h
      rw [kgLangS1AUniContAux_inducedAut_mk θ ξ (κ' h), hξ' h]
    have hβψ : ∀ β ∈ B₀, ∃ ψ : SU →* SU, ψ ⟨e, heSU⟩ = ⟨e, heSU⟩ ∧
        ψ ⟨s, hsSU⟩ = ⟨s, hsSU⟩ ∧
        ∀ h : SU, kgInducedAut θ β (θ (QuotientGroup.mk (κ' h))) =
          θ (QuotientGroup.mk (κ' (ψ h))) := by
      intro β hβ
      let ψ : SU →* SU := (SU.normalizerMonoidHom ⟨Cof β hβ, hN (hCofGU β hβ)⟩).toMonoidHom
      have hblock : ∀ i j, a i ≠ a j →
          ((U⁻¹ * Cof β hβ * U : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0 :=
        hdiag (Cof β hβ) (hCofGU β hβ) (u₀⁻¹ * kgInducedAut θ β * u₀) (hXβ β hβ)
          (hgraphCof β hβ)
      have hCe : Cof β hβ * e = e * Cof β hβ := (hcomm (Cof β hβ) hblock).1
      have hCs : Cof β hβ * s = s * Cof β hβ := (hcomm (Cof β hβ) hblock).2
      refine ⟨ψ, ?_, ?_, ?_⟩
      · apply Subtype.ext
        change Cof β hβ * e * (Cof β hβ)⁻¹ = e
        rw [hCe]; group
      · apply Subtype.ext
        change Cof β hβ * s * (Cof β hβ)⁻¹ = s
        rw [hCs]; group
      · intro h
        rw [kgLangS1AUniContAux_inducedAut_mk θ β (κ' h)]
        rw [hκ'conj β ⟨Cof β hβ, hN (hCofGU β hβ)⟩ (hCofeq β hβ) h]
        rfl
    obtain ⟨k, eK, heKne', heKp, hAe, hBk, hke⟩ :=
      kgLangTorA_concl_of_lift (H := SU) (K := K) (R := R) hSU θ A B₀ hdec κ'
        ψ₀ hψ₀ heKne hep' heσ' hsσ' hβψ
    obtain ⟨e', he'ne, he'p, hAe', hke'⟩ :=
      kgLangS1A_concl_of_xi hp hA hB₀A hξ hdec hα₀ hα₀B₀ heKne' heKp hAe hBk hke
    refine ⟨k, e', he'ne, he'p, hAe', ?_, hke'⟩
    intro α hα hαI
    exact hBk α (hmem α hα hαI)

end CFSG.StandardType
