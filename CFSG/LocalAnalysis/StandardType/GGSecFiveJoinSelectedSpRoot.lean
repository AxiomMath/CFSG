module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSpRoot
public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
import CFSG.LieType.Steinberg.Classical.Symplectic
import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.StandardType.SpRootPair

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.StandardType CFSG.StandardType.ClassicalPosition
  TauCeti.GLSymplecticFin

variable {F : Type} [Field F]

theorem ggRankOneModel_symplectic {n : ℕ} (hn : 2 ≤ n) :
    GGRankOneModel (Symplectic.rootDatum n F) F := by
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (Symplectic.rootDatum n F).isFiniteType (Dv := (Symplectic.rootDatum n F).divisible) rfl
  exact ⟨CFSG.LieType.Steinberg.Sp.x n F, CFSG.LieType.Steinberg.Sp.commC, O,
    CFSG.LieType.Steinberg.Sp.chevalleyExtras hn O _
      (CFSG.LieType.Steinberg.Sp.commutatorFormula O),
    fun h hh i => PsiDiag.Symp.ggTorus_conj_x _ (single_mem_roots i) h hh⟩

private theorem allEven_stdVec_positiveLong {n : ℕ} (i : Fin n) :
    GGRootSp.AllEven (stdVec (.positiveLong i)) := by
  intro a
  simp only [stdVec, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem allEven_of_maxHeight {n : ℕ} (hn : 2 ≤ n)
    {γ₀ : Fin (Symplectic.rootDatum n F).rank → ℤ} (hγ₀ : γ₀ ∈ (Symplectic.rootDatum n F).roots)
    (hmax : ∀ δ ∈ (Symplectic.rootDatum n F).roots, ∑ i, δ i ≤ ∑ i, γ₀ i) :
    GGRootSp.AllEven (toStd n γ₀) := by
  obtain ⟨r₀, hr₀⟩ := exists_stdVec_of_mem_roots hγ₀
  rw [← hr₀]
  obtain ⟨θ, hθ, hθstd⟩ := GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, by omega⟩)
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hle : ht (ι := Fin n) θ ≤ ht (ι := Fin n) γ₀ := hmax θ hθ
  have hγ2 := two_mul_ht (n := n) γ₀
  rw [← hr₀] at hγ2
  have h4 : 4 * (n : ℤ) - 4 < lv n (stdVec r₀) := by omega
  rw [GGRootSp.stdVec_eq_of_lv_lt hn r₀ h4]
  exact allEven_stdVec_positiveLong _

theorem exists_eq_weylAction_long {n : ℕ} (hn : 2 ≤ n)
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} (hl : GGLongRoot (Symplectic.rootDatum n F) β) :
    ∃ w : (coxeterMatrix (Symplectic.rootDatum n F).isFiniteType).Group,
      β = weylAction (Symplectic.rootDatum n F).isFiniteType w
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hl
  have hev := allEven_of_maxHeight hn hγ₀ hmax
  have hγ₀' : γ₀ ∈ roots (isFiniteType_cartanC n) ∅ := hγ₀
  rcases hγ₀' with ⟨w', k, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  have hk : ¬ k.val + 1 < n :=
    (GGRootSp.allEven_toStd_single_iff k).1 ((GGRootSp.allEven_toStd_weylAction_iff w' _).1 hev)
  have hkeq : k = ⟨n - 1, by omega⟩ := Fin.ext (by have := k.isLt; simp only; omega)
  let w₁ : (coxeterMatrix (Symplectic.rootDatum n F).isFiniteType).Group := w
  let w₂ : (coxeterMatrix (Symplectic.rootDatum n F).isFiniteType).Group := w'
  refine ⟨w₁ * w₂, ?_⟩
  rw [weylAction_mul_apply, hkeq]
  rfl

private theorem map_conj_mul {K : Type*} [Group K] (H : Subgroup K) (a b : K) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem map_conj_map {K K' : Type*} [Group K] [Group K'] (ι : K' →* K) (H : Subgroup K')
    (g : K') : (H.map (MulAut.conj g).toMonoidHom).map ι =
      (H.map ι).map (MulAut.conj (ι g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem exists_conj_rootGroup_long {n : ℕ} (hn : 2 ≤ n)
    {γ : Fin (Symplectic.rootDatum n F).rank → ℤ} (hl : GGLongRoot (Symplectic.rootDatum n F) γ) :
    ∃ g : ↥(CFSG.Open.StatedSp n F),
      ((Symplectic.rootDatum n F).rootGroup (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)).map
          (MulAut.conj g).toMonoidHom = (Symplectic.rootDatum n F).rootGroup γ ∧
      ((Symplectic.rootDatum n F).rootGroup (-Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)).map
          (MulAut.conj g).toMonoidHom = (Symplectic.rootDatum n F).rootGroup (-γ) := by
  obtain ⟨w, rfl⟩ := exists_eq_weylAction_long hn hl
  have hact := CFSG.LieType.Steinberg.actsAs_nrep (D := Symplectic.rootDatum n F)
    (Symplectic.isCTGroupDatum n F) w
  refine ⟨CFSG.LieType.Steinberg.nrep (D := Symplectic.rootDatum n F)
    (Symplectic.isCTGroupDatum n F) w, hact _ (single_mem_roots _), ?_⟩
  have hneg : -(Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 : Fin n → ℤ) ∈
      (Symplectic.rootDatum n F).roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots _ (single_mem_roots _)
  exact (hact _ hneg).trans (congrArg _ (map_neg _ _))

theorem exists_conj_rankOne_eq_map_rankOne [CharP F 2] {n r : ℕ} (hn : 2 ≤ n) (hr : 2 ≤ r)
    (ι : ↥(CFSG.Open.StatedSp r F) →* ↥(CFSG.Open.StatedSp n F))
    {β₀ : Fin (Symplectic.rootDatum r F).rank → ℤ} (hlong : GGLongRoot (Symplectic.rootDatum r F) β₀)
    {v w : Fin n ⊕ Fin n → F}
    (hvw : v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w = 1)
    (hX : (((Symplectic.rootDatum r F).rootGroup β₀).map ι).map (CFSG.Open.StatedSp n F).subtype =
      matTransvGroup v
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v))
    (hX' : (((Symplectic.rootDatum r F).rootGroup (-β₀)).map ι).map
        (CFSG.Open.StatedSp n F).subtype =
      matTransvGroup w
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w)) :
    ∃ u : ↥(CFSG.Open.StatedSp n F),
      (CFSG.LieType.CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup
          (⟨n - 1, by omega⟩ : Fin n)).map (MulAut.conj u).toMonoidHom =
        (CFSG.LieType.CurtisTits.rankOne (Symplectic.rootDatum r F).rootGroup
          (⟨r - 1, by omega⟩ : Fin r)).map ι := by
  obtain ⟨g', hg'₁, hg'₂⟩ := exists_conj_rootGroup_long hr hlong
  obtain ⟨θ, -, hlθ, u₁, hu₁, hu₁'⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSp n F (by omega) v w hvw
  obtain ⟨g, hg₁, hg₂⟩ := exists_conj_rootGroup_long hn hlθ
  have hθ₁ : ((Symplectic.rootDatum n F).rootGroup θ).map (MulAut.conj u₁).toMonoidHom =
      ((Symplectic.rootDatum r F).rootGroup β₀).map ι :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hu₁.trans hX.symm)
  have hθ₂ : ((Symplectic.rootDatum n F).rootGroup (-θ)).map (MulAut.conj u₁).toMonoidHom =
      ((Symplectic.rootDatum r F).rootGroup (-β₀)).map ι :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hu₁'.trans hX'.symm)
  refine ⟨(ι g')⁻¹ * (u₁ * g), ?_⟩
  have key : ∀ (γ : Fin (Symplectic.rootDatum n F).rank → ℤ)
      (γ' : Fin (Symplectic.rootDatum r F).rank → ℤ) (δ : Fin (Symplectic.rootDatum n F).rank → ℤ)
      (δ' : Fin (Symplectic.rootDatum r F).rank → ℤ),
      ((Symplectic.rootDatum n F).rootGroup γ).map (MulAut.conj g).toMonoidHom =
        (Symplectic.rootDatum n F).rootGroup δ →
      ((Symplectic.rootDatum n F).rootGroup δ).map (MulAut.conj u₁).toMonoidHom =
        ((Symplectic.rootDatum r F).rootGroup δ').map ι →
      ((Symplectic.rootDatum r F).rootGroup γ').map (MulAut.conj g').toMonoidHom =
        (Symplectic.rootDatum r F).rootGroup δ' →
      ((Symplectic.rootDatum n F).rootGroup γ).map (MulAut.conj ((ι g')⁻¹ * (u₁ * g))).toMonoidHom =
        ((Symplectic.rootDatum r F).rootGroup γ').map ι := by
    intro γ γ' δ δ' h₁ h₂ h₃
    rw [map_conj_mul, map_conj_mul, h₁, h₂, ← h₃, map_conj_map, ← map_conj_mul, inv_mul_cancel,
      map_one]
    exact Subgroup.map_id _
  simp only [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (key _ _ _ _ hg₁ hθ₁ hg'₁) (key _ _ _ _ hg₂ hθ₂ hg'₂)

theorem exists_models_conj_range_eq [CharP F 2] {n r : ℕ} (hn : 2 ≤ n) (hr : 2 ≤ r)
    (ι : ↥(CFSG.Open.StatedSp r F) →* ↥(CFSG.Open.StatedSp n F))
    {β₀ : Fin (Symplectic.rootDatum r F).rank → ℤ} (hlong : GGLongRoot (Symplectic.rootDatum r F) β₀)
    {v w : Fin n ⊕ Fin n → F}
    (hvw : v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w = 1)
    (hX : (((Symplectic.rootDatum r F).rootGroup β₀).map ι).map (CFSG.Open.StatedSp n F).subtype =
      matTransvGroup v
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v))
    (hX' : (((Symplectic.rootDatum r F).rootGroup (-β₀)).map ι).map
        (CFSG.Open.StatedSp n F).subtype =
      matTransvGroup w
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w)) :
    ∃ (model' : SelectedRoot.SelectedSL2Model (Symplectic.rootDatum r F) F
        (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1))
      (model : SelectedRoot.SelectedSL2Model (Symplectic.rootDatum n F) F
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1))
      (u : ↥(CFSG.Open.StatedSp n F)),
      ((MulAut.conj u).toMonoidHom.comp model.phi).range = (ι.comp model'.phi).range := by
  obtain ⟨u, hu⟩ := exists_conj_rankOne_eq_map_rankOne hn hr ι hlong hvw hX hX'
  obtain ⟨model, hmodel⟩ :=
    SelectedRoot.exists_model_of_rankOneModel (ggRankOneModel_symplectic (F := F) hn)
      (⟨n - 1, by omega⟩ : Fin n)
  obtain ⟨model', hmodel'⟩ :=
    SelectedRoot.exists_model_of_rankOneModel (ggRankOneModel_symplectic (F := F) hr)
      (⟨r - 1, by omega⟩ : Fin r)
  refine ⟨model', model, u, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_comp, hmodel, hmodel']
  exact hu

end CFSG.StandardType.SpRootPair

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition

section Presented

theorem presentedSelectedSL2At_of_transvPair {G : Type} [Group G] {n r f : ℕ} (hn : 2 ≤ n)
    (hr : 2 ≤ r) (ψ : (ggU .PSp n f).K →* G)
    (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    {β₀ : Fin (ggU .PSp r f).D.rank → ℤ} (hlong : GGLongRoot (ggU .PSp r f).D β₀)
    {v w : Fin n ⊕ Fin n → GaloisField 2 f}
    (hvw : v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ w = 1)
    (hX : (((ggU .PSp r f).D.rootGroup β₀).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v))
    (hX' : (((ggU .PSp r f).D.rootGroup (-β₀)).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup w ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ w)) :
    ∃ (δ : Fin (ggU .PSp r f).D.rank → ℤ)
      (model' : SelectedRoot.SelectedSL2Model (ggU .PSp r f).D (GaloisField 2 f) δ),
      PresentedSelectedSL2At ψ ((ψ.comp ι).comp model'.phi).range := by
  obtain ⟨model', model, u, h⟩ :=
    SpRootPair.exists_models_conj_range_eq (F := GaloisField 2 f) hn hr ι hlong hvw hX hX'
  refine ⟨_, model', GaloisField 2 f, inferInstance, inferInstance, inferInstance, _, model, u, ?_⟩
  exact ((congrArg MonoidHom.range (MonoidHom.comp_assoc _ _ _)).trans
    (MonoidHom.range_comp _ _)).trans ((congrArg (Subgroup.map ψ) h).trans
      ((congrArg MonoidHom.range (MonoidHom.comp_assoc _ _ _)).trans
        (MonoidHom.range_comp _ _)).symm)

end Presented

end CFSG.StandardType

end
