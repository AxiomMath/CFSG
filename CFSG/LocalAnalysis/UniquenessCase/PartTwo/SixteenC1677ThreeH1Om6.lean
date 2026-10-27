module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitModel
public import CFSG.CGT.Foote82.T66.ProofCaseIISplit
public import CFSG.Quasithin.Background.RealizesFaithful
import CFSG.Quasithin.Background.G11Basic
import CFSG.CGT.Foote82.T66.FaithfulBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix
open CFSG.CGT.Foote82.OmegaSix
open CFSG.Quasithin
open CFSG.Quasithin.G11

private theorem s168e3_om6_model_fix_eq_zero :
    ∀ v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
      aMat *ᵥ v = v → bMat *ᵥ v = v → v = 0 := by
  decide

private def s168e3_M : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
    1, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]

private def s168e3_N : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 0, 1, 1, 0; 1, 1, 0, 1, 1, 0; 1, 1, 0, 1, 1, 1;
    0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1]

private theorem s168e3_MN_entry : ∀ i j : Fin 2 ⊕ Fin 2 ⊕ Fin 2,
    ((aMat - 1) * s168e3_M + (bMat - 1) * s168e3_N) i j =
      (1 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) i j := by
  intro i j
  rcases i with i | i | i <;> fin_cases i <;>
    rcases j with j | j | j <;> fin_cases j <;> decide

private theorem s168e3_MN : (aMat - 1) * s168e3_M + (bMat - 1) * s168e3_N = 1 :=
  funext fun i => funext fun j => s168e3_MN_entry i j

private theorem s168e3_om6_model_span_top :
    Submodule.span (ZMod 2)
      {w : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 |
        ∃ g ∈ CFSG.RankThree.PartTwo.omegaMinusTwo 2,
          ∃ u : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
            w = (g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ u - u} =
      ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hMN := congrArg (fun X : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
      (ZMod 2) => X *ᵥ v) s168e3_MN
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at hMN
  rw [← hMN]
  refine Submodule.add_mem _
    (Submodule.subset_span ⟨aGL, aGL_mem, s168e3_M *ᵥ v, rfl⟩)
    (Submodule.subset_span ⟨bGL, bGL_mem, s168e3_N *ᵥ v, rfl⟩)

private def s168e3_mulAutToLinear (q : ℕ) [Fact q.Prime] (V : Type*) [CommGroup V]
    [Module (ZMod q) (Additive V)] :
    MulAut V →* (Additive V ≃ₗ[ZMod q] Additive V) where
  toFun f :=
    { (MulEquiv.toAdditive f : Additive V ≃+ Additive V) with
      map_smul' := fun c v => ZMod.map_smul (MulEquiv.toAdditive f).toAddMonoidHom c v }
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' := fun _ _ => LinearEquiv.ext fun _ => rfl

private theorem s168e3_mulAutToLinear_injective (q : ℕ) [Fact q.Prime] (V : Type*)
    [CommGroup V] [Module (ZMod q) (Additive V)] :
    Function.Injective (s168e3_mulAutToLinear q V) := by
  intro f g hfg
  ext v
  have := LinearEquiv.congr_fun hfg (Additive.ofMul v)
  exact congrArg Additive.toMul this

theorem s168e3_om6_ext_split
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {Y : Subgroup W} (hnat : NatOmegaMinus A ⊤ Y 6 1)
    (hY : ∀ a ∈ A, ∀ y ∈ Y, a y = y) :
    ∃ W' : Subgroup W, (∀ a ∈ A, ∀ w ∈ W', a w ∈ W') ∧ IsCompl W' Y := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := hnat
  letI : Field K := hK
  haveI : Finite K := hKf
  have htwo : ∀ v : Additive W, (2 : ℕ) • v = 0 := by
    intro v
    rw [two_nsmul,
      show v + v = Additive.ofMul (Additive.toMul v * Additive.toMul v) from rfl,
      ← pow_two, hW (Additive.toMul v)]
    rfl
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule htwo
  let Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨βR, hβsurj, hβker, hβe⟩ := R.exists_β
  let βW : W →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    βR.comp (Subgroup.topEquiv (G := W)).symm.toMonoidHom
  have hβWker : ∀ w : W, βW w = 1 ↔ w ∈ Y := fun w =>
    hβker ⟨w, Subgroup.mem_top w⟩
  have hβWe : ∀ (γ : ↥Γ) (w : W), βW (((π γ : ↥A) : MulAut W) w) =
      CFSG.Quasithin.natAct Γ γ (βW w) := fun γ w =>
    hβe γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)
  obtain ⟨θ, ψ, hθeq, hψmem⟩ := s16c1_statedOmega_minus_zmod2 hK2 hpoly
  have hθmv : ∀ (γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
      (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      θ ((γ : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v) =
        ((ψ γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ θ v := by
    intro γ v
    have h := hθeq γ v
    rwa [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] at h
  have hinj : Function.Injective π := hπ.injective_of_faithful_on (FFModel.nat_faithful _)
  let πe : ↥Γ ≃* ↥A := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let ΩZ := CFSG.RankThree.PartTwo.omegaMinusTwo 2
  have hmap : Γ.map ψ.toMonoidHom = ΩZ := by
    ext g
    rw [Subgroup.mem_map_equiv, hψmem, MulEquiv.apply_symm_apply]
    exact Iff.rfl
  let ψΩ : ↥Γ ≃* ↥ΩZ :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  let φ₀ : ↥A ≃* ↥ΩZ := πe.symm.trans ψΩ
  have hφ₀co : ∀ γ : ↥Γ, ((φ₀ (πe γ) : ↥ΩZ) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) = ψ γ := by
    intro γ
    have h1 : φ₀ (πe γ) = ψΩ γ := by
      show (πe.symm.trans ψΩ) (πe γ) = ψΩ γ
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h1]
    simp only [ψΩ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply]
    rfl
  let β₀ : W →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :=
    (AddEquiv.toMultiplicative θ).toMonoidHom.comp βW
  have hβ₀ker : ∀ w : W, β₀ w = 1 ↔ w ∈ Y := fun w =>
    ((AddEquiv.toMultiplicative θ).map_eq_one_iff).trans (hβWker w)
  have hβ₀eγ : ∀ (γ : ↥Γ) (w : W), β₀ (((π γ : ↥A) : MulAut W) w) =
      Multiplicative.ofAdd
        (((ψ γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β₀ w)) := by
    intro γ w
    have h1 := hβWe γ w
    change Multiplicative.ofAdd
        (θ (Multiplicative.toAdd (βW (((π γ : ↥A) : MulAut W) w)))) =
      Multiplicative.ofAdd
        (((ψ γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β₀ w))
    rw [h1, CFSG.Quasithin.natAct, toAdd_ofAdd, hθmv]
    rfl
  have hβ₀e : ∀ (a : ↥A) (w : W), β₀ ((a : MulAut W) w) =
      Multiplicative.ofAdd
        (((φ₀ a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β₀ w)) := by
    intro a w
    obtain ⟨γ, hγ⟩ := πe.surjective a
    rw [← hγ]
    conv_lhs => rw [show πe γ = π γ from rfl]
    rw [hβ₀eγ γ w, hφ₀co γ]
  let βbar : Additive W →+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :=
    { toFun v := Multiplicative.toAdd (β₀ (Additive.toMul v))
      map_zero' := by simp
      map_add' v v' := by
        simp only [toMul_add, map_mul, toAdd_mul] }
  have hβbar_surj : Function.Surjective βbar := by
    intro y
    obtain ⟨w, hw⟩ := (hβsurj.comp (Subgroup.topEquiv (G := W)).symm.surjective)
      ((AddEquiv.toMultiplicative θ).symm (Multiplicative.ofAdd y))
    refine ⟨Additive.ofMul w, ?_⟩
    have hw' : βW w = (AddEquiv.toMultiplicative θ).symm (Multiplicative.ofAdd y) := hw
    change Multiplicative.toAdd (β₀ w) = y
    rw [show β₀ w = (AddEquiv.toMultiplicative θ) (βW w) from rfl, hw',
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hβbar_ker : ∀ v : Additive W, βbar v = 0 ↔ Additive.toMul v ∈ Y := by
    intro v
    change Multiplicative.toAdd (β₀ (Additive.toMul v)) = 0 ↔ Additive.toMul v ∈ Y
    rw [toAdd_eq_zero]
    exact hβ₀ker (Additive.toMul v)
  have hβbar_rho : ∀ (a : ↥A) (v : Additive W),
      βbar ((s168e3_mulAutToLinear 2 W a) v) =
        ((φ₀ a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ βbar v := by
    intro a v
    conv_lhs => rw [← ofMul_toMul v]
    show Multiplicative.toAdd (β₀ ((a : MulAut W) (Additive.toMul v))) =
      ((φ₀ a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (β₀ (Additive.toMul v))
    rw [hβ₀e a (Additive.toMul v)]
    rfl
  let ρ : MulAut W →* (Additive W ≃ₗ[ZMod 2] Additive W) := s168e3_mulAutToLinear 2 W
  have hρinj : Function.Injective ρ := s168e3_mulAutToLinear_injective 2 W
  let H : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W) := A.map ρ
  let eH : ↥A ≃* ↥H := Subgroup.equivMapOfInjective A ρ hρinj
  let φ : ↥H ≃* ↥ΩZ := eH.symm.trans φ₀
  let β : ↥(commSpace H ⊤) →+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :=
    βbar.comp (commSpace H ⊤).subtype.toAddMonoidHom
  have hφ_co : ∀ a : ↥A, φ (eH a) = φ₀ a := by
    intro a
    calc φ (eH a) = φ₀ (eH.symm (eH a)) := rfl
      _ = φ₀ a := by rw [MulEquiv.symm_apply_apply]
  have heH_val : ∀ (a : MulAut W) (ha : a ∈ A), ((eH ⟨a, ha⟩ : ↥H) :
      Additive W ≃ₗ[ZMod 2] Additive W) = ρ a := fun a ha =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  have hsurj : Function.Surjective β := by
    intro y
    have hy : y ∈ Submodule.span (ZMod 2)
        {w : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 |
          ∃ g ∈ CFSG.RankThree.PartTwo.omegaMinusTwo 2,
            ∃ u : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
              w = (g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
                (ZMod 2)) *ᵥ u - u} := by
      rw [s168e3_om6_model_span_top]
      trivial
    refine Submodule.span_induction (p := fun x _ => ∃ u : ↥(commSpace H ⊤), β u = x)
      ?_ ?_ ?_ ?_ hy
    · rintro x ⟨g, hg, u, rfl⟩
      obtain ⟨a, ha⟩ := φ₀.surjective ⟨g, hg⟩
      obtain ⟨v, hv⟩ := hβbar_surj u
      refine ⟨⟨(ρ a) v - v, ?_⟩, ?_⟩
      · exact sub_mem_commSpace (Subgroup.mem_map_of_mem ρ a.2) Submodule.mem_top
      · change βbar ((ρ a) v - v) = (g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
          (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ u - u
        rw [map_sub, hβbar_rho a v, hv]
        have hga : (φ₀ a : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = g := by
          rw [ha]
        rw [hga]
        rfl
    · exact ⟨0, map_zero β⟩
    · rintro x z _ _ ⟨u, hu⟩ ⟨w, hw⟩
      exact ⟨u + w, by rw [map_add, hu, hw]⟩
    · rintro c x _ ⟨u, hu⟩
      have hc : c = 0 ∨ c = 1 := by
        revert c
        decide
      rcases hc with rfl | rfl
      · exact ⟨0, by rw [zero_smul, map_zero]⟩
      · exact ⟨u, by rw [one_smul, hu]⟩
  have hβbar_fix : ∀ v : Additive W, (∀ h ∈ H, h v = v) → βbar v = 0 := by
    intro v hv
    have hfixΩ : ∀ g ∈ ΩZ,
        ((g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ βbar v =
          βbar v := by
      intro g hg
      obtain ⟨a, ha⟩ := φ₀.surjective ⟨g, hg⟩
      have h1 : (ρ a) v = v := hv (ρ a) (Subgroup.mem_map_of_mem ρ a.2)
      have h2 := hβbar_rho a v
      rw [h1] at h2
      have hga : (φ₀ a : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = g := by
        rw [ha]
      rw [← hga]
      exact h2.symm
    exact s168e3_om6_model_fix_eq_zero (βbar v) (hfixΩ aGL aGL_mem) (hfixΩ bGL bGL_mem)
  have hker : β.ker = ((fixedSpace H).comap (commSpace H ⊤).subtype).toAddSubgroup := by
    ext u
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap]
    have hbu : β u = βbar (u : Additive W) := rfl
    rw [hbu, hβbar_ker]
    constructor
    · intro hy h hh
      obtain ⟨a, ha, hah⟩ := Subgroup.mem_map.1 hh
      have hval : (h : Additive W ≃ₗ[ZMod 2] Additive W) = ρ a := by
        have hh' : (h : Additive W ≃ₗ[ZMod 2] Additive W) = (eH ⟨a, ha⟩ :
            Additive W ≃ₗ[ZMod 2] Additive W) := by
          rw [heH_val a ha]
          exact hah.symm
        rw [hh', heH_val a ha]
      rw [hval]
      change (ρ a) (u : Additive W) = (u : Additive W)
      conv_lhs => rw [← ofMul_toMul (u : Additive W)]
      rw [show (ρ a) (Additive.ofMul (Additive.toMul (u : Additive W))) =
          Additive.ofMul (a (Additive.toMul (u : Additive W))) from rfl,
        hY a ha (Additive.toMul (u : Additive W)) hy]
      rfl
    · intro hfix
      exact (hβbar_ker (u : Additive W)).1 (hβbar_fix (u : Additive W) hfix)
  have hequiv : ∀ (h : ↥H) (w w' : ↥(commSpace H ⊤)),
      (w' : Additive W) = (h : Additive W ≃ₗ[ZMod 2] Additive W) (w : Additive W) →
      β w' = ((φ h : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).mulVec (β w) := by
    intro h w w' hw
    obtain ⟨a, ha, hah⟩ := Subgroup.mem_map.1 h.2
    have hval : (h : Additive W ≃ₗ[ZMod 2] Additive W) = ρ a := by
      have hh' : h = eH ⟨a, ha⟩ := by
        apply Subtype.ext
        rw [heH_val a ha]
        exact hah.symm
      rw [hh', heH_val a ha]
    have hφh : φ h = φ₀ ⟨a, ha⟩ := by
      have hh' : h = eH ⟨a, ha⟩ :=
        Subtype.ext (by rw [heH_val a ha]; exact hah.symm)
      rw [hh', hφ_co ⟨a, ha⟩]
    have hw' : (w' : Additive W) = (ρ a) (w : Additive W) := by
      rw [hw, hval]
    have h1 : β w' = βbar ((ρ a) (w : Additive W)) := by
      change βbar (w' : Additive W) = βbar ((ρ a) (w : Additive W))
      rw [hw']
    rw [h1, hβbar_rho ⟨a, ha⟩ (w : Additive W), hφh]
    rfl
  have hsplit := CFSG.CGT.Foote82.caseIISplit_holds (Additive W) H φ β hsurj hker hequiv
  have hfixY : fixedSpace H = AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup Y) := by
    ext v
    rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
    constructor
    · intro hv
      exact (hβbar_ker v).1 (hβbar_fix v hv)
    · intro hv h hh
      obtain ⟨a, ha, hah⟩ := Subgroup.mem_map.1 hh
      have hval : (h : Additive W ≃ₗ[ZMod 2] Additive W) = ρ a := by
        have hh' : (h : Additive W ≃ₗ[ZMod 2] Additive W) = (eH ⟨a, ha⟩ :
            Additive W ≃ₗ[ZMod 2] Additive W) := by
          rw [heH_val a ha]
          exact hah.symm
        rw [hh', heH_val a ha]
      rw [hval]
      change (ρ a) v = v
      conv_lhs => rw [← ofMul_toMul v]
      rw [show (ρ a) (Additive.ofMul (Additive.toMul v)) =
          Additive.ofMul (a (Additive.toMul v)) from rfl,
        hY a ha (Additive.toMul v) hv]
      rfl
  let e : Submodule (ZMod 2) (Additive W) ≃o Subgroup W :=
    (AddSubgroup.toZModSubmodule 2).symm.trans Subgroup.toAddSubgroup.symm
  have he_mem : ∀ (X : Submodule (ZMod 2) (Additive W)) (w : W),
      w ∈ e X ↔ Additive.ofMul w ∈ X := by
    intro X w
    show w ∈ Subgroup.toAddSubgroup.symm ((AddSubgroup.toZModSubmodule 2).symm X) ↔
      Additive.ofMul w ∈ X
    rw [AddSubgroup.mem_toSubgroup']
    rfl
  refine ⟨e (commSpace H ⊤), ?_, ?_⟩
  · intro a ha w hw
    have hw' : Additive.ofMul w ∈ commSpace H ⊤ := (he_mem _ w).1 hw
    have hmem := CFSG.CGT.Foote82.L13Aux.invariant_commSpace_top H (ρ a)
      (Subgroup.mem_map_of_mem ρ ha) (Additive.ofMul w) hw'
    have : Additive.ofMul (a w) ∈ commSpace H ⊤ := by
      change (ρ a) (Additive.ofMul w) ∈ commSpace H ⊤
      exact hmem
    exact (he_mem _ (a w)).2 this
  · have heY : e (fixedSpace H) = Y := by
      rw [hfixY]
      show Subgroup.toAddSubgroup.symm ((AddSubgroup.toZModSubmodule 2).symm
        (AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup Y))) = Y
      rw [OrderIso.symm_apply_apply, OrderIso.symm_apply_apply]
    have := (OrderIso.isCompl_iff (f := e) (x := commSpace H ⊤)
      (y := fixedSpace H)).1 hsplit
    rwa [heY] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
