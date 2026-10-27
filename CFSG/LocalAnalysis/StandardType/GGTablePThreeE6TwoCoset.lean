module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Coset

private def e6TwoCoset_threeVarpiSix : Fin Tag.E6.rank → ℤ := ![2, 3, 4, 6, 5, 4]

private def e6TwoCoset_tau₀ : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

private theorem e6TwoCoset_single_sum (x : Fin Tag.E6.rank → ℤ) :
    x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem e6TwoCoset_additive_ext
    {ρ σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (haddρ : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (haddσ : ∀ x y, σ (x + y) = σ x + σ y)
    (hagree : ∀ i : Fin Tag.E6.rank, ρ (Pi.single i 1) = σ (Pi.single i 1))
    (x : Fin Tag.E6.rank → ℤ) : ρ x = σ x := by
  have hzeroρ : ρ 0 = 0 := by
    have h := haddρ 0 0
    rw [add_zero] at h
    have h' : ρ 0 - ρ 0 = ρ 0 + ρ 0 - ρ 0 := congrArg (fun t => t - ρ 0) h
    simpa using h'.symm
  have hzeroσ : σ 0 = 0 := by
    have h := haddσ 0 0
    rw [add_zero] at h
    have h' : σ 0 - σ 0 = σ 0 + σ 0 - σ 0 := congrArg (fun t => t - σ 0) h
    simpa using h'.symm
  let f : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := ρ, map_zero' := hzeroρ, map_add' := haddρ }
  let g : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := σ, map_zero' := hzeroσ, map_add' := haddσ }
  have hf : f x = ∑ i, x i • f (Pi.single i 1) := by
    conv_lhs => rw [e6TwoCoset_single_sum x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul f (x i) _
  have hg : g x = ∑ i, x i • g (Pi.single i 1) := by
    conv_lhs => rw [e6TwoCoset_single_sum x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul g (x i) _
  calc ρ x = f x := rfl
    _ = ∑ i, x i • f (Pi.single i 1) := hf
    _ = ∑ i, x i • g (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i _
        change x i • ρ (Pi.single i 1) = x i • σ (Pi.single i 1)
        rw [hagree i]
    _ = g x := hg.symm
    _ = σ x := rfl

private theorem e6TwoCoset_tau :
    permLattice e6TwoCoset_tau₀ e6ThreeVarpiOne = e6TwoCoset_threeVarpiSix := by
  funext k
  fin_cases k <;> decide

private theorem e6TwoCoset_cartan_varpiOne :
    ∀ i : Fin Tag.E6.rank, ((∑ j, Tag.E6.cartan i j * e6ThreeVarpiOne j : ℤ) : ZMod 3) = 0 := by
  intro i
  fin_cases i <;> decide

private theorem e6TwoCoset_cartan_varpiSix :
    ∀ i : Fin Tag.E6.rank, ((∑ j, Tag.E6.cartan i j * e6TwoCoset_threeVarpiSix j : ℤ) : ZMod 3) = 0 := by
  intro i
  fin_cases i <;> decide

private theorem e6TwoCoset_tau_diff :
    ¬ (((e6TwoCoset_threeVarpiSix 0 - e6ThreeVarpiOne 0 : ℤ) : ZMod 3) = 0) := by
  decide +kernel

private theorem e6TwoCoset_weyl_congr (v : Fin Tag.E6.rank → ℤ)
    (hA : ∀ i : Fin Tag.E6.rank, ((∑ j, Tag.E6.cartan i j * v j : ℤ) : ZMod 3) = 0)
    (w : WeylGroup Tag.E6) :
    ∀ k : Fin Tag.E6.rank, (((w • v) k - v k : ℤ) : ZMod 3) = 0 := by
  induction w using (coxeterSystem Tag.E6).simple_induction_left with
  | one => intro k; simp
  | mul_simple_left w i ih =>
    intro k
    have hy : ∀ j, (((w • v) j : ℤ) : ZMod 3) = ((v j : ℤ) : ZMod 3) := by
      intro j
      have h := ih j
      rw [Int.cast_sub, sub_eq_zero] at h
      exact h
    have hsum : ((∑ j, Tag.E6.cartan i j * (w • v) j : ℤ) : ZMod 3) = 0 := by
      have h1 : ((∑ j, Tag.E6.cartan i j * (w • v) j : ℤ) : ZMod 3)
          = ∑ j, (Tag.E6.cartan i j : ZMod 3) * (((w • v) j : ℤ) : ZMod 3) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Int.cast_mul]
      have h2 : (∑ j, (Tag.E6.cartan i j : ZMod 3) * (((w • v) j : ℤ) : ZMod 3))
          = ∑ j, (Tag.E6.cartan i j : ZMod 3) * ((v j : ℤ) : ZMod 3) :=
        Finset.sum_congr rfl fun j _ => by rw [hy j]
      have h3 : (∑ j, (Tag.E6.cartan i j : ZMod 3) * ((v j : ℤ) : ZMod 3))
          = ((∑ j, Tag.E6.cartan i j * v j : ℤ) : ZMod 3) := by
        rw [Int.cast_sum]
        exact (Finset.sum_congr rfl fun j _ => by rw [Int.cast_mul]).symm
      rw [h1, h2, h3, hA i]
    rw [mul_smul, simple_smul]
    have hk : ((reflect Tag.E6 i (w • v) k - v k : ℤ) : ZMod 3)
        = (((w • v) k - v k : ℤ) : ZMod 3)
          - ((∑ j, Tag.E6.cartan i j * (w • v) j : ℤ) : ZMod 3)
            * ((Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) k : ZMod 3) := by
      simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hk, ih k, hsum]
    ring

private theorem e6TwoCoset_rho_untw
    {L : Type} [Field L] [IsAlgClosed L] (D : LangDatum Tag.E6 L)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ D.q) ∧ D.Φ = Units.map (entrywiseHom Fr)) :
    ∃ w : WeylGroup Tag.E6, ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → ρ γ = w • γ := by
  obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
  obtain ⟨w, hn⟩ := D.n_weyl
  refine ⟨w, fun γ hγ => ?_⟩
  obtain ⟨Fr₀, hFr₀, -⟩ := D.steinberg
  have hq : 0 < D.q := by
    rcases Nat.eq_zero_or_pos D.q with h | h
    · exfalso
      have h0 := hFr₀ 0
      rw [map_zero, h, pow_zero] at h0
      exact zero_ne_one h0
    · exact h
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have h1 := hρ.map_rootSubgroup γ hγ
  rw [D.map_step_rootSubgroup hsurj hΦeq hn hγ] at h1
  exact (eq_of_rootSubgroup_eq ((isRoot_smul_iff w).2 hγ) ((hρ.isRoot_iff γ).2 hγ) h1).symm

private theorem e6TwoCoset_rho_tw
    {L : Type} [Field L] [IsAlgClosed L] (D : LangDatum Tag.E6 L)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ D.q) ∧ D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ w : WeylGroup Tag.E6,
      ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → ρ γ = w • permLattice e6TwoCoset_tau₀ γ := by
  obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
  obtain ⟨w, hn⟩ := D.n_weyl
  let w' : WeylGroup TwistTag.E6.tag := w
  have hn' : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := hn
  refine ⟨w, fun γ hγ => ?_⟩
  obtain ⟨Fr₀, hFr₀, -⟩ := D.steinberg
  have hq : 0 < D.q := by
    rcases Nat.eq_zero_or_pos D.q with h | h
    · exfalso
      have h0 := hFr₀ 0
      rw [map_zero, h, pow_zero] at h0
      exact zero_ne_one h0
    · exact h
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have hstep_eq : D.step = CFSG.HardMathSupport.Timmesfeld.CrossChar.twFrob TwistTag.E6
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w') Fr := by
    rw [LangDatum.step, hn', hΦeq]
    rfl
  have hmap : (rootSubgroup Tag.E6 L γ).map D.step =
      rootSubgroup Tag.E6 L (w' • permLattice TwistTag.E6.perm γ) := by
    rw [hstep_eq]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.map_twFrob_rootSubgroup
      TwistTag.E6 hsurj w' hγ
  have heq : rootSubgroup Tag.E6 L (ρ γ) =
      rootSubgroup Tag.E6 L (w' • permLattice TwistTag.E6.perm γ) := by
    rw [← hρ.map_rootSubgroup γ hγ, hmap]
  have hmain : ρ γ = w' • permLattice TwistTag.E6.perm γ :=
    eq_of_rootSubgroup_eq (τ := TwistTag.E6.tag) (γ := ρ γ)
      (δ := w' • permLattice TwistTag.E6.perm γ)
      ((hρ.isRoot_iff γ).2 hγ)
      (IsRoot.smul (hγ.permLattice TwistTag.E6.cartan_perm) w') heq
  have hconv : w' • permLattice TwistTag.E6.perm γ = w • permLattice e6TwoCoset_tau₀ γ := rfl
  rw [hconv] at hmain
  exact hmain

end Coset

theorem e6_cosetW_of_untw
    {L : Type} [Field L] [IsAlgClosed L] (D : LangDatum Tag.E6 L)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ D.q) ∧ D.Φ = Units.map (entrywiseHom Fr)) :
    E6CosetW ρ := by
  obtain ⟨w, hw⟩ := e6TwoCoset_rho_untw D hρ hΦ
  have hρeq : ρ e6ThreeVarpiOne = w • e6ThreeVarpiOne :=
    e6TwoCoset_additive_ext (frobRootMap_map_add D hρ)
      (fun x y => smul_add w x y)
      (fun i => hw (Pi.single i 1) (IsRoot.basis i)) e6ThreeVarpiOne
  intro k
  rw [hρeq]
  exact e6TwoCoset_weyl_congr e6ThreeVarpiOne e6TwoCoset_cartan_varpiOne w k

theorem e6_not_cosetW_of_tw
    {L : Type} [Field L] [IsAlgClosed L] (D : LangDatum Tag.E6 L)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ D.q) ∧ D.Φ = twistHom TwistTag.E6 L Fr) :
    ¬ E6CosetW ρ := by
  obtain ⟨w, hw⟩ := e6TwoCoset_rho_tw D hρ hΦ
  intro hC
  have hρeq : ρ e6ThreeVarpiOne = w • e6TwoCoset_threeVarpiSix := by
    have h1 : ρ e6ThreeVarpiOne = w • (permLattice e6TwoCoset_tau₀ e6ThreeVarpiOne) :=
      e6TwoCoset_additive_ext (ρ := ρ) (σ := fun x => w • permLattice e6TwoCoset_tau₀ x)
        (frobRootMap_map_add D hρ)
        (fun x y => by
          rw [show permLattice e6TwoCoset_tau₀ (x + y)
              = permLattice e6TwoCoset_tau₀ x + permLattice e6TwoCoset_tau₀ y from rfl,
            smul_add])
        (fun i => hw (Pi.single i 1) (IsRoot.basis i)) e6ThreeVarpiOne
    rwa [e6TwoCoset_tau] at h1
  have h0 := hC 0
  rw [hρeq] at h0
  have hw0 := e6TwoCoset_weyl_congr e6TwoCoset_threeVarpiSix e6TwoCoset_cartan_varpiSix w 0
  have key : (((w • e6TwoCoset_threeVarpiSix) 0 - e6ThreeVarpiOne 0 : ℤ) : ZMod 3)
      - (((w • e6TwoCoset_threeVarpiSix) 0 - e6TwoCoset_threeVarpiSix 0 : ℤ) : ZMod 3)
      = ((e6TwoCoset_threeVarpiSix 0 - e6ThreeVarpiOne 0 : ℤ) : ZMod 3) := by
    push_cast
    ring
  rw [h0, hw0, sub_zero] at key
  exact e6TwoCoset_tau_diff key.symm

end CFSG.StandardType.TablePThreeKG

end
