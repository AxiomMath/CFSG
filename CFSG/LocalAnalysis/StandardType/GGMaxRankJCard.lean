module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pjc_sum_smul_single {p : ℕ} (x : Fin 8 → ZMod p) :
    (∑ j, x j • Pi.single j (1 : ZMod p)) = x := by
  ext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne (Ne.symm hk), smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem pjc_card_of_datum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (hsep : ∀ b : ↥Bs, (∀ i, α i (ι (Additive.ofMul b)) = 0) ↔
      (b : G) ∈ Subgroup.centralizer (X : Set G)) :
    Nat.card Bs = p ^ 8 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hBsfin : Finite ↥Bs := inferInstance
  haveI : Finite (Additive ↥Bs) := Finite.of_equiv ↥Bs (Equiv.refl ↥Bs)
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Fintype V := Fintype.ofFinite V
  let F : V →ₗ[ZMod p] (Fin 8 → ZMod p) := LinearMap.pi fun i => α i
  have hF_apply : ∀ v i, F v i = α i v := by
    intro v i
    simp [F, LinearMap.pi_apply]
  let Cinv : Matrix (Fin 8) (Fin 8) ℤ :=
    !![4, 5, 7, 10, 8, 6, 4, 2;
       5, 8, 10, 15, 12, 9, 6, 3;
       7, 10, 14, 20, 16, 12, 8, 4;
       10, 15, 20, 30, 24, 18, 12, 6;
       8, 12, 16, 24, 20, 15, 10, 5;
       6, 9, 12, 18, 15, 12, 8, 4;
       4, 6, 8, 12, 10, 8, 6, 3;
       2, 3, 4, 6, 5, 4, 3, 2]
  have hZ : CartanMatrix.E 8 * Cinv = 1 := by decide
  let M : Matrix (Fin 8) (Fin 8) (ZMod p) :=
    (CartanMatrix.E 8).map (Int.castRingHom (ZMod p))
  let C : Matrix (Fin 8) (Fin 8) (ZMod p) := Cinv.map (Int.castRingHom (ZMod p))
  have hMC : M * C = 1 := by
    have h := congrArg (fun N : Matrix (Fin 8) (Fin 8) ℤ =>
      N.map (Int.castRingHom (ZMod p))) hZ
    rw [Matrix.map_mul (f := Int.castRingHom (ZMod p))] at h
    rw [Matrix.map_one (f := (Int.castRingHom (ZMod p) : ℤ → ZMod p)) (by simp) (by simp)] at h
    simpa [M, C] using h
  have hpairM : ∀ i j, α i (h j) = M i j := by
    intro i j
    rw [hpair i j]
    simp [M, Matrix.map_apply]
  have hFh : ∀ j, F (h j) = M.mulVec (Pi.single j (1 : ZMod p)) := by
    intro j
    ext i
    rw [hF_apply, hpairM i j, Matrix.mulVec_single_one, Matrix.col_apply]
  have hF_pre : ∀ w : Fin 8 → ZMod p,
      F (∑ j, (C.mulVec w) j • h j) = w := by
    intro w
    calc F (∑ j, (C.mulVec w) j • h j)
        = ∑ j, (C.mulVec w) j • F (h j) := by simp
      _ = ∑ j, (C.mulVec w) j • (M.mulVec (Pi.single j (1 : ZMod p))) := by simp [hFh]
      _ = M.mulVec (∑ j, (C.mulVec w) j • Pi.single j (1 : ZMod p)) := by
            conv_rhs => rw [← Matrix.mulVecLin_apply]
            rw [map_sum]
            simp [Matrix.mulVecLin_apply, map_smul]
      _ = M.mulVec (C.mulVec w) := by
            congr 1
            exact pjc_sum_smul_single (C.mulVec w)
      _ = (M * C).mulVec w := by rw [Matrix.mulVec_mulVec]
      _ = w := by rw [hMC, Matrix.one_mulVec]
  have hrange : LinearMap.range F = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro w
    exact ⟨∑ j, (C.mulVec w) j • h j, hF_pre w⟩
  let φa : Additive ↥Bs →+ (Fin 8 → ZMod p) :=
    { toFun := fun b => F (ι b)
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add] }
  have hφasurj : Function.Surjective φa := by
    intro w
    have hw : w ∈ LinearMap.range F := by rw [hrange]; trivial
    obtain ⟨v, hv⟩ := hw
    exact ⟨ι.symm v, by simp [φa, hv]⟩
  have hφaker : Nat.card ↥(φa.ker) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    let Φ : ↥(φa.ker) → ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := fun b =>
      ⟨(Additive.toMul b.1 : ↥Bs), by
        rw [Subgroup.mem_inf]
        refine ⟨(Additive.toMul b.1 : ↥Bs).2, ?_⟩
        exact (hsep (Additive.toMul b.1 : ↥Bs)).mp (fun i => by
          have hb : φa b.1 = 0 := AddMonoidHom.mem_ker.mp b.2
          have hb2 := congrFun hb i
          change F (ι b.1) i = 0 at hb2
          rw [hF_apply] at hb2
          simpa using hb2)⟩
    let Ψ : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) → ↥(φa.ker) := fun b =>
      ⟨Additive.ofMul (⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩ : ↥Bs), by
        rw [AddMonoidHom.mem_ker]
        funext i
        change F (ι (Additive.ofMul (⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩ : ↥Bs))) i = 0
        rw [hF_apply]
        exact (hsep ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩).mpr (Subgroup.mem_inf.mp b.2).2 i⟩
    have hΦΨ : Function.LeftInverse Ψ Φ := by
      intro b; apply Subtype.ext; simp [Φ, Ψ]
    have hΨΦ : Function.RightInverse Ψ Φ := by
      intro b; apply Subtype.ext; simp [Φ, Ψ]
    let e : ↥(φa.ker) ≃ ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
      ⟨Φ, Ψ, hΦΨ, hΨΦ⟩
    exact Nat.card_congr e
  have hφarange : Nat.card ↥(φa.range) = p ^ 8 := by
    have htop : φa.range = ⊤ := AddMonoidHom.range_eq_top.mpr hφasurj
    rw [htop, Nat.card_congr (AddSubgroup.topEquiv).toEquiv, Nat.card_fun, Nat.card_zmod]
    simp [Nat.card_eq_fintype_card]
  have hLag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (φa.ker)
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φa).toEquiv,
    hφarange, hφaker] at hLag
  rw [← Nat.card_congr (Additive.ofMul : ↥Bs ≃ Additive ↥Bs)] at hLag
  exact hLag

theorem ggResE8Separated_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResE8SeparatedDatum p Bs X) :
    Nat.card Bs = p ^ 8 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  obtain ⟨V, hVadd, hVmod, ι, φ, h, α, hlin, hrefl, hpair, hauto, hclosure, hsep⟩ := h
  exact @pjc_card_of_datum G _ _ p _ Bs X V hVadd hVmod ι h α hpair hsep

end CFSG.StandardType

end
