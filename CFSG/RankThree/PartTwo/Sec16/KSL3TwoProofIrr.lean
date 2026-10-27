module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofOut
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTools
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix

@[expose] def KSL3TwoIrrThree : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (J : Subgroup (GL (Fin 3) K)),
    (∀ W : Submodule K (Fin 3 → K),
      (∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a) → 3 ∣ Nat.card J

namespace ProofKSL3Two

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_lift_model (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (Y : Subgroup (projImage (slPi π 3 (p ^ f) K))) (hY3 : ¬ 3 ∣ Nat.card Y) :
    ∃ Ŷ : Subgroup (GL (Fin 3) K), Ŷ ≤ slPi π 3 (p ^ f) K ∧
      ∃ e : Ŷ ≃* Y, ∀ g : Ŷ,
        ((e g : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g : GL (Fin 3) K) := by
  have hker : (projOf (slPi π 3 (p ^ f) K)).ker =
      (Subgroup.center (GL (Fin 3) K)).subgroupOf (slPi π 3 (p ^ f) K) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← Subtype.coe_inj, coe_projOf,
      Subgroup.coe_one, ProjGenLinGroup.mk_eq_one]
  have hker3 : Nat.card (projOf (slPi π 3 (p ^ f) K)).ker = 3 := by
    rw [hker, ← Subgroup.card_subtype, Subgroup.subgroupOf_map_subtype, inf_comm,
      card_slPi_inf_center hK hq]
  have hcop : Nat.Coprime (Nat.card (projOf (slPi π 3 (p ^ f) K)).ker) (Nat.card Y) := by
    rw [hker3]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3
  obtain ⟨Y', hmap, hdisj⟩ := Sec6.BThreeCensus.exists_lift_of_coprime (projOf_surjective _) Y hcop
  set f₀ : ↥Y' →* ↥Y := ((projOf (slPi π 3 (p ^ f) K)).comp Y'.subtype).codRestrict Y (fun y => by
    rw [← hmap]
    exact ⟨y, y.2, rfl⟩) with hf₀
  have hf₀bij : Function.Bijective f₀ := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have h1 : (y : slPi π 3 (p ^ f) K) ∈ (projOf (slPi π 3 (p ^ f) K)).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hy
      have h2 := Subgroup.disjoint_def.mp hdisj y.2 h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
    · rintro ⟨m, hm⟩
      rw [← hmap] at hm
      obtain ⟨y, hy, rfl⟩ := hm
      exact ⟨⟨y, hy⟩, rfl⟩
  set e₁ : ↥Y' ≃* ↥(Y'.map (slPi π 3 (p ^ f) K).subtype) :=
    Y'.equivMapOfInjective _ (slPi π 3 (p ^ f) K).subtype_injective
  refine ⟨Y'.map (slPi π 3 (p ^ f) K).subtype, Subgroup.map_subtype_le _,
    e₁.symm.trans (MulEquiv.ofBijective f₀ hf₀bij), fun g => ?_⟩
  obtain ⟨y, rfl⟩ := e₁.surjective g
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply]
  rfl

theorem eq_bot_of_perfect_of_invariant [Finite K] [CharP K 2]
    (J : Subgroup (GL (Fin 3) K)) (hJp : Group.IsPerfect J) (hJ3 : ¬ 3 ∣ Nat.card J)
    (W : Submodule K (Fin 3 → K))
    (hW : ∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) (hW0 : W ≠ ⊥)
    (hWt : W ≠ ⊤) : J = ⊥ := by
  have hWdim : Module.finrank K W ≤ 2 := by
    have h1 := Submodule.finrank_lt hWt
    rw [Module.finrank_fin_fun] at h1
    omega
  have hQdim : Module.finrank K ((Fin 3 → K) ⧸ W) ≤ 2 := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
    omega
  have hinv : ∀ g ∈ J, ∀ v ∈ W, Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K) v ∈ W :=
    fun g hg v hv => by rw [Matrix.toLin'_apply]; exact hW g hg v hv
  let baseW : J →* Module.End K W :=
    { toFun := fun g => (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).restrict
        (hinv g g.2)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [Matrix.mulVec_mulVec] }
  have hfixW : ∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    intro g hg v hv
    have h1 := Sec6.BThreeCensus.eq_one_of_finrank_le_two hWdim hJp hJ3 baseW.toHomUnits ⟨g, hg⟩
    have h2 := congrArg (fun u : (Module.End K W)ˣ => ((u : Module.End K W) ⟨v, hv⟩ : Fin 3 → K))
      h1
    simpa [baseW] using h2
  let baseQ : J →* Module.End K ((Fin 3 → K) ⧸ W) :=
    { toFun := fun g => W.mapQ W (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (fun v hv => hinv g g.2 v hv)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp }
  have hfixQ : ∀ g ∈ J, ∀ v : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W := by
    intro g hg v
    have h1 := Sec6.BThreeCensus.eq_one_of_finrank_le_two hQdim hJp hJ3 baseQ.toHomUnits ⟨g, hg⟩
    have h2 := congrArg (fun u : (Module.End K ((Fin 3 → K) ⧸ W))ˣ =>
      ((u : Module.End K ((Fin 3 → K) ⧸ W)) (W.mkQ v))) h1
    simp only [MonoidHom.toHomUnits, baseQ, Units.val_one, Module.End.one_apply] at h2
    change W.mkQ (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) v) = W.mkQ v at h2
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Matrix.toLin'_apply] at h2
    exact h2
  have hsq : ∀ g ∈ J, g * g = 1 := by
    intro g hg
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have h1 := hfixW g hg _ (hfixQ g hg v)
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [Matrix.mulVec_sub] at h1
    simp only [Matrix.toLin'_apply, Units.val_mul, Units.val_one, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    have h3 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        (2 : K) • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) - v := by
      rw [sub_eq_iff_eq_add] at h1
      rw [h1, two_smul]
      abel
    rw [h3, h2, zero_smul, zero_sub]
    funext i
    exact CharTwo.neg_eq _
  have hcomm : ∀ a b : J, a * b = b * a := by
    intro a b
    have hab : (a * b) * (a * b) = 1 := Subtype.ext (hsq _ (a * b).2)
    have ha : a * a = 1 := Subtype.ext (hsq _ a.2)
    have hb : b * b = 1 := Subtype.ext (hsq _ b.2)
    calc a * b = a * (a * b * (a * b)) * b := by rw [hab]; group
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [ha, hb]; group
  have hsolv : Group.IsSolvable J := Group.isSolvable_of_comm hcomm
  exact Sec6.BThreeCensus.eq_bot_of_isPerfect_of_isSolvable hJp hsolv

end ProofKSL3Two

open ProofKSL3Two in
theorem kS1619Perfect_of (hI : KSL3TwoIrrThree) :
    KS1619Perfect := by
  intro X _ _ n hn2 hX J hJp hJ3
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model (by omega) hX
  have := hK.finite
  have : CharP K 2 := hK.charP
  set Y := J.map φ.toMonoidHom with hY
  have hYc : Nat.card Y = Nat.card J := by
    rw [hY, Subgroup.card_map_of_injective φ.injective]
  obtain ⟨Ĵ, -, e, -⟩ := exists_lift_model hK hq Y (by rw [hYc]; exact hJ3)
  have hĴc : Nat.card Ĵ = Nat.card J := by rw [Nat.card_congr e.toEquiv, hYc]
  have hYp : Group.IsPerfect Y := Group.IsPerfect.map _
  have hĴp : Group.IsPerfect Ĵ :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hĴ3 : ¬ 3 ∣ Nat.card Ĵ := by rw [hĴc]; exact hJ3
  have hĴbot : Ĵ = ⊥ := by
    by_contra hne
    by_cases hirr : ∀ W : Submodule K (Fin 3 → K),
        (∀ g ∈ Ĵ, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
    · have hna : ∃ a ∈ Ĵ, ∃ b ∈ Ĵ, a * b ≠ b * a := by
        by_contra hall
        push Not at hall
        have hsolv : Group.IsSolvable Ĵ := Group.isSolvable_of_comm fun a b =>
          Subtype.ext (hall a a.2 b b.2)
        exact hne (Sec6.BThreeCensus.eq_bot_of_isPerfect_of_isSolvable hĴp hsolv)
      exact hĴ3 (hI K Ĵ hirr hna)
    · push Not at hirr
      obtain ⟨W, hW, hW0, hWt⟩ := hirr
      exact hne (eq_bot_of_perfect_of_invariant Ĵ hĴp hĴ3 W hW hW0 hWt)
  have h1 : Nat.card J = 1 := by rw [← hĴc, hĴbot, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq J h1

theorem ks1619LCen_of_irrThree (hI : KSL3TwoIrrThree) :
    KS1619LCen :=
  ks1619LCen_of_perfect (kS1619Perfect_of hI)

end CFSG.RankThree.PartTwo.Sec16
