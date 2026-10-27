module

public import CFSG.RankThree.GF2n.Stroth80.Sec310SLTransv
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open scoped Matrix

private theorem sld_det_one_add_vecMulVec {m : ℕ} {K : Type} [Field K] (u f : Fin m → K) :
    (1 + Matrix.vecMulVec u f).det = 1 + f ⬝ᵥ u := by
  have h : Matrix.vecMulVec u f = Matrix.replicateCol Unit u * Matrix.replicateRow Unit f := by
    ext a b
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]

private theorem sld_exists_row_of_dual {m : ℕ} {K : Type} [Field K] (φ : (Fin m → K) →ₗ[K] K) :
    ∃ r : Fin m → K, ∀ x : Fin m → K, r ⬝ᵥ x = φ x := by
  refine ⟨fun j => φ (Pi.single j 1), fun x => ?_⟩
  have hx : x = ∑ j, x j • (Pi.single j (1 : K) : Fin m → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private def SldCentre {m : ℕ} {K : Type} [Field K] (X : Subgroup (GL (Fin m) K))
    (v : Fin m → K) : Prop :=
  ∀ f : Fin m → K, f ⬝ᵥ v = 0 →
    ∃ g ∈ X, (g : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec v f

private theorem sldCentre_zero {m : ℕ} {K : Type} [Field K] (X : Subgroup (GL (Fin m) K)) :
    SldCentre X 0 := by
  intro f _
  exact ⟨1, X.one_mem, by simp⟩

private theorem sldCentre_smul {m : ℕ} {K : Type} [Field K] {X : Subgroup (GL (Fin m) K)} (c : K)
    {v : Fin m → K} (hv : SldCentre X v) : SldCentre X (c • v) := by
  intro f hf
  have h1 : (c • f) ⬝ᵥ v = 0 := by
    rw [smul_dotProduct, ← dotProduct_smul]
    exact hf
  obtain ⟨g, hgX, hg⟩ := hv (c • f) h1
  refine ⟨g, hgX, ?_⟩
  rw [hg, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]

private theorem sldCentre_invariant {m : ℕ} {K : Type} [Field K] {X : Subgroup (GL (Fin m) K)}
    {h : GL (Fin m) K} (hh : h ∈ X) {v : Fin m → K} (hv : SldCentre X v) :
    SldCentre X ((h : Matrix (Fin m) (Fin m) K) *ᵥ v) := by
  intro f hf
  have hf' : (f ᵥ* (h : Matrix (Fin m) (Fin m) K)) ⬝ᵥ v = 0 := by
    rw [← Matrix.dotProduct_mulVec]
    exact hf
  obtain ⟨g, hgX, hg⟩ := hv _ hf'
  refine ⟨h * g * h⁻¹, X.mul_mem (X.mul_mem hh hgX) (X.inv_mem hh), ?_⟩
  have hcomm : (h : Matrix (Fin m) (Fin m) K) *
      (1 + Matrix.vecMulVec v (f ᵥ* (h : Matrix (Fin m) (Fin m) K))) =
      (1 + Matrix.vecMulVec ((h : Matrix (Fin m) (Fin m) K) *ᵥ v) f) *
        (h : Matrix (Fin m) (Fin m) K) := by
    rw [mul_add, mul_one, Matrix.mul_vecMulVec, add_mul, one_mul, Matrix.vecMulVec_mul]
  rw [Units.val_mul, Units.val_mul, hg, hcomm, mul_assoc, Units.mul_inv, mul_one]

private theorem sldCentre_add {m : ℕ} {K : Type} [Field K] {X : Subgroup (GL (Fin m) K)}
    {v w : Fin m → K} (hv : SldCentre X v) (hw : SldCentre X w) :
    SldCentre X (v + w) := by
  by_cases hvw : v ∈ Submodule.span K {w}
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvw
    have h1 : c • w + w = (c + 1) • w := by rw [add_smul, one_smul]
    rw [h1]
    exact sldCentre_smul (c + 1) hw
  · obtain ⟨φ, hφv, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvw inferInstance
    have hφw : φ w = 0 := by
      have h1 : φ w ∈ Submodule.map φ (Submodule.span K {w}) :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w)
      rw [hφp] at h1
      exact (Submodule.mem_bot K).mp h1
    obtain ⟨r, hr⟩ := sld_exists_row_of_dual φ
    have hg'v : ((φ v)⁻¹ • r) ⬝ᵥ v = 1 := by
      rw [smul_dotProduct, hr, smul_eq_mul, inv_mul_cancel₀ hφv]
    have hg'w : ((φ v)⁻¹ • r) ⬝ᵥ w = 0 := by
      rw [smul_dotProduct, hr, hφw, smul_zero]
    obtain ⟨h, hhX, hh⟩ := hw _ hg'w
    have hinv := sldCentre_invariant hhX hv
    rw [hh, mulVec_one_add_vecMulVec, hg'v, one_smul] at hinv
    exact hinv

theorem eq_statedSL_of_full_centre {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (X : Subgroup (GL (Fin m) K)) (hirr : NatIrred X) (hgen : GenByTransvLines X)
    (Λ : Subgroup (GL (Fin m) K)) (hΛX : Λ ≤ X) {u : Fin m → K} (hu : u ≠ 0)
    (hΛ : ∀ g ∈ Λ, ∀ x, ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u)
    (hcard : Nat.card K ^ (m - 1) ≤ Nat.card Λ) : X = StatedSL m K := by
  classical
  have hX1 : X ≤ StatedSL m K := by
    unfold GenByTransvLines at hgen
    rw [hgen, Subgroup.closure_le]
    rintro g ⟨v, f, -, -, hfv, hg, -⟩
    refine StatedAPI.mem_statedSL_of_det ?_
    rw [hg, sld_det_one_add_vecMulVec, hfv, add_zero]
  have hdet : ∀ g ∈ X, (g : Matrix (Fin m) (Fin m) K).det = 1 := fun g hg =>
    StatedAPI.det_of_mem_statedSL (hX1 hg)
  have hex : ∀ g : Λ, ∃ f : Fin m → K,
      ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u f :=
    fun g => exists_vecMulVec_of_sub_smul (fun x => hΛ (g : GL (Fin m) K) g.2 x)
  choose F hF using hex
  have hFdot : ∀ g : Λ, F g ⬝ᵥ u = 0 := by
    intro g
    have h1 := hdet _ (hΛX g.2)
    rw [hF g, sld_det_one_add_vecMulVec] at h1
    linear_combination h1
  let Φ : Λ → {f : Fin m → K // f ⬝ᵥ u = 0} := fun g => ⟨F g, hFdot g⟩
  have hΦinj : Function.Injective Φ := by
    intro g g' hgg'
    have hF' : F g = F g' := congrArg Subtype.val hgg'
    apply Subtype.ext
    apply Units.ext
    rw [hF g, hF g', hF']
  have hcardΛ : Nat.card {f : Fin m → K // f ⬝ᵥ u = 0} = Nat.card Λ :=
    le_antisymm (by rw [card_dotProduct_ker hu]; exact hcard)
      (Nat.card_le_card_of_injective Φ hΦinj)
  have hbij : Function.Bijective Φ :=
    (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hΦinj, hcardΛ.symm⟩
  have hfull : SldCentre X u := by
    intro f hf
    obtain ⟨g, hg⟩ := hbij.2 ⟨f, hf⟩
    have hFg : F g = f := congrArg Subtype.val hg
    refine ⟨(g : GL (Fin m) K), hΛX g.2, ?_⟩
    rw [← hFg]
    exact hF g
  obtain ⟨S, hSmem⟩ : ∃ S : Submodule K (Fin m → K), ∀ v, v ∈ S ↔ SldCentre X v :=
    ⟨{ carrier := {v | SldCentre X v}
       add_mem' := fun {v w} hv hw => sldCentre_add hv hw
       zero_mem' := sldCentre_zero X
       smul_mem' := fun c {v} hv => sldCentre_smul c hv }, fun v => Iff.rfl⟩
  have hinvS : ∀ g ∈ X, ∀ x ∈ S, (g : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ S :=
    fun g hg x hx => (hSmem _).mpr (sldCentre_invariant hg ((hSmem x).mp hx))
  rcases hirr S hinvS with hbot | htop
  · exfalso
    have huS : u ∈ S := (hSmem u).mpr hfull
    rw [hbot, Submodule.mem_bot] at huS
    exact hu huS
  have hall : ∀ v, SldCentre X v :=
    fun v => (hSmem v).mp (by rw [htop]; exact Submodule.mem_top)
  have htrans : ∀ (i j : Fin m) (hij : i ≠ j) (c : K),
      Matrix.SpecialLinearGroup.transvection hij c ∈
        X.comap (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K) := by
    intro i j hij c
    have hdot : Pi.single j (1 : K) ⬝ᵥ (Pi.single i c : Fin m → K) = 0 := by
      rw [single_dotProduct, one_mul, Pi.single_apply, if_neg (Ne.symm hij)]
    obtain ⟨g, hgX, hg⟩ := hall (Pi.single i c) _ hdot
    have hmat : Matrix.single i j c =
        Matrix.vecMulVec (Pi.single i c) (Pi.single j (1 : K)) := by
      ext a b
      simp [Matrix.single, Matrix.vecMulVec_apply, Pi.single_apply, eq_comm]
      split_ifs <;> simp_all
    rw [Subgroup.mem_comap]
    have heq : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) :
        GL (Fin m) K) = g := by
      apply Units.ext
      show (Matrix.transvection i j c : Matrix (Fin m) (Fin m) K) = (g : Matrix (Fin m) (Fin m) K)
      rw [hg, Matrix.transvection, hmat]
    rw [heq]
    exact hgX
  have hSX : StatedSL m K ≤ X := by
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    have htop' := CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
      (X.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K)) htrans
    rw [StatedAPI.statedSL_eq_range_toGL]
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ X.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K) := by
      rw [htop']
      exact Subgroup.mem_top y
    exact Subgroup.mem_comap.mp hy
  exact le_antisymm hX1 hSX

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth310SLBranch_of_transv (hT : Stroth310SLTransvStatement) :
    Stroth310SLBranchStatement := by
  intro G _ _ M Q Z B hc n t hs hR hV
  obtain ⟨K, _, _, _, hK, m, hm, φ, hker, hsec, hirr, hgen, ⟨u, hu, hel⟩, hcount⟩ :=
    hT G M Q Z B hc n t hs hR hV
  have hΛX : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ ≤ φ.range :=
    Subgroup.map_le_range _ _
  have hΛ : ∀ g ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ, ∀ x : Fin m → K,
      ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u := by
    rintro g ⟨l, hl, rfl⟩ x
    exact hel l (Subgroup.mem_subgroupOf.mp hl) x
  have hsl := eq_statedSL_of_full_centre hm φ.range hirr hgen _ hΛX hu hΛ hcount
  exact ⟨K, inferInstance, inferInstance, hK, m, hm, φ, hsl, hker, hsec⟩

end CFSG.RankThree.GF2n.Stroth80
