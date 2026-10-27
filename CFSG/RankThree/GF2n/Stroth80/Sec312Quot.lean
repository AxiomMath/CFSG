module

public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.RankThree.GF2n.Stroth80.Sec310Symp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem statedSL_le_of_transvection_mem {k : ℕ} (hk : 2 ≤ k) {K : Type} [Field K]
    (S : Subgroup (GL (Fin k) K))
    (h : ∀ (i j : Fin k) (_ : i ≠ j) (c : K), ∃ g ∈ S,
      (g : Matrix (Fin k) (Fin k) K) = Matrix.transvection i j c) :
    StatedSL k K ≤ S := by
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  have htop := CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
    (S.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K)) (by
    intro i j hij c
    obtain ⟨g, hgS, hg⟩ := h i j hij c
    rw [Subgroup.mem_comap]
    have heq : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) :
        GL (Fin k) K) = g := by
      apply Units.ext
      exact hg.symm
    rw [heq]
    exact hgS)
  rw [statedSL_eq_range_toGL]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ S.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K) := by
    rw [htop]
    exact Subgroup.mem_top y
  exact Subgroup.mem_comap.mp hy


theorem normal_pGroup_le_center_of_quasisimple {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (T : Subgroup X) [T.Normal] (hT : IsPGroup 2 T) :
    T ≤ Subgroup.center X := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  haveI := hsimple
  set N' : Subgroup (X ⧸ Subgroup.center X) :=
    T.map (QuotientGroup.mk' (Subgroup.center X)) with hN'
  haveI : N'.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h | h
  · intro t ht
    have h1 : QuotientGroup.mk' (Subgroup.center X) t ∈ N' := Subgroup.mem_map_of_mem _ ht
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff t).mp h1
  · exfalso
    have hpN : IsPGroup 2 N' := IsPGroup.map hT _
    have hpg : IsPGroup 2 (X ⧸ Subgroup.center X) := by
      rw [h] at hpN
      exact hpN.of_equiv Subgroup.topEquiv
    haveI : Nontrivial (X ⧸ Subgroup.center X) :=
      ⟨⟨a, 1, fun h1 => hab (by rw [h1]; simp)⟩⟩
    haveI := hpg.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ Subgroup.center X)) with
      h2 | h2
    · exact (Subgroup.center (X ⧸ Subgroup.center X)).nontrivial_iff_ne_bot.mp inferInstance h2
    · have ha : a ∈ Subgroup.center (X ⧸ Subgroup.center X) := by rw [h2]; trivial
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem normal_pGroup_statedSL_eq_bot {k : ℕ} (hk : 2 ≤ k) {K : Type} [Field K] [Finite K]
    [CharP K 2] (h4 : 4 ≤ Nat.card K) (T : Subgroup ↥(StatedSL k K)) [T.Normal]
    (hT : IsPGroup 2 T) : T = ⊥ := by
  have hq := statedSL_quasisimple_of_card k K hk h4
  have hle := normal_pGroup_le_center_of_quasisimple hq T hT
  rw [eq_bot_iff]
  intro g hg
  have hgc := hle hg
  set e := specialLinearGroupEquivStatedSL k K with he
  have hAc : e.symm g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin k) K) := by
    rw [Subgroup.mem_center_iff] at hgc ⊢
    intro B
    have := hgc (e B)
    have h2 := congrArg e.symm this
    simpa using h2
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAc
  obtain ⟨j, hj⟩ := hT ⟨g, hg⟩
  have hj' : g ^ 2 ^ j = 1 := by
    have := congrArg (fun z : T => ((z : ↥(StatedSL k K)) : ↥(StatedSL k K))) hj
    simpa using this
  have hA : (e.symm g) ^ 2 ^ j = 1 := by
    rw [← map_pow, hj', map_one]
  have hr2 : r ^ 2 ^ j = 1 := by
    have h1 : (((e.symm g) ^ 2 ^ j : Matrix.SpecialLinearGroup (Fin k) K) :
        Matrix (Fin k) (Fin k) K) = 1 := by
      rw [hA]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow] at h1
    have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h2
  have hr1 : r = 1 := by
    have h1 : (r - 1) ^ 2 ^ j = 0 := by
      rw [sub_pow_char_pow, hr2, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)
  have h3 : e.symm g = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have h4 : g = 1 := by simpa using congrArg e h3
  rw [h4]
  exact Subgroup.one_mem _

theorem quotSat_isSLModel_of_restrict
    {G : Type} [Group G] [Finite G] (S : Subgroup G)
    {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {V : Type} [AddCommGroup V] [Module K V] (W : Submodule K V) {k : ℕ} (hk : 2 ≤ k)
    (b : Module.Basis (Fin k) K W)
    (ρ : ↥S →* (V ≃ₗ[K] V)) (hW : ∀ (s : ↥S), ∀ w ∈ W, ρ s w ∈ W)
    (hdet : ∀ s : ↥S, ((b.toGL (actionOnSubspace ρ W hW s) : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K).det = 1)
    (htrans : ∀ (i j : Fin k), i ≠ j → ∀ c : K, ∃ s : ↥S,
      ((b.toGL (actionOnSubspace ρ W hW s) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        Matrix.transvection i j c)
    (hker : ∀ s : ↥S, b.toGL (actionOnSubspace ρ W hW s) = 1 → ∃ j : ℕ, s ^ 2 ^ j = 1) :
    QuotSat S (inSubgroup (pCore 2) S) (IsSLModel k (Nat.card K)) := by
  classical
  let θ : ↥S →* GL (Fin k) K := b.toGL.toMonoidHom.comp (actionOnSubspace ρ W hW)
  have hθ : ∀ s, θ s = b.toGL (actionOnSubspace ρ W hW s) := fun s => rfl
  have hrange : θ.range = StatedSL k K := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact mem_statedSL_of_det (hdet s)
    · exact statedSL_le_of_transvection_mem hk θ.range (fun i j hij c => by
        obtain ⟨s, hs⟩ := htrans i j hij c
        exact ⟨θ s, ⟨s, rfl⟩, hs⟩)
  let θ' : ↥S →* ↥(StatedSL k K) :=
    θ.codRestrict (StatedSL k K) (fun s => hrange ▸ ⟨s, rfl⟩)
  have hθ' : ∀ s, ((θ' s : ↥(StatedSL k K)) : GL (Fin k) K) = θ s := fun s => rfl
  have hsurj : Function.Surjective θ' := by
    intro y
    have hy : (y : GL (Fin k) K) ∈ θ.range := by rw [hrange]; exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext (by rw [hθ', hs])⟩
  have hkerp : IsPGroup 2 θ'.ker := by
    intro x
    have hx1 : θ x = 1 := by
      have := x.2
      rw [MonoidHom.mem_ker] at this
      have h2 := congrArg (fun z : ↥(StatedSL k K) => (z : GL (Fin k) K)) this
      simpa [hθ'] using h2
    obtain ⟨j, hj⟩ := hker (x : ↥S) hx1
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  have hker_eq : θ'.ker = pCore 2 ↥S := by
    apply le_antisymm
    · exact le_sSup ⟨θ'.normal_ker, hkerp⟩
    · have hn : ((pCore 2 ↥S).map θ').Normal := Subgroup.Normal.map pCore_normal θ' hsurj
      have hp : IsPGroup 2 ↥((pCore 2 ↥S).map θ') := IsPGroup.map pCore_isPGroup θ'
      have hbot := normal_pGroup_statedSL_eq_bot hk h4 ((pCore 2 ↥S).map θ') hp
      exact (Subgroup.map_eq_bot_iff _).mp hbot
  have hO : (inSubgroup (pCore 2) S).subgroupOf S = pCore 2 ↥S := by
    unfold inSubgroup
    exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  haveI hn : ((inSubgroup (pCore 2) S).subgroupOf S).Normal := by
    rw [hO]
    exact pCore_normal
  refine ⟨hn, K, inferInstance, inferInstance, rfl, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq (hO.trans hker_eq.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ' hsurj)

theorem toGL_entry {ι : Type} [Fintype ι] [DecidableEq ι] {K W : Type} [Field K]
    [AddCommGroup W] [Module K W] (b : Module.Basis ι K W) (f : W ≃ₗ[K] W) (i j : ι) :
    ((b.toGL f : GL ι K) : Matrix ι ι K) i j = b.repr (f (b j)) i := by
  have h := toGL_mulVec_equivFun b f (b j)
  have h0 : b.equivFun (b j) = Pi.single j (1 : K) := by
    funext a
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [h0, Matrix.mulVec_single_one] at h
  have h2 := congrFun h i
  simpa using h2

@[expose] noncomputable def matToLin {m : ℕ} {K : Type} [Field K] :
    GL (Fin m) K ≃* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
  (Pi.basisFun K (Fin m)).toGL.symm

theorem matToLin_apply {m : ℕ} {K : Type} [Field K] (g : GL (Fin m) K) (v : Fin m → K) :
    matToLin g v = (g : Matrix (Fin m) (Fin m) K) *ᵥ v := by
  have h := toGL_mulVec_equivFun (Pi.basisFun K (Fin m)) (matToLin g) v
  have hg : (Pi.basisFun K (Fin m)).toGL (matToLin g) = g := by
    unfold matToLin
    exact MulEquiv.apply_symm_apply _ g
  rw [hg] at h
  simpa using h.symm

section Centres

private theorem ec_exists_row_of_dual {m : ℕ} {K : Type} [Field K] (φ : (Fin m → K) →ₗ[K] K) :
    ∃ r : Fin m → K, ∀ x : Fin m → K, r ⬝ᵥ x = φ x := by
  refine ⟨fun j => φ (Pi.single j 1), fun x => ?_⟩
  have hx : x = ∑ j, x j • (Pi.single j (1 : K) : Fin m → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private def EcCentre {m : ℕ} {K : Type} [Field K] (X : Subgroup (GL (Fin m) K))
    (v : Fin m → K) : Prop :=
  ∀ f : Fin m → K, f ⬝ᵥ v = 0 →
    ∃ g ∈ X, (g : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec v f

private theorem ecCentre_zero {m : ℕ} {K : Type} [Field K] (X : Subgroup (GL (Fin m) K)) :
    EcCentre X 0 := by
  intro f _
  exact ⟨1, X.one_mem, by simp⟩

private theorem ecCentre_smul {m : ℕ} {K : Type} [Field K] {X : Subgroup (GL (Fin m) K)} (c : K)
    {v : Fin m → K} (hv : EcCentre X v) : EcCentre X (c • v) := by
  intro f hf
  have h1 : (c • f) ⬝ᵥ v = 0 := by
    rw [smul_dotProduct, ← dotProduct_smul]
    exact hf
  obtain ⟨g, hgX, hg⟩ := hv (c • f) h1
  refine ⟨g, hgX, ?_⟩
  rw [hg, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]

private theorem ecCentre_invariant {m : ℕ} {K : Type} [Field K] {X : Subgroup (GL (Fin m) K)}
    {h : GL (Fin m) K} (hh : h ∈ X) {v : Fin m → K} (hv : EcCentre X v) :
    EcCentre X ((h : Matrix (Fin m) (Fin m) K) *ᵥ v) := by
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

private theorem ecCentre_add {m : ℕ} {K : Type} [Field K] {X : Subgroup (GL (Fin m) K)}
    {v w : Fin m → K} (hv : EcCentre X v) (hw : EcCentre X w) : EcCentre X (v + w) := by
  by_cases hvw : v ∈ Submodule.span K {w}
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvw
    have h1 : c • w + w = (c + 1) • w := by rw [add_smul, one_smul]
    rw [h1]
    exact ecCentre_smul (c + 1) hw
  · obtain ⟨φ, hφv, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvw inferInstance
    have hφw : φ w = 0 := by
      have h1 : φ w ∈ Submodule.map φ (Submodule.span K {w}) :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w)
      rw [hφp] at h1
      exact (Submodule.mem_bot K).mp h1
    obtain ⟨r, hr⟩ := ec_exists_row_of_dual φ
    have hg'v : ((φ v)⁻¹ • r) ⬝ᵥ v = 1 := by
      rw [smul_dotProduct, hr, smul_eq_mul, inv_mul_cancel₀ hφv]
    have hg'w : ((φ v)⁻¹ • r) ⬝ᵥ w = 0 := by
      rw [smul_dotProduct, hr, hφw, smul_zero]
    obtain ⟨h, hhX, hh⟩ := hw _ hg'w
    have hinv := ecCentre_invariant hhX hv
    rw [hh, mulVec_one_add_vecMulVec, hg'v, one_smul] at hinv
    exact hinv

theorem exists_elation_of_mem_span_centres {K : Type} [Field K] {m : ℕ}
    (Γ : Subgroup (GL (Fin m) K)) (U : Set (Fin m → K))
    (hU : ∀ u ∈ U, ∀ f : Fin m → K, f ⬝ᵥ u = 0 →
      ∃ g ∈ Γ, (g : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u f) :
    ∀ w ∈ Submodule.span K U, ∀ f : Fin m → K, f ⬝ᵥ w = 0 →
      ∃ g ∈ Γ, (g : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec w f := by
  let S : Submodule K (Fin m → K) :=
    { carrier := {v | EcCentre Γ v}
      add_mem' := fun {v w} hv hw => ecCentre_add hv hw
      zero_mem' := ecCentre_zero Γ
      smul_mem' := fun c {v} hv => ecCentre_smul c hv }
  have hUS : Submodule.span K U ≤ S := Submodule.span_le.mpr fun u hu => hU u hu
  exact fun w hw => hUS hw

end Centres

end CFSG.RankThree.GF2n.Stroth80
