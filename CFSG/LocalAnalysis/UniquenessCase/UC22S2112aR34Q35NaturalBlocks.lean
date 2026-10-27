module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.Nat.Prime.Factorial
import TauCeti.LinearAlgebra.Dimension.DirectSum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix

section General

variable {k Γ E : Type*} [Field k] [Group Γ] [AddCommGroup E] [Module k E]

private lemma commute_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module k V]
    (h : Module.finrank k V = 1) (f g : V →ₗ[k] V) : f * g = g * f := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h f
  obtain ⟨d, hd, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h g
  rw [hc, hd]
  ext v
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
    mul_comm]

theorem exists_map_eq_of_irreducible {ρ : Representation k Γ E}
    (hirr : ∀ U : Submodule k E, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    {κ : Type*} {W : κ → Submodule k E} (hind : iSupIndep W) (hW0 : ∀ i, W i ≠ ⊥)
    (hperm : ∀ g i, ∃ j, (W i).map (ρ g) = W j) (i j : κ) : ∃ g, (W i).map (ρ g) = W j := by
  classical
  let U : Submodule k E := ⨆ g, (W i).map (ρ g)
  have hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
    intro h v hv
    refine Submodule.iSup_induction (p := fun g => (W i).map (ρ g))
      (motive := fun v => ρ h v ∈ U) hv ?_ ?_ ?_
    · intro g x hx
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
      have hx' : ρ h (ρ g w) = ρ (h * g) w := by
        rw [← Module.End.mul_apply, ← map_mul]
      rw [hx']
      exact Submodule.mem_iSup_of_mem (h * g) (Submodule.mem_map_of_mem hw)
    · simp
    · intro x y hx hy
      simpa [map_add] using Submodule.add_mem U hx hy
  have hWi_le : W i ≤ U := by
    intro x hx
    exact Submodule.mem_iSup_of_mem (1 : Γ) (by simpa using hx)
  have hU0 : U ≠ ⊥ := by
    intro h
    have hle : W i ≤ (⊥ : Submodule k E) := h ▸ hWi_le
    exact hW0 i (le_bot_iff.mp hle)
  have hUtop : U = ⊤ := by
    rcases hirr U hUinv with h | h
    · exact absurd h hU0
    · exact h
  by_contra hno
  have hne : ∀ g, (W i).map (ρ g) ≠ W j := by
    intro g hg
    exact hno ⟨g, hg⟩
  have hUle : U ≤ ⨆ l, ⨆ (_ : l ≠ j), W l := by
    refine iSup_le fun g => ?_
    obtain ⟨l, hl⟩ := hperm g i
    have hlj : l ≠ j := by
      intro h
      exact hne g (by rw [hl, h])
    rw [hl]
    exact le_iSup₂_of_le l hlj le_rfl
  have hWj_le : W j ≤ ⨆ l, ⨆ (_ : l ≠ j), W l := by
    intro x hx
    have hxU : x ∈ U := by
      rw [hUtop]
      exact Submodule.mem_top
    exact hUle hxU
  exact hW0 j (Disjoint.eq_bot_of_le (iSupIndep_def.mp hind j) hWj_le)

theorem finrank_eq_of_irreducible {ρ : Representation k Γ E}
    (hirr : ∀ U : Submodule k E, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    {κ : Type*} {W : κ → Submodule k E} (hind : iSupIndep W) (hW0 : ∀ i, W i ≠ ⊥)
    (hperm : ∀ g i, ∃ j, (W i).map (ρ g) = W j) (i j : κ) :
    Module.finrank k (W i) = Module.finrank k (W j) := by
  obtain ⟨g, hg⟩ := exists_map_eq_of_irreducible hirr hind hW0 hperm i j
  have hinj : Function.Injective (ρ g) := by
    intro x y hxy
    have h := congrArg (ρ g⁻¹) hxy
    simpa [← Module.End.mul_apply, ← map_mul] using h
  rw [← hg]
  exact (Submodule.equivMapOfInjective (ρ g) hinj (W i)).finrank_eq

theorem finite_of_iSupIndep [FiniteDimensional k E] {κ : Type*} {W : κ → Submodule k E}
    (hind : iSupIndep W) (hW0 : ∀ i, W i ≠ ⊥) : Finite κ := by
  have : Fintype {i // W i ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  exact Finite.of_surjective (Subtype.val : {i // W i ≠ ⊥} → κ) fun i => ⟨⟨i, hW0 i⟩, rfl⟩

theorem card_mul_finrank_eq_of_irreducible [FiniteDimensional k E] {ρ : Representation k Γ E}
    (hirr : ∀ U : Submodule k E, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    {κ : Type*} {W : κ → Submodule k E} (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤)
    (hW0 : ∀ i, W i ≠ ⊥) (hperm : ∀ g i, ∃ j, (W i).map (ρ g) = W j) (i : κ) :
    Nat.card κ * Module.finrank k (W i) = Module.finrank k E := by
  classical
  have : Finite κ := finite_of_iSupIndep hind hW0
  let : Fintype κ := Fintype.ofFinite κ
  let : DecidableEq κ := Classical.decEq κ
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hsum : Module.finrank k E = ∑ j : κ, Module.finrank k ↥(W j) :=
    TauCeti.finrank_eq_sum_finrank_of_isInternal hint
  have hconst : ∀ j : κ, Module.finrank k (W i) = Module.finrank k (W j) := fun j =>
    finrank_eq_of_irreducible hirr hind hW0 hperm i j
  calc Nat.card κ * Module.finrank k (W i)
      = Fintype.card κ * Module.finrank k (W i) := by rw [Nat.card_eq_fintype_card]
    _ = ∑ _j : κ, Module.finrank k (W i) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ = ∑ j : κ, Module.finrank k (W j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact hconst j
    _ = Module.finrank k E := hsum.symm

theorem not_dvd_card_of_finrank_eq_one [Finite Γ] {ρ : Representation k Γ E}
    (hρ : Function.Injective ρ) {κ : Type*} [Finite κ] {W : κ → Submodule k E}
    (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤) (hW0 : ∀ i, W i ≠ ⊥)
    (hperm : ∀ g i, ∃ j, (W i).map (ρ g) = W j) (hline : ∀ i, Module.finrank k (W i) = 1)
    {r : ℕ} (hr : r.Prime) (hκ : Nat.card κ < r)
    (hO : ∀ A : Subgroup Γ, A.Normal → IsPGroup r A → A = ⊥) : ¬ r ∣ Nat.card Γ := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  have hWinj : Function.Injective W := by
    intro i j hij
    by_contra hne
    have hle : W i ≤ ⨆ l, ⨆ (_ : l ≠ i), W l := by
      have hji : W j ≤ ⨆ l, ⨆ (_ : l ≠ i), W l :=
        le_iSup₂_of_le j (fun h => hne h.symm) le_rfl
      rwa [← hij] at hji
    exact hW0 i (Disjoint.eq_bot_of_le (iSupIndep_def.mp hind i) hle)
  let σ : Γ → κ → κ := fun g i => Classical.choose (hperm g i)
  have hσ : ∀ g i, (W i).map (ρ g) = W (σ g i) := fun g i => Classical.choose_spec (hperm g i)
  have hσ_one : ∀ i, σ 1 i = i := by
    intro i
    apply hWinj
    have h1 : ρ (1 : Γ) = LinearMap.id := by
      rw [map_one]
      rfl
    rw [← hσ 1 i, h1, Submodule.map_id]
  have hσ_mul : ∀ g h i, σ (g * h) i = σ g (σ h i) := by
    intro g h i
    apply hWinj
    rw [← hσ (g * h) i, ← hσ g (σ h i), ← hσ h i]
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  let π : Γ →* Equiv.Perm κ :=
    { toFun := fun g =>
        { toFun := σ g
          invFun := σ g⁻¹
          left_inv := fun i => by rw [← hσ_mul, inv_mul_cancel, hσ_one]
          right_inv := fun i => by rw [← hσ_mul, mul_inv_cancel, hσ_one] }
      map_one' := by ext i; simpa using hσ_one i
      map_mul' := by intro g h; ext i; simpa [Equiv.Perm.mul_apply] using hσ_mul g h i }
  have hπ : ∀ g i, π g i = σ g i := fun g i => rfl
  have hDmem : ∀ g, g ∈ π.ker ↔ ∀ i, σ g i = i := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h i
      have h1 : (π g) i = (1 : Equiv.Perm κ) i := congrArg (fun e : Equiv.Perm κ => e i) h
      rw [hπ g i] at h1
      simpa using h1
    · intro h
      ext i
      rw [hπ g i]
      simpa using h i
  have hact : ∀ d, d ∈ π.ker → ∀ i, (W i).map (ρ d) = W i := by
    intro d hd i
    rw [hσ d i, (hDmem d).mp hd i]
  have hDcomm : ∀ x ∈ π.ker, ∀ y ∈ π.ker, x * y = y * x := by
    intro x hx y hy
    apply hρ
    rw [map_mul, map_mul]
    ext v
    have hv : v ∈ ⨆ i, W i := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction (p := W)
      (motive := fun v => (ρ x * ρ y) v = (ρ y * ρ x) v) hv ?_ ?_ ?_
    · intro i w hw
      have hxmaps : Set.MapsTo (ρ x) (W i) (W i) := by
        intro a ha
        have ha' := Submodule.mem_map_of_mem (f := ρ x) ha
        rwa [hact x hx i] at ha'
      have hymaps : Set.MapsTo (ρ y) (W i) (W i) := by
        intro a ha
        have ha' := Submodule.mem_map_of_mem (f := ρ y) ha
        rwa [hact y hy i] at ha'
      let fx : ↥(W i) →ₗ[k] ↥(W i) := (ρ x).restrict hxmaps
      let fy : ↥(W i) →ₗ[k] ↥(W i) := (ρ y).restrict hymaps
      have hcf : fx * fy = fy * fx := commute_of_finrank_eq_one (hline i) fx fy
      have hpt := congrArg (fun e : ↥(W i) →ₗ[k] ↥(W i) => (e ⟨w, hw⟩ : ↥(W i))) hcf
      simp only [Module.End.mul_apply] at hpt
      rw [Module.End.mul_apply, Module.End.mul_apply]
      exact congrArg Subtype.val hpt
    · simp
    · intro u v hu hv
      rw [map_add, map_add, hu, hv]
  have hcard : Nat.card Γ = Nat.card (Γ ⧸ π.ker) * Nat.card π.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have hdvdquot : Nat.card (Γ ⧸ π.ker) ∣ (Nat.card κ).factorial := by
    have h := Subgroup.card_dvd_of_injective (QuotientGroup.kerLift π) (QuotientGroup.kerLift_injective π)
    simpa [Nat.card_perm] using h
  have hnotdvd_fact : ¬ r ∣ (Nat.card κ).factorial := by
    rw [Nat.Prime.dvd_factorial hr, not_le]
    exact hκ
  have hnotdvdquot : ¬ r ∣ Nat.card (Γ ⧸ π.ker) := fun h =>
    hnotdvd_fact (dvd_trans h hdvdquot)
  have : Fact r.Prime := ⟨hr⟩
  let D : Subgroup Γ := π.ker
  let : CommGroup D :=
    { (inferInstance : Group D) with mul_comm := fun x y => Subtype.ext (hDcomm x x.2 y y.2) }
  let A' : Subgroup D := CommGroup.primaryComponent D r
  let A : Subgroup Γ := A'.map D.subtype
  have hAp : IsPGroup r A := (CommGroup.primaryComponent.isPGroup (G := D) (p := r)).map D.subtype
  have hAnorm : A.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    rw [Subgroup.mem_map] at hn ⊢
    obtain ⟨d, hdA', hdn⟩ := hn
    have hconj : g * (d : Γ) * g⁻¹ ∈ D :=
      Subgroup.Normal.conj_mem (MonoidHom.normal_ker π) d d.2 g
    refine ⟨⟨g * (d : Γ) * g⁻¹, hconj⟩, ?_, ?_⟩
    · rw [CommGroup.mem_primaryComponent] at hdA' ⊢
      obtain ⟨k, hk⟩ := hdA'
      refine ⟨k, ?_⟩
      apply Subtype.ext
      push_cast
      have hk' : (d : Γ) ^ (r ^ k) = 1 := by
        have := congrArg (fun z : D => (z : Γ)) hk
        simpa using this
      rw [conj_pow, hk']
      simp
    · rw [← hdn]
      rfl
  intro hrdvd
  have hdvdD : r ∣ Nat.card D := by
    have h := (Nat.Prime.dvd_mul hr).mp (hcard ▸ hrdvd)
    rcases h with h | h
    · exact absurd h hnotdvdquot
    · exact h
  have : Fintype D := Fintype.ofFinite D
  have hdvdD' : r ∣ Fintype.card D := by rwa [Nat.card_eq_fintype_card] at hdvdD
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card (G := D) r hdvdD'
  have hxpow : x ^ r = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hxA' : x ∈ A' := by
    rw [CommGroup.mem_primaryComponent]
    exact ⟨1, by simpa using hxpow⟩
  have hxA : D.subtype x ∈ A := Subgroup.mem_map_of_mem (f := D.subtype) hxA'
  have hxne : (D.subtype x : Γ) ≠ 1 := by
    intro h
    have hx1 : x = 1 := Subtype.ext (by simpa using h)
    have h1 : orderOf x = 1 := by rw [hx1]; exact orderOf_one
    rw [hxord] at h1
    exact hr.ne_one h1
  have hAbot : A = ⊥ := hO A hAnorm hAp
  rw [hAbot] at hxA
  exact hxne (Subgroup.mem_bot.mp hxA)

end General

section Natural

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] noncomputable def glRep (L : Type*) [Field L] [Algebra K L] :
    Representation L (GL ι K) (ι → L) where
  toFun g := Matrix.toLin' ((g : Matrix ι ι K).map (algebraMap K L))
  map_one' := by
    rw [Units.val_one, Matrix.map_one (algebraMap K L) (map_zero _) (map_one _),
      Matrix.toLin'_one, Module.End.one_eq_id]
  map_mul' g h := by
    rw [Units.val_mul, Matrix.map_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

theorem glRep_apply (L : Type*) [Field L] [Algebra K L] (g : GL ι K) (v : ι → L) :
    glRep L g v = ((g : Matrix ι ι K).map (algebraMap K L)) *ᵥ v := by
  exact Matrix.toLin'_apply ((g : Matrix ι ι K).map (algebraMap K L)) v

theorem glRep_injective (L : Type*) [Field L] [Algebra K L] :
    Function.Injective (glRep (ι := ι) (K := K) L) := by
  intro g h hgh
  have hM : (g : Matrix ι ι K).map (algebraMap K L) = (h : Matrix ι ι K).map (algebraMap K L) := by
    apply Matrix.toLin'.injective
    simpa [glRep] using hgh
  exact Units.ext (Matrix.map_injective (algebraMap K L).injective hM)

theorem eq_bot_or_eq_top_of_adjoin_eq_top {α : Type*} (f : α → GL ι K)
    (hf : Algebra.adjoin K (Set.range fun a => (f a : Matrix ι ι K)) = ⊤)
    (L : Type*) [Field L] [Algebra K L] (U : Submodule L (ι → L))
    (hU : ∀ a, ∀ u ∈ U, glRep L (f a) u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  let S : Subalgebra K (Matrix ι ι K) :=
    { carrier := {M | ∀ u ∈ U, M.map (algebraMap K L) *ᵥ u ∈ U}
      mul_mem' := by
        intro M N hM hN u hu
        rw [Matrix.map_mul, ← Matrix.mulVec_mulVec]
        exact hM _ (hN u hu)
      one_mem' := by
        intro u hu
        rw [Matrix.map_one (algebraMap K L) (map_zero _) (map_one _), Matrix.one_mulVec]
        exact hu
      add_mem' := by
        intro M N hM hN u hu
        rw [Matrix.map_add (algebraMap K L) (map_add _), Matrix.add_mulVec]
        exact Submodule.add_mem U (hM u hu) (hN u hu)
      zero_mem' := by
        intro u _
        rw [Matrix.map_zero (algebraMap K L) (map_zero _), Matrix.zero_mulVec]
        exact Submodule.zero_mem U
      algebraMap_mem' := by
        intro c u hu
        have hmap : (algebraMap K (Matrix ι ι K) c).map (algebraMap K L)
            = c • (1 : Matrix ι ι L) := by
          rw [Algebra.algebraMap_eq_smul_one,
            Matrix.map_smul (algebraMap K L) c (fun a => by simp [Algebra.smul_def]),
            Matrix.map_one (algebraMap K L) (map_zero _) (map_one _)]
        rw [hmap, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [← algebraMap_smul L c u]
        exact Submodule.smul_mem U (algebraMap K L c) hu }
  have hS : S = ⊤ := by
    have hle : Algebra.adjoin K (Set.range fun a => (f a : Matrix ι ι K)) ≤ S := by
      refine Algebra.adjoin_le ?_
      rintro M ⟨a, rfl⟩
      exact hU a
    rw [hf] at hle
    exact top_le_iff.mp hle
  have hunit : ∀ i j, Matrix.single i j (1 : K) ∈ S := by
    intro i j
    rw [hS]
    trivial
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    obtain ⟨u, huU, hu0⟩ := (Submodule.ne_bot_iff U).mp hbot
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra h
      exact hu0 (funext fun j => by simpa using not_exists.mp h j)
    have hsingle : ∀ i, Pi.single i (1 : L) ∈ U := by
      intro i
      have hmem : (Matrix.single i j (1 : K)).map (algebraMap K L) *ᵥ u ∈ U :=
        hunit i j u huU
      have hcalc : (Matrix.single i j (1 : K)).map (algebraMap K L) *ᵥ u
          = u j • Pi.single i (1 : L) := by
        rw [Matrix.map_single, map_one, Matrix.single_mulVec, one_mul]
        ext k
        simp [Pi.single_apply, Function.update_apply]
      rw [hcalc] at hmem
      have := Submodule.smul_mem U ((u j)⁻¹) hmem
      simpa [inv_smul_smul₀ hj] using this
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = ∑ i, v i • Pi.single i (1 : L) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfun : (fun j => if i = j then (1 : L) else 0) = Pi.single i (1 : L) := by
        funext k
        simp [Pi.single_apply, eq_comm]
      rw [hfun]
    rw [hv]
    exact Submodule.sum_mem U fun i _ => Submodule.smul_mem U (v i) (hsingle i)

end Natural

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
