module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofBlock

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LieType.SeitzGeneration
open Matrix

namespace Item424Res5

section Linear

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem isCompl_ker_sub_one_ker_norm (h3 : (3 : K) ≠ 0) {X : V →ₗ[K] V}
    (hX : ∀ v, X (X (X v)) = v) :
    IsCompl (LinearMap.ker (X - 1)) (LinearMap.ker (1 + X + X * X)) := by
  have hmem1 : ∀ v, v ∈ LinearMap.ker (X - 1) ↔ X v = v := fun v => by
    simp [LinearMap.mem_ker, sub_eq_zero]
  have hmem2 : ∀ v, v ∈ LinearMap.ker (1 + X + X * X) ↔ v + X v + X (X v) = 0 := fun v => by
    simp [LinearMap.mem_ker]
  refine IsCompl.of_eq ?_ ?_
  · rw [eq_bot_iff]
    intro v ⟨h1, h2⟩
    rw [SetLike.mem_coe, hmem1] at h1
    rw [SetLike.mem_coe, hmem2, h1, h1] at h2
    have h3v : (3 : K) • v = 0 := by rw [← h2]; module
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h3v).resolve_left h3)
  · rw [Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_sup]
    refine ⟨(3 : K)⁻¹ • (v + X v + X (X v)), ?_, (3 : K)⁻¹ • ((2 : K) • v - X v - X (X v)), ?_, ?_⟩
    · rw [hmem1, map_smul, map_add, map_add, hX]
      congr 1
      abel
    · rw [hmem2]
      simp only [map_smul, map_sub, hX]
      module
    · have : (3 : K)⁻¹ * 3 = 1 := inv_mul_cancel₀ h3
      linear_combination (norm := module) this • v

theorem linearIndependent_pair_of_norm (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0) {X : V →ₗ[K] V}
    {v : V} (hv : v ≠ 0) (hn : v + X v + X (X v) = 0) : LinearIndependent K ![v, X v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hv, rfl⟩
  · exfalso
    have hXv : X v = (-(s / t)) • v := by
      have : t • X v = -(s • v) := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hst
      have h2 : X v = t⁻¹ • (t • X v) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    have hXXv : X (X v) = (-(s / t)) ^ 2 • v := by
      rw [hXv, map_smul, hXv, smul_smul, pow_two]
    rw [hXXv, hXv] at hn
    have h1 : ((-(s / t)) ^ 2 + (-(s / t)) + 1) • v = 0 := by
      rw [← hn]
      module
    exact hK (-(s / t)) ((smul_eq_zero.mp h1).resolve_right hv)

theorem le_finrank_of_linearIndependent [FiniteDimensional K V] {S : Submodule K V} {k : ℕ}
    {f : Fin k → V} (hf : LinearIndependent K f) (hS : ∀ i, f i ∈ S) : k ≤ Module.finrank K S := by
  have : LinearIndependent K (fun i => (⟨f i, hS i⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hf
  simpa using this.fintype_card_le_finrank

theorem eq_zero_of_add_eq_zero {U W : Submodule K V} (hUW : Disjoint U W) {x y : V} (hx : x ∈ U)
    (hy : y ∈ W) (hxy : x + y = 0) : x = 0 := by
  have hy' : y = -x := eq_neg_of_add_eq_zero_right hxy
  exact Submodule.disjoint_def.mp hUW x hx (by rw [← neg_neg x, ← hy']; exact W.neg_mem hy)

end Linear

section Blocks

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {G : Type*} [Group G]

theorem exists_blockBasis_sl (hV : Module.finrank K V = 4) (h3 : (3 : K) ≠ 0)
    (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0) (ρ : G → Module.End K V)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h) (hone : ρ 1 = 1) (hinj : ∀ x, ρ x = 1 → x = 1)
    {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ u w : V, u + ρ a u + ρ a (ρ a u) = 0 ∧ ρ a w = w ∧
      ρ a (ρ b w) = ρ b w ∧ ρ b u = u ∧ ρ b (ρ a u) = ρ a u ∧ w + ρ b w + ρ b (ρ b w) = 0 ∧
      LinearIndependent K ![u, ρ a u, w, ρ b w] := by
  have hcomp : ∀ g h v, ρ (g * h) v = ρ g (ρ h v) := fun g h v => by
    rw [hmul, Module.End.mul_apply]
  have hcube : ∀ g : G, g ^ 3 = 1 → ∀ v, ρ g (ρ g (ρ g v)) = v := fun g hg v => by
    have h : g * g * g = 1 := by rw [← pow_three']; exact hg
    rw [← hcomp, ← hcomp, h, hone]
    rfl
  have hcommρ : ∀ x ∈ E, ∀ y ∈ E, ∀ v, ρ x (ρ y v) = ρ y (ρ x v) := fun x hx y hy v => by
    rw [← hcomp, ← hcomp, hcomm x hx y hy]
  have hnorm_ne : ∀ x ∈ E, x ≠ 1 → ∃ v : V, v ≠ 0 ∧ v + ρ x v + ρ x (ρ x v) = 0 := by
    intro x hx hx1
    by_contra hno
    push Not at hno
    apply hx1
    apply hinj
    have hc := isCompl_ker_sub_one_ker_norm h3 (hcube x (hexp x hx))
    have hbot : LinearMap.ker (1 + ρ x + ρ x * ρ x) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have hv' : v + ρ x v + ρ x (ρ x v) = 0 := by simpa [LinearMap.mem_ker] using hv
      by_contra h0
      exact hno v h0 hv'
    have htop : LinearMap.ker (ρ x - 1) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker (ρ x - 1) := htop ▸ Submodule.mem_top
    simpa [LinearMap.mem_ker, sub_eq_zero] using this
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  obtain ⟨a, ha, ha1, w₀, -, hw₀, haw₀⟩ := exists_fixed_of_plane_rep ρ hmul hone hcomm hexp hcard
    h3 (U := ⊤) (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  set A := ρ a with hAdef
  have hA3 : ∀ v, A (A (A v)) = v := hcube a (hexp a ha)
  set W₂ : Submodule K V := LinearMap.ker (A - 1) with hW₂
  set W₁ : Submodule K V := LinearMap.ker (1 + A + A * A) with hW₁
  have hmem₂ : ∀ v, v ∈ W₂ ↔ A v = v := fun v => by simp [hW₂, LinearMap.mem_ker, sub_eq_zero]
  have hmem₁ : ∀ v, v ∈ W₁ ↔ v + A v + A (A v) = 0 := fun v => by simp [hW₁, LinearMap.mem_ker]
  have hcA := isCompl_ker_sub_one_ker_norm h3 hA3
  have hstab₁ : ∀ e ∈ E, ∀ v ∈ W₁, ρ e v ∈ W₁ := by
    intro e he v hv
    rw [hmem₁] at hv ⊢
    have h1 : A (ρ e v) = ρ e (A v) := hcommρ a ha e he v
    have h2 : A (A (ρ e v)) = ρ e (A (A v)) := by
      rw [h1]
      exact hcommρ a ha e he (A v)
    rw [h2, h1, ← map_add, ← map_add, hv, map_zero]
  have hstab₂ : ∀ e ∈ E, ∀ v ∈ W₂, ρ e v ∈ W₂ := by
    intro e he v hv
    rw [hmem₂] at hv ⊢
    have h1 : A (ρ e v) = ρ e (A v) := hcommρ a ha e he v
    rw [h1, hv]
  have hW₁ne : W₁ ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := hnorm_ne a ha ha1
    intro h
    exact hv0 ((Submodule.mem_bot K).mp (h ▸ (hmem₁ v).mpr hv))
  obtain ⟨b, hb, hb1, u, hu, hu0, hbu⟩ := exists_fixed_of_plane_rep ρ hmul hone hcomm hexp hcard
    h3 hstab₁ hW₁ne
  set B := ρ b with hBdef
  have hB3 : ∀ v, B (B (B v)) = v := hcube b (hexp b hb)
  have hBAu : B (A u) = A u := by rw [hBdef, hAdef, hcommρ b hb a ha, ← hBdef, hbu]
  have hAAu : u + A u + A (A u) = 0 := (hmem₁ u).mp hu
  have hAu₁ : A u ∈ W₁ := hstab₁ a ha u hu
  have hpu : LinearIndependent K ![u, A u] := linearIndependent_pair_of_norm hK hu0 hAAu
  have hex : ∃ w ∈ W₂, w ≠ 0 ∧ w + B w + B (B w) = 0 := by
    by_contra hno
    push Not at hno
    have hfixB : ∀ v ∈ W₂, B v = v := by
      intro v hv
      set z := (2 : K) • v - B v - B (B v) with hz
      have hzW : z ∈ W₂ :=
        W₂.sub_mem (W₂.sub_mem (W₂.smul_mem 2 hv) (hstab₂ b hb v hv))
          (hstab₂ b hb _ (hstab₂ b hb v hv))
      have hzn : z + B z + B (B z) = 0 := by
        simp only [hz, map_sub, map_smul, hB3]
        module
      have hz0 : z = 0 := by
        by_contra h
        exact hno z hzW h hzn
      have hBz : B z = 0 := by rw [hz0, map_zero]
      simp only [hz, map_sub, map_smul, hB3] at hBz
      have h3v : (3 : K) • (B v - v) = 0 := by
        linear_combination (norm := module) hBz - hz0
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3v).resolve_left h3)
    have hcB := isCompl_ker_sub_one_ker_norm h3 hB3
    have hdim := Submodule.finrank_add_eq_of_isCompl hcB
    rw [hV] at hdim
    obtain ⟨v, hv0, hvn⟩ := hnorm_ne b hb hb1
    have hpv : LinearIndependent K ![v, B v] := linearIndependent_pair_of_norm hK hv0 hvn
    have hle2 : 2 ≤ Module.finrank K (LinearMap.ker (1 + B + B * B)) := by
      refine le_finrank_of_linearIndependent hpv fun i => ?_
      fin_cases i
      · simpa [LinearMap.mem_ker] using hvn
      · have : B v + B (B v) + B (B (B v)) = 0 := by
          rw [hB3, ← hvn]
          abel
        simpa [LinearMap.mem_ker] using this
    have hw₀₂ : w₀ ∈ W₂ := (hmem₂ w₀).mpr haw₀
    have hp3 : LinearIndependent K ![w₀, u, A u] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
      have hx1 : c 1 • u + c 2 • A u ∈ W₁ := W₁.add_mem (W₁.smul_mem _ hu) (W₁.smul_mem _ hAu₁)
      have hx2 : c 0 • w₀ ∈ W₂ := W₂.smul_mem _ hw₀₂
      have h1 : c 1 • u + c 2 • A u = 0 :=
        eq_zero_of_add_eq_zero hcA.disjoint.symm hx1 hx2 (by rw [← hc]; abel)
      have h2 : c 0 • w₀ = 0 := by linear_combination (norm := module) hc - h1
      have hc0 : c 0 = 0 := (smul_eq_zero.mp h2).resolve_right hw₀
      obtain ⟨hc1, hc2⟩ := (LinearIndependent.pair_iff.mp hpu) (c 1) (c 2) h1
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
      · exact hc2
    have hle3 : 3 ≤ Module.finrank K (LinearMap.ker (B - 1)) := by
      refine le_finrank_of_linearIndependent hp3 fun i => ?_
      fin_cases i
      · simpa [LinearMap.mem_ker, sub_eq_zero] using hfixB w₀ hw₀₂
      · simpa [LinearMap.mem_ker, sub_eq_zero] using hbu
      · simpa [LinearMap.mem_ker, sub_eq_zero] using hBAu
    omega
  obtain ⟨w, hw, hw0, hBBw⟩ := hex
  have hAw : A w = w := (hmem₂ w).mp hw
  have hBw₂ : B w ∈ W₂ := hstab₂ b hb w hw
  have hABw : A (B w) = B w := (hmem₂ _).mp hBw₂
  have hpw : LinearIndependent K ![w, B w] := linearIndependent_pair_of_norm hK hw0 hBBw
  refine ⟨a, ha, b, hb, u, w, hAAu, hAw, hABw, hbu, hBAu, hBBw, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hc
  have hx1 : c 0 • u + c 1 • A u ∈ W₁ := W₁.add_mem (W₁.smul_mem _ hu) (W₁.smul_mem _ hAu₁)
  have hx2 : c 2 • w + c 3 • B w ∈ W₂ := W₂.add_mem (W₂.smul_mem _ hw) (W₂.smul_mem _ hBw₂)
  have h1 : c 0 • u + c 1 • A u = 0 :=
    eq_zero_of_add_eq_zero hcA.disjoint.symm hx1 hx2 (by rw [← hc]; abel)
  have h2 : c 2 • w + c 3 • B w = 0 := by linear_combination (norm := module) hc - h1
  obtain ⟨hc0, hc1⟩ := (LinearIndependent.pair_iff.mp hpu) (c 0) (c 1) h1
  obtain ⟨hc2, hc3⟩ := (LinearIndependent.pair_iff.mp hpw) (c 2) (c 3) h2
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

end Blocks

variable {K : Type} [Field K]

@[expose] noncomputable def slRep (x : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) :
    Module.End K (Fin 4 → K) :=
  Matrix.toLin' ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem slRep_mul (x y : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) :
    slRep (x * y) = slRep x * slRep y := by
  simp only [slRep, Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul]
  rfl

theorem slRep_one : slRep (1 : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) = 1 := by
  simp only [slRep, OneMemClass.coe_one, Units.val_one, Matrix.toLin'_one]
  rfl

theorem slRep_injective {x y : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker}
    (h : slRep x = slRep y) : x = y :=
  Subtype.ext (Units.ext (Matrix.toLin'.injective h))

theorem exists_weyl_sl4 [Finite K] (h3 : (3 : K) ≠ 0) (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    (E : Subgroup (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    ∃ g : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker,
      (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧ ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹ := by
  have hV : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  have hinj : ∀ x : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker, slRep x = 1 → x = 1 :=
    fun x hx => slRep_injective (hx.trans slRep_one.symm)
  obtain ⟨a, ha, b, hb, u, w, hAA, hAw, hABw, hBu, hBAu, hBB, hli⟩ :=
    exists_blockBasis_sl hV h3 hK slRep slRep_mul slRep_one hinj hcomm hexp hcard
  obtain ⟨s, t, hst⟩ := exists_normForm_eq h3 (-1)
  set g := blockWeyl hli hV s t with hgdef
  have hdet : LinearMap.det g = 1 := by
    rw [hgdef, det_blockWeyl, hst]
    ring
  have hunit : IsUnit g := (LinearMap.isUnit_iff_isUnit_det g).mpr (by rw [hdet]; exact isUnit_one)
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : GL (Fin 4) K, Matrix.GeneralLinearGroup.toLin G₀ = hunit.unit :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hG₀g : Matrix.toLin' ((G₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = g := by
    have h := Matrix.GeneralLinearGroup.coe_toLin G₀
    rw [hG₀, IsUnit.unit_spec] at h
    exact h.symm
  have hG₀det : Matrix.GeneralLinearGroup.det G₀ = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← LinearMap.det_toLin', hG₀g, hdet, Units.val_one]
  let G : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := ⟨G₀, hG₀det⟩
  have hGg : slRep G = g := hG₀g
  have hGa : G * a = b * G := by
    apply slRep_injective
    rw [slRep_mul, slRep_mul, hGg]
    exact blockWeyl_comp_A hli hV s t hAA hAw hABw hBu hBAu hBB
  have hGb : G * b = a * a * G := by
    apply slRep_injective
    rw [slRep_mul, slRep_mul, slRep_mul, hGg]
    exact blockWeyl_comp_B hli hV s t hAA hAw hABw hBu hBAu hBB
  have ha3 : a ^ 3 = 1 := hexp a ha
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h1 : slRep (1 : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) u = u := by
      rw [slRep_one]
      rfl
    have hne := hli.injective.ne (show (0 : Fin 4) ≠ 1 by decide)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hne
    exact hne h1.symm
  have hGa' : G * a * G⁻¹ = b := by rw [hGa, mul_inv_cancel_right]
  have hGb' : G * b * G⁻¹ = a⁻¹ := by
    rw [hGb, mul_inv_cancel_right]
    rw [eq_inv_iff_mul_eq_one, ← ha3, pow_three, mul_assoc]
  have hba : b ∉ Subgroup.zpowers a := by
    intro hbz
    let S : Subgroup (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker :=
      { carrier := {x | slRep x w = w}
        mul_mem' := fun {x y} hx hy => by
          change slRep x w = w at hx
          change slRep y w = w at hy
          change slRep (x * y) w = w
          rw [slRep_mul, Module.End.mul_apply, hy, hx]
        one_mem' := by
          change slRep 1 w = w
          rw [slRep_one]
          rfl
        inv_mem' := fun {x} hx => by
          change slRep x w = w at hx
          change slRep x⁻¹ w = w
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← slRep_mul, inv_mul_cancel, slRep_one]
          rfl }
    have hle : Subgroup.zpowers a ≤ S := (Subgroup.zpowers_le).mpr hAw
    have hbw : slRep b w = w := hle hbz
    rw [hbw, hbw] at hBB
    have h3w : (3 : K) • w = 0 := by
      rw [← hBB]
      module
    have hw0 : w = 0 := (smul_eq_zero.mp h3w).resolve_left h3
    have := hli.ne_zero 2
    simp [hw0] at this
  exact ⟨G, weyl_of_gens hcomm hexp hcard ha hb ha1 hba hGa' hGb'⟩

theorem pow_four_eq_one_of_mk_eq_one {z : (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker}
    (hz : ProjGenLinGroup.mk (z : GL (Fin 4) K) = 1) : z ^ 4 = 1 := by
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet : Matrix.GeneralLinearGroup.det (z : GL (Fin 4) K) = 1 := z.2
  rw [← hc] at hdet
  have hc4 : c ^ 4 = 1 := by
    apply Units.ext
    have := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    simpa [Matrix.GeneralLinearGroup.scalar] using this
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hc, ← map_pow, hc4, map_one]
  rfl

theorem census424_of_projSL_four {X : Type} [Group X] [Finite X] [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0) (eX : X ≃* projSL 4 K) : Census424 X := by
  let Y := (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker
  let π₀ : Y →* projSL 4 K :=
    ((ProjGenLinGroup.mk : GL (Fin 4) K →* _).comp Y.subtype).codRestrict
      (projSL 4 K) (fun x => ⟨x, x.2, rfl⟩)
  have hπ₀ : Function.Surjective π₀ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Y.map (ProjGenLinGroup.mk : GL (Fin 4) K →* _) := hy
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨⟨x, hx⟩, rfl⟩
  have hπ : Function.Surjective (eX.symm.toMonoidHom.comp π₀) :=
    eX.symm.surjective.comp hπ₀
  refine census424_of_cover _ hπ (fun z hz => ?_) (fun E => exists_weyl_sl4 h3 hK E)
  have h1 : π₀ z = 1 := by
    apply eX.symm.injective
    rw [map_one]
    exact hz
  exact pow_four_eq_one_of_mk_eq_one (congrArg Subtype.val h1)

end Item424Res5

end CFSG.RankThree.PartTwo.Sec4
