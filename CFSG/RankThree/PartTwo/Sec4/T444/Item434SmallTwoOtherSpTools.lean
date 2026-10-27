module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial

section Centers

variable {r : ℕ} {K : Type} [Field K]

@[expose] def IsSpCenter (H : Subgroup (StatedSp r K)) (v : Fin r ⊕ Fin r → K) : Prop :=
  ∀ t : K, spTransvection v t ∈ H

theorem spForm_spEnd_spEnd (g : StatedSp r K) (y z : Fin r ⊕ Fin r → K) :
    spForm r K (spEnd g y) (spEnd g z) = spForm r K y z :=
  mem_sesqUnitaryGroup.mp (spLin_mem g) y z

theorem spEnd_spEnd_inv_apply (g : StatedSp r K) (y : Fin r ⊕ Fin r → K) :
    spEnd g (spEnd g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply]

theorem conj_spTransvection (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) (t : K) :
    g * spTransvection v t * g⁻¹ = spTransvection (spEnd g v) t :=
  CFSG.RankThree.PartOne.CTP.spTransvection_conj g v t

theorem spTransvection_zero_eq_one (t : K) :
    spTransvection (0 : Fin r ⊕ Fin r → K) t = 1 := by
  apply spLin_injective
  rw [map_one]
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection 0 t) y = y
  rw [spEnd_spTransvection]
  simp

theorem spTransvection_smul_eq (c : K) (v : Fin r ⊕ Fin r → K) (t : K) :
    spTransvection (c • v) t = spTransvection v (c * c * t) := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection (c • v) t) y = spEnd (spTransvection v (c * c * t)) y
  rw [spEnd_spTransvection, spEnd_spTransvection, map_smul, smul_smul]
  congr 2
  simp only [smul_eq_mul]
  ring

theorem commute_spTransvection_of_fixed {x : StatedSp r K} {u : Fin r ⊕ Fin r → K}
    (hu : spEnd x u = u) (t : K) : x * spTransvection u t = spTransvection u t * x := by
  have h := conj_spTransvection x u t
  rw [hu] at h
  exact mul_inv_eq_iff_eq_mul.mp h

variable {H : Subgroup (StatedSp r K)} {v a b : Fin r ⊕ Fin r → K}

theorem isSpCenter_zero : IsSpCenter H (0 : Fin r ⊕ Fin r → K) := fun t => by
  rw [spTransvection_zero_eq_one]
  exact H.one_mem

theorem IsSpCenter.map (hv : IsSpCenter H v) {g : StatedSp r K} (hg : g ∈ H) :
    IsSpCenter H (spEnd g v) := fun t => by
  rw [← conj_spTransvection]
  exact H.mul_mem (H.mul_mem hg (hv t)) (H.inv_mem hg)

theorem IsSpCenter.smul (hv : IsSpCenter H v) (c : K) : IsSpCenter H (c • v) := fun t => by
  rw [spTransvection_smul_eq]
  exact hv _

theorem IsSpCenter.add (ha : IsSpCenter H a) (hb : IsSpCenter H b)
    (hab : spForm r K a b ≠ 0) : IsSpCenter H (a + b) := by
  have hg := hb (spForm r K a b)⁻¹
  have h := ha.map hg
  rwa [spEnd_spTransvection, inv_mul_cancel₀ hab, one_smul] at h

section Transitivity

variable {U : Submodule K (Fin r ⊕ Fin r → K)}

theorem exists_mem_fixing_eq_of_spForm_ne_zero (hU : ∀ c ∈ U, IsSpCenter H c)
    {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ U) (hy' : y' ∈ U) (h : spForm r K y y' ≠ 0) :
    ∃ g ∈ H, spEnd g y = y' ∧ ∀ z, (∀ c ∈ U, spForm r K z c = 0) → spEnd g z = z := by
  refine ⟨spTransvection (y' - y) (spForm r K y y')⁻¹, hU _ (U.sub_mem hy' hy) _, ?_, ?_⟩
  · rw [spEnd_spTransvection, map_sub, spForm_isAlt.self_eq_zero, sub_zero,
      inv_mul_cancel₀ h, one_smul, add_sub_cancel]
  · intro z hz
    rw [spEnd_spTransvection, map_sub, hz y hy, hz y' hy']
    simp

theorem exists_mem_fixing_eq (hnd : ((spForm r K).restrict U).Nondegenerate)
    (hU : ∀ c ∈ U, IsSpCenter H c) {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ U) (hy' : y' ∈ U)
    (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) :
    ∃ g ∈ H, spEnd g y = y' ∧ ∀ z, (∀ c ∈ U, spForm r K z c = 0) → spEnd g z = z := by
  have hex : ∀ w ∈ U, w ≠ 0 → ∃ z ∈ U, spForm r K w z ≠ 0 := fun w hw hw0 => by
    by_contra hcon
    push Not at hcon
    exact hw0 (congrArg Subtype.val (hnd.1 ⟨w, hw⟩ fun z => hcon z z.2))
  by_cases hyy : y = y'
  · exact ⟨1, H.one_mem, by rw [spEnd_one, Module.End.one_apply, hyy], fun z _ => by
      rw [spEnd_one, Module.End.one_apply]⟩
  by_cases hB : spForm r K y y' = 0
  · obtain ⟨z₁, hz₁, h₁⟩ := hex y hy hy0
    obtain ⟨z₂, hz₂, h₂⟩ := hex y' hy' hy'0
    have hz : ∃ z ∈ U, spForm r K y z ≠ 0 ∧ spForm r K y' z ≠ 0 := by
      by_cases h3 : spForm r K y' z₁ = 0
      · by_cases h4 : spForm r K y z₂ = 0
        · exact ⟨z₁ + z₂, U.add_mem hz₁ hz₂, by rwa [map_add, h4, add_zero],
            by rwa [map_add, h3, zero_add]⟩
        · exact ⟨z₂, hz₂, h4, h₂⟩
      · exact ⟨z₁, hz₁, h₁, h3⟩
    obtain ⟨z₀, hz₀, hz₀1, hz₀2⟩ := hz
    have hz₀' : spForm r K z₀ y' ≠ 0 := fun h0 => hz₀2 (by
      rw [← spForm_isAlt.neg_eq, h0, neg_zero])
    obtain ⟨g₁, hg₁, hg₁y, hg₁z⟩ := exists_mem_fixing_eq_of_spForm_ne_zero hU hy hz₀ hz₀1
    obtain ⟨g₂, hg₂, hg₂y, hg₂z⟩ := exists_mem_fixing_eq_of_spForm_ne_zero hU hz₀ hy' hz₀'
    exact ⟨g₂ * g₁, H.mul_mem hg₂ hg₁, by rw [spEnd_mul, Module.End.mul_apply, hg₁y, hg₂y],
      fun z hz => by rw [spEnd_mul, Module.End.mul_apply, hg₁z z hz, hg₂z z hz]⟩
  · exact exists_mem_fixing_eq_of_spForm_ne_zero hU hy hy' hB

end Transitivity

theorem closure_spTransvections_eq_top :
    Subgroup.closure {g : StatedSp r K | ∃ (v : Fin r ⊕ Fin r → K) (t : K),
      g = spTransvection v t} = ⊤ :=
  CFSG.RankThree.PartOne.CTP.closure_spTransvection_eq_top

theorem eq_top_of_isSpCenter (h : ∀ v, IsSpCenter H v) : H = ⊤ := by
  rw [eq_top_iff, ← closure_spTransvections_eq_top (r := r) (K := K)]
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨v, t, rfl⟩
  exact h v t

section Support

variable {ι : Type*} {Vs : ι → Submodule K (Fin r ⊕ Fin r → K)}

theorem isSpCenter_of_pairs (hspan : ⨆ i, Vs i = ⊤)
    (horth : ∀ i j, i ≠ j → ∀ u ∈ Vs i, ∀ v ∈ Vs j, spForm r K u v = 0)
    (hnd : ∀ i, ((spForm r K).restrict (Vs i)).Nondegenerate)
    (hpure : ∀ i, ∀ c ∈ Vs i, IsSpCenter H c)
    (hpair : ∀ i j, i ≠ j → ∀ y ∈ Vs i, ∀ y' ∈ Vs j, y ≠ 0 → y' ≠ 0 →
      IsSpCenter H (y + y')) :
    ∀ v, IsSpCenter H v := by
  classical
  have key : ∀ n : ℕ, ∀ J : Finset ι, J.card ≤ n → ∀ v ∈ ⨆ j ∈ J, Vs j, IsSpCenter H v := by
    intro n
    induction n with
    | zero =>
      intro J hJ v hv
      have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hJ0
      have hv0 : v = 0 := by simpa using hv
      rw [hv0]
      exact isSpCenter_zero
    | succ n ih =>
      intro J hJ v hv
      obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum Vs v).1 hv
      have hmem : ∀ (S : Finset ι) (k : ι), k ∈ S → ∀ w ∈ Vs k, w ∈ ⨆ j ∈ S, Vs j :=
        fun S k hk w hw => Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk hw)
      by_cases hz : ∃ j ∈ J, (μ j : Fin r ⊕ Fin r → K) = 0
      · obtain ⟨j, hj, hμj⟩ := hz
        refine ih (J.erase j) (by rw [Finset.card_erase_of_mem hj]; omega) _ ?_
        refine (Submodule.mem_iSup_finset_iff_exists_sum Vs _).2 ⟨μ, ?_⟩
        rw [← Finset.add_sum_erase J _ hj, hμj, zero_add]
      push Not at hz
      by_cases hJ2 : ∃ i ∈ J, ∃ j ∈ J, i ≠ j
      · obtain ⟨i, hi, j, hj, hij⟩ := hJ2
        have hi' : i ∈ J.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
        have hcard : (J.erase j).card ≤ n := by rw [Finset.card_erase_of_mem hj]; omega
        set v' := ∑ k ∈ J.erase j, (μ k : Fin r ⊕ Fin r → K) with hv'
        have hsum : ∑ k ∈ J, (μ k : Fin r ⊕ Fin r → K) = v' + μ j := by
          rw [hv', Finset.sum_erase_add J _ hj]
        obtain ⟨y, hy, hBy⟩ : ∃ y ∈ Vs i, spForm r K (μ i) y ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hz i hi (congrArg Subtype.val ((hnd i).1 ⟨μ i, (μ i).2⟩ fun z => hcon z z.2))
        have hy0 : y ≠ 0 := fun h0 => hBy (by rw [h0, map_zero])
        have hv'y : spForm r K v' y = spForm r K (μ i) y := by
          rw [hv', map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
          · intro k hk hki
            exact horth k i hki _ (μ k).2 y hy
          · intro hni
            exact absurd hi' hni
        have hv'μj : spForm r K v' (μ j) = 0 := by
          rw [hv', map_sum, LinearMap.sum_apply]
          refine Finset.sum_eq_zero fun k hk => ?_
          exact horth k j (Finset.ne_of_mem_erase hk) _ (μ k).2 _ (μ j).2
        have hyμj : spForm r K y (μ j) = 0 := horth i j hij y hy _ (μ j).2
        have hB : spForm r K (v' + y) (μ j - y) ≠ 0 := by
          have h0 : spForm r K (v' + y) (μ j - y) = -spForm r K (μ i) y := by
            simp only [map_add, map_sub, LinearMap.add_apply]
            rw [hv'μj, hv'y, hyμj, spForm_isAlt.self_eq_zero]
            ring
          rw [h0]
          exact neg_ne_zero.2 hBy
        have h1 : IsSpCenter H (v' + y) := by
          refine ih (J.erase j) hcard _ (Submodule.add_mem _ ?_ (hmem _ i hi' y hy))
          exact Submodule.sum_mem _ fun k hk => hmem _ k hk _ (μ k).2
        have h2 : IsSpCenter H (μ j - y) := by
          rw [← neg_add_eq_sub]
          exact hpair i j hij (-y) ((Vs i).neg_mem hy) _ (μ j).2 (neg_ne_zero.2 hy0) (hz j hj)
        have h3 := h1.add h2 hB
        rw [hsum]
        convert h3 using 1
        abel
      · push Not at hJ2
        rcases J.eq_empty_or_nonempty with hJ0 | ⟨j0, hj0⟩
        · subst hJ0
          rw [Finset.sum_empty]
          exact isSpCenter_zero
        · have hsum : ∑ k ∈ J, (μ k : Fin r ⊕ Fin r → K) = μ j0 :=
            Finset.sum_eq_single_of_mem j0 hj0 fun k hk hne => absurd (hJ2 k hk j0 hj0) hne
          rw [hsum]
          exact hpure j0 _ (μ j0).2
  intro v
  have hv : v ∈ ⨆ i, Vs i := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨J, hJ⟩ := Submodule.mem_iSup_iff_exists_finset.1 hv
  exact key J.card J le_rfl v hJ

end Support

end Centers

section Planes

variable {r : ℕ} {K : Type} [Field K]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
theorem spForm_single_one (a c : Fin r ⊕ Fin r) :
    spForm r K (Pi.single a 1) (Pi.single c 1) = gram K r a c := by
  rw [spForm_apply, Matrix.mulVec_single_one, single_one_dotProduct]
  rfl

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
theorem spForm_single_one_cases (i j : Fin r) :
    spForm r K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) = 0 ∧
    spForm r K (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1) = 0 ∧
    spForm r K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) = (if i = j then 1 else 0) ∧
    spForm r K (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inl j) 1) =
      (if i = j then -1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [spForm_single_one]
  · rfl
  · rfl
  · rfl
  · simp only [gram, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp

@[expose] noncomputable def spPlane (i : Fin r) : Submodule K (Fin r ⊕ Fin r → K) :=
  Submodule.span K {Pi.single (Sum.inl i) 1, Pi.single (Sum.inr i) 1}

theorem single_inl_mem_spPlane (i : Fin r) :
    (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin r → K) ∈ spPlane i :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem single_inr_mem_spPlane (i : Fin r) :
    (Pi.single (Sum.inr i) 1 : Fin r ⊕ Fin r → K) ∈ spPlane i :=
  Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

theorem iSup_spPlane : ⨆ i, spPlane (r := r) (K := K) i = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin r ⊕ Fin r)).span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [Pi.basisFun_apply]
  rcases a with i | i
  · exact Submodule.mem_iSup_of_mem i (single_inl_mem_spPlane i)
  · exact Submodule.mem_iSup_of_mem i (single_inr_mem_spPlane i)

theorem spForm_eq_zero_of_mem_spPlane {i j : Fin r} (hij : i ≠ j) {u v : Fin r ⊕ Fin r → K}
    (hu : u ∈ spPlane i) (hv : v ∈ spPlane j) : spForm r K u v = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hv
  obtain ⟨h1, h2, h3, h4⟩ := spForm_single_one_cases (K := K) i j
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
    h3, h4, hij, ite_false]
  ring

theorem nondegenerate_spPlane (i : Fin r) :
    ((spForm r K).restrict (spPlane i)).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
  obtain ⟨α, β, hx'⟩ := Submodule.mem_span_pair.mp x.2
  have h1 := hx ⟨_, single_inl_mem_spPlane i⟩
  have h2 := hx ⟨_, single_inr_mem_spPlane i⟩
  obtain ⟨c1, c2, c3, c4⟩ := spForm_single_one_cases (K := K) i i
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h1 h2
  rw [← hx'] at h1 h2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, c1, c2,
    c3, c4, ite_true] at h1 h2
  have hα : α = 0 := by linear_combination h2
  have hβ : β = 0 := by linear_combination -h1
  apply Subtype.ext
  rw [← hx', hα, hβ, zero_smul, zero_smul, add_zero]
  rfl

end Planes

section Torus

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_torusHom_inl (t : Fin r → Kˣ) (i : Fin r) :
    spEnd (SymplecticTorusWeyl.torusHom t) (Pi.single (Sum.inl i) 1) =
      (t i : K) • Pi.single (Sum.inl i) 1 := by
  rw [spEnd_apply, SymplecticTorusWeyl.coe_torusHom, Matrix.mulVec_single_one]
  funext b
  rcases b with b | b
  · by_cases hb : b = i
    · subst hb
      simp
    · simp [hb]
  · simp

theorem spEnd_torusHom_inr (t : Fin r → Kˣ) (i : Fin r) :
    spEnd (SymplecticTorusWeyl.torusHom t) (Pi.single (Sum.inr i) 1) =
      (((t i)⁻¹ : Kˣ) : K) • Pi.single (Sum.inr i) 1 := by
  rw [spEnd_apply, SymplecticTorusWeyl.coe_torusHom, Matrix.mulVec_single_one]
  funext b
  rcases b with b | b
  · simp
  · by_cases hb : b = i
    · subst hb
      simp
    · simp [hb]

@[expose] noncomputable def spShortRoot (i j : Fin r) (hij : i ≠ j) : StatedSp r K :=
  SymplecticTorusWeyl.leviSp (Matrix.GeneralLinearGroup.transvection j i hij.symm 1)

theorem spEnd_spShortRoot {i j : Fin r} (hij : i ≠ j) :
    spEnd (spShortRoot (K := K) i j hij) (Pi.single (Sum.inl i) 1) =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1 := by
  rw [spEnd_apply, spShortRoot, SymplecticTorusWeyl.coe_leviSp, Matrix.mulVec_single_one,
    Matrix.GeneralLinearGroup.val_transvection]
  funext b
  rcases b with b | b
  · by_cases hbi : b = i
    · subst hbi
      simp [Matrix.transvection, Ne.symm hij]
    · by_cases hbj : b = j
      · subst hbj
        simp [Matrix.transvection, hbi]
      · simp [Matrix.transvection, hbi, hbj, Ne.symm hbj]
  · simp

theorem torusHom_mul_spShortRoot {t : Fin r → Kˣ} {i j : Fin r} (hij : i ≠ j) (ht : t i = t j) :
    SymplecticTorusWeyl.torusHom t * spShortRoot i j hij =
      spShortRoot i j hij * SymplecticTorusWeyl.torusHom t := by
  rw [SymplecticTorusWeyl.torusHom, MonoidHom.comp_apply, spShortRoot, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, Matrix.GeneralLinearGroup.val_transvection]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    ring
  · by_cases h : j = a ∧ i = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab, ht]
    · simp [hab, h]

end Torus

section GF4

variable {r : ℕ}

theorem card_units_gf4 : Nat.card (GaloisField 2 2)ˣ = 3 := by
  classical
  have := Fintype.ofFinite (GaloisField 2 2)
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem units_gf4_pow_three (u : (GaloisField 2 2)ˣ) : u ^ 3 = 1 := by
  rw [← card_units_gf4]
  exact pow_card_eq_one'

theorem card_torus_gf4 :
    Nat.card (SymplecticTorusWeyl.torus r (GaloisField 2 2)) = 3 ^ r := by
  rw [SymplecticTorusWeyl.torus, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective SymplecticTorusWeyl.torusHom_injective, Subgroup.card_top,
    Nat.card_fun, card_units_gf4, Nat.card_fin]

theorem isElemAbelian_torus_gf4 :
    CFSG.Assembly.IsElemAbelian 3 (SymplecticTorusWeyl.torus r (GaloisField 2 2)) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : StatedSp r (GaloisField 2 2)) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨t, rfl⟩ := hx
    rw [← map_pow]
    have ht : t ^ 3 = 1 := funext fun i => units_gf4_pow_three (t i)
    rw [ht, map_one]

theorem three_mul_card_map_ker {φ : (Fin r → (GaloisField 2 2)ˣ) →* (GaloisField 2 2)ˣ}
    (hφ : Function.Surjective φ) :
    3 * Nat.card (φ.ker.map (SymplecticTorusWeyl.torusHom (r := r) (k := GaloisField 2 2))) =
      Nat.card (SymplecticTorusWeyl.torus r (GaloisField 2 2)) := by
  rw [Subgroup.card_map_of_injective SymplecticTorusWeyl.torusHom_injective,
    SymplecticTorusWeyl.torus, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective SymplecticTorusWeyl.torusHom_injective, Subgroup.card_top,
    ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ,
    Subgroup.card_top, card_units_gf4, mul_comm]

theorem spTransvection_inl_mem_hyperCent (i : Fin r) (c : GaloisField 2 2) :
    spTransvection (Pi.single (Sum.inl i) 1) c ∈
      hyperCent (SymplecticTorusWeyl.torus r (GaloisField 2 2)) := by
  refine ⟨(Pi.evalMonoidHom (fun _ : Fin r => (GaloisField 2 2)ˣ) i).ker.map
    SymplecticTorusWeyl.torusHom, Subgroup.map_le_range _ _,
    three_mul_card_map_ker fun u => ⟨fun _ => u, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  apply commute_spTransvection_of_fixed
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at ht
  rw [spEnd_torusHom_inl, ht, Units.val_one, one_smul]

theorem spTransvection_inr_mem_hyperCent (i : Fin r) (c : GaloisField 2 2) :
    spTransvection (Pi.single (Sum.inr i) 1) c ∈
      hyperCent (SymplecticTorusWeyl.torus r (GaloisField 2 2)) := by
  refine ⟨(Pi.evalMonoidHom (fun _ : Fin r => (GaloisField 2 2)ˣ) i).ker.map
    SymplecticTorusWeyl.torusHom, Subgroup.map_le_range _ _,
    three_mul_card_map_ker fun u => ⟨fun _ => u, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  apply commute_spTransvection_of_fixed
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at ht
  rw [spEnd_torusHom_inr, ht, inv_one, Units.val_one, one_smul]

theorem spShortRoot_mem_hyperCent {i j : Fin r} (hij : i ≠ j) :
    spShortRoot i j hij ∈ hyperCent (SymplecticTorusWeyl.torus r (GaloisField 2 2)) := by
  set φ := Pi.evalMonoidHom (fun _ : Fin r => (GaloisField 2 2)ˣ) i /
    Pi.evalMonoidHom (fun _ : Fin r => (GaloisField 2 2)ˣ) j with hφ
  have hsurj : Function.Surjective φ := fun u => ⟨Pi.mulSingle i u, by
    rw [hφ, MonoidHom.div_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne' hij, div_one]⟩
  refine ⟨φ.ker.map SymplecticTorusWeyl.torusHom, Subgroup.map_le_range _ _,
    three_mul_card_map_ker hsurj, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ, MonoidHom.div_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply, div_eq_one] at ht
  exact torusHom_mul_spShortRoot hij ht

theorem closure_hyperCent_torus_gf4 :
    Subgroup.closure (hyperCent (SymplecticTorusWeyl.torus r (GaloisField 2 2))) = ⊤ := by
  set H := Subgroup.closure (hyperCent (SymplecticTorusWeyl.torus r (GaloisField 2 2)))
    with hH
  have hsub : ∀ x ∈ hyperCent (SymplecticTorusWeyl.torus r (GaloisField 2 2)), x ∈ H :=
    fun x hx => Subgroup.subset_closure hx
  have he : ∀ i, IsSpCenter H (Pi.single (Sum.inl i) 1) :=
    fun i c => hsub _ (spTransvection_inl_mem_hyperCent i c)
  have hf : ∀ i, IsSpCenter H (Pi.single (Sum.inr i) 1) :=
    fun i c => hsub _ (spTransvection_inr_mem_hyperCent i c)
  have hplane : ∀ i, ∀ c ∈ spPlane i, IsSpCenter H c := by
    intro i c hc
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hc
    by_cases hα : α = 0
    · rw [hα, zero_smul, zero_add]
      exact (hf i).smul β
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero]
      exact (he i).smul α
    refine ((he i).smul α).add ((hf i).smul β) ?_
    obtain ⟨-, -, c3, -⟩ := spForm_single_one_cases (K := GaloisField 2 2) i i
    simp [c3, hα, hβ]
  have he0 : ∀ k : Fin r, (Pi.single (Sum.inl k) 1 : Fin r ⊕ Fin r → GaloisField 2 2) ≠ 0 :=
    fun k h => one_ne_zero (Pi.single_eq_zero_iff.mp h)
  have hpair0 : ∀ i j, i ≠ j →
      IsSpCenter H (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1) := by
    intro i j hij
    have h := (he i).map (hsub _ (spShortRoot_mem_hyperCent hij))
    rwa [spEnd_spShortRoot] at h
  have hpair : ∀ i j, i ≠ j → ∀ y ∈ spPlane i, ∀ y' ∈ spPlane j, y ≠ 0 → y' ≠ 0 →
      IsSpCenter H (y + y') := by
    intro i j hij y hy y' hy' hy0 hy'0
    obtain ⟨g₁, hg₁, hg₁e, hg₁z⟩ := exists_mem_fixing_eq (nondegenerate_spPlane i) (hplane i)
      (single_inl_mem_spPlane i) hy (he0 i) hy0
    obtain ⟨g₂, hg₂, hg₂e, hg₂z⟩ := exists_mem_fixing_eq (nondegenerate_spPlane j) (hplane j)
      (single_inl_mem_spPlane j) hy' (he0 j) hy'0
    have h1 := ((hpair0 i j hij).map hg₁).map hg₂
    rwa [map_add, hg₁e, hg₁z _ fun c hc => spForm_eq_zero_of_mem_spPlane (Ne.symm hij)
      (single_inl_mem_spPlane j) hc, map_add, hg₂e,
      hg₂z _ fun c hc => spForm_eq_zero_of_mem_spPlane hij hy hc] at h1
  exact eq_top_of_isSpCenter (isSpCenter_of_pairs iSup_spPlane
    (fun i j hij u hu v hv => spForm_eq_zero_of_mem_spPlane hij hu hv) nondegenerate_spPlane
    hplane hpair)

end GF4

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
