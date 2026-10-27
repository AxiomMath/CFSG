module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusPlane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusVectors
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlaneIsometry
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusBorel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL lineStabilizer polar_smul_right_eq
  polar_self_eq_two_mul polar_map_of_linearIsometry toLinEquiv toLinEquiv_apply)
open CFSG.LieType.Universal.Spin (quadMinus binaryForm)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

private theorem eq_of_ne_one_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  by_contra hxy
  have h3 : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  have h4 := Finset.card_le_univ ({1, x, y} : Finset G)
  rw [h3] at h4
  have h2 : Fintype.card G ≤ 2 := by rwa [← Nat.card_eq_fintype_card]
  omega

private theorem two_eq_zero [CharP K 2] : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

private theorem neg_eq_self [CharP K 2] (x : K) : -x = x := by
  have h : x + x = 0 := by rw [← two_mul, two_eq_zero, zero_mul]
  exact neg_eq_of_add_eq_zero_left h

private theorem eq_of_add_eq_zero [CharP K 2] {x y : K} (h : x + y = 0) : x = y := by
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_self]

theorem planeBlock_eq_of_not_mem_rootGroupGL [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {T : Subgroup (GL ιM K)}
    (hT : T ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (hT2 : IsPGroup 2 ↥T)
    {g h : GL ιM K} (hg : g ∈ T) (hh : h ∈ T)
    (hgU : g ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K))
    (hhU : h ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) :
    planeBlock (g : Matrix ιM ιM K) = planeBlock (h : Matrix ιM ιM K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  set φ : ↥T →* GL (Fin 2) K :=
    (planeHom b c).comp (Subgroup.inclusion (hT.trans (isoFix_le_lineStabilizer b c))) with hφdef
  have hφ : ∀ x : ↥T, (φ x : Matrix (Fin 2) (Fin 2) K) = planeBlock (x.1 : Matrix ιM ιM K) := by
    intro x
    rw [hφdef]
    exact coe_planeHom b c _
  have hle : φ.range ≤ planeO b c := by
    rintro - ⟨x, rfl⟩
    exact planeHom_mem_planeO b c _
  have hP : IsPGroup 2 ↥φ.range := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    exact IsPGroup.of_card_dvd_pow (n := n) (by rw [← hn]; exact Subgroup.card_range_dvd φ)
  have hodd : Odd (Nat.card K + 1) := by
    obtain ⟨m, -, hKcard⟩ := FiniteField.card K 2
    have hqeven : Even (Nat.card K) := by
      rw [Nat.card_eq_fintype_card, hKcard, even_iff_two_dvd]
      exact dvd_pow_self 2 m.ne_zero
    exact hqeven.add_one
  have hcard : Nat.card ↥φ.range ≤ 2 := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : 2 ^ k ∣ 2 * (Nat.card K + 1) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rw [card_planeO hirr] at h1
      rwa [hk] at h1
    have hcop : Nat.Coprime (2 ^ k) (Nat.card K + 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    rw [hk]
    exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  have hblock : ∀ x : GL ιM K, x ∈ T → x ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) →
      planeBlock (x : Matrix ιM ιM K) ≠ 1 :=
    fun x hx hxU h1 => hxU ((planeBlock_eq_one_iff hirr (hT hx)).mp h1)
  set φg : ↥φ.range := ⟨φ ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩ with hφg
  set φh : ↥φ.range := ⟨φ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩⟩ with hφh
  have hg1 : φ ⟨g, hg⟩ ≠ 1 := by
    intro h1
    have h2 : (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [h1]; rfl
    rw [hφ ⟨g, hg⟩] at h2
    exact hblock g hg hgU h2
  have hh1 : φ ⟨h, hh⟩ ≠ 1 := by
    intro h1
    have h2 : (φ ⟨h, hh⟩ : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [h1]; rfl
    rw [hφ ⟨h, hh⟩] at h2
    exact hblock h hh hhU h2
  have hg1' : φg ≠ 1 := fun h1 => hg1 (congrArg Subtype.val h1)
  have hh1' : φh ≠ 1 := fun h1 => hh1 (congrArg Subtype.val h1)
  have hEq : φ ⟨g, hg⟩ = φ ⟨h, hh⟩ :=
    congrArg Subtype.val (eq_of_ne_one_of_card_le_two hcard hg1' hh1')
  calc planeBlock (g : Matrix ιM ιM K) = (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) :=
        (hφ ⟨g, hg⟩).symm
    _ = (φ ⟨h, hh⟩ : Matrix (Fin 2) (Fin 2) K) := by rw [hEq]
    _ = planeBlock (h : Matrix ιM ιM K) := hφ ⟨h, hh⟩

theorem exists_planeBlock_mulVec_eq_self [CharP K 2] {b c : K} {t : GL ιM K}
    (ht : t ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) {k : ℕ} (htk : t ^ 2 ^ k = 1) :
    ∃ a : Fin 2 → K, a ≠ 0 ∧ planeBlock (t : Matrix ιM ιM K) *ᵥ a = a := by
  classical
  set φ : ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) →* GL (Fin 2) K :=
    planeHom b c with hφdef
  have hk : (φ ⟨t, isoFix_le_lineStabilizer b c ht⟩) ^ 2 ^ k = 1 := by
    have h1 : (⟨t, isoFix_le_lineStabilizer b c ht⟩ :
        ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K))) ^ 2 ^ k = 1 := by
      refine Subtype.ext ?_
      simpa using htk
    rw [← map_pow, h1, map_one]
  obtain ⟨a, ha0, ha⟩ := exists_mulVec_eq_self (X := φ ⟨t, isoFix_le_lineStabilizer b c ht⟩) hk
  refine ⟨a, ha0, ?_⟩
  rw [← coe_planeHom b c ⟨t, isoFix_le_lineStabilizer b c ht⟩]
  exact ha

private theorem polar_quadMinus_eq {b c : K} (u w : ιM → K) :
    polar (quadMinus 2 K b c) u w =
      u (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) +
        w (Sum.inl 0) * u (Sum.inr (Sum.inl 0)) +
        polar (binaryForm K b c) (fun i => u (Sum.inr (Sum.inr i)))
          (fun i => w (Sum.inr (Sum.inr i))) := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus]
  simp only [QuadraticMap.polar, CFSG.LieType.Universal.Spin.binaryForm_apply, Pi.add_apply]
  have hsum : (∑ i : Fin (2 - 1), (u (Sum.inl i) * w (Sum.inr (Sum.inl i)) +
      w (Sum.inl i) * u (Sum.inr (Sum.inl i)))) =
      u (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) + w (Sum.inl 0) * u (Sum.inr (Sum.inl 0)) := by
    rw [Fin.sum_univ_one]
  rw [hsum]
  ring

private theorem mulVec_y_eq_of_isoFix {b c : K} {g : GL ιM K}
    (hg : g ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (v : ιM → K) :
    ((g : Matrix ιM ιM K) *ᵥ v) (Sum.inr (Sum.inl 0)) = v (Sum.inr (Sum.inl 0)) := by
  have hfix : (g : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K := ((mem_isoFix).mp hg).2
  have hiso := isoFix_isometry hg
  have h := polar_map_of_linearIsometry (Q := quadMinus 2 K b c) (Q' := quadMinus 2 K b c)
    (toLinEquiv ιM K g) (fun x => by rw [toLinEquiv_apply]; exact hiso x) (KTabC.e1M K) v
  rw [toLinEquiv_apply, toLinEquiv_apply, hfix, polar_e1M_eq_y, polar_e1M_eq_y] at h
  exact h

private theorem funext_coords {u v : ιM → K} (hx : u (Sum.inl 0) = v (Sum.inl 0))
    (hy : u (Sum.inr (Sum.inl 0)) = v (Sum.inr (Sum.inl 0)))
    (hP : ∀ i : Fin 2, u (Sum.inr (Sum.inr i)) = v (Sum.inr (Sum.inr i))) : u = v := by
  funext i
  rcases i with i | i | i
  · fin_cases i
    exact hx
  · fin_cases i
    exact hy
  · exact hP i

private theorem eq_smul_e1M_add_yVec_add_planeVec {w : ιM → K}
    (hw : w (Sum.inr (Sum.inl 0)) = 1) :
    w = w (Sum.inl 0) • KTabC.e1M K + Pi.single (Sum.inr (Sum.inl 0)) 1 +
      planeVec (fun i => w (Sum.inr (Sum.inr i))) := by
  funext i
  rcases i with i | i | i
  · fin_cases i
    simp [KTabC.e1M, planeVec]
  · fin_cases i
    simp [KTabC.e1M, planeVec, hw]
  · simp [KTabC.e1M, planeVec]

theorem mulVec_planeVec_eq_of_sq_eq_one [CharP K 2] {b c : K} {g : GL ιM K}
    (hg : g ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (hg2 : g ^ 2 = 1)
    (hR : planeBlock (g : Matrix ιM ιM K) ≠ 1) {a : Fin 2 → K} (ha0 : a ≠ 0)
    (ha : planeBlock (g : Matrix ιM ιM K) *ᵥ a = a) :
    (g : Matrix ιM ιM K) *ᵥ planeVec a = planeVec a := by
  classical
  have hfix : (g : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K := ((mem_isoFix).mp hg).2
  have hiso := isoFix_isometry hg
  have hpolar : ∀ u v, polar (quadMinus 2 K b c) ((g : Matrix ιM ιM K) *ᵥ u)
      ((g : Matrix ιM ιM K) *ᵥ v) = polar (quadMinus 2 K b c) u v := by
    intro u v
    have h := polar_map_of_linearIsometry (Q := quadMinus 2 K b c) (Q' := quadMinus 2 K b c)
      (toLinEquiv ιM K g) (fun x => by rw [toLinEquiv_apply]; exact hiso x) u v
    simpa only [toLinEquiv_apply] using h
  have hgg : (g : Matrix ιM ιM K) * (g : Matrix ιM ιM K) = 1 := by
    rw [← Units.val_mul, ← pow_two, hg2]
    rfl
  set f : ιM → K := Pi.single (Sum.inr (Sum.inl 0)) 1 with hf
  set w : ιM → K := (g : Matrix ιM ιM K) *ᵥ f with hw
  set z : Fin 2 → K := fun i => w (Sum.inr (Sum.inr i)) with hzdef
  have hfw : (g : Matrix ιM ιM K) *ᵥ w = f := by
    rw [hw, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hwy : w (Sum.inr (Sum.inl 0)) = 1 := by
    have h := mulVec_y_eq_of_isoFix hg f
    rw [← hw] at h
    simpa [hf] using h
  have hdec : w = w (Sum.inl 0) • KTabC.e1M K + f + planeVec z := by
    rw [hzdef, hf]
    exact eq_smul_e1M_add_yVec_add_planeVec hwy
  have hRz : planeBlock (g : Matrix ιM ιM K) *ᵥ z = z := by
    have hvec : f = w (Sum.inl 0) • KTabC.e1M K + w
        + ((g : Matrix ιM ιM K) *ᵥ planeVec z) := by
      rw [← hfw]
      conv_lhs => rw [hdec]
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, hfix, ← hw]
    funext i
    have h := congrFun hvec (Sum.inr (Sum.inr i))
    have hL : f (Sum.inr (Sum.inr i)) = 0 := by simp [hf]
    have hR : (w (Sum.inl 0) • KTabC.e1M K + w
        + ((g : Matrix ιM ιM K) *ᵥ planeVec z)) (Sum.inr (Sum.inr i))
        = w (Sum.inr (Sum.inr i))
          + (planeBlock (g : Matrix ιM ιM K) *ᵥ z) i := by
      rw [hzdef]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1M_apply_plane, mul_zero, zero_add,
        mulVec_planeVec_apply]
    rw [hL, hR] at h
    exact (eq_of_add_eq_zero h.symm).symm
  have hx : ∀ p : Fin 2 → K,
      ((g : Matrix ιM ιM K) *ᵥ planeVec p) (Sum.inl 0)
      = polar (binaryForm K b c) ((planeBlock (g : Matrix ιM ιM K)) *ᵥ p) z := by
    intro p
    have hp0 : polar (quadMinus 2 K b c) (planeVec p) f = 0 := by
      rw [hf, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl]
      simp [planeVec]
    have hp : polar (quadMinus 2 K b c) ((g : Matrix ιM ιM K) *ᵥ planeVec p) w = 0 := by
      rw [hw, hpolar (planeVec p) f, hp0]
    rw [polar_quadMinus_eq] at hp
    have hy0 : ((g : Matrix ιM ιM K) *ᵥ planeVec p) (Sum.inr (Sum.inl 0)) = 0 := by
      rw [mulVec_y_eq_of_isoFix hg]
      simp [planeVec]
    have hP : (fun i => ((g : Matrix ιM ιM K) *ᵥ planeVec p) (Sum.inr (Sum.inr i)))
        = planeBlock (g : Matrix ιM ιM K) *ᵥ p := by
      funext i
      exact mulVec_planeVec_apply _ p i
    rw [hwy, hy0, hP] at hp
    simp only [mul_one, mul_zero, add_zero] at hp
    exact eq_of_add_eq_zero hp
  obtain ⟨s, hs⟩ := eq_smul_of_mulVec_eq_self (X := planeBlock (g : Matrix ιM ιM K))
    (a := a) (z := z) hR ha0 ha hRz
  have hz0 : polar (binaryForm K b c) ((planeBlock (g : Matrix ιM ιM K)) *ᵥ a) z = 0 := by
    rw [ha, hs, polar_smul_right_eq]
    have hself : polar (binaryForm K b c) a a = 0 := by
      rw [polar_self_eq_two_mul, two_eq_zero, zero_mul]
    rw [hself, mul_zero]
  refine funext_coords ?_ ?_ ?_
  · rw [hx a, hz0, planeVec_inl]
  · rw [mulVec_y_eq_of_isoFix hg, planeVec_inr_inl]
  · intro i
    rw [mulVec_planeVec_apply, ha, planeVec_inr_inr]

theorem mulVec_planeVec_eq_of_exponent_two [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {T : Subgroup (GL ιM K)}
    (hT : T ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (hT2 : IsPGroup 2 ↥T)
    {t₀ : GL ιM K} (ht₀ : t₀ ∈ T) (ht₀U : t₀ ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K))
    {a : Fin 2 → K} (ha0 : a ≠ 0) (ha : planeBlock (t₀ : Matrix ιM ιM K) *ᵥ a = a)
    {E : Subgroup (GL ιM K)} (hET : E ≤ T) (hE : ∀ g ∈ E, g ^ 2 = 1)
    (hEU : ¬ E ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) :
    ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ planeVec a = planeVec a := by
  classical
  obtain ⟨s, hsE, hsU⟩ := Set.not_subset.mp (show ¬ (E : Set (GL ιM K)) ⊆
    (rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) : Set (GL ιM K)) from hEU)
  have hblock : ∀ g ∈ E, g ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) →
      planeBlock (g : Matrix ιM ιM K) = planeBlock (t₀ : Matrix ιM ιM K) :=
    fun g hg hgU => planeBlock_eq_of_not_mem_rootGroupGL hirr hT hT2 (hET hg) ht₀ hgU ht₀U
  have hfix : ∀ g ∈ E, g ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) →
      (g : Matrix ιM ιM K) *ᵥ planeVec a = planeVec a := by
    intro g hg hgU
    have hgiso : g ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := hT (hET hg)
    have hne : planeBlock (g : Matrix ιM ιM K) ≠ 1 := fun h1 =>
      hgU ((planeBlock_eq_one_iff hirr hgiso).mp h1)
    have hga : planeBlock (g : Matrix ιM ιM K) *ᵥ a = a := by rw [hblock g hg hgU, ha]
    exact mulVec_planeVec_eq_of_sq_eq_one hgiso (hE g hg) hne ha0 hga
  intro g hg
  by_cases hgU : g ∈ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)
  · have hsg : s * g ∈ E := E.mul_mem hsE hg
    have hsgU : s * g ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
      intro h1
      refine hsU ?_
      have h3 : (s * g) * g⁻¹ ∈ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
        (rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)).mul_mem h1
          ((rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)).inv_mem hgU)
      rwa [show (s * g) * g⁻¹ = s from by group] at h3
    have h1 := hfix (s * g) hsg hsgU
    rw [Units.val_mul, ← Matrix.mulVec_mulVec] at h1
    have h2 := hfix s hsE hsU
    have hsinv : ((s⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ planeVec a = planeVec a := by
      have h := congrArg (fun z => ((s⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ z) h2
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h
      exact h.symm
    have h := congrArg (fun z => ((s⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ z) h1
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, hsinv] at h
    exact h
  · exact hfix g hg hgU

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
