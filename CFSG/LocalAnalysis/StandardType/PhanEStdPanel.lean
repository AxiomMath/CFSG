module

public import CFSG.LocalAnalysis.StandardType.PhanEStdPanelComb

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀) (n₀ : K)

structure RankOneField {w₀ : W} (F : FrobData D n H w₀) where
  Fld : Type
  [instField : Field Fld]
  θ : Fld →+* Fld
  θ_ne : ∃ c : Fld, θ c ≠ c
  X : Fin D.rank → Fld → K
  X_add : ∀ i c d, X i (c + d) = X i c * X i d
  X_inj : ∀ i, Function.Injective (X i)
  X_range : ∀ i, Set.range (X i) = (D.rootGroup (Pi.single i 1) : Set K)
  φ_X : ∀ i c, F.φ (X i c) = X (F.op i) (θ c)
  torus_X : ∀ i, ∀ h ∈ ⨆ j, H j, ∃ s : Fld, s ≠ 0 ∧ ∀ c, h * X i c * h⁻¹ = X i (s * c)
  nrep_X : ∀ (v : W) (i j : Fin D.rank), (cs).simple i * v = v * (cs).simple j →
    ¬ (cs).IsLeftDescent v i → ∃ s : Fld, s ≠ 0 ∧
      ∀ c, (nrep hct v)⁻¹ * X i c * nrep hct v = X j (s * c)

attribute [instance] RankOneField.instField

variable (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

private theorem q2nPE_neg_single_mem_bruhatCell (hext : SteinbergExtras D n H)
    (hsq : ∀ i, n i * n i = 1)
    {i : Fin D.rank} {w : K} (hw : w ∈ D.rootGroup (-Pi.single i 1)) (hw1 : w ≠ 1) :
    w ∈ bruhatCell hct ((cs).simple i) := by
  have hmem : -Pi.single i 1 ∈ D.roots := (Φ).neg_mem _ ((Φ).single_mem i)
  have hα : Pi.single i 1 ∈ D.roots := (Φ).single_mem i
  have hρ : weylAction D.isFiniteType ((cs).simple i) (-Pi.single i 1) = Pi.single i 1 := by
    rw [map_neg, weylAction_simple_single D.isFiniteType i, neg_neg]
  have hrank : w ∈ rankOne D.rootGroup i := Subgroup.mem_sup_right hw
  rcases hext.rankOne_bruhat i w hrank with ⟨h, hh, u, hu, hwu⟩ | ⟨u, hu, h, hh, v, hv, hwu⟩
  · have hhN : h ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) :=
      iSup_le_normalizer_rootGroup hct hmem (le_iSup H i hh)
    have hwN : w ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) :=
      Subgroup.le_normalizer hw
    have hu_eq : u = h⁻¹ * w := by rw [hwu]; group
    have huN : u ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
      rw [hu_eq]; exact mul_mem (inv_mem hhN) hwN
    have hu1 : u = 1 := hext.eq_one_of_mem_normalizer i u hu huN
    have hw_eq : w = h := by rw [hwu, hu1, mul_one]
    have hzH : n i * w * (n i)⁻¹ ∈ H i := by
      rw [hw_eq]; simpa using hct.conj_H_mem i i h hh
    have hzX : n i * w * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
      have h := hct.conj_mem i (-Pi.single i 1) hmem w hw
      rwa [hρ] at h
    have hzN : n i * w * (n i)⁻¹ ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) :=
      iSup_le_normalizer_rootGroup hct hmem (le_iSup H i hzH)
    have hz1 : n i * w * (n i)⁻¹ = 1 := hext.eq_one_of_mem_normalizer i _ hzX hzN
    have hw1' : w = 1 := by
      have e : w = (n i)⁻¹ * (n i * w * (n i)⁻¹) * n i := by group
      rw [e, hz1]; group
    exact absurd hw1' hw1
  · refine ⟨u, rootGroup_le_borel hα (ht_single_pos i) hu, h * v,
      mul_mem (iSup_le_borel (le_iSup H i hh)) (rootGroup_le_borel hα (ht_single_pos i) hv), ?_⟩
    rw [hwu, nrep_simple hct i]
    group

include hext hsq in
theorem q2nPE_not_parallel (R : RankOneField hct F) {i : Fin D.rank} {v : W}
    (hasc : ¬ (cs).IsLeftDescent v i) (hpar : (cs).simple i * v = v * (cs).simple (F.op i))
    {z : K} (hz : z ∈ bruhatCell hct v) :
    ∃ x ∈ D.rootGroup (Pi.single i 1),
      (n i)⁻¹ * x⁻¹ * z * F.φ x * n (F.op i) ∉ bruhatCell hct v := by
  classical
  set i' := F.op i with hi'
  have hpar' : (cs).simple i * v = v * (cs).simple i' := by rw [hi']; exact hpar
  have hni : (n i)⁻¹ = n i := inv_eq_of_mul_eq_one_right (hsq i)
  have hni' : (n i')⁻¹ = n i' := inv_eq_of_mul_eq_one_right (hsq i')
  have hX0 : ∀ j : Fin D.rank, R.X j 0 = 1 := by
    intro j
    have h : R.X j 0 = R.X j 0 * R.X j 0 := by simpa using R.X_add j 0 0
    exact (mul_left_cancel
      (show R.X j 0 * 1 = R.X j 0 * R.X j 0 by rw [mul_one]; exact h)).symm
  have hXinv : ∀ (j : Fin D.rank) (a : R.Fld), (R.X j a)⁻¹ = R.X j (-a) := by
    intro j a
    exact inv_eq_of_mul_eq_one_right (by rw [← R.X_add j a (-a), add_neg_cancel, hX0 j])
  have hXmem : ∀ (j : Fin D.rank) (a : R.Fld), R.X j a ∈ D.rootGroup (Pi.single j 1) := by
    intro j a
    have hy : R.X j a ∈ Set.range (R.X j) := Set.mem_range_self a
    rwa [R.X_range j] at hy
  obtain ⟨b1, hb1, b2, hb2, hz_eq⟩ := hz
  obtain ⟨t1, ht1, u1, hu1, y1, hy1, hb1_eq⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hb1
  obtain ⟨d1, hd1⟩ : ∃ d1 : R.Fld, R.X i d1 = y1 := by
    have : y1 ∈ Set.range (R.X i) := by rw [R.X_range i]; exact hy1
    exact this
  obtain ⟨t2, ht2, u2, hu2, y2, hy2, hb2_eq⟩ :=
    exists_eq_mul_mul_of_mem_borel hct hext i' hb2
  obtain ⟨d2, hd2⟩ : ∃ d2 : R.Fld, R.X i' d2 = y2 := by
    have : y2 ∈ Set.range (R.X i') := by rw [R.X_range i']; exact hy2
    exact this
  obtain ⟨s1, hs1ne, hs1⟩ := R.torus_X i t1⁻¹ (inv_mem ht1)
  have hs1' : ∀ c : R.Fld, t1⁻¹ * R.X i c * t1 = R.X i (s1 * c) := by
    intro c; simpa using hs1 c
  obtain ⟨σ, hσne, hσ⟩ := R.nrep_X v i i' hpar' hasc
  obtain ⟨s2, hs2ne, hs2⟩ := R.torus_X i' t2⁻¹ (inv_mem ht2)
  have hs2' : ∀ c : R.Fld, t2⁻¹ * R.X i' c * t2 = R.X i' (s2 * c) := by
    intro c; simpa using hs2 c
  have hlen : (cs).length (v * (cs).simple i') = (cs).length v + 1 := by
    rw [← hpar']
    exact (cs).not_isLeftDescent_iff.mp hasc
  have hC : n i * nrep hct v = nrep hct v * n i' := by
    rw [← nrep_simple_mul hct hasc, hpar',
      nrep_mul hct (by rw [hlen, (cs).length_simple i']), nrep_simple hct i']
  let yfun : R.Fld → R.Fld := fun c => s2 * (σ * (d1 - s1 * c)) + d2 + R.θ c
  have hyfun : ∃ c, yfun c ≠ 0 := by
    by_contra h
    have hall : ∀ c, yfun c = 0 := fun c => not_not.mp (not_exists.mp h c)
    have hA : s2 * (σ * d1) + d2 = 0 := by
      have h0 := hall 0
      simpa [yfun] using h0
    have hB : s2 * (σ * s1) = 1 := by
      have h1 := hall 1
      have key : yfun 1 - (s2 * (σ * d1) + d2) = 0 := by rw [h1, hA, sub_zero]
      have e : yfun 1 - (s2 * (σ * d1) + d2) = 1 - s2 * (σ * s1) := by
        simp only [yfun, map_one]; ring
      have hzero : (1 : R.Fld) - s2 * (σ * s1) = 0 := by rwa [e] at key
      exact (sub_eq_zero.mp hzero).symm
    have htheta : ∀ c, R.θ c = c := by
      intro c
      have hc := hall c
      have key : yfun c - (s2 * (σ * d1) + d2) = 0 := by rw [hc, hA, sub_zero]
      have e : yfun c - (s2 * (σ * d1) + d2) = R.θ c - s2 * (σ * s1) * c := by
        simp only [yfun]; ring
      have hzero : R.θ c - s2 * (σ * s1) * c = 0 := by rwa [e] at key
      rw [sub_eq_zero.mp hzero, hB, one_mul]
    obtain ⟨c0, hc0⟩ := R.θ_ne
    exact hc0 (htheta c0)
  obtain ⟨c, hc⟩ := hyfun
  let e : R.Fld := d1 - s1 * c
  have hy : yfun c = s2 * (σ * e) + d2 + R.θ c := rfl
  set u1' : K := R.X i (s1 * (-c)) * u1 * (R.X i (s1 * (-c)))⁻¹ with hu1'_def
  have hu1'_mem : u1' ∈ posUnipotentExcept D i := by
    rw [hu1'_def]
    exact (Subgroup.mem_normalizer_iff.mp
      (rootGroup_single_le_normalizer hext i (hXmem i (s1 * (-c)))) u1).mp hu1
  have hu1'_eq : R.X i (s1 * (-c)) * u1 = u1' * R.X i (s1 * (-c)) := by
    rw [hu1'_def]; group
  have hAeq : (R.X i c)⁻¹ * b1 = t1 * u1' * R.X i e := by
    rw [hb1_eq, ← hd1, hXinv i c]
    calc R.X i (-c) * (t1 * u1 * R.X i d1)
        = t1 * R.X i (s1 * (-c)) * u1 * R.X i d1 := by
            rw [show R.X i (-c) * (t1 * u1 * R.X i d1)
                = t1 * (t1⁻¹ * R.X i (-c) * t1) * u1 * R.X i d1 by group, hs1' (-c)]
      _ = t1 * u1' * R.X i (s1 * (-c)) * R.X i d1 := by
            rw [show t1 * R.X i (s1 * (-c)) * u1 * R.X i d1
                = t1 * (R.X i (s1 * (-c)) * u1) * R.X i d1 by group, hu1'_eq]
            group
      _ = t1 * u1' * (R.X i (s1 * (-c)) * R.X i d1) := by group
      _ = t1 * u1' * R.X i (s1 * (-c) + d1) := by rw [R.X_add i (s1 * (-c)) d1]
      _ = t1 * u1' * R.X i e := by
            rw [show s1 * (-c) + d1 = d1 - s1 * c by ring]
  have hmid : n i * R.X i e * nrep hct v = (n i * nrep hct v) * R.X i' (σ * e) := by
    have e1 : n i * R.X i e * nrep hct v
        = (n i * nrep hct v) * ((nrep hct v)⁻¹ * R.X i e * nrep hct v) := by group
    rw [e1, hσ e]
  have hB2 : (n i)⁻¹ * (t1 * u1' * R.X i e) * nrep hct v
      = ((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i) * (n i * nrep hct v)
          * R.X i' (σ * e) := by
    have e1 : (n i)⁻¹ * (t1 * u1' * R.X i e) * nrep hct v
        = ((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i)
            * ((n i)⁻¹ * R.X i e * nrep hct v) := by group
    have e2 : (n i)⁻¹ * R.X i e * nrep hct v = n i * R.X i e * nrep hct v := by rw [hni]
    rw [e1, e2, hmid]
    group
  set u2' : K := R.X i' (s2 * (σ * e)) * u2 * (R.X i' (s2 * (σ * e)))⁻¹ with hu2'_def
  have hu2'_mem : u2' ∈ posUnipotentExcept D i' := by
    rw [hu2'_def]
    exact (Subgroup.mem_normalizer_iff.mp
      (rootGroup_single_le_normalizer hext i' (hXmem i' (s2 * (σ * e)))) u2).mp hu2
  have hu2'_eq : R.X i' (s2 * (σ * e)) * u2 = u2' * R.X i' (s2 * (σ * e)) := by
    rw [hu2'_def]; group
  have hβeq : R.X i' (σ * e) * b2 * R.X i' (R.θ c) = t2 * u2' * R.X i' (yfun c) := by
    rw [hb2_eq, ← hd2]
    calc R.X i' (σ * e) * (t2 * u2 * R.X i' d2) * R.X i' (R.θ c)
        = t2 * R.X i' (s2 * (σ * e)) * u2 * R.X i' d2 * R.X i' (R.θ c) := by
            rw [show R.X i' (σ * e) * (t2 * u2 * R.X i' d2) * R.X i' (R.θ c)
                = t2 * (t2⁻¹ * R.X i' (σ * e) * t2) * u2 * R.X i' d2
                    * R.X i' (R.θ c) by group, hs2' (σ * e)]
      _ = t2 * u2' * R.X i' (s2 * (σ * e)) * R.X i' d2 * R.X i' (R.θ c) := by
            rw [show t2 * R.X i' (s2 * (σ * e)) * u2 * R.X i' d2 * R.X i' (R.θ c)
                = t2 * (R.X i' (s2 * (σ * e)) * u2) * R.X i' d2
                    * R.X i' (R.θ c) by group, hu2'_eq]
            group
      _ = t2 * u2' * (R.X i' (s2 * (σ * e)) * R.X i' d2 * R.X i' (R.θ c)) := by group
      _ = t2 * u2' * R.X i' (s2 * (σ * e) + d2 + R.θ c) := by
            rw [← R.X_add i' (s2 * (σ * e)) d2,
              ← R.X_add i' (s2 * (σ * e) + d2) (R.θ c)]
      _ = t2 * u2' * R.X i' (yfun c) := by rw [hy]
  have hβn : n i' * (R.X i' (σ * e) * b2 * R.X i' (R.θ c)) * n i'
      = ((n i')⁻¹ * t2 * n i') * ((n i')⁻¹ * u2' * n i')
          * ((n i')⁻¹ * R.X i' (yfun c) * n i') := by
    rw [hβeq]
    calc n i' * (t2 * u2' * R.X i' (yfun c)) * n i'
        = (n i')⁻¹ * (t2 * u2' * R.X i' (yfun c)) * n i' := by rw [hni']
      _ = ((n i')⁻¹ * t2 * n i') * ((n i')⁻¹ * u2' * n i')
            * ((n i')⁻¹ * R.X i' (yfun c) * n i') := by group
  have hα' : Pi.single i' 1 ∈ D.roots := (Φ).single_mem i'
  have hw_mem : (n i')⁻¹ * R.X i' (yfun c) * n i' ∈ D.rootGroup (-Pi.single i' 1) := by
    have h := hct.conj_mem i' (Pi.single i' 1) hα' (R.X i' (yfun c)) (hXmem i' (yfun c))
    rw [weylAction_simple_single D.isFiniteType i'] at h
    simpa [hni'] using h
  have hw_ne : (n i')⁻¹ * R.X i' (yfun c) * n i' ≠ 1 := by
    intro h1
    have h2 : R.X i' (yfun c) = 1 := by
      have e : R.X i' (yfun c)
          = n i' * ((n i')⁻¹ * R.X i' (yfun c) * n i') * (n i')⁻¹ := by group
      rw [e, h1]
      group
    have h3 : yfun c = 0 := by
      apply R.X_inj i'
      rw [h2, hX0 i']
    exact hc h3
  have hw_cell : (n i')⁻¹ * R.X i' (yfun c) * n i' ∈ bruhatCell hct ((cs).simple i') :=
    q2nPE_neg_single_mem_bruhatCell hct hext hsq hw_mem hw_ne
  have ht'B : (n i')⁻¹ * t2 * n i' ∈ borel D H :=
    iSup_le_borel (inv_conj_n_mem_iSup hct i' ht2)
  have hu''B : (n i')⁻¹ * u2' * n i' ∈ borel D H := by
    simpa [hni'] using posUnipotent_le_borel
      (posUnipotentExcept_le_posUnipotent i' (conj_n_mem_posUnipotentExcept hct i' hu2'_mem))
  have htuw_cell : ((n i')⁻¹ * t2 * n i') * ((n i')⁻¹ * u2' * n i')
        * ((n i')⁻¹ * R.X i' (yfun c) * n i') ∈ bruhatCell hct ((cs).simple i') :=
    mul_mem_bruhatCell hct (mul_mem ht'B hu''B) hw_cell
  have hv_tuw : nrep hct v * (((n i')⁻¹ * t2 * n i') * ((n i')⁻¹ * u2' * n i')
        * ((n i')⁻¹ * R.X i' (yfun c) * n i')) ∈ bruhatCell hct (v * (cs).simple i') := by
    have h1 := Set.mul_mem_mul (nrep_mem_bruhatCell hct v) htuw_cell
    rwa [q2nPE_cell_mul_simple_add hct hext hlen] at h1
  have hu1'_B : (n i)⁻¹ * u1' * n i ∈ borel D H := by
    simpa [hni] using posUnipotent_le_borel
      (posUnipotentExcept_le_posUnipotent i (conj_n_mem_posUnipotentExcept hct i hu1'_mem))
  have hb'' : ((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i) ∈ borel D H :=
    mul_mem (iSup_le_borel (inv_conj_n_mem_iSup hct i ht1)) hu1'_B
  have hmain : (n i)⁻¹ * (R.X i c)⁻¹ * z * F.φ (R.X i c) * n i'
      = ((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i)
          * (nrep hct v * (((n i')⁻¹ * t2 * n i') * ((n i')⁻¹ * u2' * n i')
            * ((n i')⁻¹ * R.X i' (yfun c) * n i'))) := by
    rw [hz_eq]
    calc (n i)⁻¹ * (R.X i c)⁻¹ * (b1 * nrep hct v * b2) * F.φ (R.X i c) * n i'
        = (n i)⁻¹ * ((R.X i c)⁻¹ * b1) * nrep hct v
            * (b2 * F.φ (R.X i c)) * n i' := by group
      _ = (n i)⁻¹ * (t1 * u1' * R.X i e) * nrep hct v
            * (b2 * R.X i' (R.θ c)) * n i' := by
            rw [hAeq, show F.φ (R.X i c) = R.X i' (R.θ c) from R.φ_X i c]
      _ = (((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i) * (n i * nrep hct v)
            * R.X i' (σ * e)) * (b2 * R.X i' (R.θ c)) * n i' := by rw [hB2]
      _ = ((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i) * nrep hct v
            * (n i' * (R.X i' (σ * e) * b2 * R.X i' (R.θ c)) * n i') := by
            rw [hC]; group
      _ = ((n i)⁻¹ * t1 * n i) * ((n i)⁻¹ * u1' * n i)
            * (nrep hct v * (((n i')⁻¹ * t2 * n i') * ((n i')⁻¹ * u2' * n i')
              * ((n i')⁻¹ * R.X i' (yfun c) * n i'))) := by
            rw [hβn]; group
  have hzx_cell : (n i)⁻¹ * (R.X i c)⁻¹ * z * F.φ (R.X i c) * n i'
      ∈ bruhatCell hct (v * (cs).simple i') := by
    rw [hmain]
    exact mul_mem_bruhatCell hct hb'' hv_tuw
  refine ⟨R.X i c, hXmem i c, ?_⟩
  intro hmem
  have heq : v * (cs).simple i' = v := eq_of_mem_bruhatCell hct hext hzx_cell hmem
  have h1 : (cs).simple i' = 1 :=
    mul_left_cancel (show v * (cs).simple i' = v * 1 by rw [mul_one]; exact heq)
  exact (cs).simple_ne_one i' h1

include hext hw₀ hsq in
theorem stdPanel_of_rankOneField (R : RankOneField hct F) :
    StdPanel hct F n₀ := by
  intro i x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rcases q2nPE_panel_dichotomy hct F n₀ hext hw₀ hsq g i with
      hd | ⟨x0, hx0, hd'⟩ | ⟨hnd, hpar, hall⟩
  · obtain ⟨u, hu, hlt⟩ := q2nPE_panel_of_descent hct F n₀ hext hw₀ hsq g i hd
    exact ⟨(g : K ⧸ borel D H), self_mem_residue _ _, u, hu, hlt⟩
  · obtain ⟨u, hu, hlt⟩ := q2nPE_panel_of_descent hct F n₀ hext hw₀ hsq (g * x0 * n i) i hd'
    have hg' : ((g * x0 * n i : K) : K ⧸ borel D H) ∈
        residue (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) {i}
          (g : K ⧸ borel D H) := by
      refine Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨i, by simp, ?_⟩
      rw [stdδ_mk_eq_iff hct hext g (g * x0 * n i) ((cs).simple i)]
      rw [show g⁻¹ * (g * x0 * n i) = x0 * n i by group]
      exact mul_mem_bruhatCell hct
        (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hx0)
        (by rw [← nrep_simple hct i]; exact nrep_mem_bruhatCell hct ((cs).simple i))
    have hu' : u ∈ residue (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) {i}
        (g : K ⧸ borel D H) := mem_residue_trans hg' hu
    exact ⟨_, hg', u, hu', hlt⟩
  · exfalso
    have hz : g⁻¹ * (n₀ * F.φ g) ∈
        bruhatCell hct (stdδ hct (g : K ⧸ borel D H)
          (stdFlip F n₀ (g : K ⧸ borel D H))) :=
      (stdδ_flip_mk_eq_iff hct F hext hw₀ n₀ g _).mp rfl
    obtain ⟨x1, hx1, hx1not⟩ := q2nPE_not_parallel hct F hext hsq R hnd hpar hz
    exact hx1not (hall x1 hx1)

end CFSG.ClassicalInvolution.Phan.PhanE
