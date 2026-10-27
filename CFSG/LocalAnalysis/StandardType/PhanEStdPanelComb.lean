module

public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped Pointwise

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
  (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

private theorem q2nPE_exchange {v : W} {i j : Fin D.rank}
    (hi : ¬ (cs).IsLeftDescent v i) (hj : ¬ (cs).IsRightDescent v j)
    (hij : (cs).IsRightDescent ((cs).simple i * v) j) :
    (cs).simple i * v * (cs).simple j = v := by
  obtain ⟨ω, hω, rfl⟩ := (cs).exists_isReduced v
  have hdes : (cs).IsRightDescent ((cs).wordProd (i :: ω)) j := by
    rwa [(cs).wordProd_cons]
  obtain ⟨k, hk, hke⟩ := (cs).strongExchange_right (ω := i :: ω)
    (((cs).isRightInversion_simple_iff_isRightDescent _ j).mpr hdes)
  rcases k with _ | k
  · rw [← (cs).wordProd_cons, hke]
    simp
  · exfalso
    have hklen : k < ω.length := by
      have := hk
      simp only [List.length_cons] at this
      omega
    rw [(cs).wordProd_cons, List.eraseIdx_cons_succ, (cs).wordProd_cons] at hke
    have hvs : (cs).wordProd ω * (cs).simple j = (cs).wordProd (ω.eraseIdx k) := by
      have h' := congrArg (fun x => (cs).simple i * x) hke
      simpa only [mul_assoc, (cs).simple_mul_simple_cancel_left] using h'
    have hlen_vs : (cs).length ((cs).wordProd ω * (cs).simple j) = ω.length + 1 := by
      rw [(cs).not_isRightDescent_iff.mp hj, hω.eq]
    have hle : (cs).length ((cs).wordProd ω * (cs).simple j) ≤ (ω.eraseIdx k).length := by
      rw [hvs]
      exact (cs).length_wordProd_le _
    have herase : (ω.eraseIdx k).length + 1 = ω.length := List.length_eraseIdx_add_one hklen
    omega

include hext hsq in
private theorem q2nPE_panel_cell_mem (g : K) (i : Fin D.rank) {v : W}
    (hz : g⁻¹ * (n₀ * F.φ g) ∈ bruhatCell hct v)
    (hv : ¬ (cs).IsLeftDescent v i) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) :
    (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) ∈
      bruhatCell hct ((cs).simple i * v) * bruhatCell hct ((cs).simple (F.op i)) := by
  have hxB : x ∈ borel D H := rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hx
  have hxinvB : x⁻¹ ∈ borel D H := inv_mem hxB
  have hphiB : F.φ x ∈ borel D H := F.borel_map (Subgroup.mem_map_of_mem F.φ hxB)
  have hmid : x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x ∈ bruhatCell hct v :=
    mul_mem_bruhatCell_right hct (mul_mem_bruhatCell hct hxinvB hz) hphiB
  have hni : n i ∈ bruhatCell hct ((cs).simple i) := by
    rw [← nrep_simple hct i]
    exact nrep_mem_bruhatCell hct _
  have hni_inv : (n i)⁻¹ ∈ bruhatCell hct ((cs).simple i) := by
    rw [inv_eq_of_mul_eq_one_right (hsq i)]
    exact hni
  have hni' : n (F.op i) ∈ bruhatCell hct ((cs).simple (F.op i)) := by
    rw [← nrep_simple hct (F.op i)]
    exact nrep_mem_bruhatCell hct _
  have hleft : (n i)⁻¹ * (x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x) ∈
      bruhatCell hct ((cs).simple i) * bruhatCell hct v := Set.mul_mem_mul hni_inv hmid
  rw [q2nPE_simple_cell_mul_add hct hext hv] at hleft
  rw [show (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) =
      ((n i)⁻¹ * (x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x)) * n (F.op i) by group]
  exact Set.mul_mem_mul hleft hni'

include hext hw₀ hsq in
theorem q2nPE_panel_of_descent (g : K) (i : Fin D.rank)
    (hd : (cs).IsLeftDescent (stdδ hct (g : K ⧸ borel D H)
      (stdFlip F n₀ (g : K ⧸ borel D H))) i) :
    ∃ u ∈ residue (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) {i}
        (g : K ⧸ borel D H),
      (cs).length (stdδ hct u (stdFlip F n₀ (g : K ⧸ borel D H))) <
        (cs).length (stdδ hct (g : K ⧸ borel D H)
          (stdFlip F n₀ (g : K ⧸ borel D H))) := by
  set v := stdδ hct (g : K ⧸ borel D H)
    (stdFlip F n₀ (g : K ⧸ borel D H))
  set v' := (cs).simple i * v with hv'
  have hni : ¬ (cs).IsLeftDescent v' i := by
    rw [hv']
    exact (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hd
  have hlt : (cs).length v' < (cs).length v := by
    rw [hv']
    exact hd
  have hsv : (cs).simple i * v' = v := by
    rw [hv']
    exact (cs).simple_mul_simple_cancel_left i
  have hcell : bruhatCell hct v = bruhatCell hct ((cs).simple i) * bruhatCell hct v' := by
    rw [← hsv, q2nPE_simple_cell_mul_add hct hext hni]
  have hz : g⁻¹ * (n₀ * F.φ g) ∈ bruhatCell hct v :=
    (stdδ_flip_mk_eq_iff hct F hext hw₀ n₀ g v).mp rfl
  obtain ⟨p, hp, d, hdcell, hpd⟩ := Set.mem_mul.mp (hcell ▸ hz)
  obtain ⟨P, hP, hres⟩ := std_residue_mk hct hext ({i} : Set (Fin D.rank))
  have hpP : p ∈ P := by
    change p ∈ (P : Set K)
    rw [hP]
    exact Set.mem_iUnion₂.mpr
      ⟨(cs).simple i, Subgroup.subset_closure ⟨i, by simp, rfl⟩, hp⟩
  refine ⟨((g * p : K) : K ⧸ borel D H), ?_, ?_⟩
  · rw [hres g]
    refine ⟨g * p, ?_, rfl⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hgp : g⁻¹ • (g * p) = p := by rw [smul_eq_mul]; group
    rwa [hgp]
  · have hδ : stdδ hct ((g * p : K) : K ⧸ borel D H)
        (stdFlip F n₀ (g : K ⧸ borel D H)) = v' := by
      rw [stdFlip_mk]
      rw [stdδ_mk_eq_iff hct hext (g * p) (n₀ * F.φ g) v']
      rw [show (g * p)⁻¹ * (n₀ * F.φ g) =
          p⁻¹ * (g⁻¹ * (n₀ * F.φ g)) by group, ← hpd]
      rw [show p⁻¹ * (p * d) = d by group]
      exact hdcell
    rw [hδ]
    exact hlt

include hext hw₀ hsq in
theorem q2nPE_panel_dichotomy (g : K) (i : Fin D.rank) :
    (cs).IsLeftDescent (stdδ hct (g : K ⧸ borel D H)
        (stdFlip F n₀ (g : K ⧸ borel D H))) i ∨
      (∃ x ∈ D.rootGroup (Pi.single i 1),
        (cs).IsLeftDescent (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
          (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H))) i) ∨
      (¬ (cs).IsLeftDescent (stdδ hct (g : K ⧸ borel D H)
          (stdFlip F n₀ (g : K ⧸ borel D H))) i ∧
        (cs).simple i * stdδ hct (g : K ⧸ borel D H)
            (stdFlip F n₀ (g : K ⧸ borel D H)) =
          stdδ hct (g : K ⧸ borel D H) (stdFlip F n₀ (g : K ⧸ borel D H)) *
            (cs).simple (F.op i) ∧
        ∀ x ∈ D.rootGroup (Pi.single i 1),
          (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) ∈
            bruhatCell hct (stdδ hct (g : K ⧸ borel D H)
              (stdFlip F n₀ (g : K ⧸ borel D H)))) := by
  set v := stdδ hct (g : K ⧸ borel D H)
    (stdFlip F n₀ (g : K ⧸ borel D H))
  set a := (cs).simple i * v with ha
  by_cases hA : (cs).IsLeftDescent v i
  · exact Or.inl hA
  · refine Or.inr ?_
    by_cases hB : ∃ x ∈ D.rootGroup (Pi.single i 1),
        (cs).IsLeftDescent (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
          (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H))) i
    · exact Or.inl hB
    · have hB' : ∀ x, x ∈ D.rootGroup (Pi.single i 1) →
          ¬ (cs).IsLeftDescent (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
            (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H))) i := by
        intro x hx hcon
        exact hB ⟨x, hx, hcon⟩
      have hz : g⁻¹ * (n₀ * F.φ g) ∈ bruhatCell hct v :=
        (stdδ_flip_mk_eq_iff hct F hext hw₀ n₀ g v).mp rfl
      have hlen_a : (cs).length a = (cs).length v + 1 := by
        rw [ha]
        exact (cs).not_isLeftDescent_iff.mp hA
      have h1a : (cs).simple i * a = v := by
        rw [ha]
        exact (cs).simple_mul_simple_cancel_left i
      have hdesca : (cs).IsLeftDescent a i := by
        show (cs).length ((cs).simple i * a) < (cs).length a
        rw [h1a, hlen_a]
        omega
      have key : ∀ x ∈ D.rootGroup (Pi.single i 1),
          (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
            (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H))) =
            a * (cs).simple (F.op i) := by
        intro x hx
        have hcellx := q2nPE_panel_cell_mem hct F n₀ hext hsq g i hz hA hx
        have hzx : (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) ∈
            bruhatCell hct (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
              (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H))) := by
          rw [show (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) =
              (g * x * n i)⁻¹ * (n₀ * F.φ (g * x * n i)) by
            rw [map_mul, map_mul, F.n_map i]; group]
          exact (stdδ_flip_mk_eq_iff hct F hext hw₀ n₀ (g * x * n i)
            (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
              (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H)))).mp rfl
        rcases (cs).length_mul_simple a (F.op i) with hup | hdown
        · rw [q2nPE_cell_mul_simple_add hct hext hup] at hcellx
          exact eq_of_mem_bruhatCell hct hext hzx hcellx
        · rw [q2nPE_cell_mul_simple_sub hct hext hdown] at hcellx
          rcases hcellx with hcellx | hcellx
          · exact eq_of_mem_bruhatCell hct hext hzx hcellx
          · exfalso
            exact hB' x hx (by rw [eq_of_mem_bruhatCell hct hext hzx hcellx]; exact hdesca)
      have h1 : ¬ (cs).IsLeftDescent (a * (cs).simple (F.op i)) i := by
        have h := hB' 1 (one_mem _)
        rwa [key 1 (one_mem _)] at h
      have hsi : (cs).simple i * (a * (cs).simple (F.op i)) = v * (cs).simple (F.op i) := by
        rw [← mul_assoc, h1a]
      have hnot : (cs).length (v * (cs).simple (F.op i)) =
          (cs).length (a * (cs).simple (F.op i)) + 1 := by
        have h := (cs).not_isLeftDescent_iff.mp h1
        rwa [hsi] at h
      have hlen_as : (cs).length (a * (cs).simple (F.op i)) = (cs).length v := by
        rcases (cs).length_mul_simple a (F.op i) with hup | hdown
        · exfalso
          rw [hup, hlen_a] at hnot
          have hle := (cs).length_mul_le v ((cs).simple (F.op i))
          rw [(cs).length_simple] at hle
          omega
        · omega
      have hright_a : (cs).IsRightDescent a (F.op i) := by
        rw [(cs).isRightDescent_iff]
        omega
      have hnright_v : ¬ (cs).IsRightDescent v (F.op i) := by
        rw [(cs).not_isRightDescent_iff]
        omega
      have hex := q2nPE_exchange hA hnright_v hright_a
      have ha_eq : a * (cs).simple (F.op i) = v := by
        rw [ha]
        exact hex
      have hconj : (cs).simple i * v = v * (cs).simple (F.op i) := by
        have h := congrArg (fun u => u * (cs).simple (F.op i)) hex
        simpa only [mul_assoc, (cs).simple_mul_simple_self, mul_one] using h
      refine Or.inr ⟨hA, ?_, ?_⟩
      · exact hconj
      · intro x hx
        have hzx : (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) ∈
            bruhatCell hct (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
              (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H))) := by
          rw [show (n i)⁻¹ * x⁻¹ * (g⁻¹ * (n₀ * F.φ g)) * F.φ x * n (F.op i) =
              (g * x * n i)⁻¹ * (n₀ * F.φ (g * x * n i)) by
            rw [map_mul, map_mul, F.n_map i]; group]
          exact (stdδ_flip_mk_eq_iff hct F hext hw₀ n₀ (g * x * n i)
            (stdδ hct ((g * x * n i : K) : K ⧸ borel D H)
              (stdFlip F n₀ ((g * x * n i : K) : K ⧸ borel D H)))).mp rfl
        rw [key x hx, ha_eq] at hzx
        exact hzx

end CFSG.ClassicalInvolution.Phan.PhanE
