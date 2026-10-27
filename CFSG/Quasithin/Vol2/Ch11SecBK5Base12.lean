module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11
public import CFSG.Quasithin.Vol2.Ch11G2Q8Gen
public import CFSG.Quasithin.Background.HTriSp4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)
open Matrix

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in

theorem single_mem_stdF {h j : ℕ} (hj : j < h) (hj6 : j < 6) :
    (Pi.single (bv j) 1 : Ix3 → K) ∈ stdF K h := by
  refine mem_stdF.mpr fun k hk => ?_
  have hk' : k ≠ bv j := by
    rintro rfl
    rw [ht_bv hj6] at hk
    omega
  rw [Pi.single_apply, ite_eq_right hk']

theorem g2Act_single_apply (g : ↥(cayleyGroup K)) (k k' : Ix3) :
    g2Act g (Pi.single k' 1) k = ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
      (e6 k) (e6 k') := by
  rw [g2Six_apply]
  change _ = g2Act g (Pi.single (bv (ht k')) 1) (bv (ht k))
  rw [← eq_bv_of_ht (k := k') rfl, ← eq_bv_of_ht (k := k) rfl]

theorem maps_of_mem_flagStab {g : ↥(cayleyGroup K)} {h : ℕ}
    (hg : g2Six g ∈ Tri.flagStab 6 h K) {w : Ix3 → K} (hw : w ∈ stdF K h) :
    g2Act g w ∈ stdF K h := by
  refine mem_stdF.mpr fun k hk => ?_
  rw [← g2Mat_mulVec, mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rcases Nat.lt_or_ge (ht k') h with hlt | hge
  · rw [g2Mat_apply, g2Act_single_apply,
      Tri.mem_flagStab.mp hg (e6 k) (e6 k') (by exact hlt) (by exact hk), zero_mul]
  · rw [hw k' hge, mul_zero]

theorem g2Six_mem_flagStab_iff {g : ↥(cayleyGroup K)} {h : ℕ} :
    g2Six g ∈ Tri.flagStab 6 h K ↔ g ∈ stabQ (stdF K h) := by
  constructor
  · intro hg
    have hg' : g2Six g⁻¹ ∈ Tri.flagStab 6 h K := by
      rw [map_inv]
      exact (Tri.flagStab 6 h K).inv_mem hg
    refine mem_stabQ.mpr fun w => ⟨fun hw => maps_of_mem_flagStab hg hw, fun hw => ?_⟩
    have := maps_of_mem_flagStab hg' hw
    rwa [g2Act_inv_apply] at this
  · intro hg
    refine Tri.mem_flagStab.mpr fun i j hj hi => ?_
    rw [g2Six_apply]
    exact (mem_stabQ.mp hg _).mp (single_mem_stdF hj j.2) (bv i) (by rw [ht_bv i.2]; exact hi)

theorem g2Six_mem_uniGL {u : ↥(cayleyGroup K)} (hu : u ∈ U0 K) : g2Six u ∈ Tri.uniGL 6 K := by
  have hbv : ∀ i j : Fin 6, i ≠ j → bv (i : ℕ) ≠ bv (j : ℕ) := fun i j hij h =>
    hij (Fin.ext (by rw [← ht_bv i.2, ← ht_bv j.2, h]))
  refine Tri.mem_uniGL_of (fun i j hij => ?_) (fun i => ?_)
  · have h1 := (mem_U0.mp hu) j (Pi.single (bv j) 1) (single_mem_stdF (by omega) j.2) (bv i)
      (by rw [ht_bv i.2]; exact le_of_lt hij)
    rw [Pi.sub_apply, sub_eq_zero] at h1
    rw [g2Six_apply, h1, Pi.single_apply, ite_eq_right (hbv i j (ne_of_gt hij))]
  · have h1 := (mem_U0.mp hu) i (Pi.single (bv i) 1) (single_mem_stdF (by omega) i.2) (bv i)
      (by rw [ht_bv i.2])
    rw [Pi.sub_apply, sub_eq_zero] at h1
    rw [g2Six_apply, h1, Pi.single_eq_same]

theorem map_g2Six_U0_le : (U0 K).map g2Six ≤ Tri.uniGL 6 K := by
  rintro _ ⟨u, hu, rfl⟩
  exact g2Six_mem_uniGL hu

theorem map_topHom_two_g2 {Q : Subgroup (GL (Fin 6) K)} (hQ : Q ≤ Tri.flagStab 6 2 K)
    (hUQ : (U0 K).map g2Six ≤ Q) :
    (((U0 K).map g2Six).subgroupOf Q).map (Tri.topHom (by norm_num : 2 ≤ 6) hQ) =
      Tri.uni2 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hlow, hdiag⟩ := Tri.uniGL_entries (map_g2Six_U0_le hu)
    refine Tri.mem_rootGL.mpr ⟨((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 1, ?_⟩
    apply Units.ext
    change Tri.topMat (by norm_num : 2 ≤ 6) ((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      transvection (0 : Fin 2) 1 _
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Tri.topMat, transvection] using hdiag 0
    · simp [Tri.topMat, transvection]
    · simpa [Tri.topMat, transvection] using hlow 1 0 (by decide)
    · simpa [Tri.topMat, transvection] using hdiag 1
  · rintro _ ⟨c, rfl⟩
    have hmem : g2Six (g2Y ![0, Multiplicative.toAdd c, 0]) ∈ (U0 K).map g2Six :=
      ⟨_, g2Y_mem_U0 _ 0, rfl⟩
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    change Tri.topMat (by norm_num : 2 ≤ 6) ((g2Six (g2Y ![0, Multiplicative.toAdd c, 0]) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      transvection (0 : Fin 2) 1 (Multiplicative.toAdd c)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Tri.topMat, g2Six_apply, g2Act_g2Y_e12, transvection, bv, q6, Pi.single_apply]

@[expose] noncomputable def uF3 (x y z : K) : ↥(cayleyGroup K) :=
  g2Y ![0, x, z - x * y] * g2A (uSL 0 0 y)

theorem uF3_mem_U0 (x y z : K) : uF3 x y z ∈ U0 K :=
  (U0 K).mul_mem (g2Y_mem_U0 _ _) (g2A_mem_U0 0 0 y)

theorem topMat_g2Y (x w : K) :
    Tri.topMat (by norm_num : 3 ≤ 6) ((g2Six (g2Y ![0, x, w]) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = !![1, x, w; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tri.topMat, g2Six_apply, g2Act_g2Y_e12, bv, q6, Pi.single_apply]

theorem topMat_g2A (y : K) :
    Tri.topMat (by norm_num : 3 ≤ 6) ((g2Six (g2A (uSL 0 0 y)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = !![1, 0, 0; 0, 1, y; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tri.topMat, g2Six_apply, g2Act_g2A_uSL, bv, q6, Pi.single_apply]

theorem topMat_uF3 (x y z : K) :
    Tri.topMat (by norm_num : 3 ≤ 6) ((g2Six (uF3 x y z) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = !![1, x, z; 0, 1, y; 0, 0, 1] := by
  have hlow := (Tri.uniGL_entries (g2Six_mem_uniGL (g2A_mem_U0 (F := K) 0 0 y))).1
  rw [uF3, map_mul, Units.val_mul, Tri.topMat_mul (by norm_num : 3 ≤ 6)
    (fun i j hj hi => hlow i j (Fin.lt_def.mpr (by omega))), topMat_g2Y, topMat_g2A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem map_topHom_three_g2 {Q : Subgroup (GL (Fin 6) K)} (hQ : Q ≤ Tri.flagStab 6 3 K)
    (hUQ : (U0 K).map g2Six ≤ Q) :
    (((U0 K).map g2Six).subgroupOf Q).map (Tri.topHom (by norm_num : 3 ≤ 6) hQ) =
      Tri.uni3 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hlow, hdiag⟩ := Tri.uniGL_entries (map_g2Six_U0_le hu)
    exact Tri.mem_uniGL_of (fun i j hij => hlow _ _ (Fin.lt_def.mpr (Fin.lt_def.mp hij)))
      (fun i => hdiag _)
  · intro v hv
    obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries hv
    have hmem : g2Six (uF3 ((v : Matrix (Fin 3) (Fin 3) K) 0 1) ((v : Matrix (Fin 3) (Fin 3) K) 1 2)
        ((v : Matrix (Fin 3) (Fin 3) K) 0 2)) ∈ (U0 K).map g2Six := ⟨_, uF3_mem_U0 _ _ _, rfl⟩
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    change Tri.topMat (by norm_num : 3 ≤ 6) ((g2Six (uF3 _ _ _) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = (v : Matrix (Fin 3) (Fin 3) K)
    rw [topMat_uF3]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using (hdiag 0).symm
    · rfl
    · rfl
    · simpa using (hlow 1 0 (by decide)).symm
    · simpa using (hdiag 1).symm
    · rfl
    · simpa using (hlow 2 0 (by decide)).symm
    · simpa using (hlow 2 1 (by decide)).symm
    · simpa using (hdiag 2).symm

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
