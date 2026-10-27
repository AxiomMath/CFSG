module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Planes
public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81BA5Frame

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

@[expose] def imgS0 (G : GL (Fin 6) K) : Submodule K (Fin 6 → K) :=
  (S0 K).map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K))

theorem s81A12_mem_S0 {v : Fin 6 → K} : v ∈ S0 K ↔ ∀ j : Fin 6, j.val % 2 = 1 → v j = 0 :=
  Iff.rfl

theorem s81A12_single_mem_S0 {j : Fin 6} (hj : j.val % 2 = 0) (c : K) :
    (Pi.single j c : Fin 6 → K) ∈ S0 K := by
  rw [s81A12_mem_S0]
  intro k hk
  have hkj : k ≠ j := by
    rintro rfl
    omega
  rw [Pi.single_apply, if_neg hkj]

theorem s81A12_transvection_mulVec (a b : Fin 6) (c : K) (v : Fin 6 → K) (i : Fin 6) :
    (Matrix.transvection a b c *ᵥ v) i = v i + (if i = a then c * v b else 0) := by
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]

theorem s81A12_mem_UnipGL_root {a b : Fin 6} (hab : a.val % 2 = 0 ∧ b.val % 2 = 1) (c : K) :
    transvGL K a b (rootSet_ne hab) c ∈ UnipGL K (S0 K) := by
  have hne : a ≠ b := rootSet_ne hab
  refine ⟨?_, ?_, ?_⟩
  · rw [transvGL_val]
    exact Matrix.det_transvection_of_ne a b hne c
  · intro v
    rw [transvGL_val, s81A12_mem_S0]
    intro j hj
    have hja : j ≠ a := by
      rintro rfl
      have := hab.1
      omega
    rw [Pi.sub_apply, s81A12_transvection_mulVec, if_neg hja]
    simp
  · intro s hs
    rw [transvGL_val]
    have hsb : s b = 0 := (s81A12_mem_S0.1 hs) b hab.2
    funext i
    rw [s81A12_transvection_mulVec, hsb, mul_zero]
    simp

theorem s81A12_entry_of_mem {g : GL (Fin 6) K} (hg : g ∈ UnipGL K (S0 K)) (i j : Fin 6)
    (h : i.val % 2 = 1 ∨ j.val % 2 = 0) :
    (g : Matrix (Fin 6) (Fin 6) K) i j = (1 : Matrix (Fin 6) (Fin 6) K) i j := by
  obtain ⟨-, h2, h3⟩ := hg
  rcases h with hi | hj
  · have h4 := s81A12_mem_S0.1 (h2 (Pi.single j (1 : K))) i hi
    simp only [Pi.sub_apply, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at h4
    rw [Matrix.one_apply]
    exact sub_eq_zero.1 h4
  · have h4 := congrFun (h3 _ (s81A12_single_mem_S0 hj 1)) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at h4
    rw [Matrix.one_apply]
    exact h4

theorem s81A12_matrix_eq (g : GL (Fin 6) K) (hg : g ∈ UnipGL K (S0 K)) :
    (g : Matrix (Fin 6) (Fin 6) K) = 1 + ∑ p ∈ Finset.univ.filter
      (fun p : Fin 6 × Fin 6 => p.1.val % 2 = 0 ∧ p.2.val % 2 = 1),
        Matrix.single p.1 p.2 ((g : Matrix (Fin 6) (Fin 6) K) p.1 p.2) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sum_apply]
  by_cases hij : i.val % 2 = 0 ∧ j.val % 2 = 1
  · have hmem : (i, j) ∈ Finset.univ.filter
        (fun p : Fin 6 × Fin 6 => p.1.val % 2 = 0 ∧ p.2.val % 2 = 1) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩
    have hne : i ≠ j := by
      rintro rfl
      omega
    rw [Finset.sum_eq_single_of_mem (i, j) hmem]
    · simp [Matrix.single_apply, Matrix.one_apply_ne hne]
    · intro p _ hp
      have hnot : ¬ (p.1 = i ∧ p.2 = j) := fun h => hp (Prod.ext h.1 h.2)
      simp [Matrix.single_apply, hnot]
  · have hsum : ∑ p ∈ Finset.univ.filter
        (fun p : Fin 6 × Fin 6 => p.1.val % 2 = 0 ∧ p.2.val % 2 = 1),
          Matrix.single p.1 p.2 ((g : Matrix (Fin 6) (Fin 6) K) p.1 p.2) i j = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hnot : ¬ (p.1 = i ∧ p.2 = j) := by
        rintro ⟨h1, h2⟩
        apply hij
        have hp2 := (Finset.mem_filter.1 hp).2
        rw [h1, h2] at hp2
        exact hp2
      simp [Matrix.single_apply, hnot]
    rw [hsum, add_zero]
    exact s81A12_entry_of_mem hg i j (by omega)

theorem s81A12_exists_mem (g : GL (Fin 6) K) (s : Finset (Fin 6 × Fin 6))
    (hs : ∀ p ∈ s, p.1.val % 2 = 0 ∧ p.2.val % 2 = 1) :
    ∃ h ∈ (U0 K).comap (rhoEquiv K), (h : Matrix (Fin 6) (Fin 6) K) =
      1 + ∑ p ∈ s, Matrix.single p.1 p.2 ((g : Matrix (Fin 6) (Fin 6) K) p.1 p.2) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert x s hx ih =>
    obtain ⟨h, hh, hval⟩ := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
    have hx' : x.1.val % 2 = 0 ∧ x.2.val % 2 = 1 := hs x (Finset.mem_insert_self x s)
    have hr : rhoEquiv K (transvGL K x.1 x.2 (rootSet_ne hx') (g x.1 x.2)) ∈ rootSet K :=
      ⟨x.1, x.2, hx', g x.1 x.2, rfl⟩
    refine ⟨transvGL K x.1 x.2 (rootSet_ne hx') (g x.1 x.2) * h, mul_mem ?_ hh, ?_⟩
    · rw [Subgroup.mem_comap]
      exact Subgroup.subset_closure hr
    · have hNS : Matrix.single x.1 x.2 ((g : Matrix (Fin 6) (Fin 6) K) x.1 x.2) *
          ∑ p ∈ s, Matrix.single p.1 p.2 ((g : Matrix (Fin 6) (Fin 6) K) p.1 p.2) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := hs p (Finset.mem_insert_of_mem hp)
        have hne : x.2 ≠ p.1 := by
          intro h'
          have h1 := hx'.2
          have h2 := hp'.1
          rw [h'] at h1
          omega
        simp [Matrix.single_mul_single_of_ne, hne]
      rw [Units.val_mul, transvGL_val, hval, Finset.sum_insert hx]
      simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, hNS, add_zero]
      abel

theorem s81A12_Urad_le_U0 : Urad K (S0 K) ≤ U0 K := by
  rintro x ⟨g, hg, rfl⟩
  obtain ⟨h, hh, hval⟩ := s81A12_exists_mem g
    (Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1.val % 2 = 0 ∧ p.2.val % 2 = 1))
    (fun p hp => (Finset.mem_filter.1 hp).2)
  have hgh : g = h := Units.ext (by rw [hval]; exact s81A12_matrix_eq g hg)
  rw [hgh]
  exact Subgroup.mem_comap.1 hh

theorem U0_eq_Urad : U0 K = Urad K (S0 K) := by
  apply le_antisymm
  · show Subgroup.closure (rootSet K) ≤ Urad K (S0 K)
    rw [Subgroup.closure_le]
    rintro u ⟨a, b, hab, c, rfl⟩
    exact Subgroup.mem_map_of_mem (rhoEquiv K) (s81A12_mem_UnipGL_root hab c)
  · exact s81A12_Urad_le_U0

theorem s81A12_hId (G : GL (Fin 6) K) (S : Submodule K (Fin 6 → K)) :
    (S.map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K))).map
      (Matrix.mulVecLin ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = S := by
  rw [← Submodule.map_comp, ← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one,
    Submodule.map_id]

theorem s81A12_conj_mem (G : GL (Fin 6) K) (S : Submodule K (Fin 6 → K)) {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K S) :
    G * g * G⁻¹ ∈ UnipGL K (S.map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K))) := by
  obtain ⟨hdet, hS1, hS2⟩ := hg
  have hMG : (G : Matrix (Fin 6) (Fin 6) K) *
      ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv G
  have hGM : ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (G : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.inv_mul G
  have hconj : ∀ y : Fin 6 → K,
      ((G * g * G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ y =
        (G : Matrix (Fin 6) (Fin 6) K) *ᵥ ((g : Matrix (Fin 6) (Fin 6) K) *ᵥ
          (((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ y)) := by
    intro y
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hGinv : ∀ y : Fin 6 → K, (G : Matrix (Fin 6) (Fin 6) K) *ᵥ
      (((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hMG, Matrix.one_mulVec]
  have hGinv' : ∀ y : Fin 6 → K, ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
      ((G : Matrix (Fin 6) (Fin 6) K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hGM, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · show ((G * g * G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, hMG, Matrix.det_one]
  · intro v
    have key : ((G * g * G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v - v =
        (G : Matrix (Fin 6) (Fin 6) K) *ᵥ ((g : Matrix (Fin 6) (Fin 6) K) *ᵥ
          (((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v) -
          ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v) := by
      rw [Matrix.mulVec_sub, hconj v, hGinv v]
    rw [key]
    exact Submodule.mem_map_of_mem (hS1 _)
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hs
    show ((G * g * G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
      ((G : Matrix (Fin 6) (Fin 6) K) *ᵥ x) = (G : Matrix (Fin 6) (Fin 6) K) *ᵥ x
    rw [hconj, hGinv', hS2 x hx]

theorem s81A12_conj_mem_inv (G : GL (Fin 6) K) (S : Submodule K (Fin 6 → K)) {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K (S.map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)))) :
    G⁻¹ * g * G ∈ UnipGL K S := by
  have h1 := s81A12_conj_mem G⁻¹ _ hg
  rw [inv_inv, s81A12_hId] at h1
  exact h1

theorem conjSub_Urad (G : GL (Fin 6) K) (S : Submodule K (Fin 6 → K)) :
    conjSub (rhoEquiv K G) (Urad K S) =
      Urad K (S.map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K))) := by
  ext x
  rw [mem_conjSub]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hu
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem (rhoEquiv K) (s81A12_conj_mem G S hg)
  · rintro ⟨g', hg', rfl⟩
    refine ⟨rhoEquiv K (G⁻¹ * g' * G),
      Subgroup.mem_map_of_mem (rhoEquiv K) (s81A12_conj_mem_inv G S hg'), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, show G * (G⁻¹ * g' * G) * G⁻¹ = g' by group]

theorem mem_UnipGL_iff {S : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K} :
    g ∈ UnipGL K S ↔ (g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (∀ v, (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ S) ∧
      ∀ s ∈ S, (g : Matrix (Fin 6) (Fin 6) K).mulVec s = s :=
  Iff.rfl

theorem UnipGL_sub_mem {S : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K} (hg : g ∈ UnipGL K S)
    (v : Fin 6 → K) : (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ S :=
  (mem_UnipGL_iff.1 hg).2.1 v

theorem UnipGL_fix {S : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K} (hg : g ∈ UnipGL K S)
    {s : Fin 6 → K} (hs : s ∈ S) : (g : Matrix (Fin 6) (Fin 6) K).mulVec s = s :=
  (mem_UnipGL_iff.1 hg).2.2 s hs

theorem inf_UnipGL_fix_sup {S S' : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K S ⊓ UnipGL K S') {s : Fin 6 → K} (hs : s ∈ S ⊔ S') :
    (g : Matrix (Fin 6) (Fin 6) K).mulVec s = s := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
  rw [Matrix.mulVec_add, UnipGL_fix (Subgroup.mem_inf.1 hg).1 hy,
    UnipGL_fix (Subgroup.mem_inf.1 hg).2 hz]

theorem inf_UnipGL_sub_mem {S S' : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K S ⊓ UnipGL K S') (v : Fin 6 → K) :
    (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ S ⊓ S' :=
  Submodule.mem_inf.2 ⟨UnipGL_sub_mem (Subgroup.mem_inf.1 hg).1 v,
    UnipGL_sub_mem (Subgroup.mem_inf.1 hg).2 v⟩

theorem mem_Urad_iff {S : Submodule K (Fin 6 → K)} {x : Cube K ≃ₗ[K] Cube K} :
    x ∈ Urad K S ↔ ∃ g ∈ UnipGL K S, rhoEquiv K g = x :=
  Subgroup.mem_map

theorem rhoEquiv_mem_Urad_inf {S S' : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K S ⊓ UnipGL K S') : rhoEquiv K g ∈ Urad K S ⊓ Urad K S' :=
  Subgroup.mem_inf.2 ⟨mem_Urad_iff.2 ⟨g, (Subgroup.mem_inf.1 hg).1, rfl⟩,
    mem_Urad_iff.2 ⟨g, (Subgroup.mem_inf.1 hg).2, rfl⟩⟩

theorem rho_eq_of_unip {S S' : Submodule K (Fin 6 → K)} (hS : S ≠ ⊥)
    {g g' : GL (Fin 6) K} (hg : g ∈ UnipGL K S) (hg' : g' ∈ UnipGL K S')
    (h : rho K g = rho K g') : g = g' := by
  have h1 : rho K (1 : GL (Fin 6) K) = 1 :=
    (rho_eq_one_iff (1 : GL (Fin 6) K)).2 ⟨1, by simp, by simp⟩
  have hrel : rho K (g'⁻¹ * g) = 1 := by
    rw [rho_mul, h, ← rho_mul, inv_mul_cancel, h1]
  obtain ⟨l, -, hlg⟩ := (rho_eq_one_iff (g'⁻¹ * g)).1 hrel
  have hgl : (g : Matrix (Fin 6) (Fin 6) K) = l • (g' : Matrix (Fin 6) (Fin 6) K) := by
    have hg_eq : g = g' * (g'⁻¹ * g) := (mul_inv_cancel_left g' g).symm
    rw [hg_eq, Units.val_mul, hlg, Matrix.mul_smul, Matrix.mul_one]
  have hfix : ∀ s ∈ S, l • (g' : Matrix (Fin 6) (Fin 6) K).mulVec s = s := by
    intro s hs
    rw [← Matrix.smul_mulVec, ← hgl]
    exact UnipGL_fix hg hs
  have hl : l = 1 := by
    by_contra hl1
    have hne : (1 : K) - l ≠ 0 := sub_ne_zero.mpr (fun h' => hl1 h'.symm)
    have hSS' : ∀ s ∈ S, s ∈ S' := by
      intro s hs
      have key : (1 - l) • s = l • ((g' : Matrix (Fin 6) (Fin 6) K).mulVec s - s) := by
        rw [smul_sub, hfix s hs, sub_smul, one_smul]
      have hmem : (1 - l) • s ∈ S' := by
        rw [key]
        exact S'.smul_mem l (UnipGL_sub_mem hg' s)
      have h2 := S'.smul_mem (1 - l)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    have hls : l • s = s := by
      have h3 := hfix s hsS
      rwa [UnipGL_fix hg' (hSS' s hsS)] at h3
    have h4 : (l - 1) • s = 0 := by
      rw [sub_smul, one_smul, hls, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact hl1 (sub_eq_zero.1 h5)
    · exact hs0 h5
  apply Units.ext
  rw [hgl, hl, one_smul]

theorem det_one_add_of_mul_self_eq_zero {N : Matrix (Fin 6) (Fin 6) K} (hN : N * N = 0) :
    Matrix.det (1 + N) = 1 := by
  have hnil : IsNilpotent N := ⟨2, by rw [pow_two]; exact hN⟩
  have hu := Matrix.isUnit_charpolyRev_of_isNilpotent hnil
  unfold Matrix.charpolyRev at hu
  obtain ⟨r, -, hC⟩ := Polynomial.isUnit_iff.1 hu
  have hev : ∀ c : K,
      (Matrix.det (1 - (Polynomial.X : Polynomial K) • N.map Polynomial.C)).eval c =
        Matrix.det (1 - c • N) := by
    intro c
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
      ring
    · simp [Matrix.one_apply, hij]
      ring
  have h0 : r = 1 := by
    have h := hev 0
    rw [← hC, Polynomial.eval_C] at h
    simpa using h
  have h1 := hev (-1)
  rw [← hC, Polynomial.eval_C, h0] at h1
  have e : (1 : Matrix (Fin 6) (Fin 6) K) - (-1 : K) • N = 1 + N := by simp
  rw [e] at h1
  exact h1.symm

@[expose] noncomputable def unipHom (S S' : Submodule K (Fin 6 → K)) (g : GL (Fin 6) K)
    (hg : g ∈ UnipGL K S ⊓ UnipGL K S') : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S') :=
  Submodule.liftQ (S ⊔ S')
    (LinearMap.codRestrict (S ⊓ S')
      (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K) - LinearMap.id)
      (fun v => by simpa using inf_UnipGL_sub_mem hg v))
    (fun s hs => LinearMap.mem_ker.2 (Subtype.ext (by simp [inf_UnipGL_fix_sup hg hs])))

theorem unipHom_apply_mk {S S' : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K}
    (hg : g ∈ UnipGL K S ⊓ UnipGL K S') (v : Fin 6 → K) :
    ((unipHom S S' g hg (Submodule.Quotient.mk v) : ↥(S ⊓ S')) : Fin 6 → K) =
      (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v :=
  rfl

@[expose] noncomputable def unipLift (S S' : Submodule K (Fin 6 → K))
    (Y : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) : (Fin 6 → K) →ₗ[K] (Fin 6 → K) :=
  (S ⊓ S').subtype ∘ₗ (Y ∘ₗ (S ⊔ S').mkQ)

theorem unipLift_apply (S S' : Submodule K (Fin 6 → K))
    (Y : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) (v : Fin 6 → K) :
    unipLift S S' Y v = ((Y (Submodule.Quotient.mk v) : ↥(S ⊓ S')) : Fin 6 → K) :=
  rfl

theorem unipLift_mem_inf (S S' : Submodule K (Fin 6 → K))
    (Y : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) (v : Fin 6 → K) :
    unipLift S S' Y v ∈ S ⊓ S' := by
  rw [unipLift_apply]
  exact (Y _).2

theorem unipLift_eq_zero_of_mem_sup (S S' : Submodule K (Fin 6 → K))
    (Y : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) {s : Fin 6 → K} (hs : s ∈ S ⊔ S') :
    unipLift S S' Y s = 0 := by
  have h0 : (Submodule.Quotient.mk s : (Fin 6 → K) ⧸ (S ⊔ S')) = 0 :=
    (Submodule.Quotient.mk_eq_zero (S ⊔ S')).2 hs
  simp [unipLift_apply, h0]

theorem unipLift_unipLift (S S' : Submodule K (Fin 6 → K))
    (Y : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) (v : Fin 6 → K) :
    unipLift S S' Y (unipLift S S' Y v) = 0 :=
  unipLift_eq_zero_of_mem_sup S S' Y
    (Submodule.mem_sup_left (Submodule.mem_inf.1 (unipLift_mem_inf S S' Y v)).1)

theorem unipHom_surjective (S S' : Submodule K (Fin 6 → K))
    (Y : ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) :
    ∃ g : GL (Fin 6) K, ∃ hg : g ∈ UnipGL K S ⊓ UnipGL K S', unipHom S S' g hg = Y := by
  have hNN : LinearMap.toMatrix' (unipLift S S' Y) * LinearMap.toMatrix' (unipLift S S' Y) = 0 := by
    rw [← LinearMap.toMatrix'_comp]
    have h2 : (unipLift S S' Y).comp (unipLift S S' Y) = 0 :=
      LinearMap.ext fun v => unipLift_unipLift S S' Y v
    rw [h2, map_zero]
  have hdet1 : Matrix.det (1 + LinearMap.toMatrix' (unipLift S S' Y)) = 1 :=
    det_one_add_of_mul_self_eq_zero hNN
  have hdet : Matrix.det (1 + LinearMap.toMatrix' (unipLift S S' Y)) ≠ 0 := by
    rw [hdet1]
    exact one_ne_zero
  obtain ⟨g, hgN⟩ : ∃ g : GL (Fin 6) K,
      (g : Matrix (Fin 6) (Fin 6) K) = 1 + LinearMap.toMatrix' (unipLift S S' Y) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl⟩
  have hmulv : ∀ v, (g : Matrix (Fin 6) (Fin 6) K).mulVec v = v + unipLift S S' Y v := by
    intro v
    rw [hgN, Matrix.add_mulVec, Matrix.one_mulVec, LinearMap.toMatrix'_mulVec]
  have hgS : g ∈ UnipGL K S := by
    refine mem_UnipGL_iff.2 ⟨?_, fun v => ?_, fun s hs => ?_⟩
    · rw [hgN]
      exact hdet1
    · rw [hmulv, add_sub_cancel_left]
      exact (Submodule.mem_inf.1 (unipLift_mem_inf S S' Y v)).1
    · rw [hmulv, unipLift_eq_zero_of_mem_sup S S' Y (Submodule.mem_sup_left hs), add_zero]
  have hgS' : g ∈ UnipGL K S' := by
    refine mem_UnipGL_iff.2 ⟨?_, fun v => ?_, fun s hs => ?_⟩
    · rw [hgN]
      exact hdet1
    · rw [hmulv, add_sub_cancel_left]
      exact (Submodule.mem_inf.1 (unipLift_mem_inf S S' Y v)).2
    · rw [hmulv, unipLift_eq_zero_of_mem_sup S S' Y (Submodule.mem_sup_right hs), add_zero]
  have hgmem : g ∈ UnipGL K S ⊓ UnipGL K S' := Subgroup.mem_inf.2 ⟨hgS, hgS'⟩
  refine ⟨g, hgmem, ?_⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [unipHom_apply_mk, hmulv, add_sub_cancel_left]
  rfl

theorem unipHom_bijective (S S' : Submodule K (Fin 6 → K)) :
    Function.Bijective (fun g : ↥(UnipGL K S ⊓ UnipGL K S') => unipHom S S' g.1 g.2) := by
  refine ⟨?_, fun Y => ?_⟩
  · rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    have h' : unipHom S S' g hg = unipHom S S' g' hg' := h
    have hgg : g = g' := by
      apply Units.ext
      apply Matrix.ext_of_mulVec_single
      intro i
      have hi := congrArg Subtype.val
        (LinearMap.congr_fun h' (Submodule.Quotient.mk (Pi.single i 1 : Fin 6 → K)))
      change (g : Matrix (Fin 6) (Fin 6) K).mulVec (Pi.single i 1) - Pi.single i 1 =
        (g' : Matrix (Fin 6) (Fin 6) K).mulVec (Pi.single i 1) - Pi.single i 1 at hi
      exact sub_left_inj.1 hi
    subst hgg
    rfl
  · obtain ⟨g, hgmem, hY⟩ := unipHom_surjective S S' Y
    exact ⟨⟨g, hgmem⟩, hY⟩

theorem natCard_linearMap_quot (S S' : Submodule K (Fin 6 → K)) :
    Nat.card (((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S')) =
      Nat.card K ^ (Module.finrank K ↥(S ⊓ S') * (6 - Module.finrank K ↥(S ⊔ S'))) := by
  have h1 := Submodule.finrank_quotient_add_finrank (S ⊔ S')
  rw [Module.finrank_fin_fun] at h1
  have h2 := Module.natCard_eq_pow_finrank (K := K)
    (V := ((Fin 6 → K) ⧸ (S ⊔ S')) →ₗ[K] ↥(S ⊓ S'))
  rw [h2, Module.finrank_linearMap]
  congr 1
  have h3 : Module.finrank K ((Fin 6 → K) ⧸ (S ⊔ S')) = 6 - Module.finrank K ↥(S ⊔ S') := by
    omega
  rw [h3, mul_comm]

theorem card_Urad_inf [Finite K] (S S' : Submodule K (Fin 6 → K)) (hS : Module.finrank K S = 3)
    (hS' : Module.finrank K S' = 3) :
    Nat.card ↥(Urad K S ⊓ Urad K S') =
      Nat.card K ^ (Module.finrank K ↥(S ⊓ S') * (6 - Module.finrank K ↥(S ⊔ S'))) := by
  have hSne : S ≠ ⊥ := by
    rintro rfl
    simp at hS
  have hstep : Nat.card ↥(UnipGL K S ⊓ UnipGL K S') = Nat.card ↥(Urad K S ⊓ Urad K S') := by
    refine Nat.card_eq_of_bijective
      (fun g : ↥(UnipGL K S ⊓ UnipGL K S') =>
        (⟨rhoEquiv K g.1, rhoEquiv_mem_Urad_inf g.2⟩ : ↥(Urad K S ⊓ Urad K S'))) ⟨?_, ?_⟩
    · rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ h
      have h' : rhoEquiv K g₁ = rhoEquiv K g₂ := congrArg Subtype.val h
      have hrho : rho K g₁ = rho K g₂ := LinearMap.ext fun ξ => LinearEquiv.congr_fun h' ξ
      have hg : g₁ = g₂ :=
        rho_eq_of_unip hSne (Subgroup.mem_inf.1 hg₁).1 (Subgroup.mem_inf.1 hg₂).2 hrho
      subst hg
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨g, hg, hgx⟩ := mem_Urad_iff.1 (Subgroup.mem_inf.1 hx).1
      obtain ⟨g', hg', hgx'⟩ := mem_Urad_iff.1 (Subgroup.mem_inf.1 hx).2
      have hrho : rho K g = rho K g' := by
        have h' : rhoEquiv K g = rhoEquiv K g' := hgx.trans hgx'.symm
        exact LinearMap.ext fun ξ => LinearEquiv.congr_fun h' ξ
      have hgg : g = g' := rho_eq_of_unip hSne hg hg' hrho
      have hgS' : g ∈ UnipGL K S' := by
        rw [hgg]
        exact hg'
      exact ⟨⟨g, Subgroup.mem_inf.2 ⟨hg, hgS'⟩⟩, Subtype.ext hgx⟩
  rw [← hstep, Nat.card_eq_of_bijective _ (unipHom_bijective S S'), natCard_linearMap_quot]

theorem imgS0_eq_of_rho_p0 {G : GL (Fin 6) K} {c : K} (hc : c ≠ 0)
    (h : rho K G (p0 K) = c • p0 K) : imgS0 G = S0 K := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → Fin 6 → K,
      ∀ i, w i = (G : Matrix (Fin 6) (Fin 6) K) *ᵥ (![e K 0, e K 2, e K 4] i) :=
    ⟨fun i => (G : Matrix (Fin 6) (Fin 6) K) *ᵥ (![e K 0, e K 2, e K 4] i), fun i => rfl⟩
  have hrho : rho K G (p0 K) = ιMulti K 3 w := by
    rw [p0_eq, rho_ιMulti]
    congr 1
    funext i
    exact (hw i).symm
  have hs : ∀ j : Fin 3, enum S024 j = ![(0 : Fin 6), 2, 4] j := fun j =>
    enum_tripleSet (by decide) (by decide) j
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) K,
      M = Matrix.of fun i j => w i (![(0 : Fin 6), 2, 4] j) := ⟨_, rfl⟩
  have hS024 : coord K (ιMulti K 3 w) S024 = c := by
    rw [← hrho, h, coord_smul]
    unfold p0
    rw [coord_cubeBasis, if_pos rfl, mul_one]
  have hdet : M.det = c := by
    rw [hM, ← hS024, coord_ιMulti]
    simp only [hs]
  have hcoordS : ∀ I : Set.powersetCard (Fin 6) 3, I ≠ S024 → coord K (ιMulti K 3 w) I = 0 := by
    intro I hI
    have hSI : S024 ≠ I := fun h' => hI h'.symm
    rw [← hrho, h, coord_smul]
    unfold p0
    rw [coord_cubeBasis, if_neg hSI, mul_zero]
  have key : ∀ (I : Set.powersetCard (Fin 6) 3) (i j k : Fin 6), i ≠ j → i ≠ k → j ≠ k →
      I.val = {i, j, k} → I ≠ S024 → minor3 w i j k = 0 := by
    intro I i j k hij hik hjk hI hne
    rcases coord_ιMulti_triple w hI hij hik hjk with h1 | h1
    · rw [hcoordS I hne] at h1
      exact h1.symm
    · rw [hcoordS I hne] at h1
      exact neg_eq_zero.mp h1.symm
  have hodd : ∀ b : Fin 6, b.val % 2 = 1 → ∀ i : Fin 3, w i b = 0 := by
    intro b hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      revert hb
      decide
    have hb2 : b ≠ 2 := by
      rintro rfl
      revert hb
      decide
    have hb4 : b ≠ 4 := by
      rintro rfl
      revert hb
      decide
    have hnot : ∀ I : Set.powersetCard (Fin 6) 3, b ∈ I.val → I ≠ S024 := by
      intro I hbI hIS
      rw [hIS] at hbI
      exact odd_not_mem_S024 b hb hbI
    have hm1 : minor3 w b 2 4 = 0 :=
      key (tripleSet b 2 4 hb2 hb4 (by decide)) b 2 4 hb2 hb4 (by decide) rfl
        (hnot _ (by show b ∈ ({b, 2, 4} : Finset (Fin 6)); simp))
    have hm2 : minor3 w 0 b 4 = 0 :=
      key (tripleSet 0 b 4 hb0.symm (by decide) hb4) 0 b 4 hb0.symm (by decide) hb4 rfl
        (hnot _ (by show b ∈ ({0, b, 4} : Finset (Fin 6)); simp))
    have hm3 : minor3 w 0 2 b = 0 :=
      key (tripleSet 0 2 b (by decide) hb0.symm hb2.symm) 0 2 b (by decide) hb0.symm hb2.symm rfl
        (hnot _ (by show b ∈ ({0, 2, b} : Finset (Fin 6)); simp))
    have hu0 : M.updateCol 0 (fun i => w i b) = Matrix.of fun i j => w i (![b, 2, 4] j) := by
      rw [hM]
      ext i j
      fin_cases j <;> simp [Matrix.updateCol_apply]
    have hu1 : M.updateCol 1 (fun i => w i b) = Matrix.of fun i j => w i (![0, b, 4] j) := by
      rw [hM]
      ext i j
      fin_cases j <;> simp [Matrix.updateCol_apply]
    have hu2 : M.updateCol 2 (fun i => w i b) = Matrix.of fun i j => w i (![0, 2, b] j) := by
      rw [hM]
      ext i j
      fin_cases j <;> simp [Matrix.updateCol_apply]
    have hz0 : (M.updateCol 0 (fun i => w i b)).det = 0 := by
      rw [hu0]
      exact hm1
    have hz1 : (M.updateCol 1 (fun i => w i b)).det = 0 := by
      rw [hu1]
      exact hm2
    have hz2 : (M.updateCol 2 (fun i => w i b)).det = 0 := by
      rw [hu2]
      exact hm3
    have hcram : Matrix.cramer M (fun i => w i b) = 0 := by
      funext i
      rw [Matrix.cramer_apply, Pi.zero_apply]
      fin_cases i
      · exact hz0
      · exact hz1
      · exact hz2
    have hsmul : c • (fun i => w i b) = 0 := by
      have hm := Matrix.mulVec_cramer M (fun i => w i b)
      rw [hcram, Matrix.mulVec_zero, hdet] at hm
      exact hm.symm
    have hwb : (fun i => w i b) = 0 := (smul_eq_zero.mp hsmul).resolve_left hc
    intro i
    exact congrFun hwb i
  have hwS : ∀ i : Fin 3, w i ∈ S0 K := by
    intro i b hb
    exact hodd b hb i
  have hg : ∀ i : Fin 3, (G : Matrix (Fin 6) (Fin 6) K) *ᵥ (![e K 0, e K 2, e K 4] i) ∈ S0 K := by
    intro i
    rw [← hw i]
    exact hwS i
  have hle : imgS0 G ≤ S0 K := by
    rintro _ ⟨x, hx, rfl⟩
    have hcases : ∀ j : Fin 6, j.val % 2 = 1 ∨ j = 0 ∨ j = 2 ∨ j = 4 := by decide
    have hxdec : x = x 0 • e K 0 + x 2 • e K 2 + x 4 • e K 4 := by
      funext j
      rcases hcases j with hj | rfl | rfl | rfl
      · have h0 : j ≠ 0 := by
          rintro rfl
          revert hj
          decide
        have h2 : j ≠ 2 := by
          rintro rfl
          revert hj
          decide
        have h4 : j ≠ 4 := by
          rintro rfl
          revert hj
          decide
        have hxj : x j = 0 := hx j hj
        simp [hxj, e, Pi.single_apply, h0, h2, h4]
      · simp [e, Pi.single_apply]
      · simp [e, Pi.single_apply]
      · simp [e, Pi.single_apply]
    show (G : Matrix (Fin 6) (Fin 6) K) *ᵥ x ∈ S0 K
    have hGx : (G : Matrix (Fin 6) (Fin 6) K) *ᵥ x =
        x 0 • ((G : Matrix (Fin 6) (Fin 6) K) *ᵥ e K 0) +
          x 2 • ((G : Matrix (Fin 6) (Fin 6) K) *ᵥ e K 2) +
          x 4 • ((G : Matrix (Fin 6) (Fin 6) K) *ᵥ e K 4) := by
      conv_lhs => rw [hxdec]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [hGx]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hg 0))
      (Submodule.smul_mem _ _ (hg 1))) (Submodule.smul_mem _ _ (hg 2))
  have hinj : Function.Injective (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit G)
  have hfin : Module.finrank K (imgS0 G) = Module.finrank K (S0 K) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (S0 K))).symm
  exact Submodule.eq_of_le_of_finrank_eq hle hfin

theorem rho_p0_mem_span_of_imgS0 {G : GL (Fin 6) K} (h : imgS0 G = S0 K) :
    rho K G (p0 K) ∈ Submodule.span K {p0 K} := by
  have hmap : (S0 K).map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) = S0 K := h
  have heven : ∀ i : Fin 6, i.val % 2 = 0 → e K i ∈ S0 K := by
    intro i hi j hj
    have hne : j ≠ i := by
      rintro rfl
      omega
    simp [e, Pi.single_apply, hne]
  have hcol : ∀ i : Fin 3, (G : Matrix (Fin 6) (Fin 6) K) *ᵥ (![e K 0, e K 2, e K 4] i) ∈ S0 K := by
    intro i
    have hmem : (![e K 0, e K 2, e K 4] : Fin 3 → Fin 6 → K) i ∈ S0 K := by
      fin_cases i
      · exact heven 0 (by decide)
      · exact heven 2 (by decide)
      · exact heven 4 (by decide)
    rw [← hmap]
    exact Submodule.mem_map_of_mem (f := Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) hmem
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → Fin 6 → K,
      ∀ i, w i = (G : Matrix (Fin 6) (Fin 6) K) *ᵥ (![e K 0, e K 2, e K 4] i) :=
    ⟨fun i => (G : Matrix (Fin 6) (Fin 6) K) *ᵥ (![e K 0, e K 2, e K 4] i), fun i => rfl⟩
  have hrho : rho K G (p0 K) = ιMulti K 3 w := by
    rw [p0_eq, rho_ιMulti]
    congr 1
    funext i
    exact (hw i).symm
  have hwS : ∀ i : Fin 3, w i ∈ S0 K := by
    intro i
    rw [hw i]
    exact hcol i
  have hwS' : ∀ i : Fin 3, ∀ b : Fin 6, b.val % 2 = 1 → w i b = 0 :=
    fun i b hb => hwS i b hb
  have hodd_of_ne : ∀ I : Set.powersetCard (Fin 6) 3, I ≠ S024 →
      ∃ j : Fin 3, (enum I j).val % 2 = 1 := by
    intro I hI
    by_contra hcon
    apply hI
    have hxs : ∀ x ∈ I.val, x.val % 2 ≠ 1 := by
      intro x hx
      obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I x).mpr hx
      subst hj
      exact fun h' => hcon ⟨j, h'⟩
    have hfin : ∀ s : Finset (Fin 6), s.card = 3 → (∀ x ∈ s, x.val % 2 ≠ 1) → s = {0, 2, 4} := by
      decide
    exact Subtype.ext (hfin I.val I.prop hxs)
  have hzero : ∀ I : Set.powersetCard (Fin 6) 3, I ≠ S024 → coord K (rho K G (p0 K)) I = 0 := by
    intro I hI
    obtain ⟨j, hj⟩ := hodd_of_ne I hI
    rw [hrho, coord_ιMulti]
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    exact hwS' i _ hj
  have hx : rho K G (p0 K) - coord K (rho K G (p0 K)) S024 • p0 K = 0 := by
    apply eq_zero_of_coord_eq_zero
    intro I
    rw [coord_sub, coord_smul]
    by_cases hI : I = S024
    · rw [hI]
      have h1 : coord K (p0 K) S024 = 1 := by
        unfold p0
        rw [coord_cubeBasis, if_pos rfl]
      rw [h1, mul_one, sub_self]
    · have hSI : S024 ≠ I := fun h' => hI h'.symm
      have h1 : coord K (p0 K) I = 0 := by
        unfold p0
        rw [coord_cubeBasis, if_neg hSI]
      rw [hzero I hI, h1, mul_zero, sub_zero]
  have hmul : rho K G (p0 K) = coord K (rho K G (p0 K)) S024 • p0 K := sub_eq_zero.mp hx
  rw [hmul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end CFSG.RankThree.GF2n.Smith81.A5Cube
