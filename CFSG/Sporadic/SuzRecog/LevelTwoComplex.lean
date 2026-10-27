module

public import CFSG.Sporadic.SuzRecog.LevelTwoDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import Certificates.Certificate15088Base

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwo

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ElimCert
  CFSG.Sporadic.Co1Patterson

attribute [local irreducible] nbr vtab vtabs aPts wPts trips aIdx vIdx

theorem aOK_parts :
    aPts.size = 2835 ∧ eqA 1782 aPts[0]! t1Arr = true ∧
    (∀ i < 2835, isInvA 1782 aPts[i]! aPts[i]! = true ∧ aIdx.getD (fp aPts[i]!) 2835 = i) ∧
    ∀ s < 2, ∀ i < 2835, sendsB gens[s]! gensInv[s]! i (vtab s)[i]! = true := by
  have h := a_check
  simp only [aOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun i hi => ?_, fun s hs i hi => allLt_spec (allLt_spec h4 hs) hi⟩
  have := allLt_spec h3 hi
  simpa [Bool.and_eq_true, beq_iff_eq] using this

theorem vOK_parts :
    wPts.size = 162 ∧ eqA 1782 wPts[0]! w0Arr = true ∧
    (∀ j < 162, isInvA 1782 wPts[j]! wPts[j]! = true ∧ eqA 1782 (trip j)[0]! (trip j)[1]! = false ∧
      ∀ k < 3, vIdx.getD (fp (trip j)[k]!) 162 = j) ∧
    ∀ s < 2, ∀ j < 162, sendsB gens[s]! gensInv[s]! (2835 + j) (vtab s)[2835 + j]! = true := by
  have h := v_check
  simp only [vOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun j hj => ?_, fun s hs j hj => allLt_spec (allLt_spec h4 hs) hj⟩
  have := allLt_spec h3 hj
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1.1, this.1.2, fun k hk => by simpa [beq_iff_eq] using allLt_spec this.2 hk⟩

local notation "ρ" => Model.rho1

@[expose] noncomputable def aP (i : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 aPts[i]!

@[expose] noncomputable def wP (j : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 wPts[j]!

@[expose] def rhoTrip (w : Equiv.Perm (Fin 1782)) : Set (Equiv.Perm (Fin 1782)) :=
  {w, ρ * w * ρ⁻¹, ρ * (ρ * w * ρ⁻¹) * ρ⁻¹}

@[expose] noncomputable def vset (v : ℕ) : Set (Equiv.Perm (Fin 1782)) :=
  if v < 2835 then {aP v} else rhoTrip (wP (v - 2835))

@[expose] def conjSet (G : Equiv.Perm (Fin 1782)) (S : Set (Equiv.Perm (Fin 1782))) :
    Set (Equiv.Perm (Fin 1782)) :=
  (fun a => G * a * G⁻¹) '' S

theorem conjSet_one (S : Set (Equiv.Perm (Fin 1782))) : conjSet 1 S = S := by
  simp [conjSet]

theorem conjSet_mul (G H : Equiv.Perm (Fin 1782)) (S : Set (Equiv.Perm (Fin 1782))) :
    conjSet (G * H) S = conjSet G (conjSet H S) := by
  simp only [conjSet, Set.image_image, mul_inv_rev, mul_assoc]

theorem conjSet_injective (G : Equiv.Perm (Fin 1782)) : Function.Injective (conjSet G) :=
  Set.image_injective.2 fun a b h => by simpa using h

theorem rep_aP {i : ℕ} (hi : i < 2835) :
    Rep 1782 aPts[i]! (aP i) :=
  (rep_permC (aOK_parts.2.2.1 i hi).1).1

theorem rep_wP {j : ℕ} (hj : j < 162) :
    Rep 1782 wPts[j]! (wP j) :=
  (rep_permC (vOK_parts.2.2.1 j hj).1).1

theorem rep_rhoConj {w : Array ℕ} {W : Equiv.Perm (Fin 1782)}
    (hw : Rep 1782 w W) : Rep 1782 (rhoConj w) (ρ * W * ρ⁻¹) := by
  have := rep_compA rep_rho1 (rep_compA hw rep_rhoInv)
  rwa [← mul_assoc] at this

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] {L : Array α} (f : α → β)
    {i : ℕ} (hi : i < L.size) : (L.map f)[i]! = f L[i]! := by
  rw [getElem!_pos (L.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos L i hi]

theorem trip_get {j : ℕ} (hj : j < 162) :
    trip j = tripOf wPts[j]! := by
  unfold trip trips
  exact getElem!_map' _ (by rw [vOK_parts.1]; exact hj)

theorem tripOf_get0 (w : Array ℕ) : (tripOf w)[0]! = w := by simp [tripOf]

theorem tripOf_get1 (w : Array ℕ) : (tripOf w)[1]! = rhoConj w := by simp [tripOf]

theorem tripOf_get2 (w : Array ℕ) : (tripOf w)[2]! = rhoConj (rhoConj w) := by simp [tripOf]

theorem rep_trip {j : ℕ} (hj : j < 162) :
    Rep 1782 (trip j)[0]! (wP j) ∧ Rep 1782 (trip j)[1]! (ρ * wP j * ρ⁻¹) ∧
      Rep 1782 (trip j)[2]! (ρ * (ρ * wP j * ρ⁻¹) * ρ⁻¹) := by
  rw [trip_get hj, tripOf_get0, tripOf_get1, tripOf_get2]
  exact ⟨rep_wP hj, rep_rhoConj (rep_wP hj), rep_rhoConj (rep_rhoConj (rep_wP hj))⟩

theorem rho_cube : ρ * ρ * ρ = 1 := by
  have := eq_of_eqA (rep_compA rep_rho1 (rep_compA rep_rho1 rep_rho1)) rep_idA
    basicOK_parts.2.1
  rwa [← mul_assoc] at this

theorem rhoTrip_eq_of_mem {w u : Equiv.Perm (Fin 1782)}
    (hu : u ∈ rhoTrip w) : rhoTrip u = rhoTrip w := by
  have e : ∀ a : Equiv.Perm (Fin 1782), ρ * (ρ * (ρ * a * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = a := fun a => by
    calc ρ * (ρ * (ρ * a * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (ρ * ρ * ρ) * a * (ρ * ρ * ρ)⁻¹ := by group
      _ = a := by rw [rho_cube, one_mul, inv_one, mul_one]
  simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · rfl
  · ext a
    simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff, e]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · ext a
    simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff, e]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h

theorem conjSet_rhoTrip {G w : Equiv.Perm (Fin 1782)} (hG : G * ρ = ρ * G) :
    conjSet G (rhoTrip w) = rhoTrip (G * w * G⁻¹) := by
  have e : ∀ a : Equiv.Perm (Fin 1782), G * (ρ * a * ρ⁻¹) * G⁻¹ = ρ * (G * a * G⁻¹) * ρ⁻¹ :=
    fun a => by
      calc G * (ρ * a * ρ⁻¹) * G⁻¹ = (G * ρ) * a * (G * ρ)⁻¹ := by group
        _ = (ρ * G) * a * (ρ * G)⁻¹ := by rw [hG]
        _ = ρ * (G * a * G⁻¹) * ρ⁻¹ := by group
  simp only [conjSet, rhoTrip, Set.image_insert_eq, Set.image_singleton, e]

theorem sub_lt_of_not_lt {v : ℕ} (h1 : ¬ v < 2835) (h2 : v < 2997) : v - 2835 < 162 := by omega

theorem sendsB_spec {g gi : Array ℕ} {G : Equiv.Perm (Fin 1782)}
    (hg : Rep 1782 g G) (hgi : Rep 1782 gi G⁻¹) (hG : G * ρ = ρ * G) {v v' : ℕ} (hv : v < 2997)
    (h : sendsB g gi v v' = true) :
    v' < 2997 ∧ (v < 2835 ↔ v' < 2835) ∧ vset v' = conjSet G (vset v) := by
  unfold sendsB at h
  by_cases hva : v < 2835
  · simp only [hva, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hv', hc⟩ := h
    refine ⟨by omega, iff_of_true hva hv', ?_⟩
    simp only [vset, hva, hv', ↓reduceIte]
    rw [eq_of_conjEq hg hgi (rep_aP hva) (rep_aP hv') hc]
    simp [conjSet]
  · simp only [hva, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hv1, hv2⟩, hc⟩ := h
    have hva' : ¬ v' < 2835 := by omega
    have hj : v - 2835 < 162 := sub_lt_of_not_lt hva hv
    have hj' : v' - 2835 < 162 := sub_lt_of_not_lt hva' hv2
    refine ⟨hv2, iff_of_false hva hva', ?_⟩
    simp only [vset, hva, hva', ↓reduceIte]
    rw [conjSet_rhoTrip hG]
    obtain ⟨r0, r1, r2⟩ := rep_trip hj'
    have hmem : G * wP (v - 2835) * G⁻¹ ∈ rhoTrip (wP (v' - 2835)) := by
      simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hc with (hc | hc) | hc
      · exact Or.inl (eq_of_conjEq hg hgi (rep_wP hj) r0 hc).symm
      · exact Or.inr (Or.inl (eq_of_conjEq hg hgi (rep_wP hj) r1 hc).symm)
      · exact Or.inr (Or.inr (eq_of_conjEq hg hgi (rep_wP hj) r2 hc).symm)
    exact (rhoTrip_eq_of_mem hmem).symm

theorem aP_injective {i i' : ℕ} (hi : i < 2835) (hi' : i' < 2835)
    (h : aP i = aP i') : i = i' := by
  have e1 := (aOK_parts.2.2.1 i hi).2
  have e2 := (aOK_parts.2.2.1 i' hi').2
  rw [fp_eq_of_rep (rep_aP hi) (h ▸ rep_aP hi')] at e1
  exact e1.symm.trans e2

theorem wP_ne_rhoConj {j : ℕ} (hj : j < 162) :
    wP j ≠ ρ * wP j * ρ⁻¹ := by
  intro h
  obtain ⟨r0, r1, -⟩ := rep_trip hj
  have := (vOK_parts.2.2.1 j hj).2.1
  rw [(eqA_iff r0 r1).2 h] at this
  exact Bool.noConfusion this

theorem vIdx_of_mem {j : ℕ} (hj : j < 162)
    {u : Equiv.Perm (Fin 1782)} (hu : u ∈ rhoTrip (wP j)) {t : Array ℕ}
    (ht : Rep 1782 t u) : vIdx.getD (fp t) 162 = j := by
  obtain ⟨r0, r1, r2⟩ := rep_trip hj
  simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  have hk := (vOK_parts.2.2.1 j hj).2.2
  rcases hu with rfl | rfl | rfl
  · rw [fp_eq_of_rep ht r0]; exact hk 0 (by norm_num)
  · rw [fp_eq_of_rep ht r1]; exact hk 1 (by norm_num)
  · rw [fp_eq_of_rep ht r2]; exact hk 2 (by norm_num)

theorem rhoTrip_ncard_ge {j : ℕ} (hj : j < 162) :
    ∀ a, rhoTrip (wP j) ≠ {a} := by
  intro a h
  have h0 : wP j ∈ rhoTrip (wP j) := Set.mem_insert _ _
  have h1 : ρ * wP j * ρ⁻¹ ∈ rhoTrip (wP j) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  rw [h, Set.mem_singleton_iff] at h0 h1
  exact wP_ne_rhoConj hj (h0.trans h1.symm)

theorem conjSet_rhoTrip_ne_singleton {j : ℕ} (hj : j < 162)
    (G a : Equiv.Perm (Fin 1782)) : conjSet G (rhoTrip (wP j)) ≠ {a} := by
  intro h
  have h0 : G * wP j * G⁻¹ ∈ conjSet G (rhoTrip (wP j)) := ⟨wP j, Set.mem_insert _ _, rfl⟩
  have h1 : G * (ρ * wP j * ρ⁻¹) * G⁻¹ ∈ conjSet G (rhoTrip (wP j)) :=
    ⟨ρ * wP j * ρ⁻¹, Set.mem_insert_of_mem _ (Set.mem_insert _ _), rfl⟩
  rw [h, Set.mem_singleton_iff] at h0 h1
  exact wP_ne_rhoConj hj (mul_left_cancel (mul_right_cancel (h0.trans h1.symm)))

theorem vset_injective {v v' : ℕ} (hv : v < 2997)
    (hv' : v' < 2997) (h : vset v = vset v') : v = v' := by
  unfold vset at h
  by_cases ha : v < 2835 <;> by_cases ha' : v' < 2835
  · simp only [ha, ha', ↓reduceIte, Set.singleton_eq_singleton_iff] at h
    exact aP_injective ha ha' h
  · simp only [ha, ha', ↓reduceIte] at h
    exact absurd h.symm (rhoTrip_ncard_ge (by omega) _)
  · simp only [ha, ha', ↓reduceIte] at h
    exact absurd h (rhoTrip_ncard_ge (by omega) _)
  · simp only [ha, ha', ↓reduceIte] at h
    have hj : v - 2835 < 162 := sub_lt_of_not_lt ha hv
    have hj' : v' - 2835 < 162 := sub_lt_of_not_lt ha' hv'
    have hmem : wP (v - 2835) ∈ rhoTrip (wP (v' - 2835)) := by
      rw [← h]; exact Set.mem_insert _ _
    have e1 := vIdx_of_mem hj' hmem (rep_wP hj)
    have e2 := vIdx_of_mem hj (Set.mem_insert _ _ : wP (v - 2835) ∈ rhoTrip (wP (v - 2835)))
      (rep_wP hj)
    omega

theorem gens_vset {s : ℕ} (hs : s < 2) {v : ℕ} (hv : v < 2997) :
    (vtab s)[v]! < 2997 ∧ (v < 2835 ↔ (vtab s)[v]! < 2835) ∧
      vset (vtab s)[v]! = conjSet (permC 1782 gens[s]!) (vset v) := by
  have hsend : sendsB gens[s]! gensInv[s]! v (vtab s)[v]! = true := by
    by_cases ha : v < 2835
    · exact aOK_parts.2.2.2 s hs v ha
    · have := vOK_parts.2.2.2 s hs (v - 2835) (by omega)
      rwa [show 2835 + (v - 2835) = v by omega] at this
  exact sendsB_spec (rep_gens hs).1 (rep_gens hs).2 (gens_comm_rho1 hs) hv hsend

theorem xGroup_induction {P : Equiv.Perm (Fin 1782) → Prop} (h1 : P x1) (h2 : P x2) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) {g : Equiv.Perm (Fin 1782)} (hg : g ∈ xGroup) : P g := by
  have hg' : g ∈ (xGroup.toSubmonoid : Submonoid (Equiv.Perm (Fin 1782))) := hg
  rw [xGroup, Subgroup.closure_toSubmonoid_of_finite] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact h1
    · rw [Set.mem_singleton_iff] at hx; exact hx ▸ h2
  | one => exact hone
  | mul a b _ _ ha hb => exact hmul a b ha hb

theorem exists_vset_conj {g : Equiv.Perm (Fin 1782)}
    (hg : g ∈ xGroup) (v : Fin 2997) : ∃ v' : Fin 2997, vset v' = conjSet g (vset v) := by
  revert v
  refine xGroup_induction (P := fun g => ∀ v : Fin 2997, ∃ v' : Fin 2997,
    vset v' = conjSet g (vset v)) ?_ ?_ ?_ ?_ hg
  · intro v
    obtain ⟨h1, -, h3⟩ := gens_vset (s := 0) (by norm_num) v.2
    exact ⟨⟨_, h1⟩, h3⟩
  · intro v
    obtain ⟨h1, -, h3⟩ := gens_vset (s := 1) (by norm_num) v.2
    exact ⟨⟨_, h1⟩, h3⟩
  · intro v
    exact ⟨v, (conjSet_one _).symm⟩
  · intro a b ha hb v
    obtain ⟨u, hu⟩ := hb v
    obtain ⟨w, hw⟩ := ha u
    exact ⟨w, by rw [hw, hu, conjSet_mul]⟩

@[expose] noncomputable def smulV (g : xGroup) (v : Fin 2997) :
    Fin 2997 :=
  Classical.choose (exists_vset_conj g.2 v)

theorem smulV_spec (g : xGroup) (v : Fin 2997) :
    vset (smulV g v) = conjSet g.1 (vset v) :=
  Classical.choose_spec (exists_vset_conj g.2 v)

theorem smulV_eq_iff (g : xGroup) (v v' : Fin 2997) :
    smulV g v = v' ↔ vset v' = conjSet g.1 (vset v) := by
  constructor
  · rintro rfl; exact smulV_spec g v
  · intro h
    exact Fin.ext (vset_injective (smulV g v).2 v'.2 ((smulV_spec g v).trans h.symm))

noncomputable instance instMulActionXGroup :
    MulAction xGroup (Fin 2997) where
  smul := smulV
  one_smul v := (smulV_eq_iff 1 v v).2 (conjSet_one _).symm
  mul_smul g h v := (smulV_eq_iff (g * h) v _).2 (by
    show vset (smulV g (smulV h v)) = _
    rw [smulV_spec, smulV_spec, ← conjSet_mul]
    rfl)

theorem smul_spec (g : xGroup) (v : Fin 2997) :
    vset (g • v : Fin 2997) = conjSet g.1 (vset v) :=
  smulV_spec g v

theorem smul_eq_iff (g : xGroup) (v v' : Fin 2997) :
    g • v = v' ↔ vset v' = conjSet g.1 (vset v) :=
  smulV_eq_iff g v v'

theorem smul_lt_iff (g : xGroup) (v : Fin 2997) :
    (g • v).1 < 2835 ↔ v.1 < 2835 := by
  have h := smul_spec g v
  unfold vset at h
  by_cases ha : v.1 < 2835 <;> by_cases ha' : (g • v).1 < 2835
  · exact iff_of_true ha' ha
  · simp only [ha, ha', ↓reduceIte, conjSet, Set.image_singleton] at h
    exact absurd h (rhoTrip_ncard_ge (j := (g • v).1 - 2835) (by have := (g • v).2; omega) _)
  · simp only [ha, ha', ↓reduceIte] at h
    exact absurd h.symm (conjSet_rhoTrip_ne_singleton (j := v.1 - 2835)
      (by have := v.2; omega) g.1 _)
  · exact iff_of_false ha' ha

theorem gens_mem_xGroup {s : ℕ} (hs : s < 2) : permC 1782 gens[s]! ∈ xGroup := by
  interval_cases s
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def genElt (s : ℕ) (hs : s < 2) : xGroup :=
  ⟨permC 1782 gens[s]!, gens_mem_xGroup hs⟩

theorem genElt_smul {s : ℕ} (hs : s < 2) (v : Fin 2997) :
    genElt s hs • v = ⟨(vtab s)[v.1]!, (gens_vset hs v.2).1⟩ :=
  (smul_eq_iff _ _ _).2 (gens_vset hs v.2).2.2

theorem xGroup_elt_induction {P : xGroup → Prop} (h0 : P (genElt 0 (by norm_num)))
    (h1 : P (genElt 1 (by norm_num))) (hone : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (g : xGroup) : P g := by
  have hset : ({genElt 0 (by norm_num), genElt 1 (by norm_num)} : Set xGroup) =
      ((↑) : xGroup → Equiv.Perm (Fin 1782)) ⁻¹' {x1, x2} := by
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  have htop : Subgroup.closure ({genElt 0 (by norm_num), genElt 1 (by norm_num)} : Set xGroup) =
      ⊤ := by
    rw [hset]
    exact Subgroup.closure_closure_coe_preimage
  have hg : g ∈ (Subgroup.closure ({genElt 0 (by norm_num), genElt 1 (by norm_num)} :
      Set xGroup)).toSubmonoid := by
    rw [htop]; exact Subgroup.mem_top g
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact h0
    · rw [Set.mem_singleton_iff] at hx; exact hx ▸ h1
  | one => exact hone
  | mul a b _ _ ha hb => exact hmul a b ha hb

abbrev Γ : SimpleGraph (Fin 2997) := nbrGraph 2997 nbr

theorem graphOK_parts :
    ∀ s < 2, ∀ x < 2997, ∀ k < (nbr[x]!).size,
      adjB nbr (vtab s)[x]! (vtab s)[(nbr[x]!)[k]!]! = true := by
  have h := graph_check
  simp only [graphOK, Bool.and_eq_true, beq_iff_eq] at h
  intro s hs x hx k hk
  have := Array.all_eq_true.1 (allLt_spec (allLt_spec h.2 hs) hx) k hk
  rwa [← getElem!_pos (nbr[x]!) k hk] at this

theorem gens_adj {s : ℕ} (hs : s < 2) {a b : Fin 2997}
    (h : Γ.Adj a b) : Γ.Adj (genElt s hs • a) (genElt s hs • b) := by
  rw [genElt_smul, genElt_smul]
  obtain ⟨-, hab | hba⟩ := h
  · obtain ⟨k, hk, hkb⟩ := occB_iff.1 hab
    have := graphOK_parts s hs a a.2 k hk
    rw [hkb] at this
    exact nbrGraph_adj_iff.2 this
  · obtain ⟨k, hk, hkb⟩ := occB_iff.1 hba
    have := graphOK_parts s hs b b.2 k hk
    rw [hkb] at this
    exact (nbrGraph_adj_iff.2 this).symm

theorem adj_smul (g : xGroup) {a b : Fin 2997} (h : Γ.Adj a b) :
    Γ.Adj (g • a) (g • b) := by
  revert a b
  refine xGroup_elt_induction (P := fun g => ∀ {a b : Fin 2997}, Γ.Adj a b →
    Γ.Adj (g • a) (g • b)) (fun h => gens_adj _ h) (fun h => gens_adj _ h)
    (fun h => by rwa [one_smul, one_smul]) (fun x y hx hy a b h => ?_) g
  rw [mul_smul, mul_smul]
  exact hx (hy h)

@[expose] def admT (S : Set (Fin 2997)) : Prop :=
  ∃ v ∈ S, 2835 ≤ v.1 ∧ ∀ w ∈ S, w ≠ v → w.1 < 2835

theorem admT_smul (g : xGroup) (S : Set (Fin 2997))
    (h : admT S) : admT ((g • ·) '' S) := by
  obtain ⟨v, hv, hv2, hw⟩ := h
  refine ⟨g • v, ⟨v, hv, rfl⟩, ?_, ?_⟩
  · by_contra hlt
    exact absurd ((smul_lt_iff g v).1 (by omega)) (by omega)
  · rintro _ ⟨w, hw', rfl⟩ hne
    exact (smul_lt_iff g w).2 (hw w hw' fun e => hne (e ▸ rfl))

theorem adjB_ne {x y : ℕ} (h : adjB nbr x y = true) : x ≠ y := by
  simp only [adjB, Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

theorem admT_of_triB {x y z : Fin 2997} (h : triB x y z = true) : admT {x, y, z} := by
  simp only [triB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hxy, hyz⟩, hxz⟩, hc⟩ := h
  have nxy : x ≠ y := fun e => adjB_ne hxy (congrArg Fin.val e)
  have nyz : y ≠ z := fun e => adjB_ne hyz (congrArg Fin.val e)
  have nxz : x ≠ z := fun e => adjB_ne hxz (congrArg Fin.val e)
  by_cases hx : 2835 ≤ x.1 <;> by_cases hy : 2835 ≤ y.1 <;> by_cases hz : 2835 ≤ z.1 <;>
    simp only [hx, hy, hz, ↓reduceIte] at hc <;> norm_num at hc
  · refine ⟨x, Set.mem_insert _ _, hx, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd rfl hne
    · omega
    · omega
  · refine ⟨y, Set.mem_insert_of_mem _ (Set.mem_insert _ _), hy, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · omega
    · exact absurd rfl hne
    · omega
  · refine ⟨z, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), hz, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · omega
    · omega
    · exact absurd rfl hne

theorem preconnected_Γ : Γ.Preconnected :=
  preconnected_of_ok elim_check

theorem triangulableBy_Γ : TriangulableBy Γ admT :=
  triangulableBy_of_ok (fun _ _ _ h => admT_of_triB h) elim_check

theorem eltG_mem {g gi : Array ℕ} (h : elemOK g gi = true) :
    permC 1782 g ∈ xGroup := by
  simp only [elemOK, Bool.and_eq_true] at h
  exact mem_xGroup_of_memX (rep_permC h.1).1 h.2

@[expose] noncomputable def eltG (g gi : Array ℕ)
    (h : elemOK g gi = true) : xGroup :=
  ⟨permC 1782 g, eltG_mem h⟩

theorem eltG_smul {g gi : Array ℕ} (h : elemOK g gi = true)
    {v v' : ℕ} (hv : v < 2997) (hs : sendsB g gi v v' = true) :
    ∃ hv' : v' < 2997, eltG g gi h • (⟨v, hv⟩ : Fin 2997) = ⟨v', hv'⟩ := by
  have hinv : isInvA 1782 g gi = true := by
    simp only [elemOK, Bool.and_eq_true] at h; exact h.1
  have hG : permC 1782 g * ρ = ρ * permC 1782 g :=
    Subgroup.mem_centralizer_singleton_iff.1 (xGroup_le_centralizer (eltG_mem h))
  obtain ⟨hv', -, hset⟩ := sendsB_spec (rep_permC hinv).1 (rep_permC hinv).2 hG hv hs
  exact ⟨hv', (smul_eq_iff (eltG g gi h) ⟨v, hv⟩ ⟨v', hv'⟩).2 hset⟩

@[expose] noncomputable def edgeStab (a b : Fin 2997) :
    Subgroup xGroup where
  carrier := {g | (g • a = a ∧ g • b = b) ∨ (g • a = b ∧ g • b = a)}
  one_mem' := Or.inl ⟨one_smul _ _, one_smul _ _⟩
  mul_mem' := by
    rintro g h (⟨ga, gb⟩ | ⟨ga, gb⟩) (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      simp only [Set.mem_ofPred_eq, mul_smul, ha, hb, ga, gb, and_self, true_or, or_true]
  inv_mem' := by
    rintro g (⟨ga, gb⟩ | ⟨ga, gb⟩)
    · exact Or.inl ⟨inv_smul_eq_iff.2 ga.symm, inv_smul_eq_iff.2 gb.symm⟩
    · exact Or.inr ⟨inv_smul_eq_iff.2 gb.symm, inv_smul_eq_iff.2 ga.symm⟩

theorem mem_edgeStab {a b : Fin 2997} (g : xGroup) :
    g ∈ edgeStab a b ↔ (g • a = a ∧ g • b = b) ∨ (g • a = b ∧ g • b = a) :=
  Iff.rfl

theorem pElemOK_parts {e : Elt} {v v' : ℕ} (h : pElemOK e v v' = true) :
    elemOK e.1 e.2 = true ∧ sendsB e.1 e.2 0 0 = true ∧ sendsB e.1 e.2 v v' = true := by
  simp only [pElemOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem locOK_parts :
    adjB nbr 0 p1 = true ∧ adjB nbr 0 2835 = true ∧ nbPOK = true ∧ nbQOK = true ∧
    elemOK swapE.1 swapE.2 = true ∧ sendsB swapE.1 swapE.2 0 p1 = true ∧
    sendsB swapE.1 swapE.2 p1 0 = true ∧ cellReps.size = 4 ∧
    ∀ k < 4, pElemOK (cellC k) 2835 cellReps[k]! = true ∧
      pElemOK (cellC' k) 2835 (actV (cellC' k).1 (cellC' k).2 2835) = true ∧
      sendsB swapE.1 swapE.2 (actV (cellC' k).1 (cellC' k).2 2835) cellReps[k]! = true := by
  have h := loc_check
  simp only [locOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun k hk => ?_⟩
  have := allLt_spec h9 hk
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem exists_of_occB {s : Array ℕ} {y : ℕ} (h : occB s y = true) : ∃ k < s.size, s[k]! = y := by
  unfold occB at h
  obtain ⟨k, hk, he⟩ := List.any_eq_true.1 h
  exact ⟨k, List.mem_range.1 hk, beq_iff_eq.1 he⟩

theorem nbPOK_parts :
    (∀ l < 6, elemOK genP[l]!.1 genP[l]!.2 = true ∧ sendsB genP[l]!.1 genP[l]!.2 0 0 = true) ∧
    (nbr[0]!).size = 36 ∧ (nbr[0]!)[0]! = p1 ∧ (nbr[0]!)[18]! = 2835 ∧
    (∀ y < 2997, adjB nbr 0 y = true → occB nbr[0]! y = true) ∧
    ∀ k < 36, (k < 18 ↔ (nbr[0]!)[k]! < 2835) ∧ (k = 0 ∨ k = 18 ∨
      (nbPPar[k]! < 36 ∧ nbPDep[nbPPar[k]!]! < nbPDep[k]! ∧ nbPLab[k]! < 6 ∧
        sendsB genP[nbPLab[k]!]!.1 genP[nbPLab[k]!]!.2 (nbr[0]!)[nbPPar[k]!]! (nbr[0]!)[k]! =
          true)) := by
  have h := locOK_parts.2.2.1
  simp only [nbPOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun l hl => ?_, h2, h3, h4, fun y hy hadj => ?_, fun k hk => ?_⟩
  · have := allLt_spec h1 hl
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allLt_spec h5 hy
    simpa [hadj] using this
  · have := allLt_spec h6 hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc,
      or_assoc] at this
    exact ⟨by simpa using this.1, this.2⟩

theorem nbQOK_parts :
    (∀ l < 6, elemOK genQ[l]!.1 genQ[l]!.2 = true ∧
      sendsB genQ[l]!.1 genQ[l]!.2 2835 2835 = true) ∧ nbQ[0]! = 0 ∧
    (∀ y < 2997, adjB nbr 2835 y = true → occB nbQ y = true) ∧
    ∀ m < 315, m = 0 ∨ (nbQPar[m]! < 315 ∧ nbQDep[nbQPar[m]!]! < nbQDep[m]! ∧ nbQLab[m]! < 6 ∧
      sendsB genQ[nbQLab[m]!]!.1 genQ[nbQLab[m]!]!.2 nbQ[nbQPar[m]!]! nbQ[m]! = true) := by
  have h := locOK_parts.2.2.2.1
  simp only [nbQOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun l hl => ?_, h2, fun y hy hadj => ?_, fun m hm => ?_⟩
  · have := allLt_spec h1 hl
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allLt_spec h3 hy
    simpa [hadj] using this
  · have := allLt_spec h4 hm
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at this
    exact this

@[expose] def pV : Fin 2997 := ⟨0, by norm_num⟩

@[expose] def qV : Fin 2997 := ⟨2835, by norm_num⟩

theorem p1_lt : p1 < 2997 := by
  have h := locOK_parts.2.2.2.2.2.1
  unfold sendsB at h
  simp only [show (0 : ℕ) < 2835 by norm_num, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at h
  omega

@[expose] def p1V : Fin 2997 := ⟨p1, p1_lt⟩

theorem adj_p_p1 : Γ.Adj pV p1V :=
  nbrGraph_adj_iff.2 locOK_parts.1

theorem adj_p_q : Γ.Adj pV qV :=
  nbrGraph_adj_iff.2 locOK_parts.2.1

theorem smul_q_ne_p (g : xGroup) : g • qV ≠ pV := by
  intro h
  have := (smul_lt_iff g qV).1 (by rw [h]; show (0 : ℕ) < 2835; norm_num)
  exact absurd this (by show ¬ (2835 : ℕ) < 2835; norm_num)

@[expose] noncomputable def Xp : Subgroup xGroup :=
  MulAction.stabilizer xGroup pV

@[expose] noncomputable def Xq : Subgroup xGroup :=
  MulAction.stabilizer xGroup qV

@[expose] noncomputable def Xe : Subgroup xGroup :=
  edgeStab pV p1V

theorem mem_Xp (g : xGroup) : g ∈ Xp ↔ g • pV = pV :=
  MulAction.mem_stabilizer_iff

theorem mem_Xq (g : xGroup) : g ∈ Xq ↔ g • qV = qV :=
  MulAction.mem_stabilizer_iff

theorem mem_Xe (g : xGroup) :
    g ∈ Xe ↔ (g • pV = pV ∧ g • p1V = p1V) ∨ (g • pV = p1V ∧ g • p1V = pV) :=
  Iff.rfl

theorem pElem_spec {e : Elt} {v v' : ℕ} (hv : v < 2997)
    (h : pElemOK e v v' = true) :
    ∃ (he : elemOK e.1 e.2 = true) (hv' : v' < 2997), eltG e.1 e.2 he ∈ Xp ∧
      eltG e.1 e.2 he • (⟨v, hv⟩ : Fin 2997) = ⟨v', hv'⟩ := by
  obtain ⟨he, h0, h1⟩ := pElemOK_parts h
  obtain ⟨_, e0⟩ := eltG_smul he (by norm_num : 0 < 2997) h0
  obtain ⟨hv', e1⟩ := eltG_smul he hv h1
  exact ⟨he, hv', (mem_Xp _).2 e0, e1⟩

theorem genP_spec {l : ℕ} (hl : l < 6) :
    ∃ g ∈ Xp, ∀ {v v' : ℕ} (hv : v < 2997), sendsB genP[l]!.1 genP[l]!.2 v v' = true →
      ∃ hv' : v' < 2997, g • (⟨v, hv⟩ : Fin 2997) = ⟨v', hv'⟩ := by
  obtain ⟨he, h0⟩ := nbPOK_parts.1 l hl
  obtain ⟨_, e0⟩ := eltG_smul he (by norm_num : 0 < 2997) h0
  exact ⟨_, (mem_Xp _).2 e0, fun hv hs => eltG_smul he hv hs⟩

theorem genQ_spec {l : ℕ} (hl : l < 6) :
    ∃ g ∈ Xq, ∀ {v v' : ℕ} (hv : v < 2997), sendsB genQ[l]!.1 genQ[l]!.2 v v' = true →
      ∃ hv' : v' < 2997, g • (⟨v, hv⟩ : Fin 2997) = ⟨v', hv'⟩ := by
  obtain ⟨he, h0⟩ := nbQOK_parts.1 l hl
  obtain ⟨_, e0⟩ := eltG_smul he (by norm_num : 2835 < 2997) h0
  exact ⟨_, (mem_Xq _).2 e0, fun hv hs => eltG_smul he hv hs⟩

theorem nbP_reach :
    ∀ d, ∀ k < 36, nbPDep[k]! = d → ∃ hk : (nbr[0]!)[k]! < 2997, ∃ g ∈ Xp,
      (k < 18 → g • p1V = ⟨(nbr[0]!)[k]!, hk⟩) ∧ (¬ k < 18 → g • qV = ⟨(nbr[0]!)[k]!, hk⟩) := by
  obtain ⟨-, -, h0, h18, -, htree⟩ := nbPOK_parts
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd
    obtain ⟨htk, hc⟩ := htree k hk
    rcases hc with rfl | rfl | ⟨hp, hdp, hl, hs⟩
    · refine ⟨by rw [h0]; exact p1_lt, 1, one_mem _, fun _ => ?_, fun h => absurd (by norm_num) h⟩
      rw [one_smul]
      exact Fin.ext h0.symm
    · refine ⟨by rw [h18]; norm_num, 1, one_mem _, fun h => absurd h (by norm_num), fun _ => ?_⟩
      rw [one_smul]
      exact Fin.ext h18.symm
    · obtain ⟨hj, g, hg, hgs⟩ := ih _ (hd ▸ hdp) _ hp rfl
      obtain ⟨h, hh, hact⟩ := genP_spec hl
      obtain ⟨hk', hhs⟩ := hact hj hs
      have htj := (htree _ hp).1
      have hty := smul_lt_iff h ⟨_, hj⟩
      rw [hhs] at hty
      have hiff : nbPPar[k]! < 18 ↔ k < 18 := by
        rw [htj, htk]
        exact hty.symm
      refine ⟨hk', h * g, mul_mem hh hg, fun hlt => ?_, fun hlt => ?_⟩
      · rw [mul_smul, hgs.1 (hiff.2 hlt), hhs]
      · rw [mul_smul, hgs.2 (fun h' => hlt (hiff.1 h')), hhs]

theorem locp (y : Fin 2997) (hy : Γ.Adj pV y) :
    (∃ g ∈ Xp, g • p1V = y) ∨ ∃ g ∈ Xp, g • qV = y := by
  obtain ⟨-, hsz, -, -, hocc, -⟩ := nbPOK_parts
  obtain ⟨k, hk, he⟩ := exists_of_occB (hocc y.1 y.2 (nbrGraph_adj_iff.1 hy))
  rw [hsz] at hk
  obtain ⟨hk', g, hg, h1, h2⟩ := nbP_reach _ k hk rfl
  have hy' : (⟨(nbr[0]!)[k]!, hk'⟩ : Fin 2997) = y := Fin.ext he
  by_cases hlt : k < 18
  · exact Or.inl ⟨g, hg, (h1 hlt).trans hy'⟩
  · exact Or.inr ⟨g, hg, (h2 hlt).trans hy'⟩

theorem nbQ_size : nbQ.size = 315 := by
  simp [nbQ, hexTable]

theorem nbQ_reach :
    ∀ d, ∀ m < 315, nbQDep[m]! = d → ∃ hm : nbQ[m]! < 2997, ∃ g ∈ Xq,
      g • pV = ⟨nbQ[m]!, hm⟩ := by
  obtain ⟨-, h0, -, htree⟩ := nbQOK_parts
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m hm hd
    rcases htree m hm with rfl | ⟨hp, hdp, hl, hs⟩
    · refine ⟨by rw [h0]; norm_num, 1, one_mem _, ?_⟩
      rw [one_smul]
      exact Fin.ext h0.symm
    · obtain ⟨hj, g, hg, hgs⟩ := ih _ (hd ▸ hdp) _ hp rfl
      obtain ⟨h, hh, hact⟩ := genQ_spec hl
      obtain ⟨hm', hhs⟩ := hact hj hs
      exact ⟨hm', h * g, mul_mem hh hg, by rw [mul_smul, hgs, hhs]⟩

theorem locq (y : Fin 2997) (hy : Γ.Adj qV y) :
    ∃ g ∈ Xq, g • pV = y := by
  obtain ⟨-, -, hocc, -⟩ := nbQOK_parts
  obtain ⟨m, hm, he⟩ := exists_of_occB (hocc y.1 y.2 (nbrGraph_adj_iff.1 hy))
  rw [nbQ_size] at hm
  obtain ⟨hm', g, hg, h1⟩ := nbQ_reach _ m hm rfl
  exact ⟨g, hg, h1.trans (Fin.ext he)⟩

@[expose] noncomputable def sX : xGroup :=
  eltG swapE.1 swapE.2 locOK_parts.2.2.2.2.1

theorem sX_spec : sX • pV = p1V ∧ sX • p1V = pV := by
  obtain ⟨_, e1⟩ := eltG_smul locOK_parts.2.2.2.2.1 (by norm_num : 0 < 2997)
    locOK_parts.2.2.2.2.2.1
  obtain ⟨_, e2⟩ := eltG_smul locOK_parts.2.2.2.2.1 p1_lt locOK_parts.2.2.2.2.2.2.1
  exact ⟨e1, e2⟩

theorem cellC_parts (k : Fin 4) :
    ∃ (he : elemOK (cellC k).1 (cellC k).2 = true) (hr : cellReps[k.1]! < 2997),
      eltG _ _ he ∈ Xp ∧ eltG _ _ he • qV = ⟨cellReps[k.1]!, hr⟩ := by
  obtain ⟨he, hr, hmem, hs⟩ := pElem_spec (by norm_num : 2835 < 2997)
    (locOK_parts.2.2.2.2.2.2.2.2 k.1 k.2).1
  exact ⟨he, hr, hmem, hs⟩

theorem cellC'_parts (k : Fin 4) :
    ∃ (he : elemOK (cellC' k).1 (cellC' k).2 = true)
      (hr : actV (cellC' k).1 (cellC' k).2 2835 < 2997),
      eltG _ _ he ∈ Xp ∧ eltG _ _ he • qV = ⟨actV (cellC' k).1 (cellC' k).2 2835, hr⟩ := by
  obtain ⟨he, hr, hmem, hs⟩ := pElem_spec (by norm_num : 2835 < 2997)
    (locOK_parts.2.2.2.2.2.2.2.2 k.1 k.2).2.1
  exact ⟨he, hr, hmem, hs⟩

@[expose] noncomputable def cX (k : Fin 4) : xGroup :=
  eltG _ _ (cellC_parts k).1

@[expose] noncomputable def c'X (k : Fin 4) : xGroup :=
  eltG _ _ (cellC'_parts k).1

theorem cX_mem (k : Fin 4) : cX k ∈ Xp :=
  (cellC_parts k).2.2.1

theorem c'X_mem (k : Fin 4) : c'X k ∈ Xp :=
  (cellC'_parts k).2.2.1

theorem cX_smul_q (k : Fin 4) :
    cX k • qV = ⟨cellReps[k.1]!, (cellC_parts k).2.1⟩ :=
  (cellC_parts k).2.2.2

theorem cell_spec (k : Fin 4) : sX • (c'X k • qV) = cX k • qV := by
  rw [cX_smul_q, show c'X k • qV = _ from (cellC'_parts k).2.2.2]
  obtain ⟨_, e⟩ := eltG_smul locOK_parts.2.2.2.2.1 (cellC'_parts k).2.1
    (locOK_parts.2.2.2.2.2.2.2.2 k.1 k.2).2.2
  exact e

theorem triOK_parts :
    (∀ k < 4, triY1[k]! = p1 ∧ triY2[k]! = cellReps[k]!) ∧
    (∀ t < 180, t < 4 ∨ (triPar[t]! < t ∧ triLab[t]! < 6 ∧
      sendsB genP[triLab[t]!]!.1 genP[triLab[t]!]!.2 triY1[triPar[t]!]! triY1[t]! = true ∧
      sendsB genP[triLab[t]!]!.1 genP[triLab[t]!]!.2 triY2[triPar[t]!]! triY2[t]! = true)) ∧
    ∀ a < 18, ∀ b < 18, adjB nbr (nbr[0]!)[a]! (nbr[0]!)[18 + b]! = true →
      triIdx[18 * a + b]! < 180 ∧ triY1[triIdx[18 * a + b]!]! = (nbr[0]!)[a]! ∧
        triY2[triIdx[18 * a + b]!]! = (nbr[0]!)[18 + b]! := by
  have h := tri_check
  simp only [triOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k hk => ?_, fun t ht => ?_, fun a ha b hb hadj => ?_⟩
  · have := allLt_spec h1 hk
    simpa [Bool.and_eq_true, beq_iff_eq] using this
  · have := allLt_spec h2 ht
    simpa [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using this
  · have := allLt_spec (allLt_spec h3 ha) hb
    simpa [hadj, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using this

theorem tri_reach :
    ∀ t < 180, ∃ k : Fin 4, ∃ h1 : triY1[t]! < 2997, ∃ h2 : triY2[t]! < 2997, ∃ g ∈ Xp,
      g • p1V = ⟨triY1[t]!, h1⟩ ∧ g • (cX k • qV) = ⟨triY2[t]!, h2⟩ := by
  obtain ⟨hroot, htree, -⟩ := triOK_parts
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases htree t ht with h4 | ⟨hp, hl, hs1, hs2⟩
    · obtain ⟨e1, e2⟩ := hroot t h4
      have hc := cX_smul_q ⟨t, h4⟩
      refine ⟨⟨t, h4⟩, by rw [e1]; exact p1_lt, by rw [e2]; exact (cellC_parts ⟨t, h4⟩).2.1, 1,
        one_mem _, ?_, ?_⟩
      · rw [one_smul]
        exact Fin.ext e1.symm
      · rw [one_smul, hc]
        exact Fin.ext e2.symm
    · obtain ⟨k, hj1, hj2, g, hg, hg1, hg2⟩ := ih _ hp (hp.trans ht)
      obtain ⟨h, hh, hact⟩ := genP_spec hl
      obtain ⟨hk1, e1⟩ := hact hj1 hs1
      obtain ⟨hk2, e2⟩ := hact hj2 hs2
      exact ⟨k, hk1, hk2, h * g, mul_mem hh hg, by rw [mul_smul, hg1, e1],
        by rw [mul_smul, hg2, e2]⟩

theorem nbr0_pos {y : ℕ} (hy : y < 2997)
    (h : adjB nbr 0 y = true) : ∃ k < 36, (nbr[0]!)[k]! = y ∧ (k < 18 ↔ y < 2835) := by
  obtain ⟨-, hsz, -, -, hocc, htree⟩ := nbPOK_parts
  obtain ⟨k, hk, he⟩ := exists_of_occB (hocc y hy h)
  rw [hsz] at hk
  exact ⟨k, hk, he, he ▸ (htree k hk).1⟩

theorem tri_listed {y₁ y₂ : ℕ} (hy₁ : y₁ < 2997)
    (hy₂ : y₂ < 2997) (h1 : adjB nbr 0 y₁ = true) (h2 : adjB nbr 0 y₂ = true)
    (h12 : adjB nbr y₁ y₂ = true) (ht1 : y₁ < 2835) (ht2 : ¬ y₂ < 2835) :
    ∃ t < 180, triY1[t]! = y₁ ∧ triY2[t]! = y₂ := by
  obtain ⟨a, ha, ea, hta⟩ := nbr0_pos hy₁ h1
  obtain ⟨c, hc, ec, htc⟩ := nbr0_pos hy₂ h2
  have ha' : a < 18 := hta.2 ht1
  have hc' : ¬ c < 18 := fun h => ht2 (htc.1 h)
  obtain ⟨b, rfl⟩ : ∃ b, c = 18 + b := ⟨c - 18, by omega⟩
  obtain ⟨hlt, e1, e2⟩ := triOK_parts.2.2 a ha' b (by omega) (by rw [ea, ec]; exact h12)
  exact ⟨_, hlt, e1.trans ea, e2.trans ec⟩

theorem admT_pair {y₁ y₂ : Fin 2997} (h12 : y₁ ≠ y₂) (h : admT {pV, y₁, y₂}) :
    (y₁.1 < 2835 ∧ 2835 ≤ y₂.1) ∨ (2835 ≤ y₁.1 ∧ y₂.1 < 2835) := by
  obtain ⟨v, hv, hv2, hw⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact absurd hv2 (by show ¬ 2835 ≤ (0 : ℕ); norm_num)
  · exact Or.inr ⟨hv2, hw y₂ (by simp) (Ne.symm h12)⟩
  · exact Or.inl ⟨hw y₁ (by simp) h12, hv2⟩

theorem tri_spec (y₁ y₂ : Fin 2997) (h1 : Γ.Adj pV y₁)
    (h12 : Γ.Adj y₁ y₂) (h2 : Γ.Adj y₂ pV) (hT : admT {pV, y₁, y₂}) :
    (∃ k, ∃ g ∈ Xp, g • p1V = y₁ ∧ g • (cX k • qV) = y₂) ∨
      (∃ k, ∃ g ∈ Xp, g • (cX k • qV) = y₁ ∧ g • p1V = y₂) := by
  have a01 : adjB nbr 0 y₁.1 = true := nbrGraph_adj_iff.1 h1
  have a12 : adjB nbr y₁.1 y₂.1 = true := nbrGraph_adj_iff.1 h12
  have a21 : adjB nbr y₂.1 y₁.1 = true := nbrGraph_adj_iff.1 h12.symm
  have a02 : adjB nbr 0 y₂.1 = true := nbrGraph_adj_iff.1 h2.symm
  rcases admT_pair h12.ne hT with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨t, ht, e1, e2⟩ := tri_listed y₁.2 y₂.2 a01 a02 a12 h₁ (by omega)
    obtain ⟨k, hk1, hk2, g, hg, g1, g2⟩ := tri_reach t ht
    exact Or.inl ⟨k, g, hg, g1.trans (Fin.ext e1), g2.trans (Fin.ext e2)⟩
  · obtain ⟨t, ht, e1, e2⟩ := tri_listed y₂.2 y₁.2 a02 a01 a21 h₂ (by omega)
    obtain ⟨k, hk1, hk2, g, hg, g1, g2⟩ := tri_reach t ht
    exact Or.inr ⟨k, g, hg, g2.trans (Fin.ext e2), g1.trans (Fin.ext e1)⟩

end CFSG.Sporadic.SuzRecog.LevelTwo
