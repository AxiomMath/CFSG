module

public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.H13.Orbit

variable {W : Type} [CommGroup W]

@[expose] def pt (z : MulAut W) (w : W) : Set W := {w, z w, z (z w)}

theorem fsmul_ω₂ {z : MulAut W} (hzz : ∀ v : W, z (z v) = v * z v) (v : W) :
    fsmul z FieldFour.ω₂ v = z (z v) := by
  rw [hzz]
  rfl

theorem fsmul_mem_pt {z : MulAut W} (hzz : ∀ v : W, z (z v) = v * z v) {c : FieldFour}
    (hc : c ≠ 0) (v : W) : fsmul z c v ∈ pt z v := by
  have hc' : c = 1 ∨ c = FieldFour.ω ∨ c = FieldFour.ω₂ := by
    revert c
    decide
  rcases hc' with rfl | rfl | rfl
  · rw [fsmul_one]
    simp [pt]
  · rw [fsmul_ω]
    simp [pt]
  · rw [fsmul_ω₂ hzz]
    simp [pt]

theorem exists_fsmul_of_mem_pt {z : MulAut W} (hzz : ∀ v : W, z (z v) = v * z v)
    {x w : W} (hx : x ∈ pt z w) :
    ∃ a : FieldFour, (a = 1 ∨ a = FieldFour.ω ∨ a = FieldFour.ω₂) ∧ x = fsmul z a w := by
  simp only [pt, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, by rw [fsmul_one]⟩
  · exact ⟨FieldFour.ω, Or.inr (Or.inl rfl), by rw [fsmul_ω]⟩
  · exact ⟨FieldFour.ω₂, Or.inr (Or.inr rfl), by rw [fsmul_ω₂ hzz]⟩

@[expose] def points (z : MulAut W) (O : Set W) : Set (Set W) := pt z '' O

private theorem semiStab_conj_mul {z s t : MulAut W}
    (hs : s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z⁻¹)
    (ht : t * z * t⁻¹ = z ∨ t * z * t⁻¹ = z⁻¹) :
    (s * t) * z * (s * t)⁻¹ = z ∨ (s * t) * z * (s * t)⁻¹ = z⁻¹ := by
  have h_eq : (s * t) * z * (s * t)⁻¹ = s * (t * z * t⁻¹) * s⁻¹ := by group
  rw [h_eq]
  rcases ht with ht | ht
  · rw [ht]
    rcases hs with hs | hs
    · left; exact hs
    · right; exact hs
  · rw [ht]
    have h1 : s * z⁻¹ * s⁻¹ = (s * z * s⁻¹)⁻¹ := by group
    rw [h1]
    rcases hs with hs | hs
    · right; rw [hs]
    · left; rw [hs]; group

private theorem semiStab_conj_inv {z s : MulAut W}
    (hs : s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z⁻¹) :
    s⁻¹ * z * (s⁻¹)⁻¹ = z ∨ s⁻¹ * z * (s⁻¹)⁻¹ = z⁻¹ := by
  have h_eq : s⁻¹ * z * (s⁻¹)⁻¹ = s⁻¹ * z * s := by group
  rw [h_eq]
  rcases hs with hs | hs
  · left
    have h1 : s⁻¹ * (s * z * s⁻¹) * s = z := by group
    rw [hs] at h1
    exact h1
  · right
    have h1 : s⁻¹ * (s * z * s⁻¹) * s = z := by group
    rw [hs] at h1
    have h2 : s⁻¹ * z * s = (s⁻¹ * z⁻¹ * s)⁻¹ := by group
    rw [h1] at h2
    exact h2

@[expose] def semiStab (z : MulAut W) (O : Set W) : Subgroup (MulAut W) where
  carrier := {s | (s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z⁻¹) ∧ ⇑s '' O = O}
  mul_mem' := by
    intro s t hs ht
    obtain ⟨hs_conj, hs_img⟩ := hs
    obtain ⟨ht_conj, ht_img⟩ := ht
    exact ⟨semiStab_conj_mul hs_conj ht_conj, by
      rw [MulAut.coe_mul, Set.image_comp, ht_img, hs_img]⟩
  one_mem' := by
    refine ⟨?_, ?_⟩
    · left; simp
    · simp
  inv_mem' := by
    intro s hs
    obtain ⟨hs_conj, hs_img⟩ := hs
    refine ⟨semiStab_conj_inv hs_conj, ?_⟩
    have h1 : ⇑s⁻¹ '' (⇑s '' O) = O := by
      rw [Set.image_image]
      simp
    rwa [hs_img] at h1

variable {z : MulAut W} {O : Set W}

theorem mem_semiStab_iff {s : MulAut W} :
    s ∈ semiStab z O ↔ (s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z⁻¹) ∧ ⇑s '' O = O :=
  Iff.rfl

theorem image_pt (h3 : z ^ 3 = 1) {s : MulAut W}
    (hconj : s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z⁻¹) (w : W) :
    ⇑s '' pt z w = pt z (s w) := by
  rcases hconj with h | h
  · have hsz : ∀ v, s (z v) = z (s v) := by
      intro v
      have h1 := congrArg (fun f : MulAut W => f (s v)) h
      simpa [MulAut.mul_apply, MulAut.inv_apply_self] using h1
    simp only [pt, Set.image_insert_eq, Set.image_singleton]
    rw [hsz w, hsz (z w), hsz w]
  · have hsz : ∀ v, s (z v) = z⁻¹ (s v) := by
      intro v
      have h1 := congrArg (fun f : MulAut W => f (s v)) h
      simpa [MulAut.mul_apply, MulAut.inv_apply_self] using h1
    have hz_inv : z⁻¹ = z * z := by
      have h4 : z * (z * z) = 1 := by
        simpa [pow_succ, pow_two, mul_assoc] using h3
      exact inv_eq_of_mul_eq_one_right h4
    simp only [pt, Set.image_insert_eq, Set.image_singleton]
    rw [hsz w, hsz (z w), hsz w]
    rw [hz_inv]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl | rfl)
      · left; rfl
      · right; right; rfl
      · right; left
        have hz4 : z ^ 4 = z := by
          rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]
        have h4x : (z * z) ((z * z) (s w)) = z (s w) := by
          have : (z * z) ((z * z) (s w)) = (z ^ 4) (s w) := by rfl
          rw [this, hz4]
        exact h4x
    · rintro (rfl | rfl | rfl)
      · left; rfl
      · right; right
        have hz4 : z ^ 4 = z := by
          rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]
        have h4x : (z * z) ((z * z) (s w)) = z (s w) := by
          have : (z * z) ((z * z) (s w)) = (z ^ 4) (s w) := by rfl
          rw [this, hz4]
        exact h4x.symm
      · right; left; rfl

theorem image_mem_points (h3 : z ^ 3 = 1) {s : MulAut W} (hs : s ∈ semiStab z O) {P : Set W}
    (hP : P ∈ points z O) : ⇑s '' P ∈ points z O := by
  obtain ⟨w, hwO, rfl⟩ := hP
  have hconj := (mem_semiStab_iff.mp hs).1
  have h_img := (mem_semiStab_iff.mp hs).2
  have hsw : s w ∈ O := by
    rw [← h_img]
    exact Set.mem_image_of_mem _ hwO
  rw [image_pt h3 hconj w]
  exact Set.mem_image_of_mem _ hsw

@[expose] def pointPerm (h3 : z ^ 3 = 1) : ↥(semiStab z O) →* Equiv.Perm ↥(points z O) where
  toFun s :=
    { toFun := fun P => ⟨⇑(s : MulAut W) '' P.1, image_mem_points h3 s.2 P.2⟩
      invFun := fun P => ⟨⇑(s⁻¹ : MulAut W) '' P.1, image_mem_points h3 (inv_mem s.2) P.2⟩
      left_inv := by
        intro P
        apply Subtype.ext
        simp only [MulAut.coe_inv]
        rw [Set.image_image]
        simp
      right_inv := by
        intro P
        apply Subtype.ext
        simp only [MulAut.coe_inv]
        rw [Set.image_image]
        simp }
  map_one' := by
    ext P
    simp
  map_mul' := by
    intro s t
    ext P x
    change x ∈ ⇑((s : MulAut W) * (t : MulAut W)) '' P.1 ↔
      x ∈ ⇑(s : MulAut W) '' (⇑(t : MulAut W) '' P.1)
    rw [MulAut.coe_mul, Set.image_comp]

theorem coe_pointPerm_apply (h3 : z ^ 3 = 1) (s : ↥(semiStab z O)) (P : ↥(points z O)) :
    ((pointPerm h3 s P : ↥(points z O)) : Set W) = ⇑(s : MulAut W) '' P :=
  rfl

private theorem pt_z_eq_pt (h3 : z ^ 3 = 1) (w : W) : pt z (z w) = pt z w := by
  ext x
  simp only [pt, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h : z (z (z w)) = w := by
    have h1 := congrArg (fun f : MulAut W => f w) h3
    simpa [pow_succ, pow_two] using h1
  rw [h]
  constructor <;> intro hx <;> tauto

private theorem pt_eq_pt_of_mem (h3 : z ^ 3 = 1) {u w : W} (h : u ∈ pt z w) :
    pt z u = pt z w := by
  rcases (by simpa [pt] using h : u = w ∨ u = z w ∨ u = z (z w)) with rfl | rfl | rfl
  · rfl
  · exact pt_z_eq_pt h3 w
  · rw [pt_z_eq_pt h3 (z w), pt_z_eq_pt h3 w]

theorem pointPerm_eq_one_iff (h3 : z ^ 3 = 1) (s : ↥(semiStab z O)) :
    pointPerm h3 s = 1 ↔ ∀ w ∈ O, (s : MulAut W) w ∈ pt z w := by
  constructor
  · intro h w hw
    have hP : pt z w ∈ points z O := ⟨w, hw, rfl⟩
    have h1 : (pointPerm h3 s) ⟨pt z w, hP⟩ = ⟨pt z w, hP⟩ := by
      rw [h]
      rfl
    have h2 : ((pointPerm h3 s ⟨pt z w, hP⟩ : ↥(points z O)) : Set W) = pt z w := by
      rw [h1]
    rw [coe_pointPerm_apply] at h2
    have hwmem : w ∈ pt z w := by simp [pt]
    have hsw : (s : MulAut W) w ∈ ⇑(s : MulAut W) '' pt z w := Set.mem_image_of_mem _ hwmem
    rwa [h2] at hsw
  · intro h
    ext P x
    obtain ⟨w, hwO, hPw⟩ := P.2
    change x ∈ ⇑(s : MulAut W) '' P.1 ↔ x ∈ P.1
    have hEq : ⇑(s : MulAut W) '' pt z w = pt z w := by
      rw [image_pt h3 s.2.1 w]
      exact pt_eq_pt_of_mem h3 (h w hwO)
    rw [← hPw, hEq]

theorem pt_eq_pt_iff (h3 : z ^ 3 = 1) {u w : W} : pt z u = pt z w ↔ u ∈ pt z w := by
  constructor
  · intro h
    have : u ∈ pt z u := by simp [pt]
    rwa [h] at this
  · exact pt_eq_pt_of_mem h3

theorem ncard_pt (h3 : z ^ 3 = 1) (hfp : ∀ v : W, z v = v → v = 1) {w : W} (hw : w ≠ 1) :
    (pt z w).ncard = 3 := by
  have h1 : w ≠ z w := fun h => hw (hfp w h.symm)
  have h2 : w ≠ z (z w) := by
    intro h
    apply hw
    have h4 : z (z (z w)) = w := by
      have h1 := congrArg (fun f : MulAut W => f w) h3
      simpa [pow_succ, pow_two] using h1
    have h5 : z w = z (z (z w)) := congrArg z h
    rw [h4] at h5
    exact hfp w h5
  have h3' : z w ≠ z (z w) := fun h => h1 (z.injective h)
  have h4 : w ∉ ({z w, z (z w)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  have h5 : z w ∉ ({z (z w)} : Set W) := by
    simp only [Set.mem_singleton_iff]
    exact h3'
  rw [pt, Set.ncard_insert_of_notMem h4, Set.ncard_insert_of_notMem h5, Set.ncard_singleton]

theorem three_mul_card_points [Finite W] (h3 : z ^ 3 = 1) (hfp : ∀ v : W, z v = v → v = 1)
    (hO1 : (1 : W) ∉ O) (hzO : ∀ w ∈ O, z w ∈ O) :
    3 * Nat.card ↥(points z O) = Nat.card ↥O := by
  classical
  let : Fintype W := Fintype.ofFinite W
  have hO1' : ∀ w ∈ O, w ≠ 1 := fun w hw h => hO1 (h ▸ hw)
  have hpt_sub : ∀ w ∈ O, pt z w ⊆ O := by
    intro w hw x hx
    simp only [pt, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hw
    · exact hzO w hw
    · exact hzO (z w) (hzO w hw)
  have hMapsTo : (O.toFinset : Set W).MapsTo (pt z) (points z O).toFinset := by
    intro a ha
    have haO : a ∈ O := by simpa using ha
    have : pt z a ∈ points z O := ⟨a, haO, rfl⟩
    simpa using this
  have hsum := Finset.card_eq_sum_card_fiberwise hMapsTo
  have hterm : ∀ b ∈ (points z O).toFinset,
      (O.toFinset.filter (fun a => pt z a = b)).card = 3 := by
    intro b hb
    have hbpts : b ∈ points z O := by simpa using hb
    obtain ⟨w, hwO, rfl⟩ := hbpts
    have hfilter : O.toFinset.filter (fun a => pt z a = pt z w) = (pt z w).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.mem_toFinset]
      constructor
      · rintro ⟨haO, ha⟩
        exact (pt_eq_pt_iff h3).1 ha
      · intro ha
        have haO : a ∈ O := hpt_sub w hwO ha
        have ha' : pt z a = pt z w := (pt_eq_pt_iff h3).2 ha
        exact ⟨by simpa using haO, ha'⟩
    rw [hfilter, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact ncard_pt h3 hfp (hO1' w hwO)
  have hOcard : Nat.card ↥O = O.toFinset.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  have hPcard : Nat.card ↥(points z O) = (points z O).toFinset.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  have hsum3 : Nat.card ↥O = 3 * Nat.card ↥(points z O) := by
    rw [hOcard, hPcard, hsum]
    calc
      ∑ b ∈ (points z O).toFinset, (O.toFinset.filter (fun a => pt z a = b)).card
          = ∑ b ∈ (points z O).toFinset, 3 := Finset.sum_congr rfl hterm
      _ = 3 * (points z O).toFinset.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  exact hsum3.symm

private theorem pt_zpow_mem (h3 : z ^ 3 = 1) (n : ℤ) (w : W) : (z ^ n) w ∈ pt z w := by
  have h := zpow_eq_zpow_emod' n h3
  rw [h]
  have hlt : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hge : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg n (by norm_num)
  interval_cases hrem : n % (3 : ℤ)
  · simp [pt]
  · simp [pt]
  · simp [pt, pow_succ]

theorem mem_semiStab_self (h3 : z ^ 3 = 1) (hzO : ∀ w ∈ O, z w ∈ O) : z ∈ semiStab z O := by
  refine ⟨?_, ?_⟩
  · left; group
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨w, hwO, rfl⟩ := hx
      exact hzO w hwO
    · intro w hw
      have h2 : z (z (z w)) = w ∧ z (z w) ∈ O := by
        refine ⟨?_, hzO (z w) (hzO w hw)⟩
        have := congrArg (fun f : MulAut W => f w) h3
        simpa [pow_succ, pow_two] using this
      exact ⟨z (z w), h2.2, h2.1⟩

theorem zpowers_le_ker_pointPerm (h3 : z ^ 3 = 1) :
    (Subgroup.zpowers z).subgroupOf (semiStab z O) ≤ (pointPerm h3).ker := by
  intro x hx
  have hx' := Subgroup.mem_subgroupOf.1 hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx'
  rw [MonoidHom.mem_ker]
  rw [pointPerm_eq_one_iff h3 x]
  intro w hw
  rw [← hn]
  exact pt_zpow_mem h3 n w

structure Setup (W : Type) [CommGroup W] [Finite W] (K : Subgroup (MulAut W)) (z : ↥K) (f : W) :
    Prop where
  sq : ∀ w : W, w * w = 1
  card : Nat.card W = 2 ^ 6
  perf : Group.IsPerfect ↥K
  card_center : Nat.card (Subgroup.center ↥K) = 3
  quot : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6))
  center_eq : Subgroup.center ↥K = Subgroup.zpowers z
  pow_three : (z : MulAut W) ^ 3 = 1
  fpf : ∀ v : W, (z : MulAut W) v = v → v = 1
  ne_one : f ≠ 1
  orbit : ∀ v : W, v ≠ 1 →
    (v ∈ orbitIn K f → Nat.card (orbitIn K v) = 18) ∧
      (v ∉ orbitIn K f → Nat.card (orbitIn K v) = 45)

theorem exists_setup [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 2 ^ 6)
    {K : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6)) :
    ∃ (z : ↥K) (f : W), Setup W K z f := by
  obtain ⟨z, hcen, h3, hfp⟩ := exists_center_fpf hW2 hW hperf hZ e
  have hW64 : Nat.card W = 64 := by rw [hW]; norm_num
  have hperf_comm : commutator ↥K = ⊤ := hperf.commutator_eq_top
  have hfpf : ∀ y ∈ Subgroup.center ↥K, y ≠ 1 → ∀ v : W, (y : MulAut W) v = v → v = 1 := by
    intro y hy hy1 v hv
    rw [hcen] at hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hyn : (y : MulAut W) = (z : MulAut W) ^ n := by
      rw [← hn]
      exact map_zpow (Subgroup.subtype K) z n
    have hmod := zpow_eq_zpow_emod' n h3
    have hyn' : (y : MulAut W) = (z : MulAut W) ^ (n % (3 : ℤ)) := by
      rw [hyn, hmod]
      rfl
    rw [hyn'] at hv
    have hlt : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos n (by norm_num)
    have hge : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg n (by norm_num)
    interval_cases hrem : n % (3 : ℤ)
    · exfalso
      apply hy1
      apply Subtype.ext
      simpa using hyn'
    · exact hfp v (by simpa using hv)
    · have hvz : (z : MulAut W) ((z : MulAut W) v) = v := by
        have h2 : (z : MulAut W) ^ (2 : ℤ) = (z : MulAut W) * (z : MulAut W) := by
          rw [zpow_ofNat, pow_two]
        rw [h2, MulAut.mul_apply] at hv
        exact hv
      have hzv : (z : MulAut W) v = v := by
        have h := congrArg (fun x => (z : MulAut W) x) hvz
        have hz3 : (z : MulAut W) ((z : MulAut W) ((z : MulAut W) v)) = v := by
          have := congrArg (fun f : MulAut W => f v) h3
          simpa [pow_succ, pow_two] using this
        rw [hz3] at h
        exact h.symm
      exact hfp v hzv
  obtain ⟨f, hf1, horbit⟩ := hatA6_orbits hW64 hperf_comm hZ e hfpf
  exact ⟨z, f, {
    sq := fun w => by rw [← pow_two]; exact hW2 w
    card := hW
    perf := hperf
    card_center := hZ
    quot := ⟨e⟩
    center_eq := hcen
    pow_three := h3
    fpf := hfp
    ne_one := hf1
    orbit := horbit }⟩

namespace Setup

variable [Finite W] {K : Subgroup (MulAut W)} {z : ↥K} {f : W}

theorem zz (S : Setup W K z f) (w : W) :
    (z : MulAut W) ((z : MulAut W) w) = w * (z : MulAut W) w := by
  have hsq2 : ∀ v : W, v ^ 2 = 1 := fun v => by rw [pow_two]; exact S.sq v
  exact H13.zz_eq_of_fpf hsq2 S.pow_three (W := ⊤) (fun _ _ => trivial)
    (fun u _ hu => S.fpf u hu) trivial

theorem mem_orbit_self (_S : Setup W K z f) : f ∈ orbitIn K f :=
  mem_orbitIn_self K f

theorem one_not_mem_orbit (S : Setup W K z f) : (1 : W) ∉ orbitIn K f := by
  rintro ⟨k, hk, hkf⟩
  apply S.ne_one
  have h := congrArg (fun x => (k⁻¹ : MulAut W) x) hkf
  simpa using h

theorem z_mem_orbit (_S : Setup W K z f) {w : W} (hw : w ∈ orbitIn K f) :
    (z : MulAut W) w ∈ orbitIn K f := by
  obtain ⟨k, hk, rfl⟩ := hw
  exact ⟨(⟨(z : MulAut W) * k, K.mul_mem z.2 hk⟩ : K), K.mul_mem z.2 hk, rfl⟩

theorem card_orbit (S : Setup W K z f) : Nat.card ↥(orbitIn K f) = 18 :=
  (S.orbit f S.ne_one).1 S.mem_orbit_self

theorem card_points (S : Setup W K z f) : Nat.card ↥(points (z : MulAut W) (orbitIn K f)) = 6 := by
  have h := three_mul_card_points (O := orbitIn K f) S.pow_three S.fpf S.one_not_mem_orbit
    (fun w hw => S.z_mem_orbit hw)
  rw [S.card_orbit] at h
  omega

theorem commute_z (S : Setup W K z f) {k : MulAut W} (hk : k ∈ K) :
    k * (z : MulAut W) = (z : MulAut W) * k := by
  have hz_center : z ∈ Subgroup.center ↥K := by
    rw [S.center_eq]
    exact Subgroup.mem_zpowers z
  have hcomm := (Subgroup.mem_center_iff.1 hz_center) ⟨k, hk⟩
  exact congrArg (fun x : ↥K => (x : MulAut W)) hcomm

theorem le_semiStab (S : Setup W K z f) : K ≤ semiStab (z : MulAut W) (orbitIn K f) := by
  intro k hk
  constructor
  · left
    have hcomm : k * (z : MulAut W) = (z : MulAut W) * k := S.commute_z hk
    calc k * (z : MulAut W) * k⁻¹ = (z : MulAut W) * k * k⁻¹ := by rw [hcomm]
      _ = (z : MulAut W) := by group
  · apply Set.Subset.antisymm
    · rintro x ⟨w, hw, rfl⟩
      obtain ⟨h, hh, rfl⟩ := hw
      exact ⟨(⟨k * (h : MulAut W), K.mul_mem hk hh⟩ : K), K.mul_mem hk hh, rfl⟩
    · intro x hx
      obtain ⟨h, hh, rfl⟩ := hx
      refine ⟨((k⁻¹ * (h : MulAut W)) : MulAut W) f,
        ⟨(⟨k⁻¹ * (h : MulAut W), K.mul_mem (K.inv_mem hk) hh⟩ : K),
          K.mul_mem (K.inv_mem hk) hh, rfl⟩, ?_⟩
      simp [MulAut.mul_apply]

end Setup

end CFSG.Quasithin.HatA6

end
