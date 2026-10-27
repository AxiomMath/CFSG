module

public import CFSG.RankThree.PartOne.S13K.Sp6DComm
public import CFSG.RankThree.PartOne.S13K.Comm134
public import CFSG.RankThree.PartOne.S13K.Sp6Blocks

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem sact_comp (π π' : Equiv.Perm (Fin 3)) (ε ε' : Fin 3 → Bool) (x : Fin 3 → (Qext K)ˣ) :
    sact π ε (sact π' ε' x) = sact (π * π') (fun j => xor (ε (π' j)) (ε' j)) x := by
  funext j
  have h1 : (π * π').symm j = π'.symm (π.symm j) := rfl
  have h2 : π' (π'.symm (π.symm j)) = π.symm j := Equiv.apply_symm_apply _ _
  simp only [sact_apply, h1, h2]
  rcases Bool.eq_false_or_eq_true (ε (π.symm j)) with h | h <;>
    rcases Bool.eq_false_or_eq_true (ε' (π'.symm (π.symm j))) with h' | h' <;> simp [h, h']

theorem sact_faithful {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p)
    {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → Bool}
    (h : ∀ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) → sact π ε x = sact π' ε' x) :
    π = π' ∧ ε = ε' := by
  have hev : ∀ i j, evec ζ i j ^ p = 1 := evec_pow ζ hζ.pow_eq_one
  have hz1 : ∀ b : Bool, (if b then ζ⁻¹ else ζ) ≠ 1 := by
    intro b
    cases b <;> simp [zeta_ne_one hζ h5, zeta_inv_ne_one hζ h5]
  have hζne : ζ⁻¹ ≠ ζ := (zeta_ne_inv hζ h5).symm
  have hζne' : ζ ≠ ζ⁻¹ := zeta_ne_inv hζ h5
  have hb : ∀ b b' : Bool, (if b then ζ⁻¹ else ζ) = (if b' then ζ⁻¹ else ζ) → b = b' := by
    intro b b' hbb
    cases b <;> cases b'
    · rfl
    · exact absurd (show ζ = ζ⁻¹ from hbb) hζne'
    · exact absurd (show ζ⁻¹ = ζ from hbb) hζne
    · rfl
  have key : ∀ i, π i = π' i ∧ ε i = ε' i := by
    intro i
    have e1 : sact π ε (evec ζ i) (π i) = if ε i then ζ⁻¹ else ζ := by
      rw [sact_evec]
      simp
    have e2 : sact π' ε' (evec ζ i) (π i) =
        if π'.symm (π i) = i then (if ε' i then ζ⁻¹ else ζ) else 1 := sact_evec ζ π' ε' i (π i)
    have h1 := congrFun (h (evec ζ i) (hev i)) (π i)
    rw [e1, e2] at h1
    have hpi : π'.symm (π i) = i := by
      by_contra hne
      simp only [hne, ↓reduceIte] at h1
      exact hz1 (ε i) h1
    simp only [hpi, ↓reduceIte] at h1
    have hπi : π i = π' i := by
      have h2 := congrArg π' hpi
      rw [Equiv.apply_symm_apply] at h2
      exact h2
    exact ⟨hπi, hb _ _ h1⟩
  exact ⟨Equiv.ext fun i => (key i).1, funext fun i => (key i).2⟩

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

theorem tSgn_apply_eT (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : Fin 3 → (Qext K)ˣ)
    (hx : ∀ i, x i ^ p = 1) : C.tSgn π ε (C.eT x hx) = C.eT (sact π ε x) (sact_pow hx) :=
  C.tAut_eT (sg10_hg1 C.hpq' π ε) (C.hg2_of_hg1 (sg10_hg1 C.hpq' π ε))
    (fun x hx => Subtype.ext (sgnPerm_conj C.hpq' π ε x (sact π ε x) hx (fun _ => rfl))) x hx

theorem sact_comm_of_comm {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → Bool}
    (hcomm : C.tSgn π ε * C.tSgn π' ε' = C.tSgn π' ε' * C.tSgn π ε)
    (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    sact π ε (sact π' ε' x) = sact π' ε' (sact π ε x) := by
  have h := congrArg (fun m : MulAut E => m (C.eT x hx)) hcomm
  simp only [MulAut.mul_apply] at h
  rw [C.tSgn_apply_eT π' ε' x hx, C.tSgn_apply_eT π ε (sact π' ε' x) (sact_pow hx),
    C.tSgn_apply_eT π ε x hx, C.tSgn_apply_eT π' ε' (sact π ε x) (sact_pow hx)] at h
  exact C.eT_injective h

theorem comm_data {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p)
    {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → Bool}
    (hcomm : C.tSgn π ε * C.tSgn π' ε' = C.tSgn π' ε' * C.tSgn π ε) :
    π * π' = π' * π ∧ (fun j => xor (ε (π' j)) (ε' j)) = (fun j => xor (ε' (π j)) (ε j)) := by
  refine sact_faithful hζ h5 (fun x hx => ?_)
  rw [← sact_comp π π' ε ε' x, ← sact_comp π' π ε' ε x]
  exact C.sact_comm_of_comm hcomm x hx

end Sp6Ctx

local instance instDecReflShape (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    Decidable (ReflShape π ε) := by
  unfold ReflShape
  infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem shape_cases : ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool), ReflShape π ε →
    (∃ i, π = 1 ∧ ε = fun j => decide (j = i)) ∨
    (∃ a b, a ≠ b ∧ π = Equiv.swap a b ∧ ε = fun _ => false) ∨
    (∃ a b, a ≠ b ∧ π = Equiv.swap a b ∧ ε = fun j => decide (j = a ∨ j = b)) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem comm_shapes : ∀ (π π' : Equiv.Perm (Fin 3)) (ε ε' : Fin 3 → Bool), ReflShape π ε →
    ReflShape π' ε' → π * π' = π' * π →
    (fun j => xor (ε (π' j)) (ε' j)) = (fun j => xor (ε' (π j)) (ε j)) → ¬ (π = π' ∧ ε = ε') →
    (∀ j, suppB π ε j = true → suppB π' ε' j = false) ∨
    (∃ a b, a ≠ b ∧ π = Equiv.swap a b ∧ π' = Equiv.swap a b ∧
      ((ε = (fun _ => false) ∧ ε' = fun j => decide (j = a ∨ j = b)) ∨
       (ε = (fun j => decide (j = a ∨ j = b)) ∧ ε' = fun _ => false))) := by
  decide +kernel

theorem suppB_S (i j : Fin 3) : suppB 1 (fun j => decide (j = i)) j = true ↔ j = i := by
  simp [suppB]

theorem suppB_D {a b : Fin 3} (hab : a ≠ b) (ε : Fin 3 → Bool)
    (hε : ε = (fun _ => false) ∨ ε = fun j => decide (j = a ∨ j = b)) (j : Fin 3) :
    suppB (Equiv.swap a b) ε j = true ↔ j = a ∨ j = b := by
  rcases hε with rfl | rfl
  · simp only [suppB, Bool.or_false, decide_eq_true_eq]
    by_cases hja : j = a
    · subst hja
      simp [hab, hab.symm]
    · by_cases hjb : j = b
      · subst hjb
        simp [hab, hab.symm]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb, hja, hjb]
  · simp only [suppB, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hja : j = a
    · simp [hja]
    · by_cases hjb : j = b
      · simp [hjb]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb, hja, hjb]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

theorem exists_blk_shape {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool} (hs : ReflShape π ε) :
    ∃ B : Subgroup ↥(M10 K), kZero p E (C.tSgn π ε) = B.map C.phi ∧
      ∀ g ∈ B, ∀ j, suppB π ε j = false → FixCoord g.1 j := by
  rcases shape_cases π ε hs with ⟨i, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
  · obtain ⟨B, hB, hfix⟩ := C.exists_blk_S i
    refine ⟨B, hB, fun g hg j hj => hfix g hg j ?_⟩
    intro hji
    have := (suppB_S i j).mpr hji
    rw [hj] at this
    exact absurd this (by simp)
  · obtain ⟨B, hB, hfix⟩ := C.exists_blk_D0 hab
    refine ⟨B, hB, fun g hg j hj => hfix g hg j ?_ ?_⟩
    · intro hja
      have := (suppB_D hab _ (Or.inl rfl) j).mpr (Or.inl hja)
      rw [hj] at this
      exact absurd this (by simp)
    · intro hjb
      have := (suppB_D hab _ (Or.inl rfl) j).mpr (Or.inr hjb)
      rw [hj] at this
      exact absurd this (by simp)
  · obtain ⟨B, hB, hfix⟩ := C.exists_blk_D1 hab
    refine ⟨B, hB, fun g hg j hj => hfix g hg j ?_ ?_⟩
    · intro hja
      have := (suppB_D hab _ (Or.inr rfl) j).mpr (Or.inl hja)
      rw [hj] at this
      exact absurd this (by simp)
    · intro hjb
      have := (suppB_D hab _ (Or.inr rfl) j).mpr (Or.inr hjb)
      rw [hj] at this
      exact absurd this (by simp)

theorem exists_blk_D01 {a b : Fin 3} (hab : a ≠ b) :
    ∃ B0 B1 : Subgroup ↥(M10 K),
      kZero p E (C.tSgn (Equiv.swap a b) (fun _ => false)) = B0.map C.phi ∧
      kZero p E (C.tSgn (Equiv.swap a b) (fun j => decide (j = a ∨ j = b))) = B1.map C.phi ∧
      ∀ g ∈ B0, ∀ h ∈ B1, g * h = h * g := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_of_ne a b hab
  refine ⟨cj (sg10 σ (fun _ => false)) (dBlk K),
    cj (sg10 1 (fun j => decide (j = b))) (cj (sg10 σ (fun _ => false)) (dBlk K)),
    C.kZero_D0 h0 h1, C.kZero_D1 hab h0 h1, ?_⟩
  intro g hg h hh
  obtain ⟨d, hd, rfl⟩ := mem_cj.mp hg
  obtain ⟨y, hy, rfl⟩ := mem_cj.mp hh
  obtain ⟨d', hd', rfl⟩ := mem_cj.mp hy
  set m : ↥(M10 K) := sg10 σ (fun _ => false) with hm
  have hĥ : (sg10 1 (fun j => decide (j = b)) : ↥(M10 K)) = m * gS1 K * m⁻¹ := by
    unfold gS1
    rw [hm, sg10_conj_perm]
    congr 1
    · simp
    · funext j
      have : σ.symm j = 1 ↔ j = b := by rw [Equiv.symm_apply_eq, h1]
      simp [this]
  have key := dBlk_comm_twist hd hd'
  rw [hĥ]
  have key' : m * (d * (gS1 K * d' * gS1 K)) * m⁻¹ = m * ((gS1 K * d' * gS1 K) * d) * m⁻¹ := by
    rw [key]
  have e1 : (m * d * m⁻¹) * ((m * gS1 K * m⁻¹) * (m * d' * m⁻¹) * (m * gS1 K * m⁻¹)⁻¹) =
      m * (d * (gS1 K * d' * (gS1 K)⁻¹)) * m⁻¹ := by group
  have e2 : ((m * gS1 K * m⁻¹) * (m * d' * m⁻¹) * (m * gS1 K * m⁻¹)⁻¹) * (m * d * m⁻¹) =
      m * ((gS1 K * d' * (gS1 K)⁻¹) * d) * m⁻¹ := by group
  rw [e1, e2, gS1_inv]
  exact key'

theorem kZero_le_centralizer_of_blocks {s t : MulAut E} {B B' : Subgroup ↥(M10 K)}
    (hs : kZero p E s = B.map C.phi) (ht : kZero p E t = B'.map C.phi)
    (hcomm : ∀ g ∈ B, ∀ h ∈ B', g * h = h * g) :
    kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) := by
  rw [hs, ht]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ B'.map C.phi := hy
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy'
  rw [← map_mul, ← map_mul, hcomm g hg h hh]

theorem kZero_comm_of_comm (hp5 : 5 ≤ p) {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → Bool}
    (hs : ReflShape π ε) (hs' : ReflShape π' ε') (hne : C.tSgn π ε ≠ C.tSgn π' ε')
    (hcomm : C.tSgn π ε * C.tSgn π' ε' = C.tSgn π' ε' * C.tSgn π ε) :
    kZero p E (C.tSgn π ε) ≤ Subgroup.centralizer (kZero p E (C.tSgn π' ε') : Set G) := by
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot C.h.prime C.hp2 C.hpq'
  obtain ⟨hπ, hε⟩ := C.comm_data hζ hp5 hcomm
  have hne' : ¬ (π = π' ∧ ε = ε') := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  rcases comm_shapes π π' ε ε' hs hs' hπ hε hne' with hdisj | ⟨a, b, hab, rfl, rfl, hcases⟩
  · obtain ⟨B, hB, hfix⟩ := C.exists_blk_shape hs
    obtain ⟨B', hB', hfix'⟩ := C.exists_blk_shape hs'
    refine C.kZero_le_centralizer_of_blocks hB hB' (fun g hg h hh => ?_)
    refine commute_of_disjoint_supp (Jg := {j | suppB π ε j = true})
      (Jh := {j | suppB π' ε' j = true}) (fun j hj hj' => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have h1 : suppB π' ε' j = true := hj'
      rw [hdisj j hj] at h1
      exact absurd h1 (by simp)
    · exact hfix g hg j (by simpa using hj)
    · exact hfix' h hh j (by simpa using hj)
  · obtain ⟨B0, B1, hB0, hB1, hcomm01⟩ := C.exists_blk_D01 hab
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C.kZero_le_centralizer_of_blocks hB0 hB1 hcomm01
    · exact C.kZero_le_centralizer_of_blocks hB1 hB0 (fun g hg h hh => (hcomm01 h hh g hg).symm)

end Sp6Ctx

theorem kfCommRow10 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFCommRow 10 := by
  intro G _ _ p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
  obtain ⟨f, hf, hpq, hmodel⟩ := hrow
  obtain ⟨K, _, _, _, ⟨C⟩⟩ := exists_sp6ctx hGA h hF hEA hf hpq hmodel
  obtain ⟨π, ε, hshape, rfl⟩ := C.exists_shape hs hsL
  obtain ⟨π', ε', hshape', rfl⟩ := C.exists_shape ht htL
  have hc := C.kZero_comm_of_comm (Sec12Three.five_le C.h) hshape hshape' hst hcomm
  have hKs : KFAt p E f (C.tSgn π ε) := C.kfAt_tSgn_of_shape hshape
  exact ⟨hc, inf_eq_bot_of_centralizes hc (KFAt.toLiftAt hKs).2.1⟩

end CFSG.RankThree.PartOne.S13K
