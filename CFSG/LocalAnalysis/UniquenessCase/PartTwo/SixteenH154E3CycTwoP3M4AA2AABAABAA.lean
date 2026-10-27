module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private theorem s16h_e3_CycTwo_inv_eq_self (hexp : ∀ w : W, w ^ 2 = 1) (a : W) : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, hexp]

private theorem s16h_e3_CycTwo_pow_three_eq_one {z : MulAut W} (hzord : orderOf z = 3) :
    z ^ 3 = 1 := by
  rw [← hzord]
  exact pow_orderOf_eq_one z

private theorem s16h_e3_CycTwo_iter_three {z : MulAut W} (hz3 : z ^ 3 = 1) (x : W) :
    z (z (z x)) = x := by
  have h : (z ^ 3) x = x := by rw [hz3, MulAut.one_apply]
  simpa [pow_succ, MulAut.mul_apply] using h

private theorem s16h_e3_CycTwo_mul_z_mul {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (x : W) :
    x * z x * z (z x) = 1 := by
  apply hfpf
  have hiter : z (z (z x)) = x := s16h_e3_CycTwo_iter_three hz3 x
  simp only [map_mul, hiter]
  ac_rfl

private theorem s16h_e3_CycTwo_mul_eq {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1) (x : W) :
    x * z x = z (z x) := by
  have h := s16h_e3_CycTwo_mul_z_mul hz3 hfpf x
  have hzz : z (z x) * z (z x) = 1 := by rw [← pow_two, hexp]
  calc x * z x = x * z x * 1 := (mul_one _).symm
    _ = x * z x * (z (z x) * z (z x)) := by rw [hzz]
    _ = (x * z x * z (z x)) * z (z x) := by group
    _ = z (z x) := by rw [h, one_mul]

private theorem s16h_e3_CycTwo_mul_eq' {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1) (x : W) :
    z x * z (z x) = x := by
  have h := s16h_e3_CycTwo_mul_z_mul hz3 hfpf x
  have hxx : x * x = 1 := by rw [← pow_two, hexp]
  calc z x * z (z x) = (x * x) * (z x * z (z x)) := by rw [hxx, one_mul]
    _ = x * (x * z x * z (z x)) := by group
    _ = x := by rw [h, mul_one]

private theorem s16h_e3_CycTwo_comm_of_rank {A : Subgroup (MulAut W)}
    (hA : IsElemAbelianOfRank 3 2 ↥A) {g h : MulAut W} (hg : g ∈ A) (hh : h ∈ A) :
    g * h = h * g := by
  obtain ⟨e⟩ := hA
  have h1 : (⟨g, hg⟩ * ⟨h, hh⟩ : ↥A) = ⟨h, hh⟩ * ⟨g, hg⟩ := by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  simpa using congrArg (fun a : ↥A => (a : MulAut W)) h1

private theorem s16h_e3_CycTwo_card_of_rank {A : Subgroup (MulAut W)}
    (hA : IsElemAbelianOfRank 3 2 ↥A) : Nat.card ↥A = 9 := by
  obtain ⟨e⟩ := hA
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide

private theorem s16h_e3_CycTwo_orbit_mul_stab [Finite W] [Finite (MulAut W)]
    (K : Subgroup (MulAut W)) (w : W) :
    (MulAction.orbit ↥K w).ncard * Nat.card (MulAction.stabilizer ↥K w) = Nat.card ↥K := by
  rw [← MulAction.index_stabilizer, mul_comm]
  exact Subgroup.card_mul_index _

private def s16h_e3_CycTwo_line (z : MulAut W) (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1) (u : W) :
    Subgroup W where
  carrier := {y | y = 1 ∨ y = u ∨ y = z u ∨ y = z (z u)}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    change a * b = 1 ∨ a * b = u ∨ a * b = z u ∨ a * b = z (z u)
    have hsq : ∀ c : W, c * c = 1 := fun c => by rw [← pow_two, hexp]
    have hab : ∀ c : W, c * z c = z (z c) := fun c => s16h_e3_CycTwo_mul_eq hz3 hfpf hexp c
    have hbc : ∀ c : W, z c * z (z c) = c := fun c => s16h_e3_CycTwo_mul_eq' hz3 hfpf hexp c
    have hac : ∀ c : W, c * z (z c) = z c := fun c => by
      calc c * z (z c) = (z c * z (z c)) * z (z c) := by rw [hbc]
        _ = z c * (z (z c) * z (z c)) := by group
        _ = z c := by rw [hsq, mul_one]
    have hba : ∀ c : W, z c * c = z (z c) := fun c => by rw [mul_comm, hab c]
    have hca : ∀ c : W, z (z c) * c = z c := fun c => by rw [mul_comm, hac c]
    have hcb : ∀ c : W, z (z c) * z c = c := fun c => by rw [mul_comm, hbc c]
    rcases ha with ha | ha | ha | ha <;> rw [ha] <;>
      rcases hb with hb | hb | hb | hb <;> rw [hb]
    all_goals simp only [one_mul, mul_one, hsq, hab, hba, hbc, hcb, hac, hca,
      s16h_e3_CycTwo_iter_three hz3 u]
    all_goals simp
  inv_mem' := by
    intro a ha
    change a⁻¹ = 1 ∨ a⁻¹ = u ∨ a⁻¹ = z u ∨ a⁻¹ = z (z u)
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · exact Or.inl inv_one
    · rw [s16h_e3_CycTwo_inv_eq_self hexp u]; exact Or.inr (Or.inl rfl)
    · rw [s16h_e3_CycTwo_inv_eq_self hexp (z u)]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [s16h_e3_CycTwo_inv_eq_self hexp (z (z u))]
      exact Or.inr (Or.inr (Or.inr rfl))

private theorem s16h_e3_CycTwo_mem_line {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1) (u y : W) :
    y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp u ↔
      y = 1 ∨ y = u ∨ y = z u ∨ y = z (z u) :=
  Iff.rfl

private theorem s16h_e3_CycTwo_card_line {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1) {u : W} (hu : u ≠ 1) :
    Nat.card ↥(s16h_e3_CycTwo_line z hz3 hfpf hexp u) = 4 := by
  have h1 : z u ≠ 1 := fun h => hu (z.injective (by rw [h, map_one]))
  have h2 : z (z u) ≠ 1 := fun h =>
    hu ((z * z).injective (by simp only [MulAut.mul_apply, map_one]; exact h))
  have h3 : z u ≠ u := fun h => hu (hfpf u h)
  have h4 : z (z u) ≠ u := by
    intro h
    have h' := congrArg z h
    rw [s16h_e3_CycTwo_iter_three hz3 u] at h'
    exact hu (hfpf u h'.symm)
  have h5 : z (z u) ≠ z u := fun h => hu (hfpf u (z.injective h))
  have hset : (s16h_e3_CycTwo_line z hz3 hfpf hexp u : Set W) =
      ({1, u, z u, z (z u)} : Set W) := rfl
  change (s16h_e3_CycTwo_line z hz3 hfpf hexp u : Set W).ncard = 4
  rw [hset]
  have hA : (1 : W) ∉ ({u, z u, z (z u)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h | h)
    · exact hu h.symm
    · exact h1 h.symm
    · exact h2 h.symm
  have hB : u ∉ ({z u, z (z u)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact h3 h.symm
    · exact h4 h.symm
  have hC : z u ∉ ({z (z u)} : Set W) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => h5 h.symm
  rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB,
    Set.ncard_insert_of_notMem hC, Set.ncard_singleton]

private theorem s16h_e3_CycTwo_ncard_triple {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) {x : W} (hx : x ≠ 1) :
    ({x, z x, z (z x)} : Set W).ncard = 3 := by
  have h1 : z x ≠ 1 := fun h => hx (z.injective (by rw [h, map_one]))
  have h2 : z (z x) ≠ 1 := fun h =>
    hx ((z * z).injective (by simp only [MulAut.mul_apply, map_one]; exact h))
  have h3 : z x ≠ x := fun h => hx (hfpf x h)
  have h4 : z (z x) ≠ x := by
    intro h
    have h' := congrArg z h
    rw [s16h_e3_CycTwo_iter_three hz3 x] at h'
    exact hx (hfpf x h'.symm)
  have h5 : z (z x) ≠ z x := fun h => hx (hfpf x (z.injective h))
  have hA : x ∉ ({z x, z (z x)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact h3 h.symm
    · exact h4 h.symm
  have hB : z x ∉ ({z (z x)} : Set W) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => h5 h.symm
  rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB, Set.ncard_singleton]

private theorem s16h_e3_CycTwo_inf_line_bot [Finite W] {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1)
    {x₁ x₂ : W}
    (hdisj : ({x₁, z x₁, z (z x₁)} : Set W) ∩
      ({x₂, z x₂, z (z x₂)} : Set W) = ∅) :
    s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊓
      s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  by_contra hy1
  have hy1' : y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ := hy.1
  have hy2' : y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ := hy.2
  rw [s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₁] at hy1'
  rw [s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₂] at hy2'
  have hyS₁ : y ∈ ({x₁, z x₁, z (z x₁)} : Set W) := by
    rcases hy1' with h | h | h | h
    · exact absurd h hy1
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr (Or.inl rfl)
    · rw [h]; exact Or.inr (Or.inr rfl)
  have hyS₂ : y ∈ ({x₂, z x₂, z (z x₂)} : Set W) := by
    rcases hy2' with h | h | h | h
    · exact absurd h hy1
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr (Or.inl rfl)
    · rw [h]; exact Or.inr (Or.inr rfl)
  have hmem : y ∈ ({x₁, z x₁, z (z x₁)} : Set W) ∩
      ({x₂, z x₂, z (z x₂)} : Set W) := ⟨hyS₁, hyS₂⟩
  rw [hdisj] at hmem
  exact hmem

private theorem s16h_e3_CycTwo_sup_line_top [Finite W] {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hexp : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 4) {x₁ x₂ : W} (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1)
    (hdisj : ({x₁, z x₁, z (z x₁)} : Set W) ∩
      ({x₂, z x₂, z (z x₂)} : Set W) = ∅) :
    s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊔
      s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ = ⊤ := by
  have hbot := s16h_e3_CycTwo_inf_line_bot hz3 hfpf hexp hdisj
  apply Subgroup.eq_top_of_card_eq
  have hinj : Function.Injective
      (fun p : ↥(s16h_e3_CycTwo_line z hz3 hfpf hexp x₁) ×
          ↥(s16h_e3_CycTwo_line z hz3 hfpf hexp x₂) =>
        (⟨(p.1 : W) * (p.2 : W),
          Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          ↥(s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊔
            s16h_e3_CycTwo_line z hz3 hfpf hexp x₂))) := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have hmem : (a₂ : W)⁻¹ * (a₁ : W) = (b₂ : W) * (b₁ : W)⁻¹ := by
      have h := congrArg (fun t : W => (a₂ : W)⁻¹ * t * (b₁ : W)⁻¹) heq
      simpa [mul_assoc] using h
    have hmemL₁ : (a₂ : W)⁻¹ * (a₁ : W) ∈
        s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ a₂.2) a₁.2
    have hmemL₂ : (a₂ : W)⁻¹ * (a₁ : W) ∈
        s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ := by
      rw [hmem]
      exact Subgroup.mul_mem _ b₂.2 (Subgroup.inv_mem _ b₁.2)
    have hmem1 : (a₂ : W)⁻¹ * (a₁ : W) ∈
        (s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊓
          s16h_e3_CycTwo_line z hz3 hfpf hexp x₂) := ⟨hmemL₁, hmemL₂⟩
    rw [hbot] at hmem1
    have h1 : (a₂ : W)⁻¹ * (a₁ : W) = 1 := Subgroup.mem_bot.mp hmem1
    have ha : (a₂ : W) = (a₁ : W) := inv_mul_eq_one.mp h1
    have hb : (b₂ : W) = (b₁ : W) := by
      have h2 : (b₂ : W) * (b₁ : W)⁻¹ = 1 := by rw [← hmem, h1]
      exact mul_inv_eq_one.mp h2
    exact Prod.ext (Subtype.ext ha.symm) (Subtype.ext hb.symm)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, s16h_e3_CycTwo_card_line hz3 hfpf hexp hx₁,
    s16h_e3_CycTwo_card_line hz3 hfpf hexp hx₂] at hle
  have hge := Subgroup.card_le_card_group
    (s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊔
      s16h_e3_CycTwo_line z hz3 hfpf hexp x₂)
  rw [hcard] at hge
  omega

private theorem s16h_e3_CycTwo_orbit_eq_triple [Finite W] [Finite (MulAut W)]
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    {A : Subgroup (MulAut W)} (hcardA : Nat.card ↥A = 9) (hzA : z ∈ A)
    {x : W} {S T : Set W} (hS : S = ({x, z x, z (z x)} : Set W))
    (hx1 : x ≠ 1) (hxT : x ∈ T) (hTcard : T.ncard = 6)
    (hAT : ∀ g : ↥A, ∀ y ∈ T, g • y ∈ T) :
    MulAction.orbit ↥A x = S := by
  have hXsubT : MulAction.orbit ↥A x ⊆ T := by
    intro y hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    rw [← hg]
    exact hAT g x hxT
  have hXdiv : (MulAction.orbit ↥A x).ncard ∣ 9 := by
    have hos := s16h_e3_CycTwo_orbit_mul_stab (K := A) x
    rw [hcardA] at hos
    exact ⟨_, hos.symm⟩
  have hSsubX : S ⊆ MulAction.orbit ↥A x := by
    rw [hS]
    intro y hy
    rcases hy with h | h | h
    · rw [h]; exact MulAction.mem_orbit_self x
    · rw [h]; exact MulAction.mem_orbit_iff.mpr ⟨⟨z, hzA⟩, rfl⟩
    · rw [h]
      exact MulAction.mem_orbit_iff.mpr ⟨⟨z, hzA⟩ * ⟨z, hzA⟩, by rw [mul_smul]; rfl⟩
  have h3le : 3 ≤ (MulAction.orbit ↥A x).ncard := by
    have := Set.ncard_le_ncard hSsubX
    rwa [hS, s16h_e3_CycTwo_ncard_triple hz3 hfpf hx1] at this
  have hXle : (MulAction.orbit ↥A x).ncard ≤ 6 := by
    have := Set.ncard_le_ncard hXsubT
    rwa [hTcard] at this
  have hXcard : (MulAction.orbit ↥A x).ncard = 3 := by
    obtain ⟨k, hk2, hk⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 2) (by norm_num)).mp hXdiv
    interval_cases k
    · omega
    · simpa using hk
    · omega
  exact (Set.eq_of_subset_of_ncard_le hSsubX
    (by rw [hXcard, hS, s16h_e3_CycTwo_ncard_triple hz3 hfpf hx1])).symm

private theorem s16h_e3_CycTwoP3M4AA2AABAABAA_caseB
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1)
    {E E' : Subgroup (MulAut W)}
    (hE : IsElemAbelianOfRank 3 2 ↥E) (hE' : IsElemAbelianOfRank 3 2 ↥E')
    (hzE : z ∈ E) (hzE' : z ∈ E')
    {w : W} (hw : w ≠ 1)
    (hE9 : (MulAction.orbit ↥E w).ncard = 9)
    (hOrb : MulAction.orbit ↥E w = MulAction.orbit ↥E' w) :
    E = E' := by
  classical
  have hcardE : Nat.card ↥E = 9 := s16h_e3_CycTwo_card_of_rank hE
  have hcardE' : Nat.card ↥E' = 9 := s16h_e3_CycTwo_card_of_rank hE'
  set O : Set W := MulAction.orbit ↥E w with hO
  have hOrb0 : MulAction.orbit ↥E w = MulAction.orbit ↥E' w := by rw [← hO]; exact hOrb
  have hOncard : O.ncard = 9 := by rw [hO]; exact hE9
  have h1notO : (1 : W) ∉ O := by
    rw [hO]
    intro hx
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
    have h : w = 1 := by
      have h2 := congrArg (fun y => (g⁻¹ : ↥E) • y) hg
      simpa using h2
    exact hw h
  set T : Set W := {x : W | x ∉ O ∧ x ≠ 1} with hT
  have hTcard : T.ncard = 6 := by
    have hTeq : T = Oᶜ \ ({1} : Set W) := by
      rw [hT]; ext x; simp
    have hsub1 : ({1} : Set W) ⊆ Oᶜ := by
      intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simpa using h1notO
    have hcompl : Oᶜ.ncard = 7 := by
      rw [Set.ncard_compl, hcard, hOncard]; norm_num
    rw [hTeq, Set.ncard_sdiff hsub1, Set.ncard_singleton, hcompl]
  have hO_E : ∀ g : ↥E, ∀ x ∈ O, g • x ∈ O := by
    intro g x hx
    rw [hO] at hx ⊢
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hx
    rw [← hh]
    exact MulAction.mem_orbit_iff.mpr ⟨g * h, by rw [mul_smul]⟩
  have hO_E' : ∀ g : ↥E', ∀ x ∈ O, g • x ∈ O := by
    intro g x hx
    have hxE : x ∈ MulAction.orbit ↥E w := by rwa [hO] at hx
    have hxE' : x ∈ MulAction.orbit ↥E' w := by rw [← hOrb0]; exact hxE
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hxE'
    rw [← hh, hO, hOrb0]
    exact MulAction.mem_orbit_iff.mpr ⟨g * h, by rw [mul_smul]⟩
  have hT_E : ∀ g : ↥E, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    rw [hT] at hx ⊢
    refine ⟨?_, ?_⟩
    · intro hmem
      have h := hO_E g⁻¹ (g • x) hmem
      exact hx.1 (by simpa using h)
    · intro hmem
      have h1 : x = 1 := by
        have h := congrArg (fun y => g⁻¹ • y) hmem
        simpa using h
      exact hx.2 h1
  have hT_E' : ∀ g : ↥E', ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    rw [hT] at hx ⊢
    refine ⟨?_, ?_⟩
    · intro hmem
      have h := hO_E' g⁻¹ (g • x) hmem
      exact hx.1 (by simpa using h)
    · intro hmem
      have h1 : x = 1 := by
        have h := congrArg (fun y => g⁻¹ • y) hmem
        simpa using h
      exact hx.2 h1
  have hTpos : 0 < T.ncard := by rw [hTcard]; norm_num
  obtain ⟨x₁, hx₁T⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hTcard]; norm_num)
  have hx₁ne1 : x₁ ≠ 1 := hx₁T.2
  set S₁ : Set W := ({x₁, z x₁, z (z x₁)} : Set W) with hS₁
  have hS₁card : S₁.ncard = 3 := by
    rw [hS₁]; exact s16h_e3_CycTwo_ncard_triple hz3 hfpf hx₁ne1
  have hX₁eqS₁ : MulAction.orbit ↥E x₁ = S₁ :=
    s16h_e3_CycTwo_orbit_eq_triple hz3 hfpf hcardE hzE hS₁ hx₁ne1 hx₁T hTcard hT_E
  have hX₁eqS₁' : MulAction.orbit ↥E' x₁ = S₁ :=
    s16h_e3_CycTwo_orbit_eq_triple hz3 hfpf hcardE' hzE' hS₁ hx₁ne1 hx₁T hTcard hT_E'
  have hS₁_E : ∀ g ∈ E, ∀ y ∈ S₁, g y ∈ S₁ := by
    intro g hg y hy
    have hyX : y ∈ MulAction.orbit ↥E x₁ := by rw [hX₁eqS₁]; exact hy
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hyX
    rw [← hh, ← hX₁eqS₁]
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩ * h, by simp [mul_smul]⟩
  have hS₁_E' : ∀ g ∈ E', ∀ y ∈ S₁, g y ∈ S₁ := by
    intro g hg y hy
    have hyX : y ∈ MulAction.orbit ↥E' x₁ := by rw [hX₁eqS₁']; exact hy
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hyX
    rw [← hh, ← hX₁eqS₁']
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩ * h, by simp [mul_smul]⟩
  set S₂ : Set W := T \ S₁ with hS₂
  have hS₁subT : S₁ ⊆ T := by
    intro y hy
    rw [hS₁] at hy
    rcases hy with h | h | h
    · rw [h]; exact hx₁T
    · rw [h]; exact hT_E ⟨z, hzE⟩ x₁ hx₁T
    · rw [h]
      exact hT_E ⟨z, hzE⟩ (z x₁) (hT_E ⟨z, hzE⟩ x₁ hx₁T)
  have hS₂card : S₂.ncard = 3 := by
    rw [hS₂, Set.ncard_sdiff hS₁subT, hTcard, hS₁card]
  have hS₂_z : ∀ y ∈ S₂, z y ∈ S₂ := by
    intro y hy
    refine ⟨hT_E ⟨z, hzE⟩ y hy.1, ?_⟩
    intro hmem
    have h := hS₁_E z⁻¹ (E.inv_mem hzE) (z y) hmem
    exact hy.2 (by simpa using h)
  have hS₂_E : ∀ g ∈ E, ∀ y ∈ S₂, g y ∈ S₂ := by
    intro g hg y hy
    refine ⟨hT_E ⟨g, hg⟩ y hy.1, ?_⟩
    intro hmem
    have h := hS₁_E g⁻¹ (E.inv_mem hg) (g y) hmem
    exact hy.2 (by simpa using h)
  have hS₂_E' : ∀ g ∈ E', ∀ y ∈ S₂, g y ∈ S₂ := by
    intro g hg y hy
    refine ⟨hT_E' ⟨g, hg⟩ y hy.1, ?_⟩
    intro hmem
    have h := hS₁_E' g⁻¹ (E'.inv_mem hg) (g y) hmem
    exact hy.2 (by simpa using h)
  have hS₂pos : 0 < S₂.ncard := by rw [hS₂card]; norm_num
  obtain ⟨x₂, hx₂⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hS₂card]; norm_num)
  have hx₂T : x₂ ∈ T := hx₂.1
  have hx₂ne1 : x₂ ≠ 1 := hx₂.1.2
  have hS₂eq : S₂ = ({x₂, z x₂, z (z x₂)} : Set W) := by
    have hsub : ({x₂, z x₂, z (z x₂)} : Set W) ⊆ S₂ := by
      intro y hy
      rcases hy with h | h | h
      · rw [h]; exact hx₂
      · rw [h]; exact hS₂_z x₂ hx₂
      · rw [h]; exact hS₂_z (z x₂) (hS₂_z x₂ hx₂)
    refine (Set.eq_of_subset_of_ncard_le hsub ?_).symm
    rw [hS₂card, s16h_e3_CycTwo_ncard_triple hz3 hfpf hx₂ne1]
  have hS₁S₂ : S₁ ∩ S₂ = ∅ := by
    rw [hS₂]; ext y; simp
  have hL₁ : ∀ y : W, y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ↔
      y ∈ ({1} ∪ S₁ : Set W) := by
    intro y
    rw [s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₁ y, hS₁]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  have hL₂ : ∀ y : W, y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ ↔
      y ∈ ({1} ∪ S₂ : Set W) := by
    intro y
    rw [s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₂ y, hS₂eq]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  have hbot : s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊓
      s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ = ⊥ := by
    apply s16h_e3_CycTwo_inf_line_bot hz3 hfpf hexp
    rw [← hS₁, ← hS₂eq]
    exact hS₁S₂
  have htop : s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊔
      s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ = ⊤ := by
    apply s16h_e3_CycTwo_sup_line_top hz3 hfpf hexp hcard hx₁ne1 hx₂ne1
    rw [← hS₁, ← hS₂eq]
    exact hS₁S₂
  have hS₁subL₁ : S₁ ⊆ (s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ : Set W) := by
    intro y hy
    exact (hL₁ y).mpr (Set.mem_union_right _ hy)
  have hS₂subL₂ : S₂ ⊆ (s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ : Set W) := by
    intro y hy
    exact (hL₂ y).mpr (Set.mem_union_right _ hy)
  have hLE1 : ∀ g ∈ E, ∀ u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁,
      g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ := by
    intro g hg u hu
    have hu' : u = 1 ∨ u = x₁ ∨ u = z x₁ ∨ u = z (z x₁) :=
      (s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₁ u).mp hu
    rcases hu' with h | h | h | h
    · rw [h, map_one]; exact Subgroup.one_mem _
    · rw [h]; exact hS₁subL₁ (hS₁_E g hg x₁ (by rw [hS₁]; exact Or.inl rfl))
    · rw [h]
      exact hS₁subL₁ (hS₁_E g hg (z x₁) (by rw [hS₁]; exact Or.inr (Or.inl rfl)))
    · rw [h]
      exact hS₁subL₁ (hS₁_E g hg (z (z x₁)) (by rw [hS₁]; exact Or.inr (Or.inr rfl)))
  have hLE1' : ∀ g ∈ E', ∀ u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁,
      g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ := by
    intro g hg u hu
    have hu' : u = 1 ∨ u = x₁ ∨ u = z x₁ ∨ u = z (z x₁) :=
      (s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₁ u).mp hu
    rcases hu' with h | h | h | h
    · rw [h, map_one]; exact Subgroup.one_mem _
    · rw [h]; exact hS₁subL₁ (hS₁_E' g hg x₁ (by rw [hS₁]; exact Or.inl rfl))
    · rw [h]
      exact hS₁subL₁ (hS₁_E' g hg (z x₁) (by rw [hS₁]; exact Or.inr (Or.inl rfl)))
    · rw [h]
      exact hS₁subL₁ (hS₁_E' g hg (z (z x₁)) (by rw [hS₁]; exact Or.inr (Or.inr rfl)))
  have hLE2 : ∀ g ∈ E, ∀ u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂,
      g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ := by
    intro g hg u hu
    have hu' : u = 1 ∨ u = x₂ ∨ u = z x₂ ∨ u = z (z x₂) :=
      (s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₂ u).mp hu
    rcases hu' with h | h | h | h
    · rw [h, map_one]; exact Subgroup.one_mem _
    · rw [h]; exact hS₂subL₂ (hS₂_E g hg x₂ (by rw [hS₂eq]; exact Or.inl rfl))
    · rw [h]
      exact hS₂subL₂ (hS₂_E g hg (z x₂) (by rw [hS₂eq]; exact Or.inr (Or.inl rfl)))
    · rw [h]
      exact hS₂subL₂ (hS₂_E g hg (z (z x₂)) (by rw [hS₂eq]; exact Or.inr (Or.inr rfl)))
  have hLE2' : ∀ g ∈ E', ∀ u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂,
      g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ := by
    intro g hg u hu
    have hu' : u = 1 ∨ u = x₂ ∨ u = z x₂ ∨ u = z (z x₂) :=
      (s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₂ u).mp hu
    rcases hu' with h | h | h | h
    · rw [h, map_one]; exact Subgroup.one_mem _
    · rw [h]; exact hS₂subL₂ (hS₂_E' g hg x₂ (by rw [hS₂eq]; exact Or.inl rfl))
    · rw [h]
      exact hS₂subL₂ (hS₂_E' g hg (z x₂) (by rw [hS₂eq]; exact Or.inr (Or.inl rfl)))
    · rw [h]
      exact hS₂subL₂ (hS₂_E' g hg (z (z x₂)) (by rw [hS₂eq]; exact Or.inr (Or.inr rfl)))
  set A : Subgroup (MulAut W) :=
    Subgroup.centralizer ({z} : Set (MulAut W)) ⊓
      stabSub (s16h_e3_CycTwo_line z hz3 hfpf hexp x₁) ⊓
      stabSub (s16h_e3_CycTwo_line z hz3 hfpf hexp x₂) with hA
  have hEA : E ≤ A := by
    intro g hg
    rw [hA]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ∀ h ∈ ({z} : Set (MulAut W)), h * g = g * h
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (s16h_e3_CycTwo_comm_of_rank hE hg hzE).symm
    · change ∀ u : W, g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ↔
          u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁
      intro u
      constructor
      · intro hu
        have h := hLE1 g⁻¹ (E.inv_mem hg) (g u) hu
        simpa using h
      · intro hu
        exact hLE1 g hg u hu
    · change ∀ u : W, g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ ↔
          u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂
      intro u
      constructor
      · intro hu
        have h := hLE2 g⁻¹ (E.inv_mem hg) (g u) hu
        simpa using h
      · intro hu
        exact hLE2 g hg u hu
  have hEA' : E' ≤ A := by
    intro g hg
    rw [hA]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ∀ h ∈ ({z} : Set (MulAut W)), h * g = g * h
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (s16h_e3_CycTwo_comm_of_rank hE' hg hzE').symm
    · change ∀ u : W, g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ↔
          u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁
      intro u
      constructor
      · intro hu
        have h := hLE1' g⁻¹ (E'.inv_mem hg) (g u) hu
        simpa using h
      · intro hu
        exact hLE1' g hg u hu
    · change ∀ u : W, g u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ ↔
          u ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂
      intro u
      constructor
      · intro hu
        have h := hLE2' g⁻¹ (E'.inv_mem hg) (g u) hu
        simpa using h
      · intro hu
        exact hLE2' g hg u hu
  have hx₁S₁ : ∀ g : ↥A, (g : MulAut W) x₁ ∈ S₁ := by
    intro g
    have hmem : (g : MulAut W) x₁ ∈
        s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ := by
      have hg : (g : MulAut W) ∈ stabSub (s16h_e3_CycTwo_line z hz3 hfpf hexp x₁) :=
        g.2.1.2
      exact (mem_stabSub.mp hg x₁).2
        ((s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₁ x₁).mpr (Or.inr (Or.inl rfl)))
    have hmem' : (g : MulAut W) x₁ ∈ ({1} ∪ S₁ : Set W) := by rwa [hL₁] at hmem
    have hne : (g : MulAut W) x₁ ≠ 1 := by
      intro h
      have hx : x₁ = 1 := by
        have := congrArg (fun y => (g : MulAut W)⁻¹ y) h
        simpa using this
      exact hx₁ne1 hx
    rcases (by simpa only [Set.mem_union, Set.mem_singleton_iff] using hmem') with h | h
    · exact absurd h hne
    · exact h
  have hx₂S₂ : ∀ g : ↥A, (g : MulAut W) x₂ ∈ S₂ := by
    intro g
    have hmem : (g : MulAut W) x₂ ∈
        s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ := by
      have hg : (g : MulAut W) ∈ stabSub (s16h_e3_CycTwo_line z hz3 hfpf hexp x₂) :=
        g.2.2
      exact (mem_stabSub.mp hg x₂).2
        ((s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₂ x₂).mpr (Or.inr (Or.inl rfl)))
    have hmem' : (g : MulAut W) x₂ ∈ ({1} ∪ S₂ : Set W) := by rwa [hL₂] at hmem
    have hne : (g : MulAut W) x₂ ≠ 1 := by
      intro h
      have hx : x₂ = 1 := by
        have := congrArg (fun y => (g : MulAut W)⁻¹ y) h
        simpa using this
      exact hx₂ne1 hx
    rcases (by simpa only [Set.mem_union, Set.mem_singleton_iff] using hmem') with h | h
    · exact absurd h hne
    · exact h
  have hAle : Nat.card ↥A ≤ 9 := by
    have hinj : Function.Injective
        (fun g : ↥A => ((⟨(g : MulAut W) x₁, hx₁S₁ g⟩ : ↥S₁),
            (⟨(g : MulAut W) x₂, hx₂S₂ g⟩ : ↥S₂))) := by
      intro g₁ g₂ heq
      have h1 : (g₁ : MulAut W) x₁ = (g₂ : MulAut W) x₁ := by
        have := congrArg (fun p : ↥S₁ × ↥S₂ => ((p.1 : W))) heq
        simpa using this
      have h2 : (g₁ : MulAut W) x₂ = (g₂ : MulAut W) x₂ := by
        have := congrArg (fun p : ↥S₁ × ↥S₂ => ((p.2 : W))) heq
        simpa using this
      have hhx₁ : ((g₁⁻¹ * g₂ : ↥A) : MulAut W) x₁ = x₁ := by
        show ((g₁ : MulAut W)⁻¹ * (g₂ : MulAut W)) x₁ = x₁
        rw [MulAut.mul_apply, MulAut.inv_apply, ← h1]
        simp
      have hhx₂ : ((g₁⁻¹ * g₂ : ↥A) : MulAut W) x₂ = x₂ := by
        show ((g₁ : MulAut W)⁻¹ * (g₂ : MulAut W)) x₂ = x₂
        rw [MulAut.mul_apply, MulAut.inv_apply, ← h2]
        simp
      have hzcomm : ((g₁⁻¹ * g₂ : ↥A) : MulAut W) * z =
          z * ((g₁⁻¹ * g₂ : ↥A) : MulAut W) := by
        have hmem : ((g₁⁻¹ * g₂ : ↥A) : MulAut W) ∈
            Subgroup.centralizer ({z} : Set (MulAut W)) := (g₁⁻¹ * g₂).2.1.1
        exact (Subgroup.mem_centralizer_iff.mp hmem z (by simp)).symm
      have hzc : ∀ y : W, ((g₁⁻¹ * g₂ : ↥A) : MulAut W) (z y) =
          z (((g₁⁻¹ * g₂ : ↥A) : MulAut W) y) := by
        intro y
        have h := congrArg (fun φ : MulAut W => φ y) hzcomm
        simpa [MulAut.mul_apply] using h
      have hfix₁ : ∀ y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁,
          ((g₁⁻¹ * g₂ : ↥A) : MulAut W) y = y := by
        intro y hy
        have hy' : y = 1 ∨ y = x₁ ∨ y = z x₁ ∨ y = z (z x₁) :=
          (s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₁ y).mp hy
        rcases hy' with h | h | h | h
        · rw [h, map_one]
        · rw [h]; exact hhx₁
        · rw [h, hzc x₁, hhx₁]
        · rw [h, hzc (z x₁), hzc x₁, hhx₁]
      have hfix₂ : ∀ y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₂,
          ((g₁⁻¹ * g₂ : ↥A) : MulAut W) y = y := by
        intro y hy
        have hy' : y = 1 ∨ y = x₂ ∨ y = z x₂ ∨ y = z (z x₂) :=
          (s16h_e3_CycTwo_mem_line hz3 hfpf hexp x₂ y).mp hy
        rcases hy' with h | h | h | h
        · rw [h, map_one]
        · rw [h]; exact hhx₂
        · rw [h, hzc x₂, hhx₂]
        · rw [h, hzc (z x₂), hzc x₂, hhx₂]
      have hone : ((g₁⁻¹ * g₂ : ↥A) : MulAut W) = 1 := by
        refine MulEquiv.ext fun y => ?_
        have hy : y ∈ s16h_e3_CycTwo_line z hz3 hfpf hexp x₁ ⊔
            s16h_e3_CycTwo_line z hz3 hfpf hexp x₂ := by
          rw [htop]; exact Subgroup.mem_top y
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy
        rw [map_mul, hfix₁ a ha, hfix₂ b hb]
        rfl
      have hg'' : (g₁ : MulAut W)⁻¹ * (g₂ : MulAut W) = 1 := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hone
      exact Subtype.ext (inv_mul_eq_one.mp hg'')
    have := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_prod, Nat.card_coe_set_eq, hS₁card, hS₂card] at this
    simpa using this
  have hEeqA : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hcardE]; exact hAle)
  have hE'eqA : E' = A := Subgroup.eq_of_le_of_card_ge hEA' (by rw [hcardE']; exact hAle)
  rw [hEeqA, hE'eqA]

theorem s16h_e3_CycTwoP3M4AA2AABAABAA_cover_of_nine
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {z : MulAut W} (hzord : orderOf z = 3)
    (hfpf : ∀ w : W, z w = w → w = 1)
    {E E' : Subgroup (MulAut W)}
    (hE : IsElemAbelianOfRank 3 2 ↥E) (hE' : IsElemAbelianOfRank 3 2 ↥E')
    (hzE : z ∈ E) (hzE' : z ∈ E') (hne : E ≠ E')
    {w : W} (hw : w ≠ 1)
    (hE9 : (MulAction.orbit ↥E w).ncard = 9)
    (hE'9 : (MulAction.orbit ↥E' w).ncard = 9) :
    ∃ b ∈ E ⊔ E', orderOf b = 3 ∧ b ∉ Subgroup.zpowers z ∧ b w = w := by
  classical
  have hz3 : z ^ 3 = 1 := s16h_e3_CycTwo_pow_three_eq_one hzord
  set O : Set W := MulAction.orbit ↥E w with hO
  set O' : Set W := MulAction.orbit ↥E' w with hO'
  have hOncard : O.ncard = 9 := by rw [hO]; exact hE9
  have hO'ncard : O'.ncard = 9 := by rw [hO']; exact hE'9
  by_cases hOrb : O = O'
  · refine absurd (s16h_e3_CycTwoP3M4AA2AABAABAA_caseB hexp hcard hz3 hfpf hE hE' hzE hzE'
      hw hOncard ?_) hne
    rw [← hO, ← hO']; exact hOrb
  · set H : Subgroup (MulAut W) := E ⊔ E' with hH
    set OH : Set W := MulAction.orbit ↥H w with hOH
    have hEsH : E ≤ H := by rw [hH]; exact le_sup_left
    have hE'sH : E' ≤ H := by rw [hH]; exact le_sup_right
    have hOsub : O ⊆ OH := by
      intro x hx
      rw [hO] at hx
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      rw [hOH]
      exact MulAction.mem_orbit_iff.mpr ⟨⟨(g : MulAut W), hEsH g.2⟩, rfl⟩
    have hO'sub : O' ⊆ OH := by
      intro x hx
      rw [hO'] at hx
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      rw [hOH]
      exact MulAction.mem_orbit_iff.mpr ⟨⟨(g : MulAut W), hE'sH g.2⟩, rfl⟩
    have hUnionSub : O ∪ O' ⊆ OH := Set.union_subset hOsub hO'sub
    have hOHge : 10 ≤ OH.ncard := by
      have h1 : (O ∪ O').ncard ≤ OH.ncard := Set.ncard_le_ncard hUnionSub
      have hproper : O ∩ O' ⊂ O := by
        refine ⟨Set.inter_subset_left, ?_⟩
        intro hsub
        exact hOrb (Set.eq_of_subset_of_ncard_le (fun x hx => (hsub hx).2)
          (by rw [hOncard, hO'ncard]))
      have h4 : (O ∩ O').ncard < 9 := by
        have := Set.ncard_lt_ncard hproper
        rwa [hOncard] at this
      have h5 : (O ∪ O').ncard + (O ∩ O').ncard = O.ncard + O'.ncard :=
        Set.ncard_union_add_ncard_inter O O'
      omega
    have hOHle : OH.ncard ≤ 15 := by
      have hsub : OH ⊆ ({x : W | x ≠ 1} : Set W) := by
        intro x hx hx1
        rw [hOH] at hx
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
        have hw1 : w = 1 := by
          have h : g⁻¹ • x = w := by rw [← hg]; simp
          rw [hx1] at h
          simpa using h.symm
        exact hw hw1
      have h2 : ({x : W | x ≠ 1} : Set W).ncard = 15 := by
        have hcompl : ({x : W | x ≠ 1} : Set W) = ({1} : Set W)ᶜ := by
          ext x; simp
        rw [hcompl, Set.ncard_compl, Set.ncard_singleton, hcard]
        norm_num
      exact (Set.ncard_le_ncard hsub).trans (le_of_eq h2)
    have hos := s16h_e3_CycTwo_orbit_mul_stab (K := H) w
    have h9H : 9 ∣ Nat.card ↥H := by
      have := Subgroup.card_dvd_of_le hEsH
      rwa [s16h_e3_CycTwo_card_of_rank hE] at this
    have h3stab : 3 ∣ Nat.card (MulAction.stabilizer ↥H w) := by
      by_contra hc
      have hcop : Nat.Coprime 9 (Nat.card (MulAction.stabilizer ↥H w)) := by
        have h3cop : Nat.Coprime 3 (Nat.card (MulAction.stabilizer ↥H w)) :=
          Nat.prime_three.coprime_iff_not_dvd.mpr hc
        have h9 : Nat.Coprime (3 ^ 2) (Nat.card (MulAction.stabilizer ↥H w)) :=
          (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 3 _).mpr h3cop
        simpa using h9
      have h9div : 9 ∣ (MulAction.orbit ↥H w).ncard := by
        apply hcop.dvd_of_dvd_mul_right
        rw [hos]
        exact h9H
      rw [hOH] at hOHge hOHle
      obtain ⟨k, hk⟩ := h9div
      omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer ↥H w) 3 h3stab
    refine ⟨(((b : MulAction.stabilizer ↥H w) : ↥H) : MulAut W), ?_, ?_, ?_, ?_⟩
    · exact ((b : MulAction.stabilizer ↥H w) : ↥H).2
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hb]
    · intro hmem
      have hbo : orderOf (((b : MulAction.stabilizer ↥H w) : ↥H) : MulAut W) = 3 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hb]
      have heq : Subgroup.zpowers (((b : MulAction.stabilizer ↥H w) : ↥H) : MulAut W) =
          Subgroup.zpowers z := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
        simp [Nat.card_zpowers, hbo, hzord]
      have hzmem : z ∈ Subgroup.zpowers (((b : _) : ↥H) : MulAut W) := by
        rw [heq]; exact Subgroup.mem_zpowers z
      have hzH : z ∈ H := by rw [hH]; exact Subgroup.mem_sup_left hzE
      have hmemH : (⟨z, hzH⟩ : ↥H) ∈
          Subgroup.zpowers ((b : MulAction.stabilizer ↥H w) : ↥H) := by
        rw [Subgroup.mem_zpowers_iff]
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzmem
        exact ⟨m, Subtype.ext (by simpa using hm)⟩
      have hzstab : (⟨z, hzH⟩ : ↥H) ∈ MulAction.stabilizer ↥H w :=
        (Subgroup.zpowers_le.mpr b.property) hmemH
      have hzw : z w = w := by
        have h := (MulAction.mem_stabilizer_iff).mp hzstab
        rw [MulAction.subgroup_smul_def] at h
        simpa using h
      exact hw (hfpf w hzw)
    · have h := (MulAction.mem_stabilizer_iff).mp b.property
      rw [MulAction.subgroup_smul_def] at h
      simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
