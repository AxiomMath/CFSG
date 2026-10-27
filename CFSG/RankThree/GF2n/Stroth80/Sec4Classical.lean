module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iii
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank

private theorem subnormal_normal_of_top {X : Type*} [Group X] {H : Subgroup X}
    (hN : (H.subgroupOf ⊤).Normal) : H.Normal := by
  have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : H ≤ (⊤ : Subgroup X))).mp hN
  rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at h1
  exact h1

theorem isSubnormal_le_center_or_eq_top {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) {F : Subgroup X} (hF : F.IsSubnormal) :
    F ≤ Subgroup.center X ∨ F = ⊤ := by
  induction hF with
  | top => exact Or.inr rfl
  | step H K hHK _ hN ih =>
    rcases ih with hKZ | rfl
    · exact Or.inl (hHK.trans hKZ)
    · rcases normal_le_center_or_eq_top hX (subnormal_normal_of_top hN) with h | h
      · exact Or.inl h
      · exact Or.inr h

private theorem subnormal_central_one {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : ∀ g : G, z * g = g * z) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    rw [h, Subgroup.mem_bot] at hzc
    exact hzc
  · obtain ⟨a, b, hab⟩ := hG
    have ha : a ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

private theorem subnormal_exists_not_comm {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : z ≠ 1) : ∃ g : G, z * g ≠ g * z := by
  by_contra hcon
  push Not at hcon
  exact hz (subnormal_central_one hG hcon)

private theorem subnormal_comm_ne_one {G : Type*} [Group G] {x g : G} (h : x * g ≠ g * x) :
    g * x * g⁻¹ * x⁻¹ ≠ 1 := by
  intro h1
  apply h
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

private theorem subnormal_mem_fst_comm {A B : Type*} [Group A] [Group B]
    (N : Subgroup (A × B)) [hN : N.Normal] {a : A} {b : B} (h : ((a, b) : A × B) ∈ N)
    (g : A) :
    ((g * a * g⁻¹ * a⁻¹ : A), (1 : B)) ∈ N := by
  have h1 : ((g, (1 : B)) * (a, b) * (g, (1 : B))⁻¹ : A × B) ∈ N :=
    Subgroup.Normal.conj_mem hN _ h _
  have h2 := N.mul_mem h1 (N.inv_mem h)
  have heq : ((g * a * g⁻¹ * a⁻¹ : A), (1 : B)) =
      (g, (1 : B)) * (a, b) * (g, (1 : B))⁻¹ * (a, b)⁻¹ := by
    ext <;> simp
  rw [heq]
  exact h2

private theorem subnormal_mem_snd_comm {A B : Type*} [Group A] [Group B]
    (N : Subgroup (A × B)) [hN : N.Normal] {a : A} {b : B} (h : ((a, b) : A × B) ∈ N)
    (g : B) :
    ((1 : A), (g * b * g⁻¹ * b⁻¹ : B)) ∈ N := by
  have h1 : (((1 : A), g) * (a, b) * ((1 : A), g)⁻¹ : A × B) ∈ N :=
    Subgroup.Normal.conj_mem hN _ h _
  have h2 := N.mul_mem h1 (N.inv_mem h)
  have heq : ((1 : A), (g * b * g⁻¹ * b⁻¹ : B)) =
      ((1 : A), g) * (a, b) * ((1 : A), g)⁻¹ * (a, b)⁻¹ := by
    ext <;> simp
  rw [heq]
  exact h2

private theorem subnormal_le_fst {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    (N : Subgroup (A × B)) [N.Normal] {c : A} (hc : c ≠ 1)
    (hmem : ((c, (1 : B)) : A × B) ∈ N) :
    (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ N := by
  have hK : N.comap (MonoidHom.inl A B) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl A B)) with h | h
    · exfalso
      have hcK : c ∈ N.comap (MonoidHom.inl A B) := hmem
      rw [h, Subgroup.mem_bot] at hcK
      exact hc hcK
    · exact h
  intro p hp
  rw [Subgroup.mem_prod] at hp
  obtain ⟨_, hp2⟩ := hp
  have hp2' : p.2 = 1 := Subgroup.mem_bot.mp hp2
  have hpK : p.1 ∈ N.comap (MonoidHom.inl A B) := by
    rw [hK]
    exact Subgroup.mem_top _
  have hp' : ((p.1, (1 : B)) : A × B) ∈ N := hpK
  have hpe : p = (p.1, (1 : B)) := Prod.ext rfl hp2'
  rw [hpe]
  exact hp'

private theorem subnormal_le_snd {A B : Type*} [Group A] [Group B] [IsSimpleGroup B]
    (N : Subgroup (A × B)) [N.Normal] {c : B} (hc : c ≠ 1)
    (hmem : (((1 : A), c) : A × B) ∈ N) :
    (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ N := by
  have hK : N.comap (MonoidHom.inr A B) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr A B)) with h | h
    · exfalso
      have hcK : c ∈ N.comap (MonoidHom.inr A B) := hmem
      rw [h, Subgroup.mem_bot] at hcK
      exact hc hcK
    · exact h
  intro p hp
  rw [Subgroup.mem_prod] at hp
  obtain ⟨hp1, _⟩ := hp
  have hp1' : p.1 = 1 := Subgroup.mem_bot.mp hp1
  have hpK : p.2 ∈ N.comap (MonoidHom.inr A B) := by
    rw [hK]
    exact Subgroup.mem_top _
  have hp' : (((1 : A), p.2) : A × B) ∈ N := hpK
  have hpe : p = ((1 : A), p.2) := Prod.ext hp1' rfl
  rw [hpe]
  exact hp'

private theorem subnormal_top_bot_mem {A B : Type*} [Group A] [Group B] (a : A) :
    ((a, (1 : B)) : A × B) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B) :=
  Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩

private theorem subnormal_bot_top_mem {A B : Type*} [Group A] [Group B] (b : B) :
    (((1 : A), b) : A × B) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup B) :=
  Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩

private theorem subnormal_le_or {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    [IsSimpleGroup B] (hA : ∃ a b : A, a * b ≠ b * a) (hB : ∃ a b : B, a * b ≠ b * a)
    (N : Subgroup (A × B)) [N.Normal] (h : N ≠ ⊥) :
    (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ N ∨
      (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ N := by
  obtain ⟨⟨a, b⟩, hx, hne⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  by_cases ha : a = 1
  · right
    subst ha
    have hb : b ≠ 1 := by
      rintro rfl
      exact hne rfl
    obtain ⟨g, hg⟩ := subnormal_exists_not_comm hB hb
    exact subnormal_le_snd N (subnormal_comm_ne_one hg) (subnormal_mem_snd_comm N hx g)
  · left
    obtain ⟨g, hg⟩ := subnormal_exists_not_comm hA ha
    exact subnormal_le_fst N (subnormal_comm_ne_one hg) (subnormal_mem_fst_comm N hx g)

private theorem subnormal_fst {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    {H : Subgroup (A × B)} (hH : H ≤ (⊤ : Subgroup A).prod (⊥ : Subgroup B))
    (hN : (H.subgroupOf ((⊤ : Subgroup A).prod (⊥ : Subgroup B))).Normal) :
    H = ⊥ ∨ H = (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
  let L : Subgroup A := H.comap (MonoidHom.inl A B)
  have hLmem : ∀ a : A, a ∈ L ↔ ((a, (1 : B)) : A × B) ∈ H := fun a => Iff.rfl
  have hL : L.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hPa : ((a, (1 : B)) : A × B) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B) :=
      subnormal_top_bot_mem a
    have hPg : ((g, (1 : B)) : A × B) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B) :=
      subnormal_top_bot_mem g
    have hc := Subgroup.Normal.conj_mem hN ⟨((a, (1 : B)) : A × B), hPa⟩
      (Subgroup.mem_subgroupOf.mpr ((hLmem a).mp ha)) ⟨((g, (1 : B)) : A × B), hPg⟩
    have hc' : ((g, (1 : B)) * (a, (1 : B)) * (g, (1 : B))⁻¹ : A × B) ∈ H :=
      Subgroup.mem_subgroupOf.mp hc
    have heq : ((g, (1 : B)) * (a, (1 : B)) * (g, (1 : B))⁻¹ : A × B) =
        ((g * a * g⁻¹ : A), (1 : B)) := by
      ext <;> simp
    rw [heq] at hc'
    exact (hLmem _).mpr hc'
  haveI := hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hLb | hLt
  · left
    rw [eq_bot_iff]
    intro h hh
    have hP := hH hh
    rw [Subgroup.mem_prod] at hP
    obtain ⟨-, hP2⟩ := hP
    have hh2 : h.2 = 1 := Subgroup.mem_bot.mp hP2
    have hpe : ((h.1, (1 : B)) : A × B) = h := Prod.ext rfl hh2.symm
    have hL' : h.1 ∈ L := (hLmem h.1).mpr (by rw [hpe]; exact hh)
    rw [hLb, Subgroup.mem_bot] at hL'
    rw [Subgroup.mem_bot]
    exact Prod.ext hL' hh2
  · right
    refine le_antisymm hH ?_
    intro p hp
    rw [Subgroup.mem_prod] at hp
    obtain ⟨-, hp2⟩ := hp
    have hp2' : p.2 = 1 := Subgroup.mem_bot.mp hp2
    have hpL : p.1 ∈ L := by
      rw [hLt]
      exact Subgroup.mem_top _
    have hpe : ((p.1, (1 : B)) : A × B) = p := Prod.ext rfl hp2'.symm
    have hpH := (hLmem p.1).mp hpL
    rwa [hpe] at hpH

private theorem subnormal_snd {A B : Type*} [Group A] [Group B] [IsSimpleGroup B]
    {H : Subgroup (A × B)} (hH : H ≤ (⊥ : Subgroup A).prod (⊤ : Subgroup B))
    (hN : (H.subgroupOf ((⊥ : Subgroup A).prod (⊤ : Subgroup B))).Normal) :
    H = ⊥ ∨ H = (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
  let L : Subgroup B := H.comap (MonoidHom.inr A B)
  have hLmem : ∀ b : B, b ∈ L ↔ (((1 : A), b) : A × B) ∈ H := fun b => Iff.rfl
  have hL : L.Normal := by
    refine ⟨fun b hb g => ?_⟩
    have hPb : (((1 : A), b) : A × B) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup B) :=
      subnormal_bot_top_mem b
    have hPg : (((1 : A), g) : A × B) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup B) :=
      subnormal_bot_top_mem g
    have hc := Subgroup.Normal.conj_mem hN ⟨(((1 : A), b) : A × B), hPb⟩
      (Subgroup.mem_subgroupOf.mpr ((hLmem b).mp hb)) ⟨(((1 : A), g) : A × B), hPg⟩
    have hc' : (((1 : A), g) * ((1 : A), b) * ((1 : A), g)⁻¹ : A × B) ∈ H :=
      Subgroup.mem_subgroupOf.mp hc
    have heq : (((1 : A), g) * ((1 : A), b) * ((1 : A), g)⁻¹ : A × B) =
        ((1 : A), (g * b * g⁻¹ : B)) := by
      ext <;> simp
    rw [heq] at hc'
    exact (hLmem _).mpr hc'
  haveI := hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hLb | hLt
  · left
    rw [eq_bot_iff]
    intro h hh
    have hP := hH hh
    rw [Subgroup.mem_prod] at hP
    obtain ⟨hP1, -⟩ := hP
    have hh1 : h.1 = 1 := Subgroup.mem_bot.mp hP1
    have hpe : (((1 : A), h.2) : A × B) = h := Prod.ext hh1.symm rfl
    have hL' : h.2 ∈ L := (hLmem h.2).mpr (by rw [hpe]; exact hh)
    rw [hLb, Subgroup.mem_bot] at hL'
    rw [Subgroup.mem_bot]
    exact Prod.ext hh1 hL'
  · right
    refine le_antisymm hH ?_
    intro p hp
    rw [Subgroup.mem_prod] at hp
    obtain ⟨hp1, -⟩ := hp
    have hp1' : p.1 = 1 := Subgroup.mem_bot.mp hp1
    have hpL : p.2 ∈ L := by
      rw [hLt]
      exact Subgroup.mem_top _
    have hpe : (((1 : A), p.2) : A × B) = p := Prod.ext hp1'.symm rfl
    have hpH := (hLmem p.2).mp hpL
    rwa [hpe] at hpH

private theorem subnormal_normal_prod_cases {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    [IsSimpleGroup B] (hA : ∃ a b : A, a * b ≠ b * a) (hB : ∃ a b : B, a * b ≠ b * a)
    (N : Subgroup (A × B)) [N.Normal] :
    N = ⊥ ∨ N = (⊤ : Subgroup A).prod (⊥ : Subgroup B) ∨
      N = (⊥ : Subgroup A).prod (⊤ : Subgroup B) ∨ N = ⊤ := by
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  by_cases h1 : (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ N <;>
    by_cases h2 : (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ N
  · refine Or.inr (Or.inr (Or.inr (eq_top_iff.mpr ?_)))
    intro p _
    have hp : p = ((p.1, (1 : B)) : A × B) * ((1 : A), p.2) := by
      ext <;> simp
    rw [hp]
    exact N.mul_mem (h1 (subnormal_top_bot_mem p.1)) (h2 (subnormal_bot_top_mem p.2))
  · refine Or.inr (Or.inl (le_antisymm ?_ h1))
    intro x hx
    have hmem : (((1 : A), x.2) : A × B) ∈ N := by
      have h3 := N.mul_mem (N.inv_mem (h1 (subnormal_top_bot_mem x.1))) hx
      have e : (((1 : A), x.2) : A × B) = ((x.1, (1 : B)) : A × B)⁻¹ * x := by
        ext <;> simp
      rw [e]
      exact h3
    have hb : x.2 = 1 := by
      by_contra hb
      exact h2 (subnormal_le_snd N hb hmem)
    rw [Subgroup.mem_prod]
    exact ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr hb⟩
  · refine Or.inr (Or.inr (Or.inl (le_antisymm ?_ h2)))
    intro x hx
    have hmem : ((x.1, (1 : B)) : A × B) ∈ N := by
      have h3 := N.mul_mem (N.inv_mem (h2 (subnormal_bot_top_mem x.2))) hx
      have e : ((x.1, (1 : B)) : A × B) = (((1 : A), x.2) : A × B)⁻¹ * x := by
        ext <;> simp
      rw [e]
      exact h3
    have ha : x.1 = 1 := by
      by_contra ha
      exact h1 (subnormal_le_fst N ha hmem)
    rw [Subgroup.mem_prod]
    exact ⟨Subgroup.mem_bot.mpr ha, Subgroup.mem_top _⟩
  · exfalso
    rcases subnormal_le_or hA hB N h0 with h | h
    · exact h1 h
    · exact h2 h

theorem isSubnormal_prod_cases {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    [IsSimpleGroup B] (hA : ∃ a b : A, a * b ≠ b * a) (hB : ∃ a b : B, a * b ≠ b * a)
    {F : Subgroup (A × B)} (hF : F.IsSubnormal) :
    F = ⊥ ∨ F = (⊤ : Subgroup A).prod ⊥ ∨ F = (⊥ : Subgroup A).prod ⊤ ∨ F = ⊤ := by
  induction hF with
  | top => exact Or.inr (Or.inr (Or.inr rfl))
  | step H K hHK _ hN ih =>
    rcases ih with rfl | rfl | rfl | rfl
    · exact Or.inl (le_bot_iff.mp hHK)
    · rcases subnormal_fst hHK hN with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases subnormal_snd hHK hN with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · have hHn : H.Normal := subnormal_normal_of_top hN
      exact subnormal_normal_prod_cases hA hB H


theorem exists_orderOf_four_statedSL (K : Type) [Field K] [CharP K 2] (m : ℕ) (hm : 3 ≤ m) :
    ∃ g : ↥(StatedSL m K), orderOf g = 4 := by
  obtain ⟨i0, hi0⟩ : ∃ i : Fin m, i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin m, i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin m, i.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have h01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; omega
  have h10 : i1 ≠ i0 := fun h => by have := congrArg Fin.val h; omega
  have h12 : i1 ≠ i2 := fun h => by have := congrArg Fin.val h; omega
  have h21 : i2 ≠ i1 := fun h => by have := congrArg Fin.val h; omega
  have h20 : i2 ≠ i0 := fun h => by have := congrArg Fin.val h; omega
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin m) (Fin m) K,
      N = Matrix.single i0 i1 1 + Matrix.single i1 i2 1 := ⟨_, rfl⟩
  have hNN : N * N = Matrix.single i0 i2 1 := by
    rw [hN]
    simp [add_mul, mul_add, h10, h20, h21]
  have hN3 : N * N * N = 0 := by
    rw [hNN, hN]
    simp [mul_add, h20, h21]
  have hNnz : N * N ≠ 0 := by
    rw [hNN]
    intro h
    have := congrArg (fun M : Matrix (Fin m) (Fin m) K => M i0 i2) h
    simp at this
  have hNN2 : N + N = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hsq2 : N * N + N * N = 0 := by
    rw [← add_mul, hNN2, zero_mul]
  have hNNNN : N * N * (N * N) = 0 := by
    rw [← mul_assoc (N * N) N N, hN3, zero_mul]
  have hsq : (1 + N) ^ 2 = 1 + N * N := by
    have e : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    rw [sq, e, hNN2, add_zero]
  have h4 : (1 + N) ^ 4 = 1 := by
    have e1 : (1 + N) ^ 4 = (1 + N) ^ 2 * (1 + N) ^ 2 := by
      rw [← pow_add]
    have e2 : (1 + N * N) * (1 + N * N) = 1 + (N * N + N * N) + N * N * (N * N) := by
      noncomm_ring
    rw [e1, hsq, e2, hNNNN, hsq2, add_zero, add_zero]
  have hdet : (1 + N).det = 1 := by
    have htri : Matrix.IsUpperTriangular (1 + N) := by
      intro i j hji
      have hv : j.val < i.val := hji
      have h1 : i ≠ j := fun h => by subst h; omega
      have h2 : ¬ (i0 = i ∧ i1 = j) := fun h => by
        have := congrArg Fin.val h.1
        omega
      have h3 : ¬ (i1 = i ∧ i2 = j) := fun h => by
        have := congrArg Fin.val h.1
        have := congrArg Fin.val h.2
        omega
      rw [hN]
      simp [Matrix.single, Matrix.one_apply, h1, h2, h3]
    rw [Matrix.det_of_isUpperTriangular htri]
    refine Finset.prod_eq_one fun i _ => ?_
    have d1 : ¬ (i0 = i ∧ i1 = i) := fun h => h01 (h.1.trans h.2.symm)
    have d2 : ¬ (i1 = i ∧ i2 = i) := fun h => h12 (h.1.trans h.2.symm)
    rw [hN]
    simp [Matrix.single, Matrix.one_apply, d1, d2]
  have hIsU : IsUnit (1 + N) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hIsU
  have hudet : (u : Matrix (Fin m) (Fin m) K).det = 1 := by
    rw [hu, hdet]
  have hmem : u ∈ StatedSL m K := mem_statedSL_of_det hudet
  have hu2 : u ^ 2 ≠ 1 := by
    intro h
    have h' : (u : Matrix (Fin m) (Fin m) K) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    rw [hu, hsq] at h'
    apply hNnz
    simpa using h'
  have hu4 : u ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hu, h4]
  have hnot : ¬ (⟨u, hmem⟩ : ↥(StatedSL m K)) ^ 2 ^ 1 = 1 := by
    intro h
    apply hu2
    have h' := congrArg Subtype.val h
    simpa using h'
  have hfin : (⟨u, hmem⟩ : ↥(StatedSL m K)) ^ 2 ^ (1 + 1) = 1 := by
    apply Subtype.ext
    simpa using hu4
  refine ⟨⟨u, hmem⟩, ?_⟩
  have key := orderOf_eq_prime_pow hnot hfin
  simpa using key


theorem card_sylow_statedSL_two (K : Type) [Field K] [Finite K] [CharP K 2]
    (P : Sylow 2 ↥(StatedSL 2 K)) : Nat.card P = Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hq1 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq0 : Nat.card K ≠ 0 := by omega
  have hq2 : 2 ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self 2 m.ne_zero
  have hsq : 2 ∣ Nat.card K ^ 2 := dvd_pow hq2 two_ne_zero
  have hsq4 : 4 ≤ Nat.card K ^ 2 := by nlinarith
  have hodd : ¬ 2 ∣ Nat.card K ^ 2 - 1 := by omega
  have hne : Nat.card K ^ 2 - 1 ≠ 0 := by omega
  haveI : Finite (StatedSL 2 K) := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Open.StatedAPI.card_statedSL_two]
    exact Nat.mul_ne_zero hq0 hne)
  rw [Sylow.card_eq_multiplicity, CFSG.Open.StatedAPI.card_statedSL_two,
    Nat.factorization_mul hq0 hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hq,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem nonempty_statedSp_one_mulEquiv_statedSL_two (K : Type) [Field K] :
    Nonempty (↥(StatedSp 1 K) ≃* ↥(StatedSL 2 K)) := by
  exact ⟨(Subgroup.equivMapOfInjective (StatedSp 1 K) (reindexGL sumFinTwo).toMonoidHom
    (reindexGL sumFinTwo).injective).trans (MulEquiv.subgroupCongr map_reindexGL_statedSp_one)⟩


@[expose] def IsClassicalOver (K : Type) [Field K] (G : Type) [Group G] : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ Nonempty (G ≃* ↥(StatedSL m K))) ∨
  (∃ m : ℕ, 1 ≤ m ∧ Nonempty (G ≃* ↥(StatedSp m K))) ∨
  (∃ m : ℕ, 2 ≤ m ∧ Nonempty (G ≃* ↥(StatedOmega (StatedQuadPlus m K)))) ∨
  (∃ (m : ℕ) (b c : K), 2 ≤ m ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
    Nonempty (G ≃* ↥(StatedOmega (StatedQuadMinus m K b c))))

@[expose] def ClassicalOrderFourStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    (∀ m : ℕ, 2 ≤ m → ∃ g : ↥(StatedSp m K), orderOf g = 4) ∧
    (∀ m : ℕ, 3 ≤ m → ∃ g : ↥(StatedOmega (StatedQuadPlus m K)), orderOf g = 4) ∧
    (∀ (m : ℕ) (b c : K), 3 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∃ g : ↥(StatedOmega (StatedQuadMinus m K b c)), orderOf g = 4)

@[expose] def OmegaMinusFourSylowStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ (b c : K),
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ P : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)), Nat.card P = Nat.card K ^ 2

section ClassicalCases

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]

theorem IsClassicalOver.shape (hCQ : ClassicalQuasisimpleStatement) (hq : 4 ≤ Nat.card K)
    (hG : IsClassicalOver K G) :
    CFSG.IsQuasisimple G ∨ Nonempty (G ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
  obtain ⟨hSL, hSp, hOP, hOM, ⟨eΩ⟩⟩ := hCQ K hq
  rcases hG with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, b, c, hm, hirr, ⟨e⟩⟩
  · exact Or.inl (isQuasisimple_of_mulEquiv' e.symm (hSL m hm))
  · exact Or.inl (isQuasisimple_of_mulEquiv' e.symm (hSp m hm))
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 2 := by omega
      exact Or.inr ⟨e.trans eΩ⟩
    · exact Or.inl (isQuasisimple_of_mulEquiv' e.symm (hOP m h3))
  · exact Or.inl (isQuasisimple_of_mulEquiv' e.symm (hOM m b c hm hirr))

theorem IsClassicalOver.cases (hCQ : ClassicalQuasisimpleStatement)
    (hO4 : ClassicalOrderFourStatement) (hq : 4 ≤ Nat.card K) (hG : IsClassicalOver K G)
    (hno : ∀ g : G, orderOf g ≠ 4) :
    Nonempty (G ≃* ↥(StatedSL 2 K)) ∨ Nonempty (G ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) ∨
      ∃ (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* ↥(StatedOmega (StatedQuadMinus 2 K b c))) := by
  obtain ⟨-, -, -, -, ⟨eΩ⟩⟩ := hCQ K hq
  obtain ⟨hSp, hOP, hOM⟩ := hO4 K hq
  have transfer : ∀ {H : Type} [Group H], (G ≃* H) → (∃ g : H, orderOf g = 4) → False := by
    intro H _ e ⟨g, hg⟩
    exact hno (e.symm g) (by rw [MulEquiv.orderOf_eq]; exact hg)
  rcases hG with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, b, c, hm, hirr, ⟨e⟩⟩
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 2 := by omega
      exact Or.inl ⟨e⟩
    · exact (transfer e (exists_orderOf_four_statedSL K m h3)).elim
  · rcases Nat.lt_or_ge m 2 with h2 | h2
    · obtain rfl : m = 1 := by omega
      obtain ⟨e'⟩ := nonempty_statedSp_one_mulEquiv_statedSL_two K
      exact Or.inl ⟨e.trans e'⟩
    · exact (transfer e (hSp m h2)).elim
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 2 := by omega
      exact Or.inr (Or.inl ⟨e.trans eΩ⟩)
    · exact (transfer e (hOP m h3)).elim
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 2 := by omega
      exact Or.inr (Or.inr ⟨b, c, hirr, ⟨e⟩⟩)
    · exact (transfer e (hOM m b c h3 hirr)).elim

theorem noOrderFour_of_exp_two {H : Type} [Group H]
    (h : ∀ y : H, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 = 1) :
    ∀ g : H, orderOf g ≠ 4 := by
  intro g hg
  have h4 : g ^ 4 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  have h2 : g ^ 2 = 1 := h g ⟨2, by norm_num; exact h4⟩
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hg] at this
  omega

theorem subnormal_cases_of_shape (hSL2 : CFSG.IsQuasisimple ↥(StatedSL 2 K)) [Finite G]
    (hG : CFSG.IsQuasisimple G ∨ Nonempty (G ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)))
    {F : Subgroup G} (hF : F.IsSubnormal) (hns : ¬ Group.IsSolvable ↥F) :
    F = ⊤ ∨ Nonempty (↥F ≃* ↥(StatedSL 2 K)) := by
  rcases hG with hq | hne
  · rcases isSubnormal_le_center_or_eq_top hq hF with h | h
    · exfalso
      apply hns
      refine isSolvable_of_comm fun a b => ?_
      exact Subtype.ext (Subgroup.mem_center_iff.mp (h b.2) a)
    · exact Or.inl h
  · obtain ⟨e⟩ := hne
    haveI : IsSimpleGroup ↥(StatedSL 2 K) := isSimpleGroup_statedSL_two hSL2
    have hA : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact not_isSolvable_of_isQuasisimple hSL2 (isSolvable_of_comm fun a b => h a b)
    have hF' : (F.map e.toMonoidHom).IsSubnormal := hF.map e.surjective
    have eF : Nonempty (↥F ≃* ↥(F.map e.toMonoidHom)) :=
      ⟨Subgroup.equivMapOfInjective F e.toMonoidHom e.injective⟩
    obtain ⟨eF⟩ := eF
    rcases isSubnormal_prod_cases hA hA hF' with h | h | h | h
    · exfalso
      apply hns
      have : F = ⊥ := (Subgroup.map_eq_bot_iff_of_injective F e.injective).mp h
      rw [this]
      infer_instance
    · obtain ⟨t1⟩ := exists_equiv_top_bot ↥(StatedSL 2 K) ↥(StatedSL 2 K)
      exact Or.inr ⟨eF.trans ((MulEquiv.subgroupCongr h).trans t1)⟩
    · obtain ⟨b1⟩ := exists_equiv_bot_top ↥(StatedSL 2 K) ↥(StatedSL 2 K)
      exact Or.inr ⟨eF.trans ((MulEquiv.subgroupCongr h).trans b1)⟩
    · left
      rw [eq_top_iff]
      intro x _
      have hx : e x ∈ F.map e.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := e.injective hyx
      rwa [this] at hy

end ClassicalCases

section Embedding

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem subnormal_embedding_cases (hSL2 : CFSG.IsQuasisimple ↥(StatedSL 2 K)) {Γ : Type}
    [Group Γ] [Finite Γ] {R H X : Subgroup Γ} {Gc : Type} [Group Gc] (π : ↥R →* Gc)
    (hπ : Function.Surjective π)
    (hGc : CFSG.IsQuasisimple Gc ∨ Nonempty (Gc ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)))
    (hXH : X ≤ H) (hHR : H ≤ R) (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hHn : ∀ r ∈ R, ∀ h ∈ H, r * h * r⁻¹ ∈ H)
    (hinj : ∀ x : ↥X, π ⟨(x : Γ), hHR (hXH x.2)⟩ = 1 → x = 1) (hns : ¬ Group.IsSolvable ↥X) :
    ((∀ g : Gc, ∃ x : ↥X, π ⟨(x : Γ), hHR (hXH x.2)⟩ = g) ∧
      ((CFSG.IsQuasisimple Gc ∧ Nonempty (↥X ≃* Gc)) ∨
        Nonempty (↥X ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)))) ∨
      Nonempty (↥X ≃* ↥(StatedSL 2 K)) := by
  haveI : Finite Gc := Finite.of_surjective π hπ
  let f : ↥X →* Gc := π.comp (Subgroup.inclusion (hXH.trans hHR))
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    exact fun x hx => hinj x hx
  let f' : ↥H →* Gc := π.comp (Subgroup.inclusion hHR)
  have hF'n : f'.range.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨h, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hπ g
    refine ⟨⟨(r : Γ) * (h : Γ) * (r : Γ)⁻¹, hHn r r.2 h h.2⟩, ?_⟩
    show π ⟨(r : Γ) * (h : Γ) * (r : Γ)⁻¹, _⟩ = π r * π ⟨(h : Γ), hHR h.2⟩ * (π r)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hFF' : f.range ≤ f'.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨(x : Γ), hXH x.2⟩, rfl⟩
  have hFn : (f.range.subgroupOf f'.range).Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨h, hh⟩ := g.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨⟨(h : Γ) * (x : Γ) * (h : Γ)⁻¹, hXn h h.2 x x.2⟩, ?_⟩
    show π ⟨(h : Γ) * (x : Γ) * (h : Γ)⁻¹, _⟩ = (g : Gc) * (y : Gc) * (g : Gc)⁻¹
    rw [← hh, ← hx]
    show π ⟨(h : Γ) * (x : Γ) * (h : Γ)⁻¹, _⟩ =
      π ⟨(h : Γ), hHR h.2⟩ * π ⟨(x : Γ), hHR (hXH x.2)⟩ * (π ⟨(h : Γ), hHR h.2⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hFsub : f.range.IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ hFF' hF'n.isSubnormal hFn
  let e : ↥X ≃* ↥f.range := MonoidHom.ofInjective hfinj
  have hFns : ¬ Group.IsSolvable ↥f.range := fun h =>
    hns (solvable_of_solvable_injective (f := e.toMonoidHom) e.injective)
  rcases subnormal_cases_of_shape hSL2 hGc hFsub hFns with h | he'
  · have hsurj : Function.Surjective f := by
      intro g
      have : g ∈ f.range := by rw [h]; exact Subgroup.mem_top _
      exact this
    let e2 : ↥X ≃* Gc := MulEquiv.ofBijective f ⟨hfinj, hsurj⟩
    refine Or.inl ⟨hsurj, ?_⟩
    rcases hGc with hq | he3
    · exact Or.inl ⟨hq, ⟨e2⟩⟩
    · obtain ⟨e3⟩ := he3
      exact Or.inr ⟨e2.trans e3⟩
  · obtain ⟨e'⟩ := he'
    exact Or.inr ⟨e.trans e'⟩

theorem normal_embedding_cases (hSL2 : CFSG.IsQuasisimple ↥(StatedSL 2 K)) {Γ : Type} [Group Γ]
    [Finite Γ] {R X : Subgroup Γ} {Gc : Type} [Group Gc] (π : ↥R →* Gc)
    (hπ : Function.Surjective π)
    (hGc : CFSG.IsQuasisimple Gc ∨ Nonempty (Gc ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)))
    (hXR : X ≤ R) (hXn : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X)
    (hinj : ∀ x : ↥X, π ⟨(x : Γ), hXR x.2⟩ = 1 → x = 1) (hns : ¬ Group.IsSolvable ↥X) :
    (CFSG.IsQuasisimple Gc ∧ Nonempty (↥X ≃* Gc)) ∨ Nonempty (↥X ≃* ↥(StatedSL 2 K)) ∨
      Nonempty (↥X ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
  rcases subnormal_embedding_cases hSL2 π hπ hGc (le_refl X) hXR (fun h hh x hx => by
      simpa using X.mul_mem (X.mul_mem hh hx) (X.inv_mem hh)) hXn hinj hns with
    ⟨-, h | h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

end Embedding

theorem isSLModel_conjSubgroup {Γ : Type} [Group Γ] {q : ℕ} {C : Subgroup Γ}
    (h : IsSLModel 2 q ↥C) (g : Γ) : IsSLModel 2 q ↥(conjSubgroup g C) := by
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := h
  exact ⟨K, hF, hFin, hK, ⟨(Subgroup.equivMapOfInjective C (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩⟩

section Uniqueness

variable {Γ : Type} [Group Γ] [Finite Γ] {q : ℕ}

theorem not_sl2_of_normal_of_unique (hq2 : ∃ k : ℕ, q = 2 ^ k)
    (hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q → CFSG.IsQuasisimple ↥(StatedSL 2 K))
    {Y : Subgroup Γ} (hYu : ∀ C : Subgroup Γ, IsComponent C → IsSLModel 2 q ↥C → C = Y)
    (hY : Y ≠ ⊥) {X : Subgroup Γ} (hXn : X.Normal) (hXY : X ⊓ Y = ⊥) :
    ¬ IsSLModel 2 q ↥X ∧
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
        ¬ Nonempty (↥X ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
  have hnt : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a := fun K _ _ hK => by
    by_contra h
    push Not at h
    exact not_isSolvable_of_isQuasisimple (hSL2 K hK) (isSolvable_of_comm fun a b => h a b)
  constructor
  · rintro ⟨K, hF, hFin, hK, ⟨e⟩⟩
    have hq : CFSG.IsQuasisimple ↥X := isQuasisimple_of_mulEquiv' e.symm (hSL2 K hK)
    have hC : IsComponent X := ⟨hq, hXn.isSubnormal⟩
    have hXe : X = Y := hYu X hC ⟨K, hF, hFin, hK, ⟨e⟩⟩
    apply hY
    rw [← hXY, hXe, inf_idem]
  · intro K hF hFin hK hne
    obtain ⟨e⟩ := hne
    obtain ⟨k, hk⟩ := hq2
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hk)
    have hA := hnt K hK
    let F₁ : Subgroup ↥X := (⊤ : Subgroup ↥(StatedSL 2 K)).prod (⊥ : Subgroup ↥(StatedSL 2 K))
      |>.comap e.toMonoidHom
    let F₂ : Subgroup ↥X := (⊥ : Subgroup ↥(StatedSL 2 K)).prod (⊤ : Subgroup ↥(StatedSL 2 K))
      |>.comap e.toMonoidHom
    haveI hF₁n : F₁.Normal := Subgroup.Normal.comap (by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_prod.mp hn
      refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩
      have : (g * n * g⁻¹ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)).2 = 1 := by
        have h2 : n.2 = 1 := Subgroup.mem_bot.mp hn2
        simp [h2]
      exact Subgroup.mem_bot.mpr this) e.toMonoidHom
    haveI hF₂n : F₂.Normal := Subgroup.Normal.comap (by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_prod.mp hn
      refine Subgroup.mem_prod.mpr ⟨?_, Subgroup.mem_top _⟩
      have : (g * n * g⁻¹ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)).1 = 1 := by
        have h1 : n.1 = 1 := Subgroup.mem_bot.mp hn1
        simp [h1]
      exact Subgroup.mem_bot.mpr this) e.toMonoidHom
    obtain ⟨a, b, hab⟩ := hA
    have hF₁ne : F₁ ≠ ⊥ := by
      intro h
      have hmem : e.symm (a, (1 : ↥(StatedSL 2 K))) ∈ F₁ := by
        simp [F₁, Subgroup.mem_comap, Subgroup.mem_prod]
      rw [h, Subgroup.mem_bot] at hmem
      have : (a, (1 : ↥(StatedSL 2 K))) = 1 := by
        have := congrArg e hmem
        simpa using this
      have ha : a = 1 := congrArg Prod.fst this
      apply hab
      rw [ha]
      simp
    have hF₂ne : F₂ ≠ ⊥ := by
      intro h
      have hmem : e.symm ((1 : ↥(StatedSL 2 K)), a) ∈ F₂ := by
        simp [F₂, Subgroup.mem_comap, Subgroup.mem_prod]
      rw [h, Subgroup.mem_bot] at hmem
      have : ((1 : ↥(StatedSL 2 K)), a) = 1 := by
        have := congrArg e hmem
        simpa using this
      have ha : a = 1 := congrArg Prod.snd this
      apply hab
      rw [ha]
      simp
    have hcomm : ∀ x ∈ F₁, ∀ y ∈ F₂, x * y = y * x := by
      intro x hx y hy
      apply e.injective
      rw [map_mul, map_mul]
      obtain ⟨-, hx2⟩ := Subgroup.mem_prod.mp hx
      obtain ⟨hy1, -⟩ := Subgroup.mem_prod.mp hy
      have hx2' : (e x).2 = 1 := Subgroup.mem_bot.mp hx2
      have hy1' : (e y).1 = 1 := Subgroup.mem_bot.mp hy1
      apply Prod.ext <;> simp [hx2', hy1']
    obtain ⟨⟨s₁⟩, -⟩ := sl2_of_commuting_normal_prod (hSL2 K hK) e hF₁ne hF₂ne hcomm
    let A : Subgroup Γ := F₁.map X.subtype
    have hAX : A ≤ X := Subgroup.map_subtype_le _
    have hAF : A.subgroupOf X = F₁ := Subgroup.comap_map_eq_self_of_injective X.subtype_injective F₁
    have hAn : (A.subgroupOf X).Normal := by rw [hAF]; exact hF₁n
    let eA : ↥F₁ ≃* ↥A := Subgroup.equivMapOfInjective F₁ X.subtype X.subtype_injective
    have hqA : CFSG.IsQuasisimple ↥A :=
      isQuasisimple_of_mulEquiv' (eA.symm.trans s₁).symm (hSL2 K hK)
    have hCA : IsComponent A :=
      ⟨hqA, Subgroup.IsSubnormal.trans hAX hAn.isSubnormal hXn.isSubnormal⟩
    have hAY : A = Y := hYu A hCA ⟨K, hF, hFin, hK, ⟨eA.symm.trans s₁⟩⟩
    apply hY
    have : Y ≤ X ⊓ Y := le_inf (hAY ▸ hAX) le_rfl
    rw [hXY] at this
    exact le_bot_iff.mp this

end Uniqueness


section TwoFactors

variable {K : Type} [Field K] [Finite K] [CharP K 2] {Γ : Type} [Group Γ]

theorem exists_two_factors (hSL2 : CFSG.IsQuasisimple ↥(StatedSL 2 K)) {X : Subgroup Γ}
    (e : ↥X ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) :
    ∃ Z₁ Z₂ : Subgroup Γ, Z₁ ≤ X ∧ Z₂ ≤ X ∧ (Z₁.subgroupOf X).Normal ∧
      (Z₂.subgroupOf X).Normal ∧ Z₁ ⊔ Z₂ = X ∧ Z₁ ⊓ Z₂ = ⊥ ∧
      (∀ x ∈ Z₁, ∀ y ∈ Z₂, x * y = y * x) ∧ Nonempty (↥Z₁ ≃* ↥(StatedSL 2 K)) ∧
      Nonempty (↥Z₂ ≃* ↥(StatedSL 2 K)) := by
  have hnt : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact not_isSolvable_of_isQuasisimple hSL2 (isSolvable_of_comm fun a b => h a b)
  let F₁ : Subgroup ↥X := (⊤ : Subgroup ↥(StatedSL 2 K)).prod (⊥ : Subgroup ↥(StatedSL 2 K))
    |>.comap e.toMonoidHom
  let F₂ : Subgroup ↥X := (⊥ : Subgroup ↥(StatedSL 2 K)).prod (⊤ : Subgroup ↥(StatedSL 2 K))
    |>.comap e.toMonoidHom
  have hF₁n : F₁.Normal := Subgroup.Normal.comap (by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_prod.mp hn
    refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩
    have : (g * n * g⁻¹ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)).2 = 1 := by
      have h2 : n.2 = 1 := Subgroup.mem_bot.mp hn2
      simp [h2]
    exact Subgroup.mem_bot.mpr this) e.toMonoidHom
  have hF₂n : F₂.Normal := Subgroup.Normal.comap (by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_prod.mp hn
    refine Subgroup.mem_prod.mpr ⟨?_, Subgroup.mem_top _⟩
    have : (g * n * g⁻¹ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)).1 = 1 := by
      have h1 : n.1 = 1 := Subgroup.mem_bot.mp hn1
      simp [h1]
    exact Subgroup.mem_bot.mpr this) e.toMonoidHom
  obtain ⟨a, b, hab⟩ := hnt
  have hF₁ne : F₁ ≠ ⊥ := by
    intro h
    have hmem : e.symm (a, (1 : ↥(StatedSL 2 K))) ∈ F₁ := by
      simp [F₁, Subgroup.mem_comap, Subgroup.mem_prod]
    rw [h, Subgroup.mem_bot] at hmem
    have : (a, (1 : ↥(StatedSL 2 K))) = 1 := by
      have := congrArg e hmem
      simpa using this
    have ha : a = 1 := congrArg Prod.fst this
    apply hab
    rw [ha]
    simp
  have hF₂ne : F₂ ≠ ⊥ := by
    intro h
    have hmem : e.symm ((1 : ↥(StatedSL 2 K)), a) ∈ F₂ := by
      simp [F₂, Subgroup.mem_comap, Subgroup.mem_prod]
    rw [h, Subgroup.mem_bot] at hmem
    have : ((1 : ↥(StatedSL 2 K)), a) = 1 := by
      have := congrArg e hmem
      simpa using this
    have ha : a = 1 := congrArg Prod.snd this
    apply hab
    rw [ha]
    simp
  have hcomm : ∀ x ∈ F₁, ∀ y ∈ F₂, x * y = y * x := by
    intro x hx y hy
    apply e.injective
    rw [map_mul, map_mul]
    obtain ⟨-, hx2⟩ := Subgroup.mem_prod.mp hx
    obtain ⟨hy1, -⟩ := Subgroup.mem_prod.mp hy
    have hx2' : (e x).2 = 1 := Subgroup.mem_bot.mp hx2
    have hy1' : (e y).1 = 1 := Subgroup.mem_bot.mp hy1
    apply Prod.ext <;> simp [hx2', hy1']
  haveI := hF₁n
  haveI := hF₂n
  obtain ⟨⟨s₁⟩, ⟨s₂⟩⟩ := sl2_of_commuting_normal_prod hSL2 e hF₁ne hF₂ne hcomm
  have hsup : F₁ ⊔ F₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · simp [F₁, Subgroup.mem_comap, Subgroup.mem_prod]
    · simp [F₂, Subgroup.mem_comap, Subgroup.mem_prod]
  have hinf : F₁ ⊓ F₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨-, h1⟩ := Subgroup.mem_prod.mp hx1
    obtain ⟨h2, -⟩ := Subgroup.mem_prod.mp hx2
    have h1' : (e x).2 = 1 := Subgroup.mem_bot.mp h1
    have h2' : (e x).1 = 1 := Subgroup.mem_bot.mp h2
    have : e x = 1 := Prod.ext h2' h1'
    exact Subgroup.mem_bot.mpr (e.injective (by rw [this, map_one]))
  refine ⟨F₁.map X.subtype, F₂.map X.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ⟨?_⟩, ⟨?_⟩⟩
  · rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective F₁ |> fun h =>
      show (F₁.map X.subtype).subgroupOf X = F₁ from h]
    exact hF₁n
  · rw [show (F₂.map X.subtype).subgroupOf X = F₂ from
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective F₂]
    exact hF₂n
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩
    have : v = u := Subtype.ext huv
    rw [this] at hv
    have : u ∈ F₁ ⊓ F₂ := ⟨hu, hv⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.mem_bot.mpr rfl
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hcomm u hu v hv)
  · exact (Subgroup.equivMapOfInjective F₁ X.subtype X.subtype_injective).symm.trans s₁
  · exact (Subgroup.equivMapOfInjective F₂ X.subtype X.subtype_injective).symm.trans s₂

theorem not_isSimpleGroup_of_prod (hSL2 : CFSG.IsQuasisimple ↥(StatedSL 2 K)) {X : Subgroup Γ}
    [IsSimpleGroup ↥X] (e : ↥X ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) : False := by
  obtain ⟨Z₁, Z₂, hZ₁X, hZ₂X, hZ₁n, hZ₂n, hsup, hinf, hcomm, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    exists_two_factors hSL2 e
  have hnt : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact not_isSolvable_of_isQuasisimple hSL2 (isSolvable_of_comm fun a b => h a b)
  have hne : ∀ Z : Subgroup Γ, (↥Z ≃* ↥(StatedSL 2 K)) → Z ≠ ⊥ := by
    intro Z f hZ
    obtain ⟨a, b, hab⟩ := hnt
    apply hab
    have h1 : ∀ x : ↥Z, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hZ ▸ x.2))
    have hfa : f.symm a = f.symm 1 := (h1 _).trans (h1 _).symm
    have ha : a = 1 := f.symm.injective hfa
    rw [ha]
    simp
  rcases hZ₁n.eq_bot_or_eq_top with hb | ht
  · apply hne Z₁ e₁
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hZ₁X hz⟩ : ↥X) ∈ Z₁.subgroupOf X := hz
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · apply hne Z₂ e₂
    rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ Z₁ := by
      have : (⟨z, hZ₂X hz⟩ : ↥X) ∈ Z₁.subgroupOf X := by rw [ht]; exact Subgroup.mem_top _
      exact this
    have : z ∈ Z₁ ⊓ Z₂ := ⟨hz1, hz⟩
    rwa [hinf] at this

end TwoFactors



theorem exists_ne_one_inf_of_card {Γ : Type*} [Group Γ] [Finite Γ] {Λ N D A : Subgroup Γ}
    (hNΛ : N ≤ Λ) (hindex : Nat.card Λ = 2 * Nat.card N) (hDN : D ≤ N) (hAΛ : A ≤ Λ)
    (hcover : ∀ l ∈ Λ, ∃ d ∈ D, ∃ a ∈ A, l = d * a)
    (hne : Nat.card Λ ≠ 2 * Nat.card D) : ∃ c ∈ A ⊓ N, c ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hsub : Nat.card (N.subgroupOf Λ) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNΛ).toEquiv
  have hidx : (N.subgroupOf Λ).index = 2 := by
    have h2 := Subgroup.card_mul_index (N.subgroupOf Λ)
    rw [hsub, hindex] at h2
    exact Nat.eq_of_mul_eq_mul_left hNpos (by omega)
  have hinj : Function.Injective (fun a : A =>
      ((⟨a.1, hAΛ a.2⟩ : Λ) : ↥Λ ⧸ N.subgroupOf Λ)) := by
    intro a b hab
    have hab' := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_subgroupOf] at hab'
    have hmemA : (a : Γ)⁻¹ * (b : Γ) ∈ A := A.mul_mem (A.inv_mem a.2) b.2
    have hmemN : (a : Γ)⁻¹ * (b : Γ) ∈ N := hab'
    have h1 : (a : Γ)⁻¹ * (b : Γ) = 1 := hcon _ (Subgroup.mem_inf.mpr ⟨hmemA, hmemN⟩)
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hA2 : Nat.card A ≤ (N.subgroupOf Λ).index := Nat.card_le_card_of_injective _ hinj
  rw [hidx] at hA2
  have hcov : Nat.card Λ ≤ Nat.card D * Nat.card A := by
    have hsurj : Function.Surjective (fun p : ↥D × ↥A =>
        (⟨(p.1 : Γ) * (p.2 : Γ), Λ.mul_mem ((hDN.trans hNΛ) p.1.2) (hAΛ p.2.2)⟩ : ↥Λ)) := by
      intro l
      obtain ⟨d, hd, a, ha, hl⟩ := hcover l.1 l.2
      exact ⟨(⟨d, hd⟩, ⟨a, ha⟩), Subtype.ext hl.symm⟩
    have h := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod] at h
    exact h
  have hA' : Nat.card D * Nat.card A ≤ Nat.card D * 2 := Nat.mul_le_mul (le_refl _) hA2
  have hDle : Nat.card D ≤ Nat.card N := Subgroup.card_le_of_le hDN
  omega

theorem card_le_card_sylow {H : Type*} [Group H] [Finite H] {T : Subgroup H}
    (hT : IsPGroup 2 ↥T) (P : Sylow 2 H) : Nat.card T ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT.exists_le_sylow
  have h1 : Nat.card T ≤ Nat.card Q := Subgroup.card_le_of_le hQ
  have h2 : Nat.card Q = Nat.card P := by
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]
  exact h1.trans h2.le

theorem card_sylow_eq_of_mulEquiv {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']
    (e : H ≃* H') (P : Sylow 2 H) (P' : Sylow 2 H') : Nat.card P = Nat.card P' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card H = Nat.card H' := Nat.card_congr e.toEquiv
  rw [Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity P', hcard]

end CFSG.RankThree.GF2n.Stroth80
