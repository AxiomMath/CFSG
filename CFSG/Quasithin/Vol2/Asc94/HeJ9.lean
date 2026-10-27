module

public import CFSG.Quasithin.Vol2.Asc94.HeJ8

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def gl2T (h : GL2) : GL2 :=
  ⟨(h.val)ᵀ, ((h⁻¹ : GL2).val)ᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem card_orbit_pair {L : Subgroup G} {s : G} {O : Set G}
    (hO : {y : G | ∃ l ∈ L, y = l⁻¹ * s * l} = O) :
    O.ncard * Nat.card ↥(L ⊓ centralizer ({s} : Set G)) = Nat.card L := by
  have h := CFSG.Quasithin.A94.Gen.card_conjOrbit_mul_card_stab L s
  rw [← hO, ← Nat.card_coe_set_eq]
  exact h

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

include hD

theorem Data40.a_ne_one : a ≠ 1 := by
  rintro rfl
  have := hD.hT.m_one
  rw [hD.ham] at this
  exact one_ne_zero this

theorem Data40.a_mul_a : a * a = 1 := hD.hK.Asq a hD.ha.1

section X

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

include hxN hxa hx3

theorem Data40.exists_b : ∃ b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G),
    m b = ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  obtain ⟨b, hbZ, hbm⟩ := hD.hT.msurj g.val
  exact ⟨b, (hD.mem_B_iff hxN hxa hx3).2 ⟨hbZ, by rw [hbm]⟩, hbm⟩

theorem Data40.exists_d {b : G} (hbZ : b ∈ A ⊓ A')
    (hbm : m b = ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val) :
    ∃ d ∈ N ⊓ centralizer ({a} : Set G),
      m (d * b * d⁻¹) = (((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2)⁻¹ : GL2).val := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  obtain ⟨h, hh⟩ := gl2_exists_inverting g (hD.g_pow_three hxN hxa hx3)
  obtain ⟨d, hd⟩ := hD.hT.rho_surjective hD.hK (h, gl2T h⁻¹)
  have hdN : (d : G) ∈ N := d.2
  have hd1 : ((hD.hT.rho N hD.hK.norm d).1 : GL2).val = h.val := by rw [hd]
  have hd2 : ((hD.hT.rho N hD.hK.norm d).2 : GL2).val = (h⁻¹.val)ᵀ := by rw [hd]; rfl
  have hdm : m ((d : G) * a * (d : G)⁻¹) = 1 := by
    rw [hD.hT.m_conj N hD.hK.norm d hD.ha, hD.ham, hd1, hd2, Matrix.transpose_transpose, mul_one]
    exact Units.mul_inv h
  have hda : (d : G) ∈ centralizer ({a} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (d : G) * a * (d : G)⁻¹ = a :=
      hD.hT.minj _ (hD.mem_Z_conj hdN hD.ha) _ hD.ha (by rw [hdm, hD.ham])
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  refine ⟨d, ⟨hdN, hda⟩, ?_⟩
  rw [hD.hT.m_conj N hD.hK.norm d hbZ, hbm, hd1, hd2, Matrix.transpose_transpose]
  have : (h * g * h⁻¹ : GL2).val = (g⁻¹ : GL2).val := by rw [hh]
  rw [← this]
  simp

theorem Data40.B_elems {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G))
    (hb1 : b ≠ 1) (hba : b ≠ a) :
    ∀ y ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G), y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  set B : Subgroup G := (A ⊓ A') ⊓ centralizer ({x} : Set G) with hB
  have hcard : (B : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hD.card_B hxN hxa hx3
  have haB : a ∈ B := hD.a_mem_B hxN hxa hx3
  have hab : a * b ∈ B := B.mul_mem haB hb
  have ha1 := hD.a_ne_one
  have haa := hD.a_mul_a
  have h1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨ha1.symm, hb1.symm, fun h => hba ?_⟩
    have : a * b = 1 := h.symm
    calc b = a * (a * b) := by rw [← mul_assoc, haa, one_mul]
      _ = a := by rw [this, mul_one]
  have h2 : a ∉ ({b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hba.symm, fun h => hb1 (mul_eq_left.1 h.symm)⟩
  have h3 : b ∉ ({a * b} : Set G) := by
    simp only [Set.mem_singleton_iff]
    intro h
    exact ha1 (mul_eq_right.1 h.symm)
  have hS : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hsub : ({1, a, b, a * b} : Set G) ⊆ (B : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [B.one_mem, haB, hb, hab]
  have hSB := Set.eq_of_subset_of_ncard_le hsub (by rw [hS, hcard])
  intro y hy
  have : y ∈ ({1, a, b, a * b} : Set G) := by rw [hSB]; exact hy
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem Data40.conj_b_mem {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G))
    (hb1 : b ≠ 1) (hba : b ≠ a) {l : G}
    (hl : l ∈ normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) :
    l⁻¹ * b * l = b ∨ l⁻¹ * b * l = a * b := by
  have hlB : l ∈ normalizer (((A ⊓ A') ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    hD.I_le_normalizer_B hxN hxa hx3 hl
  have hmem : l⁻¹ * b * l ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G) := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hlB) b).1 hb
    simpa using this
  have hla : l * a = a * l := mem_centralizer_singleton_iff.1 hl.2
  rcases hD.B_elems hxN hxa hx3 hb hb1 hba _ hmem with h | h | h | h
  · exfalso
    apply hb1
    have : b = l * (l⁻¹ * b * l) * l⁻¹ := by group
    rw [this, h]; group
  · exfalso
    apply hba
    have : b = l * (l⁻¹ * b * l) * l⁻¹ := by group
    rw [this, h, mul_inv_eq_iff_eq_mul]
    exact hla
  · exact Or.inl h
  · exact Or.inr h

theorem Data40.centralizer_B {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G))
    (hb1 : b ≠ 1) (hba : b ≠ a) :
    centralizer (((A ⊓ A') ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) =
      centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) := by
  have haB := hD.a_mem_B hxN hxa hx3
  ext m'
  constructor
  · intro hm
    rw [mem_centralizer_iff] at hm
    exact ⟨mem_centralizer_singleton_iff.2 (hm a haB).symm,
      mem_centralizer_singleton_iff.2 (hm b hb).symm⟩
  · rintro ⟨hma, hmb⟩
    have hma' : m' * a = a * m' := mem_centralizer_singleton_iff.1 hma
    have hmb' : m' * b = b * m' := mem_centralizer_singleton_iff.1 hmb
    rw [mem_centralizer_iff]
    intro y hy
    rcases hD.B_elems hxN hxa hx3 hb hb1 hba y hy with rfl | rfl | rfl | rfl
    · simp
    · exact hma'.symm
    · exact hmb'.symm
    · calc a * b * m' = a * (b * m') := by rw [mul_assoc]
        _ = a * (m' * b) := by rw [hmb']
        _ = (a * m') * b := by rw [mul_assoc]
        _ = (m' * a) * b := by rw [hma']
        _ = m' * (a * b) := by rw [mul_assoc]

variable {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G)) (hb1 : b ≠ 1) (hba : b ≠ a)
  {d : G} (hdD : d ∈ N ⊓ centralizer ({a} : Set G)) (hdb : d * b * d⁻¹ ≠ b)

include hb hb1 hba hdD hdb

theorem Data40.d_conj_b : d * b * d⁻¹ = a * b := by
  have hdI := hD.D_le_I hdD
  rcases hD.conj_b_mem hxN hxa hx3 hb hb1 hba (l := d⁻¹) (inv_mem hdI) with h | h
  · exfalso
    apply hdb
    simpa using h
  · simpa using h

theorem Data40.orbit_b_I :
    {y : G | ∃ l ∈ normalizer (A : Set G) ⊓ centralizer ({a} : Set G), y = l⁻¹ * b * l} =
      {b, a * b} := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hD.conj_b_mem hxN hxa hx3 hb hb1 hba hl with h | h
    · left; exact h
    · right; exact h
  · intro hy
    rcases hy with rfl | rfl
    · exact ⟨1, one_mem _, by simp⟩
    · exact ⟨d⁻¹, inv_mem (hD.D_le_I hdD), by
        rw [inv_inv]; exact (hD.d_conj_b hxN hxa hx3 hb hb1 hba hdD hdb).symm⟩

theorem Data40.orbit_b_D :
    {y : G | ∃ l ∈ N ⊓ centralizer ({a} : Set G), y = l⁻¹ * b * l} = {b, a * b} := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hD.conj_b_mem hxN hxa hx3 hb hb1 hba (hD.D_le_I hl) with h | h
    · left; exact h
    · right; exact h
  · intro hy
    rcases hy with rfl | rfl
    · exact ⟨1, one_mem _, by simp⟩
    · exact ⟨d⁻¹, inv_mem hdD, by
        rw [inv_inv]; exact (hD.d_conj_b hxN hxa hx3 hb hb1 hba hdD hdb).symm⟩

theorem Data40.card_L :
    Nat.card ↥((normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G)) =
      3840 := by
  have h := card_orbit_pair (hD.orbit_b_I hxN hxa hx3 hb hb1 hba hdD hdb)
  have hne : b ≠ a * b := fun h => hD.a_ne_one (mul_eq_right.1 h.symm)
  rw [Set.ncard_pair hne, hD.cardI] at h
  omega

theorem Data40.card_K :
    Nat.card ↥((N ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G)) = 768 := by
  have h := card_orbit_pair (hD.orbit_b_D hxN hxa hx3 hb hb1 hba hdD hdb)
  have hne : b ≠ a * b := fun h => hD.a_ne_one (mul_eq_right.1 h.symm)
  rw [Set.ncard_pair hne, hD.cardD] at h
  omega

end X

end D40

end CFSG.Quasithin.A94.HeJ
