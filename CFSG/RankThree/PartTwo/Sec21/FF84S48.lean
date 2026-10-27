module

public import CFSG.RankThree.PartTwo.Sec21.FF84S48Core
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBasic
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

@[expose] def S47Facts (b : G) (B : Subgroup G) (b₁ b₂ : G) : Prop :=
  ∃ U₁ U₂ : Subgroup G, U₁ ≠ U₂ ∧ PiStar (Cen b) B 2 = {U₁, U₂} ∧ U₁ ⊓ U₂ = ⊥ ∧
    ∀ U ∈ PiStar (Cen b) B 2, IsElemAb 2 4 U ∧ IsElemAb 2 2 (U ⊓ Cen b₁) ∧
      IsElemAb 2 2 (U ⊓ Cen b₂) ∧ U ⊓ Cen (b₁ * b₂) = ⊥ ∧ U ⊓ Cen (b₁ * b₂ ^ 2) = ⊥ ∧
      U ∈ PiStar (Cen b) (Subgroup.zpowers b₁) 2 ∧ U ∈ PiStar (Cen b) (Subgroup.zpowers b₂) 2

structure S48Ctx (b : G) (L B K : Subgroup G) (b₁ b₂ : G) : Prop where
  post : FF84Post b L B K b₁ b₂
  f47 : S47Facts b B b₁ b₂
  hD : Cen (b * b₁) ≤ Nor (Subgroup.closure ({b, b₁} : Set G))

theorem conj_inv_of {n x y : G} (h : n * x * n⁻¹ = y) : n⁻¹ * y * n = x := by
  rw [← h]; group

theorem conj_comp {n m x y z : G} (h1 : m * x * m⁻¹ = y) (h2 : n * y * n⁻¹ = z) :
    (n * m) * x * (n * m)⁻¹ = z := by
  rw [← h2, ← h1]; group

theorem conj_inv_elt {n x : G} : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂)

include c

theorem sec : FF84Sec4 b L B K b₁ b₂ := c.post.sec

theorem hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
  (comm_of_mem c.post.sec hx hy).eq

theorem hB3 : ∀ x ∈ B, x ^ 3 = 1 := fun x hx => pow3_of_mem c.post.sec hx

theorem ord_b : orderOf b = 3 := c.sec.hyp.ord

theorem ord_b₁ : orderOf b₁ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (c.hB3 _ (mem_b₁ c.sec)) (b₁_ne_one c.sec)

theorem ord_b₂ : orderOf b₂ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (c.hB3 _ (mem_b₂ c.sec)) (b₂_ne_one c.sec)

theorem piU {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) :
    IsElemAb 2 4 U ∧ IsElemAb 2 2 (U ⊓ Cen b₁) ∧ IsElemAb 2 2 (U ⊓ Cen b₂) ∧
      U ⊓ Cen (b₁ * b₂) = ⊥ := by
  obtain ⟨U₁, U₂, -, -, -, h⟩ := c.f47
  obtain ⟨h1, h2, h3, h4, -⟩ := h U hU
  exact ⟨h1, h2, h3, h4⟩

theorem piU_card {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) : Nat.card U = 16 := by
  rw [(c.piU hU).1.2]; norm_num

theorem piTwo : ∃ U₁ U₂ : Subgroup G, U₁ ≠ U₂ ∧ PiStar (Cen b) B 2 = {U₁, U₂} := by
  obtain ⟨U₁, U₂, h12, hP, -⟩ := c.f47
  exact ⟨U₁, U₂, h12, hP⟩

theorem hPi : ∀ Y : Subgroup G, Y ≤ Cen b → IsPGroup 2 Y → B ≤ Nor Y →
    EA2 Y ∧ Nat.card Y ≤ 16 := by
  intro Y hY1 hY2 hY3
  obtain ⟨Z, hZ, hYZ⟩ := exists_piStar_ge hY1 hY2 hY3
  have hZ4 := (c.piU hZ).1
  refine ⟨(EA2.of_isElemAb hZ4).mono hYZ, ?_⟩
  calc Nat.card Y ≤ Nat.card Z := Subgroup.card_le_of_le hYZ
    _ = 16 := c.piU_card hZ

theorem flip₁ : ∃ m ∈ Nor B, m * b * m⁻¹ = b ∧ m * b₁ * m⁻¹ = b₁⁻¹ ∧ m * b₂ * m⁻¹ = b₂ := by
  obtain ⟨-, -, -, ⟨ι, hι, hι1, hι2, hι3⟩, ⟨n, hn, hn1, hn2, hn3⟩, -⟩ := c.sec.mono
  refine ⟨n * ι * n⁻¹, mul_mem (mul_mem hn hι) (inv_mem hn), ?_, ?_, ?_⟩
  · have a1 : n⁻¹ * b * n = b₁ := conj_inv_of hn2
    have e : n * ι * n⁻¹ * b * (n * ι * n⁻¹)⁻¹ = n * (ι * (n⁻¹ * b * n) * ι⁻¹) * n⁻¹ := by group
    rw [e, a1, hι2, hn2]
  · have a1 : n⁻¹ * b₁ * n = b := conj_inv_of hn1
    have e : n * ι * n⁻¹ * b₁ * (n * ι * n⁻¹)⁻¹ = n * (ι * (n⁻¹ * b₁ * n) * ι⁻¹) * n⁻¹ := by group
    rw [e, a1, hι1, conj_inv_elt, hn1]
  · have a1 : n⁻¹ * b₂ * n = b₂ := conj_inv_of hn3
    have e : n * ι * n⁻¹ * b₂ * (n * ι * n⁻¹)⁻¹ = n * (ι * (n⁻¹ * b₂ * n) * ι⁻¹) * n⁻¹ := by group
    rw [e, a1, hι3, hn3]

theorem swap₂₃ : ∃ m ∈ Nor B, m * b * m⁻¹ = b ∧ m * b₁ * m⁻¹ = b₂ ∧ m * b₂ * m⁻¹ = b₁ := by
  obtain ⟨-, -, -, -, ⟨n, hn, hn1, hn2, hn3⟩, ⟨t, ht, ht1, ht2, ht3⟩⟩ := c.sec.mono
  refine ⟨t * n * t⁻¹, mul_mem (mul_mem ht hn) (inv_mem ht), ?_, ?_, ?_⟩
  · have a1 : t⁻¹ * b * t = b₂ := conj_inv_of ht3
    have e : t * n * t⁻¹ * b * (t * n * t⁻¹)⁻¹ = t * (n * (t⁻¹ * b * t) * n⁻¹) * t⁻¹ := by group
    rw [e, a1, hn3, ht3]
  · have a1 : t⁻¹ * b₁ * t = b := conj_inv_of ht1
    have e : t * n * t⁻¹ * b₁ * (t * n * t⁻¹)⁻¹ = t * (n * (t⁻¹ * b₁ * t) * n⁻¹) * t⁻¹ := by group
    rw [e, a1, hn1, ht2]
  · have a1 : t⁻¹ * b₂ * t = b₁ := conj_inv_of ht2
    have e : t * n * t⁻¹ * b₂ * (t * n * t⁻¹)⁻¹ = t * (n * (t⁻¹ * b₂ * t) * n⁻¹) * t⁻¹ := by group
    rw [e, a1, hn2, ht1]

theorem hD_b₁inv : Cen (b * b₁⁻¹) ≤ Nor (Subgroup.closure ({b, b₁⁻¹} : Set G)) := by
  obtain ⟨m, -, h1, h2, -⟩ := c.flip₁
  have := hD_conj (m := m) c.hD
  rwa [h1, h2] at this

theorem hD_b₂ : Cen (b * b₂) ≤ Nor (Subgroup.closure ({b, b₂} : Set G)) := by
  obtain ⟨m, -, h1, h2, -⟩ := c.swap₂₃
  have := hD_conj (m := m) c.hD
  rwa [h1, h2] at this

theorem hD_b₂inv : Cen (b * b₂⁻¹) ≤ Nor (Subgroup.closure ({b, b₂⁻¹} : Set G)) := by
  obtain ⟨m, -, h1, h2, -⟩ := c.flip₁
  obtain ⟨m', -, h1', h2', -⟩ := c.swap₂₃
  have hb : (m' * m) * b * (m' * m)⁻¹ = b := conj_comp h1 h1'
  have hb₁ : (m' * m) * b₁ * (m' * m)⁻¹ = b₂⁻¹ := by
    refine conj_comp h2 ?_
    rw [conj_inv_elt, h2']
  have := hD_conj (m := m' * m) c.hD
  rwa [hb, hb₁] at this

theorem notin_zpowers {cc : G} (hcc : cc = b₁ ∨ cc = b₂) : cc ∉ Subgroup.zpowers b := by
  rcases hcc with rfl | rfl
  · exact b₁_notin_zpowers_b c.sec
  · exact b₂_notin_zpowers_b c.sec

theorem memB {cc : G} (hcc : cc = b₁ ∨ cc = b₂) : cc ∈ B := by
  rcases hcc with rfl | rfl
  · exact mem_b₁ c.sec
  · exact mem_b₂ c.sec

theorem ord_cc {cc : G} (hcc : cc = b₁ ∨ cc = b₂) : orderOf cc = 3 := by
  rcases hcc with rfl | rfl
  · exact c.ord_b₁
  · exact c.ord_b₂

theorem core_ex {U X : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) (hX : IsPGroup 2 X)
    (hBX : B ≤ Nor X) (hXb : X ⊓ Cen b = U) {cc : G} (hcc : cc = b₁ ∨ cc = b₂) :
    ∃ n, CoreData b cc n B X U := by
  have hD1 : Cen (b * cc) ≤ Nor (Subgroup.closure ({b, cc} : Set G)) := by
    rcases hcc with rfl | rfl
    · exact c.hD
    · exact c.hD_b₂
  have hD2 : Cen (b * cc⁻¹) ≤ Nor (Subgroup.closure ({b, cc⁻¹} : Set G)) := by
    rcases hcc with rfl | rfl
    · exact c.hD_b₁inv
    · exact c.hD_b₂inv
  have hn : ∃ n ∈ Nor B, n * cc * n⁻¹ = b := by
    obtain ⟨-, -, -, -, ⟨n, hn, hn1, hn2, hn3⟩, ⟨t, ht, ht1, ht2, ht3⟩⟩ := c.sec.mono
    rcases hcc with rfl | rfl
    · exact ⟨n, hn, hn2⟩
    · exact ⟨t, ht, ht3⟩
  obtain ⟨n, hnB, hnc⟩ := hn
  have h4 : Nat.card ↥(U ⊓ Cen cc) = 4 := by
    have h := (c.piU hU)
    rcases hcc with rfl | rfl
    · rw [h.2.1.2]; norm_num
    · rw [h.2.2.1.2]; norm_num
  exact ⟨n, ⟨c.hBcomm, c.hB3, mem_b c.sec, c.memB hcc, c.ord_b, c.ord_cc hcc,
    c.notin_zpowers hcc, hX, hBX, hXb, EA2.of_isElemAb (c.piU hU).1, hD1, hD2, hnB, hnc,
    c.hPi, c.piU_card hU, h4⟩⟩

end S48Ctx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
