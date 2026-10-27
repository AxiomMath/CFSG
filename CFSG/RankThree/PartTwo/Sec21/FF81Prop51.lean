module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF81Fusion
import CFSG.RankThree.PartTwo.Sec21.FF81S0

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_zpowers_of_pow {H : Type} [Group H] {z : H} {e : ℕ} (h : z ^ (3 ^ e) = 1) :
    IsPGroup 3 (Subgroup.zpowers z) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem commute_of_conj {x y : G} (h : x * y * x⁻¹ = y) : Commute x y :=
  mul_inv_eq_iff_eq_mul.mp h

theorem mem_normalizer_of_comm {B H : Subgroup G} (hcomm : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a)
    (hHB : H ≤ B) {g : G} (hg : g ∈ B) : g ∈ Subgroup.normalizer (H : Set G) := by
  have fw : ∀ g ∈ B, ∀ k ∈ H, g * k * g⁻¹ ∈ H := fun g hg k hk => by
    rw [show g * k * g⁻¹ = k by rw [hcomm g hg k (hHB hk)]; group]; exact hk
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fw g hg h, fun hh => ?_⟩
  have := fw g⁻¹ (B.inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem comm_of_isElemAb {p k : ℕ} {B : Subgroup G} (hB : IsElemAb p k B) :
    ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
  congrArg Subtype.val (hB.1.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : B) ⟨c, hc⟩)

theorem nor_le_normalizer_cenS (B : Subgroup G) :
    Nor B ≤ Subgroup.normalizer ((CenS B : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Nor B, ∀ h ∈ CenS B, g * h * g⁻¹ ∈ CenS B := by
    intro g hg h hh
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hz : g⁻¹ * y * g ∈ B := by
      rw [Subgroup.mem_normalizer_iff.mp hg]
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    have := Subgroup.mem_centralizer_iff.mp hh _ hz
    calc y * (g * h * g⁻¹) = g * ((g⁻¹ * y * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * h * g⁻¹ * y := by group
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

section Basis

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem FF81Basis.mem (hB : FF81Basis b L B b₁ b₂ b₃) :
    b ∈ B ∧ b₁ ∈ B ∧ b₂ ∈ B ∧ b₃ ∈ B := by
  have hBc := hB.mono.2.1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hBc] <;> exact Subgroup.subset_closure (by simp)

theorem FF81Basis.mem_cenS (hB : FF81Basis b L B b₁ b₂ b₃) {z : G} (h0 : z * b * z⁻¹ = b)
    (h1 : z * b₁ * z⁻¹ = b₁) (h2 : z * b₂ * z⁻¹ = b₂) (h3 : z * b₃ * z⁻¹ = b₃) : z ∈ CenS B := by
  have hle : B ≤ Subgroup.centralizer {z} := by
    rw [hB.mono.2.1]
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl | rfl
    · exact (commute_of_conj h0).eq.symm
    · exact (commute_of_conj h1).eq.symm
    · exact (commute_of_conj h2).eq.symm
    · exact (commute_of_conj h3).eq.symm
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem FF81Basis.mem_of_cube (hB : FF81Basis b L B b₁ b₂ b₃) {z : G} (hz : z ∈ CenS B)
    (h3 : z ^ 3 = 1) : z ∈ B :=
  hB.cenSyl z hz (isPGroup_zpowers_of_pow (e := 1) (by simpa using h3))

theorem eq_of_mem (hB : FF81Basis b L B b₁ b₂ b₃) {A : Subgroup G} (hA : IsElemAb 3 4 A)
    (hbA : b ∈ A) (hAN : A ≤ Nor B) : A = B := by
  have hB4 := hB.mono.1
  obtain ⟨-, hb1B, hb2B, hb3B⟩ := hB.mem
  have hcommA := comm_of_isElemAb hA
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => pow_three_eq_one_of_isElemAb hA ha
  have hfixb : ∀ a ∈ A, a * b * a⁻¹ = b := fun a ha => by
    rw [hcommA a ha b hbA]; group
  have hst : ∀ a ∈ A, ∀ y ∈ ({b₁, b₂, b₃} : Set G),
      a * y * a⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := fun a ha =>
    (hB.stab a (hAN ha) (by rw [conjBy_zpowers, hfixb a ha])).2
  have htriv : ∀ a ∈ A,
      (a * b₁ * a⁻¹ = b₁ ∧ a * b₂ * a⁻¹ = b₂ ∧ a * b₃ * a⁻¹ = b₃) → a ∈ B := fun a ha h =>
    hB.mem_of_cube (hB.mem_cenS (hfixb a ha) h.1 h.2.1 h.2.2) (hA3 a ha)
  obtain ⟨hE213, hE132, hE312⟩ := isElemAb_perm hB.elem
  have hE231 : IsElemAb 3 3 (Subgroup.closure ({b₂, b₃, b₁} : Set G)) := by
    have e : ({b₂, b₃, b₁} : Set G) = {b₁, b₂, b₃} := by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact e ▸ hB.elem
  have n12 := zpowers_ne hB.elem
  have n13 := zpowers_ne hE132
  have n23 := zpowers_ne hE231
  have key : ∀ z ∈ A, (conjBy z (Subgroup.zpowers b₁) = Subgroup.zpowers b₁ ∨
      conjBy z (Subgroup.zpowers b₂) = Subgroup.zpowers b₂ ∨
      conjBy z (Subgroup.zpowers b₃) = Subgroup.zpowers b₃) → z ∈ B := by
    intro z hz hfix
    rcases mono3 hB.elem (hA3 z hz) (hst z hz) with h | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
    · exact htriv z hz h
    all_goals
      exfalso
      rcases hfix with f | f | f <;> simp only [k1, k2, k3] at f <;>
      first
      | exact n12 f | exact n12 f.symm | exact n13 f | exact n13 f.symm
      | exact n23 f | exact n23 f.symm
  by_contra hne
  have hnle : ¬ A ≤ B := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hA.2, hB4.2]))
  obtain ⟨x, hxA, hxB⟩ := Set.not_subset.mp hnle
  have hx := mono3 hB.elem (hA3 x hxA) (hst x hxA)
  have hAB9 : Nat.card ↥(A ⊓ B) ≤ 9 := by
    have hle : A ⊓ B ≤ B ⊓ Cen x := fun y hy =>
      ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcommA y hy.1 x hxA)⟩
    refine (Subgroup.card_le_of_le hle).trans ?_
    rcases hx with h | ⟨k1, k2, -⟩ | ⟨k1, -, k3⟩
    · exact absurd (htriv x hxA h) hxB
    · exact card_inf_cen_le_nine hB4 hB.elem hb1B hb2B (hAN hxA) k1 k2
    · exact card_inf_cen_le_nine hB4 hE132 hb1B hb3B (hAN hxA) k1 k3
  have hcover : A ≤ Subgroup.zpowers x ⊔ (A ⊓ B) := by
    intro y hyA
    by_cases hyB : y ∈ B
    · exact Subgroup.mem_sup_right ⟨hyA, hyB⟩
    have hy := mono3 hB.elem (hA3 y hyA) (hst y hyA)
    have hxy := A.mul_mem hxA hyA
    have hxy' := A.mul_mem hxA (A.inv_mem hyA)
    have L1 : x * y ∈ B → y ∈ Subgroup.zpowers x ⊔ (A ⊓ B) := fun h => by
      rw [show y = x⁻¹ * (x * y) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)))
        (Subgroup.mem_sup_right ⟨hxy, h⟩)
    have L2 : x * y⁻¹ ∈ B → y ∈ Subgroup.zpowers x ⊔ (A ⊓ B) := fun h => by
      rw [show y = (x * y⁻¹)⁻¹ * x by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨A.inv_mem hxy', B.inv_mem h⟩)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    rcases hx with h | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
    · exact absurd (htriv x hxA h) hxB
    all_goals rcases hy with h | ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩
    · exact absurd (htriv y hyA h) hyB
    · exact L2 (key _ hxy' (Or.inr (Or.inl (by
        rw [conjBy_mul, show conjBy y⁻¹ (Subgroup.zpowers b₂) = Subgroup.zpowers b₁ by
          rw [← y1, conjBy_inv_conjBy], x1]))))
    · exact L1 (key _ hxy (Or.inl (by rw [conjBy_mul, y1, x3])))
    · exact absurd (htriv y hyA h) hyB
    · exact L1 (key _ hxy (Or.inl (by rw [conjBy_mul, y1, x2])))
    · exact L2 (key _ hxy' (Or.inr (Or.inr (by
        rw [conjBy_mul, show conjBy y⁻¹ (Subgroup.zpowers b₃) = Subgroup.zpowers b₁ by
          rw [← y1, conjBy_inv_conjBy], x1]))))
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    have hA' := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxA) h
    have hB' := Subgroup.mem_normalizer_iff.mp (hAN hxA) h
    simp only [Subgroup.mem_inf]
    exact ⟨fun hh => ⟨hA'.mp hh.1, hB'.mp hh.2⟩, fun hh => ⟨hA'.mpr hh.1, hB'.mpr hh.2⟩⟩
  have hx3 : Nat.card (Subgroup.zpowers x) ≤ 3 := by
    rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one (by norm_num) (hA3 x hxA)
  have := (Subgroup.card_le_of_le hcover).trans (card_sup_le_mul _ _ hxN)
  rw [hA.2] at this
  nlinarith

theorem not_mem_of_ne (hB : FF81Basis b L B b₁ b₂ b₃) {A : Subgroup G} (hA : IsElemAb 3 4 A)
    (hAN : A ≤ Nor B) (hne : A ≠ B) {n : G} (hn : n ∈ Nor B) : n * b * n⁻¹ ∉ A := by
  intro h
  apply hne
  have hbA' : b ∈ conjBy n⁻¹ A :=
    ⟨n * b * n⁻¹, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hA'N : conjBy n⁻¹ A ≤ Nor B := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) (hAN ha)) (by simpa using hn)
  have h1 := eq_of_mem hB (isElemAb_conjBy hA n⁻¹) hbA' hA'N
  calc A = conjBy n (conjBy n⁻¹ A) := (conjBy_conjBy_inv n A).symm
    _ = conjBy n B := by rw [h1]
    _ = B := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn

end Basis

theorem idx3 {B H : Subgroup G} (hB : IsElemAb 3 4 B) (hHB : H ≤ B) (hH : Nat.card H = 27)
    {x y : G} (hxB : x ∈ B) (hyB : y ∈ B) (hx : x ∉ H) (hy : y ∉ H) :
    x * y ∈ H ∨ x * y⁻¹ ∈ H := by
  have hcomm := comm_of_isElemAb hB
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_comm hcomm hHB hxB)
  have hxN' : x ∈ Subgroup.normalizer (H : Set G) := mem_normalizer_of_comm hcomm hHB hxB
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x) H hxN
  have hKB : Subgroup.zpowers x ⊔ H ≤ B := sup_le (Subgroup.zpowers_le.mpr hxB) hHB
  have hHK : H ≤ Subgroup.zpowers x ⊔ H := le_sup_right
  have hxK : x ∈ Subgroup.zpowers x ⊔ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hd := Subgroup.card_dvd_of_le hKB
  rw [hB.2] at hd
  have hd27 := Subgroup.card_dvd_of_le hHK
  rw [hH] at hd27
  have hne : Nat.card ↥(Subgroup.zpowers x ⊔ H) ≠ 27 := fun h => by
    have := Subgroup.eq_of_le_of_card_ge hHK (by rw [h, hH])
    apply hx; rw [this]; exact hxK
  have hK81 : Nat.card ↥(Subgroup.zpowers x ⊔ H) = 81 := by
    obtain ⟨m, hm, e⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    rw [e] at hd27 hne ⊢
    interval_cases m <;> simp_all <;> omega
  have hKeq : Subgroup.zpowers x ⊔ H = B :=
    Subgroup.eq_of_le_of_card_ge hKB (by rw [hK81, hB.2]; norm_num)
  have hyK : y ∈ ((Subgroup.zpowers x ⊔ H : Subgroup G) : Set G) := by rw [hKeq]; exact hyB
  rw [hset] at hyK
  obtain ⟨a, ha, h, hh, rfl⟩ := Set.mem_mul.mp hyK
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hx3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast pow_three_eq_one_of_isElemAb hB hxB
  rw [zpow_eq_zpow_emod k hx3] at hy ⊢
  obtain hk | hk | hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [hk, zpow_zero, one_mul] at hy; exact absurd hh hy
  · right
    rw [hk, zpow_one, show x * (x * h)⁻¹ = x * h⁻¹ * x⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp hxN' _).mp (H.inv_mem hh)
  · left
    rw [hk, show x * (x ^ (2 : ℤ) * h) = x ^ (3 : ℤ) * h by group, hx3, one_mul]
    exact hh

theorem no27 {B H : Subgroup G} (hB : IsElemAb 3 4 B) (hHB : H ≤ B) (hH : Nat.card H = 27)
    {b b₁ s : G} (hb : b ∈ B) (hb₁ : b₁ ∈ B) (hs : s ∈ B) (n0 : b ∉ H) (n1 : b₁ ∉ H)
    (w0 : b * b₁ * s ∉ H) (w1 : b⁻¹ * b₁ * s ∉ H) (w2 : b * b₁⁻¹ * s ∉ H)
    (w3 : b⁻¹ * b₁⁻¹ * s ∉ H) : False := by
  have hcomm := comm_of_isElemAb hB
  have cb1 : b * b₁ = b₁ * b := hcomm _ hb _ hb₁
  have cbs : b * s = s * b := hcomm _ hb _ hs
  have hb1 : Commute b b₁ := cb1
  have hbs : Commute b s := cbs
  have hb3 : b * b * b = 1 := by
    rw [← pow_three_eq_one_of_isElemAb hB hb, pow_three, mul_assoc]
  have hbi : b⁻¹ = b * b := (eq_inv_of_mul_eq_one_left hb3).symm
  have e1 : s * b⁻¹ = b⁻¹ * s := hbs.inv_left.eq.symm
  have e2 : b⁻¹ * b⁻¹ = b := by
    calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * (b * b * b) := by rw [hb3, mul_one]
      _ = b := by group
  have e3 : b₁⁻¹ * b = b * b₁⁻¹ := hb1.inv_right.eq.symm
  have hbB' := B.inv_mem hb
  rcases idx3 hB hHB hH hb hb₁ n0 n1 with h | h
  · have hsH : s ∉ H := fun hs' => w0 (H.mul_mem h hs')
    rcases idx3 hB hHB hH hs hb hsH n0 with h2 | h2
    · apply w1
      have : b⁻¹ * b₁ * s = b * b₁ * (s * b) := by
        rw [hbi, ← cbs, show b * b₁ * (b * s) = b * (b₁ * b) * s by group, ← cb1]
        group
      rw [this]; exact H.mul_mem h h2
    · apply w2
      have : b * b₁⁻¹ * s = (b * b₁)⁻¹ * (s * b⁻¹) := by
        calc b * b₁⁻¹ * s = b₁⁻¹ * b * s := by rw [e3]
          _ = b₁⁻¹ * (b⁻¹ * b⁻¹) * s := by rw [e2]
          _ = (b * b₁)⁻¹ * (b⁻¹ * s) := by group
          _ = (b * b₁)⁻¹ * (s * b⁻¹) := by rw [e1]
      rw [this]; exact H.mul_mem (H.inv_mem h) h2
  · have hsH : s ∉ H := fun hs' => w1 (by
      rw [show b⁻¹ * b₁ * s = (b * b₁⁻¹)⁻¹ * s by rw [hb1.inv_left.eq]; group]
      exact H.mul_mem (H.inv_mem h) hs')
    rcases idx3 hB hHB hH hs hb hsH n0 with h2 | h2
    · apply w3
      have : b⁻¹ * b₁⁻¹ * s = b * b₁⁻¹ * (s * b) := by
        calc b⁻¹ * b₁⁻¹ * s = b * b * b₁⁻¹ * s := by rw [hbi]
          _ = b * (b * b₁⁻¹) * s := by group
          _ = b * (b₁⁻¹ * b) * s := by rw [e3]
          _ = b * b₁⁻¹ * (b * s) := by group
          _ = b * b₁⁻¹ * (s * b) := by rw [cbs]
      rw [this]; exact H.mul_mem h h2
    · apply w0
      have : b * b₁ * s = (b * b₁⁻¹)⁻¹ * (s * b⁻¹) := by
        calc b * b₁ * s = b₁ * b * s := by rw [cb1]
          _ = b₁ * (b⁻¹ * b⁻¹) * s := by rw [e2]
          _ = (b * b₁⁻¹)⁻¹ * (b⁻¹ * s) := by group
          _ = (b * b₁⁻¹)⁻¹ * (s * b⁻¹) := by rw [e1]
      rw [this]; exact H.mul_mem (H.inv_mem h) h2

theorem conj_comm_mul {g h y : G} (hg : Commute g (h * y * h⁻¹)) :
    (g * h) * y * (g * h)⁻¹ = h * y * h⁻¹ := by
  calc (g * h) * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ := by group
    _ = h * y * h⁻¹ := by rw [hg.eq]; group

theorem conj4 (g p q r t : G) :
    g * (p * q * r * t) * g⁻¹ = (g * p * g⁻¹) * (g * q * g⁻¹) * (g * r * g⁻¹) * (g * t * g⁻¹) := by
  group

section Sylow

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem card_sylow_le (hB : FF81Basis b L B b₁ b₂ b₃) (haut : autOrder B ∣ 2 ^ 8 * 3 ^ 2)
    (P : Sylow 3 (Nor B)) : Nat.card ((P : Subgroup (Nor B)).map (Nor B).subtype) ≤ 729 := by
  set P' := (P : Subgroup (Nor B)).map (Nor B).subtype with hP'def
  have hP'N : P' ≤ Nor B := Subgroup.map_subtype_le _
  have hPp : IsPGroup 3 P' := P.isPGroup'.map _
  have hPC : P' ⊓ CenS B ≤ B := fun y hy =>
    hB.cenSyl y hy.2 (hPp.to_le (Subgroup.zpowers_le.mpr hy.1))
  have e := card_sup_mul_card_inf P' (CenS B) (hP'N.trans (nor_le_normalizer_cenS B))
  have hCM : CenS B ≤ P' ⊔ CenS B := le_sup_right
  have hMN : P' ⊔ CenS B ≤ Nor B := sup_le hP'N (Subgroup.centralizer_le_normalizer _)
  have e2 := Subgroup.relIndex_mul_card (CenS B) (P' ⊔ CenS B)
  rw [inf_of_le_left hCM] at e2
  have e3 := Subgroup.relIndex_mul_relIndex (CenS B) (P' ⊔ CenS B) (Nor B) hCM hMN
  have hm : (CenS B).relIndex (P' ⊔ CenS B) ∣ autOrder B := Dvd.intro _ e3
  have hcardC : 0 < Nat.card (CenS B) := Nat.card_pos
  have hP' : Nat.card P' = (CenS B).relIndex (P' ⊔ CenS B) * Nat.card ↥(P' ⊓ CenS B) := by
    rw [← e2] at e
    have : ((CenS B).relIndex (P' ⊔ CenS B) * Nat.card ↥(P' ⊓ CenS B)) * Nat.card (CenS B) =
        Nat.card P' * Nat.card (CenS B) := by rw [← e]; ring
    exact (Nat.eq_of_mul_eq_mul_right hcardC this).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  have hm3 : (CenS B).relIndex (P' ⊔ CenS B) ∣ 3 ^ k := by
    rw [← hk]; exact Dvd.intro _ hP'.symm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hm3
  have hm9 : (CenS B).relIndex (P' ⊔ CenS B) ∣ 3 ^ 2 := by
    have h1 : 3 ^ j ∣ 2 ^ 8 * 3 ^ 2 := by rw [← hj]; exact hm.trans haut
    rw [hj]
    exact (Nat.Coprime.pow j 8 (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h1
  have hI : Nat.card ↥(P' ⊓ CenS B) ≤ 81 :=
    (Subgroup.card_le_of_le hPC).trans (by rw [hB.mono.1.2]; norm_num)
  rw [hP']
  calc _ ≤ 9 * 81 := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hm9) hI
    _ = 729 := by norm_num

end Sylow

theorem ff81_5_1 :
    ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
      FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ hS
  have hB := hS.basis
  have hB4 := hB.mono.1
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := hB.mem
  obtain ⟨hm, haut, hw⟩ : HasMonomial4 B b b₁ b₂ b₃ ∧ autOrder B ∣ 2 ^ 8 * 3 ^ 2 ∧
      ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃ := by
    rcases hS.caseII with ⟨hm, h, -, hw⟩ | ⟨hm, h, -, hw⟩
    · exact ⟨hm, by rw [h]; norm_num, hw⟩
    · exact ⟨hm, by rw [h], hw⟩
  obtain ⟨c, hcN, hc0, hc1, hc2, hc3⟩ := hB.mono.2.2.2.2.2
  have cube : ∀ y z w : G, c * y * c⁻¹ = z → c * z * c⁻¹ = w → c * w * c⁻¹ = y →
      Commute (c ^ 3) y := by
    intro y z w h1 h2 h3
    apply commute_of_conj
    calc c ^ 3 * y * (c ^ 3)⁻¹ = c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ := by rw [pow_three]; group
      _ = y := by rw [h1, h2, h3]
  have k0 := cube b b b hc0 hc0 hc0
  have k1 := cube b₁ b₂ b₃ hc1 hc2 hc3
  have k2 := cube b₂ b₃ b₁ hc2 hc3 hc1
  have k3 := cube b₃ b₁ b₂ hc3 hc1 hc2
  have sqc : ∀ y, c ^ 2 * y * (c ^ 2)⁻¹ = c * (c * y * c⁻¹) * c⁻¹ := fun y => by
    rw [sq]; group
  obtain ⟨e, r, hr3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3 (by norm_num)
  obtain ⟨d, hd⟩ : ∃ d, d = c ^ r := ⟨_, rfl⟩
  have hdN : d ∈ Nor B := hd ▸ Subgroup.pow_mem _ hcN r
  have hd3 : (⟨d, hdN⟩ : Nor B) ^ (3 ^ e) = 1 := by
    ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show d ^ 3 ^ e = 1
    rw [hd, ← pow_mul,
      show r * 3 ^ e = orderOf c by rw [hord]; ring, pow_orderOf_eq_one]
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_pow hd3).exists_le_sylow
  set P' := (P : Subgroup (Nor B)).map (Nor B).subtype with hP'def
  have hdP : d ∈ P' := ⟨⟨d, hdN⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  have hrmod : r % 3 = 1 ∨ r % 3 = 2 := by
    have : r % 3 ≠ 0 := fun h => hr3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have hdec : d = c ^ (3 * (r / 3)) * c ^ (r % 3) := by rw [hd, ← pow_add, Nat.div_add_mod]
  have conjd : ∀ y, Commute (c ^ 3) (c ^ (r % 3) * y * (c ^ (r % 3))⁻¹) →
      d * y * d⁻¹ = c ^ (r % 3) * y * (c ^ (r % 3))⁻¹ := fun y hy => by
    rw [hdec]; exact conj_comm_mul (by rw [pow_mul]; exact hy.pow_left _)
  have hdb : d * b * d⁻¹ = b := by
    have : c ^ (r % 3) * b * (c ^ (r % 3))⁻¹ = b := by
      rcases hrmod with h | h
      · rw [h, pow_one, hc0]
      · rw [h, sqc, hc0, hc0]
    rw [conjd b (by rw [this]; exact k0), this]
  have hK : Nat.card ↥(B ⊓ Cen d) ≤ 9 := by
    rcases hrmod with h | h
    · have e1 : d * b₁ * d⁻¹ = b₂ := by
        rw [conjd b₁ (by rw [h, pow_one, hc1]; exact k2), h, pow_one, hc1]
      have e2 : d * b₂ * d⁻¹ = b₃ := by
        rw [conjd b₂ (by rw [h, pow_one, hc2]; exact k3), h, pow_one, hc2]
      exact card_inf_cen_le_nine hB4 hB.elem hb1B hb2B hdN (by rw [conjBy_zpowers, e1])
        (by rw [conjBy_zpowers, e2])
    · have e1 : d * b₁ * d⁻¹ = b₃ := by
        rw [conjd b₁ (by rw [h, sqc, hc1, hc2]; exact k3), h, sqc, hc1, hc2]
      have e3 : d * b₃ * d⁻¹ = b₂ := by
        rw [conjd b₃ (by rw [h, sqc, hc3, hc1]; exact k2), h, sqc, hc3, hc1]
      exact card_inf_cen_le_nine hB4 (isElemAb_perm hB.elem).2.1 hb1B hb3B hdN
        (by rw [conjBy_zpowers, e1]) (by rw [conjBy_zpowers, e3])
  refine controlsFusionIn_of_unique hB4 P fun A hAP hA => ?_
  by_contra hne
  have hAN : A ≤ Nor B := hAP.trans (Subgroup.map_subtype_le _)
  have hnot : ∀ n ∈ Nor B, n * b * n⁻¹ ∉ A := fun n hn => not_mem_of_ne hB hA hAN hne hn
  have hBP : B ≤ P' := by
    haveI : (B.subgroupOf (Nor B)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
    have hBp : IsPGroup 3 (B.subgroupOf (Nor B)) :=
      (IsPGroup.of_card hB4.2).comap_of_injective (Nor B).subtype Subtype.val_injective
    have hle := hBp.le_sylow_of_normal P
    intro y hy
    exact ⟨⟨y, Subgroup.le_normalizer hy⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hP729 := card_sylow_le hB haut P
  have hAB := card_sup_mul_card_inf A B hAN
  rw [hA.2, hB4.2] at hAB
  replace hAB : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = 6561 := by rw [hAB]; norm_num
  have hsupP : A ⊔ B ≤ P' := sup_le hAP hBP
  have hsup := (Subgroup.card_le_of_le hsupP).trans hP729
  have h9 : 9 ≤ Nat.card ↥(A ⊓ B) := by nlinarith
  have hdvd := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ B ≤ B)
  rw [hB4.2] at hdvd
  obtain ⟨m, hm4, hme⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases m
  · rw [hme] at h9; norm_num at h9
  · rw [hme] at h9; norm_num at h9
  ·
    have hsup729 : Nat.card ↥(A ⊔ B) = 729 := by rw [hme] at hAB; omega
    have hsupeq : A ⊔ B = P' :=
      Subgroup.eq_of_le_of_card_ge hsupP (by rw [hsup729]; exact hP729)
    have hdAB : d ∈ ((A ⊔ B : Subgroup G) : Set G) := by rw [hsupeq]; exact hdP
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAN] at hdAB
    obtain ⟨β, hβ, z, hz, hβz⟩ := Set.mem_mul.mp hdAB
    have hcommA := comm_of_isElemAb hA
    have hcommB := comm_of_isElemAb hB4
    have hle : A ⊓ B ≤ B ⊓ Cen d := fun y hy => by
      refine ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hβz]
      calc y * (β * z) = β * y * z := by rw [← mul_assoc, hcommA y hy.1 β hβ]
        _ = β * (z * y) := by rw [mul_assoc, hcommB y hy.2 z hz]
        _ = β * z * y := (mul_assoc _ _ _).symm
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hme]; exact le_of_le_of_eq hK (by norm_num))
    have hbC : b ∈ B ⊓ Cen d :=
      ⟨hbB, Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_conj hdb).eq.symm⟩
    rw [← heq] at hbC
    exact hnot 1 (Subgroup.one_mem _) (by simpa using hbC.1)
  ·
    obtain ⟨nt, hnt, ht0, -⟩ := hm.2.2.2.1
    obtain ⟨nw, hnw, hw'⟩ := hw
    obtain ⟨i0, hi0, f0, f1, f2, f3⟩ := hB.mono.2.2.1
    obtain ⟨i1, hi1, g0, g1, g2, g3⟩ := hB.mono.2.2.2.1
    have f1' : i0 * b₁⁻¹ * i0⁻¹ = b₁⁻¹ := by
      rw [show i0 * b₁⁻¹ * i0⁻¹ = (i0 * b₁ * i0⁻¹)⁻¹ by group, f1]
    have nA : ∀ n ∈ Nor B, ∀ y, n * b * n⁻¹ = y → y ∉ A ⊓ B := fun n hn y hy h =>
      hnot n hn (by rw [hy]; exact h.1)
    refine no27 hB4 inf_le_right (by rw [hme]; norm_num) hbB hb1B (B.mul_mem hb2B hb3B)
      (nA 1 (Subgroup.one_mem _) b (by group)) (nA nt hnt b₁ ht0)
      (nA nw hnw _ (by rw [hw']; group)) (nA (i0 * nw) (Subgroup.mul_mem _ hi0 hnw) _ ?_)
      (nA (i1 * nw) (Subgroup.mul_mem _ hi1 hnw) _ ?_)
      (nA (i0 * i1 * nw) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hi0 hi1) hnw) _ ?_)
    · rw [show (i0 * nw) * b * (i0 * nw)⁻¹ = i0 * (nw * b * nw⁻¹) * i0⁻¹ by group, hw', conj4,
        f0, f1, f2, f3]
      group
    · rw [show (i1 * nw) * b * (i1 * nw)⁻¹ = i1 * (nw * b * nw⁻¹) * i1⁻¹ by group, hw', conj4,
        g0, g1, g2, g3]
      group
    · rw [show (i0 * i1 * nw) * b * (i0 * i1 * nw)⁻¹ = i0 * (i1 * (nw * b * nw⁻¹) * i1⁻¹) * i0⁻¹
        by group, hw', conj4, g0, g1, g2, g3, conj4, f0, f1', f2, f3]
      group
  ·
    have h1 : A ⊓ B = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hme, hB4.2])
    have h2 : B ≤ A := inf_eq_right.mp h1
    exact hne (Subgroup.eq_of_le_of_card_ge h2 (by rw [hA.2, hB4.2])).symm

end CFSG.RankThree.PartTwo.Sec21.FF81
