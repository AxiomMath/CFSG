module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb)

variable {G : Type} [Group G] [Finite G]

theorem S36_elemAb_comm {H : Subgroup G} {k : ℕ} (hA : IsElemAb 2 k H) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : a * b = b * a := by
  haveI := hA.1
  have h := (inferInstance : IsMulCommutative H).is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem S36_elemAb_sq {H : Subgroup G} {k : ℕ} (hA : IsElemAb 2 k H) {a : G} (ha : a ∈ H) :
    a ^ 2 = 1 := by
  haveI := hA.1
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha

theorem S36_elemAb_map {H K : Type} [Group H] [Group K] [Finite H] {k : ℕ} (f : H →* K)
    (hf : Function.Injective f) {A : Subgroup H} (hA : IsElemAb 2 k A) :
    IsElemAb 2 k (A.map f) := by
  refine ⟨?_, by rw [Subgroup.card_map_of_injective hf]; exact hA.2⟩
  apply CFSG.IsElementaryAbelian.of_forall (p := 2)
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_mul, ← map_mul, S36_elemAb_comm hA ha' hb']
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow, S36_elemAb_sq hA ha', map_one]

theorem S36_elemAb_of_map {H K : Type} [Group H] [Group K] [Finite H] [Finite K] {k : ℕ} (f : H →* K)
    (hf : Function.Injective f) {A : Subgroup H} (hA : IsElemAb 2 k (A.map f)) :
    IsElemAb 2 k A := by
  refine ⟨?_, by rw [← Subgroup.card_map_of_injective hf]; exact hA.2⟩
  apply CFSG.IsElementaryAbelian.of_forall (p := 2)
  · intro a ha b hb
    apply hf
    rw [map_mul, map_mul]
    exact S36_elemAb_comm hA (Subgroup.mem_map_of_mem f ha) (Subgroup.mem_map_of_mem f hb)
  · intro a ha
    apply hf
    rw [map_pow, map_one]
    exact S36_elemAb_sq hA (Subgroup.mem_map_of_mem f ha)

theorem S36_elemAb_sup {A₁ A₂ : Subgroup G} (h₁ : IsElemAb 2 3 A₁) (h₂ : IsElemAb 2 3 A₂)
    (hc : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) (hint : Nat.card ↥(A₁ ⊓ A₂) = 2) :
    IsElemAb 2 5 (A₁ ⊔ A₂) := by
  obtain ⟨hcard, hsetEq⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hc
  have hdec : ∀ g ∈ A₁ ⊔ A₂, ∃ x ∈ A₁, ∃ y ∈ A₂, g = x * y := by
    intro g hg
    have hg' : g ∈ ((A₁ ⊔ A₂ : Subgroup G) : Set G) := hg
    rw [hsetEq] at hg'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hg'
    exact ⟨x, hx, y, hy, hxy.symm⟩
  have hcomm : ∀ a ∈ A₁ ⊔ A₂, ∀ b ∈ A₁ ⊔ A₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec a ha
    obtain ⟨x', hx', y', hy', rfl⟩ := hdec b hb
    have e1 : y * x' = x' * y := (hc x' hx' y hy).symm
    have e2 : y' * x = x * y' := (hc x hx y' hy').symm
    have cx := S36_elemAb_comm h₁ hx hx'
    have cy := S36_elemAb_comm h₂ hy hy'
    have h1 : x * y * (x' * y') = (x * x') * (y * y') := by
      calc x * y * (x' * y') = x * (y * x') * y' := by simp only [mul_assoc]
        _ = x * (x' * y) * y' := by rw [e1]
        _ = (x * x') * (y * y') := by simp only [mul_assoc]
    have h2 : x' * y' * (x * y) = (x * x') * (y * y') := by
      calc x' * y' * (x * y) = x' * (y' * x) * y := by simp only [mul_assoc]
        _ = x' * (x * y') * y := by rw [e2]
        _ = (x' * x) * (y' * y) := by simp only [mul_assoc]
        _ = (x * x') * (y * y') := by rw [← cx, ← cy]
    exact h1.trans h2.symm
  have hsq : ∀ a ∈ A₁ ⊔ A₂, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec a ha
    have e : y * x = x * y := (hc x hx y hy).symm
    rw [sq]
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [e]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [← sq, ← sq, S36_elemAb_sq h₁ hx, S36_elemAb_sq h₂ hy, one_mul]
  refine ⟨CFSG.IsElementaryAbelian.of_forall hcomm (fun a ha => by
    have := hsq a ha
    exact this), ?_⟩
  rw [hint, h₁.2, h₂.2] at hcard
  have h32 : Nat.card ↥(A₁ ⊔ A₂) = 32 := by omega
  rw [h32]
  norm_num

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
