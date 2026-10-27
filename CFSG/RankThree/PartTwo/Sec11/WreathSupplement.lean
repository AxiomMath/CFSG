module

public import CFSG.RankThree.PartTwo.Sec11.Wreath
public import CFSG.RankThree.PartTwo.Sec11.Data

public section

namespace CFSG.RankThree.PartTwo.Sec11

open scoped commutatorElement

abbrev wreathT : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

@[expose] def wreathK : W33 :=
  ⁅(⟨fun x => if x = 1 then wreathT else 1, 1⟩ : W33), (⟨1, wreathT⟩ : W33)⁆

@[expose] def wreathZ : W33 := ⁅(⟨fun x => x, 1⟩ : W33), (⟨1, wreathT⟩ : W33)⁆

theorem eq_one_of_commute_wreathK :
    ∀ (f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) (q : Multiplicative (ZMod 3)),
      ((⟨f, q⟩ : W33) * wreathK).left = (wreathK * ⟨f, q⟩).left → q = 1 := by
  decide

theorem pow_three_base :
    ∀ f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3),
      ((⟨f, 1⟩ : W33) ^ 3).left = (1 : W33).left ∧
        ((⟨f, 1⟩ : W33) ^ 3).right = (1 : W33).right := by
  decide

theorem eq_of_commute_base :
    ∀ f f₁ : Multiplicative (ZMod 3) → Multiplicative (ZMod 3),
      ((⟨f, 1⟩ : W33) * ⟨f₁, wreathT⟩).left = ((⟨f₁, wreathT⟩ : W33) * ⟨f, 1⟩).left →
        f = (1 : W33).left ∨ f = wreathZ.left ∨ f = wreathZ⁻¹.left := by
  decide

theorem wreathZ_right : wreathZ.right = 1 := by decide

theorem wreathZ_inv_right : wreathZ⁻¹.right = 1 := by decide

theorem right_eq_one_of_commute_wreathK {y : W33} (hy : y * wreathK = wreathK * y) :
    y.right = 1 :=
  eq_one_of_commute_wreathK y.left y.right (congrArg RegularWreathProduct.left hy)

theorem pow_three_eq_one_of_right_eq_one {y : W33} (hy : y.right = 1) : y ^ 3 = 1 := by
  obtain ⟨f, q⟩ := y
  change q = 1 at hy
  subst hy
  obtain ⟨h1, h2⟩ := pow_three_base f
  exact RegularWreathProduct.ext h1 h2

variable {G : Type*} [Group G]

theorem mul_comm_of_mem_closure_pair {a b x y : G} (hab : a * b = b * a)
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) (hy : y ∈ Subgroup.closure ({a, b} : Set G)) :
    x * y = y * x := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hab hx
  obtain ⟨i', j', rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hab hy
  have hc : Commute a b := hab
  exact (Commute.mul_left
    (Commute.mul_right (Commute.zpow_zpow_self a i i') (hc.zpow_zpow i j'))
    (Commute.mul_right (hc.symm.zpow_zpow j i') (Commute.zpow_zpow_self b j j'))).eq

theorem false_of_abelian_supplement {S : Subgroup W33} {d₁ d₂ : W33}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (h12 : d₁ * d₂ = d₂ * d₁)
    (hcomm : ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ Subgroup.closure {d₁, d₂})
    (hsup : S ⊔ Subgroup.closure {d₁, d₂} = ⊤) : False := by
  set D := Subgroup.closure ({d₁, d₂} : Set W33) with hDdef
  have hd₁ : d₁ ∈ D := Subgroup.subset_closure (by simp)
  have hd₂ : d₂ ∈ D := Subgroup.subset_closure (by simp)
  have hkD : wreathK ∈ D :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hZD : wreathZ ∈ D :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hDB : ∀ y ∈ D, y.right = 1 := fun y hy =>
    right_eq_one_of_commute_wreathK (mul_comm_of_mem_closure_pair h12 hy hkD)
  have h9 : Nat.card D ≤ 9 := card_closure_pair_le_nine h12
    (pow_three_eq_one_of_right_eq_one (hDB _ hd₁)) (pow_three_eq_one_of_right_eq_one (hDB _ hd₂))
  have hDn : D.Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact D.mul_mem (hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top n))) hn⟩
  have hmem : ∀ w : W33, ∃ s ∈ S, ∃ d ∈ D, s * d = w := by
    intro w
    have hw : w ∈ ((S ⊔ D : Subgroup W33) : Set W33) := by
      rw [hsup]
      trivial
    rw [Subgroup.mul_normal] at hw
    obtain ⟨s, hs, d, hd, hsd⟩ := hw
    exact ⟨s, hs, d, hd, hsd⟩
  have hright : ∀ s d : W33, d ∈ D → (s * d).right = s.right := by
    intro s d hd
    rw [RegularWreathProduct.mul_right, hDB d hd]
    exact mul_one _
  obtain ⟨s₁, hs₁, d, hd, hsd⟩ := hmem ⟨1, wreathT⟩
  have hs₁t : s₁.right = wreathT := by
    rw [← hright s₁ d hd, hsd]
  have hSB : ∀ s ∈ S, s.right = 1 → s ∈ D := by
    intro s hs hs1
    have hc := hS s hs s₁ hs₁
    obtain ⟨f, q⟩ := s
    obtain ⟨f₁, q₁⟩ := s₁
    change q = 1 at hs1
    change q₁ = wreathT at hs₁t
    subst hs1 hs₁t
    rcases eq_of_commute_base f f₁ (congrArg RegularWreathProduct.left hc) with h | h | h
    · have e : (⟨f, 1⟩ : W33) = 1 := RegularWreathProduct.ext h rfl
      rw [e]
      exact D.one_mem
    · have e : (⟨f, 1⟩ : W33) = wreathZ := RegularWreathProduct.ext h wreathZ_right.symm
      rw [e]
      exact hZD
    · have e : (⟨f, 1⟩ : W33) = wreathZ⁻¹ :=
        RegularWreathProduct.ext h wreathZ_inv_right.symm
      rw [e]
      exact D.inv_mem hZD
  have hBD : ∀ f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3), (⟨f, 1⟩ : W33) ∈ D := by
    intro f
    obtain ⟨s, hs, d, hd, hsd⟩ := hmem ⟨f, 1⟩
    have hs1 : s.right = 1 := by
      rw [← hright s d hd, hsd]
    have := D.mul_mem (hSB s hs hs1) hd
    rwa [hsd] at this
  have hinj : Function.Injective
      (fun f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3) => (⟨⟨f, 1⟩, hBD f⟩ : D)) :=
    fun f f' h => congrArg RegularWreathProduct.left (congrArg Subtype.val h)
  have h27 := Nat.card_le_card_of_injective _ hinj
  have hc : Nat.card (Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) = 27 := by
    rw [Nat.card_eq_fintype_card]
    decide
  omega

theorem false_of_wreath_quotient {P : Type*} [Group P] {Q : Subgroup P} [Q.Normal]
    (e : P ⧸ Q ≃* W33) {r g s x : P} (hrg : r * g = g * r) (hsx : s * x = x * s)
    (hPP : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.closure {s, x})
    (htop : Subgroup.closure {r, g} ⊔ Subgroup.closure {s, x} = ⊤) : False := by
  set π : P →* W33 := e.toMonoidHom.comp (QuotientGroup.mk' Q) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ
  have hpair : ∀ a b : P, (Subgroup.closure ({a, b} : Set P)).map π =
      Subgroup.closure {π a, π b} := by
    intro a b
    rw [MonoidHom.map_closure, Set.image_pair]
  refine false_of_abelian_supplement (S := (Subgroup.closure {r, g}).map π) (d₁ := π s)
    (d₂ := π x) ?_ ?_ ?_ ?_
  · intro a ha b hb
    rw [hpair] at ha hb
    exact mul_comm_of_mem_closure_pair (by rw [← map_mul, ← map_mul, hrg]) ha hb
  · rw [← map_mul, ← map_mul, hsx]
  · have h1 : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P).map π =
        ⁅(⊤ : Subgroup W33), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
    rw [← h1, ← hpair]
    exact Subgroup.map_mono hPP
  · rw [← hpair, ← Subgroup.map_sup, htop, ← MonoidHom.range_eq_map, hrange]

end CFSG.RankThree.PartTwo.Sec11
