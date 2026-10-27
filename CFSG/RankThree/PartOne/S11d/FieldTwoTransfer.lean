module

public import CFSG.RankThree.PartOne.S11d.FieldTransfer

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T

variable {G : Type} [Group G] [Finite G] {p : ℕ} {J : Subgroup G} {u : G}

theorem twoElement_mem_perfectResidual_of_two (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center J))
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1)
    (hT2 : ∀ x ∈ fixSub (centerQuotientConj J ⟨u, hu⟩), (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ fixRes (centerQuotientConj J ⟨u, hu⟩)) {g : G}
    (hg : g ∈ J ⊓ Subgroup.centralizer ({u} : Set G)) (hg2 : ∃ k : ℕ, orderOf g = 2 ^ k) :
    g ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨θ, hsurj, hker, hθ⟩ := exists_fixed_hom hp hZ hu hup
  obtain ⟨k, hk⟩ := hg2
  let gC : ↥(J ⊓ Subgroup.centralizer ({u} : Set G)) := ⟨g, hg⟩
  have hgCk : gC ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    show g ^ (2 ^ k) = 1
    rw [← hk]
    exact pow_orderOf_eq_one g
  have hθ2 : ∃ j : ℕ, orderOf ((θ gC : ↥(fixSub (centerQuotientConj J ⟨u, hu⟩))) :
      ↥J ⧸ Subgroup.center ↥J) = 2 ^ j := by
    have h1 : orderOf (θ gC) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgCk, map_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨j, by rw [Subgroup.orderOf_coe]; exact hj⟩
  have hmem := hT2 _ (θ gC).2 hθ2
  have hres : θ gC ∈ perfectResidual ↥(fixSub (centerQuotientConj J ⟨u, hu⟩)) := by
    obtain ⟨y, hy, hyeq⟩ := hmem
    have : y = θ gC := Subtype.ext hyeq
    rw [← this]
    exact hy
  have hkerp : ∀ z ∈ θ.ker, Nat.Coprime (orderOf z) 2 := fun z hz =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (fun h => hZ2 (h.trans (orderOf_dvd_card_center_of_mem_ker hθ z hz))))
  exact ⟨gC, mem_perfectResidual_of_map hsurj hker hkerp hgCk hres, rfl⟩

end CFSG.RankThree.PartOne.FieldFix
