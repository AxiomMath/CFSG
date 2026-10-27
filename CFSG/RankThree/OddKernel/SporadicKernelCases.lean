module

public import CFSG.RankThree.OddKernel.SporadicKernelTools
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.Schreier.ONVectorOrder
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem odd_of_coprime_six {n : ℕ} (h6 : Nat.Coprime n 6) : Odd n :=
  Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num) h6)

omit [Finite E] [Group.IsPerfect E] in
theorem ker_eq_bot_of_mulEquiv_cover {T : Type*} [Group T] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (h6 : Nat.Coprime (Nat.card π.ker) 6) (e : S ≃* T)
    (htriv : ∀ π' : E →* T, Function.Surjective π' → π'.ker ≤ Subgroup.center E →
      Odd (Nat.card π'.ker) → π'.ker = ⊥) : π.ker = ⊥ := by
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  rw [← hker]
  exact htriv _ (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ odd_of_coprime_six h6)

theorem ker_eq_bot_of_isSporadic_small (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    {s : TauCeti.SporadicName} (hs : s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1)
    (h : NativeSporadic.IsSporadic S s) : π.ker = ⊥ := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  have hS : Nat.card S = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  rcases card_small_sporadic hs with hN | hN | hN | hN
  · exact ker_eq_bot_of_card_eq π hπ hC h6 (hS.trans hN)
      ((small_sporadic_order_conditions (Or.inl rfl)).2)
  · exact ker_eq_bot_of_card_eq π hπ hC h6 (hS.trans hN)
      ((small_sporadic_order_conditions (Or.inr (Or.inl rfl))).2)
  · exact ker_eq_bot_of_card_eq π hπ hC h6 (hS.trans hN)
      ((small_sporadic_order_conditions (Or.inr (Or.inr (Or.inl rfl)))).2)
  · exact ker_eq_bot_of_card_eq π hπ hC h6 (hS.trans hN)
      ((small_sporadic_order_conditions (Or.inr (Or.inr (Or.inr rfl)))).2)

theorem ker_eq_bot_of_isSporadic_J3 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .J3) : π.ker = ⊥ := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.J3.card_J3) fun _ hr h2 h3 => sq_primes_J3 hr h2 h3

theorem ker_eq_bot_of_isSporadic_M12 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .M12) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    M12_perfect_odd_cover_trivial π' h1 h2 h3

theorem ker_eq_bot_of_isSporadic_M24 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .M24) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    M24_perfect_odd_cover_trivial π' h1 h2 h3

theorem ker_eq_bot_of_isSporadic_J2 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .J2) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    J2_perfect_odd_cover_trivial π' h1 h2 h3

theorem ker_eq_bot_of_isSporadic_HS (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .HS) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    HS_perfect_odd_cover_trivial π' h1 h2 h3

theorem ker_eq_bot_of_isSporadic_He (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .He) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    He_perfect_odd_cover_trivial π' h1 h2 h3

theorem ker_eq_bot_of_isSporadic_Ru (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Ru) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    Ru_perfect_odd_cover_trivial π' h1 h2 h3

theorem prime_dvd_of_isSporadic_Co1 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Co1) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 ∨ r = 7 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Co1.card_Co1) (fun _ hr h2 h3 h => sq_primes_Co1 hr h2 h3 h) hr hrC

theorem prime_dvd_of_isSporadic_Co2 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Co2) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Co2Cert.natCard_Co2) (fun _ hr h2 h3 h => sq_primes_Co2 hr h2 h3 h) hr hrC

theorem prime_dvd_of_isSporadic_Co3 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Co3) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Schreier.Co3.card_Co3_of_perm) (fun _ hr h2 h3 h => sq_primes_Co3 hr h2 h3 h)
    hr hrC

theorem prime_dvd_of_isSporadic_Fi22 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Fi22) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Fi22.card_Fi22) (fun _ hr h2 h3 h => sq_primes_Fi22 hr h2 h3 h) hr hrC

theorem prime_dvd_of_isSporadic_McL (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .McL) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.McL.card_McL) (fun _ hr h2 h3 h => sq_primes_McL hr h2 h3 h) hr hrC

theorem prime_dvd_of_isSporadic_Suz (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Suz) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Suz.card_Suz) (fun _ hr h2 h3 h => sq_primes_Suz hr h2 h3 h) hr hrC

theorem prime_dvd_of_isSporadic_ON (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .ONan) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 7 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.ONSchreier.fam_on_vector_schreier_order.2.2.2.2.2.1)
    (fun _ hr h2 h3 h => sq_primes_ON hr h2 h3 h) hr hrC

end CFSG.RankThree.OddKernel
