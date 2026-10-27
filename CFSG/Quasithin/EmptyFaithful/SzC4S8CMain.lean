module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8BMain
public import CFSG.Quasithin.EmptyFaithful.SzC4S8CCore
public import CFSG.Quasithin.Background.S1567V5

public section

namespace CFSG.Quasithin.SzC4S8C

theorem card_eq_two_of_sl3 {p : ℕ} (hp : 2 ≤ p)
    (h : p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) = 2 ^ 3 * ((2 ^ 2 - 1) * (2 ^ 3 - 1))) : p = 2 := by
  by_contra hne
  have hp3 : 3 ≤ p := by omega
  have h1 : 27 ≤ p ^ 3 := calc 27 = 3 ^ 3 := by norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have h2 : 9 ≤ p ^ 2 := calc 9 = 3 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
  have h3 : 8 ≤ p ^ 2 - 1 := by omega
  have h4 : 26 ≤ p ^ 3 - 1 := by omega
  have h5 : 27 * (8 * 26) ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
  norm_num at h
  omega

end CFSG.Quasithin.SzC4S8C

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement Pointwise

theorem c134Case4RigidAt_of_zq2 {G : Type} [Group G] [Finite G] {G₀ R L : Subgroup G}
    (hset : (G₀ : Set G) = (L : Set G) * (R : Set G)) (hcorr : MS93.IsC134Case4Corr G₀ R L)
    (hn1 : ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α)
    (hZ : centerOf (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G)) =
      frattiniIn (c134Q G₀ L)) : C134Case4RigidAt G₀ L := by
  intro c hcC hcG x hxQ hx
  obtain ⟨⟨n, F, _, _, α, hcard, hmod, hE2, -, -, -, hΦ, hQ₂, hQ⟩, -⟩ := hcorr
  obtain ⟨F₀, _, _, α₀, hcard₀, hmod₀⟩ := hn1
  have hF2 : Fintype.card F = 2 := by
    have hcs := S1567.card_statedSL_eq_of_same_ker α α₀ hmod.1 hmod₀.1
      (hmod.2.trans hmod₀.2.symm)
    rw [card_statedSL_three1527d, card_statedSL_three1527d] at hcs
    have hF₀ : Nat.card F₀ = 2 := by rw [Nat.card_eq_fintype_card]; exact hcard₀
    rw [hF₀] at hcs
    have hp : 2 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card]
    exact SzC4S8C.card_eq_two_of_sl3 hp hcs
  have hc2 : c * c = 1 := congrArg Subtype.val (s8_sq_eq_one_of_isE2 hE2 ⟨c, hcC⟩)
  have hLG : L ≤ G₀ := fun l hl => by
    have h1 : l * 1 ∈ (L : Set G) * (R : Set G) := Set.mul_mem_mul hl R.one_mem
    rw [← hset, mul_one] at h1
    exact h1
  have hQG : c134Q G₀ L ≤ G₀ := by
    unfold c134Q
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have ha' := pCoreOf_le 2 G₀ ha
    have hb' := hLG hb
    rw [commutatorElement_def]
    exact G₀.mul_mem (G₀.mul_mem (G₀.mul_mem ha' hb') (G₀.inv_mem ha')) (G₀.inv_mem hb')
  exact SzC4S8C.rigid_core hF2 hmod.1 hΦ hQ₂ hQ hZ.le hc2 (fun q hq => hcG q (hQG hq))
    (fun l hl => hcG l (hLG hl)) hxQ hx

end CFSG.Quasithin.SzC4
