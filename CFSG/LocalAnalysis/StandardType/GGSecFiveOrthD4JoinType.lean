module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrd
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private lemma ct_j1_card_G2 : Nat.card (CoxeterMatrix.G₂).Group = 12 := by
  let cs := (CoxeterMatrix.G₂).toCoxeterSystem
  have hs : cs.simple 0 * cs.simple 0 = 1 := cs.simple_mul_simple_self 0
  have ht : cs.simple 1 * cs.simple 1 = 1 := cs.simple_mul_simple_self 1
  have hs1 : cs.simple 0 ≠ 1 := cs.simple_ne_one 0
  have ht1 : cs.simple 1 ≠ 1 := cs.simple_ne_one 1
  have hn : orderOf (cs.simple 0 * cs.simple 1) = 6 := by
    rw [cs.orderOf_simple_mul_simple]
    decide
  have hgen : Subgroup.closure ({cs.simple 0, cs.simple 1} : Set (CoxeterMatrix.G₂).Group) = ⊤ := by
    rw [← cs.subgroup_closure_range_simple]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, hx.symm⟩
    · intro hx
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      have hi' : i = 0 ∨ i = 1 := by
        have h : i.val = 0 ∨ i.val = 1 := by omega
        rcases h with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi' with rfl | rfl <;> simp
  have e : DihedralGroup 6 ≃* (CoxeterMatrix.G₂).Group :=
    TauCeti.dihedralGroupMulEquiv (s := cs.simple 0) (t := cs.simple 1) (n := 6)
      hs ht hs1 ht1 hn hgen
  calc Nat.card (CoxeterMatrix.G₂).Group = Nat.card (DihedralGroup 6) :=
        (Nat.card_congr e.toEquiv).symm
    _ = 12 := by rw [DihedralGroup.nat_card]

private lemma ct_j1_card_B {G : Type} [Group G] {Bs : Subgroup G} {W : Subgroup (MulAut ↥Bs)}
    {n : ℕ} (h : GGWeylOfType 3 (CoxeterMatrix.B n) W) (hn : 2 ≤ n) :
    Nat.card ↥W = 2 ^ n * n.factorial := by
  rcases h with ⟨e, -⟩
  rw [← Nat.card_congr e.toEquiv]
  exact Nat.le_antisymm (card_coxeterB_le n) (CFSG.StandardType.SpFrame.card_coxeterB_ge n hn)

private lemma ct_j1_pow_fact (n : ℕ) (hn : 2 ≤ n) (h192 : 192 ∣ 2 ^ n * n.factorial)
    (hdvd : 2 ^ n * n.factorial ∣ 103680) : n = 4 ∨ n = 5 := by
  by_cases hn6 : n ≤ 6
  · interval_cases n
    · norm_num [Nat.factorial] at h192
    · norm_num [Nat.factorial] at h192
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num [Nat.factorial] at hdvd
  · push Not at hn6
    have hpow : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfac : Nat.factorial 7 ≤ n.factorial := Nat.factorial_le (by omega)
    have hbig : 2 ^ 7 * Nat.factorial 7 ≤ 2 ^ n * n.factorial := Nat.mul_le_mul hpow hfac
    norm_num at hbig
    have hle : 2 ^ n * n.factorial ≤ 103680 := Nat.le_of_dvd (by norm_num) hdvd
    omega


theorem ggOrthD4_joinType {G : Type} [Group G] {Bs : Subgroup G} {W : Subgroup (MulAut ↥Bs)}
    (hjoin : (∃ n : ℕ, 2 ≤ n ∧ GGWeylOfType 3 (CoxeterMatrix.B n) W) ∨ GGWeylOfType 3 CoxeterMatrix.F₄ W ∨
      GGWeylOfType 3 CoxeterMatrix.G₂ W)
    (h192 : 192 ∣ Nat.card ↥W) (hdvd : Nat.card ↥W ∣ 103680) :
    GGWeylOfType 3 (CoxeterMatrix.B 4) W ∨ GGWeylOfType 3 CoxeterMatrix.F₄ W ∨
      GGWeylOfType 3 (CoxeterMatrix.B 5) W := by
  rcases hjoin with ⟨n, hn, hB⟩ | hF | hG
  · have hcard := ct_j1_card_B hB hn
    have h45 := ct_j1_pow_fact n hn (by rwa [hcard] at h192) (by rwa [hcard] at hdvd)
    rcases h45 with rfl | rfl
    · exact Or.inl hB
    · exact Or.inr (Or.inr hB)
  · exact Or.inr (Or.inl hF)
  · exfalso
    rcases hG with ⟨e, -⟩
    have hcard : Nat.card ↥W = 12 := by
      rw [← Nat.card_congr e.toEquiv]
      exact ct_j1_card_G2
    have h192' : 192 ∣ 12 := by rwa [hcard] at h192
    have hle : 192 ≤ 12 := Nat.le_of_dvd (by norm_num) h192'
    omega

end CFSG.StandardType.OrthF3

end
