module

public import CFSG.LocalAnalysis.StandardType.GGKGForkOneDone
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem rootTwo_of_mem_J_of_commute {p : ℕ} {B Bs J : Subgroup G} {g : G} (hgJ : g ∈ J)
    (hgB : ∀ b ∈ B, g * b = b * g) (hev : Even (orderOf g)) :
    GGResHigherFieldRootTwo p B Bs J := by
  classical
  obtain ⟨k, hk⟩ := hev
  have hpos : 0 < orderOf g := orderOf_pos g
  have h2dvd : 2 ∣ orderOf g := ⟨k, by rw [hk, two_mul]⟩
  let h : G := g ^ (orderOf g / 2)
  have hdiv : orderOf g / 2 * 2 = orderOf g := Nat.div_mul_cancel h2dvd
  have hh2 : h ^ 2 = 1 := by
    change (g ^ (orderOf g / 2)) ^ 2 = 1
    rw [← pow_mul, hdiv, pow_orderOf_eq_one]
  have hhne : h ≠ 1 := by
    intro h1
    have hdvd : orderOf g ∣ orderOf g / 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hge2 : 2 ≤ orderOf g := by omega
    have hposdiv : 0 < orderOf g / 2 := Nat.div_pos hge2 (by norm_num)
    have hlt : orderOf g / 2 < orderOf g := Nat.div_lt_self hpos (by norm_num)
    exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hposdiv hdvd)
  have hord2 : orderOf h = 2 := orderOf_eq_prime hh2 hhne
  have hcomm : ∀ b ∈ B, Commute b h := by
    intro b hb
    have hgb : Commute g b := hgB b hb
    exact hgb.symm.pow_right (orderOf g / 2)
  have hcent : Subgroup.centralizer (Subgroup.zpowers h : Set G) =
      Subgroup.centralizer ({h} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hBcent : B ≤ Subgroup.centralizer (Subgroup.zpowers h : Set G) := by
    intro b hb
    rw [hcent]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hcomm b hb).eq.symm
  have hTne : Subgroup.zpowers h ≠ ⊥ := fun hbot =>
    hhne (Subgroup.zpowers_eq_bot.mp hbot)
  have hT2 : IsPGroup 2 (Subgroup.zpowers h) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord2]
    norm_num
  have hTJ : Subgroup.zpowers h ≤ J := by
    rw [Subgroup.zpowers_le]
    exact J.pow_mem hgJ _
  refine ⟨Subgroup.zpowers h, hTne, hT2, hTJ, ?_⟩
  exact hBcent.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers h : Set G))

theorem GGConfig.rootTwo_of_reflection_fix
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNT : GGNoTransvection p Bs) (hp5 : 5 ≤ p) {t : MulAut ↥Bs} (ht : t ∈ ggInduced L Bs)
    (htr : GGIsReflection p t) (hB : B ≤ ggFixG Bs t) : GGResHigherFieldRootTwo p B Bs J := by
  classical
  have hJr : GGForkJr := ggForkJr_of_known ggForkRootSL2KGInput_holds ggLabelRigidInput_holds
  unfold GGForkJr at hJr
  obtain ⟨-, hDJ⟩ := hJr G p B Bs x L D J hcfg hInn hNT hp5 t ht htr
  have hDB : D ≤ B := by
    rw [hcfg.2.2.1.2.2.2.2.2.2]
    exact inf_le_left
  obtain ⟨g, hgJ, -, hgact⟩ := hDJ (hDB.trans hB)
  have hcomm : ∀ b ∈ B, g * b = b * g := by
    intro b hb
    obtain ⟨b', hb'fix, hb'eq⟩ := Subgroup.mem_map.mp (hB hb)
    have htb' : t b' = b' := hb'fix
    have hconj : g * (b' : G) * g⁻¹ = (b' : G) := by
      rw [← hgact b', htb']
    rw [← hb'eq]
    calc g * (b' : G) = (g * (b' : G) * g⁻¹) * g := by group
      _ = (b' : G) * g := by rw [hconj]
  have hev : Even (orderOf g) := by
    by_contra hnot
    have hodd : Odd (orderOf g) := Nat.not_even_iff_odd.mp hnot
    obtain ⟨k, hk⟩ := hodd
    have hpow : ∀ n : ℕ, ∀ b : ↥Bs,
        (((t ^ n) b : ↥Bs) : G) = g ^ n * (b : G) * (g ^ n)⁻¹ := by
      intro n
      induction n with
      | zero =>
          intro b
          simp
      | succ n ih =>
          intro b
          rw [pow_succ, MulAut.mul_apply, ih (t b), hgact b, pow_succ]
          group
    have htord : t ^ orderOf g = 1 := by
      ext b
      rw [hpow (orderOf g) b, pow_orderOf_eq_one, one_mul, inv_one, mul_one,
        MulAut.one_apply]
    have ht_one : t = 1 := by
      rw [hk, pow_add, pow_mul, htr.1] at htord
      simpa using htord
    have hcard : Nat.card {b : ↥Bs // t b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun b => by
        rw [ht_one]
        exact MulAut.one_apply ↥Bs b)
    have hcardpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have hp1 : p = 1 := by
      have h := htr.2
      rw [hcard] at h
      exact Nat.mul_left_cancel hcardpos (by simpa using h)
    omega
  exact rootTwo_of_mem_J_of_commute hgJ hcomm hev

end CFSG.StandardType

end
