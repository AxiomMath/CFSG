module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

theorem not_isSolvable_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ¬ Group.IsSolvable G := by
  intro hs
  have hc : ∀ a b : G, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact h IsSimpleGroup.prime_card

theorem le_of_solvable_normal_of_simple_quotient {Γ : Type*} [Group Γ] {H E R : Subgroup Γ}
    [hEn : (E.subgroupOf H).Normal] [hsimple : IsSimpleGroup (↥H ⧸ E.subgroupOf H)]
    (hnp : ¬ (Nat.card (↥H ⧸ E.subgroupOf H)).Prime) (hRH : R ≤ H)
    (hN : H ≤ Subgroup.normalizer (R : Set Γ)) (hs : Group.IsSolvable ↥R) : R ≤ E := by
  have hn : (R.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hN g.2) (x : Γ)).mp hx
    simpa using this
  have hsolv : Group.IsSolvable ↥(R.subgroupOf H) := by
    have := hs
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRH).symm.surjective
  let π : ↥H →* ↥H ⧸ E.subgroupOf H := QuotientGroup.mk' (E.subgroupOf H)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective (E.subgroupOf H)
  have hnb : ((R.subgroupOf H).map π).Normal := hn.map π hπs
  rcases hsimple.eq_bot_or_eq_top_of_normal ((R.subgroupOf H).map π) with h | h
  · intro r hr
    have h1 : π ⟨r, hRH hr⟩ = 1 := by
      have : π ⟨r, hRH hr⟩ ∈ (R.subgroupOf H).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hr)
      rw [h, Subgroup.mem_bot] at this
      exact this
    have h2 : (⟨r, hRH hr⟩ : ↥H) ∈ E.subgroupOf H := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  · exfalso
    have hsq : Group.IsSolvable (↥H ⧸ E.subgroupOf H) := by
      have := hsolv
      refine Group.isSolvable_of_surjective (f := π.comp (R.subgroupOf H).subtype) ?_
      intro q
      have hq : q ∈ (R.subgroupOf H).map π := by rw [h]; exact Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    exact not_isSolvable_of_simple hnp hsq

section Hj


theorem le_Eg_of_solvable_normal {R : Subgroup J} (hRH : R ≤ Hj)
    (hN : Hj ≤ Subgroup.normalizer (R : Set J)) (hs : Group.IsSolvable ↥R) : R ≤ Eg uJ 11 := by
  have := isSimpleGroup_Hj_quotient
  refine le_of_solvable_normal_of_simple_quotient (E := Eg uJ 11) ?_ hRH hN hs
  rw [card_Hj_quotient]
  norm_num

theorem rad_Hj {R : Subgroup J} (hRH : R ≤ Hj) (hN : Hj ≤ Subgroup.normalizer (R : Set J))
    (hs : Group.IsSolvable ↥R) : ¬ 9 ∣ Nat.card ↥R := by
  have hM := j4Facts.mat
  have hle := le_Eg_of_solvable_normal hRH hN hs
  have hdvd : Nat.card ↥R ∣ Nat.card ↥(Eg uJ 11) := Subgroup.card_dvd_of_le hle
  rw [card_Eg_uJ hM] at hdvd
  intro h9
  have h3 : 3 ∣ 2 ^ 11 := (Nat.dvd_trans (by norm_num : 3 ∣ 9) h9).trans hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

end Hj

end CFSG.Quasithin.J4Rad
