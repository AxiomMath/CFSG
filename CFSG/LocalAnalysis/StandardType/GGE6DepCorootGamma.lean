module

public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem gg6D2_isReflection_ne_one {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) : φ ≠ 1 := by
  intro h1
  have hcard : Nat.card {b : ↥Bs // φ b = b} = Nat.card ↥Bs := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun b => b.1
        invFun := fun b => ⟨b, by rw [h1, MulAut.one_apply]⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have h2 : Nat.card ↥Bs * p = Nat.card ↥Bs * 1 := by
    have := h.2
    rw [hcard] at this
    simpa using this
  exact hp.ne_one (Nat.eq_of_mul_eq_mul_left hpos h2)

private theorem gg6D2_overGamma_unique {Bs X : Subgroup G}
    {hN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {c : MulAut ↥Bs} {a a' : MulAut ↥(ggGamma X hN).range}
    (h : GGOverGamma hN c a) (h' : GGOverGamma hN c a') : a = a' := by
  apply MulEquiv.ext
  intro w
  obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma X hN) w
  rw [← h b, ← h' b]

private theorem gg6D2_mem_zpowers_of_rangeRestrict {Bs L : Subgroup G} {x : G}
    {hBsN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    {a b : ↥Bs} (haL : (a : G) ∈ L) (hbL : (b : G) ∈ L)
    (h : (ggGamma L hBsN).rangeRestrict a ∈
      Subgroup.zpowers ((ggGamma L hBsN).rangeRestrict b)) :
    a ∈ Subgroup.zpowers b := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hk' : (ggGamma L hBsN b) ^ k = ggGamma L hBsN a := by
    have := congrArg Subtype.val hk
    simpa using this
  have hγ : ggGamma L hBsN (b ^ k) = ggGamma L hBsN a := by
    rw [map_zpow]; exact hk'
  have hγ1 : ggGamma L hBsN (a * b ^ (-k)) = 1 := by
    have h3 : ggGamma L hBsN (a * b ^ (-k)) =
        ggGamma L hBsN a * (ggGamma L hBsN (b ^ k))⁻¹ := by
      rw [zpow_neg, map_mul, map_inv]
    rw [h3, hγ]
    exact mul_inv_cancel _
  have hmem : ((a * b ^ (-k) : ↥Bs) : G) ∈ Subgroup.zpowers x := by
    rw [← hker, Subgroup.mem_inf]
    exact ⟨(a * b ^ (-k)).2,
      (ggGamma_eq_one_iff L hBsN (a * b ^ (-k))).mp hγ1⟩
  have hL : ((a * b ^ (-k) : ↥Bs) : G) ∈ L :=
    L.mul_mem haL (L.zpow_mem hbL (-k))
  have hbot : ((a * b ^ (-k) : ↥Bs) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hxL]; exact ⟨hmem, hL⟩
  have hone : a * b ^ (-k) = 1 := Subtype.ext (Subgroup.mem_bot.mp hbot)
  have hka : a = b ^ k := by
    calc a = a * b ^ (-k) * b ^ k := by group
      _ = 1 * b ^ k := by rw [hone]
      _ = b ^ k := one_mul _
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hka.symm⟩

private theorem gg6D2_exists_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥) {c : ↥Bs} (hcL : (c : G) ∈ L)
    {φ : MulAut ↥Bs} (hφA : φ ∈ ggAutomizer L Bs) (hφrefl : GGIsReflection p φ)
    (hφcentre : GGReflCentre φ c) :
    ∃ φ' ∈ ggTorusAut (ggGamma L hBsN).range,
      GGIsReflection p φ' ∧
      GGReflCentre φ' ((ggGamma L hBsN).rangeRestrict c) ∧
      GGOverGamma hBsN φ φ' := by
  obtain ⟨g, hgL, hg, hφ⟩ := mem_ggAutomizer_iff.mp hφA
  have hφeq : φ = ggConjAut Bs hg := MulEquiv.ext fun b => Subtype.ext (hφ b)
  have hn : MulAut.conj (⟨g, hgL⟩ : L) ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut L)) :=
    conj_mem_normalizer_range_ggGamma hBsN hgL hg
  have hover : GGOverGamma hBsN φ (ggConjAut (ggGamma L hBsN).range hn) := by
    rw [hφeq]; exact ggOverGamma_conjAut hgL hg
  have hc : MulAut.conj (⟨g, hgL⟩ : L) ∈ (MulAut.conj : L →* MulAut L).range :=
    ⟨⟨g, hgL⟩, rfl⟩
  refine ⟨ggConjAut (ggGamma L hBsN).range hn,
    ggConjAut_mem_ggAutomizer hc hn, ?_, ?_, hover⟩
  · rcases isReflection_or_eq_one_of_overGamma hp hp2 hBs hBsN hover hφrefl with
      hrefl | h1
    · exact hrefl
    · exfalso
      have hcentral : ∀ b : ↥Bs,
          ((φ b * b⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (L : Set G) := by
        intro b
        have hov := hover b
        rw [h1, MulAut.one_apply] at hov
        have h2 : ggGamma L hBsN (φ b) = ggGamma L hBsN b := by
          simpa using congrArg Subtype.val hov
        have h3 : ggGamma L hBsN (φ b * b⁻¹) =
            ggGamma L hBsN (φ b) * (ggGamma L hBsN b)⁻¹ := by
          rw [map_mul, map_inv]
        refine (ggGamma_eq_one_iff L hBsN (φ b * b⁻¹)).mp ?_
        rw [h3, h2]
        exact mul_inv_cancel _
      have hfix : φ = 1 := by
        apply MulEquiv.ext
        intro b
        have hb1 : (φ b * b⁻¹ : ↥Bs) = 1 := by
          have hb1G : ((φ b * b⁻¹ : ↥Bs) : G) ∈ (⊥ : Subgroup G) := by
            rw [← hxL, Subgroup.mem_inf]
            refine ⟨?_, ?_⟩
            · rw [← hker, Subgroup.mem_inf]
              exact ⟨(φ b * b⁻¹).2, hcentral b⟩
            · have hzpG : ((φ b * b⁻¹ : ↥Bs) : G) ∈ Subgroup.zpowers (c : G) := by
                obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hφcentre b)
                refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
                rw [← hk]
                exact (map_zpow (Subgroup.subtype Bs) c k).symm
              exact Subgroup.zpowers_le.mpr hcL hzpG
          exact Subtype.ext (Subgroup.mem_bot.mp hb1G)
        exact mul_inv_eq_one.mp hb1
      exact gg6D2_isReflection_ne_one hp hφrefl hfix
  · intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    rw [← hover b]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hφcentre b)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h3 : (ggGamma L hBsN).rangeRestrict (φ b) *
        ((ggGamma L hBsN).rangeRestrict b)⁻¹ =
        (ggGamma L hBsN).rangeRestrict (φ b * b⁻¹) := by
      rw [map_mul, map_inv]
    rw [h3, ← map_zpow, hk]

theorem ggCorootPt_gamma {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥) {c : ↥Bs} (hcL : (c : G) ∈ L)
    (hc : GGCorootPt p (ggAutomizer L Bs) c) :
    GGCorootPt p (ggTorusAut (ggGamma L hBsN).range) ((ggGamma L hBsN).rangeRestrict c) := by
  obtain ⟨hcne, φ, hφA, hφrefl, hφcentre⟩ := hc
  obtain ⟨φ', hφ'mem, hφ'refl, hφ'centre, _⟩ :=
    gg6D2_exists_lift hp hp2 hBs hBsN hker hxL hcL hφA hφrefl hφcentre
  refine ⟨?_, φ', hφ'mem, hφ'refl, hφ'centre⟩
  intro h1
  have hγ : ggGamma L hBsN c = 1 := by
    simpa using congrArg Subtype.val h1
  have hcz : (c : G) ∈ Subgroup.zpowers x := by
    rw [← hker]
    exact ⟨c.2, (ggGamma_eq_one_iff L hBsN c).mp hγ⟩
  have hcbot : (c : G) ∈ (⊥ : Subgroup G) := by
    rw [← hxL]; exact ⟨hcz, hcL⟩
  exact hcne (Subtype.ext (Subgroup.mem_bot.mp hcbot))

theorem ggCorootOrth_gamma {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥) {a b : ↥Bs} (haL : (a : G) ∈ L) (hbL : (b : G) ∈ L)
    (hab : GGCorootOrth p (ggAutomizer L Bs) a b) :
    GGCorootOrth p (ggTorusAut (ggGamma L hBsN).range) ((ggGamma L hBsN).rangeRestrict a)
      ((ggGamma L hBsN).rangeRestrict b) := by
  obtain ⟨hzp, φ, hφA, ψ, hψA, hφrefl, hφcentre, hψrefl, hψcentre, hcomm⟩ := hab
  obtain ⟨φ', hφ'mem, hφ'refl, hφ'centre, hφ'over⟩ :=
    gg6D2_exists_lift hp hp2 hBs hBsN hker hxL haL hφA hφrefl hφcentre
  obtain ⟨ψ', hψ'mem, hψ'refl, hψ'centre, hψ'over⟩ :=
    gg6D2_exists_lift hp hp2 hBs hBsN hker hxL hbL hψA hψrefl hψcentre
  refine ⟨?_, φ', hφ'mem, ψ', hψ'mem, hφ'refl, hφ'centre, hψ'refl, hψ'centre, ?_⟩
  · intro hEq
    apply hzp
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      apply gg6D2_mem_zpowers_of_rangeRestrict (L := L) (hBsN := hBsN) hker hxL haL hbL
      rw [← hEq]
      exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      apply gg6D2_mem_zpowers_of_rangeRestrict (L := L) (hBsN := hBsN) hker hxL hbL haL
      rw [hEq]
      exact Subgroup.mem_zpowers _
  · have h1 : GGOverGamma hBsN (φ * ψ) (φ' * ψ') := hφ'over.mul hψ'over
    have h2 : GGOverGamma hBsN (φ * ψ) (ψ' * φ') := by
      have := hψ'over.mul hφ'over
      rw [← hcomm] at this
      exact this
    exact gg6D2_overGamma_unique h1 h2

end CFSG.StandardType

end
