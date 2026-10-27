module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Lift
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem r5c_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine And.intro (isMulCommutative_iff.mpr ?_) ?_
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hab : a * b = b * a :=
      congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨a, ha⟩ ⟨b, hb⟩)
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hab]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 a ha, map_one]

theorem r5c_isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup H} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.comap f) := by
  refine And.intro (isMulCommutative_iff.mpr ?_) ?_
  · intro x y
    have hab : f x * f y = f y * f x :=
      congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨f x, Subgroup.mem_comap.mp x.2⟩
        ⟨f y, Subgroup.mem_comap.mp y.2⟩)
    apply Subtype.ext
    apply hf
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hab
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hE.2 (f x) (Subgroup.mem_comap.mp hx)

theorem r5c_conj_injective {G : Type*} [Group G] [Group.IsPerfect G] :
    Function.Injective
      (MulAut.conj : (G ⧸ Subgroup.center G) →* MulAut (G ⧸ Subgroup.center G)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have hh : g * h * g⁻¹ = h := by
      have h' := congrArg (fun φ : MulAut (G ⧸ Subgroup.center G) => φ h) hg
      simpa using h'
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [Group.IsPerfect.center_quotient_center_eq_bot G] at hc
  exact Subgroup.mem_bot.mp hc

theorem r5c_map_mem_normalizer {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (T : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    f x ∈ Subgroup.normalizer ((T.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  by_cases hy : y ∈ f.range
  · obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
    have e : f x * f z * (f x)⁻¹ = f (x * z * x⁻¹) := by simp only [map_mul, map_inv]
    rw [e]
    change f z ∈ T.map f ↔ f (x * z * x⁻¹) ∈ T.map f
    rw [Subgroup.mem_map_iff_mem hf, Subgroup.mem_map_iff_mem hf]
    exact hx z
  · have h1 : y ∉ T.map f := fun h => by
      obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp h
      exact hy (MonoidHom.mem_range.mpr ⟨w, hw⟩)
    have h2 : f x * y * (f x)⁻¹ ∉ T.map f := fun h => by
      obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp h
      apply hy
      refine MonoidHom.mem_range.mpr ⟨x⁻¹ * w * x, ?_⟩
      rw [map_mul, map_mul, map_inv, hw]
      group
    change y ∈ T.map f ↔ f x * y * (f x)⁻¹ ∈ T.map f
    exact iff_of_false h1 h2

theorem r5c_pow_eq_one_of_card {M : Type*} [Group M] {n : ℕ} (Y : Subgroup M)
    (hY : Nat.card Y = n) {y : M} (hy : y ∈ Y) : y ^ n = 1 := by
  have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
  rw [hY] at h
  exact congrArg Subtype.val h

theorem r5c_eq_one_of_mem_inf {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) (R Y : Subgroup M)
    (hR : ¬ p ∣ Nat.card R) (hY : Nat.card Y = p) {y : M} (hyY : y ∈ Y) (hyR : y ∈ R) :
    y = 1 := by
  have h1 : y ^ p = 1 := r5c_pow_eq_one_of_card Y hY hyY
  have h2 : y ^ Nat.card R = 1 := r5c_pow_eq_one_of_card R rfl hyR
  have hcop : Nat.gcd p (Nat.card R) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hR)
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hcop, pow_one] at h3
  exact h3

theorem r5c_cube {M : Type*} [Group M] {p : ℕ} {F Y : Subgroup M}
    (hF : CFSG.Open.IsElemAbelian p F) (hFc : Nat.card F = p ^ 2)
    (hYc : Y ≤ Subgroup.center M) (hY : Nat.card Y = p) (hYp : ∀ y ∈ Y, y ^ p = 1)
    (hFY : F ⊓ Y = ⊥) :
    ∃ A : Subgroup M, CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 3 ∧
      ∀ T : Subgroup M, F ≤ Subgroup.normalizer (T : Set M) →
        A ≤ Subgroup.normalizer (T : Set M) := by
  have hcomm : ∀ y ∈ Y, ∀ g : M, g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hYc hy) g
  have hFcomm : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := by
    intro f hf f' hf'
    have h := isMulCommutative_iff.mp hF.1 ⟨f, hf⟩ ⟨f', hf'⟩
    exact congrArg Subtype.val h
  have hFexp : ∀ f ∈ F, f ^ p = 1 := fun f hf => hF.2 f hf
  have comm : ∀ (f : ↥F) (y : ↥Y), Commute (F.subtype f) (Y.subtype y) :=
    fun f y => hcomm (y : M) y.2 (f : M)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (↥F × ↥Y) →* M, ∀ x : ↥F × ↥Y, Φ x = (x.1 : M) * (x.2 : M) :=
    ⟨F.subtype.noncommCoprod Y.subtype comm, fun x => rfl⟩
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨f, y⟩ h
    have h' : (f : M) * (y : M) = 1 := (hΦ (f, y)).symm.trans h
    have hyinv : (f : M) = (y : M)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hmem : (f : M) ∈ F ⊓ Y :=
      Subgroup.mem_inf.mpr ⟨f.2, by rw [hyinv]; exact Y.inv_mem y.2⟩
    rw [hFY, Subgroup.mem_bot] at hmem
    have hf1 : f = 1 := Subtype.ext hmem
    have hy1 : (y : M) = 1 := by
      rw [hmem, one_mul] at h'
      exact h'
    have hy1' : y = 1 := Subtype.ext hy1
    exact Prod.mk_eq_one.mpr ⟨hf1, hy1'⟩
  have hΦcard : Nat.card Φ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, Nat.card_prod, hFc, hY]
    ring
  have hAmem : ∀ a ∈ Φ.range, ∃ f ∈ F, ∃ y ∈ Y, a = f * y := by
    intro a ha
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
    exact ⟨(x.1 : M), x.1.2, (x.2 : M), x.2.2, hΦ x⟩
  have hAcomm : ∀ a ∈ Φ.range, ∀ b ∈ Φ.range, a * b = b * a := by
    intro a ha b hb
    obtain ⟨f, hf, y, hy, rfl⟩ := hAmem a ha
    obtain ⟨f', hf', y', hy', rfl⟩ := hAmem b hb
    have e1 : f * y * (f' * y') = f * f' * (y * y') := by
      calc f * y * (f' * y') = f * (y * f') * y' := by simp only [mul_assoc]
        _ = f * (f' * y) * y' := by rw [← hcomm y hy f']
        _ = f * f' * (y * y') := by simp only [mul_assoc]
    have e2 : f' * y' * (f * y) = f' * f * (y' * y) := by
      calc f' * y' * (f * y) = f' * (y' * f) * y := by simp only [mul_assoc]
        _ = f' * (f * y') * y := by rw [← hcomm y' hy' f]
        _ = f' * f * (y' * y) := by simp only [mul_assoc]
    rw [e1, e2, hFcomm f hf f' hf', hcomm y' hy' y]
  have hAexp : ∀ a ∈ Φ.range, a ^ p = 1 := by
    intro a ha
    obtain ⟨f, hf, y, hy, rfl⟩ := hAmem a ha
    have hc : Commute f y := hcomm y hy f
    rw [hc.mul_pow, hFexp f hf, hYp y hy, one_mul]
  have hAel : CFSG.Open.IsElemAbelian p Φ.range :=
    And.intro (isMulCommutative_iff.mpr (fun a b => Subtype.ext (hAcomm a.1 a.2 b.1 b.2)))
      (fun a ha => hAexp a ha)
  have hyN : ∀ y ∈ Y, ∀ T : Subgroup M, y ∈ Subgroup.normalizer (T : Set M) := by
    intro y hy T
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e : y * h * y⁻¹ = h := by
      rw [← hcomm y hy h, mul_inv_cancel_right]
    rw [e]
  refine ⟨Φ.range, hAel, hΦcard, ?_⟩
  intro T hFT a ha
  obtain ⟨f, hf, y, hy, rfl⟩ := hAmem a ha
  exact mul_mem (hFT hf) (hyN y hy T)

theorem h2a_of_lifting {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R)
    (Y : Subgroup M) (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center M)
    (J : Subgroup (M ⧸ R)) (hJ : Group.IsPerfect J) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hno : ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M)) :
    ∀ F : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      F ≤ (MulAut.conj : (J ⧸ Subgroup.center J) →* MulAut (J ⧸ Subgroup.center J)).range →
      CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
      ∀ T : Subgroup (J ⧸ Subgroup.center J), T ≠ ⊥ → IsPGroup 2 T →
        ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T := by
  intro F hFc hFel hFcard T hT hT2
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective
      (MulAut.conj : (↥J ⧸ Subgroup.center ↥J) →* MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    r5c_conj_injective
  set F₀ : Subgroup (↥J ⧸ Subgroup.center ↥J) := F.comap MulAut.conj
  have hF₀map : F₀.map MulAut.conj = F := Subgroup.map_comap_eq_self hFc
  have hF₀card : Nat.card F₀ = p ^ 2 := by
    have h := Subgroup.card_map_of_injective (K := F₀) hinj
    rw [hF₀map, hFcard] at h
    exact h.symm
  have hF₀el : CFSG.Open.IsElemAbelian p F₀ := r5c_isElemAbelian_comap MulAut.conj hinj hFel
  have hF₀p : IsPGroup p F₀ := IsPGroup.of_card hF₀card
  have hF₀T : F₀ ≤ Subgroup.normalizer (T : Set (↥J ⧸ Subgroup.center ↥J)) := by
    intro s hs
    have hs' : MulAut.conj s ∈ F := Subgroup.mem_comap.mp hs
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcon _ hs')
  obtain ⟨FJ, hFJp, hFJmap, hFJR⟩ := exists_pSubgroup_lift hp (Subgroup.center ↥J) hZ hF₀p
  have hFJel : CFSG.Open.IsElemAbelian p FJ ∧ Nat.card FJ = p ^ 2 := by
    have h3 : Nat.card (FJ.map (QuotientGroup.mk' (Subgroup.center ↥J))) = p ^ 2 := by
      rw [hFJmap, hF₀card]
    obtain ⟨h1, h2⟩ := isElemAbelian_of_lift (p := p) (Subgroup.center ↥J) hFJR
      (by rw [hFJmap]; exact hF₀el)
    exact ⟨h1, h2.trans h3⟩
  obtain ⟨hFJel1, hFJcard⟩ := hFJel
  have hFTJ : FJ.map (QuotientGroup.mk' (Subgroup.center ↥J)) ≤
      Subgroup.normalizer (T : Set (↥J ⧸ Subgroup.center ↥J)) := by
    rw [hFJmap]
    exact hF₀T
  obtain ⟨TJ, hTJne, hTJ2, hFJTJ⟩ :=
    exists_two_lift hp hp2 (Subgroup.center ↥J) hZ hFJp hT hT2 hFTJ
  have hinjJ : Function.Injective J.subtype := fun a b h => Subtype.ext h
  have hFQp : IsPGroup p (FJ.map J.subtype) := hFJp.map J.subtype
  have hFQel : CFSG.Open.IsElemAbelian p (FJ.map J.subtype) :=
    r5c_isElemAbelian_map J.subtype hFJel1
  have hFQcard : Nat.card (FJ.map J.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinjJ, hFJcard]
  have hTQne : TJ.map J.subtype ≠ ⊥ := fun h =>
    hTJne ((Subgroup.map_eq_bot_iff_of_injective TJ hinjJ).mp h)
  have hTQ2 : IsPGroup 2 (TJ.map J.subtype) := hTJ2.map J.subtype
  have hFQTQ : FJ.map J.subtype ≤
      Subgroup.normalizer ((TJ.map J.subtype : Subgroup (M ⧸ R)) : Set (M ⧸ R)) := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    exact r5c_map_mem_normalizer J.subtype hinjJ TJ (hFJTJ hx')
  obtain ⟨FM, hFMp, hFMmap, hFMR⟩ := exists_pSubgroup_lift hp R hR hFQp
  have hFMel : CFSG.Open.IsElemAbelian p FM ∧ Nat.card FM = p ^ 2 := by
    have h3 : Nat.card (FM.map (QuotientGroup.mk' R)) = p ^ 2 := by
      rw [hFMmap, hFQcard]
    obtain ⟨h1, h2⟩ := isElemAbelian_of_lift (p := p) R hFMR
      (by rw [hFMmap]; exact hFQel)
    exact ⟨h1, h2.trans h3⟩
  obtain ⟨hFMel1, hFMcard⟩ := hFMel
  obtain ⟨TM, hTMne, hTM2, hFMTM⟩ :=
    exists_two_lift hp hp2 R hR hFMp hTQne hTQ2 (by rw [hFMmap]; exact hFQTQ)
  have hFY : FM ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyF, hyY⟩ := Subgroup.mem_inf.mp hy
    have hmy : (QuotientGroup.mk' R) y ∈ FJ.map J.subtype := by
      rw [← hFMmap]
      exact Subgroup.mem_map_of_mem _ hyF
    obtain ⟨f, hfFJ, hf⟩ := Subgroup.mem_map.mp hmy
    have hf' : (f : M ⧸ R) = (QuotientGroup.mk' R) y := hf
    have hcen : ∀ g : M ⧸ R, g * (QuotientGroup.mk' R) y = (QuotientGroup.mk' R) y * g := by
      intro g
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective R g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hYc hyY) m]
    have hfc : f ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hf']
      exact hcen (g : M ⧸ R)
    have hf1 : f = 1 := by
      have h : f ∈ FJ ⊓ Subgroup.center ↥J := Subgroup.mem_inf.mpr ⟨hfFJ, hfc⟩
      rw [hFJR, Subgroup.mem_bot] at h
      exact h
    have hy1 : (QuotientGroup.mk' R) y = 1 := by
      rw [← hf', hf1, Subgroup.coe_one]
    have hyR : y ∈ R := (QuotientGroup.eq_one_iff (N := R) y).mp hy1
    exact Subgroup.mem_bot.mpr (r5c_eq_one_of_mem_inf hp R Y hR hY hyY hyR)
  have hYp : ∀ y ∈ Y, y ^ p = 1 := fun y hy => r5c_pow_eq_one_of_card Y hY hy
  obtain ⟨A, hA, hA3, hAN⟩ := r5c_cube hFMel1 hFMcard hYc hY hYp hFY
  exact hno A TM hA hA3 hTMne hTM2 (hAN TM hFMTM)

end CFSG.RankThree.PartTwo.Sec13.F135Last
