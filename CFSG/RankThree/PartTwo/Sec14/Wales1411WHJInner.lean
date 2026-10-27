module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.LargeExtraspecial.S8DimB
import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Ext

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJInner

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {M : Type} [Group M] [Finite M] {Ybar Abar Xbar Rbar : Subgroup M} {abar : M}

theorem normal_X (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) : Xbar.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  exact top_le_iff.mp (hset.sup_eq_top ▸ hset.le_normalizer_X)

theorem le_centralizer_Y_of_X (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) {e : M}
    (he : e ∈ Abar) (hX : Xbar ≤ Subgroup.centralizer ({e} : Set M)) :
    Ybar ≤ Subgroup.centralizer ({e} : Set M) := by
  rw [hset.eq_sup]
  refine sup_le hX fun r hr => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (hset.le_centralizer_R hr) e he).symm

theorem abar_not_mem (hset : HJCoreSetting Ybar Abar Xbar Rbar abar)
    (hcen : Function.Injective (MulAut.conj : ↥Xbar →* MulAut ↥Xbar)) : abar ∉ Xbar := by
  intro ha
  apply hset.ne_one
  have h : MulAut.conj (⟨abar, ha⟩ : ↥Xbar) = MulAut.conj 1 := by
    ext y
    have hy : (y : M) * abar = abar * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a (hset.le_Y y.2))
    simp only [MulAut.conj_apply, map_one, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hy, mul_inv_cancel_right]
  have := congrArg Subtype.val (hcen h)
  simpa using this

section Inner

variable (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) [hXn : Xbar.Normal]
  (hcen : Function.Injective (MulAut.conj : ↥Xbar →* MulAut ↥Xbar))
  (hinner : ∀ α : MulAut ↥Xbar, α ^ 3 = 1 → α ∈ (MulAut.conj : ↥Xbar →* MulAut ↥Xbar).range)
include hset hcen hinner

omit hinner in
theorem conjNormal_coe (x : ↥Xbar) : MulAut.conjNormal (x : M) = MulAut.conj x := by
  ext y
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem exists_inner {e : M} (he : e ∈ Abar) :
    ∃ x : ↥Xbar, (x : M) ∈ Abar ∧ MulAut.conjNormal e = MulAut.conj x ∧
      e * (x : M)⁻¹ ∈ Subgroup.zpowers abar := by
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hAc : ∀ g ∈ Abar, ∀ h ∈ Abar, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hx : ∀ g ∈ Abar, ∃ x : ↥Xbar, MulAut.conjNormal g = MulAut.conj x := by
    intro g hg
    obtain ⟨x, hx⟩ := hinner (MulAut.conjNormal g) (by rw [← map_pow, hA3 g hg, map_one])
    exact ⟨x, hx.symm⟩
  obtain ⟨x, hxe⟩ := hx e he
  have hxC : (x : M) ∈ Subgroup.centralizer (Abar : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨x', hx'⟩ := hx g hg
    have hcomm : x * x' = x' * x := by
      apply hcen
      rw [map_mul, map_mul, ← hxe, ← hx', ← map_mul, ← map_mul, hAc e he g hg]
    have h1 : (MulAut.conjNormal g x : M) = g * x * g⁻¹ := MulAut.conjNormal_apply g x
    rw [hx', MulAut.conj_apply] at h1
    have h2 : ((x' * x * x'⁻¹ : ↥Xbar) : M) = x := by rw [← hcomm, mul_inv_cancel_right]
    rw [h2] at h1
    calc g * (x : M) = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [← h1]
  have hx3 : x ^ 3 = 1 := by
    apply hcen
    rw [map_pow, ← hxe, ← map_pow, hA3 e he, map_one, map_one]
  have hxA : (x : M) ∈ Abar := by
    by_cases h1 : x = 1
    · rw [h1]
      exact one_mem _
    · refine hset.mem_A_of_three _ (hset.le_Y x.2) hxC ?_
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hx3 h1
  refine ⟨x, hxA, hxe, hset.mem_zpowers _ (mul_mem he (inv_mem hxA)) ?_⟩
  refine le_centralizer_Y_of_X hset (mul_mem he (inv_mem hxA)) fun y hy => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (MulAut.conjNormal e ⟨y, hy⟩ : M) = e * y * e⁻¹ := MulAut.conjNormal_apply e _
  rw [hxe, MulAut.conj_apply] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have hexc : (x : M) * e = e * x := (Subgroup.mem_centralizer_iff.mp hxC e he).symm
  have h3 : (x : M)⁻¹ * e * y = y * ((x : M)⁻¹ * e) := by
    calc (x : M)⁻¹ * e * y = (x : M)⁻¹ * (e * y * e⁻¹) * e := by group
      _ = (x : M)⁻¹ * ((x : M) * y * (x : M)⁻¹) * e := by rw [← h1]
      _ = y * ((x : M)⁻¹ * e) := by group
  have h4 : e * (x : M)⁻¹ = (x : M)⁻¹ * e := by
    calc e * (x : M)⁻¹ = (x : M)⁻¹ * ((x : M) * e) * (x : M)⁻¹ := by group
      _ = (x : M)⁻¹ * (e * x) * (x : M)⁻¹ := by rw [hexc]
      _ = (x : M)⁻¹ * e := by group
  rw [h4]
  exact h3.symm

theorem eq_inf_sup : Abar = Abar ⊓ Xbar ⊔ Subgroup.zpowers abar := by
  refine le_antisymm (fun e he => ?_) (sup_le inf_le_left (Subgroup.zpowers_le.mpr hset.mem_A))
  obtain ⟨x, hxA, -, hxa⟩ := exists_inner hset hcen hinner he
  have h1 : e = e * (x : M)⁻¹ * x := by group
  rw [h1]
  exact mul_mem (Subgroup.mem_sup_right hxa) (Subgroup.mem_sup_left ⟨hxA, x.2⟩)

omit hinner in
theorem zpowers_inf_eq_bot : Subgroup.zpowers abar ⊓ Xbar = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : Nat.card (Subgroup.zpowers abar) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hset.isElemAbelian.2 abar hset.mem_A) hset.ne_one
  rcases (Nat.dvd_prime Nat.prime_three).mp
      (ha3 ▸ Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers abar ⊓ Xbar ≤ _)) with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    have heq : Subgroup.zpowers abar ⊓ Xbar = Subgroup.zpowers abar :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ha3, h])
    have hm : abar ∈ Subgroup.zpowers abar ⊓ Xbar := heq.symm ▸ Subgroup.mem_zpowers abar
    exact abar_not_mem hset hcen (Subgroup.mem_inf.mp hm).2

theorem card_inf : Nat.card (Abar ⊓ Xbar : Subgroup M) = 9 := by
  have hB : Subgroup.zpowers abar ≤ Subgroup.normalizer ((Abar ⊓ Xbar : Subgroup M) : Set M) := by
    rw [Subgroup.zpowers_le]
    refine Late.le_normalizer_inf (Subgroup.le_normalizer : Abar ≤ _)
      (by rw [Subgroup.normalizer_eq_top (H := Xbar)]; exact le_top) hset.mem_A
  have h := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_le_normalizer' hB
  rw [← eq_inf_sup hset hcen hinner, hset.card_A] at h
  have hbot : Abar ⊓ Xbar ⊓ Subgroup.zpowers abar = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ Subgroup.zpowers abar ⊓ Xbar := ⟨hz.2, hz.1.2⟩
    rwa [zpowers_inf_eq_bot hset hcen] at this
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers,
    orderOf_eq_prime (hset.isElemAbelian.2 abar hset.mem_A) hset.ne_one] at h
  omega

theorem Y_eq_X (hcent : ∀ α : MulAut ↥Xbar,
    (∀ x : ↥Xbar, (x : M) ∈ Abar → α * MulAut.conj x = MulAut.conj x * α) →
    ¬ 3 ∣ orderOf α → α = 1) : Ybar = Xbar := by
  have hRX : Rbar ≤ Subgroup.centralizer (Xbar : Set M) := by
    intro r hr
    have hα : MulAut.conjNormal (H := Xbar) r = 1 := by
      refine hcent _ (fun x hx => ?_) fun h3 => ?_
      · rw [← conjNormal_coe hset hcen x, ← map_mul, ← map_mul]
        congr 1
        exact (Subgroup.mem_centralizer_iff.mp (hset.le_centralizer_R hr) x hx).symm
      · apply hset.not_three_dvd_R
        exact h3.trans ((orderOf_map_dvd _ r).trans (Subgroup.orderOf_dvd_natCard _ hr))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut ↥Xbar => ((α ⟨y, hy⟩ : ↥Xbar) : M)) hα
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * r = r * y * r⁻¹ * r := by rw [h]
      _ = r * y := by group
  have hRY : Rbar ≤ Ybar := hset.eq_sup ▸ le_sup_right
  have hYR : Ybar ≤ Subgroup.normalizer (Rbar : Set M) := by
    rw [hset.eq_sup]
    refine sup_le (fun x hx => ?_) Subgroup.le_normalizer
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hxr : x * r = r * x :=
      Subgroup.mem_centralizer_iff.mp (hRX hr) x hx
    rw [hxr, mul_inv_cancel_right]
    exact hr
  have hR1 := hset.eq_bot_of_three Rbar hRY hYR hset.not_three_dvd_R
  rw [hset.eq_sup, hR1, sup_bot_eq]

omit hcen hinner in
theorem mem_normalizer_A (hAeq : Abar = Abar ⊓ Xbar ⊔ Subgroup.zpowers abar) {n : M}
    (hnX : n ∈ Xbar) (hn : n ∈ Subgroup.normalizer ((Abar ⊓ Xbar : Subgroup M) : Set M)) :
    n ∈ Subgroup.normalizer (Abar : Set M) := by
  have hna : n * abar = abar * n :=
    Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a (hset.le_Y hnX))
  have hz : Subgroup.zpowers n ≤ Subgroup.normalizer ((Subgroup.zpowers abar : Subgroup M) :
      Set M) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute n (abar ^ k) := (Commute.zpow_right hna k)
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers abar k
  have h := le_normalizer_sup_of_le (Subgroup.zpowers_le.mpr hn) hz
  rw [← hAeq] at h
  exact h (Subgroup.mem_zpowers n)

omit hcen hinner in
theorem le_normalizer_of_inf (hAeq : Abar = Abar ⊓ Xbar ⊔ Subgroup.zpowers abar)
    {U : Subgroup M} (hUY : U ≤ Ybar)
    (hU : Abar ⊓ Xbar ≤ Subgroup.normalizer (U : Set M)) :
    Abar ≤ Subgroup.normalizer (U : Set M) := by
  rw [hAeq]
  refine sup_le hU ?_
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  have hua : u * abar = abar * u :=
    Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a (hUY hu))
  rw [← hua, mul_inv_cancel_right]
  exact hu

omit hcen hinner in
theorem conj_of_etrans2 (hAeq : Abar = Abar ⊓ Xbar ⊔ Subgroup.zpowers abar) (hYX : Ybar = Xbar)
    (hET : ETrans2 ↥Xbar ((Abar ⊓ Xbar).subgroupOf Xbar))
    {S T : Subgroup M} (hS : Maximal (InvTwo Abar Ybar) S) (hT : Maximal (InvTwo Abar Ybar) T)
    (hST : S ⊔ T = Ybar) :
    ∃ n ∈ Ybar ⊓ Subgroup.normalizer (Abar : Set M), T = S.map (MulAut.conj n).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hYX
  set E' := (Abar ⊓ Ybar).subgroupOf Ybar with hE'
  have hback : ∀ W : Subgroup M, W ≤ Ybar → W = (W.subgroupOf Ybar).map Ybar.subtype :=
    fun W hW => (Subgroup.map_subgroupOf_eq_of_le hW).symm
  have hnormE : ∀ W : Subgroup M, W ≤ Ybar → Abar ≤ Subgroup.normalizer (W : Set M) →
      E' ≤ Subgroup.normalizer ((W.subgroupOf Ybar : Subgroup ↥Ybar) : Set ↥Ybar) := by
    intro W _ hAW ε hε
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hAW (Subgroup.mem_subgroupOf.mp hε).1) w
  have hnormA : ∀ W' : Subgroup ↥Ybar,
      E' ≤ Subgroup.normalizer ((W' : Subgroup ↥Ybar) : Set ↥Ybar) →
      Abar ≤ Subgroup.normalizer ((W'.map Ybar.subtype : Subgroup M) : Set M) := by
    intro W' hW'
    refine le_normalizer_of_inf hset hAeq (Subgroup.map_subtype_le W') fun ε hε => ?_
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨w', hw', rfl⟩ := hw
    have hεY : ε ∈ Ybar := hε.2
    have hε' : (⟨ε, hεY⟩ : ↥Ybar) ∈ E' := Subgroup.mem_subgroupOf.mpr hε
    have h := (Subgroup.mem_normalizer_iff.mp (hW' hε') w').mp hw'
    exact ⟨_, h, rfl⟩
  have hSY : S ≤ Ybar := hS.prop.1
  have hTY : T ≤ Ybar := hT.prop.1
  set S' := S.subgroupOf Ybar with hS'
  set T' := T.subgroupOf Ybar with hT'
  have hsup : S' ⊔ T' = ⊤ := by
    rw [hS', hT', ← Subgroup.subgroupOf_sup hSY hTY, hST, Subgroup.subgroupOf_self]
  have hmax : ∀ R : Subgroup M, Maximal (InvTwo Abar Ybar) R → R ≤ Ybar →
      Maximal (InvTwo E' (S' ⊔ T')) (R.subgroupOf Ybar) := by
    intro R hR hRY
    obtain ⟨-, hAR, hR2⟩ := hR.prop
    refine ⟨⟨hsup ▸ le_top, hnormE R hRY hAR,
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm⟩, fun U' hU' hRU' => ?_⟩
    obtain ⟨-, hEU', hU'2⟩ := hU'
    have hU2 : IsPGroup 2 (U'.map Ybar.subtype) := hU'2.map _
    have hRU : R ≤ U'.map Ybar.subtype := by
      rw [hback R hRY]
      exact Subgroup.map_mono hRU'
    have h := hR.2 ⟨Subgroup.map_subtype_le U', hnormA U' hEU', hU2⟩ hRU
    intro u hu
    have hu' : (u : M) ∈ R := h ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hu'
  obtain ⟨n, hn, hnT⟩ := hET S' T' (hmax S hS hSY) (hmax T hT hTY)
  have hnN : (n : M) ∈ Subgroup.normalizer ((Abar ⊓ Ybar : Subgroup M) : Set M) :=
    mem_normalizer_of_subgroupOf inf_le_right (Subgroup.mem_inf.mp hn).2
  refine ⟨n, Subgroup.mem_inf.mpr ⟨n.2, mem_normalizer_A hset hAeq n.2 hnN⟩, ?_⟩
  rw [hback T hTY, ← hT', hnT, hback S hSY, ← hS', Subgroup.map_map, Subgroup.map_map]
  congr 1

end Inner

end CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJInner
