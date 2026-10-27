module

public import CFSG.Quasithin.EmptyFaithful.S153EN8H

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem barM_zpow {x : G} (hx : x ∈ M) (k : ℤ) :
    barM cx (M.zpow_mem hx k) = (barM cx hx) ^ k := by
  unfold barM
  rw [← map_zpow]
  rfl

theorem barM_congr {x y : G} (hx : x ∈ M) (hy : y ∈ M) (h : x = y) :
    barM cx hx = barM cx hy := by
  subst h
  rfl

section Gen

variable (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)

include c B in
theorem exists_gen : ∃ (d : G) (hdM : d ∈ M), d ^ 3 = 1 ∧ d ≠ 1 ∧ barM cx hdM ∈ B.L₂ ∧
    IsSylowThreeOf153 (Subgroup.zpowers d) (M ⊓ Subgroup.centralizer (V₁ : Set G)) ∧
    Nat.card (Subgroup.zpowers d) = 3 := by
  obtain ⟨R, hRK, hRp, hRi, hR3⟩ := exists_sylow_three B c.toChain15358
  have hne : ∃ d ∈ R, d ≠ 1 := by
    by_contra h
    push Not at h
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [this, Subgroup.card_bot] at hR3
    omega
  obtain ⟨d, hdR, hd1⟩ := hne
  have hd3 : d ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥R) (x := ⟨d, hdR⟩)
    rw [hR3] at this
    simpa using congrArg Subtype.val this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hzeq : Subgroup.zpowers d = R :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdR)
      (by rw [Nat.card_zpowers, hord, hR3])
  obtain ⟨hdM, hbd⟩ := (mem_M₂_iff B).1 (hRK hdR)
  refine ⟨d, hdM, hd3, hd1, hbd, ?_, ?_⟩
  · rw [hzeq]
    exact ⟨hRK, hRp, hRi⟩
  · rw [hzeq]
    exact hR3

end Gen

section JStructure

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂)

omit [Finite G] in
theorem centralizer_zpowers_iff {x : G} :
    x ∈ Subgroup.centralizer (Subgroup.zpowers d : Set G) ↔ x * d = d * x := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h d (Subgroup.mem_zpowers d)).symm
  · intro h a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((show Commute d x from (show Commute x d from h).symm).zpow_left k).eq

include c B hd3 hd1 hbd in
theorem cent_eq_Jgp :
    M ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set G) = Subgroup.zpowers d ⊔ Jgp M V₂ d := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxd : x * d = d * x := centralizer_zpowers_iff.1 hxC
    have hc : barM cx hxM * barM cx hdM = barM cx hdM * barM cx hxM := by
      rw [← barM_mul hxM hdM, ← barM_mul hdM hxM]
      exact barM_congr _ _ hxd
    obtain ⟨l, hl, j, hj⟩ := cent_decomp B.hS (barM_mem_autI hxM) hbd (barM_cube hdM hd3)
      (barM_ne_one c hdM hd3 hd1) hc
    have hdj : d ^ j ∈ M := M.pow_mem hdM j
    have hx'M : x * (d ^ j)⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem hdj)
    have hbar : barM cx hx'M = l := by
      rw [barM_mul hxM (M.inv_mem hdj), barM_inv hdj, barM_pow hdM, hj]
      group
    have hx'J : x * (d ^ j)⁻¹ ∈ Jgp M V₂ d := by
      rw [mem_Jgp]
      refine ⟨⟨hx'M, ((mem_M₁_iff B).2 ⟨hx'M, by rw [hbar]; exact hl⟩).2⟩, ?_⟩
      have h2 : Commute ((d ^ j)⁻¹) d := ((Commute.refl d).pow_left j).inv_left
      exact (Commute.mul_left (show Commute x d from hxd) h2).eq
    have e : x = x * (d ^ j)⁻¹ * d ^ j := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hx'J (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j)
  · refine sup_le (fun x hx => Subgroup.mem_inf.2 ⟨Subgroup.zpowers_le.2 hdM hx, ?_⟩)
      (fun x hx => Subgroup.mem_inf.2 ⟨(mem_Jgp.1 hx).1.1, ?_⟩)
    · rw [centralizer_zpowers_iff]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((Commute.refl d).zpow_left k).eq
    · exact centralizer_zpowers_iff.2 (mem_Jgp.1 hx).2

include c B hdM hd3 hbd in
theorem inf_eq_Jgp : Subgroup.zpowers d ⊓ Jgp M V₂ d = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxD, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxD
  have hxM : d ^ k ∈ M := M.zpow_mem hdM k
  have h1 : barM cx hxM ∈ B.L₁ := by
    obtain ⟨_, h1⟩ := (mem_M₁_iff B).1 (show d ^ k ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) from
      ⟨(mem_Jgp.1 hxJ).1.1, (mem_Jgp.1 hxJ).1.2⟩)
    exact h1
  have h2 : barM cx hxM ∈ B.L₂ := by
    have : barM cx hxM = (barM cx hdM) ^ k := barM_zpow hdM k
    rw [this]
    exact B.L₂.zpow_mem hbd k
  have h3 : barM cx hxM = 1 := by
    have : barM cx hxM ∈ B.L₁ ⊓ B.L₂ := ⟨h1, h2⟩
    rw [B.hS.Linf, Subgroup.mem_bot] at this
    exact this
  have hQ : d ^ k ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    ⟨hxM, (barM_eq_one_iff hxM).1 h3⟩
  have hxT := Q_le_T c.toChain15358 hQ
  refine eq_one_of_cube_of_mem_T cx.hF.sylow_H.2.1 hxT ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]

omit [Finite G] in
theorem comm_Jgp {a b : G} (ha : a ∈ Subgroup.zpowers d) (hb : b ∈ Jgp M V₂ d) : a * b = b * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have : Commute b d := (mem_Jgp.1 hb).2
  exact ((this.symm.zpow_left k)).eq

include h113 c B hdM hd3 hd1 hbd in
theorem transv_Jgp {x : G} (hxJ : x ∈ Jgp M V₂ d) (hx2 : orderOf x = 2) (hxV : x ∉ V₁) :
    Nat.card ↥⁅VZ T M, Subgroup.zpowers x⁆ = 2 := by
  have hV := cx.c.hyp.elemAbelian
  have hxM : x ∈ M := (mem_Jgp.1 hxJ).1.1
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := cx.c.hyp.le_normalizer hxM
  have hbL : barM cx hxM ∈ B.L₁ := by
    obtain ⟨_, h1⟩ := (mem_M₁_iff B).1 (show x ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) from
      ⟨(mem_Jgp.1 hxJ).1.1, (mem_Jgp.1 hxJ).1.2⟩)
    exact h1
  have hb1 : barM cx hxM ≠ 1 := by
    intro h
    apply hxV
    rw [← inf_centralizer_Jgp h113 c B hdM hd3 hd1 hbd]
    exact Subgroup.mem_inf.2 ⟨hxJ, (barM_eq_one_iff hxM).1 h⟩
  have hx2' : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  have hb2 : (barM cx hxM) ^ 2 = 1 := by
    have : barM cx (M.pow_mem hxM 2) = 1 :=
      (barM_eq_one_iff _).2 (by rw [hx2']; exact Subgroup.one_mem _)
    rwa [barM_pow] at this
  have hz : Subgroup.zpowers x ≤ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.zpowers_le.2 hxN
  rw [commutator_eq_map_commV hV hz, autI_zpowers_eq' hV hxN,
    Subgroup.card_map_of_injective (inclMod_injective hV)]
  exact card_commV_involution B.hS IntMod.sq_eq_one hbL hb2 hb1

end JStructure

end S153EN8

end CFSG.Quasithin
