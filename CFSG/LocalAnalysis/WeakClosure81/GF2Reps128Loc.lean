module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped commutatorElement

theorem dMinDeg_le_dMinDeg_map {G G' : Type} [Group G] [Group G'] [Finite G'] (f : G →* G')
    (X : Subgroup G) (hne : X.map f ≠ ⊥) : dMinDeg ↥X ≤ dMinDeg ↥(X.map f) := by
  have : Nontrivial ↥(X.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.dMinDeg_le_of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X)

theorem not_commute_of_isQuasisimple {G : Type*} [Group G] {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) : ¬ ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
  intro h
  have hc : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h _ y.2 _ x.2)
  obtain ⟨a, b, hab⟩ := hK.2.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [QuotientGroup.eq, hc]
      trivial

variable {V : Type} [CommGroup V] [Finite V]

theorem dMinDeg_le_rk_of_not_le_fixV (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {J : Subgroup V} (hJ : StableUnder X J) (hne : ¬ J ≤ fixV X) : dMinDeg ↥X ≤ rk ↥J := by
  by_contra hlt
  push Not at hlt
  apply hne
  have hbot : StableUnder X (⊥ : Subgroup V) := by
    intro x _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  have h := Inputs1719.commSub_le_of_rk_lt_dMinDeg hV (bot_le : (⊥ : Subgroup V) ≤ J) hJ hbot
    (by rw [rk_bot, zero_add]; exact hlt)
  exact commSub_eq_bot_iff.mp (le_bot_iff.mp h)

@[expose] def minStab (B : Subgroup (MulAut V)) (U : Subgroup V) : Set (Subgroup V) :=
  {J | J ≤ U ∧ StableUnder B J ∧ J ≠ ⊥ ∧
    ∀ J' : Subgroup V, StableUnder B J' → J' ≤ J → J' = ⊥ ∨ J' = J}

theorem exists_mem_minStab {B : Subgroup (MulAut V)} {U : Subgroup V} (hU : StableUnder B U)
    (hne : U ≠ ⊥) : ∃ J, J ∈ minStab B U := by
  classical
  have hex : ∃ n, ∃ J : Subgroup V, J ≤ U ∧ StableUnder B J ∧ J ≠ ⊥ ∧ Nat.card J = n :=
    ⟨_, U, le_rfl, hU, hne, rfl⟩
  obtain ⟨J, hJU, hJs, hJne, hJn⟩ := Nat.find_spec hex
  refine ⟨J, hJU, hJs, hJne, fun J' hJ's hJ'J => ?_⟩
  by_cases h : J' = ⊥
  · exact Or.inl h
  · right
    have hmin := Nat.find_min' hex ⟨J', hJ'J.trans hJU, hJ's, h, rfl⟩
    rw [← hJn] at hmin
    exact Subgroup.eq_of_le_of_card_ge hJ'J hmin

omit [Finite V] in
theorem mem_irrPlus_of_mem_minStab {B : Subgroup (MulAut V)} {U J : Subgroup V}
    (hJ : J ∈ minStab B U) (hJ0 : J ⊓ fixV B = ⊥) : J ∈ IrrPlus B (⊤ : Subgroup V) := by
  obtain ⟨-, hJs, hJne, hJirr⟩ := hJ
  rw [mem_irrPlus_top_iff]
  have hcomm : commSub J B = J := by
    rcases hJirr _ (stableUnder_commSub (fun h hh l hl => B.mul_mem (B.mul_mem hh hl)
        (B.inv_mem hh)) hJs) (commSub_le_of_invariant hJs) with h | h
    · exact absurd ((inf_eq_left.mpr (commSub_eq_bot_iff.mp h)).symm.trans hJ0) hJne
    · exact h
  refine ⟨hJs, hcomm, ?_, ?_⟩
  · rw [hJ0]
    exact bot_lt_iff_ne_bot.mpr hJne
  · intro J' hJ's _ hJ'J
    rw [hJ0]
    exact hJirr J' hJ's hJ'J

theorem mem_stabSub_of_rkIdx_lt {B : Subgroup (MulAut V)} {τ : MulAut V}
    (hτB : ∀ b ∈ B, τ⁻¹ * b * τ ∈ B) {U J : Subgroup V} (hJ : J ∈ minStab B U)
    (hrk : rkIdx (fixV (Subgroup.zpowers τ)) < rk ↥J) : τ ∈ stabSub J := by
  obtain ⟨-, hJs, -, hJirr⟩ := hJ
  have hτJ : StableUnder B (J.map τ.toMonoidHom) := by
    rintro b hb _ ⟨u, hu, rfl⟩
    refine ⟨(τ⁻¹ * b * τ) u, hJs _ (hτB b hb) u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self]
  rcases hJirr (J ⊓ J.map τ.toMonoidHom) (stableUnder_inf hJs hτJ) inf_le_left with h | h
  · exfalso
    have hJC : J ⊓ fixV (Subgroup.zpowers τ) = ⊥ := by
      rw [eq_bot_iff, ← h]
      intro v hv
      exact ⟨hv.1, v, hv.1, hv.2 τ (Subgroup.mem_zpowers τ)⟩
    have h1 := rk_sup_add_rk_inf J (fixV (Subgroup.zpowers τ))
    have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers τ))
    have h3 : rk ↥(J ⊔ fixV (Subgroup.zpowers τ)) ≤ rk V := (rk_mono le_top).trans rk_top.le
    rw [hJC, rk_bot] at h1
    omega
  · have hle : J ≤ J.map τ.toMonoidHom := h.ge.trans inf_le_right
    have heq : J.map τ.toMonoidHom = J := by
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [Subgroup.card_map_of_injective τ.injective]
    intro u
    constructor
    · intro hu
      rw [← heq] at hu
      obtain ⟨v, hv, hvu⟩ := hu
      have hvu' : τ v = τ u := hvu
      rwa [← τ.injective hvu']
    · intro hu
      rw [← heq]
      exact ⟨u, hu, rfl⟩

omit [Finite V] in
theorem map_mem_minStab {B : Subgroup (MulAut V)} {U J : Subgroup V} {g : MulAut V}
    (hgB : ∀ b ∈ B, g * b = b * g) (hgU : g ∈ stabSub U) (hJ : J ∈ minStab B U) :
    J.map g.toMonoidHom ∈ minStab B U := by
  obtain ⟨hJU, hJs, hJne, hJirr⟩ := hJ
  have hgB' : ∀ b ∈ B, g⁻¹ * b = b * g⁻¹ := by
    intro b hb
    have h := hgB b hb
    calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * b) * g⁻¹ := by rw [← h]
      _ = b * g⁻¹ := by group
  have hstab : ∀ {A : Subgroup V} {f : MulAut V}, (∀ b ∈ B, f * b = b * f) →
      StableUnder B A → StableUnder B (A.map f.toMonoidHom) := by
    rintro A f hf hA b hb _ ⟨u, hu, rfl⟩
    refine ⟨b u, hA b hb u hu, ?_⟩
    have := congrArg (fun φ : MulAut V => φ u) (hf b hb)
    simpa only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom] using this
  refine ⟨?_, hstab hgB hJs, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (hgU u).mpr (hJU hu)
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ g.injective]
    exact hJne
  · intro J' hJ's hJ'J
    have h1 : J'.map g⁻¹.toMonoidHom ≤ J := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hJ'J hu
      have hv' : v ∈ J := hv
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self] using hv'
    have hback : (J'.map g⁻¹.toMonoidHom).map g.toMonoidHom = J' := by
      rw [Subgroup.map_map]
      ext x
      simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulAut.apply_inv_self, exists_eq_right]
    rcases hJirr _ (hstab hgB' hJ's) h1 with h | h
    · left
      rw [← hback, h, Subgroup.map_bot]
    · right
      rw [← hback, h]

omit [Finite V] in
theorem commutatorElement_mem_stabSub {𝒥 : Set (Subgroup V)} {m s : MulAut V}
    (hm : ∀ J ∈ 𝒥, J.map m⁻¹.toMonoidHom ∈ 𝒥) (hs : ∀ J ∈ 𝒥, s ∈ stabSub J) :
    ∀ J ∈ 𝒥, ⁅m, s⁆ ∈ stabSub J := by
  intro J hJ
  have hs' := hs _ (hm J hJ)
  have hconj : m * s * m⁻¹ ∈ stabSub J := by
    intro u
    have hmem : ∀ y : V, m y ∈ J ↔ y ∈ J.map m⁻¹.toMonoidHom := by
      intro y
      constructor
      · intro hy
        exact ⟨m y, hy, by simp⟩
      · rintro ⟨j, hj, rfl⟩
        simpa using hj
    rw [MulAut.mul_apply, MulAut.mul_apply, hmem, hs' (m⁻¹ u), ← hmem, MulAut.apply_inv_self]
  rw [commutatorElement_def]
  exact (stabSub J).mul_mem hconj ((stabSub J).inv_mem (hs J hJ))

theorem conj_mem_commutator {G : Type*} [Group G] {M T : Subgroup G} {m : G} (hm : m ∈ M)
    {b : G} (hb : b ∈ ⁅M, T⁆) : m * b * m⁻¹ ∈ ⁅M, T⁆ := by
  rw [Subgroup.commutator_def] at hb ⊢
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    have e : m * ⁅g₁, g₂⁆ * m⁻¹ = ⁅m * g₁, g₂⁆ * ⁅m, g₂⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, M.mul_mem hm hg₁, g₂, hg₂, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨m, hm, g₂, hg₂, rfl⟩))
  | one => simp
  | mul x y _ _ hx hy =>
    have e : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

end CFSG.LocalAnalysis.WeakClosure81
