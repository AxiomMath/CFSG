module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Pair
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Sec2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1
open scoped commutatorElement

namespace S34

namespace Case1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

omit [Finite G] in
theorem stab_le_normalizer_Cb (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Cb δ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp
    (normalizer_le_normalizer_centralizer _ (le_normalizer_oTwoRes _ hg)) x
  constructor
  · intro hx
    exact ⟨h1.mp hx.1, h2.mp hx.2⟩
  · intro hx
    exact ⟨h1.mpr hx.1, h2.mpr hx.2⟩

theorem relIndex_le_card (X Y : Subgroup G) : X.relIndex Y ≤ Nat.card Y := by
  have h := Subgroup.card_mul_index (X.subgroupOf Y)
  have h1 : 0 < Nat.card (X.subgroupOf Y) := Nat.card_pos
  unfold Subgroup.relIndex
  nlinarith

theorem rk_le_of_comm (hG : Glob H M S) (δ : Geo H M) {y : G} (hy : y ∈ stab δ)
    {A₀ Z : Subgroup G} (hA₀ : A₀ ≤ Vn δ) (hZ : Z ≤ Vn δ)
    (h : ∀ a ∈ A₀, y * a * y⁻¹ * a⁻¹ ∈ Z) : rk δ y ≤ A₀.relIndex (Vn δ) * Nat.card Z := by
  refine (secIdx_le_of_comm (isElemAbelian_Vn' hG δ) (stab_le_normalizer_Vn δ hy)
    (stab_le_normalizer_Cb δ hy) (Cb_le_Vn δ) hA₀ hZ h).trans ?_
  exact Nat.mul_le_mul_left _ (relIndex_le_card _ _)

omit [Finite G] in
theorem comm_eq_one_of_commutator_eq_bot {X Y : Subgroup G} (h : ⁅X, Y⁆ = ⊥) {x y : G}
    (hx : x ∈ X) (hy : y ∈ Y) : y * x * y⁻¹ * x⁻¹ = 1 := by
  have h1 : ⁅y, x⁆ ∈ ⁅Y, X⁆ := Subgroup.commutator_mem_commutator hy hx
  rw [Subgroup.commutator_comm, h] at h1
  have h2 : ⁅y, x⁆ = 1 := by simpa using h1
  rwa [commutatorElement_def] at h2

omit [Finite G] in
theorem exists_zpowers_ne_bot {A B : Subgroup G} (h : ⁅A, B⁆ ≠ ⊥) :
    ∃ y ∈ B, ⁅A, Subgroup.zpowers y⁆ ≠ ⊥ := by
  by_contra hc
  push Not at hc
  refine h (le_bot_iff.mp (Subgroup.commutator_le.mpr fun a ha b hb => ?_))
  have := Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers b)
  rwa [hc b hb] at this

theorem rk_le_relIndex (hG : Glob H M S) (hp : PD δ δ')
    (h : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = ⊥) {y : G} (hy : y ∈ Vn δ') :
    rk δ y ≤ (Vn δ ⊓ Qv δ').relIndex (Vn δ) := by
  have h1 := rk_le_of_comm hG δ ((pd_Vn_le_stab hG hp).2 hy) (A₀ := Vn δ ⊓ Qv δ') (Z := ⊥)
    inf_le_left bot_le fun a ha => by
      rw [comm_eq_one_of_commutator_eq_bot h ha hy]
      exact one_mem _
  simpa using h1

theorem relIndex_Vn_le_two (hG : Glob H M S) (hirr : IrrSecSec) (hng : NG H M) (hp : PD δ δ')
    (h : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = ⊥) : (Vn δ' ⊓ Qv δ).relIndex (Vn δ') ≤ 2 := by
  have hB := isElemAbelian_Vn' hG δ'
  refine klein_le_two (quot_stab_five hG.amalg hp.vδ) (pd_Vn_le_stab hG hp).2 hB ?_
  intro g hgB hg
  by_contra hgQ
  have ho : OverInv δ g :=
    show OverIn (stab δ) g from ⟨hg, hgQ, Or.inl (by rw [hB.2 g hgB]; exact one_mem _)⟩
  have h8 := NG.rk_gt hG hirr hng hp.vδ ((pd_Vn_le_stab hG hp).2 hgB) ho
  have h4 := (rk_le_relIndex hG hp h hgB).trans (pd_relIndex hG hp).2
  omega

omit [Finite G] in
theorem comm_eq_commutator (x b : G) : x * b * x⁻¹ * b⁻¹ = ⁅x, b⁆ :=
  (commutatorElement_def x b).symm

omit [Finite G] in
theorem comm_mem_Vn {δ' : Geo H M} {x b : G} (hx : x ∈ stab δ') (hb : b ∈ Vn δ') :
    x * b * x⁻¹ * b⁻¹ ∈ Vn δ' :=
  (Vn δ').mul_mem ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ' hx) b).mp hb)
    ((Vn δ').inv_mem hb)

theorem case_n0 (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') (h : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = ⊥) (hBQ : Vn δ' ≤ Qv δ) : False := by
  obtain ⟨hAδ', hBδ⟩ := pd_Vn_le_stab hG hp
  have hA := isElemAbelian_Vn' hG δ
  have hcomm : ⁅Vn δ, Vn δ'⁆ ≤ Zv δ :=
    (Subgroup.commutator_mono le_rfl hBQ).trans (comm_Vn_Qv_le hG hp.vδ)
  have hne : ⁅Vn δ, Vn δ'⁆ ≠ ⊥ := fun h0 => pd_not_comm_le hG hp (h0 ▸ bot_le)
  obtain ⟨y, hyB, hy⟩ := exists_zpowers_ne_bot hne
  have hZeq : ⁅Vn δ, Subgroup.zpowers y⁆ = Zv δ :=
    (aon_Vn hG hp.vδ (hBQ hyB)).resolve_left hy
  have hcard : Nat.card (Zv δ) ≤ (Vn δ ⊓ Qv δ').relIndex (Vn δ) := by
    have := card_comm_le hA (stab_le_normalizer_Vn δ (hBδ hyB)) (A₀ := Vn δ ⊓ Qv δ') (Z := ⊥)
      inf_le_left bot_le fun a ha => by
        rw [comm_eq_one_of_commutator_eq_bot h ha hyB]
        exact one_mem _
    rw [hZeq] at this
    simpa using this
  have hrk : ∀ x ∈ Vn δ, rk δ' x ≤ Nat.card (Zv δ) := by
    intro x hx
    have := rk_le_of_comm hG δ' (hAδ' hx) (A₀ := Vn δ') (Z := Zv δ ⊓ Vn δ') le_rfl inf_le_right
      fun b hb => ⟨by
        rw [comm_eq_commutator]
        exact hcomm (Subgroup.commutator_mem_commutator hx hb), comm_mem_Vn (hAδ' hx) hb⟩
    rw [Subgroup.relIndex_self, one_mul] at this
    exact this.trans (Subgroup.card_le_of_le inf_le_left)
  have hle2 : (Vn δ ⊓ Qv δ').relIndex (Vn δ) ≤ 2 := by
    refine klein_le_two (quot_stab_five hG.amalg hp.vδ') hAδ' hA ?_
    intro g hgA hg
    by_contra hgQ
    have ho : OverInv δ' g :=
      show OverIn (stab δ') g from ⟨hg, hgQ, Or.inl (by rw [hA.2 g hgA]; exact one_mem _)⟩
    have h8 := NG.rk_gt hG hirr hng hp.vδ' (hAδ' hgA) ho
    have := ((hrk g hgA).trans hcard).trans (pd_relIndex hG hp).2
    omega
  obtain ⟨x, hxA, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hp.not_le
  have h4 := NG.four_le_rk hG h15 hng hp.vδ' (hAδ' hxA) hxQ
  have := ((hrk x hxA).trans hcard).trans hle2
  omega

theorem case_n1 (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') (h : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = ⊥) (hBQ : ¬ Vn δ' ≤ Qv δ) : False := by
  obtain ⟨hAδ', hBδ⟩ := pd_Vn_le_stab hG hp
  have hA := isElemAbelian_Vn' hG δ
  obtain ⟨y, hyB, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hBQ
  have hr := pd_relIndex hG hp
  have h4 := NG.four_le_rk hG h15 hng hp.vδ (hBδ hyB) hyQ
  have hy := rk_le_relIndex hG hp h hyB
  have hr4 : (Vn δ ⊓ Qv δ').relIndex (Vn δ) = 4 := by omega
  obtain ⟨x, hxA, hxo⟩ := klein_exists_over (quot_stab_five hG.amalg hp.vδ') hAδ' hA hr4
  have hB2 := relIndex_Vn_le_two hG hirr hng hp h
  obtain ⟨Z', hZ'B, hZ'c, hZ'mem⟩ : ∃ Z' : Subgroup G, Z' ≤ Vn δ' ∧ Nat.card Z' ≤ 4 ∧
      ∀ b ∈ Vn δ' ⊓ Qv δ, x * b * x⁻¹ * b⁻¹ ∈ Z' := by
    by_cases hall : ∀ y' ∈ Vn δ' ⊓ Qv δ, ⁅Vn δ, Subgroup.zpowers y'⁆ = ⊥
    · refine ⟨⊥, bot_le, by simp, fun b hb => ?_⟩
      have := Subgroup.commutator_mem_commutator hxA (Subgroup.mem_zpowers b)
      rw [hall b hb] at this
      rw [comm_eq_commutator]
      exact this
    · push Not at hall
      obtain ⟨y', hy'mem, hy'⟩ := hall
      have hZeq := (aon_Vn hG hp.vδ hy'mem.2).resolve_left hy'
      have hcard : Nat.card (Zv δ) ≤ 4 := by
        have := card_comm_le hA (stab_le_normalizer_Vn δ (hBδ hy'mem.1))
          (A₀ := Vn δ ⊓ Qv δ') (Z := ⊥) inf_le_left bot_le fun a ha => by
            rw [comm_eq_one_of_commutator_eq_bot h ha hy'mem.1]
            exact one_mem _
        rw [hZeq] at this
        simp only [Subgroup.card_bot, mul_one] at this
        omega
      refine ⟨Zv δ ⊓ Vn δ', inf_le_right, (Subgroup.card_le_of_le inf_le_left).trans hcard,
        fun b hb => ⟨?_, comm_mem_Vn (hAδ' hxA) hb.1⟩⟩
      rw [comm_eq_commutator]
      exact comm_Vn_Qv_le hG hp.vδ (Subgroup.commutator_mem_commutator hxA hb.2)
  have h8 := rk_le_of_comm hG δ' (hAδ' hxA) (A₀ := Vn δ' ⊓ Qv δ) inf_le_left hZ'B hZ'mem
  have h9 := NG.rk_gt hG hirr hng hp.vδ' (hAδ' hxA) hxo
  have := Nat.mul_le_mul hB2 hZ'c
  omega

end Case1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

theorem case1_false (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    (h : ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = ⊥) : False := by
  by_cases hBQ : Vn δ' ≤ Qv δ
  · exact Case1.case_n0 hG hirr h15 hng hp h hBQ
  · exact Case1.case_n1 hG hirr h15 hng hp h hBQ

end S34

end F53.Stellmacher

end CFSG.Quasithin
