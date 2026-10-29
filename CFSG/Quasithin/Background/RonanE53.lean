module

public import CFSG.Quasithin.Background.E3Defs
import CFSG.Quasithin.Background.VolIE54
import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin.RonanE53

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sup_thompsonJ {P C : Subgroup G} (hP : IsSylowTwoOf P ⊤)
    (hJC : thompsonJ P ≤ C) :
    C ≤ Subgroup.normalizer (thompsonJ P : Set G) ⊔ thompsonJ C := by
  have hmax : ∀ {A X : Subgroup G}, IsMaxElemAbelian P A → A ≤ X → IsMaxElemAbelian X A :=
    fun hA hAX => ⟨hAX, hA.2.1, fun B _ hB => (B6.isMaxElemAbelian_of_sylow hP hA).2.2 B le_top hB⟩
  have hJle : ∀ {X : Subgroup G}, thompsonJ P ≤ X → thompsonJ P ≤ thompsonJ X := fun hX =>
    iSup₂_le fun _ hA => B6.le_thompsonJ (hmax hA ((B6.le_thompsonJ hA).trans hX))
  obtain ⟨S, hS, hJS⟩ := A4.exists_isSylowTwoOf_ge (hJle hJC) (hP.2.1.to_le (B6.thompsonJ_le P))
  have hJS' : thompsonJ S = thompsonJ P := by
    obtain ⟨R, hR, hSR⟩ := A4.exists_isSylowTwoOf_ge (le_top : S ≤ ⊤) hS.2.1
    obtain ⟨g, -, hRg⟩ := B6.isSylowTwoOf_exists_conj hP hR
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
    have h2 : thompsonJ S ≤ thompsonJ R := iSup₂_le fun B hB => B6.le_thompsonJ
      ⟨hB.1.trans hSR, hB.2.1, fun B' _ hB' =>
        ((B6.isMaxElemAbelian_of_sylow hP hA₀).2.2 B' le_top hB').trans
          (hB.2.2 A₀ ((B6.le_thompsonJ hA₀).trans hJS) hA₀.2.1)⟩
    have h3 : Nat.card (thompsonJ R) = Nat.card (thompsonJ P) := by
      rw [hRg, B6.thompsonJ_conjSub, B6.card_conjSub]
    exact (Subgroup.eq_of_le_of_card_ge (hJle hJS) ((Subgroup.card_le_of_le h2).trans h3.le)).symm
  intro c hc
  have hcN : c ∈ Subgroup.normalizer (thompsonJ C : Set G) := B6.le_normalizer_thompsonJ C hc
  have hS' : IsSylowTwoOf (B6.conjSub c S) (thompsonJ C) := by
    have := B6.isSylowTwoOf_conjSub hS c
    rwa [B6.conjSub_eq_self hcN] at this
  obtain ⟨y, hy, hyS⟩ := B6.isSylowTwoOf_exists_conj hS hS'
  have key : B6.conjSub (y⁻¹ * c) (thompsonJ P) = thompsonJ P := by
    rw [← hJS', B6.conjSub_mul, ← B6.thompsonJ_conjSub, hyS, B6.thompsonJ_conjSub,
      ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hn : y⁻¹ * c ∈ Subgroup.normalizer (thompsonJ P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
  have e : c = y * (y⁻¹ * c) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hn)

theorem mQuot_le_one_of_card_le {D D₁ : Subgroup G} (hle : D₁ ≤ D)
    (hcard : Nat.card D ≤ 2 ^ 1 * Nat.card D₁) : E3.mQuot D D₁ ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_card D₁ D
  rw [inf_eq_left.2 hle] at h1
  have h2 : D₁.relIndex D ≤ 2 := by
    have h3 : D₁.relIndex D * Nat.card D₁ ≤ 2 * Nat.card D₁ := by
      rw [h1]; simpa using hcard
    exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  have h0 : 0 < D₁.relIndex D := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' D D₁)
  unfold E3.mQuot
  interval_cases (D₁.relIndex D) <;> simp

theorem centralizer_bot_eq_top : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
  eq_top_iff.2 fun _ _ => Subgroup.mem_centralizer_iff.2 fun x hx => by
    rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]

theorem e5_3 {P : Subgroup G} (hP : IsSylowIn 2 P ⊤) (hG : Group.IsSolvable G) :
    Subgroup.normalizer (thompsonJ P : Set G) ⊔
      (⨆ (D₁ : Subgroup G) (_ : D₁ ≤ omegaOneCenterOf (thompsonJi P 1) ∧
          E3.mQuot (omegaOneCenterOf (thompsonJi P 1)) D₁ ≤ 1),
        thompsonJ (Subgroup.centralizer (D₁ : Set G))) = ⊤ := by
  set D := omegaOneCenterOf (thompsonJi P 1) with hDdef
  set N := Subgroup.normalizer (thompsonJ P : Set G) with hNdef
  set Φ := ⨆ (D₁ : Subgroup G) (_ : D₁ ≤ D ∧ E3.mQuot D D₁ ≤ 1),
    thompsonJ (Subgroup.centralizer (D₁ : Set G)) with hΦdef
  have hC : ∀ D₁ : Subgroup G, D₁ ≤ D → E3.mQuot D D₁ ≤ 1 →
      thompsonJ P ≤ Subgroup.centralizer (D₁ : Set G) →
      Subgroup.centralizer (D₁ : Set G) ≤ N ⊔ Φ := fun D₁ h1 h2 hJ =>
    (le_normalizer_sup_thompsonJ hP hJ).trans (sup_le_sup_left
      (le_iSup₂_of_le (f := fun D₁ (_ : D₁ ≤ D ∧ E3.mQuot D D₁ ≤ 1) =>
        thompsonJ (Subgroup.centralizer (D₁ : Set G))) D₁ ⟨h1, h2⟩ le_rfl) N)
  refine eq_top_iff.2 ?_
  by_cases hm : 1 < CFSG.Open.pRank 2 P
  ·
    have hJ : thompsonJi P 1 = H13.thompsonJk 1 P := VolI.E54.thompsonJi_eq_thompsonJk hm
    have hD : D = omegaOneCenterOf (H13.thompsonJk 1 P) := by rw [hDdef, hJ]
    have hE : E1.InE 1 (⊤ : Subgroup G) := E1.inE_one_top_of_isSolvable (Nat.card G) G le_rfl hG
    rw [← E5.e5_2_centralizer (j := 1) hP hE]
    refine sup_le (inf_le_right.trans le_sup_left) (iSup₂_le fun D₁ hD₁ => inf_le_right.trans ?_)
    obtain ⟨h1, h2⟩ := hD₁
    rw [← hD] at h1 h2
    refine hC D₁ h1 (mQuot_le_one_of_card_le h1 h2) fun x hx => ?_
    have hxJ : x ∈ H13.thompsonJk 1 P :=
      (iSup₂_le fun _ hA => E5.le_thompsonJk_of_isMaxElemAbelian hA : thompsonJ P ≤ _) hx
    refine Subgroup.mem_centralizer_iff.2 fun d hd => ?_
    have hd' : d ∈ omegaOneCenterOf (H13.thompsonJk 1 P) := hD ▸ h1 hd
    exact (mem_centralizer_of_mem_omegaOneCenterOf hd' hxJ).symm
  ·
    push Not at hm
    have hD : D = ⊥ := by
      rw [hDdef, VolI.E54.thompsonJi_eq_bot_of_le hm, VolI.E54.omegaOneCenterOf_bot_eq]
    have h0 : E3.mQuot D ⊥ ≤ 1 := by rw [hD, E3.mQuot_self]; exact zero_le_one
    have := hC ⊥ bot_le h0 (by rw [centralizer_bot_eq_top]; exact le_top)
    rwa [centralizer_bot_eq_top] at this

end CFSG.Quasithin.RonanE53
