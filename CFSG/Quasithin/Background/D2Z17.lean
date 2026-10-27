module

public import CFSG.Quasithin.Background.D2Z16
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Z14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

section Structure

variable {X : Subgroup (MulAut V)} {r : ℚ}

theorem hall_of_D217 (h : D217Hyp X r) (hrk : ∀ B ∈ QhatStar X, 1 < rk B) :
    ∀ B ∈ QhatStar X, D214Hyp X B r := fun B hB => by
  obtain ⟨r', -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := QhatStar_spec hB
  exact D214Hyp_of_D217Hyp h hB (not_isCyclic_of_one_lt_rk hB2.isElemAbelian2 (hrk B hB))

theorem card_sup_pCoreOf {A : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1) (hA : A ∈ QhatStar X)
    (h14 : D214Hyp X A r) {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)} (d : PDecomp X Pi) :
    Nat.card ↥(pCoreOf 3 X ⊔ A) = 3 ^ s * 4 := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hn : A ≤ Subgroup.normalizer (pCoreOf 3 X : Set (MulAut V)) := fun a ha =>
    le_normalizer_pCoreOf 3 X (hA2.le ha)
  have hinf : pCoreOf 3 X ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxA⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_sq_eq_one_of_mem_pCoreOf hxP
      (hA2.isElemAbelian2.2 x hxA))
  rw [card_sup_of_normalizes hn hinf, d.card_P, h14.card_A hV]

theorem D2_22_structure (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r) {A : Subgroup (MulAut V)}
    (hA : A ∈ QhatStar X) (hrk : 1 < rk A) :
    r = 3 / 2 ∧
      ((∃ Pi : Fin 2 → Subgroup (MulAut V), PDecomp X Pi ∧ Set.range Pi = Pfam X ∧
          Case7i X A Pi ∧ X = pCoreOf 3 X ⊔ A) ∨
        (∃ Pi : Fin 3 → Subgroup (MulAut V), PDecomp X Pi ∧ Set.range Pi = Pfam X ∧
          Case7ii A Pi ∧ X = pCoreOf 3 X ⊔ A)) := by
  obtain ⟨h14A, hr, hrkall⟩ := D2_19 hV h hA hrk
  have hall := hall_of_D217 h hrkall
  have hW := fixV_pCoreOf_eq_bot hV h hall
  have hq1 : 1 < r := by rw [hr]; norm_num
  have hAX : A ≤ X := QhatStar_le hA
  refine ⟨hr, ?_⟩
  rcases D2_14_7 hV h14A with ⟨Pi, d, hrg, hc⟩ | ⟨Pi, d, hrg, hc⟩
  · refine Or.inl ⟨Pi, d, hrg, hc, ?_⟩
    obtain ⟨⟨a₀, u₀, hk, hsw, -⟩, -⟩ := hc
    have h1 := card_le_two_mul_K hrg d.injective (hAX hk.ha) hsw
    have h2 := X_card_bound hV h.qhat hq1 (by norm_num) d hW
    have h3 := card_sup_pCoreOf hV hA h14A d
    have hle : pCoreOf 3 X ⊔ A ≤ X := sup_le (pCoreOf_le 3 X) hAX
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [h3]
    omega
  · refine Or.inr ⟨Pi, d, hrg, hc, ?_⟩
    have hX3 := X_le_normalizers_of_three hV h hall d
    have h2 := X_card_bound hV h.qhat hq1 (by norm_num) d hW
    have h3 := card_sup_pCoreOf hV hA h14A d
    have hle : pCoreOf 3 X ⊔ A ≤ X := sup_le (pCoreOf_le 3 X) hAX
    have hKX : X ⊓ ⨅ j, Subgroup.normalizer (Pi j : Set (MulAut V)) = X := inf_eq_left.mpr hX3
    rw [hKX] at h2
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [h3]
    omega

end Structure

end CFSG.Quasithin
