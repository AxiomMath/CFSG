module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem card_sup_mul_card_inf_aux {H K : Subgroup Q}
    (hHK : H ≤ Subgroup.normalizer (K : Set Q)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK
  have hq : Nat.card (↥(H ⊔ K) ⧸ K.subgroupOf (H ⊔ K)) = Nat.card (↥H ⧸ K.subgroupOf H) :=
    (Nat.card_congr e.toEquiv).symm
  have hs : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toEquiv
  have hs' : Nat.card (K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_left K H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K)), hs, hq,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf H), hs']
  ring

omit [Finite Q] in
private theorem le_normalizer_of_commutator_eq_bot_aux {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥) :
    J₁ ≤ Subgroup.normalizer (J₂ : Set Q) :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJ).trans
    (Subgroup.centralizer_le_normalizer _)

omit [Finite Q] in
private theorem sup_le_normalizer_left_aux {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥) :
    J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₁ : Set Q) :=
  sup_le Subgroup.le_normalizer
    (le_normalizer_of_commutator_eq_bot_aux (by rw [Subgroup.commutator_comm, hJ]))

omit [Finite Q] in
private theorem sup_le_normalizer_right_aux {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥) :
    J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₂ : Set Q) :=
  sup_le (le_normalizer_of_commutator_eq_bot_aux hJ) Subgroup.le_normalizer

omit [Finite Q] in
private theorem exists_mul_of_mem_sup_aux {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥) {g : Q}
    (hg : g ∈ J₁ ⊔ J₂) : ∃ y ∈ J₁, ∃ v ∈ J₂, g = y * v := by
  have h : g ∈ ((J₁ ⊔ J₂ : Subgroup Q) : Set Q) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left J₁ J₂
    (le_normalizer_of_commutator_eq_bot_aux (by rw [Subgroup.commutator_comm, hJ]))] at h
  obtain ⟨y, hy, v, hv, rfl⟩ := h
  exact ⟨y, hy, v, hv, rfl⟩

omit [Finite Q] in
private theorem commutator_mem_inf_aux {W X : Subgroup Q} {w u : Q} (hw : w ∈ W) (hu : u ∈ X)
    (hwX : w ∈ Subgroup.normalizer (X : Set Q)) (huW : u ∈ Subgroup.normalizer (W : Set Q)) :
    ⁅w, u⁆ ∈ W ⊓ X := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : ⁅w, u⁆ = w * (u * w⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    rw [h1]
    exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp huW _).mp (W.inv_mem hw))
  · rw [commutatorElement_def]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hwX _).mp hu) (X.inv_mem hu)

omit [Finite Q] in
private theorem le_right_of_inf_le_centerIn_aux {J₁ J₂ W : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (hZ : J₁ ⊓ J₂ = Sec14.Item148PtRes.centerIn J₁)
    (e : ↥J₁ ⧸ Subgroup.center ↥J₁ ≃* alternatingGroup (Fin 6))
    (hW : W ≤ J₁ ⊔ J₂) (hWn : J₁ ⊔ J₂ ≤ Subgroup.normalizer (W : Set Q))
    (hA : W ⊓ J₁ ≤ Sec14.Item148PtRes.centerIn J₁) : W ≤ J₂ := by
  intro w hw
  obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_of_mem_sup_aux hJ (hW hw)
  have hyZ : y ∈ Sec14.Item148PtRes.centerIn J₁ := by
    refine Sec14.Item148PtRes.mem_centerIn_of_commutator_mem e hy fun u hu => ?_
    have hvu : u * v = v * u := Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ hu hv
    have h1 : ⁅y, u⁆ = ⁅y * v, u⁆ := by
      simp only [commutatorElement_def]
      calc y * u * y⁻¹ * u⁻¹ = y * (u * v) * v⁻¹ * y⁻¹ * u⁻¹ := by group
        _ = y * (v * u) * v⁻¹ * y⁻¹ * u⁻¹ := by rw [hvu]
        _ = y * v * u * (y * v)⁻¹ * u⁻¹ := by group
    rw [h1]
    exact hA (commutator_mem_inf_aux hw hu (sup_le_normalizer_left_aux hJ (hW hw))
      (hWn (Subgroup.mem_sup_left hu)))
  rw [← hZ] at hyZ
  exact J₂.mul_mem hyZ.2 hv

omit [Finite Q] in
private theorem le_sup_of_cover_aux {X W Z : Subgroup Q}
    (hZ : Sec14.Item148PtRes.centerIn X ≤ Z)
    (h : ∀ y ∈ X, ∃ w ∈ W ⊓ X, w⁻¹ * y ∈ Sec14.Item148PtRes.centerIn X) : X ≤ Z ⊔ W := by
  intro y hy
  obtain ⟨w, hw, hc⟩ := h y hy
  have h1 : y = w * (w⁻¹ * y) := by group
  rw [h1]
  exact mul_mem (Subgroup.mem_sup_right hw.1) (Subgroup.mem_sup_left (hZ hc))

theorem eq_or_eq_of_le_normalizer {J₁ J₂ W : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6))) (hW : W ≤ J₁ ⊔ J₂)
    (hWn : J₁ ⊔ J₂ ≤ Subgroup.normalizer (W : Set Q)) (hWc : Nat.card W = 1080) :
    W = J₁ ∨ W = J₂ := by
  have hc₁ := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₁
  have hc₂ := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₂
  obtain ⟨hZ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨hZ₂, ⟨e₂⟩⟩ := hT₂
  have hJ' : ⁅J₂, J₁⁆ = ⊥ := by rw [Subgroup.commutator_comm, hJ]
  have hU₁ := Sec14.Item148PtRes.inf_eq_centerIn_left hJ h3 hZ₁
  have hU₂ := Sec14.Item148PtRes.inf_eq_centerIn_right hJ h3 hZ₂
  have hn₁ : J₁ ≤ Subgroup.normalizer (W : Set Q) := le_sup_left.trans hWn
  have hn₂ : J₂ ≤ Subgroup.normalizer (W : Set Q) := le_sup_right.trans hWn
  rcases Sec14.Item148PtRes.inf_le_centerIn_or e₁ hn₁ with hA | hA
  · right
    exact Subgroup.eq_of_le_of_card_ge (le_right_of_inf_le_centerIn_aux hJ hU₁ e₁ hW hWn hA)
      (by rw [hWc, hc₂])
  · rcases Sec14.Item148PtRes.inf_le_centerIn_or e₂ hn₂ with hB | hB
    · left
      refine Subgroup.eq_of_le_of_card_ge
        (le_right_of_inf_le_centerIn_aux hJ' (by rwa [inf_comm]) e₂ (by rwa [sup_comm])
          (by rwa [sup_comm]) hB) (by rw [hWc, hc₁])
    · exfalso
      have hsup : J₁ ⊔ J₂ ≤ (J₁ ⊓ J₂) ⊔ W :=
        sup_le (le_sup_of_cover_aux hU₁.ge hA) (le_sup_of_cover_aux hU₂.ge hB)
      have h1 := card_sup_mul_card_inf_aux (le_normalizer_of_commutator_eq_bot_aux hJ)
      have h2 := card_sup_mul_card_inf_aux
        (show J₁ ⊓ J₂ ≤ Subgroup.normalizer (W : Set Q) from inf_le_left.trans hn₁)
      have h4 := Subgroup.card_le_of_le hsup
      have h5 : 0 < Nat.card ↥((J₁ ⊓ J₂) ⊓ W) := Nat.card_pos
      have h6 := Nat.le_mul_of_pos_right (Nat.card ↥((J₁ ⊓ J₂) ⊔ W)) h5
      rw [h3, hc₁, hc₂] at h1
      rw [h3, hWc] at h2
      omega

private theorem map_eq_of_pow_three_aux {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6))) {σ : MulAut Q} (hσ3 : σ ^ 3 = 1)
    (hσ : (J₁ ⊔ J₂).map σ.toMonoidHom = J₁ ⊔ J₂) :
    J₁.map σ.toMonoidHom = J₁ ∧ J₂.map σ.toMonoidHom = J₂ := by
  have hc₁ := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₁
  have hc₂ := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₂
  have hne : J₁ ≠ J₂ := by
    intro h
    rw [h, inf_idem, hc₂] at h3
    norm_num at h3
  have hinj : ∀ W W' : Subgroup Q, W.map σ.toMonoidHom = W'.map σ.toMonoidHom → W = W' :=
    fun W W' h => Subgroup.map_injective σ.injective h
  have hW : ∀ J : Subgroup Q, J ≤ J₁ ⊔ J₂ → J₁ ⊔ J₂ ≤ Subgroup.normalizer (J : Set Q) →
      Nat.card J = 1080 → J.map σ.toMonoidHom = J₁ ∨ J.map σ.toMonoidHom = J₂ := by
    intro J hJle hJn hJc
    refine eq_or_eq_of_le_normalizer hJ h3 hT₁ hT₂ ?_ ?_
      (by rw [Subgroup.card_map_of_injective σ.injective, hJc])
    · exact (Subgroup.map_mono hJle).trans hσ.le
    · calc J₁ ⊔ J₂ = (J₁ ⊔ J₂).map σ.toMonoidHom := hσ.symm
        _ ≤ (Subgroup.normalizer (J : Set Q)).map σ.toMonoidHom := Subgroup.map_mono hJn
        _ ≤ Subgroup.normalizer ((J.map σ.toMonoidHom : Subgroup Q) : Set Q) :=
          Subgroup.le_normalizer_map _
  have hW₁ := hW J₁ le_sup_left (sup_le_normalizer_left_aux hJ) hc₁
  have hW₂ := hW J₂ le_sup_right (sup_le_normalizer_right_aux hJ) hc₂
  have key : ∀ W : Subgroup Q,
      ((W.map σ.toMonoidHom).map σ.toMonoidHom).map σ.toMonoidHom = W := by
    intro W
    have h : (σ.toMonoidHom.comp σ.toMonoidHom).comp σ.toMonoidHom = MonoidHom.id Q := by
      have h5 : (σ ^ 3).toMonoidHom = (σ.toMonoidHom.comp σ.toMonoidHom).comp σ.toMonoidHom := rfl
      rw [← h5, hσ3]
      rfl
    rw [Subgroup.map_map, Subgroup.map_map, h, Subgroup.map_id]
  rcases hW₁ with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases hW₂ with h2 | h2
    · exact absurd (hinj J₂ J₁ (h2.trans h1.symm)) hne.symm
    · exact h2
  · exfalso
    rcases hW₂ with h2 | h2
    · have h4 := key J₁
      rw [h1, h2, h1] at h4
      exact hne h4.symm
    · exact hne (hinj J₁ J₂ (h1.trans h2.symm))

theorem normalizes_of_pow_three {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6))) {a : Q} (ha3 : a ^ 3 = 1)
    (ha : a ∈ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q)) :
    a ∈ Subgroup.normalizer (J₁ : Set Q) ∧ a ∈ Subgroup.normalizer (J₂ : Set Q) := by
  have hσ3 : (MulAut.conj a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  obtain ⟨h1, h2⟩ := map_eq_of_pow_three_aux hJ h3 hT₁ hT₂ hσ3
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp ha)
  exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
