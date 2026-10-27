module

public import CFSG.Walter.W67.Statements
import CFSG.Walter.W67.Section4.Lemma42A
import CFSG.Walter.W67.Section4.Lemma42B
import CFSG.Walter.W67.Section4.Lemma42E
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Basic

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_commutator {W : Subgroup G} {g : G}
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    g ∈ Subgroup.normalizer ((⁅W, W⁆ : Subgroup G) : Set G) := by
  have hmap : W.map (MulAut.conj g).toMonoidHom = W := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · obtain ⟨w, hw, rfl⟩ := hx
      exact hg w hw
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h1 : ⁅W, W⁆.map (MulAut.conj g).toMonoidHom = ⁅W, W⁆ := by
    rw [Subgroup.map_commutator, hmap]
  refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← h1]
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_eq_self_of_odd {Q : Subgroup G} {a v : G} (hvQ : v ∈ Q) (hv2 : v * v = 1)
    (hodd : Odd (orderOf a)) (h : ∀ x ∈ Q, a * x * a⁻¹ = v * x * v⁻¹) :
    ∀ x ∈ Q, a * x * a⁻¹ = x := by
  have key : ∀ k : ℕ, ∀ x ∈ Q, a ^ k * x * (a ^ k)⁻¹ = v ^ k * x * (v ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hvx : v * x * v⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hvQ hx) (Q.inv_mem hvQ)
      calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹ = a ^ k * (a * x * a⁻¹) * (a ^ k)⁻¹ := by
            rw [pow_succ]; group
        _ = a ^ k * (v * x * v⁻¹) * (a ^ k)⁻¹ := by rw [h x hx]
        _ = v ^ k * (v * x * v⁻¹) * (v ^ k)⁻¹ := ih _ hvx
        _ = v ^ (k + 1) * x * (v ^ (k + 1))⁻¹ := by rw [pow_succ]; group
  intro x hx
  obtain ⟨m, hm⟩ := hodd
  have h1 := key (orderOf a) x hx
  rw [pow_orderOf_eq_one, hm] at h1
  have hvm : v ^ (2 * m + 1) = v := by
    rw [pow_succ, pow_mul, pow_two, hv2, one_pow, one_mul]
  rw [hvm] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  rw [h x hx, ← h1]

omit [Finite G] in
theorem commutator_self_eq_of_psl25 [Fact (Nat.Prime 5)] {Y : Subgroup G}
    (e : Y ≃* PSL(2, GaloisField 5 1)) : ⁅Y, Y⁆ = Y := by
  have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  have hPs : IsSimpleGroup PSL(2, GaloisField 5 1) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; norm_num)
  have hYs : IsSimpleGroup Y := e.isSimpleGroup
  have hY60 : Nat.card Y = 60 := by
    rw [Nat.card_congr e.toEquiv, Suzuki.card_psl2_of_card _
      (isOddPrimePower_of_card hK (by decide) one_pos) hK]
    norm_num
  have hcomm : ⁅Y, Y⁆ = (commutator Y).map Y.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [hcomm, Suzuki.commutator_eq_top_of_card_sixty hY60, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem lemma_4_2 :
    S_lemma_4_2 := by
  intro G _ _ s hp T₂ hT₂ h2 N hAV hN2
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAN : s.fr.A T₂ ≤ N := le_sup_left.trans hAV
  have hVN : s.fr.V T₂ ≤ N := le_sup_right.trans hAV
  have hV4 := s.fr.card_V hT₂ h2
  rcases s.normal_or_psl25 hp hT₂ h2 hAN hVN hN2 with hn | ⟨⟨eQ⟩, hVQ⟩
  · exact hn
  exfalso
  set WN := Subgroup.closure (conjSet N (s.fr.V T₂)) with hWN
  set QN := ⁅WN, WN⁆ with hQN
  have hAQ : QN ≤ Subgroup.centralizer (s.fr.A T₂ : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    intro a ha
    have haN : a ∈ Subgroup.normalizer (QN : Set G) :=
      mem_normalizer_commutator (conj_mem_closure_conjSet (hAN ha))
    have haV : a ∈ Subgroup.centralizer (s.fr.V T₂ : Set G) := s.A_le_centralizer_V T₂ ha
    obtain ⟨v, hv, hconj⟩ := exists_conj_eq_of_normalizes eQ hVQ hV4 haN haV
    have hfix := conj_eq_self_of_odd (hVQ hv) (s.fr.mul_self_of_mem_S (s.fr.V_le_S hT₂ hv))
      (odd_orderOf_of_mem_oddPart ha) hconj
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hfix x hx
    calc x * a = (a * x * a⁻¹) * a := by rw [this]
      _ = a * x := by group
  set M := Subgroup.centralizer (s.fr.A T₂ : Set G) with hM
  have hAM : s.fr.A T₂ ≤ M := s.A_le_centralizer_of_le hp hT₂ h2 le_rfl
  have hVM : s.fr.V T₂ ≤ M :=
    Subgroup.le_centralizer_iff.mpr (s.A_le_centralizer_V T₂)
  have hM2 := s.factorization_centralizer hp hT₂ h2 le_rfl (s.A_ne_bot hp hT₂ h2)
  rcases s.normal_or_psl25 hp hT₂ h2 hAM hVM hM2 with hnM | ⟨⟨eM⟩, hVQM⟩
  ·
    have hQs : IsSimpleGroup QN := by
      have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
      have : IsSimpleGroup PSL(2, GaloisField 5 1) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; norm_num)
      exact eQ.isSimpleGroup
    have hVn : ((s.fr.V T₂).subgroupOf QN).Normal := ⟨fun x hx q => by
      have h1 := hnM.conj_mem ⟨(x : G), hAQ x.2⟩ hx ⟨(q : G), hAQ q.2⟩
      exact h1⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((s.fr.V T₂).subgroupOf QN) with h | h
    · have := congrArg (fun H : Subgroup QN => Nat.card H) h
      simp only [Subgroup.card_bot] at this
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVQ).toEquiv, hV4] at this
      omega
    · have := congrArg (fun H : Subgroup QN => Nat.card H) h
      simp only [Subgroup.card_top] at this
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVQ).toEquiv, hV4,
        Nat.card_congr eQ.toEquiv] at this
      have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
      rw [Suzuki.card_psl2_of_card _ (isOddPrimePower_of_card hK (by decide) one_pos) hK] at this
      norm_num at this
  ·
    set WM := Subgroup.closure (conjSet M (s.fr.V T₂)) with hWM
    set QM := ⁅WM, WM⁆ with hQM
    obtain ⟨τ, hτS, hτV⟩ := s.exists_mem_S_not_mem_V hT₂ h2
    have hτA : τ ∈ Subgroup.normalizer (s.fr.A T₂ : Set G) :=
      JT.mem_normalizer_of_conj_mem fun x hx => s.fr.S_conj_mem_A hτS hx hT₂
    have hτM : τ ∈ Subgroup.normalizer (M : Set G) := normalizer_le_normalizer_centralizer _ hτA
    have hτC : τ ∈ Subgroup.centralizer (s.fr.V T₂ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        s.fr.comm_of_mem_S (s.fr.V_le_S hT₂ hv) hτS
    have hτQ : τ ∈ Subgroup.normalizer (QM : Set G) := mem_normalizer_commutator
      (mem_normalizer_closure_conjSet hτM (Subgroup.centralizer_le_normalizer _ hτC))
    obtain ⟨v, hv, hconj⟩ := exists_conj_eq_of_normalizes eM hVQM hV4 hτQ hτC
    set Js := v⁻¹ * τ with hJs
    have hJsS : Js ∈ (s.fr.S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (s.fr.V_le_S hT₂ hv)) hτS
    have hJs1 : Js ≠ 1 := by
      intro h1
      apply hτV
      have : τ = v := by
        calc τ = v * (v⁻¹ * τ) := by group
          _ = v := by rw [← hJs, h1, mul_one]
      rw [this]
      exact hv
    have hJsC : ∀ x ∈ QM, Js * x * Js⁻¹ = x := by
      intro x hx
      calc Js * x * Js⁻¹ = v⁻¹ * (τ * x * τ⁻¹) * v := by rw [hJs]; group
        _ = v⁻¹ * (v * x * v⁻¹) * v := by rw [hconj x hx]
        _ = x := by group
    obtain ⟨c, -, hcJ⟩ := s.fr.exists_conj_of_cover s.hidx hJsS hJs1
    set Y := QM.map (MulAut.conj c).toMonoidHom with hY
    have hYH : Y ≤ s.H := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hcJ]
      have h1 := hJsC x hx
      change c * x * c⁻¹ * (c * Js * c⁻¹) = c * Js * c⁻¹ * (c * x * c⁻¹)
      calc c * x * c⁻¹ * (c * Js * c⁻¹) = c * (x * Js) * c⁻¹ := by group
        _ = c * ((Js * x * Js⁻¹) * Js) * c⁻¹ := by rw [h1]
        _ = c * Js * c⁻¹ * (c * x * c⁻¹) := by group
    let eY : Y ≃* PSL(2, GaloisField 5 1) :=
      (QM.equivMapOfInjective _ (MulAut.conj c).injective).symm.trans eM
    have hYK : Y ≤ s.K := by
      rw [← commutator_self_eq_of_psl25 eY]
      exact (Subgroup.commutator_mono hYH hYH).trans s.commutator_H_le_K
    have h60 : Nat.card Y = 60 := by
      have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
      rw [Nat.card_congr eY.toEquiv, Suzuki.card_psl2_of_card _
        (isOddPrimePower_of_card hK (by decide) one_pos) hK]
      norm_num
    apply s.not_five_dvd_card_K hp
    have := Subgroup.card_dvd_of_le hYK
    rw [h60] at this
    exact (by norm_num : 5 ∣ 60).trans this

end CFSG.Walter.W67
