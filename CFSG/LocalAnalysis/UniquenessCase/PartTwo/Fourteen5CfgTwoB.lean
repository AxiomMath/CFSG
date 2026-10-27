module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5CfgTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5CfgSeven
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ComponentClassification (Layer.subgroup)

variable {K : Type} [Group K] [Finite K]

theorem inf_ne_bot_of_isCyclic {p : ℕ} [Fact p.Prime] {P A B : Subgroup K} (hPc : IsCyclic ↥P)
    (hP : IsPGroup p ↥P) (hA : A ≤ P) (hB : B ≤ P) (hA1 : A ≠ ⊥) (hB1 : B ≠ ⊥) : A ⊓ B ≠ ⊥ := by
  haveI : IsCyclic ↥P := hPc
  obtain ⟨a, ha⟩ := (hP.to_le hA).exists_card_eq
  obtain ⟨b, hb⟩ := (hP.to_le hB).exists_card_eq
  have key : ∀ (A' B' : Subgroup K) (x y : ℕ), A' ≤ P → B' ≤ P →
      Nat.card A' = p ^ x → Nat.card B' = p ^ y → x ≤ y → A' ≤ B' := by
    intro A' B' x y hA' hB' hx hy hxy
    have hcardA : Nat.card (A'.subgroupOf P) = p ^ x := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA').toEquiv, hx]
    have hcardB : Nat.card (B'.subgroupOf P) = p ^ y := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB').toEquiv, hy]
    have hdvd : Nat.card (A'.subgroupOf P) ∣ Nat.card (B'.subgroupOf P) := by
      rw [hcardA, hcardB]
      exact pow_dvd_pow p hxy
    have hle : A'.subgroupOf P ≤ B'.subgroupOf P :=
      (IsCyclic.subgroup_le_iff_card_dvd (H := A'.subgroupOf P) (K := B'.subgroupOf P)).mpr hdvd
    calc A' = (A'.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hA').symm
      _ ≤ (B'.subgroupOf P).map P.subtype := Subgroup.map_mono hle
      _ = B' := Subgroup.map_subgroupOf_eq_of_le hB'
  rcases le_total a b with hab | hba
  · have hAB : A ≤ B := key A B a b hA hB ha hb hab
    rw [inf_eq_left.mpr hAB]
    exact hA1
  · have hBA : B ≤ A := key B A b a hB hA hb ha hba
    rw [inf_eq_right.mpr hBA]
    exact hB1

theorem isSylowOf_inf_of_forall {p : ℕ} [Fact p.Prime] {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) {Q : Subgroup K}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q ⊤) : CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ J₁) J₁ := by
  have hE : (J₁ ⊔ J₂ : Subgroup K).Normal := by
    rw [← layer_eq_sup_of_forall hJ₁ hJ₂ hJu]
    exact CFSG.ComponentClassification.Layer.normal K
  have hQ' : CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ (J₁ ⊔ J₂)) (J₁ ⊔ J₂) :=
    hQ.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hE).ge
  have hEN : (J₁ ⊔ J₂ : Subgroup K) ≤ normalizer (J₁ : Set K) :=
    sup_le Subgroup.le_normalizer
      ((le_centralizer_of_isComponentOf hJ₁ hJ₂ hne).trans (Subgroup.centralizer_le_normalizer _))
  have hQ'' := hQ'.inf_of_le_normalizer le_sup_left hEN
  have hJ₁inf : (J₁ ⊔ J₂) ⊓ J₁ = J₁ := inf_eq_right.mpr le_sup_left
  simpa only [inf_assoc, hJ₁inf] using hQ''

namespace Cfg145

variable {M X₁ X₂ P : Subgroup K}

theorem exists_mem_normalizer_map_eq (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂)
    (hZ : (X₁ ⊔ X₂) ⊓ J₁ ≠ X₁ ∧ (X₁ ⊔ X₂) ⊓ J₁ ≠ X₂) :
    ∃ e ∈ normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) ⊓ normalizer (P : Set K),
      J₁.map (MulAut.conj e).toMonoidHom = J₂ := by
  obtain ⟨e, he, he₁, he₂⟩ := c.exists_mem_normalizer_inf true false
  have he₁' : ∀ x ∈ X₁, e * x * e⁻¹ = x⁻¹ := by simpa using he₁
  have he₂' : ∀ x ∈ X₂, e * x * e⁻¹ = x := by simpa using he₂
  rcases map_conj_eq_or_swap hJ₁ hJ₂ hne hJu e with ⟨hm₁, _⟩ | ⟨hm₁, _⟩
  · exfalso
    have heJ₁ : e ∈ normalizer (J₁ : Set K) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := J₁) (g := e)).mpr hm₁
    have heZ : e ∈ normalizer (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K) : Set K) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨he.1, heJ₁⟩
    rcases c.eq_left_or_eq_right inf_le_left (c.card_inf_eq_three hJ₁ hJ₂ hne) heZ he₁' he₂' with
      h | h
    · exact hZ.1 h
    · exact hZ.2 h
  · exact ⟨e, he, hm₁⟩

theorem le_normalizer_inf (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) :
    P ≤ normalizer (J₁ : Set K) ⊓ normalizer (J₂ : Set K) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro x hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp c.isSylowOf_seven.isPGroup) ⟨x, hx⟩
  have hodd : Odd (orderOf x) := by
    rw [show orderOf x = 7 ^ k by simpa using hk]
    exact Odd.pow (show Odd (7 : ℕ) by norm_num)
  exact mem_normalizer_of_odd hJ₁ hJ₂ hne hJu hodd

theorem not_seven_dvd_card (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) {e : K}
    (he : J₁.map (MulAut.conj e).toMonoidHom = J₂) : ¬ 7 ∣ Nat.card J₁ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro h7
  have hcardJ₂ : Nat.card J₂ = Nat.card J₁ := by
    rw [← he, Subgroup.card_map_of_injective (MulAut.conj e).injective]
  have hA : CFSG.ABGLocalTools.IsSylowOf 7 (P ⊓ J₁) J₁ :=
    isSylowOf_inf_of_forall hJ₁ hJ₂ hne hJu c.isSylowOf_seven_top
  have hB : CFSG.ABGLocalTools.IsSylowOf 7 (P ⊓ J₂) J₂ :=
    isSylowOf_inf_of_forall hJ₂ hJ₁ hne.symm (fun J' h => (hJu J' h).symm) c.isSylowOf_seven_top
  have hAne : P ⊓ J₁ ≠ ⊥ := by
    intro hbot
    have hcard := hA.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card J₁).factorization 7 :=
      (by norm_num : Nat.Prime 7).factorization_pos_of_dvd (Nat.card_pos (α := ↥J₁)).ne' h7
    exact (one_lt_pow' (by norm_num : 1 < 7) hpos.ne').ne' hcard.symm
  have hBne : P ⊓ J₂ ≠ ⊥ := by
    intro hbot
    have hcard := hB.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card J₂).factorization 7 :=
      (by norm_num : Nat.Prime 7).factorization_pos_of_dvd (Nat.card_pos (α := ↥J₂)).ne'
        (by rw [hcardJ₂]; exact h7)
    exact (one_lt_pow' (by norm_num : 1 < 7) hpos.ne').ne' hcard.symm
  have hbot : (P ⊓ J₁) ⊓ (P ⊓ J₂) = ⊥ := by
    apply le_antisymm _ bot_le
    have hle₁ : (P ⊓ J₁) ⊓ (P ⊓ J₂) ≤ J₁ := inf_le_left.trans inf_le_right
    have hle₂ : (P ⊓ J₁) ⊓ (P ⊓ J₂) ≤ J₂ := inf_le_right.trans inf_le_right
    calc (P ⊓ J₁) ⊓ (P ⊓ J₂) ≤ J₁ ⊓ J₂ := le_inf hle₁ hle₂
      _ = ⊥ := c.inf_eq_bot_of_isComponentOf hJ₁ hJ₂ hne
  exact (inf_ne_bot_of_isCyclic (p := 7) c.isCyclic c.isSylowOf_seven.isPGroup inf_le_left
    inf_le_left hAne hBne) hbot

theorem not_le_centralizer (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) {e : K}
    (heP : e ∈ normalizer (P : Set K)) (he : J₁.map (MulAut.conj e).toMonoidHom = J₂) :
    ¬ P ≤ centralizer (J₁ : Set K) := by
  intro hPJ
  have hPJ₂ : P ≤ centralizer (J₂ : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ J₁.map (MulAut.conj e).toMonoidHom := by rw [he]; exact hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    have hzy' : e * z * e⁻¹ = y := hzy
    have hw : e⁻¹ * x * e ∈ P := (Subgroup.mem_normalizer_iff''.mp heP x).mp hx
    have hzw : z * (e⁻¹ * x * e) = (e⁻¹ * x * e) * z :=
      Subgroup.mem_centralizer_iff.mp (hPJ hw) z hz
    have hcalc : e * z * e⁻¹ * x = x * (e * z * e⁻¹) := by
      calc e * z * e⁻¹ * x = e * (z * (e⁻¹ * x * e)) * e⁻¹ := by group
        _ = e * ((e⁻¹ * x * e) * z) * e⁻¹ := by rw [hzw]
        _ = x * (e * z * e⁻¹) := by group
    rw [← hzy']
    exact hcalc
  have hle : J₁ ⊔ J₂ ≤ centralizer (P : Set K) :=
    sup_le (Subgroup.le_centralizer_iff.mpr hPJ) (Subgroup.le_centralizer_iff.mpr hPJ₂)
  have hPcent : P ≤ centralizer ((J₁ ⊔ J₂ : Subgroup K) : Set K) :=
    Subgroup.le_centralizer_iff.mpr hle
  have hPbot : P ≤ ⊥ := by
    rw [← centralizer_sup_eq_bot c hJ₁ hJ₂ hJu]
    exact hPcent
  exact c.ne_bot_seven (le_bot_iff.mp hPbot)

theorem not_nine_dvd_card (c : Cfg145 M X₁ X₂ P) {J : Subgroup K} (hJ : IsComponentOf J ⊤)
    (h3 : Nat.card ↥((X₁ ⊔ X₂) ⊓ J) = 3) : ¬ 9 ∣ Nat.card J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h9
  have hZ : ((X₁ ⊔ X₂) ⊓ J).relIndex J *
      Nat.card ↥(((X₁ ⊔ X₂) ⊓ J) ⊓ J) = Nat.card ↥J :=
    Subgroup.relIndex_mul_card ((X₁ ⊔ X₂) ⊓ J) J
  rw [inf_eq_left.mpr inf_le_right, h3] at hZ
  have hnot : ¬ 3 ∣ ((X₁ ⊔ X₂) ⊓ J).relIndex J :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp (c.isSylowOf_inf_of_isComponentOf hJ)).2.2
  obtain ⟨m, hm⟩ := h9
  have hcancel : ((X₁ ⊔ X₂) ⊓ J).relIndex J * 3 = (3 * m) * 3 := by
    rw [hZ, hm]
    ring
  have hrel : ((X₁ ⊔ X₂) ⊓ J).relIndex J = 3 * m :=
    Nat.mul_right_cancel (by norm_num : 0 < 3) hcancel
  exact hnot ⟨m, hrel⟩

theorem inf_normalizer_le (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂) :
    J₁ ⊓ normalizer (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K) : Set K) ≤ M := by
  intro n hn
  have hnJ₁ : n ∈ J₁ := hn.1
  have hnZ₁ : n ∈ normalizer (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K) : Set K) := hn.2
  have hZ₂J₂ : (((X₁ ⊔ X₂) ⊓ J₂ : Subgroup K) : Set K) ⊆ (J₂ : Set K) :=
    SetLike.coe_subset_coe.mpr inf_le_right
  have hnZ₂ : n ∈ normalizer (((X₁ ⊔ X₂) ⊓ J₂ : Subgroup K) : Set K) :=
    (Subgroup.centralizer_le_normalizer _)
      (Subgroup.centralizer_le hZ₂J₂ ((le_centralizer_of_isComponentOf hJ₂ hJ₁ hne.symm) hnJ₁))
  have hnX : n ∈ normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) := by
    rw [← c.inf_sup_inf_eq hJ₁ hJ₂ hne]
    exact Subgroup.inf_normalizer_le_normalizer_sup (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K))
      (((X₁ ⊔ X₂) ⊓ J₂ : Subgroup K)) ⟨hnZ₁, hnZ₂⟩
  exact c.normalizer_le hnX

theorem false_of_inf_ne (c : Cfg145 M X₁ X₂ P) (hKA : KSevenGen) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂)
    (hZ : (X₁ ⊔ X₂) ⊓ J₁ ≠ X₁ ∧ (X₁ ⊔ X₂) ⊓ J₁ ≠ X₂) : False := by
  obtain ⟨e, he, hemap⟩ := c.exists_mem_normalizer_map_eq hJ₁ hJ₂ hne hJu hZ
  obtain ⟨S, hS, hSM⟩ := c.exists_isSylowOf_two
  have hZ₁X : (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K) : Set K) ⊆ ((X₁ ⊔ X₂ : Subgroup K) : Set K) :=
    SetLike.coe_subset_coe.mpr inf_le_left
  have hle_cent : P ≤ centralizer (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K) : Set K) :=
    c.le_centralizer.trans (Subgroup.centralizer_le hZ₁X)
  have hgen := hKA K c.isKGroup J₁ P ((X₁ ⊔ X₂) ⊓ J₁) (S ⊓ J₁)
    (c.isSimpleGroup_of_isComponentOf hJ₁)
    (c.three_dvd_card_of_isComponentOf hJ₁)
    (c.not_nine_dvd_card hJ₁ (c.card_inf_eq_three hJ₁ hJ₂ hne))
    (c.not_seven_dvd_card hJ₁ hJ₂ hne hJu hemap)
    c.isSylowOf_seven.isPGroup
    ((c.le_normalizer_inf hJ₁ hJ₂ hne hJu).trans inf_le_left)
    (c.not_le_centralizer hJ₁ hJ₂ hJu he.2 hemap)
    (c.isSylowOf_inf_of_isComponentOf hJ₁)
    hle_cent
    (isSylowOf_inf_of_forall hJ₁ hJ₂ hne hJu hS)
  have h₁M : J₁ ⊓ normalizer (((X₁ ⊔ X₂) ⊓ J₁ : Subgroup K) : Set K) ≤ M :=
    c.inf_normalizer_le hJ₁ hJ₂ hne
  have h₂M : J₁ ⊓ centralizer (P : Set K) ≤ M :=
    inf_le_right.trans
      ((Subgroup.centralizer_le_normalizer (P : Set K)).trans c.normalizer_seven_le)
  have h₃M : S ⊓ J₁ ≤ M := inf_le_left.trans hSM
  have hJ₁M : J₁ ≤ M := hgen.trans (sup_le (sup_le h₁M h₂M) h₃M)
  have heM : e ∈ M := c.normalizer_le he.1
  have hJ₂M : J₂ ≤ M := by
    intro y hy
    rw [← hemap] at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have hzy' : e * z * e⁻¹ = y := hzy
    rw [← hzy']
    exact M.mul_mem (M.mul_mem heM (hJ₁M hz)) (M.inv_mem heM)
  exact c.false_of_sup_le hJ₁ hJ₂ hne hJu hJ₁M hJ₂M

theorem false_of_two_components (c : Cfg145 M X₁ X₂ P) (hKA : KSevenGen) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) : False := by
  by_cases hZ₁ : (X₁ ⊔ X₂) ⊓ J₁ = X₁ ∨ (X₁ ⊔ X₂) ⊓ J₁ = X₂
  · by_cases hZ₂ : (X₁ ⊔ X₂) ⊓ J₂ = X₁ ∨ (X₁ ⊔ X₂) ⊓ J₂ = X₂
    · exact c.false_of_inf_eq hJ₁ hJ₂ hne hJu hZ₁ hZ₂
    · exact c.false_of_inf_ne hKA hJ₂ hJ₁ hne.symm (fun J' h => (hJu J' h).symm)
        (not_or.mp hZ₂)
  · exact c.false_of_inf_ne hKA hJ₁ hJ₂ hne hJu (not_or.mp hZ₁)

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
