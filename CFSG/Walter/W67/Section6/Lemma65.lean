module

public import CFSG.Walter.W67.Section6.Core65C
public import CFSG.Walter.W67.Section6.Lemma64

public section

namespace CFSG.Walter.W67

namespace Sec65

open Sec6

variable {G : Type} [Group G] [Finite G] {s : Std G}

theorem exists_hyp65
    (σ : Sol s) (hreal : ∀ x y : G, orderOf x = 7 → y * x * y⁻¹ ≠ x⁻¹)
    (h3 : ∀ P : Sylow 3 G, IsElementaryAbelian 3 (P : Subgroup G)) :
    ∃ e u ρ : G, Hyp65 G e u ρ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he, hgen, he7⟩ := σ.exists_gen
  set L := s.L s.fr.E with hL
  obtain ⟨⟨u, huL⟩, huo⟩ := exists_prime_orderOf_dvd_card' (G := L) 7
    (by rw [σ.L168.card_L]; norm_num)
  rw [Subgroup.orderOf_mk] at huo
  obtain ⟨ρ, hρL, hρo, hρN, hρu⟩ := σ.L168.exists_three huL huo
  have hLC : L ≤ Subgroup.centralizer (s.fr.E : Set G) := L_le_centralizer s le_rfl s.E_ne_bot
  have hcomm : ∀ l ∈ L, e * l = l * e := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hLC hl) e he
  have hNC := Sol.normalizer_eq_centralizer (s := s)
  have hCe : Subgroup.centralizer ({e} : Set G) = Subgroup.normalizer (s.fr.E : Set G) := by
    rw [hNC, ← hgen, Sec52.centralizer_zpowers_eq]
  refine ⟨e, u, ρ, ⟨s.perfect, he7, huo, hρo, hcomm u huL, hcomm ρ hρL, hρN, hρu, ?_, ?_, ?_, ?_,
    hreal, ?_, ?_⟩⟩
  ·
    intro g hge hgu
    have hgN : g ∈ Subgroup.normalizer (s.fr.E : Set G) := by
      rw [← hCe]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hge
    obtain ⟨l, hl, a, ha, rfl, -⟩ := Sol.decomp hgN
    have hau : a * u = u * a := Subgroup.mem_centralizer_iff.mp (hLC huL) a ha
    have hlu : l * u = u * l := by
      have h1 : l * u * a = u * l * a := by
        rw [mul_assoc l u a, ← hau, ← mul_assoc, hgu, mul_assoc]
      exact mul_right_cancel h1
    have hlU : l ∈ Subgroup.zpowers u := by
      rw [← σ.L168.inf_centralizer_eq huL huo]
      exact Subgroup.mem_inf.mpr ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hlu⟩
    rw [← hgen] at ha
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlU) (Subgroup.mem_sup_left ha)
  ·
    rw [hgen, hNC]
  ·
    intro Q hQ hQC
    rw [hCe] at hQC
    have hdvd := Subgroup.card_dvd_of_le hQC
    rw [σ.card_normalizer_E] at hdvd
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk] at hdvd ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have : 7 ^ 3 ∣ 7 ^ k := pow_dvd_pow 7 (by omega)
      have := this.trans hdvd
      norm_num at this
    exact Nat.pow_le_pow_right (by norm_num) hk2
  ·
    intro Q hQ hQC
    exact σ.card_three_le hgen hQ hQC
  ·
    intro T hT a ha b hb
    obtain ⟨P, hP⟩ := hT.exists_le_sylow
    have hPa := h3 P
    exact congrArg Subtype.val (hPa.toIsMulCommutative.is_comm.comm ⟨a, hP ha⟩ ⟨b, hP hb⟩)
  ·
    intro R hR
    rw [hgen]
    exact σ.centralizer_three hR

end Sec65

open Sec6 in
theorem lemma_6_5_of
    (h64 : S_lemma_6_4) : S_lemma_6_5 := by
  intro G _ _ s _ hR r _ hr P₀ hP₀E _ hfac hsol
  have hΩE : omega1 r P₀ ≤ s.fr.E := by
    rw [omega1, Subgroup.closure_le]
    exact fun x hx => hP₀E hx.1
  have hΩ1 : omega1 r P₀ ≠ ⊥ := by
    have hrE := ((mem_sigma_iff s).mp hr).2
    have hrP : r ∣ Nat.card P₀ := by
      have h1 : 1 ≤ (Nat.card s.fr.E).factorization r :=
        (Nat.Prime.dvd_iff_one_le_factorization Fact.out Nat.card_pos.ne').mp hrE
      rw [← hfac] at h1
      exact (Nat.Prime.dvd_iff_one_le_factorization Fact.out Nat.card_pos.ne').mpr h1
    obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := P₀) r hrP
    rw [Subgroup.orderOf_mk] at hxo
    intro hbot
    have hxΩ : x ∈ omega1 r P₀ := by
      rw [omega1]
      exact Subgroup.subset_closure ⟨hx, by rw [← hxo, pow_orderOf_eq_one]⟩
    rw [hbot, Subgroup.mem_bot] at hxΩ
    rw [hxΩ, orderOf_one] at hxo
    exact (Fact.out : r.Prime).one_lt.ne hxo
  obtain ⟨-, -, hreal, hsyl⟩ := h64 G s hR hΩE hΩ1 hsol
  obtain ⟨-, ⟨σ⟩⟩ := nonempty_sol s prop_5_6
    (lemma_5_7_of lemma_2_6_i IsJRSubgroup.nonempty_jrGroup prop_5_6) hR hΩE hΩ1 hsol
  obtain ⟨e, u, ρ, h⟩ := Sec65.exists_hyp65 σ hreal fun P => (hsyl P).1
  exact h.false_of_hyp65

theorem lemma_6_5 :
    S_lemma_6_5 :=
  lemma_6_5_of lemma_6_4

end CFSG.Walter.W67
