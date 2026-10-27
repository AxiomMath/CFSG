module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ConcBase
public import CFSG.Quasithin.Recognition.Stroth.Str83G5Setup
public import CFSG.Quasithin.Recognition.Stroth.Str83G5Reg
public import CFSG.Quasithin.Recognition.Stroth.Str83G5FConf


public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

private theorem qv_zero_eq' (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) : qv Q₁ Q₂ x₁ x₂ 0 = Q₁ := by
  ext y
  rw [mem_qv_iff]
  simp [trackElt, trackPar]

private theorem qv_one_eq' (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) : qv Q₁ Q₂ x₁ x₂ 1 = Q₂ := by
  ext y
  rw [mem_qv_iff]
  simp [trackElt, trackPar]

private theorem H_le_normalizer_win {P₁ P₂ H Q₁ Q₂ : Subgroup G} {x₁ x₂ : G}
    (T : TrackData P₁ P₂ H x₁ x₂) (hH₁ : H ≤ P₁) (hH₂ : H ≤ P₂)
    (hQ₁ : P₁ ≤ normalizer (Q₁ : Set G)) (hQ₂ : P₂ ≤ normalizer (Q₂ : Set G)) (a b : ℤ) :
    H ≤ normalizer (win Q₁ Q₂ x₁ x₂ a b : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, mem_win_iff]
  have hq := fun i => mem_normalizer_iff.mp (T.le_normalizer_qv hH₁ hH₂ hQ₁ hQ₂ i hh) y
  exact ⟨fun hy i h1 h2 => (hq i).mp (hy i h1 h2), fun hy i h1 h2 => (hq i).mpr (hy i h1 h2)⟩

private theorem not_mem_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 K) {d : G} {n : ℕ}
    (hd : orderOf d = 2 ^ n - 1) (hn : 2 ≤ n) : d ∉ K := by
  intro hdK
  obtain ⟨k, hk⟩ := hK ⟨d, hdK⟩
  have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (orderOf d) := by
    rw [hd]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have h2 : orderOf d = 1 :=
    Nat.Coprime.eq_one_of_dvd (hodd.coprime_two_right.pow_right k) (orderOf_dvd_of_pow_eq_one h1)
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

private theorem relIndex_of_card {Q₁ Q₂ S : Subgroup G} {q : ℕ} (hq : 0 < q)
    (h₁₂ : Q₁ ≤ normalizer (Q₂ : Set G)) (hQS : Q₁ ⊔ Q₂ = S) (hc₁ : Nat.card Q₁ = q ^ 10)
    (hc₂ : Nat.card Q₂ = q ^ 11) (hcS : Nat.card S = q ^ 12) :
    Q₁.relIndex Q₂ = q ^ 2 ∧ Q₂.relIndex Q₁ = q := by
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer h₁₂
  rw [hQS, hcS, hc₁, hc₂] at h1
  have hI : Nat.card ↥(Q₁ ⊓ Q₂) = q ^ 9 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 12)
    rw [h1]
    ring
  have h2 := relIndex_mul_card (H := Q₁) (K := Q₂)
  have h3 := relIndex_mul_card (H := Q₂) (K := Q₁)
  rw [hI, hc₂] at h2
  rw [inf_comm, hI, hc₁] at h3
  constructor
  · apply Nat.eq_of_mul_eq_mul_right (pow_pos hq 9)
    rw [h2]
    ring
  · apply Nat.eq_of_mul_eq_mul_right (pow_pos hq 9)
    rw [h3]
    ring

private theorem pCoreOf_le_pCoreOf_vertex_right {L1 L2 S : Subgroup G} (hF : Hyp111 L1 L2 S) :
    pCoreOf 2 L2 ≤ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  have hBL : bigB L1 L2 S ≤ normalizer (L2 : Set G) :=
    sup_le (sup_le hF.h2.borel_le ((F1.borelOf_le L2 S).trans le_normalizer)) hF.h2.normalizes
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L2).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 L2) (hBL.trans (normalizer_le_normalizer_pCoreOf 2 L2)))
    (pCoreOf_isPGroup 2 L2)

theorem exists_conf_of_emb {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)) (hB : bigB L1 L2 S ≤ normalizer (S : Set G))
    (hQ₁ : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10)
    (hQ₂ : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11)
    (hS : Nat.card S = (2 ^ (2 * a + 1)) ^ 12)
    (hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = S)
    (hE₁ : S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
    (hE₂ : S = (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
    {ζ : GaloisField 2 (2 * a + 1)} (hζ : orderOf ζ = 2 ^ (2 * a + 1) - 1)
    {d₁ d₂ : G} (hd₁ : d₁ ∈ borelOf L1 S) (hd₂ : d₂ ∈ borelOf L2 S) (hcomm : Commute d₁ d₂)
    (ho₁ : orderOf d₁ = 2 ^ (2 * a + 1) - 1) (ho₂ : orderOf d₂ = 2 ^ (2 * a + 1) - 1)
    {k₀ m₀ : ZMod (2 ^ (2 * a + 1) - 1)} (hk₀ : IsUnit k₀) (hm₀ : IsUnit m₀)
    (hN₁ : ∀ l ∈ L1, d₁ ^ (-m₀).val * d₂ * l * (d₁ ^ (-m₀).val * d₂)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1)
    (hN₂ : ∀ l ∈ L2, d₂ ^ (-k₀).val * d₁ * l * (d₂ ^ (-k₀).val * d₁)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ L1 ⊔ bigB L1 L2 S) (hx₁B : x₁ ∉ bigB L1 L2 S)
    (hx₂ : x₂ ∈ L2 ⊔ bigB L1 L2 S) (hx₂B : x₂ ∉ bigB L1 L2 S)
    (hx₁H : x₁ ∈ normalizer ((zpowers d₁ ⊔ zpowers d₂ : Subgroup G) : Set G))
    (hx₂H : x₂ ∈ normalizer ((zpowers d₁ ⊔ zpowers d₂ : Subgroup G) : Set G))
    (h₁₁ : x₁ * d₁ * x₁⁻¹ = d₁⁻¹) (h₁₂ : x₁ * d₂ * x₁⁻¹ = d₁ ^ (-2 * m₀).val * d₂)
    (h₂₂ : x₂ * d₂ * x₂⁻¹ = d₂⁻¹) (h₂₁ : x₂ * d₁ * x₂⁻¹ = d₂ ^ (-2 * k₀).val * d₁)
    {X₀ : Subgroup G} (hQX : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ X₀) (hXS : X₀ ≤ S)
    (hBX : bigB L1 L2 S ≤ normalizer (X₀ : Set G))
    (hsq : ∀ s ∈ S, s ∉ X₀ → s ^ 2 ∈ X₀ ∧ s ^ 2 ∉ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
    {β β' β₂ : G → GaloisField 2 (2 * a + 1)} (hβ : IsChiEmb₁ ζ d₁ X₀ S (-1) β)
    (hβ' : IsChiEmb₁ ζ d₁ (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) X₀ (-cen (2 * a + 1)) β')
    (hβ₂ : IsChiEmb₁ ζ d₂ (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) S 1 β₂) :
    ∃ c : Conf G (2 * a + 1), c.P₁ = L1 ⊔ bigB L1 L2 S ∧ c.P₂ = L2 ⊔ bigB L1 L2 S ∧
      c.Q₁ = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ∧ c.Q₂ = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  have hn : Odd (2 * a + 1) := odd_two_mul_add_one a
  have hn0 : 2 * a + 1 ≠ 0 := by omega
  have hodd : Odd (2 ^ (2 * a + 1) - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hn0⟩) odd_one
  have hBP₁ : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hBP₂ : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S := le_sup_right
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hd₁B : d₁ ∈ bigB L1 L2 S := (le_sup_left.trans le_sup_left : borelOf L1 S ≤ _) hd₁
  have hd₂B : d₂ ∈ bigB L1 L2 S := (le_sup_right.trans le_sup_left : borelOf L2 S ≤ _) hd₂
  have hHB : zpowers d₁ ⊔ zpowers d₂ ≤ bigB L1 L2 S :=
    sup_le (zpowers_le.mpr hd₁B) (zpowers_le.mpr hd₂B)
  have hN₁Q : L1 ⊔ bigB L1 L2 S ≤ normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hN₂Q : L2 ⊔ bigB L1 L2 S ≤ normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hQ₁S : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := le_sup_left.trans hQS.le
  have hQ₂S : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S := le_sup_right.trans hQS.le
  have hSN₁ : S ≤ normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) := (hSB.trans hBP₁).trans hN₁Q
  have hSN₂ : S ≤ normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) := (hSB.trans hBP₂).trans hN₂Q
  have hHN₁ : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
    (hHB.trans hBP₁).trans hN₁Q
  have hHN₂ : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) :=
    (hHB.trans hBP₂).trans hN₂Q
  have hr := relIndex_of_card (Nat.two_pow_pos _) (hQ₁S.trans hSN₂) hQS hQ₁ hQ₂ hS
  have hd₁O : d₁ ∉ pCoreOf 2 L1 := not_mem_of_isPGroup (pCoreOf_isPGroup 2 L1) ho₁ (by omega)
  have hd₂O : d₂ ∉ pCoreOf 2 L2 := not_mem_of_isPGroup (pCoreOf_isPGroup 2 L2) ho₂ (by omega)
  have T : TrackData (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) (zpowers d₁ ⊔ zpowers d₂) x₁ x₂ :=
    trackData_bigB hF ha hSz (by omega) hL2 hHB (mem_sup_left (mem_zpowers d₁))
      (F1.borelOf_le L1 S hd₁) hd₁O (mem_sup_right (mem_zpowers d₂)) (F1.borelOf_le L2 S hd₂) hd₂O
      hx₁ hx₁B hx₁H hx₂ hx₂B hx₂H
  have hHW := H_le_normalizer_win T (hHB.trans hBP₁) (hHB.trans hBP₂) hN₁Q hN₂Q
  have hpow₁ : d₁ ^ (2 ^ (2 * a + 1) - 1) = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one d₁
  have hpow₂ : d₂ ^ (2 ^ (2 * a + 1) - 1) = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one d₂
  have htriv₁ : ∀ s ∈ S, d₁ ^ (-m₀).val * d₂ * s * (d₁ ^ (-m₀).val * d₂)⁻¹ * s⁻¹ ∈
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
    commutator_mem_of_trivial hE₁ hSN₁ hF.pCoreOf_le_pCoreOf_vertex
      (hN₁Q (hBP₁ (mul_mem (pow_mem hd₁B _) hd₂B))) hN₁
  have htriv₂ : ∀ s ∈ S, d₂ ^ (-k₀).val * d₁ * s * (d₂ ^ (-k₀).val * d₁)⁻¹ * s⁻¹ ∈
      pCoreOf 2 (L2 ⊔ bigB L1 L2 S) :=
    commutator_mem_of_trivial hE₂ hSN₂ (pCoreOf_le_pCoreOf_vertex_right hF)
      (hN₂Q (hBP₂ (mul_mem (pow_mem hd₂B _) hd₁B))) hN₂
  have eS : IsChiEmb ζ d₁ d₂ X₀ S ((-1 : ZMod (2 ^ (2 * a + 1) - 1)) • psi m₀) β := by
    have h := hβ.toIsChiEmb hn0 hζ (hB hd₁B) hXS hpow₁ (d₂ := d₂) (m := m₀)
      fun s hs => hQX (htriv₁ s hs)
    have hl : (-1 : ZMod (2 ^ (2 * a + 1) - 1)) • psi m₀ = (-1, m₀ * -1) := by
      ext <;> simp [psi]
    rw [hl]
    exact h
  have eX : IsChiEmb ζ d₁ d₂ (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) X₀
      (cen (2 * a + 1) • (-1 : ZMod (2 ^ (2 * a + 1) - 1)) • psi m₀) β' := by
    have h := hβ'.toIsChiEmb hn0 hζ (hBX hd₁B) hQX hpow₁ (d₂ := d₂) (m := m₀)
      fun s hs => htriv₁ s (hXS hs)
    have hl : cen (2 * a + 1) • (-1 : ZMod (2 ^ (2 * a + 1) - 1)) • psi m₀ =
        (-cen (2 * a + 1), m₀ * -cen (2 * a + 1)) := by
      ext <;> simp [psi] <;> ring
    rw [hl]
    exact h
  have eL : IsChiEmb ζ d₁ d₂ (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) S (chi k₀) β₂ := by
    have h := hβ₂.toIsChiEmb' hn0 hζ (hB hd₂B) hQ₂S hpow₂ (d₁ := d₁) (m := k₀) htriv₂
    have hl : chi k₀ = (k₀ * 1, 1) := by simp [chi]
    rw [hl]
    exact h
  obtain ⟨hfA, hfB, hfC⟩ := G5F.conf_fix_of_gen hF ha hSz hB hQ₁ hd₁ (hBP₁ hd₂B)
    (by rw [ho₁]; exact hodd) (by rw [ho₂]; exact hodd) hcomm hN₁
  refine ⟨
    { P₁ := L1 ⊔ bigB L1 L2 S, P₂ := L2 ⊔ bigB L1 L2 S, Q₁ := pCoreOf 2 (L1 ⊔ bigB L1 L2 S),
      Q₂ := pCoreOf 2 (L2 ⊔ bigB L1 L2 S), H := zpowers d₁ ⊔ zpowers d₂, x₁ := x₁, x₂ := x₂,
      d₁ := d₁, d₂ := d₂, ζ := ζ, k₀ := k₀, m₀ := m₀, odd := hn, three_le := by omega,
      track := T, le_normalizer₁ := hN₁Q, le_normalizer₂ := hN₂Q, H_le₁ := hHB.trans hBP₁,
      H_le₂ := hHB.trans hBP₂, isPGroup₁ := pCoreOf_isPGroup 2 _,
      isPGroup₂ := pCoreOf_isPGroup 2 _, card₁ := hQ₁, card₂ := hQ₂, relIndex₁ := hr.1,
      relIndex₂ := hr.2, H_eq := rfl, commute := hcomm, orderOf₁ := ho₁, orderOf₂ := ho₂,
      orderOf_ζ := hζ, conj₁₁ := h₁₁, conj₁₂ := h₁₂, conj₂₂ := h₂₂, conj₂₁ := h₂₁,
      isUnit_k₀ := hk₀, isUnit_m₀ := hm₀, baseS := ?_, baseL := ?_, fixA := hfA, fixB := hfB,
      fixC := hfC },
    rfl, rfl, rfl, rfl⟩
  · intro m hm
    have hY : win (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) x₁ x₂ 1 m ≤ S :=
      (win_le_qv le_rfl (by omega)).trans ((qv_one_eq' _ _ _ _).le.trans hQ₂S)
    obtain ⟨d, hd, hidx, l, hl, hfac⟩ := baseS_of_emb hn hζ (k₀ := k₀) hQX hXS hsq eS eX hSN₁
      (hSB.trans hBX) hHN₁ (hHB.trans hBX) hY (hHW 1 m)
    have hw := win_sub_one_left (Q₁ := pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
      (Q₂ := pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) (x₁ := x₁) (x₂ := x₂) (a := 1) (b := m) (by omega)
    rw [sub_self, qv_zero_eq'] at hw
    refine ⟨d, hd, ?_, l, ?_, hfac⟩
    · rw [dropS, qv_zero_eq']
      exact hidx
    · rw [hw]
      exact hl
  · intro m hm
    have hY : win (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) x₁ x₂ (1 - m) 0 ≤
        S :=
      (win_le_qv (by omega) le_rfl).trans ((qv_zero_eq' _ _ _ _).le.trans hQ₁S)
    obtain ⟨d, hd, hidx, l, hl, hfac⟩ := baseL_of_emb (m₀ := m₀) hn0 hζ hk₀ eL hSN₂ hHN₂ hY
      (hHW (1 - m) 0)
    have hw := win_add_one_right (Q₁ := pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
      (Q₂ := pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) (x₁ := x₁) (x₂ := x₂) (a := 1 - m) (b := 0)
      (by omega)
    rw [zero_add, qv_one_eq'] at hw
    refine ⟨d, hd, ?_, l, ?_, hfac⟩
    · rw [dropL, qv_one_eq']
      exact hidx
    · rw [hw]
      exact hl

end CFSG.Quasithin.Stroth.G5

end
