module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBasic
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBenderA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.GH74.Uniqueness.Bender
open Subgroup

variable {K : Type*} [Group K] [Finite K]

theorem not_mem_borel_of_sup_eq_top {q i e : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q i e P t) {g₀ : K}
    (hsup : rootCenter P ⊔ conjSubgroup (rootCenter P) g₀ = ⊤) : g₀ ∉ borel P := by
  intro hg₀
  have hconj : conjSubgroup (rootCenter P) g₀ = rootCenter P := by
    show CFSG.conjugate (rootCenter P) g₀ = rootCenter P
    rw [← rootCenter_conjugate, conjugate_eq_of_mem_borel hg₀]
  have htop : rootCenter P = ⊤ := by
    rw [hconj, sup_idem] at hsup
    exact hsup
  have hPtop : P = ⊤ := eq_top_iff.mpr (htop ▸ rootCenter_le P)
  exact hc.not_mem (by rw [hPtop]; exact Subgroup.mem_set_normalizer_iff.mpr (fun n => by simp))

theorem card_cartan_eq_card_rootCenter_sub_one {q i : ℕ} {P : Subgroup K} {s : K}
    (hc : BenderCore q i 1 P s) : Nat.card (cartan P s) = Nat.card (rootCenter P) - 1 := by
  rw [hc.card_cartan, mul_one, hc.card_center]

theorem cartan_le_normalizer_rootCenter (P : Subgroup K) (s : K) :
    cartan P s ≤ normalizer (rootCenter P : Set K) :=
  (cartan_le_borel P s).trans (borel_le_normalizer_rootCenter P)

theorem cartan_le_normalizer_conjSubgroup_rootCenter {P : Subgroup K} {s g₀ : K}
    (hPs : CFSG.conjugate P s = CFSG.conjugate P g₀) :
    cartan P s ≤ normalizer (conjSubgroup (rootCenter P) g₀ : Set K) := by
  have hconj : conjSubgroup (rootCenter P) g₀ = rootCenter (CFSG.conjugate P s) := by
    show CFSG.conjugate (rootCenter P) g₀ = rootCenter (CFSG.conjugate P s)
    rw [← rootCenter_conjugate, hPs]
  rw [hconj]
  calc cartan P s ≤ CFSG.conjugate (borel P) s := inf_le_right
    _ = borel (CFSG.conjugate P s) := conjugate_borel P s
    _ ≤ normalizer (rootCenter (CFSG.conjugate P s) : Set K) := borel_le_normalizer_rootCenter _

theorem exists_mem_cartan_conj_eq {q i e : ℕ} {P : Subgroup K} {s : K}
    (hc : BenderCore q i e P s) {a b : K} (ha : a ∈ rootCenter P) (ha1 : a ≠ 1)
    (hb : b ∈ rootCenter P) (hb1 : b ≠ 1) : ∃ d ∈ cartan P s, d * a * d⁻¹ = b := by
  obtain ⟨d, hd, hdb⟩ := hc.exists_cartan_conj ha ha1 hb hb1
  exact ⟨d⁻¹, (cartan P s).inv_mem hd, by rw [inv_inv]; exact hdb.symm⟩

theorem eq_one_of_mem_cartan_of_conj_eq {q i : ℕ} {P : Subgroup K} {s : K}
    (hc : BenderCore q i 1 P s) {d a : K} (hd : d ∈ cartan P s) (ha : a ∈ rootCenter P)
    (ha1 : a ≠ 1) (hda : d * a * d⁻¹ = a) : d = 1 := by
  have hmem : d ∈ cartan P s ⊓ centralizer ({a} : Set K) := by
    refine Subgroup.mem_inf.mpr ⟨hd, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * a = (d * a * d⁻¹) * d := by group
      _ = a * d := by rw [hda]
  have hcard := hc.card_cartan_inf_centralizer ha ha1
  exact Subgroup.mem_bot.mp ((Subgroup.card_eq_one.mp hcard) ▸ hmem)

theorem exists_eq_mul_of_mem_cartan {r i : ℕ}
    (h : BenderType K r i 1) {P : Sylow 2 K} {s : K}
    (hc : BenderCore (2 ^ r) i 1 (P : Subgroup K) s) {g₀ : K}
    (hg₀ : g₀ ∉ borel (P : Subgroup K))
    (hPs : CFSG.conjugate (P : Subgroup K) s = CFSG.conjugate (P : Subgroup K) g₀) {d : K}
    (hd : d ∈ cartan (P : Subgroup K) s) (hd1 : d ≠ 1) :
    ∃ c : K, ∃ s₁ ∈ conjSubgroup (rootCenter (P : Subgroup K)) c,
      ∃ s₂ ∈ conjSubgroup (conjSubgroup (rootCenter (P : Subgroup K)) g₀) c,
        s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ d = s₁ * s₂ := by
  have hsd : s * d * s = d⁻¹ := mul_mul_eq_inv_of_mem_cartan hc hd
  have hs2 : s * s = 1 := hc.sq_eq_one
  have hd_borel : d ∈ borel (P : Subgroup K) := cartan_le_borel _ _ hd
  have hs1 : s ≠ 1 := fun h1 =>
    hc.not_mem (by rw [h1]; exact (CFSG.GH74.Uniqueness.Bender.borel _).one_mem)
  have hu1_sq : (d * s) * (d * s) = 1 := by
    rw [show (d * s) * (d * s) = d * (s * d * s) by group, hsd, mul_inv_cancel]
  have hu1_ne : d * s ≠ 1 := by
    intro h1
    apply hc.not_mem
    rw [eq_inv_of_mul_eq_one_right h1]
    exact (CFSG.GH74.Uniqueness.Bender.borel _).inv_mem hd_borel
  obtain ⟨S₁, hS₁⟩ := exists_sylow_mem_rootCenter_of_benderType h hu1_sq
  obtain ⟨S₂, hS₂⟩ := exists_sylow_mem_rootCenter_of_benderType h hs2
  have hSne : S₁ ≠ S₂ := by
    intro hEq
    have hdS₁ : d ∈ (S₁ : Subgroup K) := by
      have hu1S : d * s ∈ (S₁ : Subgroup K) := rootCenter_le _ hS₁
      have hsS : s ∈ (S₁ : Subgroup K) := by
        rw [hEq]; exact rootCenter_le _ hS₂
      have hd_eq : d = (d * s) * s⁻¹ := by group
      rw [hd_eq]
      exact (S₁ : Subgroup K).mul_mem hu1S ((S₁ : Subgroup K).inv_mem hsS)
    obtain ⟨k, hk⟩ := S₁.isPGroup' ⟨d, hdS₁⟩
    have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd2 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hodd : Odd (orderOf d) :=
      Odd.of_dvd_nat hc.odd_card_cartan
        (Subgroup.orderOf_dvd_natCard (cartan (P : Subgroup K) s) hd)
    have hcop : (orderOf d).Coprime (2 ^ k) := hodd.coprime_two_right.pow_right k
    exact hd1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd2))
  obtain ⟨c, hc₁, hc₂⟩ := exists_conjugate_eq_conjugate_eq_of_benderCore hc hg₀ hSne
  have hmem1 : d * s ∈ conjSubgroup (rootCenter (P : Subgroup K)) c := by
    have h' := hS₁
    rw [← hc₁, rootCenter_conjugate] at h'
    exact h'
  have hmem2 : s ∈ conjSubgroup (conjSubgroup (rootCenter (P : Subgroup K)) g₀) c := by
    have h' := hS₂
    rw [← hc₂, rootCenter_conjugate, rootCenter_conjugate] at h'
    exact h'
  exact ⟨c, d * s, hmem1, s, hmem2, hu1_ne, hs1, by rw [mul_assoc, hs2, mul_one]⟩

theorem torusData_cartan {r i : ℕ} (h : BenderType K r i 1)
    {P : Sylow 2 K} {s : K} (hc : BenderCore (2 ^ r) i 1 (P : Subgroup K) s) {g₀ : K}
    (hg₀ : g₀ ∉ borel (P : Subgroup K))
    (hPs : CFSG.conjugate (P : Subgroup K) s = CFSG.conjugate (P : Subgroup K) g₀) :
    TorusData (rootCenter (P : Subgroup K)) g₀ (cartan (P : Subgroup K) s) := by
  refine ⟨hc.isCyclic, card_cartan_eq_card_rootCenter_sub_one hc,
    cartan_le_normalizer_rootCenter _ _, cartan_le_normalizer_conjSubgroup_rootCenter hPs,
    ?_, ?_, ?_⟩
  · intro a ha ha1 b hb hb1
    exact exists_mem_cartan_conj_eq hc ha ha1 hb hb1
  · intro t ht a ha ha1 hta
    exact eq_one_of_mem_cartan_of_conj_eq hc ht ha ha1 hta
  · intro t ht ht1
    exact exists_eq_mul_of_mem_cartan h hc hg₀ hPs ht ht1

theorem exists_torusData_of_benderType {r i : ℕ}
    (h : BenderType K r i 1) {A : Subgroup K} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 2 ^ r) {g₀ : K} (hsup : A ⊔ conjSubgroup A g₀ = ⊤) :
    ∃ T : Subgroup K, TorusData A g₀ T := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_rootCenter_of_benderType h hA hcard
  obtain ⟨t, ht⟩ := h.exists_benderCore P
  have hsup' : rootCenter (P : Subgroup K) ⊔
      conjSubgroup (rootCenter (P : Subgroup K)) g₀ = ⊤ := hP ▸ hsup
  have hg₀ : g₀ ∉ borel (P : Subgroup K) := not_mem_borel_of_sup_eq_top ht hsup'
  obtain ⟨s, hs, hsP, hPs⟩ := exists_involution_conjugate_eq_of_benderCore ht hg₀
  refine ⟨cartan (P : Subgroup K) s, ?_⟩
  rw [hP]
  exact torusData_cartan h (h.benderCore P hs hsP) hg₀ hPs

end CFSG.LocalAnalysis.WeakClosure81
