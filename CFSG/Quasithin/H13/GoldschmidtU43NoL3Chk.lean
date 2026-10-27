module

public import CFSG.Quasithin.H13.GoldschmidtU43ModStage
public import CFSG.Quasithin.H13.GoldschmidtU43ModOne
public import Certificates.Data.U43NoL3

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.KGroups.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LieType.Multipliers.U43

@[expose] noncomputable def x7 : X₀ := evalG g2 sevenWord

theorem rep_x7 (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true) :
    Rep 820 (wArr 820 tabA tabB sevenWord) (psi x7) :=
  rep_wArr h1 (by decide)

theorem orderOf_xElt_of_eqA (hA : eqA 820 (compA 820 tabA tabA) (idA 820) = true) :
    orderOf xElt = 2 := by
  have hsq : xElt * xElt = 1 := by
    apply psi_inj
    rw [map_mul, map_one]
    exact (eqA_iff (rep_compA rep_tabA rep_tabA) (g := psi xElt * psi xElt) (h := 1) rep_idA).1 hA
  have hne : xElt ≠ 1 := by
    intro h
    have h2 := rep_tabA ⟨0, by norm_num⟩
    rw [h, map_one] at h2
    have h3 : tabA[0]! = 288 := by decide +kernel
    simp [h3] at h2
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hsq) hne

theorem eqA_false_ne_one {t : Array ℕ} {x : X₀} (hx : Rep 820 t (psi x))
    (h : eqA 820 t (idA 820) = false) : x ≠ 1 := by
  intro hx1
  have : eqA 820 t (idA 820) = true :=
    (eqA_iff hx (g := psi x) (h := 1) rep_idA).2 (by rw [hx1, map_one])
  rw [this] at h
  exact Bool.noConfusion h

theorem noSeven_sound (h : noSevenCheck 820 tabA tabB = true) :
    orderOf xElt = 2 ∧ orderOf x7 = 7 ∧
      ∀ i < 2835, ∀ f : X₀, Rep 820 (orbRec 820 tabA tabB).L[i]! (psi f) →
      ¬ (f * (x7 * f * x7⁻¹) = (x7 * f * x7⁻¹) * f ∧
        f * (x7 ^ 2 * f * (x7 ^ 2)⁻¹) = (x7 ^ 2 * f * (x7 ^ 2)⁻¹) * f) := by
  unfold noSevenCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, hA⟩, hxi⟩, h7⟩, hne⟩, hall⟩ := h
  have hx := rep_x7 h1
  have hxi' := rep_inv_of_isInvA hx hxi
  have hx2 := rep_compA hx hx
  have hxi2 := rep_compA hxi' hxi'
  have h7' := (eqA_iff (rep_compA hx2 (rep_compA hx2 (rep_compA hx2 hx))) (h := 1) rep_idA).1 h7
  have hx7 : x7 ^ 7 = 1 := by
    apply psi_inj
    rw [map_pow, map_one, ← h7']
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hne1 : x7 ≠ 1 := eqA_false_ne_one hx hne
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨orderOf_xElt_of_eqA hA, orderOf_eq_prime hx7 hne1, ?_⟩
  rintro i hi f hf ⟨hc1, hc2⟩
  have h5 := allLt_spec hall hi
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at h5
  have hconj1 := rep_compA hx (rep_compA hf hxi')
  have hconj2 := rep_compA hx2 (rep_compA hf hxi2)
  have e1 : commuteArr 820 (orbRec 820 tabA tabB).L[i]!
      (conjugateA 820 (wArr 820 tabA tabB sevenWord) (invCand 820 (wArr 820 tabA tabB sevenWord))
        (orbRec 820 tabA tabB).L[i]!) = true := by
    unfold commuteArr conjugateA
    rw [eqA_iff (rep_compA hf hconj1) (rep_compA hconj1 hf)]
    have := congrArg psi hc1
    simpa [map_mul, map_inv, mul_assoc] using this
  have e2 : commuteArr 820 (orbRec 820 tabA tabB).L[i]!
      (conjugateA 820 (compA 820 (wArr 820 tabA tabB sevenWord) (wArr 820 tabA tabB sevenWord))
        (compA 820 (invCand 820 (wArr 820 tabA tabB sevenWord))
          (invCand 820 (wArr 820 tabA tabB sevenWord))) (orbRec 820 tabA tabB).L[i]!) = true := by
    unfold commuteArr conjugateA
    rw [eqA_iff (rep_compA hf hconj2) (rep_compA hconj2 hf)]
    have := congrArg psi hc2
    simpa [map_mul, map_inv, map_pow, pow_two, mul_assoc] using this
  rcases h5 with h5 | h5
  · rw [e1] at h5
    exact Bool.noConfusion h5
  · rw [e2] at h5
    exact Bool.noConfusion h5

theorem index_centralizer_xElt (hc : Stage2HCard) :
    (Subgroup.centralizer ({xElt} : Set X₀)).index = 2835 := by
  have h := Subgroup.index_mul_card (Subgroup.centralizer ({xElt} : Set X₀))
  have hc' : Nat.card (Subgroup.centralizer ({xElt} : Set X₀)) = 1152 := hc
  rw [hc', card_X₀, show (3265920 : ℕ) = 2835 * 1152 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem rep_index_injective {L : Array (Array ℕ)} {N : ℕ} (hsz : L.size = N)
    (hnd : keysNodup L = true) {f : ℕ → X₀} (hf : ∀ i < N, Rep 820 L[i]! (psi (f i))) :
    ∀ i < N, ∀ j < N, f i = f j → i = j := by
  intro i hi j hj hij
  have hndl : (L.toList.map keyOf).Nodup := by
    unfold keysNodup at hnd
    exact of_decide_eq_true hnd
  have key : ∀ b : ℕ, b < 820 → (L[i]!)[b]! = (L[j]!)[b]! := by
    intro b hb
    rw [(hf i hi).apply hb, (hf j hj).apply hb, hij]
  have hk : keyOf (L[i]!) = keyOf (L[j]!) := by
    unfold keyOf
    rw [key 0 (by norm_num), key 1 (by norm_num), key 9 (by norm_num)]
  have hi' : i < L.size := hsz ▸ hi
  have hj' : j < L.size := hsz ▸ hj
  have e : ∀ m (hm : m < L.size),
      (L.toList.map keyOf)[m]'(by simpa using hm) = keyOf (L[m]!) := by
    intro m hm
    simp [getElem!_pos L m hm]
  exact (List.Nodup.getElem_inj_iff hndl).1 (by rw [e i hi', e j hj']; exact hk)

theorem conj_covered (ho : orbCheck 820 tabA tabB = true) (hc : Stage2HCard) :
    ∀ y ∈ conjClass, ∃ i < 2835, Rep 820 (orbRec 820 tabA tabB).L[i]! (psi y) := by
  obtain ⟨hsz, hnd, hex⟩ := orb_sound ho
  choose! f hfT hf using hex
  let F : Fin 2835 → conjClass := fun i => ⟨f i, hfT i i.2⟩
  have hinj : Function.Injective F := by
    intro i j hij
    exact Fin.ext (rep_index_injective hsz hnd hf i i.2 j j.2 (congrArg Subtype.val hij))
  have hcard : Nat.card conjClass ≤ 2835 := by
    have h1 := card_conjClass_le_index xElt
    rw [index_centralizer_xElt hc] at h1
    exact h1
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by simpa using hcard)
  intro y hy
  obtain ⟨i, hi⟩ := hbij.2 ⟨y, hy⟩
  refine ⟨i, i.2, ?_⟩
  have hfy : f i = y := congrArg Subtype.val hi
  rw [← hfy]
  exact hf i i.2

theorem x7_involution (hck : noSevenCheck 820 tabA tabB = true)
    (ho : orbCheck 820 tabA tabB = true) (hh : h4Check 820 tabA tabB rels4Codes = true)
    (hone : X0OneClass) :
    orderOf x7 = 7 ∧ ∀ f : X₀, orderOf f = 2 →
      ¬ (f * (x7 * f * x7⁻¹) = (x7 * f * x7⁻¹) * f ∧
        f * (x7 ^ 2 * f * (x7 ^ 2)⁻¹) = (x7 ^ 2 * f * (x7 ^ 2)⁻¹) * f) := by
  obtain ⟨hxo, hord, hmain⟩ := noSeven_sound hck
  refine ⟨hord, fun f hf => ?_⟩
  have hone' : ∀ u v : X₀, orderOf u = 2 → orderOf v = 2 → IsConj u v := hone
  have hf' : f ∈ conjClass := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (hone' f xElt hf hxo)
    exact ⟨c⁻¹, by rw [← hc]; group⟩
  obtain ⟨i, hi, hri⟩ := conj_covered ho (stage2HModel_of_checks ho hh).2 f hf'
  exact hmain i hi f hri

end CFSG.Quasithin.H13.U43
