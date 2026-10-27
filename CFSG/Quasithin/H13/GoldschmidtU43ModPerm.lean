module

public import Certificates.Data.U43Model
public import CFSG.Quasithin.H13.GoldschmidtU43ModInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ} {K : Type*} [Group K]

theorem rep_of_eqA {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (hu : Rep n u g)
    (h : eqA n t u = true) : Rep n t g := fun x => by
  have h1 := (allLt_iff.1 (by unfold eqA at h; exact h)) x x.2
  rw [beq_iff_eq] at h1
  rw [h1, hu x]

theorem invsOK_spec {G Gi : Array (Array ℕ)} (h : invsOK n G Gi = true) :
    ∀ i < G.size, isInvA n G[i]! Gi[i]! = true := by
  intro i hi
  unfold invsOK at h
  simp only [Bool.and_eq_true] at h
  exact allLt_spec h.2 hi

theorem rep_invs (ρ : K →* Equiv.Perm (Fin n)) {G Gi : Array (Array ℕ)} {g : ℕ → K} {m : ℕ}
    (hG : ∀ i < m, Rep n G[i]! (ρ (g i))) (h : invsOK n G Gi = true) (hm : m ≤ G.size) :
    ∀ i < m, Rep n Gi[i]! (ρ (g i))⁻¹ := fun i hi =>
  rep_inv_of_isInvA (hG i hi) (invsOK_spec h i (lt_of_lt_of_le hi hm))

theorem rep_lettArr (ρ : K →* Equiv.Perm (Fin n)) {G Gi : Array (Array ℕ)} {g : ℕ → K} {m : ℕ}
    (hG : ∀ i < m, Rep n G[i]! (ρ (g i))) (hGi : ∀ i < m, Rep n Gi[i]! (ρ (g i))⁻¹)
    {l : ℕ × Bool} (hl : l.1 < m) : Rep n (lettArr G Gi l) (ρ (letterVal g l)) := by
  by_cases hb : l.2 = true
  · simpa [lettArr, letterVal, hb] using hG l.1 hl
  · simpa [lettArr, letterVal, hb] using hGi l.1 hl

theorem rep_evalArr (ρ : K →* Equiv.Perm (Fin n)) {G Gi : Array (Array ℕ)} {g : ℕ → K} {m : ℕ}
    (hG : ∀ i < m, Rep n G[i]! (ρ (g i))) (hGi : ∀ i < m, Rep n Gi[i]! (ρ (g i))⁻¹) :
    ∀ w : Word, (∀ l ∈ w, l.1 < m) → Rep n (evalArr n G Gi w) (ρ (evalG g w))
  | [], _ => by simpa [evalArr, evalG] using (rep_idA (n := n))
  | l :: w, hw => by
    have h1 := rep_lettArr ρ hG hGi (hw l List.mem_cons_self)
    have h2 := rep_evalArr ρ hG hGi w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    simpa [evalArr, evalG, map_mul] using rep_compA h1 h2

theorem deriv_sound (ρ : K →* Equiv.Perm (Fin n)) (T : Set K) (step : ℕ → Array ℕ → Array ℕ)
    (stepK : ℕ → K → K) {k N : ℕ} {x0 : Array ℕ} {x0K : K} (hx0 : x0K ∈ T)
    (hrx0 : Rep n x0 (ρ x0K)) (hT : ∀ j < k, ∀ x ∈ T, stepK j x ∈ T)
    (hstep : ∀ j < k, ∀ t x, Rep n t (ρ x) → Rep n (step j t) (ρ (stepK j x))) {r : Rec}
    (h : derivOK n step k x0 r N = true) : ∀ i < N, ∃ x ∈ T, Rep n r.L[i]! (ρ x) := by
  unfold derivOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hL, -⟩, -⟩, h0⟩, hall⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨x0K, hx0, rep_of_eqA hrx0 h0⟩
    · have h1 := allLt_spec hall hi
      simp only [Bool.or_eq_true, beq_iff_eq, hi0, false_or, Bool.and_eq_true,
        decide_eq_true_eq] at h1
      obtain ⟨⟨hp, hl⟩, he⟩ := h1
      obtain ⟨x, hxT, hx⟩ := ih _ hp (hp.trans hi)
      exact ⟨stepK _ x, hT _ hl x hxT, rep_of_eqA (hstep _ hl _ x hx) he⟩

theorem card_ge_of_deriv [Finite K] (ρ : K →* Equiv.Perm (Fin n)) (hn : 9 < n) (T : Set K)
    {L : Array (Array ℕ)} {N : ℕ} (hsz : L.size = N) (hn' : keysNodup L = true)
    (hex : ∀ i < N, ∃ x ∈ T, Rep n L[i]! (ρ x)) : N ≤ Nat.card T := by
  choose! f hfT hf using hex
  have hnd : (L.toList.map keyOf).Nodup := by unfold keysNodup at hn'; exact of_decide_eq_true hn'
  let F : Fin N → T := fun i => ⟨f i, hfT i i.2⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have hfe : f i = f j := congrArg Subtype.val hij
    have key : ∀ b : ℕ, b < n → (L[(i : ℕ)]!)[b]! = (L[(j : ℕ)]!)[b]! := by
      intro b hb
      rw [(hf i i.2).apply hb, (hf j j.2).apply hb, hfe]
    have hk : keyOf (L[(i : ℕ)]!) = keyOf (L[(j : ℕ)]!) := by
      unfold keyOf
      rw [key 0 (by omega), key 1 (by omega), key 9 hn]
    have hi' : (i : ℕ) < L.size := hsz ▸ i.2
    have hj' : (j : ℕ) < L.size := hsz ▸ j.2
    have e : ∀ m (hm : m < L.size),
        (L.toList.map keyOf)[m]'(by simpa using hm) = keyOf (L[m]!) := by
      intro m hm
      simp [getElem!_pos L m hm]
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 (by rw [e i hi', e j hj']; exact hk))
  have := Nat.card_le_card_of_injective F hinj
  simpa using this

theorem closedOK_spec {S Si L : Array (Array ℕ)} (h : closedOK n S Si L = true) {j i : ℕ}
    (hj : j < S.size) (hi : i < L.size) :
    (∃ i' < L.size, eqA n L[i']! (compA n S[j]! L[i]!) = true) ∧
      ∃ i' < L.size, eqA n L[i']! (compA n Si[j]! L[i]!) = true := by
  unfold closedOK at h
  have h1 := allLt_spec (allLt_spec h hj) hi
  simp only [Bool.and_eq_true, Array.any_eq_true] at h1
  obtain ⟨⟨a, ha, h2⟩, ⟨b, hb, h3⟩⟩ := h1
  exact ⟨⟨a, ha, by rwa [getElem!_pos L a ha]⟩, ⟨b, hb, by rwa [getElem!_pos L b hb]⟩⟩

theorem closure_sound (ρ : K →* Equiv.Perm (Fin n)) (gs : ℕ → K) {S Si L : Array (Array ℕ)}
    {k : ℕ} (hk : S.size = k) (hS : ∀ j < k, Rep n S[j]! (ρ (gs j)))
    (hSi : ∀ j < k, Rep n Si[j]! (ρ (gs j))⁻¹) (hid : Rep n L[0]! 1) (hL : 0 < L.size)
    (hc : closedOK n S Si L = true) :
    ∀ x ∈ Subgroup.closure (gs '' Set.Iio k), ∃ i < L.size, Rep n L[i]! (ρ x) := by
  intro x hx
  refine Subgroup.closure_induction_left (p := fun x _ => ∃ i < L.size, Rep n L[i]! (ρ x))
    ⟨0, hL, by rw [map_one]; exact hid⟩ ?_ ?_ hx
  · rintro y ⟨j, hj, rfl⟩ z _ ⟨i, hi, hr⟩
    obtain ⟨⟨i', hi', he⟩, -⟩ := closedOK_spec (n := n) hc (hk ▸ hj) hi
    exact ⟨i', hi', rep_of_eqA (by simpa using rep_compA (hS j hj) hr) he⟩
  · rintro y ⟨j, hj, rfl⟩ z _ ⟨i, hi, hr⟩
    obtain ⟨-, ⟨i', hi', he⟩⟩ := closedOK_spec (n := n) hc (hk ▸ hj) hi
    exact ⟨i', hi', rep_of_eqA (by simpa using rep_compA (hSi j hj) hr) he⟩

theorem derivOK_size {step : ℕ → Array ℕ → Array ℕ} {k N : ℕ} {x0 : Array ℕ} {r : Rec}
    (h : derivOK n step k x0 r N = true) : r.L.size = N ∧ eqA n r.L[0]! x0 = true := by
  unfold derivOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.2⟩

end CFSG.Quasithin.H13.U43
