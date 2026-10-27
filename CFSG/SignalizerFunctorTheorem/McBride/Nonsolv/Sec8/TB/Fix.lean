module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Order

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K F₁ F₂ : Subgroup G}

theorem card_inf_centralizer_zpowers
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) {a : G} (ha : a ∈ A) (haE : a ∉ E) (ha1 : a ≠ 1) :
    Nat.card ↥(sSup (Msig p A θ) ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set G)) =
      Nat.card K ^ p := by
  have hline := h.zpowers_mem_E1 ha ha1
  have hne : Subgroup.zpowers a ≠ E := fun heq => haE (heq ▸ Subgroup.mem_zpowers a)
  have hFN : Subgroup.zpowers a ⊓ E = ⊥ := h.inf_eq_bot_of_ne_E1 hline hB.mem hne
  have hΩ := isRegFam_omegaFam h hB hT
  have hfam := hΩ.smear_family h.elemAbelian.1 hline.1 hFN
  have hcardfam :
      Nat.card {Y | ∃ L ∈ omegaFam θ E F₁ F₂, Y = smear L (Subgroup.zpowers a)} = p := by
    have h1 := hfam.card_mul_card
    rw [(h.sup_mem_E2_of_ne hB.mem hline hne.symm).2, h.card] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) (h1.trans (by ring))
  rw [hfam.card_eq_pow (m := Nat.card K) (by
    rintro _ ⟨X, hX, rfl⟩
    exact (Nat.card_congr (hΩ.nonempty_mulEquiv_smear hline.1 hFN hX).some.toEquiv).trans
      (card_omegaFam_member h hB hT hX)), hcardfam]

theorem inf_centralizer_eq_apply_of_not_mem
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) {a : G} (ha : a ∈ A) (haE : a ∉ E) (ha1 : a ≠ 1) :
    sSup (Msig p A θ) ⊓ Subgroup.centralizer ({a} : Set G) = θ a := by
  have hline := h.zpowers_mem_E1 ha ha1
  have hne : Subgroup.zpowers a ≠ E := fun heq => haE (heq ▸ Subgroup.mem_zpowers a)
  have hθ : Nat.card ↥(θ a) = Nat.card K ^ p := by
    have := h.card_line_of_typeB hB.toTypeBCore hline hne
    rwa [h.isFunctor.thetaOf_zpowers ha ha1] at this
  have hle : θ a ≤ sSup (Msig p A θ) ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set G) :=
    le_inf (h.apply_le_sSup_msig ha ha1)
      (by rw [centralizer_zpowers_eq_singleton]; exact h.isFunctor.le_centralizer a ha ha1)
  rw [← centralizer_zpowers_eq_singleton]
  exact (Subgroup.eq_of_le_of_card_ge hle
    ((card_inf_centralizer_zpowers h hB hT ha haE ha1).le.trans hθ.ge)).symm

theorem le_normalizer_inf_centralizer (h : Counterexample p A θ) {B C : Subgroup G}
    (hBA : B ≤ A) (hCA : C ≤ A) :
    B ≤ Subgroup.normalizer ((sSup (Msig p A θ) ⊓ Subgroup.centralizer (C : Set G) :
      Subgroup G) : Set G) := by
  have := h.elemAbelian.1
  intro x hx
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  show (sSup (Msig p A θ) ⊓ Subgroup.centralizer (C : Set G)).map (MulAut.conj x).toMonoidHom = _
  have hW : (sSup (Msig p A θ)).map (MulAut.conj x).toMonoidHom = sSup (Msig p A θ) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.normalizes_sSup_msig (hBA hx))
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, hW,
    Near.Lemma212.map_conj_centralizer_of_commute C fun c hc =>
      setLike_mul_comm (hCA hc) (hBA hx)]

theorem inf_centralizer_eq_apply_of_mem
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    sSup (Msig p A θ) ⊓ Subgroup.centralizer ({b} : Set G) = θ b := by
  have hbA : b ∈ A := hB.mem.1 hbE
  have hEb : E = Subgroup.zpowers b := h.line_eq_zpowers hB.mem hbE hb1
  have hB₀A : F₁ ⊔ F₂ ≤ A := sup_le hT.mem₁.1 hT.mem₂.1
  refine le_antisymm ?_ (le_inf (h.apply_le_sSup_msig hbA hb1)
    (h.isFunctor.le_centralizer b hbA hb1))
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.centralizer ({b} : Set G) := by
    rw [hEb, centralizer_zpowers_eq_singleton]
  set V : Subgroup G := sSup (Msig p A θ) ⊓ Subgroup.centralizer ({b} : Set G) with hV
  have hVE : V = sSup (Msig p A θ) ⊓ Subgroup.centralizer (E : Set G) := by rw [hV, hCE]
  have hBN : F₁ ⊔ F₂ ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVE]
    exact le_normalizer_inf_centralizer h hB₀A hB.mem.1
  have hcopW : Nat.Coprime p (Nat.card (sSup (Msig p A θ) : Subgroup G)) := by
    have hX := (isRegFam_omegaFam h hB hT).card_eq_pow (m := Nat.card K) fun X hX =>
      card_omegaFam_member h hB hT hX
    rw [hX]
    refine Nat.Coprime.pow_right _ ?_
    rw [← Nat.card_congr (nonempty_mulEquiv_sup h hB hT).some.toEquiv]
    exact h.isFunctor.coprime_thetaOf hB₀A (h.ne_bot_of_mem_E2 (hT.mem_E2_sup h))
  have hcopV : Nat.Coprime p (Nat.card V) :=
    hcopW.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hgen := iSup_centralizer_nonidentity h.prime (h.isElemAbelian_of_le hB₀A)
    (hT.mem_E2_sup h).2.ge hBN hcopV
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun haB => iSup_le fun ha1 => ?_
  have haE : a ∉ E := fun haE => ha1 (Subgroup.mem_bot.mp (by
    rw [← hT.inf_sup_eq_bot h]
    exact ⟨haB, haE⟩))
  have haA : a ∈ A := hB₀A haB
  rintro x ⟨hxV, hxa⟩
  have hxθ : x ∈ θ a := by
    rw [← inf_centralizer_eq_apply_of_not_mem h hB hT haA haE ha1]
    exact ⟨hxV.1, hxa⟩
  have hxE : x ∈ θ a ⊓ Subgroup.centralizer (E : Set G) :=
    ⟨hxθ, by rw [hCE]; exact hxV.2⟩
  rw [h.isFunctor.inf_centralizer_eq_thetaOf haA ha1 hB.mem.1] at hxE
  rw [← h.thetaOf_line hB.mem hbE hb1]
  exact thetaOf_anti le_sup_right hxE

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
