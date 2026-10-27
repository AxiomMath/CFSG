module

public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace S152N

section Delta

variable {H T V : Subgroup G}

omit [Finite G] in
theorem cjSub_commutator (g : G) (X Y : Subgroup G) :
    cjSub g ⁅X, Y⁆ = ⁅cjSub g X, cjSub g Y⁆ :=
  Subgroup.map_commutator _ _ _

omit [Finite G] in
theorem cjSub_bot (g : G) : cjSub g (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

omit [Finite G] in
theorem cjSub_conjClosure {V H : Subgroup G} {h : G} (hh : h ∈ H) :
    cjSub h (conjClosure V H) = conjClosure V H :=
  B2F.cjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V H hh)

omit [Finite G] in
theorem cjSub_pCoreOf {h : G} (hh : h ∈ H) : cjSub h (pCoreOf 2 H) = pCoreOf 2 H :=
  B2F.cjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hh)

omit [Finite G] in
theorem cjSub_sup' (g : G) (A B : Subgroup G) : cjSub g (A ⊔ B) = cjSub g A ⊔ cjSub g B :=
  Subgroup.map_sup _ _ _

omit [Finite G] in
theorem isMaxElemAbelian_cjSub {h : G} (hh : h ∈ H) {A : Subgroup G}
    (hA : IsMaxElemAbelian H A) : IsMaxElemAbelian H (cjSub h A) := by
  refine ⟨cjSub_le (Subgroup.le_normalizer hh) hA.1, isElemAbelian_cjSub hA.2.1, fun B hBH hB => ?_⟩
  have h1 : cjSub h⁻¹ B ≤ H := cjSub_le (Subgroup.le_normalizer (H.inv_mem hh)) hBH
  have h2 := hA.2.2 (cjSub h⁻¹ B) h1 (isElemAbelian_cjSub hB)
  rw [card_cjSub] at h2
  rw [card_cjSub]
  exact h2

omit [Finite G] in
theorem cjSub_mem_deltaSet {h : G} (hh : h ∈ H) {A : Subgroup G} (hA : A ∈ deltaSet H V) :
    cjSub h A ∈ deltaSet H V := by
  obtain ⟨hmax, hnle, hmin, hquad⟩ := hA
  have hQ := cjSub_pCoreOf hh
  have hQ' := cjSub_pCoreOf (H.inv_mem hh)
  refine ⟨isMaxElemAbelian_cjSub hh hmax, ?_, fun A' hA' hA'nle => ?_, ?_⟩
  · intro hle
    apply hnle
    have := cjSub_mono (g := h⁻¹) hle
    rwa [cjSub_inv_cjSub, hQ'] at this
  · have e : cjSub h A ⊔ pCoreOf 2 H = cjSub h (A ⊔ pCoreOf 2 H) := by
      rw [cjSub_sup', hQ]
    rw [e, card_cjSub]
    exact hmin A' hA' hA'nle
  · have h1 := congrArg (cjSub h) hquad
    rw [cjSub_commutator, cjSub_commutator, cjSub_conjClosure hh, cjSub_bot] at h1
    exact h1

theorem exists_mem_deltaSet (hT : IsSylowTwoOf T H)
    (hne : ∃ A : Subgroup G, IsMinOffender T H V A) : (deltaSet H V).Nonempty := by
  obtain ⟨A, hAT, hAn, hmin, hq⟩ := hne
  have hRT := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hAnle : ¬ A ≤ pCoreOf 2 H := fun hle =>
    hAn ⟨hle, hAT.2.1, fun B hBQ hB => hAT.2.2 B (hBQ.trans hRT) hB⟩
  refine ⟨A, isMaxElemAbelian_of_isSylowTwoOf hT hAT, hAnle, fun A' hA' hA'nle => ?_, hq⟩
  obtain ⟨h, hh, hA'T⟩ := exists_conj_isMaxElemAbelian hT hA'
  have hQ := cjSub_pCoreOf hh
  have hQ' := cjSub_pCoreOf (H.inv_mem hh)
  have hn : ¬ IsMaxElemAbelian (pCoreOf 2 H) (cjSub h A') := fun hmax => hA'nle (by
    have := cjSub_mono (g := h⁻¹) hmax.1
    rwa [cjSub_inv_cjSub, hQ'] at this)
  have h1 := hmin (cjSub h A') hA'T hn
  have e : cjSub h A' ⊔ pCoreOf 2 H = cjSub h (A' ⊔ pCoreOf 2 H) := by
    rw [cjSub_sup', hQ]
  rwa [e, card_cjSub] at h1

omit [Finite G] in
theorem exists_deltaSet_not_le (hT : IsSylowTwoOf T H) (hne : (deltaSet H V).Nonempty) :
    ∃ A ∈ deltaSet H V, ¬ A ≤ T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨A₀, hA₀⟩ := hne
  let C : Subgroup G :=
    { carrier := {x | x ∈ H ∧ ∀ h ∈ H, h⁻¹ * x * h ∈ T}
      one_mem' := ⟨H.one_mem, fun h _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun h hh => by
        have := T.mul_mem (ha.2 h hh) (hb.2 h hh)
        simpa [mul_assoc] using this⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun h hh => by
        have := T.inv_mem (ha.2 h hh)
        simpa [mul_assoc] using this⟩ }
  have hCH : C ≤ H := fun x hx => hx.1
  have hCT : C ≤ T := fun x hx => by simpa using hx.2 1 H.one_mem
  have key : ∀ g ∈ H, ∀ x ∈ C, g * x * g⁻¹ ∈ C := fun g hg x hx =>
    ⟨H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg), fun h hh => by
      have := hx.2 (g⁻¹ * h) (H.mul_mem (H.inv_mem hg) hh)
      simpa [mul_assoc] using this⟩
  have hnorm : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => key g hg x hx, fun hx => by
      simpa [mul_assoc] using key g⁻¹ (H.inv_mem hg) _ hx⟩
  have hCQ : C ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hCH hnorm (hT.2.1.to_le hCT)
  apply hA₀.2.1
  intro a ha
  apply hCQ
  refine ⟨hA₀.1.1 ha, fun h hh => ?_⟩
  have hx : h * (h⁻¹ * a * h) * h⁻¹ = a := by group
  exact hcon _ (cjSub_mem_deltaSet (H.inv_mem hh) hA₀) (mem_cjSub.mpr (by simpa [hx] using ha))

theorem isMinOffender_cjSub (hT : IsSylowTwoOf T H) {A : Subgroup G} (hA : A ∈ deltaSet H V)
    (h2 : (A ⊓ pCoreOf 2 H).relIndex A = 2) {h : G} (hh : h ∈ H)
    (hAT : IsMaxElemAbelian T (cjSub h A)) : IsMinOffender T H V (cjSub h A) := by
  have hQT := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hQ := cjSub_pCoreOf hh
  have hQ' := cjSub_pCoreOf (H.inv_mem hh)
  have hnleQ : ¬ cjSub h A ≤ pCoreOf 2 H := by
    intro hle
    apply hA.2.1
    have := cjSub_mono (g := h⁻¹) hle
    rwa [cjSub_inv_cjSub, hQ'] at this
  have hAN : cjSub h A ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (cjSub_le (Subgroup.le_normalizer hh) hA.1.1).trans (le_normalizer_pCoreOf 2 H)
  have hrel : (pCoreOf 2 H).relIndex (cjSub h A ⊔ pCoreOf 2 H) = 2 := by
    rw [A4.relIndex_sup_eq_of_le_normalizer' hAN]
    have h1 : (pCoreOf 2 H).relIndex (cjSub h A) =
        (cjSub h A ⊓ pCoreOf 2 H).relIndex (cjSub h A) := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    have h3 : (cjSub h A ⊓ pCoreOf 2 H).relIndex (cjSub h A) =
        (A ⊓ pCoreOf 2 H).relIndex A := by
      have h4 : cjSub h A ⊓ pCoreOf 2 H = cjSub h (A ⊓ pCoreOf 2 H) := by
        rw [B2F.cjSub_inf, hQ]
      rw [h4]
      exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj h).toMonoidHom) _ _
        (MulAut.conj h).injective
    rw [h3, h2]
  have hcard1 : Nat.card ↥(cjSub h A ⊔ pCoreOf 2 H) = 2 * Nat.card ↥(pCoreOf 2 H) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 H) (cjSub h A ⊔ pCoreOf 2 H)
    rw [hrel, inf_eq_left.mpr le_sup_right] at this
    exact this.symm
  refine ⟨hAT, fun hmax => hnleQ hmax.1, fun A'' hA'' hA''n => ?_,
    (cjSub_mem_deltaSet hh hA).2.2.2⟩
  have hA''nle : ¬ A'' ≤ pCoreOf 2 H := fun hle =>
    hA''n ⟨hle, hA''.2.1, fun B hBQ hB => hA''.2.2 B (hBQ.trans hQT) hB⟩
  have hne1 : (pCoreOf 2 H).relIndex (A'' ⊔ pCoreOf 2 H) ≠ 1 := by
    intro h1
    exact hA''nle (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1))
  have hpos : (pCoreOf 2 H).relIndex (A'' ⊔ pCoreOf 2 H) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := Subgroup.relIndex_mul_card (pCoreOf 2 H) (A'' ⊔ pCoreOf 2 H)
  rw [inf_eq_left.mpr le_sup_right] at this
  rw [hcard1, ← this]
  have h2le : 2 ≤ (pCoreOf 2 H).relIndex (A'' ⊔ pCoreOf 2 H) := by omega
  exact Nat.mul_le_mul_right _ h2le

end Delta

end S152N

end CFSG.Quasithin
