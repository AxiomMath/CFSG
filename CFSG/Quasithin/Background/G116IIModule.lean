module

public import CFSG.Quasithin.Background.G10FifteenRing
public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.Background.G10Stmts

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem eq_of_hiso_of_le_sup_aux [Finite V] {H : Subgroup (GLV V)}
    {I I' J : Submodule (ZMod 2) V} (hI : IsIrr H I) (hI' : IsIrr H I') (hn : ¬ HIso H I' I)
    (hJ : IsIrr H J) (hJle : J ≤ I ⊔ I') (h : HIso H J I) : J = I := by
  let S : Set (Submodule (ZMod 2) V) := {K | IsIrr H K ∧ ¬ HIso H K I}
  have hbot := homComp_inf_eq_bot hI S (fun K hK => hK.1) (fun K hK => hK.2)
  have hJI : J ≤ I := by
    intro j hj
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hJle hj)
    have hb1 : b ∈ homComp H I := by
      have h1 : a + b ∈ homComp H I := le_homComp_of_hiso hJ h hj
      have h2 : a ∈ homComp H I := le_homComp hI ha
      have : b = (a + b) - a := by abel
      rw [this]
      exact (homComp H I).sub_mem h1 h2
    have hb2 : b ∈ sSup S := le_sSup (show I' ∈ S from ⟨hI', hn⟩) hb
    have : b ∈ homComp H I ⊓ sSup S := ⟨hb1, hb2⟩
    rw [hbot, Submodule.mem_bot] at this
    rw [this, add_zero]
    exact ha
  rcases hI.eq_bot_or_eq hJ.1 hJI with h0 | h0
  · exact absurd h0 hJ.ne_bot
  · exact h0

theorem eq_or_eq_of_isIrr_of_isCompl [Finite V] {H : Subgroup (GLV V)}
    {I I' J : Submodule (ZMod 2) V} (hI : IsIrr H I) (hI' : IsIrr H I') (hc : IsCompl I I')
    (hn : ¬ HIso H I I') (hJ : IsIrr H J) : J = I ∨ J = I' := by
  have hn' : ¬ HIso H I' I := fun h => hn (hiso_symm hI'.1 hI.1 h)
  have hJle : J ≤ I ⊔ I' := by
    rw [hc.sup_eq_top]
    exact le_top
  obtain ⟨K, hK, hJK⟩ := irr_le_sSup hJ (S := {I, I'}) (fun K hK => by
    rcases hK with rfl | rfl
    · exact hI
    · exact hI') (by rw [sSup_pair]; exact hJle)
  rcases hK with rfl | rfl
  · exact Or.inl (eq_of_hiso_of_le_sup_aux hI hI' hn' hJ hJle hJK)
  · refine Or.inr (eq_of_hiso_of_le_sup_aux hI' hI hn hJ (by rwa [sup_comm]) hJK)

theorem conjSub_eq_or_isDualOf [Finite V] {Γ H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    {x t : GLV V} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hxΓ : x ∈ Γ) (htΓ : t ∈ Γ)
    (hI : IsIrr H I) (hcompl : IsCompl I (conjSub x I)) (hn : ¬ HIso H I (conjSub x I))
    (hdual : IsDualOf H I (conjSub x I)) :
    conjSub t I = I ∨ IsDualOf H I (conjSub t I) := by
  have hI' : IsIrr H (conjSub x I) := hI.conj_of_normal hN hxΓ
  rcases eq_or_eq_of_isIrr_of_isCompl hI hI' hcompl hn (hI.conj_of_normal hN htΓ) with h | h
  · exact Or.inl h
  · rw [h]
    exact Or.inr hdual

theorem hiso_conjSub_of_commute {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} {c : GLV V}
    (hc : ∀ h ∈ H, c * h = h * c) : HIso H I (conjSub c I) := by
  refine ⟨LinearEquiv.ofSubmodules c I (conjSub c I) rfl, fun k hk i j hkij => ?_⟩
  have h1 : c (k (i : V)) = k (c (i : V)) :=
    congrArg (fun g : GLV V => g (i : V)) (hc k hk)
  show k (c (i : V)) = c (j : V)
  rw [← h1, hkij]

theorem field_eq_zero_or_eq_one_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (y : F) : y = 0 ∨ y = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have h3 : ({0, 1, y} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h.1.symm, zero_ne_one]),
      Finset.card_pair (Ne.symm h.2)]
  have := Finset.card_le_univ ({0, 1, y} : Finset F)
  rw [← Nat.card_eq_fintype_card, hF] at this
  omega

theorem eq_zero_or_eq_one_of_endIsField_one {K : Subgroup (GLV V)} (hE : EndIsField K 1)
    (z : ↥(endCommutant K)) : z = 0 ∨ z = 1 := by
  obtain ⟨e⟩ := hE
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  rcases field_eq_zero_or_eq_one_of_card_two hcard (e z) with h | h
  · left
    have : e z = e 0 := by rw [h, map_zero]
    exact e.injective this
  · right
    have : e z = e 1 := by rw [h, map_one]
    exact e.injective this

theorem fixes_of_commute_of_endIsField {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hI : IsIrr H I) (hE : EndIsField (restrictRange H I hI.1) 1) {c : GLV V}
    (hc : ∀ h ∈ H, c * h = h * c) (hcI : conjSub c I = I) : ∀ i ∈ I, c i = i := by
  set cI : GLV ↥I := restrictEquiv c I hcI with hcIdef
  have hmem : (cI : ↥I →ₗ[ZMod 2] ↥I) ∈ endCommutant (restrictRange H I hI.1) := by
    rw [endCommutant, Subalgebra.mem_centralizer_iff]
    rintro g ⟨h', hh', rfl⟩
    obtain ⟨h, hh, rfl⟩ := (mem_restrictRange_iff' hI.1).1 hh'
    ext i
    show h (c (i : V)) = c (h (i : V))
    exact congrArg (fun g : GLV V => g (i : V)) (hc h hh).symm
  rcases eq_zero_or_eq_one_of_endIsField_one hE ⟨_, hmem⟩ with h0 | h1
  · exfalso
    obtain ⟨i, hi, hi0⟩ := (Submodule.ne_bot_iff I).1 hI.ne_bot
    have h2 := congrArg (fun z : ↥(endCommutant (restrictRange H I hI.1)) =>
      ((z : Module.End (ZMod 2) ↥I) ⟨i, hi⟩ : ↥I)) h0
    have h3 : ((c i : V)) = 0 := congrArg Subtype.val h2
    exact hi0 (by simpa using h3)
  · intro i hi
    have h2 := congrArg (fun z : ↥(endCommutant (restrictRange H I hI.1)) =>
      ((z : Module.End (ZMod 2) ↥I) ⟨i, hi⟩ : ↥I)) h1
    exact congrArg Subtype.val h2

theorem eq_one_of_commute_of_endIsField [Finite V] {Γ H : Subgroup (GLV V)}
    {I : Submodule (ZMod 2) V} {x : GLV V} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hxΓ : x ∈ Γ) (hI : IsIrr H I) (hcompl : IsCompl I (conjSub x I))
    (hn : ¬ HIso H I (conjSub x I)) (hE : EndIsField (restrictRange H I hI.1) 1) {c : GLV V}
    (hcΓ : c ∈ Γ) (hc : ∀ h ∈ H, c * h = h * c) : c = 1 := by
  have hI' : IsIrr H (conjSub x I) := hI.conj_of_normal hN hxΓ
  have key : ∀ c ∈ Γ, (∀ h ∈ H, c * h = h * c) → ∀ i ∈ I, c i = i := by
    intro c hcΓ hc
    have hcirr : IsIrr H (conjSub c I) := hI.conj_of_normal hN hcΓ
    have hcI : conjSub c I = I := by
      rcases eq_or_eq_of_isIrr_of_isCompl hI hI' hcompl hn hcirr with h | h
      · exact h
      · exfalso
        have h1 := hiso_conjSub_of_commute (H := H) (I := I) hc
        rw [h] at h1
        exact hn h1
    exact fixes_of_commute_of_endIsField hI hE hc hcI
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ I ⊔ conjSub x I := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨i, hi, rfl⟩ := hb
  have hc' : ∀ h ∈ H, (x⁻¹ * c * x) * h = h * (x⁻¹ * c * x) := by
    intro h hh
    have hh' : x * h * x⁻¹ ∈ H := hN x hxΓ h hh
    have h1 := hc _ hh'
    calc (x⁻¹ * c * x) * h = x⁻¹ * (c * (x * h * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * h * x⁻¹) * c) * x := by rw [h1]
      _ = h * (x⁻¹ * c * x) := by group
  have h2 : (x⁻¹ * c * x) i = i :=
    key _ (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hxΓ) hcΓ) hxΓ) hc' i hi
  have h3 : c (x i) = x i := by
    have h4 := congrArg x h2
    simpa [mul_assoc] using h4
  show c (a + (x : V →ₗ[ZMod 2] V) i) = a + (x : V →ₗ[ZMod 2] V) i
  rw [map_add, key c hcΓ hc a ha]
  exact congrArg (fun w => a + w) h3

end G11

end CFSG.Quasithin
