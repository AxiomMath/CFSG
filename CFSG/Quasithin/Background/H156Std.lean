module

public import CFSG.Quasithin.Background.H156Cnt

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.ASVolI.ChH

section Std


theorem std_ind3 : InducesOn (img11 stabUTP) UT ⊥ (Multiplicative (Fin 3 → ZMod 2))
    (natSub 3 (ZMod 2) ⊤) := by
  refine ⟨bot_le, fun g hg u hu => ?_, fun g hg z hz => ?_, beta3.comp UT.subtype, ?_, ?_, ?_, ?_⟩
  · exact (mem_stabSub.1 (H_stab_UT hg) u).2 hu
  · have hz1 : z = 1 := hz
    rw [hz1]
    exact Subgroup.mem_bot.2 (MulEquiv.map_one g)
  · intro w
    obtain ⟨u, hu, hw⟩ := beta3_surj_UT w
    exact ⟨⟨u, hu⟩, hw⟩
  · intro u
    constructor
    · intro h
      have : (u : W11) = 1 := beta3_inj_UT u.2 h
      rw [this]
      exact Subgroup.one_mem _
    · intro h
      have h1 : (u : W11) = 1 := h
      show beta3 (u : W11) = 1
      rw [h1, map_one]
  · intro g hg
    refine ⟨natHom 3 (ZMod 2) (Psi ⟨g, hg⟩).1, ⟨_, Subgroup.mem_top _, rfl⟩, fun u u' h => ?_⟩
    show beta3 (u' : W11) = natHom 3 (ZMod 2) (Psi ⟨g, hg⟩).1 (beta3 (u : W11))
    rw [h]
    exact (Psi_spec ⟨g, hg⟩).1 u u.2
  · rintro γ ⟨a, -, rfl⟩
    obtain ⟨g', hg'⟩ := Psi_surjective (a, 1)
    have ha : (Psi g').1 = a := congrArg Prod.fst hg'
    refine ⟨g'.1, g'.2, fun u u' h => ?_⟩
    show beta3 (u' : W11) = natHom 3 (ZMod 2) a (beta3 (u : W11))
    rw [h, ← ha]
    exact (Psi_spec g').1 u u.2

theorem std_ind2 : InducesOn (img11 stabUTP) ⊤ V9 (Multiplicative (Fin 2 → ZMod 2))
    (natSub 2 (ZMod 2) ⊤) := by
  refine ⟨le_top, fun g hg u hu => Subgroup.mem_top _, fun g hg z hz => H_stab_V9 hg z |>.2 hz,
    beta2.comp (⊤ : Subgroup W11).subtype, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨x, hx⟩ := beta2_surjective w
    exact ⟨⟨x, Subgroup.mem_top _⟩, hx⟩
  · intro u
    exact MonoidHom.mem_ker (f := beta2) (x := (u : W11))
  · intro g hg
    refine ⟨natHom 2 (ZMod 2) (Psi ⟨g, hg⟩).2, ⟨_, Subgroup.mem_top _, rfl⟩, fun u u' h => ?_⟩
    show beta2 (u' : W11) = natHom 2 (ZMod 2) (Psi ⟨g, hg⟩).2 (beta2 (u : W11))
    rw [h]
    exact (Psi_spec ⟨g, hg⟩).2.1 u
  · rintro γ ⟨c, -, rfl⟩
    obtain ⟨g', hg'⟩ := Psi_surjective (1, c)
    have hc : (Psi g').2 = c := congrArg Prod.snd hg'
    refine ⟨g'.1, g'.2, fun u u' h => ?_⟩
    show beta2 (u' : W11) = natHom 2 (ZMod 2) c (beta2 (u : W11))
    rw [h, ← hc]
    exact (Psi_spec g').2.1 u

end Std

theorem beta6_surj_V9 (X : Mat32) : ∃ x ∈ V9, beta6 x = X := by
  obtain ⟨w, rfl⟩ := matOfW_bijective.2 X
  obtain ⟨y, hy, rfl⟩ := toW_surj 6 w
  have : ∀ y < 64, ∃ m ∈ combos v9Basis, actM c6 m = y := by decide +kernel
  obtain ⟨m, hm, hmy⟩ := this y hy
  refine ⟨toW 11 m, maskSub_v9_eq ▸ toW_mem_maskSub hm, ?_⟩
  rw [beta6_toW, hmy]
  rfl

theorem matBitsM_eq_zero : ∀ y < 64, matBitsM y = 0 → y = 0 := by decide +kernel

theorem beta6_ker_V9 {x : W11} (hx : x ∈ V9) : beta6 x = 1 ↔ x ∈ UT := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  have hm0 : actM c2 m = 0 := (mem_V9_iff m).1 hx
  have key : ∀ m < 2 ^ 11, actM c2 m = 0 → (actM c6 m = 0 ↔ m ∈ uTMasks) := by decide +kernel
  rw [beta6_toW, toW_mem_UT_iff hm, ← key m hm hm0]
  constructor
  · intro h
    have h1 : matBitsM (actM c6 m) = 0 := congrArg Multiplicative.toAdd h
    exact matBitsM_eq_zero _ (actM_lt c6_lt m) h1
  · intro h
    rw [h]
    have : matBitsM 0 = 0 := by decide +kernel
    rw [this]
    rfl

@[expose] def tensHom : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2) →* MulAut Mat32 where
  toFun p := tensAut p.1 p.2
  map_one' := MulEquiv.ext tensAut_one
  map_mul' p q := MulEquiv.ext fun X => (tensAut_mul p.1 q.1 p.2 q.2 X).symm

theorem closure_tensorSet32_le : Subgroup.closure tensorSet32 ≤ tensHom.range := by
  rw [Subgroup.closure_le]
  rintro γ ⟨g, h, hγ⟩
  refine ⟨(g, h), MulEquiv.ext fun X => ?_⟩
  apply Multiplicative.toAdd.injective
  exact (hγ (Multiplicative.toAdd X)).symm

section Std2


theorem std_indT : InducesOn (img11 stabUTP) V9 UT Mat32 (Subgroup.closure tensorSet32) := by
  refine ⟨UT_le_V9, fun g hg u hu => (mem_stabSub.1 (H_stab_V9 hg) u).2 hu,
    fun g hg z hz => (mem_stabSub.1 (H_stab_UT hg) z).2 hz, beta6.comp V9.subtype, ?_, ?_, ?_, ?_⟩
  · intro X
    obtain ⟨x, hx, hX⟩ := beta6_surj_V9 X
    exact ⟨⟨x, hx⟩, hX⟩
  · intro u
    exact beta6_ker_V9 u.2
  · intro g hg
    refine ⟨tensAut (invTGL 3 (Psi ⟨g, hg⟩).1) (Psi ⟨g, hg⟩).2,
      Subgroup.subset_closure (tensAut_mem _ _), fun u u' h => ?_⟩
    show beta6 (u' : W11) = tensAut (invTGL 3 (Psi ⟨g, hg⟩).1) (Psi ⟨g, hg⟩).2 (beta6 (u : W11))
    rw [h]
    exact (Psi_spec ⟨g, hg⟩).2.2 u u.2
  · intro γ hγ
    obtain ⟨p, rfl⟩ := closure_tensorSet32_le hγ
    obtain ⟨g', hg'⟩ := Psi_surjective (invTGL 3 p.1, p.2)
    have h1 : (Psi g').1 = invTGL 3 p.1 := by rw [hg']
    have h2 : (Psi g').2 = p.2 := by rw [hg']
    refine ⟨g'.1, g'.2, fun u u' h => ?_⟩
    show beta6 (u' : W11) = tensAut p.1 p.2 (beta6 (u : W11))
    rw [h]
    have := (Psi_spec g').2.2 u u.2
    rw [h1, h2, invTGL_invTGL] at this
    exact this

end Std2

end CFSG.Quasithin.H156
