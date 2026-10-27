module

public import CFSG.Quasithin.Background.B5P4Num
public import CFSG.Quasithin.Background.B5Part1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section Setting

variable {V : Type} [CommGroup V] [Finite V] {G L T : Subgroup (MulAut V)}

omit [Finite V] in
theorem le_stabSub_fixV (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hGn : ∀ g ∈ G, g⁻¹ ∈ G) :
    G ≤ stabSub (fixV L) := fun g hg => by
  refine mem_stabSub_of_inv (fixV_inv (fun l hl => ?_)) (fixV_inv (fun l hl => ?_))
  · have := hn g⁻¹ (hGn g hg) l hl
    simpa using this
  · have := hn g hg l hl
    simpa using this

theorem sec_setting (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hT : IsSylowTwoOf T G) (hGT : G = L ⊔ T) :
    G ≤ stabSub (commV L) ∧ G ≤ stabSub (⊥ : Subgroup V) ∧
      CFSG.IsQuasisimple ↥(quasithinGenFitting G) ∧
      ¬ commSub (commV L) (quasithinGenFitting G) ≤ ⊥ := by
  have hn := normal_L h
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hn (fun g hg => G.inv_mem hg)
  have hGC : G ≤ stabSub (⊥ : Subgroup V) := fun g _ u => by
    simp only [Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  have hF : quasithinGenFitting G = L := genFitting_eq_of_eq_sup h hT hGT
  have hqs : CFSG.IsQuasisimple ↥(quasithinGenFitting G) := by rw [hF]; exact quasi_L h
  have hS : ¬ commSub (commV L) (quasithinGenFitting G) ≤ ⊥ := by
    rw [hF]
    obtain ⟨-, hcomm, hlt, -⟩ := irr_data hU
    rw [hcomm]
    intro hle
    have : commV L = ⊥ := le_bot_iff.1 hle
    rw [this] at hlt
    simp at hlt
  exact ⟨hGU, hGC, hqs, hS⟩

end Setting

section LemmaA

variable {V : Type} [CommGroup V] [Finite V] {G L T : Subgroup (MulAut V)}

theorem fixV_le_of_q_one (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hT : IsSylowTwoOf T G) (hGT : G = L ⊔ T) (hD : IsIntDirect (commV L) (fixV L) ⊤)
    (hq : qOf (autSec G (commV L) ⊥) = ((1 : ℚ) : WithTop ℚ)) : fixV L ≤ fixV G := by
  have hn := normal_L h
  obtain ⟨hGU, hGC, hqs, hS⟩ := sec_setting h hU hT hGT
  have hUC : (⊥ : Subgroup V) ≤ commV L := bot_le
  have hoff : ∀ A, IsFFStarOffender G A → fixV L ≤ fixV A := by
    intro A hA
    obtain ⟨-, -, hclause⟩ := B1_5_8 hV hA (W := commV L) (U := ⊥) hUC hGU hGC hqs (o2_G h) hS
    obtain ⟨-, -, hWA⟩ := hclause hq
    intro v hv a ha
    have haG : a ∈ G := hA.1 ha
    have hvL : a v ∈ fixV L := B1Red.fixV_inv_of_normalizes hn a haG v hv
    have hvt : v ∈ commV L ⊔ fixV A := by rw [hWA]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hvt
    have hay : a y ∈ commV L := (hGU haG y).2 hy
    have hdiv : a (y * z) / (y * z) ∈ commV L ⊓ fixV L := by
      refine ⟨?_, (fixV L).div_mem hvL hv⟩
      have : a (y * z) / (y * z) = a y / y := by
        rw [map_mul, hz a ha]
        exact mul_div_mul_right_eq_div _ _ _
      rw [this]
      exact (commV L).div_mem hay hy
    rw [hD.2, Subgroup.mem_bot, div_eq_one] at hdiv
    exact hdiv
  intro v hv g hg
  have hJ : G = ffJ G := h.2.2.2.2.2
  have hle : ffJ G ≤ MulAction.stabilizer (MulAut V) v :=
    iSup₂_le fun A hA => fun a ha => hoff A hA hv a ha
  exact hle (hJ ▸ hg)

end LemmaA

section LemmaB

variable {V : Type} [CommGroup V] [Finite V] {G L T : Subgroup (MulAut V)}

theorem relIndex_fixV_eq_two (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hT : IsSylowTwoOf T G) (hGT : G = L ⊔ T) (hD : IsIntDirect (commV L) (fixV L) ⊤)
    (hne : fixV G ≠ fixV L) {r : ℚ} {N : ℕ} (hq : qOf (autSec G (commV L) ⊥) = (r : WithTop ℚ))
    (harith : ∀ a u : ℕ, 0 < a → a ≤ N → r * a ≤ u → a ≤ u + 1)
    (hN : ∀ A : Subgroup (MulAut V), A ≤ G → IsElemAbelian2 A → rk A ≤ N)
    (hidx : ∀ A : Subgroup (MulAut V), A ≤ G → ¬ A ≤ L → L ⊔ A = G) :
    (fixV G).relIndex (fixV L) = 2 := by
  have hn := normal_L h
  have hLG := le_G h
  obtain ⟨hGU, hGC, hqs, hS⟩ := sec_setting h hU hT hGT
  have hUC : (⊥ : Subgroup V) ≤ commV L := bot_le
  have hGW : G ≤ stabSub (fixV L) := le_stabSub_fixV hn (fun g hg => G.inv_mem hg)
  have hex : ∃ A, IsFFStarOffender G A ∧ ¬ A ≤ L := by
    by_contra hcon
    push Not at hcon
    have hJ : ffJ G ≤ L := iSup₂_le fun A hA => hcon A hA
    have hGL : G ≤ L := h.2.2.2.2.2 ▸ hJ
    exact hne (by rw [le_antisymm hGL hLG])
  obtain ⟨A, hA, hAL⟩ := hex
  have hAG : A ≤ G := hA.1
  have hfixG : fixV G = fixV L ⊓ fixV A := by rw [← hidx A hAG hAL, B1.fixV_sup]
  obtain ⟨hfaithA, -, -⟩ := B1_5_8 hV hA (W := commV L) (U := ⊥) hUC hGU hGC hqs (o2_G h) hS
  have hA' : IsFFStarOffender (autSec G (commV L) ⊥) (autSec A (commV L) ⊥) :=
    isFFStarOffender_autSec_bot hA hGU hfaithA
  have hq' := qOf_le_rAV_of_offender (sq_eq_one_sec hV (commV L) ⊥) hA'
  rw [hq] at hq'
  have hr : r ≤ rAV (autSec A (commV L) ⊥) := WithTop.coe_le_coe.1 hq'
  have hArk : rk (autSec A (commV L) ⊥) = rk A :=
    rk_autSec_eq (hAG.trans hGU) (hAG.trans hGC) hfaithA
  have hapos : 0 < rk A := hA.isA2.rk_pos
  unfold rAV at hr
  rw [hArk, le_div_iff₀ (by exact_mod_cast hapos)] at hr
  have hu := rkIdx_autSec_bot (A := A) (W := commV L) (hAG.trans hGU)
  have hbound : rk A ≤ rkIdx (fixV (autSec A (commV L) ⊥)) + 1 :=
    harith (rk A) _ hapos (hN A hAG hA.2.2.1) hr
  have hsplit := rkIdx_split hV hA hD.1 hD.2 (hAG.trans hGU) (hAG.trans hGW)
  have hle : fixV G ≤ fixV L := B1.fixV_le_fixV hLG
  have hP : rk ↥(fixV G) < rk ↥(fixV L) := by
    by_contra hge
    push Not at hge
    exact hne (eq_of_le_of_rk_le hV hle hge)
  have hrkP : rk ↥(fixV G) = rk ↥(fixV L ⊓ fixV A) := by rw [hfixG]
  have hW2 : rk ↥(fixV L) = rk ↥(fixV G) + 1 := by
    have h1 : rk ↥(fixV L ⊓ fixV A) ≤ rk ↥(fixV L) := rk_mono inf_le_left
    omega
  have hmul := Subgroup.relIndex_mul_card (fixV G) (fixV L)
  rw [inf_eq_left.2 hle, card_eq_two_pow hV (fixV G), card_eq_two_pow hV (fixV L), hW2,
    pow_succ] at hmul
  have hpos : 0 < 2 ^ rk ↥(fixV G) := pow_pos (by norm_num) _
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hmul, mul_comm])

end LemmaB

section BetaQ

variable {V : Type} [CommGroup V] [Finite V]

theorem b42_beta_q (hIdent : AsB42Ident) (hV : ∀ v : V, v ^ 2 = 1) {G L A : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hA : IsFFStarOffender G A) (h : B42Conclusion G L A) (hJL : ffJ G ≠ L) :
    (BinaryNaturalSp4 G (⊤ : Subgroup V) ⊥ 1 ∧ qOf G = ((2 / 3 : ℚ) : WithTop ℚ)) ∨
    (G2Natural G (⊤ : Subgroup V) ⊥ 1 ∧ qOf G = ((1 : ℚ) : WithTop ℚ)) ∨
    ((∃ n, (n = 5 ∨ n = 7) ∧ SymmetricNatural G (⊤ : Subgroup V) ⊥ n) ∧
      qOf G = ((1 : ℚ) : WithTop ℚ)) ∨
    (SLExteriorTwo L (⊤ : Subgroup V) ⊥ 4 ∧ Nonempty (↥G ≃* Equiv.Perm (Fin 8)) ∧
      qOf G = ((3 / 4 : ℚ) : WithTop ℚ)) := by
  obtain ⟨-, hGJ, -, -⟩ := hIdent V hV G L hHyp A hA (Or.inr hJL)
  rcases h with ⟨hJ, -⟩ | ⟨hJ, -⟩ | ⟨⟨n, hn, hn1⟩, hq⟩ | ⟨⟨n, hn, -, hn1⟩, hq⟩ |
    ⟨⟨n, hn5, π, hπ, -⟩, hq⟩ | ⟨hJ, -⟩ | ⟨-, hJ, -⟩ | ⟨hJ, -⟩ | ⟨hJ, -⟩ | ⟨hn, hrest⟩ | ⟨-, hJ, -⟩
  · exact absurd hJ hJL
  · exact absurd hJ hJL
  · have h1 : n = 1 := by
      by_contra hne
      exact hJL (hn1 (by have := one_le_of_binaryNaturalSp4 hn; omega))
    subst h1
    rw [← hGJ] at hn
    exact Or.inl ⟨hn, hq⟩
  · have h1 : n = 1 := by
      by_contra hne
      exact hJL (hn1 (by have := one_le_of_g2Natural hn; omega))
    subst h1
    rw [← hGJ] at hn
    exact Or.inr (Or.inl ⟨hn, hq⟩)
  · have hS : SymmetricNatural (ffJ G) (⊤ : Subgroup V) ⊥ n := ⟨π, hπ⟩
    rw [← hGJ] at hS
    exact Or.inr (Or.inr (Or.inl ⟨⟨n, hn5, hS⟩, hq⟩))
  · exact absurd hJ hJL
  · exact absurd hJ hJL
  · exact absurd hJ hJL
  · exact absurd hJ hJL
  · rcases hrest with ⟨-, hJ, -⟩ | ⟨-, e, hq⟩
    · exact absurd hJ hJL
    · exact Or.inr (Or.inr (Or.inr ⟨hn, e, hq⟩))
  · exact absurd hJ hJL

end BetaQ

section Main

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem part4_case_two (hI : B51IrrInputs) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (h1 : B51Part1 G L) (hD : IsIntDirect (commV L) (fixV L) ⊤)
    (hnd : ¬ IsIntDirect (commV L) (fixV G) ⊤) :
    commV L ∈ IrrPlus L ⊤ ∧ (∃ n, (n = 6 ∨ n = 8) ∧ SymmetricNatural G (commV L) ⊥ n) ∧
      (fixV G).relIndex (fixV L) = 2 := by
  have hGL : G ≠ L := by
    rintro rfl
    exact hnd hD
  have hne : fixV G ≠ fixV L := by
    intro heq
    apply hnd
    rw [heq]
    exact hD
  have hcase : B51Case1i G L := by
    rcases h1.2 with h' | h' | ⟨n, h'⟩ | h'
    · exact h'
    · exact absurd h'.1 hGL
    · exact absurd h'.1 hGL
    · exact absurd h'.1 hGL
  have hU : commV L ∈ IrrPlus L ⊤ := hcase.1
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  have hGT : G = L ⊔ T := by
    rcases hcase.2.2 T hT with hh | ⟨hh, -⟩
    · exact absurd hh hGL
    · exact hh
  refine ⟨hU, ?_⟩
  have hC : (⊥ : Subgroup V) = fixV L ⊓ commV L := by rw [inf_comm]; exact hD.2.symm
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  obtain ⟨A₀, hA₀G, hA₀T, B, hBA, hB⟩ := exists_section_offender' hV h hU hT hC
  have hb4 := b4Hyp_section' hV h hU hT.1 hT.2.1 hC
  have hconcl := hI.b42 (Sec (commV L) ⊥) (sq_eq_one_sec hV _ _) _ _ hb4 B hB
  have hcases := b42_cases hI.ident (sq_eq_one_sec hV _ _) hb4 hB hconcl
  rcases hcases with ⟨hJL, -, hQ⟩ | ⟨hJne, hbeta⟩
  · exact absurd (alpha_branch hI.i16 hI.nonsplit hV h hU hT hC hJL hQ) hGL
  have hq := b42_beta_q hI.ident (sq_eq_one_sec hV _ _) hb4 hB hconcl hJne
  obtain ⟨-, hLcomm, -, -⟩ := hbeta
  subst hGT
  have hLeq : L = ⁅L ⊔ T, L ⊔ T⁆ := by
    refine eq_of_autSec_eq hGU hGC hfM le_sup_left (commutator_le_self _) ?_
    rw [autSec_commutator hGU hGC]
    exact hLcomm
  have hLM : L ≤ L ⊔ T := le_sup_left
  have key : ∀ (n : ℕ) (r : ℚ) (N : ℕ), 5 ≤ n → SymmetricNatural (L ⊔ T) (commV L) ⊥ n →
      qOf (autSec (L ⊔ T) (commV L) ⊥) = (r : WithTop ℚ) →
      (∀ a u : ℕ, 0 < a → a ≤ N → r * a ≤ u → a ≤ u + 1) → ¬ 2 ^ (N + 1) ∣ n.factorial →
      (fixV (L ⊔ T)).relIndex (fixV L) = 2 := by
    intro n r N hn5 hS hqr harith hdvd
    obtain ⟨π, hπ⟩ := hS
    have hπs : Function.Surjective π := hπ.1
    have hdvd2 : (L.subgroupOf (L ⊔ T)).index ∣ 2 := by
      have := index_commutator_dvd_two n hn5 π hπs
      rwa [← hLeq] at this
    refine relIndex_fixV_eq_two hV h hU hT rfl hD hne hqr harith ?_ ?_
    · intro A hAM hA
      refine rk_le_of_card_dvd hA.isPGroup ?_ hdvd
      have h1 := Subgroup.card_dvd_of_le hAM
      have h2 := Subgroup.card_dvd_of_surjective (f := π) hπs
      have h3 : Nat.card (FFModel.symDn n).Gam = n.factorial := card_perm_fin n
      rw [h3] at h2
      exact h1.trans h2
    · intro A hAM hAL
      exact sup_eq_of_index_dvd_two hLM hAM hdvd2 hAL
  rcases hq with ⟨hSp4, hq23⟩ | ⟨hG2, hq1⟩ | ⟨⟨n, hn57, hS⟩, hq1⟩ | ⟨hExt, ⟨e8⟩, hq34⟩
  ·
    have hS6 := hI.sp4s6 _ _ _ _ hSp4
    have hS6' := symmetricNatural_of_autSec hUC hGU hGC hfM hS6
    refine ⟨⟨6, Or.inl rfl, hS6'⟩, ?_⟩
    refine key 6 (2 / 3) 4 (by norm_num) hS6' hq23 (fun a u hapos haN hr => ?_) (by decide)
    have h1 : (2 * a : ℚ) ≤ 3 * u := by linarith
    have h2 : 2 * a ≤ 3 * u := by exact_mod_cast h1
    omega
  ·
    exact absurd (le_antisymm (B1.fixV_le_fixV le_sup_left)
      (fixV_le_of_q_one hV h hU hT rfl hD hq1)) hne
  ·
    exact absurd (le_antisymm (B1.fixV_le_fixV le_sup_left)
      (fixV_le_of_q_one hV h hU hT rfl hD hq1)) hne
  ·
    have hS8 : SymmetricNatural (autSec (L ⊔ T) (commV L) ⊥) (⊤ : Subgroup (Sec (commV L) ⊥)) ⊥ 8 := by
      refine hI.s8d8 _ _ _ _ ⟨e8⟩ ?_ (fun _ _ _ _ => trivial) ?_
      · rw [← hLcomm]
        exact hExt
      · intro g _ z hz
        rw [Subgroup.mem_bot] at hz ⊢
        rw [hz]
        exact map_one g
    have hS8' := symmetricNatural_of_autSec hUC hGU hGC hfM hS8
    refine ⟨⟨8, Or.inr rfl, hS8'⟩, ?_⟩
    refine key 8 (3 / 4) 7 (by norm_num) hS8' hq34 (fun a u hapos haN hr => ?_) (by decide)
    have h1 : (3 * a : ℚ) ≤ 4 * u := by linarith
    have h2 : 3 * a ≤ 4 * u := by exact_mod_cast h1
    omega

theorem part4_of_inputs (hI : B51IrrInputs) (h2 : AsB51P2) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (h1 : B51Part1 G L) : B51Part4 G L := by
  intro hnd
  by_cases hD : IsIntDirect (commV L) (fixV L) ⊤
  · obtain ⟨hU, hn, hi⟩ := part4_case_two hI hV h h1 hD hnd
    exact ⟨hU, Or.inr ⟨hD, hn, hi⟩⟩
  · exact ⟨(h2 V hV G L h h1 hD).1, Or.inl hD⟩

end Main

end B5

end CFSG.Quasithin
