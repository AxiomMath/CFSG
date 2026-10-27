module

public import CFSG.Milestones.ASVolI.H6
import CFSG.Quasithin.Background.B5Sec
import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.ASVolI.ChH

variable {W : Type} [CommGroup W]

private theorem s16jp_le_stabSub_of_stable {L : Subgroup (MulAut W)} {Y : Subgroup W}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) : L ≤ stabSub Y := by
  intro l hl
  rw [mem_stabSub]
  intro y
  exact ⟨fun hy => by
      have h := hY l⁻¹ (L.inv_mem hl) (l y) hy
      simpa using h,
    fun hy => hY l hl y hy⟩

private theorem s16jp_card_dvd_of_modIsoSub {G : Type*} [Group G] {A B : Type*}
    [CommGroup A] [CommGroup B] {a : G →* MulAut A} {b : G →* MulAut B} {S : Subgroup B}
    (h : CFSG.ASVolI.ChH.ModIsoSub a b S) : Nat.card A ∣ Nat.card B := by
  obtain ⟨e, hinj, -, -⟩ := h
  exact Subgroup.card_dvd_of_injective e hinj

theorem s16jp_st_section [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsL3 ↥L 1) (hirr : commSub ⊤ L ∈ irrSet L)
    (h8 : E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 8) :
    ∃ (π : GL (Fin 3) (ZMod 2) →* ↥L) (β : ↥(commSub (⊤ : Subgroup W) L) →* ↥Adj3),
      Function.Surjective π ∧ Function.Surjective β ∧
      (∀ u : ↥(commSub (⊤ : Subgroup W) L), β u = 1 ↔ (u : W) ∈ commSub ⊤ L ⊓ fixV L) ∧
      ∀ (γ : GL (Fin 3) (ZMod 2)) (u : ↥(commSub (⊤ : Subgroup W) L))
        (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
        ((β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ : ↥Adj3) : AdjAmb) =
          adjAmbAct γ ((β u : ↥Adj3) : AdjAmb) := by
  classical
  rw [irrSet, Set.mem_setOf_eq] at hirr
  obtain ⟨-, hIrrOn⟩ := hirr
  rw [IsIrrOn] at hIrrOn
  obtain ⟨hZU, hStableU, hStableZ, hIrrCond⟩ := hIrrOn
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  have hLU : L ≤ stabSub U := s16jp_le_stabSub_of_stable hStableU
  have hLZ : L ≤ stabSub Z := s16jp_le_stabSub_of_stable hStableZ
  obtain ⟨eL⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
  let π : GL (Fin 3) (ZMod 2) →* ↥L := eL.symm.toMonoidHom
  let actL : ↥L →* MulAut (Sec U Z) := CFSG.Quasithin.B5.secHom L hLU hLZ
  let act : GL (Fin 3) (ZMod 2) →* MulAut (Sec U Z) := actL.comp eL.symm.toMonoidHom
  have hactLrange : actL.range = autSec L U Z :=
    CFSG.Quasithin.B5.range_secHom L hLU hLZ
  have hactrange : act.range = autSec L U Z := by
    change (actL.comp eL.symm.toMonoidHom).range = autSec L U Z
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eL.symm.surjective,
      ← MonoidHom.range_eq_map, hactLrange]
  have hUp : IsPGroup 2 U := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro u
    refine ⟨1, ?_⟩
    show u ^ 2 = 1
    exact Subtype.ext (hW2 (u : W))
  have hcard : Nat.card (Sec U Z) = 2 ^ 8 := by
    have h := E3.relIndex_eq_two_pow (V := U) hUp Z
    rw [h8] at h
    change Z.relIndex U = 2 ^ 8
    exact h
  have hQ2 : ∀ q : Sec U Z, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : (w ^ 2 : ↥U) = 1 := Subtype.ext (by simpa using hW2 (w : W))
      rw [h2]
      rfl
  have hirrsec : XMod.IsIrrSec ↥(autSec L U Z) (⊥ : Subgroup (Sec U Z)) ⊤ :=
    CFSG.Quasithin.B5.isIrrSec_autSec (V := W) (W := U) (C := Z) (L := L)
      hZU hIrrCond hLU hLZ
  have hirrOn : IsIrredOn act.range ⊤ := by
    rw [hactrange]
    refine ⟨hirrsec.1.ne', ?_⟩
    intro J _ hJ
    exact hirrsec.2 J (fun a l hl => hJ (a : MulAut (Sec U Z)) a.2 l hl) bot_le le_top
  have hcardF2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  have hcardV3 : Nat.card (Multiplicative V3) = 8 :=
    CFSG.QuasithinUnique.Setup.Family.natCard_Vec3
  rcases CFSG.ASVolI.as_H_6_1.2.2.2 (Sec U Z) hQ2 act hirrOn with h | h | h | h
  · exfalso
    have hdvd := s16jp_card_dvd_of_modIsoSub h
    rw [hcard, hcardF2] at hdvd
    exact absurd hdvd (by norm_num)
  · exfalso
    have hdvd := s16jp_card_dvd_of_modIsoSub h
    rw [hcard, hcardV3] at hdvd
    exact absurd hdvd (by norm_num)
  · exfalso
    have hdvd := s16jp_card_dvd_of_modIsoSub h
    rw [hcard, hcardV3] at hdvd
    exact absurd hdvd (by norm_num)
  ·
    obtain ⟨e, heinj, herange, hee⟩ := h
    let q : ↥U →* Sec U Z := QuotientGroup.mk' (Z.subgroupOf U)
    let β : ↥U →* ↥Adj3 :=
      { toFun := fun u => ⟨e (q u), by
          rw [← herange]
          exact MonoidHom.mem_range.2 ⟨q u, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          show e (q 1) = 1
          rw [map_one, map_one]
        map_mul' := fun a b => by
          apply Subtype.ext
          show e (q (a * b)) = e (q a) * e (q b)
          rw [map_mul, map_mul] }
    have hact_mk : ∀ (γ : GL (Fin 3) (ZMod 2)) (u : ↥U),
        act γ (QuotientGroup.mk u) = QuotientGroup.mk
          (⟨((π γ : ↥L) : MulAut W) (u : W),
            (hLU (eL.symm γ).2 u).2 u.2⟩ : ↥U) := by
      intro γ u
      change CFSG.Quasithin.B5.secHom L hLU hLZ (eL.symm γ) (QuotientGroup.mk u) =
        QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W),
          (hLU (eL.symm γ).2 u).2 u.2⟩
      rw [CFSG.Quasithin.B5.secHom_mk]
      rw [show (⟨(eL.symm γ : MulAut W) (u : W),
            (hLU (eL.symm γ).2 u).2 u.2⟩ : ↥U) =
          ⟨((π γ : ↥L) : MulAut W) (u : W),
            (hLU (eL.symm γ).2 u).2 u.2⟩ from Subtype.ext rfl]
    have hβs : Function.Surjective β := by
      intro y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (herange.ge y.2)
      obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) x
      refine ⟨u, Subtype.ext ?_⟩
      show e (q u) = (y : AdjAmb)
      rw [show q u = x from hu]
      exact hx
    have hβk : ∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z := by
      intro u
      have h1 : β u = 1 ↔ e (q u) = 1 := Subtype.ext_iff
      have h2 : e (q u) = 1 ↔ q u = 1 := by
        constructor
        · intro hh; exact heinj (by rw [hh, map_one])
        · intro hh; rw [hh, map_one]
      have h3 : q u = 1 ↔ (u : W) ∈ Z := by
        show QuotientGroup.mk' (Z.subgroupOf U) u = 1 ↔ (u : W) ∈ Z
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      rw [h1, h2, h3]
    refine ⟨π, β, eL.symm.surjective, hβs, hβk, ?_⟩
    intro γ u hu
    have hq2 : q u = QuotientGroup.mk u :=
      QuotientGroup.mk'_apply (N := Z.subgroupOf U) u
    have hq : q ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = act γ (QuotientGroup.mk u) := by
      rw [hact_mk γ u]
      exact congrArg QuotientGroup.mk (Subtype.ext rfl)
    calc ((β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ : ↥Adj3) : AdjAmb)
        = e (q ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) := rfl
      _ = e (act γ (QuotientGroup.mk u)) := by rw [hq]
      _ = e (act γ (q u)) := by rw [← hq2]
      _ = adjAmbAct γ (e (q u)) := hee γ (q u)
      _ = adjAmbAct γ ((β u : ↥Adj3) : AdjAmb) := rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
