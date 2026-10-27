module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2SzRep
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefModBot

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {X : Type} [Group X]
variable {W : Subgroup G}

theorem sectionAction_bot_apply
    (hHbot : H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) (h : ↥H) (w : ↥W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    sectionAction hHbot hHW hE h (chiefModBotMulEquiv W w) =
      chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  rw [sectionAction_apply]
  change Ch3z.chiefPsi hHbot hHW h (chiefModBotMulEquiv W w) =
    chiefModBotMulEquiv W
      ⟨(h : G) * (w : G) * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩
  rw [chiefModBotMulEquiv_apply, chiefModBotMulEquiv_apply]
  exact Ch3z.chiefPsi_iota hHbot hHW (D14.le_normalizer_bot W) h w _

theorem mem_fixSub_sectionRep_bot_iff
    (hHbot : H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (hO : pCoreOf 2 H ≤ centralizerMod (⊥ : Subgroup G) H W)
    (e : oTwoQuot ↥H ≃* X) (P : Subgroup ↥H) (w : ↥W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Additive.ofMul (chiefModBotMulEquiv W w) ∈ CFSG.RankThree.FFModules.fixSub
        (sectionRep hHbot hHW (D14.le_normalizer_bot W) hE hO e)
        ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom) ↔
      (w : G) ∈ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  rw [CFSG.RankThree.FFModules.mem_fixSub, Subgroup.mem_centralizer_iff]
  constructor
  · intro hfix p hp
    obtain ⟨h, hhP, rfl⟩ := Subgroup.mem_map.mp hp
    have himg : e (QuotientGroup.mk h) ∈
        (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H)) hhP)
    have h1 := hfix _ himg
    rw [sectionRep_apply] at h1
    rw [sectionAction_bot_apply hHbot hHW hE h w] at h1
    have h2 : chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ =
        chiefModBotMulEquiv W w := by
      simpa using h1
    have h3 : (h : G) * (w : G) * (h : G)⁻¹ = (w : G) := by
      simpa using congrArg Subtype.val ((chiefModBotMulEquiv W).injective h2)
    have h4 : (h : G) * (w : G) = (w : G) * (h : G) := by
      calc (h : G) * (w : G) = ((h : G) * (w : G) * (h : G)⁻¹) * (h : G) := by group
        _ = (w : G) * (h : G) := by rw [h3]
    simpa using h4
  · intro hcent g hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨h, hhP, rfl⟩ := Subgroup.mem_map.mp hq
    have h4 : (h : G) * (w : G) = (w : G) * (h : G) := by
      simpa using hcent (h : G) (Subgroup.mem_map_of_mem H.subtype hhP)
    have h3 : (h : G) * (w : G) * (h : G)⁻¹ = (w : G) := by
      calc (h : G) * (w : G) * (h : G)⁻¹ = ((w : G) * (h : G)) * (h : G)⁻¹ := by
            rw [h4]
        _ = (w : G) := by group
    have h2 : (⟨(h : G) * (w : G) * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHW h.2) (w : G)).mp w.2⟩ : ↥W) = w :=
      Subtype.ext h3
    change ((sectionRep hHbot hHW (D14.le_normalizer_bot W) hE hO e)
      (e ((QuotientGroup.mk' (pCore 2 ↥H)) h)))
        (Additive.ofMul (chiefModBotMulEquiv W w)) =
        Additive.ofMul (chiefModBotMulEquiv W w)
    simp only [QuotientGroup.mk'_apply]
    rw [sectionRep_apply, sectionAction_bot_apply hHbot hHW hE h w, h2]

theorem card_fixSub_sectionRep_bot
    (hHbot : H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (hO : pCoreOf 2 H ≤ centralizerMod (⊥ : Subgroup G) H W)
    (e : oTwoQuot ↥H ≃* X) (P : Subgroup ↥H) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Nat.card (CFSG.RankThree.FFModules.fixSub
      (sectionRep hHbot hHW (D14.le_normalizer_bot W) hE hO e)
      ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom)) =
    Nat.card ↥(W ⊓ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G)) := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let C : Subgroup G := Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G)
  let A : Subgroup X := (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom
  let ρ := sectionRep hHbot hHW (D14.le_normalizer_bot W) hE hO e
  have key : ∀ w : ↥W,
      Additive.ofMul (chiefModBotMulEquiv W w) ∈ CFSG.RankThree.FFModules.fixSub ρ A ↔
        (w : G) ∈ C := by
    intro w
    exact mem_fixSub_sectionRep_bot_iff hHbot hHW hE hO e P w
  refine Nat.card_congr ?_
  refine
    { toFun := fun x =>
        let w : ↥W := (chiefModBotMulEquiv W).symm x.1.toMul
        ⟨(w : G), Subgroup.mem_inf.mpr ⟨w.2, ?_⟩⟩
      invFun := fun y =>
        let w : ↥W := ⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩
        ⟨Additive.ofMul (chiefModBotMulEquiv W w),
          CFSG.RankThree.FFModules.mem_fixSub.mpr ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (key _).mp (by
      have hw : chiefModBotMulEquiv W ((chiefModBotMulEquiv W).symm x.1.toMul) = x.1.toMul :=
        Equiv.apply_symm_apply _ _
      rw [hw]
      simpa using x.2)
  · exact (key w).mpr (Subgroup.mem_inf.mp y.2).2
  · intro x
    apply Subtype.ext
    simp
  · intro y
    apply Subtype.ext
    simp

end CFSG.Quasithin.Stroth

end
