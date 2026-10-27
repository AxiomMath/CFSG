module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

noncomputable def chiefModBotMulEquiv (W : Subgroup G) :
    ↥W ≃* ↥(Ch3z.chiefMod ⊥ W) := by
  let hNL : W ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  refine MulEquiv.ofBijective (Ch3z.chiefIota hNL) ⟨?_, Ch3z.chiefIota_surjective hNL⟩
  intro x y hxy
  have h : Ch3z.chiefIota hNL (x * y⁻¹) = 1 := by
    rw [map_mul, hxy]
    exact mul_inv_cancel _
  have hmem : ((x * y⁻¹ : ↥W) : G) ∈ (⊥ : Subgroup G) :=
    (Ch3z.chiefIota_eq_one_iff hNL _).1 h
  have h2 : (x : G) * (y : G)⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  exact Subtype.ext (by
    calc (x : G) = (x : G) * (y : G)⁻¹ * (y : G) := by group
      _ = 1 * (y : G) := by rw [h2]
      _ = (y : G) := by group)

theorem chiefModBotMulEquiv_apply (W : Subgroup G) (w : ↥W) :
    chiefModBotMulEquiv W w =
      Ch3z.chiefIota (by rw [Subgroup.normalizer_eq_top]; exact le_top) w := by
  unfold chiefModBotMulEquiv
  rfl

theorem chiefModBotMulEquiv_conj {H U W : Subgroup G} (hstep : IsChiefStep H U ⊥ W)
    (hUH : U ≤ H) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W)) (h : ↥H) (w : ↥W) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    l2ChiefSectionAction hstep hE h (chiefModBotMulEquiv W w) =
      chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            ((D14.le_normalizer_of_isNormalIn hstep.1) h.2) (w : G)).mp w.2⟩ := by
  let hNL : W ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  let hHL : H ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  let hHN : H ≤ Subgroup.normalizer (W : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  change l2ChiefSectionAction hstep hE h (Ch3z.chiefIota hNL w) =
    Ch3z.chiefIota hNL ⟨(h : G) * (w : G) * (h : G)⁻¹, _⟩
  rw [l2ChiefSectionAction_eq_chiefPsi]
  exact Ch3z.chiefPsi_iota hHL hHN hNL h w _

theorem mem_fixSub_chiefMod_bot_iff {H U W : Subgroup G} {m : ℕ}
    (hstep : IsChiefStep H U ⊥ W) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (P : Subgroup ↥H) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    ∀ w : ↥W,
      Additive.ofMul (chiefModBotMulEquiv W w) ∈ CFSG.RankThree.FFModules.fixSub
        (l2ChiefSectionRep hstep hUH hE e)
        ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom) ↔
      (w : G) ∈ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  intro w
  rw [CFSG.RankThree.FFModules.mem_fixSub, Subgroup.mem_centralizer_iff]
  constructor
  · intro hfix p hp
    obtain ⟨h, hhP, rfl⟩ := Subgroup.mem_map.mp hp
    have himg : e (QuotientGroup.mk h) ∈
        (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H)) hhP)
    have h1 := hfix _ himg
    rw [l2ChiefSectionRep_apply_mk] at h1
    rw [chiefModBotMulEquiv_conj hstep hUH hE h w] at h1
    have h2 : chiefModBotMulEquiv W
        ⟨(h : G) * (w : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            ((D14.le_normalizer_of_isNormalIn hstep.1) h.2) (w : G)).mp w.2⟩ =
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
        (Subgroup.mem_normalizer_iff.mp
          ((D14.le_normalizer_of_isNormalIn hstep.1) h.2) (w : G)).mp w.2⟩ : ↥W) = w :=
      Subtype.ext h3
    change ((l2ChiefSectionRep hstep hUH hE e)
      (e ((QuotientGroup.mk' (pCore 2 ↥H)) h))) (Additive.ofMul (chiefModBotMulEquiv W w)) =
        Additive.ofMul (chiefModBotMulEquiv W w)
    simp only [QuotientGroup.mk'_apply]
    rw [l2ChiefSectionRep_apply_mk, chiefModBotMulEquiv_conj hstep hUH hE h w, h2]

theorem fixSub_chiefMod_bot_card {H U W : Subgroup G} {m : ℕ}
    (hstep : IsChiefStep H U ⊥ W) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (P : Subgroup ↥H) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Nat.card (CFSG.RankThree.FFModules.fixSub (l2ChiefSectionRep hstep hUH hE e)
      ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom)) =
    Nat.card ↥(W ⊓ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G)) := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let C : Subgroup G := Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G)
  let A : Subgroup (SL(2, GaloisField 2 m)) :=
    (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom
  let ρ := l2ChiefSectionRep hstep hUH hE e
  have key : ∀ w : ↥W,
      Additive.ofMul (chiefModBotMulEquiv W w) ∈ CFSG.RankThree.FFModules.fixSub ρ A ↔
        (w : G) ∈ C := by
    intro w
    exact mem_fixSub_chiefMod_bot_iff hstep hUH hE e P w
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
        MulEquiv.apply_symm_apply _ _
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
