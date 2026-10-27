module

public import CFSG.Quasithin.MS93.S32Main
public import CFSG.Quasithin.MS93.S32Types
public import CFSG.Quasithin.MS93.M15L3
public import CFSG.Quasithin.MS93.ML3Syl
public import CFSG.Quasithin.MS93.ML3Gen

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

section Sylow

theorem isSylowTwoOf_autI [Finite G] {U M S : Subgroup G} (hU : IsElemAbelian 2 U)
    (hM : M ≤ Subgroup.normalizer (U : Set G)) (hS : IsSylowTwoOf S M) :
    IsSylowTwoOf (autI hU S) (autI hU M) := by
  have hSN : S ≤ Subgroup.normalizer (U : Set G) := hS.1.trans hM
  refine ⟨autI_mono hU hS.1, IsPGroup.of_surjective hS.2.1 (toAutI hU hSN)
    (toAutI_surjective hU hSN), fun h2 => hS.2.2 (dvd_trans h2 ?_)⟩
  have hmap : (S.subgroupOf M).map (toAutI hU hM) = (autI hU S).subgroupOf (autI hU M) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hm
      exact convI_mem_autI hU hm (hM m.2)
    · intro hx
      obtain ⟨g, hgS, hgx⟩ := (mem_autI hU).1 hx
      refine ⟨⟨g, hS.1 hgS⟩, (Subgroup.mem_subgroupOf).2 hgS, Subtype.ext ?_⟩
      rw [← hgx]
      rfl
  rw [← hmap]
  exact Subgroup.index_map_dvd _ (toAutI_surjective hU hM)

theorem orderOf_uniTri_one {F : Type} [Field F] [CharP F 2] :
    orderOf (uniTri (1 : F) 0 1) = 4 := by
  have h2 : uniTri (1 : F) 0 1 ^ 2 = uniTri 0 1 0 := by
    rw [pow_two, uniTri_mul]
    congr 1
    · exact CharTwo.add_self_eq_zero 1
    · ring
    · exact CharTwo.add_self_eq_zero 1
  have h4 : uniTri (1 : F) 0 1 ^ 2 ^ (1 + 1) = 1 := by
    rw [pow_succ, pow_one, pow_mul, h2, pow_two, uniTri_mul, ← uniTri_zero]
    congr 1
    · ring
    · rw [mul_zero, add_zero]
      exact CharTwo.add_self_eq_zero 1
    · ring
  have hne : ¬ uniTri (1 : F) 0 1 ^ 2 ^ 1 = 1 := by
    rw [pow_one, h2, ← uniTri_zero]
    intro he
    have := uniTri_injective (F := F) (a₁ := (0, 1, 0)) (a₂ := (0, 0, 0)) he
    simp at this
  exact orderOf_eq_prime_pow hne h4

theorem exists_orderOf_four {V : Type*} [CommGroup V] [Finite V] {K : Subgroup (MulAut V)}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (e : ↥(StatedSL 3 F) ≃* ↥K)
    {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S K) : ∃ y ∈ S, orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := FFC.charP_two_of_card_pow (hF.trans (pow_one 2).symm)
  set P : Subgroup ↥(StatedSL 3 F) := (S.subgroupOf K).comap e.toMonoidHom with hPdef
  have hP2 : IsPGroup 2 P :=
    (hS.2.1.comap_of_injective K.subtype K.subtype_injective).comap_of_injective
      e.toMonoidHom e.injective
  have hPi : ¬ 2 ∣ P.index := by
    rw [hPdef, Subgroup.index_comap_of_surjective _ e.surjective]
    exact hS.2.2
  set f := (specialLinearGroupEquivStatedSL 3 F).toMonoidHom with hf
  set Q : Subgroup ↥(StatedSL 3 F) := (sStar : Subgroup (SL3 F)).map f with hQdef
  have hQ2 : IsPGroup 2 Q := (isPGroup_sStar (hF.trans (pow_one 2).symm)).map f
  have hQi : ¬ 2 ∣ Q.index := by
    rw [hQdef, Subgroup.index_map_of_bijective (specialLinearGroupEquivStatedSL 3 F).bijective]
    exact not_two_dvd_index_sStar (hF.trans (pow_one 2).symm)
  let SP := hP2.toSylow hPi
  let SQ := hQ2.toSylow hQi
  have hu : f (uniTri 1 0 1) ∈ (SQ : Subgroup ↥(StatedSL 3 F)) := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.mem_map_of_mem _ ((mem_sStar_iff).2 ⟨1, 0, 1, rfl⟩)
  have hord : orderOf (f (uniTri 1 0 1)) = 4 := by
    rw [orderOf_injective f (specialLinearGroupEquivStatedSL 3 F).injective, orderOf_uniTri_one]
  let y' : ↥SP := Sylow.equiv SQ SP ⟨_, hu⟩
  have hy' : orderOf ((y' : ↥(StatedSL 3 F))) = 4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]
  have hyP : ((y' : ↥(StatedSL 3 F))) ∈ P := by
    have := y'.2
    rwa [IsPGroup.mem_toSylow] at this
  refine ⟨((e (y' : ↥(StatedSL 3 F)) : ↥K) : MulAut V), hyP, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy']

end Sylow

theorem isIrrSec_of_natReal {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {F : Type}
    [Field F] {Z : Subgroup V} {π : ↥(StatedSL 3 F) →* ↥H}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia H ⊤ Z π) : XMod.IsIrrSec ↥H Z ⊤ := by
  refine ⟨lt_of_le_of_ne le_top (natReal_ne hπ).symm, fun J hJ hZJ hJt => ?_⟩
  exact natReal_inv_eq isTransNZ_statedSL3 hπ (fun g hg w hw => hJ ⟨g, hg⟩ w hw) hZJ hJt

section CaseIV

variable [Finite G] {M T L : Subgroup G}

theorem s32PartL3Two_of (h51 : AsB51) (hSQ : SQTKQuot)
    (hT : TypeFacts) : S32PartL3Two := by
  intro G _ _ M T L h hL3 hXL
  set hU := h.isElemAbelian_Uq with hUdef
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := (isSecW_Uq h).L_le_normalizer h
  obtain ⟨hXK, hnat, -, hcard, hsyl⟩ := hL3
  have hfixeq : fixV (autI hU M) = fixV (autI hU L) := by rw [hXK]
  have htoGM : C124.toG hU (fixV (autI hU M)) = Uq M T L ⊓ Zq M L := by
    rw [hfixeq]
    exact toG_fixV_Uq h
  have hC2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 := by
    rw [← htoGM, C124.toG, Subgroup.card_map_of_injective (C124.valHom_injective hU)]
    exact hcard
  have hCne : fixV (autI hU L) ≠ ⊥ := by
    intro hb
    rw [hfixeq, hb, Subgroup.card_bot] at hcard
    omega
  have hXZU : Xq M = Zq M L ⊔ Uq M T L := by
    have hB := (isSecW_Xq h).b51Hyp h hSQ (h.isFFModule_of_le_Xq (isSecW_Xq h))
    obtain ⟨-, -, -, -, h5, -⟩ := b51_Xq h h51 hSQ
    rcases h5 with h5 | ⟨-, hlist, hL⟩
    · have hle : fixV (ffJ (autI h.isElemAbelian_Xq M)) ≤ fixV (autI h.isElemAbelian_Xq L) :=
        fun v hv x hx => hv x (hB.2.2.2.1 hx)
      have htop : commV (autI h.isElemAbelian_Xq L) ⊔ fixV (autI h.isElemAbelian_Xq L) = ⊤ :=
        top_le_iff.mp (h5 ▸ sup_le_sup_left hle _)
      have := congrArg (C124.toG h.isElemAbelian_Xq) htop
      rw [C124.toG, Subgroup.map_sup, ← C124.toG, ← C124.toG, toG_commV_Xq h, toG_fixV_Xq h,
        toG_top, hXL] at this
      rw [← this, sup_comm]
    · exfalso
      have hX := isSecW_Xq h
      obtain ⟨F, iF, fF, hF, π, hπ⟩ := id hnat
      obtain ⟨-, hU168⟩ := card_lstar_of_sl3 (isSecW_Uq h) h hF hπ
      rcases hlist with ⟨m, F', iF', fF', hF', π', hπ'⟩ | ⟨π', hπ'⟩ | ⟨π', hπ'⟩ | hsl
      · obtain ⟨hm, hc⟩ := card_lstar_of_sp4 hX h hF' hπ'
        exact (ordBC_two_ne (by omega)).1 (hc.symm.trans hU168)
      · exact ordA_two_ne_360 le_rfl (hU168.symm.trans (card_lstar_of_alt6 hX h hπ'))
      · exact false_of_alt8 hX h hT hπ'
      · have hb := hL hsl
        have := congrArg (C124.toG h.isElemAbelian_Xq) hb
        rw [C124.toG, Subgroup.map_inf _ _ _ (C124.valHom_injective _), ← C124.toG,
          ← C124.toG, toG_commV_Xq h, toG_fixV_Xq h, hXL, C124.toG, Subgroup.map_bot,
          inf_comm] at this
        rw [this, Subgroup.card_bot] at hC2
        omega
  refine ⟨hXZU, by rw [inf_comm]; exact hC2, ?_, ?_, ?_⟩
  ·
    have hnatM : BinaryNaturalSL (autI hU M) ⊤ (fixV (autI hU M)) 3 1 := by
      rw [hXK]
      exact hnat
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnatM
    obtain ⟨α, hα, hsum⟩ := isSumNat_one_of_realizesVia hU hMU hπ
    rw [htoGM] at hsum
    exact ⟨α, hα, hsum⟩
  ·
    intro S hS
    have hSN : S ≤ Subgroup.normalizer (Uq M T L : Set G) := hS.1.trans hMU
    have hS' := isSylowTwoOf_autI hU hMU hS
    obtain ⟨F, iF, fF, hF, π, hπ⟩ := id hnat
    have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
    let e : ↥(StatedSL 3 F) ≃* ↥(autI hU M) :=
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ).trans (MulEquiv.subgroupCongr hXK.symm)
    obtain ⟨y, hyS, hy4⟩ := exists_orderOf_four hF2 e hS'
    have hirr := isIrrSec_of_natReal hπ
    have hFF := h.isFFModule_of_le_Z0q (isSecW_Uq h) (Uq_le_Z0q h.L_le)
    have h15 := (isSecW_Uq h).ms15Hyp h hSQ (commV_autI_Uq h) hCne hirr hFF
    have hyK : y ∈ autI hU L := hXK ▸ hS'.1 hyS
    have hfy := fixV_order_four IntMod.sq_eq_one h15 hnat hyK hy4
    have hfixS : fixV (autI hU S) = fixV (autI hU M) := by
      refine le_antisymm ?_ (fixV_anti (autI_mono hU hS.1))
      rw [hfixeq, ← hfy]
      exact fixV_anti ((Subgroup.zpowers_le).2 hyS)
    rw [← toG_fixV hU hSN, ← toG_fixV hU hMU, hfixS]
  ·
    intro S hS t htS ⟨u, hu, htu⟩
    have hSN : S ≤ Subgroup.normalizer (Uq M T L : Set G) := hS.1.trans hMU
    have hS' := isSylowTwoOf_autI hU hMU hS
    have htN : t ∈ Subgroup.normalizer (Uq M T L : Set G) := hSN htS
    set t' := convI hU ⟨t, htN⟩ with ht'
    have ht'S : t' ∈ autI hU S := convI_mem_autI hU htS htN
    have ht'1 : t' ≠ 1 := by
      intro h1
      apply htu
      have h2 := congrArg (fun φ : MulAut (IntMod (Uq M T L) hU) =>
        (φ (IntMod.mk hU ⟨u, hu⟩)).val) h1
      simp only [ht', convI_apply_val, MulAut.one_apply] at h2
      exact h2
    have hle := (hsyl _ hS').1 t' ht'S ht'1
    have hZt : Subgroup.zpowers t ≤ Subgroup.normalizer (Uq M T L : Set G) :=
      (Subgroup.zpowers_le).2 htN
    have hle' : commV (Subgroup.zpowers t') ≤ commV (autI hU (Subgroup.zpowers t)) :=
      commV_mono ((Subgroup.zpowers_le).2 (convI_mem_autI hU (Subgroup.mem_zpowers t) htN))
    have := (C124.toG_le_iff hU).2 (hle.trans hle')
    rw [htoGM, C124.toG_commV hU hZt, Subgroup.commutator_comm] at this
    exact this

end CaseIV

end CFSG.Quasithin.MS93.S32
