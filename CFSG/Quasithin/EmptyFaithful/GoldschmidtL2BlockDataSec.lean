module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockData

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

namespace L246

variable {G : Type} [Group G] [Finite G] {X T L : Subgroup G}

namespace BlockDataS

variable {n : ℕ} (D : BlockDataS X T L n)

include D

theorem secHyp {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    Bridge.L2Block.SecHypS (autI D.elem L) (autI D.elem A) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L)) := by
  have hV := D.elem
  have hLN := D.LN
  have hAn : A ≤ Subgroup.normalizer (L : Set G) := D.A_le_normalizer hA
  have hshort : IsShort2 L := D.block.1
  have hpsl := D.isPSL_autI
  refine ⟨RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (A5.C25.fusionIsBenderGroup_of_isPSL hpsl),
    nonab_of_isPSL hpsl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a ha l hl
    obtain ⟨a₀, ha₀, rfl⟩ := (mem_autI hV).1 ha
    obtain ⟨l₀, hl₀, rfl⟩ := (mem_autI hV).1 hl
    have h1 : (a₀ : G) * (l₀ : G) * (a₀ : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hAn ha₀) (l₀ : G)).1 hl₀
    refine (mem_autI hV).2 ⟨a₀ * l₀ * a₀⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ·
    by_contra hcon
    push Not at hcon
    apply hAc
    rw [Subgroup.commutator_le]
    intro l hl a ha
    have haN : a ∈ Subgroup.normalizer (VZ T X : Set G) := hA.1.trans D.TX |>.trans D.XN <| ha
    have hlN : l ∈ Subgroup.normalizer (VZ T X : Set G) := hLN hl
    have := hcon (convI hV ⟨a, haN⟩) (convI_mem_autI hV ha haN) (convI hV ⟨l, hlN⟩)
      (convI_mem_autI hV hl hlN)
    exact (convI_comm_iff hV hlN haN).1 this.symm
  · intro φ hφ
    obtain ⟨l, hl, rfl⟩ := (mem_autI hV).1 hφ
    exact convI_mem_stabSub_intSub hV l.2 (C1.le_normalizer_blockU L hl)
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
    exact convI_mem_stabSub_intSub hV a.2 (C1.mem_normalizer_blockU (hAn ha))
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
    exact convI_mem_stabSub_intSub hV a.2 (C1.mem_normalizer_blockZ (hAn ha))
  ·
    ext v
    rw [Subgroup.mem_inf, mem_intSub, mem_intSub, mem_fixV_autI hV hLN v]
    exact Subgroup.mem_inf
  · refine lt_of_le_of_ne (fun v hv => ?_) ?_
    · exact (inf_le_left : blockZ L ≤ blockU L) hv
    · intro h
      obtain ⟨u, huU, huZ⟩ := IsConcreteLE.exists_of_lt hshort.2.2.2.2.1
      have hmem : IntMod.mk hV ⟨u, D.uV huU⟩ ∈ intSub hV (blockU L) := huU
      rw [← h] at hmem
      exact huZ hmem
  · intro J hZJ hJU hJinv
    have hZV : blockZ L ≤ VZ T X := (inf_le_left : blockZ L ≤ blockU L).trans D.uV
    have hnorm : L ≤ Subgroup.normalizer (ambSub J : Set G) := by
      refine le_normalizer_of_forall_conj fun l hl w hw => ?_
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨convI hV ⟨l, hLN hl⟩ v, hJinv _ (convI_mem_autI hV hl (hLN hl)) v hv,
        convI_apply_val hV _ v⟩
    rcases hshort.2.2.2.2.2 (ambSub J) (le_ambSub hZV hZJ) (ambSub_le hJU) hnorm with h | h
    · left; rw [← intSub_ambSub J, h]
    · right; rw [← intSub_ambSub J, h]
  · intro u hu
    have h1 : u.val ∈ blockU L := hu
    have h2 : ⁅L, blockU L⁆ = blockU L := by
      rw [Subgroup.commutator_comm]; exact C1.commutator_blockU hshort
    have hle : ⁅L, blockU L⁆ ≤
        (commSub (intSub hV (blockU L)) (autI hV L)).map (valHom (VZ T X) hV) := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨l, hl, w, hw, rfl⟩
      refine ⟨convI hV ⟨l, hLN hl⟩ (IntMod.mk hV ⟨w, D.uV hw⟩) * (IntMod.mk hV ⟨w, D.uV hw⟩)⁻¹,
        ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨convI hV ⟨l, hLN hl⟩, convI_mem_autI hV hl (hLN hl),
          IntMod.mk hV ⟨w, D.uV hw⟩, hw, rfl⟩
      · show (convI hV ⟨l, hLN hl⟩ (IntMod.mk hV ⟨w, D.uV hw⟩) *
            (IntMod.mk hV ⟨w, D.uV hw⟩)⁻¹).val = ⁅l, w⁆
        rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
        rfl
    rw [h2] at hle
    obtain ⟨x, hx, hxu⟩ := hle h1
    have hxu' : x = u := IntMod.val_injective hxu
    rwa [← hxu']

end BlockDataS

end L246

end CFSG.QuasithinUnique
