module

public import CFSG.RankThree.GF2n.Tim79aSec22Cw

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem V_inf_wOf_le_commutator : V ⊓ wOf V H ≤ ⁅wOf V H, xOf V H⁆ := by
  obtain ⟨h, hh, u, hu, v, hv, huv⟩ := hc.exists_noncommuting_conj
  set U := conjSubgroup h V with hU
  set L := V ⊓ Subgroup.normalizer (U : Set G) with hL
  set Lb := U ⊓ Subgroup.normalizer (V : Set G) with hLb
  have hLne : L ≠ ⊥ := hc.inf_normalizer_conj_ne_bot hh
  have hLV : L ≠ V := by
    intro hLV
    apply huv
    have hVN : V ≤ Subgroup.normalizer (U : Set G) := hLV ▸ inf_le_right
    have hk : conjSubgroup h⁻¹ U = V := by
      rw [hU, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hle : conjSubgroup h⁻¹ U ≤ Subgroup.normalizer (U : Set G) := by rw [hk]; exact hVN
    have habel := Tim77.tim77_2_3 (isElemAbelian_conjSubgroup hc.elemAb h)
      (isTI_conjSubgroup hc.ti h) (g := h⁻¹) hle
    rw [hk] at habel
    exact (congrArg Subtype.val (habel.1.is_comm.comm ⟨v, Subgroup.mem_sup_left hv⟩
      ⟨u, Subgroup.mem_sup_right hu⟩)).symm
  have S : Tim77.Prop24Setup V U L Lb (L ⊔ Lb) :=
    { elem := hc.elemAb
      ti := hc.ti
      conj := ⟨h, rfl⟩
      hL := rfl
      hLb := rfl
      hM := rfl
      ne_bot := hLne
      ne := hLV }
  have hOle : ∀ x ∈ V ⊓ wOf V H, x ∈ L := by
    intro x hx
    exact ⟨hx.1, hc.pCoreH_le_normalizer_conj hh (wOf_le_pCore V H hx.2)⟩
  obtain ⟨a, haV, haL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne inf_le_left hLV)
  obtain ⟨b, hbU, hbL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hVΩ : V ∈ omegaOf V H := ⟨1, H.one_mem, (conjSubgroup_one V).symm⟩
  have haX : a ∈ xOf V H := le_xOf hVΩ haV
  have hbX : b ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hh) hbU
  have htX : a * b ∈ xOf V H := (xOf V H).mul_mem haX hbX
  have htsup : a * b ∈ V ⊔ U :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left haV) (Subgroup.mem_sup_right hbU)
  have hNc : IsMulCommutative (wOf V H ⊓ (L ⊔ Lb) : Subgroup G) :=
    ⟨⟨fun x y => Subtype.ext
      (S.comm_M (Subgroup.mem_inf.mp x.2).2 (Subgroup.mem_inf.mp y.2).2)⟩⟩
  have htN : a * b ∈ Subgroup.normalizer ((wOf V H ⊓ (L ⊔ Lb) : Subgroup G) : Set G) :=
    mem_normalizer_inf (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H htX))
      (S.sup_le_normalizer_M htsup)
  have hfix : ∀ n ∈ (wOf V H ⊓ (L ⊔ Lb) : Subgroup G), (a * b) * n * (a * b)⁻¹ = n → n = 1 :=
    fun n hn hfixn => S.centralizer_mul_eq_one haV haL hbU hbL (Subgroup.mem_inf.mp hn).2
      (mul_inv_eq_iff_eq_mul.mp hfixn)
  intro x hx
  have hxN : x ∈ (wOf V H ⊓ (L ⊔ Lb) : Subgroup G) := ⟨hx.2, Subgroup.mem_sup_left (hOle x hx)⟩
  obtain ⟨m, hmN, rfl⟩ := exists_commutator_eq_of_fixed_eq_one hNc htN hfix x hxN
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hmN).1 htX

theorem commutator_wOf_xOf : ⁅wOf V H, xOf V H⁆ = wOf V H := by
  have hcomm : ∀ g ∈ H, conjSubgroup g ⁅wOf V H, xOf V H⁆ = ⁅wOf V H, xOf V H⁆ := by
    intro g hg
    have hW : conjSubgroup g (wOf V H) = wOf V H :=
      mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hg)
    have hX : conjSubgroup g (xOf V H) = xOf V H :=
      mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_xOf V H hg)
    unfold conjSubgroup at hW hX ⊢
    rw [Subgroup.map_commutator, hW, hX]
  refine le_antisymm (Subgroup.commutator_le.2 fun w hw x hx => ?_) ?_
  · have hxN := H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hx)
    have : x * w⁻¹ * x⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp hxN w⁻¹).mp ((wOf V H).inv_mem hw)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact (wOf V H).mul_mem hw (by simpa [mul_assoc] using this)
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    have h1 : conjSubgroup h (V ⊓ wOf V H) ≤ conjSubgroup h ⁅wOf V H, xOf V H⁆ :=
      Subgroup.map_mono hc.V_inf_wOf_le_commutator
    rw [hcomm h hh] at h1
    have e : conjSubgroup h (V ⊓ wOf V H) = conjSubgroup h V ⊓ inSubgroup (pCore 2) H := by
      rw [hc.V_inf_wOf_eq, conjSubgroup_inf]
      congr 1
      exact mem_normalizer_iff_conjSubgroup_eq.mp ((inSubgroup_pCore_two H).2.2 hh)
    rwa [e] at h1

end MinCex

end CFSG.RankThree.GF2n.Tim79a
