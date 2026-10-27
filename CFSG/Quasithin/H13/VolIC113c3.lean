module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma30Iso
public import CFSG.Quasithin.H13.VolIC113

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem blockZ_eq_bot_of_alt3 (hL : IsShort2 L) (h3 : IsAltType L 3) : blockZ L = ⊥ := by
  obtain ⟨-, -, -, -, -, hZ, -⟩ := hL.alt3_structure h3
  rw [eq_bot_iff]
  rintro z ⟨hzU, hzC⟩
  exact hZ z ((C1.blockU_le_blockQ hL).trans (C1.blockQ_le L) hzU) fun l hl =>
    (Subgroup.mem_centralizer_iff.mp hzC l hl).symm

theorem pCoreOf_eq_sup_of_alt3 (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (h3 : IsAltType L 3) :
    pCoreOf 2 (L ⊔ T) = blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨-, -, -, hUab, -, -, c, hcL, -, hcN, hcfp, hLc⟩ := hL.alt3_structure h3
  refine le_antisymm (fun q hq => ?_)
    (sup_le (blockU_le_pCoreOf hL hTN) (inf_centralizer_le_pCoreOf hL hT hTN))
  have hd : q * c * q⁻¹ * c⁻¹ ∈ blockU L := commutator_mem_blockU hL hTN hq hcL
  have hcm : ∀ u ∈ blockU L, c * u⁻¹ * c⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hcN u⁻¹).mp (inv_mem hu)
  let f : ↥(blockU L) → ↥(blockU L) := fun u =>
    ⟨(u : G) * (c * (u : G)⁻¹ * c⁻¹), mul_mem u.2 (hcm u u.2)⟩
  have hfi : Function.Injective f := by
    intro u v huv
    have h1 : (u : G) * (c * (u : G)⁻¹ * c⁻¹) = (v : G) * (c * (v : G)⁻¹ * c⁻¹) :=
      congrArg Subtype.val huv
    set w : G := (v : G)⁻¹ * u with hw
    have hwU : w ∈ blockU L := mul_mem (inv_mem v.2) u.2
    have hwc : c * w * c⁻¹ = w := by
      rw [hw]
      calc c * ((v : G)⁻¹ * u) * c⁻¹ =
          (c * (v : G)⁻¹ * c⁻¹) * ((u : G) * (c * (u : G)⁻¹ * c⁻¹))⁻¹ * u := by group
        _ = (c * (v : G)⁻¹ * c⁻¹) * ((v : G) * (c * (v : G)⁻¹ * c⁻¹))⁻¹ * u := by rw [h1]
        _ = (v : G)⁻¹ * u := by group
    by_contra hne
    have hw1 : w ≠ 1 := by
      intro hw1
      apply hne
      apply Subtype.ext
      have : (v : G)⁻¹ * u = 1 := hw1
      rw [inv_mul_eq_one] at this
      exact this.symm
    exact hcfp w hwU hw1 hwc
  have hfs : Function.Surjective f := Finite.injective_iff_surjective.mp hfi
  obtain ⟨u₀, hu₀⟩ := hfs ⟨q * c * q⁻¹ * c⁻¹, hd⟩
  have hu₀' : (u₀ : G) * (c * (u₀ : G)⁻¹ * c⁻¹) = q * c * q⁻¹ * c⁻¹ := congrArg Subtype.val hu₀
  set d : G := (u₀ : G)⁻¹ * q with hd'
  have hdc : d * c = c * d := by
    have : d * c * d⁻¹ = c := by
      rw [hd']
      calc (u₀ : G)⁻¹ * q * c * ((u₀ : G)⁻¹ * q)⁻¹ =
          (u₀ : G)⁻¹ * (q * c * q⁻¹ * c⁻¹) * c * u₀ := by group
        _ = (u₀ : G)⁻¹ * ((u₀ : G) * (c * (u₀ : G)⁻¹ * c⁻¹)) * c * u₀ := by rw [hu₀']
        _ = c := by group
    calc d * c = (d * c * d⁻¹) * d := by group
      _ = c * d := by rw [this]
  have hdU : ∀ u ∈ blockU L, d * u = u * d := by
    intro u hu
    have h1 : q * u = u * q := pCoreOf_comm_blockU hL hT hTN hq hu
    have h2 : (u₀ : G) * u = u * u₀ := hUab _ u₀.2 _ hu
    rw [hd']
    calc (u₀ : G)⁻¹ * q * u = (u₀ : G)⁻¹ * (u * q) := by rw [mul_assoc, h1]
      _ = u * ((u₀ : G)⁻¹ * q) := by
        have h3 : (u₀ : G)⁻¹ * u = u * (u₀ : G)⁻¹ := by
          calc (u₀ : G)⁻¹ * u = (u₀ : G)⁻¹ * (u * u₀) * (u₀ : G)⁻¹ := by group
            _ = (u₀ : G)⁻¹ * ((u₀ : G) * u) * (u₀ : G)⁻¹ := by rw [h2]
            _ = u * (u₀ : G)⁻¹ := by group
        rw [← mul_assoc, h3, mul_assoc]
  have hdL : d ∈ Subgroup.centralizer (L : Set G) := by
    have hle : L ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [hLc]
      refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hdU u hu).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hdc.symm
    exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hl)
  have hdT : d ∈ T := mul_mem (inv_mem (hT.pCoreOf_le (blockU_le_pCoreOf hL hTN u₀.2)))
    (hT.pCoreOf_le hq)
  have hq' : q = (u₀ : G) * d := by rw [hd']; group
  rw [hq']
  exact mul_mem (Subgroup.mem_sup_left u₀.2) (Subgroup.mem_sup_right ⟨hdT, hdL⟩)

theorem nonempty_mulEquiv_alt4 (hL : IsShort2 L) (h3 : IsAltType L 3) :
    Nonempty (↥L ≃* alternatingGroup (Fin 4)) :=
  (DoubleA3.IsA4Block.of_alt3 hL h3).nonempty_mulEquiv

theorem blockQ_eq_blockU_of_alt3 (hL : IsShort2 L) (h3 : IsAltType L 3) : blockQ L = blockU L :=
  (hL.alt3_structure h3).1

end CFSG.Quasithin.H13.VolI
