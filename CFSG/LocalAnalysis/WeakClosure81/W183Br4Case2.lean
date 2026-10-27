module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Good
public import CFSG.LocalAnalysis.WeakClosure81.W183Br4NS
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3E9

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

theorem br4_false_case_two_aux {Y S : Type} [Group Y] [Finite Y] [Group S] {A B : Subgroup S}
    (h : Br4TwoSimple S A B) (gA : Br4Good ↥A) (gB : Br4Good ↥B) (θ : Y →* S)
    (hθ : Function.Surjective θ) (hQ : IsPGroup 3 θ.ker) (hr : CFSG.pRank 3 Y ≤ 3)
    (hAC : A ≤ (Subgroup.centralizer (θ.ker : Set Y)).map θ) : False := by
  haveI : Finite S := Finite.of_surjective θ hθ
  let C : Subgroup Y := Subgroup.centralizer (θ.ker : Set Y)
  let C₁ : Subgroup Y := C ⊓ A.comap θ
  have hCnorm : C.Normal := Subgroup.normal_centralizer
  have hC₁norm : C₁.Normal := by
    haveI : C.Normal := hCnorm
    haveI : (A.comap θ).Normal := h.normal₁.comap θ
    exact inferInstance
  have hC₁map : C₁.map θ = A := by
    apply le_antisymm
    · calc C₁.map θ ≤ (A.comap θ).map θ := Subgroup.map_mono inf_le_right
        _ = A := Subgroup.map_comap_eq_self_of_surjective hθ A
    · intro a ha
      obtain ⟨c, hcC, hca⟩ := Subgroup.mem_map.mp (hAC ha)
      exact Subgroup.mem_map.mpr
        ⟨c, ⟨hcC, Subgroup.mem_comap.mpr (hca ▸ ha)⟩, hca⟩
  let Sset : Set (Subgroup Y) := {J | J.Normal ∧ J ≤ C₁ ∧ J.map θ = A}
  have hC₁mem : C₁ ∈ Sset := ⟨hC₁norm, le_rfl, hC₁map⟩
  obtain ⟨J, hJmem, hJmin⟩ := wellFounded_lt.has_min Sset ⟨C₁, hC₁mem⟩
  have hJnorm : J.Normal := hJmem.1
  haveI : J.Normal := hJnorm
  have hJle : J ≤ C₁ := hJmem.2.1
  have hJmap : J.map θ = A := hJmem.2.2
  have hJJmem : ⁅J, J⁆ ∈ Sset := by
    refine ⟨Subgroup.commutator_normal J J, (Subgroup.commutator_le_left J J).trans hJle, ?_⟩
    rw [Subgroup.map_commutator, hJmap, h.commutator_left]
  have hJperf : ⁅J, J⁆ = J := by
    have hle : ⁅J, J⁆ ≤ J := Subgroup.commutator_le_left J J
    have hge : J ≤ ⁅J, J⁆ := by
      by_contra hnot
      exact hJmin ⁅J, J⁆ hJJmem (lt_of_le_of_ne hle fun heq => hnot (le_of_eq heq.symm))
    exact le_antisymm hle hge
  have hJperftop : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = ⊤ := by
    have hmap : (⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆).map J.subtype =
        (⊤ : Subgroup ↥J).map J.subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hJperf]
    exact Subgroup.map_injective J.subtype_injective hmap
  let Z : Subgroup ↥J := (J ⊓ θ.ker).subgroupOf J
  haveI hZnorm : Z.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : (J ⊓ θ.ker).Normal) J
  have hZcenter : Z ≤ Subgroup.center ↥J := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    have hyC : ((y : ↥J) : Y) ∈ C := (hJle y.2).1
    have hzQ : ((z : ↥J) : Y) ∈ θ.ker := (Subgroup.mem_subgroupOf.mp hz).2
    have hc := (Subgroup.mem_centralizer_iff.mp hyC) ((z : ↥J) : Y) hzQ
    exact Subtype.ext hc.symm
  have hZpg : IsPGroup 3 Z :=
    (hQ.to_le (inf_le_right : J ⊓ θ.ker ≤ θ.ker)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ⊓ θ.ker ≤ J)).symm
  let fJ : ↥J →* ↥(J.map θ) := θ.subgroupMap J
  have hfJker : fJ.ker = Z := by
    rw [Subgroup.ker_subgroupMap]
    exact (Subgroup.inf_subgroupOf_left θ.ker J).symm
  have hfJsurj : Function.Surjective fJ := MonoidHom.subgroupMap_surjective θ J
  have eJ : (↥J ⧸ Z) ≃* ↥A :=
    ((QuotientGroup.quotientMulEquivOfEq hfJker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fJ hfJsurj)).trans
      (MulEquiv.subgroupCongr hJmap)
  have hZbot : Z = ⊥ := gA.2.2 ↥J Z hZcenter hZpg hJperftop ⟨eJ⟩
  have hZbot' : (J ⊓ θ.ker).subgroupOf J = ⊥ := hZbot
  have hJQbot : J ⊓ θ.ker = ⊥ := by
    have hd : Disjoint (J ⊓ θ.ker) J := Subgroup.subgroupOf_eq_bot.mp hZbot'
    rw [disjoint_iff] at hd
    simpa [inf_assoc, inf_left_comm, inf_comm] using hd
  have eJA : ↥J ≃* ↥A :=
    ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).symm.trans eJ
  let P : Subgroup Y := B.comap θ
  have hPnorm : P.Normal := h.normal₂.comap θ
  haveI : P.Normal := hPnorm
  have hJPbot : J ⊓ P = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxJ : x ∈ J := hx.1
    have hxA : θ x ∈ A := by
      have := Subgroup.mem_map_of_mem θ hxJ
      rwa [hJmap] at this
    have hxB : θ x ∈ B := Subgroup.mem_comap.mp hx.2
    have hxAB : θ x ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [h.disj] at hxAB
    have hxq : x ∈ θ.ker := Subgroup.mem_bot.mp hxAB
    have : x ∈ J ⊓ θ.ker := ⟨hxJ, hxq⟩
    rw [hJQbot] at this
    exact this
  have hJPcomm : ⁅J, P⁆ = ⊥ := by
    have hle : ⁅J, P⁆ ≤ J ⊓ P := Subgroup.commutator_le_inf J P
    rw [hJPbot] at hle
    exact le_bot_iff.mp hle
  have hJcentP : J ≤ Subgroup.centralizer (P : Set Y) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hJPcomm
  obtain ⟨Ea, hEaelem, hEacard⟩ := gA.2.1
  let E1 : Subgroup ↥J :=
    Subgroup.map (eJA.symm : ↥A ≃* ↥J).toMonoidHom Ea
  have hE1elem : IsElemAbelian 3 E1 :=
    CFSG.Open.IsElemAbelian.map hEaelem (eJA.symm : ↥A ≃* ↥J).toMonoidHom
  have hE1card : Nat.card E1 = 9 := by
    rw [Subgroup.card_map_of_injective (f := (eJA.symm : ↥A ≃* ↥J).toMonoidHom)
      eJA.symm.injective, hEacard]
  let E1Y : Subgroup Y := Subgroup.map J.subtype E1
  have hE1Yelem : IsElemAbelian 3 E1Y :=
    CFSG.Open.IsElemAbelian.map hE1elem J.subtype
  have hE1Ycard : Nat.card E1Y = 9 := by
    rw [Subgroup.card_map_of_injective (f := J.subtype) J.subtype_injective, hE1card]
  obtain ⟨Eb, hEbelem, hEbcard⟩ := gB.2.1
  have hBrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥B) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hEbelem (by rw [hEbcard]; norm_num)
  have hPmap : P.map θ = B := Subgroup.map_comap_eq_self_of_surjective hθ B
  let ψ : ↥P →* ↥B :=
    (MulEquiv.subgroupCongr hPmap).toMonoidHom.comp (θ.subgroupMap P)
  have hψsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨x, hx⟩ :=
      MonoidHom.subgroupMap_surjective θ P ((MulEquiv.subgroupCongr hPmap).symm b)
    exact ⟨x, by simp [ψ, hx]⟩
  obtain ⟨E2, hE2elem, hE2card⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22ine229u3e9_exists_elemAbelian_sq
      ψ hψsurj Nat.prime_three (by norm_num) hBrank
  let E2Y : Subgroup Y := Subgroup.map P.subtype E2
  have hE2Yelem : IsElemAbelian 3 E2Y :=
    CFSG.Open.IsElemAbelian.map hE2elem P.subtype
  have hE2Ycard : Nat.card E2Y = 9 := by
    rw [Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective, hE2card]
    norm_num
  have hcomm : ∀ a ∈ E1Y, ∀ b ∈ E2Y, a * b = b * a := by
    intro a ha b hb
    have haJ : a ∈ J := Subgroup.map_subtype_le E1 ha
    have hbP : b ∈ P := Subgroup.map_subtype_le E2 hb
    exact ((Subgroup.mem_centralizer_iff.mp (hJcentP haJ)) b hbP).symm
  have hdisj : E1Y ⊓ E2Y = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxJ : x ∈ J := Subgroup.map_subtype_le E1 hx.1
    have hxP : x ∈ P := Subgroup.map_subtype_le E2 hx.2
    have : x ∈ J ⊓ P := ⟨hxJ, hxP⟩
    rw [hJPbot] at this
    exact this
  obtain ⟨hElemsup, hCardsup⟩ := br4_elem_sup hcomm hdisj hE1Yelem hE2Yelem hE1Ycard hE2Ycard
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hElemsup (by rw [hCardsup]; norm_num)
  have hr' : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 Y]
    exact hr
  omega

theorem br4_false_case_two {Y S : Type} [Group Y] [Finite Y] [Group S] {A₁ A₂ : Subgroup S}
    (h : Br4TwoSimple S A₁ A₂) (g₁ : Br4Good ↥A₁) (g₂ : Br4Good ↥A₂) (θ : Y →* S)
    (hθ : Function.Surjective θ) (hQ : IsPGroup 3 θ.ker) (hr : CFSG.pRank 3 Y ≤ 3)
    (hC : ¬ Subgroup.centralizer (θ.ker : Set Y) ≤ θ.ker) : False := by
  haveI : Finite S := Finite.of_surjective θ hθ
  let C : Subgroup Y := Subgroup.centralizer (θ.ker : Set Y)
  have hCnorm : C.Normal := Subgroup.normal_centralizer
  let M : Subgroup S := C.map θ
  have hMnorm : M.Normal := hCnorm.map θ hθ
  have hMne : M ≠ ⊥ := by
    have hC' : ¬ (C : Set Y) ⊆ (θ.ker : Set Y) := hC
    obtain ⟨x, hxC, hxQ⟩ := Set.not_subset.mp hC'
    intro hbot
    have hxM : θ x ∈ M := Subgroup.mem_map_of_mem θ hxC
    rw [hbot] at hxM
    exact hxQ (MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hxM))
  rcases h.le_or_le_of_ne_bot hMnorm hMne with hA | hA
  · exact br4_false_case_two_aux h g₁ g₂ θ hθ hQ hr hA
  · exact br4_false_case_two_aux h.symm g₂ g₁ θ hθ hQ hr hA

end CFSG.LocalAnalysis.WeakClosure81

end
