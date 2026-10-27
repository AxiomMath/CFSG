module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4NS
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSectionRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem br4_exists_cover {X S : Type} [Group X] [Finite X] [Group S] {A₁ A₂ : Subgroup S}
    (h : Br4TwoSimple S A₁ A₂) (h₁ : 3 ∣ Nat.card ↥A₁) (h₂ : 3 ∣ Nat.card ↥A₂) (θ : X →* S)
    (hθ : Function.Surjective θ) :
    ∃ (Ĝ : Type) (_ : Group Ĝ) (_ : Finite Ĝ) (θ' : Ĝ →* S), Function.Surjective θ' ∧
      IsPGroup 3 θ'.ker ∧ Group.IsPerfect Ĝ ∧ CFSG.pRank 3 Ĝ ≤ CFSG.pRank 3 X := by
  classical
  have : Finite S := Finite.of_surjective θ hθ
  obtain ⟨Y, hY, hYmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min
    {Y | Y.map θ = ⊤}
    ⟨⊤, show Subgroup.map θ ⊤ = ⊤ by rw [Subgroup.map_top, MonoidHom.range_eq_top.2 hθ]⟩
  let θY : ↥Y →* S := θ.comp Y.subtype
  have hθY : Function.Surjective θY := by
    intro s
    have : s ∈ Y.map θ := by rw [show Y.map θ = ⊤ from hY]; trivial
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  let K : Subgroup ↥Y := θY.ker
  have hKn : K.Normal := MonoidHom.normal_ker θY
  have hYcomm : ⁅Y, Y⁆ = Y := by
    have hmap : (⁅Y, Y⁆).map θ = ⊤ := by
      rw [Subgroup.map_commutator, hY, h.commutator_top]
    exact eq_of_le_of_not_lt (Subgroup.commutator_le_self Y) (hYmin ⁅Y, Y⁆ hmap)
  have hYperfect : Group.IsPerfect ↥Y := by
    rw [Group.isPerfect_def]
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hYcomm
  have hKfr : K ≤ frattini ↥Y := by
    refine CFSG.QuasithinUnique.Setup.Lift.le_frattini_of_forall_coatom K fun M hM => ?_
    by_contra hKM
    have hsup : M ⊔ K = ⊤ :=
      hM.2 (M ⊔ K) (lt_of_le_of_ne le_sup_left fun h => hKM (le_sup_right.trans h.symm.le))
    have hMtop : M.map θY = ⊤ := by
      rw [eq_top_iff]
      intro s _
      obtain ⟨z, rfl⟩ := hθY s
      have hz : z ∈ K ⊔ M := by rw [sup_comm, hsup]; trivial
      obtain ⟨k, hk, m, hm, rfl⟩ := CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul (A := M)
        (L := K) (by rw [Subgroup.normalizer_eq_top_iff.2 hKn]; exact le_top) hz
      refine ⟨m, hm, ?_⟩
      rw [map_mul, show θY k = 1 from hk, one_mul]
    have hM' : (M.map Y.subtype).map θ = ⊤ := by
      rw [Subgroup.map_map]; exact hMtop
    refine hYmin _ hM' (lt_of_le_of_ne (Subgroup.map_subtype_le M) fun heq => hM.1 ?_)
    rw [eq_top_iff]
    intro y _
    have hy : (y : X) ∈ M.map Y.subtype := by rw [heq]; exact y.2
    obtain ⟨m, hm, hmy⟩ := hy
    have : m = y := Subtype.ext hmy
    rw [← this]; exact hm
  have hKnil : Group.IsNilpotent ↥K :=
    CFSG.QuasithinUnique.Setup.Lift.nilpotent_of_le_frattini K hKfr
  let J : Subgroup ↥Y := CFSG.pPrimeCore 3 ↥Y
  have hJcop : ¬ 3 ∣ Nat.card ↥J :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y))
  have hJK : J ≤ K := by
    let N₁ : Subgroup S := J.map θY
    have hN₁n : N₁.Normal := (inferInstance : J.Normal).map θY hθY
    have hN₁cop : ¬ 3 ∣ Nat.card ↥N₁ :=
      fun hdvd => hJcop (hdvd.trans (Subgroup.card_map_dvd J θY))
    have hN₁bot : N₁ = ⊥ := h.eq_bot_of_not_dvd h₁ h₂ hN₁n hN₁cop
    intro j hj
    have hjN : θY j ∈ N₁ := ⟨j, hj, rfl⟩
    rw [hN₁bot, Subgroup.mem_bot] at hjN
    exact hjN
  let θbar : (↥Y ⧸ J) →* S := QuotientGroup.lift J θY (fun j hj => hJK hj)
  have hθbar : Function.Surjective θbar := fun s => by
    obtain ⟨y, rfl⟩ := hθY s
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hkerbar : IsPGroup 3 ↥θbar.ker := by
    have hmem : ∀ x : ↥K, θbar (QuotientGroup.mk (x : ↥Y)) = 1 := fun x => x.2
    let g : ↥K →* ↥θbar.ker :=
      ((QuotientGroup.mk' J).comp K.subtype).codRestrict θbar.ker fun x => hmem x
    have hg : Function.Surjective g := by
      intro z
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (z : ↥Y ⧸ J)
      have hyK : y ∈ K := by
        have : θbar (QuotientGroup.mk y) = 1 := by rw [hy]; exact z.2
        exact this
      exact ⟨⟨y, hyK⟩, Subtype.ext hy⟩
    have hnil : Group.IsNilpotent ↥θbar.ker := Group.nilpotent_of_surjective g hg
    exact CFSG.isPGroup_of_nilpotent_normal θbar.ker (MonoidHom.normal_ker θbar) hnil
      (CFSG.QuasithinUnique.Setup.Lift.pPrimeCore_quotient_eq_bot (p := 3) (G := ↥Y))
  have hGperfect : Group.IsPerfect (↥Y ⧸ J) := inferInstance
  have hrank : CFSG.pRank 3 (↥Y ⧸ J) ≤ CFSG.pRank 3 X := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd (p := 3)
        Nat.prime_three J hJcop,
      CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_le_of_injective (by norm_num : 1 < 3) Y.subtype
      Subtype.val_injective
  exact ⟨↥Y ⧸ J, inferInstance, inferInstance, θbar, hθbar, hkerbar, hGperfect, hrank⟩

end CFSG.LocalAnalysis.WeakClosure81

end
