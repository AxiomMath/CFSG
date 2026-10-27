module

public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt6BA
public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private instance s16c11_v1_coreMod_commGroup : CommGroup ↥(G6.coreMod 6) :=
  { (inferInstance : Group ↥(G6.coreMod 6)) with
    mul_comm := fun a b => Subtype.ext (mul_comm (a : G6.PermMod 6) (b : G6.PermMod 6)) }

private theorem s16c11_v1_symCore_six_self :
    (G64.symCoreModel 6).Realizes (V := ↥(G6.coreMod 6)) (G6.coreAct 6).range ⊤ ⊥ := by
  unfold G64.symCoreModel
  let N : Subgroup ↥(G6.coreMod 6) :=
    (⊥ : Subgroup (G6.PermMod 6)).subgroupOf (G6.coreMod 6)
  have hN : N = ⊥ := by
    ext x
    show x ∈ (⊥ : Subgroup (G6.PermMod 6)).subgroupOf (G6.coreMod 6) ↔
      x ∈ (⊥ : Subgroup ↥(G6.coreMod 6))
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  haveI : N.Normal := by rw [hN]; infer_instance
  refine ⟨(G6.coreAct 6).rangeRestrict, MonoidHom.rangeRestrict_surjective _, bot_le, bot_le,
    (fun h u _ => Subgroup.mem_top ((h : MulAut ↥(G6.coreMod 6)) u)), (fun _ z hz => ?_),
    (fun γ m hm => G6.permAct_mem_coreMod γ hm), (fun γ m hm => ?_), ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · rw [Subgroup.mem_bot] at hm ⊢
    rw [hm]
    exact map_one _
  · refine ⟨(QuotientGroup.mk' N).comp
        (Subgroup.subtype (⊤ : Subgroup ↥(G6.coreMod 6))), ?_, ?_, ?_⟩
    · intro x
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact ⟨⟨m, Subgroup.mem_top m⟩, rfl⟩
    · intro u
      have hker : Function.Injective (QuotientGroup.mk' N) := by
        intro a b hab
        have h := (QuotientGroup.eq).1 hab
        rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at h
        exact h
      change (QuotientGroup.mk' N) (u : ↥(G6.coreMod 6)) = 1 ↔
        (u : ↥(G6.coreMod 6)) ∈ (⊥ : Subgroup ↥(G6.coreMod 6))
      constructor
      · intro h
        rw [Subgroup.mem_bot]
        exact hker (by rw [h, map_one])
      · intro h
        rw [Subgroup.mem_bot] at h
        rw [h, map_one]
    · intro γ u m hu hm hβu
      let m' : ↥(G6.coreMod 6) := m
      have hβu' : (QuotientGroup.mk' N) (Subgroup.subtype (⊤ : Subgroup ↥(G6.coreMod 6)) u) =
          QuotientGroup.mk m' := hβu
      have h2 : (Subgroup.subtype (⊤ : Subgroup ↥(G6.coreMod 6)) u) = m' := by
        have h2 := (QuotientGroup.eq).1 hβu'
        rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at h2
        exact h2
      have h2' : (u : ↥(G6.coreMod 6)) = m' := h2
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show G6.permAct 6 γ ((u : ↥(G6.coreMod 6)) : G6.PermMod 6) =
        G6.permAct 6 γ (m' : G6.PermMod 6)
      rw [h2']

theorem s16c11_v1_symCore_six_of_cover {J : Type} [CommGroup J] [Finite J]
    (hJ2 : ∀ j : J, j ^ 2 = 1) {H H₀ : Subgroup (MulAut J)} (hHH₀ : H ≤ H₀)
    (hS : IsSym ↥H₀ 6) (hA : UC22.IsAlt ↥H 6) (hcomm : commV H = ⊤)
    (hR : (FFModel.altDn 6).Realizes H ⊤ (fixV H)) (hne : fixV H ≠ ⊥) :
    (G64.symCoreModel 6).Realizes H₀ ⊤ ⊥ := by
  classical
  rcases CFSG.Quasithin.H13.VolI.altNaturalCoverSix_holds (V := J) hJ2 H (fixV H) le_rfl hcomm hR
    with hZ | hcov
  · exact absurd hZ hne
  obtain ⟨hZcard, hJcard, hcore⟩ := hcov
  obtain ⟨πc, hπc⟩ := hcore
  obtain ⟨E₀, hE₀⟩ :=
    CFSG.Quasithin.G64.RealizesVia.exists_secEquiv (D := CFSG.Quasithin.H13.altCoreModel 6)
      rfl hπc
  let E : J ≃* ↥(G6.coreMod 6) := E₀
  have hE : ∀ (γ : ↥(alternatingGroup (Fin 6))) (v : J),
      E (((πc γ : ↥H) : MulAut J) v) = (G6.coreAct 6 γ) (E v) := by
    intro γ v
    exact Subtype.ext (hE₀ γ v)
  have hE'' : ∀ γ : ↥(alternatingGroup (Fin 6)),
      MulAut.congr E (πc γ) = G6.coreAct 6 γ := by
    intro γ
    apply MulEquiv.ext
    intro w
    change E (((πc γ : ↥H) : MulAut J) (E.symm w)) = (G6.coreAct 6 γ) w
    rw [hE γ (E.symm w), MulEquiv.apply_symm_apply]
  obtain ⟨eS⟩ := hS
  obtain ⟨eA⟩ := hA
  have hH0card : Nat.card ↥H₀ = 720 := by
    rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hHcard : Nat.card ↥H = 360 := by
    rw [Nat.card_congr eA.toEquiv,
      CFSG.Quasithin.H13.card_alternatingGroup_fin 6 (by norm_num)]
    norm_num
  have hcard : Nat.card ↥H₀ = 2 * Nat.card ↥H := by rw [hH0card, hHcard]
  have hnormal : ∀ x ∈ H₀, H.map (MulAut.conj x).toMonoidHom = H :=
    s16c11_map_conj_eq_of_card_two_mul hHH₀ hcard
  have hAmap : H.map (MulAut.congr E).toMonoidHom = s16c11_v1_coreA := by
    ext x
    constructor
    · intro hx
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨γ, hγ⟩ := hπc.1 ⟨h, hh⟩
      let γ' : ↥(alternatingGroup (Fin 6)) := γ
      have hγ' : πc γ' = ⟨h, hh⟩ := hγ
      refine MonoidHom.mem_range.mpr ⟨γ', ?_⟩
      change G6.coreAct 6 (γ' : Equiv.Perm (Fin 6)) = MulAut.congr E h
      rw [← hE'' γ']
      exact congrArg (fun y : MulAut J => MulAut.congr E y) (congrArg Subtype.val hγ')
    · intro hx
      simp only [s16c11_v1_coreA] at hx
      obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hx
      exact Subgroup.mem_map.mpr ⟨πc γ, (πc γ).2, (hE'' γ).trans hγ⟩
  have hnormalA : ∀ x ∈ H₀, MulAut.congr E (x : MulAut J) ∈ (G6.coreAct 6).range := by
    intro x hx
    have hcomp : (MulAut.congr E).toMonoidHom.comp
          (MulAut.conj (x : MulAut J)).toMonoidHom =
        (MulAut.conj (MulAut.congr E (x : MulAut J))).toMonoidHom.comp
          (MulAut.congr E).toMonoidHom := by
      refine MonoidHom.ext (fun f => ?_)
      refine MulEquiv.ext (fun u => ?_)
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
    have hmap : (H.map (MulAut.congr E).toMonoidHom).map
          (MulAut.conj (MulAut.congr E (x : MulAut J))).toMonoidHom =
        H.map (MulAut.congr E).toMonoidHom := by
      rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hnormal x hx]
    have hmem : MulAut.congr E (x : MulAut J) ∈
        Subgroup.normalizer ((H.map (MulAut.congr E).toMonoidHom) :
          Set (MulAut ↥(G6.coreMod 6))) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap
    rw [hAmap] at hmem
    rwa [s16c11_v1_coreAct_range_normalizer] at hmem
  let rHom : ↥H₀ →* ↥((G6.coreAct 6).range) :=
    { toFun := fun x => ⟨MulAut.congr E (x : MulAut J), hnormalA x x.2⟩
      map_one' := Subtype.ext (map_one (MulAut.congr E))
      map_mul' := fun x y =>
        Subtype.ext (map_mul (MulAut.congr E) (x : MulAut J) (y : MulAut J)) }
  have hinj : Function.Injective rHom := by
    intro x y hxy
    have h1 : (x : MulAut J) = (y : MulAut J) :=
      (MulAut.congr E).injective (Subtype.ext_iff.mp hxy)
    exact Subtype.ext h1
  have hle : Nat.card ↥((G6.coreAct 6).range) ≤ 720 := by
    have h1 : Nat.card ↥((G6.coreAct 6).range) ≤ Nat.card (Equiv.Perm (Fin 6)) :=
      Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have h2 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num [Nat.factorial]
    rwa [h2] at h1
  have hge : Nat.card ↥((G6.coreAct 6).range) ≥ 720 := by
    have h1 : Nat.card ↥H₀ ≤ Nat.card ↥((G6.coreAct 6).range) :=
      Nat.card_le_card_of_injective _ hinj
    rwa [hH0card] at h1
  have hKcard : Nat.card ↥((G6.coreAct 6).range) = 720 := le_antisymm hle hge
  have hbij : Function.Bijective rHom :=
    hinj.bijective_of_nat_card_le (by rw [hKcard, hH0card])
  let r : ↥H₀ ≃* ↥((G6.coreAct 6).range) := MulEquiv.ofBijective rHom hbij
  let j : ↥(⊤ : Subgroup J) ≃* ↥(G6.coreMod 6) :=
    (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J).trans E
  refine CFSG.Quasithin.H.FFModel.realizes_of_equiv (D := G64.symCoreModel 6) (V := J)
    (H := H₀) (U := ⊤) (K := (G6.coreAct 6).range) (fun _ _ _ _ => Subgroup.mem_top _) j r ?_
    s16c11_v1_symCore_six_self
  · intro h u
    change E ((h : MulAut J) (E.symm (E (u : J)))) = E ((h : MulAut J) (u : J))
    rw [MulEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
