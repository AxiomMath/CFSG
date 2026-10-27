module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Vol2.Ch3zBlocks
public import TauCeti.GroupTheory.Perm.FinThree.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s15k_jp_s3_altDn_three_ker : (FFModel.altDn 3).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 3 * G6.allOnes 3 = 1 := by decide +kernel
  have hnot : G6.allOnes 3 ∉ G6.coreMod 3 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 3) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

theorem s15k_jp_s3 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (hst : ∀ j ∈ J, ∀ r ∈ R, j r ∈ R)
    (hR : Nat.card R = 4) (hJ : Nat.card J = 6)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ IsCyclicOrd ↥⁅J, J⁆ 3 ∧
      AlternatingNatural ⁅J, J⁆ R ⊥ 3 := by
  classical
  have hcore : G6.IsSymCore J R 3 :=
    CFSG.Quasithin.Ch3z.isSymCore_three_of_klein hW hR hst hfaith hJ
  unfold G6.IsSymCore G6.IsSymModule at hcore
  obtain ⟨θ, β, hβe, hβr, hβk⟩ := hcore
  let ψ : Equiv.Perm (Fin 3) →* MulAut W := J.subtype.comp θ.symm.toMonoidHom
  have hψ : Function.Injective ψ := fun a b hab => θ.symm.injective (Subtype.ext hab)
  have hrange : ψ.range = J := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (θ.symm g).2
    · intro hx
      refine ⟨θ ⟨x, hx⟩, ?_⟩
      change ((θ.symm (θ ⟨x, hx⟩) : ↥J) : MulAut W) = x
      simp
  have hA : alternatingGroup (Fin 3) = commutator (Equiv.Perm (Fin 3)) :=
    TauCeti.commutator_perm_fin_three_eq_alternatingGroup.symm
  have hmap : (alternatingGroup (Fin 3)).map ψ = ⁅J, J⁆ := by
    rw [hA]
    show (⁅(⊤ : Subgroup (Equiv.Perm (Fin 3))),
        (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆).map ψ = ⁅J, J⁆
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
  have hcard : Nat.card ↥⁅J, J⁆ = 3 := by
    rw [← hmap, Subgroup.card_map_of_injective hψ,
      TauCeti.card_alternatingGroup_fin_three]
  have hcyc : IsCyclic ↥⁅J, J⁆ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hcard
  have hidx : (⁅J, J⁆.subgroupOf J).index ≤ 2 := by
    have hle : ⁅J, J⁆ ≤ J := Subgroup.commutator_le_self J
    have h := Subgroup.relIndex_mul_card (H := ⁅J, J⁆) (K := J)
    rw [inf_eq_left.2 hle] at h
    rw [hcard, hJ] at h
    have : (⁅J, J⁆).relIndex J = 2 := by omega
    show (⁅J, J⁆).relIndex J ≤ 2
    omega
  have hker : (FFModel.altDn 3).ker = ⊥ := s15k_jp_s3_altDn_three_ker
  let π' : ↥(alternatingGroup (Fin 3)) →* ↥⁅J, J⁆ :=
    (ψ.comp (alternatingGroup (Fin 3)).subtype).codRestrict ⁅J, J⁆
      (fun x => hmap ▸ Subgroup.mem_map_of_mem ψ x.2)
  let f : ↥(FFModel.altDn 3).sec →* ↥R :=
    β.codRestrict R (fun u => hβr ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩)
  have hfinj : Function.Injective f := by
    intro a b hab
    exact (MonoidHom.ker_eq_bot_iff β).mp hβk (congrArg Subtype.val hab)
  have hfsurj : Function.Surjective f := by
    intro r
    have hr : (r : W) ∈ β.range := by rw [hβr]; exact r.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hr
    exact ⟨c, Subtype.ext hc⟩
  let ι : ↥(FFModel.altDn 3).sec ≃* ↥R := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let N : Subgroup ↥(FFModel.altDn 3).sec :=
    (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec
  have hNbot : N = ⊥ := by
    change (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec = ⊥
    rw [hker, Subgroup.bot_subgroupOf]
  let β' : ↥R →* ↥(FFModel.altDn 3).sec ⧸ N := (QuotientGroup.mk' N).comp ι.symm.toMonoidHom
  have hmk_inj : Function.Injective (QuotientGroup.mk' N) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hNbot])
  have hmod : AlternatingNatural ⁅J, J⁆ R ⊥ 3 := by
    unfold AlternatingNatural FFModel.Realizes FFModel.RealizesVia
    refine ⟨π', ?_⟩
    refine ⟨?_, bot_le, inf_le_right, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro y
      have hy : (y : MulAut W) ∈ (alternatingGroup (Fin 3)).map ψ := by
        rw [hmap]; exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    ·
      intro h u hu
      exact hst (h : MulAut W) (Subgroup.commutator_le_self J h.2) u hu
    ·
      intro h z hz
      rw [Subgroup.mem_bot] at hz
      rw [Subgroup.mem_bot, hz, map_one]
    ·
      intro γ m hm
      let g : ↥(alternatingGroup (Fin 3)) := γ
      exact G6.permAct_mem_coreMod (g : Equiv.Perm (Fin 3)) hm
    ·
      intro γ m hm
      let g : ↥(alternatingGroup (Fin 3)) := γ
      rw [hker, Subgroup.mem_bot] at hm
      rw [hker, Subgroup.mem_bot, hm]
      exact map_one (G6.permAct 3 (g : Equiv.Perm (Fin 3)))
    ·
      refine ⟨β', ?_, ?_, ?_⟩
      ·
        intro x
        obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N x
        obtain ⟨u, rfl⟩ := ι.symm.surjective s
        exact ⟨u, rfl⟩
      ·
        intro u
        rw [Subgroup.mem_bot]
        constructor
        · intro h
          have h1 : ι.symm u = 1 :=
            hmk_inj (h.trans (map_one (QuotientGroup.mk' N)).symm)
          exact congrArg Subtype.val (ι.symm.injective (h1.trans (map_one ι.symm).symm))
        · intro h
          have hu : u = 1 := Subtype.ext (by simpa using h)
          rw [hu, map_one]
      ·
        intro γ u m hu hm hβ
        let γ' : ↥(alternatingGroup (Fin 3)) := γ
        have hsym : ι.symm u = m := by
          apply hmk_inj
          rw [QuotientGroup.mk'_apply (N := N) m]
          exact hβ
        have huW : (u : W) = β m := by
          have happ := ι.apply_symm_apply u
          rw [hsym] at happ
          exact (congrArg Subtype.val happ).symm
        have hmain : ((π' γ' : ↥⁅J, J⁆) : MulAut W) (u : W) =
            β (G6.coreAct 3 (γ' : Equiv.Perm (Fin 3)) m) := by
          change (ψ (γ' : Equiv.Perm (Fin 3))) (u : W) =
            β (G6.coreAct 3 (γ' : Equiv.Perm (Fin 3)) m)
          change ((θ.symm (γ' : Equiv.Perm (Fin 3)) : ↥J) : MulAut W) (u : W) =
            β (G6.coreAct 3 (γ' : Equiv.Perm (Fin 3)) m)
          rw [huW]
          have he := hβe (θ.symm (γ' : Equiv.Perm (Fin 3))) m
          simp only [MulEquiv.apply_symm_apply] at he
          exact he.symm
        show (QuotientGroup.mk' N)
            (ι.symm ⟨((π' γ' : ↥⁅J, J⁆) : MulAut W) (u : W), hu⟩) =
          (QuotientGroup.mk' N)
            ⟨(FFModel.altDn 3).act γ (m : (FFModel.altDn 3).Amb), hm⟩
        refine congrArg (QuotientGroup.mk' N) ?_
        rw [MulEquiv.symm_apply_eq]
        apply Subtype.ext
        show ((π' γ' : ↥⁅J, J⁆) : MulAut W) (u : W) =
          (ι ⟨(FFModel.altDn 3).act γ (m : (FFModel.altDn 3).Amb), hm⟩ : W)
        rw [hmain]
        exact (congrArg β (Subtype.ext rfl)).trans rfl
  exact ⟨hidx, ⟨hcyc, hcard⟩, hmod⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
