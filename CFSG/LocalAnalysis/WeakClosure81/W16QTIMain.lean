module

public import CFSG.LocalAnalysis.WeakClosure81.W16QTIU3
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateSzProof
public import CFSG.LieType.SuzukiSubgroups.Input

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem two_mul_le_mSub_of_sz
    (d : DichCfg M V₀ V U S H φ) [Finite X] (hK : KGroup1616Input)
    (hn : 1 < E3.mQuot V (iSub16 V H))
    (hSz : CFSG.Quasithin.IsSz (E3.mQuot V (iSub16 V H)) X) :
    2 * E3.mQuot V (iSub16 V H) ≤ mSub V₀ := by
  set n := E3.mQuot V (iSub16 V H) with hndef
  set Y := SevenK.barSub (conjClosure V H) φ V with hY
  have hYc : Nat.card Y = 2 ^ n := d.shape.1
  have hYel : IsElemAbelian 2 Y := d.isElemAbelian_barSub
  haveI hsimple : IsSimpleGroup X := hK.sz_simple n X hn hSz
  have hcard := hK.sz_card n X hn hSz
  have h2 : 2 < Nat.card Y := by
    rw [hYc]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g, hg⟩ := SevenK.twoConjugateGenerationSz_of_suzukiSubgroupInput
    CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds X n hn hSz Y hYel h2
  obtain ⟨y, hy⟩ := d.bar.surjective g
  have hx1 : yConj V H φ 1 = Y := by
    ext z
    rw [yConj, map_one, mem_conjSubgroup_iff]
    simp only [inv_one, mul_one, one_mul]
    exact Iff.rfl
  have hyy : yConj V H φ y = conjSubgroup Y g := by
    rw [yConj, hy]
  have hYg : IsElemAbelian 2 (conjSubgroup Y g) :=
    CFSG.Open.IsElemAbelian.map hYel (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_sup_eq_top
    (fun a ha a' ha' => hYel.comm ha ha') (fun b hb b' hb' => hYg.comm hb hb') hg
    (sz_not_comm hK hn hSz)
  have hxy : ¬ ∀ a ∈ yConj V H φ 1, ∀ b ∈ yConj V H φ y, a * b = b * a := by
    intro h
    exact hab (h a (hx1 ▸ ha) b (hyy ▸ hb))
  have hne : conjSubgroup V₀ ((1 : ↥(conjClosure V H)) : G) ≠ conjSubgroup V₀ (y : G) := by
    intro h
    have h' := (d.conj_V₀_eq_iff 1 y).1 h
    rw [hx1, hyy] at h'
    exact hab (hYel.comm ha (h' ▸ hb))
  obtain ⟨D⟩ := d.exists_modDataB 1 y
  have hρ := d.exists_ρ_ne_one hxy hne D
  have hB : yConj V H φ 1 ⊔ yConj V H φ y = ⊤ := by
    rw [hx1, hyy]
    exact hg
  have hV₀card : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub (d.cfg.cex.hyp.isPGroup.to_le d.cfg.cex.hyp.h6.le)
  have hW : Module.finrank (ZMod 2) D.W = 2 * mSub V₀ := by
    have h1 := d.natCard_modDataB hne D
    have h3 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.W)
    rw [Nat.card_zmod, h1, hV₀card, ← pow_mul] at h3
    exact (Nat.pow_right_injective (le_refl 2) h3).symm.trans (by ring)
  have hdvd : (2 ^ n) ^ 2 + 1 ∣ Nat.card X := ⟨(2 ^ n) ^ 2 * (2 ^ n - 1), by rw [hcard]; ring⟩
  have h4 := four_mul_le_finrank_of_simple (by omega) hdvd _ hB D.ρ hρ
  omega

theorem two_mul_le_mSub_of_u3 (d : DichCfg M V₀ V U S H φ) [Finite X] (hK : KGroup1616Input)
    (hn : 1 < E3.mQuot V (iSub16 V H)) (hX : IsU3Shape X (E3.mQuot V (iSub16 V H))) :
    2 * E3.mQuot V (iSub16 V H) ≤ mSub V₀ := by
  set n := E3.mQuot V (iSub16 V H) with hndef
  by_contra hlt
  have hge : n ≤ mSub V₀ := d.cfg.mQuot_le_mSub
  obtain ⟨s, hs⟩ := d.exists_mSub_eq_mul hK hn hX
  have hm : mSub V₀ = n := by
    have h1 : s < 2 := by nlinarith
    have h2 : s ≠ 0 := by
      rintro rfl
      omega
    have : s = 1 := by omega
    rw [hs, this, mul_one]
  have hV₀card : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub (d.cfg.cex.hyp.isPGroup.to_le d.cfg.cex.hyp.h6.le)
  have hYc : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 ^ n := d.shape.1
  have hYel : IsElemAbelian 2 (SevenK.barSub (conjClosure V H) φ V) := d.isElemAbelian_barSub
  let 𝒞 : Set (Subgroup G) := {A | ∃ z : ↥(conjClosure V H), A = conjSubgroup V₀ (z : G)}
  let J : Subgroup G := Subgroup.closure (⋃ A ∈ 𝒞, (A : Set G))
  have h1mem : V₀ ∈ 𝒞 := by
    refine ⟨1, ?_⟩
    ext z
    rw [mem_conjSubgroup_iff]
    simp
  have hcov : ∀ j ∈ J, ∃ A ∈ 𝒞, j ∈ A := by
    intro j hj
    refine exists_mem_of_mem_closure 𝒞 ⟨V₀, h1mem⟩ ?_ hj
    intro A hA B hB a ha b hb
    obtain ⟨x, rfl⟩ := hA
    obtain ⟨y, rfl⟩ := hB
    by_cases h : conjSubgroup V₀ (x : G) = conjSubgroup V₀ (y : G)
    · exact ⟨conjSubgroup V₀ (x : G), ⟨x, rfl⟩, mul_mem ha (h ▸ hb)⟩
    · obtain ⟨z, hz⟩ := d.exists_mem_conj_mul hK hn hX hm x y ha hb
      exact ⟨_, ⟨z, rfl⟩, hz⟩
  have hle : ∀ A ∈ 𝒞, A ≤ J := fun A hA a ha => Subgroup.subset_closure (Set.mem_biUnion hA ha)
  have hcard : ∀ A ∈ 𝒞, Nat.card A = 2 ^ n := by
    rintro A ⟨z, rfl⟩
    rw [← hm, ← hV₀card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective V₀ (MulAut.conj (z : G)⁻¹).toMonoidHom
      (MulAut.conj (z : G)⁻¹).injective).toEquiv).symm
  have hti : ∀ A ∈ 𝒞, ∀ B ∈ 𝒞, A ≠ B → A ⊓ B = ⊥ := by
    rintro A ⟨x, rfl⟩ B ⟨y, rfl⟩ hAB
    exact d.inf_conj_V₀_eq_bot hAB
  have hJI : J ≤ iSub16 V H := by
    refine (Subgroup.closure_le _).2 ?_
    refine Set.iUnion₂_subset ?_
    rintro A ⟨z, rfl⟩
    exact d.conj_V₀_le_iSub16 z
  have hIp : IsPGroup 2 (iSub16 V H) :=
    B2F.isPGroup_of_isElemAbelian
      (Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (hIp.to_le hJI)
  have hnc : 𝒞.ncard = (2 ^ n) ^ 3 + 1 :=
    (d.ncard_conj_V₀).trans (ncard_conj hK hn hX hYel hYc)
  have hpart := card_eq_of_partition hle hcard hti hcov
  rw [hnc, hk] at hpart
  exact not_two_pow_of_partition (by omega) k hpart.symm

end DichCfg

theorem tiModule166_holds
    (hK : KGroup1616Input) (G : Type) [Group G] [Finite G] :
    W16One G → W16Five G → W16Fifteen G →
    Std15 G → ∀ ⦃M V₀ V U S H : Subgroup G⦄, Cex16 M V₀ V U S → IsMinFam16 M U S H →
      ¬ V ≤ pCoreOf 2 H →
        ∀ {X : Type} [Group X] (φ : ↥(conjClosure V H) →* X),
          SevenK.IsBarMap (conjClosure V H) (iSub16 V H) φ →
          Shape166 X (SevenK.barSub (conjClosure V H) φ V) (E3.mQuot V (iSub16 V H)) →
          (∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) →
          1 < E3.mQuot V (iSub16 V H) →
          (CFSG.Quasithin.IsSz (E3.mQuot V (iSub16 V H)) X ∨
            IsU3Shape X (E3.mQuot V (iSub16 V H))) →
          2 * E3.mQuot V (iSub16 V H) ≤ mSub V₀ := by
  intro h1 h5 h15 hS M V₀ V U S H hcex hmin hV X _ φ hbar hshape ho2 hn1 hsh
  haveI : Finite X := Finite.of_surjective φ hbar.surjective
  have d : DichCfg M V₀ V U S H φ := ⟨⟨hS, h1, h5, h15, hcex, hmin, hV⟩, hbar, hshape, ho2⟩
  rcases hsh with hSz | hU3
  · exact d.two_mul_le_mSub_of_sz hK hn1 hSz
  · exact d.two_mul_le_mSub_of_u3 hK hn1 hU3

end CFSG.LocalAnalysis.WeakClosure81

end
