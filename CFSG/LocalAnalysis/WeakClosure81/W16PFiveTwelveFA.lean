module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveS
public import CFSG.LocalAnalysis.WeakClosure81.W15SixG
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenF
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

private theorem repQuad_eRep_of_quad {V₀ B X T : Subgroup G}
    [Fact (IsElemAbelian 2 (eSub V₀ X T))] (hBX : B ≤ X)
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ e ∈ eSub V₀ X T,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹) :
    RepQuad (eRep V₀ X T) (B.subgroupOf X) := by
  have hgen : ∀ (a : G) (ha : a ∈ B) (b : G) (hb : b ∈ B)
      (v : Additive ↥(eSub V₀ X T)),
      eRep V₀ X T ⟨a, hBX ha⟩ (eRep V₀ X T ⟨b, hBX hb⟩ v - v) =
        eRep V₀ X T ⟨b, hBX hb⟩ v - v := by
    intro a ha b hb v
    obtain ⟨e, he⟩ : ∃ e : ↥(eSub V₀ X T), v = Additive.ofMul e :=
      ⟨Additive.toMul v, rfl⟩
    rw [he]
    apply Additive.toMul.injective
    apply Subtype.ext
    have h := hquad a ha b hb (e : G) e.2
    simp only [eRep_apply, toMul_sub, toMul_ofMul, Subgroup.coe_mul, Subgroup.coe_inv,
      div_eq_mul_inv, mul_assoc, commutatorElement_def] at h ⊢
    exact h
  have hle : commSub ((B.subgroupOf X).map (eRep V₀ X T)) ≤
      fixSub ((B.subgroupOf X).map (eRep V₀ X T)) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨b, ⟨b', hb', rfl⟩, v, rfl⟩ k ⟨a', ha', rfl⟩
    exact hgen a' ha' b' hb' v
  unfold RepQuad commSpace
  rw [Submodule.span_eq_bot]
  rintro w ⟨k, hk, u, hu, rfl⟩
  rw [hle hu k hk, sub_self]

theorem Hyp167.finrank_sub_le [Fact (IsElemAbelian 2 (eSub V₀ X T))]
    (hX : Hyp167 M V₀ V U S H g X T) :
    Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) ≤ mSub V₀ := by
  have h1 : Nat.card (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 := CFSG.Goldschmidt.G2.card_sub (A := eSub V₀ X T) V₀
  have h3 : Nat.card ↥(eSub V₀ X T ⊓ V₀) ∣ Nat.card ↥V₀ :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [← h2, h1, card_eq_two_pow_mSub hX.cex.hyp.elemAbelian₀.isPGroup] at h3
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3

theorem Hyp167.setting12One [Fact (IsElemAbelian 2 (eSub V₀ X T))]
    (hX : Hyp167 M V₀ V U S H g X T) (hm : 1 < mSub V₀)
    (hBC : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) = ⊥)
    (hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G))
    (hquad : ∀ a ∈ conjSubgroup V₀ g, ∀ b ∈ conjSubgroup V₀ g, ∀ e ∈ eSub V₀ X T,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹)
    {n : ℕ} (hn : IsPSL 2 2 n (KerQuot M X) ∨ IsSz n (KerQuot M X))
    (hB : IsBorelIn (⊤ : Subgroup (KerQuot M X)) (kerQuotImg M X M))
    {ρ : KerQuot M X →* LGL 2 (Additive ↥(eSub V₀ X T))}
    (hρ : ∀ x : ↥X, ρ (kerQuotMk M X x) = eRep V₀ X T x) :
    Setting12One ρ (kerQuotImg M X M) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀)
      (kerQuotImg M X (conjSubgroup V₀ g)) n (mSub V₀) := by
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le
  have hBX : conjSubgroup V₀ g ≤ X := hV₀g.trans hX.mem.2.2.A_le
  have hBM : conjSubgroup V₀ g ≤ M := hV₀g.trans hX.mem.2.2.A_le_M
  have hBmax : IsMaxSubgroupIn ⊤ (kerQuotImg M X M) := by
    have hmem : kerQuotImg M X M ∈ maxOver ⊤ (kerQuotImg M X (conjSubgroup V g)) := by
      rw [maxOver_kerQuotImg_of_inf hX.mem.2.2.A_le hX.mem.2.2.maxOver_eq]
      exact Set.mem_singleton _
    exact hmem.1
  refine ⟨hn, hB, ?_, ?_, ?_, ?_, hm, ?_⟩
  · refine mem_iff_forall_of_isMaxSubgroupIn ρ hBmax
      (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) ?_ ?_
    · intro y hy z hz
      obtain ⟨x, rfl⟩ := kerQuotMk_surjective M X y
      have hxM : (x : G) ∈ M := (kerQuotMk_mem_kerQuotImg_iff x).1 hy
      rw [hρ x, CFSG.Goldschmidt.G2.mem_sub, eRep_apply]
      have hnorm : (x : G) ∈ normalizer (V₀ : Set G) := by
        rw [hX.cex.hyp.normalizer₀]
        exact hxM
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hz
    · by_contra hcon
      have hstab_all : ∀ (y : KerQuot M X) (w : Additive ↥(eSub V₀ X T)),
          w ∈ CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀ → ρ y w ∈
            CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀ := by
        intro y w hw
        by_contra hw'
        exact hcon ⟨y, w, hw, hw'⟩
      have hZne : CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀ ≠ ⊥ := by
        intro hZbot
        rw [CFSG.Goldschmidt.G2.sub_eq_bot_iff] at hZbot
        have hTnorm : T ≤ Subgroup.normalizer (V₀ : Set G) := by
          rw [hX.cex.hyp.normalizer₀]
          exact hX.sylow.le.trans inf_le_right
        have hfix : V₀ ⊓ centralizer (T : Set G) ≠ ⊥ :=
          CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
            Nat.prime_two hX.sylow.isPGroup hX.cex.hyp.elemAbelian₀.isPGroup
            hX.cex.hyp.ne_bot hTnorm
        exact hfix (le_bot_iff.1 ((le_inf (le_conjClosure _ _) inf_le_left).trans
          (le_of_eq hZbot)))
      obtain ⟨z, hzZ, hz0⟩ := (Submodule.ne_bot_iff _).mp hZne
      have hzV₀ : ((Additive.toMul z : ↥(eSub V₀ X T)) : G) ∈ V₀ := hzZ
      have hz1 : ((Additive.toMul z : ↥(eSub V₀ X T)) : G) ≠ 1 := by
        intro h
        exact hz0 (Additive.toMul.injective (Subtype.ext h))
      have hXM : X ≤ M := by
        intro x hx
        have hxmem : ((Additive.toMul z : ↥(eSub V₀ X T)) : G) ∈
            CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ V₀ := by
          rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
          have hstab := hstab_all (kerQuotMk M X ⟨x, hx⟩) z hzZ
          rw [hρ ⟨x, hx⟩] at hstab
          have hmem : ((Additive.toMul (eRep V₀ X T ⟨x, hx⟩ z) :
              ↥(eSub V₀ X T)) : G) ∈ V₀ := hstab
          simpa [eRep_apply] using hmem
        have hne : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ V₀ ≠ ⊥ := by
          intro hbot
          have h : ((Additive.toMul z : ↥(eSub V₀ X T)) : G) ∈ (⊥ : Subgroup G) := by
            rw [← hbot]
            exact Subgroup.mem_inf.2 ⟨hzV₀, hxmem⟩
          exact hz1 (Subgroup.mem_bot.1 h)
        have h1 : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ V₀ = V₀ :=
          (hX.cex.hyp.isTI x⁻¹).resolve_left hne
        have hle : V₀ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ V₀ :=
          (le_of_eq h1.symm).trans inf_le_right
        have hcard : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ V₀) =
            Nat.card V₀ := by
          rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
          exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj x⁻¹))
        have heq : V₀ = CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ V₀ :=
          Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
        have hxinvN : x⁻¹ ∈ Subgroup.normalizer (V₀ : Set G) := by
          rw [Subgroup.mem_normalizer_iff'']
          intro w
          rw [← CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
          exact SetLike.ext_iff.1 heq w
        have hxN : x ∈ Subgroup.normalizer (V₀ : Set G) := by
          simpa using (Subgroup.normalizer (V₀ : Set G)).inv_mem hxinvN
        rwa [← hX.cex.hyp.normalizer₀]
      have hN : (X.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).2 Subgroup.le_normalizer
      exact hX.mem.2.2.not_le_ker
        (hX.mem.2.2.A_le.trans (le_kerMOf_of_normal le_rfl hN hXM))
  · exact kerQuotImg_mono hBM
  · exact isElemAbelian_kerQuotImg (E3.isElemAbelian_conjSubgroup hX.cex.hyp.elemAbelian₀ g)
  · rw [card_kerQuotImg hBX]
    have hinf : conjSubgroup V₀ g ⊓ kerMOf M X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.1 hx
      have hx' : x ∈ conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) :=
        ⟨hxB, hK hxK⟩
      rw [hBC] at hx'
      exact hx'
    rw [hinf, Subgroup.relIndex_bot_left, E3.card_conjSubgroup,
      card_eq_two_pow_mSub hX.cex.hyp.elemAbelian₀.isPGroup]
  · have hmap : (kerQuotImg M X (conjSubgroup V₀ g)).map ρ =
        ((conjSubgroup V₀ g).subgroupOf X).map (eRep V₀ X T) := by
      have hker : kerQuotImg M X (conjSubgroup V₀ g) =
          ((conjSubgroup V₀ g).subgroupOf X).map (kerQuotMk M X) := rfl
      rw [hker, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext hρ
    have hquad' := repQuad_eRep_of_quad (V₀ := V₀) (B := conjSubgroup V₀ g) (X := X)
      (T := T) hBX hquad
    unfold RepQuad at hquad' ⊢
    rwa [hmap]

end CFSG.LocalAnalysis.WeakClosure81

end
