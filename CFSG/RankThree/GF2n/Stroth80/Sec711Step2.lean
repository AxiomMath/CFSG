module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem orthogonal_eq_of_le_of_card {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (f : LinearMap.BilinForm (ZMod 2) E) (hf : f.Nondegenerate) (S T : Submodule (ZMod 2) E)
    (hTS : T ≤ f.orthogonal S) (hcard : Nat.card T * Nat.card S = Nat.card E) :
    T = f.orthogonal S := by
  haveI : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  have h2 : Nat.card (ZMod 2) = 2 := by simp
  have hE : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), h2]
  have hT : Nat.card T = 2 ^ Module.finrank (ZMod 2) T := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := T), h2]
  have hS : Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S), h2]
  rw [hE, hT, hS, ← pow_add] at hcard
  have hsum : Module.finrank (ZMod 2) T + Module.finrank (ZMod 2) S =
      Module.finrank (ZMod 2) E := Nat.pow_right_injective (le_refl 2) hcard
  have horth := LinearMap.BilinForm.finrank_orthogonal hf S
  refine Submodule.eq_of_le_of_finrank_eq hTS ?_
  rw [horth]
  have := Submodule.finrank_le S
  omega


theorem n12Lemma2_of (h34 : Stroth34Statement) (h52c : Stroth52cStatement) :
    N12Lemma2Statement := by
  classical
  intro G _ _ M Q Z B hc n t hs
  have hVW := Vt_le_Wt_of_34 h34 hc hs.toSec5
  have hVab : ∀ a ∈ Vt M (LB M Q B) B Z t, ∀ b ∈ Vt M (LB M Q B) B Z t, ⁅a, b⁆ = 1 := by
    intro a ha b hb
    have h1 := Subgroup.mem_centralizer_iff.mp (hVW ha).2 b hb
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm
  refine ⟨hVab, fun lam hlam a haQ => ⟨fun haW v hv => ?_, fun hperp => ?_⟩⟩
  · have h1 : ⁅a, v⁆ = 1 := by
      have := Subgroup.mem_centralizer_iff.mp haW.2 v hv
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact this.symm
    refine ⟨by rw [h1]; exact Z.one_mem, ?_⟩
    have : (⟨⁅a, v⁆, by rw [h1]; exact Z.one_mem⟩ : ↥Z) = 1 := Subtype.ext h1
    rw [this, map_one]
  · set V := Vt M (LB M Q B) B Z t with hV
    set W := Wt Q V with hW
    obtain ⟨hZQ, hZc, hcomm, hsq⟩ := n12Q_holds G M Q Z B hc
    have hnd := n12Lemma1_holds G M Q Z B hc lam hlam
    have hZV : Z ≤ V := sec39_Z_le_Vt
    have hVQ : V ≤ Q := hc.Vt_le_Q t
    have hWQ : W ≤ Q := inf_le_left
    have hZW : Z ≤ W := hZV.trans (by
      intro v hv
      exact hVW hv)
    have hsec : SecHyp (⊥ : Subgroup G) Q Z :=
      ⟨hZQ, hcomm, hsq, fun r hr x hx => by rw [Subgroup.mem_bot] at hr; simpa [hr] using hx,
        fun r hr x hx => by rw [Subgroup.mem_bot] at hr; simpa [hr] using hx⟩
    obtain ⟨Mo, iM, iA, κ, hκ⟩ := exists_sectionModule hsec
    haveI : Finite Mo := hκ.finite
    letI : Module (ZMod 2) Mo := AddCommGroup.zmodModule (fun a => by
      rw [two_nsmul]; exact hκ.two a)
    haveI : FiniteDimensional (ZMod 2) Mo := Module.Finite.of_finite
    obtain ⟨f, hfnd, hfalt, hfκ⟩ := exists_lamForm lam hcomm hZc hκ hnd
    let Sub : Subgroup G → Submodule (ZMod 2) Mo := fun U =>
      AddSubgroup.toZModSubmodule 2 (secSub κ U)
    have hrep : ∀ x : Mo, ∃ a : ↥Q, Multiplicative.toAdd (κ a) = x := by
      intro x
      obtain ⟨a, ha⟩ := hκ.surj (Multiplicative.ofAdd x)
      exact ⟨a, by rw [ha]; rfl⟩
    have hmemU : ∀ U : Subgroup G, Z ≤ U → ∀ a : ↥Q,
        Multiplicative.toAdd (κ a) ∈ Sub U ↔ (a : G) ∈ U :=
      fun U hU a => toAdd_mem_secSub_iff hκ hU a
    have hle : Sub W ≤ f.orthogonal (Sub V) := by
      intro x hx
      obtain ⟨a', rfl⟩ := hrep x
      have ha' : (a' : G) ∈ W := (hmemU W hZW a').1 hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n' hn'
      obtain ⟨v, rfl⟩ := hrep n'
      have hv : (v : G) ∈ V := (hmemU V hZV v).1 hn'
      rw [hfκ]
      have h1 : ⁅(v : G), (a' : G)⁆ = 1 := by
        have := Subgroup.mem_centralizer_iff.mp ha'.2 v hv
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this
      unfold comm2
      have : (⟨⁅(v : G), (a' : G)⁆, hcomm _ v.2 _ a'.2⟩ : ↥Z) = 1 := Subtype.ext h1
      rw [this, map_one, toAdd_one]
    haveI : (Z.subgroupOf V).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
    have hchi := h52c G M Q Z B hc n t hs.toSec5 hs.omegaNat _ _ _ rfl rfl rfl
    have hcardχ := card_mul_card_of_isChiIso hchi hWQ hZV
    have hZQ' : Nat.card Q = Nat.card Z * Nat.card Mo := natCard_eq_of_isSecMod hZQ hκ
    have hSW := natCard_secSub_mul hZQ hκ hZW hWQ
    have hSV := natCard_secSub_mul hZQ hκ hZV hVQ
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hcard : Nat.card (Sub W) * Nat.card (Sub V) = Nat.card Mo := by
      have e1 : Nat.card (Sub W) = Nat.card (secSub κ W) := rfl
      have e2 : Nat.card (Sub V) = Nat.card (secSub κ V) := rfl
      rw [e1, e2]
      have : (Nat.card (secSub κ W) * Nat.card (secSub κ V)) * (Nat.card Z * Nat.card Z) =
          Nat.card Mo * (Nat.card Z * Nat.card Z) := by
        calc (Nat.card (secSub κ W) * Nat.card (secSub κ V)) * (Nat.card Z * Nat.card Z)
            = (Nat.card (secSub κ W) * Nat.card Z) * (Nat.card (secSub κ V) * Nat.card Z) := by
              ring
          _ = Nat.card W * Nat.card V := by rw [hSW, hSV]
          _ = Nat.card Q * Nat.card Z := hcardχ.symm
          _ = Nat.card Mo * (Nat.card Z * Nat.card Z) := by rw [hZQ']; ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hZpos hZpos) this
    have heq := orthogonal_eq_of_le_of_card f hfnd (Sub V) (Sub W) hle hcard
    have hao : Multiplicative.toAdd (κ ⟨a, haQ⟩) ∈ f.orthogonal (Sub V) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n' hn'
      obtain ⟨v, rfl⟩ := hrep n'
      have hv : (v : G) ∈ V := (hmemU V hZV v).1 hn'
      rw [hfκ, comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm]
      exact hperp v hv
    rw [← heq] at hao
    exact (hmemU W hZW ⟨a, haQ⟩).1 hao

end CFSG.RankThree.GF2n.Stroth80
