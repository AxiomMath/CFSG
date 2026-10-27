module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTStable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTDelta
import CFSG.Quasithin.Background.D2Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

private theorem dElt_mem_torus {F : Type} [Field F] (z : Fˣ) :
    dElt z ∈ CFSG.CGT.Timmesfeld75.torus F := by
  rw [CFSG.CGT.Timmesfeld75.mem_torus_entries]
  constructor <;> simp [dElt]

theorem borelMoves_of_realizesVia {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {J J₀ : Subgroup W} {K : Type}
    [Field K] [Finite K] [CharP K 2] (h8 : 8 ≤ Nat.card K) (π : ↥(StatedSL 2 K) →* ↥L)
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L J J₀ π) (hJ₀ : J₀ ≤ fixV L)
    (hcard : Nat.card ↥L = Nat.card SL(2, K)) :
    ∃ S₀ : Subgroup (MulAut W), IsSylowIn 2 S₀ L ∧ BorelMoves L S₀ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : SL(2, K) ≃* ↥(StatedSL 2 K) := (H13.A5.statedSLEquivSL 2 K).symm
  have hπinj : Function.Injective π := by
    haveI : Fintype ↥(StatedSL 2 K) := Fintype.ofFinite _
    haveI : Fintype ↥L := Fintype.ofFinite _
    refine (Finite.injective_iff_surjective_of_equiv (f := π) ?_).2 hπ.1
    exact Fintype.equivOfCardEq (by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      exact (Nat.card_congr e.toEquiv).symm.trans hcard.symm)
  have hπsurj : Function.Surjective π := hπ.1
  let ψ₀ : SL(2, K) →* ↥L := π.comp e.toMonoidHom
  have hψ₀bij : Function.Bijective ψ₀ := by
    refine ⟨fun x y hxy => e.injective (hπinj hxy), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hπsurj y
    exact ⟨e.symm x, by simp [ψ₀, hx]⟩
  let ψe : SL(2, K) ≃* ↥L := MulEquiv.ofBijective ψ₀ hψ₀bij
  let U₀ : Subgroup SL(2, K) := CFSG.CGT.Timmesfeld75.utri K
  let T₀ : Subgroup SL(2, K) := CFSG.CGT.Timmesfeld75.torus K
  have hU₀ : IsSylowIn 2 U₀ ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · simpa [U₀] using CFSG.CGT.Timmesfeld75.isPGroup_utri (F := K)
    · rw [Subgroup.relIndex_top_right]
      have ho := CFSG.CGT.Timmesfeld75.odd_index_utri (F := K)
      exact fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
  have hT₀ : Odd (Nat.card ↥T₀) := by
    change Odd (Nat.card (CFSG.CGT.Timmesfeld75.torus K))
    rw [CFSG.CGT.Timmesfeld75.card_torus]
    obtain ⟨n, hn, hcardK⟩ :=
      CFSG.CGT.Timmesfeld75.exists_natCard_eq_two_pow (F := K)
    rw [hcardK]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, hn.ne'⟩) odd_one
  have hTN : T₀ ≤ Subgroup.normalizer (U₀ : Set SL(2, K)) :=
    (CFSG.CGT.Timmesfeld75.torus_le_borel (F := K)).trans
      (CFSG.CGT.Timmesfeld75.normalizer_utri (F := K)).ge
  have hN : Subgroup.normalizer (U₀ : Set SL(2, K)) ≤ U₀ ⊔ T₀ := by
    change Subgroup.normalizer (CFSG.CGT.Timmesfeld75.utri K : Set SL(2, K)) ≤
      CFSG.CGT.Timmesfeld75.utri K ⊔ CFSG.CGT.Timmesfeld75.torus K
    rw [CFSG.CGT.Timmesfeld75.normalizer_utri (F := K),
      CFSG.CGT.Timmesfeld75.borel_eq_sup]
  obtain ⟨x, -, hxS, hxD⟩ := exists_fixed_uElt_of_realizesVia hW h8 π hπ hJ₀
  have hx : ∀ u ∈ U₀, ((ψe u : ↥L) : MulAut W) x = x := by
    intro u hu
    rw [show u = CFSG.CGT.Timmesfeld75.utriElt (u 0 1) from
      CFSG.CGT.Timmesfeld75.eq_utriElt_of_mem_utri hu]
    rw [MulEquiv.ofBijective_apply]
    rw [show CFSG.CGT.Timmesfeld75.utriElt (u 0 1) = uElt (u 0 1) from rfl]
    exact hxS (u 0 1)
  have ht : ∃ t ∈ T₀, ((ψe t : ↥L) : MulAut W) x ≠ x := by
    have hlt : 1 < Fintype.card Kˣ := by
      rw [Fintype.card_eq_nat_card, Nat.card_units]
      omega
    obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : Kˣ)
    refine ⟨dElt z, dElt_mem_torus z, ?_⟩
    rw [MulEquiv.ofBijective_apply]
    simpa [ψ₀, e] using hxD z hz
  exact ⟨_, borelMoves_map hW ψe hU₀ hT₀ hTN hN hx ht⟩

theorem borelMoves_of_isSylowIn {W : Type} [CommGroup W] [Finite W]
    {L S₀ S : Subgroup (MulAut W)} (hS₀ : IsSylowIn 2 S₀ L) (h : BorelMoves L S₀)
    (hS : IsSylowIn 2 S L) : BorelMoves L S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hS_eq⟩ := isSylowIn_exists_conj hS₀ hS
  obtain ⟨H₀, hH₀L, hH₀N, hH₀odd, hH₀sup, hH₀comm⟩ := h
  refine ⟨H₀.map (MulAut.conj l).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change (MulAut.conj l) x ∈ L
    rw [MulAut.conj_apply]
    exact L.mul_mem (L.mul_mem hl (hH₀L hx)) (L.inv_mem hl)
  · rw [hS_eq, ← Subgroup.map_equiv_normalizer_eq S₀ (MulAut.conj l)]
    exact Subgroup.map_mono hH₀N
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj l).toMonoidHom)
      (MulAut.conj l).injective]
    exact hH₀odd
  · have hL : L.map (MulAut.conj l).toMonoidHom = L := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        change (MulAut.conj l) x ∈ L
        rw [MulAut.conj_apply]
        exact L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
      · intro x hx
        refine ⟨l⁻¹ * x * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl, ?_⟩
        show (MulAut.conj l) (l⁻¹ * x * l) = x
        rw [MulAut.conj_apply]
        group
    have hmap := Subgroup.map_mono (f := (MulAut.conj l).toMonoidHom) hH₀sup
    rw [Subgroup.map_inf _ _ _ (MulAut.conj l).injective, hL,
      Subgroup.map_equiv_normalizer_eq S₀ (MulAut.conj l), ← hS_eq,
      Subgroup.map_sup, ← hS_eq] at hmap
    exact hmap
  · have hfix : (fixV S₀).map l.toMonoidHom = fixV S := by
      rw [← CFSG.Quasithin.fixV_map_conj_eq S₀ l, ← hS_eq]
    have hcongr : MulAut.congr l = MulAut.conj l := by
      ext x
      rfl
    have hcommmap : commSub (fixV S) (H₀.map (MulAut.conj l).toMonoidHom) =
        (commSub (fixV S₀) H₀).map l.toMonoidHom := by
      rw [← hfix, ← hcongr]
      exact commSub_map_mulAutCongr (V := W) (V' := W) l (fixV S₀) H₀
    intro hbot
    rw [hcommmap] at hbot
    exact hH₀comm ((Subgroup.map_eq_bot_iff_of_injective (commSub (fixV S₀) H₀)
      (f := l.toMonoidHom) l.injective).mp hbot)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
