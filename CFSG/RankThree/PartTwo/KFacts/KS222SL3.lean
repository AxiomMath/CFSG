module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStatements
public import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec21.SL3Lines

open CFSG CFSG.RankThree
open U4Lines (mapL embedOf)

variable {G M : Type} [Group G] [Group M]

theorem mapL_inf_centralizer_eq_of_conj {L : Subgroup G} {Y : Subgroup M} (ε : L ≃* Y) {b : G}
    (hN : b ∈ Subgroup.normalizer (L : Set G)) {y : M}
    (hy : ∀ x : L, ((ε (L.normalizerMonoidHom ⟨b, hN⟩ x) : Y) : M) = y * ε x * y⁻¹) :
    mapL ε (L ⊓ Subgroup.centralizer ({b} : Set G)) = Y ⊓ Subgroup.centralizer ({y} : Set M) := by
  have hfix : ∀ x : L, (x : G) * b = b * x ↔ L.normalizerMonoidHom ⟨b, hN⟩ x = x := by
    intro x
    rw [← Subtype.coe_inj, Sec4.normalizerMonoidHom_apply_coe]
    constructor
    · intro h
      rw [← h, mul_inv_cancel_right]
    · intro h
      calc (x : G) * b = b * x * b⁻¹ * b := by rw [h]
        _ = b * x := by group
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxb : (x : G) * b = b * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx).2
    refine Subgroup.mem_inf.mpr ⟨(ε x).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := hy x
    rw [(hfix x).mp hxb] at h
    show (ε x : M) * y = y * ε x
    calc (ε x : M) * y = y * ε x * y⁻¹ * y := by rw [← h]
      _ = y * ε x := by group
  · intro hz
    obtain ⟨hzY, hzC⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hzC
    set x : L := ε.symm ⟨z, hzY⟩ with hxdef
    have hεx : ((ε x : Y) : M) = z := by rw [hxdef, ε.apply_symm_apply]
    have hσ : L.normalizerMonoidHom ⟨b, hN⟩ x = x := by
      apply ε.injective
      apply Subtype.ext
      rw [hy x, hεx]
      calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [hzC]
        _ = z := by group
    refine ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩), hεx⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hfix x).mpr hσ)

end CFSG.RankThree.PartTwo.Sec21.SL3Lines

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSL)
open U4Lines (mapL mapLEquiv card_mapL mapL_perfectResidual)

theorem ks222SL3 : KS222SL3 := by
  intro G _ _ L A n hn he ⟨eL⟩ _ hAN hC b hbA hbx hev
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, -⟩ := hC
  have hθ := Item222Proof.inSubgroup_theta_eq_bot_of_mulEquiv_SL3 hn he eL
  have hθ' : LocalRank.aschbacherSolvableCore 3 L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hθ
  have hmk : Function.Bijective (QuotientGroup.mk' (LocalRank.aschbacherSolvableCore 3 L)) := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hθ'
  set ε : L ≃* Sec4.slPi π 3 (p ^ f) K := (MulEquiv.ofBijective _ hmk).trans e with hεdef
  obtain ⟨rfl, rfl, rfl⟩ := SL3Lines.params_eq hn he hPi hmod (eL.symm.trans ε)
  have := hPi.finite
  have hn2 : 2 ≤ f := by obtain ⟨k, hk⟩ := he; omega
  have h2 : (2 : K) = 0 := SL3Lines.two_eq_zero_of_mulEquiv hn2
    (fun x hx => (Sec4.mem_slPi_true _).mp hx) (eL.symm.trans ε)
  have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
  have hK : Nat.card K = 2 ^ f := hPi.card
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn2
  have hN : b ∈ Subgroup.normalizer (L : Set G) := hAN hbA
  obtain ⟨y, hyD, hy⟩ := hconj (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hN⟩))
    (Sec4.mem_autThetaQuot_iff.mpr ⟨b, hN, hbA, rfl⟩)
  have hy' : ∀ x : L, ((ε (L.normalizerMonoidHom ⟨b, hN⟩ x) : Sec4.slPi true 3 (2 ^ f) K) :
      GL (Fin 3) K) = y * (ε x : GL (Fin 3) K) * y⁻¹ := fun x => hy (x : L ⧸ _)
  have hmap := SL3Lines.mapL_inf_centralizer_eq_of_conj ε hN hy'
  have hnc : ∃ M ∈ Sec4.slPi true 3 (2 ^ f) K, M * y ≠ y * M := by
    obtain ⟨x, hxL, hxb⟩ := hbx
    refine ⟨ε ⟨x, hxL⟩, (ε ⟨x, hxL⟩).2, fun h => hxb ?_⟩
    have hmem : ((ε ⟨x, hxL⟩ : Sec4.slPi true 3 (2 ^ f) K) : GL (Fin 3) K) ∈
        Sec4.slPi true 3 (2 ^ f) K ⊓ Subgroup.centralizer {y} :=
      Subgroup.mem_inf.mpr ⟨(ε ⟨x, hxL⟩).2, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
    rw [← hmap] at hmem
    obtain ⟨x', hx', hx'e⟩ := hmem
    have hxx : x' = ⟨x, hxL⟩ := ε.injective (Subtype.ext hx'e)
    rw [hxx] at hx'
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx').2
  have hev' : Even (Nat.card ↥(Sec4.slPi true 3 (2 ^ f) K ⊓ Subgroup.centralizer {y})) := by
    rw [← hmap, card_mapL ε inf_le_left]
    exact hev
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  obtain ⟨l, s, t, -, -, hyg⟩ := hdiag y hyD
  obtain ⟨e₁⟩ := SL3Lines.perfectResidual_centralizer_of_conj hPi hK4 hyg hnc hev'
  have hZ : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ L :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 f)
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 f (by omega)]
  exact ⟨(mapLEquiv ε hZ).trans ((MulEquiv.subgroupCongr (mapL_perfectResidual ε inf_le_left)).trans
    ((MulEquiv.subgroupCongr (congrArg (inSubgroup perfectResidual) hmap)).trans (e₁.trans
      ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
        (FiniteField.ringEquivOfCardEq hcard)).trans (projSLTwoEquivSL _).symm))))⟩

end CFSG.RankThree.PartTwo.Sec21
