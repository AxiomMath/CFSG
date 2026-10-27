module

public import CFSG.RankThree.GF2n.Tim79a34Local
public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim79a34TwWSplit
public import CFSG.RankThree.GF2n.Tim79a34TwBound
public import CFSG.RankThree.GF2n.Tim79a34TwStruct

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

theorem lemma11a_holds (hB4 : SpRadFactsStatement) : Lemma11aStatement := by
  intro G _ _ M V Q P H hH hZ hcP n Φ ψ hNat a T ha hT hTV
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      apply ha
      funext i
      rcases i with i | i <;> exact i.elim0
    · omega
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hWcard : Nat.card ↥(wOf V H) = 2 ^ (2 * n) := by
    have h1 : Nat.card (Fin n ⊕ Fin n → GaloisField 2 1) = Nat.card ↥(wOf V H) :=
      Nat.card_congr (ψ.toEquiv.trans Additive.toMul)
    rw [← h1, Nat.card_fun, Nat.card_sum, hF2]
    simp [two_mul, Nat.card_eq_fintype_card]
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hPW : Nat.card ↥(P ⊓ wOf V H) = 2 ^ (2 * n - 1) := by
    have h := twistedWSplit_holds G M V Q P H hH.setup hH.concl
    rw [hWcard, hVW] at h
    have h2 : 2 ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : Nat.card ↥(P ⊓ wOf V H) * 2 = 2 ^ (2 * n - 1) * 2 := by
      rw [← h, h2]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  have hKcard : Nat.card ↥(LinearMap.ker (spFormL a)) = 2 ^ (2 * n - 1) := by
    rw [natCard_ker_spFormL ha, hF2]
  have hSncard : Set.ncard {w : Fin n ⊕ Fin n → GaloisField 2 1 | CaseM.spForm a w = 0} =
      2 ^ (2 * n - 1) := by
    rw [← Nat.card_coe_set_eq, ← hKcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
      (LinearMap.mem_ker (f := spFormL a) (y := w)).symm)
  have hLncard : Set.ncard {w : Fin n ⊕ Fin n → GaloisField 2 1 |
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} = 2 ^ (2 * n - 1) := by
    have hinj : Function.Injective (fun w : Fin n ⊕ Fin n → GaloisField 2 1 =>
        ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)) := by
      intro w w' h
      apply ψ.injective
      apply Additive.toMul.injective
      exact Subtype.ext h
    have himg : (fun w : Fin n ⊕ Fin n → GaloisField 2 1 =>
        ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)) ''
        {w | ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} =
          ((P ⊓ wOf V H : Subgroup G) : Set G) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Subgroup.mem_inf.mpr ⟨hw, (Additive.toMul (ψ w)).2⟩
      · intro hx
        have hx' : x ∈ P ⊓ wOf V H := hx
        have hxW : x ∈ wOf V H := (Subgroup.mem_inf.mp hx').2
        refine ⟨ψ.symm (Additive.ofMul ⟨x, hxW⟩), ?_, ?_⟩
        · show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul ⟨x, hxW⟩))) : ↥(wOf V H)) : G) ∈ P
          rw [AddEquiv.apply_symm_apply]
          exact (Subgroup.mem_inf.mp hx').1
        · show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul ⟨x, hxW⟩))) : ↥(wOf V H)) : G) = x
          rw [AddEquiv.apply_symm_apply]
          rfl
    have h1 := Set.ncard_image_of_injective
      {w : Fin n ⊕ Fin n → GaloisField 2 1 | ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} hinj
    rw [himg] at h1
    rw [← h1, ← hPW]
    exact (Nat.card_coe_set_eq _).symm
  have hfwd : ∀ w : Fin n ⊕ Fin n → GaloisField 2 1,
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P → CaseM.spForm a w = 0 := by
    intro w hw
    obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
    have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hvV
    have hxmem : xToXbar hVH ⟨v, hvX⟩ ∈ Vy V H :=
      Subgroup.mem_subgroupOf.mpr
        (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩, hvV, rfl⟩)
    have hmemT : xToXbar hVH ⟨v, hvX⟩ ∈ T.map Φ.toMonoidHom := by
      rw [hTV]
      exact hxmem
    have ht_mem : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ∈ T := Subgroup.mem_map_equiv.mp hmemT
    have ht1 : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ≠ 1 := by
      intro h1
      apply hvW
      have h2 : xToXbar hVH ⟨v, hvX⟩ = 1 := by
        have h3 := Φ.apply_symm_apply (xToXbar hVH ⟨v, hvX⟩)
        rw [h1, map_one] at h3
        exact h3.symm
      have h4 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩) = 1 := by
        rw [← coe_xToXbar hVH ⟨v, hvX⟩, h2, Subgroup.coe_one]
      exact (piBar_eq_one_iff _).mp h4
    have hmat := tw_mat_eq_spTrans_one hF2 hT ht_mem ht1
    have key := hNat.equiv ⟨v, hvX⟩ w
    have hcomm := hc.commute_of_mem_P hw hvV
    have hval : ((⟨v, hvX⟩ : ↥(xOf V H)) : G) = v := rfl
    rw [hval, hcomm, mul_assoc, mul_inv_cancel, mul_one] at key
    have hσw := ψ.injective (Additive.toMul.injective (Subtype.ext key))
    rw [hmat, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec] at hσw
    have h0 : (1 * CaseM.spForm a w) • a = 0 := by
      have h5 := congrArg (fun y => y - w) hσw
      simpa using h5
    rcases smul_eq_zero.mp h0 with h | h
    · simpa using h
    · exact absurd h ha
  have hsub : {w : Fin n ⊕ Fin n → GaloisField 2 1 |
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} ⊆ {w | CaseM.spForm a w = 0} :=
    fun w hw => hfwd w hw
  have hLS := Set.eq_of_subset_of_ncard_le hsub (by rw [hSncard, hLncard])
  have hiff : ∀ w : Fin n ⊕ Fin n → GaloisField 2 1,
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P ↔ CaseM.spForm a w = 0 :=
    fun w => Set.ext_iff.mp hLS w
  have hxOf : xOf V H = H := by
    have h := hH.concl.2.1
    rw [sup_eq_left.mpr (hcP.trans (wOf_le_xOf V H))] at h
    exact h
  have hπinj : Function.Injective (projZ V H) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff x).mp hx
    rw [hZ] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hΨbij : Function.Bijective ((projZ V H).comp Φ.toMonoidHom) :=
    ⟨hπinj.comp Φ.injective,
      (QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H))).comp Φ.surjective⟩
  have hVZ : VZ V H = T.map ((projZ V H).comp Φ.toMonoidHom) := by
    unfold VZ
    rw [← hTV, Subgroup.map_map]
  have hnorm : Subgroup.normalizer ((T.map ((projZ V H).comp Φ.toMonoidHom) :
      Subgroup (XbarZ V H)) : Set (XbarZ V H)) =
      (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))).map
        ((projZ V H).comp Φ.toMonoidHom) :=
    (Subgroup.map_normalizer_eq_of_bijective T hΨbij).symm
  have hpc : pCoreOf 2 ((Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))).map
      ((projZ V H).comp Φ.toMonoidHom)) =
      (pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1))))).map
        ((projZ V H).comp Φ.toMonoidHom) :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective _ hΨbij) _
  have hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))) =
      spRad a :=
    spCoreStmt_holds n (GaloisField 2 1) ha hT
  have hRt : Rtilde V H P = (spRad a).map ((projZ V H).comp Φ.toMonoidHom) := by
    have hP' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :=
      hH.tilde
    rw [hP', hVZ, hnorm, hpc, hcore]
  have hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom := by
    refine Subgroup.map_injective hπinj ?_
    rw [Subgroup.map_map]
    exact hRt
  have hPH : P ≤ H := hc.PleH
  have hPX : P ≤ xOf V H := by
    rw [hxOf]
    exact hPH
  have hbarP : barOf V H P ≤ barOf V H (xOf V H) := barOf_mono hPX
  have hRcard : Nat.card ↥(Rbar V H P) = 2 ^ (2 * n - 1) := by
    rw [hRbar, Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective]
    exact (hB4 n hn (GaloisField 2 1) hF2 a ha).2.2
  have hbar_card : Nat.card ↥(barOf V H P) = 2 ^ (2 * n - 1) := by
    rw [← hRcard]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarP).toEquiv).symm
  have hPcard := twb_card_barOf_mul (V := V) (H := H) (K := P) hPH
  rw [hbar_card, hPW] at hPcard
  refine ⟨hiff, hRbar, hxOf, ?_⟩
  rw [← hPcard, ← pow_add]
  congr 1
  omega

end CFSG.RankThree.GF2n.Tim79a
