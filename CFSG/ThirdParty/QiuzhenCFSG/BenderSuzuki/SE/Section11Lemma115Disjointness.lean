module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115FixedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the `r'`-core of `V`

This module isolates the solvable-group step used in part (c).  In a finite
solvable group, an `r`-group Fitting subgroup forces the `r'`-core to vanish.
Proposition 10.2 supplies exactly that Fitting hypothesis for the selected
subgroup `V`, while odd-order solvability supplies the solvability instance.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- In a finite solvable group, an `r`-group Fitting subgroup forces the
`r'`-core to be trivial. -/
public theorem lemma115_pPrimeCore_eq_bot_of_solvable_fitting_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime)
    (hsolv : Group.IsSolvable G)
    (hFp : IsPGroup p (fittingSubgroup G)) :
    pPrimeCore p G = ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Group.IsSolvable G := hsolv
  rw [pPrimeCore_eq_bot_iff]
  intro K hKnorm hKcop
  by_contra hKne
  have hfitK_ne_bot : fittingSubgroup K ≠ ⊥ := by
    intro hfitK
    have hcardK : Nat.card K = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp hfitK
    exact hKne ((Subgroup.card_eq_one (H := K)).1 hcardK)
  let L : Subgroup G := (fittingSubgroup K).map K.subtype
  have hL_ne_bot : L ≠ ⊥ := by
    intro hLbot
    exact hfitK_ne_bot
      (Subgroup.map_injective K.subtype_injective (by simpa [L] using hLbot))
  have hL_normal : L.Normal := by
    letI : K.Normal := hKnorm
    letI : (fittingSubgroup K).Characteristic :=
      fittingSubgroup_characteristic
    change ((fittingSubgroup K).map K.subtype).Normal
    infer_instance
  have hL_nilpotent : Group.IsNilpotent L := by
    haveI : Group.IsNilpotent (fittingSubgroup K) := by infer_instance
    let e : fittingSubgroup K ≃* L :=
      Subgroup.equivMapOfInjective
        (f := K.subtype) (fittingSubgroup K) K.subtype_injective
    exact nilpotent_of_mulEquiv (G := fittingSubgroup K) (G' := L) e
  have hL_le_fitting : L ≤ fittingSubgroup G :=
    proposition102_normal_nilpotent_le_fitting hL_normal hL_nilpotent
  have hL_p : IsPGroup p L := by
    let Lsub : Subgroup (fittingSubgroup G) :=
      L.subgroupOf (fittingSubgroup G)
    have hLsub_p : IsPGroup p Lsub := hFp.to_subgroup Lsub
    have e : Lsub ≃* L :=
      Subgroup.subgroupOfEquivOfLe
        (H := L) (K := fittingSubgroup G) hL_le_fitting
    exact hLsub_p.of_equiv e
  have hLcop : Nat.Coprime p (Nat.card L) := by
    have hL_dvd_fitK : Nat.card L ∣ Nat.card (fittingSubgroup K) := by
      simpa [L] using
        Subgroup.card_map_dvd (H := fittingSubgroup K) K.subtype
    have hfitK_dvd_K : Nat.card (fittingSubgroup K) ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card (fittingSubgroup K)
    exact Nat.Coprime.of_dvd_right
      (hL_dvd_fitK.trans hfitK_dvd_K) hKcop
  rcases hL_p.exists_card_eq with ⟨n, hn⟩
  by_cases hn0 : n = 0
  · exact hL_ne_bot
      ((Subgroup.card_eq_one (H := L)).1 (by simp [hn, hn0]))
  · have hpdvd : p ∣ Nat.card L := by
      rw [hn]
      exact dvd_pow_self p hn0
    exact (hp.coprime_iff_not_dvd.mp hLcop) hpdvd

/-- Proposition 10.2's Fitting `r`-group conclusion gives
`O_{r'}(V)=1`. -/
public theorem lemma115_pPrimeCore_V_eq_bot
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (htM : t ∉ M)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d) :
    pPrimeCore h102.exponent.r
      (peterfalviV (M ⊓ rightConjugate M t) t) = ⊥ := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hVleD : V ≤ D := by
    simp [V, peterfalviV]
  have hVodd : Odd (Nat.card V) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hVleD)
  have hFambient : IsPGroup h102.exponent.r (fittingSubgroupOf V) := by
    rw [h102.fitting_eq_derived_inf]
    simpa [D, V] using h102.derived_inf_isPGroup
  letI : Fact h102.exponent.r.Prime := ⟨h102.exponent.r_prime⟩
  have hFinternal : IsPGroup h102.exponent.r (fittingSubgroup V) := by
    let e : fittingSubgroup V ≃* fittingSubgroupOf V :=
      Subgroup.equivMapOfInjective (f := V.subtype)
        (fittingSubgroup V) V.subtype_injective
    exact hFambient.of_equiv e.symm
  exact lemma115_pPrimeCore_eq_bot_of_solvable_fitting_isPGroup
    h102.exponent.r_prime (odd_order_theorem V hVodd) hFinternal

/-- Proposition 10.2's Hall subgroup contains an ambient Sylow
`r`-subgroup lying in the selected two-point stabilizer `D`. -/
public theorem lemma115_ambient_sylow_r_le_D
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d) :
    ∃ R : Sylow h102.exponent.r X,
      (R : Subgroup X) ≤ M ⊓ rightConjugate M t := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let r : Nat.Primes := ⟨h102.exponent.r, h102.exponent.r_prime⟩
  letI : Fact h102.exponent.r.Prime := ⟨h102.exponent.r_prime⟩
  have hHleD : H ≤ D :=
    (Subgroup.map_subtype_le (derivedSubgroup E)).trans inf_le_right
  have hrH : h102.exponent.r ∣ Nat.card H := by
    simpa [H, E, D] using h102.exponent.r_dvd_derived_card
  have hHall : IsHallSubgroup (subgroupPrimeSet H) H := by
    simpa [H, E, D] using h102.derived_hall
  have hrPi : r ∈ subgroupPrimeSet H := by
    change (r : ℕ) ∣ Nat.card H
    exact hrH
  let S : Sylow h102.exponent.r H := Sylow.nonempty.some
  let P : Subgroup X := (S : Subgroup H).map H.subtype
  have hPp : IsPGroup h102.exponent.r P :=
    S.isPGroup'.map H.subtype
  have hnotHindex : ¬ h102.exponent.r ∣ H.index := by
    intro hdiv
    exact (hHall.p_in_pi_of_p_dvd_index r hdiv) hrPi
  have hnotPindex : ¬ h102.exponent.r ∣ P.index := by
    have hidx : P.index = (S : Subgroup H).index * H.index := by
      simpa [P] using
        Subgroup.index_map_subtype (H := H) (K := (S : Subgroup H))
    rw [hidx]
    exact h102.exponent.r_prime.not_dvd_mul S.not_dvd_index hnotHindex
  let R : Sylow h102.exponent.r X := hPp.toSylow hnotPindex
  refine ⟨R, ?_⟩
  have hR : (R : Subgroup X) = P :=
    IsPGroup.toSylow_coe hPp hnotPindex
  rw [hR]
  exact (Subgroup.map_subtype_le (S : Subgroup H)).trans hHleD

/-- No element of the Lemma 11.5 anti-fixed set has order `r`.  Such an
element would lie in a conjugate of the ambient Sylow subgroup in `D` and
therefore fix a conjugate coset, contradicting part (b). -/
public theorem lemma115_B_no_order_r
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    ∀ {x : X},
      x ∈ peterfalviKSet
        (Subgroup.centralizer ({t * d83.u} : Set X)) t →
      orderOf x ≠ h102.exponent.r := by
  intro x hxB hxorder
  have hxne : x ≠ 1 := by
    intro hxone
    have hone : orderOf x = 1 := orderOf_eq_one_iff.mpr hxone
    rw [hxorder] at hone
    exact h102.exponent.r_prime.ne_one hone
  have hfix := lemma115_B_nonidentity_fixedPoints_eq_empty
    hM ht htM d83 htwo h42 d h102 h114 hxB hxne
  obtain ⟨R, hRD⟩ := lemma115_ambient_sylow_r_le_D d h102
  letI : Fact h102.exponent.r.Prime := ⟨h102.exponent.r_prime⟩
  have hxpg : IsPGroup h102.exponent.r (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, hxorder]
  obtain ⟨Q, hQ⟩ := hxpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
  have hxQ : x ∈ (Q : Subgroup X) :=
    hQ (Subgroup.mem_zpowers x)
  have hxconjR : g * x * g⁻¹ ∈ (R : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨x, hxQ, rfl⟩
  have hxconjM : g * x * g⁻¹ ∈ M := (hRD hxconjR).1
  have hxright : x ∈ rightConjugate M g := by
    have h := rightConjugateElem_mem_rightConjugate (g := g) hxconjM
    simpa [rightConjugateElem, mul_assoc] using h
  have hxfix : x •
      (QuotientGroup.mk g⁻¹ : conjugateCosetSpace M) =
        QuotientGroup.mk g⁻¹ := by
    apply (fixed_coset_iff_mem_rightConjugate M g⁻¹ x).mpr
    simpa using hxright
  have hmem : (QuotientGroup.mk g⁻¹ : conjugateCosetSpace M) ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M)
        (Subgroup.zpowers x) :=
    mem_fixedPointsOfSubgroup_zpowers_iff.mpr hxfix
  rw [hfix] at hmem
  exact hmem

/-- The generated anti-fixed subgroup has order prime to `r`. -/
public theorem lemma115_closure_B_coprime_r
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    Nat.Coprime h102.exponent.r
      (Nat.card (Subgroup.closure (peterfalviKSet
        (Subgroup.centralizer ({t * d83.u} : Set X)) t))) := by
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let K : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  have hCodd : Odd (Nat.card C) := by
    simpa [C] using
      lemma115_centralizer_tu_odd hM ht htM d83 htwo h42 d h102 h114
  have hCnorm : t ∈ Subgroup.normalizer (C : Set X) := by
    simpa [C] using
      (lemma115_inverter_mem_normalizer_centralizer_singleton (X := X)
        ht (by
          have htt : t * t = 1 := by
            simpa [pow_two] using ht.sq_eq_one
          simp [rightConjugateElem, ht.inv_eq_self,
            d83.u_involution.inv_eq_self, ← mul_assoc, htt]))
  apply h102.exponent.r_prime.coprime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨x, hxB, hxorder⟩ :=
    lemma115_exists_prime_order_mem_peterfalviKSet_of_dvd_closure
      h42 ht hCodd hCnorm h102.exponent.r_prime
        (by simpa [K, C] using hdiv)
  exact lemma115_B_no_order_r hM ht htM d83 h42 htwo d h102 h114
    hxB hxorder

/-- The generated anti-fixed subgroup is disjoint from the fixed subgroup
`V`, because their intersection is a normal `r'`-subgroup of `V` and
`O_{r'}(V)=1`. -/
public theorem lemma115_closure_B_disjoint_V
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    Disjoint
      (Subgroup.closure (peterfalviKSet
        (Subgroup.centralizer ({t * d83.u} : Set X)) t))
      (peterfalviV (M ⊓ rightConjugate M t) t) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let K : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let V : Subgroup X := peterfalviV D t
  have hVeq : peterfalviV C t = V := by
    simpa [C, D, V] using
      lemma115_peterfalviV_centralizer_tu_eq hM ht d83
  obtain ⟨_hleft, _hright, hKnorm, _hsup⟩ :=
    lemma115_centralizer_tu_decomposition
      hM ht htM d83 htwo h42 d h102 h114
  have hKcop : Nat.Coprime h102.exponent.r (Nat.card K) := by
    simpa [K, C] using
      lemma115_closure_B_coprime_r
        hM ht htM d83 h42 htwo d h102 h114
  have hVcore : pPrimeCore h102.exponent.r V = ⊥ := by
    simpa [D, V] using lemma115_pPrimeCore_V_eq_bot hM htM d h102
  have hKleC : K ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hVleC : V ≤ C := by
    rw [← hVeq]
    exact inf_le_left
  let Kc : Subgroup C := K.subgroupOf C
  have hKcNorm : Kc.Normal := by
    simpa [Kc] using hKnorm
  let i : V →* C :=
    { toFun := fun x => ⟨(x : X), hVleC x.property⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  let J : Subgroup V := Kc.comap i
  have hJnormal : J.Normal := hKcNorm.comap i
  have hJeq : J = K.subgroupOf V := by
    dsimp [J, Kc, i]
    ext x
    change (x : X) ∈ K ↔ (x : X) ∈ K
    rfl
  have hcardJ : Nat.card J = Nat.card (K ⊓ V : Subgroup X) := by
    rw [hJeq]
    calc
      Nat.card (K.subgroupOf V) =
          Nat.card ((K.subgroupOf V).map V.subtype) := by
            symm
            exact Subgroup.card_map_of_injective V.subtype_injective
      _ = Nat.card (K ⊓ V : Subgroup X) := by
        rw [Subgroup.subgroupOf_map_subtype]
  have hJcop : Nat.Coprime h102.exponent.r (Nat.card J) := by
    rw [hcardJ]
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left) hKcop
  have hJbot : J = ⊥ := by
    apply (pPrimeCore_eq_bot_iff (G := V)
      (p := h102.exponent.r)).mp hVcore
    · exact hJnormal
    · exact hJcop
  apply (Subgroup.subgroupOf_eq_bot).mp
  rw [← hJeq]
  exact hJbot

/-- Part (c), before adding the normal-complement packaging: the anti-fixed
set is the carrier of its closure subgroup, is abelian and odd, and has
order coprime to the Fitting subgroup of `V`. -/
public theorem lemma115_B_subgroup_properties
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
    let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
    let V : Subgroup X := peterfalviV (M ⊓ rightConjugate M t) t
    (B : Set X) = peterfalviKSet C t ∧
      IsMulCommutative B ∧ Odd (Nat.card B) ∧
      Nat.Coprime (Nat.card B)
        (Nat.card (fittingSubgroupOf V)) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let V : Subgroup X := peterfalviV D t
  have hCodd : Odd (Nat.card C) := by
    simpa [C] using
      lemma115_centralizer_tu_odd hM ht htM d83 htwo h42 d h102 h114
  have hCnorm : t ∈ Subgroup.normalizer (C : Set X) := by
    simpa [C] using
      (lemma115_inverter_mem_normalizer_centralizer_singleton (X := X)
        ht (by
          have htt : t * t = 1 := by
            simpa [pow_two] using ht.sq_eq_one
          simp [rightConjugateElem, ht.inv_eq_self,
            d83.u_involution.inv_eq_self, ← mul_assoc, htt]))
  have hVeq : peterfalviV C t = V := by
    simpa [C, D, V] using
      lemma115_peterfalviV_centralizer_tu_eq hM ht d83
  have hdisj : Disjoint B (peterfalviV C t) := by
    rw [hVeq]
    simpa [B, C, D, V] using
      lemma115_closure_B_disjoint_V
        hM ht htM d83 h42 htwo d h102 h114
  have hBset : (B : Set X) = peterfalviKSet C t :=
    lemma115_closure_peterfalviKSet_eq_set_of_disjoint
      ht hCnorm hCodd hdisj
  have hBcomm : IsMulCommutative B :=
    lemma115_peterfalviKernel_commutative_of_eq_set hBset
  have hBleC : B ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hBodd : Odd (Nat.card B) :=
    hCodd.of_dvd_nat (Subgroup.card_dvd_of_le hBleC)
  have hBcopR : Nat.Coprime h102.exponent.r (Nat.card B) := by
    simpa [B, C] using
      lemma115_closure_B_coprime_r
        hM ht htM d83 h42 htwo d h102 h114
  have hFp : IsPGroup h102.exponent.r (fittingSubgroupOf V) := by
    rw [h102.fitting_eq_derived_inf]
    simpa [D, V] using h102.derived_inf_isPGroup
  have hBcopF : Nat.Coprime (Nat.card B)
      (Nat.card (fittingSubgroupOf V)) := by
    letI : Fact h102.exponent.r.Prime := ⟨h102.exponent.r_prime⟩
    rcases hFp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hBcopR.symm.pow_right n
  exact ⟨hBset, hBcomm, hBodd, hBcopF⟩

end CFSG.BenderSuzuki
