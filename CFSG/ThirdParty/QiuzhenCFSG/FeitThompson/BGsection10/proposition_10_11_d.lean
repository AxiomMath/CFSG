module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_11_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_commutator_le_left_of_le_normalizer
    {K P : Subgroup G} (hPnormK : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, P⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro k hk p hp
  have hp_norm : p ∈ Subgroup.normalizer (K : Set G) := hPnormK hp
  have hpk_inv : p * k⁻¹ * p⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hp_norm k⁻¹).1 (K.inv_mem hk)
  simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hpk_inv

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_commutator_isPiSubgroup_of_left
    {π : Set Nat.Primes} {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hKπ : IsPiSubgroup (G := G) π K) :
    IsPiSubgroup (G := G) π ⁅K, P⁆ := by
  intro q hq
  exact hKπ q
    (hq.trans (Subgroup.card_dvd_of_le
      (section10_commutator_le_left_of_le_normalizer hPnormK)))

private theorem CFSG.section10_msigma_isPiSubgroup_pPrime_of_not_mem_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpσ : p ∉ section10SigmaPrimes M) :
    IsPiSubgroup (G := G) (section10PPrimeSet p) (section10Msigma M) := by
  intro q hq_dvd
  rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hqp
  have hqσ : q ∈ section10SigmaPrimes M :=
    (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card q hq_dvd
  exact hpσ (by simpa [hqp] using hqσ)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_commutator_le_ambientDerived_of_le
    {M K P : Subgroup G} (hKle : K ≤ M) (hPle : P ≤ M) :
    ⁅K, P⁆ ≤ ambientDerivedSubgroup M := by
  have hcomm_le : ⁅K, P⁆ ≤ ⁅M, M⁆ :=
    Subgroup.commutator_mono hKle hPle
  rw [ambientDerivedSubgroup, derivedSubgroup, derivedSeries_one]
  change ⁅K, P⁆ ≤ (_root_.commutator M).map M.subtype
  rw [Subgroup.map_subtype_commutator]
  exact hcomm_le

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isPiSubgroup_sup_of_normal_right
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hH : IsPiSubgroup (G := G) π H) (hK : IsPiSubgroup (G := G) π K)
    [K.Normal] :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  intro p hpSup
  have hmul : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) := by
    simpa using (Subgroup.mul_normal H K)
  have hcard_sup_set :
      Nat.card (↑(H ⊔ K) : Set G) =
        Nat.card ((H : Set G) * (K : Set G) : Set G) :=
    Nat.card_congr (Set.equivOfEq hmul)
  have hcard_sup :
      Nat.card (↥(H ⊔ K)) = Nat.card ((H : Set G) * (K : Set G) : Set G) := by
    simpa using hcard_sup_set
  have hcard_mul :
      Nat.card ((H : Set G) * (K : Set G) : Set G) =
        Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient
        (s := K) (t := (H : Set G)))
  have hset_image :
      ((H : Set G).image (↑) : Set (G ⧸ K)) =
        (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcard_image_set :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) :=
    Nat.card_congr (Set.equivOfEq hset_image)
  have hcard_image_subgroup :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K)) := by
    exact hcard_image_set
  have hp_mul :
      p.val ∣ Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    rw [← hcard_mul, ← hcard_sup]
    exact hpSup
  rcases p.property.dvd_mul.mp hp_mul with hpK | hpImg
  · exact hK p hpK
  · have hpMap : p.val ∣ Nat.card (H.map (QuotientGroup.mk' K)) := by
      rwa [hcard_image_subgroup] at hpImg
    exact hH p (hpMap.trans
      (Subgroup.card_map_dvd (H := H) (QuotientGroup.mk' K)))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isPiSubgroup_sup_of_le_normalizer
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hHπ : IsPiSubgroup (G := G) π H) (hKπ : IsPiSubgroup (G := G) π K)
    (hHnormK : H ≤ Subgroup.normalizer (K : Set G)) :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  classical
  let S : Subgroup G := H ⊔ K
  let Hs : Subgroup S := H.subgroupOf S
  let Ks : Subgroup S := K.subgroupOf S
  have hHsπ : IsPiSubgroup (G := S) π Hs := by
    intro q hq
    have hcard : Nat.card Hs = Nat.card H := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := S)
          (by simp [S])).toEquiv
    exact hHπ q (by simpa [hcard] using hq)
  have hKsπ : IsPiSubgroup (G := S) π Ks := by
    intro q hq
    have hcard : Nat.card Ks = Nat.card K := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := S)
          (by simp [S])).toEquiv
    exact hKπ q (by simpa [hcard] using hq)
  haveI : Ks.Normal := by
    simpa [S, Ks] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := H) (N := K) hHnormK)
  have hHsKs_top : Hs ⊔ Ks = ⊤ := by
    calc
      Hs ⊔ Ks = S.subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := H) (A' := K) (B := S)
          (by simp [S])
          (by simp [S])
      _ = ⊤ := by simp
  have htopπ : IsPiSubgroup (G := S) π (⊤ : Subgroup S) := by
    rw [← hHsKs_top]
    exact section10_isPiSubgroup_sup_of_normal_right
      (G := S) (π := π) (H := Hs) (K := Ks) hHsπ hKsπ
  intro q hq
  exact htopπ q (by simpa using hq)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_le_normalizer_sup_of_le_normalizers
    {R A B : Subgroup G}
    (hRA : R ≤ Subgroup.normalizer (A : Set G))
    (hRB : R ≤ Subgroup.normalizer (B : Set G)) :
    R ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  classical
  intro r hr
  have hforward :
      ∀ g ∈ R, ∀ x, x ∈ A ⊔ B → g * x * g⁻¹ ∈ A ⊔ B := by
    intro g hg x hx
    rw [Subgroup.sup_eq_closure] at hx ⊢
    refine
      Subgroup.closure_induction (p := fun y _hy => g * y * g⁻¹ ∈
        Subgroup.closure ((A : Set G) ∪ (B : Set G))) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyA | hyB
      · exact Subgroup.subset_closure
          (Or.inl ((Subgroup.mem_normalizer_iff.mp (hRA hg) y).1 hyA))
      · exact Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp (hRB hg) y).1 hyB))
    · simp
    · intro y z _hy _hz hy hz
      simpa [mul_assoc] using
        (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem hy hz
    · intro y _hy hy
      simpa [mul_assoc] using
        (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward r hr x
  · intro hx
    have hx' := hforward r⁻¹ (R.inv_mem hr) (r * x * r⁻¹) hx
    simpa [mul_assoc] using hx'

omit [IsMinCE G] in
private theorem CFSG.section10_commutator_centralizerIn_eq_bot_of_coprime
    {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hKcomm : IsMulCommutative K) :
    subgroupCentralizerIn ⁅K, P⁆ P = ⊥ := by
  classical
  haveI : Subgroup.Normalizes P K := ⟨hPnormK⟩
  let Cfix : Subgroup K := fixedPointSubgroup (↥P) (↥K)
  let Ccomm : Subgroup K := commutatorAction (A := ↥P) (G := ↥K)
  have hfixed_eq :
      Cfix = (subgroupCentralizerIn K P).subgroupOf K := by
    simpa [Cfix] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K P hPnormK
  have hcomm_map : Ccomm.map K.subtype = ⁅K, P⁆ := by
    simpa [Ccomm] using
      commutatorAction_subgroup_conj_map_eq_commutator K P hPnormK
  have hsolvK : IsSolvable K :=
    isSolvable_of_comm fun x y => hKcomm.is_comm.comm x y
  have hcompl : IsCompl Cfix Ccomm := by
    simpa [Cfix, Ccomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := K) (A := P) hsolvK hcop hKcomm)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxK0, hxCentP⟩
  have hxK : x ∈ K :=
    section10_commutator_le_left_of_le_normalizer hPnormK hxK0
  let xK : K := ⟨x, hxK⟩
  have hxFix : xK ∈ Cfix := by
    rw [hfixed_eq]
    change (x : G) ∈ subgroupCentralizerIn K P
    exact ⟨hxK, hxCentP⟩
  have hxComm : xK ∈ Ccomm := by
    have hxMap : x ∈ Ccomm.map K.subtype := by
      simpa [hcomm_map] using hxK0
    rcases Subgroup.mem_map.mp hxMap with ⟨y, hyC, hyx⟩
    have hy_eq : y = xK := Subtype.ext hyx
    simpa [hy_eq] using hyC
  have hxbot : xK ∈ (⊥ : Subgroup K) := by
    have hinf_bot : Cfix ⊓ Ccomm = ⊥ := hcompl.disjoint.eq_bot
    have hxinf : xK ∈ Cfix ⊓ Ccomm := ⟨hxFix, hxComm⟩
    simpa [hinf_bot] using hxinf
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_subgroupCentralizerIn_sup_eq_bot_of_normalized_factors
    {A B P : Subgroup G}
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hPnormB : P ≤ Subgroup.normalizer (B : Set G))
    (hAnormB : A ≤ Subgroup.normalizer (B : Set G))
    (hABdisj : Disjoint A B)
    (hAfix : subgroupCentralizerIn A P = ⊥)
    (hBfix : subgroupCentralizerIn B P = ⊥) :
    subgroupCentralizerIn (A ⊔ B : Subgroup G) P = ⊥ := by
  classical
  let S : Subgroup G := A ⊔ B
  let As : Subgroup S := A.subgroupOf S
  let Bs : Subgroup S := B.subgroupOf S
  haveI : Bs.Normal := by
    simpa [S, Bs] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := B) hAnormB)
  have hAsBs_top : As ⊔ Bs = ⊤ := by
    calc
      As ⊔ Bs = S.subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := A) (A' := B) (B := S)
          (by simp [S])
          (by simp [S])
      _ = ⊤ := by simp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxS, hxCentP⟩
  let xS : S := ⟨x, hxS⟩
  have hxTop : xS ∈ As ⊔ Bs := by simp [hAsBs_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := As) (t := Bs) (x := xS)).1 hxTop with
    ⟨aS, haS, bS, hbS, habxS⟩
  let a : G := aS
  let b : G := bS
  have haA : a ∈ A := by
    simpa [a, As, Subgroup.mem_subgroupOf] using haS
  have hbB : b ∈ B := by
    simpa [b, Bs, Subgroup.mem_subgroupOf] using hbS
  have hx_eq : x = a * b := by
    have hval := congrArg (fun y : S => (y : G)) habxS
    simpa [a, b, xS] using hval.symm
  have hfactor_fixed :
      ∀ p0 : G, p0 ∈ P →
        p0 * a * p0⁻¹ = a ∧ p0 * b * p0⁻¹ = b := by
    intro p0 hp0
    let a' : G := p0 * a * p0⁻¹
    let b' : G := p0 * b * p0⁻¹
    have ha'A : a' ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hPnormA hp0) a).1 haA
    have hb'B : b' ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hPnormB hp0) b).1 hbB
    have hx_comm : p0 * x = x * p0 :=
      Subgroup.mem_centralizer_iff.mp hxCentP p0 hp0
    have hconj_x : p0 * x * p0⁻¹ = x := by
      calc
        p0 * x * p0⁻¹ = (x * p0) * p0⁻¹ := by rw [hx_comm]
        _ = x := by simp [mul_assoc]
    have hEq : a' * b' = a * b := by
      simpa [a', b', hx_eq, mul_assoc] using hconj_x
    have ha'_eq : a' = a * b * b'⁻¹ := by
      calc
        a' = (a' * b') * b'⁻¹ := by simp [mul_assoc]
        _ = (a * b) * b'⁻¹ := by rw [hEq]
        _ = a * b * b'⁻¹ := by simp [mul_assoc]
    have hcross : a⁻¹ * a' = b * b'⁻¹ := by
      calc
        a⁻¹ * a' = a⁻¹ * (a * b * b'⁻¹) := by rw [ha'_eq]
        _ = b * b'⁻¹ := by simp [mul_assoc]
    have hcrossA : a⁻¹ * a' ∈ A := A.mul_mem (A.inv_mem haA) ha'A
    have hcrossB : a⁻¹ * a' ∈ B := by
      rw [hcross]
      exact B.mul_mem hbB (B.inv_mem hb'B)
    have hcross1 : a⁻¹ * a' = 1 :=
      Subgroup.disjoint_def.mp hABdisj hcrossA hcrossB
    have ha_fixed : a' = a := by
      have h := congrArg (fun t : G => a * t) hcross1
      simpa [mul_assoc] using h
    have hb_fixed : b' = b := by
      have h := hEq
      rw [ha_fixed] at h
      have h' := congrArg (fun t : G => a⁻¹ * t) h
      simpa [mul_assoc] using h'
    exact ⟨by simpa [a'] using ha_fixed, by simpa [b'] using hb_fixed⟩
  have haCent : a ∈ subgroupCentralizerIn A P := by
    refine ⟨haA, ?_⟩
    change a ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p0 hp0
    have hfix := (hfactor_fixed p0 hp0).1
    have hmul := congrArg (fun t : G => t * p0) hfix
    simpa [mul_assoc] using hmul
  have hbCent : b ∈ subgroupCentralizerIn B P := by
    refine ⟨hbB, ?_⟩
    change b ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p0 hp0
    have hfix := (hfactor_fixed p0 hp0).2
    have hmul := congrArg (fun t : G => t * p0) hfix
    simpa [mul_assoc] using hmul
  have ha1 : a = 1 := by
    have : a ∈ (⊥ : Subgroup G) := by simpa [hAfix] using haCent
    exact Subgroup.mem_bot.mp this
  have hb1 : b = 1 := by
    have : b ∈ (⊥ : Subgroup G) := by simpa [hBfix] using hbCent
    exact Subgroup.mem_bot.mp this
  simp [hx_eq, ha1, hb1]

private theorem CFSG.section10_commutator_le_centralizer_msigma_of_10_11d
    {M K P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hKle : K ≤ M)
    (hKσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K) (hpσ : p ∉ section10SigmaPrimes M)
    (hPle : P ≤ subgroupNormalizerIn M (K : Set G)) (hPcard : Nat.card P = p.val)
    (hCσ : subgroupCentralizerIn (section10Msigma M) P = ⊥)
    (hKcomm : IsMulCommutative K) (hKp' : IsPiSubgroup (section10PPrimeSet p) K) :
    ⁅K, P⁆ ≤ Subgroup.centralizer (section10Msigma M : Set G) := by
  classical
  let K0 : Subgroup G := ⁅K, P⁆
  let S : Subgroup G := K0 ⊔ section10Msigma M
  let T : Subgroup G := P ⊔ S
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) :=
    hPle.trans (section10_subgroupNormalizerIn_le_normalizer M (K : Set G))
  have hPleM : P ≤ M :=
    hPle.trans (section10_subgroupNormalizerIn_le M (K : Set G))
  have hK0leK : K0 ≤ K := by
    simpa [K0] using section10_commutator_le_left_of_le_normalizer hPnormK
  have hK0leM : K0 ≤ M := hK0leK.trans hKle
  have hMsigma_le_M : section10Msigma M ≤ M := by
    rw [section10_msigma_eq_piCoreIn]
    exact piCoreIn_le (G := G) (section10SigmaPrimes M) M
  have hSleM : S ≤ M := by
    exact sup_le hK0leM hMsigma_le_M
  have hTleM : T ≤ M := by
    exact sup_le hPleM hSleM
  have hK0norm_KP :
      (K0.subgroupOf (K ⊔ P : Subgroup G)).Normal := by
    simpa [K0] using commutator_normal_in_sup K P
  have hKP_norm_K0 : K ⊔ P ≤ Subgroup.normalizer (K0 : Set G) := by
    have hK0leKP : K0 ≤ K ⊔ P := by
      simpa [K0] using commutator_le_sup K P
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := K0) (K := K ⊔ P) hK0leKP).mp hK0norm_KP
  have hPnormK0 : P ≤ Subgroup.normalizer (K0 : Set G) :=
    le_sup_right.trans hKP_norm_K0
  have hK0normMsigma : K0 ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hK0leM.trans (section10_le_normalizer_msigma (G := G))
  have hPnormMsigma : P ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hPleM.trans (section10_le_normalizer_msigma (G := G))
  have hPnormS : P ≤ Subgroup.normalizer (S : Set G) := by
    simpa [S] using
      section10_le_normalizer_sup_of_le_normalizers
        (G := G) (R := P) (A := K0) (B := section10Msigma M)
        hPnormK0 hPnormMsigma
  have hK0σc : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K0 := by
    simpa [K0] using
      section10_commutator_isPiSubgroup_of_left
        (G := G) (π := (section10SigmaPrimes M)ᶜ)
        hPnormK hKσ
  have hMsigmaσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) (section10Msigma M) := by
    intro q hq
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hq
  have hK0_Msigma_disj : Disjoint K0 (section10Msigma M) := by
    have hσdisj : Disjoint (section10SigmaPrimes M)ᶜ (section10SigmaPrimes M) := by
      rw [Set.disjoint_left]
      intro q hqcomp hqσ
      exact hqcomp hqσ
    exact section10_disjoint_of_isPiSubgroup_disjoint_primes
      (G := G) hK0σc hMsigmaσ hσdisj
  have hK0p' : IsPiSubgroup (G := G) (section10PPrimeSet p) K0 := by
    simpa [K0] using
      section10_commutator_isPiSubgroup_of_left
        (G := G) (π := section10PPrimeSet p) hPnormK hKp'
  have hMsigmap' : IsPiSubgroup (G := G) (section10PPrimeSet p) (section10Msigma M) :=
    section10_msigma_isPiSubgroup_pPrime_of_not_mem_sigma (G := G) hM hpσ
  have hSp' : IsPiSubgroup (G := G) (section10PPrimeSet p) S := by
    simpa [S] using
      section10_isPiSubgroup_sup_of_le_normalizer
        (G := G) (π := section10PPrimeSet p)
        (H := K0) (K := section10Msigma M)
        hK0p' hMsigmap' hK0normMsigma
  have hPp : IsPGroup p.val P := by
    refine (IsPGroup.iff_card (p := p.val) (G := P)).2 ?_
    exact ⟨1, by simp [hPcard, pow_one]⟩
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup hPp
  have hp'_disj_singleton : Disjoint (section10PPrimeSet p) ({p} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro q hqcomp hqp
    exact hqcomp hqp
  have hS_P_disj : Disjoint S P :=
    section10_disjoint_of_isPiSubgroup_disjoint_primes
      (G := G) hSp' hPπ hp'_disj_singleton
  have hsingleton_disj_p' : Disjoint ({p} : Set Nat.Primes) (section10PPrimeSet p) := by
    exact hp'_disj_singleton.symm
  have hcopPK : Nat.Coprime (Nat.card P) (Nat.card K) :=
    section10_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hPπ hKp' hsingleton_disj_p'
  have hK0fix : subgroupCentralizerIn K0 P = ⊥ := by
    simpa [K0] using
      section10_commutator_centralizerIn_eq_bot_of_coprime
        (G := G) hPnormK hcopPK hKcomm
  have hSfix : subgroupCentralizerIn S P = ⊥ := by
    simpa [S] using
      section10_subgroupCentralizerIn_sup_eq_bot_of_normalized_factors
        (G := G) (A := K0) (B := section10Msigma M) (P := P)
        hPnormK0 hPnormMsigma hK0normMsigma hK0_Msigma_disj hK0fix hCσ
  have hTne_top : T ≠ ⊤ := by
    intro hTtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x hx
      exact hTleM (by simp [hTtop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvT : IsSolvable T :=
    IsMinCE.proper_subgroups_solvable T (lt_top_iff_ne_top.2 hTne_top)
  have hoddT : Odd (Nat.card T) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card T)
  have hSnormalT : (S.subgroupOf T).Normal := by
    simpa [S, T] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := P) (N := S) hPnormS)
  have hSsub_Psub_disj : Disjoint (S.subgroupOf T) (P.subgroupOf T) := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxP
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hS_P_disj hxS hxP
  have hSsubPsub_top :
      S.subgroupOf T ⊔ P.subgroupOf T = ⊤ := by
    calc
      S.subgroupOf T ⊔ P.subgroupOf T = P.subgroupOf T ⊔ S.subgroupOf T := by
        rw [sup_comm]
      _ = T.subgroupOf T := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := P) (A' := S) (B := T)
          (by simp [T])
          (by simp [T])
      _ = ⊤ := by simp
  have hcompT : (S.subgroupOf T).IsComplement' (P.subgroupOf T) := by
    letI : (S.subgroupOf T).Normal := hSnormalT
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · exact hSsub_Psub_disj
    · rw [Set.eq_univ_iff_forall]
      intro y
      have hyTop : y ∈ S.subgroupOf T ⊔ P.subgroupOf T := by
        simp [hSsubPsub_top]
      rcases (Subgroup.mem_sup_of_normal_left
          (s := S.subgroupOf T) (t := P.subgroupOf T) (x := y)).1 hyTop with
        ⟨s, hs, r, hr, hsr⟩
      exact ⟨s, hs, r, hr, hsr⟩
  have hPsub_prime : Nat.Prime (Nat.card (P.subgroupOf T)) := by
    have hcard : Nat.card (P.subgroupOf T) = p.val := by
      rw [natCard_subgroupOf_eq P T (by simp [T]), hPcard]
    simpa [hcard] using p.property
  have hfixT : subgroupCentralizerIn (S.subgroupOf T) (P.subgroupOf T) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq T S P (by simp [T]), hSfix]
    simp
  have hSnil_sub : Group.IsNilpotent (S.subgroupOf T) :=
    theorem_3_7 (G := T) (S.subgroupOf T) (P.subgroupOf T)
      hsolvT hoddT hSnormalT hcompT hPsub_prime hfixT
  have hSnil : Group.IsNilpotent S := by
    let e : S.subgroupOf T ≃* S :=
      Subgroup.subgroupOfEquivOfLe (H := S) (K := T) (by simp [T])
    letI : Group.IsNilpotent (S.subgroupOf T) := hSnil_sub
    exact Group.nilpotent_of_mulEquiv (G := S.subgroupOf T) (G' := S) e
  -- In the nilpotent group `S`, the `sigma(M)'` subgroup `K₀` centralizes
  -- the normal `sigma(M)` subgroup `M_sigma`.
  have hK0cent : K0 ≤ Subgroup.centralizer (section10Msigma M : Set G) := by
    have hσdisj : Disjoint (section10SigmaPrimes M)ᶜ (section10SigmaPrimes M) := by
      rw [Set.disjoint_left]
      intro q hqcomp hqσ
      exact hqcomp hqσ
    exact
      section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
        (G := G) (π := (section10SigmaPrimes M)ᶜ)
        (ρ := section10SigmaPrimes M) (L := S) (A := K0)
        (B := section10Msigma M) hσdisj hSnil
        (by simp [S])
        (by simp [S])
        hK0σc hMsigmaσ
  simpa [K0] using hK0cent

/-- Proposition 10.11(d). -/
public theorem CFSG.proposition_10_11_d
    {M K P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hKle : K ≤ M)
    (hKσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K) (hpσ : p ∉ section10SigmaPrimes M)
    (hPle : P ≤ subgroupNormalizerIn M (K : Set G)) (hPcard : Nat.card P = p.val)
    (hCσ : subgroupCentralizerIn (section10Msigma M) P = ⊥)
    (hKcomm : IsMulCommutative K) (hKp' : IsPiSubgroup (section10PPrimeSet p) K) :
    (⁅K, P⁆) ≤ Subgroup.centralizer (section10Msigma M : Set G) ∧
      section10NormalIn (⁅K, P⁆) M ∧
      IsCyclic ↥(⁅K, P⁆) := by
  classical
  let K0 : Subgroup G := ⁅K, P⁆
  let D : Subgroup G := subgroupCentralizerIn K (section10Msigma M) ⊓ ambientDerivedSubgroup M
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) :=
    hPle.trans (section10_subgroupNormalizerIn_le_normalizer M (K : Set G))
  have hPleM : P ≤ M :=
    hPle.trans (section10_subgroupNormalizerIn_le M (K : Set G))
  have hK0cent : K0 ≤ Subgroup.centralizer (section10Msigma M : Set G) := by
    simpa [K0] using
      section10_commutator_le_centralizer_msigma_of_10_11d
        (G := G) hM hKle hKσ hpσ hPle hPcard hCσ hKcomm hKp'
  have hK0leK : K0 ≤ K := by
    simpa [K0] using section10_commutator_le_left_of_le_normalizer hPnormK
  have hK0leDer : K0 ≤ ambientDerivedSubgroup M := by
    simpa [K0] using section10_commutator_le_ambientDerived_of_le hKle hPleM
  have hK0leD : K0 ≤ D := by
    intro x hx
    exact ⟨⟨hK0leK hx, hK0cent hx⟩, hK0leDer hx⟩
  rcases proposition_10_11_c (G := G) hM hKle hKσ with ⟨hDnormM, hDcyc⟩
  have hK0cyc : IsCyclic K0 := by
    letI : IsCyclic D := by simpa [D] using hDcyc
    exact Subgroup.isCyclic_of_le hK0leD
  have hK0normM : section10NormalIn K0 M := by
    rcases hDnormM with ⟨hDleM, hDnormalM⟩
    let K0D : Subgroup D := K0.subgroupOf D
    haveI : IsCyclic D := by simpa [D] using hDcyc
    have hK0Dchar : K0D.Characteristic :=
      section10_characteristic_of_subgroup_of_isCyclic_pre (K := K0D)
    letI : K0D.Characteristic := hK0Dchar
    have hnormD_le_normK0 :
        Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (K0 : Set G) := by
      have hnorm :=
        section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
          (G := G) D K0D
      have hmap_eq : (K0D.map D.subtype : Subgroup G) = K0 := by
        calc
          (K0D.map D.subtype : Subgroup G) = K0 ⊓ D := by
            simp [K0D]
          _ = K0 := inf_eq_left.mpr hK0leD
      simpa [hmap_eq] using hnorm
    have hMnormD : M ≤ Subgroup.normalizer (D : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).mp hDnormalM
    exact
      section10_normalIn_of_le_normalizer
        (by exact hK0leD.trans hDleM)
        (hMnormD.trans hnormD_le_normK0)
  exact ⟨by simpa [K0] using hK0cent,
    by simpa [K0] using hK0normM,
    by simpa [K0] using hK0cyc⟩

end Section10
