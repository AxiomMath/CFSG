module

public import CFSG.RankThree.PartOne.KF4.F4ThreePerX
public import CFSG.RankThree.PartOne.KF4.F4ThreeArith
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.NativeCyclicF4
public import CFSG.RankThree.PartOne.KF4.F4Pointwise
public import CFSG.RankThree.PartOne.KF4.F4Sylow

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise

theorem exists_ne_one_ker_of_card_sq' {A : Type*} [Group A] [Finite A] {L : Type*} [Field L]
    {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ 2) (χ : A →* Lˣ) (hχ : ∀ a, χ a ^ p = 1) :
    ∃ a : A, a ≠ 1 ∧ χ a = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective χ := (injective_iff_map_eq_one χ).2 fun a ha => by
    by_contra hne
    exact hcon a hne ha
  have hle : Nat.card A ≤ Nat.card (rootsOfUnity p L) :=
    Nat.card_le_card_of_injective (fun a => (⟨χ a, (mem_rootsOfUnity p (χ a)).2 (hχ a)⟩ :
      rootsOfUnity p L)) fun a b hab => hinj (congrArg Subtype.val hab)
  have h2 := card_rootsOfUnity L p
  have hp2 := hp.two_le
  rw [hA] at hle
  nlinarith

@[expose] def f4Cox : WeylGroup Tag.F4 :=
  (coxeterSystem Tag.F4).wordProd [f4Index 0, f4Index 1, f4Index 2, f4Index 3]

@[expose] def f4CoxMat : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![0, 1, 0, -1; 1, 1, 0, -1; 0, 2, 0, -1; 0, 0, 1, -1]


theorem weylMatrix_f4Cox : weylMatrix f4Cox = f4CoxMat :=
  weylMatrix_wordProd_of' (ω := [f4Index 0, f4Index 1, f4Index 2, f4Index 3])
    (by decide +kernel)

theorem weylMatrix_f4Cox_ten : weylMatrix (f4Cox ^ 10) = -weylMatrix f4W3 := by
  have h6 : f4CoxMat ^ 6 = -1 := by decide +kernel
  have h4 : f4CoxMat ^ 4 = f4W3Mat := by decide +kernel
  rw [weylMatrix_pow, weylMatrix_f4Cox, weylMatrix_f4W3, show 10 = 6 + 4 from rfl, pow_add, h6, h4,
    neg_one_mul]

section Main

theorem f4_three_main (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hq3 : δ = -1 → 2 < ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      ((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (δ • weylMatrix f4W3) *ᵥ u)
    (hstep : F4CoreStep K p L) :
    (∀ x : adjointGroup .F4 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V)) ∧
    (∀ B : Subgroup (MulAut (adjointGroup .F4 K)),
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .F4 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .F4 K))))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .F4 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ = (fixedCharTuples (f4ThreeM δ) Fr).map (rootDiagUnitHom .F4 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show f4ThreeM δ = δ • weylMatrix f4W3 from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set N : ℕ := (((Nat.card K : ℤ) ^ 2 + δ * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .F4 L) := (f4ThreeZ δ Fr).map (rootDiagUnitHom .F4 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact f4Three_card_Z δ hδ Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := f4ThreeP_eval_ne_zero δ hδ hq2
    rwa [f4ThreeP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .F4 K)).factorization p = p ^ N.factorization p :=
    f4Three_ordProj K δ hδ hp hp3 hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow_F4 K hf hK L hp hp3 n hnC Z0 hZ0le
    hN hZ0card hord
  have hodd : Odd (((Nat.card K : ℤ) ^ 2 + δ * (Nat.card K : ℤ) + 1).natAbs) :=
    f4Three_odd δ hδ _
  have hsolv : ∀ x : adjointGroup .F4 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    have hpg : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hpg
    have hxc : c * x * c⁻¹ ∈ subtorusImage (adjEmb .F4 K L) g0 Z0 :=
      hc x (Subgroup.mem_zpowers x)
    have hh : g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ :=
      hZ0le ((mem_subtorusImage_iff _ _ _ _).1 hxc)
    obtain ⟨ψ, hψinj, -, hψV, -⟩ := f4_three_perx K hf hK δ hδ hq3 hp hp3 L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh
    by_contra hnodd
    have h2 : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hv2 : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) = 2 := by
      rw [orderOf_injective ψ hψinj, Subgroup.orderOf_coe, hv]
    have hmem := hψV V hVn hVs v v.2
    rw [hT] at hmem
    obtain ⟨b', hb', hb'v⟩ := hmem
    have hdvd : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) ∣
        (((Nat.card K : ℤ) ^ 2 + δ * (Nat.card K : ℤ) + 1).natAbs) := by
      rw [← hb'v]
      exact (orderOf_map_dvd (rootDiagUnitHom .F4 L) b').trans
        (f4Three_orderOf_dvd δ hδ Fr hFr hb')
    rw [hv2] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  refine ⟨hsolv, ?_⟩
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .F4 K) :=
    A.comap (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let φ : A₀ →* ModGL .F4 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .F4 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .F4 K L (c * (q : adjointGroup .F4 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc q q.2))
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.F4.rank → Lˣ, φ q = rootDiagUnit .F4 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  set α₀ : Fin Tag.F4.rank → ℤ := Pi.single (f4Index 0) 1 with hα₀def
  have hα₀ : IsRoot .F4 α₀ := IsRoot.basis (f4Index 0)
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => rootChar (β q) α₀
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α₀
      map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h1 : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))
        ((q : adjointGroup .F4 K) ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    have h2 : (q : adjointGroup .F4 K) ^ p = 1 := hIntinj (h1.trans (map_one _).symm)
    have h3 : q ^ p = 1 := Subtype.ext h2
    rw [h3, map_one]
  obtain ⟨q, hq1, hqχ⟩ := exists_ne_one_ker_of_card_sq' hp hA₀card χ hχp
  set x : adjointGroup .F4 K := (q : adjointGroup .F4 K) with hxdef
  have hx1 : x ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h1 : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) (x ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    exact hIntinj (h1.trans (map_one _).symm)
  have hx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxA : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) x ∈ A := q.2
  have hh : g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ q]
    exact hφT q
  obtain ⟨ψ, hψinj, hψ, -, hψK⟩ := f4_three_perx K hf hK δ hδ hq3 hp hp3 L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  have hb : rootDiagUnit .F4 (β q) = g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hne : (rootCharKernel (β q)).Nonempty := ⟨α₀, hα₀, hqχ⟩
  obtain ⟨Pt, hPq, hcomm, i, hi, h₀, hh₀C, hh₀⟩ := hψK (β q) hb hne
  refine ⟨MulAut.conj x, hxA, fun h1 => hx1 (hIntinj (by rw [h1, map_one])), ?_⟩
  exact hstep hB c g0 hg0C ψ hψinj hψ hPq hcomm i hi h₀ hh₀C hh₀ (hsolv x hx)

end Main

section Final


theorem planeLocalCoreOdd_F4_three_six (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 3).eval (Nat.card K : ℤ) ∨
      (p : ℤ) ∣ (exhaustionPhi 6).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .F4 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := F4_outer_commutator_odd K
  have hcore := localCoreTrivialOn_noninner_F4 K hp hp3
  have hq2odd : 2 < ℓ ^ f := by
    have := four_le_or_eq_three_of_ne_two hℓ hℓ2 hf
    omega
  rcases hpf with h3 | h6
  ·
    have h3' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 := by
      simpa [exhaustionPhi] using h3
    have hΦ3 : ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
        p).2 h3'
      simpa using this
    have hcm := canonicalRep_mem_monomialSubgroup L f4W3
    have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W3, hcm⟩ = f4W3 :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep f4W3)
    have hnW : ∀ u, weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W3, hcm⟩ • u =
        ((1 : ℤ) • weylMatrix f4W3) *ᵥ u := fun u => by
      rw [hπ, one_smul, weylMatrix_mulVec]
    have h := f4_three_main K hf hK 1 (Or.inl rfl) (fun h => absurd h (by decide)) hp hp3
      (f4Three_hΦ_one _ hΦ3) L _ hcm hnW (f4_odd_core_step K hℓ hℓ2 hf hK hp L)
    exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore
      h.2
  ·
    have h6' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
      simpa [exhaustionPhi] using h6
    have hΦ6 : ((Nat.card K : ℕ) : ZMod p) ^ 2 - ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
        p).2 h6'
      simpa using this
    have hcm := canonicalRep_mem_monomialSubgroup L (f4Cox ^ 10)
    have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L (f4Cox ^ 10), hcm⟩ =
        f4Cox ^ 10 := weylQuotientHom_eq (mapsRootLines_canonicalRep (f4Cox ^ 10))
    have hnW : ∀ u, weylQuotientHom .F4 L
        ⟨canonicalRep (coxeterSystem .F4) L (f4Cox ^ 10), hcm⟩ • u =
          ((-1 : ℤ) • weylMatrix f4W3) *ᵥ u := fun u => by
      rw [hπ, ← weylMatrix_mulVec, weylMatrix_f4Cox_ten, neg_one_smul]
    have h := f4_three_main K hf hK (-1) (Or.inr rfl) (fun _ => hq2odd) hp hp3
      (f4Three_hΦ_neg _ hΦ6) L _ hcm hnW (f4_odd_core_step K hℓ hℓ2 hf hK hp L)
    exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore
      h.2

theorem oddEndpoint_F4_oddPhi3Phi6 :
    OddEndpoint .F4 fun p ℓ f =>
      ℓ ≠ 2 ∧ ((p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f) := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_three_six K hℓ hc.1 hf hK hp hp3 (by simpa [cycloVal, hK] using hc.2))).1

end Final

end CFSG.RankThree.PartOne.KF4
