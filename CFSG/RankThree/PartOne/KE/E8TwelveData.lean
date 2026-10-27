module

public import CFSG.RankThree.PartOne.KE.E8TwelveKernel
public import CFSG.RankThree.PartOne.KE.E8TwelveBlock
public import CFSG.RankThree.PartOne.KE.E8TwelveArith
public import CFSG.RankThree.PartOne.KE.E8PerXCore
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.RankThree.PartOne.KE.FiniteFieldAlgClosure
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Pointwise MatrixGroups

section Facts

theorem e8T12_weylImage (u : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd e8T12WW • u = e8T12V *ᵥ u := by
  rw [wordProd_smul_eq_wordMat_mulVec, e8T12WW, wordMat_append, e8T12V, pow_two]
  rfl

theorem d4Set_isRoot (v : WeylGroup Tag.E8) :
    ∀ r ∈ (fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8), IsRoot Tag.E8 r := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact IsRoot.smul hγ.1 v

theorem d4Set_neg (v : WeylGroup Tag.E8) :
    ∀ r ∈ (fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      -r ∈ (fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact ⟨-γ, ⟨IsRoot.neg hγ.1, fun i hi => by simp [hγ.2 i hi]⟩, by simp⟩

theorem twoA2Set_isRoot (v₁ v₂ : WeylGroup Tag.E8) :
    ∀ r ∈ sigmaSetE8 v₁ ∪ sigmaSetE8 v₂, IsRoot Tag.E8 r := by
  intro r hr
  rcases hr with hr | hr <;>
  · rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    exact isRoot_sigmaRootE8 _ hij

theorem twoA2Set_neg (v₁ v₂ : WeylGroup Tag.E8) :
    ∀ r ∈ sigmaSetE8 v₁ ∪ sigmaSetE8 v₂, -r ∈ sigmaSetE8 v₁ ∪ sigmaSetE8 v₂ := by
  intro r hr
  rcases hr with hr | hr
  · rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    left
    rw [sigmaSetE8_eq, sigmaRootE8_neg]
    exact ⟨j, i, hij.symm, rfl⟩
  · rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    right
    rw [sigmaSetE8_eq, sigmaRootE8_neg]
    exact ⟨j, i, hij.symm, rfl⟩

end Facts

section PerX

theorem e8_twelve_perx (hD4 : D4TrialityLayer Tag.E8) (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp7 : 7 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 - ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T12WW)
    (g0 : ModGL .E8 L) (hg0C : g0 ∈ adjointGroup .E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e8T12V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L))
    {x : adjointGroup .E8 K} (hx : orderOf x = p) (c : adjointGroup .E8 K)
    (hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ b : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
        toVec Tag.E8.rank e8T12Alpha0 ∈ rootCharKernel b →
        ∃ Pt : Subgroup (ModGL .E8 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
          ∃ h₀ : ModGL .E8 L, ∀ Y : SL2 K, h₀ * simpleRootSL2 .E8 L (e8Index 3)
            (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T12V *ᵥ u := fun u => by
    rw [hnW]
    exact e8T12_weylImage u
  set ι : adjointGroup .E8 K →* ModGL .E8 L := adjEmb .E8 K L with hιdef
  set h : ModGL .E8 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E8 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit .E8 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have hkd := e8T12_kernel_structure Fr hFr hp hp3 hΦ hb hap hb1
  rcases hkd with hA | ⟨cc, hcc, hker', hgood⟩ | ⟨cc, hcc, hker', hgood⟩
  ·
    have hspan : rootSpan .E8 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    have hfam : IsSigmaFamily n Fr (rootCharKernel b) (fun e : Empty => (e.elim : Subgroup _)) := by
      refine ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
        fun e => e.elim, fun y hy hyR _ => ?_⟩
      rw [hspan, sup_bot_eq] at hy
      refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [hspan] at hg
      have : g = 1 := hg
      rw [this, one_mul, mul_one]
    obtain ⟨ψ, hψinj, hψ, -, -, -, -, hψV⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW hx c
      hbh' hh rfl (fun α hα => hα.1)
      (fun α hα => ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩) hfam
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v hv), fun b' hb' hα => ?_⟩
    exfalso
    rw [hker b' hb', hA] at hα
    exact Set.notMem_empty _ hα
  ·
    obtain ⟨hS1, u, hu, hcertw⟩ := D4Cert.sound hgood
    obtain ⟨-, -, -, hab, hbc, hac, ha, hbl, hcl, -⟩ := hgood
    set v : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w with hv
    have hSeq : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots .E8 (d4Nodes .E8) :=
      hker'.trans hS1
    have hcert : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
        ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
          (v⁻¹ * weylQuotientHom .E8 L ⟨n, hnm⟩ * v) • α =
            u • permLattice (List.formPerm [cc.a, cc.b, cc.c]) α := by
      rw [hnW]
      exact ⟨u, hu, hcertw⟩
    obtain ⟨P, hfam, hP1, h₀, hh₀⟩ := e8_d4_family hD4 hf hK v n hnm hnC cc.a cc.b cc.c hab hbc hac
      (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
      (by rcases hcl with h | h | h <;> simp [h]) hcert
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, hψV⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp
      hordW hx c hbh' hh hSeq (d4Set_isRoot v) (d4Set_neg v) hfam
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v' hv' => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v' hv'), fun b' hb'' _ => ⟨P (), hfam.2.1 (), ?_, h₀, hh₀⟩⟩
    exact e8_perx_commutator Fr n (d4Set_isRoot v) ψ hψHQ hψR hP1 (hPψ ()) (hfam.2.1 ())
  ·
    obtain ⟨hS1, hex12, hex21, hπ₁, hπ₂, horth⟩ :=
      TwoA2Cert.sound (M := e8T12V) (Wl := e8T12VList) e8T12V_eq hgood
    obtain ⟨k₂, _, _, _, hk₂⟩ := exists_finite_field_isAlgClosure ℓ (2 * f) (by omega) K L
    obtain ⟨P, hfam⟩ := e8_two_A2_family hf Fr hFr' hk₂ e8T12V n hnm hnWv
      ((coxeterSystem .E8).wordProd cc.w₁) ((coxeterSystem .E8).wordProd cc.w₂) hex12 hex21 hπ₁
      hπ₂ horth
    have hSeq : rootCharKernel b = sigmaSetE8 ((coxeterSystem .E8).wordProd cc.w₁) ∪
        sigmaSetE8 ((coxeterSystem .E8).wordProd cc.w₂) := hker'.trans hS1
    obtain ⟨ψ, hψinj, hψ, -, -, -, -, hψV⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW hx c
      hbh' hh hSeq (twoA2Set_isRoot _ _) (twoA2Set_neg _ _) hfam
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v' hv' => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v' hv'), fun b' hb'' hα => ?_⟩
    exfalso
    have hα' : toVec Tag.E8.rank e8T12Alpha0 ∈ classSetL e8T12Rows cc.cls := by
      rw [← hker', ← hker b' hb'']
      exact hα
    obtain ⟨l, hl, hl'⟩ := hα'
    exact e8T12Alpha0_not_twoA2 cc hcc l hl hl'.symm

end PerX


section Main

theorem e8_twelve_main (hD4 : D4TrialityLayer Tag.E8) (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T12WW) :
    (∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V)) ∧
    (∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E8 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .E8 K))))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hp7, hpq, hord12⟩ := CTE6.e6Twelve_data hp hp3 hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 - ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 2 + 1) p).2
      hpf
    simpa using this
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T12V *ᵥ u := fun u => by
    rw [hnW]
    exact e8T12_weylImage u
  have hT : twistedTorusOf n Φ = (fixedCharTuples e8T12V Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G1 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG1
  set G2 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG2
  set N : ℕ := (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G1 ⊔ G2).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8T12_card_sup Fr hFr hℓ hℓq hq2
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq2) (by norm_num)
  have hN : N ≠ 0 := pow_ne_zero 2 (by omega)
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8T12_ordProj hp hp3 hpq hord12
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  have hodd : Odd (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) := e8T12_odd _
  have hsolv : ∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    have hpg : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hpg
    have hxc : c * x * c⁻¹ ∈ subtorusImage (adjEmb .E8 K L) g0 Z0 :=
      hc x (Subgroup.mem_zpowers x)
    have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ :=
      hZ0le ((mem_subtorusImage_iff _ _ _ _).1 hxc)
    obtain ⟨ψ, hψinj, -, hψV, -⟩ := e8_twelve_perx hD4 K hf hK hp hp3 hp7 hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh
    by_contra hnodd
    have h2 : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hv2 : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))) = 2 := by
      rw [orderOf_injective ψ hψinj, Subgroup.orderOf_coe, hv]
    have hmem := hψV V hVn hVs v v.2
    rw [hT] at hmem
    obtain ⟨b', hb', hb'v⟩ := hmem
    have hdvd : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))) ∣
        Nat.card K ^ 4 - Nat.card K ^ 2 + 1 := by
      rw [← hb'v]
      exact (orderOf_map_dvd (rootDiagUnitHom .E8 L) b').trans
        (e8T12_orderOf_dvd Fr hFr hb' hq2)
    rw [hv2] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  refine ⟨hsolv, ?_⟩
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E8 K) :=
    A.comap (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let φ : A₀ →* ModGL .E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E8 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .E8 K L (c * (q : adjointGroup .E8 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc q q.2))
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ q = rootDiagUnit .E8 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  set α₀ : Fin Tag.E8.rank → ℤ := toVec Tag.E8.rank e8T12Alpha0 with hα₀def
  have hα₀ : IsRoot .E8 α₀ := isRoot_toVec e8T12Alpha0_mem.1
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => rootChar (β q) α₀
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α₀
      map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h1 : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))
        ((q : adjointGroup .E8 K) ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    have h2 : (q : adjointGroup .E8 K) ^ p = 1 := hIntinj (h1.trans (map_one _).symm)
    have h3 : q ^ p = 1 := Subtype.ext h2
    rw [h3, map_one]
  obtain ⟨q, hq1, hqχ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
  set x : adjointGroup .E8 K := (q : adjointGroup .E8 K) with hxdef
  have hx1 : x ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h1 : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) (x ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    exact hIntinj (h1.trans (map_one _).symm)
  have hx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxA : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) x ∈ A := q.2
  have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ q]
    exact hφT q
  obtain ⟨ψ, hψinj, hψ, -, hψK⟩ := e8_twelve_perx hD4 K hf hK hp hp3 hp7 hΦ L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  have hb : rootDiagUnit .E8 (β q) = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hne : α₀ ∈ rootCharKernel (β q) := ⟨hα₀, hqχ⟩
  obtain ⟨Pt, hPq, hcomm, h₀, hh₀⟩ := hψK (β q) hb hne
  have hle := e8_core_le_range_conj_of_embedding K L hp hB c g0 ψ hψinj hψ hPq hcomm
    (e8Index 3) h₀ hh₀
  refine ⟨MulAut.conj x, hxA, fun h1 => hx1 (hIntinj (by rw [h1, map_one])), ?_⟩
  have hsx := odd_card_inf_range_of_solvable (B := B) hp hC hB (hsolv x hx)
  rwa [inf_eq_left.2 hle] at hsx

end Main

section Final

theorem planeLocalCoreOdd_E8_twelve (hD4 : D4TrialityLayer Tag.E8) (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .E8 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := (ordinary_E_outer_derived_subgroup_odd .E8 (Or.inr (Or.inr rfl)) K).1
  have hcore := localCoreTrivialOn_noninner_E .E8 (Or.inr (Or.inr rfl)) K hp hp3
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 2 + 1 := by
    simpa [exhaustionPhi] using hpf
  have hcm := canonicalRep_mem_monomialSubgroup L ((coxeterSystem .E8).wordProd e8T12WW)
  have hπ : weylQuotientHom .E8 L
      ⟨canonicalRep (coxeterSystem .E8) L ((coxeterSystem .E8).wordProd e8T12WW), hcm⟩ =
        (coxeterSystem .E8).wordProd e8T12WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have h := e8_twelve_main hD4 K hf hK hp hp3 hpf' L _ hcm hπ
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore h.2

theorem oddEndpoint_E8_phi12 (hD4 : D4TrialityLayer Tag.E8) :
    OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 12 ℓ f := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E8_twelve hD4 K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end Final

end CFSG.RankThree.PartOne.KE
