module

public import CFSG.RankThree.PartOne.KE.E8EightPerX
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E8EightArith
public import CFSG.RankThree.PartOne.KE.E8EightBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Pointwise MatrixGroups

section Frame

theorem e8_eight_frame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T8WW) :
    ∃ g0 : ModGL .E8 L, g0 ∈ adjointGroup .E8 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .E8 K L).range) ∧
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
        (fixedCharTuples e8T8V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L) ∧
      ∀ A : Subgroup (adjointGroup .E8 K), IsPGroup p A → ∃ c : adjointGroup .E8 K, ∀ x ∈ A,
        g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
          twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hp7, hpq, hord8⟩ := CTE6.e6Eight_data hp hp3 hpf
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
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T8V *ᵥ u := fun u => by
    rw [hnW]
    exact e8T8_weylImage u
  have hT : twistedTorusOf n Φ = (fixedCharTuples e8T8V Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G1 := fixedBlockTuples e8T8V Fr
    (e8T8Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG1
  set G2 := fixedBlockTuples e8T8V Fr
    (e8T8Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG2
  set N : ℕ := (Nat.card K ^ 4 + 1) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G1 ⊔ G2).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8T8_card_sup Fr hFr hℓ hℓq
  have hN : N ≠ 0 := pow_ne_zero 2 (by positivity)
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8T8_ordProj hp hp3 hpq hord8
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨g0, hg0C, hg0, hperf, hT, fun A hA => ?_⟩
  obtain ⟨c, hc⟩ := hconj A hA
  exact ⟨c, fun x hx => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x hx))⟩

end Frame

section Solvable

theorem e8_eight_abelian_two_torsion {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {V : Type*} [Group V] (ψ : V →* ModGL .E8 L)
    (hψ : Function.Injective ψ)
    (hV : ∀ v : V, ψ v ∈ (fixedCharTuples e8T8V Fr).map (rootDiagUnitHom .E8 L)) :
    (∀ v w : V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  choose a ha hav using fun v : V => hV v
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hmul : ∀ v w : V, a (v * w) = a v * a w := fun v w => by
    apply hinj0
    rw [hav, map_mul, map_mul, hav, hav]
  refine ⟨fun v w => ?_, ?_⟩
  · apply hψ
    rw [map_mul, map_mul, ← hav v, ← hav w, ← map_mul, ← map_mul, mul_comm]
  · set Γ : Subgroup (Fin Tag.E8.rank → Lˣ) :=
      (fixedCharTuples e8T8V Fr) ⊓ ψ.range.comap (rootDiagUnitHom .E8 L) with hΓ
    have hΓle : Γ ≤ fixedCharTuples e8T8V Fr := inf_le_left
    let φ : {v : V // v ^ 2 = 1} → {g : Γ // g ^ 2 = 1} := fun v =>
      ⟨⟨a v.1, Subgroup.mem_inf.2 ⟨ha v.1, ⟨v.1, (hav v.1).symm⟩⟩⟩, by
        apply Subtype.ext
        apply hinj0
        change rootDiagUnitHom .E8 L (a v.1 ^ 2) = rootDiagUnitHom .E8 L 1
        rw [map_pow, hav, ← map_pow, v.2, map_one, map_one]⟩
    have hφ : Function.Injective φ := fun v w h => by
      apply Subtype.ext
      apply hψ
      rw [← hav v.1, ← hav w.1]
      have := congrArg (fun g : {g : Γ // g ^ 2 = 1} => ((g.1 : Γ) : Fin Tag.E8.rank → Lˣ)) h
      simp only [φ] at this
      rw [this]
    obtain ⟨hfin, hcard⟩ := e8T8_card_two_torsion_le_four Fr hFr hΓle
    exact (Nat.card_le_card_of_injective φ hφ).trans hcard

theorem e8_eight_solvable (hD4 : D4TranspositionLayer Tag.E8) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T8WW) :
    ∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp7, hpq, hord8⟩ := CTE6.e6Eight_data hp hp3 hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + 1) p).2 hpf
    simpa using this
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e8_eight_frame K hf hK hp hp3 hpf L n hnm hnW
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, -, hψb⟩ := e8_eight_perx hD4 K hf hK hp hp3 hp7 hΦ L n hnm hnW g0 hg0C hg0
    hperf hT hx c hh
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
  obtain ⟨hψV, -⟩ := hψb b hb.symm
  have hVT : ∀ v : V, ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) ∈
      (fixedCharTuples e8T8V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L) := fun v => by
    rw [← hT]
    exact subtorusSigma_le_twistedTorusOf _ _ _ (hψV V hVn hVs v v.2)
  obtain ⟨hab, h2⟩ := e8_eight_abelian_two_torsion (iterateFrobenius L ℓ f) hFr
    (ψ.comp V.subtype) (hψinj.comp V.subtype_injective) hVT
  refine ⟨fun v hv w hw => ?_, h2⟩
  have := hab ⟨v, hv⟩ ⟨w, hw⟩
  exact congrArg Subtype.val this

end Solvable

section InnerTrivial

theorem e8_eight_inner_trivial (hD4 : D4TranspositionLayer Tag.E8) (K : Type) [Field K]
    [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T8WW)
    (g0 : ModGL .E8 L) (hg0C : g0 ∈ adjointGroup .E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e8T8V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L))
    (A₀ : Subgroup (adjointGroup .E8 K)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : adjointGroup .E8 K)
    (hc : ∀ q ∈ A₀, g0⁻¹ * adjEmb .E8 K L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B)
    (w : adjointGroup .E8 K)
    (hw : ∀ q ∈ A₀, q ≠ 1 → (MulAut.conj w : MulAut (adjointGroup .E8 K)) ∈
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (adjointGroup .E8 K))} :
          Set (MulAut (adjointGroup .E8 K))))) : w = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hp7, hpq, hord8⟩ := CTE6.e6Eight_data hp hp3 hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + 1) p).2 hpf
    simpa using this
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hC : Subgroup.center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) :=
    conj_injective_of_center_eq_bot hC
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  let φ : A₀ →* ModGL .E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E8 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .E8 K L (c * (q : adjointGroup .E8 K) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ q = rootDiagUnit .E8 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hex : ∀ i : Fin Tag.E8.rank, ∃ q : A₀, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => ?_
    have h1 : rootDiagUnit .E8 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  set zw : ModGL .E8 L := g0⁻¹ * adjEmb .E8 K L (c * w * c⁻¹) * g0 with hzw
  have hzw_key : ∀ i : Fin Tag.E8.rank, ∃ a : Fin Tag.E8.rank → Lˣ,
      zw = rootDiagUnit .E8 a ∧ a i = 1 := by
    intro i
    obtain ⟨q, hq1, hqi⟩ := hex i
    have hqA : (q : adjointGroup .E8 K) ∈ A₀ := q.2
    have hq1' : (q : adjointGroup .E8 K) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hqp : orderOf (q : adjointGroup .E8 K) = p :=
      orderOf_eq_prime (hA₀exp _ hqA) hq1'
    obtain ⟨ψ, hψinj, hψ, hψb⟩ := e8_eight_perx hD4 K hf hK hp hp3 hp7 hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT hqp c (hc _ hqA)
    have hb : rootDiagUnit .E8 (β q) = g0⁻¹ * adjEmb .E8 K L
        (c * (q : adjointGroup .E8 K) * c⁻¹) * g0 := by
      rw [← hβ, hφ]
    obtain ⟨hψV, -⟩ := hψb (β q) hb
    obtain ⟨V, hVn, hVs, hVl⟩ := inner_core_preimage hp hC hB (q : adjointGroup .E8 K)
    obtain ⟨v, hvV, hvw⟩ := hVl (MulAut.conj w) (Subgroup.mem_inf.2
      ⟨hw _ hqA hq1', ⟨w, rfl⟩⟩)
    have hvw' : (v : adjointGroup .E8 K) = w := hIntinj hvw
    have hmem := hψV V hVn hVs v hvV
    rw [hψ v, hvw'] at hmem
    obtain ⟨hmemT, hmemC⟩ := Subgroup.mem_inf.1 hmem
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hmemT).1
    refine ⟨a, ha, ?_⟩
    have hα : (Pi.single i 1 : Fin Tag.E8.rank → ℤ) ∈ rootCharKernel (β q) := by
      refine ⟨IsRoot.basis i, ?_⟩
      rw [CTTorus.rootChar_single]
      exact hqi
    have hXmem : pinnedX .E8 L (Pi.single i 1) 1 ∈ rootSpan .E8 L (rootCharKernel (β q)) :=
      pinnedX_mem_rootSpan hα 1
    have hcomm := Subgroup.mem_centralizer_iff.1 hmemC _ hXmem
    rw [ha] at hcomm
    have hconj := rootDiagUnit_conj_pinnedX a (IsRoot.basis i) (1 : L)
    have hX : rootDiagUnit .E8 a * pinnedX .E8 L (Pi.single i 1) 1 *
        (rootDiagUnit .E8 a)⁻¹ = pinnedX .E8 L (Pi.single i 1) 1 := by
      rw [← hcomm]
      group
    have h3 : pinnedX .E8 L (Pi.single i 1) (((rootChar a (Pi.single i 1) : Lˣ) : L) * 1) =
        pinnedX .E8 L (Pi.single i 1) 1 := hconj.symm.trans hX
    have h4 := pinnedX_injective (τ := .E8) (R := L) (Pi.single i 1) h3
    have h5 : rootChar a (Pi.single i 1) = 1 := Units.ext (by simpa using h4)
    rwa [CTTorus.rootChar_single] at h5
  obtain ⟨a0, ha0, -⟩ := hzw_key ⟨0, by decide⟩
  have ha0one : a0 = 1 := by
    funext j
    obtain ⟨aj, haj, hajj⟩ := hzw_key j
    have : aj = a0 := rootDiagUnit_injective (τ := .E8) (K := L) (haj.symm.trans ha0)
    rw [← this]
    exact hajj
  have hz1 : zw = 1 := by rw [ha0, ha0one, rootDiagUnit_one]
  have hw1 : adjEmb .E8 K L (c * w * c⁻¹) = adjEmb .E8 K L 1 := by
    rw [map_one]
    have : g0⁻¹ * adjEmb .E8 K L (c * w * c⁻¹) * g0 = 1 := hz1
    calc adjEmb .E8 K L (c * w * c⁻¹)
        = g0 * (g0⁻¹ * adjEmb .E8 K L (c * w * c⁻¹) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [this]; group
  have := adjEmb_injective hw1
  calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
    _ = 1 := by rw [this]; group

end InnerTrivial

section Plane

theorem e8_eight_hI (hD4 : D4TranspositionLayer Tag.E8) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T8WW) :
    ∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E8 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
        Odd (Nat.card ↥(autThetaT p B A)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hp7, hpq, hord8⟩ := CTE6.e6Eight_data hp hp3 hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + 1) p).2 hpf
    simpa using this
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e8_eight_frame K hf hK hp hp3 hpf L n hnm hnW
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom (iterateFrobenius L ℓ f))
    with hΦdef
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
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hIntinj
    rw [map_pow, map_one]
    exact hpow _ hq
  let φ : A₀ →* ModGL .E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E8 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .E8 K L (c * (q : adjointGroup .E8 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ q = rootDiagUnit .E8 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  set α₀ : Fin Tag.E8.rank → ℤ := toVec Tag.E8.rank e8T8Alpha0 with hα₀def
  have hα₀ : IsRoot .E8 α₀ := isRoot_toVec e8T8Alpha0_mem.1
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => rootChar (β q) α₀
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α₀
      map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
  have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h3 : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
    rw [h3, map_one]
  obtain ⟨q₀, hq₀1, hq₀χ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
  set x₀ : adjointGroup .E8 K := (q₀ : adjointGroup .E8 K) with hx₀def
  have hx₀1 : x₀ ≠ 1 := fun h => hq₀1 (Subtype.ext h)
  have hx₀ : orderOf x₀ = p := orderOf_eq_prime (hA₀exp _ q₀.2) hx₀1
  have hh₀ : g0⁻¹ * adjEmb .E8 K L (c * x₀ * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ q₀]
    exact hφT q₀
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e8_eight_perx hD4 K hf hK hp hp3 hp7 hΦ L n hnm hnW g0 hg0C hg0
    hperf hT hx₀ c hh₀
  have hb₀ : rootDiagUnit .E8 (β q₀) = g0⁻¹ * adjEmb .E8 K L (c * x₀ * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hne : α₀ ∈ rootCharKernel (β q₀) := ⟨hα₀, hq₀χ⟩
  obtain ⟨Pt, hPq, hcomm, h₀, hh₀'⟩ := (hψb (β q₀) hb₀).2 hne
  have hle := e8_core_le_range_conj_of_embedding K L hp hB c g0 ψ hψinj hψ hPq hcomm
    (e8Index 3) h₀ hh₀'
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → autThetaT p B A ≤
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .E8 K)))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  have hne1 : ∀ q ∈ A₀, q ≠ 1 → (MulAut.conj q : MulAut (adjointGroup .E8 K)) ≠ 1 :=
    fun q _ hq1 h => hq1 (hIntinj (h.trans (map_one _).symm))
  have hbot : autThetaT p B A = ⊥ := by
    rw [eq_bot_iff]
    intro η hη
    have hη₀ := hthetaT_le (MulAut.conj x₀) q₀.2 (hne1 _ q₀.2 hx₀1) hη
    obtain ⟨w, rfl⟩ := hle hη₀
    have hw1 : w = 1 := e8_eight_inner_trivial hD4 K hf hK hp hp3 hpf L n hnm hnW g0 hg0C hg0
      hperf hT A₀ hA₀card hA₀exp c hc hB w fun q hqA hq1 =>
        hthetaT_le (MulAut.conj q) hqA (hne1 q hqA hq1) hη
    rw [hw1, map_one]
    exact Subgroup.one_mem _
  rw [hbot, Subgroup.card_bot]
  exact odd_one

end Plane

section Final

theorem planeLocalCoreOdd_E8_eight (hD4 : D4TranspositionLayer Tag.E8) (K : Type) [Field K]
    [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K : ℤ)) :
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
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1 := by
    simpa [exhaustionPhi] using hpf
  have hcm := canonicalRep_mem_monomialSubgroup L ((coxeterSystem .E8).wordProd e8T8WW)
  have hπ : weylQuotientHom .E8 L
      ⟨canonicalRep (coxeterSystem .E8) L ((coxeterSystem .E8).wordProd e8T8WW), hcm⟩ =
        (coxeterSystem .E8).wordProd e8T8WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot
    (e8_eight_solvable hD4 K hf hK hp hp3 hpf' L _ hcm hπ) hout hcore
    (e8_eight_hI hD4 K hf hK hp hp3 hpf' L _ hcm hπ)

theorem oddEndpoint_E8_phi8 (hD4 : D4TranspositionLayer Tag.E8) :
    OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E8_eight hD4 K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end Final

end CFSG.RankThree.PartOne.KE
