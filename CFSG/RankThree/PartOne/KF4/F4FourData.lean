module

public import CFSG.RankThree.PartOne.KF4.F4FourPerX
public import CFSG.RankThree.PartOne.KF4.F4FourArith
public import CFSG.RankThree.PartOne.KF4.F4ThreeData
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE.E6FourPlane

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise


section Frame

theorem f4_four_frame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (weylMatrix f4W4) *ᵥ u) :
    ∃ g0 : ModGL .F4 L, g0 ∈ adjointGroup .F4 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL .F4 L), Finite P → P ≤ adjointGroup .F4 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .F4 K L).range) ∧
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
        (fixedCharTuples (weylMatrix f4W4) (iterateFrobenius L ℓ f)).map
          (rootDiagUnitHom .F4 L) ∧
      ∀ Q : Subgroup (adjointGroup .F4 K), IsPGroup p Q →
        ∃ c : adjointGroup .F4 K, ∀ q ∈ Q, g0⁻¹ * adjEmb .F4 K L (c * q * c⁻¹) * g0 ∈
          twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
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
  have hT : twistedTorusOf n Φ = (fixedCharTuples (weylMatrix f4W4) Fr).map
      (rootDiagUnitHom .F4 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set Z0 : Subgroup (ModGL .F4 L) := (f4FourZ Fr).map (rootDiagUnitHom .F4 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = (Nat.card K ^ 2 + 1) ^ 2 := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact f4Four_card_Z Fr hFr hℓ hℓq hq2
  have hN : (Nat.card K ^ 2 + 1) ^ 2 ≠ 0 := by positivity
  have hord : p ^ (Nat.card (adjointGroup .F4 K)).factorization p =
      p ^ ((Nat.card K ^ 2 + 1) ^ 2).factorization p := f4Four_ordProj K hp hp3 hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow_F4 K hf hK L hp hp3 n hnC Z0 hZ0le
    hN hZ0card hord
  refine ⟨g0, hg0C, hg0, hperf, hT, fun Q hQ => ?_⟩
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact ⟨c, fun q hq => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc q hq))⟩

end Frame

section HV

theorem f4_four_hV (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (weylMatrix f4W4) *ᵥ u) :
    ∀ x : adjointGroup .F4 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V →
          (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := f4_four_frame K hf hK hp hp3 hΦ L n hnm hnW
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, -, hψV, -, -⟩ := f4_four_perx K hK
    (four_le_or_eq_three_of_ne_two Fact.out hℓ2 hf) hp hp3 L n hnm hnW g0 hg0C hg0 hperf hT hx c hh
  have hψT : ∀ v : V, ∃ a ∈ fixedCharTuples (weylMatrix f4W4) (iterateFrobenius L ℓ f),
      rootDiagUnit .F4 a = ψ v := by
    intro v
    have hm := hψV V hVn hVs v v.2
    rw [hT] at hm
    obtain ⟨a, ha, hav⟩ := hm
    exact ⟨a, ha, hav⟩
  choose a ha hav using hψT
  refine ⟨fun v hv w hw => ?_, ?_⟩
  · apply hψinj
    rw [map_mul, map_mul, ← hav ⟨v, hv⟩, ← hav ⟨w, hw⟩, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      mul_comm (a ⟨v, hv⟩)]
  · obtain ⟨hfin, hcard⟩ := f4Four_two_torsion_card (L := L) (iterateFrobenius L ℓ f)
    have hsq : ∀ v : V, v ^ 2 = 1 → (a v) ^ 2 = 1 := by
      intro v hv
      apply rootDiagUnit_injective (τ := .F4) (K := L)
      have h1 : rootDiagUnit .F4 ((a v) ^ 2) = rootDiagUnit .F4 (a v) ^ 2 :=
        (map_pow (rootDiagUnitHom .F4 L) (a v) 2).symm ▸ rfl
      rw [h1, hav v, ← map_pow, rootDiagUnit_one]
      have : (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))) ^ 2 = 1 := by
        have := congrArg Subtype.val hv
        exact this
      rw [this, map_one]
    let φ : {v : V // v ^ 2 = 1} → {b : Fin Tag.F4.rank → Lˣ //
        b ∈ fixedCharTuples (weylMatrix f4W4) (iterateFrobenius L ℓ f) ∧ b ^ 2 = 1} :=
      fun v => ⟨a v.1, ha v.1, hsq v.1 v.2⟩
    have hφ : Function.Injective φ := by
      intro v w h
      have h1 : a v.1 = a w.1 := congrArg Subtype.val h
      have h2 : ψ v.1 = ψ w.1 := by rw [← hav v.1, ← hav w.1, h1]
      exact Subtype.ext (Subtype.ext (hψinj h2))
    have := hfin
    exact (Nat.card_le_card_of_injective φ hφ).trans hcard

end HV

section InnerTrivial

theorem f4_four_inner_trivial (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (weylMatrix f4W4) *ᵥ u)
    (g0 : ModGL .F4 L) (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .F4 L), Finite P → P ≤ adjointGroup .F4 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .F4 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples (weylMatrix f4W4) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .F4 L))
    (A₀ : Subgroup (adjointGroup .F4 K)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : adjointGroup .F4 K)
    (hc : ∀ q ∈ A₀, g0⁻¹ * adjEmb .F4 K L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {B : Subgroup (MulAut (adjointGroup .F4 K))}
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (w : adjointGroup .F4 K)
    (hw : ∀ q ∈ A₀, q ≠ 1 → (MulAut.conj w : MulAut (adjointGroup .F4 K)) ∈
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (adjointGroup .F4 K))} :
          Set (MulAut (adjointGroup .F4 K))))) : w = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hC : Subgroup.center (adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    conj_injective_of_center_eq_bot hC
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  let φ : A₀ →* ModGL .F4 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .F4 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * adjEmb .F4 K L (c * (q : adjointGroup .F4 K) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.F4.rank → Lˣ, φ q = rootDiagUnit .F4 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hex : ∀ i : Fin Tag.F4.rank, ∃ q : A₀, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine exists_ne_one_ker_of_card_sq' hp hA₀ χ fun q => ?_
    have h1 : rootDiagUnit .F4 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  set zw : ModGL .F4 L := g0⁻¹ * adjEmb .F4 K L (c * w * c⁻¹) * g0 with hzw
  have hzw_key : ∀ i : Fin Tag.F4.rank, ∃ a : Fin Tag.F4.rank → Lˣ,
      zw = rootDiagUnit .F4 a ∧ a i = 1 := by
    intro i
    obtain ⟨q, hq1, hqi⟩ := hex i
    have hqA : (q : adjointGroup .F4 K) ∈ A₀ := q.2
    have hq1' : (q : adjointGroup .F4 K) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hqp : orderOf (q : adjointGroup .F4 K) = p :=
      orderOf_eq_prime (hA₀exp _ hqA) hq1'
    obtain ⟨ψ, hψinj, hψ, -, -, hψS⟩ := f4_four_perx K hK
      (four_le_or_eq_three_of_ne_two Fact.out hℓ2 hf) hp hp3 L n hnm hnW g0 hg0C hg0 hperf hT hqp c
      (hc _ hqA)
    have hb : rootDiagUnit .F4 (β q) = g0⁻¹ * adjEmb .F4 K L
        (c * (q : adjointGroup .F4 K) * c⁻¹) * g0 := by
      rw [← hβ, hφ]
    have hψV := hψS (β q) hb
    obtain ⟨V, hVn, hVs, hVl⟩ := inner_core_preimage hp hC hB (q : adjointGroup .F4 K)
    obtain ⟨v, hvV, hvw⟩ := hVl (MulAut.conj w) (Subgroup.mem_inf.2
      ⟨hw _ hqA hq1', ⟨w, rfl⟩⟩)
    have hvw' : (v : adjointGroup .F4 K) = w := hIntinj hvw
    have hmem := hψV V hVn hVs v hvV
    rw [hψ v, hvw'] at hmem
    obtain ⟨hmemT, hmemC⟩ := Subgroup.mem_inf.1 hmem
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hmemT).1
    refine ⟨a, ha, ?_⟩
    have hα : (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ rootCharKernel (β q) := by
      refine ⟨IsRoot.basis i, ?_⟩
      rw [CTTorus.rootChar_single]
      exact hqi
    have hXmem : pinnedX .F4 L (Pi.single i 1) 1 ∈ rootSpan .F4 L (rootCharKernel (β q)) :=
      pinnedX_mem_rootSpan hα 1
    have hcomm := Subgroup.mem_centralizer_iff.1 hmemC _ hXmem
    rw [ha] at hcomm
    have hconj := rootDiagUnit_conj_pinnedX a (IsRoot.basis i) (1 : L)
    have hX : rootDiagUnit .F4 a * pinnedX .F4 L (Pi.single i 1) 1 * (rootDiagUnit .F4 a)⁻¹ =
        pinnedX .F4 L (Pi.single i 1) 1 := by
      rw [← hcomm]
      group
    have h3 : pinnedX .F4 L (Pi.single i 1) (((rootChar a (Pi.single i 1) : Lˣ) : L) * 1) =
        pinnedX .F4 L (Pi.single i 1) 1 := hconj.symm.trans hX
    have h4 := pinnedX_injective (τ := Tag.F4) (R := L) (Pi.single i 1) h3
    have h5 : rootChar a (Pi.single i 1) = 1 := Units.ext (by simpa using h4)
    rwa [CTTorus.rootChar_single] at h5
  obtain ⟨a0, ha0, -⟩ := hzw_key ⟨0, by decide⟩
  have ha0one : a0 = 1 := by
    funext j
    obtain ⟨aj, haj, hajj⟩ := hzw_key j
    have : aj = a0 := rootDiagUnit_injective (τ := .F4) (K := L) (haj.symm.trans ha0)
    rw [← this]
    exact hajj
  have hz1 : zw = 1 := by rw [ha0, ha0one, rootDiagUnit_one]
  have hw1 : adjEmb .F4 K L (c * w * c⁻¹) = adjEmb .F4 K L 1 := by
    rw [map_one]
    have : g0⁻¹ * adjEmb .F4 K L (c * w * c⁻¹) * g0 = 1 := hz1
    calc adjEmb .F4 K L (c * w * c⁻¹)
        = g0 * (g0⁻¹ * adjEmb .F4 K L (c * w * c⁻¹) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [this]; group
  have := adjEmb_injective hw1
  calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
    _ = 1 := by rw [this]; group


theorem f4_four_exists_nonregular (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} (hp : p.Prime)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (g0 : ModGL .F4 L)
    (A₀ : Subgroup (adjointGroup .F4 K)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : adjointGroup .F4 K)
    (hc : ∀ q ∈ A₀, g0⁻¹ * adjEmb .F4 K L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) (i : Fin Tag.F4.rank) :
    ∃ q ∈ A₀, q ≠ 1 ∧ ∃ b : Fin Tag.F4.rank → Lˣ,
      rootDiagUnit .F4 b = g0⁻¹ * adjEmb .F4 K L (c * q * c⁻¹) * g0 ∧
        (rootCharKernel b).Nonempty := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hA₀fin : Finite A₀ := Finite.of_injective _ A₀.subtype_injective
  let φ : A₀ →* ModGL .F4 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .F4 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * adjEmb .F4 K L (c * (q : adjointGroup .F4 K) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
    fun q => by
      rw [hφ]
      exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.F4.rank → Lˣ, φ q = rootDiagUnit .F4 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => β q i
      map_one' := by rw [hβone]; rfl
      map_mul' := fun q q' => by rw [hβmul]; rfl }
  obtain ⟨q, hq1, hqi⟩ := exists_ne_one_ker_of_card_sq' hp hA₀ χ fun q => by
    have h1 : rootDiagUnit .F4 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  refine ⟨q, q.2, fun h => hq1 (Subtype.ext h), β q, by rw [← hβ, hφ], ⟨Pi.single i 1, ?_⟩⟩
  refine ⟨IsRoot.basis i, ?_⟩
  rw [CTTorus.rootChar_single]
  exact hqi



end InnerTrivial

section Plane

theorem f4_four_hI (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (weylMatrix f4W4) *ᵥ u) :
    ∀ B : Subgroup (MulAut (adjointGroup .F4 K)),
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .F4 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
          Odd (Nat.card ↥(autThetaT p B A)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := f4_four_frame K hf hK hp hp3 hΦ L n hnm hnW
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
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    have h1 : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) (q ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ hq
    exact hIntinj (h1.trans (map_one _).symm)
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  set I : Subgroup (MulAut (adjointGroup .F4 K)) := autThetaT p B A with hI
  have hIle : ∀ q ∈ A₀, q ≠ 1 → I ≤ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (adjointGroup .F4 K))} :
        Set (MulAut (adjointGroup .F4 K)))) := by
    intro q hq hq1
    have hqA : (MulAut.conj q : MulAut (adjointGroup .F4 K)) ∈ A := by
      have : (MulAut.conj q : MulAut (adjointGroup .F4 K)) ∈ A₀.map
          (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) := ⟨q, hq, rfl⟩
      rwa [hA₀map] at this
    have hq1' : (MulAut.conj q : MulAut (adjointGroup .F4 K)) ≠ 1 := fun h =>
      hq1 (hIntinj (h.trans (map_one _).symm))
    exact iInf₂_le_of_le _ hqA (iInf_le_of_le hq1' le_rfl)
  have hinner : ∀ s ∈ I, s ∈ (MulAut.conj : adjointGroup .F4 K →*
      MulAut (adjointGroup .F4 K)).range → s = 1 := by
    rintro s hs ⟨w, rfl⟩
    have hw : w = 1 := f4_four_inner_trivial K hf hK hℓ2 hp hp3 L n hnm hnW g0 hg0C hg0 hperf
      hT A₀ hA₀card hA₀exp c hc hB w fun q hq hq1 => hIle q hq hq1 hs
    rw [hw, map_one]
  obtain ⟨x, hxA, hx1, b, hb, hne⟩ := f4_four_exists_nonregular K hp L n g0 A₀ hA₀card hA₀exp c hc
    (f4Index 1)
  have hxp : orderOf x = p := orderOf_eq_prime (hA₀exp x hxA) hx1
  obtain ⟨ψ, hψinj, hψ, -, hψK, -⟩ := f4_four_perx K hK
    (four_le_or_eq_three_of_ne_two Fact.out hℓ2 hf) hp hp3 L n hnm hnW g0 hg0C hg0 hperf hT hxp c
    (hc x hxA)
  obtain ⟨Pt, hPq, hcomm, i, hi, h₀, -, hh₀⟩ := hψK b hb hne
  have hℓ : ℓ.Prime := Fact.out
  have hle := f4_core_le_range_conj_of_embedding K hℓ hℓ2 hf hK L hp hB c g0 ψ hψinj hψ hPq
    hcomm i hi h₀ hh₀
  have hIbot : I = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    have hs' := hle (hIle x hxA hx1 hs)
    rw [hinner s hs hs']
    exact one_mem _
  rw [hIbot, Subgroup.card_bot]
  exact odd_one

end Plane

section Final


theorem planeLocalCoreOdd_F4_four (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ)) :
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
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by simpa [exhaustionPhi] using hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpq
    simpa using this
  have hcm := canonicalRep_mem_monomialSubgroup L f4W4
  have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W4, hcm⟩ = f4W4 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep f4W4)
  have hnW : ∀ u, weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W4, hcm⟩ • u =
      (weylMatrix f4W4) *ᵥ u := fun u => by
    rw [hπ, weylMatrix_mulVec]
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot
    (f4_four_hV K hf hK hℓ2 hp hp3 hΦ L _ hcm hnW) hout hcore
    (f4_four_hI K hf hK hℓ2 hp hp3 hΦ L _ hcm hnW)

theorem oddEndpoint_F4_oddPhi4 :
    OddEndpoint .F4 fun p ℓ f => ℓ ≠ 2 ∧ (p : ℤ) ∣ cycloVal 4 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_four K hℓ hc.1 hf hK hp hp3
      (by simpa [cycloVal, hK] using hc.2))).1

end Final

end CFSG.RankThree.PartOne.KF4
