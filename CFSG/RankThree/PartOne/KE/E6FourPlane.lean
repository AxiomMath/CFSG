module

public import CFSG.RankThree.PartOne.KE.E6FourCore
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix e6Index)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section InnerPreimage

theorem inner_core_preimage {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C) :
    ∃ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal ∧ Group.IsSolvable V ∧
      ∀ q ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range,
      ∃ v ∈ V, MulAut.conj (v : C) = q := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set Int : C →* MulAut C := MulAut.conj with hInt
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup C, D = Subgroup.centralizer ({x} : Set C) := ⟨_, rfl⟩
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSsol : Group.IsSolvable S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).1
    rw [hS, inSubgroup]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p M) M.subtype
        M.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    rw [hD] at hd
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  have hYSD : S.comap Int ≤ D := by
    intro y hy
    have hyM : Int y ∈ M := hSM hy
    rw [hM] at hyM
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyM).2 (Int x) rfl
    rw [hD]
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hinj (by rw [map_mul, map_mul]; exact h1.symm))
  have hVnormal : ((S.comap Int).subgroupOf D).Normal := ⟨fun v hv d => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    change Int ((d : C) * (v : C) * (d : C)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSnorm _ (hIntD d d.2) _ hv⟩
  have hVsol : Group.IsSolvable ((S.comap Int).subgroupOf D) := by
    let f : ((S.comap Int).subgroupOf D) →* S :=
      ((Int.comp D.subtype).comp ((S.comap Int).subgroupOf D).subtype).codRestrict S
        fun v => Subgroup.mem_subgroupOf.1 v.2
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (hinj (congrArg Subtype.val hab)))
  subst hD
  refine ⟨(S.comap Int).subgroupOf (Subgroup.centralizer ({x} : Set C)), hVnormal, hVsol, ?_⟩
  intro q hq
  obtain ⟨hqS, y, hy⟩ := Subgroup.mem_inf.1 hq
  have hyS : y ∈ S.comap Int := by
    rw [Subgroup.mem_comap, hy]
    exact hqS
  exact ⟨⟨y, hYSD hyS⟩, Subgroup.mem_subgroupOf.2 hyS, hy⟩

end InnerPreimage

section InnerTrivial

theorem e6_four_inner_trivial (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (g0 : ModGL .E6 L) (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L))
    (A₀ : Subgroup (adjointGroup .E6 K)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : adjointGroup .E6 K)
    (hc : ∀ q ∈ A₀, g0⁻¹ * adjEmb .E6 K L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {B : Subgroup (MulAut (adjointGroup .E6 K))}
    (hB : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ B)
    (w : adjointGroup .E6 K)
    (hw : ∀ q ∈ A₀, q ≠ 1 → (MulAut.conj w : MulAut (adjointGroup .E6 K)) ∈
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (adjointGroup .E6 K))} :
          Set (MulAut (adjointGroup .E6 K))))) : w = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr) with hΦdef
  have hC : Subgroup.center (adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) :=
    conj_injective_of_center_eq_bot hC
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  let φ : A₀ →* ModGL .E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E6 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * adjEmb .E6 K L (c * (q : adjointGroup .E6 K) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit .E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hex : ∀ i : Fin Tag.E6.rank, ∃ q : A₀, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => ?_
    have h1 : rootDiagUnit .E6 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  set zw : ModGL .E6 L := g0⁻¹ * adjEmb .E6 K L (c * w * c⁻¹) * g0 with hzw
  have hzw_key : ∀ i : Fin Tag.E6.rank, ∃ a : Fin Tag.E6.rank → Lˣ,
      zw = rootDiagUnit .E6 a ∧ a i = 1 := by
    intro i
    obtain ⟨q, hq1, hqi⟩ := hex i
    have hqA : (q : adjointGroup .E6 K) ∈ A₀ := q.2
    have hq1' : (q : adjointGroup .E6 K) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hqp : orderOf (q : adjointGroup .E6 K) = p :=
      orderOf_eq_prime (hA₀exp _ hqA) hq1'
    obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_four_perx K hf hK hp hp3 hord hΦ L n hnm hnW g0 hg0C hg0
      hperf hT hqp c (hc _ hqA)
    have hb : rootDiagUnit .E6 (β q) = g0⁻¹ * adjEmb .E6 K L
        (c * (q : adjointGroup .E6 K) * c⁻¹) * g0 := by
      rw [← hβ, hφ]
    obtain ⟨hψV, -⟩ := hψb (β q) hb
    obtain ⟨V, hVn, hVs, hVl⟩ := inner_core_preimage hp hC hB (q : adjointGroup .E6 K)
    obtain ⟨v, hvV, hvw⟩ := hVl (MulAut.conj w) (Subgroup.mem_inf.2
      ⟨hw _ hqA hq1', ⟨w, rfl⟩⟩)
    have hvw' : (v : adjointGroup .E6 K) = w := hIntinj hvw
    have hmem := hψV V hVn hVs v hvV
    rw [hψ v, hvw'] at hmem
    obtain ⟨hmemT, hmemC⟩ := Subgroup.mem_inf.1 hmem
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hmemT).1
    refine ⟨a, ha, ?_⟩
    have hα : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel (β q) := by
      refine ⟨IsRoot.basis i, ?_⟩
      rw [CTTorus.rootChar_single]
      exact hqi
    have hXmem : pinnedX .E6 L (Pi.single i 1) 1 ∈ rootSpan .E6 L (rootCharKernel (β q)) :=
      pinnedX_mem_rootSpan hα 1
    have hcomm := Subgroup.mem_centralizer_iff.1 hmemC _ hXmem
    rw [ha] at hcomm
    have hconj := rootDiagUnit_conj_pinnedX a (IsRoot.basis i) (1 : L)
    have hX : rootDiagUnit .E6 a * pinnedX .E6 L (Pi.single i 1) 1 * (rootDiagUnit .E6 a)⁻¹ =
        pinnedX .E6 L (Pi.single i 1) 1 := by
      rw [← hcomm]
      group
    have h3 : pinnedX .E6 L (Pi.single i 1) (((rootChar a (Pi.single i 1) : Lˣ) : L) * 1) =
        pinnedX .E6 L (Pi.single i 1) 1 := hconj.symm.trans hX
    have h4 := pinnedX_injective (τ := Tag.E6) (R := L) (Pi.single i 1) h3
    have h5 : rootChar a (Pi.single i 1) = 1 := Units.ext (by simpa using h4)
    rwa [CTTorus.rootChar_single] at h5
  obtain ⟨a0, ha0, -⟩ := hzw_key ⟨0, by decide⟩
  have ha0one : a0 = 1 := by
    funext j
    obtain ⟨aj, haj, hajj⟩ := hzw_key j
    have : aj = a0 := rootDiagUnit_injective (τ := .E6) (K := L) (haj.symm.trans ha0)
    rw [← this]
    exact hajj
  have hz1 : zw = 1 := by rw [ha0, ha0one, rootDiagUnit_one]
  have hw1 : adjEmb .E6 K L (c * w * c⁻¹) = adjEmb .E6 K L 1 := by
    rw [map_one]
    have : g0⁻¹ * adjEmb .E6 K L (c * w * c⁻¹) * g0 = 1 := hz1
    calc adjEmb .E6 K L (c * w * c⁻¹)
        = g0 * (g0⁻¹ * adjEmb .E6 K L (c * w * c⁻¹) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [this]; group
  have := adjEmb_injective hw1
  calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
    _ = 1 := by rw [this]; group

end InnerTrivial

section Nonregular

theorem e6_four_exists_nonregular (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} (hp : p.Prime)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (g0 : ModGL .E6 L)
    (A₀ : Subgroup (adjointGroup .E6 K)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : adjointGroup .E6 K)
    (hc : ∀ q ∈ A₀, g0⁻¹ * adjEmb .E6 K L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) (i : Fin Tag.E6.rank) :
    ∃ q ∈ A₀, q ≠ 1 ∧ ∃ b : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * q * c⁻¹) * g0 ∧
        (rootCharKernel b).Nonempty := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hA₀fin : Finite A₀ := Finite.of_injective _ A₀.subtype_injective
  let φ : A₀ →* ModGL .E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E6 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * adjEmb .E6 K L (c * (q : adjointGroup .E6 K) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
    fun q => by
      rw [hφ]
      exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit .E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => β q i
      map_one' := by rw [hβone]; rfl
      map_mul' := fun q q' => by rw [hβmul]; rfl }
  obtain ⟨q, hq1, hqi⟩ := exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => by
    have h1 : rootDiagUnit .E6 (β q) ^ p = 1 := by
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

end Nonregular

section CardDvd

theorem e6_four_card_dvd (K : Type) [Field K] [Finite K]
    (I : Subgroup (MulAut (adjointGroup .E6 K)))
    (hinner : ∀ s ∈ I, s ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range
      → s = 1)
    (hdiag : ∀ s ∈ I, ∃ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ),
      s = MulAut.conj g * rootDiagAut .E6 K a) :
    Nat.card I ∣ 3 := by
  classical
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (τ := .E6) (K := K) (Or.inl rfl)
  set π : MulAut (adjointGroup .E6 K) →* Outer (adjointGroup .E6 K) :=
    QuotientGroup.mk' (inner (adjointGroup .E6 K)) with hπ
  let f : I →* Outer (adjointGroup .E6 K) := π.comp I.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : π (s : MulAut (adjointGroup .E6 K)) = 1 := hs
    have h2 : (s : MulAut (adjointGroup .E6 K)) ∈ inner (adjointGroup .E6 K) :=
      (QuotientGroup.eq_one_iff (N := inner (adjointGroup .E6 K)) _).1 h1
    exact Subtype.ext (hinner s s.2 h2)
  have hrange : f.range ≤ Φ.ker := by
    rintro _ ⟨s, rfl⟩
    rw [hker]
    obtain ⟨g, a, hga⟩ := hdiag s s.2
    refine ⟨a, ?_⟩
    change π (rootDiagAutHom .E6 K a) = π (s : MulAut (adjointGroup .E6 K))
    rw [hga, map_mul]
    have : π (MulAut.conj g : MulAut (adjointGroup .E6 K)) = 1 :=
      (QuotientGroup.eq_one_iff (N := inner (adjointGroup .E6 K)) _).2 ⟨g, rfl⟩
    rw [this, one_mul]
    rfl
  have hcard : Nat.card I = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
  rw [hcard]
  refine (Subgroup.card_dvd_of_le hrange).trans (hdvd.trans ?_)
  rw [det_cartan_E6]
  norm_num

end CardDvd

section Plane

theorem e6_four_hI (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u) :
    ∀ B : Subgroup (MulAut (adjointGroup .E6 K)),
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E6 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range →
          Odd (Nat.card ↥(autThetaT p B A)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_four_frame K hf hK hp hp3 hpq L n hnm hnW
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E6 K) :=
    A.comap (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    have h1 : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) (q ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ hq
    exact hIntinj (h1.trans (map_one _).symm)
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  set I : Subgroup (MulAut (adjointGroup .E6 K)) := autThetaT p B A with hI
  have hIle : ∀ q ∈ A₀, q ≠ 1 → I ≤ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (adjointGroup .E6 K))} :
        Set (MulAut (adjointGroup .E6 K)))) := by
    intro q hq hq1
    have hqA : (MulAut.conj q : MulAut (adjointGroup .E6 K)) ∈ A := by
      have : (MulAut.conj q : MulAut (adjointGroup .E6 K)) ∈ A₀.map
          (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) := ⟨q, hq, rfl⟩
      rwa [hA₀map] at this
    have hq1' : (MulAut.conj q : MulAut (adjointGroup .E6 K)) ≠ 1 := fun h =>
      hq1 (hIntinj (h.trans (map_one _).symm))
    exact iInf₂_le_of_le _ hqA (iInf_le_of_le hq1' le_rfl)
  have hinner : ∀ s ∈ I, s ∈ (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)).range → s = 1 := by
    rintro s hs ⟨w, rfl⟩
    have hw : w = 1 := e6_four_inner_trivial K hf hK hp hp3 hordq hΦ L n hnm hnW g0 hg0C hg0 hperf
      hT A₀ hA₀card hA₀exp c hc hB w fun q hq hq1 => hIle q hq hq1 hs
    rw [hw, map_one]
  obtain ⟨x, hxA, hx1, b, hb, hne⟩ := e6_four_exists_nonregular K hp L n g0 A₀ hA₀card hA₀exp c hc
    ⟨0, by decide⟩
  have hxp : orderOf x = p := orderOf_eq_prime (hA₀exp x hxA) hx1
  have hdiag : ∀ s ∈ I, ∃ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ),
      s = MulAut.conj g * rootDiagAut .E6 K a := by
    intro s hs
    obtain ⟨g, a, σ, ε, hsE⟩ := exists_conj_mul_exactNormalAut (τ := .E6) (K := K) (Or.inl rfl) s
    have hexpr : ∀ y : adjointGroup .E6 K, (s y : ModGL .E6 K) = (g : ModGL .E6 K) *
        rootDiagUnit .E6 a * exactQ .E6 K ε * Units.map (entrywiseHom σ.toRingHom)
          (y : ModGL .E6 K) * (exactQ .E6 K ε)⁻¹ * (rootDiagUnit .E6 a)⁻¹ *
            (g : ModGL .E6 K)⁻¹ := by
      intro y
      rw [hsE, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_exactNormalAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    obtain ⟨hσ, hε⟩ := e6_four_core_normal_form K hf hK hp hp3 hordq hΦ L n hnm hnW g0 hg0C hg0
      hperf hT hxp c (hc x hxA) hb hne hB (hIle x hxA hx1 hs) g a σ ε hexpr
    refine ⟨g, a, ?_⟩
    rw [hsE]
    congr 1
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [coe_exactNormalAut, coe_rootDiagAut, hσ, hε]
    have hid : ∀ y : ModGL .E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) y = y :=
      fun y => Units.ext (entrywise_id _)
    rw [hid]
    have hQ0 : exactQ .E6 K 0 = 1 := exactQ_zero .E6 K
    rw [hQ0]
    group
  have hdvd := e6_four_card_dvd K I hinner hdiag
  have hd3 : Nat.card I = 1 ∨ Nat.card I = 3 := (Nat.dvd_prime Nat.prime_three).1 hdvd
  rcases hd3 with h | h <;> rw [h] <;> decide

end Plane

end CFSG.RankThree.PartOne.KE
