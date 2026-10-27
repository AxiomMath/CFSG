module

public import CFSG.RankThree.PartOne.KE.E6TwFourCore
public import CFSG.RankThree.PartOne.KE.E6FourPlane

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix e6Index e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)
open scoped Matrix MatrixGroups Pointwise

section CardDvd

@[expose] def conjActionOfNormal {C G : Type*} [Group C] [Group G] (ι : C →* G)
    (hι : Function.Injective ι) (R : Subgroup G) (hle : ι.range ≤ R)
    [hN : (ι.range.subgroupOf R).Normal] : R →* MulAut C :=
  (MulAut.congr ((MonoidHom.ofInjective hι).trans
    (Subgroup.subgroupOfEquivOfLe hle).symm).symm).toMonoidHom.comp MulAut.conjNormal

theorem ι_conjActionOfNormal {C G : Type*} [Group C] [Group G] (ι : C →* G)
    (hι : Function.Injective ι) (R : Subgroup G) (hle : ι.range ≤ R)
    [hN : (ι.range.subgroupOf R).Normal] (a : R) (y : C) :
    ι (conjActionOfNormal ι hι R hle a y) = (a : G) * ι y * (a : G)⁻¹ := by
  set e' := (MonoidHom.ofInjective hι).trans (Subgroup.subgroupOfEquivOfLe hle).symm with he'
  have hval : ∀ z : C, (((e' z : ι.range.subgroupOf R) : R) : G) = ι z := fun z => rfl
  have h1 : conjActionOfNormal ι hι R hle a y = e'.symm (MulAut.conjNormal a (e' y)) := rfl
  have h2 := congrArg (fun m : ι.range.subgroupOf R => ((m : R) : G))
    (e'.apply_symm_apply (MulAut.conjNormal a (e' y)))
  simp only [hval] at h2
  rw [h1, h2, MulAut.conjNormal_apply]
  rfl

theorem card_dvd_index_of_rinner {C R : Type*} [Group C] [Group R] [Finite C]
    (I : Subgroup (MulAut C)) (Λ : R →* MulAut C) (N : Subgroup R)
    (hN : ∀ x ∈ N, Λ x ∈ inner C) (hI : ∀ η ∈ I, η ∈ Λ.range)
    (hinner : ∀ η ∈ I, η ∈ inner C → η = 1) : Nat.card I ∣ N.index := by
  classical
  set π : MulAut C →* Outer C := QuotientGroup.mk' (inner C) with hπ
  set f : R →* Outer C := π.comp Λ with hf
  let F : I →* Outer C := π.comp I.subtype
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : π (s : MulAut C) = 1 := hs
    have h2 : (s : MulAut C) ∈ inner C := (QuotientGroup.eq_one_iff _).1 h1
    exact Subtype.ext (hinner s s.2 h2)
  have hFr : F.range ≤ f.range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨r, hr⟩ := hI s s.2
    exact ⟨r, by simp [f, F, hr]⟩
  have hker : N ≤ f.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (hN x hx)
  have hcard : Nat.card I = Nat.card F.range :=
    Nat.card_congr (MonoidHom.ofInjective hFinj).toEquiv
  rw [hcard]
  refine (Subgroup.card_dvd_of_le hFr).trans ?_
  rw [← Subgroup.index_ker f]
  exact Subgroup.index_dvd_of_le hker

theorem e6_tw_rational_group {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∃ (kk : ℕ) (R : Subgroup (ModGL Tag.E6 L)),
      (∀ a, a ∈ R ↔ a ∈ adjointGroup Tag.E6 L ∧ twistE6 Fr a = a) ∧
      (twE6Emb K σ L).range ≤ R ∧
        ((twE6Emb K σ L).range.subgroupOf R).Normal ∧
          ((twE6Emb K σ L).range.subgroupOf R).index = 3 ^ kk := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨-, -, hder, ⟨kk, hk⟩, -, -, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  have hrange : (twE6Emb K σ L).range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨kk, R, fun a => (mem_twistedFixedGroup_iff_twistHom _ _ _), hrange ▸ hle,
    hrange ▸ hnormal, hrange ▸ hk⟩

end CardDvd

section InnerTrivial

theorem e6_tw_four_inner_trivial {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((ℓ ^ f : ℕ) : ZMod p) = 4) (hΦ : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x)
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    (hT : twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) =
      (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom Tag.E6 L))
    (A₀ : Subgroup (twistedE6RootGroup K σ)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : twistedE6RootGroup K σ)
    (hc : ∀ q ∈ A₀, g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)))
    {B : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hB : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B)
    (w : twistedE6RootGroup K σ)
    (hw : ∀ q ∈ A₀, q ≠ 1 → (MulAut.conj w : MulAut (twistedE6RootGroup K σ)) ∈
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (twistedE6RootGroup K σ))} :
          Set (MulAut (twistedE6RootGroup K σ))))) : w = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E6 L →* ModGL Tag.E6 L := twistE6 Fr with hΦdef
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hIntinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    conj_injective_of_center_eq_bot hC
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  let φ : A₀ →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((twE6Emb K σ L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * twE6Emb K σ L (c * (q : twistedE6RootGroup K σ) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit Tag.E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hex : ∀ i : Fin Tag.E6.rank, ∃ q : A₀, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => ?_
    have h1 : rootDiagUnit Tag.E6 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  set zw : ModGL Tag.E6 L := g0⁻¹ * twE6Emb K σ L (c * w * c⁻¹) * g0 with hzw
  have hzw_key : ∀ i : Fin Tag.E6.rank, ∃ a : Fin Tag.E6.rank → Lˣ,
      zw = rootDiagUnit Tag.E6 a ∧ a i = 1 := by
    intro i
    obtain ⟨q, hq1, hqi⟩ := hex i
    have hqA : (q : twistedE6RootGroup K σ) ∈ A₀ := q.2
    have hq1' : (q : twistedE6RootGroup K σ) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hqp : orderOf (q : twistedE6RootGroup K σ) = p :=
      orderOf_eq_prime (hA₀exp _ hqA) hq1'
    obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_tw_four_perx K hf hK σ hσ hp hp3 hord hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT hqp c (hc _ hqA)
    have hb : rootDiagUnit Tag.E6 (β q) = g0⁻¹ * twE6Emb K σ L
        (c * (q : twistedE6RootGroup K σ) * c⁻¹) * g0 := by
      rw [← hβ, hφ]
    obtain ⟨hψV, -⟩ := hψb (β q) hb
    obtain ⟨V, hVn, hVs, hVl⟩ := inner_core_preimage hp hC hB (q : twistedE6RootGroup K σ)
    obtain ⟨v, hvV, hvw⟩ := hVl (MulAut.conj w) (Subgroup.mem_inf.2
      ⟨hw _ hqA hq1', ⟨w, rfl⟩⟩)
    have hvw' : (v : twistedE6RootGroup K σ) = w := hIntinj hvw
    have hmem := hψV V hVn hVs v hvV
    rw [hψ v, hvw'] at hmem
    obtain ⟨hmemT, hmemC⟩ := Subgroup.mem_inf.1 hmem
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hmemT).1
    refine ⟨a, ha, ?_⟩
    have hα : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel (β q) := by
      refine ⟨IsRoot.basis i, ?_⟩
      rw [CTTorus.rootChar_single]
      exact hqi
    have hXmem : pinnedX Tag.E6 L (Pi.single i 1) 1 ∈ rootSpan Tag.E6 L (rootCharKernel (β q)) :=
      pinnedX_mem_rootSpan hα 1
    have hcomm := Subgroup.mem_centralizer_iff.1 hmemC _ hXmem
    rw [ha] at hcomm
    have hconj := rootDiagUnit_conj_pinnedX a (IsRoot.basis i) (1 : L)
    have hX : rootDiagUnit Tag.E6 a * pinnedX Tag.E6 L (Pi.single i 1) 1 *
        (rootDiagUnit Tag.E6 a)⁻¹ = pinnedX Tag.E6 L (Pi.single i 1) 1 := by
      rw [← hcomm]
      group
    have h3 : pinnedX Tag.E6 L (Pi.single i 1) (((rootChar a (Pi.single i 1) : Lˣ) : L) * 1) =
        pinnedX Tag.E6 L (Pi.single i 1) 1 := hconj.symm.trans hX
    have h4 := pinnedX_injective (τ := Tag.E6) (R := L) (Pi.single i 1) h3
    have h5 : rootChar a (Pi.single i 1) = 1 := Units.ext (by simpa using h4)
    rwa [CTTorus.rootChar_single] at h5
  obtain ⟨a0, ha0, -⟩ := hzw_key ⟨0, by decide⟩
  have ha0one : a0 = 1 := by
    funext j
    obtain ⟨aj, haj, hajj⟩ := hzw_key j
    have : aj = a0 := rootDiagUnit_injective (τ := Tag.E6) (K := L) (haj.symm.trans ha0)
    rw [← this]
    exact hajj
  have hz1 : zw = 1 := by rw [ha0, ha0one, rootDiagUnit_one]
  have hw1 : twE6Emb K σ L (c * w * c⁻¹) = twE6Emb K σ L 1 := by
    rw [map_one]
    have : g0⁻¹ * twE6Emb K σ L (c * w * c⁻¹) * g0 = 1 := hz1
    calc twE6Emb K σ L (c * w * c⁻¹)
        = g0 * (g0⁻¹ * twE6Emb K σ L (c * w * c⁻¹) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [this]; group
  have := twE6Emb_injective hw1
  calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
    _ = 1 := by rw [this]; group

end InnerTrivial

section Nonregular

theorem e6_tw_four_exists_nonregular {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (g0 : ModGL Tag.E6 L)
    (A₀ : Subgroup (twistedE6RootGroup K σ)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : twistedE6RootGroup K σ)
    (hc : ∀ q ∈ A₀, g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f))) (i : Fin Tag.E6.rank) :
    ∃ q ∈ A₀, q ≠ 1 ∧ ∃ b : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∧
        (rootCharKernel b).Nonempty := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hA₀fin : Finite A₀ := Finite.of_injective _ A₀.subtype_injective
  let φ : A₀ →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((twE6Emb K σ L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * twE6Emb K σ L (c * (q : twistedE6RootGroup K σ) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) :=
    fun q => by
      rw [hφ]
      exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit Tag.E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => β q i
      map_one' := by rw [hβone]; rfl
      map_mul' := fun q q' => by rw [hβmul]; rfl }
  obtain ⟨q, hq1, hqi⟩ := exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => by
    have h1 : rootDiagUnit Tag.E6 (β q) ^ p = 1 := by
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

section Plane

theorem e6_tw_four_hI {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x) :
    ∀ B : Subgroup (MulAut (twistedE6RootGroup K σ)),
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B →
      ∀ A : Subgroup (MulAut (twistedE6RootGroup K σ)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range →
          Odd (Nat.card ↥(autThetaT p B A)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_tw_four_frame K hf hK σ hσ hp hp3 hpq L n hnm hnW
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨kk, R, hRmem, hle, hRnormal, hRindex⟩ :=
    e6_tw_rational_group hℓ hf K hK σ hσ L (iterateFrobenius L ℓ f) hFr
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hIntinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (twistedE6RootGroup K σ) :=
    A.comap (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    have h1 : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ))
        (q ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ hq
    exact hIntinj (h1.trans (map_one _).symm)
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  set I : Subgroup (MulAut (twistedE6RootGroup K σ)) := autThetaT p B A with hI
  have hIle : ∀ q ∈ A₀, q ≠ 1 → I ≤ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut (twistedE6RootGroup K σ))} :
        Set (MulAut (twistedE6RootGroup K σ)))) := by
    intro q hq hq1
    have hqA : (MulAut.conj q : MulAut (twistedE6RootGroup K σ)) ∈ A := by
      have : (MulAut.conj q : MulAut (twistedE6RootGroup K σ)) ∈ A₀.map
          (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
        ⟨q, hq, rfl⟩
      rwa [hA₀map] at this
    have hq1' : (MulAut.conj q : MulAut (twistedE6RootGroup K σ)) ≠ 1 := fun h =>
      hq1 (hIntinj (h.trans (map_one _).symm))
    exact iInf₂_le_of_le _ hqA (iInf_le_of_le hq1' le_rfl)
  have hinner : ∀ s ∈ I, s ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (twistedE6RootGroup K σ) → s = 1 := by
    rintro s hs ⟨w, rfl⟩
    have hw : w = 1 := e6_tw_four_inner_trivial K hf hK σ hσ hp hp3 hordq hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT A₀ hA₀card hA₀exp c hc hB w fun q hq hq1 => hIle q hq hq1 hs
    rw [hw, map_one]
  obtain ⟨x, hxA, hx1, b, hb, hne⟩ := e6_tw_four_exists_nonregular K σ hp L n g0 A₀ hA₀card
    hA₀exp c hc ⟨0, by decide⟩
  have hxp : orderOf x = p := orderOf_eq_prime (hA₀exp x hxA) hx1
  have hR : ∀ s ∈ I, s ∈ (conjActionOfNormal (twE6Emb K σ L) twE6Emb_injective R hle
      (hN := hRnormal)).range := by
    intro s hs
    obtain ⟨a, haC, haF, hae⟩ := e6_tw_four_core_normal_form K hf hK σ hσ hp hp3 hordq hΦ L n
      hnm hnW g0 hg0C hg0 hperf hT hxp c (hc x hxA) hb hne hB (hIle x hxA hx1 hs)
    have haR : a ∈ R := (hRmem a).2 ⟨haC, haF⟩
    refine ⟨⟨a, haR⟩, ?_⟩
    apply MulEquiv.ext
    intro u
    apply (twE6Emb_injective (K := K) (σ := σ) (L := L))
    rw [ι_conjActionOfNormal (hN := hRnormal)]
    exact (hae u).symm
  have hN : ∀ y ∈ (twE6Emb K σ L).range.subgroupOf R,
      conjActionOfNormal (twE6Emb K σ L) twE6Emb_injective R hle (hN := hRnormal) y ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (twistedE6RootGroup K σ) := by
    intro y hy
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 hy
    refine ⟨u, ?_⟩
    apply MulEquiv.ext
    intro z
    apply (twE6Emb_injective (K := K) (σ := σ) (L := L))
    rw [ι_conjActionOfNormal (hN := hRnormal), ← hu]
    change twE6Emb K σ L (u * z * u⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hdvd := card_dvd_index_of_rinner I
    (conjActionOfNormal (twE6Emb K σ L) twE6Emb_injective R hle (hN := hRnormal))
    ((twE6Emb K σ L).range.subgroupOf R) hN hR hinner
  rw [hRindex] at hdvd
  exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) hdvd

end Plane

end CFSG.RankThree.PartOne.KE
