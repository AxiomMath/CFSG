module

public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
open scoped Matrix Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Plane

theorem d4T36_hactor {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (hC : Subgroup.center 𝒞[K, σ] = ⊥) :
    ∀ B : Subgroup (MulAut 𝒞[K, σ]),
      (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ≤ B →
      ∀ A : Subgroup (MulAut 𝒞[K, σ]), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut 𝒞[K, σ]))))) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨n, hn, w, hnw, hw, g0, hg0C, hg0, hperf, hconj⟩ :=
    d4T36_frame hf K hK σ hσ hε hp hp3 hpd L
  intro B hB A hAB hA hcard hAin
  have hIntinj : Function.Injective (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) :=
    mulAut_conj_injective_of_center_eq_bot hC
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  set A₀ : Subgroup 𝒞[K, σ] :=
    A.comap (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) with hA₀
  have hA₀map : A₀.map (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    have h1 : (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) (q ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ hq
    exact hIntinj (h1.trans (map_one _).symm)
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let φ : A₀ →* ModGL TwistTag.D4.tag L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((triEmb K σ L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 := fun q => by
    change (MulAut.conj g0⁻¹ : MulAut (ModGL TwistTag.D4.tag L))
      (triEmb K σ L ((MulAut.conj c : MulAut 𝒞[K, σ]) (q : 𝒞[K, σ]))) = _
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin TwistTag.D4.tag.rank → Lˣ, φ q = rootDiagUnit TwistTag.D4.tag b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  obtain ⟨q, hq1, hqi⟩ : ∃ q : A₀, q ≠ 1 ∧ β q ⟨0, by decide⟩ = 1 := by
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => β q ⟨0, by decide⟩
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine d4Q_exists_ne_one_ker_of_card_sq hp hA₀card χ fun q => ?_
    have h1 : rootDiagUnit TwistTag.D4.tag (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 ⟨0, by decide⟩
  have hqA : (q : 𝒞[K, σ]) ∈ A₀ := q.2
  have hq1' : (q : 𝒞[K, σ]) ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hqp : orderOf (q : 𝒞[K, σ]) = p := orderOf_eq_prime (hA₀exp _ hqA) hq1'
  have hqAA : (MulAut.conj (q : 𝒞[K, σ]) : MulAut 𝒞[K, σ]) ∈ A := by
    have : (MulAut.conj (q : 𝒞[K, σ]) : MulAut 𝒞[K, σ]) ∈
        A₀.map (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) := ⟨q, hqA, rfl⟩
    rwa [hA₀map] at this
  have hq1'' : (MulAut.conj (q : 𝒞[K, σ]) : MulAut 𝒞[K, σ]) ≠ 1 := fun h =>
    hq1' (hIntinj (h.trans (map_one _).symm))
  have hb : rootDiagUnit TwistTag.D4.tag (β q) =
      g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hh : rootDiagUnit TwistTag.D4.tag (β q) ∈ twistedTorusOf n
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
    rw [← hβ]
    exact hφT q
  have hsing : (rootCharKernel (β q)).Nonempty :=
    ⟨Pi.single ⟨0, by decide⟩ 1, IsRoot.basis ⟨0, by decide⟩, by
      rw [CTTorus.rootChar_single]
      exact hqi⟩
  exact ⟨_, hqAA, hq1'', d4T36_core_odd hf K hK σ hσ hε hp hp3 hpd L hC hn w hnw hw hg0C hg0 hperf
    hB hqp c hb hh hsing⟩

end Plane

section Final

theorem planeLocalCoreOdd_triality_36 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    PlaneLocalCoreOdd p 𝒞[K, σ] := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨hZ, hcyc, Θ, hΘ, hker⟩ := triality_normal_form_data hℓ hf K hK σ hσ
  have hout : ¬ 2 ∣ Nat.card (commutator (Outer 𝒞[K, σ])) := by
    have := hcyc
    exact outer_commutator_odd_of_hom
      (fun a b => (IsCyclic.commGroup : CommGroup (K ≃+* K)).mul_comm a b) Θ hker
  have hcore : LocalCoreTrivialOn p fun α : MulAut 𝒞[K, σ] =>
      α ∉ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ
        hp hp3 B hB α hα hαp).2.2.2
  have hsolv : ∀ x : 𝒞[K, σ], orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set 𝒞[K, σ])), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    obtain ⟨n, hn, w, hnw, hw, g0, hg0C, hg0, hperf, hconj⟩ :=
      d4T36_frame hf K hK σ hσ hε hp hp3 hpd L
    have hzp : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hzp
    exact d4T36_solvable hf K hK σ hσ hε hp hp3 hpd L hn w hnw hw hg0C hg0 hperf hx c
      (hc x (Subgroup.mem_zpowers x)) V hVn hVs
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp hZ hsolv hout hcore
    (d4T36_hactor hf K hK σ hσ hε hp hp3 hpd L hZ)

theorem triality_36_component {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (hT : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 ℓ f)
    (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G)) :
    ComponentLocalCoreOddConclusion p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) := by
  have hm : TwistedChevalleyModel (L ⧸ Subgroup.center L) .D4 (ℓ ^ f) := hT.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hm
  have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
  exact component_odd_conclusion_of_native hp (by omega) hE hEcard ht ht1 hL hEL hSL e.symm
    (planeLocalCoreOdd_triality_36 hℓ hf K hK3 σ hσ hε hp hp3 hpd)

end Final

end CFSG.RankThree.PartOne.KGD
