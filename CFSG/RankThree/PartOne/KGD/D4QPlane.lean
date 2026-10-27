module

public import CFSG.RankThree.PartOne.KGD.D4QPerX
public import CFSG.RankThree.PartOne.KGD.D4QPlaneGen
public import CFSG.RankThree.PartOne.KGD.D4QOuter
public import CFSG.RankThree.PartOne.KGD.G2Abstract
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE.NativeCyclicF4
public import CFSG.RankThree.PartOne.KE.Endpoint
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
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
public import Certificates.Certificate117
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.NativeCyclicEndpoint
public import CFSG.RankThree.PartOne.KGD.PlaneBridge
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Plane

variable {ℓ f : ℕ} [Fact ℓ.Prime]

theorem d4Q_hcomm (K : Type) [Field K] (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type)
    [Field L] [Algebra K L] [CharP L ℓ] :
    (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L) := by
  refine RingHom.ext fun c => ?_
  change algebraMap K L (σ c) = iterateFrobenius L ℓ f (algebraMap K L c)
  rw [hσ, map_pow, iterateFrobenius_def]

theorem d4Q_solvable (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : 𝒞[K, σ], orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set 𝒞[K, σ])), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  intro x hx V hVn hVs
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := d4Q_frame hf K hK σ hσ hp hp3 hpq L
  have hcomm := d4Q_hcomm K σ hσ L
  have hzp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hzp
  have hhx := hc x (Subgroup.mem_zpowers x)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hhx).1
  have hperx := d4Q_perx hf K σ hp hp3 hpq hg0C hg0 hperf hcomm hx c hb.symm (by rw [← hb]; exact hhx)
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hex : ∀ v : V, ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, a ∈ fixedCharTuples d4QM Fr ∧
      d4QPsi (triEmb K σ L) g0 c x (v : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) =
        rootDiagUnit TwistTag.D4.tag a := by
    intro v
    obtain ⟨hT, a, ha, -⟩ := hperx V hVn hVs v v.2
    refine ⟨a, ?_, ha⟩
    rw [d4Q_twistedTorus Fr] at hT
    obtain ⟨a', ha', hae⟩ := Subgroup.mem_map.1 hT
    have : a' = a := rootDiagUnit_injective (hae.trans ha)
    exact this ▸ ha'
  choose a haF hav using hex
  have hamul : ∀ v w : V, a (v * w) = a v * a w := fun v w => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [rootDiagUnit_mul, ← hav (v * w), ← hav v, ← hav w]
    exact map_mul (d4QPsi (triEmb K σ L) g0 c x) _ _
  have haone : a 1 = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [rootDiagUnit_one, ← hav 1]
    exact map_one (d4QPsi (triEmb K σ L) g0 c x)
  let Ψ : V →* (Fin 2 → Lˣ) :=
    { toFun := fun v => d4QCoord (a v)
      map_one' := by rw [haone, map_one]
      map_mul' := fun v w => by rw [hamul, map_mul] }
  have hΨinj : Function.Injective Ψ := by
    intro v w h
    have h1 : a v = a w := eq_of_d4QCoord_eq hFr (haF v) (haF w) h
    have h2 : d4QPsi (triEmb K σ L) g0 c x (v : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) =
        d4QPsi (triEmb K σ L) g0 c x (w : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) := by
      rw [hav, hav, h1]
    exact Subtype.ext (d4QPsi_injective triEmb_injective g0 c x h2)
  obtain ⟨hab, hcard⟩ := abelian_card_involutions_le_four Ψ hΨinj
  exact ⟨fun v hv w hw => congrArg Subtype.val (hab ⟨v, hv⟩ ⟨w, hw⟩), hcard⟩

theorem d4Q_inner_trivial (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (hC : Subgroup.center 𝒞[K, σ] = ⊥)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * trialityOpposition L)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (A₀ : Subgroup 𝒞[K, σ]) (hA₀ : Nat.card A₀ = p ^ 2) (hA₀exp : ∀ q ∈ A₀, q ^ p = 1)
    (c : 𝒞[K, σ])
    (hc : ∀ q ∈ A₀, g0⁻¹ * triEmb K σ L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    {B : Subgroup (MulAut 𝒞[K, σ])}
    (hB : (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ≤ B) (w : 𝒞[K, σ])
    (hw : ∀ q ∈ A₀, q ≠ 1 → (MulAut.conj w : MulAut 𝒞[K, σ]) ∈
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut 𝒞[K, σ])} :
          Set (MulAut 𝒞[K, σ])))) : w = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hcomm := d4Q_hcomm K σ hσ L
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  have hIntinj : Function.Injective (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) :=
    mulAut_conj_injective_of_center_eq_bot hC
  let φ : A₀ →* ModGL TwistTag.D4.tag L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((triEmb K σ L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 := fun q => by
    change (MulAut.conj g0⁻¹ : MulAut (ModGL TwistTag.D4.tag L))
      (triEmb K σ L ((MulAut.conj c : MulAut 𝒞[K, σ]) (q : 𝒞[K, σ]))) = _
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf (trialityOpposition L)
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
  have hex : ∀ i : Fin TwistTag.D4.tag.rank, ∃ q : A₀, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine d4Q_exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => ?_
    have h1 : rootDiagUnit TwistTag.D4.tag (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  obtain ⟨zw, hzw⟩ : ∃ zw : ModGL TwistTag.D4.tag L,
      zw = g0⁻¹ * triEmb K σ L (c * w * c⁻¹) * g0 := ⟨_, rfl⟩
  have hzw_key : ∀ i : Fin TwistTag.D4.tag.rank, ∃ a : Fin TwistTag.D4.tag.rank → Lˣ,
      zw = rootDiagUnit TwistTag.D4.tag a ∧ a i = 1 := by
    intro i
    obtain ⟨q, hq1, hqi⟩ := hex i
    have hqA : (q : 𝒞[K, σ]) ∈ A₀ := q.2
    have hq1' : (q : 𝒞[K, σ]) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hqp : orderOf (q : 𝒞[K, σ]) = p := orderOf_eq_prime (hA₀exp _ hqA) hq1'
    have hb : rootDiagUnit TwistTag.D4.tag (β q) =
        g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 := by
      rw [← hβ, hφ]
    have hh : rootDiagUnit TwistTag.D4.tag (β q) ∈ twistedTorusOf (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
      rw [← hβ]
      exact hφT q
    have hperx := d4Q_perx hf K σ hp hp3 hpq hg0C hg0 hperf hcomm hqp c hb hh
    obtain ⟨V, hVn, hVs, hVl⟩ := innerCorePreimage hp hIntinj hB (q : 𝒞[K, σ])
    obtain ⟨v, hvV, hvw⟩ := hVl (MulAut.conj w) (Subgroup.mem_inf.2
      ⟨hw _ hqA hq1', ⟨w, rfl⟩⟩)
    have hvw' : (v : 𝒞[K, σ]) = w := hIntinj hvw
    obtain ⟨-, a, ha, hker⟩ := hperx V hVn hVs v hvV
    refine ⟨a, ?_, ?_⟩
    · rw [d4QPsi_apply] at ha
      rw [hzw, ← hvw']
      exact ha
    · have hα : (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ rootCharKernel (β q) :=
        ⟨IsRoot.basis i, by rw [CTTorus.rootChar_single]; exact hqi⟩
      have h1 := hker _ hα
      rwa [CTTorus.rootChar_single] at h1
  obtain ⟨a0, ha0, -⟩ := hzw_key ⟨0, by decide⟩
  have ha0one : a0 = 1 := by
    funext j
    obtain ⟨aj, haj, hajj⟩ := hzw_key j
    have : aj = a0 := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (haj.symm.trans ha0)
    rw [← this]
    exact hajj
  have hz1 : zw = 1 := by rw [ha0, ha0one, rootDiagUnit_one]
  have hw1 : triEmb K σ L (c * w * c⁻¹) = triEmb K σ L 1 := by
    rw [map_one]
    have h1 : g0⁻¹ * triEmb K σ L (c * w * c⁻¹) * g0 = 1 := hzw ▸ hz1
    calc triEmb K σ L (c * w * c⁻¹)
        = g0 * (g0⁻¹ * triEmb K σ L (c * w * c⁻¹) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have h2 := triEmb_injective hw1
  calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
    _ = 1 := by rw [h2]; group

theorem d4Q_hI (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (hC : Subgroup.center 𝒞[K, σ] = ⊥) :
    ∀ B : Subgroup (MulAut 𝒞[K, σ]),
      (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ≤ B →
      ∀ A : Subgroup (MulAut 𝒞[K, σ]), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range →
          Odd (Nat.card ↥(autThetaT p B A)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := d4Q_frame hf K hK σ hσ hp hp3 hpq L
  intro B hB A hAB hA hcard hAin
  have hIntinj : Function.Injective (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) :=
    mulAut_conj_injective_of_center_eq_bot hC
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
  set I : Subgroup (MulAut 𝒞[K, σ]) := autThetaT p B A with hI
  have hIle : ∀ q ∈ A₀, q ≠ 1 → I ≤ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj q : MulAut 𝒞[K, σ])} :
        Set (MulAut 𝒞[K, σ]))) := by
    intro q hq hq1
    have hqA : (MulAut.conj q : MulAut 𝒞[K, σ]) ∈ A := by
      have : (MulAut.conj q : MulAut 𝒞[K, σ]) ∈
          A₀.map (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) := ⟨q, hq, rfl⟩
      rwa [hA₀map] at this
    have hq1' : (MulAut.conj q : MulAut 𝒞[K, σ]) ≠ 1 := fun h =>
      hq1 (hIntinj (h.trans (map_one _).symm))
    exact iInf₂_le_of_le _ hqA (iInf_le_of_le hq1' le_rfl)
  have hinner : ∀ s ∈ I, s ∈ inner 𝒞[K, σ] → s = 1 := by
    rintro s hs ⟨w, rfl⟩
    have hw : w = 1 := d4Q_inner_trivial hf K σ hσ hp hp3 hpq L hC hg0C hg0 hperf A₀ hA₀card
      hA₀exp c hc hB w fun q hq hq1 => hIle q hq hq1 hs
    rw [hw, map_one]
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    omega
  have hη2 : (g : MulAut 𝒞[K, σ]) ^ 2 = 1 := by
    have h3 := pow_orderOf_eq_one g
    rw [hg] at h3
    exact congrArg Subtype.val h3
  have hηo : (g : MulAut 𝒞[K, σ]) ∉
      (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range := fun hmem =>
    hg1 (Subtype.ext (hinner g g.2 hmem))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A₀) p
    (hA₀card ▸ dvd_pow_self p two_ne_zero)
  have hxA : (x : 𝒞[K, σ]) ∈ A₀ := x.2
  have hxp : orderOf (x : 𝒞[K, σ]) = p := by rw [Subgroup.orderOf_coe, hx]
  have hx1 : (x : 𝒞[K, σ]) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hcomm' := mem_centralizer_of_mem_autCore (hIle (x : 𝒞[K, σ]) hxA hx1 g.2)
  have hηx := apply_eq_of_comm_conj hIntinj (g : MulAut 𝒞[K, σ]) x hcomm'
  exact d4Q_no_outer_involution hℓ hf K hK σ hσ hp hp3 (by exact_mod_cast hpq) g hη2 hηo hxp hηx

end Plane

section Final

theorem planeLocalCoreOdd_triality_qplus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1) : PlaneLocalCoreOdd p 𝒞[K, σ] := by
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
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 hZ
    (d4Q_solvable hf K hK σ hσ hp hp3 hpq L) hout hcore (d4Q_hI hf K hK σ hσ hp hp3 hpq L hZ)

theorem triality_qplus_component {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1)
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
    (planeLocalCoreOdd_triality_qplus hℓ hf K hK3 σ hσ hp hp3 hpq)

end Final

end CFSG.RankThree.PartOne.KGD
