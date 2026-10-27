module

public import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.GroupTheory.CentralLineComponentAction
import CFSG.RankThree.Coprime.PlaneCoreCentralizesComponent
import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item422Proof

variable {X : Type} [Group X] [Finite X]

namespace Faithful

def faithfulComponents (Bb K₁ : Subgroup X) : Set (Subgroup X) :=
  {K | IsComponent K ∧ K ≠ K₁ ∧ Bb ⊓ Subgroup.centralizer (K : Set X) = ⊥}

def componentNormalizer : Subgroup X :=
  ⨅ (K : Subgroup X) (_ : IsComponent K), Subgroup.normalizer (K : Set X)

noncomputable def thetaCentralizer (b : X) : Subgroup X :=
  inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X))

def faithfulCentralizer (Bb K₁ : Subgroup X) : Subgroup X :=
  ⨅ K ∈ faithfulComponents Bb K₁, Subgroup.centralizer (K : Set X)

def faithfulC₀X (Bb K₁ : Subgroup X) : Subgroup X :=
  (componentNormalizer (X := X)) ⊓
    (Subgroup.centralizer (K₁ : Set X) ⊓ faithfulCentralizer Bb K₁)

def faithfulK₀' (Bb K₁ : Subgroup X) : Subgroup (componentNormalizer (X := X)) :=
  (faithfulCentralizer Bb K₁).subgroupOf (componentNormalizer (X := X))

def faithfulC₀' {K₁ : Subgroup X} (Bb : Subgroup X)
    (φ : componentNormalizer (X := X) →* autIn (componentNormalizer (X := X)) K₁) :
    Subgroup (componentNormalizer (X := X)) :=
  φ.ker ⊓ faithfulK₀' Bb K₁

def faithfulAutA (Ab K₁ : Subgroup X) :
    Subgroup (autIn (componentNormalizer (X := X)) K₁) :=
  (autIn Ab K₁).subgroupOf (autIn (componentNormalizer (X := X)) K₁)

theorem mem_componentNormalizer {g : X} :
    g ∈ componentNormalizer (X := X) ↔
      ∀ K : Subgroup X, IsComponent K → g ∈ Subgroup.normalizer (K : Set X) := by
  simp only [componentNormalizer, Subgroup.mem_iInf]

theorem mem_faithfulCentralizer {Bb K₁ : Subgroup X} {g : X} :
    g ∈ faithfulCentralizer Bb K₁ ↔
      ∀ K ∈ faithfulComponents Bb K₁, g ∈ Subgroup.centralizer (K : Set X) := by
  simp only [faithfulCentralizer, Subgroup.mem_iInf]

noncomputable def componentConjHom (K₁ : Subgroup X)
    (h : componentNormalizer (X := X) ≤ Subgroup.normalizer (K₁ : Set X)) :
    componentNormalizer (X := X) →* autIn (componentNormalizer (X := X)) K₁ :=
  (K₁.normalizerMonoidHom.comp (Subgroup.inclusion h)).codRestrict _ fun w => by
    rw [autIn_eq_range h]
    exact ⟨w, rfl⟩

structure FaithfulHypotheses where
  hSz : KFacts.KPSz
  hθ : aschbacherSolvableCore 3 X = ⊥
  hKX : CFSG.IsKGroup X
  Ab : Subgroup X
  Bb : Subgroup X
  cb : X
  K₁ : Subgroup X
  hcbZ : cb ∈ Subgroup.center X
  hcb3 : orderOf cb = 3
  hBb : CFSG.Assembly.IsElemAbelian 3 Bb
  hBcard : Nat.card Bb = 9
  hBZ : Bb ⊓ Subgroup.zpowers cb = ⊥
  hABZ : Ab = Bb ⊔ Subgroup.zpowers cb
  hmaxX : ∀ u : X, u ^ 3 = 1 → u ∈ Subgroup.centralizer (Ab : Set X) → u ∈ Ab
  hAN : ∀ K : Subgroup X, IsComponent K → Ab ≤ Subgroup.normalizer (K : Set X)
  hK₁ : IsComponent K₁
  hfaith : ∀ x ∈ Ab, x ∈ Subgroup.centralizer (K₁ : Set X) ↔ x ∈ Subgroup.zpowers cb
  hQ : ¬ thetaAlpha 3 Bb ≤ Subgroup.centralizer (K₁ : Set X)
  hKF : ∀ K : Subgroup X, IsComponent K → K ≠ K₁ →
    Bb ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
      σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range

structure BasicSetup extends FaithfulHypotheses (X := X) where
  hBA : Bb ≤ Ab
  hBbp : IsPGroup 3 Bb
  hBbE : IsElementaryAbelian 3 Bb
  hBcard' : Nat.card Bb = 3 ^ 2
  hBN : ∀ K : Subgroup X, IsComponent K → Bb ≤ Subgroup.normalizer (K : Set X)
  hBK₁ : Bb ⊓ Subgroup.centralizer (K₁ : Set X) = ⊥
  hBne : Bb ≠ ⊥
  h_exists : ∃ b ∈ Bb, b ≠ 1

structure ComponentSetup extends BasicSetup (X := X) where
  hcomm₁ : ∀ K : Subgroup X, IsComponent K → K ≠ K₁ →
    K ≤ Subgroup.centralizer (K₁ : Set X)
  h𝒵c : ∀ K ∈ faithfulComponents Bb K₁, cb ∈ K

structure NormalizerSetup extends ComponentSetup (X := X) where
  hWn : (componentNormalizer (X := X)).Normal
  hWN : ∀ K : Subgroup X, IsComponent K →
    componentNormalizer (X := X) ≤ Subgroup.normalizer (K : Set X)
  hmemW : ∀ g : X, (∀ K : Subgroup X, IsComponent K →
    g ∈ Subgroup.normalizer (K : Set X)) → g ∈ componentNormalizer (X := X)
  hBW : Bb ≤ componentNormalizer (X := X)
  hcbW : cb ∈ componentNormalizer (X := X)
  hAW : Ab ≤ componentNormalizer (X := X)
  hcompW : ∀ K : Subgroup X, IsComponent K → K ≤ componentNormalizer (X := X)

structure PieceSetup extends NormalizerSetup (X := X) where
  hRn : ∀ b : X, ((thetaCentralizer b).subgroupOf
    (Subgroup.centralizer ({b} : Set X))).Normal
  hRC : ∀ b : X, thetaCentralizer b ≤ Subgroup.centralizer ({b} : Set X)
  hRBb : ∀ b ∈ Bb, Bb ≤ Subgroup.normalizer (thetaCentralizer b : Set X)
  hVR : ∀ b ∈ Bb, ⁅thetaCentralizer b, Bb⁆ ≤ thetaCentralizer b
  hTR : ∀ b ∈ Bb, b ≠ 1 → thetaT 3 Bb ≤ thetaCentralizer b
  hR3 : ∀ b : X, ¬ 3 ∣ Nat.card (thetaCentralizer b)
  hRo : ∀ b : X, ∀ x ∈ thetaCentralizer b, ¬ 3 ∣ orderOf x

structure PieceCentralizerSetup extends PieceSetup (X := X) where
  hRO : ∀ b ∈ Bb, thetaCentralizer b ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X)
  hNF : ∀ K : Subgroup X, IsComponent K → Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
    ∀ b ∈ Bb, b ≠ 1 → ⁅thetaCentralizer b, Bb⁆ ≤ Subgroup.centralizer (K : Set X) ∧
      thetaT 3 Bb ≤ Subgroup.centralizer (K : Set X)
  hVW : ∀ b : X, ⁅thetaCentralizer b, Bb⁆ ≤ componentNormalizer (X := X)
  hTW : thetaT 3 Bb ≤ componentNormalizer (X := X)

structure CentralizerSetup extends PieceCentralizerSetup (X := X) where
  hmemK₀ : ∀ g : X, g ∈ faithfulCentralizer Bb K₁ ↔
    ∀ K ∈ faithfulComponents Bb K₁, g ∈ Subgroup.centralizer (K : Set X)
  hWK₀ : componentNormalizer (X := X) ≤
    Subgroup.normalizer (faithfulCentralizer Bb K₁ : Set X)
  hWC₀ : componentNormalizer (X := X) ≤
    Subgroup.normalizer (faithfulC₀X Bb K₁ : Set X)
  hC₀𝒮 : ∀ K ∈ insert K₁ (faithfulComponents Bb K₁),
    faithfulC₀X Bb K₁ ≤ Subgroup.centralizer (K : Set X)
  hpiece : ∀ b ∈ Bb, b ≠ 1 → ∀ s : X, s ∈ componentNormalizer (X := X) →
    s ∈ thetaCentralizer b →
    (∀ K : Subgroup X, IsComponent K → Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
      s ∈ Subgroup.centralizer (K : Set X)) →
    s ∈ Subgroup.centralizer (faithfulC₀X Bb K₁ : Set X)

structure ActionSetup extends CentralizerSetup (X := X) where
  ψ : componentNormalizer (X := X) →* MulAut K₁
  φ : componentNormalizer (X := X) →* autIn (componentNormalizer (X := X)) K₁
  hφeq : φ = componentConjHom K₁ (hWN K₁ hK₁)
  hφs : Function.Surjective φ
  hφker : ∀ w : componentNormalizer (X := X),
    w ∈ φ.ker ↔ (w : X) ∈ Subgroup.centralizer (K₁ : Set X)
  hK₀'n : (faithfulK₀' Bb K₁).Normal
  hkern : φ.ker.Normal
  hC₀'n : (faithfulC₀' Bb φ).Normal
  hC₀'le : faithfulC₀' Bb φ ≤ φ.ker
  hK₀'C : faithfulK₀' Bb K₁ ⊓ φ.ker ≤ faithfulC₀' Bb φ

structure CommutatorSetup extends ActionSetup (X := X) where
  hcommW : ∀ x y : componentNormalizer (X := X),
    x * y * x⁻¹ * y⁻¹ ∈ φ.ker ⊔ faithfulK₀' Bb K₁

structure TransferSetup extends CommutatorSetup (X := X) where
  hGL : ∀ P : Subgroup X, P ≤ componentNormalizer (X := X) →
    ∀ b' : componentNormalizer (X := X), (b' : X) ∈ Bb → (b' : X) ≠ 1 →
    P ≤ thetaCentralizer (b' : X) →
    (∀ s ∈ P, ∀ K : Subgroup X, IsComponent K →
      Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
      s ∈ Subgroup.centralizer (K : Set X)) →
    (P.subgroupOf (componentNormalizer (X := X))).map φ ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({φ b'} : Set (autIn (componentNormalizer (X := X)) K₁)))

structure AutSetup extends TransferSetup (X := X) where
  hB₃ : faithfulAutA Ab K₁ = (Bb.subgroupOf (componentNormalizer (X := X))).map φ

structure NormalSetup extends AutSetup (X := X) where
  hnormal : ((autIn (componentNormalizer (X := X)) K₁).subgroupOf (autIn ⊤ K₁)).Normal

section Certificates

variable [Fact (Nat.Prime 3)]

def basicSetup (h : FaithfulHypotheses (X := X)) : BasicSetup (X := X) where
  toFaithfulHypotheses := h
  hBA := h.hABZ ▸ le_sup_left
  hBbp := fun x => ⟨1, Subtype.ext (by simpa using h.hBb.2 x x.2)⟩
  hBbE := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 h.Bb).mpr h.hBb
  hBcard' := by rw [h.hBcard]; norm_num
  hBN := fun K hK => (h.hABZ ▸ le_sup_left).trans (h.hAN K hK)
  hBK₁ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz := (h.hfaith x ((h.hABZ ▸ le_sup_left) hx.1)).mp hx.2
    have hmem : x ∈ h.Bb ⊓ Subgroup.zpowers h.cb := ⟨hx.1, hxz⟩
    rwa [h.hBZ] at hmem
  hBne := by
    intro hbot
    have hc := h.hBcard
    rw [hbot, Subgroup.card_bot] at hc
    norm_num at hc
  h_exists := by
    have hne : h.Bb ≠ ⊥ := by
      intro hbot
      have hc := h.hBcard
      rw [hbot, Subgroup.card_bot] at hc
      norm_num at hc
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨b, hb, fun h' => hb1 (Subtype.ext h')⟩

def componentSetup (s : BasicSetup (X := X)) : ComponentSetup (X := X) where
  toBasicSetup := s
  hcomm₁ := by
    intro K hK hKK₁
    rcases CFSG.LocalCores.distinct_components_commute hK s.hK₁ with h | h
    · exact absurd h hKK₁
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  h𝒵c := by
    intro K hK
    simp only [faithfulComponents, Set.mem_setOf_eq] at hK
    have h3 : 3 ∣ Nat.card (K ⧸ Subgroup.center K) := by
      by_contra h
      exact inf_centralizer_ne_bot_of_not_three_dvd s.hSz s.hKX s.hBb s.hBcard hK.1
        (s.hBN K hK.1) h hK.2.2
    exact mem_component_of_three_dvd s.hmaxX s.hABZ s.hcbZ s.hcb3 s.hK₁ s.hfaith s.hBbp
      hK.1 hK.2.1 (s.hBN K hK.1) (h3.trans (Subgroup.card_quotient_dvd_card _))

def normalizerSetup (s : ComponentSetup (X := X)) : NormalizerSetup (X := X) :=
  let hWn : (componentNormalizer (X := X)).Normal := iInf_normalizer_components_normal
  let hWN : ∀ K : Subgroup X, IsComponent K →
      componentNormalizer (X := X) ≤ Subgroup.normalizer (K : Set X) :=
    fun K hK => iInf₂_le K hK
  let hmemW : ∀ g : X, (∀ K : Subgroup X, IsComponent K →
      g ∈ Subgroup.normalizer (K : Set X)) → g ∈ componentNormalizer (X := X) :=
    fun g hg => (mem_componentNormalizer (X := X)).mpr hg
  let hBW : s.Bb ≤ componentNormalizer (X := X) := fun x hx =>
    (mem_componentNormalizer (X := X)).mpr fun K hK => s.hBN K hK hx
  let hcbW : s.cb ∈ componentNormalizer (X := X) :=
    (mem_componentNormalizer (X := X)).mpr fun K _ =>
      Subgroup.mem_normalizer_fintype fun n _ => by
        rw [← Subgroup.mem_center_iff.mp s.hcbZ n]
        group
        exact ‹n ∈ (K : Set X)›
  let hAW : s.Ab ≤ componentNormalizer (X := X) := by
    rw [s.hABZ]
    exact sup_le hBW (Subgroup.zpowers_le.mpr hcbW)
  let hcompW : ∀ K : Subgroup X, IsComponent K → K ≤ componentNormalizer (X := X) := by
    intro K hK x hx
    exact (mem_componentNormalizer (X := X)).mpr fun K' hK' =>
      (by
        rcases CFSG.LocalCores.distinct_components_commute hK hK' with h | h
        · exact h ▸ Subgroup.le_normalizer hx
        · exact Subgroup.centralizer_le_normalizer _
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx))
  { toComponentSetup := s, hWn := hWn, hWN := hWN, hmemW := hmemW, hBW := hBW,
    hcbW := hcbW, hAW := hAW, hcompW := hcompW }

def pieceSetup (s : NormalizerSetup (X := X)) : PieceSetup (X := X) :=
  let hRn : ∀ b : X, ((thetaCentralizer b).subgroupOf
      (Subgroup.centralizer ({b} : Set X))).Normal := by
    intro b
    rw [show (thetaCentralizer b).subgroupOf (Subgroup.centralizer ({b} : Set X)) =
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) from
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _]
    infer_instance
  let hRC : ∀ b : X, thetaCentralizer b ≤ Subgroup.centralizer ({b} : Set X) :=
    fun b => Subgroup.map_subtype_le _
  let hRBb : ∀ b ∈ s.Bb, s.Bb ≤ Subgroup.normalizer (thetaCentralizer b : Set X) := by
    intro b hb
    have hBC : s.Bb ≤ Subgroup.centralizer ({b} : Set X) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (s.hBb.1.is_comm.comm (⟨x, hx⟩ : s.Bb) ⟨b, hb⟩))
    exact hBC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (hRC b)).mp (hRn b))
  let hVR : ∀ b ∈ s.Bb, ⁅thetaCentralizer b, s.Bb⁆ ≤ thetaCentralizer b := fun b hb =>
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hRBb b hb)
  let hTR : ∀ b ∈ s.Bb, b ≠ 1 → thetaT 3 s.Bb ≤ thetaCentralizer b :=
    fun b hb hb1 => iInf₂_le_of_le b hb (iInf_le _ hb1)
  let hR3 : ∀ b : X, ¬ 3 ∣ Nat.card (thetaCentralizer b) :=
    fun b => (inSubgroup_theta_solvable_coprime _).2
  let hRo : ∀ b : X, ∀ x ∈ thetaCentralizer b, ¬ 3 ∣ orderOf x :=
    fun b x hx h => hR3 b (h.trans (Subgroup.orderOf_dvd_natCard _ hx))
  { toNormalizerSetup := s, hRn := hRn, hRC := hRC, hRBb := hRBb, hVR := hVR,
    hTR := hTR, hR3 := hR3, hRo := hRo }

def pieceCentralizerSetup (s : PieceSetup (X := X)) : PieceCentralizerSetup (X := X) :=
  let hRO : ∀ b ∈ s.Bb,
      thetaCentralizer b ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
    intro b hb
    have hbp : IsPGroup 3 (Subgroup.zpowers b) := s.hBbp.to_le (Subgroup.zpowers_le.mpr hb)
    have hzc : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X) =
        Subgroup.centralizer ({b} : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hRP : ⁅thetaCentralizer b, CFSG.pCore 3 X⁆ = ⊥ :=
      local_prime_complement_centralizes_normal_prime_group Nat.prime_three
        (P := CFSG.pCore 3 X) (A := Subgroup.zpowers b) (S := thetaCentralizer b)
        CFSG.pCore_isPGroup hbp (by rw [hzc]; exact s.hRC b)
        (by rw [hzc]; exact s.hRn b) (s.hR3 b)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRP
  let hNF : ∀ K : Subgroup X, IsComponent K →
      s.Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
      ∀ b ∈ s.Bb, b ≠ 1 → ⁅thetaCentralizer b, s.Bb⁆ ≤ Subgroup.centralizer (K : Set X) ∧
        thetaT 3 s.Bb ≤ Subgroup.centralizer (K : Set X) := by
    intro K hK hne b hb hb1
    obtain ⟨h1, h2, -⟩ := Coprime.nonfaithful_plane_local_core_product_centralizes_component
      Nat.prime_three s.hBbE s.hBcard' hb hb1 hK
      (commutator_le_normalizer_of_components s.hBN hK) hne
    exact ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2⟩
  let hVW : ∀ b : X, ⁅thetaCentralizer b, s.Bb⁆ ≤ componentNormalizer (X := X) :=
    fun b x hx => (mem_componentNormalizer (X := X)).mpr fun K hK =>
      commutator_le_normalizer_of_components s.hBN hK hx
  let hTW : thetaT 3 s.Bb ≤ componentNormalizer (X := X) := by
    intro x hx
    exact (mem_componentNormalizer (X := X)).mpr fun K hK => by
      by_cases h3 : 3 ∣ Nat.card (K ⧸ Subgroup.center K)
      · exact Coprime.theta_plane_intersection_normalizes_prime_component Nat.prime_three hK
          (center_component_le_pCore Nat.prime_three s.hθ hK) h3 (s.hBN K hK) s.hBbE
          s.hBcard' hx
      · obtain ⟨b₀, hb₀, hb₀1⟩ := s.h_exists
        exact Subgroup.centralizer_le_normalizer _
          ((hNF K hK (inf_centralizer_ne_bot_of_not_three_dvd s.hSz s.hKX s.hBb s.hBcard hK
            (s.hBN K hK) h3) b₀ hb₀ hb₀1).2 hx)
  { toPieceSetup := s, hRO := hRO, hNF := hNF, hVW := hVW, hTW := hTW }

def centralizerSetup (s : PieceCentralizerSetup (X := X)) : CentralizerSetup (X := X) :=
  let hmemK₀ : ∀ g : X, g ∈ faithfulCentralizer s.Bb s.K₁ ↔
      ∀ K ∈ faithfulComponents s.Bb s.K₁, g ∈ Subgroup.centralizer (K : Set X) :=
    fun g => mem_faithfulCentralizer
  let hWK₀ : componentNormalizer (X := X) ≤
      Subgroup.normalizer (faithfulCentralizer s.Bb s.K₁ : Set X) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    rw [SetLike.mem_coe, hmemK₀] at hk ⊢
    intro K hK
    exact (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_centralizer (s.hWN K hK.1 hw)) k).mp (hk K hK)
  let hWC₀ : componentNormalizer (X := X) ≤
      Subgroup.normalizer (faithfulC₀X s.Bb s.K₁ : Set X) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨hkW, hkC, hkK₀⟩ := hk
    refine ⟨s.hWn.conj_mem k hkW w, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer (s.hWN s.K₁ s.hK₁ hw)) k).mp hkC
    · exact (Subgroup.mem_normalizer_iff.mp (hWK₀ hw) k).mp hkK₀
  let hC₀𝒮 : ∀ K ∈ insert s.K₁ (faithfulComponents s.Bb s.K₁),
      faithfulC₀X s.Bb s.K₁ ≤ Subgroup.centralizer (K : Set X) := by
    intro K hK x hx
    rcases Set.mem_insert_iff.mp hK with rfl | hK𝒵
    · exact hx.2.1
    · exact (hmemK₀ x).mp hx.2.2 K hK𝒵
  let hpiece : ∀ b ∈ s.Bb, b ≠ 1 → ∀ y : X, y ∈ componentNormalizer (X := X) →
      y ∈ thetaCentralizer b →
      (∀ K : Subgroup X, IsComponent K → s.Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
        y ∈ Subgroup.centralizer (K : Set X)) →
      y ∈ Subgroup.centralizer (faithfulC₀X s.Bb s.K₁ : Set X) := by
    intro b hb _ y hyW hyR hyK
    refine mem_centralizer_of_coprime s.hθ s.hWN inf_le_left hWC₀
      (insert s.K₁ (faithfulComponents s.Bb s.K₁)) hC₀𝒮 hyW (s.hRo b y hyR)
      (s.hRO b hb hyR) fun K hK hK𝒮 => hyK K hK fun hbot => hK𝒮 ?_
    exact Set.mem_insert_of_mem _ ⟨hK, fun h => hK𝒮 (h ▸ Set.mem_insert _ _), hbot⟩
  { toPieceCentralizerSetup := s, hmemK₀ := hmemK₀, hWK₀ := hWK₀, hWC₀ := hWC₀,
    hC₀𝒮 := hC₀𝒮, hpiece := hpiece }

def actionSetup (s : CentralizerSetup (X := X)) : ActionSetup (X := X) :=
  let hWK₁ : componentNormalizer (X := X) ≤ Subgroup.normalizer (s.K₁ : Set X) :=
    s.hWN s.K₁ s.hK₁
  let ψ : componentNormalizer (X := X) →* MulAut s.K₁ :=
    s.K₁.normalizerMonoidHom.comp (Subgroup.inclusion hWK₁)
  let hψ : ψ = s.K₁.normalizerMonoidHom.comp (Subgroup.inclusion hWK₁) := rfl
  let hY : autIn (componentNormalizer (X := X)) s.K₁ = ψ.range := autIn_eq_range hWK₁
  let hψmem : ∀ w, ψ w ∈ autIn (componentNormalizer (X := X)) s.K₁ := fun w => by
    rw [hY]; exact ⟨w, rfl⟩
  let φ : componentNormalizer (X := X) →* autIn (componentNormalizer (X := X)) s.K₁ :=
    ψ.codRestrict _ hψmem
  let hφeq : φ = componentConjHom s.K₁ hWK₁ := MonoidHom.ext fun w => Subtype.ext rfl
  let hφs : Function.Surjective φ := by
    rintro ⟨σ, hσ⟩
    rw [hY] at hσ
    obtain ⟨w, rfl⟩ := hσ
    exact ⟨w, rfl⟩
  let hφker : ∀ w : componentNormalizer (X := X),
      w ∈ φ.ker ↔ (w : X) ∈ Subgroup.centralizer (s.K₁ : Set X) := by
    intro w
    have hiff : φ w = 1 ↔ ψ w = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [MonoidHom.mem_ker, hiff, hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  let hK₀'n : (faithfulK₀' s.Bb s.K₁).Normal := ⟨fun k hk w => by
    rw [faithfulK₀', Subgroup.mem_subgroupOf] at hk ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (s.hWK₀ w.2) k).mp hk⟩
  let hkern : φ.ker.Normal := MonoidHom.normal_ker φ
  let hC₀'n : (faithfulC₀' s.Bb φ).Normal := Subgroup.normal_inf_normal _ _
  let hC₀'le : faithfulC₀' s.Bb φ ≤ φ.ker := inf_le_left
  let hK₀'C : faithfulK₀' s.Bb s.K₁ ⊓ φ.ker ≤ faithfulC₀' s.Bb φ := by
    simp only [faithfulC₀', inf_comm]
    exact le_rfl
  { toCentralizerSetup := s, ψ := ψ, φ := φ, hφeq := hφeq, hφs := hφs, hφker := hφker,
    hK₀'n := hK₀'n, hkern := hkern, hC₀'n := hC₀'n, hC₀'le := hC₀'le, hK₀'C := hK₀'C }

def commutatorSetup (s : ActionSetup (X := X)) : CommutatorSetup (X := X) where
  toActionSetup := s
  hcommW := by
    intro x y
    let g : X := (x : X) * y * (x : X)⁻¹ * (y : X)⁻¹
    have hinner : ∀ K ∈ faithfulComponents s.Bb s.K₁,
        ∃ k ∈ K, ∀ w ∈ K, g * w * g⁻¹ = k * w * k⁻¹ := by
      intro K hK
      have hK' : IsComponent K ∧ K ≠ s.K₁ ∧
          s.Bb ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
        simpa only [faithfulComponents, Set.mem_setOf_eq] using hK
      exact exists_inner_of_fixComm (s.hKF K hK'.1 hK'.2.1 hK'.2.2) (s.h𝒵c K hK)
        s.hcbZ s.hcb3 (s.hWN K hK'.1 x.2) (s.hWN K hK'.1 y.2)
    obtain ⟨e, he, hec⟩ := exists_mem_iSup_conj (faithfulComponents s.Bb s.K₁)
      (fun K hK => by simpa only [faithfulComponents, Set.mem_setOf_eq] using hK.1) g hinner
    have heW : e ∈ componentNormalizer (X := X) :=
      (iSup₂_le fun K hK => s.hcompW K (by
        simpa only [faithfulComponents, Set.mem_setOf_eq] using hK.1)) he
    have heK₁ : e ∈ Subgroup.centralizer (s.K₁ : Set X) :=
      (iSup₂_le fun K hK => s.hcomm₁ K (by
        simpa only [faithfulComponents, Set.mem_setOf_eq] using hK.1) (by
        simpa only [faithfulComponents, Set.mem_setOf_eq] using hK.2.1)) he
    have h1 : (⟨e, heW⟩ : componentNormalizer (X := X)) ∈ s.φ.ker := (s.hφker _).mpr heK₁
    have h2 : (⟨e, heW⟩ : componentNormalizer (X := X))⁻¹ *
        (x * y * x⁻¹ * y⁻¹) ∈ faithfulK₀' s.Bb s.K₁ := by
      rw [faithfulK₀', Subgroup.mem_subgroupOf, mem_faithfulCentralizer]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      intro K hK
      exact hec K hK
    have := Subgroup.mul_mem_sup h1 h2
    rwa [mul_inv_cancel_left] at this

def transferSetup (s : CommutatorSetup (X := X)) : TransferSetup (X := X) where
  toCommutatorSetup := s
  hGL := by
    intro P hPW b' hb' hb'1 hPR hPK
    have : Finite (MulAut s.K₁) :=
      Finite.of_injective (fun σ : MulAut s.K₁ => (σ : s.K₁ → s.K₁))
        (fun σ τ h => MulEquiv.ext (congrFun h))
    refine map_le_theta_centralizer s.φ s.hφs b' s.hC₀'n s.hK₀'n s.hC₀'le s.hK₀'C
      s.hcommW ?_ ?_
    · have hle : P.subgroupOf (componentNormalizer (X := X)) ≤
          (thetaCentralizer (b' : X)).subgroupOf (componentNormalizer (X := X)) := fun v hv =>
        Subgroup.mem_subgroupOf.mpr (hPR (Subgroup.mem_subgroupOf.mp hv))
      exact hle.trans (subgroupOf_theta_le b'.2)
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcX : (c : X) ∈ faithfulC₀X s.Bb s.K₁ :=
        ⟨c.2, (s.hφker c).mp hc.1, Subgroup.mem_subgroupOf.mp hc.2⟩
      have hvX := Subgroup.mem_subgroupOf.mp hv
      have := Subgroup.mem_centralizer_iff.mp
        (s.hpiece _ hb' hb'1 _ (hPW hvX) (hPR hvX) (hPK _ hvX)) _ hcX
      exact Subtype.ext this

def autSetup (s : TransferSetup (X := X)) : AutSetup (X := X) where
  toTransferSetup := s
  hB₃ := by
    ext β
    rw [faithfulAutA, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hβ
      obtain ⟨g, hgN, hgA, hg⟩ := mem_autIn_iff.mp hβ
      rw [s.hABZ] at hgA
      have hzN : (Subgroup.zpowers s.cb).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr s.hcbZ)
      obtain ⟨b', hb', z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hgA
      refine ⟨⟨b', s.hBW hb'⟩, Subgroup.mem_subgroupOf.mpr hb', ?_⟩
      apply Subtype.ext
      rw [← hg, s.hφeq]
      ext k
      change (b' : X) * k * b'⁻¹ = b' * z * k * (b' * z)⁻¹
      have hzk : z * k = k * z := (Subgroup.mem_center_iff.mp
        (Subgroup.zpowers_le.mpr s.hcbZ hz) k).symm
      calc (b' : X) * k * b'⁻¹ = b' * (k * z) * z⁻¹ * b'⁻¹ := by group
        _ = b' * (z * k) * z⁻¹ * b'⁻¹ := by rw [hzk]
        _ = b' * z * k * (b' * z)⁻¹ := by group
    · rintro ⟨b', hb', rfl⟩
      refine mem_autIn_iff.mpr ⟨b', s.hWN s.K₁ s.hK₁ b'.2,
        s.hBA (Subgroup.mem_subgroupOf.mp hb'), ?_⟩
      rw [s.hφeq]
      rfl

def normalSetup (s : AutSetup (X := X)) : NormalSetup (X := X) where
  toAutSetup := s
  hnormal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (autIn_mono le_top)]
    intro σ hσ
    obtain ⟨n, hnN, -, rfl⟩ := mem_autIn_iff.mp hσ
    refine Subgroup.mem_normalizer_fintype fun τ hτ => ?_
    obtain ⟨w, hwN, hwW, rfl⟩ := mem_autIn_iff.mp hτ
    refine mem_autIn_iff.mpr ⟨n * w * n⁻¹, ?_, s.hWn.conj_mem w hwW n, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN hwN) (Subgroup.inv_mem _ hnN)
    · rw [← map_inv, ← map_mul, ← map_mul]
      rfl

theorem piece_image_ne_bot (s : NormalSetup (X := X)) {b : X} (hb : b ∈ s.Bb)
    (hVK : ¬ ⁅thetaCentralizer b, s.Bb⁆ ≤ Subgroup.centralizer (s.K₁ : Set X)) :
    ((⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf
      (componentNormalizer (X := X))).map s.φ ≠ ⊥ := by
  intro hbot
  apply hVK
  intro v hv
  have hmem : s.φ ⟨v, s.hVW b hv⟩ ∈
      ((⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf
        (componentNormalizer (X := X))).map s.φ :=
    Subgroup.mem_map_of_mem s.φ (Subgroup.mem_subgroupOf.mpr hv)
  rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, s.hφker] at hmem
  exact hmem

theorem piece_image_le_thetaJ (s : NormalSetup (X := X)) {b : X} (hb : b ∈ s.Bb)
    (hb1 : b ≠ 1) :
    ((⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf
      (componentNormalizer (X := X))).map s.φ ≤ thetaJ 3 (faithfulAutA s.Ab s.K₁) := by
  let b' : componentNormalizer (X := X) := ⟨b, s.hBW hb⟩
  have hVle := s.hGL _ (s.hVW b) b' hb hb1 (s.hVR b hb) fun v hv K hK hne =>
    (s.hNF K hK hne b hb hb1).1 hv
  have hβB : s.φ b' ∈ faithfulAutA s.Ab s.K₁ :=
    s.hB₃ ▸ ⟨b', Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hβ1 : s.φ b' ≠ 1 := by
    intro h
    have hk : b' ∈ s.φ.ker := h
    rw [s.hφker] at hk
    have hmem : b ∈ s.Bb ⊓ Subgroup.centralizer (s.K₁ : Set X) := ⟨hb, hk⟩
    rw [s.hBK₁] at hmem
    exact hb1 hmem
  have hidem : ⁅⁅thetaCentralizer b, s.Bb⁆, s.Bb⁆ = ⁅thetaCentralizer b, s.Bb⁆ :=
    CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three s.Bb (thetaCentralizer b) s.hBbp (s.hR3 b) (s.hRBb b hb)
  have hcomm' : ⁅(⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf
      (componentNormalizer (X := X)),
      s.Bb.subgroupOf (componentNormalizer (X := X))⁆ =
      (⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf (componentNormalizer (X := X)) := by
    rw [commutator_subgroupOf (s.hVW b) s.hBW, hidem]
  calc ((⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf
          (componentNormalizer (X := X))).map s.φ
      = ⁅((⁅thetaCentralizer b, s.Bb⁆ : Subgroup X).subgroupOf
          (componentNormalizer (X := X))).map s.φ,
          (s.Bb.subgroupOf (componentNormalizer (X := X))).map s.φ⁆ := by
        rw [← Subgroup.map_commutator, hcomm']
    _ ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer
            ({s.φ b'} : Set (autIn (componentNormalizer (X := X)) s.K₁))),
          faithfulAutA s.Ab s.K₁⁆ :=
        Subgroup.commutator_mono hVle s.hB₃.symm.le
    _ ≤ thetaJ 3 (faithfulAutA s.Ab s.K₁) :=
        le_iSup₂_of_le (s.φ b') hβB (le_iSup_of_le hβ1 le_rfl)

theorem thetaAlpha_ne_bot_of_thetaT_le (s : NormalSetup (X := X))
    (hTK : thetaT 3 s.Bb ≤ Subgroup.centralizer (s.K₁ : Set X)) :
    thetaAlpha 3 (faithfulAutA s.Ab s.K₁) ≠ ⊥ := by
  have hJ : ¬ thetaJ 3 s.Bb ≤ Subgroup.centralizer (s.K₁ : Set X) := fun h =>
    s.hQ (by rw [thetaAlpha]; exact sup_le h hTK)
  obtain ⟨b, hb, hb1, hVK⟩ : ∃ b ∈ s.Bb, b ≠ 1 ∧
      ¬ ⁅thetaCentralizer b, s.Bb⁆ ≤ Subgroup.centralizer (s.K₁ : Set X) := by
    by_contra hcon
    push Not at hcon
    exact hJ (iSup₂_le fun b hb => iSup_le fun hb1 => hcon b hb hb1)
  have hVne := piece_image_ne_bot s hb hVK
  have hJle := piece_image_le_thetaJ s hb hb1
  intro hbot
  apply hVne
  rw [eq_bot_iff, ← hbot, thetaAlpha]
  exact hJle.trans le_sup_left

theorem thetaAlpha_ne_bot_of_not_thetaT_le (s : NormalSetup (X := X))
    (hTK : ¬ thetaT 3 s.Bb ≤ Subgroup.centralizer (s.K₁ : Set X)) :
    thetaAlpha 3 (faithfulAutA s.Ab s.K₁) ≠ ⊥ := by
  have hTne : ((thetaT 3 s.Bb).subgroupOf (componentNormalizer (X := X))).map s.φ ≠ ⊥ := by
    intro hbot
    apply hTK
    intro t ht
    have hmem : s.φ ⟨t, s.hTW ht⟩ ∈
        ((thetaT 3 s.Bb).subgroupOf (componentNormalizer (X := X))).map s.φ :=
      Subgroup.mem_map_of_mem s.φ (Subgroup.mem_subgroupOf.mpr ht)
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, s.hφker] at hmem
    exact hmem
  have hTle : ((thetaT 3 s.Bb).subgroupOf (componentNormalizer (X := X))).map s.φ ≤
      thetaT 3 (faithfulAutA s.Ab s.K₁) := by
    refine le_iInf fun β => le_iInf fun hβ => le_iInf fun hβ1 => ?_
    rw [s.hB₃] at hβ
    obtain ⟨b', hb', rfl⟩ := hβ
    have hb'B : (b' : X) ∈ s.Bb := Subgroup.mem_subgroupOf.mp hb'
    have hb'1 : (b' : X) ≠ 1 := fun h =>
      hβ1 (by rw [show b' = 1 from Subtype.ext h, map_one])
    obtain ⟨b₀, hb₀, hb₀1⟩ := s.h_exists
    exact s.hGL (thetaT 3 s.Bb) s.hTW b' hb'B hb'1 (s.hTR _ hb'B hb'1)
      fun v hv K hK hne => (s.hNF K hK hne b₀ hb₀ hb₀1).2 hv
  intro hbot
  apply hTne
  rw [eq_bot_iff, ← hbot, thetaAlpha]
  exact hTle.trans le_sup_right

theorem faithfulConclusion (s : NormalSetup (X := X)) :
    thetaAlpha 3 ((autIn s.Ab s.K₁).subgroupOf (autIn ⊤ s.K₁)) ≠ ⊥ := by
  have : Finite (MulAut s.K₁) :=
    Finite.of_injective (fun σ : MulAut s.K₁ => (σ : s.K₁ → s.K₁))
      (fun σ τ h => MulEquiv.ext (congrFun h))
  refine thetaAlpha_ne_bot_of_le' (autIn_mono s.hAW) (autIn_mono le_top) s.hnormal ?_
  change thetaAlpha 3 (faithfulAutA s.Ab s.K₁) ≠ ⊥
  by_cases hTK : thetaT 3 s.Bb ≤ Subgroup.centralizer (s.K₁ : Set X)
  · exact thetaAlpha_ne_bot_of_thetaT_le s hTK
  · exact thetaAlpha_ne_bot_of_not_thetaT_le s hTK

end Certificates

end Faithful

open Faithful

theorem thetaAlpha_autIn_ne_bot_of_fixComm_faithful
    (hSz : KFacts.KPSz) (hθ : aschbacherSolvableCore 3 X = ⊥) (hKX : CFSG.IsKGroup X)
    {Ab Bb : Subgroup X} {cb : X} (hcbZ : cb ∈ Subgroup.center X) (hcb3 : orderOf cb = 3)
    (hBb : CFSG.Assembly.IsElemAbelian 3 Bb) (hBcard : Nat.card Bb = 9)
    (hBZ : Bb ⊓ Subgroup.zpowers cb = ⊥) (hABZ : Ab = Bb ⊔ Subgroup.zpowers cb)
    (hmaxX : ∀ u : X, u ^ 3 = 1 → u ∈ Subgroup.centralizer (Ab : Set X) → u ∈ Ab)
    (hAN : ∀ K : Subgroup X, IsComponent K → Ab ≤ Subgroup.normalizer (K : Set X))
    {K₁ : Subgroup X} (hK₁ : IsComponent K₁)
    (hfaith : ∀ x ∈ Ab, x ∈ Subgroup.centralizer (K₁ : Set X) ↔ x ∈ Subgroup.zpowers cb)
    (hQ : ¬ thetaAlpha 3 Bb ≤ Subgroup.centralizer (K₁ : Set X))
    (hKF : ∀ K : Subgroup X, IsComponent K → K ≠ K₁ →
      Bb ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
      ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range) :
    thetaAlpha 3 ((autIn Ab K₁).subgroupOf (autIn ⊤ K₁)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let h : FaithfulHypotheses (X := X) :=
    { hSz := hSz, hθ := hθ, hKX := hKX, Ab := Ab, Bb := Bb, cb := cb, K₁ := K₁,
      hcbZ := hcbZ, hcb3 := hcb3, hBb := hBb, hBcard := hBcard, hBZ := hBZ, hABZ := hABZ,
      hmaxX := hmaxX, hAN := hAN, hK₁ := hK₁, hfaith := hfaith, hQ := hQ, hKF := hKF }
  let s1 := basicSetup h
  let s2 := componentSetup s1
  let s3 := normalizerSetup s2
  let s4 := pieceSetup s3
  let s5 := pieceCentralizerSetup s4
  let s6 := centralizerSetup s5
  let s7 := actionSetup s6
  let s8 := commutatorSetup s7
  let s9 := transferSetup s8
  let s10 := autSetup s9
  let s11 := normalSetup s10
  exact faithfulConclusion s11

end Item422Proof

end CFSG.RankThree.PartTwo.Sec4
