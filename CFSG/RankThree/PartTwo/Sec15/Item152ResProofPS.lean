module

public import CFSG.RankThree.PartTwo.Sec15.Item152ResProofT
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofPS
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofEnd
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofF
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Proof152ResPS

open Proof152ResT

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coe_sup_eq_mul_comm {H K : Subgroup G}
    (h : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G)) :
    ((K ⊔ H : Subgroup G) : Set G) = (K : Set G) * (H : Set G) := by
  ext x
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ ((H ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact inv_mem hx
    rw [h] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
    refine Set.mem_mul.mpr ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, ?_⟩
    rw [← mul_inv_rev, hab, inv_inv]
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem le_pCoreOf_of_le {P S V₀ : Subgroup G} (hS : IsPGroup 2 S)
    (hPS : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G)) (hV₀S : V₀ ≤ S)
    (hPV₀ : P ≤ Subgroup.normalizer (V₀ : Set G)) : V₀ ≤ CFSG.Open.pCoreOf 2 (P ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP : ((P ⊔ S : Subgroup G) : Set G) = (S : Set G) * (P : Set G) := by
    rw [sup_comm]
    exact coe_sup_eq_mul_comm hPS
  set N₁ : Subgroup G := ⨅ g : ↥(P ⊔ S), S.comap (MulAut.conj (g : G)).toMonoidHom with hN₁
  have hmem : ∀ x, x ∈ N₁ ↔ ∀ g ∈ P ⊔ S, g * x * g⁻¹ ∈ S := fun x => by
    rw [hN₁, Subgroup.mem_iInf]
    constructor
    · intro hx g hg
      have := hx ⟨g, hg⟩
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    · intro hx g
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using hx g g.2
  have hN₁S : N₁ ≤ S := fun x hx => by
    simpa using (hmem x).mp hx 1 (one_mem _)
  have hV₀N₁ : V₀ ≤ N₁ := by
    intro v hv
    refine (hmem v).mpr fun g hg => ?_
    have hg' : g ∈ ((P ⊔ S : Subgroup G) : Set G) := hg
    rw [hSP] at hg'
    obtain ⟨s, hs, u, hu, rfl⟩ := hg'
    have huv : u * v * u⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp (hPV₀ hu) v).mp hv
    rw [show s * u * v * (s * u)⁻¹ = s * (u * v * u⁻¹) * s⁻¹ by group]
    exact mul_mem (mul_mem hs (hV₀S huv)) (inv_mem hs)
  have hN₁n : P ⊔ S ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro h hh
    refine mem_normalizer_of_conj_mem fun x hx => (hmem _).mpr fun g hg => ?_
    rw [show g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ by group]
    exact (hmem x).mp hx (g * h) (mul_mem hg hh)
  exact hV₀N₁.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hN₁S.trans le_sup_right) hN₁n (hS.to_le hN₁S))

theorem inf_centralizer_commutator_eq_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X P : Subgroup G}
    (hPX : P ≤ X) (hP : IsPGroup p P) (hX : IsCharacteristicP 2 ↥X) :
    P ⊓ Subgroup.centralizer ((⁅CFSG.Open.pCoreOf 2 X, P⁆ : Subgroup G) : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hO
  set C := P ⊓ Subgroup.centralizer ((⁅O, P⁆ : Subgroup G) : Set G) with hC
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hCp : IsPGroup p C := hP.to_le inf_le_left
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := (inf_le_left.trans hPX).trans hXO
  have hOp : ¬ p ∣ Nat.card O := by
    intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO2
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    p Fact.out C O hCp hOp hCO
  have hOC : ⁅O, C⁆ ≤ O ⊓ Subgroup.centralizer (C : Set G) := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hCO) ?_
    have h1 : ⁅O, C⁆ ≤ ⁅O, P⁆ := Subgroup.commutator_mono le_rfl inf_le_left
    exact h1.trans (Subgroup.le_centralizer_iff.mp inf_le_right)
  have hOcent : O ≤ Subgroup.centralizer (C : Set G) := by
    rw [hfac]
    exact sup_le (hOC.trans inf_le_right) inf_le_right
  rw [eq_bot_iff]
  intro x hx
  have hxX : x ∈ X := hPX hx.1
  have hxC : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.centralizer ((CFSG.pCore 2 ↥X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : (o : G) ∈ O := by
      rw [hO, CFSG.Open.pCoreOf]
      exact ⟨o, ho, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hOcent ho') x hx).symm
  have hxO : x ∈ O := by
    rw [hO, CFSG.Open.pCoreOf]
    exact ⟨_, hX hxC, rfl⟩
  have h := Proof152ConfA.inf_eq_bot_of_isPGroup hp2 hO2 hP
  have hx' : x ∈ O ⊓ P := ⟨hxO, hx.1⟩
  rw [h] at hx'
  exact hx'

variable {A : Subgroup G}

theorem mem_scriptQ_of_tData (hA : Late.IsE27 A) (h146 : Item146 A (lB A)) {X P T : Subgroup G}
    {p : ℕ} (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX0 : X = deltaZero A (lB A) X)
    (h147 : ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X))
    (hPd : PData152 A X p P) (hp3 : p ≠ 3) (hTd : TData152 A (lB A) X P T) :
    P ∈ scriptQ A (lB A) := by
  have : Fact p.Prime := ⟨hPd.prime⟩
  have hK := Sec17.Proof17Q0.pPrimeCoreOf_mem_invariantPiSubgroups hAX
  have hPO : P ≤ pPrimeCoreOf 3 X := by
    refine (le_oTwoP_of_pData hPd.char_p).trans
      (le_pPrimeCoreOf (Subgroup.map_subtype_le _) (le_normalizer_oTwoP p X) ?_)
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mp
        (isPiSubgroup_oTwoP (T := ↥X) hPd.prime hp3))
  have hTX : T ≤ X := hTd.mem_t.prop.1.2
  have hAN : A ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) :
      Set G) :=
    Late.le_normalizer_inf hTd.mem_t.prop.1.1.1.2.2
      (hPd.norm_p.trans (Sec6.normalizer_le_normalizer_normalizer P))
  have hUle : ⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆ ≤ T ⊓ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hle : P ≤ delta A (lB A) (pPrimeCoreOf 3 X) :=
    calc P = ⁅⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆, P⁆ := hTd.eq_comm_p
      _ ≤ ⁅X, pPrimeCoreOf 3 X⁆ :=
          Subgroup.commutator_mono (hUle.trans (inf_le_left.trans hTX)) hPO
      _ = ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ :=
          congrArg (fun Z => ⁅Z, pPrimeCoreOf 3 X⁆) hX0
      _ ≤ _ := h147
  exact mem_scriptQ_of_le (delta_mem_scriptQ hA h146 hK) hle hPd.norm_p

theorem coe_sup_eq_mul_of_mem_scriptQ (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {P S K : Subgroup G} {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hP : IsPGroup p P)
    (hPQ : P ∈ scriptQ A (lB A)) (hPK : P ≤ K) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hS : S ∈ scriptQPiStar A (lB A) K (piOf 2))
    (hn : ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal) :
    ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 K with hR
  set Z := P ⊔ S with hZ
  have hSK : S ≤ K := hS.prop.1.2
  have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hRK : R ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hKPR : K ≤ Subgroup.normalizer ((P ⊔ R : Subgroup G) : Set G) :=
    Sec4.le_normalizer_of_subgroupOf_normal (sup_le hPK hRK) hn
  have hZK : Z ≤ K := sup_le hPK hSK
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := Sec14.le_normalizer_sup hPQ.1.2.2 hSQ.1.2.2
  have hP3 : IsPiSubgroup (piCompl 3) P := isPiSubgroup_piCompl_three_of_isPGroup Fact.out hp3 hP
  have hR3 : IsPiSubgroup (piCompl 3) R :=
    isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num) hR2
  have hS3 : IsPiSubgroup (piCompl 3) S :=
    isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num) hS2
  have hPR3 : IsPiSubgroup (piCompl 3) (P ⊔ R) :=
    isPiSubgroup_piCompl_sup hP3 hR3 (hPK.trans hKR)
  have hSPR3 : IsPiSubgroup (piCompl 3) (S ⊔ (P ⊔ R)) :=
    isPiSubgroup_piCompl_sup hS3 hPR3 (hSK.trans hKPR)
  have hZ3 : IsPiSubgroup (piCompl 3) Z :=
    isPiSubgroup_piCompl_of_le hSPR3 (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
  have hZQ : Z ∈ scriptQ A (lB A) := by
    have hΔ := delta_mem_scriptQ hA h146 (⟨le_top, hZ3, hAZ⟩ :
      Z ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    have heq : delta A (lB A) Z = Z :=
      le_antisymm (delta_le Z) (sup_le (le_delta hPQ le_sup_left) (le_delta hSQ le_sup_right))
    rwa [heq] at hΔ
  set V := Z ⊓ R with hV
  have hZV : Z ≤ Subgroup.normalizer (V : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hZK.trans hKR)
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := Late.le_normalizer_inf hAZ hAR
  have hSV : S ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hZV
  have hV2 : IsPGroup 2 V := hR2.to_le inf_le_right
  have hVS : V ≤ S := by
    have hSVQ : S ⊔ V ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hZQ (sup_le le_sup_right inf_le_left) (Sec14.le_normalizer_sup
        hSQ.1.2.2 hAV)
    have hmem : S ⊔ V ∈ scriptQPi A (lB A) K (piOf 2) :=
      ⟨⟨hSVQ, sup_le hSK (inf_le_right.trans hRK)⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_sup_of_normal_right' hV2 hSV)⟩
    exact le_sup_right.trans (hS.2 hmem le_sup_left)
  have hPRs : ((P ⊔ R : Subgroup G) : Set G) = (P : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P R (hPK.trans hKR)
  have hPVeq : P ⊔ V = Z ⊓ (P ⊔ R) := by
    refine le_antisymm (sup_le (le_inf le_sup_left le_sup_left)
      (inf_le_inf_left Z le_sup_right)) ?_
    rintro x ⟨hxZ, hxPR⟩
    have hx' : x ∈ ((P ⊔ R : Subgroup G) : Set G) := hxPR
    rw [hPRs] at hx'
    obtain ⟨u, hu, r, hr, rfl⟩ := hx'
    have hrZ : r ∈ Z := by
      have : r = u⁻¹ * (u * r) := by group
      rw [this]
      exact mul_mem (inv_mem (Subgroup.mem_sup_left hu)) hxZ
    exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hrZ, hr⟩)
  have hSN : S ≤ Subgroup.normalizer ((P ⊔ V : Subgroup G) : Set G) := by
    rw [hPVeq]
    exact le_sup_right.trans (Late.le_normalizer_inf Subgroup.le_normalizer (hZK.trans hKPR))
  have h := coe_sup_eq_mul_of_le_normalizer hVS (le_sup_left.trans hZV) hSN
  exact coe_sup_eq_mul_comm h

theorem inf_centralizer_pCoreOf_eq_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X P S : Subgroup G}
    (hPX : P ≤ X) (hP : IsPGroup p P) (hX : IsCharacteristicP 2 ↥X) (hS : IsPGroup 2 S)
    (hWS : ⁅CFSG.Open.pCoreOf 2 X, X⁆ ≤ S)
    (hPS : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G)) :
    P ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (P ⊔ S) : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hO
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hV₀S : ⁅O, P⁆ ≤ S := (Subgroup.commutator_mono le_rfl hPX).trans hWS
  have hPV₀ : P ≤ Subgroup.normalizer ((⁅O, P⁆ : Subgroup G) : Set G) :=
    Sec14.le_normalizer_commutator (A := P) (hPX.trans hXO) Subgroup.le_normalizer
  have hV₀ := le_pCoreOf_of_le hS hPS hV₀S hPV₀
  rw [eq_bot_iff, ← inf_centralizer_commutator_eq_bot hp2 hPX hP hX]
  exact inf_le_inf_left P (Subgroup.centralizer_le hV₀)

end Proof152ResPS

open Proof152ResT Proof152ResPS

variable {G : Type} [Group G] [Finite G]

theorem facts_of_ctx152 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hLB : LB = lB A) (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X))
    {Y M X : Subgroup G} (hctx : Ctx152 A LB Y M X) :
    X = deltaZero A (lB A) X ∧
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X) ∧
      ⁅CFSG.Open.pCoreOf 2 X, X⁆ ∈ scriptQ A (lB A) := by
  subst hLB
  have hX := hctx.mem_comp
  have hX3 : X = oPrimeResidualOf 3 X :=
    eq_oPrimeResidualOf_of_le (isPerfect_of_mem_thetaComponentsIn hX)
      (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hctx.le_x hctx.mem_y4.2.1
      (isPerfect_of_mem_scriptY4 hctx.mem_y4) (ne_bot_of_mem_scriptY4 hctx.mem_y4)
  have hX0 : X = deltaZero A (lB A) X :=
    eq_deltaZero_of_bot hA hbot hctx.norm_x hX3 hctx.delta_x
  have hXtop : X ≠ ⊤ := fun h' =>
    hctx.mem_y2.1.1 (top_le_iff.mp (h' ▸ le_of_mem_thetaComponentsIn hX))
  have h147X := h147 X ⟨hXtop, hctx.norm_x⟩ hctx.delta_x
  exact ⟨hX0, h147X, commutator_pCoreOf_mem_scriptQ_of_le hA h146 hctx.norm_x hX0 h147X⟩

theorem step152ConfPSProd_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X)) :
    Step152ConfPSProd A (lB A) := by
  intro Y M X c' L' p P T K S hpt hPd hTd hKd hθ hn
  have hA : Late.IsE27 A := h.isE27
  have : Fact p.Prime := ⟨hPd.prime⟩
  have hp3 := ne_three_of_le_theta hPd hθ
  obtain ⟨hX0, h147X, -⟩ := facts_of_ctx152 rfl hA h146 hbot h147 hpt.ctx
  have hPQ := mem_scriptQ_of_tData hA h146 hpt.ctx.norm_x hX0 h147X hPd hp3 hTd
  exact coe_sup_eq_mul_of_mem_scriptQ hA h146 hp3 (isPGroup_of_pData hPd) hPQ
    ((le_sup_right : P ≤ T ⊔ P).trans hKd.le_k) hKd.mem_k.1.2 hKd.mem_sk hn

theorem step152ConfPSFaith_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X)) :
    Step152ConfPSFaith A (lB A) := by
  intro Y M X c' L' p P T K S hpt hPd hTd hKd _ _ hps
  have hA : Late.IsE27 A := h.isE27
  have : Fact p.Prime := ⟨hPd.prime⟩
  obtain ⟨-, -, hW⟩ := facts_of_ctx152 rfl hA h146 hbot h147 hpt.ctx
  have hWT := commutator_le_of_mem_scriptQPiStar hA h146 hW hTd.mem_t
  exact inf_centralizer_pCoreOf_eq_bot hPd.odd hPd.le_px (isPGroup_of_pData hPd)
    (isCharacteristicP_of_mem_thetaComponentsIn hpt.ctx.fstar hpt.ctx.mem_comp)
    (isPGroup_of_mem_scriptQPi Nat.prime_two hKd.mem_sk.prop) (hWT.trans hKd.le_ts) hps

theorem step152ConfPSProd_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) : Step152ConfPSProd A (lB A) :=
  step152ConfPSProd_of_le h h146 hbot fun _ hXY hXΔ =>
    commutator_le_delta_of_eq_delta h.isE27 h1444 h146 hXY.2 hXΔ

theorem step152ConfPSFaith_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) : Step152ConfPSFaith A (lB A) :=
  step152ConfPSFaith_of_le h h146 hbot fun _ hXY hXΔ =>
    commutator_le_delta_of_eq_delta h.isE27 h1444 h146 hXY.2 hXΔ

theorem step152ConfPSProdR_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) :
    Step152ConfPSProdR :=
  fun G _ _ A c L hR => step152ConfPSProd_of hR.toSec14Std (h1444 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std)

theorem step152ConfPSFaithR_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) :
    Step152ConfPSFaithR :=
  fun G _ _ A c L hR => step152ConfPSFaith_of hR.toSec14Std (h1444 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std)

theorem step152ConfPSR_of_items (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) : Step152ConfPSR :=
  step152ConfPSR_of (step152ConfPSProdR_of h1444 h146 hbot) (step152ConfPSFaithR_of h1444 h146 hbot)

end CFSG.RankThree.PartTwo.Sec15
