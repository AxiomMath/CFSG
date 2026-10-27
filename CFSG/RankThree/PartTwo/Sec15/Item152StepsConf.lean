module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Pt152 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y M X : Subgroup G) (c' : G)
    (L' : Subgroup G) : Prop where
  ctx : Ctx152 A LB Y M X
  omega : Subgroup.zpowers c' ∈ omegaA A
  mem_lA : L' ∈ lA A c'
  hj : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2)
  dec : deltaZero A LB X = pPrimeCoreOf 3 (deltaZero A LB X) ⊔
    deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))

structure DData152 (A X : Subgroup G) (c' : G) (L' : Subgroup G) (d : G) : Prop where
  mem_d : d ∈ A
  ne_d : d ≠ 1
  central_d : IsThreeCentralIn L' d
  cent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
    (Subgroup.closure {c', d} : Set G)

structure PData152 (A X : Subgroup G) (p : ℕ) (P : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  le_px : P ≤ X
  char_p : ∃ R : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype) ∧ P ≤ R ∧
      (P.subgroupOf R).Characteristic
  norm_p : A ≤ Subgroup.normalizer (P : Set G)
  type_p : (IsElementaryAbelian p ↥P ∧ Nat.card P = p ^ 2) ∨
    (CFSG.IsExtraspecialPGroup p ↥P ∧ Nat.card P = p ^ 3)
  cent_p : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X

structure TData152 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (X P T : Subgroup G) :
    Prop where
  mem_t : T ∈ scriptQPiStar A LB X (piOf 2)
  tp_eq : ((T ⊔ P : Subgroup G) : Set G) = (T : Set G) * (P : Set G)
  eq_comm_p : P = ⁅⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆, P⁆

structure KData152 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (P T K S : Subgroup G) :
    Prop where
  le_k : T ⊔ P ≤ K
  mem_k : K ∈ scriptY2 A
  le_ts : T ≤ S
  mem_sk : S ∈ scriptQPiStar A LB K (piOf 2)
  s_max : ∀ K' ∈ scriptY2 A, T ⊔ P ≤ K' → ∀ S' ∈ scriptQPiStar A LB K' (piOf 2), S ≤ S' →
    S' = S

@[expose] def Step152ConfD (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G), Pt152 A LB Y M X c' L' →
    ∃ d : G, DData152 A X c' L' d

@[expose] def Step152ConfP (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G), Pt152 A LB Y M X c' L' →
    ∃ (p : ℕ) (P : Subgroup G), PData152 A X p P

@[expose] def Step152ConfT (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → ∃ T : Subgroup G, TData152 A LB X P T

@[expose] def Step152ConfTheta (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype ∧
        ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal

@[expose] def Step152ConfPS (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
      ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
        ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) ∧
          generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S)

@[expose] def Step152ConfF (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → DData152 A X c' L' d → PData152 A X p P →
    TData152 A LB X P T → KData152 A LB P T K S →
    P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
    ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
    ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) →
    generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S) →
      P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype

@[expose] def Step152ConfW (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → DData152 A X c' L' d → PData152 A X p P →
    TData152 A LB X P T → KData152 A LB P T K S →
    P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
    ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
    ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) →
    generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S) →
    P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G)

theorem exists_kData152 {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M X P T : Subgroup G}
    (hM : M ∈ scriptY2 A) (hXM : X ≤ M) (hPX : P ≤ X)
    (hT : T ∈ scriptQPiStar A LB X (piOf 2)) :
    ∃ K S : Subgroup G, KData152 A LB P T K S := by
  set C : Set (Subgroup G) := {S' | ∃ K' ∈ scriptY2 A, T ⊔ P ≤ K' ∧
    S' ∈ scriptQPiStar A LB K' (piOf 2) ∧ T ≤ S'} with hC
  have hTX : T ≤ X := hT.prop.1.2
  have hTPM : T ⊔ P ≤ M := sup_le (hTX.trans hXM) (hPX.trans hXM)
  have hTM : T ∈ scriptQPi A LB M (piOf 2) := ⟨⟨hT.prop.1.1, hTX.trans hXM⟩, hT.prop.2⟩
  obtain ⟨SM, hTSM, hSM⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A LB M (piOf 2))) hTM
  have hSMC : SM ∈ C := ⟨M, hM, hTPM, hSM, hTSM⟩
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal (p := (· ∈ C)) hSMC
  obtain ⟨K, hK, hTPK, hSK, hTS⟩ := hS.prop
  refine ⟨K, S, ⟨hTPK, hK, hTS, hSK, fun K' hK' hTPK' S' hS' hSS' => ?_⟩⟩
  exact (hS.eq_of_le ⟨K', hK', hTPK', hS', hTS.trans hSS'⟩ hSS').symm

theorem step152Conf_of {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hD : Step152ConfD A LB) (hP : Step152ConfP A LB) (hT : Step152ConfT A LB)
    (hTheta : Step152ConfTheta A LB) (hPS : Step152ConfPS A LB) (hF : Step152ConfF A LB)
    (hW : Step152ConfW A LB) : Step152Conf A LB := by
  intro Y M X hctx c' L' hc' hL' hJ hdec
  have hpt : Pt152 A LB Y M X c' L' := ⟨hctx, hc', hL', hJ, hdec⟩
  obtain ⟨d, hd⟩ := hD Y M X c' L' hpt
  obtain ⟨p, P, hPd⟩ := hP Y M X c' L' hpt
  obtain ⟨T, hTd⟩ := hT Y M X c' L' p P hpt hPd
  obtain ⟨K, S, hKd⟩ := exists_kData152 hctx.mem_y2 (le_of_mem_thetaComponentsIn hctx.mem_comp)
    hPd.le_px hTd.mem_t
  obtain ⟨hθ, hn⟩ := hTheta Y M X c' L' p P T K S hpt hPd hTd hKd
  obtain ⟨hps, hfs⟩ := hPS Y M X c' L' p P T K S hpt hPd hTd hKd hθ hn
  have hfr := hF Y M X c' L' d p P T K S hpt hd hPd hTd hKd hθ hn hps hfs
  have hw := hW Y M X c' L' d p P T K S hpt hd hPd hTd hKd hθ hn hps hfs hfr
  exact ⟨d, p, P, T, K, S, hc', hL', hJ, hd.mem_d, hd.ne_d, hd.central_d, hd.cent, hPd.prime,
    hPd.odd, hPd.le_px, hPd.char_p, hPd.norm_p, hPd.type_p, hPd.cent_p, hTd.mem_t, hTd.tp_eq,
    hTd.eq_comm_p, hKd.le_k, hKd.mem_k, hKd.le_ts, hKd.mem_sk, hKd.s_max, hθ, hn, hps, hfs, hfr,
    hw⟩

@[expose] noncomputable def Step152ConfDR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfD A (lB A)

@[expose] noncomputable def Step152ConfPR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfP A (lB A)

@[expose] noncomputable def Step152ConfTR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfT A (lB A)

@[expose] noncomputable def Step152ConfThetaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfTheta A (lB A)

@[expose] noncomputable def Step152ConfPSR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfPS A (lB A)

@[expose] noncomputable def Step152ConfFR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfF A (lB A)

@[expose] noncomputable def Step152ConfWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfW A (lB A)

theorem step152ConfR_of (hD : Step152ConfDR) (hP : Step152ConfPR) (hT : Step152ConfTR)
    (hTheta : Step152ConfThetaR) (hPS : Step152ConfPSR) (hF : Step152ConfFR)
    (hW : Step152ConfWR) : Step152ConfR :=
  fun G _ _ A c L hR => step152Conf_of (hD G A c L hR) (hP G A c L hR) (hT G A c L hR)
    (hTheta G A c L hR) (hPS G A c L hR) (hF G A c L hR) (hW G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
