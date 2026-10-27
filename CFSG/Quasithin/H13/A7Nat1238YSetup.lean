module

public import CFSG.Quasithin.Background.FFStarOffenderMoving
public import CFSG.Quasithin.H13.A7Nat1238Ke
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

abbrev Ue (hyp : Hyp1223 G T L V) (e : G) : Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) (hyp.Gv e)

theorem T_le_Gv (hyp : Hyp1223 G T L V) {e : G} (heZ : e ∈ quasithinOmegaOneCenter T) :
    T ≤ hyp.Gv e := by
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  exact fun t ht => mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC heZ) t ht))

theorem isTwoReducedIn_Ue (hyp : Hyp1223 G T L V) {e : G} (he2 : orderOf e = 2)
    (heZ : e ∈ quasithinOmegaOneCenter T) : IsTwoReducedIn (hyp.Gv e) (Ue hyp e) := by
  obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
    ⟨_, IsPGroup.toSylow_coe hyp.sylow.1 hyp.sylow.2⟩
  have hTe : T ≤ hyp.Gv e := T_le_Gv hyp heZ
  have hH2 : pCoreOf 2 (hyp.Gv e) ≠ ⊥ :=
    pCoreOf_ne_bot_of_le_centralizer he2 (mem_centralizer_singleton_iff.2 rfl) le_rfl
  have hInH : InH (Ts : Subgroup G) (hyp.Gv e) := by
    rw [hTs]
    exact ⟨hTe, hH2⟩
  have hF := charTwo_of_inH hyp.qtke.2.1 Ts hInH
  exact isTwoReducedIn_conjClosure (hyp.Gv e) Ts (hTs ▸ hTe) hF (Z := quasithinOmegaOneCenter T)
    (by rw [hTs])

theorem pCoreOf_le_centralizer_of_isTwoReducedIn {H U K : Subgroup G} (hred : IsTwoReducedIn H U)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G)) :
    pCoreOf 2 K ≤ centralizer (U : Set G) := by
  refine hred.2.2.2 (pCoreOf 2 K) ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
    (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) fun d hd => ?_
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have h1 : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [h1]
  exact one_mem _

theorem alt5_noncomm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩, fun h => by
      have := congrArg Subtype.val h
      exact absurd this (by decide)⟩

theorem Kv_modO2_alt5
    (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS) :
    Nonempty (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e) ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, ⟨e5⟩⟩ := Kv_quasisimple hyp h he
  have hA : A134TypesCentral (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) :=
    Or.inl ⟨2, CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _
      ⟨e5⟩⟩
  have hZ2 := CFSG.Quasithin.mult2Fact _ hq hA
  have hZ : center (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) = ⊥ := by
    have hle : center (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) ≤
        CFSG.pCore 2 (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) :=
      le_sSup ⟨inferInstance, hZ2⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
    exact le_bot_iff.1 hle
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    e5⟩

theorem autOn_Kv_equiv
    (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS)
    {U : Subgroup G} (hKU : Kv hyp e ≤ normalizer (U : Set G))
    (hO2 : pCoreOf 2 (Kv hyp e) ≤ centralizer (U : Set G))
    (hnc : ¬ Kv hyp e ≤ centralizer (U : Set G)) :
    Nonempty (↥(autOn (Kv hyp e) U) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨eQ⟩ := Kv_modO2_alt5 hyp h he
  set K := Kv hyp e with hK
  set φ := autOnHom hKU with hφ
  have hP : CFSG.pCore 2 ↥K ≤ φ.ker := fun x hx =>
    (mem_ker_autOnHom hKU x).2 (hO2 (by rw [pCoreOf_eq_map_cfsgPCore]; exact ⟨x, hx, rfl⟩))
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := eQ.isSimpleGroup
  have hker : φ.ker = CFSG.pCore 2 ↥K := by
    refine le_antisymm ?_ hP
    have hN : (φ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
      φ.normal_ker.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (φ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with h1 | h1
    · intro x hx
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈
          φ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := ⟨x, hx, rfl⟩
      rw [h1, mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).1 hmem
    · exfalso
      apply hnc
      intro k hk
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ ∈
          φ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        rw [h1]
        exact mem_top _
      obtain ⟨x, hx, hxk⟩ := hmem
      have h2 : x⁻¹ * ⟨k, hk⟩ ∈ φ.ker := hP (QuotientGroup.eq.1 hxk)
      have h3 : (⟨k, hk⟩ : ↥K) ∈ φ.ker := by
        have := φ.ker.mul_mem hx h2
        rwa [mul_inv_cancel_left] at this
      exact (mem_ker_autOnHom hKU _).1 h3
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ (autOnHom_surjective hKU)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans eQ⟩

theorem exists_offender_moving {T L Y W : Subgroup G} [IsMulCommutative ↥W]
    (hT : IsSylowTwoOf T Y) (hTL : T ≤ normalizer (L : Set G)) (hred : IsTwoReducedIn Y W)
    (hLW : L ≤ normalizer (W : Set G)) (hsimp : IsSimpleGroup ↥(autOn L W))
    (hJ : L = ⁅L, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W :=
  CFSG.Quasithin.AutOn.exists_isFFStarOffender_moving hT hTL hred hLW hsimp hJ

omit [Finite G] in
theorem commutator_le_map_commV {U L : Subgroup G} [IsMulCommutative ↥U]
    (hLU : L ≤ normalizer (U : Set G)) : ⁅U, L⁆ ≤ (commV (autOn L U)).map U.subtype := by
  rw [Subgroup.commutator_le]
  intro u hu l hl
  have hmem : conjAct U ⟨l, hLU hl⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹ ∈ commV (autOn L U) :=
    Subgroup.subset_closure ⟨_, conjAct_mem_autOn hLU hl, ⟨u, hu⟩, rfl⟩
  refine ⟨(conjAct U ⟨l, hLU hl⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹)⁻¹,
    (commV (autOn L U)).inv_mem hmem, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, coe_conjAct_apply]
  rw [commutatorElement_def]
  group

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {y : G} (hA : y ∈ normalizer (A : Set G))
    (hB : y ∈ normalizer (B : Set G)) : y ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (A : Set G) → g ∈ normalizer (B : Set G) →
      ∀ w ∈ ⁅A, B⁆, g * w * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hgA hgB w hw
    have hle : ⁅A, B⁆ ≤ (⁅A, B⁆ : Subgroup G).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅A, B⁆
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.1 hgA a).1 ha)
        ((mem_normalizer_iff.1 hgB b).1 hb)
    exact hle hw
  rw [mem_normalizer_iff]
  intro w
  refine ⟨fun hw => key y hA hB w hw, fun hw => ?_⟩
  have := key y⁻¹ (inv_mem hA) (inv_mem hB) _ hw
  simpa [mul_assoc] using this

end CFSG.Quasithin.H13.A7
