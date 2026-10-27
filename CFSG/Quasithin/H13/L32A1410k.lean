module

public import CFSG.Quasithin.H13.L32A1410j
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.H13.L32A1410g
public import CFSG.Quasithin.H13.L32A1410h

public section

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B Mat8Cert G5ACert
  L1442M L128P
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {b : Bool}

omit [Finite G] in
theorem mem_normalizer_centerOf {U : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) :
    x ∈ Subgroup.normalizer (centerOf U : Set G) := by
  have key : ∀ y ∈ Subgroup.normalizer (U : Set G), ∀ z ∈ centerOf U,
      y * z * y⁻¹ ∈ centerOf U := by
    intro y hy z hz
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hy z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) w).mp hw
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hw'
    calc w * (y * z * y⁻¹) = y * ((y⁻¹ * w * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * w * y)) * y⁻¹ := by rw [hc]
      _ = y * z * y⁻¹ * w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key x hx z, fun hz => ?_⟩
  have e : z = x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ := by group
  rw [e]
  exact key x⁻¹ (Subgroup.inv_mem _ hx) _ hz

namespace CtxA

variable (C : CtxA G T L V V₂ g D e b)
include C

theorem false_of_pCoreOf_ne_bot (h1332 : Stmt13_3_2) (h12213 : Stmt12_2_13)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hodd : FiveQuotientOddIndexSolvable) (hU : fsuU T V = pCoreOf 2 (l32nH T V))
    (h0 : pCoreOf 2 (preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T) ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := C.base.hyp.fsu.sylow
  have hK := C.base.hyp.fsu.qtke
  have hs := C.base.hyp.fsu.simple
  have hnab := C.base.hyp.fsu.nonabelian
  have hTG : T ≤ preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T := le_sup_right
  have hKG : preM D e KA5 ≤ preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T :=
    le_sup_left.trans le_sup_left
  have hIG : i128 T L V (fsuV1 T V) ≤ preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T :=
    le_sup_right.trans le_sup_left
  have hSyl := isSylowTwoOf_of_quasithinIsSylowTwo hT hTG
  obtain ⟨J, hJ, hKJ⟩ :=
    lemma_1_2_4_exists hK hs hnab h37 h39 h0 hSyl hKG (C.mem_cComp_K0 hU)
  let S : Sylow 2 G := hT.1.toSylow hT.2
  have hInH : InH (S : Subgroup G) (preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T) := ⟨hTG, h0⟩
  have hCT := charTwo_of_inH hK.2.1 S hInH
  have hR := isTwoReducedIn_conjClosure_of_sylowIn hTG hT.1 hSyl.2.2 hCT
    (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)
  have hVJ : ⁅conjClosure (fsuV1 T V) (preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T), J⁆ ≠ ⊥ := by
    obtain ⟨a, ha, k, hk, hka⟩ := C.exists_K0_moves
    intro hbot
    have hV2 : V₂ ≤ conjClosure (fsuV1 T V) (preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T) :=
      (V2_le_conjClosure h12213 C.base).trans
        (conjClosure_le fun h hh z hz => mem_conjClosure (hIG hh) hz)
    have hc := Subgroup.commutator_mem_commutator (hV2 ha) (hKJ hk)
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hc
    apply hka
    calc k * a * k⁻¹ = (a * k * a⁻¹ * k⁻¹)⁻¹ * a := by group
      _ = a := by rw [hc]; group
  have hJf : quasithinIsFaithfulLocal T J := by
    have htfae := lemma_1_2_10_of_a36 hK hs hnab h36 S hInH hJ
    have hex : ∃ W, IsTwoReducedIn (preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T) W ∧
        ⁅W, J⁆ ≠ ⊥ := ⟨_, hR, hVJ⟩
    exact (htfae.out 2 1).mp hex
  obtain ⟨h5, ⟨hTJ, -⟩, ⟨⟨VJ, hVJirr⟩, hVJall⟩, -⟩ := h1332 G T L C.base.hyp.hyp.h13 J hJf
  have hJq := (hVJall VJ hVJirr).2.2.1.quasisimple
  have hK1 : preM D e KA5 ≠ ⊥ := by
    intro h
    have := C.card_K0_gt
    rw [h, Subgroup.card_bot] at this
    omega
  have hKJeq : preM D e KA5 = J :=
    eq_of_le_of_perfect hodd hT hK1 (C.perfect_K0 hU) C.T_le_normalizer_K0 hKJ hTJ hJq h5 hJf.2.1
  have hN := normal_conjClosure_of_pCoreOf_ne_bot hK hs hnab h37 h38 h0 hSyl hJ
  have hcl : conjClosure J T = J :=
    le_antisymm (conjClosure_le fun t ht j hj => (Subgroup.mem_normalizer_iff.mp (hTJ ht) j).mp hj)
      (le_conjClosure J T)
  rw [hcl, ← hKJeq] at hN
  apply not_I2_le_H h12213 C.base
  intro x hx
  have hxK : x ∈ Subgroup.normalizer (preM D e KA5 : Set G) := hN (hIG hx)
  have hxU : x ∈ Subgroup.normalizer (fsuU T V : Set G) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxK
    rwa [C.pCoreOf_K0, ← hU] at this
  show x ∈ Subgroup.normalizer (fsuV1 T V : Set G)
  rw [← C.base.zU]
  exact mem_normalizer_centerOf hxU

end CtxA

end CFSG.Quasithin.H13.Q1410

end
