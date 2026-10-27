module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qMod
public import CFSG.Quasithin.Background.A1cA133
public import CFSG.GroupTheory.SectionLemmas
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section


namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

private theorem exists_mem_commutator_mem_of_ne {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p H) {M Z : Subgroup H} [M.Normal] [Z.Normal]
    (hZM : Z ≤ M) (hMZ : M ≠ Z) :
    ∃ m ∈ M, m ∉ Z ∧ ∀ y : H, ⁅m, y⁆ ∈ Z := by
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  let M' : Subgroup (H ⧸ Z) := M.map π
  have hM'ne : M' ≠ ⊥ := by
    intro hbot
    apply hMZ
    have hle : M ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff (f := π) M).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    exact le_antisymm hle hZM
  haveI : M'.Normal := Subgroup.Normal.map (inferInstance : M.Normal) π
    (QuotientGroup.mk'_surjective Z)
  haveI : Group.IsNilpotent (H ⧸ Z) := (hp.to_quotient Z).isNilpotent
  have hInt : M' ⊓ Subgroup.center (H ⧸ Z) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hM'ne
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hInt
  obtain ⟨m, hmM, hmx⟩ := Subgroup.mem_map.mp x.2.1
  have hmx' : QuotientGroup.mk' Z m = (x : H ⧸ Z) := hmx
  have hmZ : m ∉ Z := by
    intro hmZ'
    apply hx1
    have hπ : QuotientGroup.mk' Z m = 1 :=
      (QuotientGroup.eq_one_iff (N := Z) (x := m)).mpr hmZ'
    exact Subtype.ext (hmx' ▸ hπ)
  refine ⟨m, hmM, hmZ, fun y => ?_⟩
  have hcomm : QuotientGroup.mk' Z (m * y) = QuotientGroup.mk' Z (y * m) := by
    rw [map_mul, map_mul, hmx']
    exact (Subgroup.mem_center_iff.mp x.2.2 (QuotientGroup.mk' Z y)).symm
  refine (QuotientGroup.eq_one_iff (N := Z) (x := ⁅m, y⁆)).mp ?_
  have h1 : QuotientGroup.mk' Z (m * y * m⁻¹ * y⁻¹) = 1 := by
    rw [show m * y * m⁻¹ * y⁻¹ = (m * y) * (y * m)⁻¹ by group]
    rw [map_mul, map_inv, hcomm, mul_inv_cancel]
  rwa [commutatorElement_def]

namespace U4qBase

variable {X : Setup Γ G}

theorem commutator_inf_Q0_ne_bot (B : X.U4qBase) : ⁅X.Q 0 ⊓ X.Q 1, X.Q 0⁆ ≠ ⊥ := by
  intro hcomm
  have hnab := B.commutator_Q0_ne_bot
  have hPle : X.Q 0 ⊓ X.Q 1 ≤ centerOf (X.Q 0) :=
    le_inf inf_le_left (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  obtain ⟨t, -, htv, -⟩ := X.exists_reflection_oTwoRes B.gen.hyp 0
  have ht1 : t • X.vert 1 = X.vert (-1) := by simpa using htv 1
  have ht0 : t • X.vert 0 = X.vert 0 := by simpa using htv 0
  have hQm1 : X.Q (-1) = conjSub t (X.Q 1) := X.Q_smul X ht1
  have hQ0 : X.Q 0 = conjSub t (X.Q 0) := X.Q_smul X ht0
  have hPm1 : X.Q 0 ⊓ X.Q (-1) ≤ centerOf (X.Q 0) := by
    have hconj : conjSub t (X.Q 0 ⊓ X.Q 1) ≤ centerOf (X.Q 0) := by
      calc conjSub t (X.Q 0 ⊓ X.Q 1) ≤ conjSub t (centerOf (X.Q 0)) :=
            conjSub_mono t hPle
        _ = centerOf (conjSub t (X.Q 0)) := (centerOf_conjSub t (X.Q 0)).symm
        _ = centerOf (X.Q 0) := by rw [← hQ0]
    have hinf : conjSub t (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q (-1) := by
      rw [conjSub_inf, ← hQ0, ← hQm1]
    rwa [hinf] at hconj
  have hQ0le : X.Q 0 ≤ centerOf (X.Q 0) := by
    conv_lhs => rw [B.Q0_eq_sup]
    exact sup_le hPle hPm1
  exact hnab (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hQ0le.trans inf_le_right))

theorem commutator_Q0_eq (B : X.U4qBase) : ⁅X.Q 0, X.Q 0⁆ = X.Z 0 := by
  have hnab := B.commutator_Q0_ne_bot
  have hKQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.K_le_Gi 0).trans (by simpa [Setup.Q] using
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hKU : X.K ≤ Subgroup.normalizer (⁅X.Q 0, X.Q 0⁆ : Subgroup G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k ⁅X.Q 0, X.Q 0⁆ = ⁅X.Q 0, X.Q 0⁆
    rw [← conjSub_commutator, CFSG.Quasithin.F7.conjSub_eq_of_mem_normalizer (hKQ0 hk)]
  have hUle : ⁅X.Q 0, X.Q 0⁆ ≤
      pCoreOf 2 (X.arcStab (-2) ((-2 : ℤ) + ((4 : ℕ) : ℤ))) := by
    have h' : (-2 : ℤ) + ((4 : ℕ) : ℤ) = 2 := by norm_num
    rw [h', ← B.Z0_eq_pCore]
    exact B.isElemSec_Q0.2.1
  have hEq := X.eq_of_le_pCoreOf_arcStab_r B.gen.hyp (U := ⁅X.Q 0, X.Q 0⁆) (a := -2) hKU hnab hUle
  have h' : (-2 : ℤ) + ((4 : ℕ) : ℤ) = 2 := by norm_num
  rw [h', ← B.Z0_eq_pCore] at hEq
  exact hEq

private theorem exists_mem_relCent_of_centerOf_ne (B : X.U4qBase)
    (hMne : centerOf (X.Q 0) ≠ X.Z 0) :
    ∃ m ∈ centerOf (X.Q 0), m ∉ X.Z 0 ∧
      m ∈ relCent (X.Q 0) (X.Z 0) (X.Q 1) := by
  have hZleM : X.Z 0 ≤ centerOf (X.Q 0) := X.Z_le_center 0
  have hG0Z : X.Gi 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (X.Z 0) = X.Z 0
    exact X.Z_normal 0 g hg
  have hQ1G0 : X.Q 1 ≤ X.Gi 0 := by
    have h := (X.Q_le_Gi_adj 1).trans
      (inf_le_left : X.Gi (1 - 1) ⊓ X.Gi (1 + 1) ≤ X.Gi (1 - 1))
    simpa using h
  have hDleG0 : X.Q 0 ⊔ X.Q 1 ≤ X.Gi 0 := sup_le (X.Q_le_Gi 0) hQ1G0
  have hDnormQ0 : X.Q 0 ⊔ X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hDleG0.trans (by simpa [Setup.Q] using
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hDnormM : X.Q 0 ⊔ X.Q 1 ≤ Subgroup.normalizer (centerOf (X.Q 0) : Set G) :=
    hDnormQ0.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (X.Q 0))
  have hDnormZ : X.Q 0 ⊔ X.Q 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) := hDleG0.trans hG0Z
  haveI hGi0fin : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI hDfin : Finite ↥(X.Q 0 ⊔ X.Q 1) :=
    Finite.of_injective (Subgroup.inclusion hDleG0) (Subgroup.inclusion_injective hDleG0)
  have hD2 : IsPGroup 2 ↥(X.Q 0 ⊔ X.Q 1) := by
    have hQ0 : IsPGroup 2 ↥(X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
    have hQ1 : IsPGroup 2 ↥(X.Q 1) := pCoreOf_isPGroup' (X.Gi 1)
    exact IsPGroup.to_sup_of_normal_left' hQ0 hQ1
      (hQ1G0.trans (by simpa [Setup.Q] using
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  let Msub : Subgroup ↥(X.Q 0 ⊔ X.Q 1) := (centerOf (X.Q 0)).subgroupOf (X.Q 0 ⊔ X.Q 1)
  let Zsub : Subgroup ↥(X.Q 0 ⊔ X.Q 1) := (X.Z 0).subgroupOf (X.Q 0 ⊔ X.Q 1)
  haveI hMsubN : Msub.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDnormM
  haveI hZsubN : Zsub.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDnormZ
  have hMsub_ne : Msub ≠ Zsub := by
    intro heq
    apply hMne
    have hMle : centerOf (X.Q 0) ≤ X.Q 0 ⊔ X.Q 1 := inf_le_left.trans le_sup_left
    have hZle : X.Z 0 ≤ X.Q 0 ⊔ X.Q 1 := (X.Z_le_Q 0).trans le_sup_left
    have h := congrArg (Subgroup.map (Subgroup.subtype (X.Q 0 ⊔ X.Q 1))) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hMle, Subgroup.map_subgroupOf_eq_of_le hZle] at h
  obtain ⟨m, hmM, hmZ, hmcomm⟩ :=
    exists_mem_commutator_mem_of_ne (p := 2) hD2 (Subgroup.subgroupOf_mono _ hZleM) hMsub_ne
  have hmrel : (m : G) ∈ relCent (X.Q 0) (X.Z 0) (X.Q 1) := by
    rw [mem_relCent ((X.Q_le_Gi 0).trans hG0Z)]
    refine ⟨(Subgroup.mem_subgroupOf.mp hmM).1, ?_⟩
    intro q hq
    have hqD : q ∈ X.Q 0 ⊔ X.Q 1 := (show X.Q 1 ≤ X.Q 0 ⊔ X.Q 1 from le_sup_right) hq
    have hmem := hmcomm ⟨q, hqD⟩
    have hmem' : ((⁅m, (⟨q, hqD⟩ : ↥(X.Q 0 ⊔ X.Q 1))⁆ : ↥(X.Q 0 ⊔ X.Q 1)) : G) ∈ X.Z 0 :=
      Subgroup.mem_subgroupOf.mp hmem
    have hcoe : ((⁅m, (⟨q, hqD⟩ : ↥(X.Q 0 ⊔ X.Q 1))⁆ : ↥(X.Q 0 ⊔ X.Q 1)) : G) = ⁅(m : G), q⁆ :=
      map_commutatorElement (Subgroup.subtype (X.Q 0 ⊔ X.Q 1)) m ⟨q, hqD⟩
    exact hcoe ▸ hmem'
  exact ⟨(m : G), Subgroup.mem_subgroupOf.mp hmM,
    fun h => hmZ (Subgroup.mem_subgroupOf.mpr h), hmrel⟩

private theorem false_of_centerOf_Q0_ne (B : X.U4qBase)
    (hC : relCent (X.Q 0) (X.Z 0) (X.Q 1) = X.Q 0 ⊓ X.Q 1)
    (hnab : ⁅X.Q 0, X.Q 0⁆ ≠ ⊥)
    (hY : centerOf (X.Q 0) ⊓ (X.Q 0 ⊓ X.Q 1) = X.Z 0)
    (hMne : centerOf (X.Q 0) ≠ X.Z 0) : False := by
  obtain ⟨m, hmM, hmZ, hmrel⟩ := exists_mem_relCent_of_centerOf_ne B hMne
  rw [hC] at hmrel
  exact hmZ (hY ▸ ⟨hmM, hmrel⟩)

theorem centerOf_Q0 (B : X.U4qBase) : centerOf (X.Q 0) = X.Z 0 := by
  have hK1 : ∀ Y : Subgroup G, X.Z 0 ≤ Y → Y ≤ X.Q 0 ⊓ X.Q 1 →
      X.K ≤ Subgroup.normalizer (Y : Set G) → Y = X.Z 0 ∨ Y = X.Q 0 ⊓ X.Q 1 :=
    fun _ hZY hY hK => B.eq_or_eq_of_normalizer_K hZY hY hK
  have hC := B.relCent_Q1
  have hnab := B.commutator_Q0_ne_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZleM : X.Z 0 ≤ centerOf (X.Q 0) := X.Z_le_center 0
  have hZleQ01 : X.Z 0 ≤ X.Q 0 ⊓ X.Q 1 :=
    le_inf (X.Z_le_Q 0) (B.Z0_le_Z1.trans (X.Z_le_Q 1))
  have hKQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.K_le_Gi 0).trans (by simpa [Setup.Q] using
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hKQ1 : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.K_le_Gi 1).trans (by simpa [Setup.Q] using
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hKM : X.K ≤ Subgroup.normalizer (centerOf (X.Q 0) : Set G) :=
    hKQ0.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (X.Q 0))
  have hKQ01 : X.K ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
    fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKQ0 hk, hKQ1 hk⟩
  have hKnormY : X.K ≤ Subgroup.normalizer
      ((centerOf (X.Q 0) ⊓ (X.Q 0 ⊓ X.Q 1) : Subgroup G) : Set G) :=
    fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKM hk, hKQ01 hk⟩
  have hY : centerOf (X.Q 0) ⊓ (X.Q 0 ⊓ X.Q 1) = X.Z 0 := by
    have hYle : centerOf (X.Q 0) ⊓ (X.Q 0 ⊓ X.Q 1) ≤ X.Q 0 ⊓ X.Q 1 := inf_le_right
    have hYge : X.Z 0 ≤ centerOf (X.Q 0) ⊓ (X.Q 0 ⊓ X.Q 1) := le_inf hZleM hZleQ01
    rcases hK1 _ hYge hYle hKnormY with h | h
    · exact h
    · exfalso
      have hcent : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.Q 0 : Set G) := by
        rw [← h]
        exact inf_le_left.trans inf_le_right
      exact commutator_inf_Q0_ne_bot B
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent)
  by_contra hMne
  exact false_of_centerOf_Q0_ne B hC hnab hY hMne

theorem isSpecialPGroup_Q0 (B : X.U4qBase) : IsSpecialPGroup 2 ↥(X.Q 0) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
  haveI : Fact (IsPGroup 2 ↥(X.Q 0)) := ⟨hP⟩
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  have hcent := centerOf_Q0 B
  have hcomm := commutator_Q0_eq B
  have hcenter : (Subgroup.center ↥(X.Q 0)).map (X.Q 0).subtype = X.Z 0 :=
    (CFSG.Quasithin.A1c.centerOf_eq_map_center (X.Q 0)).symm.trans hcent
  have hcomm_map : (_root_.commutator ↥(X.Q 0)).map (X.Q 0).subtype = X.Z 0 := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hcomm
  have hcomm_eq : _root_.commutator ↥(X.Q 0) = Subgroup.center ↥(X.Q 0) :=
    Subgroup.map_injective (X.Q 0).subtype_injective (hcomm_map.trans hcenter.symm)
  have hΦle : frattini ↥(X.Q 0) ≤ (X.Z 0).subgroupOf (X.Q 0) := by
    apply CFSG.GroupTheory.frattini_le_of_comm_pow hP
    · intro x y
      exact Subgroup.mem_subgroupOf.mpr
        (B.isElemSec_Q0.2.1 (Subgroup.commutator_mem_commutator x.2 y.2))
    · intro x
      exact Subgroup.mem_subgroupOf.mpr (B.isElemSec_Q0.2.2 (x : G) x.2)
  have hZleΦ : (X.Z 0).subgroupOf (X.Q 0) ≤ frattini ↥(X.Q 0) := by
    have hcommfr : _root_.commutator ↥(X.Q 0) ≤ frattini ↥(X.Q 0) :=
      CFSG.commutator_le_frattini_of_isPGroup (R := ↥(X.Q 0)) (p := 2)
    intro z hz
    have hzmap : (z : G) ∈ (_root_.commutator ↥(X.Q 0)).map (X.Q 0).subtype := by
      rw [hcomm_map]
      exact Subgroup.mem_subgroupOf.mp hz
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzmap
    exact (Subtype.ext hcz) ▸ hcommfr hc
  have hΦmap : (frattini ↥(X.Q 0)).map (X.Q 0).subtype = X.Z 0 := by
    apply le_antisymm
    · have h := Subgroup.map_mono (f := (X.Q 0).subtype) hΦle
      rwa [Subgroup.map_subgroupOf_eq_of_le (X.Z_le_Q 0)] at h
    · have h := Subgroup.map_mono (f := (X.Q 0).subtype) hZleΦ
      rwa [Subgroup.map_subgroupOf_eq_of_le (X.Z_le_Q 0)] at h
  have hΦ_eq : frattini ↥(X.Q 0) = Subgroup.center ↥(X.Q 0) :=
    Subgroup.map_injective (X.Q 0).subtype_injective (hΦmap.trans hcenter.symm)
  refine ⟨hP, Or.inr ⟨hcomm_eq, hΦ_eq, ?_⟩⟩
  intro z hz
  have hzZ : (z : G) ∈ X.Z 0 := by
    rw [← hcenter]
    exact Subgroup.mem_map_of_mem (X.Q 0).subtype hz
  have hsq := B.elem_Z0.2 (z : G) hzZ
  apply Subtype.ext
  simpa using hsq

theorem isSpecialPow_Q0 (B : X.U4qBase) (h : X.n 1 = 2 * X.n 0) :
    CFSG.Quasithin.IsSpecialPow 2 (2 ^ X.n 0) 2 ↥(pCoreOf 2 (X.L 0)) := by
  have hQ : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  rw [hQ]
  refine ⟨isSpecialPGroup_Q0 B, ?_, ?_⟩
  · rw [B.card_Q0, h, ← pow_mul]
    congr 1
    ring
  · calc Nat.card (Subgroup.center ↥(X.Q 0))
        = Nat.card ((Subgroup.center ↥(X.Q 0)).map (X.Q 0).subtype) :=
          (Subgroup.card_map_of_injective (X.Q 0).subtype_injective).symm
      _ = Nat.card (centerOf (X.Q 0)) := by
          rw [CFSG.Quasithin.A1c.centerOf_eq_map_center]
      _ = Nat.card (X.Z 0) := by rw [centerOf_Q0 B]
      _ = 2 ^ X.n 0 := B.card_Z0

theorem L0_le_centralizer (B : X.U4qBase) :
    X.L 0 ≤ Subgroup.centralizer
      (CFSG.Quasithin.centerOf (pCoreOf 2 (X.L 0)) : Set G) := by
  have hQ : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hcent := centerOf_Q0 B
  rw [hQ, hcent, B.Z0_eq]
  exact Subgroup.le_centralizer_iff.mpr inf_le_right

end U4qBase

end Setup

end CFSG.Quasithin.St84

end
