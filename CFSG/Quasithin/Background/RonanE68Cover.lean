module

public import CFSG.Quasithin.Background.RonanE68Defs
public import CFSG.Quasithin.Background.ONanE68LieDispatch

public section

namespace CFSG.Quasithin

namespace RonanE68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68 CFSG.Quasithin.E6
  CFSG.Quasithin.E6.E68Proof CFSG.QuasithinUnique.Vol2Native.L239

section Case

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem case1P_of_borel (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (hBX : borOf T V L ≤ M) (hXB : L ⊓ M ≤ borOf T V L)
    {n : ℕ} (hn : 2 ≤ n)
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L)
    (hcard : Nat.card (omegaCenter (sylowBar T V L)) = 2 ^ n)
    (hsing : ∃ x ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ z ∈ omegaCenter (sylowBar T V L), z ≠ 1 → ∀ w ∈ omegaCenter (sylowBar T V L), w ≠ 1 →
        ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w)
    (hmodel : ((2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel ↥L 2 n) ∨
      (1 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 n) ∨
      (n = 2 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 2 ∧
        IsPGroup 2 (Subgroup.center ↥L)))) :
    Case1P hV T M U L := by
  classical
  have hZ := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hXeq : L ⊓ M = borOf T V L := le_antisymm hXB (le_inf borOf_le_left hBX)
  obtain ⟨-, hres, hXN⟩ := sandwich h hU hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  obtain ⟨θ, hθ, hθZ⟩ := exists_theta hInn hmod h hU hL
  set P := sylowBar T V L with hP
  obtain ⟨x, hxN, htrans⟩ := hsing
  have hS := singerHyp_omegaCenter hquot hxN htrans
  have hBW := normalizer_le_normalizer_omegaCenter P
  have hWle : θ.range ≤ omegaCenter P := by
    rintro _ ⟨a, rfl⟩
    exact hθZ a
  obtain ⟨x₀, hx₀B, hx₀⟩ := exists_mem_borOf_of_mem_normalizer hZ hxN
  have hx₀X : x₀ ∈ L ⊓ M := by rw [hXeq]; exact hx₀B
  have hinvW : ∀ w ∈ θ.range, x * w * x⁻¹ ∈ θ.range := by
    intro w hw
    have := theta_range_invariant hVN θ hθ hZ0 hx₀X.1 (hXN hx₀X) w hw
    rwa [hx₀] at this
  have hne : θ.range ≠ ⊥ :=
    theta_range_ne_bot h.isPGroup_V hVN θ hθ hZ0 hperf (mQuot_ne_zero_of_not_le h hLM)
  have hWeq : θ.range = omegaCenter P := hS.eq_of_invariant hWle hinvW hne
  have hk : Nat.card θ.range = 2 ^ n := by rw [hWeq]; exact hcard
  have hm : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n :=
    mQuot_eq_of_card_range h.isPGroup_V hVN θ hθ hZ0 hperf hk
  have hodd := odd_card_autI hV hXN (hres.trans inf_le_right)
  have hW0 : omegaCenter P ≠ ⊥ := hWeq ▸ hne
  have hXB' : ∀ y ∈ L ⊓ M, ∃ b ∈ Subgroup.normalizer (P : Set (Bar.Qbar L)),
      ∀ w ∈ omegaCenter P, piG L y * w * (piG L y)⁻¹ = b * w * b⁻¹ := fun y hy =>
    ⟨piG L y, piG_mem_normalizer_of_mem_borOf hZ (hXeq ▸ hy), fun _ _ => rfl⟩
  obtain ⟨hcyc, hcard'⟩ := autI_cyclic_of_singerHyp hV hXN inf_le_left hodd hVN θ hθ hZ0 hperf
    hS hBW hWeq hW0 hx₀X hx₀ hXB'
  rw [hcard] at hcard'
  refine ⟨n, hmodel, hXeq, hcyc, hcard', hm, hm ▸ E3.mQuot_mono
    (le_inf_centralizer_component hU.1 hL), fun hn1 => ?_⟩
  have h3 : 3 ≤ Nat.card (omegaCenter P) := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hfix : ∀ v ∈ V, (∀ y ∈ L ⊓ M, y * v = v * y) → v ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    intro v hv hfv
    refine ⟨hv, ?_⟩
    have h1 := theta_comm_of_comm hVN θ hθ ⟨x₀, hx₀X.1⟩ ⟨v, hv⟩ (hfv x₀ hx₀X)
    have hxv : x * θ ⟨v, hv⟩ * x⁻¹ = θ ⟨v, hv⟩ := by
      rw [← hx₀, piG_of_mem hx₀X.1, h1]
      group
    have hmem : θ ⟨v, hv⟩ ∈ omegaCenter P := hWle ⟨⟨v, hv⟩, rfl⟩
    exact (theta_eq_one_iff hVN θ hθ hZ0 hperf ⟨v, hv⟩).1 (hS.eq_one_of_fixed h3 hmem hxv)
  have hXU : L ⊓ M ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := inf_le_left.trans (le_centralizer_inf_centralizer V L)
  obtain ⟨hd1, hd2⟩ := decomp_of_fixed hV inf_le_left hXN hXU hodd hfix
  refine ⟨by rw [inf_comm]; exact hd1, by rw [sup_comm]; exact hd2, ?_⟩
  exact mQuot_bot_eq_of_decomp h.isPGroup_V inf_le_left (le_sup_right.trans hd2.le)
    (fun a ha b hb => B2F.isElemAbelian_comm hV ha hb) hd1 hd2 hm

theorem out_of_coverP
    (hF : E68LieFacts) (hInn : Ch1.EvenLieAutInner)
    (h121 : Id2519.Prop121Three) (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L ∧ Subgroup.center ↥L ≠ ⊥ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2) :
    Case1P hV T M U L := by
  classical
  obtain ⟨hcp, -, hm⟩ := hc
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) := by
    have : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    rwa [← hcp] at this
  have hSyl : IsSylowTwoOf (pgOf T V L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  have hSm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar.Qbar L) .PSL 3 2 2 :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcp) hm
  have hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L) := sqtkCharTwoLie_of_psl_three (by omega) hSm
  have hQN := le_normalizer_of_nonIso h121 h hU hL (n := 2) le_rfl (Or.inl hm)
  have hrk : IsRankTwoEvenType L := Or.inr (Or.inr (Or.inr hm))
  have hCh := (rankTwoBorelFacts G L (pgOf T V L) hq hrk hSyl).1
  have hdata := hF.lin3 (Bar.Qbar L) 2 le_rfl hSm (sylowBar T V L)
    (isSylowTwoOf_sylowBar h hU hL hZ2)
  have hBX := borel_le_M_of_strict hInn hmod h hU hL hQN hZ2 hCh hdata.quot_comm hdata.order_three
  have hZ := center_le_sylow h hU hL hZ2
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hPg2 : IsPGroup 2 (pgOf T V L) := h.isPGroup_Q.to_le inf_le_left
  have hsolvB := isSolvable_borOf hZ hPg2 hdata.quot_comm
  have hCV := centralizer_le_borOf_of_root hInn hmod h hU hL hZ2 hdata.centralizer_root
  obtain ⟨-, hres, -⟩ := sandwich h hU hL
  have hPX : pgOf T V L ≤ L ⊓ M :=
    le_inf pgOf_le_left (inf_le_left.trans (inf_le_right.trans h.centralizer_le))
  have hXB : L ⊓ M ≤ borOf T V L :=
    inf_le_borOf_of_residual hZ hPX (fun hh => hLM (hh ▸ inf_le_right)) hBX hsolvB
      (hres.trans hCV) hdata.not_solvable
  exact case1P_of_borel hInn hmod hV h hU hL hZ2 hBX hXB (n := 2) le_rfl hdata.quot_comm
    hdata.card_root hdata.singer (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hSm, hZ2⟩))))

end Case

end RonanE68

end CFSG.Quasithin
