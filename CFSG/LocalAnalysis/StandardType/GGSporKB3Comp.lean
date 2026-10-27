module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeAGlue
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeAssemble
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
import CFSG.Assembly.OpenBridges

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.HardMathSupport.Dickson.I271
  CFSG.Yardstones.Md0ec50421ce4

private theorem gkb3_comp_of_decomp {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Q H : Subgroup G} {s : G} (hsp : s ^ p = 1) (hqs : ∀ q ∈ Q, q * s = s * q) (hHQ : H ≤ Q)
    (hdecomp : ∀ g ∈ Subgroup.centralizer ({s} : Set G), ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q)
    (hHn : ∀ q ∈ Q, ∀ h ∈ H, q * h * q⁻¹ ∈ H) (hLq : CFSG.Open.IsQuasisimple ↥H)
    (hpL : p ∣ Nat.card ↥H) (hCQH : ∀ q ∈ Q, (∀ h ∈ H, q * h = h * q) → q = 1) :
    ∃ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({s} : Set G)) J := by
  have hQC : Q ≤ Subgroup.centralizer ({s} : Set G) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hLn : ∀ g ∈ Subgroup.centralizer ({s} : Set G), ∀ l ∈ H, g * l * g⁻¹ ∈ H := by
    intro g hg h hh
    obtain ⟨k, q, hq, rfl⟩ := hdecomp g hg
    have hqh := hHn q hq h hh
    have hc : Commute s (q * h * q⁻¹) := (hqs _ (hHQ hqh)).symm
    have hcomm' : s ^ k * (q * h * q⁻¹) = q * h * q⁻¹ * s ^ k := (hc.pow_left k).eq
    have e : s ^ k * q * h * (s ^ k * q)⁻¹ = q * h * q⁻¹ := by
      calc s ^ k * q * h * (s ^ k * q)⁻¹ = s ^ k * (q * h * q⁻¹) * (s ^ k)⁻¹ := by group
        _ = q * h * q⁻¹ := by rw [hcomm', mul_inv_cancel_right]
    rw [e]
    exact hqh
  have hcent : IsPGroup p ↥(Subgroup.centralizer ({s} : Set G) ⊓
      Subgroup.centralizer (H : Set G)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine IsPGroup.iff_orderOf.2 fun g => ?_
    obtain ⟨hgC, hgH⟩ := Subgroup.mem_inf.1 g.2
    obtain ⟨k, q, hq, hgq⟩ := hdecomp _ hgC
    have hq1 : q = 1 := by
      refine hCQH q hq fun h hh => ?_
      have hgh : (g : G) * h = h * g := (Subgroup.mem_centralizer_iff.1 hgH h hh).symm
      have hsh : s ^ k * h = h * s ^ k :=
        ((Commute.pow_left (show Commute s h from (hqs h (hHQ hh)).symm) k)).eq
      have : s ^ k * (q * h) = s ^ k * (h * q) := by
        calc s ^ k * (q * h) = (g : G) * h := by rw [hgq, mul_assoc]
          _ = h * g := hgh
          _ = h * s ^ k * q := by rw [hgq, mul_assoc]
          _ = s ^ k * (h * q) := by rw [← hsh, mul_assoc]
      exact mul_left_cancel this
    rw [hq1, mul_one] at hgq
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hgq, ← pow_mul, mul_comm, pow_mul, hsp, one_pow, Subgroup.coe_one]
    have hdvd : orderOf g ∣ p ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hgp)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨j, hj⟩
  have hcore := glaPPrimeCore_eq_bot_of_normal_quasisimple hp (hHQ.trans hQC) hLn hLq hpL hcent
  exact ⟨H, glaPComponent_of_normal_quasisimple (hHQ.trans hQC) hLn hLq hcore⟩

private theorem gkb3_comp_transport {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] (e : Q ≃* Q')
    {s : Q}
    (h : ∃ J : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({s} : Set Q)) J) :
    ∃ J' : Subgroup Q', GLAPComponent 3 (Subgroup.centralizer ({e s} : Set Q')) J' := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J.map e.toMonoidHom, ?_⟩
  rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e s]
  exact glaPComponent_map_equiv Nat.prime_three e hJ

private theorem gkb3_comp_Shat
    {v w : CVert} (hw : w ∈ sphereThree v)
    (hcard : Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat)) :
    ∃ J : Subgroup Shat,
      GLAPComponent 3 (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) J := by
  obtain ⟨hHQ, hHnorm, hcenter, hCQH⟩ : cnGroup v w ≤ vStab v ⊓ vStab w ∧
      ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal ∧
      Subgroup.center (cnGroup v w) = ⊥ ∧
      (∀ q ∈ vStab v ⊓ vStab w, (∀ h ∈ cnGroup v w, q * h = h * q) → q = 1) := by
    obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
    obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -, -, -, h14, -⟩ := hTT v w hw
    exact ⟨h1, h2, h10, h14⟩
  obtain ⟨hsimp, hcardH, hcomm⟩ : IsSimpleGroup (cnGroup v w) ∧
      Nat.card (cnGroup v w) = 64561751654400 ∧ commutator (cnGroup v w) = ⊤ := by
    obtain ⟨h1, -, h3, h4, -⟩ := native_three_transposition_group_simple v w hw
    exact ⟨h1, h3, h4⟩
  have h3 : orderOf (clabel v * clabel w) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  have hd2 : clabelS v * clabelS v = 1 := by
    have := pow_orderOf_eq_one (clabelS v)
    rwa [orderOf_clabelS, sq] at this
  have he2 : clabelS w * clabelS w = 1 := by
    have := pow_orderOf_eq_one (clabelS w)
    rwa [orderOf_clabelS, sq] at this
  have hso : orderOf (clabelS v * clabelS w) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h3
  obtain ⟨s, hs⟩ : ∃ s : Shat, s = clabelS v * clabelS w := ⟨_, rfl⟩
  rw [← hs] at hcard hso ⊢
  have hs3 : s * s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hso, pow_three'] at this
  have hqs : ∀ q ∈ vStab v ⊓ vStab w, q * s = s * q := by
    intro q hq
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).1
    have h2 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).2
    rw [hs]
    calc q * (clabelS v * clabelS w) = q * clabelS v * clabelS w := by rw [mul_assoc]
      _ = clabelS v * q * clabelS w := by rw [h1]
      _ = clabelS v * (q * clabelS w) := by rw [mul_assoc]
      _ = clabelS v * (clabelS w * q) := by rw [h2]
      _ = clabelS v * clabelS w * q := by rw [mul_assoc]
  have hQC : vStab v ⊓ vStab w ≤ Subgroup.centralizer ({s} : Set Shat) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hsQ : s ∉ vStab v ⊓ vStab w := by
    intro hsQ
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hsQ).1
    rw [hs] at h1
    have h2 : s * s = 1 := by
      rw [hs]
      calc clabelS v * clabelS w * (clabelS v * clabelS w)
          = clabelS v * clabelS w * clabelS v * clabelS w := by simp only [mul_assoc]
        _ = clabelS v * (clabelS v * clabelS w) * clabelS w := by rw [h1]
        _ = 1 := by rw [← mul_assoc, hd2, one_mul, he2]
    have h4 : s = 1 := by
      calc s = s * s * s * (s * s)⁻¹ := by group
        _ = 1 := by rw [hs3, h2, inv_one, one_mul]
    rw [h4, orderOf_one] at hso
    exact absurd hso (by norm_num)
  have hdecomp := mem_pow_mul_of_card_le (Subgroup.mem_centralizer_singleton_iff.2 rfl) hQC hs3
    hsQ hcard
  have hHn : ∀ q ∈ vStab v ⊓ vStab w, ∀ h ∈ cnGroup v w, q * h * q⁻¹ ∈ cnGroup v w := by
    intro q hq h hh
    have := hHnorm.conj_mem ⟨h, hHQ hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hLq : CFSG.Open.IsQuasisimple ↥(cnGroup v w) :=
    ⟨hcomm, MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot)⟩
  have hpL : 3 ∣ Nat.card ↥(cnGroup v w) := by rw [hcardH]; norm_num
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  exact gkb3_comp_of_decomp Nat.prime_three hs3' hqs hHQ hdecomp hHn hLq hpL hCQH

theorem ggSporK_bThree_component_of_inverted
    {s d : NativeSporadic.B} (hs : orderOf s = 3)
    (hd : BabyInv 0 d) (hinv : d * s * d⁻¹ = s⁻¹) :
    ∃ J : Subgroup NativeSporadic.B,
      LargeEvenPComponent 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) J := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨v, w, hw, hvw⟩ := tabBThree_typeThree_of_inverted hs hd hinv
  have hQ := (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2
  have hcard : Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat) := by
    rw [hQ, ← hvw, tabBThree_card_centralizer_babyToShat]
    exact (tabBThreeACard_thm s hs ⟨d, hd, hinv⟩).trans (by norm_num)
  obtain ⟨J, hJ⟩ := gkb3_comp_Shat hw hcard
  have h1 : ∃ J' : Subgroup NativeSporadic.B, GLAPComponent 3 (Subgroup.centralizer
      ({babyToShat.symm (clabelS v * clabelS w)} : Set NativeSporadic.B)) J' := by
    with_reducible_and_instances exact gkb3_comp_transport babyToShat.symm ⟨J, hJ⟩
  rw [← hvw, MulEquiv.symm_apply_apply] at h1
  obtain ⟨J', hJ'⟩ := h1
  exact ⟨J', (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 _ _).2 hJ'⟩

end CFSG.StandardType.SporadicShape
