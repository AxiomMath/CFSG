module

public import CFSG.RankThree.GF2n.Stroth80.Sec8SectionOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec8SecComm
public import CFSG.RankThree.GF2n.Stroth80.Sec8CommNorm
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem sec8_m_eq_two_of_pow_le {m a q : ℕ} (hm : 2 ≤ m) (ha : 1 ≤ a) (hq : 2 ≤ q)
    (h : q ^ (2 ^ m * a + 1) ≤ q ^ (2 * m + 1)) : m = 2 := by
  have h1 : 2 ^ m * a + 1 ≤ 2 * m + 1 := (Nat.pow_le_pow_iff_right hq).mp h
  have h2 : 2 ^ m ≤ 2 * m := by
    have := Nat.le_mul_of_pos_right (2 ^ m) ha
    omega
  by_contra hne
  have h3 : 3 ≤ m := by omega
  have key : ∀ k : ℕ, 3 ≤ k → 2 * k < 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have := key m h3
  omega

section

variable {G : Type} [Group G]

theorem sec8_comm_mem_of_conj_mem {S : Subgroup G} {x w : G} (hxw : x * w * x⁻¹ ∈ S)
    (hw : w ∈ S) : ⁅x, w⁆ ∈ S := by
  rw [commutatorElement_def]
  exact S.mul_mem hxw (S.inv_mem hw)

theorem sec8_comm_mem_Ut {Q Z : Subgroup G} {x w : G} (hw : w ∈ Q) : ⁅x, w⁆ ∈ Ut Q Z x := by
  have h1 : ⁅w, x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ :=
    Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers x)
  have h2 : ⁅x, w⁆ = ⁅w, x⁆⁻¹ := (commutatorElement_inv w x).symm
  rw [h2]
  exact Subgroup.mem_sup_left (Subgroup.inv_mem _ h1)

end

variable {G : Type} [Group G] [Finite G]

theorem sec8TypeCount_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) : Sec8TypeCountStatement := by
  intro G _ _ M Q Z B hc n t hs r hr _ g hgM hxt hxN hxcent hxW
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨m, hm2, hmSp⟩ := hs.sp
  suffices hm : m = 2 by
    subst hm
    exact hmSp
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, -⟩ := sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := sec8_Z_le_V1 hc t r
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs r hr ρ hρ
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8W1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).2 hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8V1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).1 hy
  have h53b := h53.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53c := h53.2.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hsec : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    SecHyp.of_isOppDecomp h53c hP hI
  have hxV : g * t * g⁻¹ ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    sec8_normV_of_comm hc hxM hxt
  have hVx : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
    fun v hv => hxcent v (hVV₁ hv)
  have hxc : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * (g * t * g⁻¹) * ρ⁻¹ * (g * t * g⁻¹)⁻¹ ∈ hc.CN t :=
    fun ρ hρ => sec8_comm_mem_CN hc ht hxM hxt hVx hρ
  have hxWn : g * t * g⁻¹ ∈ Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) :=
    sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 hxM) hxN
  have hxP : ∀ y ∈ Sec8W1 M Q Z B t r, (g * t * g⁻¹) * y * (g * t * g⁻¹)⁻¹ ∈
      Sec8W1 M Q Z B t r := fun y hy => (Subgroup.mem_normalizer_iff.mp hxWn y).mp hy
  obtain ⟨U, hIU, hUP, hUinv, hUx, hUcov⟩ :=
    sec8_exists_comm_section hsec hxP hxc h53b.2
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem ht hrR
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  obtain ⟨-, a, ha⟩ := sec8_invariant_section (R := Rt M (LB M Q B) t) (N := hc.CN t)
    (P := Sec8W1 M Q Z B t r) (I := Sec8V1 M Q Z B t r) (L₁ := LB M Q B)
    (L₂ := LB M Q (conjSubgroup r B))
    (A₁ := (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (A₂ := (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) (U := U) φ
    hpts.range (by omega) hpts.ker hP hI h53b.2 h53c hLR hLCR hpts.uu' hpts.u_ne_zero hpts.hL hL2
    (fun y hy => hQN (hc.sq_mem_Q_of_mem_LB hy)) hrR (hc.LB_conj hrM).symm hIU hUP hUinv
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨w₀, hw₀, hw₀V⟩ := hxW
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h00 : a = 0 := by omega
    rw [h00, mul_zero, pow_zero, mul_one] at ha
    have hUeq : Sec8V1 M Q Z B t r = U := Subgroup.eq_of_le_of_card_ge hIU ha.le
    exact hw₀V (hUeq ▸ hUx w₀ hw₀)
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t hs5 (Or.inl hs.spNat)).1
  have hVg : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * t * g⁻¹) :=
    sec8_conj_V_eq_Ut hc hV hgM
  have hZg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    (hc.conj_Z_eq hgM).symm.le.trans (Subgroup.map_mono sec39_Z_le_Vt)
  have hZT : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r :=
    le_inf hZg (sec8_Z_le_W1 hc t r)
  have hUT : ∀ y ∈ U, ∃ w ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r,
      y * w⁻¹ ∈ Sec8V1 M Q Z B t r := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hUcov y hy
    refine ⟨⁅g * t * g⁻¹, w⁆, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hyw⟩
    · rw [hVg]
      exact sec8_comm_mem_Ut (sec8_W1_le_Q M Q Z B t r hw)
    · exact sec8_comm_mem_of_conj_mem (hxP w hw) hw
  obtain ⟨Mo, iMo, iAct, κ, hκ⟩ := exists_sectionModule hsec
  have hcard := sec8_card_le_of_comm_section hκ hIU hUP hZV₁ inf_le_right hZT hUT
  have hTcard : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) ≤
      Nat.card Z ^ (2 * m + 1) := by
    calc Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r)
        ≤ Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
          Subgroup.card_le_of_le inf_le_left
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) := card_conjSubgroup g _
      _ = Nat.card Z ^ (2 * m + 1) := hmSp.card_V
  rw [ha, hpts.card] at hcard
  have hpos : 0 < Nat.card ↥(Sec8V1 M Q Z B t r) := Nat.card_pos
  have h1 : Nat.card Z ^ (2 ^ m * a) * Nat.card Z ≤ Nat.card Z ^ (2 * m + 1) := by
    have h2 : Nat.card ↥(Sec8V1 M Q Z B t r) *
        (Nat.card Z ^ (2 ^ m * a) * Nat.card Z) ≤
        Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 * m + 1) := by
      calc Nat.card ↥(Sec8V1 M Q Z B t r) * (Nat.card Z ^ (2 ^ m * a) * Nat.card Z)
          = Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 ^ m * a) * Nat.card Z := by ring
        _ ≤ Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) *
            Nat.card ↥(Sec8V1 M Q Z B t r) := hcard
        _ ≤ Nat.card Z ^ (2 * m + 1) * Nat.card ↥(Sec8V1 M Q Z B t r) :=
            Nat.mul_le_mul_right _ hTcard
        _ = Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 * m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left h2 hpos
  rw [← pow_succ] at h1
  exact sec8_m_eq_two_of_pow_le hm2 ha1 hq2 h1

end CFSG.RankThree.GF2n.Stroth80
