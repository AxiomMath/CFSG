module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAIface
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrANbrFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaAdj
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAbsorb

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem exists_conj_eq_mul_of_not_mem_bar (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement)
    (hZcard : Sec7ZCardStatement) (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hCommN : Sec7CommNStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G}
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : IsCentrePre Z0 (hc.CN t) Q)
    {u : Mbar M Q} (hu : u ∈ bar M Q (hc.CN t)) (huV : u ∉ bar M Q Z0) {w : Mbar M Q}
    (hw : w ∈ bar M Q Z0) : ∃ m ∈ bar M Q (hc.CN t), m * u * m⁻¹ = w * u := by
  classical
  obtain ⟨x, hx, rfl⟩ := S714.exists_of_mem_bar hu
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ hc.CN t, ⁅(x : G), y⁆ ∉ Q := by
    by_contra! hall
    exact huV (S714.mk_mem_bar x ((hZN x).mpr ⟨hx, hall⟩))
  have hyM : y ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hy).1
  have hy' : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
    S714.mk_mem_bar _ hy
  have hc₁ : cscal hc ρ hs.toSec5.mem
      ⁅(QuotientGroup.mk x : Mbar M Q), QuotientGroup.mk (⟨y, hyM⟩ : ↥M)⁆ ≠ 0 := by
    rw [Ne, cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 (comm_mem_bar_Z0 hCommN hs hZ0 hu hy')]
    intro h1
    exact hxy ((mk_commute_iff x ⟨y, hyM⟩).mp (commutatorElement_eq_one_iff_commute.mp h1))
  set k : K := cscal hc ρ hs.toSec5.mem w⁻¹ / cscal hc ρ hs.toSec5.mem
    ⁅(QuotientGroup.mk x : Mbar M Q), QuotientGroup.mk (⟨y, hyM⟩ : ↥M)⁆ with hk
  obtain ⟨m, hm, hmΔ⟩ := S714.exists_delta_smul h34 hRoot h310chi h51 h52a h52b hNO hZcard hCRW
    hMp hS hs hr hy' k
  have hb := bN_comb_right h310chi h52a hMp hCommN hS hs hr hZ0
    (f₁ := S714.delta hS t _ (S714.mem_bar_H0_of_CN hy'))
    (f₂ := S714.delta hS t _ (S714.mem_bar_H0_of_CN hy'))
    (f₃ := S714.delta hS t m (S714.mem_bar_H0_of_CN hm)) ⟨_, hy', rfl⟩ ⟨_, hy', rfl⟩ ⟨m, hm, rfl⟩
    (k₁ := k) (k₂ := 0) (by rw [hmΔ, zero_smul, add_zero])
    (S714.delta hS t _ (S714.mem_bar_H0_of_CN hu))
  rw [bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hu hm,
    bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hu hy', zero_mul, add_zero, hk,
    div_mul_cancel₀ _ hc₁] at hb
  have hum : ⁅(QuotientGroup.mk x : Mbar M Q), m⁆ ∈ bar M Q Z0 :=
    comm_mem_bar_Z0 hCommN hs hZ0 hu hm
  have h2 : ⁅(QuotientGroup.mk x : Mbar M Q), m⁆ * w = 1 := by
    rw [← cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 (Subgroup.mul_mem _ hum hw),
      cscal_mul h310chi h52a hMp hS hs hr hZ0 hum hw, hb,
      cscal_inv h310chi h52a hMp hS hs hr hZ0 hw, neg_add_cancel]
  have h3 : ⁅m, (QuotientGroup.mk x : Mbar M Q)⁆ = w := by
    rw [← commutatorElement_inv, eq_inv_of_mul_eq_one_left h2, inv_inv]
  refine ⟨m, hm, ?_⟩
  rw [← h3, commutatorElement_def]
  group

theorem nonOrthNbrs_of (h77 : Stroth77Statement) (hAdj : Sec715AdjStatement)
    (hCent : Sec715CentStatement) (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZV : Sec7ZVStatement)
    (hMp : Sec7CentreMpStatement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hCRW : Sec7CRWStatement)
    (hCommN : Sec7CommNStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G}
    (hs : Sec7Hyp hc n t) (hp : OmegaPlusNat hc t 4) (hn : n = 16) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hr : Sec7A hc t r) : NonOrthNbrsProp M₀ ρ hc t Z0 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  obtain ⟨s, hsR, hsc, g, hgM, hgsL, hgsN⟩ : Conc71a hc t := by
    rcases h77 G M Q Z B hc n t hs with h | h | h | h
    · exact h
    · exact absurd (hn.symm.trans h.2) (by norm_num)
    · exact absurd (hn.symm.trans h.2) (by norm_num)
    · exact absurd (hn.symm.trans h.2) (by norm_num)
  have hsZ0 : s ∈ Z0 := (hZ0 s).mpr ⟨hsR, hsc⟩
  have hsQ : s ∉ Q := fun h =>
    hgsN (hQN ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) s).mp h))
  have hgL : conjSubgroup g Z0 ≤ LB M Q B := by
    have h1 := centre_le_conj_LB hMp hZt hc hs hZ0 (M.inv_mem hgM) hsZ0 hsQ
      (by rw [mem_conjSubgroup, inv_inv]; exact hgsL)
    intro x hx
    have h2 := mem_conjSubgroup.mp (h1 (mem_conjSubgroup.mp hx))
    simpa [mul_assoc] using h2
  have hgN : ¬ conjSubgroup g Z0 ≤ hc.CN t := fun hle =>
    hgsN (hle (by rw [mem_conjSubgroup]; simpa [mul_assoc] using hsZ0))
  have hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)) := sec7_CN_pgroup_bar h34 h311a hc hs
  have hC : CentTwoInV hc t Z0 := fun k _ hk2 hkc =>
    hCent G M Q Z B hc n t hs (Or.inr hp) Z0 hZ0 hZN k hk2 hkc
  obtain ⟨h₀, hh₀H, hh₀⟩ := hc.exists_H0_conj hs hZ0 hZt hZcard hN2 hTI hC hgM
  have hh₀M : h₀ ∈ M := hHM hh₀H
  rw [hh₀] at hgL hgN
  obtain ⟨x, hxN, s', hs'Z, -, hxs'Q, -, hxs'N⟩ :=
    hAdj G M Q Z B hc n t hs hp hn Z0 hZ0 hZN hTI h₀ hh₀M hgL hgN
  obtain ⟨Tt, F⟩ :=
    Ctx.sec715Frame h34 hZt hZcard hMp hZV hc hs hZ0 M₀ (hAct hS) (hAct_compat hS)
  have hmem : ∀ {S : Subgroup G}, Q ≤ S → ∀ (x : ↥(bar M Q (H0 M Z))) (y : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) →
        (x ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) ↔ (y : G) ∈ S) := by
    intro S hQS x y hy
    rw [Subgroup.mem_subgroupOf, ← hy]
    exact mk_mem_bar_iff_sec4 hQS y
  have hrep : ∀ x : ↥(bar M Q (H0 M Z)), ∃ y : ↥M,
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) :=
    fun x => QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  have hbarH : ∀ y : ↥M, (y : G) ∈ H0 M Z →
      QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) :=
    fun y hy => (mk_mem_bar_iff_sec4 hQH y).mpr hy
  set h : ↥(bar M Q (H0 M Z)) := ⟨_, hbarH ⟨h₀, hh₀M⟩ hh₀H⟩ with hh
  have hconjmk : ∀ (a : ↥(bar M Q (H0 M Z))) (z : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) z = (a : Mbar M Q) →
      QuotientGroup.mk' (Q.subgroupOf M) (⟨h₀, hh₀M⟩ * z * ⟨h₀, hh₀M⟩⁻¹) =
        ((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q) := by
    intro a z hz
    simp only [map_mul, map_inv, hz, Subgroup.coe_mul, Subgroup.coe_inv, hh]
  have hL : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) := by
    intro a ha
    obtain ⟨z, hz⟩ := hrep a
    have hzZ : (z : G) ∈ Z0 := (hmem hQZ0 a z hz).mp ha
    refine (hmem hQL _ _ (hconjmk a z hz)).mpr ?_
    apply hgL
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hzZ
  have hout : ¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
    intro hall
    apply hgN
    intro w hw
    obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z0, h₀ * z * h₀⁻¹ = w :=
      ⟨h₀⁻¹ * w * h₀, mem_conjSubgroup.mp hw, by group⟩
    have hzM : z ∈ M := hZ0M hzZ
    have haV : (⟨_, hbarH ⟨z, hzM⟩ (hZ0.le.trans hRH hzZ)⟩ : ↥(bar M Q (H0 M Z))) ∈
        (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := (hmem hQZ0 _ ⟨z, hzM⟩ rfl).mpr hzZ
    exact (hmem hQN _ _ (hconjmk _ ⟨z, hzM⟩ rfl)).mp (hall _ haV)
  have hxM : x ∈ M := hc.Rt_le_M t (hNR hxN)
  have hs'M : s' ∈ M := hZ0M hs'Z
  set nH : ↥(bar M Q (H0 M Z)) := ⟨_, hbarH ⟨x, hxM⟩ (hRH (hNR hxN))⟩ with hnH
  set bH : ↥(bar M Q (H0 M Z)) := ⟨_, hbarH ⟨s', hs'M⟩ (hRH (hZ0.le hs'Z))⟩ with hbH
  have hnN : nH ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
    (hmem hQN _ ⟨x, hxM⟩ rfl).mpr hxN
  have hbV : bH ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
    (hmem hQZ0 _ ⟨s', hs'M⟩ rfl).mpr hs'Z
  have hcomm : QuotientGroup.mk' (Q.subgroupOf M)
      ⁅(⟨x, hxM⟩ : ↥M), ⟨h₀, hh₀M⟩ * ⟨s', hs'M⟩ * ⟨h₀, hh₀M⟩⁻¹⁆ =
        ((⁅nH, h * bH * h⁻¹⁆ : ↥(bar M Q (H0 M Z))) : Mbar M Q) := by
    simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hh,
      hnH, hbH]
  have hnb : ⁅nH, h * bH * h⁻¹⁆ ≠ 1 := by
    intro h1
    apply hxs'Q
    have h2 : QuotientGroup.mk' (Q.subgroupOf M)
        ⁅(⟨x, hxM⟩ : ↥M), ⟨h₀, hh₀M⟩ * ⟨s', hs'M⟩ * ⟨h₀, hh₀M⟩⁻¹⁆ = 1 := by
      rw [hcomm, h1, Subgroup.coe_one]
    have h3 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    simpa [commutatorElement_def] using h3
  have hnX : h⁻¹ * ⁅nH, h * bH * h⁻¹⁆ * h ∈
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
    refine (hmem hQN _ (⟨h₀, hh₀M⟩⁻¹ *
      ⁅(⟨x, hxM⟩ : ↥M), ⟨h₀, hh₀M⟩ * ⟨s', hs'M⟩ * ⟨h₀, hh₀M⟩⁻¹⁆ * ⟨h₀, hh₀M⟩) ?_).mpr ?_
    · rw [map_mul, map_mul, hcomm]
      simp only [map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hh]
    · have h1 := mem_conjSubgroup.mp hxs'N
      simpa [commutatorElement_def, mul_assoc] using h1
  have hsep : ∀ v : M₀.E, (∀ e, M₀.B e v = 0) → v = 0 := fun v hv =>
    M₀.nondeg v fun f => by rw [Tim79.QuadModel.B_comm, hv f, neg_zero]
  have hiso : ∀ (y : ↥(bar M Q (H0 M Z))) (u v : M₀.E),
      M₀.B (hAct hS y u) (hAct hS y v) = M₀.B u v := fun y u v => by
    rw [hAct_apply, hAct_apply]
    exact hS.iso _ y.2 u v
  have habs : ∀ k : ↥(bar M Q (H0 M Z)), ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      a ≠ 1 → k * a * k⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) →
      ∀ c ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        k * c * k⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) := by
    intro k a ha ha1 hka c hc'
    obtain ⟨k₀, hk₀⟩ := hrep k
    obtain ⟨a₀, ha₀⟩ := hrep a
    obtain ⟨c₀, hc₀⟩ := hrep c
    have ha₀Z : (a₀ : G) ∈ Z0 := (hmem hQZ0 a a₀ ha₀).mp ha
    have hc₀Z : (c₀ : G) ∈ Z0 := (hmem hQZ0 c c₀ hc₀).mp hc'
    have ha₀Q : (a₀ : G) ∉ Q := fun hq => ha1 (Subtype.ext (by
      rw [← ha₀, Subgroup.coe_one]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hq)))
    have hka' : (k₀ : G) * a₀ * (k₀ : G)⁻¹ ∈ LB M Q B := by
      have h1 := (hmem hQL (k * a * k⁻¹) (k₀ * a₀ * k₀⁻¹) (by
        simp only [map_mul, map_inv, hk₀, ha₀, Subgroup.coe_mul, Subgroup.coe_inv])).mp hka
      simpa using h1
    have h1 := centre_le_conj_LB hMp hZt hc hs hZ0 (M.inv_mem k₀.2) ha₀Z ha₀Q
      (by rw [mem_conjSubgroup, inv_inv]; exact hka')
    have h2 := mem_conjSubgroup.mp (h1 hc₀Z)
    rw [inv_inv] at h2
    refine (hmem hQL (k * c * k⁻¹) (k₀ * c₀ * k₀⁻¹) (by
      simp only [map_mul, map_inv, hk₀, hc₀, Subgroup.coe_mul, Subgroup.coe_inv])).mpr ?_
    simpa using h2
  have hsemi : ∀ z ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      z ∉ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) →
      ∀ w ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        ∃ m ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), m * z * m⁻¹ = w * z := by
    intro z hz hzV w hw
    obtain ⟨m, hm, hmz⟩ := exists_conj_eq_mul_of_not_mem_bar h34 hRoot h310chi h51 h52a h52b hNO
      hZcard hCRW hMp hCommN hS hs hr hZ0 hZN (Subgroup.mem_subgroupOf.mp hz)
      (fun h' => hzV (Subgroup.mem_subgroupOf.mpr h')) (Subgroup.mem_subgroupOf.mp hw)
    refine ⟨⟨m, S714.mem_bar_H0_of_CN hm⟩, Subgroup.mem_subgroupOf.mpr hm, Subtype.ext ?_⟩
    simpa using hmz
  obtain ⟨g₁, g₂, ⟨h1a, h1b, h1c⟩, ⟨h2a, h2b, h2c⟩, a, ha, a', ha', e, e', hne⟩ :=
    F.exists_nonOrth_symNbrs hsep hiso habs hsemi hL hout hnN hbV hnb hnX
  have key : ∀ g' : ↥(bar M Q (H0 M Z)),
      (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        g' * a * g'⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) →
      (¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        g'⁻¹ * a * g' ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) →
      (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        g'⁻¹ * a * g' ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) →
      ∃ k : ↥M, QuotientGroup.mk' (Q.subgroupOf M) k = (g' : Mbar M Q) ∧
        IsSymNbr hc t Z0 (k : G) := by
    intro g' hA hB hC'
    obtain ⟨k, hk⟩ := hrep g'
    refine ⟨k, hk, k.2, fun w hw => ?_, fun heq => ?_, fun z hz => ?_⟩
    · obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z0, (k : G) * z * (k : G)⁻¹ = w :=
        ⟨(k : G)⁻¹ * w * k, mem_conjSubgroup.mp hw, by group⟩
      have hzM : z ∈ M := hZ0M hzZ
      have haV : (⟨_, hbarH ⟨z, hzM⟩ (hZ0.le.trans hRH hzZ)⟩ : ↥(bar M Q (H0 M Z))) ∈
          (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := (hmem hQZ0 _ ⟨z, hzM⟩ rfl).mpr hzZ
      refine (hmem hQN _ (k * ⟨z, hzM⟩ * k⁻¹) ?_).mp (hA _ haV)
      simp only [map_mul, map_inv, hk, Subgroup.coe_mul, Subgroup.coe_inv]
    · apply hB
      intro a ha
      obtain ⟨z, hz⟩ := hrep a
      have hzZ : (z : G) ∈ Z0 := (hmem hQZ0 a z hz).mp ha
      have h1 : (k : G)⁻¹ * z * k ∈ Z0 := by
        rw [← mem_conjSubgroup, heq]
        exact hzZ
      refine (hmem hQZ0 _ (k⁻¹ * z * k) ?_).mpr (by simpa using h1)
      simp only [map_mul, map_inv, hk, hz, Subgroup.coe_mul, Subgroup.coe_inv]
    · rw [mem_conjSubgroup]
      have hzM : z ∈ M := hZ0M hz
      have haV : (⟨_, hbarH ⟨z, hzM⟩ (hZ0.le.trans hRH hz)⟩ : ↥(bar M Q (H0 M Z))) ∈
          (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := (hmem hQZ0 _ ⟨z, hzM⟩ rfl).mpr hz
      refine (hmem hQN _ (k⁻¹ * ⟨z, hzM⟩ * k) ?_).mp (hC' _ haV)
      simp only [map_mul, map_inv, hk, Subgroup.coe_mul, Subgroup.coe_inv]
  have hmemconj : ∀ (g' : ↥(bar M Q (H0 M Z))) (k : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) k = (g' : Mbar M Q) →
      ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        ((g' * a * g'⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q) ∈ bar M Q (conjSubgroup (k : G) Z0) := by
    intro g' k hk a ha
    rw [← conjSubgroup_bar hQZ0 hQM k, mem_conjSubgroup, hk]
    have e1 : (g' : Mbar M Q)⁻¹ * ((g' * a * g'⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q) * g' = a := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact Subgroup.mem_subgroupOf.mp ha
  obtain ⟨k₁, hk₁, hS₁⟩ := key g₁ h1a h1b h1c
  obtain ⟨k₂, hk₂, hS₂⟩ := key g₂ h2a h2b h2c
  exact ⟨k₁, k₂, hS₁, hS₂, _, hmemconj g₁ k₁ hk₁ a ha, _, hmemconj g₂ k₂ hk₂ a' ha', e, e', hne⟩

end CFSG.RankThree.GF2n.Stroth80.S715L
