module

public import CFSG.RankThree.GF2n.Stroth80.Step715Hyp79Proof
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitStmt
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Rec
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerPair
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerDim
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfig
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec4ClassicalFacts
public import CFSG.RankThree.GF2n.Stroth80.Sec51Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjCited
public import CFSG.RankThree.GF2n.Stroth80.Sec78Centre
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec78QB
public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVOrder
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MPrime

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S715L

section Unipotent

variable {K : Type} {X H : Type*} [Field K] [AddCommGroup X] [Module K X] [Group H]

theorem eq_one_of_isCompl_irrSub [Finite K] [CharP K 2] [FiniteDimensional K X]
    (act : H →* (X ≃ₗ[K] X))
    {N₁ N₂ : Submodule K X} (hN : IsCompl N₁ N₂) (h₁ : IsIrrSub act N₁) (h₂ : IsIrrSub act N₂)
    (hpres : ∀ T : X →ₗ[K] X, (∀ h x, T (act h x) = act h (T x)) →
      (∀ x ∈ N₁, T x ∈ N₁) ∧ (∀ x ∈ N₂, T x ∈ N₂))
    (T : X →ₗ[K] X) (hT : ∀ h x, T (act h x) = act h (T x)) {k : ℕ} (hk : T ^ 2 ^ k = 1) :
    T = 1 := by
  set φ : X →ₗ[K] X := T - 1 with hφdef
  have hφ : ∀ h x, φ (act h x) = act h (φ x) := fun h x => by
    simp only [hφdef, LinearMap.sub_apply, Module.End.one_apply, hT, map_sub]
  have hφk : φ ^ 2 ^ k = 0 := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [hφdef, Sp6NoEmb.sub_one_pow_two_pow, hk, sub_self]
  have key : ∀ N : Submodule K X, IsIrrSub act N → (∀ x ∈ N, φ x ∈ N) → ∀ x ∈ N, φ x = 0 := by
    intro N hNirr hNφ
    obtain ⟨hNbot, hNinv, hNmin⟩ := hNirr
    have hinv : IsInvSub act (LinearMap.ker φ ⊓ N) := by
      intro h x hx
      refine ⟨LinearMap.mem_ker.mpr ?_, hNinv h x hx.2⟩
      rw [hφ, LinearMap.mem_ker.mp hx.1, map_zero]
    rcases hNmin _ inf_le_right hinv with h0 | hN'
    · exfalso
      obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNbot
      have hpow : ∀ j : ℕ, (φ ^ j) x ∈ N ∧ (φ ^ j) x ≠ 0 := by
        intro j
        induction j with
        | zero => exact ⟨hxN, hx0⟩
        | succ j ih =>
          rw [pow_succ', Module.End.mul_apply]
          refine ⟨hNφ _ ih.1, fun hz => ih.2 ?_⟩
          have hmem : (φ ^ j) x ∈ LinearMap.ker φ ⊓ N := ⟨hz, ih.1⟩
          rw [h0] at hmem
          exact (Submodule.mem_bot K).mp hmem
      exact (hpow (2 ^ k)).2 (by rw [hφk, LinearMap.zero_apply])
    · intro x hx
      have hx' : x ∈ LinearMap.ker φ ⊓ N := by rw [hN']; exact hx
      exact hx'.1
  obtain ⟨hp₁, hp₂⟩ := hpres φ hφ
  have e₁ := key N₁ h₁ hp₁
  have e₂ := key N₂ h₂ hp₂
  have hφ0 : φ = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ N₁ ⊔ N₂ := by rw [hN.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, e₁ y hy, e₂ z hz, add_zero, LinearMap.zero_apply]
  rw [hφdef] at hφ0
  exact sub_eq_zero.mp hφ0

end Unipotent

end S715L

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_CN_of_comm_le [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hY : Sec713YStatement)
    (hCent : Sec715CentStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp : OmegaPlusNat hc t 4) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q) {x : G} (hxK : x ∈ NormH0 M Z Z0)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k ∈ Q) (hxN : ∀ m ∈ hc.CN t, ⁅x, m⁆ ∈ Z0)
    (hxR : ∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t) : x ∈ hc.CN t := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hNR : ∀ m ∈ hc.CN t, m ∈ Rt M (LB M Q B) t := fun m hm => (Ctx.mem_CN.mp hm).1
  have hxM : x ∈ M := hxK.1.1
  have hxZ := sec715_comm_Z0_mem_Q h34 h310chi hZc hZV hc hs hZ0 hxK hx2
  obtain ⟨y, hyR, -, hy3, hyC⟩ := hY G M Q Z B hc n t hs Z0 hZ0
  have hyM : y ∈ M := hRM hyR
  let xm : ↥M := ⟨x, hxM⟩
  let ym : ↥M := ⟨y, hyM⟩
  have hxRn : conjSubgroup x (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hxK).1
  have hxNn : conjSubgroup x (hc.CN t) = hc.CN t := sec7_conj_CN_eq hZt hZcard hc hs hZ0 hxK
  have hZN' : bar M Q Z0 ≤ bar M Q (hc.CN t) := bar_mono' hZN.le
  have hNN' : ∀ a ∈ bar M Q (hc.CN t), ∀ b ∈ bar M Q (hc.CN t), ⁅a, b⁆ ∈ bar M Q Z0 := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_bar_iff_exists_lift.mp hb
    rw [← map_commutatorElement]
    exact mem_bar_iff_exists_lift.mpr ⟨⁅a', b'⁆,
      hCommN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator ha' hb'), rfl⟩
  have hZc' : ∀ a ∈ bar M Q Z0, ∀ b ∈ bar M Q (hc.CN t), Commute a b := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_bar_iff_exists_lift.mp hb
    exact (mk_commute_iff a' b').mpr (hZ0.comm_mem ha' (hNR _ hb'))
  have hZ2' : ∀ a ∈ bar M Q Z0, a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    have hsq : (a' : G) ^ 2 ∈ Q :=
      hc.sq_mem_Q_of_mem_LB (hZc G M Q Z B hc n t hs Z0 hZ0 _ ha').1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hsq))
  have hxN' : ∀ m ∈ bar M Q (hc.CN t),
      ⁅m, QuotientGroup.mk' (Q.subgroupOf M) xm⁆ ∈ bar M Q Z0 := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
    rw [← map_commutatorElement]
    refine mem_bar_iff_exists_lift.mpr ⟨⁅m', xm⁆, ?_, rfl⟩
    have h := Z0.inv_mem (hxN _ hm')
    rwa [commutatorElement_inv] at h
  have hxZ' : ∀ a ∈ bar M Q Z0, Commute a (QuotientGroup.mk' (Q.subgroupOf M) xm) := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    exact (mk_commute_iff a' xm).mpr (hxZ _ ha')
  have hy3' : QuotientGroup.mk' (Q.subgroupOf M) ym ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hy3))
  have hyN' : ∀ m ∈ bar M Q (hc.CN t), QuotientGroup.mk' (Q.subgroupOf M) ym * m *
      (QuotientGroup.mk' (Q.subgroupOf M) ym)⁻¹ ∈ bar M Q (hc.CN t) := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_bar_iff_exists_lift.mpr ⟨ym * m' * ym⁻¹, hc.CN_conj_mem ht hyR hm', rfl⟩
  have hyZ' : ∀ a ∈ bar M Q Z0, Commute (QuotientGroup.mk' (Q.subgroupOf M) ym) a := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    exact ((mk_commute_iff a' ym).mpr (hZ0.comm_mem ha' hyR)).symm
  have hyC' : ∀ m ∈ bar M Q (hc.CN t), Commute (QuotientGroup.mk' (Q.subgroupOf M) ym) m →
      m ∈ bar M Q Z0 := by
    intro m hm hcm
    obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
    exact mem_bar_iff_exists_lift.mpr ⟨m', hyC _ hm' ((mk_commute_iff ym m').mp hcm), rfl⟩
  have hxy : ⁅x⁻¹, y⁻¹⁆ ∈ hc.CN t := by
    have hr : x⁻¹ * y⁻¹ * x ∈ Rt M (LB M Q B) t := by
      have h1 : x⁻¹ * y⁻¹ * x⁻¹⁻¹ ∈ conjSubgroup x⁻¹ (Rt M (LB M Q B) t) :=
        ⟨y⁻¹, (Rt M (LB M Q B) t).inv_mem hyR, rfl⟩
      rw [inv_inv] at h1
      have e : conjSubgroup x⁻¹ (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
        conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer _).inv_mem
          (conjSubgroup_eq_self_iff.mp hxRn))
      rwa [e] at h1
    have h2 := (hc.CN t).inv_mem (hxR _ hr)
    rwa [show ⁅x, x⁻¹ * y⁻¹ * x⁆⁻¹ = ⁅x⁻¹, y⁻¹⁆ by simp only [commutatorElement_def]; group]
      at h2
  have hxy' : ⁅(QuotientGroup.mk' (Q.subgroupOf M) xm)⁻¹,
      (QuotientGroup.mk' (Q.subgroupOf M) ym)⁻¹⁆ ∈ bar M Q (hc.CN t) := by
    rw [← map_inv, ← map_inv, ← map_commutatorElement]
    exact mem_bar_iff_exists_lift.mpr ⟨⁅xm⁻¹, ym⁻¹⁆, hxy, rfl⟩
  obtain ⟨dbar, hdN, hcomm⟩ := exists_commute_mul_inv_of_orbit hZN' hNN' hZc' hZ2' hxN' hxZ'
    hy3' hyN' hyZ' hyC' hxy'
  obtain ⟨hD2, -, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)) := by
    have h1 : IsPGroup 2 ↥(hc.CN t) :=
      hD2.to_le (sec715_CN_le_O2NormPre h34 h51 hA hZt hZcard hc hs hZ0)
    have h2 : IsPGroup 2 ↥((hc.CN t).subgroupOf M) := h1.comap_subtype
    exact h2.map _
  have hx2' : IsPGroup 2 ↥(Subgroup.zpowers (QuotientGroup.mk' (Q.subgroupOf M) xm)) := by
    obtain ⟨k, hk⟩ := hx2
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
  have hxnorm : Subgroup.zpowers (QuotientGroup.mk' (Q.subgroupOf M) xm) ≤
      Subgroup.normalizer ((bar M Q (hc.CN t) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
    · obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
      rw [← map_inv, ← map_mul, ← map_mul]
      have h1 : x * (m' : G) * x⁻¹ ∈ conjSubgroup x (hc.CN t) := ⟨m', hm', rfl⟩
      rw [hxNn] at h1
      exact mem_bar_iff_exists_lift.mpr ⟨xm * m' * xm⁻¹, h1, rfl⟩
    · have e : m = (QuotientGroup.mk' (Q.subgroupOf M) xm)⁻¹ *
          (QuotientGroup.mk' (Q.subgroupOf M) xm * m * (QuotientGroup.mk' (Q.subgroupOf M) xm)⁻¹) *
          QuotientGroup.mk' (Q.subgroupOf M) xm := by group
      obtain ⟨m', hm', hm'e⟩ := mem_bar_iff_exists_lift.mp hm
      rw [e, ← hm'e, ← map_inv, ← map_mul, ← map_mul]
      have h1 : x⁻¹ * (m' : G) * x⁻¹⁻¹ ∈ conjSubgroup x⁻¹ (hc.CN t) := ⟨m', hm', rfl⟩
      rw [conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer _).inv_mem
        (conjSubgroup_eq_self_iff.mp hxNn)), inv_inv] at h1
      exact mem_bar_iff_exists_lift.mpr ⟨xm⁻¹ * m' * xm, h1, rfl⟩
  have hP2 := IsPGroup.to_sup_of_normal_left' hN2 hx2' hxnorm
  have hk2 : IsPGroup 2 (Subgroup.zpowers (QuotientGroup.mk' (Q.subgroupOf M) xm * dbar⁻¹)) :=
    hP2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left hdN))))
  have hkZ := hCent G M Q Z B hc n t hs (Or.inr hp) Z0 hZ0 hZN _ hk2
    (fun u hu => (hcomm u hu).eq.symm)
  have hxbar : QuotientGroup.mk' (Q.subgroupOf M) xm ∈ bar M Q (hc.CN t) := by
    have e : QuotientGroup.mk' (Q.subgroupOf M) xm =
        QuotientGroup.mk' (Q.subgroupOf M) xm * dbar⁻¹ * dbar := by group
    rw [e]
    exact (bar M Q (hc.CN t)).mul_mem (hZN' hkZ) hdN
  exact (mk_mem_bar_iff_sec4 hQN xm).mp hxbar

namespace S715L

open S714

variable [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem comm_mem_Z_iff_act_eq (hS : IsTensorSetup hc n M₀ ρ b) (y : ↥M) {v : G} (hv : v ∈ Q) :
    ⁅(y : G), v⁆ ∈ Z ↔ (ρ (QuotientGroup.mk y)).toAdd (M₀.π v) = M₀.π v := by
  have hyv : (y : G) * v * (y : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2) v).mp hv
  have hcQ : ⁅(y : G), v⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem hyv (Q.inv_mem hv)
  have hid : (y : G) * v * (y : G)⁻¹ = ⁅(y : G), v⁆ * v := by
    rw [commutatorElement_def]; group
  rw [← hS.conj y v hv, hid, M₀.π_mul _ hcQ v hv, ← M₀.π_ker _ hcQ]
  constructor
  · intro h; rw [h, zero_add]
  · intro h; exact add_eq_right.mp h


theorem comm_mem_CN_of_centralizes (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {z : G} (hzK : z ∈ NormH0 M Z Z0)
    (hzV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅z, v⁆ ∈ Z) :
    ∀ x ∈ Rt M (LB M Q B) t, ⁅z, x⁆ ∈ hc.CN t := by
  intro x hx
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hzM : z ∈ M := hzK.1.1
  have hxM : x ∈ M := hc.Rt_le_M t hx
  have hRn : conjSubgroup z (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hzK).1
  have hcR : ⁅z, x⁆ ∈ Rt M (LB M Q B) t := by
    have h1 : z * x * z⁻¹ ∈ conjSubgroup z (Rt M (LB M Q B) t) := ⟨x, hx, rfl⟩
    rw [hRn] at h1
    rw [commutatorElement_def]
    exact (Rt M (LB M Q B) t).mul_mem h1 ((Rt M (LB M Q B) t).inv_mem hx)
  refine Ctx.mem_CN.mpr ⟨hcR, fun v hv => ?_⟩
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  let zm : ↥M := ⟨z, hzM⟩
  let xm : ↥M := ⟨x, hxM⟩
  have hfix : ∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk zm)).toAdd e = e := by
    intro e he
    obtain ⟨u, huV, huQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp he)
    exact (comm_mem_Z_iff_act_eq hS zm huQ).mp (hzV u huV)
  have hxR : (QuotientGroup.mk xm : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := mk_mem_bar xm hx
  have hπv : M₀.π v ∈ hc.VtSub hS.model t :=
    (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hv hvQ)
  have he₁ : (ρ (QuotientGroup.mk xm)⁻¹).toAdd (M₀.π v) ∈ hc.VtSub hS.model t :=
    hc.act_mem_VtSub hS ht _ ((bar M Q (Rt M (LB M Q B) t)).inv_mem hxR) _ hπv
  have hinv : ∀ (a : Mbar M Q) (e : M₀.E), (ρ a).toAdd e = e → (ρ a⁻¹).toAdd e = e := by
    intro a e h
    conv_lhs => rw [← h]
    rw [← act_mul_apply, inv_mul_cancel]
    exact act_one_apply _
  have hxx : ∀ e, (ρ (QuotientGroup.mk xm)).toAdd ((ρ (QuotientGroup.mk xm)⁻¹).toAdd e) = e := by
    intro e
    rw [← act_mul_apply, mul_inv_cancel]
    exact act_one_apply _
  refine (comm_mem_Z_iff_act_eq hS ⁅zm, xm⁆ hvQ).mpr ?_
  rw [show (QuotientGroup.mk ⁅zm, xm⁆ : Mbar M Q) =
      ⁅(QuotientGroup.mk zm : Mbar M Q), QuotientGroup.mk xm⁆ from
      map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) zm xm, commutatorElement_def,
    act_mul_apply, act_mul_apply, act_mul_apply, hinv _ _ (hfix _ he₁), hxx,
    hfix _ hπv]

theorem mem_CN_of_centralizes_configC (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hY : Sec713YStatement)
    (hCent : Sec715CentStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G}
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    {N₁ N₂ : Submodule K ↥(deltaSub hS t)} (hN : IsCompl N₁ N₂)
    (h₁ : IsIrrSub (deltaAct hS hs.toSec5.mem) N₁) (h₂ : IsIrrSub (deltaAct hS hs.toSec5.mem) N₂)
    (hpres : ∀ T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t),
      (∀ x f, T (deltaAct hS hs.toSec5.mem x f) = deltaAct hS hs.toSec5.mem x (T f)) →
        (∀ f ∈ N₁, T f ∈ N₁) ∧ (∀ f ∈ N₂, T f ∈ N₂))
    {z : G} (hzK : z ∈ NormH0 M Z Z0) (hz2 : ∃ k : ℕ, z ^ 2 ^ k ∈ Q)
    (hzV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅z, v⁆ ∈ Z) : z ∈ hc.CN t := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hzM : z ∈ M := hzK.1.1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  haveI : Module.Finite K M₀.E := M₀.fin
  let zm : ↥M := ⟨z, hzM⟩
  set zb : Mbar M Q := QuotientGroup.mk zm with hzb
  have hzH : zb ∈ bar M Q (H0 M Z) := mk_mem_bar zm hzK.1
  have hzR := comm_mem_CN_of_centralizes hZt hZcard hS hs hZ0 hzK hzV
  have hNn : conjSubgroup z (hc.CN t) = hc.CN t := sec7_conj_CN_eq hZt hZcard hc hs hZ0 hzK
  have hzN : ∀ m ∈ bar M Q (hc.CN t), zb * m * zb⁻¹ ∈ bar M Q (hc.CN t) := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := exists_of_mem_bar hm
    have h1 : z * (m' : G) * z⁻¹ ∈ conjSubgroup z (hc.CN t) := ⟨m', hm', rfl⟩
    rw [hNn] at h1
    exact mk_mem_bar (zm * m' * zm⁻¹) h1
  have hzW' : ∀ w ∈ wsub hS t, (ρ zb⁻¹).toAdd w ∈ wsub hS t := by
    have h := stab_wsub_of_mem_NormH0 hS hZt hZcard hs hZ0 ((NormH0 M Z Z0).inv_mem hzK)
    intro w hw
    exact h w hw
  set C := conjE hS zb hzH hzW' with hC
  have hCΔ : ∀ (m : Mbar M Q) (hm : m ∈ bar M Q (hc.CN t)),
      C (delta hS t m (mem_bar_H0_of_CN hm)) =
        delta hS t (zb * m * zb⁻¹) (mem_bar_H0_of_CN (hzN m hm)) := fun m hm =>
    (delta_conj_of_stab hS zb hzH hzW' (mem_bar_H0_of_CN hm)).symm
  have hCmem : ∀ f ∈ deltaSub hS t, C f ∈ deltaSub hS t := by
    intro f hf
    obtain ⟨m, hm, rfl⟩ := hSΔ f hf
    rw [hCΔ m hm]
    exact delta_mem_deltaSub hS (hzN m hm)
  set T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t) := C.restrict hCmem with hT
  have hTapp : ∀ f : ↥(deltaSub hS t), ((T f : ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E) =
      C f := fun f => rfl
  have hNtriv : ∀ (c : Mbar M Q) (hc' : c ∈ bar M Q (hc.CN t)) (m : Mbar M Q)
      (hm : m ∈ bar M Q (hc.CN t)),
      delta hS t (c * m * c⁻¹) (mem_bar_H0_of_CN (hc.bar_CN_conj_mem ht
        (bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hc') hm)) =
        delta hS t m (mem_bar_H0_of_CN hm) := by
    intro c hc' m hm
    have hcR : c ∈ bar M Q (Rt M (LB M Q B) t) := bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hc'
    have h1 := deltaAct_delta hS ht ⟨c, hcR⟩ hm
    rw [deltaAct_of_mem_CN h310chi h52a hS hs hr ⟨c, hcR⟩ hc'] at h1
    exact (congrArg Subtype.val h1).symm
  have hTeq : ∀ x f, T (deltaAct hS ht x f) = deltaAct hS ht x (T f) := by
    intro x f
    obtain ⟨f, hf⟩ := f
    obtain ⟨m, hm, rfl⟩ := hSΔ f hf
    have hxm := hc.bar_CN_conj_mem ht x.2 hm
    refine Subtype.ext ?_
    rw [hTapp, deltaAct_delta hS ht x hm]
    show C (delta hS t _ _) = ((deltaAct hS ht x ⟨C (delta hS t m _), _⟩ :
      ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E)
    have e1 : (⟨C (delta hS t m (mem_bar_H0_of_CN hm)), hCmem _ (delta_mem_deltaSub hS hm)⟩ :
        ↥(deltaSub hS t)) = ⟨delta hS t (zb * m * zb⁻¹) (mem_bar_H0_of_CN (hzN m hm)),
          delta_mem_deltaSub hS (hzN m hm)⟩ := Subtype.ext (hCΔ m hm)
    rw [e1, deltaAct_delta hS ht x (hzN m hm), hCΔ _ hxm]
    show delta hS t (zb * ((x : Mbar M Q) * m * (x : Mbar M Q)⁻¹) * zb⁻¹) _ =
      delta hS t ((x : Mbar M Q) * (zb * m * zb⁻¹) * (x : Mbar M Q)⁻¹) _
    obtain ⟨xr, hxr, hxe⟩ := exists_of_mem_bar x.2
    have hcN : ⁅zb, (x : Mbar M Q)⁆ ∈ bar M Q (hc.CN t) := by
      rw [← hxe, show ⁅zb, (QuotientGroup.mk xr : Mbar M Q)⁆ = QuotientGroup.mk ⁅zm, xr⁆ from
        (map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) zm xr).symm]
      exact mk_mem_bar _ (hzR _ hxr)
    have hy := hc.bar_CN_conj_mem ht x.2 (hzN m hm)
    have e2 : zb * ((x : Mbar M Q) * m * (x : Mbar M Q)⁻¹) * zb⁻¹ =
        ⁅zb, (x : Mbar M Q)⁆ * ((x : Mbar M Q) * (zb * m * zb⁻¹) * (x : Mbar M Q)⁻¹) *
          ⁅zb, (x : Mbar M Q)⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [delta_congr hS t e2 _ (mem_bar_H0_of_CN (hc.bar_CN_conj_mem ht
      (bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hcN) hy))]
    exact hNtriv _ hcN _ hy
  have hmemj : ∀ (j : ℕ) (m : Mbar M Q), m ∈ bar M Q (hc.CN t) →
      zb ^ j * m * (zb ^ j)⁻¹ ∈ bar M Q (hc.CN t) := by
    intro j m hm
    induction j with
    | zero => simpa using hm
    | succ j ih =>
      have h1 := hzN _ ih
      rwa [show zb * (zb ^ j * m * (zb ^ j)⁻¹) * zb⁻¹ = zb ^ (j + 1) * m * (zb ^ (j + 1))⁻¹
        by group] at h1
  have hCpow : ∀ (j : ℕ) (m : Mbar M Q) (hm : m ∈ bar M Q (hc.CN t)),
      (C ^ j) (delta hS t m (mem_bar_H0_of_CN hm)) =
        delta hS t (zb ^ j * m * (zb ^ j)⁻¹) (mem_bar_H0_of_CN (hmemj j m hm)) := by
    intro j
    induction j with
    | zero =>
      intro m hm
      rw [pow_zero, Module.End.one_apply]
      exact delta_congr hS t (by group) _ _
    | succ j ih =>
      intro m hm
      rw [pow_succ', Module.End.mul_apply, ih m hm, hCΔ _ (hmemj j m hm)]
      exact delta_congr hS t (by group) _ _
  have hTpow : ∀ (j : ℕ) (f : ↥(deltaSub hS t)),
      (((T ^ j) f : ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E) = (C ^ j) f := by
    intro j
    induction j with
    | zero => intro f; rfl
    | succ j ih =>
      intro f
      rw [pow_succ', Module.End.mul_apply, hTapp, ih, pow_succ', Module.End.mul_apply]
  obtain ⟨k, hk⟩ := hz2
  have hzk : zb ^ 2 ^ k = 1 := by
    rw [hzb, show (QuotientGroup.mk zm : Mbar M Q) ^ 2 ^ k = QuotientGroup.mk (zm ^ 2 ^ k) from
      (map_pow (QuotientGroup.mk' (Q.subgroupOf M)) zm _).symm]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
  have hTk : T ^ 2 ^ k = 1 := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    rw [hTpow, Module.End.one_apply]
    obtain ⟨f, hf⟩ := f
    obtain ⟨m, hm, rfl⟩ := hSΔ f hf
    show (C ^ 2 ^ k) (delta hS t m _) = delta hS t m _
    rw [hCpow _ m hm]
    exact delta_congr hS t (by rw [hzk]; group) _ _
  have hT1 := eq_one_of_isCompl_irrSub (deltaAct hS ht) hN h₁ h₂ hpres T hTeq hTk
  have hxN : ∀ m ∈ hc.CN t, ⁅z, m⁆ ∈ Z0 := by
    intro m hm
    have hmM : m ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hm).1
    let mm : ↥M := ⟨m, hmM⟩
    have hmb : (QuotientGroup.mk mm : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar mm hm
    have hfix : delta hS t (zb * QuotientGroup.mk mm * zb⁻¹) (mem_bar_H0_of_CN (hzN _ hmb)) =
        delta hS t (QuotientGroup.mk mm) (mem_bar_H0_of_CN hmb) := by
      have h1 := congrArg (fun T' : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t) =>
        ((T' ⟨_, delta_mem_deltaSub hS hmb⟩ : ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E)) hT1
      simp only [Module.End.one_apply] at h1
      rw [hTapp, hCΔ _ hmb] at h1
      exact h1
    have hinvN : (QuotientGroup.mk mm : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) :=
      (bar M Q (hc.CN t)).inv_mem hmb
    have hd1 := delta_mul h310chi h52a hS hs hr (hzN _ hmb) hinvN
    have hd2 := delta_mul h310chi h52a hS hs hr hmb hinvN
    have hcomm : ⁅zb, (QuotientGroup.mk mm : Mbar M Q)⁆ ∈ bar M Q (hc.CN t) :=
      (bar M Q (hc.CN t)).mul_mem (hzN _ hmb) hinvN
    have hR : ⁅zb, (QuotientGroup.mk mm : Mbar M Q)⁆ ∈ bar M Q (Rt M (LB M Q B) t) :=
      bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hcomm
    have h0 : delta hS t ⁅zb, (QuotientGroup.mk mm : Mbar M Q)⁆ (mem_bar_H0_of_Rt hc hR) = 0 := by
      rw [delta_congr hS t (commutatorElement_def _ _) _
        (Subgroup.mul_mem _ (mem_bar_H0_of_CN (hzN _ hmb)) (mem_bar_H0_of_CN hinvN)), hd1, hfix,
        ← hd2, delta_congr hS t (mul_inv_cancel _) _ (Subgroup.one_mem _)]
      refine LinearMap.ext fun w => ?_
      rw [delta_apply, dmap_one, LinearMap.zero_apply]
    have hZb := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mp h0
    rw [show ⁅zb, (QuotientGroup.mk mm : Mbar M Q)⁆ = QuotientGroup.mk ⁅zm, mm⁆ from
      (map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) zm mm).symm] at hZb
    exact (mk_mem_bar_iff_sec4 hQZ0 ⁅zm, mm⁆).mp hZb
  exact mem_CN_of_comm_le h34 h310chi h51 hA hZt hZcard hZc hZV hCommN hY hCent hc hs hp hZ0 hZN
    hzK ⟨k, hk⟩ hxN hzR


theorem two_mul_finrank_range_delta_le (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    2 * Module.finrank K (LinearMap.range (delta hS t g (mem_bar_H0_of_CN hg))) ≤
      Module.finrank K (LinearMap.range (dlin hS g (mem_bar_H0_of_CN hg))) := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  have hgH := mem_bar_H0_of_CN hg
  obtain ⟨-, hDW, hDE⟩ := dmap_CN_facts h310chi h52a hS hs hr hg
  obtain ⟨hnd, -⟩ := bilin_nondegenerate_isRefl (M₀ := M₀)
  have hW : wsub hS t = M₀.B.orthogonal (hc.VtSub hS.model t) := wsub_eq_orthogonal hS t
  have hadj : ∀ x, ∀ w ∈ wsub hS t, M₀.B (dmap ρ g x) w = -M₀.B x (dmap ρ g w) := fun x w hw =>
    bilin_D_right (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t)
      (D := dlin hS g hgH) (dmap_iso hS hgH) (fun x => hDE x) (fun w hw => hDW w hw)
      (fun w hw v hv => bilin_wsub_vsub hS t hw hv) x hw
  set U := LinearMap.range (dlin hS g hgH) with hU
  set V := hc.VtSub hS.model t with hV
  have hker : (LinearMap.ker (delta hS t g hgH)).map (wsub hS t).subtype =
      M₀.B.orthogonal (V ⊔ U) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw0 : dmap ρ g w = 0 := by
        have h1 : delta hS t g hgH w = 0 := hw
        rwa [delta_apply] at h1
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨e, rfl⟩ := hu
      show M₀.B (v + dlin hS g hgH e) w = 0
      rw [map_add, LinearMap.add_apply, bilin_vsub_wsub hS t hv w.2, dlin_apply, hadj e w w.2,
        hw0, map_zero, neg_zero, add_zero]
    · intro hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      have hxW : x ∈ wsub hS t := by
        rw [hW, LinearMap.BilinForm.mem_orthogonal_iff]
        exact fun v hv => hx v (Submodule.mem_sup_left hv)
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      show delta hS t g hgH ⟨x, hxW⟩ = 0
      rw [delta_apply]
      show dmap ρ g x = 0
      refine M₀.nondeg _ fun e => ?_
      have h1 : M₀.B (dmap ρ g e) x = 0 := hx _ (Submodule.mem_sup_right ⟨e, rfl⟩)
      rw [hadj e x hxW, neg_eq_zero] at h1
      rw [Tim79.QuadModel.B_comm, h1, neg_zero]
  have e1 := LinearMap.finrank_range_add_finrank_ker (delta hS t g hgH)
  have e2 : Module.finrank K ↥(LinearMap.ker (delta hS t g hgH)) =
      Module.finrank K ↥(M₀.B.orthogonal (V ⊔ U)) := by
    rw [← hker, Submodule.finrank_map_subtype_eq]
  have e3 := LinearMap.BilinForm.finrank_orthogonal hnd (V ⊔ U)
  have e4 : Module.finrank K ↥(wsub hS t) = Module.finrank K M₀.E - Module.finrank K ↥V := by
    rw [hW]; exact LinearMap.BilinForm.finrank_orthogonal hnd V
  have e5 := Submodule.finrank_sup_add_finrank_inf_eq V U
  have e6 : Module.finrank K ↥(LinearMap.range (delta hS t g hgH)) ≤
      Module.finrank K ↥(V ⊓ U) := by
    refine Submodule.finrank_mono ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨hDW w w.2, ⟨w, rfl⟩⟩
  have e7 := Submodule.finrank_le (V ⊔ U)
  have e8 := Submodule.finrank_le V
  omega


theorem dmap_conj (g u : Mbar M Q) (e : M₀.E) :
    dmap ρ (g * u * g⁻¹) e = (ρ g).toAdd (dmap ρ u ((ρ g⁻¹).toAdd e)) := by
  have hinv : (ρ g).toAdd ((ρ g⁻¹).toAdd e) = e := by
    rw [← act_mul_apply, mul_inv_cancel]
    exact act_one_apply _
  simp only [dmap]
  rw [act_mul_apply, act_mul_apply, map_sub, hinv]

theorem finrank_range_dlin_conj_le (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (g : Mbar M Q) {u : Mbar M Q}
    (hu : u ∈ bar M Q Z0) (hgu : g * u * g⁻¹ ∈ bar M Q (H0 M Z)) :
    Module.finrank K (LinearMap.range (dlin hS (g * u * g⁻¹) hgu)) ≤
      Module.finrank K (hc.VtSub hS.model t) := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  obtain ⟨hψV, -, -⟩ := psi_facts_tbar h310chi hS hs
  have hmapV : ∀ y ∈ LinearMap.range (dlin hS (g * u * g⁻¹) hgu),
      (ρ g⁻¹).toAdd y ∈ hc.VtSub hS.model t := by
    rintro _ ⟨e, rfl⟩
    rw [dlin_apply, dmap_conj, ← act_mul_apply, inv_mul_cancel, act_one_apply]
    have h1 := act_eq_cscal h310chi h52a hMp hS hs hr hZ0 hu ((ρ g⁻¹).toAdd e)
    rw [act_eq_add_dmap] at h1
    rw [add_left_cancel h1]
    exact Submodule.smul_mem _ _ (hψV _)
  let ι : ↥(LinearMap.range (dlin hS (g * u * g⁻¹) hgu)) → ↥(hc.VtSub hS.model t) :=
    fun y => ⟨(ρ g⁻¹).toAdd y, hmapV y y.2⟩
  have hι : Function.Injective ι := by
    intro y y' h
    exact Subtype.ext ((ρ g⁻¹).toAdd.injective (congrArg Subtype.val h))
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hcard := Nat.card_le_card_of_injective ι hι
  have e1 : Nat.card ↥(LinearMap.range (dlin hS (g * u * g⁻¹) hgu)) =
      Nat.card K ^ Module.finrank K ↥(LinearMap.range (dlin hS (g * u * g⁻¹) hgu)) :=
    Module.natCard_eq_pow_finrank
  have e2 : Nat.card ↥(hc.VtSub hS.model t) =
      Nat.card K ^ Module.finrank K ↥(hc.VtSub hS.model t) := Module.natCard_eq_pow_finrank
  rw [e1, e2] at hcard
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp hcard

theorem dmap_dmap_eq_zero_of_piece (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Na Nb : Submodule K ↥(deltaSub hS t)}
    {Mc Md : Submodule K (wvQ hS t)} (hM : IsCompl Mc Md)
    (hcd : ∀ w w' : ↥(wsub hS t), (Submodule.Quotient.mk w : wvQ hS t) ∈ Mc →
      (Submodule.Quotient.mk w' : wvQ hS t) ∈ Md → M₀.B (w : M₀.E) (w' : M₀.E) = 0)
    (hcb : ∀ (w : ↥(wsub hS t)) (f : ↥(deltaSub hS t)), (Submodule.Quotient.mk w : wvQ hS t) ∈ Mc →
      f ∈ Nb → (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0)
    (hda : ∀ (w : ↥(wsub hS t)) (f : ↥(deltaSub hS t)), (Submodule.Quotient.mk w : wvQ hS t) ∈ Md →
      f ∈ Na → (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0)
    {v x : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) (hx : x ∈ bar M Q (hc.CN t))
    (hva : (⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩ : ↥(deltaSub hS t)) ∈ Na)
    (hxb : (⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ : ↥(deltaSub hS t)) ∈ Nb)
    (e : M₀.E) : dmap ρ x (dmap ρ v e) = 0 := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  have hvH := mem_bar_H0_of_CN hv
  obtain ⟨-, hvW, hvE⟩ := dmap_CN_facts h310chi h52a hS hs hr hv
  obtain ⟨hnd, hrefl⟩ := bilin_nondegenerate_isRefl (M₀ := M₀)
  have hadj : ∀ y, ∀ w ∈ wsub hS t, M₀.B (dmap ρ v y) w = -M₀.B y (dmap ρ v w) := fun y w hw =>
    bilin_D_right (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t)
      (D := dlin hS v hvH) (dmap_iso hS hvH) (fun x => hvE x) (fun w hw => hvW w hw)
      (fun w hw v hv => bilin_wsub_vsub hS t hw hv) y hw
  set w : ↥(wsub hS t) := ⟨dmap ρ v e, hvE e⟩ with hwdef
  let Bw : ↥(wsub hS t) →ₗ[K] ↥(wsub hS t) →ₗ[K] K :=
    M₀.B.compl₁₂ (wsub hS t).subtype (wsub hS t).subtype
  have hBw : ∀ a a' : ↥(wsub hS t), Bw a a' = M₀.B (a : M₀.E) (a' : M₀.E) := fun a a' => rfl
  have hle : vInW hS t ≤ LinearMap.ker Bw := by
    intro a ha
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun a' => ?_)
    rw [hBw, LinearMap.zero_apply]
    exact bilin_vsub_wsub hS t ((mem_vInW hS t).mp ha) a'.2
  have hle' : vInW hS t ≤ LinearMap.ker Bw.flip := by
    intro a ha
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun a' => ?_)
    rw [LinearMap.flip_apply, hBw, LinearMap.zero_apply]
    exact bilin_wsub_vsub hS t a'.2 ((mem_vInW hS t).mp ha)
  let Bq : wvQ hS t →ₗ[K] wvQ hS t →ₗ[K] K := LinearMap.liftQ₂ (vInW hS t) (vInW hS t) Bw hle hle'
  have hBq : ∀ a a' : ↥(wsub hS t), Bq (Submodule.Quotient.mk a) (Submodule.Quotient.mk a') =
      M₀.B (a : M₀.E) (a' : M₀.E) := fun a a' => rfl
  have hskew : ∀ m m' : wvQ hS t, Bq m m' = -Bq m' m := by
    intro m m'
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ m'
    rw [hBq, hBq]
    exact Tim79.QuadModel.B_comm _ _
  have hcdq : ∀ m ∈ Mc, ∀ m' ∈ Md, Bq m m' = 0 := by
    intro m hm m' hm'
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ m'
    rw [hBq]
    exact hcd a a' hm hm'
  have hndq : ∀ m : wvQ hS t, (∀ m', Bq m m' = 0) → m = 0 := by
    intro m hm
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine (Submodule.Quotient.mk_eq_zero _).mpr ((mem_vInW hS t).mpr ?_)
    have hW := wsub_eq_orthogonal hS t
    have hWW : M₀.B.orthogonal (wsub hS t) = hc.VtSub hS.model t := by
      rw [hW]; exact LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl _
    rw [← hWW, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have h1 := hm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [hBq] at h1
    show M₀.B y a = 0
    rw [Tim79.QuadModel.B_comm, h1, neg_zero]
  have hwMd : ∀ m' ∈ Md, Bq (Submodule.Quotient.mk w) m' = 0 := by
    intro m' hm'
    obtain ⟨w', rfl⟩ := Submodule.Quotient.mk_surjective _ m'
    rw [hBq]
    show M₀.B (dmap ρ v e) w' = 0
    rw [hadj e w' w'.2]
    have h1 := hda w' ⟨delta hS t v hvH, delta_mem_deltaSub hS hv⟩ hm' hva
    rw [delta_apply] at h1
    rw [h1, map_zero, neg_zero]
  have hmem : (Submodule.Quotient.mk w : wvQ hS t) ∈ Mc ⊔ Md := by
    rw [hM.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨mc, hmc, md, hmd, hsum⟩ := Submodule.mem_sup.mp hmem
  have hmd0 : md = 0 := by
    refine hndq md fun m' => ?_
    have hm' : m' ∈ Mc ⊔ Md := by rw [hM.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨ac, hac, ad, had, rfl⟩ := Submodule.mem_sup.mp hm'
    have e1 : md = Submodule.Quotient.mk w - mc := by rw [← hsum]; abel
    rw [map_add, hskew md ac, hcdq ac hac md hmd, neg_zero, zero_add, e1, map_sub,
      LinearMap.sub_apply, hwMd ad had, hcdq mc hmc ad had, sub_zero]
  have hwc : (Submodule.Quotient.mk w : wvQ hS t) ∈ Mc := by
    rw [← hsum, hmd0, add_zero]
    exact hmc
  have h1 := hcb w ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ hwc hxb
  rw [delta_apply] at h1
  exact h1


theorem conj_delta_mem_piece (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {N₁ N₂ : Submodule K ↥(deltaSub hS t)}
    (hN : IsCompl N₁ N₂)
    (hT : ∀ f ∈ N₁, ∀ f' ∈ N₂, f ≠ 0 → f' ≠ 0 →
      5 ≤ Module.finrank K (LinearMap.range ((f + f' : ↥(deltaSub hS t)) :
        ↥(wsub hS t) →ₗ[K] M₀.E)))
    {g : G} (hgM : g ∈ M) (hV' : conjSubgroup g Z0 ≤ hc.CN t) :
    (∀ v (hv : v ∈ bar M Q (conjSubgroup g Z0)),
      (⟨delta hS t v (mem_bar_H0_of_CN (bar_mono' hV' hv)),
        delta_mem_deltaSub hS (bar_mono' hV' hv)⟩ : ↥(deltaSub hS t)) ∈ N₁) ∨
    (∀ v (hv : v ∈ bar M Q (conjSubgroup g Z0)),
      (⟨delta hS t v (mem_bar_H0_of_CN (bar_mono' hV' hv)),
        delta_mem_deltaSub hS (bar_mono' hV' hv)⟩ : ↥(deltaSub hS t)) ∈ N₂) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hV8 := finrank_vtSub hS ht hp
  set Dl : ∀ v, v ∈ bar M Q (conjSubgroup g Z0) → ↥(deltaSub hS t) := fun v hv =>
    ⟨delta hS t v (mem_bar_H0_of_CN (bar_mono' hV' hv)), delta_mem_deltaSub hS (bar_mono' hV' hv)⟩
    with hDl
  have hone : ∀ v (hv : v ∈ bar M Q (conjSubgroup g Z0)), Dl v hv ∈ N₁ ∨ Dl v hv ∈ N₂ := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := exists_of_mem_bar hv
    have hu : g⁻¹ * (v' : G) * g ∈ Z0 := mem_conjSubgroup.mp hv'
    have huM : g⁻¹ * (v' : G) * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) v'.2) hgM
    let gm : ↥M := ⟨g, hgM⟩
    let um : ↥M := ⟨g⁻¹ * (v' : G) * g, huM⟩
    have hvm : v' = gm * um * gm⁻¹ := Subtype.ext (by
      show (v' : G) = g * (g⁻¹ * (v' : G) * g) * g⁻¹
      group)
    have hub : (QuotientGroup.mk um : Mbar M Q) ∈ bar M Q Z0 := mk_mem_bar um hu
    have hvN := bar_mono' hV' hv
    have hvb : (QuotientGroup.mk v' : Mbar M Q) =
        QuotientGroup.mk gm * QuotientGroup.mk um * (QuotientGroup.mk gm)⁻¹ := by
      rw [hvm]; rfl
    have h1 := two_mul_finrank_range_delta_le h310chi h52a hS hs hr hvN
    have h2 := finrank_range_dlin_conj_le h310chi h52a hMp hS hs hr hZ0 (QuotientGroup.mk gm)
      hub (by rw [← hvb]; exact mem_bar_H0_of_CN hvN)
    have e1 : LinearMap.range (dlin hS (QuotientGroup.mk gm * QuotientGroup.mk um *
        (QuotientGroup.mk gm)⁻¹) (by rw [← hvb]; exact mem_bar_H0_of_CN hvN)) =
        LinearMap.range (dlin hS (QuotientGroup.mk v') (mem_bar_H0_of_CN hvN)) := by
      congr 2
      exact hvb.symm
    rw [e1, hV8] at h2
    have hmem : Dl _ hv ∈ N₁ ⊔ N₂ := by rw [hN.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨f₁, hf₁, f₂, hf₂, hsum⟩ := Submodule.mem_sup.mp hmem
    by_cases h₁ : f₁ = 0
    · right
      rw [← hsum, h₁, zero_add]
      exact hf₂
    by_cases h₂ : f₂ = 0
    · left
      rw [← hsum, h₂, add_zero]
      exact hf₁
    exfalso
    have h3 := hT f₁ hf₁ f₂ hf₂ h₁ h₂
    rw [hsum] at h3
    have e2 : ((Dl _ hv : ↥(deltaSub hS t)) : ↥(wsub hS t) →ₗ[K] M₀.E) =
        delta hS t (QuotientGroup.mk v') (mem_bar_H0_of_CN hvN) := rfl
    rw [e2] at h3
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha, ha₁⟩, ⟨c, hc', hc₂⟩⟩ := hcon
  have ha₂ := (hone a ha).resolve_left ha₁
  have hc₁ := (hone c hc').resolve_right hc₂
  have hac : a * c ∈ bar M Q (conjSubgroup g Z0) := Subgroup.mul_mem _ ha hc'
  have hsum : Dl (a * c) hac = Dl a ha + Dl c hc' := by
    refine Subtype.ext ?_
    exact delta_mul h310chi h52a hS hs hr (bar_mono' hV' ha) (bar_mono' hV' hc')
  rcases hone _ hac with h | h
  · rw [hsum] at h
    have : Dl a ha ∈ N₁ := by
      have h' := N₁.sub_mem h hc₁
      rwa [add_sub_cancel_right] at h'
    exact ha₁ this
  · rw [hsum] at h
    have : Dl c hc' ∈ N₂ := by
      have h' := N₂.sub_mem h ha₂
      rwa [add_sub_cancel_left] at h'
    exact hc₂ this


theorem false_of_conj_le_piece (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) (hY : Sec713YStatement) (hCent : Sec715CentStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (hp : OmegaPlusNat hc t 4) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    {Na Nb : Submodule K ↥(deltaSub hS t)} (hN : IsCompl Na Nb)
    (ha : IsIrrSub (deltaAct hS hs.toSec5.mem) Na) (hb : IsIrrSub (deltaAct hS hs.toSec5.mem) Nb)
    (hpres : ∀ T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t),
      (∀ x f, T (deltaAct hS hs.toSec5.mem x f) = deltaAct hS hs.toSec5.mem x (T f)) →
        (∀ f ∈ Na, T f ∈ Na) ∧ (∀ f ∈ Nb, T f ∈ Nb))
    {Mc Md : Submodule K (wvQ hS t)} (hM : IsCompl Mc Md)
    (hcd : ∀ w w' : ↥(wsub hS t), (Submodule.Quotient.mk w : wvQ hS t) ∈ Mc →
      (Submodule.Quotient.mk w' : wvQ hS t) ∈ Md → M₀.B (w : M₀.E) (w' : M₀.E) = 0)
    (hcb : ∀ (w : ↥(wsub hS t)) (f : ↥(deltaSub hS t)), (Submodule.Quotient.mk w : wvQ hS t) ∈ Mc →
      f ∈ Nb → (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0)
    (hda : ∀ (w : ↥(wsub hS t)) (f : ↥(deltaSub hS t)), (Submodule.Quotient.mk w : wvQ hS t) ∈ Md →
      f ∈ Na → (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0)
    (hab : ∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t)) (y : Mbar M Q)
      (hy : y ∈ bar M Q (hc.CN t)),
      (⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ : ↥(deltaSub hS t)) ∈ Na →
      (⟨delta hS t y (mem_bar_H0_of_CN hy), delta_mem_deltaSub hS hy⟩ : ↥(deltaSub hS t)) ∈ Nb →
        x * y = y * x)
    {g : G} (hgM : g ∈ M) (hV' : conjSubgroup g Z0 ≤ hc.CN t) (hne : conjSubgroup g Z0 ≠ Z0)
    (hVa : ∀ v (hv : v ∈ bar M Q (conjSubgroup g Z0)),
      (⟨delta hS t v (mem_bar_H0_of_CN (bar_mono' hV' hv)),
        delta_mem_deltaSub hS (bar_mono' hV' hv)⟩ : ↥(deltaSub hS t)) ∈ Na) : False := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hNM : ∀ x ∈ hc.CN t, x ∈ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  obtain ⟨hD2, -, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hN2 : IsPGroup 2 ↥(hc.CN t) :=
    hD2.to_le (sec715_CN_le_O2NormPre h34 h51 hA hZt hZcard hc hs hZ0)
  let gm : ↥M := ⟨g, hgM⟩
  set gb : Mbar M Q := QuotientGroup.mk gm with hgb
  obtain ⟨v, hvZ, hvQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  let vm : ↥M := ⟨v, hc.centre_le_M t hZ0 hvZ⟩
  set vb : Mbar M Q := QuotientGroup.mk vm with hvbdef
  have hvbZ : vb ∈ bar M Q Z0 := mk_mem_bar vm hvZ
  have hv'V : gb * vb * gb⁻¹ ∈ bar M Q (conjSubgroup g Z0) := by
    refine mk_mem_bar (gm * vm * gm⁻¹) (mem_conjSubgroup.mpr ?_)
    show g⁻¹ * (g * v * g⁻¹) * g ∈ Z0
    rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
    exact hvZ
  have hv'N := bar_mono' hV' hv'V
  have hv'a := hVa _ hv'V
  have hvb1 : vb ≠ 1 := by
    intro h
    exact hvQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff vm).mp h))
  have hc0 : cscal hc ρ ht vb ≠ 0 := fun h =>
    hvb1 ((cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 hvbZ).mp h)
  obtain ⟨-, hψsurj, -⟩ := psi_facts_tbar h310chi hS hs
  obtain ⟨-, -, htH⟩ := tbar_mem hc hs
  have hVrange : ∀ e' ∈ hc.VtSub hS.model t, ∃ e, dmap ρ vb e = e' := by
    intro e' he'
    obtain ⟨e₀, he₀⟩ := hψsurj e' he'
    refine ⟨(cscal hc ρ ht vb)⁻¹ • e₀, ?_⟩
    have h1 := act_eq_cscal h310chi h52a hMp hS hs hr hZ0 hvbZ ((cscal hc ρ ht vb)⁻¹ • e₀)
    rw [act_eq_add_dmap] at h1
    rw [add_left_cancel h1, dmap_smul hS htH, smul_smul, mul_inv_cancel₀ hc0, one_smul, he₀]
  have hgg : ∀ e, (ρ gb⁻¹).toAdd ((ρ gb).toAdd e) = e := fun e => by
    rw [← act_mul_apply, inv_mul_cancel]; exact act_one_apply _
  have hxconj : ∀ x (hx : x ∈ hc.CN t),
      (⟨delta hS t (QuotientGroup.mk (⟨x, hNM x hx⟩ : ↥M)) (mem_bar_H0_of_CN (mk_mem_bar _ hx)),
        delta_mem_deltaSub hS (mk_mem_bar _ hx)⟩ : ↥(deltaSub hS t)) ∈ Nb →
      g⁻¹ * x * g ∈ hc.CN t := by
    intro x hx hxb
    let xm : ↥M := ⟨x, hNM x hx⟩
    have hxbN : (QuotientGroup.mk xm : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar xm hx
    have hxV' : ∀ u ∈ conjSubgroup g Z0, ⁅x, u⁆ ∈ Q := by
      intro u hu
      let um : ↥M := ⟨u, hNM u (hV' hu)⟩
      have hub : (QuotientGroup.mk um : Mbar M Q) ∈ bar M Q (conjSubgroup g Z0) := mk_mem_bar um hu
      have h1 := hab _ (bar_mono' hV' hub) _ hxbN (hVa _ hub) hxb
      exact (mk_commute_iff xm um).mp h1.symm
    have hyM : g⁻¹ * x * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) xm.2) hgM
    have hyH : g⁻¹ * x * g ∈ H0 M Z := by
      have h1 := hc.conj_mem_H0 (M.inv_mem hgM) (hc.Rt_le_H0 t (Ctx.mem_CN.mp hx).1)
      rwa [inv_inv] at h1
    have hyK : g⁻¹ * x * g ∈ NormH0 M Z Z0 := by
      refine ⟨hyH, Subgroup.mem_normalizer_fintype fun u hu => ?_⟩
      have hu' : g * u * g⁻¹ ∈ conjSubgroup g Z0 := mem_conjSubgroup.mpr (by group; exact hu)
      have hcQ := hxV' _ hu'
      have hq : g⁻¹ * ⁅x, g * u * g⁻¹⁆ * g ∈ Q := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hgM)) _).mp hcQ
        rwa [inv_inv] at h1
      have e1 : g⁻¹ * x * g * u * (g⁻¹ * x * g)⁻¹ = (g⁻¹ * ⁅x, g * u * g⁻¹⁆ * g) * u := by
        rw [commutatorElement_def]; group
      rw [e1]
      exact Z0.mul_mem (hQZ0 hq) hu
    have hy2 : ∃ k : ℕ, (g⁻¹ * x * g) ^ 2 ^ k ∈ Q := by
      obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
      refine ⟨k, ?_⟩
      have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have e1 : (g⁻¹ * x * g) ^ 2 ^ k = g⁻¹ * x ^ 2 ^ k * g⁻¹⁻¹ := by
        rw [← conj_pow, inv_inv]
      rw [e1, h1, mul_one, inv_inv, inv_mul_cancel]
      exact Q.one_mem
    have hyV : ∀ w ∈ Vt M (LB M Q B) B Z t, ⁅g⁻¹ * x * g, w⁆ ∈ Z := by
      intro w hw
      have hwQ : w ∈ Q := hc.Vt_le_Q t hw
      refine (comm_mem_Z_iff_act_eq hS ⟨g⁻¹ * x * g, hyM⟩ hwQ).mpr ?_
      have hwV : M₀.π w ∈ hc.VtSub hS.model t :=
        (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hw hwQ)
      obtain ⟨e, he⟩ := hVrange _ hwV
      rw [← he]
      have hyb : (QuotientGroup.mk (⟨g⁻¹ * x * g, hyM⟩ : ↥M) : Mbar M Q) =
          gb⁻¹ * QuotientGroup.mk xm * gb := rfl
      have hstep := dmap_dmap_eq_zero_of_piece h310chi h52a hS hs hr hM hcd hcb hda hv'N hxbN
        hv'a hxb ((ρ gb).toAdd e)
      rw [hyb, act_mul_apply, act_mul_apply]
      have e1 : (ρ gb).toAdd (dmap ρ vb e) = dmap ρ (gb * vb * gb⁻¹) ((ρ gb).toAdd e) := by
        rw [dmap_conj, hgg]
      rw [e1, act_eq_add_dmap (QuotientGroup.mk xm), hstep, add_zero, dmap_conj, hgg, hgg]
    exact mem_CN_of_centralizes_configC h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN hCRW
      hMp hY hCent hS hs hr hp hZ0 hZN hSΔ hN ha hb hpres hyK hy2 hyV
  obtain ⟨hbne, -, -⟩ := hb
  obtain ⟨f, hfb, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbne
  obtain ⟨x₁b, hx₁b, hf⟩ := hSΔ f f.2
  obtain ⟨x₁, hx₁N, rfl⟩ := exists_of_mem_bar hx₁b
  have hx₁Z : (x₁ : G) ∉ Z0 := by
    intro h
    have hR : (QuotientGroup.mk x₁ : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) :=
      mk_mem_bar x₁ (Ctx.mem_CN.mp hx₁N).1
    have h0 := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mpr (mk_mem_bar x₁ h)
    exact hf0 (Subtype.ext (hf.trans h0))
  have hex : ∃ y ∈ hc.CN t, ⁅(x₁ : G), y⁆ ∉ Q := by
    by_contra hcon
    push Not at hcon
    exact hx₁Z ((hZN _).mpr ⟨hx₁N, hcon⟩)
  obtain ⟨y, hyN, hyQ⟩ := hex
  let ym : ↥M := ⟨y, hNM y hyN⟩
  have hybN : (QuotientGroup.mk ym : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar ym hyN
  have hmem : (⟨delta hS t _ (mem_bar_H0_of_CN hybN), delta_mem_deltaSub hS hybN⟩ :
      ↥(deltaSub hS t)) ∈ Na ⊔ Nb := by rw [hN.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨fa, hfa, fb, hfb', hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨ab, hab', hfa'⟩ := hSΔ fa fa.2
  obtain ⟨bb, hbb, hfb''⟩ := hSΔ fb fb.2
  have hfaE : fa = ⟨delta hS t ab (mem_bar_H0_of_CN hab'), delta_mem_deltaSub hS hab'⟩ :=
    Subtype.ext hfa'
  have hfbE : fb = ⟨delta hS t bb (mem_bar_H0_of_CN hbb), delta_mem_deltaSub hS hbb⟩ :=
    Subtype.ext hfb''
  have hx₁b' : (⟨delta hS t _ (mem_bar_H0_of_CN hx₁b), delta_mem_deltaSub hS hx₁b⟩ :
      ↥(deltaSub hS t)) ∈ Nb := by
    have : f = ⟨delta hS t _ (mem_bar_H0_of_CN hx₁b), delta_mem_deltaSub hS hx₁b⟩ := Subtype.ext hf
    rw [← this]; exact hfb
  have hca := hab ab hab' _ hx₁b (hfaE ▸ hfa) hx₁b'
  have habN : ab * bb ∈ bar M Q (hc.CN t) := Subgroup.mul_mem _ hab' hbb
  have hzN : (QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹ ∈ bar M Q (hc.CN t) :=
    Subgroup.mul_mem _ hybN (Subgroup.inv_mem _ habN)
  have hzR : (QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹ ∈ bar M Q (Rt M (LB M Q B) t) :=
    bar_mono' (fun z hz => (Ctx.mem_CN.mp hz).1) hzN
  have hzZ : (QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹ ∈ bar M Q Z0 := by
    refine (delta_eq_zero_iff hCRW hMp hS hs hZ0 hzR).mp ?_
    have hd1 := delta_mul h310chi h52a hS hs hr hzN habN
    have hd2 := delta_mul h310chi h52a hS hs hr hab' hbb
    have e1 : (QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹ * (ab * bb) = QuotientGroup.mk ym := by
      group
    have hy' : delta hS t (QuotientGroup.mk ym) (mem_bar_H0_of_CN hybN) =
        delta hS t ab (mem_bar_H0_of_CN hab') + delta hS t bb (mem_bar_H0_of_CN hbb) := by
      have h1 := congrArg Subtype.val hsum
      rw [hfaE, hfbE] at h1
      exact h1.symm
    rw [delta_congr hS t e1.symm _ (Subgroup.mul_mem _ (mem_bar_H0_of_CN hzN)
      (mem_bar_H0_of_CN habN)), hd1, hd2] at hy'
    have h2 := congrArg (fun f => f - (delta hS t ab (mem_bar_H0_of_CN hab') +
      delta hS t bb (mem_bar_H0_of_CN hbb))) hy'
    simp only [add_sub_cancel_right, sub_self] at h2
    rw [← h2]
  have hcz : (QuotientGroup.mk x₁ : Mbar M Q) * ((QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹) =
      ((QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹) * QuotientGroup.mk x₁ := by
    obtain ⟨z', hz', hz'e⟩ := exists_of_mem_bar hzZ
    rw [← hz'e]
    exact (endg_comm_centre hZ0 (hc.Rt_le_M t) hz' (bar_mono' (fun z hz => (Ctx.mem_CN.mp hz).1)
      (mk_mem_bar x₁ hx₁N))).symm
  have hnc : ¬ (QuotientGroup.mk x₁ : Mbar M Q) * bb = bb * QuotientGroup.mk x₁ := by
    intro hcb'
    apply hyQ
    have hcy : Commute (QuotientGroup.mk' (Q.subgroupOf M) x₁)
        (QuotientGroup.mk' (Q.subgroupOf M) ym) := by
      have e1 : (QuotientGroup.mk ym : Mbar M Q) =
          ((QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹) * ab * bb := by group
      show (QuotientGroup.mk x₁ : Mbar M Q) * QuotientGroup.mk ym =
        QuotientGroup.mk ym * QuotientGroup.mk x₁
      rw [e1]
      have c1 : Commute (QuotientGroup.mk x₁ : Mbar M Q)
          ((QuotientGroup.mk ym : Mbar M Q) * (ab * bb)⁻¹) := hcz
      have c2 : Commute (QuotientGroup.mk x₁ : Mbar M Q) ab := hca.symm
      have c3 : Commute (QuotientGroup.mk x₁ : Mbar M Q) bb := hcb'
      exact ((c1.mul_right c2).mul_right c3).eq
    exact (mk_commute_iff x₁ ym).mp hcy
  obtain ⟨x₂, hx₂N, rfl⟩ := exists_of_mem_bar hbb
  have hc12 : ⁅(x₁ : G), (x₂ : G)⁆ ∉ Q := by
    intro h
    exact hnc ((mk_commute_iff x₁ x₂).mpr h).eq
  have hx₂b : (⟨delta hS t _ (mem_bar_H0_of_CN hbb), delta_mem_deltaSub hS hbb⟩ :
      ↥(deltaSub hS t)) ∈ Nb := hfbE ▸ hfb'
  have hy₁ := hxconj x₁ hx₁N hx₁b'
  have hy₂ := hxconj x₂ hx₂N hx₂b
  have hcZ : ⁅(x₁ : G), (x₂ : G)⁆ ∈ Z0 :=
    hCommN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hx₁N hx₂N)
  have hcZg : ⁅g⁻¹ * (x₁ : G) * g, g⁻¹ * (x₂ : G) * g⁆ ∈ Z0 :=
    hCommN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hy₁ hy₂)
  have e2 : g * ⁅g⁻¹ * (x₁ : G) * g, g⁻¹ * (x₂ : G) * g⁆ * g⁻¹ = ⁅(x₁ : G), (x₂ : G)⁆ := by
    simp only [commutatorElement_def]; group
  have hnQ : ⁅g⁻¹ * (x₁ : G) * g, g⁻¹ * (x₂ : G) * g⁆ ∉ Q := by
    intro h
    apply hc12
    rw [← e2]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) _).mp h
  have hgN := hTI g hgM _ hcZg hnQ (by rw [e2]; exact hcZ)
  exact hne (conjSubgroup_eq_self_iff.mpr hgN)


theorem configC_false (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) (hY : Sec713YStatement) (hCent : Sec715CentStatement)
    (hConj : Sec715ConjStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G}
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) (hn : n = 16)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    {M₃ M₄ : Submodule K (wvQ hS t)} {N₄ N₃ : Submodule K ↥(deltaSub hS t)}
    (hM : IsCompl M₃ M₄) (hN : IsCompl N₄ N₃) (h₄ : IsIrrSub (deltaAct hS hs.toSec5.mem) N₄)
    (h₃ : IsIrrSub (deltaAct hS hs.toSec5.mem) N₃)
    (hpres : ∀ T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t),
      (∀ x f, T (deltaAct hS hs.toSec5.mem x f) = deltaAct hS hs.toSec5.mem x (T f)) →
        (∀ f ∈ N₄, T f ∈ N₄) ∧ (∀ f ∈ N₃, T f ∈ N₃))
    (hM34 : ∀ w w' : ↥(wsub hS t), (Submodule.Quotient.mk w : wvQ hS t) ∈ M₃ →
      (Submodule.Quotient.mk w' : wvQ hS t) ∈ M₄ → M₀.B (w : M₀.E) (w' : M₀.E) = 0)
    (hβ : ∀ (w : ↥(wsub hS t)) (f : ↥(deltaSub hS t)),
      ((Submodule.Quotient.mk w : wvQ hS t) ∈ M₃ → f ∈ N₃ →
        (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0) ∧
      ((Submodule.Quotient.mk w : wvQ hS t) ∈ M₄ → f ∈ N₄ →
        (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0))
    (hc5 : ∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t)) (y : Mbar M Q)
      (hy : y ∈ bar M Q (hc.CN t)),
      (⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ : ↥(deltaSub hS t)) ∈ N₄ →
      (⟨delta hS t y (mem_bar_H0_of_CN hy), delta_mem_deltaSub hS hy⟩ : ↥(deltaSub hS t)) ∈ N₃ →
        x * y = y * x)
    (hT : ∀ f ∈ N₄, ∀ f' ∈ N₃, f ≠ 0 → f' ≠ 0 →
      5 ≤ Module.finrank K (LinearMap.range ((f + f' : ↥(deltaSub hS t)) :
        ↥(wsub hS t) →ₗ[K] M₀.E))) :
    False := by
  obtain ⟨g, hgM, hV', hne⟩ := hConj G M Q Z B hc n t hs hp hn Z0 hZ0 hZN hTI
  rcases conj_delta_mem_piece h310chi h52a hMp hS hs hr hp hZ0 hN hT hgM hV' with h | h
  · exact false_of_conj_le_piece h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN hCRW hMp hY
      hCent hS hs hr hp hZ0 hZN hTI hSΔ hN h₄ h₃ hpres hM hM34 (fun w f hw hf => (hβ w f).1 hw hf)
      (fun w f hw hf => (hβ w f).2 hw hf) hc5 hgM hV' hne h
  · refine false_of_conj_le_piece h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN hCRW hMp hY
      hCent hS hs hr hp hZ0 hZN hTI hSΔ hN.symm h₃ h₄ (fun T hT' => (hpres T hT').symm) hM.symm
      (fun w w' hw hw' => ?_) (fun w f hw hf => (hβ w f).2 hw hf)
      (fun w f hw hf => (hβ w f).1 hw hf) (fun x hx y hy hx3 hy4 => (hc5 y hy x hx hy4 hx3).symm)
      hgM hV' hne h
    rw [Tim79.QuadModel.B_comm, hM34 w' w hw' hw, neg_zero]


theorem false_of_isLayerConfigC (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) (hY : Sec713YStatement) (hCent : Sec715CentStatement)
    (hConj : Sec715ConjStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G}
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) (hn : n = 16)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    (hC : IsLayerConfigC hS hs.toSec5.mem) : False := by
  obtain ⟨M₃, M₄, N₄, N₃, hM, hN, h₄, h₃, hpres, hM34, hβ, hc5, hT⟩ := hC
  exact configC_false h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN hCRW hMp hY hCent hConj
    hS hs hr hp hn hZ0 hZN hTI hSΔ hM hN h₄ h₃ hpres hM34 hβ hc5 hT

end S715L

end CFSG.RankThree.GF2n.Stroth80
