module

public import CFSG.RankThree.GF2n.Stroth80.Sec78CentreStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal
public import CFSG.RankThree.GF2n.Stroth80.Sec7LBElation

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step77TameCommNStatement (d : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t) →
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ (1 + d) →
    ∀ y ∈ hc.CN t, ⁅y, s⁆ ∈ Q

theorem sec7_adjoint_zero {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (hrefl : B.IsRefl) (U : Submodule K E) (S : E ≃ₗ[K] E)
    (hiso : ∀ a c, B (S a) (S c) = B a c) (hSU : ∀ u ∈ U, S u = u) (w y : E)
    (hw : ∀ u ∈ U, B u w = 0) (hy : S y - y ∈ U) : B (S w - w) y = 0 := by
  have h3 : S.symm y - y ∈ U := by
    have hu : S.symm (S y - y) = S y - y := by
      apply S.injective
      rw [S.apply_symm_apply]
      exact (hSU _ hy).symm
    have e : S.symm y - y = -(S.symm (S y - y)) := by
      rw [map_sub, S.symm_apply_apply]
      abel
    rw [e, hu]
    exact U.neg_mem hy
  have h4 : B (S w) y = B w (S.symm y) := by
    have := hiso w (S.symm y)
    rwa [S.apply_symm_apply] at this
  have h5 : B w (S.symm y - y) = 0 := LinearMap.IsRefl.eq_zero hrefl (hw _ h3)
  calc B (S w - w) y = B w (S.symm y - y) := by
        rw [map_sub, LinearMap.sub_apply, h4, map_sub]
    _ = 0 := h5

theorem sec7_tame_perp_core {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (hrefl : B.IsRefl) (T U : Submodule K E) (b : E)
    (hT : ∀ v, (∀ u ∈ T, B v u = 0) → v ∈ T) (S' : E ≃ₗ[K] E)
    (hiso : ∀ a c, B (S' a) (S' c) = B a c) (hSU : ∀ u ∈ U, S' u = u) (hbT : S' b = b)
    {ι : Type*} (φ : ι → (E ≃ₗ[K] E))
    (hel : ∀ i, ∀ x ∈ T, ∃ c : K, φ i x - x = c • b)
    (hcomm : ∀ i e, φ i (S' e) = S' (φ i e))
    (hfix : ∀ e, (∀ i, φ i e = e) → e ∈ U)
    (w : E) (hw : ∀ u ∈ U, B u w = 0) : S' w - w ∈ T := by
  have h1 : ∀ x ∈ T, S' x - x ∈ U := by
    intro x hx
    refine hfix _ fun i => ?_
    obtain ⟨c, hc⟩ := hel i x hx
    have hx' : φ i x = x + c • b := by
      rw [← hc]
      abel
    rw [map_sub, hcomm, hx', map_add, map_smul, hbT]
    abel
  exact hT _ fun x hx => sec7_adjoint_zero B hrefl U S' hiso hSU w x hw (h1 x hx)

theorem sec7_tame_comm_core {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement) (hCV : Sec7CVStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    {s₁ : G} (hs₁M : s₁ ∈ M) (hs₁H : s₁ ∈ H0 M Z)
    (hs₁V : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅s₁, v⁆ ∈ Z)
    (hs₁D : ∀ y ∈ LB M Q B ⊓ hc.CN t, ⁅y, s₁⁆ ∈ Q) {w : G} (hwQ : w ∈ Q)
    (hwU : M₀.π w ∈ M₀.B.orthogonal (hc.VtSub hS.model t)) :
    M₀.π ⁅s₁, w⁆ ∈ M₀.img (Q ⊓ QB B) := by
  classical
  have hcard35 := stroth_3_5 h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨T, bT, hT, hfT, hLag, hb0, hB, hact, -⟩ :=
    sec7_LB_elation hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hcard35.2.2.1
      hcard35.2.2.2 hS.model
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hs₁bar : (QuotientGroup.mk (⟨s₁, hs₁M⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨s₁, hs₁M⟩, Subgroup.mem_subgroupOf.mpr hs₁H, rfl⟩
  let S' : M₀.E ≃ₗ[K] M₀.E :=
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨s₁, hs₁M⟩ : ↥M))).toAdd (hS.lin _ hs₁bar)
  have hiso : ∀ a c, M₀.B (S' a) (S' c) = M₀.B a c := fun a c => hS.iso _ hs₁bar a c
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hSU : ∀ u ∈ hc.VtSub hS.model t, S' u = u := by
    intro u hu
    obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    have h1 := sec7_act_sub_comm hc M₀ ρ b hS hs₁M hvQ
    have h2 : M₀.π ⁅s₁, v⁆ = 0 := (M₀.π_ker _ (sec7_comm_mem_Q hc hs₁M hvQ)).mpr (hs₁V v hvV)
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  have hbimg : (bT : M₀.E) ∈ M₀.img B := (hB bT).mpr ⟨1, (one_smul K _).symm⟩
  have hbU : (bT : M₀.E) ∈ hc.VtSub hS.model t :=
    (hc.mem_VtSub hS.model t).mpr (M₀.img_mono (hc.B_le_Vt hs.toSec5.mem) hbimg)
  have hyM : ∀ y : ↥(LB M Q B ⊓ hc.CN t), (y : G) ∈ M := fun y => hc.LB_le_M y.2.1
  have hybar : ∀ y : ↥(LB M Q B ⊓ hc.CN t),
      (QuotientGroup.mk (⟨(y : G), hyM y⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) := fun y =>
    Subgroup.mem_map.mpr ⟨⟨(y : G), hyM y⟩,
      Subgroup.mem_subgroupOf.mpr (hc.LB_le_H0 y.2.1), rfl⟩
  let φ : ↥(LB M Q B ⊓ hc.CN t) → (M₀.E ≃ₗ[K] M₀.E) := fun y =>
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨(y : G), hyM y⟩ : ↥M))).toAdd
      (hS.lin _ (hybar y))
  have hφconj : ∀ (y : ↥(LB M Q B ⊓ hc.CN t)), ∀ x ∈ Q,
      M₀.π ((y : G) * x * (y : G)⁻¹) = φ y (M₀.π x) := fun y x hx =>
    hS.conj ⟨(y : G), hyM y⟩ x hx
  have hel : ∀ (y : ↥(LB M Q B ⊓ hc.CN t)), ∀ x ∈ T, ∃ c : K, φ y x - x = c • (bT : M₀.E) :=
    fun y x hx => (hact (y : G) y.2.1 (φ y) (hφconj y)).2.1 x hx
  have hcomm : ∀ (y : ↥(LB M Q B ⊓ hc.CN t)) (e : M₀.E), φ y (S' e) = S' (φ y e) := by
    intro y e
    have hc' : Commute (QuotientGroup.mk' (Q.subgroupOf M) (⟨(y : G), hyM y⟩ : ↥M))
        (QuotientGroup.mk' (Q.subgroupOf M) (⟨s₁, hs₁M⟩ : ↥M)) :=
      (mk_commute_iff _ _).mpr (hs₁D y y.2)
    have h1 : (QuotientGroup.mk (⟨(y : G), hyM y⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨s₁, hs₁M⟩ : ↥M) =
        QuotientGroup.mk (⟨s₁, hs₁M⟩ : ↥M) * QuotientGroup.mk (⟨(y : G), hyM y⟩ : ↥M) := hc'.eq
    have h2 := congrArg (fun a : Mbar M Q => (ρ a).toAdd e) h1
    simp only [act_mul_apply] at h2
    exact h2
  have hfix : ∀ e, (∀ y : ↥(LB M Q B ⊓ hc.CN t), φ y e = e) → e ∈ hc.VtSub hS.model t := by
    intro e he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hxV : x ∈ Vt M (LB M Q B) B Z t := by
      refine (hCV G M Q Z B hc n t hs x hxQ).mpr fun y hy => ?_
      have h1 := sec7_act_sub_comm hc M₀ ρ b hS (hc.LB_le_M hy.1) hxQ
      have h2 : (ρ (QuotientGroup.mk (⟨y, hc.LB_le_M hy.1⟩ : ↥M))).toAdd (M₀.π x) = M₀.π x :=
        he ⟨y, hy⟩
      rw [h2, sub_self] at h1
      exact (M₀.π_ker _ (sec7_comm_mem_Q hc (hc.LB_le_M hy.1) hxQ)).mp h1.symm
    exact (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hxV hxQ)
  have hw' : ∀ u ∈ hc.VtSub hS.model t, M₀.B u (M₀.π w) = 0 := fun u hu =>
    LinearMap.BilinForm.isOrtho_def.mp (LinearMap.BilinForm.mem_orthogonal_iff.mp hwU u hu)
  have hres := sec7_tame_perp_core M₀.B hr T (hc.VtSub hS.model t) (bT : M₀.E) hLag S' hiso
    hSU (hSU _ hbU) φ hel hcomm hfix (M₀.π w) hw'
  have hsub := sec7_act_sub_comm hc M₀ ρ b hS hs₁M hwQ
  have hres' : (ρ (QuotientGroup.mk (⟨s₁, hs₁M⟩ : ↥M))).toAdd (M₀.π w) - M₀.π w ∈ T := hres
  rw [hsub] at hres'
  exact (hT _).mp hres'

theorem sec7_tame_false_of_comm (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (hCV : Sec7CVStatement)
    (hIrr : Sec7VtIrredStatement) (d : ℕ) (hd2 : 2 ≤ d) (hd3 : d ≤ 3)
    (hT2 : Step77TameCommNStatement d) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
        Nat.card Z ^ (1 + d) → False := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcardV
  classical
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  obtain ⟨ψs, hψs, hrs, hker⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hgM hsM hs1
  obtain ⟨hHcard, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  obtain ⟨hc1, hd4, hdV⟩ := sec7_pair_card_meet hc M₀ ρ b hS hgM ψs hrs hUcard
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
  have hvan := sec7_pair_vanish h71 hc hs hno hgM hs1 hs2
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  have hsH : s ∈ H0 M Z :=
    sec7_mem_H0_of_mul_Q hc (sec7_conj_mem_H0 hc hgM (hc.LB_le_H0 ht)) hs1
  have hddim : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) = d := by
    rw [hcardV, hZK] at hc1
    have h1 : 1 + d = 1 + Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) :=
      Nat.pow_right_injective hK2 hc1
    omega
  have hfR : Module.finrank K (LinearMap.range ψs) = 4 := by
    have hcard : Nat.card (LinearMap.range ψs) = Nat.card K ^ 4 := by
      have h1 : Nat.card (LinearMap.range ψs) = Nat.card (M₀.img (conjSubgroup g
          (Vt M (LB M Q B) B Z t))) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrs)
      rw [h1, sec7_card_img_conj hc M₀ ρ b hS hgM hZV']
      have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card (hc.VtSub hS.model t) := rfl
      rw [h2, hUcard]
    have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range ψs)
    rw [hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ψs hker (hc.VtSub hS.model t)
  rw [hddim, hfR] at hmap
  have hVn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hx) y).mp hy
  have hWn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx y hy =>
    sec7WVOrd_conj_mem hc ht hx hy
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hLZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hsW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Z := by
    let H : Subgroup G := (Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z
    have hHV : H ≤ Vt M (LB M Q B) B Z t := sup_le inf_le_left hZV'
    have hZH : Z ≤ H := le_sup_right
    have hkey : ∀ r ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        r * ⁅s, w⁆ * r⁻¹ ∈ H := by
      intro r hr w hw
      have hrM : r ∈ M := hRM hr
      have hr' : r⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hr
      have hs₁M : r * s * r⁻¹ ∈ M := M.mul_mem (M.mul_mem hrM hsM) (M.inv_mem hrM)
      have hs₁H : r * s * r⁻¹ ∈ H0 M Z := sec7_conj_mem_H0 hc hrM hsH
      have hs₁V : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅r * s * r⁻¹, v⁆ ∈ Z := by
        intro v hv
        have h1 : ⁅r * s * r⁻¹, v⁆ = r * ⁅s, r⁻¹ * v * (r⁻¹)⁻¹⁆ * r⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact hZn r hrM _ (hvan _ (hVn r⁻¹ hr' v hv))
      have hNeq : conjSubgroup r (hc.CN t) = hc.CN t :=
        conjSubgroup_CN_eq hc hrM
          (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr))
          (conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr))
      have hs₁D : ∀ y ∈ LB M Q B ⊓ hc.CN t, ⁅y, r * s * r⁻¹⁆ ∈ Q := by
        intro y hy
        have hy' : y ∈ conjSubgroup r (hc.CN t) := by rw [hNeq]; exact hy.2
        have hk := hT2 G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcardV
          (r⁻¹ * y * r) (mem_conjSubgroup.mp hy')
        have h1 : ⁅y, r * s * r⁻¹⁆ = r * ⁅r⁻¹ * y * r, s⁆ * r⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact (hc.conj_mem_Q_of_mem_M hrM).1 _ hk
      have hw_r : r * w * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := hWn r hr w hw
      have hwU : M₀.π (r * w * r⁻¹) ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
        rw [← hk1]
        exact LinearMap.mem_ker.mpr ((hW _ hw_r.1).mp hw_r)
      have hcore := sec7_tame_comm_core h34 hCV hc hs M₀ ρ b hS hs₁M hs₁H hs₁V hs₁D hw_r.1 hwU
      have e : ⁅r * s * r⁻¹, r * w * r⁻¹⁆ = r * ⁅s, w⁆ * r⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e] at hcore
      have hxV : r * ⁅s, w⁆ * r⁻¹ ∈ Vt M (LB M Q B) B Z t := hVn r hr _ (htame w hw)
      have hxQ : r * ⁅s, w⁆ * r⁻¹ ∈ Q := hVQ hxV
      have hxL : r * ⁅s, w⁆ * r⁻¹ ∈ Q ⊓ QB B :=
        (Tim79.QuadModel.mem_img_iff M₀ hLZ hxQ).mp hcore
      exact Subgroup.mem_sup_left ⟨hxV, hxL.2⟩
    let X : Subgroup G :=
      { carrier := {x | x ∈ H ∧ ∀ r ∈ Rt M (LB M Q B) t, r * x * r⁻¹ ∈ H}
        mul_mem' := by
          rintro x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
          refine ⟨H.mul_mem hx hy, fun r hr => ?_⟩
          have e : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
          rw [e]
          exact H.mul_mem (hxr r hr) (hyr r hr)
        one_mem' := ⟨H.one_mem, fun r _ => by simpa using H.one_mem⟩
        inv_mem' := by
          rintro x ⟨hx, hxr⟩
          refine ⟨H.inv_mem hx, fun r hr => ?_⟩
          have e : r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
          rw [e]
          exact H.inv_mem (hxr r hr) }
    have hZX : Z ≤ X := fun z hz => ⟨hZH hz, fun r hr => hZH (hZn r (hRM hr) z hz)⟩
    have hXV : X ≤ Vt M (LB M Q B) B Z t := fun x hx => hHV hx.1
    have hXinv : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ X, r * u * r⁻¹ ∈ X := by
      intro r hr u hu
      refine ⟨hu.2 r hr, fun r' hr' => ?_⟩
      have h1 := hu.2 (r' * r) ((Rt M (LB M Q B) t).mul_mem hr' hr)
      have e : r' * (r * u * r⁻¹) * r'⁻¹ = (r' * r) * u * (r' * r)⁻¹ := by group
      rw [e]
      exact h1
    rcases hIrr G M Q Z B hc n t hs X hZX hXV hXinv with hXZ | hXV'
    · intro w hw
      have hx : ⁅s, w⁆ ∈ X := ⟨by simpa using hkey 1 (Subgroup.one_mem _) w hw,
        fun r hr => hkey r hr w hw⟩
      rw [hXZ] at hx
      exact hx
    · exfalso
      have hVH : Vt M (LB M Q B) B Z t ≤ H := fun x hx => by
        have : x ∈ X := hXV' ▸ hx
        exact this.1
      have hHeq : H = Vt M (LB M Q B) B Z t := le_antisymm hHV hVH
      have h1 : Nat.card (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B) =
          Nat.card (hc.VtSub hS.model t) := by
        show Nat.card (M₀.img H) = _
        rw [hHeq]
        rfl
      rw [hHcard, hUcard] at h1
      exact absurd (Nat.pow_right_injective hK2 h1) (by decide)
  have hAbot : ∀ e ∈ (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs, e = 0 := by
    rintro _ ⟨e₀, he₀, rfl⟩
    obtain ⟨w, hwQ, rfl⟩ := M₀.π_surj e₀
    have hwW : w ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      refine (hW w hwQ).mpr ?_
      rw [← hk1] at he₀
      exact LinearMap.mem_ker.mp he₀
    rw [sec7_psi_apply_comm hc M₀ ρ b hS hsM ψs hψs hwQ]
    exact (M₀.π_ker _ (sec7_comm_mem_Q hc hsM hwQ)).mpr (hsW w hwW)
  have hApos : 0 < Module.finrank K
      ((M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs) := by
    rw [hmap]
    omega
  obtain ⟨⟨a, haA⟩, ha0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hApos
  exact ha0 (Subtype.ext (hAbot a haA))

end CFSG.RankThree.GF2n.Stroth80
