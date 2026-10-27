module

public import CFSG.RankThree.GF2n.Stroth80.Swap
public import CFSG.RankThree.GF2n.Stroth80.DictA2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem commutes_commutator_of_comm_mem {L₀ Z : Subgroup G} {x : G}
    (hL : ∀ s ∈ L₀, ∀ z ∈ Z, s * z = z * s) (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hZ : ∀ s ∈ L₀, ⁅s, x⁆ ∈ Z) {s t : G} (hs : s ∈ L₀) (ht : t ∈ L₀) :
    x * ⁅s, t⁆ = ⁅s, t⁆ * x := by
  have hphi : ∀ a ∈ L₀, ∀ b ∈ L₀, ⁅a * b, x⁆ = ⁅b, x⁆ * ⁅a, x⁆ := by
    intro a ha b hb
    have hv : b * x * b⁻¹ = ⁅b, x⁆ * x := by rw [commutatorElement_def]; group
    have hcv : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
      rw [hL a ha _ (hZ b hb)]; group
    calc ⁅a * b, x⁆ = a * (b * x * b⁻¹) * a⁻¹ * x⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (a * ⁅b, x⁆ * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by rw [hv]; group
      _ = ⁅b, x⁆ * ⁅a, x⁆ := by rw [hcv]; simp only [commutatorElement_def]
  have hc : ⁅s, t⁆ ∈ L₀ := by
    rw [commutatorElement_def]
    exact L₀.mul_mem (L₀.mul_mem (L₀.mul_mem hs ht) (L₀.inv_mem hs)) (L₀.inv_mem ht)
  have e : s * t = ⁅s, t⁆ * (t * s) := by rw [commutatorElement_def]; group
  have h1 := hphi s hs t ht
  have h2 := hphi ⁅s, t⁆ hc (t * s) (L₀.mul_mem ht hs)
  have h3 := hphi t ht s hs
  rw [e, h2, h3] at h1
  have hab := hZab _ (hZ s hs) _ (hZ t ht)
  have h4 : ⁅⁅s, t⁆, x⁆ = 1 := mul_eq_left.mp (h1.trans hab.symm)
  have := h4
  rw [commutatorElement_def] at this
  have h5 : ⁅s, t⁆ * x * ⁅s, t⁆⁻¹ = x := by
    have := mul_inv_eq_one.mp this
    exact this
  calc x * ⁅s, t⁆ = (⁅s, t⁆ * x * ⁅s, t⁆⁻¹) * ⁅s, t⁆ := by rw [h5]
    _ = ⁅s, t⁆ * x := by group

theorem Ctx.L0_le_LB (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) : t ∈ LB M Q B := by
  rw [← hc.QB_inf_M_eq] at ht
  exact Subgroup.mem_sup_right ht

theorem Ctx.Z_comm (hc : Ctx M Q Z B) : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a :=
  fun a ha b hb => hc.hyp.toHyp79.V_central ha (hc.Z_le_Q hb)

theorem Ctx.cq_centralizes_B (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) (hw2 : 2 ≤ w) {x : G}
    (hxC : x ∈ CQt Q Z (LB M Q B)) : ∀ b ∈ B, b * x = x * b := by
  intro b hb
  set L₀ := QB B ⊓ Subgroup.centralizer (Z : Set G) with hL₀
  have hcomm : ⁅L₀, L₀⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutes_commutator_of_comm_mem (L₀ := L₀) (Z := Z) (x := x)
      (fun s hs z hz => (Subgroup.mem_centralizer_iff.mp hs.2 z hz).symm) hc.Z_comm
      (fun s hs => hxC.2 s (hc.L0_le_LB hs)) hs ht).symm
  have hB' : b ∈ ⁅L₀, L₀⁆ := by rw [hc.commutator_L0 hw hw2]; exact hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcomm hB')

theorem Ctx.cq_not_mem_QB (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) (hw2 : 2 ≤ w) {x : G}
    (hxC : x ∈ CQt Q Z (LB M Q B)) (hxB : x ∉ (Z ⊔ B : Subgroup G)) : x ∉ QB B := by
  intro hxQB
  set L₀ := QB B ⊓ Subgroup.centralizer (Z : Set G) with hL₀
  have hxL₀ : x ∈ L₀ := ⟨hxQB, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    hc.hyp.toHyp79.V_central hz hxC.1⟩
  refine hxB ((hc.mem_center_iff_L0 hxL₀).mp fun s hs => ?_)
  have h1 : ⁅s, x⁆ ∈ Z := hxC.2 s (hc.L0_le_LB hs)
  have h2 : ⁅s, x⁆ ∈ B := by
    rw [← hc.commutator_L0 hw hw2]
    exact Subgroup.commutator_mem_commutator hs hxL₀
  have h3 : ⁅s, x⁆ ∈ Z ⊓ B := ⟨h1, h2⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
  have h4 := commutatorElement_eq_one_iff_mul_comm.mp h3
  exact h4.symm

theorem Ctx.isA2_QB (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) (hw2 : 2 ≤ w) {x : G}
    (hxC : x ∈ CQt Q Z (LB M Q B)) (hxB : x ∉ (Z ⊔ B : Subgroup G)) (hx2 : x ^ 2 = 1) :
    IsA2 (QB B) B x := by
  classical
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hN : Subgroup.normalizer (B : Set G) = conjSubgroup g M := (Ctx.QB_eq hc hg).1
  have hxQB : x ∉ QB B := hc.cq_not_mem_QB hw hw2 hxC hxB
  have hxcB : ∀ b ∈ B, x * b * x⁻¹ = b := fun b hb => by
    rw [mul_inv_eq_iff_eq_mul]; exact (hc.cq_centralizes_B hw hw2 hxC b hb).symm
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    rw [hxcB b hb]; exact hb
  obtain ⟨n, γ, M₀, hn, h⟩ := stroth_globalModelDataGF hc.hyp
  have h' := h.conj g
  set M' := M₀.conj g with hM'
  rw [hN] at hxN
  have hZB : Z ≤ QB B := hc.Z_le_QB.1
  have hZg : Z ≤ conjSubgroup g Q := hQB ▸ hZB
  have hBg : B = conjSubgroup g Z := hg
  have hxcent : ∀ z ∈ conjSubgroup g Z, x * z * x⁻¹ = z := fun z hz => hxcB z (hg ▸ hz)
  obtain ⟨T, hTπ, hTQ, hTB⟩ := h'.linear_of_centralizes hxN hxcent
  have hne : conjSubgroup g⁻¹ Z ≠ Z := by
    intro e
    apply hc.ne
    rw [hg]
    conv_lhs => rw [← e]
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hle : conjSubgroup g⁻¹ Z ≤ Q := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have := hZg (show g⁻¹⁻¹ * y * g⁻¹ ∈ Z from hy)
    rw [mem_conjSubgroup] at this
    simpa [mul_assoc] using this
  obtain ⟨e₀, he₀, hline⟩ := h.line g⁻¹ hne hle
  set e₁ : M'.E := e₀ with he₁def
  have he₁ : e₁ ≠ 0 := he₀
  have hline' : ∀ v : M'.E, v ∈ M'.img Z ↔ ∃ s : GaloisField 2 n, v = s • e₁ := by
    intro v
    have h1 := Tim79.QuadModel.mem_img_conj M₀ g (S := conjSubgroup g⁻¹ Z) v
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one] at h1
    exact h1.trans (hline v)
  have hZel : CFSG.Open.IsElemAbelian 2 Z := hc.hyp.isElemAbelian_Z
  have hqf : M'.Qf e₁ = 0 := Tim79.QuadModel.IsLine.qf_zero (M₀ := M') h'.reg hZg hZel hline'
  have hcentZ : ∀ y ∈ conjSubgroup g Q,
      y ∈ Subgroup.centralizer (Z : Set G) ↔ M'.B (M'.π y) e₁ = 0 := fun y hy =>
    Tim79.QuadModel.centralizer_iff (M₀ := M') h'.reg hZg hline' hy
  have hxQ : x ∈ Q := hxC.1
  have hxz : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    rw [← hc.hyp.toHyp79.V_central hz hxQ]; group
  have hTe₁ : T e₁ = e₁ := by
    obtain ⟨z, hz, hzQ, hzπ⟩ := (hline' e₁).mpr ⟨1, (one_smul _ e₁).symm⟩
    rw [← hzπ, ← hTπ z hzQ, hxz z hz]
  have hxNQ : x ∈ Subgroup.normalizer ((conjSubgroup g Q : Subgroup G) : Set G) := by
    rw [mem_normalizer_conj_iff]
    exact hc.hyp.Q_normal.2 (mem_conjSubgroup.mp hxN)
  have ha : ∀ y ∈ conjSubgroup g Q, x * y * x⁻¹ ∈ conjSubgroup g Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hxNQ y).mp hy
  have ha' : ∀ y ∈ conjSubgroup g Q, x⁻¹ * y * x ∈ conjSubgroup g Q := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxNQ) y).mp hy
    simpa using this
  have hr : ∀ v : M'.E, M'.B v e₁ = 0 → ∃ c : GaloisField 2 n,
      (T : M'.E →ₗ[GaloisField 2 n] M'.E) v = v + c • e₁ := by
    intro v hv
    obtain ⟨t, htQ, rfl⟩ := M'.π_surj v
    have htC : t ∈ Subgroup.centralizer (Z : Set G) := (hcentZ t htQ).mpr hv
    have ht₀ : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := ⟨hQB ▸ htQ, htC⟩
    have hct : ⁅t, x⁆ ∈ Z := hxC.2 t (hc.L0_le_LB ht₀)
    have hxt : x * t * x⁻¹ = ⁅x, t⁆ * t := by rw [commutatorElement_def]; group
    have hxt' : ⁅x, t⁆ ∈ Z := by
      rw [← commutatorElement_inv]; exact Z.inv_mem hct
    have hxtQ : ⁅x, t⁆ ∈ conjSubgroup g Q := hZg hxt'
    have h1 : M'.π (x * t * x⁻¹) = M'.π ⁅x, t⁆ + M'.π t := by
      rw [hxt]; exact M'.π_mul _ hxtQ _ htQ
    obtain ⟨c, hc'⟩ := (hline' _).mp (M'.pi_mem_img hxt' hxtQ)
    refine ⟨c, ?_⟩
    show T (M'.π t) = _
    rw [← hTπ t htQ, h1, hc']
    exact add_comm _ _
  have hTne : ∃ e, (T : M'.E →ₗ[GaloisField 2 n] M'.E) e ≠ e := by
    by_contra hcon
    push Not at hcon
    apply hxQB
    refine hc.mem_QB_of_comm_mem (hN ▸ hxN) fun y hy => ?_
    have hyg : y ∈ conjSubgroup g Q := hQB ▸ hy
    rw [hg]
    exact (M'.comm_mem_iff hyg (ha y hyg)).mpr (by rw [hTπ y hyg]; exact hcon _)
  have hfin2 := Tim79.QuadModel.finrank_range_eq_two (M₀ := M')
    (T := (T : M'.E →ₗ[GaloisField 2 n] M'.E)) hTQ he₁ hqf hr hTne
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx2)
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hQfzero : ∀ v ∈ LinearMap.range ((T : M'.E →ₗ[GaloisField 2 n] M'.E) - 1), M'.Qf v = 0 := by
    rintro v ⟨w, rfl⟩
    obtain ⟨s, hsQ, rfl⟩ := M'.π_surj w
    have hxsQ : x * s * x⁻¹ ∈ conjSubgroup g Q := ha s hsQ
    have hrQ : x * s * x⁻¹ * s⁻¹ ∈ conjSubgroup g Q :=
      Subgroup.mul_mem _ hxsQ (Subgroup.inv_mem _ hsQ)
    have hπr : M'.π (x * s * x⁻¹ * s⁻¹) =
        ((T : M'.E →ₗ[GaloisField 2 n] M'.E) - 1) (M'.π s) := by
      rw [M'.π_mul _ hxsQ _ (Subgroup.inv_mem _ hsQ), hTπ s hsQ, Tim79.QuadModel.pi_inv M' hsQ]
      simp [LinearMap.sub_apply, sub_eq_add_neg]
    have hBr : M'.B (M'.π (x * s * x⁻¹ * s⁻¹)) e₁ = 0 := by
      rw [hπr]
      have := Tim79.QuadModel.B_iso (M₀ := M') (T := (T : M'.E →ₗ[GaloisField 2 n] M'.E)) hTQ
        (M'.π s) e₁
      have hTe : (T : M'.E →ₗ[GaloisField 2 n] M'.E) e₁ = e₁ := hTe₁
      rw [hTe] at this
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearMap.sub_apply]
      rw [this, sub_self]
    have hr₀ : x * s * x⁻¹ * s⁻¹ ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) :=
      ⟨hQB ▸ hrQ, (hcentZ _ hrQ).mpr hBr⟩
    have h1 : ⁅x * s * x⁻¹ * s⁻¹, x⁆ ∈ Z := hxC.2 _ (hc.L0_le_LB hr₀)
    have hxr : x * (x * s * x⁻¹ * s⁻¹) * x⁻¹ = (x * s * x⁻¹ * s⁻¹)⁻¹ := by
      rw [hxinv]
      calc x * (x * s * x * s⁻¹) * x = (x * x) * s * x * s⁻¹ * x := by group
        _ = s * x * s⁻¹ * x := by rw [hxx, one_mul]
        _ = (x * s * x * s⁻¹)⁻¹ := by
          rw [show (x * s * x * s⁻¹)⁻¹ = s * x⁻¹ * s⁻¹ * x⁻¹ by group, hxinv]
    have hcomm : ⁅x * s * x⁻¹ * s⁻¹, x⁆ = (x * s * x⁻¹ * s⁻¹) ^ 2 := by
      rw [commutatorElement_def, pow_two]
      calc (x * s * x⁻¹ * s⁻¹) * x * (x * s * x⁻¹ * s⁻¹)⁻¹ * x⁻¹
          = (x * s * x⁻¹ * s⁻¹) * (x * (x * s * x⁻¹ * s⁻¹)⁻¹ * x⁻¹) := by group
        _ = (x * s * x⁻¹ * s⁻¹) * (x * (x * s * x⁻¹ * s⁻¹) * x⁻¹)⁻¹ := by
          rw [show x * (x * s * x⁻¹ * s⁻¹)⁻¹ * x⁻¹ = (x * (x * s * x⁻¹ * s⁻¹) * x⁻¹)⁻¹ by group]
        _ = (x * s * x⁻¹ * s⁻¹) * (x * s * x⁻¹ * s⁻¹) := by rw [hxr, inv_inv]
    have h2 : (x * s * x⁻¹ * s⁻¹) ^ 2 ∈ conjSubgroup g Z :=
      hc.hyp.toHyp79.sq_mem_conj g hrQ
    have h3 : (x * s * x⁻¹ * s⁻¹) ^ 2 ∈ Z ⊓ B := ⟨hcomm ▸ h1, hg ▸ h2⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
    rw [← hπr, ← M'.sq_eq _ hrQ, h3]
    exact h'.reg.one
  have hK : 1 < Nat.card (GaloisField 2 n) := by
    rw [h'.card, card_conjSubgroup]
    have := hc.hyp.q4
    omega
  have hiff := isA2_iff (M₀ := M') h'.reg h'.card hK T ha ha' hTπ
  rw [hQB, hg]
  exact hiff.mpr ⟨hQB ▸ hxQB, by rw [hx2]; exact Subgroup.one_mem _, hfin2, hQfzero⟩

theorem stroth_3_1 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) :
    (¬ ∃ x ∈ CQt Q Z (LB M Q B), x ∉ (B ⊔ Z : Subgroup G) ∧ x ^ 2 = 1) ∨
      ∃ a ∈ LB M Q B, IsA2 Q Z a := by
  by_cases hcon : ∃ x ∈ CQt Q Z (LB M Q B), x ∉ (B ⊔ Z : Subgroup G) ∧ x ^ 2 = 1
  · right
    obtain ⟨x, hxC, hxB, hx2⟩ := hcon
    have hxB' : x ∉ (Z ⊔ B : Subgroup G) := by rwa [sup_comm]
    have hA2 := hc.isA2_QB hw (by omega) hxC hxB' hx2
    obtain ⟨m, h1, h2, h3, h4⟩ := hc.exists_swap'
    have hxcB := hc.cq_centralizes_B hw (by omega) hxC
    have hQ' : conjSubgroup m⁻¹ (QB B) = Q := by
      rw [← h1, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hB' : conjSubgroup m⁻¹ B = Z := by
      rw [← h3, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hA2' := hA2.conj m⁻¹
    rw [hQ', hB', inv_inv] at hA2'
    refine ⟨m⁻¹ * x * m, ?_, hA2'⟩
    apply hc.L0_le_LB
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    · have : x ∈ conjSubgroup m (QB B) := by rw [h2]; exact hxC.1
      exact mem_conjSubgroup.mp this
    · have hzB : m * z * m⁻¹ ∈ B := by
        rw [← h3, mem_conjSubgroup]; simpa [mul_assoc] using hz
      have := hxcB _ hzB
      calc z * (m⁻¹ * x * m) = m⁻¹ * ((m * z * m⁻¹) * x) * m := by group
        _ = m⁻¹ * (x * (m * z * m⁻¹)) * m := by rw [this]
        _ = (m⁻¹ * x * m) * z := by group
  · left; exact hcon

end CFSG.RankThree.GF2n.Stroth80
