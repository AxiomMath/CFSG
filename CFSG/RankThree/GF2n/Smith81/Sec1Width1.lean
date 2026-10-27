module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Plane

variable {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem exists_hyp_basis (M₀ : Tim79.QuadModel Q Z K γ) (h2 : Module.finrank K M₀.E = 2)
    (hyp : ∃ S₁ S₂ : Submodule K M₀.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M₀.Qf x = 0) ∧
      ∀ x ∈ S₂, M₀.Qf x = 0) :
    ∃ s₁ s₂ : M₀.E, M₀.Qf s₁ = 0 ∧ M₀.Qf s₂ = 0 ∧ M₀.B s₁ s₂ = 1 ∧
      ∀ e, ∃ α β : K, e = α • s₁ + β • s₂ := by
  obtain ⟨S₁, S₂, hS, h1, h2s⟩ := hyp
  have hB : ∀ (S : Submodule K M₀.E), (∀ x ∈ S, M₀.Qf x = 0) → ∀ x ∈ S, ∀ y ∈ S, M₀.B x y = 0 := by
    intro S hS x hx y hy
    have := M₀.Qf_add x y
    rw [hS _ (S.add_mem hx hy), hS x hx, hS y hy] at this
    simpa using this.symm
  have hne : ∀ S S' : Submodule K M₀.E, IsCompl S S' → (∀ x ∈ S', M₀.Qf x = 0) → S ≠ ⊥ := by
    intro S S' hSS' hS' hbot
    have htop : S' = ⊤ := by
      have := hSS'.sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have hall : ∀ e : M₀.E, e = 0 := by
      intro e
      refine M₀.nondeg e fun f => hB S' hS' e ?_ f ?_ <;> simp [htop]
    have : Module.finrank K M₀.E = 0 := by
      rw [Module.finrank_zero_iff]
      exact ⟨fun a b => by rw [hall a, hall b]⟩
    omega
  obtain ⟨s₁, hs₁, hs₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne S₁ S₂ hS h2s)
  obtain ⟨s₂, hs₂, hs₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne S₂ S₁ hS.symm h1)
  have hli : LinearIndependent K ![s₁, s₂] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1' : a • s₁ ∈ S₁ := S₁.smul_mem a hs₁
    have h2' : b • s₂ ∈ S₂ := S₂.smul_mem b hs₂
    have h3 : a • s₁ = -(b • s₂) := eq_neg_of_add_eq_zero_left hab
    have hmem : a • s₁ ∈ S₁ ⊓ S₂ := ⟨h1', by rw [h3]; exact S₂.neg_mem h2'⟩
    rw [hS.inf_eq_bot, Submodule.mem_bot] at hmem
    have ha : a = 0 := by
      rcases smul_eq_zero.mp hmem with h | h
      · exact h
      · exact absurd h hs₁0
    refine ⟨ha, ?_⟩
    rw [ha, zero_smul, zero_add] at hab
    rcases smul_eq_zero.mp hab with h | h
    · exact h
    · exact absurd h hs₂0
  have hspan : Submodule.span K (Set.range ![s₁, s₂]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [h2])
  have hrep : ∀ e : M₀.E, ∃ α β : K, e = α • s₁ + β • s₂ := by
    intro e
    have he : e ∈ Submodule.span K (Set.range ![s₁, s₂]) := by rw [hspan]; trivial
    have hr : Set.range ![s₁, s₂] = {s₁, s₂} := by
      ext y; simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hr, Submodule.mem_span_pair] at he
    obtain ⟨a, b, hab⟩ := he
    exact ⟨a, b, hab.symm⟩
  have hB12 : M₀.B s₁ s₂ ≠ 0 := by
    intro h0
    apply hs₁0
    refine M₀.nondeg s₁ fun f => ?_
    obtain ⟨α, β, rfl⟩ := hrep f
    rw [map_add, map_smul, map_smul, h0, M₀.alt]
    simp
  refine ⟨s₁, (M₀.B s₁ s₂)⁻¹ • s₂, h1 s₁ hs₁, ?_, ?_, ?_⟩
  · rw [M₀.Qf_smul, h2s s₂ hs₂]; simp
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hB12]
  · intro e
    obtain ⟨α, β, rfl⟩ := hrep e
    exact ⟨α, β * M₀.B s₁ s₂, by rw [smul_smul, mul_assoc, mul_inv_cancel₀ hB12, mul_one]⟩

theorem plane_invol_classify [CharP K 2] (M₀ : Tim79.QuadModel Q Z K γ) {s₁ s₂ : M₀.E}
    (hQ1 : M₀.Qf s₁ = 0) (hQ2 : M₀.Qf s₂ = 0) (hB : M₀.B s₁ s₂ = 1)
    (hrep : ∀ e, ∃ α β : K, e = α • s₁ + β • s₂) (T : M₀.E ≃ₗ[K] M₀.E)
    (hTQ : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f)
    (hT2 : ∀ e, T (T e) = e) :
    (T s₁ = s₁ ∧ T s₂ = s₂) ∨ ∃ b : K, b ≠ 0 ∧ T s₁ = b • s₂ ∧ T s₂ = b⁻¹ • s₁ := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hB11 : M₀.B s₁ s₁ = 0 := M₀.alt s₁
  have hB22 : M₀.B s₂ s₂ = 0 := M₀.alt s₂
  have hB21 : M₀.B s₂ s₁ = -1 := by rw [Tim79.QuadModel.B_comm s₂ s₁, hB]
  have hBf : ∀ a b c d : K, M₀.B (a • s₁ + b • s₂) (c • s₁ + d • s₂) = a * d - b * c := by
    intro a b c d
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB11,
      hB22, hB, hB21]
    ring
  have hQf : ∀ a b : K, M₀.Qf (a • s₁ + b • s₂) = a * b := by
    intro a b
    rw [M₀.Qf_add, M₀.Qf_smul, M₀.Qf_smul, hQ1, hQ2]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB]
    ring
  have hc1 : ∀ a b : K, M₀.B (a • s₁ + b • s₂) s₂ = a := by
    intro a b
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB22, hB]
    ring
  have hc2 : ∀ a b : K, M₀.B s₁ (a • s₁ + b • s₂) = b := by
    intro a b
    simp only [map_add, map_smul, smul_eq_mul, hB11, hB]
    ring
  obtain ⟨a, b, hTs₁⟩ := hrep (T s₁)
  obtain ⟨c, d, hTs₂⟩ := hrep (T s₂)
  have e1 : a * b = 0 := by have := hTQ s₁; rw [hTs₁, hQf, hQ1] at this; exact this
  have e2 : c * d = 0 := by have := hTQ s₂; rw [hTs₂, hQf, hQ2] at this; exact this
  have e3 : a * d - b * c = 1 := by
    have := hTB s₁ s₂
    rw [hTs₁, hTs₂, hBf, hB] at this
    exact this
  have hTT1 : a • (a • s₁ + b • s₂) + b • (c • s₁ + d • s₂) = s₁ := by
    have := hT2 s₁
    rw [hTs₁, map_add, map_smul, map_smul, hTs₁, hTs₂] at this
    exact this
  have hTT2 : c • (a • s₁ + b • s₂) + d • (c • s₁ + d • s₂) = s₂ := by
    have := hT2 s₂
    rw [hTs₂, map_add, map_smul, map_smul, hTs₁, hTs₂] at this
    exact this
  have hTT1' : (a * a + b * c) • s₁ + (a * b + b * d) • s₂ = s₁ := by
    have e : (a * a + b * c) • s₁ + (a * b + b * d) • s₂ =
        a • (a • s₁ + b • s₂) + b • (c • s₁ + d • s₂) := by module
    rw [e]; exact hTT1
  have hTT2' : (c * a + d * c) • s₁ + (c * b + d * d) • s₂ = s₂ := by
    have e : (c * a + d * c) • s₁ + (c * b + d * d) • s₂ =
        c • (a • s₁ + b • s₂) + d • (c • s₁ + d • s₂) := by module
    rw [e]; exact hTT2
  have f1 : a * a + b * c = 1 := by
    have := congrArg (fun v => M₀.B v s₂) hTT1'
    change M₀.B ((a * a + b * c) • s₁ + (a * b + b * d) • s₂) s₂ = M₀.B s₁ s₂ at this
    rw [hc1, hB] at this
    exact this
  have f2 : a * b + b * d = 0 := by
    have := congrArg (fun v => M₀.B s₁ v) hTT1'
    change M₀.B s₁ ((a * a + b * c) • s₁ + (a * b + b * d) • s₂) = M₀.B s₁ s₁ at this
    rw [hc2, hB11] at this
    exact this
  have f3 : c * a + d * c = 0 := by
    have := congrArg (fun v => M₀.B v s₂) hTT2'
    change M₀.B ((c * a + d * c) • s₁ + (c * b + d * d) • s₂) s₂ = M₀.B s₂ s₂ at this
    rw [hc1, hB22] at this
    exact this
  have f4 : c * b + d * d = 1 := by
    have := congrArg (fun v => M₀.B s₁ v) hTT2'
    change M₀.B s₁ ((c * a + d * c) • s₁ + (c * b + d * d) • s₂) = M₀.B s₁ s₂ at this
    rw [hc2, hB] at this
    exact this
  have sq1 : ∀ u : K, u * u = 1 → u = 1 := by
    intro u hu
    have : (u - 1) ^ 2 = 0 := by linear_combination hu + (1 - u) * h2K
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  by_cases hb : b = 0
  · left
    subst hb
    have ha : a = 1 := sq1 a (by linear_combination f1)
    have hd : d = 1 := sq1 d (by linear_combination f4)
    have hc : c = 0 := by rw [hd, mul_one] at e2; exact e2
    rw [hTs₁, hTs₂, ha, hd, hc]
    simp
  · right
    have ha : a = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact h
      · exact absurd h hb
    have hbc : b * c = 1 := by rw [ha] at f1; linear_combination f1
    have hc : c = b⁻¹ := by field_simp; linear_combination hbc
    have hc0 : c ≠ 0 := by intro h; rw [h] at hbc; simp at hbc
    have hd : d = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h hc0
      · exact h
    refine ⟨b, hb, ?_, ?_⟩
    · rw [hTs₁, ha]; simp
    · rw [hTs₂, hd, hc]; simp

theorem plane_invol_eq [CharP K 2] (M₀ : Tim79.QuadModel Q Z K γ) {s₁ s₂ : M₀.E}
    (hQ1 : M₀.Qf s₁ = 0) (hQ2 : M₀.Qf s₂ = 0) (hB : M₀.B s₁ s₂ = 1)
    (hrep : ∀ e, ∃ α β : K, e = α • s₁ + β • s₂) (T T' : M₀.E ≃ₗ[K] M₀.E)
    (hTQ : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f)
    (hT2 : ∀ e, T (T e) = e) (hT'Q : ∀ e, M₀.Qf (T' e) = M₀.Qf e)
    (hT'B : ∀ e f, M₀.B (T' e) (T' f) = M₀.B e f) (hT'2 : ∀ e, T' (T' e) = e)
    (hcomm : ∀ e, T (T' e) = T' (T e)) (hne : ∃ e, T e ≠ e) (hne' : ∃ e, T' e ≠ e) :
    ∀ e, T e = T' e := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hs₁0 : s₁ ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hB
    exact zero_ne_one hB
  have hid : ∀ U : M₀.E ≃ₗ[K] M₀.E, U s₁ = s₁ → U s₂ = s₂ → ∀ e, U e = e := by
    intro U h1 h2 e
    obtain ⟨α, β, rfl⟩ := hrep e
    rw [map_add, map_smul, map_smul, h1, h2]
  obtain ⟨b, hb, hTs₁, hTs₂⟩ : ∃ b : K, b ≠ 0 ∧ T s₁ = b • s₂ ∧ T s₂ = b⁻¹ • s₁ := by
    rcases plane_invol_classify M₀ hQ1 hQ2 hB hrep T hTQ hTB hT2 with ⟨h1, h2⟩ | h
    · obtain ⟨e, he⟩ := hne
      exact absurd (hid T h1 h2 e) he
    · exact h
  obtain ⟨b', hb', hT's₁, hT's₂⟩ : ∃ b : K, b ≠ 0 ∧ T' s₁ = b • s₂ ∧ T' s₂ = b⁻¹ • s₁ := by
    rcases plane_invol_classify M₀ hQ1 hQ2 hB hrep T' hT'Q hT'B hT'2 with ⟨h1, h2⟩ | h
    · obtain ⟨e, he⟩ := hne'
      exact absurd (hid T' h1 h2 e) he
    · exact h
  have hc := hcomm s₁
  rw [hT's₁, hTs₁, map_smul, map_smul, hTs₂, hT's₂, smul_smul, smul_smul] at hc
  have hcoef : b' * b⁻¹ = b * b'⁻¹ := by
    have := sub_eq_zero.mpr hc
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hs₁0
  have hsq : b' ^ 2 = b ^ 2 := by
    field_simp at hcoef
    linear_combination hcoef
  have hbb : b' = b := by
    have : (b' - b) ^ 2 = 0 := by linear_combination hsq + (b ^ 2 - b' * b) * h2K
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have h1 : T s₁ = T' s₁ := by rw [hTs₁, hT's₁, hbb]
  have h2 : T s₂ = T' s₂ := by rw [hTs₂, hT's₂, hbb]
  intro e
  obtain ⟨α, β, rfl⟩ := hrep e
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, h1, h2]

end Plane

section Width1

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem Sit.x_cent_of_mem (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) {w : G} (hw : w ∈ X) :
    ∀ z ∈ Z, w * z * w⁻¹ = z := by
  intro z hz
  have := Subgroup.mem_centralizer_iff.mp (h12.1 hw).2 z hz
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem card_Q_eq {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hZQ : Z ≤ Q) : Nat.card Q = Nat.card M₀.E * Nat.card Z := by
  have h := card_preimageSub hZQ (⊤ : Submodule K M₀.E)
  have hQ : preimageSub M₀ (⊤ : Submodule K M₀.E) = Q := by
    ext y
    rw [mem_preimageSub]
    simp
  rw [hQ] at h
  rw [h]
  congr 1
  exact Nat.card_congr Submodule.topEquiv.toEquiv

theorem smith_1_12_n1 (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) (hw : Width Q Z 1) : False := by
  have H := hs.hyp
  have hZQ := H.Z_normal.1
  have hx2 : ∀ w ∈ X, w * w = 1 := hs.X_sq
  have hXM : ∀ w ∈ X, w ∈ M := fun w hw => (h12.1 hw).1
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcard := hD.card
  have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
  have hfin2 : Module.finrank K M₀.E = 2 := by
    have h1 := card_Q_eq M₀ hZQ
    rw [Module.natCard_eq_pow_finrank (K := K) (V := M₀.E), hcard] at h1
    have h2 : Nat.card Q = Nat.card Z ^ 3 := hw
    have hZpos : 0 < Nat.card Z := by omega
    have h3 : Nat.card Z ^ Module.finrank K M₀.E * Nat.card Z = Nat.card Z ^ 2 * Nat.card Z := by
      rw [← h1, h2]; ring
    exact Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_right hZpos h3)
  obtain ⟨s₁, s₂, hQ1, hQ2, hB, hrep⟩ := exists_hyp_basis M₀ hfin2 hD.hyperbolic
  have hact : ∀ w ∈ X, ∃ A : XAct M₀ w, ∀ e, A.T (A.T e) = e := by
    intro w hw
    obtain ⟨A⟩ := exists_xact hD (hXM w hw) (hs.x_cent_of_mem h12 hw)
    exact ⟨A, A.T_T H (hXM w hw) (hx2 w hw)⟩
  have htriv : ∀ w ∈ X, ∀ A : XAct M₀ w, (∀ e, A.T e = e) → w = 1 := by
    intro w hw A hid
    have hwQ : w ∈ Q := by
      refine H.centralizer_Qt w (hXM w hw) fun y hy => ?_
      have hyw : w * y * w⁻¹ ∈ Q := conj_mem_Q H (hXM w hw) hy
      have e : ⁅w, y⁆ = (w * y * w⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
      have hmem : ⁅w, y⁆ ∈ Q := by rw [e]; exact Q.mul_mem hyw (Q.inv_mem hy)
      refine (M₀.π_ker _ hmem).mp ?_
      rw [e, M₀.π_mul _ hyw _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy, A.hπ y hy, hid]
      exact add_neg_cancel _
    have : w ∈ X ⊓ Q := ⟨hw, hwQ⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact this
  have hXcard : 2 < Nat.card X := by
    obtain ⟨g, hg⟩ := hs.conj
    have : Nat.card X = Nat.card Z := by rw [hg]; exact card_conjSubgroup g Z
    have h4 := H.q4
    omega
  obtain ⟨w₁, w₂, hw₁, hw₂, hw₁1, hw₂1, hw₁₂⟩ : ∃ w₁ w₂ : G, w₁ ∈ X ∧ w₂ ∈ X ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧
      w₁ ≠ w₂ := by
    have h := (Set.two_lt_ncard_iff (Set.toFinite (X : Set G))).mp
      (by rw [← Nat.card_coe_set_eq]; exact hXcard)
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := h
    by_cases h1 : a = 1
    · exact ⟨b, c, hb, hc, fun h => hab (h1.trans h.symm), fun h => hac (h1.trans h.symm), hbc⟩
    by_cases h2 : b = 1
    · exact ⟨a, c, ha, hc, h1, fun h => hbc (h2.trans h.symm), hac⟩
    · exact ⟨a, b, ha, hb, h1, h2, hab⟩
  obtain ⟨A₁, hA₁⟩ := hact w₁ hw₁
  obtain ⟨A₂, hA₂⟩ := hact w₂ hw₂
  have hw₁₂c : w₁ * w₂ = w₂ * w₁ := hs.X_comm w₁ hw₁ w₂ hw₂
  have hconj : ∀ y ∈ Q, ∀ (u v : G), u ∈ X → v ∈ X → ∀ (A : XAct M₀ u) (B : XAct M₀ v),
      A.T (B.T (M₀.π y)) = M₀.π ((u * v) * y * (u * v)⁻¹) := by
    intro y hy u v hu hv A B
    rw [← B.hπ y hy, ← A.hπ _ (conj_mem_Q H (hXM v hv) hy)]
    congr 1
    group
  have hcomm : ∀ e, A₁.T (A₂.T e) = A₂.T (A₁.T e) := by
    intro e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
    rw [hconj y hy w₁ w₂ hw₁ hw₂ A₁ A₂, hconj y hy w₂ w₁ hw₂ hw₁ A₂ A₁, hw₁₂c]
  have hne₁ : ∃ e, A₁.T e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact hw₁1 (htriv w₁ hw₁ A₁ hcon)
  have hne₂ : ∃ e, A₂.T e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact hw₂1 (htriv w₂ hw₂ A₂ hcon)
  have heq := plane_invol_eq M₀ hQ1 hQ2 hB hrep A₁.T A₂.T A₁.hQ A₁.hB hA₁ A₂.hQ A₂.hB hA₂ hcomm
    hne₁ hne₂
  have hw₁₂Q : w₁ * w₂ ∈ X := X.mul_mem hw₁ hw₂
  have hid : ∀ e, A₁.T (A₂.T e) = e := by
    intro e
    rw [← heq e]
    exact hA₁ e
  obtain ⟨A₃⟩ := exists_xact hD (hXM _ hw₁₂Q) (hs.x_cent_of_mem h12 hw₁₂Q)
  have hA₃ : ∀ e, A₃.T e = A₁.T (A₂.T e) := by
    intro e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
    rw [← A₃.hπ y hy, hconj y hy w₁ w₂ hw₁ hw₂ A₁ A₂]
  have h13 := htriv _ hw₁₂Q A₃ fun e => by rw [hA₃, hid]
  have h12' : w₂ = w₁ := by
    have h1 : w₂ = w₁⁻¹ := by
      have := congrArg (fun t => w₁⁻¹ * t) h13
      simpa using this
    rw [h1, inv_eq_of_mul_eq_one_right (hx2 w₁ hw₁)]
  exact hw₁₂ h12'.symm

end Width1

end CFSG.RankThree.GF2n.Smith81
