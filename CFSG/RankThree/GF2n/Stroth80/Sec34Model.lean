module

public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GF2n.Basic
public import CFSG.RankThree.GF2n.Stroth80.QuadIso
public import CFSG.RankThree.GF2n.Stroth80.QuadWitt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

section ModelCard

variable {Q Z : Subgroup G} {K : Type} [Field K] [Finite K] {γ : G → K}

theorem comm_zpowers_le_of_conj {a : G} (ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q) : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
  have hnorm : a ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨ha h, fun hh => ?_⟩
    have := ha' _ hh
    rwa [show a⁻¹ * (a * h * a⁻¹) * a = h by group] at this
  rw [Subgroup.commutator_le]
  intro x hx z hz
  have hzn : z ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr hnorm) hz
  have h1 : z * x⁻¹ * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hzn _).mp (Q.inv_mem hx)
  rw [show ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) by rw [commutatorElement_def]; group]
  exact Q.mul_mem hx h1

theorem mem_img_comm_zpowers_sup_iff (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ)
    {a : G} (T : M₀.E ≃ₗ[K] M₀.E) (ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q) (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x))
    (v : M₀.E) :
    v ∈ M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z) ↔
      v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
  have hSQ := comm_zpowers_le_of_conj ha ha'
  rw [← Tim79.QuadModel.mem_img_commutator_zpowers T ha ha' hT]
  constructor
  · rintro ⟨x, hx, hxQ, rfl⟩
    have hle : ⁅Q, Subgroup.zpowers a⁆ ⊔ Z ≤ M₀.lift (M₀.img ⁅Q, Subgroup.zpowers a⁆) := by
      refine sup_le (fun y hy => ⟨hSQ hy, M₀.pi_mem_img hy (hSQ hy)⟩) (fun z hz => ?_)
      refine ⟨R.V_le hz, ?_⟩
      rw [(M₀.π_ker z (R.V_le hz)).mpr hz]
      exact AddSubgroup.zero_mem _
    exact (hle hx).2
  · exact fun h => M₀.img_mono le_sup_left h

theorem card_comm_zpowers_sup (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ)
    {a : G} (T : M₀.E ≃ₗ[K] M₀.E) (ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q) (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) :
    Nat.card ↥(⁅Q, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z *
      Nat.card K ^ Module.finrank K (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
  have hSQ := comm_zpowers_le_of_conj ha ha'
  have hcardS : Nat.card ↥(⁅Q, Subgroup.zpowers a⁆ ⊔ Z) =
      Nat.card Z * Nat.card (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
    rw [M₀.card_eq (sup_le hSQ R.V_le) le_sup_right]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      mem_img_comm_zpowers_sup_iff M₀ R T ha ha' hT v)
  rw [hcardS]
  congr 1
  exact Module.natCard_eq_pow_finrank

theorem isElemAbelian_comm_zpowers_iff (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ)
    {a : G} (T : M₀.E ≃ₗ[K] M₀.E) (ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q) (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) :
    IsElemAbelian 2 ⁅Q, Subgroup.zpowers a⁆ ↔
      ∀ v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0 := by
  have hSQ := comm_zpowers_le_of_conj ha ha'
  have himg : ∀ v, v ∈ M₀.img ⁅Q, Subgroup.zpowers a⁆ ↔
      v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) :=
    fun v => Tim79.QuadModel.mem_img_commutator_zpowers T ha ha' hT
  rw [M₀.isElemAbelian_iff R hSQ]
  exact ⟨fun h v hv => h v ((himg v).mpr hv), fun h v hv => h v ((himg v).mp hv)⟩

end ModelCard

section Eichler

variable {QF V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}

theorem card_le_sq_of_eichler_group (M₀ : Tim79.QuadModel QF V K γ)
    (Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)) {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hiso : ∀ T ∈ Λ, ∀ e, M₀.Qf (T e) = M₀.Qf e) (hfix : ∀ T ∈ Λ, T b = b)
    (hr : ∀ T ∈ Λ, ∀ y, M₀.B y b = 0 → ∃ c : K, T y = y + c • b)
    (hani : ∀ T ∈ Λ,
      (∀ v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0) → T = 1) :
    Nat.card Λ ≤ Nat.card K ^ 2 := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hxx : ∀ x : M₀.E, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  obtain ⟨f, hfb⟩ : ∃ f : M₀.E, M₀.B f b = 1 := by
    obtain ⟨f₀, hf₀⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
    exact ⟨(M₀.B f₀ b)⁻¹ • f₀, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]⟩
  have hbf : M₀.B b f = 1 := by
    rw [Tim79.QuadModel.B_comm b f, hfb, CharTwo.neg_eq]
  have hBT : ∀ T ∈ Λ, ∀ y, M₀.B (T y) b = M₀.B y b := by
    intro T hT y
    have h1 : M₀.B (T y) (T b) = M₀.B y b :=
      Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hiso T hT) y b
    rwa [hfix T hT] at h1
  have hv_perp : ∀ T ∈ Λ, M₀.B (T f - f) b = 0 := by
    intro T hT
    rw [map_sub, LinearMap.sub_apply, hBT T hT, sub_self]
  let ρ : M₀.E → M₀.E := fun w => w - M₀.B w f • b
  have ρ_add : ∀ x y, ρ (x + y) = ρ x + ρ y := by
    intro x y
    simp only [ρ, map_add, LinearMap.add_apply, add_smul]
    abel
  have ρ_b : ∀ c : K, ρ (c • b) = 0 := by
    intro c
    simp only [ρ, map_smul, LinearMap.smul_apply, smul_eq_mul, hbf, mul_one, sub_self]
  have Qf_ρ : ∀ w, M₀.B w b = 0 → M₀.Qf (ρ w) = M₀.Qf w := by
    intro w hw
    have e : ρ w = w + (-M₀.B w f) • b := by
      simp only [ρ, sub_eq_add_neg, neg_smul]
    have hB1 : M₀.B w ((-M₀.B w f) • b) = 0 := by rw [map_smul, hw, smul_zero]
    rw [e, M₀.Qf_add, M₀.Qf_smul, hbs, hB1]
    ring
  let wv : (M₀.E ≃ₗ[K] M₀.E) → M₀.E := fun T => ρ (T f - f)
  have wv_one : wv 1 = 0 := by
    show ρ (f - f) = 0
    simp [ρ]
  have wv_mul : ∀ T₁ ∈ Λ, ∀ T₂ ∈ Λ, wv (T₁ * T₂) = wv T₁ + wv T₂ := by
    intro T₁ h₁ T₂ h₂
    obtain ⟨c, hc⟩ := hr T₁ h₁ (T₂ f - f) (hv_perp T₂ h₂)
    have e : (T₁ * T₂) f - f = (c • b) + ((T₂ f - f) + (T₁ f - f)) := by
      have h3 : (T₁ * T₂) f = T₁ (T₂ f) := rfl
      rw [h3]
      have h4 : T₁ (T₂ f) = T₁ (T₂ f - f) + T₁ f := by rw [← map_add]; congr 1; abel
      rw [h4, hc]
      abel
    show ρ ((T₁ * T₂) f - f) = ρ (T₁ f - f) + ρ (T₂ f - f)
    rw [e, ρ_add, ρ_b, zero_add, ρ_add, add_comm]
  have key : ∀ T ∈ Λ, M₀.Qf (wv T) = 0 → T = 1 := by
    intro T hT hq
    refine hani T hT ?_
    have hv : M₀.B (T f - f) b = 0 := hv_perp T hT
    have hqv : M₀.Qf (T f - f) = 0 := by rw [← Qf_ρ _ hv]; exact hq
    rintro _ ⟨e, rfl⟩
    set y := e - M₀.B e b • f with hy
    have hyb : M₀.B y b = 0 := by
      rw [hy, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hfb,
        mul_one, sub_self]
    obtain ⟨c, hc⟩ := hr T hT y hyb
    have e1 : ((T : M₀.E →ₗ[K] M₀.E) - 1) e = M₀.B e b • (T f - f) + c • b := by
      have e0 : e = M₀.B e b • f + y := by rw [hy]; abel
      have e2 : T e = M₀.B e b • T f + T y := by
        conv_lhs => rw [e0]
        rw [map_add, map_smul]
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
      calc T e - e = (M₀.B e b • T f + T y) - (M₀.B e b • f + y) := by rw [← e2, ← e0]
        _ = M₀.B e b • (T f - f) + c • b := by rw [hc, smul_sub]; abel
    have hB1 : M₀.B (M₀.B e b • (T f - f)) (c • b) = 0 := by
      rw [map_smul, map_smul, LinearMap.smul_apply, hv, smul_zero, smul_zero]
    rw [e1, M₀.Qf_add, M₀.Qf_smul, M₀.Qf_smul, hqv, hbs, hB1]
    ring
  let W : AddSubgroup M₀.E :=
    { carrier := {w | ∃ T ∈ Λ, wv T = w}
      add_mem' := by
        rintro _ _ ⟨T₁, h₁, rfl⟩ ⟨T₂, h₂, rfl⟩
        exact ⟨T₁ * T₂, Λ.mul_mem h₁ h₂, wv_mul T₁ h₁ T₂ h₂⟩
      zero_mem' := ⟨1, Λ.one_mem, wv_one⟩
      neg_mem' := by
        rintro _ ⟨T, h, rfl⟩
        exact ⟨T, h, (neg_eq_of_add_eq_zero_right (hxx _)).symm⟩ }
  have hW : Nat.card W ≤ Nat.card K ^ 2 := by
    let β : W →+ W →+ K :=
      AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => M₀.B x.1 y.1) (fun y z => by simp))
        (fun x y => by ext z; simp)
    refine card_le_sq_of_anisotropic (A := W) (K := K) (fun x => Subtype.ext (hxx x.1))
      (fun x => M₀.Qf x.1) β (fun x y => M₀.Qf_add x.1 y.1) ?_
    rintro ⟨_, T, hT, rfl⟩ hx
    exact Subtype.ext (by show wv T = 0; rw [key T hT hx]; exact wv_one)
  have hinj : Function.Injective (fun T : Λ => (⟨wv T.1, T.1, T.2, rfl⟩ : W)) := by
    intro T₁ T₂ h
    have h' : wv T₁.1 = wv T₂.1 := congrArg Subtype.val h
    have hinv : wv T₁.1⁻¹ + wv T₁.1 = 0 := by
      rw [← wv_mul _ (Λ.inv_mem T₁.2) _ T₁.2, inv_mul_cancel]
      exact wv_one
    have h0 : wv (T₁.1⁻¹ * T₂.1) = 0 := by
      rw [wv_mul _ (Λ.inv_mem T₁.2) _ T₂.2, ← h']
      exact hinv
    have h1 := key _ (Λ.mul_mem (Λ.inv_mem T₁.2) T₂.2) (by rw [h0]; exact Tim79.QuadModel.Qf_zero)
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  exact (Nat.card_le_card_of_injective _ hinj).trans hW

end Eichler

section Involution

variable {QF V : Subgroup G} {K : Type} [Field K] [CharP K 2] {γ : G → K}

theorem eichler_of_involution (M₀ : Tim79.QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e) {b : M₀.E} (hb0 : b ≠ 0)
    (hdim : Module.finrank K (LinearMap.range (T - 1)) = 2)
    (hnz : ∃ v ∈ LinearMap.range (T - 1), M₀.Qf v ≠ 0)
    (hU : ∀ y, M₀.B y b = 0 → M₀.Qf (T y - y) = 0) :
    ∀ y, M₀.B y b = 0 → ∃ c : K, T y = y + c • b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hxx : ∀ x : M₀.E, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have hN : ∀ x, (T - 1) x = T x - x := fun x => by
    simp only [LinearMap.sub_apply, Module.End.one_apply]
  have hsq : ∀ x, T (T x - x) - (T x - x) = 0 := fun x => by
    rw [map_sub, hT2]
    calc x - T x - (T x - x) = (x + x) - (T x + T x) := by abel
      _ = 0 := by rw [hxx, hxx, sub_zero]
  have hadj : ∀ x y, M₀.B (T x - x) y = M₀.B x (T y - y) := fun x y => by
    have h1 := Tim79.QuadModel.B_iso hT x (T y)
    rw [hT2 y] at h1
    rw [map_sub, LinearMap.sub_apply, map_sub, h1]
  have hiso : ∀ x y, M₀.B (T x - x) (T y - y) = 0 := fun x y => by
    rw [hadj, hsq, map_zero]
  obtain ⟨J, hJ⟩ : ∃ J : Submodule K M₀.E,
      ∀ v, v ∈ J ↔ (∃ x, T x - x = v) ∧ M₀.Qf v = 0 := by
    refine ⟨{ carrier := {v | (∃ x, T x - x = v) ∧ M₀.Qf v = 0}
              add_mem' := ?_
              zero_mem' := ⟨⟨0, by simp⟩, Tim79.QuadModel.Qf_zero⟩
              smul_mem' := ?_ }, fun v => Iff.rfl⟩
    · rintro _ _ ⟨⟨x, rfl⟩, hx⟩ ⟨⟨y, rfl⟩, hy⟩
      refine ⟨⟨x + y, by rw [map_add]; abel⟩, ?_⟩
      rw [M₀.Qf_add, hx, hy, hiso, add_zero, add_zero]
    · rintro c _ ⟨⟨x, rfl⟩, hx⟩
      refine ⟨⟨c • x, by rw [map_smul, smul_sub]⟩, ?_⟩
      rw [M₀.Qf_smul, hx, mul_zero]
  have hJI : J < LinearMap.range (T - 1) := by
    refine lt_of_le_of_ne (fun v hv => ?_) (fun heq => ?_)
    · obtain ⟨⟨x, rfl⟩, -⟩ := (hJ v).mp hv
      exact ⟨x, hN x⟩
    · obtain ⟨v, hv, hq⟩ := hnz
      exact hq ((hJ v).mp (heq ▸ hv)).2
  have hJ1 : Module.finrank K J ≤ 1 := by
    have := Submodule.finrank_lt_finrank_of_lt hJI
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨y₁, hy₁, hy₁c⟩ := hcon
  obtain ⟨u, hu⟩ : ∃ u, T y₁ - y₁ = u := ⟨_, rfl⟩
  have hu_ne : ∀ c : K, u ≠ c • b := fun c hc => hy₁c c (sub_eq_iff_eq_add'.mp (hu.trans hc))
  have hu0 : u ≠ 0 := fun h0 => hu_ne 0 (by rw [zero_smul]; exact h0)
  have huJ : u ∈ J := (hJ u).mpr ⟨⟨y₁, hu⟩, hu ▸ hU y₁ hy₁⟩
  have huq : M₀.Qf u = 0 := ((hJ u).mp huJ).2
  have hJu : ∀ w ∈ J, ∃ s : K, w = s • u := by
    have hle : Submodule.span K {u} ≤ J := by
      rw [Submodule.span_le]
      exact Set.singleton_subset_iff.mpr huJ
    have hspan := Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_span_singleton hu0]; exact hJ1)
    intro w hw
    rw [← hspan] at hw
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨s, hs.symm⟩
  have hmult : ∀ y, M₀.B y b = 0 → ∃ s : K, T y - y = s • u := fun y hy =>
    hJu _ ((hJ _).mpr ⟨⟨y, rfl⟩, hU y hy⟩)
  obtain ⟨y₀, hy₀, hBy₀⟩ : ∃ y₀, M₀.B y₀ b = 0 ∧ M₀.B y₀ u ≠ 0 := by
    by_contra hcon2
    push Not at hcon2
    obtain ⟨c, hc⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hb0 (v := u) (fun h hh => by
      rw [Tim79.QuadModel.B_comm, hcon2 h hh, neg_zero])
    exact hu_ne c hc
  have hkey : ∀ y s, T y - y = s • u → s * M₀.B y u = 0 := by
    intro y s hs
    have h1 : T y = y + s • u := by rw [← hs]; abel
    have h3 := hT y
    rw [h1, M₀.Qf_add, M₀.Qf_smul, huq, map_smul, smul_eq_mul] at h3
    linear_combination h3
  obtain ⟨s₀, hs₀⟩ := hmult y₀ hy₀
  have hs₀0 : s₀ = 0 := by
    rcases mul_eq_zero.mp (hkey y₀ s₀ hs₀) with h | h
    · exact h
    · exact absurd h hBy₀
  have hN0 : T y₀ - y₀ = 0 := by rw [hs₀, hs₀0, zero_smul]
  obtain ⟨s₁, hs₁⟩ := hmult y₁ hy₁
  have hs₁0 : s₁ = 0 := by
    have h3 : M₀.B y₀ (T y₁ - y₁) = 0 := by
      rw [← hadj, hN0, map_zero, LinearMap.zero_apply]
    rw [hs₁, map_smul, smul_eq_mul] at h3
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hBy₀
  exact hu0 (by rw [← hu, hs₁, hs₁0, zero_smul])

end Involution

section Conj

variable {G : Type} [Group G]

theorem conjSubgroup_comm_zpowers {Q : Subgroup G} {m : G} (hQ : conjSubgroup m Q = Q) (t : G) :
    conjSubgroup m ⁅Q, Subgroup.zpowers t⁆ = ⁅Q, Subgroup.zpowers (m * t * m⁻¹)⁆ := by
  have h : conjSubgroup m ⁅Q, Subgroup.zpowers t⁆ =
      ⁅conjSubgroup m Q, conjSubgroup m (Subgroup.zpowers t)⁆ := Subgroup.map_commutator _ _ _
  rw [h, hQ]
  congr 1
  show Subgroup.map (MulAut.conj m).toMonoidHom (Subgroup.zpowers t) = _
  rw [MonoidHom.map_zpowers]
  rfl

theorem card_comm_zpowers_conj {Q Z : Subgroup G} {m : G} (hQ : conjSubgroup m Q = Q)
    (hZ : conjSubgroup m Z = Z) (t : G) :
    Nat.card ↥(⁅Q, Subgroup.zpowers (m * t * m⁻¹)⁆ ⊔ Z) =
      Nat.card ↥(⁅Q, Subgroup.zpowers t⁆ ⊔ Z) := by
  have h : conjSubgroup m (⁅Q, Subgroup.zpowers t⁆ ⊔ Z) =
      ⁅Q, Subgroup.zpowers (m * t * m⁻¹)⁆ ⊔ Z := by
    have h1 : conjSubgroup m (⁅Q, Subgroup.zpowers t⁆ ⊔ Z) =
        conjSubgroup m ⁅Q, Subgroup.zpowers t⁆ ⊔ conjSubgroup m Z := Subgroup.map_sup _ _ _
    rw [h1, hZ, conjSubgroup_comm_zpowers hQ]
  rw [← h, card_conjSubgroup]

theorem isElemAbelian_comm_zpowers_conj {Q : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (Q : Set G)) (t : G) :
    IsElemAbelian 2 ⁅Q, Subgroup.zpowers (m * t * m⁻¹)⁆ ↔
      IsElemAbelian 2 ⁅Q, Subgroup.zpowers t⁆ := by
  have fwd : ∀ {m : G}, m ∈ Subgroup.normalizer (Q : Set G) → ∀ t : G,
      IsElemAbelian 2 ⁅Q, Subgroup.zpowers t⁆ →
        IsElemAbelian 2 ⁅Q, Subgroup.zpowers (m * t * m⁻¹)⁆ := by
    intro m hm t h
    rw [← conjSubgroup_comm_zpowers (conjSubgroup_eq_self_iff.mpr hm) t]
    exact CFSG.Open.IsElemAbelian.map h (MulAut.conj m).toMonoidHom
  refine ⟨fun h => ?_, fwd hm t⟩
  have := fwd (Subgroup.inv_mem _ hm) _ h
  rwa [show m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t by group] at this

end Conj

section ModelC

variable {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem exists_smul_of_singular_mem_range [CharP K 2] (M₀ : Tim79.QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0) (hbR : b ∈ LinearMap.range (T - 1))
    (hdim : Module.finrank K (LinearMap.range (T - 1)) = 2)
    (hnz : ∃ v ∈ LinearMap.range (T - 1), M₀.Qf v ≠ 0)
    {u : M₀.E} (hu : u ∈ LinearMap.range (T - 1)) (huq : M₀.Qf u = 0) :
    ∃ c : K, u = c • b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hxx : ∀ x : M₀.E, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have hN : ∀ x, (T - 1) x = T x - x := fun x => by
    simp only [LinearMap.sub_apply, Module.End.one_apply]
  have hsq : ∀ x, T (T x - x) - (T x - x) = 0 := fun x => by
    rw [map_sub, hT2]
    calc x - T x - (T x - x) = (x + x) - (T x + T x) := by abel
      _ = 0 := by rw [hxx, hxx, sub_zero]
  have hadj : ∀ x y, M₀.B (T x - x) y = M₀.B x (T y - y) := fun x y => by
    have h1 := Tim79.QuadModel.B_iso hT x (T y)
    rw [hT2 y] at h1
    rw [map_sub, LinearMap.sub_apply, map_sub, h1]
  have hiso : ∀ x y, M₀.B (T x - x) (T y - y) = 0 := fun x y => by
    rw [hadj, hsq, map_zero]
  obtain ⟨J, hJ⟩ : ∃ J : Submodule K M₀.E,
      ∀ v, v ∈ J ↔ (∃ x, T x - x = v) ∧ M₀.Qf v = 0 := by
    refine ⟨{ carrier := {v | (∃ x, T x - x = v) ∧ M₀.Qf v = 0}
              add_mem' := ?_
              zero_mem' := ⟨⟨0, by simp⟩, Tim79.QuadModel.Qf_zero⟩
              smul_mem' := ?_ }, fun v => Iff.rfl⟩
    · rintro _ _ ⟨⟨x, rfl⟩, hx⟩ ⟨⟨y, rfl⟩, hy⟩
      refine ⟨⟨x + y, by rw [map_add]; abel⟩, ?_⟩
      rw [M₀.Qf_add, hx, hy, hiso, add_zero, add_zero]
    · rintro c _ ⟨⟨x, rfl⟩, hx⟩
      refine ⟨⟨c • x, by rw [map_smul, smul_sub]⟩, ?_⟩
      rw [M₀.Qf_smul, hx, mul_zero]
  have hJI : J < LinearMap.range (T - 1) := by
    refine lt_of_le_of_ne (fun v hv => ?_) (fun heq => ?_)
    · obtain ⟨⟨x, rfl⟩, -⟩ := (hJ v).mp hv
      exact ⟨x, hN x⟩
    · obtain ⟨v, hv, hq⟩ := hnz
      exact hq ((hJ v).mp (heq ▸ hv)).2
  have hJ1 : Module.finrank K J ≤ 1 := by
    have := Submodule.finrank_lt_finrank_of_lt hJI
    omega
  have hmemJ : ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0 → v ∈ J := by
    rintro v ⟨x, rfl⟩ hq
    exact (hJ _).mpr ⟨⟨x, (hN x).symm⟩, hq⟩
  have hle : Submodule.span K {b} ≤ J := by
    rw [Submodule.span_le]
    exact Set.singleton_subset_iff.mpr (hmemJ b hbR hbs)
  have hspan := Submodule.eq_of_le_of_finrank_le hle
    (by rw [finrank_span_singleton hb0]; exact hJ1)
  have huJ := hmemJ u hu huq
  rw [← hspan] at huJ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp huJ
  exact ⟨c, hc.symm⟩

theorem mem_of_perp_le_of_stable [CharP K 2] (M₀ : Tim79.QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hdim : Module.finrank K (LinearMap.range (T - 1)) = 2)
    (hnz : ∃ v ∈ LinearMap.range (T - 1), M₀.Qf v ≠ 0)
    (hr : ∀ y, M₀.B y b = 0 → ∃ c : K, T y = y + c • b)
    {W : Submodule K M₀.E} (hW : ∀ w ∈ W, M₀.Qf w = 0) (hTW : ∀ w ∈ W, T w ∈ W)
    (hperp : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) : b ∈ W := by
  have hN : ∀ x, (T - 1) x = T x - x := fun x => by
    simp only [LinearMap.sub_apply, Module.End.one_apply]
  have hbR : b ∈ LinearMap.range (T - 1) := by
    by_cases hA : ∀ h, M₀.B h b = 0 → T h = h
    · exfalso
      have hone := Tim79.QuadModel.eq_one_of_fix_perp hT hb0 hbs hA
      have h0 : LinearMap.range (T - 1) = ⊥ := by
        refine (Submodule.eq_bot_iff _).mpr ?_
        rintro _ ⟨e, rfl⟩
        rw [hN, hone, sub_self]
      rw [h0, finrank_bot] at hdim
      omega
    · push Not at hA
      obtain ⟨h₀, hh₀, hTh₀⟩ := hA
      obtain ⟨c₀, hc₀⟩ := hr h₀ hh₀
      have hc₀0 : c₀ ≠ 0 := by
        rintro rfl
        exact hTh₀ (by rw [hc₀, zero_smul, add_zero])
      exact ⟨c₀⁻¹ • h₀, by
        rw [map_smul, hN, hc₀, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc₀0, one_smul]⟩
  by_contra hbW
  have hfix : ∀ y ∈ W, T y = y := by
    intro y hy
    have hyW : T y - y ∈ W := W.sub_mem (hTW y hy) hy
    have hyR : T y - y ∈ LinearMap.range (T - 1) := ⟨y, hN y⟩
    obtain ⟨c, hc⟩ := exists_smul_of_singular_mem_range M₀ hT hT2 hb0 hbs hbR hdim hnz hyR
      (hW _ hyW)
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, sub_eq_zero] at hc
      exact hc
    · exfalso
      apply hbW
      have : b = c⁻¹ • (T y - y) := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact W.smul_mem _ hyW
  obtain ⟨f, hf⟩ := hbR
  rw [hN] at hf
  refine hbW (hperp b fun w hw => ?_)
  have h1 : M₀.B (T w) (T (T f)) = M₀.B w (T f) := Tim79.QuadModel.B_iso hT w (T f)
  rw [hfix w hw, hT2 f] at h1
  have h2 : M₀.B w b = 0 := by
    rw [← hf, map_sub, h1, sub_self]
  rw [Tim79.QuadModel.B_comm, h2, neg_zero]

theorem exists_submodule_of_card_eq [Finite K] (M₀ : Tim79.QuadModel QF V K γ) {w : ℕ}
    (hdim : Module.finrank K M₀.E = 2 * w) {U : AddSubgroup M₀.E}
    (hU : ∀ e ∈ U, M₀.Qf e = 0) (hcard : Nat.card U = Nat.card K ^ w) :
    ∃ W : Submodule K M₀.E, (∀ v, v ∈ W ↔ v ∈ U) ∧
      ∀ v, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  set W : Submodule K M₀.E := Submodule.span K (U : Set M₀.E) with hWdef
  have hUW : ∀ u ∈ U, u ∈ W := fun u hu => Submodule.subset_span (SetLike.mem_coe.2 hu)
  have hWs : ∀ x ∈ W, M₀.Qf x = 0 := by
    intro x hx
    exact (Tim79.QuadModel.toQuadraticForm_apply M₀ x).symm.trans
      (CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span (Q := M₀.toQuadraticForm)
        (S := (U : Set M₀.E))
        (fun u hu => (Tim79.QuadModel.toQuadraticForm_apply M₀ u).trans (hU u hu))
        (fun u hu v hv => by
          rw [Tim79.QuadModel.polar_toQuadraticForm]
          exact Tim79.QuadModel.B_eq_zero_of_singular M₀ hU hu hv) hx)
  have hle : Module.finrank K W ≤ w := by
    have := Tim79.QuadModel.two_mul_finrank_le_of_totallySingular M₀ W hWs
    omega
  have hKpos : 1 < Nat.card K := Finite.one_lt_card
  have hinj : Function.Injective (fun u : U => (⟨u.1, hUW u.1 u.2⟩ : W)) := fun a b h =>
    Subtype.ext (congrArg (fun z : W => (z : M₀.E)) h)
  have hWcard : Nat.card W = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
  have hge : w ≤ Module.finrank K W := by
    have h1 : Nat.card U ≤ Nat.card W := Nat.card_le_card_of_injective _ hinj
    rw [hcard, hWcard] at h1
    exact (Nat.pow_le_pow_iff_right hKpos).mp h1
  have hfin : Module.finrank K W = w := le_antisymm hle hge
  have hbij : Function.Bijective (fun u : U => (⟨u.1, hUW u.1 u.2⟩ : W)) :=
    hinj.bijective_of_nat_card_le (by rw [hWcard, hfin, hcard])
  have hWU : ∀ v, v ∈ W → v ∈ U := fun v hv => by
    obtain ⟨u, hu⟩ := hbij.2 ⟨v, hv⟩
    have h' : (u : M₀.E) = v := congrArg (fun z : W => (z : M₀.E)) hu
    exact h' ▸ u.2
  refine ⟨W, fun v => ⟨hWU v, hUW v⟩, fun v hv => ?_⟩
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]
  have hsub : W ≤ M₀.B.orthogonal W := fun x hx => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact Tim79.QuadModel.B_eq_zero_of_singular M₀ (U := W.toAddSubgroup) hWs hy hx
  have hdimperp : Module.finrank K (M₀.B.orthogonal W) = Module.finrank K W := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, hdim, hfin]
    omega
  have heq : W = M₀.B.orthogonal W := Submodule.eq_of_le_of_finrank_eq hsub hdimperp.symm
  have hv' : v ∈ M₀.B.orthogonal W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [Tim79.QuadModel.B_comm, hv u hu, neg_zero]
  rw [heq]
  exact hv'

end ModelC

end CFSG.RankThree.GF2n.Stroth80
