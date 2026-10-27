module

public import CFSG.RankThree.GF2n.Smith81.LinOddDefs
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.LinGammaAlg
public import CFSG.RankThree.GF2n.Smith81.LinGammaCoord

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement
open Module

namespace LinGammaEven

section Lin

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem range_eq_ker (B : LinearMap.BilinForm K E) (Qf : E → K) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (T : E ≃ₗ[K] E) (hTT : ∀ e, T (T e) = e) (hTB : ∀ e f, B (T e) (T f) = B e f)
    (N : E →ₗ[K] E) (hNapp : ∀ f, N f = T f - f)
    {m : ℕ} (hE : finrank K E = 4 * m) (W₁ W₂ : Submodule K E) (hW : IsCompl W₁ W₂)
    (hW₁T : ∀ w ∈ W₁, T w ∈ W₁) (hW₂T : ∀ w ∈ W₂, T w ∈ W₂)
    (hW₁Q : ∀ w ∈ W₁, Qf w = 0) (hW₂Q : ∀ w ∈ W₂, Qf w = 0)
    (hN₁ : finrank K (W₁.map N) = m) (hN₂ : finrank K (W₂.map N) = m) :
    LinearMap.range N = LinearMap.ker N ∧ (∀ e, Qf (N e) = 0) ∧
      finrank K ↥(LinearMap.ker N ⊓ W₁) = m ∧ finrank K ↥(LinearMap.ker N ⊓ W₂) = m := by
  have h2 : ∀ e : E, e + e = 0 := fun e => by rw [← two_smul K e, hK2, zero_smul]
  have hneg : ∀ e : E, -e = e := fun e => neg_eq_of_add_eq_zero_right (h2 e)
  have hN : ∀ f, N f = T f + f := fun f => by rw [hNapp, sub_eq_add_neg, hneg]
  have hNN : ∀ u, N (N u) = 0 := fun u => by
    rw [hN, hN, map_add, hTT, show u + T u + (T u + u) = (u + u) + (T u + T u) by abel, h2, h2,
      add_zero]
  have hadj : ∀ a f, B a (N f) = B (N a) f := fun a f => by
    have : B a (T f) = B (T a) f := by rw [← hTB a (T f), hTT]
    simp only [hN, map_add, LinearMap.add_apply, this]
  have hN₁' : ∀ w ∈ W₁, N w ∈ W₁ := fun w hw => by
    rw [hN]
    exact W₁.add_mem (hW₁T w hw) hw
  have hN₂' : ∀ w ∈ W₂, N w ∈ W₂ := fun w hw => by
    rw [hN]
    exact W₂.add_mem (hW₂T w hw) hw
  have hiso_of : ∀ S : Submodule K E, (∀ w ∈ S, Qf w = 0) → ∀ u ∈ S, ∀ v ∈ S, B u v = 0 :=
    fun S hS u hu v hv => by
      have := hQadd u v
      rw [hS u hu, hS v hv, hS _ (S.add_mem hu hv)] at this
      linear_combination -this
  have hd₁ := LinGamma.two_mul_finrank_le_of_iso B hK2 halt hnd W₁ (hiso_of W₁ hW₁Q)
  have hd₂ := LinGamma.two_mul_finrank_le_of_iso B hK2 halt hnd W₂ (hiso_of W₂ hW₂Q)
  have hdsum := Submodule.finrank_add_eq_of_isCompl hW
  have hW₁d : finrank K W₁ = 2 * m := by omega
  have hW₂d : finrank K W₂ = 2 * m := by omega
  have hQN : ∀ e, Qf (N e) = 0 := by
    intro e
    have he : e ∈ W₁ ⊔ W₂ := by
      rw [hW.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp he
    rw [map_add, hQadd, hW₁Q _ (hN₁' a ha), hW₂Q _ (hN₂' b hb), ← hadj a (N b), hNN, map_zero]
    ring
  have hker : finrank K (LinearMap.ker N) = 2 * m := by
    have := LinGamma.finrank_ker_of_isCompl N W₁ W₂ hW hN₁' hN₂' hN₁ hN₂
    omega
  have hR : finrank K (LinearMap.range N) = 2 * m :=
    LinGamma.finrank_range_of_isCompl N W₁ W₂ hW hN₁' hN₂' hN₁ hN₂
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨e, rfl⟩
    exact LinearMap.mem_ker.mpr (hNN e)
  refine ⟨Submodule.eq_of_le_of_finrank_eq hle (by omega), hQN, ?_, ?_⟩
  · have h := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker N W₁
    rw [inf_comm]
    omega
  · have h := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker N W₂
    rw [inf_comm]
    omega

end Lin

end LinGammaEven

section Group

variable {G : Type} [Group G] {V : Subgroup G} {x : G}

theorem gamma_conclusions_of_card_gen [Finite G]
    {M Q Z : Subgroup G} {a b m : ℕ} (H : StrothHyp M Q Z)
    (hZV : Z ≤ V) (hVQ : V ≤ Q) (hVsq : ∀ v ∈ V, v * v = 1)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx2 : x * x = 1)
    (hVcard : Nat.card V = Nat.card Z ^ a)
    (hC : Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ b)
    (hab : a = b + m) (hdim : HasDimOn V Z m x) :
    ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧ Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
  have hinv : ∀ a ∈ V, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hVsq a ha)
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have h := inv_eq_of_mul_eq_one_right (hVsq (a * b) (V.mul_mem ha hb))
    rw [mul_inv_rev, hinv a ha, hinv b hb] at h
    exact h.symm
  have hcommV : ∀ v ∈ V, ⁅v, x⁆ ∈ V := fun v hv => by
    have e : ⁅v, x⁆ = v * (x * v * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hv (V.inv_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv))
  have key : ∀ a ∈ V, ∀ b ∈ V, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro a ha b hb
    have hcb : ⁅b, x⁆ ∈ V := hcommV b hb
    have e1 : ⁅a * b, x⁆ = a * ⁅b, x⁆ * (x * a⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e1, hcomm a ha _ hcb, hcomm _ (hcommV a ha) _ hcb]
    simp only [commutatorElement_def]
    group
  let f : V →* G :=
    { toFun := fun v => ⁅(v : G), x⁆
      map_one' := by simp
      map_mul' := fun a b => key a a.2 b b.2 }
  have hker : f.ker = (V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show ⁅(v : G), x⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have hrange : f.range = ⁅V, Subgroup.zpowers x⁆ := by
    rw [commutator_zpowers_eq_closure hx2]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, v.2, rfl⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hkercard : Nat.card f.ker = Nat.card Z ^ b := by
    rw [hker, ← hC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul : Nat.card f.ker * Nat.card f.range = Nat.card V := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hrcard : Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
    rw [← hrange]
    have h1 : Nat.card Z ^ b * Nat.card f.range = Nat.card Z ^ b * Nat.card Z ^ m := by
      have h := hmul
      rw [hkercard, hVcard] at h
      rw [h, hab, pow_add]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hZpos _) h1
  refine ⟨?_, hrcard⟩
  have hDV : ⁅V, Subgroup.zpowers x⁆ ≤ V := by
    rw [← hrange]
    rintro _ ⟨v, rfl⟩
    exact hcommV v v.2
  have hZQ : Z ≤ Q := hZV.trans hVQ
  have hZn : Z ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhQ := hVQ (hDV hh)
      rwa [show z * h * z⁻¹ = h by rw [Z_central H hz hhQ]; group]
    · intro hh
      have hhQ' : z * h * z⁻¹ ∈ Q := hVQ (hDV hh)
      have hhQ : h ∈ Q := by
        have := Q.mul_mem (Q.mul_mem (Q.inv_mem (hZQ hz)) hhQ') (hZQ hz)
        rwa [show z⁻¹ * (z * h * z⁻¹) * z = h by group] at this
      rwa [show z * h * z⁻¹ = h by rw [Z_central H hz hhQ]; group] at hh
  have hprod := card_sup_mul_card_inf_of_normalizer hZn
  unfold HasDimOn at hdim
  rw [hdim, hrcard] at hprod
  have h1 : Nat.card Z ^ (m + 1) * Nat.card ↥(⁅V, Subgroup.zpowers x⁆ ⊓ Z) =
      Nat.card Z ^ (m + 1) * 1 := by
    rw [hprod, mul_one]
    ring
  exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_of_mul_eq_mul_left (pow_pos hZpos _) h1)

end Group

section Model

variable {G : Type} [Group G] [Finite G]

theorem linGammaEven_of_model {M Q Z B X : Subgroup G} {x : G} {n m : ℕ} {V₁ V₂ : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : n = 2 * m) (hm : 2 ≤ m) (hV₁ : ∀ v ∈ V₁, v * v = 1) (hV₂ : ∀ v ∈ V₂, v * v = 1)
    (hs : Sit M Q Z X x) (hx : x ∈ Lgen M (LB M Q B)) (hQ : Q ⊓ QB X = ⊥) :
    Nat.card ↥(Kx Q X) = Nat.card Z ^ (n + 1) ∧
      ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
        Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 1) ∧
        ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧ Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
  have H := hc.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hq : 2 ≤ Nat.card Z := by
    have := H.q4
    omega
  have hcard : Nat.card K = Nat.card Z := hD.card
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hn3 : 3 ≤ n := by omega
  have hn1 : n + 1 = 2 * m + 1 := by omega
  have hw : Width Q Z n := hS.width H
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hxH : x ∈ H0 M Z := hSH hx
  have hHD := lin115RankStatement_holds G M Q Z B X x n V₁ V₂ hc hS hn3 hs hx hQ
  have hnm : n / 2 = m := by omega
  rw [hnm] at hHD
  obtain ⟨φ, hφπ, -, hφiso⟩ := exists_actionHom_H0 H hD
  obtain ⟨W₁, W₂, hW₁, hW₂⟩ := LinSetup.exists_subspaces hc hn3 hS hD φ hφπ
  obtain ⟨F, hFfield, hFfin, hFcard, φ', -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup, hs₁, hs₂,
    -, -⟩ := id hS
  have hxN₁ : x ∈ Subgroup.normalizer (V₁ : Set G) := hs₁.1 hx
  have hxN₂ : x ∈ Subgroup.normalizer (V₂ : Set G) := hs₂.1 hx
  have hV₁card : Nat.card V₁ = Nat.card Z ^ (n + 1) := by
    obtain ⟨-, hN₁, ψ₁, -⟩ := hs₁
    exact card_eq_pow_of_sectionIso hZV₁ hFcard ψ₁
  have hV₂card : Nat.card V₂ = Nat.card Z ^ (n + 1) := by
    obtain ⟨-, hN₂, ψ₂, -⟩ := hs₂
    exact card_eq_pow_of_sectionIso hZV₂ hFcard ψ₂
  obtain ⟨T, hπT, hQT, hBT⟩ : ∃ T : M₀.E ≃ₗ[K] M₀.E, (∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)) ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧ ∀ e f, M₀.B (T e) (T f) = M₀.B e f := by
    refine ⟨φ ⟨x, hxH⟩, fun y hy => hφπ ⟨x, hxH⟩ y hy, hφiso ⟨x, hxH⟩, fun e f => ?_⟩
    have h1 := M₀.Qf_add (φ ⟨x, hxH⟩ e) (φ ⟨x, hxH⟩ f)
    have h2 := M₀.Qf_add e f
    rw [← map_add, hφiso _ (e + f), hφiso _ e, hφiso _ f] at h1
    linear_combination h2 - h1
  let A : XAct M₀ x := ⟨T, hπT, hQT, hBT⟩
  have hTT : ∀ e, T (T e) = e := fun e => A.T_T H hxM hx2 e
  set N : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - LinearMap.id
  have hNapp : ∀ f, N f = T f - f := fun f => rfl
  have hstab : ∀ (V : Subgroup G) (W : Submodule K M₀.E), V ≤ Q →
      x ∈ Subgroup.normalizer (V : Set G) → (∀ e, e ∈ W ↔ e ∈ M₀.img V) → ∀ w ∈ W, T w ∈ W := by
    intro V W hVQ hxV hW w hw
    obtain ⟨v, hvV, hvQ, rfl⟩ := (hW w).mp hw
    rw [← hπT v hvQ]
    exact (hW _).mpr (M₀.pi_mem_img ((Subgroup.mem_normalizer_iff.mp hxV v).mp hvV)
      (conj_mem_Q H hxM hvQ))
  have hsing : ∀ (V : Subgroup G) (W : Submodule K M₀.E), V ≤ Q → (∀ v ∈ V, v * v = 1) →
      (∀ e, e ∈ W ↔ e ∈ M₀.img V) → ∀ w ∈ W, M₀.Qf w = 0 := by
    intro V W hVQ hVsq hW w hw
    obtain ⟨v, hvV, hvQ, rfl⟩ := (hW w).mp hw
    exact (GM.sq_eq_one_iff hD hvQ).mp (by rw [pow_two]; exact hVsq v hvV)
  have hW₁T := hstab V₁ W₁ hV₁Q hxN₁ hW₁
  have hW₂T := hstab V₂ W₂ hV₂Q hxN₂ hW₂
  have hW₁Q := hsing V₁ W₁ hV₁Q hV₁ hW₁
  have hW₂Q := hsing V₂ W₂ hV₂Q hV₂ hW₂
  have hN₁' : ∀ w ∈ W₁, N w ∈ W₁ := fun w hw => by
    rw [hNapp]
    exact W₁.sub_mem (hW₁T w hw) hw
  have hN₂' : ∀ w ∈ W₂, N w ∈ W₂ := fun w hw => by
    rw [hNapp]
    exact W₂.sub_mem (hW₂T w hw) hw
  have hcompl : IsCompl W₁ W₂ := by
    have h := isCompl_img M₀ hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro e he
      have he' : e ∈ M₀.img V₁ ⊓ M₀.img V₂ := ⟨(hW₁ e).mp he.1, (hW₂ e).mp he.2⟩
      rw [h.inf_eq_bot] at he'
      exact (Submodule.mem_bot K).mpr (AddSubgroup.mem_bot.mp he')
    · rw [codisjoint_iff, eq_top_iff]
      intro e _
      have he : e ∈ M₀.img V₁ ⊔ M₀.img V₂ := by
        rw [h.sup_eq_top]
        exact AddSubgroup.mem_top e
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp he
      exact Submodule.add_mem_sup ((hW₁ a).mpr ha) ((hW₂ b).mpr hb)
  have hE : finrank K M₀.E = 4 * m := by
    have := hD.finrank_E hw (by rw [hcard]; omega : 1 < Nat.card K)
    omega
  have hfr : ∀ (V : Subgroup G) (W : Submodule K M₀.E), Z ≤ V → V ≤ Q →
      x ∈ Subgroup.normalizer (V : Set G) → (∀ e, e ∈ W ↔ e ∈ M₀.img V) → HasDimOn V Z m x →
      finrank K ↥(W.map N) = m := by
    intro V W hZV hVQ hxV hW hdim
    have h := card_commSup_section A H hxM hx2 hZV hVQ hxV W hW
    unfold HasDimOn at hdim
    rw [hdim] at h
    have h2 : Nat.card ↥(W.map N) = Nat.card Z ^ m := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card Z by omega)
      rw [← h, pow_succ']
    rw [Module.natCard_eq_pow_finrank (K := K), hcard] at h2
    exact Nat.pow_right_injective hq h2
  have hfr₁ := hfr V₁ W₁ hZV₁ hV₁Q hxN₁ hW₁ hHD.1
  have hfr₂ := hfr V₂ W₂ hZV₂ hV₂Q hxN₂ hW₂ hHD.2
  obtain ⟨hRK, hQN, hker₁, hker₂⟩ := LinGammaEven.range_eq_ker M₀.B M₀.Qf hK2 M₀.alt M₀.nondeg
    M₀.Qf_add T hTT hBT N hNapp hE W₁ W₂ hcompl hW₁T hW₂T hW₁Q hW₂Q hfr₁ hfr₂
  have hkerdim : finrank K (LinearMap.ker N) = 2 * m := by
    have := LinGamma.finrank_ker_of_isCompl N W₁ W₂ hcompl hN₁' hN₂' hfr₁ hfr₂
    omega
  have hpow : ∀ R : Submodule K M₀.E,
      Nat.card (preimageSub M₀ R) = Nat.card Z ^ (finrank K R + 1) := by
    intro R
    rw [card_preimageSub hZQ, Module.natCard_eq_pow_finrank (K := K), hcard, pow_succ]
  have hcomm_sq : ∀ q ∈ Q, ⁅q, x⁆ ^ 2 = 1 := by
    intro q hq
    rw [GM.sq_eq_one_iff hD (comm_mem_Q H hxM hq), A.pi_comm H hxM hq]
    have e : M₀.π q - T (M₀.π q) = (-1 : K) • N (M₀.π q) := by
      rw [neg_one_smul, hNapp]
      abel
    change M₀.Qf (M₀.π q - T (M₀.π q)) = 0
    rw [e, M₀.Qf_smul, hQN]
    ring
  have hcomm_x : ∀ q ∈ Q, ⁅q, x⁆ * x = x * ⁅q, x⁆ := by
    intro q hq
    have hmem : ⁅q, x⁆ ∈ Subgroup.closure (commGens Q x) := by
      rw [← commutator_zpowers_eq_closure' hx2]
      exact Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
    have h := D_comm_x hD A hK2 H hxM hx2 hmem
    rw [hcomm_sq q hq] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hCx : Q ⊓ Subgroup.centralizer ({x} : Set G) = preimageSub M₀ (LinearMap.ker N) := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      have hcomm : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      refine mem_preimageSub.mpr ⟨hyQ, ?_⟩
      show N (M₀.π y) = 0
      rw [hNapp, ← A.hπ y hyQ, show x * y * x⁻¹ = y by rw [← hcomm]; group, sub_self]
    · intro hy
      obtain ⟨hyQ, hyK⟩ := mem_preimageSub.mp hy
      rw [← hRK] at hyK
      have hyC : M₀.π y ∈ commSpace A := by
        obtain ⟨f, hf⟩ := hyK
        rw [← hf]
        obtain ⟨q, hq, hπq⟩ := M₀.π_surj (-f)
        have h := ((mem_commSup_iff A H hxM hx2 hZQ).mp (Subgroup.mem_sup_left
          (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)))).2
        rw [A.pi_comm H hxM hq, hπq] at h
        have e : N f = -f - T (-f) := by
          rw [hNapp, map_neg]
          abel
        rw [e]
        exact h
      obtain ⟨q, hq, z₀, hz₀, rfl⟩ := exists_comm_rep A H hxM hyQ hyC
      refine ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hz : z₀ * x = x * z₀ := (mul_inv_eq_iff_eq_mul.mp (hxZ z₀ hz₀)).symm
      rw [mul_assoc, hz, ← mul_assoc, hcomm_x q hq, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [Kx_eq hs h12, hCx, hpow, hkerdim, hn1]
  ·
    have hmain : ∀ (V : Subgroup G) (Wk : Submodule K M₀.E), Z ≤ V → V ≤ Q →
        (∀ v ∈ V, v * v = 1) → x ∈ Subgroup.normalizer (V : Set G) →
        Nat.card V = Nat.card Z ^ (n + 1) → (∀ e, e ∈ Wk ↔ e ∈ M₀.img V) →
        finrank K ↥(LinearMap.ker N ⊓ Wk) = m → HasDimOn V Z m x →
        Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 1) ∧
        ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧
          Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
      intro V Wk hZV hVQ hVsq hxV hVcard hWk hdimk hdim
      have hVeq : V ⊓ Subgroup.centralizer ({x} : Set G) =
          V ⊓ preimageSub M₀ (LinearMap.ker N) := by
        rw [← hCx]
        ext v
        constructor
        · rintro ⟨hvV, hvC⟩
          exact ⟨hvV, hVQ hvV, hvC⟩
        · rintro ⟨hvV, hvQ, hvC⟩
          exact ⟨hvV, hvC⟩
      have hZS : Z ≤ V ⊓ preimageSub M₀ (LinearMap.ker N) := fun z hz =>
        ⟨hZV hz, mem_preimageSub.mpr ⟨hZQ hz, by
          rw [(M₀.π_ker z (hZQ hz)).mpr hz]
          exact Submodule.zero_mem _⟩⟩
      have hSQ : V ⊓ preimageSub M₀ (LinearMap.ker N) ≤ Q := fun v hv => hVQ hv.1
      have hC : Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 1) := by
        rw [hVeq, M₀.card_eq hSQ hZS]
        have himg : Nat.card ↥(M₀.img (V ⊓ preimageSub M₀ (LinearMap.ker N))) =
            Nat.card K ^ m := by
          rw [← hdimk, ← Module.natCard_eq_pow_finrank (K := K)]
          refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
          constructor
          · rintro ⟨y, hyS, hyQ, rfl⟩
            exact ⟨(mem_preimageSub.mp hyS.2).2, (hWk _).mpr (M₀.pi_mem_img hyS.1 hyQ)⟩
          · rintro ⟨heWc, heWk⟩
            obtain ⟨y, hyV, hyQ, rfl⟩ := (hWk e).mp heWk
            exact ⟨y, ⟨hyV, mem_preimageSub.mpr ⟨hyQ, heWc⟩⟩, hyQ, rfl⟩
        rw [himg, hcard]
        ring
      exact ⟨hC, gamma_conclusions_of_card_gen H hZV hVQ hVsq hxV hx2 hVcard hC
        (by omega) hdim⟩
    rintro V (hV | hV)
    · rw [hV]
      exact hmain V₁ W₁ hZV₁ hV₁Q hV₁ hxN₁ hV₁card hW₁ hker₁ hHD.1
    · rw [Set.mem_singleton_iff.mp hV]
      exact hmain V₂ W₂ hZV₂ hV₂Q hV₂ hxN₂ hV₂card hW₂ hker₂ hHD.2

end Model

theorem linGammaEvenStatement_holds : LinGammaEvenStatement := by
  intro G _ _ M Q Z B X x n m V₁ V₂ hc hS hn hm hV₁ hV₂ hs hx hQ
  obtain ⟨m', γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  exact linGammaEven_of_model hD hc hS hn hm hV₁ hV₂ hs hx hQ

end CFSG.RankThree.GF2n.Smith81
