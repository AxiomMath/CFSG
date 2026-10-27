module

public import CFSG.RankThree.GF2n.Smith81.LinCoord
import CFSG.RankThree.GF2n.Smith81.LinGammaAlg
import CFSG.RankThree.GF2n.Smith81.LinGammaCoord
public import CFSG.RankThree.GF2n.Smith81.LinRank

public section

namespace CFSG.RankThree.GF2n.Smith81.LinFour

open Module

section Lagrangian

variable {K E : Type*} [Field K] [Finite K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem card_le_pow_of_lagrangian_fixed {ι : Type*} (B : LinearMap.BilinForm K E)
    (hK2 : (2 : K) = 0) (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (W₁ W₂ Kt : Submodule K E) (hW : IsCompl W₁ W₂)
    (hW₁ : ∀ u ∈ W₁, ∀ v ∈ W₁, B u v = 0) (hW₂ : ∀ u ∈ W₂, ∀ v ∈ W₂, B u v = 0)
    (hKt : ∀ u ∈ Kt, ∀ v ∈ Kt, B u v = 0) (hdim : 2 * finrank K Kt = finrank K E)
    (S : ι → (E ≃ₗ[K] E)) (hSinj : Function.Injective S)
    (hS : ∀ i, (∀ e f, B (S i e) (S i f) = B e f) ∧ (∀ e, S i (S i e) = e) ∧
      (∀ w ∈ W₁, S i w ∈ W₁) ∧ (∀ w ∈ W₂, S i w ∈ W₂) ∧ ∀ k ∈ Kt, S i k = k) :
    Nat.card ι ≤
      Nat.card K ^ ((finrank K W₁ - finrank K ↥(Kt ⊓ W₁)) * finrank K ↥(Kt ⊓ W₁)) := by
  classical
  have hBnd : B.Nondegenerate := LinGamma.nondeg_of B hK2 halt hnd
  have hsymm := LinGamma.B_symm B hK2 halt
  have hKperp : B.orthogonal Kt = Kt := by
    have hle : Kt ≤ B.orthogonal Kt := fun v hv =>
      (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => hKt u hu v hv
    have h1 := LinearMap.BilinForm.finrank_orthogonal hBnd Kt
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hSK : ∀ i e, S i e - e ∈ Kt := by
    intro i e
    obtain ⟨hB, -, -, -, hfix⟩ := hS i
    rw [← hKperp]
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun k hk => ?_
    show B k (S i e - e) = 0
    have h1 := hB k e
    rw [hfix k hk] at h1
    rw [map_sub, h1, sub_self]
  set C₁ : Submodule K E := Kt ⊓ W₁ with hC₁
  obtain ⟨D₀, hD₀⟩ := Submodule.exists_isCompl C₁
  set D : Submodule K E := D₀ ⊓ W₁ with hD
  have hCW : C₁ ≤ W₁ := inf_le_right
  have hDW : D ≤ W₁ := inf_le_right
  have hsupD : C₁ ⊔ D = W₁ := by
    rw [hD, ← sup_inf_assoc_of_le D₀ hCW, hD₀.sup_eq_top, top_inf_eq]
  have hinfD : C₁ ⊓ D = ⊥ := by
    refine le_bot_iff.mp ?_
    calc C₁ ⊓ D ≤ C₁ ⊓ D₀ := inf_le_inf_left _ inf_le_left
      _ = ⊥ := hD₀.inf_eq_bot
  have hDdim : finrank K D = finrank K W₁ - finrank K C₁ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq C₁ D
    rw [hsupD, hinfD, finrank_bot] at h
    omega
  have hmemC : ∀ i, ∀ d ∈ D, S i d - d ∈ C₁ := fun i d hd =>
    ⟨hSK i d, W₁.sub_mem ((hS i).2.2.1 d (hDW hd)) (hDW hd)⟩
  let Φ : ι → (↥D →ₗ[K] ↥C₁) := fun i =>
    LinearMap.codRestrict C₁
      (((S i : E ≃ₗ[K] E).toLinearMap - LinearMap.id).domRestrict D)
      (fun d => hmemC i d d.2)
  have hΦapp : ∀ i (d : D), ((Φ i d : C₁) : E) = S i d - d := fun i d => rfl
  have hΦinj : Function.Injective Φ := by
    intro i j hij
    apply hSinj
    have hD' : ∀ d ∈ D, S i d = S j d := by
      intro d hd
      have h1 := congrArg (fun L : ↥D →ₗ[K] ↥C₁ => ((L ⟨d, hd⟩ : C₁) : E)) hij
      simp only [hΦapp] at h1
      exact sub_left_injective h1
    have hC' : ∀ c ∈ C₁, S i c = S j c := by
      intro c hc
      rw [(hS i).2.2.2.2 c hc.1, (hS j).2.2.2.2 c hc.1]
    have hW₁' : ∀ w ∈ W₁, S i w = S j w := by
      intro w hw
      rw [← hsupD] at hw
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add, map_add, hC' c hc, hD' d hd]
    have hW₂' : ∀ f ∈ W₂, S i f = S j f := by
      intro f hf
      have hdiff : S i f - S j f ∈ W₂ := W₂.sub_mem ((hS i).2.2.2.1 f hf) ((hS j).2.2.2.1 f hf)
      have hadj : ∀ k, ∀ e, B e (S k f) = B (S k e) f := by
        intro k e
        have h1 := (hS k).1 e (S k f)
        rw [(hS k).2.1 f] at h1
        exact h1.symm
      have hz : ∀ e, B (S i f - S j f) e = 0 := by
        intro e
        rw [hsymm]
        have he : e ∈ W₁ ⊔ W₂ := by
          rw [hW.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp he
        have h₁ : B e₁ (S i f - S j f) = 0 := by
          rw [map_sub, hadj i e₁, hadj j e₁, hW₁' e₁ he₁, sub_self]
        have h₂ : B e₂ (S i f - S j f) = 0 := hW₂ e₂ he₂ _ hdiff
        rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
      exact sub_eq_zero.mp (hnd _ hz)
    apply LinearEquiv.ext
    intro e
    have he : e ∈ W₁ ⊔ W₂ := by
      rw [hW.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp he
    rw [map_add, map_add, hW₁' e₁ he₁, hW₂' e₂ he₂]
  have hfin : Finite (↥D →ₗ[K] ↥C₁) := Module.finite_of_finite K
  calc Nat.card ι ≤ Nat.card (↥D →ₗ[K] ↥C₁) := Nat.card_le_card_of_injective Φ hΦinj
    _ = Nat.card K ^ finrank K (↥D →ₗ[K] ↥C₁) := Module.natCard_eq_pow_finrank
    _ = Nat.card K ^ ((finrank K W₁ - finrank K C₁) * finrank K C₁) := by
      rw [Module.finrank_linearMap, hDdim]

end Lagrangian

section Model

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem Qf_pi_eq_zero_of_sq (M₀ : Tim79.QuadModel Q Z K γ) {c : G} (hc : c ∈ Q)
    (h : c ^ 2 = 1) : M₀.Qf (M₀.π c) = 0 := by
  have h1 := M₀.sq_eq c hc
  have h0 : γ 1 = 0 := by
    have := M₀.sq_eq 1 Q.one_mem
    rw [one_pow, Tim79.QuadModel.pi_one M₀, Tim79.QuadModel.Qf_zero] at this
    exact this
  rw [h, h0] at h1
  exact h1.symm

theorem B_eq_zero_of_Qf_eq_zero (M₀ : Tim79.QuadModel Q Z K γ) {P : M₀.E → Prop}
    (hadd : ∀ u v, P u → P v → P (u + v)) (hP : ∀ e, P e → M₀.Qf e = 0) {u v : M₀.E}
    (hu : P u) (hv : P v) : M₀.B u v = 0 := by
  have h := M₀.Qf_add u v
  rw [hP u hu, hP v hv, hP _ (hadd u v hu hv)] at h
  linear_combination -h

theorem B_eq_of_Qf_eq (M₀ : Tim79.QuadModel Q Z K γ) (T : M₀.E ≃ₗ[K] M₀.E)
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (e f : M₀.E) : M₀.B (T e) (T f) = M₀.B e f := by
  have h1 := M₀.Qf_add (T e) (T f)
  have h2 := M₀.Qf_add e f
  rw [← map_add, hT (e + f), hT e, hT f] at h1
  linear_combination h2 - h1

end Model

section Coord

open CFSG.RankThree.GF2n.Stroth80

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')

theorem exists_summands : ∃ W₁ W₂ : Submodule K E, (∀ e, e ∈ W₁ ↔ e ∈ C.W₁) ∧
    (∀ e, e ∈ W₂ ↔ e ∈ C.W₂) ∧ IsCompl W₁ W₂ := by
  let W₁ : Submodule K E :=
    { carrier := {e | (C.Ψ e).2 = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, Prod.snd_add] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c e he => by
        simp only [Set.mem_setOf_eq] at *
        rw [C.smul, he, smul_zero] }
  let W₂ : Submodule K E :=
    { carrier := {e | (C.Ψ e).1 = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, Prod.fst_add] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c e he => by
        simp only [Set.mem_setOf_eq] at *
        rw [C.smul, he, smul_zero] }
  refine ⟨W₁, W₂, fun e => C.mem_W₁.symm, fun e => C.mem_W₂.symm, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro e he
    have h1 : (C.Ψ e).2 = 0 := he.1
    have h2 : (C.Ψ e).1 = 0 := he.2
    rw [Submodule.mem_bot]
    apply C.Ψ.injective
    rw [map_zero]
    exact Prod.ext h2 h1
  · rw [codisjoint_iff, eq_top_iff]
    intro e _
    have h1 : C.inl (C.Ψ e).1 ∈ W₁ := C.mem_W₁.mp (C.inl_mem_W₁ _)
    have h2 : C.inr (C.Ψ e).2 ∈ W₂ := C.mem_W₂.mp (C.inr_mem_W₂ _)
    rw [C.eq_inl_add_inr e]
    exact Submodule.add_mem_sup h1 h2

theorem preserves_of_fixed {T : E ≃ₗ[K] E} (hps : C.Preserves T ∨ C.Swaps T) {w : E}
    (hw : w ∈ C.W₁) (hw0 : w ≠ 0) (hT : T w = w) : C.Preserves T := by
  rcases hps with h | h
  · exact h
  · exfalso
    obtain ⟨h1, -⟩ := (C.swaps_iff_forall_mem T).mp h
    have h2 := h1 w hw
    rw [hT] at h2
    apply hw0
    apply C.Ψ.injective
    rw [map_zero]
    exact Prod.ext (C.mem_W₂.mp h2) (C.mem_W₁.mp hw)

end Coord

end CFSG.RankThree.GF2n.Smith81.LinFour

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement
open Module

theorem lin_count_of_card_Kx {G : Type} [Group G] [Finite G]
    {M Q Z B Y : Subgroup G} {y : G} {n m : ℕ} {V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : n = 2 * m) (hm : 2 ≤ m)
    (hV₁ : ∀ v ∈ V₁, v * v = 1) (hV₂ : ∀ v ∈ V₂, v * v = 1) (hs : Sit M Q Z Y y)
    (hy : y ∈ Lgen M (LB M Q B)) (hQ : Q ⊓ QB Y = ⊥)
    (hKY : Nat.card ↥(Kx Q Y) = Nat.card Z ^ (n + 1)) :
    Nat.card ↥(Lx M Y) ≤ Nat.card Z ^ (m * m) := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hq : 2 ≤ Nat.card Z := by
    have := H.q4
    omega
  have hHD := lin115RankStatement_holds G M Q Z B Y y n V₁ V₂ hc hS (by omega) hs hy hQ
  have hnm : n / 2 = m := by omega
  rw [hnm] at hHD
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hV₁card, hV₂card, hyN₁, hyN₂⟩ : Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧
      V₂ ≤ Q ∧ Nat.card V₁ = Nat.card Z ^ (n + 1) ∧ Nat.card V₂ = Nat.card Z ^ (n + 1) ∧
      y ∈ Subgroup.normalizer (V₁ : Set G) ∧ y ∈ Subgroup.normalizer (V₂ : Set G) := by
    obtain ⟨F', hF'field, hF'fin, hF'card, φ', -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, -, -, hs₁, hs₂, -,
      -⟩ := id hS
    refine ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, ?_, ?_, hs₁.1 hy, hs₂.1 hy⟩
    · obtain ⟨-, hN₁, ψ₁, -⟩ := hs₁
      exact card_eq_pow_of_sectionIso hZV₁ hF'card ψ₁
    · obtain ⟨-, hN₂, ψ₂, -⟩ := hs₂
      exact card_eq_pow_of_sectionIso hZV₂ hF'card ψ₂
  obtain ⟨K, _, _, _, γ, M₀, φ, F, _, _, _, ρ', C, hKcard, hK2lt, hφπ, hφker, hφiso, hrange,
    hV₁img, hV₂img, hps⟩ := exists_linCoord hc hS (by omega : 3 ≤ n)
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hyH : y ∈ H0 M Z := hSH hy
  have hyM : y ∈ M := hs.memM
  have hy2 : y * y = 1 := hs.x_sq
  obtain ⟨W₁, W₂, hW₁C, hW₂C, hcompl⟩ := LinFour.exists_summands C
  have hW₁ : ∀ e, e ∈ W₁ ↔ e ∈ M₀.img V₁ := fun e =>
    (hW₁C e).trans (C.mem_W₁.trans (hV₁img e).symm)
  have hW₂ : ∀ e, e ∈ W₂ ↔ e ∈ M₀.img V₂ := fun e =>
    (hW₂C e).trans (C.mem_W₂.trans (hV₂img e).symm)
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hKge : 2 ≤ Nat.card K := hK2lt.le
  have hZpos : 0 < Nat.card Z := by omega
  have hW₁sq : ∀ w ∈ W₁, M₀.Qf w = 0 := by
    intro w hw
    obtain ⟨v, hvV, hvQ, rfl⟩ := (hW₁ w).mp hw
    exact LinFour.Qf_pi_eq_zero_of_sq M₀ hvQ (by rw [pow_two]; exact hV₁ v hvV)
  have hW₂sq : ∀ w ∈ W₂, M₀.Qf w = 0 := by
    intro w hw
    obtain ⟨v, hvV, hvQ, rfl⟩ := (hW₂ w).mp hw
    exact LinFour.Qf_pi_eq_zero_of_sq M₀ hvQ (by rw [pow_two]; exact hV₂ v hvV)
  have hW₁iso : ∀ u ∈ W₁, ∀ v ∈ W₁, M₀.B u v = 0 := fun u hu v hv =>
    LinFour.B_eq_zero_of_Qf_eq_zero M₀ (P := fun e => e ∈ W₁)
      (fun a b ha hb => W₁.add_mem ha hb) hW₁sq hu hv
  have hW₂iso : ∀ u ∈ W₂, ∀ v ∈ W₂, M₀.B u v = 0 := fun u hu v hv =>
    LinFour.B_eq_zero_of_Qf_eq_zero M₀ (P := fun e => e ∈ W₂)
      (fun a b ha hb => W₂.add_mem ha hb) hW₂sq hu hv
  obtain ⟨T, hTdef⟩ : ∃ T : M₀.E ≃ₗ[K] M₀.E, T = φ ⟨y, hyH⟩ := ⟨_, rfl⟩
  have hπT : ∀ z ∈ Q, M₀.π (y * z * y⁻¹) = T (M₀.π z) := fun z hz => by
    rw [hTdef]
    exact hφπ ⟨y, hyH⟩ z hz
  have hQT : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => by
    rw [hTdef]
    exact hφiso _ e
  have hBT : ∀ e f, M₀.B (T e) (T f) = M₀.B e f := LinFour.B_eq_of_Qf_eq M₀ T hQT
  let A : XAct M₀ y := ⟨T, hπT, hQT, hBT⟩
  set N : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - LinearMap.id with hNdef
  have hNapp : ∀ f, N f = T f - f := fun f => rfl
  have hTW₁ : ∀ w ∈ W₁, T w ∈ W₁ := by
    intro w hw
    have h := C.ρ_mem_W₁ ⟨y, hy⟩ ((hW₁C w).mp hw)
    rw [hW₁C, hTdef]
    exact h
  have hTW₂ : ∀ w ∈ W₂, T w ∈ W₂ := by
    intro w hw
    have h := C.ρ_mem_W₂ ⟨y, hy⟩ ((hW₂C w).mp hw)
    rw [hW₂C, hTdef]
    exact h
  have hN₁' : ∀ w ∈ W₁, N w ∈ W₁ := fun w hw => by
    rw [hNapp]
    exact W₁.sub_mem (hTW₁ w hw) hw
  have hN₂' : ∀ w ∈ W₂, N w ∈ W₂ := fun w hw => by
    rw [hNapp]
    exact W₂.sub_mem (hTW₂ w hw) hw
  have hfinW : ∀ (V : Subgroup G) (W : Submodule K M₀.E), Z ≤ V → V ≤ Q →
      Nat.card V = Nat.card Z ^ (n + 1) → (∀ e, e ∈ W ↔ e ∈ M₀.img V) →
      finrank K ↥W = n := by
    intro V W hZV hVQ hVcard hW
    have h1 := M₀.card_eq hVQ hZV
    have h2 : Nat.card ↥(M₀.img V) = Nat.card ↥W :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => (hW e).symm)
    rw [hVcard, h2, pow_succ'] at h1
    have h3 : Nat.card ↥W = Nat.card Z ^ n := (Nat.eq_of_mul_eq_mul_left hZpos h1).symm
    have h4 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W)
    rw [h3, ← hKcard] at h4
    exact (Nat.pow_right_injective hKge h4).symm
  have hfinW₁ : finrank K ↥W₁ = n := hfinW V₁ W₁ hZV₁ hV₁Q hV₁card hW₁
  have hfinW₂ : finrank K ↥W₂ = n := hfinW V₂ W₂ hZV₂ hV₂Q hV₂card hW₂
  have hE : finrank K M₀.E = 2 * n := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  have hfr : ∀ (V : Subgroup G) (W : Submodule K M₀.E), Z ≤ V → V ≤ Q →
      y ∈ Subgroup.normalizer (V : Set G) → (∀ e, e ∈ W ↔ e ∈ M₀.img V) →
      HasDimOn V Z m y → finrank K ↥(W.map N) = m := by
    intro V W hZV hVQ hxV hW hdim
    have h := card_commSup_section A H hyM hy2 hZV hVQ hxV W hW
    unfold HasDimOn at hdim
    rw [hdim] at h
    have h2 : Nat.card ↥(W.map N) = Nat.card Z ^ m := by
      apply Nat.eq_of_mul_eq_mul_left hZpos
      rw [← h, pow_succ']
    rw [Module.natCard_eq_pow_finrank (K := K), hKcard] at h2
    exact Nat.pow_right_injective hq h2
  have hfr₁ := hfr V₁ W₁ hZV₁ hV₁Q hyN₁ hW₁ hHD.1
  have hfr₂ := hfr V₂ W₂ hZV₂ hV₂Q hyN₂ hW₂ hHD.2
  have hkerdim : finrank K ↥(LinearMap.ker N) = n := by
    have := LinGamma.finrank_ker_of_isCompl N W₁ W₂ hcompl hN₁' hN₂' hfr₁ hfr₂
    omega
  have hC₁dim : finrank K ↥(W₁ ⊓ LinearMap.ker N) = m := by
    have h := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker N W₁
    omega
  have hKZ : Z ≤ Kx Q Y := le_inf hZQ (Z_le_normalizer_X h12)
  have hKxQ : Kx Q Y ≤ Q := inf_le_left
  have himgcard : Nat.card ↥(M₀.img (Kx Q Y)) = Nat.card Z ^ n := by
    have h1 := M₀.card_eq hKxQ hKZ
    rw [hKY, pow_succ'] at h1
    exact (Nat.eq_of_mul_eq_mul_left hZpos h1).symm
  have hKtcard : Nat.card ↥(LinearMap.ker N) = Nat.card Z ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.ker N)), hkerdim, hKcard]
  have hKT : ∀ c ∈ Kx Q Y, T (M₀.π c) = M₀.π c := by
    intro c hc
    have hc' : c ∈ Q ⊓ Subgroup.centralizer ({y} : Set G) := by
      rw [← Kx_eq hs h12]
      exact hc
    have hcomm : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hc'.2
    rw [← hπT c hc'.1]
    congr 1
    rw [← hcomm]
    group
  have hle : M₀.img (Kx Q Y) ≤ (LinearMap.ker N).toAddSubgroup := by
    rintro _ ⟨c, hcK, hcQ, rfl⟩
    show N (M₀.π c) = 0
    rw [hNapp, hKT c hcK, sub_self]
  have hKtimg : ∀ e, e ∈ LinearMap.ker N ↔ e ∈ M₀.img (Kx Q Y) := by
    have heq : M₀.img (Kx Q Y) = (LinearMap.ker N).toAddSubgroup :=
      AddSubgroup.eq_of_le_of_card_ge hle (by
        show Nat.card ↥(LinearMap.ker N) ≤ _
        rw [hKtcard, himgcard])
    intro e
    rw [heq]
    exact Iff.rfl
  have hKtQf : ∀ e ∈ M₀.img (Kx Q Y), M₀.Qf e = 0 := by
    rintro _ ⟨c, hcK, hcQ, rfl⟩
    exact LinFour.Qf_pi_eq_zero_of_sq M₀ hcQ (Kx_sq_eq_one hs hQ hcK)
  have hKtiso : ∀ u ∈ LinearMap.ker N, ∀ v ∈ LinearMap.ker N, M₀.B u v = 0 := fun u hu v hv =>
    LinFour.B_eq_zero_of_Qf_eq_zero M₀ (P := fun e => e ∈ M₀.img (Kx Q Y))
      (fun a b ha hb => (M₀.img (Kx Q Y)).add_mem ha hb) hKtQf ((hKtimg u).mp hu)
      ((hKtimg v).mp hv)
  have hLH : ∀ a : ↥(Lx M Y), (a : G) ∈ H0 M Z := fun a => Lx_le_H0 hs h12 a.2
  let ψ : ↥(Lx M Y) → (M₀.E ≃ₗ[K] M₀.E) := fun a => φ ⟨(a : G), hLH a⟩
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : φ ((⟨(a : G), hLH a⟩ : ↥(H0 M Z))⁻¹ * ⟨(b : G), hLH b⟩) = 1 := by
      rw [map_mul, map_inv]
      have hab' : φ ⟨(a : G), hLH a⟩ = φ ⟨(b : G), hLH b⟩ := hab
      rw [hab']
      exact inv_mul_cancel _
    have h2 : (a : G)⁻¹ * (b : G) ∈ Q := (hφker _).mp h1
    have h3 : (a : G)⁻¹ * (b : G) ∈ QB Y := ((Lx M Y).mul_mem ((Lx M Y).inv_mem a.2) b.2).1
    have h4 : (a : G)⁻¹ * (b : G) = 1 := by
      have h5 : (a : G)⁻¹ * (b : G) ∈ Q ⊓ QB Y := ⟨h2, h3⟩
      rw [hQ, Subgroup.mem_bot] at h5
      exact h5
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hψB : ∀ a e f, M₀.B (ψ a e) (ψ a f) = M₀.B e f := fun a =>
    LinFour.B_eq_of_Qf_eq M₀ (ψ a) (fun e => hφiso _ e)
  have hψψ : ∀ a e, ψ a (ψ a e) = e := by
    intro a e
    have hsq : (⟨(a : G), hLH a⟩ : ↥(H0 M Z)) * ⟨(a : G), hLH a⟩ = 1 :=
      Subtype.ext (by
        show (a : G) * (a : G) = 1
        rw [← pow_two]
        exact Lx_sq_eq_one hs hQ a.2)
    have h1 : φ ((⟨(a : G), hLH a⟩ : ↥(H0 M Z)) * ⟨(a : G), hLH a⟩) = 1 := by
      rw [hsq, map_one]
    have := LinearEquiv.congr_fun h1 e
    rwa [map_mul, LinearEquiv.mul_apply] at this
  have hψfix : ∀ a, ∀ k ∈ LinearMap.ker N, ψ a k = k := by
    intro a k hk
    obtain ⟨c, hcK, hcQ, rfl⟩ := (hKtimg k).mp hk
    have hcomm : c * (a : G) = (a : G) * c := (smith_1_15_elem hs hQ).2.1 c hcK a a.2
    show φ ⟨(a : G), hLH a⟩ (M₀.π c) = M₀.π c
    rw [← hφπ ⟨(a : G), hLH a⟩ c hcQ]
    congr 1
    show (a : G) * c * (a : G)⁻¹ = c
    rw [← hcomm]
    group
  obtain ⟨w₀, hw₀mem, hw₀ne⟩ : ∃ w ∈ W₁ ⊓ LinearMap.ker N, w ≠ 0 := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W₁ ⊓ LinearMap.ker N)
      (by
        intro hbot
        rw [hbot, finrank_bot] at hC₁dim
        omega)
    exact ⟨b, hb, hb0⟩
  have hψP : ∀ a, C.Preserves (ψ a) := fun a =>
    LinFour.preserves_of_fixed C (T := ψ a) (hps ⟨(a : G), hLH a⟩)
      ((hW₁C w₀).mp hw₀mem.1) hw₀ne (hψfix a w₀ hw₀mem.2)
  have hψW : ∀ a, (∀ w ∈ W₁, ψ a w ∈ W₁) ∧ ∀ w ∈ W₂, ψ a w ∈ W₂ := fun a => by
    obtain ⟨h1, h2⟩ := (C.preserves_iff_forall_mem _).mp (hψP a)
    exact ⟨fun w hw => (hW₁C _).mpr (h1 w ((hW₁C w).mp hw)),
      fun w hw => (hW₂C _).mpr (h2 w ((hW₂C w).mp hw))⟩
  have hbound := LinFour.card_le_pow_of_lagrangian_fixed (ι := ↥(Lx M Y)) M₀.B hK2 M₀.alt
    M₀.nondeg W₁ W₂ (LinearMap.ker N) hcompl hW₁iso hW₂iso hKtiso (by rw [hkerdim, hE]) ψ hψinj
    (fun a => ⟨hψB a, hψψ a, (hψW a).1, (hψW a).2, hψfix a⟩)
  have hexp : (finrank K ↥W₁ - finrank K ↥(LinearMap.ker N ⊓ W₁)) *
      finrank K ↥(LinearMap.ker N ⊓ W₁) = m * m := by
    have h1 : finrank K ↥W₁ - finrank K ↥(LinearMap.ker N ⊓ W₁) = m := by
      rw [inf_comm, hfinW₁, hC₁dim]
      omega
    rw [h1, inf_comm, hC₁dim]
  rw [hexp, hKcard] at hbound
  exact hbound

theorem linFourCountStatement_of (hΓ : LinGammaEvenStatement) :
    LinFourCountStatement := fun G _ _ M Q Z B Y y V₁ V₂ hc hS hV₁ hV₂ hs hy hQ =>
  lin_count_of_card_Kx (n := 4) (m := 2) hc hS rfl le_rfl hV₁ hV₂ hs hy hQ
    (hΓ G M Q Z B Y y 4 2 V₁ V₂ hc hS rfl le_rfl hV₁ hV₂ hs hy hQ).1

end CFSG.RankThree.GF2n.Smith81
