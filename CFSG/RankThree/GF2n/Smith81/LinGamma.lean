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

section Model

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizer_subspace {M Q Z X : Subgroup G} {x : G} {m : ℕ} {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (hQ : Q ⊓ QB X = ⊥)
    (A : XAct M₀ x) (hK2 : (2 : K) = 0) (hE : finrank K M₀.E = 4 * m + 2)
    (hkerdim : finrank K (LinearMap.ker ((A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id)) = 2 * m + 2) :
    ∃ Wc : Submodule K M₀.E,
      Wc ≤ LinearMap.ker ((A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id) ∧ (∀ w ∈ Wc, M₀.Qf w = 0) ∧
      finrank K Wc = 2 * m + 1 ∧
      Q ⊓ Subgroup.centralizer ({x} : Set G) = preimageSub M₀ Wc ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (2 * m + 2) ∧
      ∀ z ∈ Z, ∃ c ∈ Q, c * x * c⁻¹ = x * z := by
  have H := hs.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hq : 2 ≤ Nat.card Z := by
    have := H.q4
    omega
  have hcard : Nat.card K = Nat.card Z := hD.card
  set N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id with hNdef
  have hNapp : ∀ f, N f = A.T f - f := fun f => rfl
  have hpow : ∀ R : Submodule K M₀.E,
      Nat.card (preimageSub M₀ R) = Nat.card Z ^ (finrank K R + 1) := by
    intro R
    rw [card_preimageSub hZQ, Module.natCard_eq_pow_finrank (K := K), hcard, pow_succ]
  let Cx : Subgroup G := Q ⊓ Subgroup.centralizer ({x} : Set G)
  have hCxQf : ∀ c ∈ Cx, M₀.Qf (M₀.π c) = 0 := fun c hc =>
    (GM.sq_eq_one_iff hD hc.1).mp (Kx_sq_eq_one hs hQ (by rw [Kx_eq hs h12]; exact hc))
  have hCxT : ∀ c ∈ Cx, A.T (M₀.π c) = M₀.π c := fun c hc => by
    have hcomm : c * x = x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    rw [← A.hπ c (Subgroup.mem_inf.mp hc).1]
    congr 1
    rw [← hcomm]
    group
  let Wc : Submodule K M₀.E := Submodule.span K (M₀.π '' (Cx : Set G))
  have hWC : Wc ≤ LinearMap.ker N := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    show N (M₀.π c) = 0
    rw [hNapp, hCxT c hc, sub_self]
  have hSiso : ∀ c ∈ Cx, ∀ c' ∈ Cx, M₀.B (M₀.π c) (M₀.π c') = 0 := fun c hc c' hc' => by
    have h := M₀.Qf_add (M₀.π c) (M₀.π c')
    rw [← M₀.π_mul c hc.1 c' hc'.1, hCxQf _ (Cx.mul_mem hc hc'), hCxQf c hc, hCxQf c' hc'] at h
    linear_combination -h
  have hWiso : ∀ u ∈ Wc, ∀ v ∈ Wc, M₀.B u v = 0 := by
    have h1 : ∀ c ∈ Cx, ∀ v ∈ Wc, M₀.B (M₀.π c) v = 0 := by
      intro c hc v hv
      have : Wc ≤ LinearMap.ker (M₀.B (M₀.π c)) := by
        rw [Submodule.span_le]
        rintro _ ⟨c', hc', rfl⟩
        exact hSiso c hc c' hc'
      exact this hv
    intro u hu v hv
    have : Wc ≤ LinearMap.ker (M₀.B.flip v) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      exact h1 c hc v hv
    exact this hu
  have hWQ : ∀ w ∈ Wc, M₀.Qf w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem a ha => obtain ⟨c, hc, rfl⟩ := ha; exact hCxQf c hc
    | zero => simpa using M₀.Qf_smul 0 0
    | add a b ha hb iha ihb => rw [M₀.Qf_add, iha, ihb, hWiso a ha b hb]; ring
    | smul r a ha iha => rw [M₀.Qf_smul, iha, mul_zero]
  have hCxW : Cx ≤ preimageSub M₀ Wc := fun c hc =>
    mem_preimageSub.mpr ⟨hc.1, Submodule.subset_span ⟨c, hc, rfl⟩⟩
  have hc1 := Subgroup.card_le_of_le hCxW
  let P := preimageSub M₀ (LinearMap.ker N)
  have hPZ : ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro y hy
    have hyQ := (mem_preimageSub.mp hy).1
    have hT : A.T (M₀.π y) = M₀.π y := by
      have := LinearMap.mem_ker.mp (mem_preimageSub.mp hy).2
      rw [hNapp, sub_eq_zero] at this
      exact this
    have hc := conj_mem_Q H hxM hyQ
    refine (M₀.π_ker _ (Q.mul_mem hc (Q.inv_mem hyQ))).mp ?_
    rw [M₀.π_mul _ hc _ (Q.inv_mem hyQ), Tim79.QuadModel.pi_inv M₀ hyQ, A.hπ y hyQ, hT,
      add_neg_cancel]
  let θ : P →* Z :=
    { toFun := fun y => ⟨x * y * x⁻¹ * (y : G)⁻¹, hPZ y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        show x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹ =
          (x * a * x⁻¹ * (a : G)⁻¹) * (x * b * x⁻¹ * (b : G)⁻¹)
        have hv : Commute (x * b * x⁻¹ * (b : G)⁻¹) (a : G)⁻¹ :=
          Commute.inv_right (Z_central H (hPZ b b.2) (mem_preimageSub.mp a.2).1)
        calc x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹
            = x * a * x⁻¹ * ((x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = x * a * x⁻¹ * ((a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹)) := by rw [hv.eq]
          _ = _ := by group }
  have hkerC : ∀ k : P, k ∈ θ.ker → (k : G) ∈ Cx := by
    intro k hk
    have h' : x * (k : G) * x⁻¹ * (k : G)⁻¹ = 1 := congrArg Subtype.val hk
    have h2 : x * (k : G) = k * x := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h')
    exact ⟨(mem_preimageSub.mp k.2).1, Subgroup.mem_centralizer_singleton_iff.mpr h2.symm⟩
  have hker : Nat.card θ.ker ≤ Nat.card Cx :=
    Nat.card_le_card_of_injective (fun k : θ.ker => (⟨k.1.1, hkerC k.1 k.2⟩ : Cx))
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  have hP : Nat.card P ≤ Nat.card Z * Nat.card Cx := by
    rw [← Subgroup.card_mul_index θ.ker, Subgroup.index_ker, mul_comm]
    exact Nat.mul_le_mul (Subgroup.card_le_card_group _) hker
  have hcount : finrank K (LinearMap.ker N) ≤ finrank K Wc + 1 := by
    have h1 := hpow (LinearMap.ker N)
    have h2 := hpow Wc
    have h3 : Nat.card Z ^ (finrank K (LinearMap.ker N) + 1) ≤
        Nat.card Z ^ (finrank K Wc + 1 + 1) := by
      rw [← h1, pow_succ, ← h2, mul_comm]
      exact hP.trans (Nat.mul_le_mul_left _ hc1)
    have := (Nat.pow_le_pow_iff_right (by omega)).mp h3
    omega
  have hWcd : finrank K Wc = 2 * m + 1 := by
    have h1 := LinGamma.two_mul_finrank_le_of_iso M₀.B hK2 M₀.alt M₀.nondeg Wc hWiso
    omega
  have hPcard : Nat.card P = Nat.card Z ^ (2 * m + 3) := by
    have h := hpow (LinearMap.ker N)
    rw [hkerdim] at h
    exact h
  have hpreWc : Nat.card (preimageSub M₀ Wc) = Nat.card Z ^ (2 * m + 2) := by
    rw [hpow Wc, hWcd]
  have hCxcard_ge : Nat.card Z ^ (2 * m + 2) ≤ Nat.card Cx := by
    have h := hP
    rw [hPcard] at h
    have h' : Nat.card Z * Nat.card Z ^ (2 * m + 2) ≤ Nat.card Z * Nat.card Cx := by
      rw [← pow_succ']
      exact h
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  have hCxeq : Cx = preimageSub M₀ Wc :=
    Subgroup.eq_of_le_of_card_ge hCxW (by rw [hpreWc]; exact hCxcard_ge)
  have hθtop : θ.range = ⊤ := by
    have hmul : Nat.card θ.ker * Nat.card θ.range = Nat.card P := by
      rw [← Subgroup.index_ker θ]
      exact Subgroup.card_mul_index θ.ker
    have hkerle : Nat.card θ.ker ≤ Nat.card Z ^ (2 * m + 2) :=
      hker.trans (by rw [hCxeq, hpreWc])
    have hge : Nat.card Z ≤ Nat.card θ.range := by
      have h1 : Nat.card Z ^ (2 * m + 2) * Nat.card Z ≤
          Nat.card Z ^ (2 * m + 2) * Nat.card θ.range := by
        calc Nat.card Z ^ (2 * m + 2) * Nat.card Z = Nat.card P := by rw [hPcard]; ring
          _ = Nat.card θ.ker * Nat.card θ.range := hmul.symm
          _ ≤ Nat.card Z ^ (2 * m + 2) * Nat.card θ.range := Nat.mul_le_mul_right _ hkerle
      exact Nat.le_of_mul_le_mul_left h1 (pow_pos (by omega) _)
    exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) hge)
  refine ⟨Wc, hWC, hWQ, hWcd, hCxeq, by show Nat.card Cx = _; rw [hCxeq, hpreWc], ?_⟩
  intro z hz
  have hz' : z⁻¹ ∈ Z := Z.inv_mem hz
  obtain ⟨y, hy⟩ : ∃ y : P, θ y = ⟨z⁻¹, hz'⟩ := by
    have hmem : (⟨z⁻¹, hz'⟩ : Z) ∈ θ.range := by
      rw [hθtop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy⟩
  have hyQ : (y : G) ∈ Q := (mem_preimageSub.mp y.2).1
  refine ⟨y, hyQ, ?_⟩
  have h1 : x * (y : G) * x⁻¹ * (y : G)⁻¹ = z⁻¹ := congrArg Subtype.val hy
  have h2 : (y : G) * x * (y : G)⁻¹ * x⁻¹ = z := by
    have e : (y : G) * x * (y : G)⁻¹ * x⁻¹ = (x * (y : G) * x⁻¹ * (y : G)⁻¹)⁻¹ := by group
    rw [e, h1, inv_inv]
  have h3 : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hxZ z hz)
  calc (y : G) * x * (y : G)⁻¹ = ((y : G) * x * (y : G)⁻¹ * x⁻¹) * x := by group
    _ = z * x := by rw [h2]
    _ = x * z := h3.symm

theorem linGamma_of_model {M Q Z B X : Subgroup G} {x : G} {n m : ℕ} {V₁ V₂ : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : n = 2 * m + 1) (hm : 1 ≤ m) (hV₁ : ∀ v ∈ V₁, v * v = 1) (hV₂ : ∀ v ∈ V₂, v * v = 1)
    (hs : Sit M Q Z X x) (hx : x ∈ Lgen M (LB M Q B)) (hQ : Q ⊓ QB X = ⊥) :
    Nat.card ↥(Kx Q X) = Nat.card Z ^ (n + 1) ∧
      (∀ z ∈ Z, ∃ c ∈ Q, c * x * c⁻¹ = x * z) ∧
      ∃ V ∈ ({V₁, V₂} : Set (Subgroup G)),
        Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 2) ∧
        ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧
        Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
  have H := hc.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have h12 := smith_1_12 hs
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hq : 2 ≤ Nat.card Z := by
    have := H.q4
    omega
  have hcard : Nat.card K = Nat.card Z := hD.card
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hn3 : 3 ≤ n := by omega
  have hn1 : n + 1 = 2 * m + 2 := by omega
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
  have hV₁card : Nat.card V₁ = Nat.card Z ^ (2 * m + 2) := by
    obtain ⟨-, hN₁, ψ₁, -⟩ := hs₁
    rw [card_eq_pow_of_sectionIso hZV₁ hFcard ψ₁, hn1]
  have hV₂card : Nat.card V₂ = Nat.card Z ^ (2 * m + 2) := by
    obtain ⟨-, hN₂, ψ₂, -⟩ := hs₂
    rw [card_eq_pow_of_sectionIso hZV₂ hFcard ψ₂, hn1]
  obtain ⟨T, hπT, hQT, hBT⟩ : ∃ T : M₀.E ≃ₗ[K] M₀.E, (∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)) ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧ ∀ e f, M₀.B (T e) (T f) = M₀.B e f := by
    refine ⟨φ ⟨x, hxH⟩, fun y hy => hφπ ⟨x, hxH⟩ y hy, hφiso ⟨x, hxH⟩, fun e f => ?_⟩
    have h1 := M₀.Qf_add (φ ⟨x, hxH⟩ e) (φ ⟨x, hxH⟩ f)
    have h2 := M₀.Qf_add e f
    rw [← map_add, hφiso _ (e + f), hφiso _ e, hφiso _ f] at h1
    linear_combination h2 - h1
  let A : XAct M₀ x := ⟨T, hπT, hQT, hBT⟩
  have hTT : ∀ e, T (T e) = e := fun e => A.T_T H hxM hx2 e
  set N : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - LinearMap.id with hNdef
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
  have hE : finrank K M₀.E = 4 * m + 2 := by
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
  have hkerdim : finrank K (LinearMap.ker N) = 2 * m + 2 := by
    have := LinGamma.finrank_ker_of_isCompl N W₁ W₂ hcompl hN₁' hN₂' hfr₁ hfr₂
    omega
  obtain ⟨Wc, hWC, hWQ, hWcd, hCxeq, hCxcard, hconj⟩ :=
    exists_centralizer_subspace hD hs hQ A hK2 hE hkerdim
  refine ⟨?_, hconj, ?_⟩
  · rw [Kx_eq hs h12, hCxcard, hn1]
  · have hdich := LinGamma.lagrangian_split M₀.B M₀.Qf hK2 M₀.alt M₀.nondeg M₀.Qf_add T hTT hBT
      hE W₁ W₂ hcompl hW₁T hW₂T hW₁Q hW₂Q hfr₁ hfr₂ Wc hWC hWQ hWcd
    have hfinal : ∀ (V : Subgroup G) (Wk : Submodule K M₀.E), Z ≤ V → V ≤ Q →
        (∀ e, e ∈ Wk ↔ e ∈ M₀.img V) → finrank K ↥(Wc ⊓ Wk) = m + 1 →
        Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 2) := by
      intro V Wk hZV hVQ hWk hdimk
      have hVeq : V ⊓ Subgroup.centralizer ({x} : Set G) = V ⊓ preimageSub M₀ Wc := by
        rw [← hCxeq]
        ext v
        constructor
        · rintro ⟨hvV, hvC⟩
          exact ⟨hvV, hVQ hvV, hvC⟩
        · rintro ⟨hvV, hvQ, hvC⟩
          exact ⟨hvV, hvC⟩
      have hZS : Z ≤ V ⊓ preimageSub M₀ Wc := fun z hz =>
        ⟨hZV hz, mem_preimageSub.mpr ⟨hZQ hz, by
          rw [(M₀.π_ker z (hZQ hz)).mpr hz]
          exact Submodule.zero_mem _⟩⟩
      have hSQ : V ⊓ preimageSub M₀ Wc ≤ Q := fun v hv => hVQ hv.1
      rw [hVeq, M₀.card_eq hSQ hZS]
      have himg : Nat.card ↥(M₀.img (V ⊓ preimageSub M₀ Wc)) = Nat.card K ^ (m + 1) := by
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
    rcases hdich with h | h
    · refine ⟨V₁, Set.mem_insert _ _, hfinal V₁ W₁ hZV₁ hV₁Q hW₁ h, ?_⟩
      exact gamma_conclusions_of_card H hZV₁ hV₁Q hV₁ hxN₁ hx2 hV₁card
        (hfinal V₁ W₁ hZV₁ hV₁Q hW₁ h) hHD.1
    · refine ⟨V₂, Set.mem_insert_of_mem _ (Set.mem_singleton _), hfinal V₂ W₂ hZV₂ hV₂Q hW₂ h, ?_⟩
      exact gamma_conclusions_of_card H hZV₂ hV₂Q hV₂ hxN₂ hx2 hV₂card
        (hfinal V₂ W₂ hZV₂ hV₂Q hW₂ h) hHD.2

end Model

theorem linGammaStatement_holds : LinGammaStatement := by
  intro G _ _ M Q Z B X x n m V₁ V₂ hc hS hn hm hV₁ hV₂ hs hx hQ
  obtain ⟨m', γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  exact linGamma_of_model hD hc hS hn hm hV₁ hV₂ hs hx hQ

end CFSG.RankThree.GF2n.Smith81
