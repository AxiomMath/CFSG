module

public import CFSG.RankThree.GF2n.Smith81.Sec115
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig

public section

namespace CFSG.RankThree.GF2n.Smith81.Sec115Dim

open Module

section Lin

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem B_symm (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0) (halt : ∀ e, B e e = 0)
    (a b : E) : B a b = B b a := by
  have h := halt (a + b)
  simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
  linear_combination h - B b a * hK2

theorem nondeg_of (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0) (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) : B.Nondegenerate :=
  ⟨hnd, fun e he => hnd e fun f => by rw [B_symm B hK2 halt]; exact he f⟩

theorem two_mul_finrank_le_of_iso (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (W : Submodule K E)
    (hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0) : 2 * finrank K W ≤ finrank K E := by
  have hle : W ≤ B.orthogonal W := fun v hv =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => hW u hu v hv
  have h1 := LinearMap.BilinForm.finrank_orthogonal (nondeg_of B hK2 halt hnd) W
  have h2 := Submodule.finrank_mono hle
  have h3 := Submodule.finrank_le W
  omega

theorem lin_main (B : LinearMap.BilinForm K E) (Qf : E → K) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (T : E ≃ₗ[K] E) (hTT : ∀ e, T (T e) = e) (hTB : ∀ e f, B (T e) (T f) = B e f)
    (hTQ : ∀ e, Qf (T e) = Qf e) (n : ℕ) (hE : finrank K E = 2 * n) (W : Submodule K E)
    (hWC : W ≤ LinearMap.ker ((T : E →ₗ[K] E) - LinearMap.id)) (hWQ : ∀ w ∈ W, Qf w = 0)
    (hcount : finrank K (LinearMap.ker ((T : E →ₗ[K] E) - LinearMap.id)) ≤ finrank K W + 1) :
    finrank K (LinearMap.range ((T : E →ₗ[K] E) - LinearMap.id)) = n ∨
      (Odd n ∧ finrank K (LinearMap.range ((T : E →ₗ[K] E) - LinearMap.id)) = n - 1) := by
  set N : E →ₗ[K] E := (T : E →ₗ[K] E) - LinearMap.id with hNdef
  have h2 : ∀ e : E, e + e = 0 := fun e => by rw [← two_smul K e, hK2, zero_smul]
  have hneg : ∀ e : E, -e = e := fun e => neg_eq_of_add_eq_zero_right (h2 e)
  have hN : ∀ f, N f = T f + f := fun f => by
    simp [hNdef, sub_eq_add_neg, hneg]
  have hNN : ∀ u, N (N u) = 0 := fun u => by
    rw [hN, hN, map_add, hTT, show u + T u + (T u + u) = (u + u) + (T u + T u) by abel, h2, h2,
      add_zero]
  have hadj : ∀ a f, B a (N f) = B (N a) f := fun a f => by
    have : B a (T f) = B (T a) f := by rw [← hTB a (T f), hTT]
    simp only [hN, map_add, LinearMap.add_apply, this]
  have hsymm := B_symm B hK2 halt
  have hRiso : ∀ u ∈ LinearMap.range N, ∀ v ∈ LinearMap.range N, B u v = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [hadj, hNN, map_zero, LinearMap.zero_apply]
  have hd := two_mul_finrank_le_of_iso B hK2 halt hnd _ hRiso
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  have hWiso : ∀ u ∈ W, ∀ v ∈ W, B u v = 0 := fun u hu v hv => by
    have := hQadd u v
    rw [hWQ u hu, hWQ v hv, hWQ _ (W.add_mem hu hv)] at this
    linear_combination -this
  have hdW := two_mul_finrank_le_of_iso B hK2 halt hnd W hWiso
  rw [hE] at hd hdW hrn
  by_cases hdn : finrank K (LinearMap.range N) = n
  · exact Or.inl hdn
  right
  have hd1 : finrank K (LinearMap.range N) = n - 1 := by omega
  have hW_n : finrank K W = n := by omega
  have hWperp : B.orthogonal W = W := by
    have hle : W ≤ B.orthogonal W := fun v hv =>
      (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => hWiso u hu v hv
    have h1 := LinearMap.BilinForm.finrank_orthogonal (nondeg_of B hK2 halt hnd) W
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hRW : LinearMap.range N ≤ W := by
    rw [← hWperp]
    rintro _ ⟨e, rfl⟩
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => ?_
    rw [hadj, LinearMap.mem_ker.mp (hWC hw), map_zero, LinearMap.zero_apply]
  have hBNe : ∀ e, B (N e) e = 0 := fun e => by
    have h := hTQ e
    have hTe : T e = N e + e := by rw [hN, add_assoc, h2, add_zero]
    rw [hTe, hQadd, hWQ _ (hRW ⟨e, rfl⟩), zero_add] at h
    linear_combination h
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective N.rangeRestrict
    (LinearMap.range_rangeRestrict N)
  have hNg : ∀ r : LinearMap.range N, N (g r) = r := fun r =>
    congrArg Subtype.val (LinearMap.congr_fun hg r)
  let β : LinearMap.BilinForm K (LinearMap.range N) := B.compl₁₂ g (LinearMap.range N).subtype
  have hβ : ∀ r s, β r s = B (g r) s := fun r s => rfl
  have halt' : β.IsAlt := fun r => by
    rw [hβ, ← hNg r, hadj, hBNe]
  have hleft : β.SeparatingLeft := fun r hr => by
    have hall : ∀ f, B r f = 0 := fun f => by
      have h : B (g r) (N f) = 0 := hr ⟨N f, LinearMap.mem_range_self N f⟩
      rwa [hadj, hNg] at h
    exact Subtype.ext (hnd _ hall)
  have hndβ : β.Nondegenerate :=
    ⟨hleft, fun s hs => hleft s fun r => halt'.eq_iff.mp (hs r)⟩
  obtain ⟨k, hk⟩ := Stroth80.even_finrank_of_alt_nondegenerate β halt' hndβ
  exact ⟨⟨k, by omega⟩, hd1⟩

end Lin

end CFSG.RankThree.GF2n.Smith81.Sec115Dim

namespace CFSG.RankThree.GF2n.Smith81

open Module

section Grp

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

theorem smith115DimStatement_holds : Smith115DimStatement := by
  intro G _ _ M Q Z X x hs n hw hQ
  have H := hs.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  obtain ⟨K, _, _, γ, M₀, hD, hcard, hK2, ⟨A⟩⟩ := exists_model H hxM hxZ
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
  have hinj := Nat.pow_right_injective hq
  have hdim : ∀ k, HasDim Q Z k x ↔ finrank K (commSpace A) = k := by
    intro k
    unfold HasDim
    rw [card_comm_sup hcard A H hxM hx2]
    exact ⟨fun h => by have := hinj h; omega, fun h => by rw [h]⟩
  have hpow : ∀ R : Submodule K M₀.E,
      Nat.card (preimageSub M₀ R) = Nat.card Z ^ (finrank K R + 1) := by
    intro R
    rw [card_preimageSub hZQ, Module.natCard_eq_pow_finrank (K := K), hcard, pow_succ]
  have hE : finrank K M₀.E = 2 * n := by
    have h1 := hpow ⊤
    have h2 : preimageSub M₀ ⊤ = Q := by ext y; simp [mem_preimageSub]
    rw [h2, hw, finrank_top] at h1
    have := hinj h1
    omega
  set N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id with hNdef
  have hNapp : ∀ f, N f = A.T f - f := fun f => rfl
  have hcs : commSpace A = LinearMap.range N := by
    ext e
    constructor
    · intro he
      obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
      obtain ⟨q, hq, z₀, hz₀, rfl⟩ := exists_comm_rep A H hxM hyQ he
      rw [M₀.π_mul _ (comm_mem_Q H hxM hq) _ (hZQ hz₀), (M₀.π_ker _ (hZQ hz₀)).mpr hz₀,
        add_zero, A.pi_comm H hxM hq]
      exact ⟨-(M₀.π q), by rw [hNapp, map_neg]; abel⟩
    · rintro ⟨f, rfl⟩
      obtain ⟨q, hq, hπq⟩ := M₀.π_surj (-f)
      have h := ((mem_commSup_iff A H hxM hx2 hZQ).mp (Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)))).2
      rw [A.pi_comm H hxM hq, hπq] at h
      have e : N f = -f - A.T (-f) := by rw [hNapp, map_neg]; abel
      rw [e]
      exact h
  rw [hcs] at hdim
  have hTT := A.T_T H hxM hx2
  let Cx : Subgroup G := Q ⊓ Subgroup.centralizer ({x} : Set G)
  have hCxQf : ∀ c ∈ Cx, M₀.Qf (M₀.π c) = 0 := fun c hc =>
    (GM.sq_eq_one_iff hD hc.1).mp (Kx_sq_eq_one hs hQ (by rw [Kx_eq hs h12]; exact hc))
  have hCxT : ∀ c ∈ Cx, A.T (M₀.π c) = M₀.π c := fun c hc => by
    have hcomm : c * x = x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    rw [← A.hπ c (Subgroup.mem_inf.mp hc).1]
    congr 1
    rw [← hcomm]; group
  let W : Submodule K M₀.E := Submodule.span K (M₀.π '' (Cx : Set G))
  have hWC : W ≤ LinearMap.ker N := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    show N (M₀.π c) = 0
    rw [hNapp, hCxT c hc, sub_self]
  have hSiso : ∀ c ∈ Cx, ∀ c' ∈ Cx, M₀.B (M₀.π c) (M₀.π c') = 0 := fun c hc c' hc' => by
    have h := M₀.Qf_add (M₀.π c) (M₀.π c')
    rw [← M₀.π_mul c hc.1 c' hc'.1, hCxQf _ (Cx.mul_mem hc hc'), hCxQf c hc, hCxQf c' hc'] at h
    linear_combination -h
  have hWiso : ∀ u ∈ W, ∀ v ∈ W, M₀.B u v = 0 := by
    have h1 : ∀ c ∈ Cx, ∀ v ∈ W, M₀.B (M₀.π c) v = 0 := by
      intro c hc v hv
      have : W ≤ LinearMap.ker (M₀.B (M₀.π c)) := by
        rw [Submodule.span_le]
        rintro _ ⟨c', hc', rfl⟩
        exact hSiso c hc c' hc'
      exact this hv
    intro u hu v hv
    have : W ≤ LinearMap.ker (M₀.B.flip v) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      exact h1 c hc v hv
    exact this hu
  have hWQ : ∀ w ∈ W, M₀.Qf w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem a ha => obtain ⟨c, hc, rfl⟩ := ha; exact hCxQf c hc
    | zero => simpa using M₀.Qf_smul 0 0
    | add a b ha hb iha ihb => rw [M₀.Qf_add, iha, ihb, hWiso a ha b hb]; ring
    | smul r a ha iha => rw [M₀.Qf_smul, iha, mul_zero]
  have hCxW : Cx ≤ preimageSub M₀ W := fun c hc =>
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
  let φ : P →* Z :=
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
  have hkerC : ∀ k : P, k ∈ φ.ker → (k : G) ∈ Cx := by
    intro k hk
    have h' : x * (k : G) * x⁻¹ * (k : G)⁻¹ = 1 := congrArg Subtype.val hk
    have h2 : x * (k : G) = k * x := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h')
    exact ⟨(mem_preimageSub.mp k.2).1, Subgroup.mem_centralizer_singleton_iff.mpr h2.symm⟩
  have hker : Nat.card φ.ker ≤ Nat.card Cx :=
    Nat.card_le_card_of_injective (fun k : φ.ker => (⟨k.1.1, hkerC k.1 k.2⟩ : Cx))
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  have hP : Nat.card P ≤ Nat.card Z * Nat.card Cx := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, mul_comm]
    exact Nat.mul_le_mul (Subgroup.card_le_card_group _) hker
  have hcount : finrank K (LinearMap.ker N) ≤ finrank K W + 1 := by
    have h1 := hpow (LinearMap.ker N)
    have h2 := hpow W
    have h3 : Nat.card Z ^ (finrank K (LinearMap.ker N) + 1) ≤
        Nat.card Z ^ (finrank K W + 1 + 1) := by
      rw [← h1, pow_succ, ← h2, mul_comm]
      exact hP.trans (Nat.mul_le_mul_left _ hc1)
    have := (Nat.pow_le_pow_iff_right (by omega)).mp h3
    omega
  rcases Sec115Dim.lin_main M₀.B M₀.Qf hK2 M₀.alt M₀.nondeg M₀.Qf_add A.T hTT A.hB A.hQ n hE
    W hWC hWQ hcount with h | ⟨hodd, h⟩
  · exact Or.inl ((hdim n).mpr h)
  · exact Or.inr ⟨hodd, (hdim (n - 1)).mpr h⟩

end Grp

theorem smith115Statement_holds : Smith115Statement :=
  smith115Statement_of_dim smith115DimStatement_holds

end CFSG.RankThree.GF2n.Smith81
