module

public import CFSG.RankThree.GF2n.Smith81.Sec1Main

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

section Lin

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem jx_bilin_symm (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0) (halt : ∀ e, B e e = 0)
    (a b : E) : B a b = B b a := by
  have h := halt (a + b)
  simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
  linear_combination h - B b a * hK2

theorem jx_orth_bound (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (N : E →ₗ[K] E) (hadj : ∀ a f, B a (N f) = B (N a) f) (W : Submodule K E)
    (hWN : W ≤ LinearMap.ker N)
    (hcount : Module.finrank K (LinearMap.ker N) ≤ Module.finrank K W + 1) :
    LinearMap.range N ≤ B.orthogonal W ∧
      Module.finrank K (B.orthogonal W) ≤ Module.finrank K (LinearMap.range N) + 1 := by
  have hnd' : B.Nondegenerate :=
    ⟨hnd, fun e he => hnd e fun f => by rw [jx_bilin_symm B hK2 halt]; exact he f⟩
  have hrange : LinearMap.range N ≤ B.orthogonal W := by
    rintro _ ⟨e, rfl⟩
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => ?_
    rw [hadj, LinearMap.mem_ker.mp (hWN hw), map_zero, LinearMap.zero_apply]
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd' W
  have h2 := LinearMap.finrank_range_add_finrank_ker N
  exact ⟨hrange, by omega⟩

end Lin

section Main

variable {G : Type} [Group G] [Finite G] {M Q Z X : Subgroup G}
  {x : G}

theorem Sit.card_inf_le_Jx (hs : Sit M Q Z X x) :
    Nat.card ↥(Q ⊓ QB X) ≤ Nat.card Z * Nat.card ↥(Jx Q X x) := by
  have H := hs.hyp
  have hxM := hs.memM
  have hxQ := hs.notQ
  have h12 := smith_1_12 hs
  have hx2 := hs.x_sq
  have hxZ := hs.x_cent h12
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨-, -, -, -, hdc⟩ := smith_1_13 hs
  obtain ⟨K, _, _, γ, M₀, hD, hcard, hK2, ⟨A⟩⟩ := exists_model H hxM hxZ
  have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
  have hqpos : 0 < Nat.card Z := by omega
  set N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id
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
  have hTT := A.T_T H hxM hx2
  let Cx : Subgroup G := Q ⊓ Subgroup.centralizer ({x} : Set G)
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
  have hCxW : Cx ≤ preimageSub M₀ W := fun c hc =>
    mem_preimageSub.mpr ⟨hc.1, Submodule.subset_span ⟨c, hc, rfl⟩⟩
  have hpow : ∀ R : Submodule K M₀.E,
      Nat.card (preimageSub M₀ R) = Nat.card Z ^ (Module.finrank K R + 1) := by
    intro R
    rw [card_preimageSub hZQ, Module.natCard_eq_pow_finrank (K := K), hcard, pow_succ]
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
  have hc1 : Nat.card Cx ≤ Nat.card (preimageSub M₀ W) := Subgroup.card_le_of_le hCxW
  have hcount : Module.finrank K (LinearMap.ker N) ≤ Module.finrank K W + 1 := by
    have h1 := hpow (LinearMap.ker N)
    have h2 := hpow W
    have h3 : Nat.card Z ^ (Module.finrank K (LinearMap.ker N) + 1) ≤
        Nat.card Z ^ (Module.finrank K W + 1 + 1) := by
      rw [← h1, pow_succ, ← h2, mul_comm]
      exact hP.trans (Nat.mul_le_mul_left _ hc1)
    have := (Nat.pow_le_pow_iff_right (by omega)).mp h3
    omega
  have hadj : ∀ a f, M₀.B a (N f) = M₀.B (N a) f := fun a f => by
    have h1 : M₀.B a (A.T f) = M₀.B (A.T a) f := by
      rw [← A.hB a (A.T f), hTT]
    simp only [hNapp, map_sub, LinearMap.sub_apply, h1]
  obtain ⟨hrangeW, hdimW⟩ := jx_orth_bound M₀.B hK2 M₀.alt M₀.nondeg N hadj W hWC hcount
  obtain ⟨Bg, hBgdef⟩ : ∃ S : Subgroup G, S = preimageSub M₀ (commSpace A) := ⟨_, rfl⟩
  obtain ⟨Aa, hAadef⟩ : ∃ S : Subgroup G, S = preimageSub M₀ (M₀.B.orthogonal W) :=
    ⟨_, rfl⟩
  have hBg : Bg = ⁅Q, Subgroup.zpowers x⁆ := by
    have h1 : (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) = Bg := by
      rw [hBgdef]
      ext y
      rw [mem_preimageSub]
      exact mem_commSup_iff A H hxM hx2 hZQ
    rw [← h1]
    exact sup_eq_left.mpr (Z_le_comm H hxM hxQ hx2 hxZ)
  have hBQ : ⁅Q, Subgroup.zpowers x⁆ ≤ Q := by
    rw [← hBg, hBgdef]
    intro y hy
    exact (mem_preimageSub.mp hy).1
  have hcsle : commSpace A ≤ M₀.B.orthogonal W := by
    rw [hcs]
    exact hrangeW
  have hBA : Bg ≤ Aa := by
    rw [hBgdef, hAadef]
    intro y hy
    exact mem_preimageSub.mpr ⟨(mem_preimageSub.mp hy).1, hcsle (mem_preimageSub.mp hy).2⟩
  have hDA : Q ⊓ QB X ≤ Aa := by
    rw [hAadef]
    intro d hd
    have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
    refine mem_preimageSub.mpr ⟨hdQ, LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_⟩
    have hsp : W ≤ LinearMap.ker (M₀.B.flip (M₀.π d)) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      have hc' : c ∈ Cx := hc
      have hcQ : c ∈ Q := (Subgroup.mem_inf.mp hc').1
      have hcd : c * d = d * c := (hdc d hd c hc').symm
      exact (GM.comm_eq_one_iff hD hcQ hdQ).mp (commutatorElement_eq_one_iff_mul_comm.mpr hcd)
    exact LinearMap.mem_ker.mp (hsp hu)
  have hinf : Bg ⊓ (Q ⊓ QB X) = Jx Q X x := by
    unfold Jx
    rw [hBg, ← inf_assoc, inf_eq_left.mpr hBQ]
  have hD_rel : Bg.relIndex (Q ⊓ QB X) * Nat.card ↥(Jx Q X x) = Nat.card ↥(Q ⊓ QB X) := by
    have h : Bg.relIndex (Q ⊓ QB X) * Nat.card ↥(Bg ⊓ (Q ⊓ QB X)) = Nat.card ↥(Q ⊓ QB X) :=
      Subgroup.relIndex_mul_card Bg (Q ⊓ QB X)
    rw [hinf] at h
    exact h
  have hA_rel : Bg.relIndex Aa * Nat.card ↥Bg = Nat.card ↥Aa := by
    have h : Bg.relIndex Aa * Nat.card ↥(Bg ⊓ Aa) = Nat.card ↥Aa :=
      Subgroup.relIndex_mul_card Bg Aa
    rw [inf_eq_left.mpr hBA] at h
    exact h
  have hAapos : 0 < Nat.card ↥Aa := Nat.card_pos
  have hne : Bg.relIndex Aa ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hA_rel
    omega
  have hR : Nat.card ↥(LinearMap.range N) =
      Nat.card K ^ Module.finrank K (LinearMap.range N) :=
    Module.natCard_eq_pow_finrank
  have hWp : Nat.card ↥(M₀.B.orthogonal W) =
      Nat.card K ^ Module.finrank K (M₀.B.orthogonal W) :=
    Module.natCard_eq_pow_finrank
  have hBcard : Nat.card ↥Bg =
      Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z := by
    rw [hBgdef, card_preimageSub hZQ, hcs, hR, hcard]
  have hAcard : Nat.card ↥Aa =
      Nat.card Z ^ Module.finrank K (M₀.B.orthogonal W) * Nat.card Z := by
    rw [hAadef, card_preimageSub hZQ, hWp, hcard]
  have hrel_le : Bg.relIndex Aa ≤ Nat.card Z := by
    have hdW : Nat.card Z ^ Module.finrank K (M₀.B.orthogonal W) ≤
        Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z := by
      calc Nat.card Z ^ Module.finrank K (M₀.B.orthogonal W)
          ≤ Nat.card Z ^ (Module.finrank K (LinearMap.range N) + 1) :=
            Nat.pow_le_pow_right hqpos hdimW
        _ = Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z := pow_succ _ _
    have hpos : 0 < Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z :=
      mul_pos (pow_pos hqpos _) hqpos
    have key : Bg.relIndex Aa * (Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z)
        ≤ Nat.card Z * (Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z) := by
      rw [hBcard, hAcard] at hA_rel
      calc Bg.relIndex Aa * (Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z)
          = Nat.card Z ^ Module.finrank K (M₀.B.orthogonal W) * Nat.card Z := hA_rel
        _ ≤ (Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z) * Nat.card Z :=
            Nat.mul_le_mul_right _ hdW
        _ = Nat.card Z * (Nat.card Z ^ Module.finrank K (LinearMap.range N) * Nat.card Z) := by
            ring
    exact Nat.le_of_mul_le_mul_right key hpos
  have hfin : Nat.card ↥(Q ⊓ QB X) ≤ Nat.card Z * Nat.card ↥(Jx Q X x) := by
    rw [← hD_rel]
    exact Nat.mul_le_mul_right _ ((Subgroup.relIndex_le_of_le_right hDA hne).trans hrel_le)
  exact hfin

end Main

end CFSG.RankThree.GF2n.Smith81
