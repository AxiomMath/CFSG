module

public import CFSG.RankThree.GF2n.Smith81.Sec115Dim
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

section Lin

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem finrank_ker_ge_of_involution (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (T : E ≃ₗ[K] E) (hTT : ∀ e, T (T e) = e) (hTB : ∀ e f, B (T e) (T f) = B e f)
    (n : ℕ) (hE : finrank K E = 2 * n) :
    n ≤ finrank K (LinearMap.ker ((T : E →ₗ[K] E) - LinearMap.id)) := by
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
  have hRiso : ∀ u ∈ LinearMap.range N, ∀ v ∈ LinearMap.range N, B u v = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [hadj, hNN, map_zero, LinearMap.zero_apply]
  have hd := Sec115Dim.two_mul_finrank_le_of_iso B hK2 halt hnd _ hRiso
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [hE] at hd hrn
  omega

end Lin

section LemmaC

open Module

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem card_centralizer_ge (H : StrothHyp M Q Z) {n : ℕ} (hw : Width Q Z n) {y : G}
    (hyM : y ∈ M) (hyZ : ∀ z ∈ Z, y * z * y⁻¹ = z) (hy2 : y * y = 1) :
    Nat.card Z ^ n ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) := by
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
  obtain ⟨K, _, _, γ, M₀, -, hcard, hK2, ⟨A⟩⟩ := exists_model H hyM hyZ
  have hpow : ∀ R : Submodule K M₀.E,
      Nat.card (preimageSub M₀ R) = Nat.card Z ^ (finrank K R + 1) := by
    intro R
    rw [card_preimageSub hZQ, Module.natCard_eq_pow_finrank (K := K), hcard, pow_succ]
  have hE : finrank K M₀.E = 2 * n := by
    have h1 := hpow ⊤
    have h2 : preimageSub M₀ ⊤ = Q := by ext c; simp [mem_preimageSub]
    rw [h2, hw, finrank_top] at h1
    have := (Nat.pow_right_injective hq) h1
    omega
  set N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id
  have hNapp : ∀ f, N f = A.T f - f := fun f => rfl
  have hTT : ∀ e, A.T (A.T e) = e := A.T_T H hyM hy2
  have hfix : n ≤ finrank K (LinearMap.ker N) :=
    finrank_ker_ge_of_involution M₀.B hK2 M₀.alt M₀.nondeg A.T hTT A.hB n hE
  have hPZ : ∀ c ∈ preimageSub M₀ (LinearMap.ker N), y * c * y⁻¹ * c⁻¹ ∈ Z := by
    intro c hc
    have hcQ := (mem_preimageSub.mp hc).1
    have hT : A.T (M₀.π c) = M₀.π c := by
      have := LinearMap.mem_ker.mp (mem_preimageSub.mp hc).2
      rw [hNapp, sub_eq_zero] at this
      exact this
    have hcc := conj_mem_Q H hyM hcQ
    refine (M₀.π_ker _ (Q.mul_mem hcc (Q.inv_mem hcQ))).mp ?_
    rw [M₀.π_mul _ hcc _ (Q.inv_mem hcQ), Tim79.QuadModel.pi_inv M₀ hcQ, A.hπ c hcQ, hT,
      add_neg_cancel]
  let φ : preimageSub M₀ (LinearMap.ker N) →* Z :=
    { toFun := fun c => ⟨y * c * y⁻¹ * (c : G)⁻¹, hPZ c c.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        show y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹ =
          (y * a * y⁻¹ * (a : G)⁻¹) * (y * b * y⁻¹ * (b : G)⁻¹)
        have hv : Commute (y * b * y⁻¹ * (b : G)⁻¹) (a : G)⁻¹ :=
          Commute.inv_right (Z_central H (hPZ b b.2) (mem_preimageSub.mp a.2).1)
        calc y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹
            = y * a * y⁻¹ * ((y * b * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = y * a * y⁻¹ * ((a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹)) := by rw [hv.eq]
          _ = _ := by group }
  have hkerC : ∀ k : preimageSub M₀ (LinearMap.ker N), k ∈ φ.ker →
      (k : G) ∈ Q ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro k hk
    have h' : y * (k : G) * y⁻¹ * (k : G)⁻¹ = 1 := congrArg Subtype.val hk
    have h2 : y * (k : G) = k * y := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h')
    exact ⟨(mem_preimageSub.mp k.2).1, Subgroup.mem_centralizer_singleton_iff.mpr h2.symm⟩
  have hker : Nat.card φ.ker ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) :=
    Nat.card_le_card_of_injective
      (fun k : φ.ker => (⟨k.1.1, hkerC k.1 k.2⟩ : ↥(Q ⊓ Subgroup.centralizer ({y} : Set G))))
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  have hP : Nat.card ↥(preimageSub M₀ (LinearMap.ker N)) ≤
      Nat.card Z * Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, mul_comm]
    exact Nat.mul_le_mul (Subgroup.card_le_card_group _) hker
  have hcount : Nat.card Z ^ (n + 1) ≤
      Nat.card Z * Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) := by
    refine le_trans ?_ hP
    rw [hpow (LinearMap.ker N)]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hpow' : Nat.card Z ^ (n + 1) = Nat.card Z * Nat.card Z ^ n := by ring
  rw [hpow'] at hcount
  exact Nat.le_of_mul_le_mul_left hcount (by omega)

theorem Sit.card_Lx_ge {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {n : ℕ}
    (hw : Width Q Z n) : Nat.card Z ^ n ≤ Nat.card ↥(Lx M X) := by
  have h12 := smith_1_12 hs
  obtain ⟨g, hg, hQB, hN⟩ := hs.QB_eq
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton ↥Z :=
      ⟨fun a b => Subtype.ext (by rw [hcon (a : G) a.2, hcon (b : G) b.2])⟩
    have h1 : Nat.card ↥Z = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    have := hs.hyp.q4
    omega
  have hzN : z ∈ Subgroup.normalizer (X : Set G) := Z_le_normalizer_X h12 hz
  rw [hN, mem_conjSubgroup] at hzN
  have hyM : g⁻¹ * z * g ∈ M := hzN
  have hzz : z * z = 1 := (sq z).symm.trans (Z_sq hs.hyp hz)
  have hy2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  have hyZ : ∀ w ∈ Z, g⁻¹ * z * g * w * (g⁻¹ * z * g)⁻¹ = w := by
    intro w hw'
    have hwX : g * w * g⁻¹ ∈ X := by
      rw [hg, mem_conjSubgroup]
      have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rw [e]
      exact hw'
    have hc : z * (g * w * g⁻¹) = (g * w * g⁻¹) * z :=
      Subgroup.mem_centralizer_iff.mp (h12.1 hwX).2 z hz
    calc g⁻¹ * z * g * w * (g⁻¹ * z * g)⁻¹ = g⁻¹ * (z * (g * w * g⁻¹)) * z⁻¹ * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * z) * z⁻¹ * g := by rw [hc]
      _ = w := by group
  have hL := card_centralizer_ge hs.hyp hw hyM hyZ hy2
  have hconj : ∀ c ∈ Q ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G),
      g * c * g⁻¹ ∈ QB X ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro c hc
    obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcy : c * (g⁻¹ * z * g) = (g⁻¹ * z * g) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcC
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hQB, mem_conjSubgroup]
      have e : g⁻¹ * (g * c * g⁻¹) * g = c := by group
      rw [e]
      exact hcQ
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [hcy]
        _ = z * (g * c * g⁻¹) := by group
  have hT : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) ≤
      Nat.card ↥(QB X ⊓ Subgroup.centralizer ({z} : Set G)) :=
    Nat.card_le_card_of_injective
      (fun c : ↥(Q ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) =>
        (⟨g * (c : G) * g⁻¹, hconj c c.2⟩ : ↥(QB X ⊓ Subgroup.centralizer ({z} : Set G))))
      (fun a b h => by
        have h' : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val h
        exact Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  have hCM : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c ∈ M := fun c hc =>
    mem_M_of_commute_Z hs.hyp hz hz1 (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hLx : QB X ⊓ Subgroup.centralizer ({z} : Set G) ≤ Lx M X := fun c hc => by
    obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
    show c ∈ QB X ⊓ M
    exact Subgroup.mem_inf.mpr ⟨hcQ, hCM c hcC⟩
  exact le_trans hL (le_trans hT (Subgroup.card_le_of_le hLx))

end LemmaC

end CFSG.RankThree.GF2n.Smith81
