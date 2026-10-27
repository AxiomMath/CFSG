module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private abbrev s16c11_v1_cyc : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private abbrev s16c11_v1_tr (i : Fin 3) : Equiv.Perm (Fin 3) :=
  ![Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 0 1] i

private abbrev s16c11_v1_sg (i : Fin 3) : Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 2] i

private theorem s16c11_v1_cyc_pow_three : s16c11_v1_cyc ^ 3 = 1 := by decide +kernel

private theorem s16c11_v1_cyc_ne_one : s16c11_v1_cyc ≠ 1 := by decide +kernel

private theorem s16c11_v1_orderOf_cyc : orderOf s16c11_v1_cyc = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime s16c11_v1_cyc_pow_three s16c11_v1_cyc_ne_one

private theorem s16c11_v1_tr_sq (i : Fin 3) : s16c11_v1_tr i * s16c11_v1_tr i = 1 := by
  decide +kernel +revert

private theorem s16c11_v1_sg_mul_tr (i : Fin 3) :
    s16c11_v1_sg i * s16c11_v1_tr i * (s16c11_v1_sg i)⁻¹ = s16c11_v1_tr 0 := by
  decide +kernel +revert

private theorem s16c11_v1_sg_conj_fix (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (s16c11_v1_sg i * π * (s16c11_v1_sg (π⁻¹ i))⁻¹) 0 = 0 := by
  decide +kernel +revert

private theorem s16c11_v1_fix_zero_eq :
    ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ = 1 ∨ σ = s16c11_v1_tr 0 := by
  decide +kernel

theorem s16c11_v1_model_of_fpf {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {K X : Subgroup (MulAut W)} (hKX : K ≤ X) (hK : IsSym ↥K 3)
    (hfpf : ∀ k ∈ K, orderOf k = 3 → ∀ w : W, k w = w → w = 1) :
    ∃ J₀ : Subgroup W, S16C11Model X K J₀ := by
  classical
  have hsq : ∀ w : W, w * w = 1 := fun w => by simpa [sq] using hW2 w
  obtain ⟨e⟩ := hK
  let c : ↥K := e.symm s16c11_v1_cyc
  let t0 : ↥K := e.symm (s16c11_v1_tr 0)
  have hce : e c = s16c11_v1_cyc := e.apply_symm_apply _
  have hte : e t0 = s16c11_v1_tr 0 := e.apply_symm_apply _
  have hc3 : c ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, hce, s16c11_v1_cyc_pow_three, map_one]
  have hcord : orderOf (c : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq, hce, s16c11_v1_orderOf_cyc]
  have hc3a : (c : MulAut W) ^ 3 = 1 := by
    simpa using congrArg (fun k : ↥K => (k : MulAut W)) hc3
  have ht02 : t0 * t0 = 1 := by
    apply e.injective
    rw [map_mul, hte, s16c11_v1_tr_sq 0, map_one]
  have ht02a : (t0 : MulAut W) * (t0 : MulAut W) = 1 := by
    simpa using congrArg (fun k : ↥K => (k : MulAut W)) ht02
  have ht0apply : ∀ u : W, (t0 : MulAut W) ((t0 : MulAut W) u) = u := by
    intro u
    have h := congrArg (fun f : MulAut W => f u) ht02a
    simpa [MulAut.mul_apply] using h
  let J₀ : Subgroup W :=
  { carrier := {w | (t0 : MulAut W) w = w}
    one_mem' := map_one _
    mul_mem' := by
      intro a b ha hb
      show (t0 : MulAut W) (a * b) = a * b
      rw [map_mul, ha, hb]
    inv_mem' := by
      intro a ha
      show (t0 : MulAut W) a⁻¹ = a⁻¹
      rw [map_inv, ha] }
  let S : Fin 3 → ↥K := ![1, c * t0, c ^ 2 * t0]
  let T : Fin 3 → ↥K := ![t0, c ^ 2 * t0, c * t0]
  have hSe : ∀ i, e (S i) = s16c11_v1_sg i := by
    intro i
    fin_cases i <;> simp [S, s16c11_v1_sg, hce, hte] <;> decide +kernel
  have hTe : ∀ i, e (T i) = s16c11_v1_tr i := by
    intro i
    fin_cases i <;> simp [T, s16c11_v1_tr, hce, hte] <;> decide +kernel
  have hc_inv : c⁻¹ = c ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hc3]
  have hc3apply : ∀ u : W, (c : MulAut W) ((c : MulAut W) ((c : MulAut W) u)) = u := by
    intro u
    have h := congrArg (fun f : MulAut W => f u) hc3a
    simpa [pow_succ, pow_two, MulAut.mul_apply] using h
  have hzfix : ∀ w : W, w * (c : MulAut W) w * (c : MulAut W) ((c : MulAut W) w) = 1 := by
    intro w
    have hfix : (c : MulAut W) (w * (c : MulAut W) w * (c : MulAut W) ((c : MulAut W) w))
        = w * (c : MulAut W) w * (c : MulAut W) ((c : MulAut W) w) := by
      rw [map_mul, map_mul, hc3apply]
      ac_rfl
    exact hfpf (c : MulAut W) c.2 hcord _ hfix
  have hzz : ∀ u : W,
      (c : MulAut W) u * (c : MulAut W) ((c : MulAut W) u) = u := by
    intro u
    calc (c : MulAut W) u * (c : MulAut W) ((c : MulAut W) u)
        = (u * u) * ((c : MulAut W) u * (c : MulAut W) ((c : MulAut W) u)) := by
          rw [hsq u, one_mul]
      _ = u * (u * (c : MulAut W) u * (c : MulAut W) ((c : MulAut W) u)) := by ac_rfl
      _ = u * 1 := by rw [hzfix u]
      _ = u := mul_one u
  have hSTconj : ∀ i, S i * T i * (S i)⁻¹ = t0 := by
    intro i
    apply e.injective
    rw [map_mul, map_mul, map_inv, hSe i, hTe i, hte]
    exact s16c11_v1_sg_mul_tr i
  have htct : t0 * c * t0 = c ^ 2 := by
    apply e.injective
    simp only [map_mul, map_pow, hte, hce]
    decide +kernel
  have hS0 : (S 0 : MulAut W) = 1 := rfl
  have hS1 : (S 1 : MulAut W) = (c : MulAut W) * (t0 : MulAut W) := rfl
  have hS2 : (S 2 : MulAut W) = (c : MulAut W) ^ 2 * (t0 : MulAut W) := rfl
  have hSsum : ∀ w : W, (S 0 : MulAut W) w * (S 1 : MulAut W) w * (S 2 : MulAut W) w
      = w * (t0 : MulAut W) w := by
    intro w
    rw [hS0, hS1, hS2, pow_two]
    show w * (c : MulAut W) ((t0 : MulAut W) w)
        * (c : MulAut W) ((c : MulAut W) ((t0 : MulAut W) w))
        = w * (t0 : MulAut W) w
    rw [mul_assoc, hzz ((t0 : MulAut W) w)]
  let D : W →* W :=
  { toFun := fun w => w * (t0 : MulAut W) w
    map_one' := by simp
    map_mul' := by
      intro a b
      show (a * b) * (t0 : MulAut W) (a * b)
          = a * (t0 : MulAut W) a * (b * (t0 : MulAut W) b)
      rw [map_mul]
      ac_rfl }
  have hDfix : ∀ w : W, (t0 : MulAut W) (D w) = D w := by
    intro w
    show (t0 : MulAut W) (w * (t0 : MulAut W) w) = w * (t0 : MulAut W) w
    rw [map_mul, ht0apply w, mul_comm]
  have hD2 : ∀ w : W, D (D w) = 1 := by
    intro w
    show D w * (t0 : MulAut W) (D w) = 1
    rw [hDfix w]
    simpa [pow_two] using hW2 (D w)
  have hDτ : ∀ u : W, D ((t0 : MulAut W) u) = D u := by
    intro u
    show (t0 : MulAut W) u * (t0 : MulAut W) ((t0 : MulAut W) u)
        = u * (t0 : MulAut W) u
    rw [ht0apply u, mul_comm]
  have hScosetMul : ∀ (κ : ↥K) (i : Fin 3),
      (S i : MulAut W) * (κ : MulAut W) * ((S ((e κ)⁻¹ i) : MulAut W))⁻¹ = 1 ∨
      (S i : MulAut W) * (κ : MulAut W) * ((S ((e κ)⁻¹ i) : MulAut W))⁻¹
        = (t0 : MulAut W) := by
    intro κ i
    have hfix : e (S i * κ * (S ((e κ)⁻¹ i))⁻¹) 0 = 0 := by
      rw [map_mul, map_mul, map_inv, hSe i, hSe ((e κ)⁻¹ i)]
      exact s16c11_v1_sg_conj_fix (e κ) i
    rcases s16c11_v1_fix_zero_eq (e (S i * κ * (S ((e κ)⁻¹ i))⁻¹)) hfix with h | h
    · left
      have hX : S i * κ * (S ((e κ)⁻¹ i))⁻¹ = 1 := e.injective (by rw [h, map_one])
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        using congrArg (fun k : ↥K => (k : MulAut W)) hX
    · right
      have hX : S i * κ * (S ((e κ)⁻¹ i))⁻¹ = t0 := e.injective (by rw [h, hte])
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv]
        using congrArg (fun k : ↥K => (k : MulAut W)) hX
  let x : Fin 3 → W →* ↥J₀ := fun i =>
    { toFun := fun w => ⟨D ((S i : MulAut W) w), hDfix _⟩
      map_one' := by
        apply Subtype.ext
        show D ((S i : MulAut W) 1) = 1
        rw [map_one, map_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        show D ((S i : MulAut W) (a * b))
            = D ((S i : MulAut W) a) * D ((S i : MulAut W) b)
        rw [map_mul, map_mul] }
  have htriple : ∀ w : W, x 0 w * x 1 w * x 2 w = 1 := by
    intro w
    apply Subtype.ext
    show D ((S 0 : MulAut W) w) * D ((S 1 : MulAut W) w) * D ((S 2 : MulAut W) w) = 1
    rw [← map_mul, ← map_mul, hSsum w]
    exact hD2 w
  let φ : W →* ↥(s16c2m_Triples ↥J₀) :=
    { toFun := fun w => ⟨fun i => x i w, by
        rw [s16c2m_mem_Triples_iff]
        exact htriple w⟩
      map_one' := by
        apply Subtype.ext
        funext i
        exact map_one (x i)
      map_mul' := by
        intro a b
        apply Subtype.ext
        funext i
        show x i (a * b) = x i a * x i b
        exact map_mul (x i) a b }
  have hφker : ∀ w : W, φ w = 1 → w = 1 := by
    intro w hw
    have hx1 : ∀ i : Fin 3, x i w = 1 := by
      intro i
      have h := congrArg (fun t : ↥(s16c2m_Triples ↥J₀) => (t : Fin 3 → ↥J₀) i) hw
      show x i w = 1
      exact h
    have hxw : ∀ i : Fin 3, (S i : MulAut W) w * (t0 : MulAut W) ((S i : MulAut W) w) = 1 := by
      intro i
      have h := congrArg (fun u : ↥J₀ => (u : W)) (hx1 i)
      show (S i : MulAut W) w * (t0 : MulAut W) ((S i : MulAut W) w) = 1
      exact h
    have hτS : ∀ i : Fin 3, (t0 : MulAut W) ((S i : MulAut W) w) = (S i : MulAut W) w := by
      intro i
      rw [eq_inv_of_mul_eq_one_right (hxw i),
        inv_eq_of_mul_eq_one_right (hsq ((S i : MulAut W) w))]
    have hSTi : ∀ i : Fin 3,
        (S i : MulAut W) ((T i : MulAut W) w) = (t0 : MulAut W) ((S i : MulAut W) w) := by
      intro i
      have h2 : (S i : MulAut W) * (T i : MulAut W)
          = (t0 : MulAut W) * (S i : MulAut W) := by
        have h := congrArg (fun k : ↥K => (k : MulAut W)) (hSTconj i)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
        calc (S i : MulAut W) * (T i : MulAut W)
            = ((S i : MulAut W) * (T i : MulAut W)) * ((S i : MulAut W))⁻¹
                * (S i : MulAut W) := by group
          _ = (t0 : MulAut W) * (S i : MulAut W) := by rw [h]
      calc (S i : MulAut W) ((T i : MulAut W) w)
          = ((S i : MulAut W) * (T i : MulAut W)) w := rfl
        _ = ((t0 : MulAut W) * (S i : MulAut W)) w := by rw [h2]
        _ = (t0 : MulAut W) ((S i : MulAut W) w) := rfl
    have hTfix : ∀ i : Fin 3, (T i : MulAut W) w = w := by
      intro i
      exact ((S i : MulAut W)).injective (by rw [hSTi i, hτS i])
    have hτw : (t0 : MulAut W) w = w := by
      have := hTfix 0
      simpa [T] using this
    have hcw : (c : MulAut W) w = w := by
      have h := hTfix 2
      have hT2 : (T 2 : MulAut W) = (c : MulAut W) * (t0 : MulAut W) := rfl
      rw [hT2, MulAut.mul_apply, hτw] at h
      exact h
    exact hfpf (c : MulAut W) c.2 hcord w hcw
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by
      rw [map_mul, hab, map_inv, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hφker (a * b⁻¹) h1)
  have hker : D.ker = J₀ := by
    ext w
    rw [MonoidHom.mem_ker]
    change D w = 1 ↔ (t0 : MulAut W) w = w
    constructor
    · intro hw
      rw [eq_inv_of_mul_eq_one_right hw, inv_eq_of_mul_eq_one_right (hsq w)]
    · intro hw
      show w * (t0 : MulAut W) w = 1
      rw [hw]
      exact hsq w
  have hrange : D.range = J₀ := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hy
      exact hDfix w
    · intro hy
      rw [MonoidHom.mem_range]
      refine ⟨(c : MulAut W) y, ?_⟩
      show (c : MulAut W) y * (t0 : MulAut W) ((c : MulAut W) y) = y
      have hτcy : (t0 : MulAut W) ((c : MulAut W) y) = (c : MulAut W) ((c : MulAut W) y) := by
        have hτc2 : ∀ u : W, (t0 : MulAut W) ((c : MulAut W) u)
            = (c : MulAut W) ((c : MulAut W) ((t0 : MulAut W) u)) := by
          intro u
          have h1 : (t0 : MulAut W) * (c : MulAut W)
              = (c : MulAut W) ^ 2 * (t0 : MulAut W) := by
            have h2 : t0 * c * t0 = c ^ 2 := htct
            have h3 : t0 * c = c ^ 2 * t0 := by
              calc t0 * c = (t0 * c) * (t0 * t0) := by rw [ht02, mul_one]
                _ = ((t0 * c) * t0) * t0 := by rw [← mul_assoc]
                _ = c ^ 2 * t0 := by rw [h2]
            simpa using congrArg (fun k : ↥K => (k : MulAut W)) h3
          have h := congrArg (fun f : MulAut W => f u) h1
          simpa [MulAut.mul_apply, pow_two] using h
        rw [hτc2 y, hy]
      rw [hτcy, hzz y]
  have hcard : Nat.card W = Nat.card ↥J₀ * Nat.card ↥J₀ := by
    have h := card_ker_mul_card_range D
    rw [hker, hrange] at h
    exact h.symm
  have htriples : Nat.card ↥(s16c2m_Triples ↥J₀) = Nat.card W := by
    rw [s16c2m_card_Triples, sq, hcard]
  have hle : Nat.card ↥(s16c2m_Triples ↥J₀) ≤ Nat.card W := by rw [htriples]
  have hφbij : Function.Bijective φ := hφinj.bijective_of_nat_card_le hle
  let ψ : W ≃* ↥(s16c2m_Triples ↥J₀) := MulEquiv.ofBijective φ hφbij
  have hψ : ∀ (w : W) (i : Fin 3), ((ψ w).1 i) = x i w := fun w i => rfl
  have hxequiv : ∀ (κ : ↥K) (w : W) (i : Fin 3),
      x i ((κ : MulAut W) w) = x ((e κ)⁻¹ i) w := by
    intro κ w i
    rcases hScosetMul κ i with h | h
    · apply Subtype.ext
      show D ((S i : MulAut W) ((κ : MulAut W) w))
          = D ((S ((e κ)⁻¹ i) : MulAut W) w)
      have h1 : (S i : MulAut W) * (κ : MulAut W) = (S ((e κ)⁻¹ i) : MulAut W) := by
        calc (S i : MulAut W) * (κ : MulAut W)
            = ((S i : MulAut W) * (κ : MulAut W)
                * ((S ((e κ)⁻¹ i) : MulAut W))⁻¹) * (S ((e κ)⁻¹ i) : MulAut W) := by
              group
          _ = (S ((e κ)⁻¹ i) : MulAut W) := by rw [h, one_mul]
      have hL : (S i : MulAut W) ((κ : MulAut W) w)
          = (S ((e κ)⁻¹ i) : MulAut W) w := by
        rw [← MulAut.mul_apply, h1]
      rw [hL]
    · apply Subtype.ext
      show D ((S i : MulAut W) ((κ : MulAut W) w))
          = D ((S ((e κ)⁻¹ i) : MulAut W) w)
      have h1 : (S i : MulAut W) * (κ : MulAut W)
          = (t0 : MulAut W) * (S ((e κ)⁻¹ i) : MulAut W) := by
        calc (S i : MulAut W) * (κ : MulAut W)
            = ((S i : MulAut W) * (κ : MulAut W)
                * ((S ((e κ)⁻¹ i) : MulAut W))⁻¹) * (S ((e κ)⁻¹ i) : MulAut W) := by
              group
          _ = (t0 : MulAut W) * (S ((e κ)⁻¹ i) : MulAut W) := by rw [h]
      have hL : (S i : MulAut W) ((κ : MulAut W) w)
          = (t0 : MulAut W) ((S ((e κ)⁻¹ i) : MulAut W) w) := by
        rw [← MulAut.mul_apply, h1, MulAut.mul_apply]
      rw [hL, hDτ]
  refine ⟨J₀, e, ψ, ?_, ?_⟩
  · intro κ w i
    rw [hψ ((κ : MulAut W) w) i, hψ w ((e κ)⁻¹ i)]
    exact hxequiv κ w i
  · intro g hgX hgK w i
    rw [hψ (g w) i, hψ w i]
    show D ((S i : MulAut W) (g w)) = g (D ((S i : MulAut W) w))
    have hgτ : g * (t0 : MulAut W) = (t0 : MulAut W) * g := hgK (t0 : MulAut W) t0.2
    have hgS : g * (S i : MulAut W) = (S i : MulAut W) * g := hgK (S i : MulAut W) (S i).2
    have hDg : ∀ u : W, D (g u) = g (D u) := by
      intro u
      show g u * (t0 : MulAut W) (g u) = g (u * (t0 : MulAut W) u)
      rw [map_mul]
      congr 1
      have h := congrArg (fun f : MulAut W => f u) hgτ
      simpa [MulAut.mul_apply] using h.symm
    have hL : (S i : MulAut W) (g w) = g ((S i : MulAut W) w) := by
      rw [← MulAut.mul_apply, ← hgS, MulAut.mul_apply]
    rw [hL]
    exact hDg ((S i : MulAut W) w)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
