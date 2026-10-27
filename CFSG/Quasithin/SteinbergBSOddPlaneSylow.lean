module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeLinear
public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo

public section

namespace CFSG.Quasithin.SteinbergBS

open Matrix

theorem eq_one_of_mulVec_eq_self_of_two_pow {k : Type*} [Field k] (h2 : (2 : k) ≠ 0)
    {g : GL (Fin 2) k} (hdet : (g : Matrix (Fin 2) (Fin 2) k).det = 1) {v : Fin 2 → k}
    (hv : v ≠ 0) (hgv : (g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v) {m : ℕ} (hm : g ^ 2 ^ m = 1) :
    g = 1 := by
  obtain ⟨Q, hQ⟩ := CFSG.SectionRank.Ccomm.exists_GL_mulVec_single_eq hv
  set g' := Q⁻¹ * g * Q with hg'
  have he : (g' : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hg', Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hQ, hgv, ← hQ,
      mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have h00 : (g' : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    simpa [mulVec_single_one] using congrFun he 0
  have h10 : (g' : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    simpa [mulVec_single_one] using congrFun he 1
  have hdet' : (g' : Matrix (Fin 2) (Fin 2) k).det = 1 := by
    rw [hg', Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have h11 : (g' : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := by
    have h := hdet'
    rw [det_fin_two, h00, h10] at h
    simpa using h
  set c := (g' : Matrix (Fin 2) (Fin 2) k) 0 1 with hc
  have hform : (g' : Matrix (Fin 2) (Fin 2) k) = !![1, c; 0, 1] := by
    rw [eta_fin_two (g' : Matrix (Fin 2) (Fin 2) k), h00, h10, h11]
  have hpow : ∀ n : ℕ, ((g' ^ n : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, (n : k) * c; 0, 1] := by
    intro n
    induction n with
    | zero => simp [one_fin_two]
    | succ n ih =>
      rw [pow_succ, Units.val_mul, ih, hform, mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [add_mul, add_comm]
  have hg'm : g' ^ 2 ^ m = 1 := by
    rw [hg', show Q⁻¹ * g * Q = MulAut.conj Q⁻¹ g by simp, ← map_pow, hm, map_one]
  have hc0 : c = 0 := by
    have h := congrArg (fun A : GL (Fin 2) k => (A : Matrix (Fin 2) (Fin 2) k) 0 1) hg'm
    simp only [hpow, Units.val_one] at h
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h
    push_cast at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ h2)
  have hg'1 : g' = 1 := by
    apply Units.ext
    rw [hform, hc0, Units.val_one, one_fin_two]
  calc g = Q * g' * Q⁻¹ := by rw [hg']; group
    _ = 1 := by rw [hg'1, mul_one, mul_inv_cancel]

theorem nq_perfect_odd_plane_sylow_two_irreducibility
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (hV : Module.finrank (ZMod p) V = 2) (α : L →* (V ≃ₗ[ZMod p] V))
    (hα : α ≠ 1) (S : Sylow 2 L) (W : Submodule (ZMod p) V)
    (hW : ∀ s ∈ (S : Subgroup L), ∀ w ∈ W, α s w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  by_contra hWne
  push Not at hWne
  obtain ⟨hW0, hWT⟩ := hWne
  have : FiniteDimensional (ZMod p) V := Module.finite_of_finrank_pos (by omega)
  have hW1 : Module.finrank (ZMod p) W = 1 := by
    have h1 := Submodule.finrank_lt hWT
    have h2 : 0 < Module.finrank (ZMod p) W :=
      Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hW0)
    omega
  obtain ⟨w₀, hw₀, hspan⟩ := finrank_eq_one_iff'.1 hW1
  have hw : (w₀ : V) ≠ 0 := fun h => hw₀ (Subtype.ext h)
  have heig : ∀ s ∈ (S : Subgroup L), ∃ c : ZMod p, α s w₀ = c • (w₀ : V) := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan ⟨α s w₀, hW s hs w₀ w₀.2⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  let b := Module.finBasisOfFinrankEq (ZMod p) V hV
  let ψ : L →* GL (Fin 2) (ZMod p) :=
    (((LinearMap.toMatrixAlgEquiv b : Module.End (ZMod p) V ≃ₐ[ZMod p] _) :
      Module.End (ZMod p) V →* Matrix (Fin 2) (Fin 2) (ZMod p)).comp
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp α)).toHomUnits
  have hψ : ∀ l : L, ((ψ l : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      LinearMap.toMatrix b b (α l : V →ₗ[ZMod p] V) := fun _ => rfl
  set v : Fin 2 → ZMod p := ⇑(b.repr w₀) with hvdef
  have hv : v ≠ 0 := by
    intro h
    apply hw
    have h' : b.repr (w₀ : V) = 0 := Finsupp.ext fun i => congrFun h i
    simpa using h'
  have hψv : ∀ s ∈ (S : Subgroup L), ∃ c : ZMod p,
      ((ψ s : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = c • v := by
    intro s hs
    obtain ⟨c, hc⟩ := heig s hs
    refine ⟨c, ?_⟩
    rw [hψ, hvdef, LinearMap.toMatrix_mulVec_repr]
    change ⇑(b.repr (α s w₀)) = c • ⇑(b.repr w₀)
    rw [hc, map_smul]
    rfl
  set J := ψ.range with hJ
  have : Group.IsPerfect J := Group.IsPerfect.range ψ
  have hJ1 : J ≠ ⊥ := by
    intro hbot
    apply hα
    ext l x
    have h1 : ψ l = 1 := by
      have : ψ l ∈ J := ⟨l, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have h2 : LinearMap.toMatrix b b (α l : V →ₗ[ZMod p] V) = 1 := by
      rw [← hψ, h1, Units.val_one]
    have h3 : (α l : V →ₗ[ZMod p] V) = LinearMap.id := by
      rw [← LinearMap.toMatrix_id b, ] at h2
      exact (LinearMap.toMatrix b b).injective h2
    simpa using congrArg (fun f : V →ₗ[ZMod p] V => f x) h3
  have hdet : ∀ g ∈ J, (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := fun g hg =>
    CFSG.SectionRank.Ccomm.det_eq_one_of_perfect J hg
  let P : Sylow 2 J := S.mapSurjective ψ.rangeRestrict_surjective
  have hPmem : ∀ x : J, x ∈ (P : Subgroup J) → ∃ c : ZMod p,
      ((x : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = c • v := by
    intro x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact hψv s hs
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hval : ∀ x : J, x ∈ (P : Subgroup J) → ∀ c : ZMod p,
      ((x : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = c • v →
      (((x : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v) i₀ * (v i₀)⁻¹ = c := by
    intro x _ c hc
    rw [hc, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hi₀, mul_one]
  let χ : (P : Subgroup J) →* ZMod p :=
    { toFun := fun x => ((((x : J) : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v)
        i₀ * (v i₀)⁻¹
      map_one' := by simp [mul_inv_cancel₀ hi₀]
      map_mul' := fun x y => by
        obtain ⟨cx, hcx⟩ := hPmem x x.2
        obtain ⟨cy, hcy⟩ := hPmem y y.2
        have hxy : ((((x * y : (P : Subgroup J)) : J) : GL (Fin 2) (ZMod p)) :
            Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = (cx * cy) • v := by
          change (((x : J) : GL (Fin 2) (ZMod p)) * ((y : J) : GL (Fin 2) (ZMod p)) :
            Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = _
          rw [← mulVec_mulVec, hcy, mulVec_smul, hcx, smul_smul, mul_comm]
        show _ = _ * _
        rw [hval _ (x * y).2 _ hxy, hval _ x.2 _ hcx, hval _ y.2 _ hcy] }
  have hχ : Function.Injective χ := by
    intro x y hxy
    set z := x * y⁻¹ with hz
    have hχz : χ z = 1 := by
      have h1 : χ y * χ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [hz, map_mul, hxy, h1]
    obtain ⟨cz, hcz⟩ := hPmem z z.2
    have hcz1 : cz = 1 := (hval _ z.2 _ hcz).symm.trans hχz
    rw [hcz1, one_smul] at hcz
    obtain ⟨m, hm⟩ := P.isPGroup' z
    have hz1 : ((z : J) : GL (Fin 2) (ZMod p)) = 1 :=
      eq_one_of_mulVec_eq_self_of_two_pow (CFSG.SectionRank.Ccomm.two_ne_zero_zmod hp2)
        (hdet _ (z : J).2) hv hcz
        (by rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, hm]; rfl)
    have hz1' : z = 1 := Subtype.ext (Subtype.ext hz1)
    rw [hz, mul_inv_eq_one] at hz1'
    exact hz1'
  have hPcyc : IsCyclic (P : Subgroup J) := isCyclic_of_injective_ringHom χ hχ
  have hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ J :=
    CFSG.SectionRank.Ccomm.neg_one_mem_of_perfect hp2 J hJ1
  let : Fintype J := Fintype.ofFinite J
  have heven : Even (Fintype.card J) := by
    have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    have hne : (⟨-1, hneg⟩ : J) ≠ 1 := by
      intro h
      have h1 := congrArg (fun x : J => ((x : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
      simp only [Units.val_neg, Units.val_one, one_apply_eq, OneMemClass.coe_one] at h1
      exact Ring.neg_one_ne_one_of_char_ne_two hchar h1
    have hord : orderOf (⟨-1, hneg⟩ : J) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simp)) hne
    have hdvd := orderOf_dvd_natCard (⟨-1, hneg⟩ : J)
    rw [hord, Nat.card_eq_fintype_card] at hdvd
    exact even_iff_two_dvd.2 hdvd
  obtain ⟨-, hsurj, -, -⟩ := CFSG.LinearGroups.cyclic_sylow_index_two heven P hPcyc
  obtain ⟨x, hx⟩ := hsurj (-1)
  rw [CFSG.SectionRank.Ccomm.perfect_hom_eq_one] at hx
  exact absurd hx (by decide)

end CFSG.Quasithin.SteinbergBS
