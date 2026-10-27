module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem exists_involution_specialLinear (F : Type) [Field F] [CharP F 2] :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 ∧ x * x = 1 := by
  have hij : (0 : Fin 2) ≠ 1 := by decide
  refine ⟨Matrix.SpecialLinearGroup.transvection hij (1 : F), ?_, ?_⟩
  · intro hx
    have hmem : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [hx]; exact Subgroup.one_mem _
    exact one_ne_zero
      ((Matrix.SpecialLinearGroup.transvection_mem_center_iff hij (1 : F)).1 hmem)
  · have h2 : (1 : F) + 1 = 0 := by
      rw [one_add_one_eq_two, CharTwo.two_eq_zero]
    calc Matrix.SpecialLinearGroup.transvection hij (1 : F) *
          Matrix.SpecialLinearGroup.transvection hij (1 : F)
        = Matrix.SpecialLinearGroup.transvection hij ((1 : F) + 1) :=
          (Matrix.SpecialLinearGroup.transvection_add hij (1 : F) (1 : F)).symm
      _ = Matrix.SpecialLinearGroup.transvection hij (0 : F) := by rw [h2]
      _ = 1 := Matrix.SpecialLinearGroup.transvection_coeff_zero hij

private lemma w85g_wreathAct_apply {L : Type} [Group L] {m : ℕ} (σ : Equiv.Perm (Fin m))
    (r : Fin m → L) (i : Fin m) :
    (wreathAct L m σ r) i = r (σ.symm i) := by
  simp [wreathAct]

theorem exists_noncomm_mulSingle {L : Type} [Group L] {m : ℕ} {x₀ : L} (hx₀ : x₀ ≠ 1)
    (d : WreathSym L m) (hd : SemidirectProduct.rightHom d ≠ 1) :
    ∃ k : Fin m, d * SemidirectProduct.inl (Pi.mulSingle k x₀) ≠
      SemidirectProduct.inl (Pi.mulSingle k x₀) * d := by
  have hσ : d.right ≠ 1 := by simpa using hd
  obtain ⟨k, hk⟩ : ∃ k : Fin m, d.right k ≠ k := by
    by_contra h
    rw [not_exists] at h
    exact hσ (Equiv.ext fun k => by simpa using not_not.mp (h k))
  refine ⟨k, fun heq => ?_⟩
  have hleft : d.left * (wreathAct L m d.right) (Pi.mulSingle k x₀) =
      Pi.mulSingle k x₀ * d.left := by
    simpa using congrArg SemidirectProduct.left heq
  have heval := congrFun hleft (d.right k)
  rw [Pi.mul_apply, Pi.mul_apply, w85g_wreathAct_apply, Equiv.symm_apply_apply,
    Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hk, one_mul] at heval
  exact hx₀ (mul_left_cancel (by rw [heval, mul_one]))

theorem not_centralInSylow_wreathSym {L : Type} [Group L] {m : ℕ} [Finite (WreathSym L m)]
    (hm : 2 ≤ m) {x₀ : L} (hx₀ : x₀ ≠ 1) (hx₀2 : x₀ * x₀ = 1) (d : WreathSym L m)
    (hcl : Subgroup.normalClosure ({d} : Set (WreathSym L m)) = ⊤) :
    ¬ CentralInSylow (WreathSym L m) (Subgroup.zpowers d) := by
  classical
  rintro ⟨P, hdP, hcomm⟩
  have hσ : SemidirectProduct.rightHom d ≠ 1 := by
    intro h1
    have hker : Subgroup.normalClosure ({d} : Set (WreathSym L m)) ≤
        (SemidirectProduct.rightHom : WreathSym L m →* Equiv.Perm (Fin m)).ker :=
      Subgroup.normalClosure_le_normal (by simpa using h1)
    rw [hcl, top_le_iff] at hker
    obtain ⟨y, hy⟩ := SemidirectProduct.rightHom_surjective (N := Fin m → L)
      (φ := wreathAct L m) (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, hm⟩)
    have hy1 : SemidirectProduct.rightHom y = 1 := by
      have : y ∈ (SemidirectProduct.rightHom : WreathSym L m →* Equiv.Perm (Fin m)).ker := by
        rw [hker]; exact Subgroup.mem_top y
      simpa using this
    have h01 := congrArg (fun f : Equiv.Perm (Fin m) => f ⟨0, by omega⟩) (hy.symm.trans hy1)
    simp at h01
  let Q : Subgroup (WreathSym L m) :=
    (Subgroup.pi (Set.univ : Set (Fin m)) (fun _ => Subgroup.zpowers x₀)).map
      SemidirectProduct.inl
  have hQ : IsPGroup 2 Q := by
    rintro ⟨q, hq⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hq
    refine ⟨1, Subtype.ext ?_⟩
    have hx2 : x₀ ^ (2 : ℤ) = 1 := by rw [zpow_two, hx₀2]
    have hr2 : r ^ 2 = 1 := by
      funext k
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_pi _).1 hr k (Set.mem_univ k))
      simp only [Pi.pow_apply, Pi.one_apply, pow_two]
      rw [← hj, ← zpow_add, ← mul_two, zpow_mul', hx2, one_zpow]
    show (SemidirectProduct.inl r) ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, hr2, map_one]
  obtain ⟨P', hQP'⟩ := IsPGroup.exists_le_sylow hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WreathSym L m) P' P
  have hconj : ∀ q ∈ Q, g * q * g⁻¹ ∈ (P : Subgroup (WreathSym L m)) := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ ((g • P' : Sylow 2 (WreathSym L m)) : Subgroup (WreathSym L m)) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨q, hQP' hq, rfl⟩
    rwa [hg] at h1
  have hd' : SemidirectProduct.rightHom (g⁻¹ * d * g) ≠ 1 := by
    intro h1
    apply hσ
    have := congrArg (fun z : Equiv.Perm (Fin m) =>
      SemidirectProduct.rightHom g * z * (SemidirectProduct.rightHom g)⁻¹) h1
    simpa [map_mul, map_inv, mul_assoc] using this
  obtain ⟨k, hk⟩ := exists_noncomm_mulSingle hx₀ (g⁻¹ * d * g) hd'
  apply hk
  have hmem : SemidirectProduct.inl (Pi.mulSingle k x₀) ∈ Q :=
    Subgroup.mem_map.2 ⟨Pi.mulSingle k x₀, (Subgroup.mem_pi _).2 fun i _ => by
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik], rfl⟩
  have hc2 := hcomm d (Subgroup.mem_zpowers d) _ (hconj _ hmem)
  calc g⁻¹ * d * g * SemidirectProduct.inl (Pi.mulSingle k x₀)
      = g⁻¹ * (d * (g * SemidirectProduct.inl (Pi.mulSingle k x₀) * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * SemidirectProduct.inl (Pi.mulSingle k x₀) * g⁻¹) * d) * g := by rw [hc2]
    _ = SemidirectProduct.inl (Pi.mulSingle k x₀) * (g⁻¹ * d * g) := by group

theorem not_centralInSylow_of_isL2WrSymGp {Y : Type} [Group Y] [Finite Y] {n m : ℕ}
    (hm : 2 ≤ m) (hY : IsL2WrSymGp Y n m) (d : Y)
    (hcl : Subgroup.normalClosure ({d} : Set Y) = ⊤) :
    ¬ CentralInSylow Y (Subgroup.zpowers d) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  haveI : Finite (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) := Finite.of_equiv Y e.toEquiv
  obtain ⟨x₀, hx₀, hx₀2⟩ := exists_involution_specialLinear F
  intro hc
  have hmap := centralInSylow_map e.toMonoidHom e.surjective _ hc
  rw [MonoidHom.map_zpowers] at hmap
  refine not_centralInSylow_wreathSym hm hx₀ hx₀2 (e d) ?_ hmap
  have := Subgroup.map_normalClosure ({d} : Set Y) e.toMonoidHom e.surjective
  rw [hcl, Set.image_singleton, Subgroup.map_top_of_surjective _ e.surjective] at this
  exact this.symm

end CFSG.LocalAnalysis.WeakClosure81

end
