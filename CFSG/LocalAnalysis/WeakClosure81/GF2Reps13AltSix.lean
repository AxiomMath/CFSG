module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.Setup.X3Aut CFSG.Quasithin.H13.A5 Equiv
open scoped commutatorElement

section PGL

private theorem pgl_coset_check : Core.autL.all (fun c => Core.cmul c c != Core.cid ||
    c == Core.cid || Core.pslLit.contains c || Core.inS6 c ||
      Core.pslLit.contains (Core.cmul (invC c) CFSG.QuasithinUnique.DoubleA3.tMulC)) = true := by
  decide +kernel

private theorem pgl_coset {α : P10} (hα : α ∈ A6Models.autA6) (h2 : α * α = 1) (hne : α ≠ 1)
    (hpsl : α ∉ A6Models.psl29) (hs6 : α ∉ s6) : α⁻¹ * A6Models.tMul ∈ A6Models.psl29 := by
  have h := pgl_coset_check
  rw [List.all_eq_true] at h
  have h1 := h (code α) (code_mem_autL hα)
  have e1 : (Core.cmul (code α) (code α) != Core.cid) = false := by
    rw [← code_mul, h2, code_one]
    simp
  have e2 : (code α == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro hc
    exact hne (code_injective hc)
  have e3 : Core.pslLit.contains (code α) = false := by
    rw [← Bool.not_eq_true, List.contains_iff_mem, ← mem_psl29_iff]
    exact hpsl
  have e4 : Core.inS6 (code α) = false :=
    Bool.eq_false_iff.mpr fun h => hs6 ((mem_s6_iff α).mpr h)
  rw [e1, e2, e3, e4] at h1
  simp only [Bool.false_or] at h1
  rw [mem_psl29_iff, code_mul, code_inv, CFSG.QuasithinUnique.DoubleA3.tMul_code]
  exact List.contains_iff_mem.mp h1

private theorem tMul_pair_facts :
    A6Models.tAdd ^ 3 = 1 ∧
    (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) ^ 3 = 1 ∧
    A6Models.tAdd * (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) =
      (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) * A6Models.tAdd ∧
    (∀ i j i' j' : Fin 3,
      A6Models.tAdd ^ (i : ℕ) * (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) ^ (j : ℕ) =
        A6Models.tAdd ^ (i' : ℕ) * (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) ^ (j' : ℕ) →
          i = i' ∧ j = j') ∧
    A6Models.tMul * (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) * A6Models.tMul⁻¹ =
      A6Models.tAdd * (A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹) ^ 2 := by
  decide +kernel

end PGL

section Center

variable {X : Type} [Group X] [Finite X]

private theorem comm_central_ne_one (hX : IsHat X ↥(alternatingGroup (Fin 6)))
    (ψ' : (X ⧸ Subgroup.center X) ≃* ↥A6Models.psl29) {e₁ e₂ : P10}
    (he₁ : e₁ ∈ A6Models.psl29) (he₂ : e₂ ∈ A6Models.psl29) (h31 : e₁ ^ 3 = 1) (h32 : e₂ ^ 3 = 1)
    (hcomm : e₁ * e₂ = e₂ * e₁)
    (hinj9 : ∀ i j i' j' : Fin 3, e₁ ^ (i : ℕ) * e₂ ^ (j : ℕ) = e₁ ^ (i' : ℕ) * e₂ ^ (j' : ℕ) →
      i = i' ∧ j = j')
    {x y : X} (hψx : ψ' (QuotientGroup.mk x) = ⟨e₁, he₁⟩)
    (hψy : ψ' (QuotientGroup.mk y) = ⟨e₂, he₂⟩) :
    ⁅x, y⁆ ∈ Subgroup.center X ∧ ⁅x, y⁆ ≠ 1 := by
  have hxy : (QuotientGroup.mk x : X ⧸ Subgroup.center X) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x := by
    apply ψ'.injective
    rw [map_mul, map_mul, hψx, hψy]
    exact Subtype.ext hcomm
  have hcZ : ⁅x, y⁆ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hxy]
    group
  have hX1080 := card_of_isHat hX
  obtain ⟨hq, hZ3, -⟩ := hX
  refine ⟨hcZ, commutatorElement_ne_one_of_nine (Group.isPerfect_def.mp hq.1) hZ3
    (by rw [hX1080]; decide) ?_ ?_ hcZ fun i j i' j' h => ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    apply ψ'.injective
    rw [map_pow, hψx, map_one]
    exact Subtype.ext h31
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    apply ψ'.injective
    rw [map_pow, hψy, map_one]
    exact Subtype.ext h32
  · have h' := congrArg ψ' h
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_pow, map_mul, map_mul,
      map_pow, map_pow, map_pow, map_pow, hψx, hψy] at h'
    exact hinj9 i j i' j' (congrArg Subtype.val h')

omit [Finite X] in
private theorem inv_center_of_inv_gen (hZ3 : Nat.card (Subgroup.center X) = 3) (α : MulAut X)
    {c : X} (hcZ : c ∈ Subgroup.center X) (hc1 : c ≠ 1) (hαc : α c = c⁻¹) :
    ∀ z ∈ Subgroup.center X, α z = z⁻¹ := by
  intro z hz
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzc : (⟨z, hz⟩ : ↥(Subgroup.center X)) ∈
      Subgroup.zpowers (⟨c, hcZ⟩ : ↥(Subgroup.center X)) :=
    mem_zpowers_of_prime_card hZ3 (fun h => hc1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc
  have hk' : c ^ k = z := by
    have := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_zpow] at this
  rw [← hk', map_zpow, hαc, inv_zpow]

theorem inv_center_of_not_inner_six (hX : IsHat X ↥(alternatingGroup (Fin 6))) (α : MulAut X)
    (hα2 : α * α = 1) (hout : ∀ y : X, α ≠ MulAut.conj y) :
    ∀ z ∈ Subgroup.center X, α z = z⁻¹ := by
  have hX' := hX
  obtain ⟨hq, hZ3, ⟨θ⟩⟩ := hX'
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hq.1
  have hZα : (Subgroup.center X).map (α : X →* X) = Subgroup.center X :=
    Subgroup.map_center_eq α
  let αb : (X ⧸ Subgroup.center X) ≃* (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) α hZα
  have hαb : ∀ x : X, αb (QuotientGroup.mk x) = QuotientGroup.mk (α x) := fun x =>
    QuotientGroup.congr_mk (Subgroup.center X) (Subgroup.center X) α hZα x
  let ψ' : (X ⧸ Subgroup.center X) ≃* ↥A6Models.psl29 := θ.trans psiEquiv.symm
  let Γ : AutA6 ≃* MulAut ↥A6Models.psl29 := MulEquiv.ofBijective conjHom
    ⟨CFSG.QuasithinUnique.DoubleA3.conjAut_injective,
      CFSG.QuasithinUnique.DoubleA3.conjAut_surjective⟩
  let β : MulAut ↥A6Models.psl29 := MulAut.congr ψ' αb
  let b : AutA6 := Γ.symm β
  have hΓb : Γ b = β := Γ.apply_symm_apply β
  have hβ : ∀ u : X ⧸ Subgroup.center X, β (ψ' u) = ψ' (αb u) := fun u => by
    show ψ' (αb (ψ'.symm (ψ' u))) = ψ' (αb u)
    rw [MulEquiv.symm_apply_apply]
  have hbp : ∀ u : X ⧸ Subgroup.center X, ((ψ' (αb u) : ↥A6Models.psl29) : P10) =
      (b : P10) * (ψ' u : P10) * (b : P10)⁻¹ := fun u => by
    rw [← hβ, ← hΓb]
    rfl
  have hαb2 : αb * αb = 1 := by
    refine MulEquiv.ext fun u => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    show αb (αb (QuotientGroup.mk x)) = QuotientGroup.mk x
    rw [hαb, hαb]
    have := congrArg (fun f : MulAut X => f x) hα2
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [this]
  have hb2 : (b : P10) * (b : P10) = 1 := by
    have h1 : Γ (b * b) = Γ 1 := by
      rw [map_mul, map_one, hΓb]
      refine MulEquiv.ext fun p => ?_
      obtain ⟨u, rfl⟩ := ψ'.surjective p
      show β (β (ψ' u)) = ψ' u
      rw [hβ, hβ]
      show ψ' ((αb * αb) u) = ψ' u
      rw [hαb2, MulAut.one_apply]
    have h2 := Γ.injective h1
    exact congrArg Subtype.val h2
  have hbpsl : (b : P10) ∉ A6Models.psl29 := by
    intro hbm
    obtain ⟨y, hy'⟩ := QuotientGroup.mk_surjective (ψ'.symm ⟨(b : P10), hbm⟩)
    apply hout y
    refine eq_conj_of_mk_eq hperf α y fun x => ?_
    apply ψ'.injective
    apply Subtype.ext
    rw [← hαb, hbp, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy',
      map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hb1 : (b : P10) ≠ 1 := fun h => hbpsl (h ▸ Subgroup.one_mem _)
  by_cases hs6 : (b : P10) ∈ s6
  ·
    obtain ⟨e₁, he₁, e₂, he₂, h31, h32, hcomm, hinj9, hinv, hfix⟩ :=
      exists_s6_pair b.2 hb2 hb1 hbpsl hs6
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ'.symm ⟨e₁, he₁⟩)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ψ'.symm ⟨e₂, he₂⟩)
    have hψx : ψ' (QuotientGroup.mk x) = ⟨e₁, he₁⟩ := by rw [hx, MulEquiv.apply_symm_apply]
    have hψy : ψ' (QuotientGroup.mk y) = ⟨e₂, he₂⟩ := by rw [hy, MulEquiv.apply_symm_apply]
    have hαx : (QuotientGroup.mk (α x) : X ⧸ Subgroup.center X) = QuotientGroup.mk x⁻¹ := by
      rw [← hαb]
      apply ψ'.injective
      apply Subtype.ext
      rw [hbp, hψx, QuotientGroup.mk_inv, map_inv, hψx]
      exact hinv
    have hαy : (QuotientGroup.mk (α y) : X ⧸ Subgroup.center X) = QuotientGroup.mk y := by
      rw [← hαb]
      apply ψ'.injective
      apply Subtype.ext
      rw [hbp, hψy]
      exact hfix
    have hz₁ : x * α x ∈ Subgroup.center X := by
      have := QuotientGroup.eq.mp hαx.symm
      rwa [inv_inv] at this
    have hz₂ : y⁻¹ * α y ∈ Subgroup.center X := QuotientGroup.eq.mp hαy.symm
    obtain ⟨hcZ, hc1⟩ := comm_central_ne_one hX ψ' he₁ he₂ h31 h32 hcomm hinj9 hψx hψy
    have hαc : α ⁅x, y⁆ = ⁅x, y⁆⁻¹ := by
      rw [map_commutatorElement]
      have e1 : α x = x⁻¹ * (x * α x) := by group
      have e2 : α y = y * (y⁻¹ * α y) := by group
      rw [e1, e2, commutator_mul_central_left hz₁, commutator_mul_central_right hz₂,
        commutator_inv_left_of_central hcZ]
    exact inv_center_of_inv_gen hZ3 α hcZ hc1 hαc
  ·
    have hp : (b : P10)⁻¹ * A6Models.tMul ∈ A6Models.psl29 := pgl_coset b.2 hb2 hb1 hbpsl hs6
    obtain ⟨p, hp'⟩ := QuotientGroup.mk_surjective (ψ'.symm ⟨_, hp⟩)
    have hβmod : ∀ x : X,
        ((ψ' (QuotientGroup.mk (α (p * x * p⁻¹))) : ↥A6Models.psl29) : P10) =
          A6Models.tMul * (ψ' (QuotientGroup.mk x) : P10) * A6Models.tMul⁻¹ := fun x => by
      rw [← hαb, hbp, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
        map_mul, map_inv, hp', MulEquiv.apply_symm_apply]
      show (b : P10) * ((b : P10)⁻¹ * A6Models.tMul * (ψ' (QuotientGroup.mk x) : P10) *
          ((b : P10)⁻¹ * A6Models.tMul)⁻¹) * (b : P10)⁻¹ =
        A6Models.tMul * (ψ' (QuotientGroup.mk x) : P10) * A6Models.tMul⁻¹
      group
    obtain ⟨h31, h32, hcomm, hinj9, hconj⟩ := tMul_pair_facts
    have he₁ : A6Models.tAdd ∈ A6Models.psl29 := Subgroup.subset_closure (by simp)
    have he₂ : A6Models.tMul * A6Models.tAdd * A6Models.tMul⁻¹ ∈ A6Models.psl29 :=
      psl29_normal _ CFSG.QuasithinUnique.DoubleA3.tMul_mem _ he₁
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ'.symm ⟨_, he₁⟩)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ψ'.symm ⟨_, he₂⟩)
    have hψx : ψ' (QuotientGroup.mk x) = ⟨_, he₁⟩ := by rw [hx, MulEquiv.apply_symm_apply]
    have hψy : ψ' (QuotientGroup.mk y) = ⟨_, he₂⟩ := by rw [hy, MulEquiv.apply_symm_apply]
    have hβx : (QuotientGroup.mk (α (p * x * p⁻¹)) : X ⧸ Subgroup.center X) =
        QuotientGroup.mk y := by
      apply ψ'.injective
      apply Subtype.ext
      rw [hβmod, hψx, hψy]
    have hβy : (QuotientGroup.mk (α (p * y * p⁻¹)) : X ⧸ Subgroup.center X) =
        QuotientGroup.mk (x * y ^ 2) := by
      apply ψ'.injective
      apply Subtype.ext
      rw [hβmod, QuotientGroup.mk_mul, QuotientGroup.mk_pow, map_mul, map_pow, hψx, hψy]
      exact hconj
    have hw₁ : y⁻¹ * α (p * x * p⁻¹) ∈ Subgroup.center X := QuotientGroup.eq.mp hβx.symm
    have hw₂ : (x * y ^ 2)⁻¹ * α (p * y * p⁻¹) ∈ Subgroup.center X :=
      QuotientGroup.eq.mp hβy.symm
    obtain ⟨hcZ, hc1⟩ := comm_central_ne_one hX ψ' he₁ he₂ h31 h32 hcomm hinj9 hψx hψy
    have hαc : α ⁅x, y⁆ = ⁅x, y⁆⁻¹ := by
      have h1 : α (p * ⁅x, y⁆ * p⁻¹) = α ⁅x, y⁆ := by
        rw [Subgroup.mem_center_iff.mp hcZ p, mul_inv_cancel_right]
      have h2 : p * ⁅x, y⁆ * p⁻¹ = ⁅p * x * p⁻¹, p * y * p⁻¹⁆ :=
        map_commutatorElement (MulAut.conj p) x y
      rw [← h1, h2, map_commutatorElement]
      have e1 : α (p * x * p⁻¹) = y * (y⁻¹ * α (p * x * p⁻¹)) := by group
      have e2 : α (p * y * p⁻¹) = (x * y ^ 2) * ((x * y ^ 2)⁻¹ * α (p * y * p⁻¹)) := by group
      rw [e1, e2, commutator_mul_central_left hw₁, commutator_mul_central_right hw₂]
      simp only [commutatorElement_def]
      group
    exact inv_center_of_inv_gen hZ3 α hcZ hc1 hαc

end Center

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

end
