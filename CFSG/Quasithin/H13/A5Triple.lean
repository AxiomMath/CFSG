module

public import CFSG.Quasithin.H13.A5TripleData
public import CFSG.Quasithin.H13.A5RowsAlt
public import CFSG.Quasithin.H13.A5Semilinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
open Equiv
open scoped commutatorElement

theorem alt6_inv_pair : ∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 → Perm.sign σ = 1 →
    ∃ τ : Perm (Fin 6), Perm.sign τ = 1 ∧ (σ * (τ * σ * τ⁻¹)) ^ 5 = 1 ∧
      σ * (τ * σ * τ⁻¹) ≠ 1 := by
  decide +kernel

section Ext

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_conj_of_mk_eq (hperf : commutator X = ⊤) (α : MulAut X) (y : X)
    (h : ∀ x : X,
      (QuotientGroup.mk (α x) : X ⧸ Subgroup.center X) = QuotientGroup.mk (y * x * y⁻¹)) :
    α = MulAut.conj y := by
  have hc : ∀ x : X, (y * x * y⁻¹)⁻¹ * α x ∈ Subgroup.center X := fun x =>
    QuotientGroup.eq.mp (h x).symm
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨(y * x * y⁻¹)⁻¹ * α x, hc x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show (y * (a * b) * y⁻¹)⁻¹ * α (a * b) =
          (y * a * y⁻¹)⁻¹ * α a * ((y * b * y⁻¹)⁻¹ * α b)
        have hza := Subgroup.mem_center_iff.mp (hc a)
        rw [map_mul]
        calc (y * (a * b) * y⁻¹)⁻¹ * (α a * α b)
            = (y * b * y⁻¹)⁻¹ * ((y * a * y⁻¹)⁻¹ * α a) * α b := by group
          _ = ((y * a * y⁻¹)⁻¹ * α a) * (y * b * y⁻¹)⁻¹ * α b := by
              rw [hza ((y * b * y⁻¹)⁻¹)]
          _ = (y * a * y⁻¹)⁻¹ * α a * ((y * b * y⁻¹)⁻¹ * α b) := by group }
  have hf : ∀ x, f x = 1 := by
    intro x
    have hx : x ∈ commutator X := hperf ▸ Subgroup.mem_top x
    have hle : commutator X ≤ f.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.mp (f b).2 (f a : X))
    exact MonoidHom.mem_ker.mp (hle hx)
  refine MulEquiv.ext fun x => ?_
  have h1 : (y * x * y⁻¹)⁻¹ * α x = 1 := congrArg Subtype.val (hf x)
  rw [MulAut.conj_apply]
  calc α x = (y * x * y⁻¹) * ((y * x * y⁻¹)⁻¹ * α x) := by group
    _ = y * x * y⁻¹ := by rw [h1, mul_one]

omit [Finite X] in
theorem commutator_mul_central_left {a b z : X} (hz : z ∈ Subgroup.center X) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite X] in
theorem commutator_mul_central_right {a b z : X} (hz : z ∈ Subgroup.center X) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite X] in
theorem commutator_inv_left_of_central {x y : X} (hc : ⁅x, y⁆ ∈ Subgroup.center X) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have h := Subgroup.mem_center_iff.mp hc
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  rw [commutatorElement_def]
  calc x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (⁅x, y⁆⁻¹ * (x * y * x⁻¹)) * x * y⁻¹ := by
        rw [h1]; group
    _ = ⁅x, y⁆⁻¹ * (x⁻¹ * (x * y * x⁻¹) * x) * y⁻¹ := by
        have h2 := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc)
        rw [← mul_assoc x⁻¹, h2 x⁻¹]
        group
    _ = ⁅x, y⁆⁻¹ := by group

theorem false_of_transfer (hperf : commutator X = ⊤) (A : Subgroup X) (hA : IsMulCommutative A)
    {z : X} (hzZ : z ∈ Subgroup.center X) (hpow : z ^ A.index ≠ 1) : False := by
  let _ : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hA.is_comm.comm }
  have : A.FiniteIndex := Subgroup.finiteIndex_of_finite
  let t : X →* ↥A := MonoidHom.transfer (MonoidHom.id ↥A)
  have ht := MonoidHom.transfer_eq_pow (MonoidHom.id ↥A) z (fun k g₀ _ => by
    have hzk : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hzZ k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hzk g₀, ← mul_assoc, inv_mul_cancel, one_mul])
  have ht1 : t z = 1 := by
    have hz : z ∈ commutator X := hperf ▸ Subgroup.mem_top z
    have hle : commutator X ≤ t.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.mp (hle hz)
  have h2 : MonoidHom.transfer (MonoidHom.id ↥A) z = 1 := ht1
  rw [ht] at h2
  exact hpow (congrArg Subtype.val h2)

omit [Finite X] in
theorem injective_27 {x y z : X} (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (h9 : ∀ i j i' j' : Fin 3, (QuotientGroup.mk (x ^ (i : ℕ) * y ^ (j : ℕ)) :
      X ⧸ Subgroup.center X) = QuotientGroup.mk (x ^ (i' : ℕ) * y ^ (j' : ℕ)) →
        i = i' ∧ j = j') :
    Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
      x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * z ^ (t.2.2 : ℕ) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  simp only at h
  have hzk : ∀ m : ℕ, z ^ m ∈ Subgroup.center X := fun m => Subgroup.pow_mem _ hz m
  have hm : ∀ (a : X) (m : ℕ), (QuotientGroup.mk (a * z ^ m) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk a := fun a m => by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (hzk m), mul_one]
  have h1 : (QuotientGroup.mk (x ^ (i : ℕ) * y ^ (j : ℕ)) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (x ^ (i' : ℕ) * y ^ (j' : ℕ)) := by
    rw [← hm _ k, h, hm]
  obtain ⟨hi, hj⟩ := h9 i j i' j' h1
  subst hi
  subst hj
  have h2 : z ^ (k : ℕ) = z ^ (k' : ℕ) := mul_left_cancel h
  have h3 := pow_inj_mod.mp h2
  rw [hz3, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h3
  exact Prod.ext rfl (Prod.ext rfl (Fin.ext h3))


omit [Finite X] in
theorem card_of_isHat (hX : IsHat X ↥(alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  obtain ⟨-, hZ3, ⟨θ⟩⟩ := hX
  have h1 := (Subgroup.center X).card_mul_index
  rw [hZ3, Subgroup.index, Nat.card_congr θ.toEquiv, nat_card_alternatingGroup,
    Nat.card_fin] at h1
  exact h1.symm.trans (by decide)

theorem inv_center_of_outer (hX : IsHat X ↥(alternatingGroup (Fin 6))) (α : MulAut X)
    (hα2 : α * α = 1) (hout : ∀ y : X, α ≠ MulAut.conj y) (S : Subgroup X)
    (hS : Nat.card S = 8) (hSα : ∀ s ∈ S, α s = s) :
    ∀ z ∈ Subgroup.center X, α z = z⁻¹ := by
  have hX1080 := card_of_isHat hX
  obtain ⟨hq, hZ3, ⟨θ⟩⟩ := hX
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hq.1
  have hZpow : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center X))
    rw [hZ3] at this
    have h := orderOf_dvd_iff_pow_eq_one.mp this
    exact congrArg Subtype.val h
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
    have hαc : α ⁅x, y⁆ = ⁅x, y⁆⁻¹ := by
      rw [map_commutatorElement]
      have e1 : α x = x⁻¹ * (x * α x) := by group
      have e2 : α y = y * (y⁻¹ * α y) := by group
      rw [e1, e2, commutator_mul_central_left hz₁, commutator_mul_central_right hz₂,
        commutator_inv_left_of_central hcZ]
    have hc1 : ⁅x, y⁆ ≠ 1 := by
      intro hc
      have hxy' : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.mp hc
      obtain ⟨⟨z₀, hz₀⟩, hz₀1'⟩ : ∃ z₀ : ↥(Subgroup.center X), z₀ ≠ 1 := by
        by_contra h
        push Not at h
        have : Nat.card ↥(Subgroup.center X) = 1 := Nat.card_eq_one_iff_unique.mpr
          ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
        omega
      have hz₀1 : z₀ ≠ 1 := fun h => hz₀1' (Subtype.ext h)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hz₀3 : orderOf z₀ = 3 := orderOf_eq_prime (hZpow z₀ hz₀) hz₀1
      have hcommA : ({x, y} ∪ (Subgroup.center X : Set X)).Pairwise Commute := by
        intro a ha c hc _
        rcases ha with ha | ha <;> rcases hc with hc | hc
        · rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
          · exact Commute.refl _
          · exact hxy'
          · exact hxy'.symm
          · exact Commute.refl _
        · exact (Subgroup.mem_center_iff.mp hc a)
        · exact (Subgroup.mem_center_iff.mp ha c).symm
        · exact (Subgroup.mem_center_iff.mp hc a)
      have hAc := Subgroup.isMulCommutative_closure hcommA
      obtain ⟨A, hA, hA9, hxA, hyA, hzA⟩ : ∃ A : Subgroup X, IsMulCommutative A ∧
          (∀ a ∈ A, a ^ 9 = 1) ∧ x ∈ A ∧ y ∈ A ∧ z₀ ∈ A := by
        have hx9 : x ^ 9 = 1 := by
          have h1 : x ^ 3 ∈ Subgroup.center X := by
            rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
            apply ψ'.injective
            rw [map_pow, hψx, map_one]
            exact Subtype.ext h31
          rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZpow _ h1]
        have hy9 : y ^ 9 = 1 := by
          have h1 : y ^ 3 ∈ Subgroup.center X := by
            rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
            apply ψ'.injective
            rw [map_pow, hψy, map_one]
            exact Subtype.ext h32
          rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZpow _ h1]
        refine ⟨Subgroup.closure ({x, y} ∪ (Subgroup.center X : Set X)), hAc, ?_,
          Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_insert x {y})),
          Subgroup.subset_closure
            (Set.mem_union_left _ (Set.mem_insert_of_mem x (Set.mem_singleton y))),
          Subgroup.subset_closure (Set.mem_union_right _ hz₀)⟩
        intro a ha
        induction ha using Subgroup.closure_induction with
        | mem a ha =>
          rcases ha with ha | ha
          · rcases ha with rfl | rfl
            · exact hx9
            · exact hy9
          · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZpow _ ha, one_pow]
        | one => exact one_pow 9
        | mul a c ha hc iha ihc =>
          have hac : Commute a c := by
            have := hAc.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩
            exact congrArg Subtype.val this
          rw [hac.mul_pow, iha, ihc, one_mul]
        | inv a ha iha => rw [inv_pow, iha, inv_one]
      have hAp : IsPGroup 3 A := fun a => ⟨2, Subtype.ext (by simpa using hA9 a a.2)⟩
      have hge : 27 ≤ Nat.card A := by
        have hinj := injective_27 (x := x) (y := y) hz₀ hz₀3 fun i j i' j' h => by
          have h' := congrArg ψ' h
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
            QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_pow, map_mul, map_mul,
            map_pow, map_pow, map_pow, map_pow, hψx, hψy] at h'
          exact hinj9 i j i' j' (congrArg Subtype.val h')
        have hmemA : ∀ t : Fin 3 × Fin 3 × Fin 3,
            x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * z₀ ^ (t.2.2 : ℕ) ∈ A := fun t =>
          A.mul_mem (A.mul_mem (A.pow_mem hxA _) (A.pow_mem hyA _)) (A.pow_mem hzA _)
        have h1 := Nat.card_le_card_of_injective
          (fun t => (⟨_, hmemA t⟩ : ↥A)) (fun t t' h => hinj (congrArg Subtype.val h))
        rw [Nat.card_eq_fintype_card (α := Fin 3 × Fin 3 × Fin 3)] at h1
        simpa using h1
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
      have hdvd : 3 ^ m ∣ 1080 := by
        rw [← hm, ← hX1080]
        exact Subgroup.card_subgroup_dvd_card A
      have hm3 : m = 3 := by
        have hm4 : m < 4 := by
          by_contra h
          have h81 : 81 ∣ 1080 := (Nat.pow_dvd_pow 3 (by omega : 4 ≤ m)).trans hdvd
          omega
        rw [hm] at hge
        interval_cases m <;> first | rfl | (norm_num at hge)
      have hidx : A.index = 40 := by
        have h1 := A.card_mul_index
        rw [hm, hm3, hX1080] at h1
        norm_num at h1
        omega
      apply false_of_transfer hperf A hA hz₀
      rw [hidx]
      intro h40
      apply hz₀1
      have : z₀ ^ 40 = z₀ ^ (3 * 13 + 1) := rfl
      rw [this, pow_succ, pow_mul, hZpow z₀ hz₀, one_pow, one_mul] at h40
      exact h40
    intro z hz
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hzc : (⟨z, hz⟩ : ↥(Subgroup.center X)) ∈
        Subgroup.zpowers (⟨⁅x, y⁆, hcZ⟩ : ↥(Subgroup.center X)) :=
      mem_zpowers_of_prime_card hZ3 (fun h => hc1 (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc
    have hk' : ⁅x, y⁆ ^ k = z := by
      have := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_zpow] at this
    rw [← hk', map_zpow, hαc, inv_zpow]
  ·
    exfalso
    have h10 := card_psl29_centralizer_of_not_mem b.2 hb2 hb1 hbpsl hs6
    let f : ↥S →* P10 := A6Models.psl29.subtype.comp
      (ψ'.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center X)).comp S.subtype))
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker] at hs
      have h1 : (s : X) ∈ Subgroup.center X := by
        have h2 : ψ' (QuotientGroup.mk (s : X)) = 1 := Subtype.ext hs
        rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
        exact h2
      have h3 : orderOf (s : X) ∣ 3 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact hZpow _ h1
      have h4 : orderOf s ∣ 8 := hS ▸ orderOf_dvd_natCard s
      rw [Subgroup.orderOf_coe] at h3
      have h5 : orderOf s ∣ Nat.gcd 3 8 := Nat.dvd_gcd h3 h4
      rw [show Nat.gcd 3 8 = 1 from rfl, Nat.dvd_one, orderOf_eq_one_iff] at h5
      exact (Subgroup.mem_bot).mpr h5
    have hrange : f.range ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({(b : P10)} : Set P10) := by
      rintro _ ⟨s, rfl⟩
      refine ⟨(ψ' (QuotientGroup.mk (s : X))).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := hbp (QuotientGroup.mk (s : X))
      rw [hαb, hSα s s.2] at h1
      show (ψ' (QuotientGroup.mk (s : X)) : P10) * (b : P10) =
        (b : P10) * (ψ' (QuotientGroup.mk (s : X)) : P10)
      calc (ψ' (QuotientGroup.mk (s : X)) : P10) * (b : P10)
          = ((b : P10) * (ψ' (QuotientGroup.mk (s : X)) : P10) * (b : P10)⁻¹) * (b : P10) := by
            rw [← h1]
        _ = (b : P10) * (ψ' (QuotientGroup.mk (s : X)) : P10) := by group
    have h8 : Nat.card f.range = 8 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, hS]
    have := Subgroup.card_dvd_of_le hrange
    rw [h8, h10] at this
    omega

end Ext


section Fact

variable {V : Type} [CommGroup V] [Finite V]

theorem factTripleA6Row1321 : FactTripleA6Row1321 := by
  intro V _ _ hV G L A v hB4 hc h8
  obtain ⟨-, hcardV, -, K, _, _, Γ₀, hK4, -, hHat, hcent, π, hπ, -⟩ := h8
  have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB4.2.1 ▸ le_normalizer_quasithinGenFitting G
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let eπ : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hHatL : IsHat ↥L ↥(alternatingGroup (Fin 6)) := IsHat.of_mulEquiv eπ hHat
  have hL1080 : Nat.card ↥L = 1080 := card_of_isHat hHatL
  obtain ⟨E₀, hE₀⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.nat Γ₀) rfl hπ
  let E : V ≃* Multiplicative (Fin 3 → K) := E₀.trans Subgroup.topEquiv
  have hE : ∀ (γ : ↥Γ₀) (w : V), Multiplicative.toAdd (E (((π γ : ↥L) : MulAut V) w)) =
      ((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd (E w)) := fun γ w => congrArg Multiplicative.toAdd (hE₀ γ w)
  have hHatL' := hHatL
  obtain ⟨-, hZ3, ⟨θL⟩⟩ := hHatL'
  obtain ⟨z₀, hz₀1⟩ : ∃ z₀ : ↥(Subgroup.center ↥L), z₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card ↥(Subgroup.center ↥L) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  have hz₀3 : (z₀ : ↥L) ^ 3 = 1 := by
    have := orderOf_dvd_natCard z₀
    rw [hZ3] at this
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp this)
  have hz₀ne : (z₀ : ↥L) ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hzΓ : eπ.symm (z₀ : ↥L) ∈ Subgroup.center ↥Γ₀ :=
    Subgroup.mem_center_iff.mpr fun h => eπ.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp z₀.2 (eπ h))
  obtain ⟨c, hcγ⟩ := hcent _ hzΓ
  have hact : ∀ w : V, Multiplicative.toAdd (E (((z₀ : ↥L) : MulAut V) w)) =
      c • Multiplicative.toAdd (E w) := by
    intro w
    have h1 := hE (eπ.symm (z₀ : ↥L)) w
    have h2 : π (eπ.symm (z₀ : ↥L)) = (z₀ : ↥L) := eπ.apply_symm_apply _
    rw [h2, hcγ, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    exact h1
  have hc1 : c ≠ 1 := by
    intro h1
    apply hz₀ne
    have h2 : eπ.symm (z₀ : ↥L) = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hcγ, h1, one_smul]
      rfl
    exact (MulEquiv.map_eq_one_iff eπ.symm).mp h2
  have hc3 : c ^ 3 = 1 := by
    have h1 : (eπ.symm (z₀ : ↥L)) ^ 3 = 1 := by rw [← map_pow, hz₀3, map_one]
    have h2 := congrArg (fun g : ↥Γ₀ =>
      (((g : Matrix.GeneralLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcγ, smul_pow, one_pow,
      Matrix.smul_apply, Matrix.one_apply_eq, Subgroup.coe_one, Units.val_one, smul_eq_mul,
      mul_one] at h2
    exact h2
  have hc2 : c ^ 2 = c + 1 := by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK4]; norm_num
    have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
    have h1 : (c - 1) * (c ^ 2 + c + 1) = c ^ 3 - 1 := by ring
    rw [hc3, sub_self] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hc1
    · have h2 : c ^ 2 = -(c + 1) := by linear_combination h
      rw [h2, neg_add, CharTwo.neg_eq, CharTwo.neg_eq]
  have hsc : ∀ w : V, ((z₀ : ↥L) : MulAut V) (((z₀ : ↥L) : MulAut V) w) =
      ((z₀ : ↥L) : MulAut V) w * w := by
    intro w
    apply E.injective
    apply Multiplicative.toAdd.injective
    rw [hact, hact, map_mul E, toAdd_mul, hact, smul_smul, ← pow_two, hc2, add_smul, one_smul]
  obtain ⟨S, hS, hSv⟩ := hc.sylow
  have hS8 : Nat.card (S.subgroupOf L) = 8 :=
    card_sylowTwoOf_eq hS (n := 3) (m := 135) (by norm_num) (hL1080.trans (by norm_num))
  by_cases hvL : v ∈ L
  ·
    let q : ↥L →* ↥(alternatingGroup (Fin 6)) :=
      θL.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hq : Function.Surjective q :=
      θL.surjective.comp (QuotientGroup.mk'_surjective _)
    set σ : Perm (Fin 6) := (q ⟨v, hvL⟩ : Perm (Fin 6)) with hσ
    have hσ2 : σ * σ = 1 := by
      have h1 : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := Subtype.ext hc.sq
      rw [hσ, ← Subgroup.coe_mul, ← map_mul, h1, map_one, Subgroup.coe_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      have h2 : q ⟨v, hvL⟩ = 1 := Subtype.ext h1
      have h3 : (⟨v, hvL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        have : QuotientGroup.mk' (Subgroup.center ↥L) ⟨v, hvL⟩ = 1 :=
          θL.injective (h2.trans (map_one θL).symm)
        exact (QuotientGroup.eq_one_iff _).mp this
      have h4 := orderOf_dvd_natCard (⟨⟨v, hvL⟩, h3⟩ : ↥(Subgroup.center ↥L))
      rw [hZ3, Subgroup.orderOf_mk] at h4
      have h6 : orderOf (⟨v, hvL⟩ : ↥L) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by
          rw [Subgroup.coe_pow, pow_two]; exact hc.sq))
      have h7 : orderOf (⟨v, hvL⟩ : ↥L) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h4 h6
      rw [show Nat.gcd 3 2 = 1 from rfl, Nat.dvd_one, orderOf_eq_one_iff] at h7
      exact hc.ne_one (congrArg Subtype.val h7)
    obtain ⟨τ, hτ, hx5, hx1⟩ :=
      alt6_inv_pair σ hσ2 hσ1 (Perm.mem_alternatingGroup.mp (q ⟨v, hvL⟩).2)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hord : orderOf (σ * (τ * σ * τ⁻¹)) = 5 := orderOf_eq_prime hx5 hx1
    obtain ⟨g, hg⟩ := hq ⟨τ, Perm.mem_alternatingGroup.mpr hτ⟩
    have hmap : ∀ m : ℕ, (v * ((g : MulAut V) * v * (g : MulAut V)⁻¹)) ^ m = 1 →
        (σ * (τ * σ * τ⁻¹)) ^ m = 1 := by
      intro m hm
      have h1 : ((⟨v, hvL⟩ : ↥L) * (g * ⟨v, hvL⟩ * g⁻¹)) ^ m = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hm)
      have h2 := congrArg (fun x => ((q x : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))) h1
      simp only [map_pow, map_mul, map_inv, hg, map_one, Subgroup.coe_pow, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_one] at h2
      exact h2
    rcases hc.pair g (hLG g.2) with ⟨k, hk⟩ | h3
    · have h := orderOf_dvd_of_pow_eq_one (hmap _ hk)
      rw [hord] at h
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)
    · have h := orderOf_dvd_of_pow_eq_one (hmap _ h3)
      rw [hord] at h
      exact absurd h (by norm_num)
  ·
    let vG : ↥G := ⟨v, hc.mem⟩
    let α : MulAut ↥L := conjOnL hGL vG
    have hα : ∀ l : ↥L, ((α l : ↥L) : MulAut V) = v * (l : MulAut V) * v⁻¹ :=
      fun l => conjOnL_apply_coe hGL vG l
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hc.sq
    have hα2 : α * α = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      show ((α (α l) : ↥L) : MulAut V) = (l : MulAut V)
      rw [hα, hα, hvi]
      calc v * (v * (l : MulAut V) * v) * v = (v * v) * (l : MulAut V) * (v * v) := by group
        _ = (l : MulAut V) := by rw [hc.sq, one_mul, mul_one]
    have hout : ∀ y : ↥L, α ≠ MulAut.conj y := by
      intro y hy
      apply hvL
      have h1 : conjOnL hGL (vG * ⟨y, hLG y.2⟩⁻¹) = 1 := by
        refine MulEquiv.ext fun l => Subtype.ext ?_
        rw [conjOnL_apply_coe]
        show v * (y : MulAut V)⁻¹ * (l : MulAut V) * (v * (y : MulAut V)⁻¹)⁻¹ = (l : MulAut V)
        have h2 := congrArg (fun φ : MulAut ↥L => ((φ (y⁻¹ * l * y) : ↥L) : MulAut V)) hy
        simp only [hα, MulAut.conj_apply] at h2
        have h4 : ((y * (y⁻¹ * l * y) * y⁻¹ : ↥L) : MulAut V) = (l : MulAut V) := by
          rw [show y * (y⁻¹ * l * y) * y⁻¹ = l by group]
        have h3 : v * ((y : MulAut V)⁻¹ * (l : MulAut V) * (y : MulAut V)) * v⁻¹ =
            (l : MulAut V) := h2.trans h4
        calc v * (y : MulAut V)⁻¹ * (l : MulAut V) * (v * (y : MulAut V)⁻¹)⁻¹
            = v * ((y : MulAut V)⁻¹ * (l : MulAut V) * (y : MulAut V)) * v⁻¹ := by group
          _ = (l : MulAut V) := h3
      have h2 := mem_of_conjOnL_eq_one hB4 hGL h1
      have h3 : v * (y : MulAut V)⁻¹ ∈ L := h2
      have h4 := L.mul_mem h3 y.2
      simpa using h4
    have hSα : ∀ s ∈ S.subgroupOf L, α s = s := by
      intro s hs
      apply Subtype.ext
      rw [hα]
      have hsv : (s : MulAut V) * v = v * (s : MulAut V) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hSv (Subgroup.mem_subgroupOf.mp hs))
      rw [← hsv, mul_assoc, mul_inv_cancel, mul_one]
    have hinvZ := inv_center_of_outer hHatL α hα2 hout (S.subgroupOf L) hS8 hSα
      (z₀ : ↥L) z₀.2
    have hvz : v * ((z₀ : ↥L) : MulAut V) * v⁻¹ = ((z₀ : ↥L) : MulAut V)⁻¹ := by
      rw [← hα, hinvZ, Subgroup.coe_inv]
    have hθ : ∀ w : V, v (((z₀ : ↥L) : MulAut V) w) =
        ((z₀ : ↥L) : MulAut V) (v w) * v w := by
      intro w
      have h1 : v * ((z₀ : ↥L) : MulAut V) = ((z₀ : ↥L) : MulAut V)⁻¹ * v := by
        rw [← hvz]; group
      have h2 : ((z₀ : ↥L) : MulAut V)⁻¹ = ((z₀ : ↥L) : MulAut V) * ((z₀ : ↥L) : MulAut V) := by
        have h3 : ((z₀ : ↥L) : MulAut V) ^ 3 = 1 := by
          rw [← Subgroup.coe_pow, hz₀3, Subgroup.coe_one]
        rw [inv_eq_iff_mul_eq_one, ← pow_three, h3]
      have h4 := congrArg (fun f : MulAut V => f w) h1
      simp only [MulAut.mul_apply] at h4
      rw [h4, h2, MulAut.mul_apply, hsc]
    have hidx := index_fixV_of_semilinear hV ((z₀ : ↥L) : MulAut V).toMonoidHom v hc.sq hθ
      (k := 3) (hcardV.trans (by norm_num))
    have hrk := hc.rank
    unfold rkIdx at hrk
    rw [hidx, padicValNat.prime_pow] at hrk
    omega

end Fact

end CFSG.Quasithin.H13.A5
