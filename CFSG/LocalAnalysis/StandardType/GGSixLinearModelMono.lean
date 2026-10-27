module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace LinModel

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem eq_of_diagGL_eq_scalar {d : Fin (m + 1) → Fˣ} {c : Fˣ}
    (h : InnerDiagA.diagGL d = GeneralLinearGroup.scalar (Fin (m + 1)) c) (i : Fin (m + 1)) :
    d i = c := by
  have := congrArg (fun A : GL (Fin (m + 1)) F => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) h
  simp only [diagGL_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_apply_eq] at this
  exact Units.ext this

theorem le_rootTorus [CharP F 2] {p : ℕ}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {Bs : Subgroup G} (hBsD : ∀ b ∈ Bs, ∃ d : Fin (m + 1) → Fˣ,
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ)
    (hexp : ∀ b ∈ Bs, b ^ p = 1) : Bs ≤ rootTorus p ψ := by
  intro b hb
  obtain ⟨d, hd⟩ := hBsD b hb
  have h1 := (LinFusion.ggInducedPairs ψ).pow_mem hd p
  rw [Prod.pow_mk, hexp b hb, ← diagGL_pow] at h1
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1
  have hent : ∀ i, d i ^ p = c := fun i => eq_of_diagGL_eq_scalar hc i
  refine ⟨fun i => (d 0)⁻¹ * d i, fun i => ?_, ?_⟩
  · rw [mul_pow, inv_pow, hent, hent, inv_mul_cancel]
  · have h2 := scalar_mul_mem_ggInducedPairs hd (d 0)⁻¹
    rwa [scalar_mul_diagGL] at h2

theorem eq_of_ne_zero_of_mem_normalizer [CharP F 2] {p : ℕ}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {ω : Fˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ)
    {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs) {u : G}
    (hu : u ∈ Subgroup.normalizer (Bs : Set G)) {A : GL (Fin (m + 1)) F}
    (hA : (u, A) ∈ LinFusion.ggInducedPairs ψ) {i l l' : Fin (m + 1)}
    (hl : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l i ≠ 0)
    (hl' : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l' i ≠ 0) : l = l' := by
  by_contra hne
  obtain ⟨g, hg⟩ := hreal l
  have hgBs : g ∈ Bs := by
    rw [← hBs]
    refine ⟨_, fun k => ?_, hg⟩
    by_cases hk : k = l
    · rw [hk, Pi.mulSingle_eq_same, hωp]
    · rw [Pi.mulSingle_eq_of_ne hk, one_pow]
  have hbBs : u⁻¹ * g * u ∈ Bs := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) g).mp hgBs
    rwa [inv_inv] at this
  rw [← hBs] at hbBs
  obtain ⟨d, -, hbd⟩ := hbBs
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem ((LinFusion.ggInducedPairs ψ).mul_mem hA hbd)
    ((LinFusion.ggInducedPairs ψ).inv_mem hA)
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk,
    show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at h1
  obtain ⟨κ, hκ⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hg h1
  rw [scalar_mul_diagGL] at hκ
  have h2 : A * InnerDiagA.diagGL d =
      InnerDiagA.diagGL (fun k => κ * (Pi.mulSingle l ω : Fin (m + 1) → Fˣ) k) * A := by
    rw [← hκ]
    group
  have h3 := congrArg (fun X : GL (Fin (m + 1)) F => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    h2
  simp only [Units.val_mul, InnerDiagA.coe_diagGL] at h3
  have hli := congrFun (congrFun h3 l) i
  have hl'i := congrFun (congrFun h3 l') i
  rw [mul_diagonal, diagonal_mul, Pi.mulSingle_eq_same] at hli
  rw [mul_diagonal, diagonal_mul, Pi.mulSingle_eq_of_ne (Ne.symm hne), Units.val_one,
    mul_one] at hl'i
  have e1 : ((d i : Fˣ) : F) = (κ : F) * (ω : F) := mul_left_cancel₀ hl (by rw [hli]; ring)
  have e2 : ((d i : Fˣ) : F) = (κ : F) := mul_left_cancel₀ hl' (by rw [hl'i]; ring)
  apply hω1
  have e3 : (κ : F) * (ω : F) = (κ : F) * 1 := by rw [← e1, e2, mul_one]
  exact Units.ext (by rw [mul_left_cancel₀ κ.ne_zero e3, Units.val_one])

@[expose] def IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (π : Equiv.Perm (Fin (m + 1))) : Prop :=
  ∀ i l, A l i ≠ 0 ↔ l = π i

theorem IsPermOf.unique {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {π π' : Equiv.Perm (Fin (m + 1))} (h : IsPermOf A π) (h' : IsPermOf A π') : π = π' := by
  ext i
  exact congrArg Fin.val ((h' i (π i)).mp ((h i (π i)).mpr rfl))

theorem exists_isPermOf {A : GL (Fin (m + 1)) F}
    (hcol : ∀ i l l', (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l i ≠ 0 →
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l' i ≠ 0 → l = l') :
    ∃ π, IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π := by
  have hdet : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hex : ∀ i, ∃ l, (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l i ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero i h)
  choose π₀ hπ₀ using hex
  have hsurj : Function.Surjective π₀ := by
    intro k
    by_contra h
    push Not at h
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero k fun i => ?_
    by_contra hki
    exact h i (hcol i k (π₀ i) hki (hπ₀ i)).symm
  refine ⟨Equiv.ofBijective π₀ hsurj.bijective_of_finite, fun i l =>
    ⟨fun hl => hcol i l (π₀ i) hl (hπ₀ i), fun hl => ?_⟩⟩
  rw [hl]
  exact hπ₀ i

theorem IsPermOf.mul {A B : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {π π' : Equiv.Perm (Fin (m + 1))} (hA : IsPermOf A π) (hB : IsPermOf B π') :
    IsPermOf (A * B) (π * π') := by
  intro i l
  have hB0 : B (π' i) i ≠ 0 := (hB i (π' i)).mpr rfl
  rw [Matrix.mul_apply, Finset.sum_eq_single (π' i), Equiv.Perm.mul_apply, mul_ne_zero_iff,
    and_iff_left hB0, hA (π' i) l]
  · intro k _ hk
    have : B k i = 0 := by
      by_contra h
      exact hk ((hB i k).mp h)
    rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem IsPermOf.scalar_mul {A : GL (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (hA : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) (c : Fˣ) :
    IsPermOf ((GeneralLinearGroup.scalar (Fin (m + 1)) c * A : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) π := by
  intro i l
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_mul,
    mul_ne_zero_iff, and_iff_right (Units.ne_zero c), hA i l]

theorem IsPermOf.exists_eq_diagGL {A : GL (Fin (m + 1)) F}
    (hA : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 1) :
    ∃ d : Fin (m + 1) → Fˣ, A = InnerDiagA.diagGL d :=
  LinTorus.exists_eq_diagGL fun i j hij => by
    by_contra h
    exact hij ((hA j i).mp h)

theorem IsPermOf.eq_one_of_mem_centralizer [CharP F 2] {p : ℕ} (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {ω : Fˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ)
    {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs) {u : G}
    (hu : u ∈ Subgroup.centralizer (Bs : Set G)) {A : GL (Fin (m + 1)) F}
    (hA : (u, A) ∈ LinFusion.ggInducedPairs ψ) {π : Equiv.Perm (Fin (m + 1))}
    (hπ : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) : π = 1 := by
  ext i
  by_contra hπi
  have hπi' : π i ≠ i := fun h => hπi (by rw [h]; rfl)
  obtain ⟨g, hg⟩ := hreal i
  have hgBs : g ∈ Bs := by
    rw [← hBs]
    refine ⟨_, fun k => ?_, hg⟩
    by_cases hk : k = i
    · rw [hk, Pi.mulSingle_eq_same, hωp]
    · rw [Pi.mulSingle_eq_of_ne hk, one_pow]
  have hcomm : u * g * u⁻¹ = g := by
    rw [(Subgroup.mem_centralizer_iff.mp hu g hgBs).symm, mul_inv_cancel_right]
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem ((LinFusion.ggInducedPairs ψ).mul_mem hA hg)
    ((LinFusion.ggInducedPairs ψ).inv_mem hA)
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, hcomm] at h1
  obtain ⟨κ, hκ⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hg h1
  rw [scalar_mul_diagGL] at hκ
  have h2 : A * InnerDiagA.diagGL (Pi.mulSingle i ω) =
      InnerDiagA.diagGL (fun k => κ * (Pi.mulSingle i ω : Fin (m + 1) → Fˣ) k) * A := by
    rw [← hκ]
    group
  have h3 := congrArg (fun X : GL (Fin (m + 1)) F => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    h2
  simp only [Units.val_mul, InnerDiagA.coe_diagGL] at h3
  have key : ∀ j, (((Pi.mulSingle i ω : Fin (m + 1) → Fˣ) j : Fˣ) : F) =
      (κ : F) * (((Pi.mulSingle i ω : Fin (m + 1) → Fˣ) (π j) : Fˣ) : F) := by
    intro j
    have hj := congrFun (congrFun h3 (π j)) j
    rw [mul_diagonal, diagonal_mul] at hj
    have h0 : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (π j) j ≠ 0 := (hπ j (π j)).mpr rfl
    exact mul_left_cancel₀ h0 (by rw [hj]; ring)
  obtain ⟨j, hji, hjπ⟩ : ∃ j, j ≠ i ∧ π j ≠ i := by
    have hcard : ({i, π.symm i} : Finset (Fin (m + 1))).card < (Finset.univ : Finset (Fin (m + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_insert_le i ({π.symm i} : Finset (Fin (m + 1)))
      rw [Finset.card_singleton] at this
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨j, fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _), fun h => hj ?_⟩
    rw [← h, Equiv.symm_apply_apply]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hκ1 : (κ : F) = 1 := by
    have := key j
    rw [Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hjπ, Units.val_one, mul_one] at this
    exact this.symm
  have := key i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hπi', hκ1, Units.val_one, one_mul] at this
  exact hω1 (Units.ext (by rw [this, Units.val_one]))

theorem card_le_of_isPGroup_perm {p : ℕ} (hp : p.Prime) (hmp : m + 1 = p)
    {H : Subgroup (Equiv.Perm (Fin (m + 1)))} (hH : IsPGroup p H) : Nat.card H ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hH
  have hdvd : p ^ k ∣ p.factorial := by
    have h1 := Subgroup.card_subgroup_dvd_card H
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin (m + 1))), Fintype.card_perm,
      Fintype.card_fin, hk] at h1
    rwa [hmp] at h1
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : p ^ 2 ∣ p.factorial := (pow_dvd_pow p (by omega)).trans hdvd
    rw [← Nat.mul_factorial_pred hp.ne_zero, pow_two] at h2
    have h3 : p ∣ (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left hp.pos h2
    have h4 := (hp.dvd_factorial).mp h3
    omega
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

theorem torus_clause_one [Finite G] [CharP F 2] {p : ℕ} (hp : p.Prime) (hmp : m + 1 = p)
    (hm : 2 ≤ m) (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {ω : Fˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ)
    {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs)
    (hmat : ∀ u ∈ Subgroup.normalizer (Bs : Set G), (∃ k, u ^ (p ^ k) = 1) →
      ∃ A : GL (Fin (m + 1)) F, (u, A) ∈ LinFusion.ggInducedPairs ψ)
    (Q : Subgroup G) (hQN : Q ≤ Subgroup.normalizer (Bs : Set G)) (hQp : IsPGroup p Q) :
    IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
      Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hmono : ∀ u ∈ Q, ∃ (π : Equiv.Perm (Fin (m + 1))) (A : GL (Fin (m + 1)) F),
      (u, A) ∈ LinFusion.ggInducedPairs ψ ∧
        IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π := by
    intro u hu
    obtain ⟨k, hk⟩ := hQp ⟨u, hu⟩
    obtain ⟨A, hA⟩ := hmat u (hQN hu) ⟨k, by
      have := congrArg Subtype.val hk
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this⟩
    obtain ⟨π, hπ⟩ := exists_isPermOf (A := A) fun i l l' hl hl' =>
      eq_of_ne_zero_of_mem_normalizer hker hω1 hωp hreal hBs (hQN hu) hA hl hl'
    exact ⟨π, A, hA, hπ⟩
  choose π A hA hπ using hmono
  have hmul : ∀ u v : Q, π ((u * v : Q) : G) (u * v).2 = π u u.2 * π v v.2 := by
    intro u v
    have h1 := (LinFusion.ggInducedPairs ψ).mul_mem (hA u u.2) (hA v v.2)
    obtain ⟨κ, hκ⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker h1
      (hA _ (u * v).2)
    have h2 : IsPermOf (((A _ (u * v).2 : GL (Fin (m + 1)) F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) (π u u.2 * π v v.2) := by
      rw [hκ]
      refine IsPermOf.scalar_mul ?_ κ
      rw [Units.val_mul]
      exact (hπ u u.2).mul (hπ v v.2)
    exact (hπ _ _).unique h2
  set φ : Q →* Equiv.Perm (Fin (m + 1)) := MonoidHom.mk' (fun u => π u u.2) hmul with hφ
  have hdiag : ∀ (u : G) (hu : u ∈ Q), π u hu = 1 → u ∈ Subgroup.centralizer (Bs : Set G) := by
    intro u hu hu1
    have hπ1 := hπ u hu
    rw [hu1] at hπ1
    obtain ⟨d, hd⟩ := IsPermOf.exists_eq_diagGL hπ1
    have hud := hA u hu
    rw [hd] at hud
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨e, -, hbe⟩ := hb
    exact mul_comm_of_mem_diag hC hbe hud
  have hcard : Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := by
    rw [← Subgroup.card_ker_mul_card_range φ]
    have hr : Nat.card φ.range ≤ p := card_le_of_isPGroup_perm hp hmp
      (IsPGroup.of_surjective hQp φ.rangeRestrict φ.rangeRestrict_surjective)
    have hk : Nat.card φ.ker ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := by
      have hle : (φ.ker).map Q.subtype ≤ Q ⊓ Subgroup.centralizer (Bs : Set G) := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u.2, hdiag u u.2 (MonoidHom.mem_ker.mp hu)⟩
      calc Nat.card φ.ker = Nat.card ((φ.ker).map Q.subtype) :=
            (Subgroup.card_map_of_injective Q.subtype_injective).symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    calc Nat.card φ.ker * Nat.card φ.range ≤
          Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) * p := Nat.mul_le_mul hk hr
      _ = p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := mul_comm _ _
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, hcard⟩
  obtain ⟨u, huQ, huC⟩ := x
  obtain ⟨v, hvQ, hvC⟩ := y
  have hd : ∀ (w : G) (hwQ : w ∈ Q), w ∈ Subgroup.centralizer (Bs : Set G) →
      ∃ d : Fin (m + 1) → Fˣ, (w, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := by
    intro w hwQ hwC
    have hw1 := IsPermOf.eq_one_of_mem_centralizer hm hker hω1 hωp hreal hBs hwC (hA w hwQ)
      (hπ w hwQ)
    have hπ1 := hπ w hwQ
    rw [hw1] at hπ1
    obtain ⟨d, hd⟩ := IsPermOf.exists_eq_diagGL hπ1
    have hwd := hA w hwQ
    rw [hd] at hwd
    exact ⟨d, hwd⟩
  obtain ⟨d, hud⟩ := hd u huQ huC
  obtain ⟨e, hve⟩ := hd v hvQ hvC
  exact mul_comm_of_mem_diag hC hud hve

end LinModel

end CFSG.StandardType
