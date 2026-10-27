module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs
import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup

private noncomputable def sz5e1_wdc_tau {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) : Representation F ↥E V :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)).comp E.subtype

private theorem sz5e1_wdc_tau_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (e : ↥E) (v : V) :
    sz5e1_wdc_tau E e v = (e : V ≃ₗ[F] V) v := rfl

private theorem sz5e1_wdc_weightSpace_eq {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (χ : ↥E →* Fˣ) :
    CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence.weightSpace
      (sz5e1_wdc_tau E) χ = wt E χ := by
  ext v
  rw [CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence.mem_weightSpace,
    mem_wt]
  rfl

private theorem sz5e1_wdc_tau_sq {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (hE2 : ∀ a ∈ E, a ^ 2 = 1) (e : ↥E) :
    (sz5e1_wdc_tau E e) ^ 2 = 1 := by
  rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (hE2 _ e.2), map_one]

private theorem sz5e1_wdc_isSemisimple {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (hF : ringChar F ≠ 2) (hE2 : ∀ a ∈ E, a ^ 2 = 1) (e : ↥E) :
    Module.End.IsSemisimple (sz5e1_wdc_tau E e) := by
  have h2 : (sz5e1_wdc_tau E e) ^ 2 = 1 := sz5e1_wdc_tau_sq E hE2 e
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : Polynomial F) ^ 2 - Polynomial.C 1)
  · exact
      (Polynomial.separable_X_pow_sub_C (n := 2) (1 : F) (Ring.two_ne_zero hF)
        one_ne_zero).squarefree
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    simp [h2]

private theorem sz5e1_wdc_iSup_eigenspace_eq_top {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (g : Module.End F V) (hF : ringChar F ≠ 2) (hg : g ^ 2 = 1) :
    (⨆ μ : F, Module.End.eigenspace g μ) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hgg : g (g v) = v := by
    have h := congrArg (fun f : Module.End F V => f v) hg
    simpa [pow_two, Module.End.mul_apply] using h
  have hv1 : (2⁻¹ : F) • (v + g v) ∈ Module.End.eigenspace g 1 := by
    rw [Module.End.mem_eigenspace_iff]
    rw [map_smul, map_add, hgg, one_smul]
    rw [add_comm]
  have hv2 : (2⁻¹ : F) • (v - g v) ∈ Module.End.eigenspace g (-1) := by
    have hmem : v - g v ∈ Module.End.eigenspace g (-1) := by
      have hneg : (-1 : F) • (v - g v) = -(v - g v) := neg_one_smul F _
      rw [Module.End.mem_eigenspace_iff, map_sub, hgg, hneg]
      abel
    exact Submodule.smul_mem _ _ hmem
  have hsum : (2⁻¹ : F) • (v + g v) + (2⁻¹ : F) • (v - g v) = v := by
    rw [← smul_add]
    have h : (v + g v) + (v - g v) = (2 : F) • v := by
      rw [two_smul]
      abel
    rw [h, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [← hsum]
  exact add_mem (le_iSup (fun μ : F => Module.End.eigenspace g μ) 1 hv1)
    (le_iSup (fun μ : F => Module.End.eigenspace g μ) (-1) hv2)

theorem sz5e1_weight_decomp {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (E : Subgroup (V ≃ₗ[F] V))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    iSupIndep (fun χ : ↥E →* Fˣ => wt E χ) ∧ ⨆ χ : ↥E →* Fˣ, wt E χ = ⊤ := by
  have hsq : ∀ e : ↥E, (sz5e1_wdc_tau E e) ^ 2 = 1 := fun e => sz5e1_wdc_tau_sq E hE2 e
  have hss : ∀ e : ↥E, Module.End.IsSemisimple (sz5e1_wdc_tau E e) := fun e =>
    sz5e1_wdc_isSemisimple E hF hE2 e
  have hind : iSupIndep (fun χ : ↥E →* Fˣ => wt E χ) := by
    have h := CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence.independent
      (sz5e1_wdc_tau E) (fun x : ↥E →* Fˣ => x) Function.injective_id
    simpa only [sz5e1_wdc_weightSpace_eq] using h
  refine ⟨hind, ?_⟩
  have h' : ∀ e : ↥E, ⨆ μ : F, Module.End.maxGenEigenspace (sz5e1_wdc_tau E e) μ = ⊤ := by
    intro e
    have hif := (hss e).isFinitelySemisimple
    calc ⨆ μ : F, Module.End.maxGenEigenspace (sz5e1_wdc_tau E e) μ
        = ⨆ μ : F, Module.End.eigenspace (sz5e1_wdc_tau E e) μ :=
          iSup_congr fun μ =>
            Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace hif μ
      _ = ⊤ := sz5e1_wdc_iSup_eigenspace_eq_top (sz5e1_wdc_tau E e) hF (hsq e)
  have hcomm : Pairwise fun i j : ↥E => Commute (sz5e1_wdc_tau E i) (sz5e1_wdc_tau E j) := by
    intro i j _
    show sz5e1_wdc_tau E i * sz5e1_wdc_tau E j = sz5e1_wdc_tau E j * sz5e1_wdc_tau E i
    rw [← map_mul, ← map_mul]
    exact congrArg (sz5e1_wdc_tau E) (Subtype.ext (hEc _ i.2 _ j.2))
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun e : ↥E => sz5e1_wdc_tau E e) hcomm h'
  rw [eq_top_iff, ← htop]
  refine iSup_le fun μ => ?_
  have heig : (⨅ e, Module.End.maxGenEigenspace (sz5e1_wdc_tau E e) (μ e))
      = ⨅ e, Module.End.eigenspace (sz5e1_wdc_tau E e) (μ e) := by
    refine iInf_congr fun e => ?_
    exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (hss e).isFinitelySemisimple (μ e)
  rw [heig]
  by_cases hbot : (⨅ e, Module.End.eigenspace (sz5e1_wdc_tau E e) (μ e)) = ⊥
  · rw [hbot]; exact bot_le
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hv' : ∀ e : ↥E, sz5e1_wdc_tau E e v = μ e • v := fun e =>
      Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).mp hv e)
    have hmul : ∀ a b : ↥E, μ (a * b) = μ a * μ b := by
      intro a b
      have hzero : (μ (a * b) - μ a * μ b) • v = 0 := by
        rw [sub_smul, ← hv' (a * b), map_mul, Module.End.mul_apply, hv' b, map_smul, hv' a,
          smul_smul, mul_comm, sub_self]
      rcases smul_eq_zero.1 hzero with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hv0
    have hone : μ 1 = 1 := by
      have hzero : (μ 1 - 1) • v = 0 := by
        rw [sub_smul, ← hv' 1, one_smul, map_one]; simp
      rcases smul_eq_zero.1 hzero with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hv0
    have hne : ∀ e : ↥E, μ e ≠ 0 := by
      intro e h0
      have h1 : sz5e1_wdc_tau E e v = 0 := by rw [hv' e, h0, zero_smul]
      have h2 : v = 0 := by
        have h3 := congrArg (fun w => (e : V ≃ₗ[F] V).symm w) h1
        rw [sz5e1_wdc_tau_apply] at h3
        simpa using h3
      exact hv0 h2
    let ψ : ↥E →* Fˣ :=
      { toFun := fun e => Units.mk0 (μ e) (hne e)
        map_one' := by ext; exact hone
        map_mul' := by intro a b; ext; exact hmul a b }
    refine le_trans ?_ (le_iSup (fun ψ : ↥E →* Fˣ => wt E ψ) ψ)
    intro w hw e
    have hwe : w ∈ Module.End.eigenspace (sz5e1_wdc_tau E e) (μ e) :=
      (Submodule.mem_iInf _).mp hw e
    have hw' : sz5e1_wdc_tau E e w = μ e • w := Module.End.mem_eigenspace_iff.1 hwe
    show (e : V ≃ₗ[F] V) w = ((ψ e : Fˣ) : F) • w
    have hpsi : ((ψ e : Fˣ) : F) = μ e := rfl
    rw [hpsi, ← hw']
    exact (sz5e1_wdc_tau_apply E e w).symm

private noncomputable def sz5e1_chc_kerEquiv {F : Type} [Field F] {E : Type} [Group E] (b : E) :
    {χ : E →* Fˣ // χ b = 1} ≃
      (MonoidHom.domRestrictHom (Subgroup.zpowers b) Fˣ).ker where
  toFun χ := ⟨χ.1, by
    simp only [MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply,
      MonoidHom.domRestrict_eq_one_iff]
    intro x hx
    exact (MonoidHom.mem_ker).mp
      ((Subgroup.zpowers_le.mpr ((MonoidHom.mem_ker).mpr χ.2)) hx)⟩
  invFun χ := ⟨χ.1, by
    have h : ∀ y ∈ Subgroup.zpowers b, χ.1 y = 1 := by
      have h := (MonoidHom.mem_ker).mp χ.2
      simpa using h
    exact h b (Subgroup.mem_zpowers b)⟩
  left_inv χ := Subtype.ext rfl
  right_inv χ := Subtype.ext rfl

private noncomputable def sz5e1_charEquiv {F : Type} [Field F] {E : Type} [Group E]
    (h2 : ∀ a : E, a ^ 2 = 1) : (E →* Fˣ) ≃ (E →* rootsOfUnity 2 F) where
  toFun χ := χ.codRestrict (rootsOfUnity 2 F) fun e => by
    rw [mem_rootsOfUnity, ← map_pow, h2 e, map_one]
  invFun ψ := (rootsOfUnity 2 F).subtype.comp ψ
  left_inv χ := by ext e; rfl
  right_inv ψ := by ext e; rfl

theorem sz5e1_char_count {F : Type} [Field F] {E : Type} [Group E] [Finite E]
    (hF : ringChar F ≠ 2) (hc : ∀ a b : E, a * b = b * a)
    (h8 : Nat.card E = 8) (h2 : ∀ a : E, a ^ 2 = 1) :
    Nat.card (E →* Fˣ) = 8 ∧
      ∀ b : E, b ≠ 1 → Nat.card {χ : E →* Fˣ // χ b = 1} = 4 := by
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := hc }
  have : IsMulCommutative E := ⟨⟨hc⟩⟩
  have hexp : Monoid.exponent E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one h2
  have hroots2 : HasEnoughRootsOfUnity F 2 :=
    { prim := ⟨-1, IsPrimitiveRoot.neg_one (ringChar F) hF⟩
      cyc := rootsOfUnity.isCyclic F 2 }
  have : HasEnoughRootsOfUnity F (Monoid.exponent E) :=
    HasEnoughRootsOfUnity.of_dvd F hexp
  have hcard : Nat.card (E →* Fˣ) = 8 := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity E F, h8]
  refine ⟨hcard, ?_⟩
  intro b hb
  have horder : orderOf b = 2 := by
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h2 b)
    have hne : orderOf b ≠ 1 := fun h => hb (orderOf_eq_one_iff.mp h)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf b) hdvd with h | h
    · exact absurd h hne
    · exact h
  have hcardH : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers, horder]
  have hquot : Nat.card (E ⧸ Subgroup.zpowers b) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers b)
    have h' : (8 : ℕ) = Nat.card (E ⧸ Subgroup.zpowers b) * 2 := by
      simpa [h8, hcardH] using h
    omega
  have : Finite (E ⧸ Subgroup.zpowers b) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.zpowers b))
      (QuotientGroup.mk'_surjective _)
  have : HasEnoughRootsOfUnity F (Monoid.exponent (E ⧸ Subgroup.zpowers b)) :=
    HasEnoughRootsOfUnity.of_dvd F
      (dvd_trans (Group.exponent_quotient_dvd (Subgroup.zpowers b)) hexp)
  have hker1 : Nat.card (MonoidHom.domRestrictHom (Subgroup.zpowers b) Fˣ).ker = 4 := by
    rw [CommGroup.card_domRestrictHom_ker (M := F) (Subgroup.zpowers b), hquot]
  have hequiv : Nat.card {χ : E →* Fˣ // χ b = 1} =
      Nat.card (MonoidHom.domRestrictHom (Subgroup.zpowers b) Fˣ).ker :=
    Nat.card_congr (sz5e1_chc_kerEquiv b)
  rw [hequiv, hker1]

private theorem sz5e1_wct_unit_sq {F : Type} [Field F] :
    ∀ u : Fˣ, u ^ 2 = 1 → u = 1 ∨ u = -1 := by
  intro u hu
  have hu' : ((u : F)) ^ 2 = 1 := by
    simpa using congrArg (fun v : Fˣ => (v : F)) hu
  rcases sq_eq_one_iff.mp hu' with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

private theorem sz5e1_wct_finrank_biSup_eq_sum {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] [Module.Finite F M] {ι : Type} [DecidableEq ι]
    {p : ι → Submodule F M} (hp : iSupIndep p) (S : Finset ι) :
    Module.finrank F ↥(⨆ i ∈ S, p i) = ∑ i ∈ S, Module.finrank F (p i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hdis : Disjoint (p a) (⨆ i ∈ S, p i) := by
      have := hp.disjoint_biSup (y := (S : Set ι)) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ S, p i)
    rw [hdis.eq_bot, finrank_bot, add_zero] at h
    exact h

private noncomputable def sz5e1_wct_precomp {G A : Type} [Group G] [MulOneClass A]
    (c : MulAut G) : Equiv.Perm (G →* A) where
  toFun χ := χ.comp (c.symm : G →* G)
  invFun χ := χ.comp (c : G →* G)
  left_inv χ := by ext g; simp
  right_inv χ := by ext g; simp

private theorem sz5e1_wct_precomp_pow {G A : Type} [Group G] [MulOneClass A]
    (c : MulAut G) (n : ℕ) (χ : G →* A) :
    (sz5e1_wct_precomp c ^ n) χ = χ.comp (((c.symm) ^ n : MulAut G) : G →* G) := by
  induction n with
  | zero => ext g; simp [sz5e1_wct_precomp]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    ext g
    rw [show sz5e1_wct_precomp c (χ.comp (((c.symm) ^ n : MulAut G) : G →* G)) =
        (χ.comp (((c.symm) ^ n : MulAut G) : G →* G)).comp (c.symm : G →* G) from rfl]
    simp only [MonoidHom.comp_apply]
    rw [pow_succ]
    rfl

private theorem sz5e1_wct_precomp_seven {G A : Type} [Group G] [MulOneClass A]
    (c : MulAut G) (hc : c ^ 7 = 1) :
    (sz5e1_wct_precomp (A := A) c) ^ 7 = 1 := by
  ext χ g
  rw [sz5e1_wct_precomp_pow]
  have h7 : (c.symm) ^ 7 = (1 : MulAut G) := by
    rw [show (c.symm : MulAut G) = c⁻¹ from rfl, inv_pow, hc]
    rfl
  rw [h7]
  simp

private noncomputable def sz5e1_wct_conj {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] : MulAut ↥E :=
  let f : ↥E →* ↥E :=
    { toFun := fun e => ⟨y * (e : V ≃ₗ[F] V) * y⁻¹, hyE (e : V ≃ₗ[F] V) e.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hab' : y * (a : V ≃ₗ[F] V) * y⁻¹ = y * (b : V ≃ₗ[F] V) * y⁻¹ :=
      congrArg Subtype.val hab
    exact mul_left_cancel (mul_right_cancel hab')
  MulEquiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩

private theorem sz5e1_wct_conj_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] (e : ↥E) :
    ((sz5e1_wct_conj E y hyE e : ↥E) : V ≃ₗ[F] V) =
      y * (e : V ≃ₗ[F] V) * y⁻¹ := by
  rfl

private theorem sz5e1_wct_conj_pow_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] (n : ℕ) (e : ↥E) :
    (((sz5e1_wct_conj E y hyE) ^ n) e : V ≃ₗ[F] V) =
      y ^ n * (e : V ≃ₗ[F] V) * (y ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    rw [sz5e1_wct_conj_apply, ih]
    rw [pow_succ']
    group

private theorem sz5e1_wct_conj_seven {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] (hy7 : orderOf y = 7) :
    sz5e1_wct_conj E y hyE ^ 7 = 1 := by
  ext e
  rw [sz5e1_wct_conj_pow_apply]
  have hy7' : y ^ 7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one y
  rw [hy7']
  simp

private noncomputable def sz5e1_wct_twist {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] :
    Equiv.Perm (↥E →* Fˣ) :=
  sz5e1_wct_precomp (A := Fˣ) (sz5e1_wct_conj E y hyE)

private theorem sz5e1_wct_twist_seven {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] (hy7 : orderOf y = 7) :
    sz5e1_wct_twist E y hyE ^ 7 = 1 :=
  sz5e1_wct_precomp_seven (A := Fˣ) (sz5e1_wct_conj E y hyE)
    (sz5e1_wct_conj_seven E y hyE hy7)

private theorem sz5e1_wct_conj_symm_apply_coe {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E] (e : ↥E) :
    (((sz5e1_wct_conj E y hyE).symm e : ↥E) : V ≃ₗ[F] V) =
      y⁻¹ * (e : V ≃ₗ[F] V) * y := by
  have h := congrArg Subtype.val (MulEquiv.apply_symm_apply (sz5e1_wct_conj E y hyE) e)
  rw [sz5e1_wct_conj_apply] at h
  rw [← h]
  group

private theorem sz5e1_wct_twist_mapsTo {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E]
    (χ : ↥E →* Fˣ) {v : V} (hv : v ∈ wt E χ) :
    y v ∈ wt E (sz5e1_wct_twist E y hyE χ) := by
  rw [mem_wt] at hv ⊢
  intro e
  have hee : (e : V ≃ₗ[F] V) * y =
      y * ((sz5e1_wct_conj E y hyE).symm e : V ≃ₗ[F] V) := by
    rw [sz5e1_wct_conj_symm_apply_coe]
    group
  have hTe : (sz5e1_wct_twist E y hyE χ) e =
      χ ((sz5e1_wct_conj E y hyE).symm e) := rfl
  calc (e : V ≃ₗ[F] V) (y v)
      = ((e : V ≃ₗ[F] V) * y) v := rfl
    _ = (y * ((sz5e1_wct_conj E y hyE).symm e : V ≃ₗ[F] V)) v := by rw [hee]
    _ = y (((sz5e1_wct_conj E y hyE).symm e : V ≃ₗ[F] V) v) := rfl
    _ = y (((χ ((sz5e1_wct_conj E y hyE).symm e) : Fˣ) : F) • v) := by rw [hv]
    _ = ((χ ((sz5e1_wct_conj E y hyE).symm e) : Fˣ) : F) • (y v) := by
        rw [map_smul]
    _ = (((sz5e1_wct_twist E y hyE χ) e : Fˣ) : F) • (y v) := by rw [hTe]

private noncomputable def sz5e1_wct_wtMap {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E]
    (χ : ↥E →* Fˣ) :
    ↥(wt E χ) ≃ₗ[F] ↥(wt E (sz5e1_wct_twist E y hyE χ)) where
  toFun v := ⟨y v.1, sz5e1_wct_twist_mapsTo E y hyE χ v.2⟩
  invFun v := ⟨y⁻¹ v.1, by
    rw [mem_wt]
    intro e
    have hee : (e : V ≃ₗ[F] V) * y⁻¹ =
        y⁻¹ * ((sz5e1_wct_conj E y hyE) e : V ≃ₗ[F] V) := by
      rw [sz5e1_wct_conj_apply]
      group
    have hv := (mem_wt E (sz5e1_wct_twist E y hyE χ) v.1).mp v.2
      (sz5e1_wct_conj E y hyE e)
    have hTe : (sz5e1_wct_twist E y hyE χ) ((sz5e1_wct_conj E y hyE) e) = χ e := by
      show χ ((sz5e1_wct_conj E y hyE).symm ((sz5e1_wct_conj E y hyE) e)) = χ e
      rw [MulEquiv.symm_apply_apply]
    have hv' : ((sz5e1_wct_conj E y hyE) e : V ≃ₗ[F] V) v.1 =
        ((χ e : Fˣ) : F) • v.1 := by
      rw [hv, hTe]
    calc (e : V ≃ₗ[F] V) (y⁻¹ v.1)
        = ((e : V ≃ₗ[F] V) * y⁻¹) v.1 := rfl
      _ = (y⁻¹ * ((sz5e1_wct_conj E y hyE) e : V ≃ₗ[F] V)) v.1 := by rw [hee]
      _ = y⁻¹ (((sz5e1_wct_conj E y hyE) e : V ≃ₗ[F] V) v.1) := rfl
      _ = y⁻¹ (((χ e : Fˣ) : F) • v.1) := by rw [hv']
      _ = ((χ e : Fˣ) : F) • (y⁻¹ v.1) := by rw [map_smul]⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  map_add' v w := by ext; simp
  map_smul' a v := by ext; simp

private theorem sz5e1_wct_wt_finrank {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) [Finite ↥E]
    (χ : ↥E →* Fˣ) :
    Module.finrank F (wt E (sz5e1_wct_twist E y hyE χ)) =
      Module.finrank F (wt E χ) :=
  (LinearEquiv.finrank_eq (sz5e1_wct_wtMap E y hyE χ)).symm

private theorem sz5e1_wct_fixSpace_eq_iSup {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) [Fintype (↥E →* Fˣ)] (hF : ringChar F ≠ 2)
    (g : V ≃ₗ[F] V) (a : (↥E →* Fˣ) → Prop) [DecidablePred a]
    (htop : ⨆ χ : ↥E →* Fˣ, wt E χ = ⊤)
    (hfix : ∀ χ, a χ → ∀ v ∈ wt E χ, g v = v)
    (hneg : ∀ χ, ¬ a χ → ∀ v ∈ wt E χ, g v = -v) :
    fixSpaceOf g = ⨆ χ ∈ Finset.univ.filter a, wt E χ := by
  classical
  set s1 : Finset (↥E →* Fˣ) := Finset.univ.filter a with hs1
  set s2 : Finset (↥E →* Fˣ) := Finset.univ.filter (fun χ => ¬ a χ) with hs2
  set W1 : Submodule F V := ⨆ χ ∈ s1, wt E χ with hW1
  set W2 : Submodule F V := ⨆ χ ∈ s2, wt E χ with hW2
  have hW12 : W1 ⊔ W2 = ⊤ := by
    have hs : s1 ∪ s2 = Finset.univ := by
      simp only [hs1, hs2]
      exact Finset.filter_union_filter_not_eq a Finset.univ
    calc W1 ⊔ W2 = ⨆ χ ∈ s1 ∪ s2, wt E χ := Finset.iSup_union.symm
      _ = ⨆ χ ∈ Finset.univ, wt E χ := by rw [hs]
      _ = ⨆ χ : ↥E →* Fˣ, wt E χ := by simp
      _ = ⊤ := htop
  have hfixW1 : W1 ≤ fixSpaceOf g := by
    refine iSup₂_le fun χ hχ => ?_
    intro v hv
    rw [mem_fixSpaceOf]
    exact hfix χ (Finset.mem_filter.mp hχ).2 v hv
  have hnegW2 : W2 ≤ LinearMap.ker ((g : V →ₗ[F] V) + 1) := by
    refine iSup₂_le fun χ hχ => ?_
    intro v hv
    have h := hneg χ (Finset.mem_filter.mp hχ).2 v hv
    rw [LinearMap.mem_ker, LinearMap.add_apply]
    change (g : V →ₗ[F] V) v + v = 0
    rw [show (g : V →ₗ[F] V) v = -v from h]
    simp
  apply le_antisymm
  · intro v hv
    have hmem : v ∈ W1 ⊔ W2 := by rw [hW12]; trivial
    rw [Submodule.mem_sup] at hmem
    obtain ⟨u, hu, w, hw, rfl⟩ := hmem
    have hu' : g u = u := (mem_fixSpaceOf g u).mp (hfixW1 hu)
    have hw' : g w = -w := by
      have h := hnegW2 hw
      rw [LinearMap.mem_ker, LinearMap.add_apply] at h
      change (g : V →ₗ[F] V) w + w = 0 at h
      exact eq_neg_iff_add_eq_zero.mpr h
    rw [mem_fixSpaceOf] at hv
    rw [map_add, hu', hw'] at hv
    have hnegw : -w = w := add_left_cancel hv
    have h2 : w + w = 0 := eq_neg_iff_add_eq_zero.mp hnegw.symm
    have h2' : (2 : F) • w = 0 := by rwa [two_smul]
    have hw0 : w = 0 := (smul_eq_zero.mp h2').resolve_left (Ring.two_ne_zero hF)
    rw [hw0, add_zero]
    exact hu
  · exact hfixW1

theorem sz5e1_weights_count {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (E : Subgroup (V ≃ₗ[F] V)) (y : V ≃ₗ[F] V)
    (hE8 : Nat.card E = 8) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1)
    (hy7 : orderOf y = 7) (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hyf : ∀ e ∈ E, y * e * y⁻¹ = e → e = 1) :
    ∃ a c : ℕ, 1 ≤ c ∧ Module.finrank F V = a + 7 * c ∧
      Module.finrank F (wt E 1) = a ∧
      (∀ χ : ↥E →* Fˣ, χ ≠ 1 → Module.finrank F (wt E χ) = c) ∧
      (∀ b ∈ E, b ≠ 1 → Module.finrank F (fixSpaceOf b) = a + 3 * c ∧
        Module.finrank F (fixSpaceOf (negOne F V * b)) = 4 * c) := by
  classical
  let : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE8]; norm_num)
  have hsqE : ∀ b : ↥E, b ^ 2 = 1 := fun b => by
    apply Subtype.ext
    simpa using hE2 (b : V ≃ₗ[F] V) b.2
  have : Fintype ↥E := Fintype.ofFinite ↥E
  have : Fintype (rootsOfUnity 2 F) := Fintype.ofFinite _
  have : Fintype (↥E →* rootsOfUnity 2 F) :=
    Fintype.ofInjective (fun χ : ↥E →* rootsOfUnity 2 F => fun e : ↥E => χ e)
      (fun χ ψ h => MonoidHom.ext fun e => congrFun h e)
  have : Fintype (↥E →* Fˣ) :=
    Fintype.ofEquiv (↥E →* rootsOfUnity 2 F) (sz5e1_charEquiv hsqE).symm
  obtain ⟨hind, htop⟩ := sz5e1_weight_decomp hF E hEc hE2
  obtain ⟨hcharcard, hcharcount⟩ :=
    sz5e1_char_count (E := ↥E) hF
      (fun a b => Subtype.ext (hEc (a : V ≃ₗ[F] V) a.2 (b : V ≃ₗ[F] V) b.2))
      (by simpa using hE8) (fun a => Subtype.ext (hE2 (a : V ≃ₗ[F] V) a.2))
  have hcard8 : Fintype.card (↥E →* Fˣ) = 8 := by
    rw [← Nat.card_eq_fintype_card, hcharcard]
  have hex : ∃ χ : ↥E →* Fˣ, χ ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton (↥E →* Fˣ) := ⟨fun x y => by rw [h x, h y]⟩
    have : Fintype.card (↥E →* Fˣ) ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    rw [hcard8] at this
    norm_num at this
  obtain ⟨χ₀, hχ₀⟩ := hex
  let T : Equiv.Perm (↥E →* Fˣ) := sz5e1_wct_twist E y hyE
  have hT7 : T ^ 7 = 1 := sz5e1_wct_twist_seven E y hyE hy7
  have hTmap : ∀ χ : ↥E →* Fˣ,
      Module.finrank F (wt E (T χ)) = Module.finrank F (wt E χ) :=
    fun χ => sz5e1_wct_wt_finrank E y hyE χ
  have hTno : ∀ χ : ↥E →* Fˣ, T χ = χ → χ = 1 := by
    intro χ hfix
    have hχ : ∀ e : ↥E, χ ((sz5e1_wct_conj E y hyE).symm e) = χ e := by
      intro e
      have := congrArg (fun f : ↥E →* Fˣ => f e) hfix
      simpa [T, sz5e1_wct_twist, sz5e1_wct_precomp, MonoidHom.comp_apply] using this
    let φ : ↥E →* ↥E :=
      { toFun := fun e => (sz5e1_wct_conj E y hyE).symm e * e⁻¹
        map_one' := by simp
        map_mul' := by intro a b; simp [mul_assoc, mul_left_comm, mul_comm] }
    have hφker : ∀ e : ↥E, φ e = 1 → e = 1 := by
      intro e he
      have hsymm : (sz5e1_wct_conj E y hyE).symm e = e := by
        have h : (sz5e1_wct_conj E y hyE).symm e * e⁻¹ = 1 := he
        exact mul_inv_eq_one.mp h
      have hcoe : y⁻¹ * (e : V ≃ₗ[F] V) * y = (e : V ≃ₗ[F] V) := by
        rw [← sz5e1_wct_conj_symm_apply_coe E y hyE e, hsymm]
      have hconj : y * (e : V ≃ₗ[F] V) * y⁻¹ = (e : V ≃ₗ[F] V) := by
        have h1 : (e : V ≃ₗ[F] V) * y = y * (e : V ≃ₗ[F] V) := by
          have h := congrArg (fun z => y * z) hcoe
          simpa [mul_assoc] using h
        rw [← h1]; group
      exact Subtype.ext (hyf (e : V ≃ₗ[F] V) e.2 hconj)
    have hφsurj : Function.Surjective φ :=
      Finite.surjective_of_injective (f := φ) (fun a b hab => by
        have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
        exact mul_inv_eq_one.mp (hφker _ h1))
    apply MonoidHom.ext
    intro f
    obtain ⟨e, rfl⟩ := hφsurj f
    show χ (φ e) = 1
    have hval : χ (φ e) = χ ((sz5e1_wct_conj E y hyE).symm e) * (χ e)⁻¹ := by
      show χ ((sz5e1_wct_conj E y hyE).symm e * e⁻¹) = _
      rw [map_mul, map_inv]
    rw [hval, hχ e, mul_inv_cancel]
  have hTno' : ∀ χ : ↥E →* Fˣ, χ ≠ 1 → T χ ≠ χ := fun χ h h' => h (hTno χ h')
  have hne : orderOf T ≠ 1 := by
    intro h1
    have hT1 : T = 1 := orderOf_eq_one_iff.mp h1
    exact hTno' χ₀ hχ₀ (by rw [hT1]; rfl)
  have hord : orderOf T = 7 := by
    have hdvd : orderOf T ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hT7
    exact (Nat.prime_seven.eq_one_or_self_of_dvd (orderOf T) hdvd).resolve_left hne
  have hcycle : T.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [hord]; exact Nat.prime_seven)
      (by rw [hord, hcard8]; norm_num)
  have hdim_all : ∀ χ ψ : ↥E →* Fˣ, χ ≠ 1 → ψ ≠ 1 →
      Module.finrank F (wt E χ) = Module.finrank F (wt E ψ) := by
    intro χ ψ hχ hψ
    obtain ⟨i, hi⟩ := hcycle.exists_pow_eq (hTno' χ hχ) (hTno' ψ hψ)
    have hpow : ∀ i : ℕ, Module.finrank F (wt E ((T ^ i) χ)) =
        Module.finrank F (wt E χ) := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, hTmap, ih]
    rw [← hi, hpow i]
  let a := Module.finrank F (wt E 1)
  let c := Module.finrank F (wt E χ₀)
  have hdim : ∀ χ : ↥E →* Fˣ, χ ≠ 1 → Module.finrank F (wt E χ) = c :=
    fun χ hχ => hdim_all χ χ₀ hχ hχ₀
  have hcpos : 1 ≤ c := by
    by_contra hc
    have hc0 : c = 0 := by omega
    have hbot : ∀ χ : ↥E →* Fˣ, χ ≠ 1 → wt E χ = ⊥ := by
      intro χ hχ
      exact (Submodule.finrank_eq_zero).mp (by rw [hdim χ hχ, hc0])
    have htop1 : (⨆ χ : ↥E →* Fˣ, wt E χ) ≤ wt E 1 := by
      refine iSup_le fun χ => ?_
      by_cases hχ : χ = 1
      · rw [hχ]
      · rw [hbot χ hχ]; exact bot_le
    have hV : wt E 1 = ⊤ := by
      apply le_antisymm le_top
      rw [← htop]
      exact htop1
    have hall : ∀ e : ↥E, (e : V ≃ₗ[F] V) = 1 := by
      intro e
      ext v
      have hv : v ∈ wt E 1 := by rw [hV]; trivial
      simpa using (mem_wt E 1 v).mp hv e
    have hEbot : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      exact hall ⟨e, he⟩
    have hcard1 : Nat.card E = 1 := by
      rw [hEbot]; simp
    omega
  have hVsum : Module.finrank F V =
      ∑ χ : ↥E →* Fˣ, Module.finrank F (wt E χ) := by
    have h1 := sz5e1_wct_finrank_biSup_eq_sum (M := V)
      (p := fun χ : ↥E →* Fˣ => wt E χ) hind
      (Finset.univ : Finset (↥E →* Fˣ))
    have htop' : (⨆ χ ∈ (Finset.univ : Finset (↥E →* Fˣ)), wt E χ) = ⊤ := by
      rw [show (⨆ χ ∈ (Finset.univ : Finset (↥E →* Fˣ)), wt E χ) =
          (⨆ χ : ↥E →* Fˣ, wt E χ) from by simp]
      exact htop
    rw [htop'] at h1
    simpa using h1
  have hsum : (∑ χ : ↥E →* Fˣ, Module.finrank F (wt E χ)) = a + 7 * c := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥E →* Fˣ))]
    have hrest : ∑ χ ∈ (Finset.univ.erase (1 : ↥E →* Fˣ)),
        Module.finrank F (wt E χ) = 7 * c := by
      rw [Finset.sum_congr rfl (fun χ hχ => hdim χ (Finset.ne_of_mem_erase hχ)),
        Finset.sum_const, smul_eq_mul]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard8]
    rw [hrest]
  have hVfin : Module.finrank F V = a + 7 * c := by
    rw [hVsum, hsum]
  have hfix_eq : ∀ b : ↥E,
      fixSpaceOf (b : V ≃ₗ[F] V) =
        ⨆ χ ∈ Finset.univ.filter (fun χ : ↥E →* Fˣ => χ b = 1), wt E χ :=
    fun b => sz5e1_wct_fixSpace_eq_iSup E hF (b : V ≃ₗ[F] V)
      (fun χ : ↥E →* Fˣ => χ b = 1) htop
      (fun χ hχ v hv => by
        rw [mem_wt] at hv
        simp [hv b, hχ])
      (fun χ hχ v hv => by
        rw [mem_wt] at hv
        have hχ1 : χ b = -1 := by
          have hsq : (χ b) ^ 2 = 1 := by rw [← map_pow, hsqE b, map_one]
          exact (sz5e1_wct_unit_sq (χ b) hsq).resolve_left hχ
        simp [hv b, hχ1])
  have hfixneg_eq : ∀ b : ↥E,
      fixSpaceOf (negOne F V * (b : V ≃ₗ[F] V)) =
        ⨆ χ ∈ Finset.univ.filter (fun χ : ↥E →* Fˣ => χ b = -1), wt E χ :=
    fun b => sz5e1_wct_fixSpace_eq_iSup E hF (negOne F V * (b : V ≃ₗ[F] V))
      (fun χ : ↥E →* Fˣ => χ b = -1) htop
      (fun χ hχ v hv => by
        rw [mem_wt] at hv
        simp [LinearEquiv.mul_apply, negOne_apply, hv b, hχ])
      (fun χ hχ v hv => by
        rw [mem_wt] at hv
        have hχ1 : χ b = 1 := by
          have hsq : (χ b) ^ 2 = 1 := by rw [← map_pow, hsqE b, map_one]
          rcases sz5e1_wct_unit_sq (χ b) hsq with h | h
          · exact h
          · exact absurd h hχ
        simp [LinearEquiv.mul_apply, negOne_apply, hv b, hχ1])
  refine ⟨a, c, hcpos, hVfin, rfl, hdim, ?_⟩
  intro b hbE hb1
  have hb' : (⟨b, hbE⟩ : ↥E) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hbsq : (⟨b, hbE⟩ : ↥E) ^ 2 = 1 := hsqE ⟨b, hbE⟩
  have hcnt := hcharcount ⟨b, hbE⟩ hb'
  have hs1card : (Finset.univ.filter
      (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1)).card = 4 := by
    have h := hcnt
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    simpa using h
  have hone : (1 : Fˣ) ≠ -1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hF (by
      simpa using (congrArg (fun u : Fˣ => (u : F)) h).symm)
  have hall : ∀ χ : ↥E →* Fˣ, χ ⟨b, hbE⟩ = 1 ∨ χ ⟨b, hbE⟩ = -1 := by
    intro χ
    have hsq : (χ ⟨b, hbE⟩) ^ 2 = 1 := by rw [← map_pow, hbsq, map_one]
    exact sz5e1_wct_unit_sq _ hsq
  have hsnegcard : (Finset.univ.filter
      (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1)).card = 4 := by
    have hunion : (Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1)) ∪
        (Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1)) =
        Finset.univ := by
      rw [← Finset.filter_or, Finset.filter_true_of_mem]
      intro χ _
      exact hall χ
    have hdisj : Disjoint
        (Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1))
        (Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1)) := by
      rw [Finset.disjoint_left]
      intro χ h1 h2
      rw [Finset.mem_filter] at h1 h2
      exact hone (h1.2 ▸ h2.2)
    have hcard := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, hcard8, hs1card] at hcard
    omega
  have hsum1 : ∑ χ ∈ Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1),
      Module.finrank F (wt E χ) = a + 3 * c := by
    set s1 := Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1) with hs1
    change ∑ χ ∈ s1, Module.finrank F (wt E χ) = a + 3 * c
    have h1mem : (1 : ↥E →* Fˣ) ∈ s1 := by
      rw [hs1, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp⟩
    have hs1card' : s1.card = 4 := by rw [hs1]; exact hs1card
    rw [← Finset.add_sum_erase s1 _ h1mem]
    have hrest : ∑ χ ∈ s1.erase (1 : ↥E →* Fˣ),
        Module.finrank F (wt E χ) = 3 * c := by
      rw [Finset.sum_congr rfl (fun χ hχ => hdim χ (Finset.ne_of_mem_erase hχ)),
        Finset.sum_const, smul_eq_mul]
      rw [Finset.card_erase_of_mem h1mem, hs1card']
    rw [hrest]
  have hsnegsum : ∑ χ ∈ Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1),
      Module.finrank F (wt E χ) = 4 * c := by
    set sneg := Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1) with hsneg
    change ∑ χ ∈ sneg, Module.finrank F (wt E χ) = 4 * c
    have hsnegcard' : sneg.card = 4 := by rw [hsneg]; exact hsnegcard
    rw [Finset.sum_congr rfl (fun χ hχ => hdim χ (by
        intro h1
        have hb1' : χ ⟨b, hbE⟩ = 1 := by rw [h1]; rfl
        have hneg' := (Finset.mem_filter.mp hχ).2
        rw [hb1'] at hneg'
        exact hone hneg')),
      Finset.sum_const, smul_eq_mul, hsnegcard']
  have hfix1 : Module.finrank F (fixSpaceOf b) = a + 3 * c := by
    have hEq : fixSpaceOf b = ⨆ χ ∈ Finset.univ.filter
        (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1), wt E χ := hfix_eq ⟨b, hbE⟩
    rw [hEq, sz5e1_wct_finrank_biSup_eq_sum (M := V)
      (p := fun χ : ↥E →* Fˣ => wt E χ) hind
      (Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = 1)), hsum1]
  have hfixneg1 : Module.finrank F (fixSpaceOf (negOne F V * b)) = 4 * c := by
    have hEq : fixSpaceOf (negOne F V * b) = ⨆ χ ∈ Finset.univ.filter
        (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1), wt E χ := by
      simpa using hfixneg_eq ⟨b, hbE⟩
    rw [hEq, sz5e1_wct_finrank_biSup_eq_sum (M := V)
      (p := fun χ : ↥E →* Fˣ => wt E χ) hind
      (Finset.univ.filter (fun χ : ↥E →* Fˣ => χ ⟨b, hbE⟩ = -1)), hsnegsum]
  exact ⟨hfix1, hfixneg1⟩

private lemma sz5e1_wfm_span_singleton_of_finrank_le_one
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (hW : Module.finrank F W ≤ 1) :
    ∃ v : V, v ∈ W ∧ ∀ x ∈ W, ∃ c : F, c • v = x := by
  obtain ⟨v₀, hv₀⟩ := (finrank_le_one_iff (K := F) (V := W)).mp hW
  refine ⟨(v₀ : V), v₀.2, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := hv₀ ⟨x, hx⟩
  exact ⟨c, by simpa using congrArg (fun y : W => (y : V)) hc⟩

private lemma sz5e1_wfm_alt_zero_of_finrank_le_one
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (hW : Module.finrank F W ≤ 1)
    (f : V →ₗ[F] V →ₗ[F] F) (halt : ∀ v, f v v = 0)
    {v w : V} (hv : v ∈ W) (hw : w ∈ W) : f v w = 0 := by
  obtain ⟨u, -, hgen⟩ := sz5e1_wfm_span_singleton_of_finrank_le_one W hW
  obtain ⟨c, hc⟩ := hgen v hv
  obtain ⟨d, hd⟩ := hgen w hw
  have hcf : f (c • u) = c • f u := LinearMap.map_smul f c u
  have hdf : f u (d • u) = d • f u u := LinearMap.map_smul (f u) d u
  rw [← hc, ← hd, hcf, LinearMap.smul_apply, hdf, smul_smul, halt u, smul_zero]

private lemma sz5e1_wfm_scalar_on_finrank_le_one
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (hW : Module.finrank F W ≤ 1)
    (g : V →ₗ[F] V) (hg : ∀ x ∈ W, g x ∈ W) :
    ∃ a : F, ∀ x ∈ W, g x = a • x := by
  obtain ⟨u, hu, hgen⟩ := sz5e1_wfm_span_singleton_of_finrank_le_one W hW
  obtain ⟨a, ha⟩ := hgen (g u) (hg u hu)
  refine ⟨a, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hgen x hx
  rw [← hc]
  calc g (c • u) = c • g u := LinearMap.map_smul g c u
    _ = c • (a • u) := by rw [← ha]
    _ = (c * a) • u := smul_smul c a u
    _ = (a * c) • u := by rw [mul_comm]
    _ = a • (c • u) := (smul_smul a c u).symm

private lemma sz5e1_wfm_commute_on_finrank_le_one
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (hW : Module.finrank F W ≤ 1)
    (g h : V →ₗ[F] V) (hg : ∀ x ∈ W, g x ∈ W) (hh : ∀ x ∈ W, h x ∈ W)
    {x : V} (hx : x ∈ W) : g (h x) = h (g x) := by
  obtain ⟨a, ha⟩ := sz5e1_wfm_scalar_on_finrank_le_one W hW g hg
  obtain ⟨b, hb⟩ := sz5e1_wfm_scalar_on_finrank_le_one W hW h hh
  rw [hb x hx, LinearMap.map_smul g b x, ha x hx, hb (a • x) (W.smul_mem a hx)]

private lemma sz5e1_wfm_mem_wt_map
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (s : V ≃ₗ[F] V)
    (hs : ∀ e ∈ E, s * e = e * s) (χ : ↥E →* Fˣ)
    {v : V} (hv : v ∈ wt E χ) : s v ∈ wt E χ := by
  rw [mem_wt] at hv ⊢
  intro e
  have hcomm : s ((e : V ≃ₗ[F] V) v) = (e : V ≃ₗ[F] V) (s v) := by
    have h := congrArg (fun f : V ≃ₗ[F] V => f v) (hs (e : V ≃ₗ[F] V) e.2)
    simpa using h
  rw [← hcomm, hv e]
  exact s.toLinearMap.map_smul _ _

private lemma sz5e1_wfm_neg_one_smul_eq_zero {F : Type} [Field F]
    (hF : ringChar F ≠ 2) (x : F)
    (h : (-1 : F) • x = x) : x = 0 := by
  rw [neg_one_smul] at h
  exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h

private lemma sz5e1_wfm_mul_eq_neg_one {F : Type} [Field F] (a b : F)
    (ha : a * a = 1) (hb : b * b = 1) (hne : a ≠ b) : a * b = -1 := by
  have ha' : a ^ 2 = 1 := by simpa [sq] using ha
  have hb' : b ^ 2 = 1 := by simpa [sq] using hb
  rcases sq_eq_one_iff.mp ha' with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hb' with rfl | rfl <;> simp_all

theorem sz5e1_weights_forms {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (E : Subgroup (V ≃ₗ[F] V))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1)
    (hwt : ∀ χ : ↥E →* Fˣ, Module.finrank F (wt E χ) ≤ 1) :
    (∀ f : V →ₗ[F] V →ₗ[F] F, (∀ v, f v v = 0) →
        (∀ e ∈ E, ∀ v w, f (e v) (e w) = f v w) → f = 0) ∧
    (∀ s t : V ≃ₗ[F] V, (∀ e ∈ E, s * e = e * s) → (∀ e ∈ E, t * e = e * t) →
        s * t = t * s) := by
  have hspan : ⨆ χ : ↥E →* Fˣ, wt E χ = ⊤ := (sz5e1_weight_decomp hF E hEc hE2).2
  constructor
  · intro f halt hinv
    have hpoint : ∀ (χ ψ : ↥E →* Fˣ) (v : V), v ∈ wt E χ →
        ∀ w : V, w ∈ wt E ψ → f v w = 0 := by
      intro χ ψ v hv w hw
      by_cases hχψ : χ = ψ
      · subst hχψ
        exact sz5e1_wfm_alt_zero_of_finrank_le_one (wt E χ) (hwt χ) f halt hv hw
      · obtain ⟨e, he⟩ : ∃ e : ↥E, χ e ≠ ψ e := by
          by_contra h
          exact hχψ (MonoidHom.ext (fun e => by
            by_contra hne
            exact h ⟨e, hne⟩))
        set a : F := ((χ e : Fˣ) : F) with ha
        set b : F := ((ψ e : Fˣ) : F) with hb
        have he2 : (e : ↥E) ^ 2 = 1 := by
          apply Subtype.ext
          simpa using hE2 (e : V ≃ₗ[F] V) e.2
        have haa : a * a = 1 := by
          have hchi : (χ e) ^ 2 = 1 := by rw [← map_pow, he2, map_one]
          have h := congrArg (fun u : Fˣ => (u : F)) hchi
          rw [ha]
          simpa [Units.val_pow_eq_pow_val, sq] using h
        have hbb : b * b = 1 := by
          have hpsi : (ψ e) ^ 2 = 1 := by rw [← map_pow, he2, map_one]
          have h := congrArg (fun u : Fˣ => (u : F)) hpsi
          rw [hb]
          simpa [Units.val_pow_eq_pow_val, sq] using h
        have hne : a ≠ b := by
          intro h
          exact he (Units.ext (by rw [← ha, ← hb]; exact h))
        have hab : a * b = -1 := sz5e1_wfm_mul_eq_neg_one a b haa hbb hne
        have hinv' := hinv (e : V ≃ₗ[F] V) e.2 v w
        rw [mem_wt] at hv hw
        have hev : (e : V ≃ₗ[F] V) v = a • v := by rw [ha]; exact hv e
        have hew : (e : V ≃ₗ[F] V) w = b • w := by rw [hb]; exact hw e
        rw [hev, hew] at hinv'
        have hL : f (a • v) (b • w) = (a * b) • f v w := by
          have h1 : f (a • v) = a • f v := LinearMap.map_smul f a v
          have h2 : f v (b • w) = b • f v w := LinearMap.map_smul (f v) b w
          rw [h1, LinearMap.smul_apply, h2, smul_smul]
        rw [hL, hab] at hinv'
        exact sz5e1_wfm_neg_one_smul_eq_zero hF (f v w) hinv'
    have hvw : ∀ v w : V, f v w = 0 := by
      intro v
      have hv : v ∈ ⨆ χ : ↥E →* Fˣ, wt E χ := by rw [hspan]; exact Submodule.mem_top
      refine Submodule.iSup_induction (p := fun χ : ↥E →* Fˣ => wt E χ)
        (motive := fun x => ∀ w : V, f x w = 0) hv ?_ ?_ ?_
      · intro χ x hx w
        have hw : w ∈ ⨆ ψ : ↥E →* Fˣ, wt E ψ := by rw [hspan]; exact Submodule.mem_top
        exact Submodule.iSup_induction (p := fun ψ : ↥E →* Fˣ => wt E ψ)
          (motive := fun y => f x y = 0) hw
          (fun ψ y hy => hpoint χ ψ x hx y hy) (by simp)
          (fun p q hp hq => by simp [map_add, hp, hq])
      · intro w; simp
      · intro x y hx hy w
        simp [map_add, hx w, hy w]
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    simpa using hvw v w
  · intro s t hs ht
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ ⨆ χ : ↥E →* Fˣ, wt E χ := by rw [hspan]; exact Submodule.mem_top
    refine Submodule.iSup_induction (p := fun χ : ↥E →* Fˣ => wt E χ)
      (motive := fun x => (s * t) x = (t * s) x) hv ?_ ?_ ?_
    · intro χ x hx
      have hcomm := sz5e1_wfm_commute_on_finrank_le_one (W := wt E χ) (hwt χ)
        s.toLinearMap t.toLinearMap
        (fun y hy => sz5e1_wfm_mem_wt_map E s hs χ hy)
        (fun y hy => sz5e1_wfm_mem_wt_map E t ht χ hy) hx
      simpa [LinearEquiv.mul_apply, LinearEquiv.coe_toLinearMap] using hcomm
    · simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
