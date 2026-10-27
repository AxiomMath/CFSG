module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeA

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem unit_eq_one_of_pow_prime_pow {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1)
    {u : Kˣ} {k : ℕ} (hu : u ^ p ^ k = 1) : u = 1 := by
  have h1 : orderOf u ∣ p ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard u
  have hcop : Nat.Coprime (p ^ k) (Nat.card K - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK)
  have h3 : orderOf u = 1 := Nat.dvd_one.mp (by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this)
  exact orderOf_eq_one_iff.mp h3

theorem exists_lift_of_not_dvd {d p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 0 < d)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    ∃ E : Subgroup (GL (Fin d) K), IsElemAbelian p E ∧ Nat.card E = Nat.card X ∧
      ∀ g ∈ E, (g : Matrix (Fin d) (Fin d) K).det = 1 := by
  classical
  have := Fact.mk hp
  set Xt := X.comap (conjAut d K) with hXt
  let f : Xt →* X := ((conjAut d K).comp Xt.subtype).codRestrict X fun A => A.2
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨A, rfl⟩ := hXI hx
    exact ⟨⟨A, hx⟩, rfl⟩
  have hker : ∀ g : Xt, f g = 1 → ∀ k : ℕ, g ^ p ^ k = 1 → g = 1 := by
    intro g hg k hgk
    have h1 : conjAut d K (g : GL (Fin d) K) = 1 := congrArg Subtype.val hg
    obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one h1
    obtain ⟨u, hu⟩ := exists_unit_of_scalar hd hc
    have hu1 : u ^ p ^ k = 1 := by
      have h1 : (Matrix.GeneralLinearGroup.scalar (Fin d) (u ^ p ^ k) : GL (Fin d) K) = 1 := by
        rw [map_pow, ← hu]
        exact congrArg Subtype.val hgk
      have h2 := congrArg
        (fun A : GL (Fin d) K => (A : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩) h1
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
      exact Units.ext h2
    have hu2 := unit_eq_one_of_pow_prime_pow hp hpK hu1
    exact Subtype.ext (by rw [hu, hu2, map_one]; rfl)
  have : Finite Xt := inferInstance
  obtain ⟨P⟩ : Nonempty (Sylow p Xt) := inferInstance
  have hPinj : ∀ g ∈ (P : Subgroup Xt), f g = 1 → g = 1 := by
    intro g hg h1
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    exact hker g h1 k (congrArg Subtype.val hk)
  have hfinj : Function.Injective (f.comp (P : Subgroup Xt).subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hPinj g g.2 hg)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hX)
  have hkerp : ¬ p ∣ Nat.card f.ker := by
    intro h
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) p h
    have hgp : (g : Xt) ^ p ^ 1 = 1 := by
      rw [pow_one]
      have h0 := pow_orderOf_eq_one g
      rw [hg] at h0
      exact congrArg Subtype.val h0
    have h1 := hker g (MonoidHom.mem_ker.mp g.2) 1 hgp
    have h2 : orderOf g = 1 := by rw [orderOf_eq_one_iff]; exact Subtype.ext h1
    rw [hg] at h2
    exact hp.one_lt.ne' h2
  have hcardXt : Nat.card Xt = Nat.card f.ker * Nat.card X := by
    rw [← Subgroup.card_ker_mul_card_range f, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  have hP : Nat.card (P : Subgroup Xt) = Nat.card X := by
    rw [P.card_eq_multiplicity, hcardXt, hk, Nat.factorization_mul (Nat.pos_iff_ne_zero.mp
      Nat.card_pos) (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hkerp, zero_add, hp.factorization_pow,
      Finsupp.single_eq_same]
  refine ⟨(P : Subgroup Xt).map Xt.subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show (a : GL (Fin d) K) * b = b * a
    have hc : a * b * a⁻¹ * b⁻¹ = 1 := hPinj _ ((P : Subgroup Xt).mul_mem
      ((P : Subgroup Xt).mul_mem ((P : Subgroup Xt).mul_mem ha hb) ((P : Subgroup Xt).inv_mem ha))
        ((P : Subgroup Xt).inv_mem hb)) (by
      have hab : f a * f b = f b * f a := Subtype.ext (TableB.IsElemAbelian.comm hX (f a).2 (f b).2)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
      group)
    have hc' : a * b = b * a := by
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [hc, one_mul]
    exact congrArg Subtype.val hc'
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ p = 1 := hPinj _ ((P : Subgroup Xt).pow_mem ha p) (by
      rw [map_pow]; exact Subtype.ext (hX.2 _ (f a).2))
    exact congrArg Subtype.val h1
  · rw [Subgroup.card_map_of_injective Xt.subtype_injective, hP]
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ p = 1 := hPinj _ ((P : Subgroup Xt).pow_mem ha p) (by
      rw [map_pow]; exact Subtype.ext (hX.2 _ (f a).2))
    have h2 : (Matrix.GeneralLinearGroup.det (a : GL (Fin d) K)) ^ p ^ 1 = 1 := by
      rw [pow_one, ← map_pow]
      have : (a : GL (Fin d) K) ^ p = 1 := congrArg Subtype.val h1
      rw [this, map_one]
    have h3 := unit_eq_one_of_pow_prime_pow hp hpK h2
    have h4 := congrArg Units.val h3
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h4

theorem card_lt_cube_pgl_of_le_three [CharP K 2] {d p : ℕ} (hd : 0 < d) (hd3 : d ≤ 3)
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup (MulAut (projectiveSL d K))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X < p ^ 3 := by
  by_cases hpK : p ∣ Nat.card K - 1
  · exact card_lt_of_torality hp hpK hd hd3 (ggPGLTorality_holds hp hp2 hpK) hX hXI
  · obtain ⟨E, hE, hcard, hdet⟩ := exists_lift_of_not_dvd hp hpK hd hX hXI
    rw [← hcard]
    by_cases hd' : d = 3
    · subst d
      have h := CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_gl hp
        (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2) (Fintype.card_fin 3) E
        (fun g hg h hh => TableB.IsElemAbelian.comm hE hg hh) (fun g hg => hE.2 g hg) hdet
      exact h.trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
    · have h := CFSG.RankThree.PartOne.LIT.card_le_pow_card_gl hp
        (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2) E
        (fun g hg h hh => TableB.IsElemAbelian.comm hE hg hh) (fun g hg => hE.2 g hg)
      simp only [Fintype.card_fin] at h
      exact h.trans_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))

theorem card_lt_cube_pgl3 [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut (projectiveSL 3 K))} (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL 3 K))) ⊆ Set.range (conjAut 3 K)) :
    Nat.card X < p ^ 3 :=
  card_lt_cube_pgl_of_le_three (by norm_num) le_rfl hp hp2 hX hXI

end TypeA

theorem recipeLinear_card_lt_three_all {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear 3 (2 ^ N) Q) :
    LargeEvenRecipeLinear 3 (2 ^ N) fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  exact StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv 3 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TypeA.card_lt_cube_pgl3 hp hp2 hX' hX'I) hXI hX

theorem largeEvenLabelAll_card_lt_A2_all {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (ht : lab.tag = .A) (hl : lab.rank = 2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl
  subst ht hl
  intro Q hQ
  exact recipeLinear_card_lt_three_all (N := n) hp hp2 hQ

namespace TableBUE

open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K] {n p : ℕ}

theorem card_lt_unitary_three_all (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h2 : 2 < 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n))) (LargeEvenGUSet (Fin 3) K (2 ^ n)),
        ∀ l : L', φ (ψ l) = ψ (a l)) :
    Nat.card A < p ^ 3 := by
  classical
  have hdq : (3, 2 ^ n) ≠ (3, 2) := by
    intro he
    have := congrArg Prod.snd he
    simp only at this
    omega
  have : CharP K 2 := h.charP
  obtain ⟨p', hp', hp'q⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n + 1) (by omega)
  have hN := gu_subset_normalizer (d := 3) h
  set ρ := TableB.projConj (LargeEvenSUGroup (Fin 3) K (2 ^ n)) with hρ
  set N₀ : Subgroup
      (Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K))) :=
    (TypeA.inducedSub ψ A).comap ρ with hN₀
  set χ : Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K)) →*
      MulAut (projectiveSL 3 K) :=
    (conjAut 3 K).comp
      (Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K))).subtype
    with hχ
  set X := N₀.map χ with hX
  have hscal : ∀ M ∈ N₀, ρ M = 1 → χ M = 1 := by
    intro M _ hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK le_rfl hdq hp' hp'q hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hab := TypeA.isElemAbelian_inducedSub hψ hA (ψ := ψ)
  have hXab : IsElemAbelian p X := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hab hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ (N₀.mul_mem (N₀.mul_mem (N₀.mul_mem hM hM') (N₀.inv_mem hM))
        (N₀.inv_mem hM')) hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (N₀.pow_mem hM p) (by rw [map_pow]; exact hab.2 _ hM)
  have hXI : (X : Set (MulAut (projectiveSL 3 K))) ⊆ Set.range (conjAut 3 K) := by
    rintro _ ⟨M, -, rfl⟩
    exact ⟨M, rfl⟩
  have hlift : ∀ a : A,
      ∃ M : Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K)),
      ∀ l : L', ρ M (ψ l) = ψ ((a : MulAut L') l) := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨M, hMgu, hMeq⟩ := TableB.exists_eq_projConj hN hφI
    exact ⟨⟨M, hN hMgu⟩, fun l => by rw [← hMeq]; exact hφ l⟩
  choose Mf hMf using hlift
  have hMN : ∀ a : A, Mf a ∈ N₀ := fun a =>
    TypeA.mem_inducedSub.mpr ⟨a, a.2, hMf a⟩
  let f : A → X := fun a => ⟨χ (Mf a), Mf a, hMN a, rfl⟩
  have hf : Function.Injective f := by
    intro a b hab'
    have h1 : χ ((Mf a)⁻¹ * Mf b) = 1 := by
      have := congrArg Subtype.val hab'
      simp only [f] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    have hz := mem_scalars_of_eq_scalar hc
    have h2 : ρ ((Mf a)⁻¹ * Mf b) = 1 := by
      have he : (Mf a)⁻¹ * Mf b = ⟨_, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
      rw [he]
      exact TableB.projConj_of_scalar _ hz
    have h3 : ρ (Mf a) = ρ (Mf b) := by
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2
    apply Subtype.ext
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hMf a l, ← hMf b l, h3]
  have hle := Nat.card_le_card_of_injective f hf
  have hlt := TypeA.card_lt_cube_pgl3 hp hp2 hXab hXI
  omega

end TableBUE

theorem largeEvenLabelAll_lift_card_lt_unitaryThree_all {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA)
    (hl : lab.rank = 2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl
  subst ht hl
  obtain ⟨hn, -, hl22⟩ := hlab
  dsimp only at hn hl22
  have h2 : 2 < 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl22 rfl)
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  exact ⟨K, i1, i2, hK, hq', fun L' _ _ ψ hψ hker hperf A hA hAI =>
    TableBUE.card_lt_unitary_three_all (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hp2 hψ
      hker hperf hA hAI⟩

open scoped commutatorElement in
theorem largeEvenLabelAll_card_lt_unitaryThree_all {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA)
    (hl : lab.rank = 2) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl
  subst ht hl
  obtain ⟨hn, -, hl22⟩ := hlab
  dsimp only at hn hl22
  have h2 : 2 < 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl22 rfl)
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun hs hna X hXI hX => ?_⟩
  have : Finite (LargeEvenSUGroup (Fin 3) K (2 ^ n)) := Subtype.finite
  have : Finite (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) = ⊤ := by
    have : (commutator (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))).Normal :=
      Subgroup.commutator_normal ⊤ ⊤
    rcases hs.eq_bot_or_eq_top_of_normal (commutator _) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.mp hc
    · exact h
  refine TableBUE.card_lt_unitary_three_all (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hp2
    (ψ := MonoidHom.id _) Function.surjective_id ?_ hperf hX fun a ha => ⟨a, hXI ha, fun _ => rfl⟩
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

end CFSG.StandardType

end
