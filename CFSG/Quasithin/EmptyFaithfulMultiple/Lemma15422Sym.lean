module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineSymmetricSix
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Core

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6 Matrix
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace L15422

section Mobius

variable {F : Type} [Field F]

private theorem upper_eq_transvection' (b : F) :
    CFSG.GorensteinWalter.sl2UpperUnipotent b = Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.GorensteinWalter.sl2UpperUnipotent, Matrix.SpecialLinearGroup.transvection_coe]

private theorem lower_eq_weyl_upper' (b : F) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) b =
      CFSG.GorensteinWalter.sl2SymplecticMatrix F * CFSG.GorensteinWalter.sl2UpperUnipotent (-b) *
        (CFSG.GorensteinWalter.sl2SymplecticMatrix F)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change (1 : Matrix (Fin 2) (Fin 2) F) + Matrix.single 1 0 b =
    ((CFSG.GorensteinWalter.sl2SymplecticMatrix F).val *
        (CFSG.GorensteinWalter.sl2UpperUnipotent (-b)).val) *
      !![(CFSG.GorensteinWalter.sl2SymplecticMatrix F).val 1 1,
          -(CFSG.GorensteinWalter.sl2SymplecticMatrix F).val 0 1;
        -(CFSG.GorensteinWalter.sl2SymplecticMatrix F).val 1 0,
          (CFSG.GorensteinWalter.sl2SymplecticMatrix F).val 0 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.GorensteinWalter.sl2UpperUnipotent, CFSG.GorensteinWalter.sl2SymplecticMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem map_transvection (σ : F ≃+* F) {i j : Fin 2} (hij : i ≠ j) (b : F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.transvection hij b) =
      Matrix.SpecialLinearGroup.transvection hij (σ b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.map_add _ (map_add σ.toRingHom),
    Matrix.map_one _ (map_zero σ.toRingHom) (map_one σ.toRingHom), Matrix.map_single]
  rfl

theorem fieldExtension_conj_coordinatePSLAction (σ : F ≃+* F) (A : SpecialLinearGroup (Fin 2) F) :
    fieldExtension F σ * coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F A) *
        (fieldExtension F σ)⁻¹ =
      coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F
        (Matrix.SpecialLinearGroup.map σ.toRingHom A)) := by
  obtain ⟨s, hs⟩ : ∃ s, s = fieldExtension F σ := ⟨_, rfl⟩
  rw [← hs]
  refine Matrix.SL2.transvection_induction
    (fun A => s * coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F A) * s⁻¹ =
      coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F
        (Matrix.SpecialLinearGroup.map σ.toRingHom A))) ?_ ?_ A
  · intro i j hij c
    rw [map_transvection]
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change s * coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F
          (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)) * s⁻¹ =
        coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F
          (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (σ c)))
      rw [← upper_eq_transvection', ← upper_eq_transvection', coordinatePSLAction_upper,
        coordinatePSLAction_upper, mul_inv_eq_iff_eq_mul, hs]
      exact CFSG.LocalAnalysis.ComponentInitial.FieldNine.fieldExtension_mul_translation σ c
    · change s * coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F
          (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c)) * s⁻¹ =
        coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F
          (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (σ c)))
      rw [lower_eq_weyl_upper', lower_eq_weyl_upper']
      simp only [map_mul, map_inv]
      rw [show CFSG.GorensteinWalter.psl2QuotientMap F
          (CFSG.GorensteinWalter.sl2SymplecticMatrix F) =
          CFSG.GorensteinWalter.psl2SymplecticElement F from rfl,
        coordinatePSLAction_weyl, coordinatePSLAction_upper, coordinatePSLAction_upper]
      have hsi := CFSG.LocalAnalysis.ComponentInitial.FieldNine.fieldExtension_mul_inversion σ
      have hst := CFSG.LocalAnalysis.ComponentInitial.FieldNine.fieldExtension_mul_translation σ
        (-c)
      rw [map_neg, ← hs] at hst
      rw [← hs] at hsi
      calc s * (inversion F * translation F (-c) * (inversion F)⁻¹) * s⁻¹
          = (s * inversion F) * translation F (-c) * (inversion F)⁻¹ * s⁻¹ := by group
        _ = inversion F * (s * translation F (-c)) * (inversion F)⁻¹ * s⁻¹ := by
          rw [hsi]; group
        _ = inversion F * translation F (-σ c) * (s * (inversion F)⁻¹ * s⁻¹) := by
          rw [hst]; group
        _ = inversion F * translation F (-σ c) * (inversion F)⁻¹ := by
          have : s * (inversion F)⁻¹ * s⁻¹ = (inversion F)⁻¹ := by
            rw [mul_inv_eq_iff_eq_mul, eq_comm, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hsi,
              mul_assoc, mul_inv_cancel, mul_one]
          rw [this]
    · exact (hij rfl).elim
  · intro A B hA hB
    simp only [map_mul]
    rw [← hA, ← hB]
    group

end Mobius

section Conj

variable {D J : Type*} [Group D] [Group J]

theorem nonempty_mulEquiv_of_conj [Finite D] [Finite J] {N₀ : Subgroup D} (hidx : N₀.index = 2)
    {G' : Subgroup J} (hJ : ∀ j : J, (∀ x ∈ G', j * x = x * j) → j = 1)
    (hD : ∀ d : D, (∀ x ∈ N₀, d * x = x * d) → d = 1) (E : ↥N₀ ≃* ↥G') {t : D}
    (ht : t ∉ N₀) {τ : J}
    (hτ : ∀ n m : N₀, (m : D) = t * n * t⁻¹ → (E m : J) = τ * E n * τ⁻¹)
    (hcard : Nat.card D = Nat.card J) : Nonempty (D ≃* J) := by
  have hN : N₀.Normal := Subgroup.normal_of_index_eq_two hidx
  let cj : D → N₀ → N₀ := fun d n => ⟨d * n * d⁻¹, hN.conj_mem n n.2 d⟩
  let R : D → J → Prop := fun d j => ∀ n : N₀, (E (cj d n) : J) = j * E n * j⁻¹
  have hEcj : ∀ (d : N₀) (n : N₀),
      (E (cj (d : D) n) : J) = (E d : J) * (E n : J) * (E d : J)⁻¹ := by
    intro d n
    have : cj (d : D) n = d * n * d⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]
    rfl
  have hex : ∀ d, ∃ j, R d j := by
    intro d
    by_cases hd : d ∈ N₀
    · exact ⟨E ⟨d, hd⟩, fun n => hEcj ⟨d, hd⟩ n⟩
    · have hd₀ : t⁻¹ * d ∈ N₀ := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
        exact iff_of_false ht hd
      refine ⟨τ * E ⟨t⁻¹ * d, hd₀⟩, fun n => ?_⟩
      have h1 := hτ (cj (t⁻¹ * d) n) (cj d n) (by
        change d * n * d⁻¹ = t * (t⁻¹ * d * n * (t⁻¹ * d)⁻¹) * t⁻¹
        group)
      rw [h1, hEcj ⟨t⁻¹ * d, hd₀⟩ n]
      group
  have huniq : ∀ d j j', R d j → R d j' → j = j' := by
    intro d j j' hj hj'
    have hc : ∀ x ∈ G', (j'⁻¹ * j) * x = x * (j'⁻¹ * j) := by
      intro x hx
      obtain ⟨n, hn⟩ := E.surjective ⟨x, hx⟩
      have h1 := (hj n).symm.trans (hj' n)
      rw [hn] at h1
      change j * x * j⁻¹ = j' * x * j'⁻¹ at h1
      calc j'⁻¹ * j * x = j'⁻¹ * (j * x * j⁻¹) * j := by group
        _ = j'⁻¹ * (j' * x * j'⁻¹) * j := by rw [h1]
        _ = x * (j'⁻¹ * j) := by group
    have := hJ _ hc
    calc j = j' * (j'⁻¹ * j) := by group
      _ = j' := by rw [this, mul_one]
  choose Ψ hΨ using hex
  have hmul : ∀ a b, Ψ (a * b) = Ψ a * Ψ b := by
    intro a b
    refine huniq (a * b) _ _ (hΨ (a * b)) fun n => ?_
    have e1 : cj (a * b) n = cj a (cj b n) := Subtype.ext (by
      change a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹
      group)
    rw [e1, hΨ a, hΨ b]
    group
  let Ψh : D →* J := MonoidHom.mk' Ψ hmul
  have hinj : Function.Injective Ψh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    have hd1 : Ψ d = 1 := hd
    refine Subgroup.mem_bot.mpr (hD d fun x hx => ?_)
    have h1 := hΨ d ⟨x, hx⟩
    rw [hd1, one_mul, inv_one, mul_one] at h1
    have h2 : cj d ⟨x, hx⟩ = ⟨x, hx⟩ := E.injective (Subtype.ext h1)
    have h3 : d * x * d⁻¹ = x := congrArg Subtype.val h2
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [h3]
  exact ⟨MulEquiv.ofBijective Ψh ((Nat.bijective_iff_injective_and_card Ψh).mpr ⟨hinj, hcard⟩)⟩

end Conj

section Nine

theorem nonempty_mulEquiv_perm_six {D : Type} [Group D] [Finite D]
    (hQ : Open.pCore 2 D = ⊥) (hL : IsL2FieldExt 3 D) :
    Nonempty (D ≃* Equiv.Perm (Fin 6)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, hF, hFin, hcard, N₀, e, t, g, hidx, ht, hact⟩ := hL
  let _ : Fintype F := Fintype.ofFinite F
  have hF9 : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨⟨σ, hσ⟩, hΦ⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_semilinear_symmetric_six_isomorphism F hF9
  obtain ⟨Φ, -⟩ := hΦ σ hσ
  set J := Subgroup.closure ((coordinateG F : Set (Equiv.Perm (Omega F))) ∪ {fieldExtension F σ})
  have hGJ : coordinateG F ≤ J := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hsJ : fieldExtension F σ ∈ J := Subgroup.subset_closure (Or.inr rfl)
  set G' := (coordinateG F).subgroupOf J
  let ψ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  let E₀ : ↥N₀ ≃* ↥(coordinateG F) := (e.trans ψ.symm).trans (pslEquivCoordinateG F)
  let E : ↥N₀ ≃* ↥G' := E₀.trans (Subgroup.subgroupOfEquivOfLe hGJ).symm
  have hEval : ∀ n : N₀, ((E n : J) : Equiv.Perm (Omega F)) =
      coordinatePSLAction F (ψ.symm (e n)) := fun n => rfl
  have hGcard : Nat.card (coordinateG F) = 360 :=
    CFSG.LocalAnalysis.ComponentInitial.FieldNine.card_coordinateG_of_card_eq_nine
      (by rw [Nat.card_eq_fintype_card, hF9])
  have hJcard : Nat.card J = 720 := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hN₀card : Nat.card N₀ = 360 := by rw [Nat.card_congr E₀.toEquiv, hGcard]
  have hDcard : Nat.card D = 720 := by rw [← N₀.index_mul_card, hidx, hN₀card]
  have hG'card : Nat.card G' = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGJ).toEquiv, hGcard]
  have hA6 : G'.map Φ.toMonoidHom = alternatingGroup (Fin 6) := by
    refine Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_
    have h := (G'.map Φ.toMonoidHom).card_mul_index
    rw [Subgroup.card_map_of_injective Φ.injective, hG'card, Nat.card_perm, Nat.card_fin] at h
    have h720 : Nat.factorial 6 = 360 * 2 := by decide
    rw [h720] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hcen : ∀ j : J, (∀ x ∈ G', j * x = x * j) → j = 1 := by
    intro j hj
    have : Φ j = 1 := perm_six_eq_one_of_forall_commute fun τ hτ => by
      rw [← hA6] at hτ
      obtain ⟨x, hx, rfl⟩ := hτ
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hj x hx]
    exact Φ.injective (this.trans Φ.map_one.symm)
  have hN₀n : N₀.Normal := Subgroup.normal_of_index_eq_two hidx
  have hZ : ∀ x : N₀, (∀ y : N₀, x * y = y * x) → x = 1 := by
    intro x hx
    have h1 : (E x : J) = 1 := by
      refine hcen _ fun z hz => ?_
      obtain ⟨y, hy⟩ := E.surjective ⟨z, hz⟩
      have := congrArg (fun w : G' => (w : J)) (congrArg E (hx y))
      simp only [map_mul, Subgroup.coe_mul] at this
      rw [hy] at this
      exact this
    have h2 : E x = 1 := Subtype.ext h1
    exact E.injective (h2.trans E.map_one.symm)
  have hD : ∀ d : D, (∀ x ∈ N₀, d * x = x * d) → d = 1 := by
    set C := Subgroup.centralizer (N₀ : Set D)
    have hCn : C.Normal := inferInstance
    have hCN : C ⊓ N₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have := hZ ⟨x, hx.2⟩ fun y => Subtype.ext
        (((Subgroup.mem_centralizer_iff.mp hx.1) y y.2).symm)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hcard2 : Nat.card C ∣ 2 := by
      have h1 : N₀.relIndex C ∣ N₀.index := Subgroup.relIndex_dvd_index_of_normal N₀ C
      rw [← Subgroup.inf_relIndex_right, inf_comm, hCN, Subgroup.relIndex_bot_left, hidx] at h1
      exact h1
    have hcard2' : Nat.card C ∣ 2 ^ 1 := by rw [pow_one]; exact hcard2
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcard2'
    have hC2 : IsPGroup 2 C := IsPGroup.of_card hm
    have hCle : C ≤ Open.pCore 2 D := CFSG.LieType.BorelTits.le_pCore 2 hCn hC2
    rw [hQ, le_bot_iff] at hCle
    intro d hd
    have hdC : d ∈ C := Subgroup.mem_centralizer_iff.mpr fun x hx => (hd x hx).symm
    rw [hCle] at hdC
    exact Subgroup.mem_bot.mp hdC
  set g' : SpecialLinearGroup (Fin 2) F :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm g
  set Mg := coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F g')
  have hMg : Mg ∈ J := hGJ (by rw [← coordinatePSLAction_range_eq_G]; exact ⟨_, rfl⟩)
  let τ : J := ⟨Mg * fieldExtension F σ, J.mul_mem hMg hsJ⟩
  have hg' : (g' : Matrix (Fin 2) (Fin 2) F) = ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
  have hg'inv : ((g'⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (((g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : ((g'⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g' : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    rw [hg'] at h1
    calc ((g'⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((g'⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (((g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
          rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hτ : ∀ n m : N₀, (m : D) = t * n * t⁻¹ → (E m : J) = τ * E n * τ⁻¹ := by
    intro n m hnm
    obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e n)
    set A' := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm A
    set B' := g' * Matrix.SpecialLinearGroup.map σ.toRingHom A' * g'⁻¹
    set B := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F B'
    have hB : ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map fun x => x ^ 3) *
          (((g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg', hg'inv,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      congr 2
      have hA' : (A' : Matrix (Fin 2) (Fin 2) F) =
          ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
          MulEquiv.apply_symm_apply]
      rw [hA']
      congr 1
      funext x
      exact hσ x
    have hm := hact n m A B hnm hA.symm hB
    have hψB : ψ.symm (e m) = CFSG.GorensteinWalter.psl2QuotientMap F B' := by
      rw [hm, MulEquiv.symm_apply_eq]
      exact (QuotientGroup.congr_mk _ _ _ _ B').symm
    have hψA : ψ.symm (e n) = CFSG.GorensteinWalter.psl2QuotientMap F A' := by
      rw [← hA, MulEquiv.symm_apply_eq]
      have := QuotientGroup.congr_mk (Subgroup.center (SpecialLinearGroup (Fin 2) F))
        ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F).subgroupOf
          (CFSG.Assembly.LowTwoRank.StatedSL 2 F))
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
        (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 F) A'
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hEval, hEval, hψB, hψA]
    change coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F B') =
      Mg * fieldExtension F σ *
        coordinatePSLAction F (CFSG.GorensteinWalter.psl2QuotientMap F A') *
        (Mg * fieldExtension F σ)⁻¹
    rw [show B' = g' * Matrix.SpecialLinearGroup.map σ.toRingHom A' * g'⁻¹ from rfl, map_mul,
      map_mul, map_inv, map_mul, map_mul, map_inv,
      ← fieldExtension_conj_coordinatePSLAction σ A']
    group
    rfl
  obtain ⟨Ψ⟩ := nonempty_mulEquiv_of_conj hidx hcen hD E ht hτ (by rw [hDcard, hJcard])
  exact ⟨Ψ.trans Φ⟩

end Nine

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
