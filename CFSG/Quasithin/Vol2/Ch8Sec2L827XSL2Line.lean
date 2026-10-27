module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2Basis

public section

namespace CFSG.Quasithin.H13.L827X.SL2Orb

variable {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module F E]

instance finite_linearEquiv [Finite E] : Finite (E ≃ₗ[F] E) :=
  Finite.of_injective (fun g : E ≃ₗ[F] E => (g : E → E))
    (fun _ _ h => LinearEquiv.ext (fun x => congrFun h x))

@[expose] def lineStab (Λ : Subgroup (E ≃ₗ[F] E)) {x : E} (hx : x ≠ 0) : Subgroup Λ where
  carrier := {g | ∃ c : F, (g : E ≃ₗ[F] E) x = c • x}
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    change (g : E ≃ₗ[F] E) ((h : E ≃ₗ[F] E) x) = (c * d) • x
    rw [hd, map_smul, hc, smul_smul, mul_comm]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hx
      have h0 : (g : E ≃ₗ[F] E) x = 0 := by rw [hc, zero_smul]
      calc x = (g : E ≃ₗ[F] E).symm ((g : E ≃ₗ[F] E) x) := by simp
        _ = 0 := by rw [h0, map_zero]
    refine ⟨c⁻¹, ?_⟩
    have key : (g : E ≃ₗ[F] E) (c⁻¹ • x) = x := by
      rw [map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    show (g : E ≃ₗ[F] E).symm x = c⁻¹ • x
    rw [LinearEquiv.symm_apply_eq, key]

theorem three_le_index_lineStab [Finite E] (hE : Module.finrank F E = 2)
    (Λ : Subgroup (E ≃ₗ[F] E)) [Group.IsPerfect Λ] (hns : ¬ Group.IsSolvable Λ)
    {x : E} (hx : x ≠ 0) : 3 ≤ (lineStab Λ hx).index := by
  classical
  by_contra hlt
  push Not at hlt
  have hne0 : (lineStab Λ hx).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard_quot : Nat.card (Λ ⧸ lineStab Λ hx) = (lineStab Λ hx).index := rfl
  have hle2 : (lineStab Λ hx).index = 1 ∨ (lineStab Λ hx).index = 2 := by omega
  rcases hle2 with h1 | h2
  ·
    have htop : lineStab Λ hx = ⊤ := Subgroup.index_eq_one.mp h1
    obtain ⟨b, hb⟩ := exists_basis_zero_eq hE hx
    have hmemline : ∀ g : Λ, ∃ c : F, (g : E ≃ₗ[F] E) x = c • x := by
      intro g
      have : g ∈ lineStab Λ hx := by rw [htop]; exact Subgroup.mem_top g
      exact this
    have hcol : ∀ g : Λ, matHom b (g : E ≃ₗ[F] E) 1 0 = 0 := by
      intro g
      obtain ⟨c, hc⟩ := hmemline g
      exact (matHom_col_zero b (g : E ≃ₗ[F] E) c (by rw [hb]; exact hc)).2
    have hM00ne : ∀ g : Λ, matHom b (g : E ≃ₗ[F] E) 0 0 ≠ 0 := by
      intro g h0
      have hd := det_matHom b (g : E ≃ₗ[F] E)
      rw [det_eq_one_of_isPerfect Λ g, Matrix.det_fin_two, h0, hcol g] at hd
      simp at hd
    let cHom : Λ →* Fˣ :=
      { toFun := fun g => Units.mk0 (matHom b (g : E ≃ₗ[F] E) 0 0) (hM00ne g)
        map_one' := by
          ext
          simp
        map_mul' := by
          intro g h
          ext
          simp [Matrix.mul_apply, Fin.sum_univ_two, hcol h] }
    haveI : Group.IsPerfect cHom.range := Group.IsPerfect.range cHom
    haveI : Subsingleton cHom.range := inferInstance
    have hc1 : ∀ g : Λ, matHom b (g : E ≃ₗ[F] E) 0 0 = 1 := by
      intro g
      have h := congrArg Subtype.val
        (Subsingleton.elim (⟨cHom g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : cHom.range) 1)
      have h' := congrArg Units.val h
      simpa [cHom] using h'
    have hfix : ∀ g : Λ, (g : E ≃ₗ[F] E) (b 0) = b 0 := by
      intro g
      apply b.repr.injective
      ext i
      have key : b.repr ((g : E ≃ₗ[F] E) (b 0)) i = matHom b (g : E ≃ₗ[F] E) i 0 :=
        (matHom_apply_entry b (g : E ≃ₗ[F] E) i 0).symm
      rw [key]
      fin_cases i
      · simp [hc1 g, Module.Basis.repr_self, Finsupp.single_apply]
      · simp [hcol g, Module.Basis.repr_self, Finsupp.single_apply]
    obtain ⟨hcomm, -⟩ := fixing_comm_card_dvd (F := F) (E := E) b Λ.subtype Subtype.val_injective
      (fun g => det_eq_one_of_isPerfect Λ g) hfix
    haveI := hcomm
    exact hns inferInstance
  ·
    haveI : (lineStab Λ hx).Normal := Subgroup.normal_of_index_eq_two h2
    haveI : IsCyclic (Λ ⧸ lineStab Λ hx) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card (by rw [hcard_quot, h2])
    haveI : IsMulCommutative (Λ ⧸ lineStab Λ hx) := inferInstance
    have hsub : Subsingleton (Λ ⧸ lineStab Λ hx) :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    have hle := Finite.card_le_one_iff_subsingleton.mpr hsub
    rw [hcard_quot, h2] at hle
    omega

theorem line_bound [Finite E] (hE : Module.finrank F E = 2)
    (Λ : Subgroup (E ≃ₗ[F] E)) [Group.IsPerfect Λ] (hns : ¬ Group.IsSolvable Λ)
    {x : E} (hx : x ≠ 0) (ℓ : Submodule F E) (hℓ : Module.finrank F ℓ = 1) :
    3 * Set.ncard ({y : E | ∃ g ∈ Λ, g x = y} ∩ (ℓ : Set E)) ≤
      Set.ncard {y : E | ∃ g ∈ Λ, g x = y} := by
  classical
  have hidx := three_le_index_lineStab hE Λ hns hx
  have hOorb : {y : E | ∃ g ∈ Λ, g x = y} = MulAction.orbit Λ x := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨⟨g, hg⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [hOorb]
  set O : Set E := MulAction.orbit Λ x with hO
  set A : Set E := O ∩ (ℓ : Set E) with hA_def
  set stab := MulAction.stabilizer Λ x with hstab
  set S := lineStab Λ hx with hS
  have hstabcard : Nat.card stab * stab.index = Nat.card Λ := Subgroup.card_mul_index stab
  have hidx_orb : stab.index = O.ncard := MulAction.index_stabilizer Λ x
  have hScard : Nat.card S * S.index = Nat.card Λ := Subgroup.card_mul_index S
  have hsec : ∀ y ∈ O, ∃ g : Λ, g • x = y := by
    intro y hy
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, hg⟩
  choose! sec hsec using hsec
  have horb_ne : ∀ g : Λ, g • x ≠ 0 := by
    intro g h0
    apply hx
    have h0' : (g : E ≃ₗ[F] E) x = 0 := h0
    calc x = (g : E ≃ₗ[F] E).symm ((g : E ≃ₗ[F] E) x) := by simp
      _ = 0 := by rw [h0', map_zero]
  have hsS : ∀ s ∈ stab, s ∈ S := by
    intro s hs
    have hs' : (s : E ≃ₗ[F] E) x = x := hs
    exact ⟨1, by rw [one_smul]; exact hs'⟩
  rcases Set.eq_empty_or_nonempty A with hempty | hne
  · rw [hempty, Set.ncard_empty]
    simp
  obtain ⟨y0, hy0O, hy0ℓ⟩ := hne
  set g0 : Λ := sec y0 with hg0
  have hg0x : (g0 : E ≃ₗ[F] E) x = y0 := hsec y0 hy0O
  have hy0_ne : y0 ≠ 0 := by
    rw [← hg0x]
    exact fun h => horb_ne g0 h
  have hmemS : ∀ y ∈ A, ∃ c : F, ((g0⁻¹ * sec y : Λ) : E ≃ₗ[F] E) x = c • x := by
    intro y hy
    obtain ⟨hyO, hyℓ⟩ := hy
    have hline : ∀ w : ℓ, ∃ c : F, c • (⟨y0, hy0ℓ⟩ : ℓ) = w :=
      (finrank_eq_one_iff_of_nonzero' (⟨y0, hy0ℓ⟩ : ℓ)
        (fun h => hy0_ne (congrArg Subtype.val h))).mp hℓ
    obtain ⟨c, hc⟩ := hline ⟨y, hyℓ⟩
    have hcy : c • y0 = y := congrArg Subtype.val hc
    refine ⟨c, ?_⟩
    have hsy0 : (g0 : E ≃ₗ[F] E).symm y0 = x := by
      rw [← hg0x, LinearEquiv.symm_apply_apply]
    have hsecy : ((sec y : Λ) : E ≃ₗ[F] E) x = y := hsec y hyO
    show (g0 : E ≃ₗ[F] E).symm (((sec y : Λ) : E ≃ₗ[F] E) x) = c • x
    rw [hsecy, ← hcy, map_smul, hsy0]
  let Φ : A × stab → S := fun p =>
    ⟨g0⁻¹ * sec p.1.1 * (p.2 : Λ),
      S.mul_mem (show g0⁻¹ * sec p.1.1 ∈ S from hmemS p.1.1 p.1.2) (hsS _ p.2.2)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨y, hy⟩, s⟩ ⟨⟨y', hy'⟩, s'⟩ h
    have h1 : g0⁻¹ * sec y * (s : Λ) = g0⁻¹ * sec y' * (s' : Λ) := congrArg Subtype.val h
    have h2 : sec y * (s : Λ) = sec y' * (s' : Λ) := by
      have := congrArg (fun u => g0 * u) h1
      simpa [mul_assoc] using this
    have hs : (s : E ≃ₗ[F] E) x = x := MulAction.mem_stabilizer_iff.mp s.2
    have hs' : (s' : E ≃ₗ[F] E) x = x := MulAction.mem_stabilizer_iff.mp s'.2
    have hyy : y = y' := by
      have e1 := congrArg (fun u : Λ => (u : E ≃ₗ[F] E) x) h2
      simp only [Subgroup.coe_mul, LinearEquiv.coe_coe, LinearEquiv.mul_apply] at e1
      have hy1 : ((sec y : Λ) : E ≃ₗ[F] E) x = y := hsec y hy.1
      have hy2 : ((sec y' : Λ) : E ≃ₗ[F] E) x = y' := hsec y' hy'.1
      rw [hs, hs', hy1, hy2] at e1
      exact e1
    subst hyy
    have hss : (s : Λ) = (s' : Λ) := mul_left_cancel h2
    have hss' : s = s' := Subtype.ext hss
    subst hss'
    rfl
  have hcardle : Nat.card A * Nat.card stab ≤ Nat.card S := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective Φ hΦ
  have hA : Nat.card A = A.ncard := Nat.card_coe_set_eq A
  rw [hA] at hcardle
  have hB : 0 < Nat.card stab := Nat.card_pos
  have h3 : 3 * Nat.card S ≤ Nat.card Λ := by
    rw [← hScard]
    nlinarith [hidx]
  have hOc : Nat.card Λ = Nat.card stab * O.ncard := by
    rw [← hstabcard, hidx_orb]
  have key : (3 * A.ncard) * Nat.card stab ≤ O.ncard * Nat.card stab := by
    calc (3 * A.ncard) * Nat.card stab
        = 3 * (A.ncard * Nat.card stab) := by ring
      _ ≤ 3 * Nat.card S := Nat.mul_le_mul_left 3 hcardle
      _ ≤ Nat.card Λ := h3
      _ = Nat.card stab * O.ncard := hOc
      _ = O.ncard * Nat.card stab := by ring
  exact Nat.le_of_mul_le_mul_right key hB

end CFSG.Quasithin.H13.L827X.SL2Orb

end
