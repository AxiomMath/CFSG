module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.Assembly.LowTwoRank

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def diagMat (x : Kˣ × Kˣ) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(x.1 : K), (x.2 : K), (((x.1 * x.2)⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩

theorem diagMat_apply (x : Kˣ × Kˣ) :
    ((diagMat x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(x.1 : K), (x.2 : K), (((x.1 * x.2)⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def diagHom : Kˣ × Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun := diagMat
  map_one' := by
    apply Subtype.ext
    rw [diagMat_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, diagMat_apply, diagMat_apply, diagMat_apply,
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring


theorem diagHom_injective : Function.Injective (diagHom (K := K)) := by
  intro x y h
  have h' : (diagMat x : Matrix (Fin 3) (Fin 3) K) = diagMat y := congrArg Subtype.val h
  rw [diagMat_apply, diagMat_apply] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

end Torus

section Main

open CFSG

theorem exists_elemAbelian_sq_of_surjective_SL3 {J : Type*} [Group J] [Finite J] {K : Type}
    [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m)
    (f : J →* ↥(StatedSL 3 K)) (hf : Function.Surjective f) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ E : Subgroup J, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ m - 1) (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  have : Fact p.Prime := ⟨hp⟩
  have hcardU : Nat.card Kˣ = 2 ^ m - 1 := by
    rw [Nat.card_units, hK]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p (hcardU ▸ hpd)
  set Z : Subgroup Kˣ := Subgroup.zpowers ζ with hZ
  have hZcard : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, hζ]
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hZp : ∀ a ∈ Z, a ^ p = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  set E0 : Subgroup (Kˣ × Kˣ) := Z.prod Z with hE0
  let δ : Kˣ × Kˣ →* StatedSL 3 K :=
    (specialLinearGroupEquivStatedSL 3 K).toMonoidHom.comp diagHom
  have hδinj : Function.Injective δ :=
    (specialLinearGroupEquivStatedSL 3 K).injective.comp diagHom_injective
  set Es : Subgroup (StatedSL 3 K) := E0.map δ with hEs
  have hEscard : Nat.card Es = p ^ 2 := by
    rw [hEs, Subgroup.card_map_of_injective hδinj, hE0,
      Nat.card_congr (Subgroup.prodEquiv Z Z).toEquiv, Nat.card_prod, hZcard, sq]
  have hEsexp : ∀ x ∈ Es, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Prod.ext (hZp _ ha.1) (hZp _ ha.2)
    rw [this, map_one]
  have hEspgroup : IsPGroup p Es := fun x => ⟨1, Subtype.ext (by simpa using hEsexp x x.2)⟩
  have hEsnc : ¬ IsCyclic Es := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hEsexp g g.2)
    have h1 : orderOf g = Nat.card Es := orderOf_eq_card_of_forall_mem_zpowers hg
    have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rw [h1, hEscard] at h2
    have h3 := Nat.le_of_dvd hp.pos h2
    nlinarith [hp.two_le]
  obtain ⟨Ps, hEsPs⟩ := IsPGroup.exists_le_sylow hEspgroup
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf p Ps
  have hPmap : (P : Subgroup J).map f = (Ps : Subgroup (StatedSL 3 K)) := by
    rw [← hP, Sylow.coe_mapSurjective]
  have hPnc : ¬ IsCyclic (P : Subgroup J) := by
    intro hcyc
    have hcyc2 : IsCyclic ↥(Ps : Subgroup (StatedSL 3 K)) := by
      have hrange : (f.comp (P : Subgroup J).subtype).range = (Ps : Subgroup (StatedSL 3 K)) := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
      have : IsCyclic ↥(f.comp (P : Subgroup J).subtype).range :=
        isCyclic_of_surjective _ (f.comp (P : Subgroup J).subtype).rangeRestrict_surjective
      rw [← hrange]
      exact this
    have hcyc3 : IsCyclic ↥(Es.subgroupOf (Ps : Subgroup (StatedSL 3 K))) := inferInstance
    exact hEsnc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEsPs).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEsPs).surjective)
  have : Fact (IsPGroup p (P : Subgroup J)) := ⟨P.isPGroup'⟩
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hPnc
  refine ⟨p, hp, hp2, E.map (P : Subgroup J).subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have := hEel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg (fun z : ↥E => ((z : ↥(P : Subgroup J)) : J)) this
  · rintro _ ⟨a, ha, rfl⟩
    have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (a : ↥(P : Subgroup J)) ha
    simpa using congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective (P : Subgroup J).subtype_injective, hEcard]

end Main

end CFSG.Quasithin.S146zW
