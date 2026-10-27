module

public import CFSG.Quasithin.Background.SmithCurtisChevType
public import CFSG.LieType.Chevalley.TorusCoordinates

public noncomputable section

namespace CFSG.Quasithin.B42G2Cur

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev

@[expose] def g2W0Word : List (Fin Tag.G2.rank) := ([0, 1, 0, 1, 0, 1] : List (Fin 2))

theorem wordProd_smul_G2 (l : List (Fin Tag.G2.rank)) (v : Fin Tag.G2.rank → ℤ) :
    (coxeterSystem .G2).wordProd l • v = l.foldr (reflect .G2) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem g2W0_single : ∀ i : Fin Tag.G2.rank,
    g2W0Word.foldr (reflect .G2) (Pi.single i 1) = -Pi.single i 1 := by
  decide +kernel

theorem g2W0_smul (α : Fin Tag.G2.rank → ℤ) :
    (coxeterSystem .G2).wordProd g2W0Word • α = -α := by
  have hf : ∀ i : Fin Tag.G2.rank, ∀ c : ℤ,
      (coxeterSystem .G2).wordProd g2W0Word • (Pi.single i c : Fin Tag.G2.rank → ℤ) =
        -(Pi.single i c : Fin Tag.G2.rank → ℤ) := by
    intro i c
    have e : (Pi.single i c : Fin Tag.G2.rank → ℤ) = c • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, smul_comm, wordProd_smul_G2, g2W0_single, smul_neg]
  conv_lhs => rw [← Finset.univ_sum_single α]
  rw [Finset.smul_sum]
  simp only [hf, Finset.sum_neg_distrib, Finset.univ_sum_single]

theorem exists_weyl_neg_G2 : ∃ w₁ : WeylGroup .G2, ∀ α : Fin Tag.G2.rank → ℤ, w₁ • α = -α :=
  ⟨_, g2W0_smul⟩

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] def g2Datum
    :
    CurtisDatum (adjointGroup .G2 K) (coxeterSystem .G2) 2 :=
  chevDatum .G2 K 2 exists_weyl_neg_G2

variable {K}

theorem g2Datum_U
    : (g2Datum K).U = (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) :=
  rfl

theorem g2Datum_H
    : (g2Datum K).H = (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
  rfl

theorem g2Datum_n
    (i : Fin Tag.G2.rank) : (g2Datum K).n i = nC .G2 K i := rfl

theorem mem_g2Datum_X
    {i : Fin Tag.G2.rank} {x : adjointGroup .G2 K} :
    x ∈ (g2Datum K).X i ↔ ∃ c : K, xC .G2 K i c = x :=
  mem_X_chevDatum

theorem g2_heckeT_apply
    [Fintype K] {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (adjointGroup .G2 K) V) (i : Fin Tag.G2.rank) (v : V) :
    (g2Datum K).heckeT ρ i v = ∑ c : K, ρ (xC .G2 K i c * nC .G2 K i) v :=
  heckeT_chevDatum ρ i v

abbrev IsG2Type
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (adjointGroup .G2 K) V) (y : V) (χ : adjointGroup .G2 K → k)
    (J : Finset (Fin Tag.G2.rank)) : Prop :=
  IsChevType .G2 K 2 exists_weyl_neg_G2 ρ y χ J

theorem g2_exists_type
    {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] {ρ : Representation k (adjointGroup .G2 K) V} (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ χ : adjointGroup .G2 K → k, ∃ J : Finset (Fin Tag.G2.rank), IsG2Type ρ y χ J := by
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_isChevType hρ

theorem g2_type_unique
    {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] {ρ : Representation k (adjointGroup .G2 K) V} (hρ : IsSimpleRep ρ) {y y' : V}
    {χ χ' : adjointGroup .G2 K → k} {J J' : Finset (Fin Tag.G2.rank)} (ht : IsG2Type ρ y χ J)
    (ht' : IsG2Type ρ y' χ' J') : (∀ h ∈ (g2Datum K).H, χ h = χ' h) ∧ J = J' := by
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ht.unique hρ ht'

theorem g2_finrank_fixU
    {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] {ρ : Representation k (adjointGroup .G2 K) V} (hρ : IsSimpleRep ρ) :
    Module.finrank k ((g2Datum K).fixU ρ) = 1 := by
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (g2Datum K).finrank_fixU (splitOver_torus k) hρ

theorem g2_iso_of_type
    {k V V' : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] [AddCommGroup V'] [Module k V'] {ρ : Representation k (adjointGroup .G2 K) V}
    {ρ' : Representation k (adjointGroup .G2 K) V'} (hρ : IsSimpleRep ρ) (hρ' : IsSimpleRep ρ')
    {y : V} {y' : V'} {χ : adjointGroup .G2 K → k} {J : Finset (Fin Tag.G2.rank)}
    (ht : IsG2Type ρ y χ J) (ht' : IsG2Type ρ' y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : adjointGroup .G2 K) (v : V), β (ρ g v) = ρ' g (β v) := by
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact iso_of_isChevType hρ hρ' ht ht'

theorem g2_isSimpleRep_of_fixU
    {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] [Nontrivial V] {ρ : Representation k (adjointGroup .G2 K) V} {y : V}
    (hfix : ∀ x ∈ (g2Datum K).fixU ρ, ∃ c : k, x = c • y) (hgen : orbitSpan ρ y = ⊤) :
    IsSimpleRep ρ := by
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (g2Datum K).isSimpleRep_of_fixU ρ hfix hgen

theorem card_units_cast_eq_one {k : Type*} [Field k] [Algebra K k] [Fintype Kˣ] :
    ((Fintype.card Kˣ : ℕ) : k) = 1 := by
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rw [Fintype.card_eq_nat_card, Nat.card_units, hK]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hpos : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
  rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_ofNat, h2, zero_pow n.ne_zero, Nat.cast_one,
    zero_sub, CharTwo.neg_eq]

open Classical in
theorem g2_heckeT_eq
    {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] {ρ : Representation k (adjointGroup .G2 K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup .G2 K → k} {J : Finset (Fin Tag.G2.rank)} (ht : IsG2Type ρ y χ J)
    (i : Fin Tag.G2.rank) :
    (g2Datum K).heckeT ρ i y =
      (if (∀ t : Kˣ, χ (dC .G2 K i t) = 1) ∧ i ∉ J then (1 : k) else 0) • y := by
  classical
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype Kˣ := Fintype.ofFinite Kˣ
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  change (chevDatum .G2 K 2 exists_weyl_neg_G2).heckeT ρ i y = _
  rw [hμ.2.2.2 i, ht.mu_eq hμ i]
  split_ifs with h
  · rw [Finset.sum_congr rfl fun t _ => h.1 t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, card_units_cast_eq_one]
  · rfl

variable (K) in
@[expose] def dH
    (i : Fin Tag.G2.rank) : Kˣ →* (g2Datum K).H where
  toFun t := ⟨dC .G2 K i t, dC_mem_H i t⟩
  map_one' := Subtype.ext (dC_one i)
  map_mul' s t := Subtype.ext (dC_mul i s t)

variable (K) in
abbrev G2TypeSet
    (k : Type*) [Field k] : Type _ :=
  {p : ((g2Datum K).H →* kˣ) × Finset (Fin Tag.G2.rank) // ∀ i ∈ p.2, ∀ t : Kˣ, p.1 (dH K i t) = 1}

@[expose] def IsG2Type.toTypeSet
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (adjointGroup .G2 K) V} {y : V} {χ : adjointGroup .G2 K → k}
    {J : Finset (Fin Tag.G2.rank)} (ht : IsG2Type ρ y χ J) {μ : Fin Tag.G2.rank → k}
    (hμ : (g2Datum K).IsCurtisType ρ y χ μ) : G2TypeSet K k :=
  ⟨(hμ.chiHom.toHomUnits, J), fun i hi t => Units.ext (by
    rw [MonoidHom.coe_toHomUnits, hμ.chiHom_apply, Units.val_one]
    exact ht.subset hi t)⟩

theorem torus_coords
    : ∃ e : (Fin Tag.G2.rank → Kˣ) ≃* (g2Datum K).H,
    ∀ i t, e (Pi.mulSingle i t) = dH K i t := by
  obtain ⟨e, he⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hle : torusGroup .G2 K ≤ adjointGroup .G2 K := fun h hh =>
    (triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K |>.1
      (Subgroup.mem_sup_left hh)
  refine ⟨e.trans (Subgroup.subgroupOfEquivOfLe hle).symm, fun i t => ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  change (e (Pi.mulSingle i t) : ModGL .G2 K) = torusElt .G2 K i t
  rw [he, ← coe_torusCoordHom, coe_torusCoordHom_mulSingle]

abbrev i0 : Fin Tag.G2.rank := (0 : Fin 2)

abbrev i1 : Fin Tag.G2.rank := (1 : Fin 2)

theorem i0_ne_i1 : i0 ≠ i1 := by decide

theorem fin2_cases (j : Fin Tag.G2.rank) : j = i0 ∨ j = i1 := by
  rcases j with ⟨_ | _ | n, hn⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hn (by change ¬ (n + 2 < 2); omega)

theorem fin2_eq_mulSingle {M : Type*} [Monoid M] (t : Fin Tag.G2.rank → M) :
    t = Pi.mulSingle i0 (t i0) * Pi.mulSingle i1 (t i1) := by
  funext j
  rcases fin2_cases j with rfl | rfl
  · simp [i0_ne_i1]
  · simp [i0_ne_i1.symm]

theorem bijective_comp_dH
    (k : Type*) [Field k] :
    Function.Bijective fun χ : (g2Datum K).H →* kˣ =>
      fun i : Fin Tag.G2.rank => χ.comp (dH K i) := by
  obtain ⟨e, he⟩ := torus_coords (K := K)
  refine ⟨fun χ χ' h => ?_, fun a => ?_⟩
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨t, rfl⟩ := e.surjective x
    rw [fin2_eq_mulSingle t, map_mul, map_mul, map_mul, he, he]
    have h0 := DFunLike.congr_fun (congrFun h i0) (t i0)
    have h1 := DFunLike.congr_fun (congrFun h i1) (t i1)
    simp only [MonoidHom.comp_apply] at h0 h1
    rw [h0, h1]
  · refine ⟨((a i0).comp (Pi.evalMonoidHom (fun _ => Kˣ) i0) *
      (a i1).comp (Pi.evalMonoidHom (fun _ => Kˣ) i1)).comp e.symm.toMonoidHom,
      funext fun i => MonoidHom.ext fun t => ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← he, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.mul_apply,
      MonoidHom.comp_apply,
      MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply]
    rcases fin2_cases i with rfl | rfl
    · simp [i0_ne_i1.symm]
    · simp [i0_ne_i1]

omit [CharP K 2] in
theorem card_hom_units
    (k : Type*) [Field k] [Algebra K k] :
    Nat.card (Kˣ →* kˣ) = Nat.card K - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hprim : IsPrimitiveRoot (algebraMap K k (g : K)) (Nat.card Kˣ) := by
    have h1 : IsPrimitiveRoot (g : K) (Nat.card Kˣ) := by
      rw [← hg, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective (algebraMap K k).injective
  have : HasEnoughRootsOfUnity k (Nat.card Kˣ) :=
    ⟨⟨_, hprim⟩, rootsOfUnity.isCyclic k _⟩
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Kˣ k
  rw [Nat.card_congr e.toEquiv, Nat.card_units]

abbrev TypeLetter (A : Type*) [One A] : Type _ := {x : A × Bool // x.2 = true → x.1 = 1}

theorem card_typeLetter {A : Type*} [One A] [Finite A] :
    Nat.card (TypeLetter A) = Nat.card A + 1 := by
  classical
  have e : TypeLetter A ≃ A ⊕ Unit :=
    { toFun := fun x => if x.1.2 then Sum.inr () else Sum.inl x.1.1
      invFun := fun s => Sum.elim (fun a => ⟨(a, false), by simp⟩) (fun _ => ⟨(1, true),
        fun _ => rfl⟩) s
      left_inv := fun x => by
        obtain ⟨⟨a, ε⟩, h⟩ := x
        cases ε
        · rfl
        · simp only [↓reduceIte, Sum.elim_inr]
          exact Subtype.ext (Prod.ext (h rfl).symm rfl)
      right_inv := fun s => by
        rcases s with a | u
        · rfl
        · rfl }
  rw [Nat.card_congr e, Nat.card_sum, Nat.card_eq_fintype_card (α := Unit), Fintype.card_unit]

theorem card_g2TypeSet
    (k : Type*) [Field k] [Algebra K k] :
    Nat.card (G2TypeSet K k) = Nat.card K ^ 2 := by
  classical
  set Φ := fun χ : (g2Datum K).H →* kˣ => fun i : Fin Tag.G2.rank => χ.comp (dH K i)
  have hΦ := bijective_comp_dH (K := K) k
  let eΦ := Equiv.ofBijective Φ hΦ
  have e1 : G2TypeSet K k ≃
      {q : (Fin Tag.G2.rank → (Kˣ →* kˣ)) × Finset (Fin Tag.G2.rank) // ∀ i ∈ q.2, q.1 i = 1} :=
    { toFun := fun p => ⟨(Φ p.1.1, p.1.2), fun i hi => MonoidHom.ext fun t => by
        simp only [Φ, MonoidHom.comp_apply, MonoidHom.one_apply]
        exact p.2 i hi t⟩
      invFun := fun q => ⟨(eΦ.symm q.1.1, q.1.2), fun i hi t => by
        have h := DFunLike.congr_fun (congrFun (eΦ.apply_symm_apply q.1.1) i) t
        simp only [eΦ, Equiv.ofBijective_apply, Φ, MonoidHom.comp_apply] at h
        rw [h, q.2 i hi, MonoidHom.one_apply]⟩
      left_inv := fun p => by
        refine Subtype.ext (Prod.ext ?_ rfl)
        exact eΦ.symm_apply_apply p.1.1
      right_inv := fun q => by
        refine Subtype.ext (Prod.ext ?_ rfl)
        exact eΦ.apply_symm_apply q.1.1 }
  have e2 : {q : (Fin Tag.G2.rank → (Kˣ →* kˣ)) × Finset (Fin Tag.G2.rank) //
      ∀ i ∈ q.2, q.1 i = 1} ≃ (Fin Tag.G2.rank → TypeLetter (Kˣ →* kˣ)) :=
    { toFun := fun q i => ⟨(q.1.1 i, decide (i ∈ q.1.2)), fun h => q.2 i (by simpa using h)⟩
      invFun := fun f => ⟨(fun i => (f i).1.1, Finset.univ.filter fun i => (f i).1.2 = true),
        fun i hi => (f i).2 (Finset.mem_filter.mp hi).2⟩
      left_inv := fun q => by
        refine Subtype.ext (Prod.ext rfl ?_)
        ext i
        simp
      right_inv := fun f => by
        funext i
        refine Subtype.ext (Prod.ext rfl ?_)
        simp }
  have : Finite (Kˣ →* kˣ) := by
    have h := card_hom_units (K := K) k
    have hq : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
      omega
    exact Nat.finite_of_card_ne_zero (by omega)
  rw [Nat.card_congr (e1.trans e2), Nat.card_fun, card_typeLetter, card_hom_units,
    Nat.sub_add_cancel Nat.card_pos, Nat.card_fin]
  rfl

end CFSG.Quasithin.B42G2Cur
