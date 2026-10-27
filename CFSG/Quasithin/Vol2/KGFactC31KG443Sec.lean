module

public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.RankThree.PartOne.Q1327F.SL2Inv
public import CFSG.Quasithin.Vol2.KGFactC31M22RefBase

public section

namespace CFSG.Quasithin.KGC31.KG443

open Function CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped MatrixGroups

@[expose] def SecOnto (S T : Type) [Group S] [Group T] : Prop :=
  ∃ (Y : Subgroup S) (φ : ↥Y →* T), Surjective φ

theorem exists_range_surj {A S T : Type} [Group A] [Group S] [Group T] (f : A →* S)
    (ψ : A →* T) (hψ : Surjective ψ) (h : f.ker ≤ ψ.ker) :
    ∃ φ : ↥f.range →* T, Surjective φ := by
  refine ⟨(QuotientGroup.lift f.ker ψ h).comp
    (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom, fun t => ?_⟩
  obtain ⟨a, rfl⟩ := hψ t
  refine ⟨f.rangeRestrict a, ?_⟩
  have e : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict a) =
      (a : A ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, comp_apply, e,
    QuotientGroup.lift_mk]

theorem secOnto_of_ker_le {A S T : Type} [Group A] [Group S] [Group T] (f : A →* S)
    (ψ : A →* T) (hψ : Surjective ψ) (h : f.ker ≤ ψ.ker) : SecOnto S T :=
  ⟨f.range, exists_range_surj f ψ hψ h⟩

theorem SecOnto.of_injective {S S' T : Type} [Group S] [Group S'] [Group T] (h : SecOnto S T)
    (ι : S →* S') (hι : Injective ι) : SecOnto S' T := by
  obtain ⟨Y, φ, hφ⟩ := h
  exact ⟨Y.map ι, φ.comp (Y.equivMapOfInjective ι hι).symm.toMonoidHom,
    hφ.comp (Y.equivMapOfInjective ι hι).symm.surjective⟩

theorem SecOnto.of_equiv {S S' T : Type} [Group S] [Group S'] [Group T] (h : SecOnto S T)
    (e : S ≃* S') : SecOnto S' T :=
  h.of_injective e.toMonoidHom e.injective

theorem SecOnto.card_dvd {S T : Type} [Group S] [Group T] [Finite S] (h : SecOnto S T) :
    Nat.card T ∣ Nat.card S := by
  obtain ⟨Y, φ, hφ⟩ := h
  calc Nat.card T = Nat.card (↥Y ⧸ φ.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
    _ ∣ Nat.card Y := Subgroup.card_quotient_dvd_card _
    _ ∣ Nat.card S := Subgroup.card_subgroup_dvd_card Y

theorem card_dvd_of_surjective {A T : Type} [Group A] [Group T] [Finite A] {φ : A →* T}
    (hφ : Surjective φ) : Nat.card T ∣ Nat.card A := by
  calc Nat.card T = Nat.card (A ⧸ φ.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
    _ ∣ Nat.card A := Subgroup.card_quotient_dvd_card _

theorem SecOnto.quot {S Q T : Type} [Group S] [Group Q] [Group T] [IsSimpleGroup T]
    (h : SecOnto S T) (hT : ∃ a b : T, a * b ≠ b * a) (ψ : S →* Q)
    (hsol : Group.IsSolvable ↥ψ.ker) : SecOnto Q T := by
  obtain ⟨Y, φ, hφ⟩ := h
  let f : ↥Y →* Q := ψ.comp Y.subtype
  have hsolf : Group.IsSolvable ↥f.ker := by
    let ι : ↥f.ker →* ↥ψ.ker :=
      { toFun := fun y => ⟨(y : ↥Y), y.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := ι) fun y z hyz => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥ψ.ker => ((x : S))) hyz))
  have hn : (f.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ _ hn with hb | ht
  · refine secOnto_of_ker_le f φ hφ fun y hy => ?_
    have : φ y ∈ f.ker.map φ := Subgroup.mem_map_of_mem φ hy
    rw [hb, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hs : Surjective (φ.comp f.ker.subtype) := fun t => by
      have ht' : t ∈ f.ker.map φ := by rw [ht]; exact Subgroup.mem_top t
      obtain ⟨y, hy, rfl⟩ := ht'
      exact ⟨⟨y, hy⟩, rfl⟩
    have : Group.IsSolvable T := Group.isSolvable_of_surjective hs
    obtain ⟨a, b, hab⟩ := hT
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 this a b)

theorem isSimpleGroup_m22 :
    IsSimpleGroup (NativeSporadic.Carrier .M22) :=
  (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2

@[expose] def e3W : List ℤ := [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1]

@[expose] def e3W' : List ℤ := [1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2,
  1, 2, 1, 2, 2]

theorem perm_eq_of_rep {T T' : Table} {g h : Equiv.Perm (Fin 22)} (hg : Rep 22 T g)
    (hh : Rep 22 T' h) (hT : T = T') : g = h := by
  subst hT
  ext i
  rw [← rep_apply hg i, ← rep_apply hh i]

theorem perm_ne_of_rep {T T' : Table} {g h : Equiv.Perm (Fin 22)} (hg : Rep 22 T g)
    (hh : Rep 22 T' h) (i : Fin 22) (hT : ap T i.val ≠ ap T' i.val) : g ≠ h := by
  rintro rfl
  exact hT (by rw [rep_apply hg i, rep_apply hh i])

theorem not_comm_m22 : ∃ a b : NativeSporadic.Carrier .M22, a * b ≠ b * a := by
  refine ⟨M22.elt [1], M22.elt [2], fun h => ?_⟩
  have h1 : ((M22.elt [1] * M22.elt [2] : M22.G₀) : Equiv.Perm (Fin 22)) =
      ((M22.elt [2] * M22.elt [1] : M22.G₀) : Equiv.Perm (Fin 22)) := congrArg Subtype.val h
  refine perm_ne_of_rep ((M22.rep_elt [1]).compT (M22.rep_elt [2]))
    ((M22.rep_elt [2]).compT (M22.rep_elt [1])) ⟨0, by norm_num⟩ ?_ h1
  decide +kernel

theorem center_m22 :
    Subgroup.center (NativeSporadic.Carrier .M22) = ⊥ := by
  have := isSimpleGroup_m22
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (NativeSporadic.Carrier .M22) _ _
    (Subgroup.center _) inferInstance with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := not_comm_m22
    have hb : b ∈ Subgroup.center (NativeSporadic.Carrier .M22) := by rw [h]; exact trivial
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem e3_cube : (M22.elt e3W) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine perm_eq_of_rep ((M22.rep_elt e3W).powT M22.hn22 3) (Rep.idT M22.hn22) ?_
  decide +kernel

theorem e3'_cube : (M22.elt e3W') ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine perm_eq_of_rep ((M22.rep_elt e3W').powT M22.hn22 3) (Rep.idT M22.hn22) ?_
  decide +kernel

theorem e3_comm : M22.elt e3W * M22.elt e3W' = M22.elt e3W' * M22.elt e3W := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  refine perm_eq_of_rep ((M22.rep_elt e3W).compT (M22.rep_elt e3W'))
    ((M22.rep_elt e3W').compT (M22.rep_elt e3W)) ?_
  decide +kernel

theorem e3'_ne_one : M22.elt e3W' ≠ 1 := fun h => by
  have h1 : ((M22.elt e3W' : M22.G₀) : Equiv.Perm (Fin 22)) =
      ((1 : M22.G₀) : Equiv.Perm (Fin 22)) := congrArg Subtype.val h
  refine perm_ne_of_rep (M22.rep_elt e3W') (Rep.idT M22.hn22) ⟨0, by norm_num⟩ ?_ h1
  decide +kernel

theorem e3'_ne : M22.elt e3W' ≠ M22.elt e3W := fun h => by
  have h1 : ((M22.elt e3W' : M22.G₀) : Equiv.Perm (Fin 22)) = ((M22.elt e3W : M22.G₀) :
      Equiv.Perm (Fin 22)) := congrArg Subtype.val h
  refine perm_ne_of_rep (M22.rep_elt e3W') (M22.rep_elt e3W) ⟨0, by norm_num⟩ ?_ h1
  decide +kernel

theorem e3'_ne_sq : M22.elt e3W' ≠ (M22.elt e3W) ^ 2 := fun h => by
  have h1 : ((M22.elt e3W' : M22.G₀) : Equiv.Perm (Fin 22)) = (((M22.elt e3W) ^ 2 : M22.G₀) :
      Equiv.Perm (Fin 22)) := congrArg Subtype.val h
  rw [Subgroup.coe_pow] at h1
  refine perm_ne_of_rep (M22.rep_elt e3W') ((M22.rep_elt e3W).powT M22.hn22 2) ⟨0, by norm_num⟩
    ?_ h1
  decide +kernel

theorem e3_ne_one : M22.elt e3W ≠ 1 := fun h => by
  have h1 : ((M22.elt e3W : M22.G₀) : Equiv.Perm (Fin 22)) =
      ((1 : M22.G₀) : Equiv.Perm (Fin 22)) := congrArg Subtype.val h
  refine perm_ne_of_rep (M22.rep_elt e3W) (Rep.idT M22.hn22) ⟨1, by norm_num⟩ ?_ h1
  decide +kernel

theorem not_secOnto_sl2_of {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {T : Type} [Group T] [Finite T]
    {a b : T} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) : ¬ SecOnto (SL(2, ZMod p)) T := by
  classical
  rintro ⟨Y, φ, hφ⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup T := Subgroup.closure {a, b}
  have hcomm : ({a, b} : Set T).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    have : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure hcomm
    let c : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := this.is_comm.comm }
    let π : ↥E →* ↥E := @powMonoidHom ↥E c.toCommMonoid 3
    have hle : E ≤ (π.ker).map E.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | rfl)
      · refine ⟨⟨x, Subgroup.subset_closure (Set.mem_insert _ _)⟩, ?_, rfl⟩
        exact Subtype.ext (by simpa [π] using ha3)
      · refine ⟨⟨x, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩, ?_, rfl⟩
        exact Subtype.ext (by simpa [π] using hb3)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    have : π y = 1 := hy
    exact congrArg Subtype.val this
  let Q : Subgroup ↥Y := E.comap φ
  let φQ : ↥Q →* ↥E := (φ.comp Q.subtype).codRestrict E fun q => q.2
  have hφQ : Surjective φQ := fun e => by
    obtain ⟨y, hy⟩ := hφ (e : T)
    refine ⟨⟨y, show φ y ∈ E from hy ▸ e.2⟩, Subtype.ext hy⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 ↥Q))
  have hEp : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  have hPE : (P : Subgroup ↥Q).map φQ = ⊤ := by
    rw [← Sylow.coe_mapSurjective hφQ P]
    exact ((Sylow.mapSurjective hφQ P).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  have hne : NeZero ((3 : ℕ) : ZMod p) := ⟨fun h => hp3
    ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 ((ZMod.natCast_eq_zero_iff 3 p).1 h))⟩
  have hr : CFSG.pRank 3 ↥(⊤ : Subgroup (SL(2, ZMod p))) ≤ 1 :=
    CFSG.RankThree.PartOne.Q1327F.pRank_le_one_of_equiv_sl2_ne Nat.prime_three Subgroup.topEquiv
  let ι : ↥Q →* SL(2, ZMod p) := Y.subtype.comp Q.subtype
  have hι : Injective ι := Y.subtype_injective.comp Q.subtype_injective
  have hcyc : IsCyclic ↥((P : Subgroup ↥Q).map ι) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) le_top
      (P.isPGroup'.map ι) hr
  have hcycP : IsCyclic ↥(P : Subgroup ↥Q) :=
    (MulEquiv.isCyclic ((P : Subgroup ↥Q).equivMapOfInjective ι hι)).2 hcyc
  have hcycI : IsCyclic ↥((P : Subgroup ↥Q).map φQ) :=
    isCyclic_of_surjective _ (φQ.subgroupMap_surjective (P : Subgroup ↥Q))
  have hcycE : IsCyclic ↥E := by
    rw [hPE] at hcycI
    exact (MulEquiv.isCyclic Subgroup.topEquiv).1 hcycI
  have : Fintype ↥E := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥E) (n := 3) (by norm_num)
  have hall : (Finset.univ.filter fun x : ↥E => x ^ 3 = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun x _ => Subtype.ext (by simpa using hE3 x x.2)
  rw [hall, Finset.card_univ] at hle
  have haE : a ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbE : b ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have ha2 : a ^ 2 ≠ 1 := fun h => ha1 (by
    have : a ^ 3 = a ^ 2 * a := pow_succ a 2
    rw [ha3, h, one_mul] at this
    exact this.symm)
  have haa : a ≠ a ^ 2 := fun h => ha1 (by
    have : a ^ 2 = a * a := pow_two a
    rw [← h] at this
    exact mul_eq_left.mp this.symm)
  let f4 : Fin 4 → ↥E := ![1, ⟨a, haE⟩, ⟨a ^ 2, E.pow_mem haE 2⟩, ⟨b, hbE⟩]
  have hf4 : Injective f4 := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f4] at hv ⊢
    all_goals first
      | exact absurd hv.symm ha1 | exact absurd hv ha1 | exact absurd hv.symm ha2
      | exact absurd hv ha2 | exact absurd hv haa | exact absurd hv.symm haa
      | exact absurd hv.symm hb1 | exact absurd hv hb1
      | exact absurd hv.symm hba | exact absurd hv hba
      | exact absurd hv.symm hba2 | exact absurd hv hba2
  have := Fintype.card_le_of_injective f4 hf4
  rw [Fintype.card_fin] at this
  omega

theorem not_secOnto_sl2 {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    ¬ SecOnto (SL(2, ZMod p)) (NativeSporadic.Carrier .M22) :=
  have : Finite (NativeSporadic.Carrier .M22) := (inferInstance : Finite M22.G₀)
  not_secOnto_sl2_of hp3 e3_cube e3'_cube e3_comm e3_ne_one e3'_ne_one e3'_ne e3'_ne_sq

end CFSG.Quasithin.KGC31.KG443

end
