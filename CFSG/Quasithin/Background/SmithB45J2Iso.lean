module

public import CFSG.Quasithin.Background.SmithB45J2Q
public import CFSG.Quasithin.Background.SmithB45J2Cls
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.PairJ2Faithful

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Model CFSG.Quasithin.J2Bits CFSG.Blueprint CFSG.CharacterTheory.SteinbergBY

theorem bijective_of_surjective {G H : Type*} [Group G] [Group H] [IsSimpleGroup G]
    [Nontrivial H] {f : G →* H} (hf : Function.Surjective f) : Function.Bijective f := by
  refine ⟨?_, hf⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff f).1 h
  · exfalso
    obtain ⟨x, y, hxy⟩ := exists_pair_ne H
    obtain ⟨x', rfl⟩ := hf x
    obtain ⟨y', rfl⟩ := hf y
    have hx : x' ∈ f.ker := h ▸ Subgroup.mem_top x'
    have hy : y' ∈ f.ker := h ▸ Subgroup.mem_top y'
    rw [MonoidHom.mem_ker] at hx hy
    exact hxy (hx.trans hy.symm)

theorem gA_mem : gA ∈ Γ₆ :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem gB_mem : gB ∈ Γ₆ :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem a6_ne_one : a6.eqv BM.one = false := by
  decide +kernel

theorem gA_ne_one : gA ≠ 1 := by
  intro h
  have h1 : a6.toMat = BM.one.toMat := by
    rw [BM.toMat_one]
    exact congrArg (fun g : GL6 => (g : M6)) h
  have h2 := (BM.eqv_iff a6 BM.one).mpr h1
  rw [a6_ne_one] at h2
  exact Bool.false_ne_true h2

instance : Nontrivial ↥Γ₆ :=
  ⟨⟨⟨gA, gA_mem⟩, 1, fun h => gA_ne_one (congrArg Subtype.val h)⟩⟩

@[expose] noncomputable def qHomΓ : ↥j2Γ₀ →* ↥Γ₆ :=
  qHomJ.codRestrict Γ₆ qHomJ_mem

theorem qHomΓ_surjective : Function.Surjective qHomΓ := by
  rintro ⟨y, hy⟩
  rw [← range_qHomJ] at hy
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨γ, rfl⟩

theorem nonempty_presEquiv :
    Nonempty (NativeSporadic.J2 ≃* TauCeti.Sporadic.j2Presentation.Group) := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Bridge.J2.finite_card_le
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_mulEquiv_of_surjective
    CFSG.Sporadic.Bridge.J2.toNative CFSG.Sporadic.Bridge.J2.toNative_surjective hcard
    CFSG.Sporadic.Bridge.J2.le_card_seedGroup
  exact ⟨CFSG.Sporadic.Bridge.J2.nativeEquiv.trans e⟩

@[expose] noncomputable def presEquiv :
    NativeSporadic.J2 ≃* TauCeti.Sporadic.j2Presentation.Group :=
  Classical.choice nonempty_presEquiv

@[expose] noncomputable def toGamma : NativeSporadic.J2 →* ↥Γ₆ :=
  qHomΓ.comp (j2PresOnto.comp presEquiv.toMonoidHom)

theorem toGamma_surjective : Function.Surjective toGamma :=
  qHomΓ_surjective.comp (j2PresOnto_surjective.comp presEquiv.surjective)

@[expose] noncomputable def gammaEquiv :
    NativeSporadic.J2 ≃* ↥Γ₆ :=
  have := CFSG.Sporadic.J2.isSimpleGroup_J2
  MulEquiv.ofBijective toGamma (bijective_of_surjective toGamma_surjective)

theorem card_Γ₆ : Nat.card ↥Γ₆ = 604800 := by
  rw [← Nat.card_congr gammaEquiv.toEquiv, CFSG.Sporadic.J2.card_J2]

instance : Finite ↥Γ₆ :=
  Nat.finite_of_card_ne_zero (by rw [card_Γ₆]; norm_num)

theorem card_pRegularClass_le_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] (p : ℕ) (e : G ≃* H) :
    Fintype.card (PRegularClass p G) ≤ Fintype.card (PRegularClass p H) := by
  classical
  let f : PRegularClass p G → PRegularClass p H := fun C =>
    ⟨ConjClasses.mk (e (PRegularClass.repr C)), by
      rw [← ConjClasses.quotient_mk_eq_mk, ConjClass.mk_isPRegular]
      exact IsPRegular.map p e.toMonoidHom (PRegularClass.repr_isPRegular C)⟩
  refine Fintype.card_le_of_injective f fun C C' hCC' => ?_
  have h1 : IsConj (e (PRegularClass.repr C)) (e (PRegularClass.repr C')) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val hCC')
  have h2 : IsConj (PRegularClass.repr C) (PRegularClass.repr C') := by
    obtain ⟨c, hc⟩ := isConj_iff.1 h1
    refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
  apply PRegularClass.ext
  have hC : ConjClasses.mk (PRegularClass.repr C) = C.1 := Quotient.out_eq C.1
  have hC' : ConjClasses.mk (PRegularClass.repr C') = C'.1 := Quotient.out_eq C'.1
  rw [← hC, ← hC']
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr h2

theorem card_pRegularClass_Γ₆ :
    Fintype.card (PRegularClass 2 ↥Γ₆) ≤ 10 := by
  exact (card_pRegularClass_le_of_mulEquiv 2
    (gammaEquiv.symm.trans CFSG.Sporadic.Schreier.j2PermEquiv)).trans
    J2Cls.card_pRegularClass_j2P

end CFSG.Quasithin.J2Row
