module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.LocalCores

variable {G : Type} [Group G] [Finite G]

private theorem isSubnormal_map_iff {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (S : Subgroup A) : (S.map f.toMonoidHom).IsSubnormal ↔ S.IsSubnormal :=
  ⟨fun h => by
    simpa only [CFSG.LocalCores.map_map_symm] using
      Subgroup.IsSubnormal.map (f := f.symm.toMonoidHom) f.symm.surjective h,
   fun h => Subgroup.IsSubnormal.map (f := f.toMonoidHom) f.surjective h⟩

private theorem subnormal_subgroupOf_iff {K C Y : Subgroup G} (hCY : C ≤ Y) :
    ((K.subgroupOf Y).subgroupOf (C.subgroupOf Y)).IsSubnormal ↔
      (K.subgroupOf C).IsSubnormal := by
  let φ : ↥(C.subgroupOf Y) ≃* ↥C := Subgroup.subgroupOfEquivOfLe hCY
  have h : ((K.subgroupOf Y).subgroupOf (C.subgroupOf Y)).map φ.toMonoidHom =
      K.subgroupOf C := by
    ext c
    rw [Subgroup.mem_map_equiv]
    exact Iff.rfl
  rw [← h, isSubnormal_map_iff]

private theorem isComponent_subgroupOf_iff {K C Y : Subgroup G} (hKC : K ≤ C) (hCY : C ≤ Y)
    (hn : ∀ y ∈ Y, ∀ c ∈ C, y * c * y⁻¹ ∈ C) :
    IsComponent (K.subgroupOf Y) ↔ IsComponent (K.subgroupOf C) := by
  haveI : (C.subgroupOf Y).Normal := ⟨fun c hc y => by
    simpa [Subgroup.mem_subgroupOf] using hn y y.2 c hc⟩
  let e1 : ↥(K.subgroupOf Y) ≃* ↥K := Subgroup.subgroupOfEquivOfLe (hKC.trans hCY)
  let e2 : ↥(K.subgroupOf C) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hq : IsQuasisimple (K.subgroupOf Y) ↔ IsQuasisimple (K.subgroupOf C) :=
    ⟨fun h => isQuasisimple_of_mulEquiv (e1.trans e2.symm) h,
     fun h => isQuasisimple_of_mulEquiv (e2.trans e1.symm) h⟩
  refine ⟨fun ⟨h1, h2⟩ => ⟨hq.mp h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨hq.mpr h1, ?_⟩⟩
  · exact (subnormal_subgroupOf_iff hCY).mp h2.subgroupOf
  · refine Subgroup.IsSubnormal.trans (K := C.subgroupOf Y)
      (fun x hx => ?_) ((subnormal_subgroupOf_iff hCY).mpr h2)
      (Subgroup.Normal.isSubnormal inferInstance)
    exact hKC hx

private theorem le_lay_of_isComponent {K Y : Subgroup G} (hKY : K ≤ Y)
    (hK : IsComponent (K.subgroupOf Y)) : K ≤ Lay Y := by
  have h : K = (K.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hKY).symm
  rw [h]
  exact Subgroup.map_mono (le_sSup hK)

theorem lay_eq_of_perfect {C Y : Subgroup G} (hCY : C ≤ Y)
    (hn : ∀ y ∈ Y, ∀ c ∈ C, y * c * y⁻¹ ∈ C)
    (hP : ∀ S : Subgroup G, S ≤ Y → Group.IsPerfect ↥S → S ≤ C) : Lay Y = Lay C := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.map_le_iff_le_comap.mpr (sSup_le fun Q hQ => ?_)
    refine Subgroup.map_le_iff_le_comap.mp ?_
    have hperf : Group.IsPerfect ↥Q := hQ.1.1
    have hKY : Q.map Y.subtype ≤ Y := Subgroup.map_subtype_le Q
    haveI : Group.IsPerfect ↥(Q.map Y.subtype) := Group.IsPerfect.map Y.subtype
    have hKC : Q.map Y.subtype ≤ C := hP _ hKY inferInstance
    have hsub : (Q.map Y.subtype).subgroupOf Y = Q :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective Q
    refine le_lay_of_isComponent hKC ?_
    rw [← isComponent_subgroupOf_iff hKC hCY hn, hsub]
    exact hQ
  · refine Subgroup.map_le_iff_le_comap.mpr (sSup_le fun Q hQ => ?_)
    refine Subgroup.map_le_iff_le_comap.mp ?_
    have hKC : Q.map C.subtype ≤ C := Subgroup.map_subtype_le Q
    have hsub : (Q.map C.subtype).subgroupOf C = Q :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective Q
    refine le_lay_of_isComponent (hKC.trans hCY) ?_
    rw [isComponent_subgroupOf_iff hKC hCY hn, hsub]
    exact hQ

theorem perfect_le_of_comm_mem {C Y : Subgroup G}
    (hab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' * y⁻¹ * y'⁻¹ ∈ C) :
    ∀ S : Subgroup G, S ≤ Y → Group.IsPerfect ↥S → S ≤ C := by
  intro S hS hperf
  have h1 : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hperf
  rw [← h1]
  exact Subgroup.commutator_le.mpr fun s hs t ht => hab s (hS hs) t (hS ht)

theorem lay_eq_lay_inf_of_normal {D J Y : Subgroup G} (hJD : J ≤ D)
    (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J) (hYD : Y ≤ D)
    (hP : ∀ S : Subgroup G, S ≤ D → Group.IsPerfect ↥S → S ≤ J) : Lay Y = Lay (J ⊓ Y) :=
  lay_eq_of_perfect inf_le_right
    (fun y hy c hc => ⟨hJn y (hYD hy) c hc.1, Y.mul_mem (Y.mul_mem hy hc.2) (Y.inv_mem hy)⟩)
    fun S hSY hS => le_inf (hP S (hSY.trans hYD) hS) hSY

private theorem comm_aut_inner {X : Type} [Group X] (δ : MulAut X)
    (hform : ∀ α : MulAut X, ∃ s : X, ∃ ε : ℕ, ε ≤ 1 ∧ α = MulAut.conj s * δ ^ ε)
    (α β : MulAut X) : ∃ s : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj s := by
  let N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  haveI : N.Normal := ⟨fun a ⟨s, hs⟩ g => ⟨g s, by
    rw [← hs]
    ext x
    simp [MulAut.conj_apply]⟩⟩
  have key : ∀ a : MulAut X, ∃ k : ℤ, (QuotientGroup.mk δ : MulAut X ⧸ N) ^ k =
      QuotientGroup.mk a := by
    intro a
    obtain ⟨s, ε, -, rfl⟩ := hform a
    refine ⟨ε, ?_⟩
    have h1 : (QuotientGroup.mk (MulAut.conj s) : MulAut X ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨s, rfl⟩
    rw [QuotientGroup.mk_mul, h1, one_mul, zpow_natCast, QuotientGroup.mk_pow]
  obtain ⟨i, hi⟩ := key α
  obtain ⟨j, hj⟩ := key β
  have h1 : (QuotientGroup.mk (α * β * α⁻¹ * β⁻¹) : MulAut X ⧸ N) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← hi, ← hj]
    group
  obtain ⟨s, hs⟩ := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨s, hs.symm⟩

private def conjHom {D J : Subgroup G} (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J) :
    ↥D →* MulAut ↥J where
  toFun d :=
    { toFun := fun x => ⟨d * x * d⁻¹, hJn d d.2 x x.2⟩
      invFun := fun x => ⟨d⁻¹ * x * d, by simpa using hJn d⁻¹ (D.inv_mem d.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext x
    simp
  map_mul' d d' := by
    ext x
    simp [mul_assoc]

private theorem conjHom_apply {D J : Subgroup G} (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J)
    (d : ↥D) (x : ↥J) : ((conjHom hJn d x : ↥J) : G) = d * x * d⁻¹ := rfl

private theorem comm_acts_inner {D J : Subgroup G} (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J)
    {X : Type} [Group X] (f : ↥J ≃* X) (δ : MulAut X)
    (hform : ∀ α : MulAut X, ∃ s : X, ∃ ε : ℕ, ε ≤ 1 ∧ α = MulAut.conj s * δ ^ ε)
    (d d' : ↥D) : ∃ j : ↥J, ∀ x : ↥J,
      ((d * d' * d⁻¹ * d'⁻¹ : ↥D) : G) * x * ((d * d' * d⁻¹ * d'⁻¹ : ↥D) : G)⁻¹ =
        j * x * (j : G)⁻¹ := by
  let ψ : ↥D →* MulAut X := (MulAut.congr f).toMonoidHom.comp (conjHom hJn)
  obtain ⟨s, hs⟩ := comm_aut_inner δ hform (ψ d) (ψ d')
  refine ⟨f.symm s, fun x => ?_⟩
  have h1 : ψ (d * d' * d⁻¹ * d'⁻¹) = MulAut.conj s := by
    rw [← hs]
    simp
  have h2 : ψ (d * d' * d⁻¹ * d'⁻¹) (f x) = f (conjHom hJn (d * d' * d⁻¹ * d'⁻¹) x) := by
    simp [ψ, MulAut.congr_apply]
  rw [h1] at h2
  have h3 : conjHom hJn (d * d' * d⁻¹ * d'⁻¹) x = f.symm s * x * (f.symm s)⁻¹ := by
    apply f.injective
    rw [← h2]
    simp [MulAut.conj_apply]
  exact (conjHom_apply hJn _ x).symm.trans (congrArg Subtype.val h3)

private theorem perfect_le_of_aut_form {D J : Subgroup G} (hJD : J ≤ D)
    (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J) {X : Type} [Group X] (f : ↥J ≃* X)
    (δ : MulAut X)
    (hform : ∀ α : MulAut X, ∃ s : X, ∃ ε : ℕ, ε ≤ 1 ∧ α = MulAut.conj s * δ ^ ε)
    (hZ : Group.IsSolvable ↥(D ⊓ CenS J)) :
    ∀ S : Subgroup G, S ≤ D → Group.IsPerfect ↥S → S ≤ J := by
  intro S hSD hS
  haveI hJnorm : (J.subgroupOf D).Normal := ⟨fun c hc y => by
    simpa [Subgroup.mem_subgroupOf] using hJn y y.2 c hc⟩
  let π : ↥D →* ↥D ⧸ J.subgroupOf D := QuotientGroup.mk' (J.subgroupOf D)
  let Z : Subgroup G := D ⊓ CenS J
  have hZD : Z ≤ D := inf_le_left
  haveI : Group.IsSolvable ↥(Z.subgroupOf D) :=
    solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hZD).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hZD).injective
  let ζ : ↥(Z.subgroupOf D) →* ↥D ⧸ J.subgroupOf D := π.comp (Z.subgroupOf D).subtype
  haveI : Group.IsSolvable ↥ζ.range := solvable_of_surjective ζ.rangeRestrict_surjective
  have hcomm : ∀ a b : ↥D ⧸ J.subgroupOf D, a * b * a⁻¹ * b⁻¹ ∈ ζ.range := by
    intro a b
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨d', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨j, hj⟩ := comm_acts_inner hJn f δ hform d d'
    obtain ⟨c, hc⟩ : ∃ c : ↥D, c = d * d' * d⁻¹ * d'⁻¹ := ⟨_, rfl⟩
    rw [← hc] at hj
    have hjD : (j : G) ∈ D := hJD j.2
    let z : ↥D := ⟨(j : G)⁻¹ * c, D.mul_mem (D.inv_mem hjD) c.2⟩
    have hzZ : (z : G) ∈ Z := ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have h := hj ⟨x, hx⟩
      calc x * ((j : G)⁻¹ * c) = (j : G)⁻¹ * ((j : G) * x * (j : G)⁻¹) * c := by group
        _ = (j : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * c := by rw [← h]
        _ = (j : G)⁻¹ * c * x := by group⟩
    refine ⟨⟨z, hzZ⟩, ?_⟩
    have hcz : c = ⟨j, hjD⟩ * z := Subtype.ext (by simp [z])
    have hj1 : (QuotientGroup.mk (⟨j, hjD⟩ : ↥D) : ↥D ⧸ J.subgroupOf D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr j.2)
    have : (QuotientGroup.mk c : ↥D ⧸ J.subgroupOf D) = QuotientGroup.mk z := by
      rw [hcz, QuotientGroup.mk_mul, hj1, one_mul]
    show QuotientGroup.mk z = _
    rw [← this, hc]
    simp [QuotientGroup.mk_mul]
  have hP := perfect_le_of_comm_mem (C := ζ.range) (Y := ⊤) (fun y _ y' _ => hcomm y y')
  let g : ↥S →* ↥D ⧸ J.subgroupOf D := π.comp (Subgroup.inclusion hSD)
  haveI := hS
  haveI : Group.IsPerfect ↥g.range := Group.IsPerfect.range g
  have hle : g.range ≤ ζ.range := hP g.range le_top inferInstance
  haveI : Group.IsSolvable ↥g.range :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  intro x hx
  by_contra hxJ
  have hnt : Nontrivial ↥g.range := by
    refine ⟨⟨⟨g ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hxJ ?_⟩⟩
    have h1 : g ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    have h2 := (QuotientGroup.eq_one_iff (⟨x, hSD hx⟩ : ↥D)).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  exact Group.IsPerfect.not_isSolvable ↥g.range inferInstance

private noncomputable def slGL5 :
    Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) ≃* GL (Fin 5) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      haveI : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
      have hker : g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 5) (ZMod 2) →* (ZMod 2)ˣ).ker :=
        MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
      rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hker
      exact hker⟩

theorem perfect_le_of_cen_solvable {D J : Subgroup G} (hJD : J ≤ D)
    (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J) (e : J ≃* GL (Fin 5) (ZMod 2))
    (hZ : Group.IsSolvable ↥(D ⊓ CenS J)) :
    ∀ S : Subgroup G, S ≤ D → Group.IsPerfect ↥S → S ≤ J :=
  perfect_le_of_aut_form hJD hJn (e.trans slGL5.symm) (TLn.deltaS (Or.inr rfl))
    (fun α => by
      obtain ⟨s, ε, hε, h⟩ := TLn.autForm (Or.inr rfl) α
      exact ⟨s, ε, hε, h⟩) hZ

theorem lay_conjBy (n : G) (Y : Subgroup G) : Lay (conjBy n Y) = conjBy n (Lay Y) := by
  let f : G ≃* G := MulAut.conj n
  let g : ↥Y ≃* ↥(conjBy n Y) := Subgroup.equivMapOfInjective Y f.toMonoidHom f.injective
  have hlay : (layer ↥Y).map g.toMonoidHom = layer ↥(conjBy n Y) := by
    have hbij := (component_isomorphism g).2
    change MulEquiv.mapSubgroup g (sSup {K : Subgroup ↥Y | IsComponent K}) = _
    rw [OrderIso.map_sSup, ← sSup_image]
    exact congrArg sSup hbij.image_eq
  change (layer ↥(conjBy n Y)).map (conjBy n Y).subtype =
    ((layer ↥Y).map Y.subtype).map f.toMonoidHom
  rw [← hlay, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isLnq_conjBy_iff (n : G) (Y : Subgroup G) (a p f : ℕ) :
    IsLnq a p f (conjBy n Y) ↔ IsLnq a p f Y := by
  let g : ↥Y ≃* ↥(conjBy n Y) :=
    Subgroup.equivMapOfInjective Y (MulAut.conj n : G ≃* G).toMonoidHom
      (MulAut.conj n : G ≃* G).injective
  exact ⟨fun h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv g.symm h,
    fun h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv g h⟩

theorem conjBy_inf_cen {J : Subgroup G} {n : G} (hn : n ∈ Nor J) (x : G) :
    conjBy n (J ⊓ Cen x) = J ⊓ Cen (n * x * n⁻¹) := by
  have hJ := Subgroup.mem_normalizer_iff.mp hn
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨hyJ, hyc⟩, rfl⟩
    refine ⟨(hJ y).mp hyJ, ?_⟩
    calc n * y * n⁻¹ * (n * x * n⁻¹) = n * (y * x) * n⁻¹ := by group
      _ = n * (x * y) * n⁻¹ := by rw [hyc]
      _ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
  · rintro ⟨hzJ, hzc⟩
    refine ⟨n⁻¹ * z * n, ⟨?_, ?_⟩, by group⟩
    · rw [hJ]
      simpa [mul_assoc] using hzJ
    · calc n⁻¹ * z * n * x = n⁻¹ * (z * (n * x * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * x * n⁻¹) * z) * n := by rw [hzc]
        _ = x * (n⁻¹ * z * n) := by group

end CFSG.RankThree.PartTwo.Sec21.FF79
