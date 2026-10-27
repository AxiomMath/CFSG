module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {S S' : Type} [Group S] [Finite S] [Group S'] [Finite S']

private theorem iso_isSLThreePi {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : Sec4.IsSLThreePi Y) : Sec4.IsSLThreePi Y' := by
  unfold Sec4.IsSLThreePi Sec4.IsSLThreePiAt at h ⊢
  obtain ⟨q, K, hK, hfin, hcase⟩ := h
  refine ⟨q, K, hK, hfin, ?_⟩
  rcases hcase with ⟨h1, h2, ⟨f⟩⟩ | ⟨h1, h2, ⟨f⟩⟩
  · exact Or.inl ⟨h1, h2, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨h1, h2, ⟨e.symm.trans f⟩⟩

private theorem iso_isTripleCover {Y Y' Z : Type} [Group Y] [Group Y'] [Group Z]
    (e : Y ≃* Y') (h : Sec4.IsTripleCover Y Z) : Sec4.IsTripleCover Y' Z := by
  unfold Sec4.IsTripleCover at h ⊢
  obtain ⟨hcard, ⟨f⟩⟩ := h
  have hmap : (Subgroup.center Y).map e.toMonoidHom = Subgroup.center Y' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y') e hmap).symm.trans f⟩⟩
  rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact hcard

theorem isType198_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsType198 Y) : IsType198 Y' := by
  unfold IsType198 at h ⊢
  rcases h with h | h | h
  · exact Or.inl (iso_isSLThreePi e h)
  · exact Or.inr (Or.inl (iso_isTripleCover e h))
  · exact Or.inr (Or.inr (iso_isTripleCover e h))

private theorem iso_theta (e : S ≃* S') (L : Subgroup S) :
    (aschbacherSolvableCore 3 L).map (L.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      aschbacherSolvableCore 3 (L.map e.toMonoidHom) :=
  CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three _

private noncomputable def iso_quotCore (e : S ≃* S') (L : Subgroup S) :
    (L ⧸ aschbacherSolvableCore 3 L) ≃*
      (L.map e.toMonoidHom) ⧸ aschbacherSolvableCore 3 (L.map e.toMonoidHom) :=
  QuotientGroup.congr (aschbacherSolvableCore 3 L) (aschbacherSolvableCore 3 (L.map e.toMonoidHom))
    (L.equivMapOfInjective e.toMonoidHom e.injective) (iso_theta e L)

private theorem iso_thetaIn (e : S ≃* S') (L : Subgroup S) :
    thetaIn (L.map e.toMonoidHom) = (thetaIn L).map e.toMonoidHom := by
  have hcomp : (L.map e.toMonoidHom).subtype.comp
      (L.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
        e.toMonoidHom.comp L.subtype :=
    MonoidHom.ext fun _ => rfl
  unfold thetaIn
  rw [← iso_theta e L, Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem iso_centralizer (e : S ≃* S') (c : S) :
    (Subgroup.centralizer ({c} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e c} : Set S') := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e x * e c = e c * e x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

private theorem iso_congr_conj (e : S ≃* S') (s : S) :
    (MulAut.congr e).toMonoidHom (MulAut.conj s) = MulAut.conj (e s) := by
  apply MulEquiv.ext
  intro x
  change e (s * e.symm x * s⁻¹) = e s * x * (e s)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem LocalDatum.map (e : S ≃* S') {c : S} {L : Subgroup S} (h : LocalDatum S c L) :
    LocalDatum S' (e c) (L.map e.toMonoidHom) where
  orderOf_eq := (orderOf_injective e.toMonoidHom e.injective c).trans h.orderOf_eq
  le_centralizer := by
    rintro _ ⟨l, hl, rfl⟩
    have hlc := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e l * e c = e c * e l
    rw [← map_mul, ← map_mul, hlc]
  mem := Subgroup.mem_map_of_mem e.toMonoidHom h.mem
  subnormal := by
    let φ : Subgroup.centralizer ({c} : Set S) ≃* Subgroup.centralizer ({e c} : Set S') :=
      (Subgroup.equivMapOfInjective (Subgroup.centralizer ({c} : Set S)) e.toMonoidHom
        e.injective).trans (MulEquiv.subgroupCongr (iso_centralizer e c))
    have hφ : (L.subgroupOf (Subgroup.centralizer ({c} : Set S))).map φ.toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf (Subgroup.centralizer ({e c} : Set S')) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_map_of_mem e.toMonoidHom (Subgroup.mem_subgroupOf.mp hy))
      · intro hx
        obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        exact ⟨⟨l, h.le_centralizer hl⟩, Subgroup.mem_subgroupOf.mpr hl, Subtype.ext hle⟩
    have hsn := Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective h.subnormal
    rw [hφ] at hsn
    exact hsn
  perfect := by
    haveI := h.perfect
    exact Group.IsPerfect.map e.toMonoidHom
  quasisimple := CFSG.IsQuasisimple.of_mulEquiv (iso_quotCore e L).symm h.quasisimple
  type := isType198_of_mulEquiv (iso_quotCore e L) h.type

theorem AutDatum.map (e : S ≃* S') {c : S} {L : Subgroup S} {𝒟 : Subgroup (MulAut S)}
    (h : AutDatum S c L 𝒟) :
    AutDatum S' (e c) (L.map e.toMonoidHom) (𝒟.map (MulAut.congr e).toMonoidHom) where
  toLocalDatum := LocalDatum.map e h.toLocalDatum
  pow_three := by
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    rw [← map_pow, h.pow_three ψ hψ, map_one]
  card := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective]
    exact h.card
  conj_mem := Subgroup.mem_map.mpr ⟨MulAut.conj c, h.conj_mem, iso_congr_conj e c⟩
  map_eq := by
    intro φ hφ x
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have key : e.symm ((MulAut.congr e).toMonoidHom ψ x) = ψ (e.symm x) := by
      change e.symm (e (ψ (e.symm x))) = ψ (e.symm x)
      exact e.symm_apply_apply _
    rw [key]
    exact h.map_eq ψ hψ (e.symm x)
  trivial := by
    intro φ hφ l hl
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hl
    rw [iso_thetaIn]
    have key : (MulAut.congr e).toMonoidHom ψ (e.toMonoidHom m) * (e.toMonoidHom m)⁻¹ =
        e.toMonoidHom (ψ m * m⁻¹) := by
      change e (ψ (e.symm (e m))) * (e m)⁻¹ = e (ψ m * m⁻¹)
      rw [e.symm_apply_apply, map_mul, map_inv]
    rw [key]
    exact Subgroup.mem_map_of_mem _ (h.trivial ψ hψ m hm)

theorem NoLocalDatum.of_mulEquiv (e : S ≃* S') (h : NoLocalDatum S') : NoLocalDatum S := by
  intro c L hLD
  exact h (e c) (L.map e.toMonoidHom) (LocalDatum.map e hLD)

theorem NoAutDatum.of_mulEquiv (e : S ≃* S') (h : NoAutDatum S') : NoAutDatum S := by
  intro c L 𝒟 hA
  exact h (e c) (L.map e.toMonoidHom) (𝒟.map (MulAut.congr e).toMonoidHom) (AutDatum.map e hA)

theorem NoLocalDatum.noAutDatum (h : NoLocalDatum S) : NoAutDatum S := by
  intro c L 𝒟 hA
  exact h c L hA.toLocalDatum

end CFSG.RankThree.PartTwo.Sec19.SimsC198
