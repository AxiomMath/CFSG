module

public import CFSG.Monster.B.E6.StdF4FiberFlags
public import CFSG.Monster.B.E6.StdF4FiberProd

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup betaG parStar mem_parStar
  parLeft parSmul parSmul_mk parMap_eq_mul parStar_left_mul betaPar thetaFirst
  residueFlag_parSmul_first SUFrob mem_betaGroup_iff coe_betaG_apply
  apply_mem_nativeParabolic_iff)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical
open scoped Pointwise

theorem stdLevi_le_stdGroup' :
    stdLevi firstJ ≤ stdGroup :=
  (stdLevi_le_nativeParabolic two_mem_firstJ).trans (nativeParabolic_le_stdGroup firstJ)

theorem leviStar_le_parStar :
    leviStar ≤ parStar firstJ := fun _ hγ =>
  stdLevi_le_nativeParabolic two_mem_firstJ hγ

theorem leviProj_betaPar
    (b : betaGroup) (p : nativeParabolic firstJ) :
    ((leviProj two_mem_firstJ (betaPar b p) : stdLevi firstJ) : ModGL Tag.E6 K) =
      (((b : MulAut stdGroup) ⟨(leviProj two_mem_firstJ p : ModGL Tag.E6 K),
        stdLevi_le_stdGroup' (leviProj two_mem_firstJ p).2⟩ : stdGroup) : ModGL Tag.E6 K) := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · have e : betaPar b p = p := Subtype.ext (by simp [h])
    rw [e, h]
    rfl
  · have e : betaPar b p = ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ :=
      Subtype.ext (by simp [h, coe_betaG_apply])
    rw [e, h, coe_betaG_apply]
    exact leviProj_betaGL two_mem_firstJ p

@[expose] def piStar :
    parStar firstJ →* leviStar where
  toFun γ := ⟨⟨⟨(leviProj two_mem_firstJ (parLeft γ) : ModGL Tag.E6 K),
    stdLevi_le_stdGroup' (leviProj two_mem_firstJ (parLeft γ)).2⟩, γ.1.right⟩,
    (leviProj two_mem_firstJ (parLeft γ)).2⟩
  map_one' := by
    refine Subtype.ext (SemidirectProduct.ext (Subtype.ext ?_) rfl)
    change ((leviProj two_mem_firstJ 1 : stdLevi firstJ) : ModGL Tag.E6 K) = 1
    rw [map_one]
    rfl
  map_mul' γ γ' := by
    refine Subtype.ext (SemidirectProduct.ext (Subtype.ext ?_) rfl)
    change ((leviProj two_mem_firstJ (parLeft (γ * γ')) : stdLevi firstJ) : ModGL Tag.E6 K) =
      (leviProj two_mem_firstJ (parLeft γ) : ModGL Tag.E6 K) *
        (((γ.1.right : MulAut stdGroup) ⟨(leviProj two_mem_firstJ (parLeft γ') : ModGL Tag.E6 K),
          stdLevi_le_stdGroup' (leviProj two_mem_firstJ (parLeft γ')).2⟩ : stdGroup) :
            ModGL Tag.E6 K)
    rw [parStar_left_mul, map_mul, Subgroup.coe_mul, leviProj_betaPar]

theorem coe_piStar_left
    (γ : parStar firstJ) :
    (((piStar γ : GStar).left : stdGroup) : ModGL Tag.E6 K) =
      (leviProj two_mem_firstJ (parLeft γ) : ModGL Tag.E6 K) :=
  rfl

theorem piStar_right
    (γ : parStar firstJ) : (piStar γ : GStar).right = γ.1.right :=
  rfl

theorem piStar_of_mem
    {γ : parStar firstJ} (hγ : (γ : GStar) ∈ leviStar) :
    piStar γ = ⟨γ, hγ⟩ := by
  refine Subtype.ext (SemidirectProduct.ext (Subtype.ext ?_) rfl)
  rw [coe_piStar_left, leviProj_of_mem two_mem_firstJ hγ]

theorem piStar_eq_one_iff
    (γ : parStar firstJ) : piStar γ = 1 ↔ (γ : GStar) ∈ radStar := by
  rw [mem_radStar]
  constructor
  · intro h
    have h1 := congrArg (fun z : leviStar => (((z : GStar).left : stdGroup) : ModGL Tag.E6 K)) h
    have h2 := congrArg (fun z : leviStar => (z : GStar).right) h
    simp only [coe_piStar_left] at h1
    refine ⟨(leviProj_eq_one_iff two_mem_firstJ (parLeft γ)).1 (Subtype.ext h1), h2⟩
  · rintro ⟨h1, h2⟩
    refine Subtype.ext (SemidirectProduct.ext (Subtype.ext ?_) h2)
    rw [coe_piStar_left, (leviProj_eq_one_iff two_mem_firstJ (parLeft γ)).2 h1]
    rfl

theorem exists_mul_of_mem_parStar
    (γ : parStar firstJ) :
    ∃ u ∈ radStar, ∃ l ∈ leviStar, (γ : GStar) = u * l := by
  have key : ∀ l : leviStar, piStar γ = l →
      ∃ u ∈ radStar, ∃ l' ∈ leviStar, (γ : GStar) = u * l' := by
    intro l hlγ
    let lP : parStar firstJ := ⟨l, leviStar_le_parStar l.2⟩
    have h1 : piStar lP = l := piStar_of_mem l.2
    have h2 : piStar (γ * lP⁻¹) = 1 := by rw [map_mul, map_inv, h1, hlγ, mul_inv_cancel]
    exact ⟨γ * (l : GStar)⁻¹, (piStar_eq_one_iff _).1 h2, l, l.2, by rw [inv_mul_cancel_right]⟩
  exact key _ rfl

abbrev parIStar
    (d : Fin 5) : Subgroup GStar :=
  betaStar (nativeParabolic (fibIF d : Set (Fin 4))) fun _ => betaGL_mem_nativeParabolic

theorem exists_mul_of_mem_parIStar
    {d : Fin 5} {δ : GStar} (hδ : δ ∈ parIStar d) :
    ∃ u ∈ radStar, ∃ l ∈ fibLStar d, δ = u * l := by
  have hδ' : (δ.left : ModGL Tag.E6 K) ∈ ((stdRadical firstJ : Set (ModGL Tag.E6 K)) *
      (leviParabolic firstJ (fibIF d : Set (Fin 4)) : Set (ModGL Tag.E6 K))) := by
    rw [← coe_nativeParabolic_eq_mul (fibIF_subset d)]
    exact hδ
  obtain ⟨q, hq, l, hl, e⟩ := hδ'
  have hqG : q ∈ stdGroup := stdRadical_le_stdGroup' hq
  have hlG : l ∈ stdGroup := fibLevi_le_stdGroup d hl
  refine ⟨SemidirectProduct.inl ⟨q, hqG⟩, mem_radStar.2 ⟨hq, rfl⟩,
    ⟨⟨l, hlG⟩, δ.right⟩, hl, SemidirectProduct.ext ?_ ?_⟩
  · apply Subtype.ext
    rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply, Subgroup.coe_mul]
    exact e.symm
  · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]

theorem fibCent_le_parIStar
    (d : Fin 5) : fibCent d ≤ parIStar d := by
  intro c hc
  obtain ⟨v, hv, m, hm, rfl⟩ := exists_mul_of_mem_fibCent hc
  obtain ⟨hv1, hv2⟩ := mem_fibVStar.1 hv
  change (((v * m).left : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic (fibIF d : Set (Fin 4))
  rw [SemidirectProduct.mul_left, hv2, map_one, MulAut.one_apply, Subgroup.coe_mul]
  exact mul_mem ((stdRadical_le_nativeParabolic' _) (fibV_le_stdRadical d hv1))
    (leviParabolic_le_nativeParabolic firstJ _ hm)

theorem mem_conjOrbit_radStar_iff
    {d : Fin 5} {γ γ' : GStar} (hγ : γ ∈ parStar firstJ)
    (hγ' : γ' ∈ parStar firstJ) :
    γ' * SemidirectProduct.inl (fibT d) * γ'⁻¹ ∈
        conjOrbit radStar (γ * SemidirectProduct.inl (fibT d) * γ⁻¹) ↔
      γ⁻¹ * γ' ∈ parIStar d := by
  set t : GStar := SemidirectProduct.inl (fibT d)
  constructor
  · rintro ⟨u, hu, e⟩
    have hc : (u * γ)⁻¹ * γ' ∈ fibCent d := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (mul_mem (radStar_le_parStar hu) hγ)) hγ', ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul]
      calc (u * γ)⁻¹ * γ' * t * ((u * γ)⁻¹ * γ')⁻¹ =
            (u * γ)⁻¹ * (γ' * t * γ'⁻¹) * (u * γ) := by group
        _ = (u * γ)⁻¹ * (u * (γ * t * γ⁻¹) * u⁻¹) * (u * γ) := by rw [e]
        _ = t := by group
    have hγu : γ⁻¹ * u * γ ∈ radStar := by
      have := conj_mem_radStar (inv_mem hγ) hu
      rwa [inv_inv] at this
    have e2 : γ⁻¹ * γ' = (γ⁻¹ * u * γ) * ((u * γ)⁻¹ * γ') := by group
    rw [e2]
    have h1 : γ⁻¹ * u * γ ∈ parIStar d := by
      change (((γ⁻¹ * u * γ).left : stdGroup) : ModGL Tag.E6 K) ∈
        nativeParabolic (fibIF d : Set (Fin 4))
      exact stdRadical_le_nativeParabolic' _ (mem_radStar.1 hγu).1
    exact mul_mem h1 (fibCent_le_parIStar d hc)
  · intro h
    obtain ⟨u, hu, l, hl, e⟩ := exists_mul_of_mem_parIStar h
    have hlc := (Subgroup.mem_inf.1 (fibLStar_le d hl)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hlc
    refine ⟨γ * u * γ⁻¹, conj_mem_radStar hγ hu, ?_⟩
    have hγ'e : γ' = γ * u * l := by rw [mul_assoc, ← e, mul_inv_cancel_left]
    rw [hγ'e]
    calc γ * u * γ⁻¹ * (γ * t * γ⁻¹) * (γ * u * γ⁻¹)⁻¹ = γ * u * t * u⁻¹ * γ⁻¹ := by group
      _ = γ * u * (l * t * l⁻¹) * u⁻¹ * γ⁻¹ := by rw [hlc, mul_inv_cancel_right]
      _ = γ * u * l * t * (γ * u * l)⁻¹ := by group

theorem mem_parIStar_iff_parLeft
    {d : Fin 5} (γ γ' : parStar firstJ) :
    (γ : GStar)⁻¹ * γ' ∈ parIStar d ↔
      ((parLeft γ)⁻¹ * parLeft γ' : nativeParabolic firstJ).1 ∈
        nativeParabolic (fibIF d : Set (Fin 4)) := by
  have e : parLeft (γ⁻¹ * γ') = betaPar (γ : GStar).right⁻¹ ((parLeft γ)⁻¹ * parLeft γ') := by
    apply Subtype.ext
    change ((((γ : GStar)⁻¹ * γ').left : stdGroup) : ModGL Tag.E6 K) = _
    rw [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      ← map_mul]
    rfl
  change ((parLeft (γ⁻¹ * γ') : nativeParabolic firstJ) : ModGL Tag.E6 K) ∈
    nativeParabolic (fibIF d : Set (Fin 4)) ↔ _
  rw [e]
  exact apply_mem_nativeParabolic_iff _ _ _

abbrev fibCosets
    (d : Fin 5) : Type := leviStar ⧸ (fibLStar d).subgroupOf leviStar

theorem fibLStar_le_leviStar
    (d : Fin 5) : fibLStar d ≤ leviStar := fun _ hγ =>
  leviParabolic_le_stdLevi two_mem_firstJ (fibIF_subset d) hγ

open _root_.Classical in
@[expose] def fibCoset
    (d : Fin 5) (x : GStar) : fibCosets d :=
  if h : ∃ γ : parStar firstJ, (γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹ = x
  then QuotientGroup.mk (piStar h.choose) else QuotientGroup.mk 1

theorem fibCoset_conj
    (d : Fin 5) (γ : parStar firstJ) :
    fibCoset d ((γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹) =
      QuotientGroup.mk (piStar γ) := by
  have hex : ∃ γ' : parStar firstJ, (γ' : GStar) * SemidirectProduct.inl (fibT d) *
      (γ' : GStar)⁻¹ = (γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹ := ⟨γ, rfl⟩
  rw [fibCoset, dite_eq_left hex]
  set δ := hex.choose
  have hδ : (γ : GStar)⁻¹ * δ ∈ parIStar d :=
    (mem_conjOrbit_radStar_iff γ.2 δ.2).1 (by rw [hex.choose_spec]; exact mem_conjOrbit_self _ _)
  obtain ⟨u, hu, l, hl, e⟩ := exists_mul_of_mem_parIStar hδ
  refine (QuotientGroup.eq.2 ?_).symm
  have hu' : piStar ⟨u, radStar_le_parStar hu⟩ = 1 := (piStar_eq_one_iff _).2 hu
  have hl' : piStar ⟨l, leviStar_le_parStar (fibLStar_le_leviStar d hl)⟩ =
      ⟨l, fibLStar_le_leviStar d hl⟩ := piStar_of_mem _
  have e' : (γ⁻¹ * δ : parStar firstJ) = ⟨u, radStar_le_parStar hu⟩ *
      ⟨l, leviStar_le_parStar (fibLStar_le_leviStar d hl)⟩ := Subtype.ext e
  rw [← map_inv, ← map_mul, e', map_mul, hu', hl', one_mul, Subgroup.mem_subgroupOf]
  exact hl

theorem fibCoset_mul
    (d : Fin 5) {u l : GStar} (hu : u ∈ radStar) (hl : l ∈ leviStar) :
    fibCoset d (u * l * SemidirectProduct.inl (fibT d) * (u * l)⁻¹) =
      QuotientGroup.mk (⟨l, hl⟩ : leviStar) := by
  have h := fibCoset_conj d (⟨u, radStar_le_parStar hu⟩ * ⟨l, leviStar_le_parStar hl⟩)
  rw [map_mul, (piStar_eq_one_iff _).2 hu, piStar_of_mem hl, one_mul] at h
  exact h

theorem fibCoset_eq_iff
    {d : Fin 5} {x y : GStar} (hx : x ∈ fibOrbit d) (hy : y ∈ fibOrbit d) :
    fibCoset d x = fibCoset d y ↔ y ∈ conjOrbit radStar x := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  obtain ⟨γ', hγ', rfl⟩ := hy
  rw [mem_conjOrbit_radStar_iff hγ hγ', fibCoset_conj d ⟨γ, hγ⟩, fibCoset_conj d ⟨γ', hγ'⟩,
    QuotientGroup.eq, ← map_inv, ← map_mul, Subgroup.mem_subgroupOf, mem_betaStar, mem_betaStar,
    coe_piStar_left, ← mem_nativeParabolic_iff two_mem_firstJ (fibIF_subset d)]
  exact Iff.rfl

open _root_.Classical in
@[expose] def fibSub
    (d : Fin 5) (x : GStar) : Submodule K (Fin 6 → K) :=
  if h : ∃ γ : parStar firstJ, (γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹ = x
  then flagSub (fibKd d) (parLeft h.choose) else ⊥

theorem flagSub_eq_iff_parIStar
    {d : Fin 5} (hd : IsMid d) (γ γ' : parStar firstJ) :
    flagSub (fibKd d) (parLeft γ) = flagSub (fibKd d) (parLeft γ') ↔
      (γ : GStar)⁻¹ * γ' ∈ parIStar d := by
  rw [flagSub_eq_iff_mem (flagStab_fibKd hd), mem_parIStar_iff_parLeft]

theorem fibSub_conj
    {d : Fin 5} (hd : IsMid d) (γ : parStar firstJ) :
    fibSub d ((γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹) =
      flagSub (fibKd d) (parLeft γ) := by
  have hex : ∃ γ' : parStar firstJ, (γ' : GStar) * SemidirectProduct.inl (fibT d) *
      (γ' : GStar)⁻¹ = (γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹ := ⟨γ, rfl⟩
  rw [fibSub, dite_eq_left hex]
  refine ((flagSub_eq_iff_parIStar hd γ hex.choose).2 ?_).symm
  exact (mem_conjOrbit_radStar_iff γ.2 hex.choose.2).1
    (by rw [hex.choose_spec]; exact mem_conjOrbit_self _ _)

theorem fibSub_eq_iff
    {d : Fin 5} (hd : IsMid d) {x y : GStar} (hx : x ∈ fibOrbit d)
    (hy : y ∈ fibOrbit d) : fibSub d x = fibSub d y ↔ y ∈ conjOrbit radStar x := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  obtain ⟨γ', hγ', rfl⟩ := hy
  rw [mem_conjOrbit_radStar_iff hγ hγ', fibSub_conj hd ⟨γ, hγ⟩, fibSub_conj hd ⟨γ', hγ'⟩]
  exact flagSub_eq_iff_parIStar hd ⟨γ, hγ⟩ ⟨γ', hγ'⟩

theorem image_fibSub
    {d : Fin 5} (hd : IsMid d) : fibSub d '' fibOrbit d = isoSubs (fibKd d) := by
  ext S
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    rw [fibSub_conj hd ⟨γ, hγ⟩]
    exact flagSub_mem_isoSubs _ _
  · intro hS
    obtain ⟨p, rfl⟩ := exists_flagSub_eq hS
    have hpG : (p : ModGL Tag.E6 K) ∈ stdGroup := nativeParabolic_le_stdGroup firstJ p.2
    have hγ : SemidirectProduct.inl (⟨p, hpG⟩ : stdGroup) ∈ parStar firstJ := p.2
    refine ⟨_, ⟨_, hγ, rfl⟩, ?_⟩
    rw [fibSub_conj hd ⟨_, hγ⟩]
    rfl

theorem fibSub_conj_conj
    {d : Fin 5} (hd : IsMid d) (γ γ' : parStar firstJ) :
    fibSub d ((γ' : GStar) * ((γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹) *
      (γ' : GStar)⁻¹) =
      (thetaFirst γ' • residueFlag (QuotientGroup.mk (parLeft γ))).sub (fibKd d) := by
  have e : (γ' : GStar) * ((γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹) *
      (γ' : GStar)⁻¹ = ((γ' * γ : parStar firstJ) : GStar) * SemidirectProduct.inl (fibT d) *
        ((γ' * γ : parStar firstJ) : GStar)⁻¹ := by
    rw [Subgroup.coe_mul, mul_inv_rev]
    group
  rw [e, fibSub_conj hd, ← residueFlag_parSmul_first, parSmul_mk, parMap_eq_mul,
    ← parStar_left_mul]
  rfl

theorem fibLevi_of_JJ
    {d : Fin 5} (hd : d = 0 ∨ d = 4) : fibLevi d = stdLevi firstJ := by
  have hJ : ((({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4))) = firstJ := by
    ext i
    simp [firstJ]
  rcases hd with rfl | rfl
  · exact (congrArg (leviParabolic firstJ) hJ).trans leviParabolic_firstJ
  · exact (congrArg (leviParabolic firstJ) hJ).trans leviParabolic_firstJ

theorem mem_conjOrbit_radStar_of_JJ
    {d : Fin 5} (hd : d = 0 ∨ d = 4) {x y : GStar}
    (hx : x ∈ fibOrbit d) (hy : y ∈ fibOrbit d) : y ∈ conjOrbit radStar x := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  obtain ⟨γ', hγ', rfl⟩ := hy
  rw [mem_conjOrbit_radStar_iff hγ hγ']
  change ((((γ⁻¹ * γ').left : stdGroup) : ModGL Tag.E6 K)) ∈
    nativeParabolic (fibIF d : Set (Fin 4))
  have hJ : (fibIF d : Set (Fin 4)) = firstJ := by
    rcases hd with rfl | rfl <;> (ext i; simp [firstJ, fibIF])
  rw [hJ]
  exact (mul_mem (inv_mem hγ) hγ' : γ⁻¹ * γ' ∈ parStar firstJ)

end CFSG.Monster.B.E6.StdF4
