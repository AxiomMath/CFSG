module

public import CFSG.Timmesfeld.Bridge.RootStructWTIFaithful
public import CFSG.Timmesfeld.Bridge.RootStructWTICard

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def lineRadical (D : Set G) (a : G) (L : Subgroup G) : Subgroup G :=
  (⨆ p : {p : G // p ∈ D ∧ p ∈ L ∧ p ∉ rootGroup D a},
    nCore D p.1 ⊓ Subgroup.centralizer (L : Set G)) ⊔ nCore D a

theorem nCore_le_lineRadical (a : G) (L : Subgroup G) : nCore D a ≤ lineRadical D a L :=
  le_sup_right

theorem nCore_inf_le_lineRadical {a p : G} {L : Subgroup G} (hp : p ∈ D) (hpL : p ∈ L)
    (hpa : p ∉ rootGroup D a) :
    nCore D p ⊓ Subgroup.centralizer (L : Set G) ≤ lineRadical D a L :=
  le_sup_left.trans' (le_iSup (fun p : {p : G // p ∈ D ∧ p ∈ L ∧ p ∉ rootGroup D a} =>
    nCore D p.1 ⊓ Subgroup.centralizer (L : Set G)) ⟨p, hp, hpL, hpa⟩)

theorem map_conj_lineRadical_le (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a g : G}
    (hga : Commute g a) (L : Subgroup G) :
    (lineRadical D a L).map (MulAut.conj g).toMonoidHom ≤
      lineRadical D a (L.map (MulAut.conj g).toMonoidHom) := by
  have hA : (rootGroup D a).map (MulAut.conj g).toMonoidHom = rootGroup D a := by
    rw [← rootGroup_conj hclass, hga.eq, mul_inv_cancel_right]
  rw [lineRadical, Subgroup.map_sup, Subgroup.map_iSup]
  refine sup_le (iSup_le fun p => ?_) ?_
  · obtain ⟨p, hpD, hpL, hpa⟩ := p
    refine (?_ : _ ≤ nCore D (g * p * g⁻¹) ⊓
      Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).trans
      (nCore_inf_le_lineRadical (conj_mem_of_isClass hclass g hpD)
        ⟨p, hpL, rfl⟩ fun h' => hpa ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨conj_mem_nCore_conj hclass hxN g, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      have := (Subgroup.mem_centralizer_iff.1 hxC) t ht
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
        _ = g * (x * t) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
    · rw [← hA] at h'
      have := RankOne.mem_map_conj.1 h'
      rwa [show g⁻¹ * (g * p * g⁻¹) * g = p by group] at this
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact nCore_le_lineRadical a _ (conj_mem_nCore hclass hga hx)

theorem nCore_le_closure_commute (D : Set G) (a : G) :
    nCore D a ≤ Subgroup.closure {x | x ∈ D ∧ Commute a x} :=
  Subgroup.closure_mono fun _ hx => ⟨hx.1, (Moufang.commute_of_mem_twoCore hx.2).symm⟩

theorem map_conj_lineRadical (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a g : G}
    (hga : Commute g a) (L : Subgroup G) :
    (lineRadical D a L).map (MulAut.conj g).toMonoidHom =
      lineRadical D a (L.map (MulAut.conj g).toMonoidHom) := by
  refine le_antisymm (map_conj_lineRadical_le hclass hga L) ?_
  have h1 := map_conj_lineRadical_le hclass hga.inv_left (L.map (MulAut.conj g).toMonoidHom)
  rw [RankOne.map_conj_inv_map_conj] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rwa [RankOne.map_conj_map_conj_inv] at h2

theorem centralizer_le_normalizer_rootGroup (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (rootGroup D a : Set G) := by
  intro g hg
  rw [← RankOne.map_conj_eq_self_iff, ← rootGroup_conj hclass,
    (Subgroup.mem_centralizer_singleton_iff.1 hg), mul_inv_cancel_right]

namespace LineSetting

variable (hL : LineSetting G D) {a : G} (ha : a ∈ D)
include hL ha

theorem lineRadical_eq {L : Subgroup G} (hL' : L ∈ rootLines D a) {p : G} (hp : p ∈ D)
    (hpL : p ∈ L) (hpa : p ∉ rootGroup D a) :
    lineRadical D a L = (nCore D p ⊓ Subgroup.centralizer (L : Set G)) ⊔ nCore D a := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  refine le_antisymm (sup_le (iSup_le fun p' => ?_) le_sup_right)
    (sup_le (nCore_inf_le_lineRadical hp hpL hpa) le_sup_right)
  obtain ⟨p', hp'D, hp'L, hp'a⟩ := p'
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hL'
  obtain ⟨L₂, hL₂, hL₂T⟩ := hL.exists_ne_mem_rootLines ha ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨b, hb, hab, habD, hbT, rfl⟩ := hL₂
  have hbL : b ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hL₂T (hL.sup_rootGroup_eq_of_mem_sup ha hb hd hab hbT had hadD hdT h')
  obtain ⟨m, hm, hmp⟩ := hL.exists_conj_mem_rootSet ha hd had hadD hdT hb hab habD hbL hpL hpa
    hp'L hp'a
  have hmC : m ∈ Subgroup.closure {x | x ∈ D ∧ Commute a x} := by
    rcases hm with rfl | hm
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hm.1, ((hm.2 a ha).2 hab.symm).symm⟩
  have hmM : m ∈ nCore D a := hL.closure_commute_le_nCore ha hmC
  have hmL := hL.map_conj_eq_of_mem_closure ha hmC ⟨d, hd, had, hadD, hdT, rfl⟩
  intro x hx
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
  have h1 : m * x * m⁻¹ ∈ nCore D p ⊓ Subgroup.centralizer
      ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← nCore_eq_of_mem_rootSet hclass hD hp hmp]
      exact conj_mem_nCore_conj hclass hxN m
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : m⁻¹ * t * m ∈ rootGroup D a ⊔ rootGroup D d := by
        rw [← hmL] at ht
        exact RankOne.mem_map_conj.1 ht
      have h2 := (Subgroup.mem_centralizer_iff.1 hxC) _ ht'
      calc t * (m * x * m⁻¹) = m * ((m⁻¹ * t * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * t * m)) * m⁻¹ := by rw [h2]
        _ = m * x * m⁻¹ * t := by group
  have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hmM))
    (Subgroup.mem_sup_left h1)) (Subgroup.mem_sup_right hmM)

omit hL in
theorem lineRadical_le_centralizer {L : Subgroup G} (hL' : L ∈ rootLines D a) :
    lineRadical D a L ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hL'
  refine sup_le (iSup_le fun p x hx => ?_) fun x hx => ?_
  · exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2) a (left_mem_line ha)).symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_nCore hx).eq

theorem lineRadical_le_normalizer {L : Subgroup G} (hL' : L ∈ rootLines D a) :
    lineRadical D a L ≤ Subgroup.normalizer (L : Set G) := by
  refine sup_le (iSup_le fun p x hx => ?_) fun x hx => ?_
  · rw [← RankOne.map_conj_eq_self_iff]
    exact map_conj_eq_of_forall_commute fun t ht =>
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2) t ht).symm
  · rw [← RankOne.map_conj_eq_self_iff]
    exact hL.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hx) hL'

theorem mem_nCore_of_mem_lineRadical {L L' : Subgroup G} (hL' : L ∈ rootLines D a)
    (hL'' : L' ∈ rootLines D a) (hne : L' ≠ L) {x : G} (hx : x ∈ lineRadical D a L)
    (hxL : L'.map (MulAut.conj x).toMonoidHom = L') : x ∈ nCore D a := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hL'
  obtain ⟨b, hb, hab, habD, hbT, rfl⟩ := hL''
  have hbL : b ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hne (hL.sup_rootGroup_eq_of_mem_sup ha hb hd hab hbT had hadD hdT h')
  rw [hL.lineRadical_eq ha ⟨d, hd, had, hadD, hdT, rfl⟩ hd (right_mem_line hd)
    (fun h' => hdT (mem_rootSet_of_mem_rootGroup hclass ha hd h'))] at hx
  have hle : nCore D d ⊓ Subgroup.centralizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) :
      Set G) ≤ Subgroup.normalizer (nCore D a : Set G) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    have hka : Commute k a :=
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2) a (left_mem_line ha)).symm
    intro y
    refine ⟨fun hy => conj_mem_nCore hclass hka hy, fun hy => ?_⟩
    have := conj_mem_nCore hclass hka.inv_left hy
    rwa [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at this
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
  obtain ⟨k, hk, m, hm, rfl⟩ := hx
  obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.1 hk
  have hka : Commute k a :=
    ((Subgroup.mem_centralizer_iff.1 hkC) a (left_mem_line ha)).symm
  have hmL := hL.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hm)
    (L := rootGroup D a ⊔ rootGroup D b) ⟨b, hb, hab, habD, hbT, rfl⟩
  have hkL : (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj k).toMonoidHom =
      rootGroup D a ⊔ rootGroup D b := by
    rw [RankOne.map_conj_mul, hmL] at hxL
    exact hxL
  exact Subgroup.mul_mem _ (hL.mem_nCore_of_map_conj_eq ha hd had hadD hdT hb hab habD hbL hkN hka
    hkL) hm

theorem exists_mem_lineRadical_map_conj_eq {L L₁ L₂ : Subgroup G} (hL' : L ∈ rootLines D a)
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h₁L : L₁ ≠ L) (h₂L : L₂ ≠ L) :
    ∃ x ∈ lineRadical D a L, L₁.map (MulAut.conj x).toMonoidHom = L₂ := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hL'
  obtain ⟨b, hb, hab, habD, hbT, rfl⟩ := h₁
  obtain ⟨c, hcD, hac, hacD, hcT, rfl⟩ := h₂
  have hbL : b ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    h₁L (hL.sup_rootGroup_eq_of_mem_sup ha hb hd hab hbT had hadD hdT h')
  have hcL : c ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    h₂L (hL.sup_rootGroup_eq_of_mem_sup ha hcD hd hac hcT had hadD hdT h')
  obtain ⟨k, ⟨hkN, hkC⟩, hk⟩ := hL.exists_mem_nCore_conj_line_eq ha hd had hadD hdT hb hab habD hbL
    hcD hac hacD hcL
  have hka := Subgroup.mem_centralizer_singleton_iff.1 hkC
  refine ⟨k, nCore_inf_le_lineRadical hd (right_mem_line hd)
    (fun h' => hdT (mem_rootSet_of_mem_rootGroup hclass ha hd h'))
    (Subgroup.mem_inf.2 ⟨hkN, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩), hk⟩
  exact (hL.commute_of_mem_nCore_of_commute ha hd had hadD hdT hkN hka ht).symm.eq

theorem exists_map_conj_eq_of_three_le {L L' : Subgroup G} (hL₁ : L ∈ rootLines D a)
    (hL₂ : L' ∈ rootLines D a) (h3 : 3 ≤ (rootLines D a).ncard) :
    ∃ g ∈ Subgroup.centralizer ({a} : Set G), L.map (MulAut.conj g).toMonoidHom = L' := by
  by_cases hLL : L = L'
  · exact ⟨1, Subgroup.one_mem _, by rw [hLL, RankOne.map_conj_one]⟩
  obtain ⟨L₃, hL₃, h₃⟩ : ∃ L₃ ∈ rootLines D a, L₃ ≠ L ∧ L₃ ≠ L' := by
    by_contra! hno
    have hsub : rootLines D a ⊆ {L, L'} := fun L₃ hL₃ => by
      by_cases h : L₃ = L
      · exact Or.inl h
      · exact Or.inr (hno L₃ hL₃ h)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hLL] at this
    omega
  obtain ⟨x, hx, hxL⟩ := hL.exists_mem_lineRadical_map_conj_eq ha hL₃ hL₁ hL₂ (Ne.symm h₃.1)
    (Ne.symm h₃.2)
  exact ⟨x, lineRadical_le_centralizer ha hL₃ hx, hxL⟩

theorem lineGroup_eq {d : G} (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) {T' : Subgroup G} (hT' : T' ∈ rootLines D a)
    (hne : T' ≠ rootGroup D a ⊔ rootGroup D d) (h3 : 3 ≤ (rootLines D a).ncard) :
    lineGroup D a d = lineRadical D a (rootGroup D a ⊔ rootGroup D d) ⊔ lineRadical D a T' := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  set T := rootGroup D a ⊔ rootGroup D d with hTdef
  have hT : T ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  have hda : d ∉ rootGroup D a := fun h' => hdT (mem_rootSet_of_mem_rootGroup hclass ha hd h')
  have hK : (nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a = lineRadical D a T := by
    rw [hL.lineRadical_eq ha hT hd (right_mem_line hd) hda]
    refine le_antisymm (sup_le (fun k hk => ?_) le_sup_right)
      (sup_le ((inf_le_inf_left _ fun k hk => ?_).trans le_sup_left) le_sup_right)
    · obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.1 hk
      refine Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hkN, Subgroup.mem_centralizer_iff.2
        fun t ht => ?_⟩)
      exact (hL.commute_of_mem_nCore_of_commute ha hd had hadD hdT hkN
        (Subgroup.mem_centralizer_singleton_iff.1 hkC) ht).symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hk) a (left_mem_line ha)).symm
  have hall : ∀ L ∈ rootLines D a, lineRadical D a L ≤ lineRadical D a T ⊔ lineRadical D a T' := by
    intro L hL'
    by_cases hLT : L = T
    · rw [hLT]; exact le_sup_left
    by_cases hLT' : L = T'
    · rw [hLT']; exact le_sup_right
    obtain ⟨z, hz, hzL⟩ := hL.exists_mem_lineRadical_map_conj_eq ha hT' hT hL' hne.symm hLT'
    have hza := Subgroup.mem_centralizer_singleton_iff.1 (lineRadical_le_centralizer ha hT' hz)
    rw [← hzL, ← map_conj_lineRadical hclass hza]
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hz' : z ∈ lineRadical D a T ⊔ lineRadical D a T' := Subgroup.mem_sup_right hz
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz' (Subgroup.mem_sup_left hx))
      (Subgroup.inv_mem _ hz')
  refine le_antisymm (iSup_le fun g => ?_) (sup_le ?_ ?_)
  · have hga := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [hK, map_conj_lineRadical hclass hga]
    exact hall _ (hL.map_conj_mem_rootLines ha (centralizer_le_normalizer_rootGroup hclass a g.2)
      hT)
  · rw [← hK]
    calc (nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a =
        ((nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a).map
          (MulAut.conj ((1 : Subgroup.centralizer ({a} : Set G)) : G)).toMonoidHom := by
          rw [Subgroup.coe_one, RankOne.map_conj_one]
      _ ≤ lineGroup D a d := le_iSup (fun g : Subgroup.centralizer ({a} : Set G) =>
          ((nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a).map
            (MulAut.conj (g : G)).toMonoidHom) 1
  · obtain ⟨g, hg, hgT⟩ := hL.exists_map_conj_eq_of_three_le ha hT hT' h3
    rw [← hgT, ← map_conj_lineRadical hclass (Subgroup.mem_centralizer_singleton_iff.1 hg), ← hK]
    exact le_iSup (fun g : Subgroup.centralizer ({a} : Set G) =>
      ((nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a).map (MulAut.conj (g : G)).toMonoidHom)
      ⟨g, hg⟩

end LineSetting

end CFSG.Timmesfeld.Bridge
