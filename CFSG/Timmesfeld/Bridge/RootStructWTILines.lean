module

public import CFSG.Timmesfeld.Bridge.RootStructWTIRegular

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem map_conj_inv_map_conj_eq (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

theorem closure_commute_le_normalizer (D : Set G) (a : G) :
    Subgroup.closure {x | x ∈ D ∧ Commute a x} ≤ Subgroup.normalizer (rootGroup D a : Set G) := by
  rw [Subgroup.closure_le]
  rintro x ⟨hx, hax⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [(commute_of_mem_rootGroup_of_commute hu hx hax).symm.eq, mul_inv_cancel_right]
    exact hu
  · intro hu
    have h1 := commute_of_mem_rootGroup_of_commute hu hx hax
    have h2 : u = x⁻¹ * (x * u * x⁻¹) * x := by group
    rw [h2, mul_assoc, h1.eq, inv_mul_cancel_left]
    exact hu


theorem mul_self_mem_rootGroup_of_mem_nCore (h : Hyp G D) (hc : RootClosure D) {p k : G}
    (hp : p ∈ D) (hk : k ∈ nCore D p) : k * k ∈ rootGroup D p := by
  have hR := nCoreCommutatorInRoot_of_hyp h hc
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rw [h.root.mul_self_eq_one hx.1]
    exact (rootGroup D p).one_mem
  | one => rw [mul_one]; exact (rootGroup D p).one_mem
  | mul x y hx hy ihx ihy =>
    have e : x * y * (x * y) = x * x * (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹) * (y * y) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ihx (hR p hp _ (Subgroup.inv_mem _ hx) _ hy)) ihy
  | inv x _ ih =>
    rw [← mul_inv_rev]
    exact Subgroup.inv_mem _ ih

@[expose] def lineCoreGen (D : Set G) (a : G) (T : Subgroup G) : Set G :=
  {k | (∃ p ∈ D, p ∈ T ∧ p ∉ rootGroup D a ∧ k ∈ Subgroup.closure {x | x ∈ D ∧ Commute p x}) ∧
    ∀ t ∈ T, Commute k t}

theorem map_conj_eq_of_forall_commute {T : Subgroup G} {g : G} (hg : ∀ t ∈ T, Commute g t) :
    T.map (MulAut.conj g).toMonoidHom = T := by
  refine le_antisymm ?_ fun t ht => ⟨t, ht, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hg t ht).eq, mul_inv_cancel_right]
    exact ht
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hg t ht).eq, mul_inv_cancel_right]

namespace LineSetting

variable (hL : LineSetting G D) {a : G} (ha : a ∈ D)
include hL ha

theorem map_conj_mem_rootLines {g : G} (hg : g ∈ Subgroup.normalizer (rootGroup D a : Set G))
    {L : Subgroup G} (hL' : L ∈ rootLines D a) :
    L.map (MulAut.conj g).toMonoidHom ∈ rootLines D a := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  obtain ⟨b, hb, hab, habD, hbT, rfl⟩ := hL'
  have haA : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self ha)
  have ha' : g * a * g⁻¹ ∈ rootSet D a :=
    mem_rootSet_of_mem_rootGroup hclass ha (conj_mem_of_isClass hclass g ha)
      ((Subgroup.mem_normalizer_iff.1 hg a).1 haA)
  have hb' : g * b * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hb
  have hab' : Commute a (g * b * g⁻¹) := ((ha'.2 _ hb').1 ((Commute.conj_iff g).2 hab))
  have hbT' : g * b * g⁻¹ ∉ rootSet D a := by
    rw [← rootSet_eq_of_mem ha', rootSet_conj hclass]
    rintro ⟨e, he, he'⟩
    have hex : e = b := by simpa using he'
    exact hbT (hex ▸ he)
  refine ⟨g * b * g⁻¹, hb', hab', ?_, hbT', ?_⟩
  · rcases hL.mem_rootSet_or_collinear ha hb' hab'.symm with h' | ⟨-, h'⟩
    · exact absurd h' hbT'
    · exact h'
  · rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass,
      rootGroup_eq_of_mem ha']

@[expose] noncomputable def linePerm (g : Subgroup.normalizer (rootGroup D a : Set G)) :
    Equiv.Perm (rootLines D a) where
  toFun L := ⟨L.1.map (MulAut.conj (g : G)).toMonoidHom, hL.map_conj_mem_rootLines ha g.2 L.2⟩
  invFun L := ⟨L.1.map (MulAut.conj (g : G)⁻¹).toMonoidHom,
    hL.map_conj_mem_rootLines ha (Subgroup.inv_mem _ g.2) L.2⟩
  left_inv L := Subtype.ext (map_conj_inv_map_conj_eq (g : G) L.1)
  right_inv L := Subtype.ext (by
    have := map_conj_inv_map_conj_eq (g : G)⁻¹ L.1
    rwa [inv_inv] at this)

@[expose] noncomputable def lineAction :
    Subgroup.normalizer (rootGroup D a : Set G) →* Equiv.Perm (rootLines D a) where
  toFun := hL.linePerm ha
  map_one' := by
    ext L : 2
    change L.1.map (MulAut.conj (1 : G)).toMonoidHom = L.1
    convert Subgroup.map_id L.1
    ext x
    simp
  map_mul' g g' := by
    ext L : 2
    change L.1.map (MulAut.conj ((g : G) * g')).toMonoidHom =
      (L.1.map (MulAut.conj (g' : G)).toMonoidHom).map (MulAut.conj (g : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group

theorem lineAction_apply (g : Subgroup.normalizer (rootGroup D a : Set G))
    (L : rootLines D a) :
    ((hL.lineAction ha g) L : Subgroup G) = L.1.map (MulAut.conj (g : G)).toMonoidHom := rfl

theorem map_conj_eq_of_commute {x : G} (hx : x ∈ D) (hax : Commute a x) {L : Subgroup G}
    (hL' : L ∈ rootLines D a) : L.map (MulAut.conj x).toMonoidHom = L := by
  obtain ⟨b, hb, hab, habD, hbT, rfl⟩ := hL'
  have hD := hL.hyp.root
  have hx2 := hD.mul_self_eq_one hx
  by_cases hxL : x ∈ rootGroup D a ⊔ rootGroup D b
  · exact map_conj_eq_of_mul_self_eq_one hx2 fun u hu =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxL hu) (Subgroup.inv_mem _ hxL)
  have hxa : a * x ∈ D := by
    rcases hL.mem_rootSet_or_collinear ha hx hax.symm with h' | ⟨-, h'⟩
    · exact absurd (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h')) hxL
    · exact h'
  have h4 : orderOf (x * b) = 4 := orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha
    hb hab habD hbT (hL.lineTI ha hb hab habD hbT) hx hax hxL
  have hN := normalizesLine_of_special hD hL.special hL.commLambda hb ha hab.symm
    (by rw [← hab.eq]; exact habD) hx hax hxa (by rwa [orderOf_mul_comm_eq]) (mem_rootSet_self hx)
  refine map_conj_eq_of_mul_self_eq_one hx2 fun u hu => ?_
  rw [sup_comm] at hu ⊢
  exact hN u hu

theorem map_conj_eq_of_mem_closure {g : G} (hg : g ∈ Subgroup.closure {x | x ∈ D ∧ Commute a x})
    {L : Subgroup G} (hL' : L ∈ rootLines D a) : L.map (MulAut.conj g).toMonoidHom = L := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hL.map_conj_eq_of_commute ha hx.1 hx.2 hL'
  | one =>
    convert Subgroup.map_id L
    ext x
    simp
  | mul x y _ _ ihx ihy =>
    rw [show (MulAut.conj (x * y)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom by
        ext z; simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          mul_inv_rev]; group, ← Subgroup.map_map, ihy, ihx]
  | inv x _ ih =>
    conv_lhs => rw [← ih]
    exact map_conj_inv_map_conj_eq x L


theorem exists_conj_mem_rootSet {d b p p' : G} (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) (hp : p ∈ rootGroup D a ⊔ rootGroup D d)
    (hpa : p ∉ rootGroup D a) (hp' : p' ∈ rootGroup D a ⊔ rootGroup D d)
    (hp'a : p' ∉ rootGroup D a) :
    ∃ m : G, (m = 1 ∨ m ∈ rootSet D b) ∧ m * p' * m⁻¹ ∈ rootSet D p := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hp1 : p ≠ 1 := fun h' => hpa (h' ▸ (rootGroup D a).one_mem)
  have hpD := mem_of_mem_sup_rootGroup hL.hyp hL.closure hL.special ha hd had hadD hdT hp hp1
  have hpT : p ∉ rootSet D a := fun h' => hpa (rootSet_subset_rootGroup D a h')
  have hap : Commute a p := commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) hp
  have hsup := sup_rootGroup_eq_of_mem hL.hyp hL.closure hL.special ha hd had hadD hdT
    (left_mem_line ha) hp (hD.ne_one ha) hp1 hpT
  rw [rootGroup_eq_of_mem (mem_rootSet_self ha)] at hsup
  rw [← hsup] at hp' hbL
  obtain ⟨α, hα, π, hπ, rfl⟩ := exists_mul_eq_of_mem_line hpD hap hp'
  have hπ1 : π ≠ 1 := fun h' => hp'a (by rw [h', mul_one]; exact hα)
  have hπT : π ∈ rootSet D p := mem_rootSet_of_mem_rootGroup_of_ne_one hD hL.closure hpD hπ hπ1
  have hαπ : Commute α π := commute_of_mem_rootGroup_of_commute' hpD hα hπ hap
  rcases (mem_rootGroup_iff_of_rootClosure hD hL.closure ha).1 hα with rfl | hαT
  · exact ⟨1, Or.inl rfl, by rw [one_mul, one_mul, inv_one, mul_one]; exact hπT⟩
  have hπD := hπT.1
  have haπ : Commute a π := ((hπT.2 a ha).2 hap.symm).symm
  have hπL : π ∈ rootGroup D a ⊔ rootGroup D p := Subgroup.mem_sup_right hπ
  have haπ1 : a * π ≠ 1 := fun h' => by
    have hπa : π = a := by rw [eq_inv_of_mul_eq_one_right h', hD.inv_eq ha]
    exact hpT (mem_rootSet_comm hpD (hπa ▸ hπT))
  have hapD : a * p ∈ D := by
    rcases hL.mem_rootSet_or_collinear ha hpD hap.symm with h' | ⟨-, h'⟩
    · exact absurd h' hpT
    · exact h'
  have haπD : a * π ∈ D := mem_of_mem_sup_rootGroup hL.hyp hL.closure hL.special ha hpD hap hapD
    hpT (Subgroup.mul_mem _ (left_mem_line ha) hπL) haπ1
  have hπnT : π ∉ rootSet D a := fun h' => hpT (by
    rw [← (rootSet_eq_of_mem hπT).symm.trans (rootSet_eq_of_mem h')]
    exact mem_rootSet_self hpD)
  have hbLπ : b ∉ rootGroup D a ⊔ rootGroup D π := by rwa [rootGroup_eq_of_mem hπT]
  have h4 := orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha hπD haπ haπD hπnT
    (hL.lineTI ha hπD haπ haπD hπnT) hb hab hbLπ
  obtain ⟨b₁, hb₁, hb₁π⟩ := exists_mem_rootSet_conj_eq_mul hL.hyp hL.closure hL.special
    hL.commLambda ha hπD haπ haπD hb hab habD (by rwa [orderOf_mul_comm_eq]) hαT
  refine ⟨b₁⁻¹, Or.inr (by rw [hD.inv_eq hb₁.1]; exact hb₁), ?_⟩
  have e : b₁⁻¹ * (α * π) * b₁⁻¹⁻¹ = π := by rw [hαπ.eq, ← hb₁π]; group
  rw [e]
  exact hπT

@[expose] noncomputable def lineRoot (T : Subgroup G) : Subgroup (Equiv.Perm (rootLines D a)) :=
  Subgroup.closure {σ | ∃ g : Subgroup.normalizer (rootGroup D a : Set G),
    (g : G) ∈ lineCoreGen D a T ∧ hL.lineAction ha g = σ}

theorem lineAction_eq_one {g : Subgroup.normalizer (rootGroup D a : Set G)}
    (hg : (g : G) ∈ Subgroup.closure {x | x ∈ D ∧ Commute a x}) : hL.lineAction ha g = 1 := by
  ext L : 2
  exact hL.map_conj_eq_of_mem_closure ha hg L.2

theorem lineRoot_apply_self {T : Subgroup G} (hT : T ∈ rootLines D a)
    {σ : Equiv.Perm (rootLines D a)} (hσ : σ ∈ hL.lineRoot ha T) : σ ⟨T, hT⟩ = ⟨T, hT⟩ := by
  have hle : hL.lineRoot ha T ≤
      MulAction.stabilizer (Equiv.Perm (rootLines D a)) (⟨T, hT⟩ : rootLines D a) := by
    rw [lineRoot, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact Subtype.ext (map_conj_eq_of_forall_commute hg.2)
  exact (MulAction.mem_stabilizer_iff.1 (hle hσ))

omit hL ha in
theorem mem_normalizer_of_forall_commute {H : Subgroup G} {g : G} (hg : ∀ t ∈ H, Commute g t) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    rw [(hg t ht).eq, mul_inv_cancel_right]
    exact ht
  · intro ht
    have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [e, mul_assoc, (hg _ ht).symm.eq, inv_mul_cancel_left]
    exact ht

theorem exists_mem_lineRoot_apply_eq {T : Subgroup G} (hT : T ∈ rootLines D a)
    {L₁ L₂ : rootLines D a} (h₁ : L₁.1 ≠ T) (h₂ : L₂.1 ≠ T) :
    ∃ σ ∈ hL.lineRoot ha T, σ L₁ = L₂ := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hT
  obtain ⟨b, hb, hab, habD, hbT, hLb⟩ := L₁.2
  obtain ⟨c, hcD, hac, hacD, hcT, hLc⟩ := L₂.2
  have hbL : b ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    h₁ (hLb.trans (hL.sup_rootGroup_eq_of_mem_sup ha hb hd hab hbT had hadD hdT h'))
  have hcL : c ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    h₂ (hLc.trans (hL.sup_rootGroup_eq_of_mem_sup ha hcD hd hac hcT had hadD hdT h'))
  have hTI := hL.lineTI ha hd had hadD hdT
  obtain ⟨y, hy, hdy, hdyD, hay⟩ := exists_special_of_not_mem_line hL.hyp hL.closure hL.special
    hL.lineCentralizerEq ha hd had hadD hdT hTI hb hab habD hbT hbL
  obtain ⟨b₁, hb₁, k, hk, hkT, hkL⟩ := exists_mem_closure_conj_line_eq hL.hyp hL.closure
    hL.special hL.commLambda hL.lineCentralizerEq ha hd had hadD hdT hTI hy hdy hdyD hay hb hab
    habD hbL hcD hac hacD hcL
  have hdb : orderOf (d * b) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha hd had hadD hdT hTI hb
      hab hbL
  have hpL : b₁ * d * b₁⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
    have hN := normalizesLine_of_special hD hL.special hL.commLambda hd ha had.symm
      (by rw [← had.eq]; exact hadD) hb hab habD hdb hb₁
    have := hN d (left_mem_line hd)
    rwa [sup_comm] at this
  have hpa : b₁ * d * b₁⁻¹ ∉ rootGroup D a := fun h' => by
    have h1 := (Commute.conj_iff b₁⁻¹).2 (commute_of_mem_rootGroup_of_commute h' hb hab)
    have hbb₁ : Commute b₁ b := commute_of_mem_rootSet hb hb₁ (mem_rootSet_self hb)
    rw [show b₁⁻¹ * (b₁ * d * b₁⁻¹) * b₁⁻¹⁻¹ = d by group, inv_inv,
      hbb₁.inv_left.eq, inv_mul_cancel_right] at h1
    exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hb)
      hdb h1
  have hkN : k ∈ Subgroup.normalizer (rootGroup D a : Set G) :=
    mem_normalizer_of_forall_commute fun t ht => hkT t (Subgroup.mem_sup_left ht)
  refine ⟨hL.lineAction ha ⟨k, hkN⟩, Subgroup.subset_closure ⟨⟨k, hkN⟩,
    ⟨⟨_, conj_mem_of_isClass hclass b₁ hd, hpL, hpa, hk⟩, hkT⟩, rfl⟩, Subtype.ext ?_⟩
  rw [lineAction_apply, hLb, hkL, hLc]

omit hL in
theorem rootGroup_le_closure_commute {d p : G} (hd : d ∈ D) (had : Commute a d)
    (hp : p ∈ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D p ≤ Subgroup.closure {x | x ∈ D ∧ Commute a x} := by
  have hap : Commute a p := commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) hp
  rw [rootGroup]
  exact Subgroup.closure_mono fun x hx => ⟨hx.1, ((hx.2 a ha).2 hap.symm).symm⟩

theorem lineAction_commute {T : Subgroup G} (hT : T ∈ rootLines D a)
    {g g' : Subgroup.normalizer (rootGroup D a : Set G)} (hg : (g : G) ∈ lineCoreGen D a T)
    (hg' : (g' : G) ∈ lineCoreGen D a T) :
    Commute (hL.lineAction ha g) (hL.lineAction ha g') := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  obtain ⟨⟨p, hpD, hpT, hpa, hgp⟩, -⟩ := hg
  obtain ⟨⟨p', hp'D, hp'T, hp'a, hgp'⟩, -⟩ := hg'
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hT
  by_cases hex : ∃ b ∈ D, Commute a b ∧ a * b ∈ D ∧ b ∉ rootGroup D a ⊔ rootGroup D d
  · obtain ⟨b, hb, hab, habD, hbL⟩ := hex
    obtain ⟨m, hm, hmp⟩ := hL.exists_conj_mem_rootSet ha hd had hadD hdT hb hab habD hbL hpT hpa
      hp'T hp'a
    have hmC : m ∈ Subgroup.closure {x | x ∈ D ∧ Commute a x} := by
      rcases hm with rfl | hm
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨hm.1, ((hm.2 a ha).2 hab.symm).symm⟩
    have hmN := closure_commute_le_normalizer D a hmC
    have hψm := hL.lineAction_eq_one ha (g := ⟨m, hmN⟩) hmC
    have hψ'' : hL.lineAction ha (⟨m, hmN⟩ * g' * ⟨m, hmN⟩⁻¹) = hL.lineAction ha g' := by
      rw [map_mul, map_mul, map_inv, hψm, one_mul, inv_one, mul_one]
    have hg''p : ((⟨m, hmN⟩ * g' * ⟨m, hmN⟩⁻¹ : Subgroup.normalizer (rootGroup D a : Set G)) : G)
        ∈ Subgroup.closure {x | x ∈ D ∧ Commute p x} := by
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hgp'
      rw [MonoidHom.map_closure] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine Subgroup.closure_mono ?_ h1
      rintro _ ⟨x, ⟨hxD, hp'x⟩, rfl⟩
      have hx' := conj_mem_of_isClass hclass m hxD
      exact ⟨hx', (hmp.2 _ hx').1 ((Commute.conj_iff m).2 hp'x)⟩
    have hcomm := nCoreCommutatorInRoot_of_hyp hL.hyp hL.closure p hpD g
      (hL.closure_commute_le_nCore hpD hgp) _ (hL.closure_commute_le_nCore hpD hg''p)
    have h1 := hL.lineAction_eq_one ha (g := g * (⟨m, hmN⟩ * g' * ⟨m, hmN⟩⁻¹) * g⁻¹ *
      (⟨m, hmN⟩ * g' * ⟨m, hmN⟩⁻¹)⁻¹) (rootGroup_le_closure_commute ha hd had hpT (by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcomm))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψ'', mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · push Not at hex
    have hsub : Subsingleton (rootLines D a) := by
      refine ⟨fun L L' => Subtype.ext ?_⟩
      have key : ∀ L : rootLines D a, L.1 = rootGroup D a ⊔ rootGroup D d := fun L => by
        obtain ⟨b, hb, hab, habD, hbT, hLb⟩ := L.2
        rw [hLb]
        exact hL.sup_rootGroup_eq_of_mem_sup ha hb hd hab hbT had hadD hdT (hex b hb hab habD)
      rw [key L, key L']
    exact Equiv.ext fun _ => Subsingleton.elim _ _

theorem lineAction_mul_self {T : Subgroup G} (hT : T ∈ rootLines D a)
    {g : Subgroup.normalizer (rootGroup D a : Set G)} (hg : (g : G) ∈ lineCoreGen D a T) :
    hL.lineAction ha g * hL.lineAction ha g = 1 := by
  obtain ⟨⟨p, hpD, hpT, -, hgp⟩, -⟩ := hg
  obtain ⟨d, hd, had, -, -, rfl⟩ := hT
  rw [← map_mul]
  exact hL.lineAction_eq_one ha (rootGroup_le_closure_commute ha hd had hpT
    (mul_self_mem_rootGroup_of_mem_nCore hL.hyp hL.closure hpD
      (hL.closure_commute_le_nCore hpD hgp)))

theorem lineRoot_commute {T : Subgroup G} (hT : T ∈ rootLines D a)
    {σ τ : Equiv.Perm (rootLines D a)} (hσ : σ ∈ hL.lineRoot ha T) (hτ : τ ∈ hL.lineRoot ha T) :
    Commute σ τ := by
  refine commute_of_mem_closure (fun s hs s' hs' => ?_) hσ hτ
  obtain ⟨g, hg, rfl⟩ := hs
  obtain ⟨g', hg', rfl⟩ := hs'
  exact hL.lineAction_commute ha hT hg hg'

theorem lineRoot_mul_self {T : Subgroup G} (hT : T ∈ rootLines D a)
    {σ : Equiv.Perm (rootLines D a)} (hσ : σ ∈ hL.lineRoot ha T) : σ * σ = 1 := by
  refine mul_self_eq_one_of_mem_closure (fun s hs s' hs' _ => ?_) (fun s hs => ?_) hσ
  · obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨g', hg', rfl⟩ := hs'
    exact hL.lineAction_commute ha hT hg hg'
  · obtain ⟨g, hg, rfl⟩ := hs
    exact hL.lineAction_mul_self ha hT hg

theorem lineRoot_eq_one {T : Subgroup G} (hT : T ∈ rootLines D a)
    {σ : Equiv.Perm (rootLines D a)} (hσ : σ ∈ hL.lineRoot ha T) {L : rootLines D a}
    (hLT : L.1 ≠ T) (hσL : σ L = L) : σ = 1 := by
  refine Equiv.ext fun L' => ?_
  rw [Equiv.Perm.one_apply]
  by_cases hL'T : L'.1 = T
  · have e : L' = ⟨T, hT⟩ := Subtype.ext hL'T
    rw [e]
    exact hL.lineRoot_apply_self ha hT hσ
  · obtain ⟨τ, hτ, hτL⟩ := hL.exists_mem_lineRoot_apply_eq ha hT hLT hL'T
    rw [← hτL, ← Equiv.Perm.mul_apply, (hL.lineRoot_commute ha hT hσ hτ).eq,
      Equiv.Perm.mul_apply, hσL]

theorem exists_ncard_rootLines_eq {T L : Subgroup G} (hT : T ∈ rootLines D a)
    (hL' : L ∈ rootLines D a) (hLT : L ≠ T) :
    ∃ m : ℕ, (rootLines D a).ncard = 2 ^ m + 1 ∧ Nat.card (hL.lineRoot ha T) = 2 ^ m := by
  have := hL.hyp.finite
  set L₀ : rootLines D a := ⟨L, hL'⟩
  have hne : ∀ σ ∈ hL.lineRoot ha T, (σ L₀).1 ≠ T := fun σ hσ h' => by
    have h1 : σ L₀ = σ ⟨T, hT⟩ := by rw [hL.lineRoot_apply_self ha hT hσ]; exact Subtype.ext h'
    exact hLT (congrArg Subtype.val (σ.injective h1))
  let f : hL.lineRoot ha T → ↥(rootLines D a \ {T}) := fun σ =>
    ⟨(σ.1 L₀).1, (σ.1 L₀).2, hne σ.1 σ.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun σ τ hστ => ?_, fun L' => ?_⟩
    · have h1 : σ.1 L₀ = τ.1 L₀ := Subtype.ext (by simpa [f] using congrArg Subtype.val hστ)
      have h2 : (τ.1⁻¹ * σ.1) L₀ = L₀ := by
        rw [Equiv.Perm.mul_apply, h1, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
      have h3 := hL.lineRoot_eq_one ha hT (Subgroup.mul_mem _ (Subgroup.inv_mem _ τ.2) σ.2) hLT h2
      exact Subtype.ext (inv_mul_eq_one.1 h3).symm
    · obtain ⟨σ, hσ, hσL⟩ := hL.exists_mem_lineRoot_apply_eq ha hT (L₁ := L₀)
        (L₂ := ⟨L'.1, L'.2.1⟩) hLT L'.2.2
      exact ⟨⟨σ, hσ⟩, Subtype.ext (by simp only [f]; exact congrArg Subtype.val hσL)⟩
  have hcard : Nat.card (hL.lineRoot ha T) = (rootLines D a).ncard - 1 := by
    rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem hT]
  have hp : IsPGroup 2 (hL.lineRoot ha T) := fun σ => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hL.lineRoot_mul_self ha hT σ.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hp
  have hpos : 0 < (rootLines D a).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨T, hT⟩
  exact ⟨m, by omega, hm⟩

end LineSetting

end CFSG.Timmesfeld.Bridge
