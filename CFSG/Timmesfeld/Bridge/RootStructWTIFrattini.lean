module

public import CFSG.Timmesfeld.Bridge.RootStructWTIRadical
public import CFSG.Timmesfeld.Bridge.RootStructWTIModuleProps

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem map_conj_mul_eq_map_map (g g' : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * g')).toMonoidHom =
      (H.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext u
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

theorem conj_mem_of_map_conj_eq {H : Subgroup G} {g u : G}
    (hH : H.map (MulAut.conj g).toMonoidHom = H) (hu : u ∈ H) : g * u * g⁻¹ ∈ H := by
  rw [← hH]
  exact ⟨u, hu, rfl⟩

theorem mem_of_conj_mem_of_map_conj_eq {H : Subgroup G} {g u : G}
    (hH : H.map (MulAut.conj g).toMonoidHom = H) (hu : g * u * g⁻¹ ∈ H) : u ∈ H := by
  rw [← hH] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hvu
  exact hvu ▸ hv

theorem map_conj_eq_of_mem_self {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ fun u hu =>
    ⟨g⁻¹ * u * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hu) hg, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact H.mul_mem (H.mul_mem hg hu) (H.inv_mem hg)
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

namespace LineSetting

variable (hL : LineSetting G D) {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
  (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
include hL ha hd had hadD hdT

theorem exists_mem_nCore_conj_mem_rootSet {x x' : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxL : x ∉ rootGroup D a ⊔ rootGroup D d) (hx' : x' ∈ D)
    (hax' : Commute a x') (hax'D : a * x' ∈ D) (hx'L : x' ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ n ∈ nCore D d ⊓ Subgroup.centralizer {a},
      (∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute n t) ∧ n * x' * n⁻¹ ∈ rootSet D x := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hxT : x ∉ rootSet D a := fun h' =>
    hxL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  obtain ⟨k, ⟨hk, hka⟩, hkL⟩ := hL.exists_mem_nCore_conj_line_eq ha hd had hadD hdT hx' hax'
    hax'D hx'L hx hax haxD hxL
  have hka' : Commute k a := Subgroup.mem_centralizer_singleton_iff.1 hka
  have hkT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute k t := fun t ht =>
    hL.commute_of_mem_nCore_of_commute ha hd had hadD hdT hk hka' ht
  have hp' : k * x' * k⁻¹ ∈ rootGroup D a ⊔ rootGroup D x := by
    rw [← hkL]
    exact ⟨x', right_mem_line hx', rfl⟩
  have hp'a : k * x' * k⁻¹ ∉ rootGroup D a := fun h' => hx'L (Subgroup.mem_sup_left
    (mem_of_conj_mem_of_map_conj_eq (map_conj_eq_of_forall_commute fun s hs =>
      hkT s (Subgroup.mem_sup_left hs)) h'))
  have hdL : d ∉ rootGroup D a ⊔ rootGroup D x := fun h' => hxL (by
    rw [hL.sup_rootGroup_eq_of_mem_sup ha hd hx had hdT hax haxD hxT h']
    exact right_mem_line hx)
  obtain ⟨m, hm, hmx⟩ := hL.exists_conj_mem_rootSet ha hx hax haxD hxT hd had hadD hdL
    (right_mem_line hx) (fun h' => hxL (Subgroup.mem_sup_left h')) hp' hp'a
  have hmA : m ∈ rootGroup D d := (mem_rootGroup_iff_of_rootClosure hD hL.closure hd).2 hm
  have hmT : m ∈ rootGroup D a ⊔ rootGroup D d := Subgroup.mem_sup_right hmA
  refine ⟨m * k, ⟨Subgroup.mul_mem _ (hL.sup_rootGroup_le_nCore hd ha had.symm
    (Subgroup.mem_sup_left hmA)) hk, Subgroup.mem_centralizer_singleton_iff.2
    ((commute_of_mem_sup_rootGroup ha hd had hmT (left_mem_line ha)).mul_left hka').eq⟩,
    fun t ht => (commute_of_mem_sup_rootGroup ha hd had hmT ht).mul_left (hkT t ht), ?_⟩
  rw [show m * k * x' * (m * k)⁻¹ = m * (k * x' * k⁻¹) * m⁻¹ by group]
  exact hmx

theorem exists_mem_nCore_conj_mem_rootSet_of_mem {p x x₁ y₁ y₂ : G}
    (hp : p ∈ rootGroup D a ⊔ rootGroup D d) (hpa : p ∉ rootGroup D a) (hx : x ∈ D)
    (hax : Commute a x) (haxD : a * x ∈ D) (hxL : x ∉ rootGroup D a ⊔ rootGroup D d)
    (hx₁ : x₁ ∈ rootSet D x) (hy₁ : y₁ ∈ D) (hpy₁ : Commute p y₁) (hpy₁D : p * y₁ ∈ D)
    (hy₁L : y₁ ∉ rootGroup D a ⊔ rootGroup D d) (hy₂ : y₂ ∈ D) (hpy₂ : Commute p y₂)
    (hpy₂D : p * y₂ ∈ D) (hy₂L : y₂ ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ n ∈ nCore D a, (∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute n t) ∧
      n * x₁ * n⁻¹ ∈ rootSet D x ∧ n * y₁ * n⁻¹ ∈ rootSet D y₂ := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hxT : x ∉ rootSet D a := fun h' =>
    hxL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hp1 : p ≠ 1 := fun h' => hpa (h' ▸ (rootGroup D a).one_mem)
  have hpD : p ∈ D :=
    mem_of_mem_sup_rootGroup hL.hyp hL.closure hL.special ha hd had hadD hdT hp hp1
  have hpT : p ∉ rootSet D a := fun h' => hpa (rootSet_subset_rootGroup D a h')
  have hap : Commute a p := commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) hp
  have haT : a ∉ rootSet D p := fun h' => hpT (mem_rootSet_comm hpD h')
  have hpaD : p * a ∈ D := by
    rcases hL.mem_rootSet_or_collinear hpD ha hap with h' | ⟨-, h'⟩
    · exact absurd h' haT
    · exact h'
  have hTp : rootGroup D p ⊔ rootGroup D a = rootGroup D a ⊔ rootGroup D d :=
    sup_rootGroup_eq_of_mem hL.hyp hL.closure hL.special ha hd had hadD hdT hp (left_mem_line ha)
      hp1 (hD.ne_one ha) haT
  have hApT : rootGroup D p ≤ rootGroup D a ⊔ rootGroup D d :=
    rootGroup_le_sup_of_mem hL.hyp hL.closure hL.special ha hd had hadD hdT hp hp1
  have hTa : rootGroup D a ⊔ rootGroup D d ≤ nCore D a := hL.sup_rootGroup_le_nCore ha hd had
  obtain ⟨k, ⟨hk, hkp⟩, hkL⟩ := hL.exists_mem_nCore_conj_line_eq hpD ha hap.symm hpaD haT hy₁
    hpy₁ hpy₁D (by rwa [hTp]) hy₂ hpy₂ hpy₂D (by rwa [hTp])
  have hkT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute k t := fun t ht =>
    hL.commute_of_mem_nCore_of_commute hpD ha hap.symm hpaD haT hk
      (Subgroup.mem_centralizer_singleton_iff.1 hkp) (by rwa [hTp])
  have hkx : (rootGroup D a ⊔ rootGroup D x).map (MulAut.conj k).toMonoidHom =
      rootGroup D a ⊔ rootGroup D x :=
    hL.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hk)
      ⟨x, hx, hax, haxD, hxT, rfl⟩
  have hkx₁ : k * x₁ * k⁻¹ ∈ rootGroup D a ⊔ rootGroup D x := by
    rw [← hkx]
    exact ⟨x₁, Subgroup.mem_sup_right (rootSet_subset_rootGroup D x hx₁), rfl⟩
  have hkx₁a : k * x₁ * k⁻¹ ∉ rootGroup D a := fun h' => hxT (by
    have h1 := mem_rootSet_of_mem_rootGroup hclass ha hx₁.1 (mem_of_conj_mem_of_map_conj_eq
      (map_conj_eq_of_forall_commute fun s hs => hkT s (Subgroup.mem_sup_left hs)) h')
    rw [← rootSet_eq_of_mem h1]
    exact mem_rootSet_comm hx hx₁)
  have hpLx : p ∉ rootGroup D a ⊔ rootGroup D x := fun h' => hxL (by
    have h1 := hL.sup_rootGroup_eq_of_mem_sup ha hpD hx hap hpT hax haxD hxT h'
    rw [← hTp, sup_comm, h1]
    exact right_mem_line hx)
  obtain ⟨m₁, hm₁, hm₁x⟩ := hL.exists_conj_mem_rootSet ha hx hax haxD hxT hpD hap
    (by rw [hap.eq]; exact hpaD) hpLx (right_mem_line hx)
    (fun h' => hxL (Subgroup.mem_sup_left h')) hkx₁ hkx₁a
  have hm₁A : m₁ ∈ rootGroup D p := (mem_rootGroup_iff_of_rootClosure hD hL.closure hpD).2 hm₁
  have hm₁T : m₁ ∈ rootGroup D a ⊔ rootGroup D d := hApT hm₁A
  have hy₂p : y₂ ∉ rootGroup D p := fun h' => hy₂L (hApT h')
  have hy₂T : y₂ ∉ rootSet D p := fun h' => hy₂p (rootSet_subset_rootGroup D p h')
  have hm₁L : (rootGroup D p ⊔ rootGroup D y₂).map (MulAut.conj m₁).toMonoidHom =
      rootGroup D p ⊔ rootGroup D y₂ :=
    hL.map_conj_eq_of_mem_closure hpD (rootGroup_le_closure_commute hpD ha hap.symm
      (left_mem_line hpD) hm₁A) ⟨y₂, hy₂, hpy₂, hpy₂D, hy₂T, rfl⟩
  have hq : m₁ * k * y₁ * (m₁ * k)⁻¹ ∈ rootGroup D p ⊔ rootGroup D y₂ := by
    have hky : k * y₁ * k⁻¹ ∈ rootGroup D p ⊔ rootGroup D y₂ := by
      rw [← hkL]
      exact ⟨y₁, right_mem_line hy₁, rfl⟩
    rw [show m₁ * k * y₁ * (m₁ * k)⁻¹ = m₁ * (k * y₁ * k⁻¹) * m₁⁻¹ by group, ← hm₁L]
    exact ⟨_, hky, rfl⟩
  have hqp : m₁ * k * y₁ * (m₁ * k)⁻¹ ∉ rootGroup D p := fun h' => hy₁L (hApT
    (mem_of_conj_mem_of_map_conj_eq (map_conj_eq_of_forall_commute fun s hs =>
      (commute_of_mem_sup_rootGroup ha hd had hm₁T (hApT hs)).mul_left (hkT s (hApT hs))) h'))
  have haL : a ∉ rootGroup D p ⊔ rootGroup D y₂ := fun h' => hy₂L (by
    rw [← hTp, hL.sup_rootGroup_eq_of_mem_sup hpD ha hy₂ hap.symm haT hpy₂ hpy₂D hy₂T h']
    exact right_mem_line hy₂)
  obtain ⟨m₃, hm₃, hm₃y⟩ := hL.exists_conj_mem_rootSet hpD hy₂ hpy₂ hpy₂D hy₂T ha hap.symm hpaD
    haL (right_mem_line hy₂) hy₂p hq hqp
  have hm₃A : m₃ ∈ rootGroup D a := (mem_rootGroup_iff_of_rootClosure hD hL.closure ha).2 hm₃
  have hm₃T : m₃ ∈ rootGroup D a ⊔ rootGroup D d := Subgroup.mem_sup_left hm₃A
  refine ⟨m₃ * m₁ * k, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTa hm₃T) (hTa hm₁T)) hk,
    fun t ht => ((commute_of_mem_sup_rootGroup ha hd had hm₃T ht).mul_left
      (commute_of_mem_sup_rootGroup ha hd had hm₁T ht)).mul_left (hkT t ht), ?_, ?_⟩
  · have hm₃w : Commute m₃ (m₁ * (k * x₁ * k⁻¹) * m₁⁻¹) :=
      commute_of_mem_rootGroup_of_commute hm₃A hm₁x.1 ((hm₁x.2 a ha).2 hax.symm).symm
    rw [show m₃ * m₁ * k * x₁ * (m₃ * m₁ * k)⁻¹ =
      m₃ * (m₁ * (k * x₁ * k⁻¹) * m₁⁻¹) * m₃⁻¹ by group, hm₃w.eq, mul_inv_cancel_right]
    exact hm₁x
  · rw [show m₃ * m₁ * k * y₁ * (m₃ * m₁ * k)⁻¹ =
      m₃ * (m₁ * k * y₁ * (m₁ * k)⁻¹) * m₃⁻¹ by group]
    exact hm₃y

end LineSetting

theorem rootLinesFrattiniStep :
    ∀ (G : Type) [Group G] (D : Set G), LineSetting G D →
      ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      ∀ x ∈ D, Commute a x → a * x ∈ D → x ∉ rootGroup D a ⊔ rootGroup D d →
      ∀ y ∈ D, Commute d y → d * y ∈ D → y ∉ rootGroup D a ⊔ rootGroup D d →
      ∀ h : G, (rootGroup D a).map (MulAut.conj h).toMonoidHom = rootGroup D a →
        (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj h).toMonoidHom =
          rootGroup D a ⊔ rootGroup D d →
        ∃ n ∈ lineN D a d, (rootGroup D x ⊔ rootGroup D y).map (MulAut.conj (n * h)).toMonoidHom =
          rootGroup D x ⊔ rootGroup D y := by
  intro G _ D hL a ha d hd had hadD hdT x hx hax haxD hxL y hy hdy hdyD hyL h hha hhT
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have hda : d ∉ rootGroup D a := fun h' => hdT (mem_rootSet_of_mem_rootGroup hclass ha hd h')
  have ha' : h * a * h⁻¹ ∈ rootSet D a :=
    mem_rootSet_of_mem_rootGroup hclass ha (conj_mem_of_isClass hclass h ha)
      (conj_mem_of_map_conj_eq hha (rootSet_subset_rootGroup D a (mem_rootSet_self ha)))
  have hx' : h * x * h⁻¹ ∈ D := conj_mem_of_isClass hclass h hx
  have hax' : Commute a (h * x * h⁻¹) := (ha'.2 _ hx').1 ((Commute.conj_iff h).2 hax)
  have hx'L : h * x * h⁻¹ ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hxL (mem_of_conj_mem_of_map_conj_eq hhT h')
  have hax'D : a * (h * x * h⁻¹) ∈ D := by
    rcases hL.mem_rootSet_or_collinear ha hx' hax'.symm with h' | ⟨-, h'⟩
    · exact absurd (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h')) hx'L
    · exact h'
  obtain ⟨n₁, hn₁, hn₁T, hn₁x⟩ := hL.exists_mem_nCore_conj_mem_rootSet ha hd had hadD hdT hx hax
    haxD hxL hx' hax' hax'D hx'L
  obtain ⟨p, hpdef⟩ : ∃ p, p = h * d * h⁻¹ := ⟨_, rfl⟩
  have hp : p ∈ rootGroup D a ⊔ rootGroup D d := by
    rw [hpdef]
    exact conj_mem_of_map_conj_eq hhT (right_mem_line hd)
  have hpa : p ∉ rootGroup D a := fun h' =>
    hda (mem_of_conj_mem_of_map_conj_eq hha (by rwa [← hpdef]))
  have hpD : p ∈ D := by
    rw [hpdef]
    exact conj_mem_of_isClass hclass h hd
  obtain ⟨ξ, hξ, hξd⟩ := hL.exists_conj_mem_rootSet ha hd had hadD hdT hx hax haxD hxL hp hpa
    (right_mem_line hd) hda
  have hξA : ξ ∈ rootGroup D x := (mem_rootGroup_iff_of_rootClosure hD hL.closure hx).2 hξ
  have hξT : (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj ξ).toMonoidHom =
      rootGroup D a ⊔ rootGroup D d := by
    rcases hξ with rfl | hξx
    · exact map_conj_eq_of_forall_commute fun t _ => Commute.one_left t
    · have hdx : orderOf (d * x) = 4 := by
        rw [orderOf_mul_comm_eq]
        exact orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha hd had hadD hdT
          (hL.lineTI ha hd had hadD hdT) hx hax hxL
      have hN := normalizesLine_of_special hD hL.special hL.commLambda hd ha had.symm hdaD hx hax
        haxD hdx hξx
      refine map_conj_eq_of_mul_self_eq_one (hD.mul_self_eq_one hξx.1) fun u hu => ?_
      rw [sup_comm] at hu ⊢
      exact hN u hu
  have hApT : rootGroup D p ≤ rootGroup D a ⊔ rootGroup D d :=
    rootGroup_le_sup_of_mem hL.hyp hL.closure hL.special ha hd had hadD hdT hp (hD.ne_one hpD)
  have hy₂ : ξ * y * ξ⁻¹ ∈ D := conj_mem_of_isClass hclass ξ hy
  have hpy₂ : Commute p (ξ * y * ξ⁻¹) := (hξd.2 _ hy₂).1 ((Commute.conj_iff ξ).2 hdy)
  have hy₂L : ξ * y * ξ⁻¹ ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hyL (mem_of_conj_mem_of_map_conj_eq hξT h')
  have hpy₂D : p * (ξ * y * ξ⁻¹) ∈ D := by
    rcases hL.mem_rootSet_or_collinear hpD hy₂ hpy₂.symm with h' | ⟨-, h'⟩
    · exact absurd (hApT (rootSet_subset_rootGroup D p h')) hy₂L
    · exact h'
  have hg₁d : n₁ * h * d * (n₁ * h)⁻¹ = p := by
    rw [show n₁ * h * d * (n₁ * h)⁻¹ = n₁ * (h * d * h⁻¹) * n₁⁻¹ by group, ← hpdef,
      (hn₁T p hp).eq, mul_inv_cancel_right]
  have hg₁T : (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj (n₁ * h)).toMonoidHom =
      rootGroup D a ⊔ rootGroup D d := by
    rw [map_conj_mul_eq_map_map, hhT, map_conj_eq_of_forall_commute hn₁T]
  have hy₁ : n₁ * h * y * (n₁ * h)⁻¹ ∈ D := conj_mem_of_isClass hclass _ hy
  have hpy₁ : Commute p (n₁ * h * y * (n₁ * h)⁻¹) := by
    rw [← hg₁d]
    exact (Commute.conj_iff _).2 hdy
  have hpy₁D : p * (n₁ * h * y * (n₁ * h)⁻¹) ∈ D := by
    rw [← hg₁d, show n₁ * h * d * (n₁ * h)⁻¹ * (n₁ * h * y * (n₁ * h)⁻¹) =
      n₁ * h * (d * y) * (n₁ * h)⁻¹ by group]
    exact conj_mem_of_isClass hclass _ hdyD
  have hy₁L : n₁ * h * y * (n₁ * h)⁻¹ ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hyL (mem_of_conj_mem_of_map_conj_eq hg₁T h')
  have hx₁ : n₁ * h * x * (n₁ * h)⁻¹ ∈ rootSet D x := by
    rw [show n₁ * h * x * (n₁ * h)⁻¹ = n₁ * (h * x * h⁻¹) * n₁⁻¹ by group]
    exact hn₁x
  obtain ⟨n₂, hn₂, hn₂T, hn₂x, hn₂y⟩ := hL.exists_mem_nCore_conj_mem_rootSet_of_mem ha hd had
    hadD hdT hp hpa hx hax haxD hxL hx₁ hy₁ hpy₁ hpy₁D hy₁L hy₂ hpy₂ hpy₂D hy₂L
  have hn : n₂ * n₁ ∈ lineN D a d := by
    unfold lineN
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hn₂,
      Subgroup.mem_centralizer_singleton_iff.2 (hn₂T d (right_mem_line hd)).eq⟩)
      (Subgroup.mem_sup_right hn₁)
  refine ⟨n₂ * n₁, hn, ?_⟩
  have hgx : n₂ * n₁ * h * x * (n₂ * n₁ * h)⁻¹ ∈ rootSet D x := by
    rw [show n₂ * n₁ * h * x * (n₂ * n₁ * h)⁻¹ = n₂ * (n₁ * h * x * (n₁ * h)⁻¹) * n₂⁻¹ by group]
    exact hn₂x
  have hgy : n₂ * n₁ * h * y * (n₂ * n₁ * h)⁻¹ ∈ rootSet D (ξ * y * ξ⁻¹) := by
    rw [show n₂ * n₁ * h * y * (n₂ * n₁ * h)⁻¹ = n₂ * (n₁ * h * y * (n₁ * h)⁻¹) * n₂⁻¹ by group]
    exact hn₂y
  have hξx : Commute ξ x := commute_of_mem_rootGroup_of_commute hξA hx (Commute.refl x)
  rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass, rootGroup_eq_of_mem hgx,
    rootGroup_eq_of_mem hgy]
  calc rootGroup D x ⊔ rootGroup D (ξ * y * ξ⁻¹)
      = rootGroup D (ξ * x * ξ⁻¹) ⊔ rootGroup D (ξ * y * ξ⁻¹) := by
        rw [hξx.eq, mul_inv_cancel_right]
    _ = (rootGroup D x ⊔ rootGroup D y).map (MulAut.conj ξ).toMonoidHom := by
        rw [Subgroup.map_sup, rootGroup_conj hclass, rootGroup_conj hclass]
    _ = rootGroup D x ⊔ rootGroup D y := map_conj_eq_of_mem_self (Subgroup.mem_sup_left hξA)

end CFSG.Timmesfeld.Bridge
