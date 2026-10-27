module

public import CFSG.RankThree.PartOne.FIS.PermInput
public import CFSG.RankThree.PartOne.FIS.CenterQuotient

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm

variable {n : ℕ}

theorem exists_localEquiv {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y} {d : X}
    (f : X →* Y) (hinj : ∀ a ∈ LocalGroup E d, ∀ b ∈ LocalGroup E d, f a = f b → a = b)
    (h1 : ∀ x ∈ LocalClass E d, f x ∈ LocalClass F (f d))
    (h2 : ∀ y ∈ LocalClass F (f d), ∃ x ∈ LocalClass E d, f x = y) :
    ∃ ι : ↥(LocalGroup E d) ≃* ↥(LocalGroup F (f d)), (∀ t, (ι t : Y) = f t) ∧
      ∀ t : ↥(LocalGroup E d), (t : X) ∈ LocalClass E d ↔ (ι t : Y) ∈ LocalClass F (f d) := by
  let g : ↥(LocalGroup E d) →* Y := f.comp (LocalGroup E d).subtype
  have hg : Function.Injective g := fun a b h => Subtype.ext (hinj a a.2 b b.2 h)
  have hle : (LocalGroup E d).map f ≤ LocalGroup F (f d) := by
    rw [LocalGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (h1 x hx)
  have hrange : g.range = LocalGroup F (f d) := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      exact hle ⟨t, t.2, rfl⟩
    · rw [LocalGroup, Subgroup.closure_le]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := h2 y hy
      exact ⟨⟨x, mem_localGroup hx⟩, rfl⟩
  let ι : ↥(LocalGroup E d) ≃* ↥(LocalGroup F (f d)) :=
    (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hrange)
  have hι : ∀ t, (ι t : Y) = f t := fun t => by
    show ((MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hg t) : ↥(LocalGroup F (f d))) :
      Y) = f t
    rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
    rfl
  refine ⟨ι, hι, fun t => ?_⟩
  rw [hι]
  constructor
  · exact h1 t
  · intro hy
    obtain ⟨x, hx, hxy⟩ := h2 _ hy
    have hxt := hinj x (mem_localGroup hx) t t.2 hxy
    rw [← hxt]
    exact hx

@[expose] def LocalIso.transport {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y} {d : X}
    {e : Y} (L : LocalIso E d n) (ι : ↥(LocalGroup E d) ≃* ↥(LocalGroup F e))
    (hι : ∀ t : ↥(LocalGroup E d), (t : X) ∈ LocalClass E d ↔ (ι t : Y) ∈ LocalClass F e) :
    LocalIso F e n where
  φ := ι.symm.trans L.φ
  isSwap_iff t := by
    have h := hι (ι.symm t)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm.trans (L.isSwap_iff _)

@[expose] def LocalIso.transportSymm {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}
    {d : X} {e : Y} (L : LocalIso F e n) (ι : ↥(LocalGroup E d) ≃* ↥(LocalGroup F e))
    (hι : ∀ t : ↥(LocalGroup E d), (t : X) ∈ LocalClass E d ↔ (ι t : Y) ∈ LocalClass F e) :
    LocalIso E d n where
  φ := ι.trans L.φ
  isSwap_iff t := (hι t).trans (L.isSwap_iff (ι t))

theorem exists_localEquiv_conj {X : Type} [Group X] {E : Set X} (hP : Pair X E) (d g : X) :
    ∃ ι : ↥(LocalGroup E d) ≃* ↥(LocalGroup E (g * d * g⁻¹)),
      ∀ t : ↥(LocalGroup E d), (t : X) ∈ LocalClass E d ↔
        (ι t : X) ∈ LocalClass E (g * d * g⁻¹) := by
  let f : X →* X :=
    { toFun := fun x => g * x * g⁻¹
      map_one' := by simp
      map_mul' := fun a b => by group }
  obtain ⟨ι, -, hι⟩ := exists_localEquiv (E := E) (F := E) (d := d) f
    (fun a _ b _ h => by simpa [f] using h)
    (fun x hx => (Pair.conj_mem_localClass_iff hP g).2 hx)
    (fun y hy => ⟨g⁻¹ * y * g,
      (Pair.conj_mem_localClass_iff hP g (e := d) (f := g⁻¹ * y * g)).1 (by
        rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
        exact hy), by simp [f, mul_assoc]⟩)
  exact ⟨ι, hι⟩

theorem image_star_eq_swaps (hI : PermInput n) {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    {d : X} (θ : ↥(LocalGroup E d) ≃* Perm (Fin n)) :
    θ '' {t : ↥(LocalGroup E d) | (t : X) ∈ LocalClass E d} = {σ | σ.IsSwap} := by
  refine hI.eq_swaps ?_ ?_ ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← map_mul]
      have : u * u = 1 := Subtype.ext (Pair.mul_self hP hu.1)
      rw [this, map_one]
    · intro h
      have : u = 1 := θ.injective (h.trans (map_one θ).symm)
      exact Pair.ne_one hP hu.1 (congrArg Subtype.val this)
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨u * v * u⁻¹, ?_, by simp⟩
    have := Pair.conj_mem_localClass_of_mem hP u.2 hv
    simpa using this
  · have h1 : Subgroup.closure ({t : ↥(LocalGroup E d) | (t : X) ∈ LocalClass E d}) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have h2 := MonoidHom.map_closure θ.toMonoidHom
      {t : ↥(LocalGroup E d) | (t : X) ∈ LocalClass E d}
    rw [h1, Subgroup.map_top_of_surjective _ θ.surjective] at h2
    exact h2.symm
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, Subgroup.coe_mul]
    have h := Pair.orderOf_mul_mem hP hu.1 hv.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega

@[expose] def localIso_of_iso (hI : PermInput n) {X : Type} [Group X] {E : Set X}
    (hP : Pair X E) {d : X} (θ : ↥(LocalGroup E d) ≃* Perm (Fin n)) : LocalIso E d n where
  φ := θ
  isSwap_iff t := by
    have himg := image_star_eq_swaps hI hP θ
    constructor
    · intro h
      have hmem : θ t ∈ θ '' {t : ↥(LocalGroup E d) | (t : X) ∈ LocalClass E d} := ⟨t, h, rfl⟩
      rw [himg] at hmem
      exact hmem
    · intro h
      have hmem : θ t ∈ θ '' {t : ↥(LocalGroup E d) | (t : X) ∈ LocalClass E d} := by
        rw [himg]
        exact h
      obtain ⟨u, hu, hut⟩ := hmem
      have hu' : u = t := θ.injective hut
      rw [← hu']
      exact hu

theorem star_map_center {G : Type} [Group G] {D : Set G} (hP : Pair G D)
    (hnc : ∀ e ∈ D, e ∉ Subgroup.center G) (π : G →* G ⧸ Subgroup.center G)
    (hπ : ∀ g, π g = (g : G ⧸ Subgroup.center G)) {d : G} (hd : d ∈ D) :
    (∀ u ∈ LocalClass D d, π u ∈ LocalClass (π '' D) (π d)) ∧
      ∀ y ∈ LocalClass (π '' D) (π d), ∃ u ∈ LocalClass D d, π u = y := by
  have hnoncomm : ∀ e ∈ D, ∃ f ∈ D, e * f ≠ f * e := by
    intro e he
    by_contra! hall
    exact hnc e he ((Pair.mem_center_iff hP).2 fun f hf => (hall f hf).symm)
  have hπeq : ∀ g h, π g = π h ↔ g⁻¹ * h ∈ Subgroup.center G := fun g h => by
    rw [hπ, hπ]
    exact QuotientGroup.eq
  refine ⟨fun u hu => ?_, ?_⟩
  · refine ⟨⟨u, hu.1, rfl⟩, fun h => hu.2.1 ?_, ?_⟩
    · have hz : u * d ∈ Subgroup.center G := by
        have := (hπeq u d).1 h
        rwa [Pair.inv_eq hP hu.1] at this
      exact Pair.eq_of_mul_mem_center hP hu.1 hd hz (hnoncomm u hu.1)
    · rw [← map_mul, ← map_mul, hu.2.2]
  · rintro y ⟨⟨u, hu, rfl⟩, hne, hcomm⟩
    refine ⟨u, ⟨hu, fun h => hne (by rw [h]), ?_⟩, rfl⟩
    rcases comm_or_eq_of_map hP π hu hd hcomm with h | h
    · exact h
    · exact absurd h hne

theorem localGroup_inj_center {G : Type} [Group G] {D : Set G} (h3 : 3 ≤ n) {d : G}
    (L : LocalIso D d n) (π : G →* G ⧸ Subgroup.center G)
    (hπ : ∀ g, π g = (g : G ⧸ Subgroup.center G)) :
    ∀ a ∈ LocalGroup D d, ∀ b ∈ LocalGroup D d, π a = π b → a = b := by
  intro a ha b hb hab
  have hz : a⁻¹ * b ∈ Subgroup.center G := by
    rw [hπ, hπ] at hab
    exact QuotientGroup.eq.1 hab
  have hzmem : a⁻¹ * b ∈ LocalGroup D d := mul_mem (inv_mem ha) hb
  have h1 : L.φ ⟨a⁻¹ * b, hzmem⟩ = 1 := by
    apply perm_eq_one_of_commute_swaps h3
    intro τ hτ
    have hu : ((L.φ.symm τ : ↥(LocalGroup D d)) : G) ∈ LocalClass D d := L.mem_of_swap hτ
    have hc : (a⁻¹ * b) * ((L.φ.symm τ : ↥(LocalGroup D d)) : G) =
        ((L.φ.symm τ : ↥(LocalGroup D d)) : G) * (a⁻¹ * b) :=
      (Subgroup.mem_center_iff.1 hz _).symm
    have hc' : (⟨a⁻¹ * b, hzmem⟩ : ↥(LocalGroup D d)) * L.φ.symm τ =
        L.φ.symm τ * ⟨a⁻¹ * b, hzmem⟩ := Subtype.ext hc
    have h' := congrArg L.φ hc'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  have h2 : (⟨a⁻¹ * b, hzmem⟩ : ↥(LocalGroup D d)) = 1 :=
    L.φ.injective (h1.trans (map_one _).symm)
  have h3' : a⁻¹ * b = 1 := congrArg Subtype.val h2
  rwa [inv_mul_eq_one] at h3'

end CFSG.RankThree.PartOne.FIS
