module

public import CFSG.Quasithin.Background.C31SporJA

public section

namespace CFSG.Quasithin.C31SporJ

open CFSG.Open CFSG.Quasithin.AmalTransport

section Map

variable {G E : Type} [Group G] [Group E]

theorem centerOf_map_of_injective (f : G →* E) (hf : Function.Injective f) (X : Subgroup G) :
    centerOf (X.map f) = (centerOf X).map f := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hyc⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr fun x' hx' => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hyc (f x') ⟨x', hx', rfl⟩
  · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxc x' hx']

theorem omegaOneOf_map_of_injective (f : G →* E) (hf : Function.Injective f) (X : Subgroup G) :
    omegaOneOf (X.map f) = (omegaOneOf X).map f := by
  unfold omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy2⟩
    refine ⟨x, ⟨hx, hf ?_⟩, rfl⟩
    rw [map_pow, hy2, map_one]
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, hx2, map_one]⟩

end Map

structure ProdFunctor (F : ∀ {G : Type} [Group G], Subgroup G → Subgroup G) : Prop where
  le_self : ∀ {G : Type} [Group G] (X : Subgroup G), F X ≤ X
  map_inj : ∀ {G E : Type} [Group G] [Group E] (f : G →* E), Function.Injective f →
    ∀ X : Subgroup G, F (X.map f) = (F X).map f
  sup_eq : ∀ {G : Type} [Group G] [Finite G] {X Y : Subgroup G},
    (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) → X ⊓ Y = ⊥ → F (X ⊔ Y) = F X ⊔ F Y
  ne_bot : ∀ {G : Type} [Group G] [Finite G] {R : Subgroup G}, IsPGroup 2 ↥R → R ≠ ⊥ → F R ≠ ⊥

namespace ProdFunctor

variable {F : ∀ {G : Type} [Group G], Subgroup G → Subgroup G}

theorem characteristic (hF : ProdFunctor F) {G : Type} [Group G] (R : Subgroup G) :
    ((F R).subgroupOf R).Characteristic := by
  have hR : F R = (F (⊤ : Subgroup ↥R)).map R.subtype := by
    rw [← hF.map_inj _ R.subtype_injective, Subgroup.map_top, Subgroup.range_subtype]
  have hsub : (F R).subgroupOf R = F (⊤ : Subgroup ↥R) := by
    rw [hR]
    exact Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  rw [hsub, Subgroup.characteristic_iff_map_eq]
  intro α
  rw [← hF.map_inj α.toMonoidHom α.injective, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr α.surjective]

end ProdFunctor

theorem prodFunctor_thompsonJ : ProdFunctor (fun X => thompsonJ X) where
  le_self _ := iSup₂_le fun _ hA => hA.1
  map_inj f hf X := thompsonJ_map_of_injective f hf X
  sup_eq hc hXY := thompsonJ_sup_of_commute hc hXY
  ne_bot hR hne := thompsonJ_ne_bot hR hne

theorem prodFunctor_centerOf : ProdFunctor (fun X => centerOf X) where
  le_self X := inf_le_left
  map_inj f hf X := centerOf_map_of_injective f hf X
  sup_eq hc _ := centerOf_sup_of_commute hc
  ne_bot {G} _ _ {R} hR hne := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnt : Nontrivial ↥R := (Subgroup.bot_or_nontrivial R).resolve_left hne
    have hZ := hR.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥R)
    intro hb
    apply hz
    have hzc : ((z : ↥R) : G) ∈ centerOf R :=
      ⟨(z : ↥R).2, Subgroup.mem_centralizer_iff.mpr fun g hg => by
        have := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
        exact congrArg Subtype.val this⟩
    rw [hb, Subgroup.mem_bot] at hzc
    exact Subtype.ext (Subtype.ext hzc)

theorem omegaOneOf_ne_bot {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : IsPGroup 2 ↥X)
    (hne : X ≠ ⊥) : omegaOneOf X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq X (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h2
  intro hb
  have ht2 : (t : G) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
  have hmem : (t : G) ∈ omegaOneOf X := Subgroup.subset_closure ⟨t.2, ht2⟩
  rw [hb, Subgroup.mem_bot] at hmem
  have : t = 1 := Subtype.ext hmem
  rw [this, orderOf_one] at ht
  omega

theorem prodFunctor_omegaOneCenterJ : ProdFunctor (fun X => omegaOneCenterOf (thompsonJ X)) where
  le_self X := (Subgroup.closure_le _).mpr fun _ hx =>
    (prodFunctor_thompsonJ.le_self X) (inf_le_left (a := thompsonJ X) hx.1)
  map_inj f hf X := by
    unfold omegaOneCenterOf
    rw [thompsonJ_map_of_injective f hf, centerOf_map_of_injective f hf,
      omegaOneOf_map_of_injective f hf]
  sup_eq {G} _ _ {X Y} hc hXY := by
    unfold omegaOneCenterOf
    have hJX := prodFunctor_thompsonJ.le_self X
    have hJY := prodFunctor_thompsonJ.le_self Y
    have hcJ : ∀ x ∈ thompsonJ X, ∀ y ∈ thompsonJ Y, x * y = y * x :=
      fun x hx y hy => hc x (hJX hx) y (hJY hy)
    rw [thompsonJ_sup_of_commute hc hXY, centerOf_sup_of_commute hcJ]
    refine omegaOneOf_sup_of_commute (fun x hx y hy => hcJ x hx.1 y hy.1) ?_
    rw [eq_bot_iff]
    intro g hg
    rw [← hXY]
    exact ⟨hJX hg.1.1, hJY hg.2.1⟩
  ne_bot {G} _ _ {R} hR hne := by
    have hJ := thompsonJ_ne_bot hR hne
    have hJ2 : IsPGroup 2 ↥(thompsonJ R) := hR.to_le (prodFunctor_thompsonJ.le_self R)
    have hZ := prodFunctor_centerOf.ne_bot hJ2 hJ
    exact omegaOneOf_ne_bot (hJ2.to_le inf_le_left) hZ

end CFSG.Quasithin.C31SporJ
