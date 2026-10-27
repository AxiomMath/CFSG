module

public import CFSG.Quasithin.Background.GoldschmidtShultI85

public section

namespace CFSG.Quasithin.Loc442Q

open CFSG.Open CFSG.Quasithin.Shult MulAction


theorem centralizer_subgroupOf_normal {G : Type*} [Group G] {X V : Subgroup G}
    (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ((Subgroup.centralizer (V : Set G)).subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
  intro v hv
  have hv' : (g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹ ∈ V := hVn _ (X.inv_mem g.2) v hv
  have h := hn _ hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc v * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹)) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * (n : G) * (g : G)⁻¹ * v := by group

theorem mk_eq_one_iff_mem {K : Type*} [Group K] {X : Subgroup K} (l : K) :
    ((l : K ⧸ X) = ((1 : K) : K ⧸ X)) ↔ l ∈ X := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem shult_finish {G : Type} [Group G] [Finite G] {K X V : Subgroup G} (hXK : X ≤ K)
    (hVX : V ≤ X) (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hV1 : V ≠ ⊥)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hfix : ∀ v ∈ V, v ≠ 1 → ∀ g ∈ K, g⁻¹ * v * g ∈ X → g ∈ X)
    [((Subgroup.centralizer (V : Set G)).subgroupOf X).Normal]
    (hns : ¬ Group.IsSolvable (↥X ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf X)) :
    K ≤ X := by
  by_contra hne
  have hVK : V ≤ K := hVX.trans hXK
  have hX' : X.subgroupOf K ≠ ⊤ := by
    intro h
    apply hne
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ X.subgroupOf K := by rw [h]; trivial
    exact this
  have hV1' : V.subgroupOf K ≠ ⊥ := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    intro h
    have hmem : (⟨v, hVK hv⟩ : ↥K) ∈ V.subgroupOf K := hv
    rw [h, Subgroup.mem_bot] at hmem
    have h2 : v = 1 := congrArg (fun w : ↥K => (w : G)) hmem
    exact hv1 (Subtype.ext h2)
  have hVX' : V.subgroupOf K ≤ X.subgroupOf K := fun v hv => hVX hv
  have hVn' : ∀ x ∈ X.subgroupOf K, ∀ v ∈ V.subgroupOf K, x * v * x⁻¹ ∈ V.subgroupOf K :=
    fun x hx v hv => hVn x hx v hv
  have hVnn : ((V.subgroupOf K).subgroupOf (X.subgroupOf K)).Normal :=
    ⟨fun n hn g => hVn _ g.2 _ hn⟩
  have hVel : IsElemAbelian 2 (V.subgroupOf K) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hVab a.1.1 a.2 b.1.1 b.2))⟩⟩,
      fun a ha => Subtype.ext (hV2 a ha)⟩
  have hfix' : ShultFixedPoint (X.subgroupOf K) (V.subgroupOf K) := by
    intro v hv hv1
    refine ⟨((1 : ↥K) : ↥K ⧸ X.subgroupOf K), ?_, ?_⟩
    · show ((v * 1 : ↥K) : ↥K ⧸ X.subgroupOf K) = ((1 : ↥K) : ↥K ⧸ X.subgroupOf K)
      rw [mul_one]
      exact (mk_eq_one_iff_mem _).2 (hVX' hv)
    · intro c hc
      induction c using QuotientGroup.induction_on with
      | H g =>
        have h' : ((v * g : ↥K) : ↥K ⧸ X.subgroupOf K) = (g : ↥K ⧸ X.subgroupOf K) := hc
        rw [QuotientGroup.eq] at h'
        have hg : (g : G)⁻¹ * (v : G) * (g : G) ∈ X := by
          have := X.inv_mem (Subgroup.mem_subgroupOf.1 h')
          simpa [mul_assoc] using this
        have hgX := hfix v hv (fun h => hv1 (Subtype.ext h)) g g.2 hg
        exact ((mk_eq_one_iff_mem (X := X.subgroupOf K) g).2 hgX).trans rfl
  have hyp : ShultI85Hyp (X.subgroupOf K) (V.subgroupOf K) :=
    ⟨hX', hV1', hVX', hVnn, hVel, hfix'⟩
  have : ((Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K)).subgroupOf
      (X.subgroupOf K)).Normal := centralizer_subgroupOf_normal hVn'
  have hsolv := shultI85Part2 ↥K (X.subgroupOf K) (V.subgroupOf K) hyp
  let e : ↥(X.subgroupOf K) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
  have hle : (Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K)).subgroupOf
      (X.subgroupOf K) ≤ ((Subgroup.centralizer (V : Set G)).subgroupOf X).comap
        e.toMonoidHom := by
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro v hv
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn) ⟨v, hVK hv⟩ hv
    exact congrArg Subtype.val this
  have hsurj : Function.Surjective (QuotientGroup.map
      ((Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K)).subgroupOf
        (X.subgroupOf K))
      ((Subgroup.centralizer (V : Set G)).subgroupOf X) e.toMonoidHom hle) :=
    QuotientGroup.map_surjective_of_surjective _ _ e.toMonoidHom
      (QuotientGroup.mk_surjective.comp e.surjective) hle
  exact hns (Group.isSolvable_of_surjective hsurj)

end CFSG.Quasithin.Loc442Q
