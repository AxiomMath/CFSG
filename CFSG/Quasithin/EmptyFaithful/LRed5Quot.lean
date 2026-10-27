module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace LRed5

section Quot

variable {G W : Type} [Group G] [CommGroup W]

theorem pCoreOf_range_eq_bot [Finite G] [Finite W] {X : Subgroup G} (ρ : ↥X →* MulAut W)
    (hker : ∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 X) : pCoreOf 2 ρ.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerp : IsPGroup 2 ρ.ker := by
    intro x
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X
      ⟨(x : ↥X), (hker x).1 x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  set P := pCoreOf 2 ρ.range with hP
  have hPp : IsPGroup 2 P := pCoreOf_isPGroup 2 _
  have hP' : IsPGroup 2 (P.comap ρ) := hPp.comap_of_ker_isPGroup ρ hkerp
  have hsub : ((P.comap ρ).map X.subtype).subgroupOf X = P.comap ρ :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hnorm : (((P.comap ρ).map X.subtype).subgroupOf X).Normal := by
    rw [hsub]
    constructor
    intro n hn g
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    have hg : ρ g ∈ Subgroup.normalizer (P : Set (MulAut W)) :=
      le_normalizer_pCoreOf 2 ρ.range ⟨g, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg (ρ n)).mp hn
  have hle : (P.comap ρ).map X.subtype ≤ pCoreOf 2 X :=
    le_pCoreOf 2 (Subgroup.map_subtype_le _) hnorm (hP'.map _)
  rw [eq_bot_iff]
  intro γ hγ
  have hγr : γ ∈ ρ.range := pCoreOf_le 2 _ hγ
  obtain ⟨x, rfl⟩ := hγr
  have hx : (x : G) ∈ pCoreOf 2 X := hle ⟨x, hγ, rfl⟩
  rw [Subgroup.mem_bot]
  exact (hker x).2 hx

theorem exists_mul_of_mem_sup_of_le_normalizer {Γ L T₀ : Subgroup G}
    (hn : (L.subgroupOf Γ).Normal) (hLΓ : L ≤ Γ) (hT₀Γ : T₀ ≤ Γ) {x : G} (hx : x ∈ L ⊔ T₀) :
    ∃ l ∈ L, ∃ t ∈ T₀, l * t = x := by
  have hxΓ : x ∈ Γ := sup_le hLΓ hT₀Γ hx
  have hsup : (L ⊔ T₀).subgroupOf Γ = L.subgroupOf Γ ⊔ T₀.subgroupOf Γ :=
    Subgroup.subgroupOf_sup hLΓ hT₀Γ
  have hx' : (⟨x, hxΓ⟩ : ↥Γ) ∈ L.subgroupOf Γ ⊔ T₀.subgroupOf Γ := by
    rw [← hsup]
    exact hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
  exact ⟨(y : G), hy, (z : G), hz, congrArg Subtype.val hyz⟩

theorem centralizer_eq_bot_of_two_quotient [Finite G] {Γ L T₀ : Subgroup G}
    (hLΓ : L ≤ Γ) (hn : (L.subgroupOf Γ).Normal)
    (hZ : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1) (hT₀Γ : T₀ ≤ Γ) (hT₀ : IsPGroup 2 T₀)
    (hΓ : Γ = L ⊔ T₀) (hO2 : pCoreOf 2 Γ = ⊥) :
    Γ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := Γ ⊓ Subgroup.centralizer (L : Set G) with hD
  set L' := L.subgroupOf Γ with hL'
  set q : ↥Γ →* ↥Γ ⧸ L' := QuotientGroup.mk' L' with hq
  have hT₀' : IsPGroup 2 (T₀.subgroupOf Γ) := hT₀.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀Γ).symm
  have hqs : Function.Surjective ((q.comp (T₀.subgroupOf Γ).subtype)) := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L' c
    obtain ⟨l, hl, t, ht, hlt⟩ := exists_mul_of_mem_sup_of_le_normalizer hn hLΓ hT₀Γ
      (show (g : G) ∈ L ⊔ T₀ by rw [← hΓ]; exact g.2)
    refine ⟨⟨⟨t, hT₀Γ ht⟩, ht⟩, ?_⟩
    have hg : g = ⟨l, hLΓ hl⟩ * ⟨t, hT₀Γ ht⟩ := Subtype.ext hlt.symm
    show q ⟨t, hT₀Γ ht⟩ = q g
    rw [hg, map_mul, show q ⟨l, hLΓ hl⟩ = 1 from (QuotientGroup.eq_one_iff _).2 hl, one_mul]
  have hQ2 : IsPGroup 2 (↥Γ ⧸ L') := hT₀'.of_surjective _ hqs
  have hinj : Function.Injective (q.comp (D.subgroupOf Γ).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, hd⟩ h
    have h1 : (d : ↥Γ) ∈ L' := (QuotientGroup.eq_one_iff _).1 h
    have hdD : (d : G) ∈ D := hd
    have hdL : (d : G) ∈ L := h1
    have hd1 : (d : G) = 1 := hZ _ hdL fun y hy => (Subgroup.mem_centralizer_iff.1 hdD.2 y hy).symm
    refine Subtype.ext (Subtype.ext hd1)
  have hDp' : IsPGroup 2 (D.subgroupOf Γ) := hQ2.of_injective _ hinj
  have hDp : IsPGroup 2 D := hDp'.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ≤ Γ))
  have hDn : (D.subgroupOf Γ).Normal := by
    constructor
    intro n hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hn' ⊢
    obtain ⟨hnΓ, hnC⟩ := hn'
    refine ⟨Γ.mul_mem (Γ.mul_mem g.2 hnΓ) (Γ.inv_mem g.2), Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hl' : (g : G)⁻¹ * l * g ∈ L := by
      have := Subgroup.mem_subgroupOf.1 (hn.conj_mem ⟨l, hLΓ hl⟩ (Subgroup.mem_subgroupOf.2 hl) g⁻¹)
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 hnC _ hl'
    have key : l * ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹) * l :=
      calc l * ((g : G) * (n : G) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * l * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((n : G) * ((g : G)⁻¹ * l * (g : G))) * (g : G)⁻¹ := by rw [h2]
        _ = ((g : G) * (n : G) * (g : G)⁻¹) * l := by group
    simpa using key
  have hle : D ≤ pCoreOf 2 Γ := le_pCoreOf 2 inf_le_left hDn hDp
  rw [hO2] at hle
  exact le_bot_iff.1 hle

end Quot

section Quot2

theorem isPGroup_quotient_of_sup {X : Type*} [Group X] {N T₁ : Subgroup X} [N.Normal]
    (hsup : N ⊔ T₁ = ⊤) (hT₁ : IsPGroup 2 T₁) : IsPGroup 2 (X ⧸ N) := by
  have hs : Function.Surjective ((QuotientGroup.mk' N).comp T₁.subtype) := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
    have hg : g ∈ N ⊔ T₁ := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨n, hn, t, ht, hnt⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    refine ⟨⟨t, ht⟩, ?_⟩
    show QuotientGroup.mk' N t = QuotientGroup.mk' N g
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [← hnt, map_mul, h1, one_mul]
  exact hT₁.of_surjective _ hs

theorem le_of_perfect_of_quotient_two {X : Type*} [Group X] [Finite X] {N T₁ P : Subgroup X} [N.Normal]
    (hsup : N ⊔ T₁ = ⊤) (hT₁ : IsPGroup 2 T₁) (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (X ⧸ N) := isPGroup_quotient_of_sup hsup hT₁
  set Q := P.map (QuotientGroup.mk' N) with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, hP]
  by_contra hne
  have hQne : Q ≠ ⊥ := by
    intro h
    apply hne
    intro x hx
    have : QuotientGroup.mk' N x ∈ Q := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have hQp : IsPGroup 2 Q := hQ2.to_subgroup Q
  have := hQp.isNilpotent
  have hsolv : Group.IsSolvable Q := inferInstance
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.2 hQperf
  exact Group.IsPerfect.not_isSolvable Q hsolv

end Quot2

end LRed5

end CFSG.Quasithin
