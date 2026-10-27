module

public import CFSG.Quasithin.Background.RonanE114O2
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

section Roots

@[expose] def i0 : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def i1 : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem i0_ne_i1 : i0 ≠ i1 := by decide

theorem eq_i0_or_i1 (j : Fin Tag.G2.rank) : j = i0 ∨ j = i1 := by
  revert j
  decide

theorem sum_g2 (f : Fin Tag.G2.rank → ℤ) : ∑ j, f j = f i0 + f i1 := Fin.sum_univ_two f

theorem cartan_g2_00 : Tag.G2.cartan i0 i0 = 2 := by decide
theorem cartan_g2_01 : Tag.G2.cartan i0 i1 = -1 := by decide
theorem cartan_g2_10 : Tag.G2.cartan i1 i0 = -3 := by decide
theorem cartan_g2_11 : Tag.G2.cartan i1 i1 = 2 := by decide

theorem reflect_g2_i0 (v : Fin Tag.G2.rank → ℤ) :
    reflect Tag.G2 i0 v i0 = v i1 - v i0 ∧ reflect Tag.G2 i0 v i1 = v i1 := by
  have h01 : i0 ≠ i1 := i0_ne_i1
  have h10 : i1 ≠ i0 := i0_ne_i1.symm
  simp [reflect, sum_g2, cartan_g2_00, cartan_g2_01, Pi.single_apply, h01, h10]
  ring

theorem reflect_g2_i1 (v : Fin Tag.G2.rank → ℤ) :
    reflect Tag.G2 i1 v i0 = v i0 ∧ reflect Tag.G2 i1 v i1 = 3 * v i0 - v i1 := by
  have h01 : i0 ≠ i1 := i0_ne_i1
  have h10 : i1 ≠ i0 := i0_ne_i1.symm
  simp [reflect, sum_g2, cartan_g2_10, cartan_g2_11, Pi.single_apply, h01, h10]
  ring

@[expose] def g2High : Fin Tag.G2.rank → ℤ := ![2, 3]

theorem g2High_i0 : g2High i0 = 2 := rfl
theorem g2High_i1 : g2High i1 = 3 := rfl

@[expose] def g2RootCoords : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (1, 1), (1, 2), (1, 3), (2, 3),
    (-1, 0), (0, -1), (-1, -1), (-1, -2), (-1, -3), (-2, -3)}

theorem g2_reflect_coords :
    ∀ p ∈ g2RootCoords, (p.2 - p.1, p.2) ∈ g2RootCoords ∧ (p.1, 3 * p.1 - p.2) ∈ g2RootCoords := by
  decide

theorem g2_root_coords {γ : Fin Tag.G2.rank → ℤ} (h : IsRoot Tag.G2 γ) :
    (γ i0, γ i1) ∈ g2RootCoords := by
  induction h with
  | basis j =>
    have h01 : i0 ≠ i1 := i0_ne_i1
    have h10 : i1 ≠ i0 := i0_ne_i1.symm
    rcases eq_i0_or_i1 j with rfl | rfl <;> simp [g2RootCoords, Pi.single_apply, h01, h10]
  | reflect i hv ih =>
    rcases eq_i0_or_i1 i with rfl | rfl
    · obtain ⟨e0, e1⟩ := reflect_g2_i0 _
      rw [e0, e1]
      exact (g2_reflect_coords _ ih).1
    · obtain ⟨e0, e1⟩ := reflect_g2_i1 _
      rw [e0, e1]
      exact (g2_reflect_coords _ ih).2

theorem isRoot_g2High : IsRoot Tag.G2 g2High := by
  have h1 : IsRoot Tag.G2 (Pi.single i0 1) := IsRoot.basis i0
  have h2 := IsRoot.reflect (τ := Tag.G2) i1 h1
  have h3 := IsRoot.reflect (τ := Tag.G2) i0 h2
  convert h3 using 1
  ext j
  have h01 : i0 ≠ i1 := i0_ne_i1
  have h10 : i1 ≠ i0 := i0_ne_i1.symm
  rcases eq_i0_or_i1 j with rfl | rfl
  · rw [(reflect_g2_i0 _).1, (reflect_g2_i1 _).2, (reflect_g2_i1 _).1]
    simp [g2High_i0, Pi.single_apply, h01, h10]
  · rw [(reflect_g2_i0 _).2, (reflect_g2_i1 _).2]
    simp [g2High_i1, Pi.single_apply, h01, h10]

theorem g2_height_le {γ : Fin Tag.G2.rank → ℤ} (h : IsRoot Tag.G2 γ) :
    height (τ := Tag.G2) γ ≤ 5 := by
  have := g2_root_coords h
  simp only [g2RootCoords, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
  rw [height, sum_g2]
  omega

theorem height_g2 (γ : Fin Tag.G2.rank → ℤ) : height (τ := Tag.G2) γ = γ i0 + γ i1 := by
  rw [height, sum_g2]

theorem g2_bezout {γ : Fin Tag.G2.rank → ℤ} (h : IsRoot Tag.G2 γ) :
    ∃ a b : ℤ, a * (∑ j, Tag.G2.cartan i0 j * γ j) + b * (∑ j, Tag.G2.cartan i1 j * γ j) = 1 := by
  have h12 := g2_root_coords h
  simp only [g2RootCoords, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h12
  have hxy : ∃ x y : ℤ, x * γ i0 + y * γ i1 = 1 := by
    rcases h12 with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ |
      ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨1, 0, by omega⟩
    · exact ⟨0, 1, by omega⟩
    · exact ⟨1, 0, by omega⟩
    · exact ⟨1, 0, by omega⟩
    · exact ⟨1, 0, by omega⟩
    · exact ⟨-1, 1, by omega⟩
    · exact ⟨-1, 0, by omega⟩
    · exact ⟨0, -1, by omega⟩
    · exact ⟨-1, 0, by omega⟩
    · exact ⟨-1, 0, by omega⟩
    · exact ⟨-1, 0, by omega⟩
    · exact ⟨1, -1, by omega⟩
  obtain ⟨x, y, hxy⟩ := hxy
  refine ⟨2 * x + 3 * y, x + 2 * y, ?_⟩
  simp only [sum_g2, cartan_g2_00, cartan_g2_01, cartan_g2_10, cartan_g2_11]
  linarith

end Roots


section MLevel


variable {K : Type} [Field K]

theorem borelGroup_le_normalizer_high :
    borelGroup Tag.G2 K ≤
      Subgroup.normalizer (rootSubgroup Tag.G2 K g2High : Set (ModGL Tag.G2 K)) := by
  have hr : IsRoot Tag.G2 g2High := isRoot_g2High
  have hspan : rootSpan Tag.G2 K {g2High} = rootSubgroup Tag.G2 K g2High := by
    simp [rootSpan]
  rw [← hspan]
  refine sup_le (torusGroup_le_normalizer_rootSpan fun α hα => ?_)
    (posUnipotent_le_normalizer_of_absorbs (fun α hα => ?_) ?_)
  · rw [Set.mem_singleton_iff] at hα
    rw [hα]
    exact hr
  · rw [Set.mem_singleton_iff] at hα
    rw [hα]
    exact ⟨hr, by rw [height_g2, g2High_i0, g2High_i1]; norm_num⟩
  · intro α hα β hβ a b ha hb hroot
    exfalso
    rw [Set.mem_singleton_iff] at hβ
    have h1 := g2_height_le hroot
    have h2 : (1 : ℤ) ≤ height (τ := Tag.G2) α := hα.2
    rw [height_g2] at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply] at h1
    simp only [nsmul_eq_mul, hβ, g2High_i0, g2High_i1] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith

theorem exists_bruhat_conj {g : ModGL Tag.G2 K} (hg : g ∈ adjointGroup Tag.G2 K) :
    ∃ b ∈ borelGroup Tag.G2 K, ∃ γ : Fin Tag.G2.rank → ℤ, IsRoot Tag.G2 γ ∧
      A1b.conjSub g (rootSubgroup Tag.G2 K g2High) = A1b.conjSub b (rootSubgroup Tag.G2 K γ) := by
  have hcover : g ∈ ⋃ w, bruhatCell Tag.G2 K w := by
    have h := adjointGroup_eq_iUnion_bruhatCell (τ := Tag.G2) (K := K)
    rw [← h]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hcover
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
  refine ⟨b₁, hb₁, w • g2High, IsRoot.smul isRoot_g2High w, ?_⟩
  rw [A1b.conjSub_mul, A1b.conjSub_mul]
  have h2 : A1b.conjSub b₂ (rootSubgroup Tag.G2 K g2High) = rootSubgroup Tag.G2 K g2High :=
    A1b.conjSub_eq_iff_mem_normalizer.mpr (borelGroup_le_normalizer_high hb₂)
  rw [h2]
  exact congrArg (A1b.conjSub b₁)
    ((canonical_weyl_root_transport Tag.G2 K).2.1 w g2High isRoot_g2High)

theorem torus_dichotomy {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ)
    {O : Subgroup (ModGL Tag.G2 K)}
    (hO : ∀ h ∈ torusGroup Tag.G2 K, ∀ z ∈ O, h * z * h⁻¹ ∈ O) :
    rootSubgroup Tag.G2 K γ ⊓ O = ⊥ ∨ rootSubgroup Tag.G2 K γ ≤ O := by
  by_cases hbot : rootSubgroup Tag.G2 K γ ⊓ O = ⊥
  · exact Or.inl hbot
  refine Or.inr fun y hy => ?_
  obtain ⟨⟨x, hxR, hxO⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.mp hxR
  obtain ⟨s, rfl⟩ := mem_rootSubgroup.mp hy
  have ht : t ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (pinnedX_zero (τ := Tag.G2) (R := K) γ))
  by_cases hs : s = 0
  · rw [hs, pinnedX_zero]
    exact O.one_mem
  have hv : s / t ≠ 0 := div_ne_zero hs ht
  obtain ⟨a, b, hab⟩ := g2_bezout hγ
  set v : Kˣ := Units.mk0 (s / t) hv with hvdef
  set u₀ := torusElt Tag.G2 K i0 (v ^ a) with hu₀
  set u₁ := torusElt Tag.G2 K i1 (v ^ b) with hu₁
  have hu₀T : u₀ ∈ torusGroup Tag.G2 K := Subgroup.subset_closure ⟨(i0, v ^ a), rfl⟩
  have hu₁T : u₁ ∈ torusGroup Tag.G2 K := Subgroup.subset_closure ⟨(i1, v ^ b), rfl⟩
  have hconj : u₀ * (u₁ * pinnedX Tag.G2 K γ t * u₁⁻¹) * u₀⁻¹ = pinnedX Tag.G2 K γ s := by
    rw [root_torus_conjugation i1 hγ (v ^ b) t, root_torus_conjugation i0 hγ (v ^ a)]
    congr 1
    rw [← mul_assoc, ← Units.val_mul, ← zpow_mul, ← zpow_mul, ← zpow_add, hab, zpow_one]
    simp [hvdef, hv, ht]
  have hmem := hO (u₀ * u₁) (mul_mem hu₀T hu₁T) _ hxO
  rw [← hconj]
  simpa [mul_assoc, mul_inv_rev] using hmem

end MLevel


section SLevel


variable {K : Type} [Field K]

@[expose] noncomputable def g2Root (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.G2 K) :=
  (rootSubgroup Tag.G2 K g2High).subgroupOf (adjointGroup Tag.G2 K)

theorem map_subtype_conjSub {M : Type} [Group M] {C : Subgroup M} (c : ↥C) (Y : Subgroup ↥C) :
    (A1b.conjSub c Y).map C.subtype = A1b.conjSub (c : M) (Y.map C.subtype) := by
  rw [A1b.conjSub, A1b.conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem g2_hpos (c : ↥(adjointGroup Tag.G2 K)) :
    ∃ b ∈ (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K),
      ∃ A₁ : Subgroup ↥(adjointGroup Tag.G2 K),
        (∀ O : Subgroup ↥(adjointGroup Tag.G2 K),
          (torusGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤
            Subgroup.normalizer (O : Set ↥(adjointGroup Tag.G2 K)) → A₁ ⊓ O = ⊥ ∨ A₁ ≤ O) ∧
        A1b.conjSub c⁻¹ (g2Root K) = A1b.conjSub b A₁ := by
  obtain ⟨b₁, hb₁, γ, hγ, heq⟩ := exists_bruhat_conj
    (g := (((c⁻¹ : ↥(adjointGroup Tag.G2 K))) : ModGL Tag.G2 K)) (c⁻¹).2
  have hb₁C : b₁ ∈ adjointGroup Tag.G2 K := borelGroup_le_adjointGroup' hb₁
  refine ⟨⟨b₁, hb₁C⟩, hb₁, (rootSubgroup Tag.G2 K γ).subgroupOf (adjointGroup Tag.G2 K), ?_, ?_⟩
  · intro O hO
    set O' := O.map (adjointGroup Tag.G2 K).subtype with hO'def
    have hO' : ∀ h ∈ torusGroup Tag.G2 K, ∀ z ∈ O', h * z * h⁻¹ ∈ O' := by
      intro h hh z hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hhC : h ∈ adjointGroup Tag.G2 K :=
        borelGroup_le_adjointGroup' (torusGroup_le_borelGroup hh)
      have hmem : (⟨h, hhC⟩ : ↥(adjointGroup Tag.G2 K)) ∈ Subgroup.normalizer (O : Set _) :=
        hO (by simpa [Subgroup.mem_subgroupOf] using hh)
      have := (Subgroup.mem_normalizer_iff.mp hmem z').mp hz'
      exact ⟨_, this, by simp⟩
    rcases torus_dichotomy hγ hO' with h | h
    · left
      refine eq_bot_iff.mpr fun x hx => ?_
      have hx1 : (x : ModGL Tag.G2 K) ∈ rootSubgroup Tag.G2 K γ ⊓ O' :=
        ⟨hx.1, ⟨x, hx.2, rfl⟩⟩
      rw [h, Subgroup.mem_bot] at hx1
      exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
    · right
      intro x hx
      obtain ⟨y, hy, hyx⟩ := h hx
      have : y = x := Subtype.ext hyx
      rwa [← this]
  · apply Subgroup.map_injective (adjointGroup Tag.G2 K).subtype_injective
    rw [map_subtype_conjSub, map_subtype_conjSub, g2Root,
      Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup _),
      Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup _)]
    simpa using heq

theorem g2_normalTwo [Finite K] [CharP K 2] (R : Subgroup ↥(adjointGroup Tag.G2 K))
    (hR : g2Root K ≤ R) : NormalTwoDichotomy (g2Root K) R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU : IsSylowIn 2 ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  have hBN : borelGroup Tag.G2 K ≤
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp
      (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.2.2.2.1
  have hBU : (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤
      Subgroup.normalizer (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := Subgroup.mem_normalizer_iff.mp (hBN hb) (u : ModGL Tag.G2 K)
    simpa [Subgroup.mem_subgroupOf] using h
  exact normalTwo_of_BT (CFSG.LieType.Chevalley.holds_adjointGroup_tag Tag.G2 K 2) hU hBU
    (Subgroup.subgroupOf_mono _ torusGroup_le_borelGroup) g2_hpos R hR

end SLevel


section Model


variable {K : Type} [Field K]

theorem isElemAbelian_g2Root [CharP K 2] : IsElemAbelian 2 (g2Root K) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.mp x.2)
    obtain ⟨d, hd⟩ := mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.mp y.2)
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hc, ← hd, ← pinnedX_add, ← pinnedX_add, add_comm]
  · obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.mp hx)
    apply Subtype.ext
    simp only [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    rw [← hc, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem card_g2Root : Nat.card (g2Root K) = Nat.card K := by
  have h1 : Nat.card (g2Root K) = Nat.card (rootSubgroup Tag.G2 K g2High) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSubgroup_le_adjointGroup _)).toEquiv
  rw [h1, ← Nat.card_congr (rootSubgroupEquiv Tag.G2 K g2High).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem g2_nonabelian [Finite K] (hK4 : 4 ≤ Nat.card K) :
    ∃ x y : ↥(adjointGroup Tag.G2 K), x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  have hK4' : (4 : ℕ∞) ≤ ENat.card K := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hK4
  set i : Fin Tag.G2.rank := i0 with hi
  have hperf := (rank_one_scalar_perfect Tag.G2 K i).2 hK4'
  have hbot : commutator ↥(rankOneSubgroup (τ := Tag.G2) (K := K) i) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (hc y x)
  rw [hbot] at hperf
  have hx : xElt (τ := Tag.G2) (K := K) i 1 ∈ rankOneSubgroup (τ := Tag.G2) (K := K) i :=
    Subgroup.mem_sup_left (xElt_mem_simplePosSubgroup i 1)
  have h1 : (⟨xElt (τ := Tag.G2) (K := K) i 1, hx⟩ :
      ↥(rankOneSubgroup (τ := Tag.G2) (K := K) i)) ∈
      (⊥ : Subgroup ↥(rankOneSubgroup (τ := Tag.G2) (K := K) i)) := by
    rw [hperf]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_bot] at h1
  have h2 : xElt (τ := Tag.G2) (K := K) i 1 = 1 := congrArg Subtype.val h1
  have h3 : (xUnit Tag.G2 K i 1 : Module.End K (RootModule Tag.G2 K)) = xUnit Tag.G2 K i 0 := by
    rw [xUnit_zero]
    exact congrArg (fun g : adjointGroup Tag.G2 K =>
      ((g : ModGL Tag.G2 K) : Module.End K (RootModule Tag.G2 K))) h2
  exact one_ne_zero (xOp_injective i h3)

variable {G : Type} [Group G] [Finite G]

theorem le_nParam_of_isG2 {T : Subgroup G} {n : ℕ}
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hG2 : CFSG.Quasithin.IsG2 2 n ↥(CFSG.generalizedFitting G)) :
    (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  obtain ⟨hn2, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hG2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  exact le_nParam_of_normalTwo_model hn2 hs hT hFT e (g2_nonabelian hK4) isElemAbelian_g2Root
    (by rw [card_g2Root, hK]) fun R hR => g2_normalTwo R hR

end Model

end CFSG.Quasithin.RonanE114
