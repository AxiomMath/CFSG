module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts
public import CFSG.Quasithin.Vol2.Ch11SecAVi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped IsMulCommutative

section General

variable {G : Type} [Group G]

theorem isCyclic_of_le_zpowers {X : Subgroup G} {g : G} (h : X ≤ Subgroup.zpowers g) :
    IsCyclic ↥X :=
  isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe h).surjective

theorem conjV_zpow (V : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (k : ℤ) :
    conjV V (x ^ k) (Subgroup.zpow_mem _ hx k) = conjV V x hx ^ k := by
  unfold conjV
  rw [← map_zpow]
  rfl

theorem exists_fixed_ne_one {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1) (a : MulAut W)
    (ha : a ^ 2 = 1) {v : W} (hv : v ≠ 1) : ∃ w : W, w ≠ 1 ∧ a w = w := by
  by_cases hfix : a v = v
  · exact ⟨v, hv, hfix⟩
  · refine ⟨v * a v, fun h => hfix ?_, ?_⟩
    · have h1 : a v = v⁻¹ := eq_inv_of_mul_eq_one_right h
      have h2 : v⁻¹ = v := by
        have := hW v
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      rw [h1, h2]
    · have haa : a (a v) = v := by
        have := congrArg (fun b : MulAut W => b v) ha
        simpa [pow_two, MulAut.mul_apply] using this
      rw [map_mul, haa, mul_comm]

theorem odd_card_of_fixes {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {v : W} (hv : v ≠ 1) {X : Subgroup (MulAut W)}
    (hfix : ∀ x ∈ X, ∀ w : W, w ≠ 1 → x w = w → x = 1) : Odd (Nat.card X) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h2
  have hx2 : (x : MulAut W) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨w, hw, hxw⟩ := exists_fixed_ne_one hW (x : MulAut W) hx2 hv
  have h1 : (x : MulAut W) = 1 := hfix x x.2 w hw hxw
  have h3 : x = 1 := Subtype.ext h1
  rw [h3, orderOf_one] at hx
  exact absurd hx (by norm_num)

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem autOn_T_props (hyp : Hyp11 G T L I n) {U : Subgroup G} (hUV : U ≤ fsuV T I)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    IsPGroup 2 (autOn T (fsuV T I)) ∧
      (∀ s ∈ autOn T (fsuV T I), ∀ h ∈ autOn L (fsuV T I), s * h * s⁻¹ ∈ autOn L (fsuV T I)) ∧
      autOn T (fsuV T I) ≤ stabW (U.subgroupOf (fsuV T I)) := by
  refine ⟨B6.isPGroup_autOn hyp.fsu.sylow.1 _, fun s hs h hh => ?_, fun s hs => ?_⟩
  · obtain ⟨t, ht, htV, rfl⟩ := mem_autOn_iff.mp hs
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hh
    rw [conjV_conj]
    exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp (hyp.normal ht) l).mp hl) _
  · obtain ⟨t, ht, htV, rfl⟩ := mem_autOn_iff.mp hs
    exact (conjV_mem_stabW_iff hUV htV).mpr (hTU ht)

theorem actsOn_point (hF : PointFacts) (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ActsCyclicallyOn (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I)))
        (V₁.subgroupOf (fsuV T I)) ∧
      ActsRegularlyOn (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I)))
        (V₁.subgroupOf (fsuV T I)) ∧
      ActsCyclicallyOn (autOn T (fsuV T I)) (V₁.subgroupOf (fsuV T I)) := by
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n hyp
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV hyp).2 w w.2)
  have hn : 2 ≤ n := hyp.one_lt
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [← inf_centralizer_subgroupOf, hC, Subgroup.bot_subgroupOf]
  have hflag := isFlagW_of_isVi hyp hV₁
  rw [hZ] at hflag
  obtain ⟨hS2, hSH, hSU⟩ := autOn_T_props hyp (IsVi.le_fsuV hV₁) (IsVi.le_normalizer hV₁)
  rcases hk with ⟨K, _, _, hK, -, π, hπ, hng⟩ | ⟨K, _, _, hK, -, π, hπ, hng⟩ |
      ⟨-, -, -, -, -, hG2⟩
  · rw [hZ] at hπ
    obtain ⟨h1, h2⟩ := hF.pointSL3 K n hn hK _ hsq _ π hπ _ (isSylowTwoOf_P hyp) _ hflag
    exact ⟨h1, h2,
      hF.pointTSL3 K n hn hK _ hsq _ π hπ _ (isSylowTwoOf_P hyp) _ hflag _ hS2 hSH hSU hng⟩
  · rw [hZ] at hπ
    obtain ⟨h1, h2⟩ := hF.pointSp4 K n hn hK _ hsq _ π hπ _ (isSylowTwoOf_P hyp) _ hflag
    exact ⟨h1, h2,
      hF.pointTSp4 K n hn hK _ hsq _ π hπ _ (isSylowTwoOf_P hyp) _ hflag _ hS2 hSH hSU hng⟩
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    rw [hZ] at hπ
    obtain ⟨h1, h2⟩ := hF.pointG2 K n hn hK _ hsq _ π hπ _ (isSylowTwoOf_P hyp) _ hflag
    exact ⟨h1, h2,
      hF.pointTG2 K n hn hK _ hsq _ π hπ _ (isSylowTwoOf_P hyp) _ hflag _ hS2 hSH hSU⟩

omit [Finite G] in
theorem conjV_restrict {V₁ V : Subgroup G} (hle : V₁ ≤ V) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hx₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (v : ↥V₁) : ((conjV V₁ x hx₁ v : ↥V₁) : G) = ((conjV V x hx ⟨v, hle v.2⟩ : ↥V) : G) := by
  rw [conjV_apply_coe, conjV_apply_coe]

omit [Finite G] in
theorem autOn_inf_stabW {L V₁ V : Subgroup G} (hle : V₁ ≤ V) :
    autOn L V ⊓ stabW (V₁.subgroupOf V) =
      autOn (L ⊓ Subgroup.normalizer (V₁ : Set G)) V := by
  ext h
  constructor
  · rintro ⟨hL, hU⟩
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hL
    exact conjV_mem_autOn (L := L ⊓ Subgroup.normalizer (V₁ : Set G))
      ⟨hl, (conjV_mem_stabW_iff hle hlV).mp hU⟩ hlV
  · intro hh
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hh
    exact ⟨conjV_mem_autOn hl.1 _, (conjV_mem_stabW_iff hle hlV).mpr hl.2⟩

omit [Finite G] in
theorem isCyclic_autOn_of_actsCyclicallyOn {A V₁ V : Subgroup G} (hle : V₁ ≤ V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hAV₁ : A ≤ Subgroup.normalizer (V₁ : Set G))
    (h : ActsCyclicallyOn (autOn A V) (V₁.subgroupOf V)) : IsCyclic ↥(autOn A V₁) := by
  obtain ⟨s₀, hs₀, hgen⟩ := h
  obtain ⟨a₀, ha₀, ha₀V, rfl⟩ := mem_autOn_iff.mp hs₀
  refine isCyclic_of_le_zpowers (g := conjV V₁ a₀ (hAV₁ ha₀)) fun x hx => ?_
  obtain ⟨a, ha, haV₁, rfl⟩ := mem_autOn_iff.mp hx
  obtain ⟨k, hk⟩ := hgen (conjV V a (hAV ha)) (conjV_mem_autOn ha _)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  ext v
  have hv : (⟨v, hle v.2⟩ : ↥V) ∈ V₁.subgroupOf V := Subgroup.mem_subgroupOf.mpr v.2
  rw [← conjV_zpow, conjV_restrict hle (Subgroup.zpow_mem _ ha₀V k), conjV_zpow V ha₀V k,
    ← hk _ hv, conjV_restrict hle (hAV ha)]

omit [Finite G] in
theorem regular_autOn_of_actsRegularlyOn {A V₁ V : Subgroup G} (hle : V₁ ≤ V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hAV₁ : A ≤ Subgroup.normalizer (V₁ : Set G))
    (h : ActsRegularlyOn (autOn A V) (V₁.subgroupOf V)) :
    (∀ v w : ↥V₁, v ≠ 1 → w ≠ 1 → ∃! x : ↥(autOn A V₁), (x : MulAut ↥V₁) v = w) ∧
      ∀ x ∈ autOn A V₁, ∀ w : ↥V₁, w ≠ 1 → x w = w → x = 1 := by
  have hmem : ∀ v : ↥V₁, (⟨v, hle v.2⟩ : ↥V) ∈ V₁.subgroupOf V := fun v =>
    Subgroup.mem_subgroupOf.mpr v.2
  have hne : ∀ v : ↥V₁, v ≠ 1 → (⟨v, hle v.2⟩ : ↥V) ≠ 1 := fun v hv h1 =>
    hv (Subtype.ext (by simpa using congrArg Subtype.val h1))
  have hfix : ∀ x ∈ autOn A V₁, ∀ w : ↥V₁, w ≠ 1 → x w = w → x = 1 := by
    intro x hx w hw hxw
    obtain ⟨a, ha, haV₁, rfl⟩ := mem_autOn_iff.mp hx
    have h1 : conjV V a (hAV ha) ⟨w, hle w.2⟩ = ⟨w, hle w.2⟩ := by
      apply Subtype.ext
      rw [← conjV_restrict hle (hAV ha) haV₁, hxw]
    have h2 := h.2 _ (conjV_mem_autOn ha _) _ (hmem w) (hne w hw) h1
    ext v
    rw [conjV_restrict hle (hAV ha) haV₁, h2 _ (hmem v)]
    rfl
  refine ⟨fun v w hv hw => ?_, hfix⟩
  obtain ⟨s, hs, hsv⟩ := h.1 _ (hmem v) _ (hmem w) (hne v hv) (hne w hw)
  obtain ⟨a, ha, haV, rfl⟩ := mem_autOn_iff.mp hs
  have hx : conjV V₁ a (hAV₁ ha) ∈ autOn A V₁ := conjV_mem_autOn ha _
  have hxv : conjV V₁ a (hAV₁ ha) v = w := by
    apply Subtype.ext
    rw [conjV_restrict hle haV, hsv]
  refine ⟨⟨_, hx⟩, hxv, fun y hy => ?_⟩
  have hyx : (y : MulAut ↥V₁)⁻¹ * conjV V₁ a (hAV₁ ha) = 1 := by
    refine hfix _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ y.2) hx) v hv ?_
    rw [MulAut.mul_apply, hxv, ← hy, MulAut.inv_apply_self]
  apply Subtype.ext
  exact inv_mul_eq_one.mp hyx

end CFSG.Quasithin.Vol2.Ch11.SecB
