module

public import CFSG.Quasithin.H13.A5W1622e
public import CFSG.Quasithin.EmptyFaithful.SBc9Heart
public import CFSG.LieType.SteinbergBRSmallAltSylow

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.SteinbergBR.SmallAlt (a6P a6P_mul a6P_inv a6P_one a6P_sign a6P_injective)

instance : DecidablePred (· ∈ evenWeight 6) := fun x => by
  unfold evenWeight
  exact inferInstanceAs (Decidable (_ = _))

instance : DecidablePred (· ∈ constWeight 6) := fun x => by
  unfold constWeight
  exact inferInstanceAs (Decidable (∀ i j, _ = _))


@[expose] def heartAct6 : ↥(alternatingGroup (Fin 6)) →* MulAut (Multiplicative (AltHeart 6)) where
  toFun σ :=
    { toFun := fun u => Multiplicative.ofAdd (SBc9.heartAct σ (Multiplicative.toAdd u))
      invFun := fun u => Multiplicative.ofAdd (SBc9.heartAct σ⁻¹ (Multiplicative.toAdd u))
      left_inv := fun u => by simp [SBc9.heartAct_inv_apply]
      right_inv := fun u => by simp [SBc9.heartAct_apply_inv]
      map_mul' := fun u w => by
        show Multiplicative.ofAdd
          (SBc9.heartAct σ (Multiplicative.toAdd u + Multiplicative.toAdd w)) = _
        rw [map_add]
        rfl }
  map_one' := by
    ext u
    simp [SBc9.heartAct_one]
  map_mul' σ τ := by
    ext u
    simp [SBc9.heartAct_mul]

theorem heartAct6_apply (σ : ↥(alternatingGroup (Fin 6))) (u : Multiplicative (AltHeart 6)) :
    heartAct6 σ u = Multiplicative.ofAdd (SBc9.heartAct σ (Multiplicative.toAdd u)) := rfl

theorem a6_fixed_unique_rep : ∀ x y : Fin 6 → ZMod 2, ∑ i, x i = 0 → ∑ i, y i = 0 →
    (¬ ∀ i, x i = x 0) → (¬ ∀ i, y i = y 0) →
    (∀ i, x ((a6P 4)⁻¹ i) + x i = x ((a6P 4)⁻¹ 0) + x 0) →
    (∀ i, x ((a6P 6)⁻¹ i) + x i = x ((a6P 6)⁻¹ 0) + x 0) →
    (∀ i, y ((a6P 4)⁻¹ i) + y i = y ((a6P 4)⁻¹ 0) + y 0) →
    (∀ i, y ((a6P 6)⁻¹ i) + y i = y ((a6P 6)⁻¹ 0) + y 0) →
    ∀ i, x i + y i = x 0 + y 0 := by
  decide +kernel

theorem mem_constWeight_iff {x : ↥(evenWeight 6)} :
    x ∈ constWeight 6 ↔ ∀ i, (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) 0 :=
  ⟨fun h i => h i 0, fun h i j => (h i).trans (h j).symm⟩

theorem heartAct_mk_eq_iff (σ : Equiv.Perm (Fin 6)) (x : ↥(evenWeight 6)) :
    SBc9.heartAct σ (QuotientAddGroup.mk x : AltHeart 6) = QuotientAddGroup.mk x ↔
      ∀ i, (x : Fin 6 → ZMod 2) (σ⁻¹ i) + (x : Fin 6 → ZMod 2) i =
        (x : Fin 6 → ZMod 2) (σ⁻¹ 0) + (x : Fin 6 → ZMod 2) 0 := by
  rw [SBc9.heartAct_mk, QuotientAddGroup.eq, mem_constWeight_iff]
  have hval : ∀ i, ((-permWeight 6 σ x + x : ↥(evenWeight 6)) : Fin 6 → ZMod 2) i =
      (x : Fin 6 → ZMod 2) (σ⁻¹ i) + (x : Fin 6 → ZMod 2) i := by
    intro i
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
    rw [ZMod.neg_eq_self_mod_two]
    rfl
  simp only [hval]

theorem a6_fixed_unique : ∀ n p : AltHeart 6, n ≠ 0 → p ≠ 0 →
    SBc9.heartAct (a6P 4) n = n → SBc9.heartAct (a6P 6) n = n →
    SBc9.heartAct (a6P 4) p = p → SBc9.heartAct (a6P 6) p = p → n = p := by
  intro n p hn hp hn4 hn6 hp4 hp6
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective n
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective p
  have hx0 : ¬ ∀ i, (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) 0 := by
    intro h
    apply hn
    exact (QuotientAddGroup.eq_zero_iff x).mpr (mem_constWeight_iff.mpr h)
  have hy0 : ¬ ∀ i, (y : Fin 6 → ZMod 2) i = (y : Fin 6 → ZMod 2) 0 := by
    intro h
    apply hp
    exact (QuotientAddGroup.eq_zero_iff y).mpr (mem_constWeight_iff.mpr h)
  have hxs : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := by
    have := x.2
    simpa [evenWeight] using this
  have hys : ∑ i, (y : Fin 6 → ZMod 2) i = 0 := by
    have := y.2
    simpa [evenWeight] using this
  have h := a6_fixed_unique_rep _ _ hxs hys hx0 hy0 ((heartAct_mk_eq_iff _ x).mp hn4)
    ((heartAct_mk_eq_iff _ x).mp hn6) ((heartAct_mk_eq_iff _ y).mp hp4)
    ((heartAct_mk_eq_iff _ y).mp hp6)
  rw [QuotientAddGroup.eq, mem_constWeight_iff]
  intro i
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
  rw [ZMod.neg_eq_self_mod_two, ZMod.neg_eq_self_mod_two]
  exact h i

@[expose] def a6Syl : Subgroup ↥(alternatingGroup (Fin 6)) :=
  CFSG.LieType.SteinbergBR.SmallAlt.finSubgroup a6P a6P_mul a6P_inv a6P_one

theorem isSylowTwoOf_a6Syl : IsSylowTwoOf a6Syl ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card a6Syl = 8 :=
    CFSG.LieType.SteinbergBR.SmallAlt.card_finSubgroup _ _ _ _ a6P_injective
      fun i => (Equiv.Perm.mem_alternatingGroup).2 (a6P_sign i)
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have := CFSG.LieType.SteinbergBR.SmallAlt.card_alternating (m := 6) (by norm_num)
    rw [show Nat.factorial 6 = 720 by decide] at this
    omega
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), ?_⟩
  rw [show (a6Syl.subgroupOf ⊤).index = a6Syl.index from Subgroup.relIndex_top_right _]
  have hidx := Subgroup.card_mul_index a6Syl
  rw [hcard, hA] at hidx
  omega

theorem modelFix_a6 : ModelFix heartAct6 a6Syl := by
  intro n p hn hp hnS hpS x hx
  have hfix : ∀ w : Multiplicative (AltHeart 6), (∀ s ∈ a6Syl, heartAct6 s w = w) →
      ∀ i : Fin 8, SBc9.heartAct (a6P i) (Multiplicative.toAdd w) = Multiplicative.toAdd w := by
    intro w hw i
    have := congrArg Multiplicative.toAdd
      (hw ⟨a6P i, (Equiv.Perm.mem_alternatingGroup).2 (a6P_sign i)⟩ ⟨i, rfl⟩)
    rwa [heartAct6_apply, toAdd_ofAdd] at this
  have hnp : n = p := Multiplicative.toAdd.injective
    (a6_fixed_unique _ _ (by simpa using hn) (by simpa using hp) (hfix n hnS 4) (hfix n hnS 6)
      (hfix p hpS 4) (hfix p hpS 6))
  rw [← hnp]
  exact hx

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_altBlock6 (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsAltBlockType K₀ 6) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  obtain ⟨⟨-, -, ⟨hUQ, hU2⟩, -, -⟩, α, hα, -, β, hβ, hβk, hβe⟩ := hblk
  have hQn : K₀ ≤ Subgroup.normalizer (blockQ K₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hKU : K₀ ≤ Subgroup.normalizer (blockU K₀ : Set G) :=
    le_normalizer_commutator hQn Subgroup.le_normalizer
  have hUc : ∀ x ∈ blockU K₀, ∀ x' ∈ blockU K₀, x * x' = x' * x := fun x hx x' hx' =>
    (Subgroup.mem_centralizer_iff.mp (hUQ hx).2 x' (hUQ hx').1).symm
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  have hlA : ∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ blockU K₀ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hKU (hLvK₀ hy)) _).mp he2U
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      β v = heartAct6 (α ℓ) (β u) := by
    intro ℓ u v h
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
    apply Multiplicative.toAdd.injective
    rw [heartAct6_apply, toAdd_ofAdd, ← hx, SBc9.heartAct_mk]
    exact (hβe ℓ u v h x hx).symm
  have hN2 : ∀ n : Multiplicative (AltHeart 6), n ^ 2 = 1 := by
    intro n
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd n)
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← hx, ← QuotientAddGroup.mk_nsmul]
    have h2x : 2 • x = 0 := by
      apply Subtype.ext
      funext i
      simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, AddSubgroup.coe_zero, Pi.zero_apply]
      rw [two_nsmul, CharTwo.add_self_eq_zero]
    rw [h2x, QuotientAddGroup.mk_zero]
  exact S.false_of_closing_model h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ hKU (Zc := blockZ K₀) inf_le_right hU2 hUc hcommA he2U hlA hN2 heartAct6
    isSylowTwoOf_a6Syl modelFix_a6 α hα β hβk hβe'

end Setting

end CFSG.Quasithin.H13.A5
