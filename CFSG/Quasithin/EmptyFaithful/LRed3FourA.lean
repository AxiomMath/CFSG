module

public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Vol2.Ch10SecQ1Base
import CFSG.Models.PGLSimple

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

section Generic

theorem lred3_fourList_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : FourList X) :
    FourList Y := by
  rcases h with ⟨n, hn, h | h | h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h | h | h
  · exact Or.inl ⟨n, hn, Or.inl (isPSL_congr e h)⟩
  · exact Or.inl ⟨n, hn, Or.inr (Or.inl (isSz_congr e h))⟩
  · exact Or.inl ⟨n, hn, Or.inr (Or.inr (isPSU_congr e h))⟩
  · exact Or.inr (Or.inl ⟨n, hn, isPSL_congr e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, isPSp4_congr e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isAlt_congr e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, IsG2.of_mulEquiv e h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isPSU_congr e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isPSL_congr e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isPSL_congr e h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isAlt_congr e h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (isSporadic_congr e h)))))))))

variable {Y Γ : Type} [Group Y] [Group Γ]

theorem lred3_cq_equiv (hY : CFSG.IsQuasisimple Y) (π : Γ →* Y) (hπ : Function.Surjective π)
    (Z : Subgroup Γ) [Z.Normal] (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hΓZ : IsSimpleGroup (Γ ⧸ Z)) : Nonempty (Y ⧸ Subgroup.center Y ≃* Γ ⧸ Z) := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hY
  have hnt : Nontrivial (Y ⧸ Subgroup.center Y) := ⟨⟨a, b, by rintro rfl; exact hab rfl⟩⟩
  let ψ : Γ →* Y ⧸ Subgroup.center Y := (QuotientGroup.mk' (Subgroup.center Y)).comp π
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  have hle : Z ≤ ψ.ker := le_ker_of_commute hsimple ⟨a, b, hab⟩ Z hZ ψ hψ
  let φ : Γ ⧸ Z →* Y ⧸ Subgroup.center Y := QuotientGroup.lift Z ψ hle
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨g, rfl⟩ := hψ x
    exact ⟨QuotientGroup.mk g, rfl⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hΓZ φ hφ
  exact ⟨e.symm⟩

private theorem lred3_scalars_comm' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) :
    ∀ x ∈ (StatedScalars ι K).subgroupOf H, ∀ y ∈ (StatedScalars ι K).subgroupOf H,
      x * y = y * x :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_mul_comm H

theorem lred3_cq_stated (hY : CFSG.IsQuasisimple Y) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) (hsimple : IsSimpleGroup (StatedProj H)) (π : ↥H →* Y)
    (hπ : Function.Surjective π) : Nonempty (Y ⧸ Subgroup.center Y ≃* StatedProj H) := by
  have : ((StatedScalars ι K).subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal ι K) _
  exact lred3_cq_equiv hY π hπ _ (lred3_scalars_comm' H) hsimple

theorem lred3_cq_simple (hY : CFSG.IsQuasisimple Y) (hΓ : IsSimpleGroup Γ) (π : Γ →* Y)
    (hπ : Function.Surjective π) : Nonempty (Y ⧸ Subgroup.center Y ≃* Γ) := by
  have : (⊥ : Subgroup Γ).Normal := inferInstance
  obtain ⟨e⟩ := lred3_cq_equiv hY π hπ ⊥ (fun x hx y hy => by
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]) (QuotientGroup.quotientBot (G := Γ)).isSimpleGroup
  exact ⟨e.trans QuotientGroup.quotientBot⟩

private theorem lred3_exists_four {K : Type} [Field K] [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
  exact ⟨s, hs⟩

theorem lred3_simple_statedProj_sl {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 2 ≤ d)
    (h : 3 ≤ d ∨ 4 ≤ Nat.card K) : IsSimpleGroup (StatedProj (StatedSL d K)) :=
  CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K hd (by omega) (by omega)

end Generic

section Convert

variable {Y : Type} [Group Y]

private theorem lred3_four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem lred3_four_of_sl2 (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (π : ↥(StatedSL 2 K) →* Y)
    (hπ : Function.Surjective π) : FourList (Y ⧸ Subgroup.center Y) := by
  have h4 := lred3_four_le_two_pow hn
  obtain ⟨e⟩ := lred3_cq_stated hY (StatedSL 2 K)
    (lred3_simple_statedProj_sl le_rfl (Or.inr (hK ▸ h4))) π hπ
  refine Or.inl ⟨n, hn, Or.inl ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨e⟩⟩⟩
  · intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)
  · intro h
    have h2 : 2 ^ n = 3 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)

theorem lred3_four_of_sl3 (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (π : ↥(StatedSL 3 K) →* Y)
    (hπ : Function.Surjective π) : FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_stated hY (StatedSL 3 K)
    (lred3_simple_statedProj_sl (by norm_num) (Or.inl le_rfl)) π hπ
  exact Or.inr (Or.inl ⟨n, hn, ⟨Nat.prime_two, hn, by norm_num,
    fun h => absurd (congrArg Prod.fst h) (by norm_num),
    fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩)

theorem lred3_four_of_sl4 (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (π : ↥(StatedSL 4 K) →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_stated hY (StatedSL 4 K)
    (lred3_simple_statedProj_sl (by norm_num) (Or.inl (by norm_num))) π hπ
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
      fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩, K, inferInstance, inferInstance,
      by rw [hK]; norm_num, ⟨e⟩⟩)))))) 

theorem lred3_four_of_sl5 (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (π : ↥(StatedSL 5 K) →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_stated hY (StatedSL 5 K)
    (lred3_simple_statedProj_sl (by norm_num) (Or.inl (by norm_num))) π hπ
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
      fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩, K, inferInstance, inferInstance,
      by rw [hK]; norm_num, ⟨e⟩⟩))))))) 

theorem lred3_four_of_sp4 (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (π : ↥(StatedSp 2 K) →* Y)
    (hπ : Function.Surjective π) : FourList (Y ⧸ Subgroup.center Y) := by
  have h4 := lred3_four_le_two_pow hn
  obtain ⟨e⟩ := lred3_cq_stated hY (StatedSp 2 K)
    (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (hK ▸ h4)))) π hπ
  refine Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨e⟩⟩))
  intro h
  have h2 : 2 ^ n = 2 := congrArg Prod.snd h
  exact absurd (h2 ▸ h4) (by norm_num)

theorem lred3_four_of_su3 (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 2) (π : ↥(StatedSU 3 (2 ^ m) K) →* Y)
    (hπ : Function.Surjective π) : FourList (Y ⧸ Subgroup.center Y) := by
  have h4 := lred3_four_le_two_pow hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := fun h => by
    have h2 : 2 ^ m = 2 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)
  obtain ⟨e⟩ := lred3_cq_stated hY (StatedSU 3 (2 ^ m) K)
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 m hK 3 le_rfl hne) π hπ
  exact Or.inl ⟨m, hm, Or.inr (Or.inr ⟨⟨Nat.prime_two, by omega, le_rfl, hne⟩, K, inferInstance,
    inferInstance, hK, ⟨e⟩⟩)⟩

theorem lred3_four_of_alt (hY : CFSG.IsQuasisimple Y) {m : ℕ}
    (hm : m = 5 ∨ m = 6 ∨ m = 7) (π : ↥(alternatingGroup (Fin m)) →* Y)
    (hπ : Function.Surjective π) : FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_simple hY (isSimpleGroup_alt (by omega)) π hπ
  rcases hm with rfl | rfl | rfl
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
    exact Or.inl ⟨2, le_rfl, Or.inl ⟨⟨Nat.prime_two, by norm_num, le_rfl,
      fun h => absurd (congrArg Prod.snd h) (by norm_num),
      fun h => absurd (congrArg Prod.snd h) (by norm_num)⟩, GaloisField 2 2, inferInstance,
      inferInstance, hK, ⟨e.trans e5.symm⟩⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))))

theorem lred3_four_of_sz (hY : CFSG.IsQuasisimple Y) {a : ℕ}
    (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (π : ↥(CFSG.Blueprint.suzukiGroup a K) →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  have hs : IsSimpleGroup ↥(CFSG.Blueprint.suzukiGroup a K) :=
    (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  obtain ⟨e⟩ := lred3_cq_simple hY hs π hπ
  exact Or.inl ⟨2 * a + 1, by omega, Or.inr (Or.inl ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl,
    hK, ⟨e⟩⟩)⟩

theorem lred3_cq_of_quasisimple {Γ₀ : Type} [Group Γ₀] (hΓ : CFSG.IsQuasisimple Γ₀)
    (hY : CFSG.IsQuasisimple Y) (π : Γ₀ →* Y) (hπ : Function.Surjective π) :
    Nonempty (Γ₀ ⧸ Subgroup.center Γ₀ ≃* Y ⧸ Subgroup.center Y) := by
  have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY
  obtain ⟨y, hy⟩ := exists_ne (1 : Y)
  obtain ⟨k, rfl⟩ := hπ y
  exact ⟨CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hΓ hπ
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hΓ ⟨k, hy⟩)⟩

theorem lred3_four_of_hat6 (hY : CFSG.IsQuasisimple Y) {Γ₀ : Type} [Group Γ₀]
    (hhat : IsHat Γ₀ ↥(alternatingGroup (Fin 6))) (π : Γ₀ →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_of_quasisimple hhat.1 hY π hπ
  obtain ⟨f⟩ := hhat.2.2
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩)))

theorem lred3_four_of_hatM22 (hY : CFSG.IsQuasisimple Y) {Γ₀ : Type} [Group Γ₀]
    (hhat : IsHat Γ₀ ↥CFSG.Open.quasithinM22) (π : Γ₀ →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_of_quasisimple hhat.1 hY π hπ
  obtain ⟨f⟩ := hhat.2.2
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨(e.symm.trans f).trans (MulEquiv.subgroupCongr
      (by rfl : CFSG.Open.quasithinM22 = CFSG.Blueprint.NativeSporadic.M22))⟩))))))))

end Convert

end CFSG.Quasithin
