module

public import CFSG.Quasithin.Vol2.Ch10SecAFactsProved
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

theorem four_dvd_of_shapeCard {N : ℕ} (h : ShapeCard N) : 4 ∣ N := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨a, -, rfl⟩ | rfl
  · exact Dvd.dvd.mul_right ((show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 hn) _
  · refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ⟨(2 ^ (2 * a)) ^ 2, ?_⟩ _) _
    rw [pow_succ]
    ring
  · norm_num

theorem not_prime_of_shapeCard {N : ℕ} (h : ShapeCard N) : ¬ N.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd 4 (four_dvd_of_shapeCard h) with h4 | h4
  · norm_num at h4
  · rw [← h4] at hp
    norm_num at hp

theorem sixty_le_of_shapeCard {N : ℕ} (h : ShapeCard N) : 60 ≤ N := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨a, ha, rfl⟩ | rfl
  · have h4 : 4 ≤ 2 ^ n :=
      (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hn
    have h16 : 16 ≤ 4 ^ n :=
      (show (16 : ℕ) = 4 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hn
    have : 15 ≤ 4 ^ n - 1 := by omega
    nlinarith
  · have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
      (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
    set q := 2 ^ (2 * a + 1)
    have h1 : 7 ≤ q - 1 := by omega
    have h2 : 64 ≤ q ^ 2 := by nlinarith
    have h3 : 1 ≤ q ^ 2 + 1 := by omega
    calc 60 ≤ q ^ 2 := by omega
      _ ≤ q ^ 2 * (q - 1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ h3
  · norm_num

theorem isSimpleGroup_of_isShapeGroup
    {X : Type} [Group X] (h : IsShapeGroup X) : IsSimpleGroup X := by
  rcases h with ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨n, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ | he
  · have := CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL2 hn hK
    exact e.isSimpleGroup
  · subst hf
    have := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := he
    have := isSimpleGroup_SL_two (n := 3) le_rfl
    exact e.isSimpleGroup

theorem exists_mul_ne_of_isShapeGroup
    {X : Type} [Group X] (h : IsShapeGroup X) : ∃ a b : X, a * b ≠ b * a := by
  have hs := isSimpleGroup_of_isShapeGroup h
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => hc a b }
  exact not_prime_of_shapeCard (shapeCard_of_isShapeGroup h) IsSimpleGroup.prime_card

theorem not_surjective_of_isSimpleGroup
    {Γ X : Type} [Group Γ] [Group X] (hΓ : IsSimpleGroup Γ) (hc : ¬ ShapeCard (Nat.card Γ))
    (hX : IsShapeGroup X) (π : Γ →* X) : ¬ Function.Surjective π := by
  intro hπ
  have := nontrivial_of_isShapeGroup hX
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hΓ π hπ
  exact hc (by rw [Nat.card_congr e.toEquiv]; exact shapeCard_of_isShapeGroup hX)

theorem not_surjective_of_mulEquiv
    {Γ Γ' X : Type} [Group Γ] [Group Γ'] [Group X] (e : Γ ≃* Γ') (hΓ : IsSimpleGroup Γ')
    (hc : ¬ ShapeCard (Nat.card Γ')) (hX : IsShapeGroup X) (π : Γ →* X) :
    ¬ Function.Surjective π := by
  intro hπ
  exact not_surjective_of_isSimpleGroup hΓ hc hX (π.comp e.symm.toMonoidHom)
    (hπ.comp e.symm.surjective)

theorem le_ker_of_commute {G X : Type} [Group G] [Group X] (hX : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (π : G →* X) (hπ : Function.Surjective π) :
    Z ≤ π.ker := by
  have : (Z.map π).Normal := Subgroup.Normal.map ‹_› π hπ
  rcases hX.eq_bot_or_eq_top_of_normal (Z.map π) with h | h
  · exact (Subgroup.map_eq_bot_iff Z).mp h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    obtain ⟨x, hx, rfl⟩ : a ∈ Z.map π := h ▸ Subgroup.mem_top a
    obtain ⟨y, hy, rfl⟩ : b ∈ Z.map π := h ▸ Subgroup.mem_top b
    exact hab (by rw [← map_mul, ← map_mul, hZ x hx y hy])

theorem exists_quotient_surjective
    {G X : Type} [Group G] [Group X] (hX : IsShapeGroup X) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (π : G →* X) (hπ : Function.Surjective π) :
    ∃ φ : G ⧸ Z →* X, Function.Surjective φ := by
  have hle := le_ker_of_commute (isSimpleGroup_of_isShapeGroup hX)
    (exists_mul_ne_of_isShapeGroup hX) Z hZ π hπ
  refine ⟨QuotientGroup.lift Z π hle, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := hπ x
  exact ⟨QuotientGroup.mk g, rfl⟩

theorem nonempty_mulEquiv_quotient_of_isShapeGroup
    {G X : Type} [Group G] [Group X] (hX : IsShapeGroup X) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hGZ : IsSimpleGroup (G ⧸ Z)) (π : G →* X)
    (hπ : Function.Surjective π) : Nonempty (G ⧸ Z ≃* X) := by
  obtain ⟨φ, hφ⟩ := exists_quotient_surjective hX Z hZ π hπ
  have := nontrivial_of_isShapeGroup hX
  exact nonempty_mulEquiv_of_surjective hGZ φ hφ

theorem ne_bot_of_isQuasisimple {H : Type} [Group H] {N : Subgroup H}
    (hN : CFSG.IsQuasisimple ↥N) : N ≠ ⊥ := by
  rintro rfl
  have := hN.2.1.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊥ : Subgroup H) ⧸ Subgroup.center ↥(⊥ : Subgroup H))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (congrArg _ (Subsingleton.elim x y))

theorem eq_commutator_of_isPerfect {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    [Group.IsPerfect ↥N] (hN : N ≠ ⊥) (hs : IsSimpleGroup ↥(commutator H)) :
    N = commutator H := by
  have hle : N ≤ commutator H := by
    calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := (commutator_def H).symm
  have : (N.subgroupOf (commutator H)).Normal := Subgroup.Normal.subgroupOf ‹_› _
  rcases hs.eq_bot_or_eq_top_of_normal (N.subgroupOf (commutator H)) with h | h
  · exfalso
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hle hx⟩ : ↥(commutator H)) ∈ N.subgroupOf (commutator H) := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem not_shapeCard_95040 : ¬ ShapeCard 95040 :=
  not_shapeCard_num (a := 6) (b := 1485) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_shapeCard_443520 : ¬ ShapeCard 443520 :=
  not_shapeCard_num (a := 7) (b := 3465) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_shapeCard_10200960 : ¬ ShapeCard 10200960 :=
  not_shapeCard_num (a := 7) (b := 79695) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem false_of_shapeCard_dvd_72 {N : ℕ} (h : ShapeCard N) (hd : N ∣ 72) : False := by
  have h60 := sixty_le_of_shapeCard h
  have hle := Nat.le_of_dvd (by norm_num) hd
  have h72 : N = 72 := by
    interval_cases N <;> first | rfl | (norm_num at hd)
  subst h72
  exact not_shapeCard_of (a := 3) (b := 9) (by decide) (by decide) (fun _ => by decide)
    (fun _ => by decide) ((show (72 : ℕ) = 2 ^ 3 * 9 by norm_num) ▸ h)

end CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
