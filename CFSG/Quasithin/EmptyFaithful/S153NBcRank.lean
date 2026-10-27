module

public import CFSG.Quasithin.EmptyFaithful.S153NBcSqtk
public import CFSG.Quasithin.Background.FFC4Three
public import CFSG.Quasithin.Background.S1567Z4

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace BridgeC

section General

theorem three_le_pRank_of_gens {X : Type} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {x y z : X} (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z) (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y)
    (hz1 : ∀ m n : ℕ, x ^ m * y ^ n ≠ z) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  set B₀ : Subgroup X := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := CFSG.SectionRank.exists_extend hc₀ hp₀ hcard₀
    B₀.subtype Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := CFSG.SectionRank.exists_extend hc₁ hp₁ hcard₁ F₁ hF₁
    (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, -⟩ := CFSG.SectionRank.exists_extend hc₂ hp₂ hcard₂ F₂ hF₂
    (y := z) hz
    (by
      rintro ⟨a, ha⟩
      obtain ⟨b, n, hn⟩ := hr₂ a
      obtain ⟨m, hm⟩ := hr₁' b
      exact hz1 m n (by rw [← hm, ← hn, ha]))
    (fun a => by
      obtain ⟨b, n, hn⟩ := hr₂ a
      obtain ⟨m, hm⟩ := hr₁' b
      rw [hn, hm]
      exact (hxz.pow_left m).mul_left (hyz.pow_left n))
  exact CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt hc₃ hp₃ hcard₃ F₃ hF₃ le_top

end General

section Rank

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem YE_inf_centralizer_le_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    YE153 Mc M E ⊓ Subgroup.centralizer (E : Set G) ≤ S1567.K167 T M E := by
  intro g hg
  refine ⟨hg.2, fun v hv => ?_⟩
  have h := Subgroup.mem_centralizer_iff.mp (S1567.YE_inf_centralizer_le_centralizer_VE h113 k hg) v hv
  have e : g * v * g⁻¹ * v⁻¹ = 1 := by rw [← h]; group
  rw [e]
  exact E.one_mem

theorem commutator_YE_centralizer_mem_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    {y c : G} (hy : y ∈ YE153 Mc M E) (hc : c ∈ Subgroup.centralizer (E : Set G)) :
    y * c * y⁻¹ * c⁻¹ ∈ S1567.K167 T M E := by
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hy
  have hcE : c ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hc
  refine YE_inf_centralizer_le_K167 h113 k ⟨?_, ?_⟩
  · have h1 : c * y⁻¹ * c⁻¹ ∈ YE153 Mc M E :=
      (Subgroup.mem_normalizer_iff.mp (S1567.normalizer_le_normalizer_YE h113 k hcE) y⁻¹).mp
        ((YE153 Mc M E).inv_mem hy)
    have e : y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) := by group
    rw [e]
    exact (YE153 Mc M E).mul_mem hy h1
  · have h1 : y * c * y⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (S1567.normalizer_le_normalizer_CE E hyE) c).mp hc
    exact (Subgroup.centralizer (E : Set G)).mul_mem h1 ((Subgroup.centralizer _).inv_mem hc)

end Rank

end BridgeC

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem bridgeC_rank (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {Q : Type} [Group Q]
    (φ : ↥(Subgroup.centralizer (E : Set G)) →* Q)
    (hker : φ.ker = (S1567.K167 T M E).subgroupOf (Subgroup.centralizer (E : Set G)))
    (h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G))) : ¬ FFC.ThreeRank2 ↥φ.range := by
  rintro ⟨a, b, ha1, ha3, hb3, hab, hb⟩
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hKC : S1567.K167 T M E ≤ Subgroup.centralizer (E : Set G) := S1567.K167_le_centralizer
  have hKN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (S1567.K167 T M E : Set G) :=
    S1567.normalizer_le_normalizer_K167 T M E
  have hKGE : S1567.K167 T M E ≤ Subgroup.normalizer (E : Set G) := hKC.trans hCN
  have hKMC : S1567.K167 T M E ≤ M ⊓ Subgroup.centralizer (E : Set G) := fun κ hκ =>
    ⟨(S1567.K167_le_M_inf_normalizer k hκ).1, hKC hκ⟩
  have hKgn : ((S1567.K167 T M E).subgroupOf (Subgroup.normalizer (E : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKGE).mpr hKN
  have hK3 : ¬ 3 ∣ Nat.card ↥((S1567.K167 T M E).subgroupOf (Subgroup.normalizer (E : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKGE).toEquiv]
    exact fun hd => h3 (hd.trans (Subgroup.card_dvd_of_le hKMC))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) _ hK3
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Subgroup.normalizer (E : Set G))) ≤ 2 :=
    (BridgeC.sqtkGroup_normalizer k).1 3 Nat.prime_three (by norm_num)
  obtain ⟨ι, hι0⟩ : ∃ ι : ↥(Subgroup.centralizer (E : Set G)) →*
      ↥(Subgroup.normalizer (E : Set G)) ⧸
        (S1567.K167 T M E).subgroupOf (Subgroup.normalizer (E : Set G)),
      ∀ c, ι c = QuotientGroup.mk' _ (Subgroup.inclusion hCN c) :=
    ⟨(QuotientGroup.mk' _).comp (Subgroup.inclusion hCN), fun _ => rfl⟩
  have hι1 : ∀ c : ↥(Subgroup.centralizer (E : Set G)), ι c = 1 ↔ φ c = 1 := by
    intro c
    have h1 : ι c = 1 ↔ (c : G) ∈ S1567.K167 T M E := by
      rw [hι0, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have h2 : φ c = 1 ↔ (c : G) ∈ S1567.K167 T M E := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rw [h1, h2]
  have hι : ∀ c d : ↥(Subgroup.centralizer (E : Set G)), ι c = ι d ↔ φ c = φ d := by
    intro c d
    rw [← inv_mul_eq_one (a := ι c), ← inv_mul_eq_one (a := φ c), ← map_inv, ← map_inv, ← map_mul,
      ← map_mul]
    exact hι1 _
  obtain ⟨y₀, hy₀Y, ⟨e₀, he₀E, hy₀e⟩, hy₀3⟩ := (Y_facts h113 k.c k.L).2
  have hy₀GE : y₀ ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hy₀Y
  have hy₀C : y₀ ∉ Subgroup.centralizer (E : Set G) := fun hc => hy₀e (by
    have := Subgroup.mem_centralizer_iff.mp hc e₀ he₀E
    rw [← this]
    group)
  have hy₀3K : y₀ ^ 3 ∈ S1567.K167 T M E :=
    BridgeC.YE_inf_centralizer_le_K167 h113 k
      ⟨(YE153 Mc M E).pow_mem hy₀Y 3, Subgroup.centralizer_le k.L.le_V hy₀3⟩
  obtain ⟨z, hz0⟩ : ∃ z : ↥(Subgroup.normalizer (E : Set G)) ⧸
      (S1567.K167 T M E).subgroupOf (Subgroup.normalizer (E : Set G)),
      z = QuotientGroup.mk' _ (⟨y₀, hy₀GE⟩ : ↥(Subgroup.normalizer (E : Set G))) := ⟨_, rfl⟩
  have hz3 : z ^ 3 = 1 := by
    rw [hz0, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy₀3K
  have hzc : ∀ c : ↥(Subgroup.centralizer (E : Set G)), Commute (ι c) z := by
    intro c
    have h1 := BridgeC.commutator_YE_centralizer_mem_K167 h113 k ((YE153 Mc M E).inv_mem hy₀Y)
      ((Subgroup.centralizer (E : Set G)).inv_mem c.2)
    show ι c * z = z * ι c
    rw [hι0, hz0, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((Subgroup.inclusion hCN c * ⟨y₀, hy₀GE⟩)⁻¹ * (⟨y₀, hy₀GE⟩ * Subgroup.inclusion hCN c) :
        ↥(Subgroup.normalizer (E : Set G))) : G) =
        y₀⁻¹ * (c : G)⁻¹ * y₀⁻¹⁻¹ * (c : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, inv_inv]
      group
    rw [e]
    exact h1
  have hz_nr : ∀ c : ↥(Subgroup.centralizer (E : Set G)), ι c ≠ z := by
    intro c hc
    rw [hι0, hz0, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hc
    have h1 : (c : G)⁻¹ * y₀ ∈ Subgroup.centralizer (E : Set G) := hKC hc
    apply hy₀C
    have := (Subgroup.centralizer (E : Set G)).mul_mem c.2 h1
    simpa using this
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
  have ha3' : (a : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val ha3
  have hb3' : (b : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hb3
  have hx3 : (ι x) ^ 3 = 1 := by
    rw [← map_pow, hι1, map_pow, hx]
    exact ha3'
  have hy3 : (ι y) ^ 3 = 1 := by
    rw [← map_pow, hι1, map_pow, hy]
    exact hb3'
  have hxy : Commute (ι x) (ι y) := by
    show ι x * ι y = ι y * ι x
    rw [← map_mul, ← map_mul, hι, map_mul, map_mul, hx, hy]
    simpa using congrArg Subtype.val hab
  have hx1 : ι x ≠ 1 := fun h => ha1 (Subtype.ext (by rw [← hx]; exact (hι1 x).mp h))
  have hy1 : ∀ n : ℕ, (ι x) ^ n ≠ ι y := fun n h => by
    rw [← map_pow, hι, map_pow, hx, hy] at h
    have hba : b = a ^ n := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h.symm)
    exact hb (hba ▸ Subgroup.npow_mem_zpowers a n)
  have hz1 : ∀ m n : ℕ, (ι x) ^ m * (ι y) ^ n ≠ z := fun m n h =>
    hz_nr (x ^ m * y ^ n) (by rw [map_mul, map_pow, map_pow]; exact h)
  have h3rk := BridgeC.three_le_pRank_of_gens (p := 3) hx3 hy3 hz3 hxy (hzc x) (hzc y) hx1 hy1 hz1
  omega

end Main

end CFSG.Quasithin.S153N
