module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A
public import CFSG.Quasithin.Vol2.Ch4Sec4L448

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_surj_of_isHat [Finite G] {K : Subgroup G}
    (h : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (NativeSporadic.Carrier .M22)) :
    ∃ g : ↥K →* NativeSporadic.Carrier .M22, Function.Surjective g ∧
      Group.IsSolvable ↥g.ker := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K with hQ
  set π₁ : ↥K →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ₁
  set π₂ : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hπ₂
  set g : ↥K →* NativeSporadic.Carrier .M22 := e.toMonoidHom.comp (π₂.comp π₁) with hg
  refine ⟨g, e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)), ?_⟩
  have hmem : ∀ x : ↥g.ker, π₁ (x : ↥K) ∈ Subgroup.center Q := by
    intro x
    have hx : e (π₂ (π₁ x)) = 1 := x.2
    rw [MulEquiv.map_eq_one_iff, hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  set f : ↥g.ker →* ↥(Subgroup.center Q) := (π₁.comp g.ker.subtype).codRestrict _ hmem with hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : IsPGroup 2 ↥f.ker := by
    intro y
    have hy : π₁ ((y : ↥g.ker) : ↥K) = 1 := congrArg Subtype.val y.2
    rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨_, hy⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have : Group.IsNilpotent ↥f.ker := hk.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

omit [Finite G] in
theorem two_le_pRank_of_le_ker {K : Subgroup G} {S : Type} [Group S] [Finite S]
    (g : ↥K →* S) (hg : Function.Surjective g) (hS : 2 ≤ CFSG.pRank 3 S)
    {Q : Type} [Group Q] [Finite Q] (f : ↥K →* Q) (hf : ∀ k, f k = 1 → g k = 1) :
    2 ≤ CFSG.Open.pRank 3 f.range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : f.ker ≤ g.ker := fun k hk => hf k hk
  set h : ↥f.range →* S := (QuotientGroup.lift f.ker g hle).comp
    (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom with hh
  have hhs : Function.Surjective h := by
    intro s
    obtain ⟨k, rfl⟩ := hg s
    refine ⟨⟨f k, k, rfl⟩, ?_⟩
    have e : (QuotientGroup.quotientKerEquivRange f).symm ⟨f k, k, rfl⟩ = (k : ↥K ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hh, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, QuotientGroup.lift_mk]
  refine T425C27.two_le_pRank_of_surjective h hhs (by norm_num) ?_
  rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top]

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  intro x hx
  have hxz : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hx
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((hxz.zpow_right n).eq).symm

omit [Finite G] in
theorem zpowers_ne_bot {z : G} (hz : z ≠ 1) : Subgroup.zpowers z ≠ ⊥ := fun h => hz (by
  have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rwa [h, Subgroup.mem_bot] at this)

omit [Finite G] in
theorem isPGroup_zpowers {z : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz, pow_one])

theorem coprime_six (hqtke : quasithinIsQTKECat G) {K KZ B : Subgroup G} {z : G}
    (hE : 2 ≤ CFSG.Open.pRank 3 KZ) (hKZK : KZ ≤ K)
    (hKZz : KZ ≤ Subgroup.centralizer ({z} : Set G))
    (hBz : B ≤ Subgroup.centralizer ({z} : Set G)) (hBK : B ≤ Subgroup.centralizer (K : Set G))
    (hBK1 : B ⊓ K = ⊥) (hBodd : Odd (Nat.card B)) (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Nat.Coprime (Nat.card B) 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.coprime_mul_iff_right]
  refine ⟨((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h => by
    rcases hBodd with ⟨k, hk⟩
    omega).symm, ?_⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hb' : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe, hb]
  obtain ⟨E, hEKZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hE
  have hbE : (b : G) ∉ E := by
    intro hbE
    have h1 : (b : G) ∈ B ⊓ K := ⟨b.2, hKZK (hEKZ hbE)⟩
    rw [hBK1, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hb'
    exact absurd hb' (by norm_num)
  have hcomm : ∀ e ∈ E, Commute e (b : G) := fun e he =>
    Subgroup.mem_centralizer_iff.mp (hBK b.2) e (hKZK (hEKZ he))
  obtain ⟨hE', hcard⟩ := exists_elemAbelian_sup_zpowers hEab hb' hcomm hbE
  set P := Subgroup.zpowers z with hP
  have hCN := centralizer_le_normalizer_zpowers z
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) :=
    ⟨P, zpowers_ne_bot hz, isPGroup_zpowers hz hz2, rfl⟩
  have hle : E ⊔ Subgroup.zpowers (b : G) ≤ Subgroup.normalizer (P : Set G) :=
    sup_le ((hEKZ.trans hKZz).trans hCN) (Subgroup.zpowers_le.mpr (hCN (hBz b.2)))
  have h3' := le_pRank Nat.prime_three hle hE' (k := 3) (by rw [hcard, hEcard]; norm_num)
  have h2 := pRank_le_two_of_isTwoLocal hqtke Nat.prime_three (by norm_num) hloc
  omega

end CFSG.Quasithin.H13.Ch4.G443J4
