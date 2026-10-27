module

public import CFSG.Quasithin.Vol2.Ch3T326PF
public import CFSG.Quasithin.Vol2.Ch3T326PE

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem card_dvd_five_of_le {G : Type} [Group G] {R : Subgroup G} (hR : IsPGroup 5 ↥R)
    (hfin : Finite ↥R) (h16 : Nat.card ↥R ≤ 16) : Nat.card ↥R ∣ 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  rw [hm] at h16 ⊢
  have hm1 : m ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : 5 ^ 2 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases m <;> norm_num

theorem pow_five_eq_one_of_dvd {G : Type} [Group G] [Finite G] (h5 : Nat.card G ∣ 5) (x : G) :
    x ^ 5 = 1 := by
  obtain ⟨m, hm⟩ := h5
  rw [hm, pow_mul, pow_card_eq_one', one_pow]

theorem mul_comm_of_dvd_five {G : Type} [Group G] [Finite G] (h5 : Nat.card G ∣ 5) (x y : G) :
    x * y = y * x := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h5 with h1 | h1
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · have : IsCyclic G := isCyclic_of_prime_card h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
    exact (Commute.zpow_zpow_self g a b).eq

namespace O2Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (h : O2Sit M Mp T L V t)
include h

theorem five_subgroup {P : Subgroup (MulAut W)}
    (hPC : P ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) (hP5 : IsPGroup 5 ↥P) :
    (∀ g ∈ P, g ^ 5 = 1) ∧ (∀ g ∈ P, ∀ g' ∈ P, g * g' = g' * g) ∧ Nat.card ↥P ≤ 25 := by
  have hM := h.hB.hD.hyp.Mp_normal
  let _i := qAct hM
  have hPM : P ≤ M := hPC.trans inf_le_left
  set P₀ := P.subgroupOf M with hP₀
  have hP₀5 : IsPGroup 5 ↥P₀ := hP5.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hPC₀ : ∀ g ∈ P₀, ((g : ↥M) : MulAut W) ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
    fun g hg => hPC (Subgroup.mem_subgroupOf.1 hg)
  have hPX₁ : ∀ g ∈ P₀, ∀ l ∈ L, ((g : ↥M) : MulAut W) * l = l * ((g : ↥M) : MulAut W) :=
    fun g hg => h.comm_L (hPC₀ g hg)
  have hPX₂ : ∀ g ∈ P₀, ∀ l ∈ conjAutSub t L,
      ((g : ↥M) : MulAut W) * l = l * ((g : ↥M) : MulAut W) :=
    fun g hg => h.comm_Lt (hPC₀ g hg)
  have hPY₁ : ∀ g ∈ P₀, ∀ q ∈ tilde Mp ⊤ (commV L), g • q ∈ tilde Mp ⊤ (commV L) := by
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (mem_normalizer_of_comm (hPX₁ g hg)) u hu, rfl⟩
  have hPY₂ : ∀ g ∈ P₀, ∀ q ∈ tilde Mp ⊤ (commV (conjAutSub t L)),
      g • q ∈ tilde Mp ⊤ (commV (conjAutSub t L)) := by
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem (mem_normalizer_of_comm (hPX₂ g hg)) u hu, rfl⟩
  set ρ₁ := resJ P₀ (tilde Mp ⊤ (commV L)) hPY₁ with hρ₁
  set ρ₂ := resJ P₀ (tilde Mp ⊤ (commV (conjAutSub t L))) hPY₂ with hρ₂
  have hd₁ : Nat.card ↥ρ₁.range ∣ 5 := card_dvd_five_of_le
    (hP₀5.of_surjective ρ₁.rangeRestrict ρ₁.rangeRestrict_surjective) inferInstance
    (card_range_le_sixteen h.hB.exp h.side hP₀5 hPX₁ hPY₁)
  have hd₂ : Nat.card ↥ρ₂.range ∣ 5 := card_dvd_five_of_le
    (hP₀5.of_surjective ρ₂.rangeRestrict ρ₂.rangeRestrict_surjective) inferInstance
    (card_range_le_sixteen h.hB.exp h.side' hP₀5 hPX₂ hPY₂)
  have htriv : ∀ g : ↥P₀, ρ₁ g = 1 → ρ₂ g = 1 → ((g : ↥M) : MulAut W) = 1 := by
    intro g h1 h2
    have hgM := ((g : ↥M)).2
    refine h.eq_one_of_triv (triv_of_tilde hM h.hZ hgM
      (mem_normalizer_of_comm (hPX₁ g g.2)) fun q hq => ?_)
      (triv_of_tilde hM h.inf_fixV_Lt hgM (mem_normalizer_of_comm (hPX₂ g g.2)) fun q hq => ?_)
    · exact congrArg (fun e : MulAut ↥(tilde Mp ⊤ (commV L)) =>
        ((e ⟨q, hq⟩ : ↥(tilde Mp ⊤ (commV L))) : W ⧸ modFix Mp (⊤ : Subgroup W))) h1
    · exact congrArg (fun e : MulAut ↥(tilde Mp ⊤ (commV (conjAutSub t L))) =>
        ((e ⟨q, hq⟩ : ↥(tilde Mp ⊤ (commV (conjAutSub t L)))) :
          W ⧸ modFix Mp (⊤ : Subgroup W))) h2
  have hmem : ∀ g (hg : g ∈ P), (⟨g, hPM hg⟩ : ↥M) ∈ P₀ := fun g hg =>
    Subgroup.mem_subgroupOf.2 hg
  refine ⟨fun g hg => ?_, fun g hg g' hg' => ?_, ?_⟩
  · set g₀ : ↥P₀ := ⟨⟨g, hPM hg⟩, hmem g hg⟩ with hg₀
    have e₁ : ρ₁ (g₀ ^ 5) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val (pow_five_eq_one_of_dvd hd₁ ⟨ρ₁ g₀, g₀, rfl⟩)
    have e₂ : ρ₂ (g₀ ^ 5) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val (pow_five_eq_one_of_dvd hd₂ ⟨ρ₂ g₀, g₀, rfl⟩)
    simpa using htriv (g₀ ^ 5) e₁ e₂
  · set g₀ : ↥P₀ := ⟨⟨g, hPM hg⟩, hmem g hg⟩ with hg₀
    set g₀' : ↥P₀ := ⟨⟨g', hPM hg'⟩, hmem g' hg'⟩ with hg₀'
    have c₁ : ρ₁ g₀ * ρ₁ g₀' = ρ₁ g₀' * ρ₁ g₀ :=
      congrArg Subtype.val (mul_comm_of_dvd_five hd₁ ⟨ρ₁ g₀, g₀, rfl⟩ ⟨ρ₁ g₀', g₀', rfl⟩)
    have c₂ : ρ₂ g₀ * ρ₂ g₀' = ρ₂ g₀' * ρ₂ g₀ :=
      congrArg Subtype.val (mul_comm_of_dvd_five hd₂ ⟨ρ₂ g₀, g₀, rfl⟩ ⟨ρ₂ g₀', g₀', rfl⟩)
    have e₁ : ρ₁ (g₀ * g₀' * (g₀' * g₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, c₁]
      exact mul_inv_cancel _
    have e₂ : ρ₂ (g₀ * g₀' * (g₀' * g₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, c₂]
      exact mul_inv_cancel _
    have h3 := htriv _ e₁ e₂
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    exact mul_inv_eq_one.1 h3
  · have hinj : Function.Injective (ρ₁.rangeRestrict.prod ρ₂.rangeRestrict) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have h1 : ρ₁ g = 1 := congrArg Subtype.val (congrArg Prod.fst hg)
      have h2 : ρ₂ g = 1 := congrArg Subtype.val (congrArg Prod.snd hg)
      exact Subtype.ext (Subtype.ext (htriv g h1 h2))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod] at h1
    have h2 : Nat.card ↥P = Nat.card ↥P₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv.symm
    have h3 := Nat.le_of_dvd (by norm_num) hd₁
    have h4 := Nat.le_of_dvd (by norm_num) hd₂
    rw [h2]
    calc Nat.card ↥P₀ ≤ Nat.card ↥ρ₁.range * Nat.card ↥ρ₂.range := h1
      _ ≤ 5 * 5 := Nat.mul_le_mul h3 h4

end O2Sit

end CFSG.Quasithin.H13.T326
