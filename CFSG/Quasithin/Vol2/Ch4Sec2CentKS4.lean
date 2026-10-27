module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKS2
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKS3
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKRank
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKS1

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_pCore_of_mem_pCoreOf_lemma27 {H : Subgroup G} {w : ↥H}
    (hw : (w : G) ∈ pCoreOf 2 H) : w ∈ CFSG.pCore 2 ↥H :=
  (Subgroup.mem_map_iff_mem H.subtype_injective).1 hw

private theorem mem_pCoreOf_of_mem_pCore_lemma27 {H : Subgroup G} {w : ↥H}
    (hw : w ∈ CFSG.pCore 2 ↥H) : (w : G) ∈ pCoreOf 2 H :=
  Subgroup.mem_map_of_mem H.subtype hw

private theorem natCard_statedSL_two_dvd_of_surjective_lemma27 {Y : Subgroup G} {F : Type}
    [Field F] [Finite F] (ρ : ↥Y →* ↥(StatedSL 2 F)) (hρ : Function.Surjective ρ) :
    Nat.card ↥(StatedSL 2 F) ∣ Nat.card ↥Y := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv]
  exact dvd_mul_right _ _

private theorem prime_dvd_natCard_statedSL_two_lemma27 {F : Type} [Field F] [Fintype F] {p : ℕ}
    (hpF : p ∣ Fintype.card F - 1) : p ∣ Nat.card ↥(StatedSL 2 F) := by
  rw [CFSG.Open.StatedAPI.card_statedSL_two F, Nat.card_eq_fintype_card]
  refine Dvd.dvd.mul_left ?_ _
  have h := Nat.sub_dvd_pow_sub_pow (Fintype.card F) 1 2
  rw [one_pow] at h
  exact dvd_trans hpF h

theorem lemma27 (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK) {H K : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hKc : K ∈ cComp H) (hKN : H ≤ Subgroup.normalizer (K : Set G))
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    {Y : Subgroup G} (hYH : Y ≤ H) (hYp : ⁅Y, Y⁆ = Y)
    (ρ : ↥Y →* ↥(StatedSL 2 F)) (hρ : Function.Surjective ρ) (hρ2 : IsPGroup 2 ρ.ker) :
    Y ≤ K := by
  by_contra hYK
  obtain ⟨p, hp, hp2, hpd, hp3⟩ := exists_prime_dvd_two_pow_sub_one hn
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : p ∣ Fintype.card F - 1 := by rw [hF]; exact hpd
  have hF3 : p = 3 → Fintype.card F = 4 := fun h => by rw [hF, hp3 h] <;> norm_num
  have hdvdY : p ∣ Nat.card ↥Y :=
    dvd_trans (prime_dvd_natCard_statedSL_two_lemma27 hpF)
      (natCard_statedSL_two_dvd_of_surjective_lemma27 ρ hρ)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hdvdY
  rcases x with ⟨y₀, hy₀Y⟩
  have hρx : ρ ⟨y₀, hy₀Y⟩ ≠ 1 := by
    intro h1
    have hxk : (⟨y₀, hy₀Y⟩ : ↥Y) ∈ ρ.ker := MonoidHom.mem_ker.2 h1
    obtain ⟨j, hj⟩ := hρ2.exists_pow_pow_eq_one (⟨⟨y₀, hy₀Y⟩, hxk⟩ : ↥ρ.ker)
    have hj' : (⟨y₀, hy₀Y⟩ : ↥Y) ^ 2 ^ j = 1 := by
      simpa using congrArg Subtype.val hj
    have hdvd : p ∣ 2 ^ j := by
      have h := orderOf_dvd_of_pow_eq_one hj'
      rwa [hxord] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hy₀p : y₀ ^ p = 1 := by
    have h := pow_orderOf_eq_one (⟨y₀, hy₀Y⟩ : ↥Y)
    rw [hxord] at h
    simpa using congrArg Subtype.val h
  have hy₀KA : y₀ ∉ K ⊔ pCoreOf 2 H := fun hmem =>
    hYK (le_of_mem_sup_of_ne_one hKN hYH hYp hn hF ρ hρ hρ2 hy₀Y hρx hmem)
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hKc
  obtain ⟨K', hK'H, hcomm, hdec⟩ := exists_decomp_cComp hK hs hnab h37 h39 hH hKc hYH hYp
  obtain ⟨k, hkK, k', hk'K', hkk'⟩ := hdec y₀ hy₀Y
  obtain ⟨θ, hθinj, hθ⟩ := exists_hom_modO2 hKH hKN hα hker
  set π : ↥H →* (↥H ⧸ CFSG.pCore 2 ↥H) := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set Y₀ : ↥H := ⟨y₀, hYH hy₀Y⟩ with hY₀
  have hY₀p : Y₀ ^ p = 1 := Subtype.ext (by simpa [hY₀] using hy₀p)
  have hY₀eq : Y₀ = (⟨k, hKH hkK⟩ : ↥H) * ⟨k', hK'H hk'K'⟩ :=
    Subtype.ext (by simpa [hY₀] using hkk')
  have hyp : (π Y₀) ^ p = 1 := by rw [← map_pow, hY₀p, map_one]
  have hyK : π Y₀ ∉ θ.range := by
    rintro ⟨g, hg⟩
    obtain ⟨k₁, rfl⟩ := hα g
    have h1 : θ (α k₁) = π ⟨k₁.1, hKH k₁.2⟩ := hθ k₁.1 k₁.2
    have hw : (⟨k₁.1, hKH k₁.2⟩ : ↥H)⁻¹ * Y₀ ∈ CFSG.pCore 2 ↥H :=
      QuotientGroup.eq.1 (h1.symm.trans hg)
    apply hy₀KA
    have hy : y₀ = k₁.1 * (((⟨k₁.1, hKH k₁.2⟩ : ↥H)⁻¹ * Y₀ : ↥H) : G) := by
      simp [hY₀]
    rw [hy]
    exact Subgroup.mul_mem_sup k₁.2 (mem_pCoreOf_of_mem_pCore_lemma27 hw)
  have hc : ∀ b ∈ (K'.subgroupOf H).map π, ∀ g : ↥(StatedSL 3 F), b * θ g = θ g * b := by
    rintro b ⟨x, hx, rfl⟩ g
    obtain ⟨k₁, rfl⟩ := hα g
    have h1 : θ (α k₁) = π ⟨k₁.1, hKH k₁.2⟩ := hθ k₁.1 k₁.2
    rw [h1, ← map_mul, ← map_mul]
    apply QuotientGroup.eq.2
    apply mem_pCore_of_mem_pCoreOf_lemma27
    have hk1 : k₁.1⁻¹ ∈ K := K.inv_mem k₁.2
    have hx' : x.1⁻¹ ∈ K' := K'.inv_mem (Subgroup.mem_subgroupOf.1 hx)
    have hcm := hcomm _ hk1 _ hx'
    have hE : ((x * ⟨k₁.1, hKH k₁.2⟩)⁻¹ * (⟨k₁.1, hKH k₁.2⟩ * x) : ↥H).1 =
        ⁅k₁.1⁻¹, x.1⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [hE]
    exact hcm
  have hb' : π ⟨k', hK'H hk'K'⟩ ∈ (K'.subgroupOf H).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hk'K')
  have hyKK : ∃ (a : ↥(StatedSL 3 F)) (b : ↥H ⧸ CFSG.pCore 2 ↥H),
      b ∈ (K'.subgroupOf H).map π ∧ π Y₀ = θ a * b :=
    ⟨α ⟨k, hkK⟩, π ⟨k', hK'H hk'K'⟩, hb', by rw [hθ k hkK, hY₀eq, map_mul]⟩
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_rank_three θ hθinj ((K'.subgroupOf H).map π) hc
    hp hp2 hpF hF3 hyp hyK hyKK
  exact false_of_elemAbelian_quotient hK hH hp hp2 hE hcard

end CFSG.Quasithin.H13.Ch4.CentK
