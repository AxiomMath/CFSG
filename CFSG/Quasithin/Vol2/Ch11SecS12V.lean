module

public import CFSG.Quasithin.Vol2.Ch11SecS12N
public import CFSG.Quasithin.Vol2.Ch11SecS12U
public import CFSG.Quasithin.Vol2.Ch11SecS12Z
public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open hiding StatedSL
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

theorem lemmaB414Head_aux (hC : H13.Ch4.LemmaB414Corrected) {G : Type} [Group G] [Finite G]
    {Γ V Z L X : Subgroup G} {F : Type} [Field F] [Fintype F] (hF4 : Fintype.card F = 4)
    (hΓV : Γ ≤ Subgroup.normalizer (V : Set G)) (hΓZ : Γ ≤ Subgroup.normalizer (Z : Set G))
    (hZV : Z < V) (hsq : ∀ v ∈ V, v ^ 2 ∈ Z) (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ Z)
    (hirr : ∀ J : Subgroup G, Z ≤ J → J ≤ V → Γ ≤ Subgroup.normalizer (J : Set G) →
      J = Z ∨ J = V)
    (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) (α : ↥Γ →* PGL3 F) (hα : Function.Surjective α)
    (h3 : ∀ γ : ↥Γ, α γ = 1 → ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z)
    (h4 : ∃ γ : ↥Γ, α γ ∈ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ ∧
      ∃ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∉ Z)
    (hperf : ⁅(L.subgroupOf Γ).map α, (L.subgroupOf Γ).map α⁆ = (L.subgroupOf Γ).map α)
    (hne : (L.subgroupOf Γ).map α ≠ ⊥)
    (hneR : (L.subgroupOf Γ).map α ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆)
    (hS : ∃ S : Subgroup (PGL3 F), QuasithinUnique.IsSylowTwoOf S ⊤ ∧
      S ≤ Subgroup.normalizer (((L.subgroupOf Γ).map α : Subgroup (PGL3 F)) : Set (PGL3 F)))
    (hX3 : Nat.card ↥((X.subgroupOf Γ).map α) = 3)
    (hXL : ∀ y ∈ X, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    (α₀ : ↥L →* ↥(StatedSL 2 F)) (hα₀ : Function.Surjective α₀)
    (hker : α₀.ker = (pCoreOf 2 L).subgroupOf L)
    (γx : ↥Γ) (hγxX : (γx : G) ∈ X) (hγx1 : α γx ≠ 1)
    (hser : ∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V) :
    ∃ (μ : F) (j : ℕ), j < 3 ∧ μ ^ 3 = 1 ∧
      (∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V ∧
        labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F)) ∧
      (j = 0 → ∀ J : Subgroup G, ⁅V, pCoreOf 2 L⁆ ⊔ Z ≤ J → J ≤ V →
        (∀ v ∈ V, (γx : G) * v * (γx : G)⁻¹ * v⁻¹ ∈ J) → J = V) := by
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF4]
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hF]; norm_num)
  obtain ⟨S, hS, hSA⟩ := hS
  obtain ⟨c, j₀, hS0, hcj⟩ := exists_conj_Ptheta hF hS hSA hne hperf hneR
  obtain ⟨α', hα'⟩ : ∃ α' : ↥Γ →* PGL3 F, α' = (MulAut.conj c).toMonoidHom.comp α := ⟨_, rfl⟩
  have hα's : Function.Surjective α' := by
    rw [hα']
    exact (MulAut.conj c).surjective.comp hα
  have hα'1 : ∀ γ, α' γ = 1 ↔ α γ = 1 := fun γ => by
    rw [hα', MonoidHom.comp_apply]
    exact (MulAut.conj c).map_eq_one_iff
  have hα'L : (L.subgroupOf Γ).map α' = Ptheta F j₀ := by
    rw [hα', ← Subgroup.map_map]
    exact hcj
  have hX3' : Nat.card ↥((X.subgroupOf Γ).map α') = 3 := by
    rw [hα', ← Subgroup.map_map, Subgroup.card_map_of_injective (MulAut.conj c).injective, hX3]
  set P := Subgroup.normalizer (Ptheta F j₀ : Set (PGL3 F)) with hP
  have hPmax := isMaxParabolic2_normalizer_Ptheta hS0 hF j₀
  have hPc : perfectCore P = Ptheta F j₀ := perfectCore_normalizer_Ptheta hS0 hF j₀
  have hLP : (L.subgroupOf Γ).map α' = perfectCore P := hα'L.trans hPc.symm
  have hkerα : ∀ γ : ↥Γ, α' γ = 1 ↔ ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z := fun γ =>
    (hα'1 γ).trans (ker_iff hF α hα hΓV hΓZ h3 h4 γ)
  have hXN : ∀ y : ↥Γ, (y : G) ∈ X → (y : G) ∈ Subgroup.normalizer (L : Set G) := fun _ hy =>
    mem_normalizer_of_comm hXL hy
  have hXP : (X.subgroupOf Γ).map α' ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    have := map_mem_normalizer α' L (hXN y (Subgroup.mem_subgroupOf.mp hy))
    rwa [hα'L] at this
  have hcent : ∀ x ∈ (X.subgroupOf Γ).map α', ∀ l ∈ (L.subgroupOf Γ).map α',
      x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 ((L.subgroupOf Γ).map α') := by
    rintro _ ⟨y, hy, rfl⟩ l hl
    have hy' := Subgroup.mem_subgroupOf.mp hy
    exact (map_mem_sectionCentralizer α' hLΓ (hXN y hy') (hXL _ hy')).2.2 l hl
  obtain ⟨lser, hlser⟩ := hser
  obtain ⟨⟨k, hk3, hkA⟩, hall⟩ := hC G Γ V Z L X F hF4 hΓV hΓZ hZV hsq hab hirr hLΓ hXΓ α' hα's
    hkerα P hPmax hLP hXP hX3' hcent (isNaturalSection_of_labSeries hα₀ hab hlser)
  obtain ⟨-, -, j, hj3, hj0, -, heig⟩ := hall k hk3 hkA
  obtain ⟨α₀', hα₀'s, hα₀'k, hα₀'c⟩ := exists_levi hF hLΓ α' hLP (perfectCore_perfect P)
    (by rw [hPc]; exact Ptheta_ne_bot hF j₀) α₀ hα₀ hker
  have hγx' : α' γx ≠ 1 := fun h => hγx1 ((hα'1 γx).mp h)
  obtain ⟨μ, hμ, l, hl, hlm⟩ := heig α₀' hα₀'s hα₀'k α₀ hα₀'c γx hγxX hγx'
  have hγ3 : α' γx ^ 3 = 1 := map_pow_three α' hγxX hX3'
  have hμ3 : μ ^ 3 = 1 := by
    refine pow_three_eq_one_of_isNatEig hμ hγ3 ?_
    have := map_mem_normalizer α' L (hXN γx hγxX)
    rw [hLP] at this
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ this
  refine ⟨μ, j, hj3, hμ3, ⟨l, hl, hlm⟩, fun hj0' J hJ hJV hxJ => ?_⟩
  obtain rfl : k = 0 := hj0.mp hj0'
  obtain ⟨-, -, α₂, hα₂s, hα₂k, β, hβsl, hβon, hβker, hβact⟩ := hkA
  exact head_of_adjoint hF hΓV hLΓ hXL α' hα's hS0 hα'L α₀ hα₀ hker hγxX hγ3 hγx' α₂ hα₂s hα₂k β
    (fun v => AddMonoidHom.mem_ker.mp (hβsl v)) (fun M hM => hβon M (AddMonoidHom.mem_ker.mpr hM))
    (fun v => by rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf])
    (fun γ u v huv g hg => by rw [hβact γ u v huv g hg, H13.Ch4.twAdj, pow_zero, one_smul])
    hJ hJV hxJ

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

theorem lemmaB414Head_of (hC : H13.Ch4.LemmaB414Corrected) : LemmaB414Head := by
  intro G _ _ Γ V Z L X F _ _ hF4 hΓV hΓZ hZV hsq hab hirr hLΓ hXΓ α hα h3 h4 hperf hne hneR hS
    hX3 hXL α₀ hα₀ hker γx hγxX hγx1 hser
  exact lemmaB414Head_aux hC hF4 hΓV hΓZ hZV hsq hab hirr hLΓ hXΓ α hα h3 h4 hperf hne hneR hS hX3
    hXL α₀ hα₀ hker γx hγxX hγx1 hser

theorem obl11_1_2StarSL3_of_corrected (hB : H13.Ch4.LemmaB414Corrected)
    (hAb : Obl11_1_2StarSL3Ab) (hC : CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) : Obl11_1_2StarSL3 :=
  obl11_1_2StarSL3_of (lemmaB414Head_of hB) hAb hC hN hG2 hFb h1102 h1103

end CFSG.Quasithin.Vol2.Ch11.SecS
