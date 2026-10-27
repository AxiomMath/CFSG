module

public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace Sec121

variable {G : Type} [Group G]

theorem conjAct_eq_of_inv_mul_mem {V : Subgroup G} {x y : Subgroup.normalizer (V : Set G)}
    (h : ((x⁻¹ * y : Subgroup.normalizer (V : Set G)) : G) ∈ Subgroup.centralizer (V : Set G)) :
    conjAct V x = conjAct V y := by
  have h1 : conjAct V (x⁻¹ * y) = 1 := A4.conjAct_eq_one_iff.mpr h
  calc conjAct V x = conjAct V x * conjAct V (x⁻¹ * y) := by rw [h1, mul_one]
    _ = conjAct V y := by rw [← map_mul, mul_inv_cancel_left]

theorem isTwoReducedIn_of_cent {M L V : Subgroup G} (hVM : V ≤ M)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V) (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) (hsimp : IsSimpleGroup ↥(autOn L V))
    (h3 : 3 ∣ Nat.card (autOn L V)) [Finite ↥(autOn L V)]
    (hcent : ∀ c : MulAut ↥V, (∀ y ∈ autOn L V, c * y = y * c) → c = 1) :
    IsTwoReducedIn M V := by
  refine ⟨hVM, hMV, hV, fun D hDM hMD hD2 => ?_⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLM.trans hMV
  have hLDL : L ≤ Subgroup.normalizer ((D ⊓ L : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hMD (hLM hl)) x
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl : l ∈ _) x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hDL : D ⊓ L ≤ Subgroup.centralizer (V : Set G) := by
    set N := autOn (D ⊓ L) V with hN
    have hNle : N ≤ autOn L V := A4.autOn_mono inf_le_right
    have hNnorm : (N.subgroupOf (autOn L V)).Normal := ⟨fun k hk x => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact InternalSec.autOn_normal_of hLDL _ x.2 _ hk⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (autOn L V)) with h | h
    · intro g hg
      have hgN : g ∈ Subgroup.normalizer (V : Set G) := hLV hg.2
      have h1 : conjAct V ⟨g, hgN⟩ ∈ N := Setup.mem_autOn_iff.mpr ⟨⟨g, hgN⟩, hg, rfl⟩
      have h3 : (⟨conjAct V ⟨g, hgN⟩, hNle h1⟩ : ↥(autOn L V)) ∈ N.subgroupOf (autOn L V) :=
        Subgroup.mem_subgroupOf.mpr h1
      rw [h, Subgroup.mem_bot] at h3
      exact A4.conjAct_eq_one_iff.mp (congrArg Subtype.val h3)
    · exfalso
      have hle : autOn L V ≤ N := Subgroup.subgroupOf_eq_top.mp h
      have hp : IsPGroup 2 ↥(autOn L V) := fun y => by
        obtain ⟨g, hg, hgy⟩ := Setup.mem_autOn_iff.mp (hle y.2)
        obtain ⟨k, hk⟩ := hD2 g hg.1
        refine ⟨k, Subtype.ext ?_⟩
        rw [Subgroup.coe_pow, ← hgy, ← map_pow, Subgroup.coe_one]
        exact A4.conjAct_eq_one_iff.mpr (by rw [Subgroup.coe_pow]; exact hk)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
      rw [hk] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  intro d hd
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := hMV (hDM hd)
  have hc : conjAct V ⟨d, hdN⟩ = 1 := by
    apply hcent
    intro y hy
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hy
    rw [← map_mul, ← map_mul]
    apply conjAct_eq_of_inv_mul_mem
    apply hDL
    change (d * (g : G))⁻¹ * ((g : G) * d) ∈ D ⊓ L
    rw [mul_inv_rev]
    refine ⟨?_, ?_⟩
    · have h1 : (g : G)⁻¹ * d⁻¹ * (g : G)⁻¹⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hMD (hLM (L.inv_mem hgL))) _).mp (D.inv_mem hd)
      rw [inv_inv] at h1
      rw [show (g : G)⁻¹ * d⁻¹ * (g * d) = (g : G)⁻¹ * d⁻¹ * g * d by group]
      exact D.mul_mem h1 hd
    · have h1 : d⁻¹ * (g : G) * d⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hML (hDM (D.inv_mem hd))) _).mp hgL
      rw [inv_inv] at h1
      rw [show (g : G)⁻¹ * d⁻¹ * (g * d) = (g : G)⁻¹ * (d⁻¹ * g * d) by group]
      exact L.mul_mem (L.inv_mem hgL) h1
  exact A4.conjAct_eq_one_iff.mp hc

theorem nonempty_autOn_mulEquiv_mulAut [Finite G] {M L V : Subgroup G} (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G))
    (hcent : ∀ c : MulAut ↥V, (∀ y ∈ autOn L V, c * y = y * c) → c = 1)
    (hne : autOn L V ≠ autOn M V) {Q S : Type*} [Group Q] [Group S] [Finite S]
    (eQ : Q ≃* S) (e : ↥(autOn L V) ≃* S) (hAut : Nat.card (MulAut S) ≤ 2 * Nat.card S) :
    Nonempty (↥(autOn M V) ≃* MulAut Q) := by
  set Lb := autOn L V with hLb
  set Mb := autOn M V with hMb
  have hLbMb : Lb ≤ Mb := A4.autOn_mono hLM
  have hMbN : Mb ≤ Subgroup.normalizer (Lb : Set (MulAut ↥V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => InternalSec.autOn_normal_of hML x hx k hk, fun hk => ?_⟩
    have := InternalSec.autOn_normal_of hML x⁻¹ (Mb.inv_mem hx) _ hk
    rwa [show x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k by group] at this
  let φ : ↥Mb →* MulAut ↥Lb := Lb.normalizerMonoidHom.comp (Subgroup.inclusion hMbN)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : Subgroup.inclusion hMbN m ∈ Lb.normalizerMonoidHom.ker := hm
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      at h1
    exact Subtype.ext (hcent m fun y hy => (h1 y hy).symm)
  have hcardAut : Nat.card (MulAut ↥Lb) ≤ 2 * Nat.card Lb := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact hAut
  have hcardM : 2 * Nat.card Lb ≤ Nat.card Mb := by
    set Lb' := Lb.subgroupOf Mb with hLb'
    have h1 : Nat.card Lb' = Nat.card Lb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLbMb).toEquiv
    have h2 := Lb'.card_mul_index
    have h3 : Lb'.index ≠ 1 := fun h => hne (le_antisymm hLbMb
      (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h)))
    have h4 : Lb'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [← h2, h1]
    have : 2 ≤ Lb'.index := by omega
    calc 2 * Nat.card Lb = Nat.card Lb * 2 := mul_comm _ _
      _ ≤ Nat.card Lb * Lb'.index := Nat.mul_le_mul_left _ this
  have hbij := hφ.bijective_of_nat_card_le (hcardAut.trans hcardM)
  exact ⟨(MulEquiv.ofBijective φ hbij).trans (MulAut.congr (e.trans eQ.symm))⟩

end Sec121

end CFSG.Quasithin.H13
