module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Block

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem exists_centralized_ne_one {p : ℕ} [Fact p.Prime] [Finite G] {P W : Subgroup G}
    (hP : IsPGroup p P) (hW : IsPGroup p W) (hPW : P ≤ Subgroup.normalizer (W : Set G))
    (hW1 : W ≠ ⊥) : ∃ w ∈ W, w ≠ 1 ∧ ∀ g ∈ P, g * w = w * g := by
  classical
  let _ : MulAction P W := MulAction.compHom W (conjAut hPW)
  have hmod := hP.card_modEq_card_fixedPoints (α := W)
  have hpW : p ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := hW.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hW1 (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self p hn0
  have hpF : p ∣ Nat.card (MulAction.fixedPoints P W) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpW))
  have hFpos : 0 < Nat.card (MulAction.fixedPoints P W) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, fun m => map_one (conjAut hPW m)⟩⟩, inferInstance⟩
  have hFp : p ≤ Nat.card (MulAction.fixedPoints P W) := Nat.le_of_dvd hFpos hpF
  obtain ⟨r, hrF, hr1⟩ : ∃ r : W, r ∈ MulAction.fixedPoints P W ∧ r ≠ 1 := by
    by_contra hne
    push Not at hne
    have : Nat.card (MulAction.fixedPoints P W) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨fun a b => Subtype.ext ?_⟩
      rw [hne a a.2, hne b b.2]
    have := (Fact.out : p.Prime).two_le
    omega
  refine ⟨r, r.2, fun h => hr1 (Subtype.ext h), fun g hg => ?_⟩
  have := MulAction.mem_fixedPoints.mp hrF ⟨g, hg⟩
  have h2 : g * (r : G) * g⁻¹ = (r : G) := congrArg Subtype.val this
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem commutator_mem_blockQ_of_alt3 [Finite G] {X : Subgroup G} (halt : IsAltType X 3) {z : G}
    (hzN : z ∈ Subgroup.normalizer (X : Set G)) {k : G} (hk : k ∈ X) (hkQ : k ∉ blockQ X)
    (hkz : k * z = z * k) : ∀ l ∈ X, z * l * z⁻¹ * l⁻¹ ∈ blockQ X := by
  obtain ⟨α, hαs, hαk, -⟩ := halt
  have hk' : (⟨k, hk⟩ : ↥X) ∉ CFSG.pCore 2 ↥X := fun h => hkQ ((mem_blockQ_iff_pCore ⟨k, hk⟩).mpr h)
  have hα1 : α ⟨k, hk⟩ ≠ 1 := fun h => hk' (hαk ▸ h)
  have hcard3 : Nat.card (alternatingGroup (Fin 3)) = 3 := S15221.card_alternatingGroup_three
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro l hl
  obtain ⟨i, hi⟩ : α ⟨l, hl⟩ ∈ Subgroup.zpowers (α ⟨k, hk⟩) :=
    mem_zpowers_of_prime_card hcard3 hα1
  have hq : (⟨l, hl⟩ : ↥X) * ⟨k, hk⟩ ^ (-i) ∈ CFSG.pCore 2 ↥X := by
    rw [← hαk, MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, ← hi]
    simp
  have hqQ : l * k ^ (-i) ∈ blockQ X := (mem_blockQ_iff_pCore _).mpr hq
  have hzQ : z ∈ Subgroup.normalizer (blockQ X : Set G) := C1.mem_normalizer_blockQ hzN
  have hzq : z * (l * k ^ (-i)) * z⁻¹ ∈ blockQ X := (Subgroup.mem_normalizer_iff.mp hzQ _).mp hqQ
  have hzk : ∀ j : ℤ, z * k ^ j = k ^ j * z := fun j => ((Commute.zpow_left
    (show Commute k z from hkz) j)).eq.symm
  have hl_eq : l = (l * k ^ (-i)) * k ^ i := by
    rw [mul_assoc, ← zpow_add]
    simp
  have hc : z * k ^ i * z⁻¹ = k ^ i := by rw [hzk i]; group
  have key : z * l * z⁻¹ * l⁻¹ = (z * (l * k ^ (-i)) * z⁻¹) * (l * k ^ (-i))⁻¹ := by
    conv_lhs => rw [hl_eq]
    calc z * (l * k ^ (-i) * k ^ i) * z⁻¹ * (l * k ^ (-i) * k ^ i)⁻¹
        = (z * (l * k ^ (-i)) * z⁻¹) * (z * k ^ i * z⁻¹) * (k ^ i)⁻¹ * (l * k ^ (-i))⁻¹ := by
          group
      _ = _ := by rw [hc]; group
  rw [key]
  exact mul_mem hzq (inv_mem hqQ)

end CFSG.Quasithin.S15223
