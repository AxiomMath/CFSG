module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7E

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

theorem mem_pCore_of_mem_ker {Q : Type} [Group Q] [Finite Q]
    (hA7 : IsAlt 7 (Q ⧸ CFSG.pCore 2 Q) ∨
      IsHat (Q ⧸ CFSG.pCore 2 Q) ↥(alternatingGroup (Fin 7)))
    {K : Subgroup Q} [K.Normal] (hpK : CFSG.pCore 2 Q ≤ K) (hK : K ≠ ⊤) {x : Q} (hx : x ∈ K)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ CFSG.pCore 2 Q := by
  set N := K.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) with hN
  have hNn : N.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hNt : N ≠ ⊤ := by
    intro h
    apply hK
    have hc : N.comap (QuotientGroup.mk' (CFSG.pCore 2 Q)) = K := by
      rw [hN, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hpK]
    rw [← hc, h, Subgroup.comap_top]
  have hle := Ch11.SecA.le_center_of_normal_ne_top (K7.isQuasisimple_A7 hA7) hNt
  have hxc : QuotientGroup.mk' (CFSG.pCore 2 Q) x ∈
      Subgroup.center (Q ⧸ CFSG.pCore 2 Q) := hle ⟨x, hx, rfl⟩
  have hc : Nat.card (Subgroup.center (Q ⧸ CFSG.pCore 2 Q)) ∣ 3 := by
    rcases hA7 with hA | hH
    · rw [K7.center_eq_bot_of_isAlt hA, Subgroup.card_bot]
      exact one_dvd 3
    · rw [hH.2.1]
  have ho1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Q) x) ∣ 3 :=
    (Subgroup.orderOf_dvd_natCard _ hxc).trans hc
  have ho2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Q) x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Q) x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop ho1 ho2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

variable {G : Type} [Group G] [Finite G]

theorem card_modO2Image_le {X B W : Subgroup G} (hBX : B ≤ X)
    (hBW : B ≤ Subgroup.normalizer (W : Set G))
    (hk : ∀ b ∈ B, b ∈ Subgroup.centralizer (W : Set G) → b ∈ pCoreOf 2 X) :
    Nat.card ↥(modO2Image X B) ≤ Nat.card ↥(autOn B W) := by
  set φ₁ : ↥B →* ↥(modO2Image X B) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hBX)).codRestrict _
      fun b => ⟨⟨b, hBX b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩ with hφ₁
  have hs₁ : Function.Surjective φ₁ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  set φ₂ := InternalSec.autOnHom hBW with hφ₂
  have hs₂ := InternalSec.autOnHom_surjective hBW
  have hker : φ₂.ker ≤ φ₁.ker := by
    intro b hb
    rw [InternalSec.mem_ker_autOnHom] at hb
    obtain ⟨y, hy, hyb⟩ := hk b b.2 hb
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hBX b.2⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have : (⟨b, hBX b.2⟩ : ↥X) = y := Subtype.ext hyb.symm
    rw [this]
    exact hy
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ₁.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ₂.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ₁ hs₁).toEquiv] at h1
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ₂ hs₂).toEquiv] at h2
  have h3 : Nat.card φ₂.ker ≤ Nat.card φ₁.ker := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card φ₁.ker := Nat.card_pos
  have h4 : Nat.card ↥(modO2Image X B) * Nat.card φ₁.ker ≤
      Nat.card ↥(autOn B W) * Nat.card φ₁.ker := by
    rw [← h1, h2]
    exact Nat.mul_le_mul_left _ h3
  exact Nat.le_of_mul_le_mul_right h4 hpos

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
