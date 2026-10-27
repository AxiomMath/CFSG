module

public import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {L Q H : Subgroup G}

theorem sup_inf_centralizer_sup_eq_of_coprime
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card Q))
    (hcomm : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ * l⁻¹ ∈ Q) :
    Q ⊔ ((L ⊓ Subgroup.centralizer (H : Set G)) ⊔ H) = L ⊔ H := by
  rw [← sup_assoc, sup_inf_centralizer_eq_of_coprime hQL hLQ hHQ hcop hcomm]

private theorem le_normalizer_inf_centralizer :
    H ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh k hk
  have hc : h * k = k * h :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 h hh
  rwa [show h * k * h⁻¹ = k by rw [hc]; group]

theorem inf_inf_centralizer_sup_eq_bot (hQL : Q ≤ L)
    (hfix : ∀ x ∈ Q, (∀ h ∈ H, h * x * h⁻¹ = x) → x = 1)
    (hHL : H ⊓ L = ⊥) :
    Q ⊓ ((L ⊓ Subgroup.centralizer (H : Set G)) ⊔ H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxKH⟩ := Subgroup.mem_inf.mp hx
  have hnormK : H ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer
  obtain ⟨k, hkK, h, hhH, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hnormK).mp hxKH
  have hhL : h ∈ L := by
    have he : h = k⁻¹ * (k * h) := by group
    rw [he]
    exact L.mul_mem (L.inv_mem hkK.1) (hQL hxQ)
  have hh1 : h = 1 := by
    have hmem : h ∈ H ⊓ L := ⟨hhH, hhL⟩
    rwa [hHL, Subgroup.mem_bot] at hmem
  have hkQ : k ∈ Q := by
    rw [hh1, mul_one] at hxQ
    exact hxQ
  have hk1 : k = 1 := by
    have hmem : k ∈ L ⊓ Subgroup.centralizer (H : Set G) ⊓ Q := ⟨hkK, hkQ⟩
    rw [inf_centralizer_inf_eq_bot_of_fixed (L := L) (Q := Q) (H := H) hfix,
      Subgroup.mem_bot] at hmem
    exact hmem
  rw [hk1, hh1, one_mul]
  exact Subgroup.one_mem _

theorem inf_centralizer_sup_le_normalizer
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    (L ⊓ Subgroup.centralizer (H : Set G)) ⊔ H ≤ Subgroup.normalizer (Q : Set G) :=
  sup_le (inf_le_left.trans hLQ) hHQ

theorem card_inf_centralizer_sup (hHL : H ⊓ L = ⊥) :
    Nat.card ↥((L ⊓ Subgroup.centralizer (H : Set G)) ⊔ H) =
      Nat.card ↥(L ⊓ Subgroup.centralizer (H : Set G)) * Nat.card H := by
  have hHK : H ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer
  have hdisj : Disjoint (L ⊓ Subgroup.centralizer (H : Set G)) H := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨⟨hxL, -⟩, hxH⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ H ⊓ L := ⟨hxH, hxL⟩
    rw [hHL, Subgroup.mem_bot] at hmem
    rwa [Subgroup.mem_bot]
  exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (A := L ⊓ Subgroup.centralizer (H : Set G)) (B := H) hHK hdisj

theorem sup_bigB_inf_centralizer_le_left_of_le {L1 L2 S : Subgroup G}
    (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2) :
    (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer (pCoreOf 2 L1 : Set G) ≤ pCoreOf 2 L1 := by
  have hPchar : L1 ⊔ S ⊔ borelOf L2 S = L1 ⊔ bigB L1 L2 S := by
    rw [sup_eq_left.mpr hS1,
      sup_bigB_left_of_le (L1 := L1) (L2 := L2) (S := S) hS1]
  have h := hH.h1.charTwo
  change (L1 ⊔ S ⊔ borelOf L2 S) ⊓
    Subgroup.centralizer (pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) : Set G) ≤
      pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) at h
  rw [hPchar, pCoreOf_sup_bigB_left_of_le (L1 := L1) (L2 := L2) (S := S) hH hS1 hS2] at h
  exact h

end CFSG.Quasithin.F112R.St84

end
