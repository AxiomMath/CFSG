module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepTauLt
public import CFSG.Quasithin.Background.GoldschmidtB69DeepTwist
public import CFSG.Quasithin.Background.GoldschmidtB69DeepA6
public import CFSG.Quasithin.Background.GoldschmidtB69DeepCount

public section

namespace CFSG.Quasithin

open B6

namespace B69

variable {V : Type} [CommGroup V]

theorem autSec_sup_conj {L A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (hMW : L ⊔ A ≤ stabSub W)
    (hMU : L ⊔ A ≤ stabSub U) {ψ φ : MulAut (Sec W U)} (hψ : ψ ∈ autSec (L ⊔ A) W U)
    (hφ : φ ∈ autSec L W U) : ψ * φ * ψ⁻¹ ∈ autSec L W U := by
  have hmapL := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMU (le_sup_left : L ≤ L ⊔ A)
  rw [← B5.range_secHom (L ⊔ A) hMW hMU] at hψ
  obtain ⟨m, rfl⟩ := hψ
  rw [← hmapL] at hφ ⊢
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.1 hφ
  refine Subgroup.mem_map.2 ⟨m * l₀ * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [Subgroup.mem_subgroupOf] at hl₀ ⊢
  have hmN : (m : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    (sup_le Subgroup.le_normalizer hAnL) m.2
  exact (Subgroup.mem_normalizer_iff.1 hmN _).1 hl₀

theorem normal_autSec_subgroupOf {L A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (hMW : L ⊔ A ≤ stabSub W)
    (hMU : L ⊔ A ≤ stabSub U) {H : Subgroup (MulAut (Sec W U))} (hH : H ≤ autSec (L ⊔ A) W U) :
    ((autSec L W U).subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact autSec_sup_conj hAnL hMW hMU (hH g.2) hn

variable [Finite V]

theorem false_of_twist_lt (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {W₁ : Subgroup V} (hW₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V)) (S : SpTwist L W₁ K) : False := by
  obtain ⟨W₂, hW₂, hne, e₂, he₂⟩ :=
    exists_twist_member_sp4 S.r hW₁ S.e₁ S.he₁ S.t S.ht S.ht' S.htw S.hniso
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA hW₁
  have hA₂ := a_stab_irr hV hA hL hLA hW₂
  have hAW₁ : A ≤ stabSub W₁ := B1.le_stabSub_of_invariant hA₁
  have hAW₂ : A ≤ stabSub W₂ := B1.le_stabSub_of_invariant hA₂
  have hAU : A ≤ stabSub (fixV L) :=
    B1.le_stabSub_of_invariant (B1Red.fixV_inv_of_normalizes hAn)
  have hLW₁ : L ≤ stabSub W₁ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₁).1
  have hLW₂ : L ≤ stabSub W₂ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₂).1
  have hLU : L ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant (isInv_fixV L)
  have hB := not_le_centSec_of_irr hL hAn hLA hW₁ hA₁
  have hGT := card_lt_of_tau hn hK hA.1.2.2.1 hAn hAW₁ hAW₂ hAU hLW₁ hLW₂ hLU S.r S.hnorm S.e₁ e₂
    (S.he₁ hLW₁ hLU) (he₂ hLW₂ hLU) hB
  exact absurd (two_sections_count hV hA hL hLA hW₁ hW₂ hne) (not_le.2 hGT)

end B69

end CFSG.Quasithin
