module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.S14610P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.eight_le_card_conjClosure_I₂ {H : Subgroup G} {u : G} {I I₂ : Subgroup G}
    (c : Hyp14610 T M H u I I₂) : 2 ^ 3 ≤ Nat.card (conjClosure (VZ T M) I₂) := by
  have S := c.setting
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hNV : Subgroup.normalizer (VZ T M : Set G) = M := S.hyp1281.normalizer_VZ
  have hI₁M : i1Of1469 T M I ≤ M :=
    (i1Of1469_le_yOfL22_sup T M I).trans (sup_le S.hyp1281.le hTM)
  have hUT : conjClosure (VZ T M) H ≤ T :=
    (S.conjClosure_le_pCoreOf c.hH).trans (S.pCoreOf_le_T c.hH)
  have hV₀U : conjClosure (VZ T M) I₂ ≤ conjClosure (VZ T M) H :=
    conjClosure_mono le_rfl c.I₂_le
  have hV₀2 : IsPGroup 2 (conjClosure (VZ T M) I₂) :=
    (S.hyp.sylow.1.to_le hUT).to_le hV₀U
  obtain ⟨n, hn⟩ := hV₀2.exists_card_eq
  have hVV₀ : VZ T M ≤ conjClosure (VZ T M) I₂ := le_conjClosure _ _
  have hdvd : 4 ∣ 2 ^ n := by
    have := Subgroup.card_dvd_of_le hVV₀
    rwa [hV4, hn] at this
  have h2n : 2 ≤ n := by
    by_contra hlt
    interval_cases n <;> simp at hdvd
  have hne : n ≠ 2 := by
    intro h2
    have hcard : Nat.card (conjClosure (VZ T M) I₂) ≤ Nat.card (VZ T M) := by
      rw [hn, h2, hV4]
      norm_num
    have heq : VZ T M = conjClosure (VZ T M) I₂ := Subgroup.eq_of_le_of_card_ge hVV₀ hcard
    have hI₂M : I₂ ≤ M := by
      rw [← hNV]
      have := le_normalizer_conjClosure (VZ T M) I₂
      rwa [← heq] at this
    exact c.hI.1.2.2 (c.gen ▸ sup_le hI₁M hI₂M)
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem Setting146.conjClosure_I₂_le_conjClosure_K {H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Hyp14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) :
    conjClosure (VZ T M) I₂ ≤ conjClosure (VZ T M) K := by
  have S := c.setting
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hI₂I : I₂ ≤ I := c.gen ▸ le_sup_right
  refine conjClosure_le fun g hg v hv => ?_
  have hgI : g ∈ ((K ⊔ (T ⊓ I) : Subgroup G) : Set G) := by
    rw [← hK.eq_sup]
    exact hI₂I hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K (T ⊓ I) (inf_le_right.trans hK.normal)] at hgI
  obtain ⟨k, hk, t, ht, rfl⟩ := hgI
  have htv : t * v * t⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV (hTM ht.1)) v).mp hv
  have := mem_conjClosure hk htv
  simpa [mul_assoc] using this

end CFSG.Quasithin
