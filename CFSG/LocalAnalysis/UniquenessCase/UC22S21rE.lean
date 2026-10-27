module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21re_le_or_le {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {M T H₁ H₂ : Subgroup G}
    (hTM : IsSylowIn 2 T M) (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂)
    (hH : ∀ X : Subgroup G, X ≤ M → T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {R : Subgroup (Bar2 M)} (hR : IsPiece q (barImage M T) R) :
    barPreimage M (R ⊔ barImage M T) ≤ H₁ ∨ barPreimage M (R ⊔ barImage M T) ≤ H₂ := by
  classical
  obtain ⟨hR0, hRq, hRS, hirr⟩ := hR
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set X : Subgroup G := barPreimage M (R ⊔ barImage M T) with hX
  have hXM : X ≤ M := Subgroup.map_subtype_le _
  have hmemX : ∀ x : ↥X, π (Subgroup.inclusion hXM x) ∈ R ⊔ barImage M T := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact hm
  have hTb : barImage M T ≤ R ⊔ barImage M T := le_sup_right
  have hTX : T ≤ X := fun t ht => ⟨⟨t, hTM.le ht⟩, hTb ⟨⟨t, hTM.le ht⟩, ht, rfl⟩, rfl⟩
  have hSyl : IsSylowIn 2 T X := by
    refine ⟨hTX, hTM.isPGroup, fun h2 => hTM.not_dvd_relIndex ?_⟩
    exact h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T X M hTX hXM))
  set ρ : ↥X →* Bar2 M := π.comp (Subgroup.inclusion hXM) with hρ
  have hker : ρ.ker ≤ CFSG.pCore 2 ↥X := by
    haveI : (ρ.ker).Normal := MonoidHom.normal_ker ρ
    have hp : IsPGroup 2 ρ.ker := by
      rintro ⟨g, hg⟩
      have hg' : Subgroup.inclusion hXM g ∈ CFSG.pCore 2 ↥M := by
        have h := MonoidHom.mem_ker.mp hg
        rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply] at h
        exact (QuotientGroup.eq_one_iff _).mp h
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥M) (p := 2)) ⟨_, hg'⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (Subgroup.inclusion hXM g) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have h2 : g ^ 2 ^ k = 1 := by
        apply Subgroup.inclusion_injective hXM
        rw [map_pow, map_one]
        exact h1
      simpa using h2
    exact le_sSup ⟨inferInstance, hp⟩
  have hRTn : R ⊔ barImage M T ≤ normalizer (R : Set (Bar2 M)) :=
    sup_le Subgroup.le_normalizer hRS
  have hRn : ρ.range ≤ normalizer (R : Set (Bar2 M)) := by
    rintro _ ⟨x, rfl⟩
    exact hRTn (hmemX x)
  have hRr : R ≤ ρ.range := by
    intro r hr
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) r
    exact ⟨⟨m, ⟨m, Subgroup.mem_sup_left hr, rfl⟩⟩, rfl⟩
  have hPT : R.comap ρ ⊔ T.subgroupOf X = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ρ x ∈ ((R ⊔ barImage M T : Subgroup (Bar2 M)) : Set (Bar2 M)) := hmemX x
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R (barImage M T) hRS] at hx
    obtain ⟨r, hr, tb, htb, hrt⟩ := hx
    obtain ⟨y, hy, hyt⟩ := htb
    set t' : ↥X := ⟨(y : G), hTX hy⟩ with ht'
    have ht'T : t' ∈ T.subgroupOf X := hy
    have hρt : ρ t' = tb := hyt
    have hxr : x * t'⁻¹ ∈ R.comap ρ := by
      have h2 : ρ (x * t'⁻¹) = r := by
        rw [map_mul, map_inv, hρt, ← hrt]
        group
      rw [Subgroup.mem_comap, h2]
      exact hr
    simpa using Subgroup.mul_mem_sup hxr ht'T
  have hbar : barImage M T ≤ (T.subgroupOf X).map ρ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), hTX hy⟩, hy, rfl⟩
  exact uc22s21rd_le_or_le hq hq2 hSyl hT₁ hT₂ (hH X hXM hTX) ρ hker hR0 hRq hRn hRr hPT
    fun Z hZR hTZ => hirr Z hZR (hbar.trans hTZ)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
