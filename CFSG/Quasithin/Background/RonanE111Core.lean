module

public import CFSG.Quasithin.Background.RonanE111Ind
public import CFSG.Quasithin.Background.RonanE111Gamma
public import CFSG.Quasithin.Background.RonanE111Mem
public import CFSG.Quasithin.Background.RonanE111Half
public import CFSG.Quasithin.Background.GoldschmidtE1Transfer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

variable {G : Type} [Group G] [Finite G]

theorem J_le_of_data {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) (hH : HypT n G T) {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω)
    {G₁ : Subgroup G} (hTG : T ≤ G₁)
    (hmem : ∀ A ∈ Ω, A ≤ T → ∀ K : Subgroup G, E1.IsE n ⊤ T A K → K ≤ G₁)
    (hsol : ∀ H : Subgroup G, T ≤ H → Group.IsSolvable ↥H → H ≤ G₁)
    (hNW : (⊤ : Subgroup G) ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G) ≤ G₁) :
    J ≤ G₁ := by
  classical
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hS
  set H : Subgroup G := J ⊔ S with hHdef
  have hJH : J ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hHN : H ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSN
  set Γ : Set (Subgroup G) := {B | ∃ A ∈ Ω, A ≤ T ∧ ∃ g ∈ H,
    B = A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))} with hΓ
  have hΓinv : E1.IsInvColl H Γ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨A, hAΩ, hAT, g, hg, rfl⟩
      intro y hy
      rw [A1b.mem_conjSub_iff] at hy
      have hyS : g⁻¹ * y * g ∈ S := ⟨hAT hy.1, hy.2⟩
      have := H.mul_mem (H.mul_mem hg (hSH hyS)) (H.inv_mem hg)
      simpa [mul_assoc] using this
    · rintro _ ⟨A, hAΩ, hAT, g, hg, rfl⟩
      exact isElemAbelian_of_le
        (CFSG.Open.IsElemAbelian.map (hΩ.isElemAbelian A hAΩ) (MulAut.conj g).toMonoidHom)
        (Subgroup.map_mono inf_le_left)
    · rintro _ ⟨A, hAΩ, hAT, g, hg, rfl⟩ h hh
      exact ⟨A, hAΩ, hAT, h * g, H.mul_mem hh hg, by rw [A1b.conjSub_mul]⟩
  have hmain : E1.eGen n H S Γ ⊔ (H ⊓ Subgroup.normalizer (E1.weakClosure S Γ : Set G)) = H :=
    inEFor_compSup hn hR hH hJ Γ hΓinv
  have hCov1 : E1.eGen n H S Γ ≤ Cov G₁ J := by
    unfold E1.eGen
    refine iSup₂_le fun B hB => iSup_le fun hBS => iSup₂_le fun K hK => ?_
    obtain ⟨A, hAΩ, hAT, g, hg, rfl⟩ := hB
    obtain ⟨A'', hA''Ω, hA''T, hKA''⟩ := gamma_member hR hJ hΩ hg hAΩ hAT hBS hK
    exact P_le_cov hR hJ hn hTG hA''T (hΩ.isElemAbelian A'' hA''Ω) (hmem A'' hA''Ω hA''T) hKA''
  have hW₀S : E1.weakClosure S Γ ≤ S := E1.weakClosure_le
  have hCov2 : H ⊓ Subgroup.normalizer (E1.weakClosure S Γ : Set G) ≤ Cov G₁ J := by
    by_cases hW : E1.weakClosure T Ω ≤ S
    ·
      have hW₀ : E1.weakClosure S Γ = E1.weakClosure T Ω := by
        apply le_antisymm
        · refine iSup₂_le fun B hB => iSup_le fun hBS => ?_
          obtain ⟨A, hAΩ, hAT, g, hg, rfl⟩ := hB
          have hAS : A ≤ S := (E1.le_weakClosure hAΩ hAT).trans hW
          have hAN : A ⊓ Subgroup.normalizer (J : Set G) = A := inf_eq_left.mpr (hAS.trans hSN)
          rw [hAN] at hBS ⊢
          exact E1.le_weakClosure (hΩ.conj A hAΩ g (Subgroup.mem_top g))
            (hBS.trans inf_le_left)
        · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
          have hAS : A ≤ S := (E1.le_weakClosure hA hAT).trans hW
          have hAN : A ⊓ Subgroup.normalizer (J : Set G) = A := inf_eq_left.mpr (hAS.trans hSN)
          exact E1.le_weakClosure (X := S) ⟨A, hA, hAT, 1, H.one_mem, by rw [hAN, A1b.conjSub_one]⟩ hAS
      rw [hW₀]
      intro g hg
      exact mem_Cov_of_mem (hNW ⟨Subgroup.mem_top g, hg.2⟩) (hHN hg.1)
    ·
      obtain ⟨A₀, hA₀Ω, hA₀T, hA₀S⟩ : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ S := by
        by_contra hcon
        push Not at hcon
        exact hW (iSup₂_le fun A hA => iSup_le fun hAT => hcon A hA hAT)
      have hSW₀ : S ≤ Subgroup.normalizer (E1.weakClosure S Γ : Set G) :=
        E1.le_normalizer_weakClosure_of_inv hSH hΓinv.conj
      have hV₀ : A₀ ⊓ Subgroup.normalizer (J : Set G) ≤ E1.weakClosure S Γ := by
        refine E1.le_weakClosure (X := S) ⟨A₀, hA₀Ω, hA₀T, 1, H.one_mem, (A1b.conjSub_one _).symm⟩ ?_
        exact le_inf (inf_le_left.trans hA₀T) inf_le_right
      exact half_two hR hJ hn hTG hsol hA₀T (hΩ.isElemAbelian A₀ hA₀Ω) hA₀S
        (hmem A₀ hA₀Ω hA₀T) hW₀S hSW₀ hV₀
  have hHCov : H ≤ Cov G₁ J := by
    rw [← hmain]
    exact sup_le hCov1 hCov2
  exact le_of_le_Cov hR hJ (exists_involution_of_isComp hJ) hTG (hJH.trans hHCov)

theorem e111CoreT : E111CoreT := by
  intro G _ _ X T n hn hH hR
  by_cases hXs : IsSimpleGroup ↥X
  · exact inEFor_of_simple hn hR hH hXs
  intro Ω hΩ
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  set G₁ : Subgroup G := E1.eGen n ⊤ T Ω ⊔
    (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) with hG₁
  have hTG : T ≤ G₁ := fun t ht =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_top t, E1.le_normalizer_weakClosure hΩ ht⟩
  have hmem : ∀ A ∈ Ω, A ≤ T → ∀ K : Subgroup G, E1.IsE n ⊤ T A K → K ≤ G₁ :=
    fun A hA hAT K hK => (E1.le_eGen hA hAT hK).trans le_sup_left
  have hNW : (⊤ : Subgroup G) ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G) ≤ G₁ :=
    le_sup_right
  have hsol : ∀ H' : Subgroup G, T ≤ H' → Group.IsSolvable ↥H' → H' ≤ G₁ := by
    intro H' hTH' hs
    have hTH'syl : IsSylowIn 2 T H' := by
      refine ⟨hTH', hT.2.1, fun h2 => hT.2.2 ?_⟩
      have := Subgroup.relIndex_mul_relIndex T H' ⊤ hTH' le_top
      rw [← this]
      exact Dvd.dvd.mul_right h2 _
    have h1 : E1.nParam H' ≤ (n : ℕ∞) := (E1.solvable_nParam_le_one hs).trans (by exact_mod_cast hn)
    have hInE : E1.InEFor n H' T := ((E1.nParam_le_iff (by omega)).mp h1) T hTH'syl
    exact le_of_inEFor_sub hT hTH' hInE hΩ
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥
  · obtain ⟨A₀, hA₀Ω, hA₀T, hA₀1⟩ := hex
    obtain ⟨J, hJ, -⟩ := exists_isComp_not_le hR hA₀1
    have hJG : J ≤ G₁ := J_le_of_data hR hJ hn hH hΩ hTG hmem hsol hNW
    have hXG : X ≤ G₁ := by
      rw [← iSup_conj_eq hR hJ]
      refine iSup₂_le fun t ht => ?_
      rintro _ ⟨s, hs, rfl⟩
      exact G₁.mul_mem (G₁.mul_mem (hTG ht) (hJG hs)) (G₁.inv_mem (hTG ht))
    refine le_antisymm le_top ?_
    rw [← hR.2.2.2.2.2.2]
    exact sup_le hXG hTG
  · push Not at hex
    have hW : E1.weakClosure T Ω = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => (hex A hA hAT).le)
    rw [hG₁, hW, Subgroup.normalizer_eq_top, inf_top_eq, sup_top_eq]


end CFSG.Quasithin.RonanE111
