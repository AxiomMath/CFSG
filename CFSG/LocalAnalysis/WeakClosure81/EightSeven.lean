module

public import CFSG.LocalAnalysis.WeakClosure81.EightDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFour
public import CFSG.Quasithin.Background.E3Bar
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem ne_bot_of_two_le_card {A : Subgroup G} (h : 2 ≤ Nat.card A) : A ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.card_bot] at h
  omega

theorem isCalH0_of_isE {V H T A K : Subgroup G} {j : ℕ} (hV : IsElemAbelian 2 V)
    (hH0 : IsCalH0 V H) (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hAT : A ≤ T) (hAV : ∃ g : G, A ≤ conjSubgroup V g) (hK : E1.IsE j H T A K) :
    A ≤ K ∧ pCoreOf 2 H ≤ pCoreOf 2 K ∧ IsCalH0 V K ∧
      IsSylowIn 2 (T ⊓ K) (K ⊓ Subgroup.normalizer (V : Set G)) := by
  have hH : IsCalH V H := hH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  obtain ⟨g, hAg⟩ := hAV
  have hAab : IsElemAbelian 2 A :=
    CFSG.Open.IsElemAbelian.mono (isElemAbelian_conjSubgroup' hV g) hAg
  have hAsupK : A ⊔ pCoreOf 2 H ≤ T ⊓ K := (E1.le_tauOf hTH hAT hAab).trans hK.2.1
  have hAK : A ≤ K := (le_sup_left.trans hAsupK).trans inf_le_right
  have hO2HK : pCoreOf 2 H ≤ pCoreOf 2 K := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact (le_sup_right.trans hAsupK).trans inf_le_right
    · intro x hx
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H (hK.1 hx)
    · exact hT.isPGroup.to_le (pCoreOf_le_of_isCalH hH hT)
  have hKcal : IsCalH V K := by
    refine ⟨?_, ?_, ?_⟩
    · exact (hH0.2.trans hO2HK).trans (CFSG.openPCoreOf_le 2 K)
    · intro x hx
      obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxH : x ∈ H := hK.1 hxK
      have hxC' : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
        Subgroup.centralizer_le hO2HK hxC
      exact hO2HK (hH.2.1 (Subgroup.mem_inf.mpr ⟨hxH, hxC'⟩))
    · have hle : T ⊓ K ≤ K ⊓ Subgroup.normalizer (V : Set G) :=
        le_inf inf_le_right (inf_le_left.trans (hT.le.trans inf_le_right))
      have hdvd : (K ⊓ Subgroup.normalizer (V : Set G)).relIndex K ∣
          (T ⊓ K).relIndex K :=
        Subgroup.relIndex_dvd_of_le_left (L := K) hle
      have hnot : ¬ 2 ∣ (T ⊓ K).relIndex K := hK.2.2.1.not_dvd_relIndex
      exact Nat.not_even_iff_odd.mp fun hev =>
        hnot (even_iff_two_dvd.mp hev |>.trans hdvd)
  refine ⟨hAK, hO2HK, ⟨hKcal, hH0.2.trans hO2HK⟩, ?_⟩
  refine ⟨le_inf inf_le_right (inf_le_left.trans (hT.le.trans inf_le_right)), ?_, ?_⟩
  · exact hT.isPGroup.to_le inf_le_left
  · intro h2
    have hdiv : (T ⊓ K).relIndex (K ⊓ Subgroup.normalizer (V : Set G)) ∣
        (T ⊓ K).relIndex K :=
      ⟨(K ⊓ Subgroup.normalizer (V : Set G)).relIndex K,
        (Subgroup.relIndex_mul_relIndex (T ⊓ K) (K ⊓ Subgroup.normalizer (V : Set G)) K
          (le_inf inf_le_right (inf_le_left.trans (hT.le.trans inf_le_right)))
          inf_le_left).symm⟩
    exact hK.2.2.1.not_dvd_relIndex (h2.trans hdiv)

theorem inf_centralizer_eSub_ne_bot_of_isE {V H T A K : Subgroup G} {i k : ℕ}
    (hV : IsElemAbelian 2 V) (hH0 : IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hA : A ∈ E3.gammaSet V i T) (hrank : k + i < rk ↥V) (hK : E1.IsE k H T A K) :
    A ⊓ Subgroup.centralizer (eSub V K (T ⊓ K) : Set G) ≠ ⊥ := by
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hH : IsCalH V H := hH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hAab : IsElemAbelian 2 A :=
    CFSG.Open.IsElemAbelian.mono (isElemAbelian_conjSubgroup' hV g) hAg
  obtain ⟨-, -, hKcal, hTK⟩ := isCalH0_of_isE hV hH0 hT hAT ⟨g, hAg⟩ hK
  have hcardV : Nat.card (conjSubgroup V g) = 2 ^ rk ↥V := by
    rw [E3.card_conjSubgroup V g,
      CFSG.Quasithin.card_eq_two_pow_of_isPGroup (CFSG.Open.IsElemAbelian.isPGroup hV)]
  have hcard1 : Nat.card (conjSubgroup V g) = 2 ^ i * Nat.card A := by
    rw [E3.card_eq_two_pow_mul (E3.isPGroup_conjSubgroup (CFSG.Open.IsElemAbelian.isPGroup hV) g)
      hAg, hm]
  have hcard : 2 ^ i * Nat.card A = 2 ^ rk ↥V := hcard1.symm.trans hcardV
  have hAle : 2 ^ (k + 1) ≤ Nat.card A := by
    have hle : 2 ^ i * 2 ^ (k + 1) ≤ 2 ^ i * Nat.card A := by
      rw [hcard, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.le_of_mul_le_mul_left hle (pow_pos (by norm_num) i)
  have hcle := E3.card_le_of_isE hTH hAT hAab hK
  have h2le : 2 ≤ Nat.card ↥(A ⊓ pCoreOf 2 K) := by
    have hle : 2 ^ k * 2 ≤ 2 ^ k * Nat.card ↥(A ⊓ pCoreOf 2 K) := by
      calc 2 ^ k * 2 = 2 ^ (k + 1) := (pow_succ 2 k).symm
        _ ≤ Nat.card A := hAle
        _ ≤ 2 ^ k * Nat.card ↥(A ⊓ pCoreOf 2 K) := hcle.2
    exact Nat.le_of_mul_le_mul_left hle (pow_pos (by norm_num) k)
  have hne : A ⊓ pCoreOf 2 K ≠ ⊥ := ne_bot_of_two_le_card h2le
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxCent : (x : G) ∈ Subgroup.centralizer (eSub V K (T ⊓ K) : Set G) :=
    Subgroup.le_centralizer_iff.mp (eSub_centralizes_pCoreOf hV hKcal.1 hTK) x.2.2
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(x : G), x.2.1, hxCent⟩, ?_⟩
  intro hx
  exact hx1 (Subtype.ext (by simpa using congrArg Subtype.val hx))

theorem le_normalizer_of_isE {V H T A K : Subgroup G} {j : ℕ} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hVne : V ≠ ⊥) (hH0 : IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hAT : A ≤ T) (hAV : ∃ g : G, A ≤ conjSubgroup V g) (hK : E1.IsE j H T A K)
    (hCA : A ⊓ Subgroup.centralizer (eSub V K (T ⊓ K) : Set G) ≠ ⊥) :
    K ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hAK, -, hKcal, hTK⟩ := isCalH0_of_isE hV hH0 hT hAT hAV hK
  obtain ⟨g, hAg⟩ := hAV
  have hU : A ≤ conjSubgroup V g ⊓ K := le_inf hAg hAK
  have hfirst : ((conjSubgroup V g ⊓ K) ≤
        Subgroup.centralizer (eSub V K (T ⊓ K) : Set G)) ∧
      ∀ h ∈ K, conjSubgroup (conjSubgroup V g ⊓ K) h ≤
        Subgroup.normalizer (V : Set G) := by
    rcases eight_four_one hV hTI hVne hKcal hTK g with h | ⟨hbot, -⟩
    · exact h
    · exfalso
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCA
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨hU x.2.1, x.2.2⟩
      exact hx1 (Subtype.ext (by simpa using Subgroup.mem_bot.mp hxbot))
  have hcl : conjClosure A K ≤ Subgroup.normalizer (V : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    have hmem : h * z * h⁻¹ ∈ conjSubgroup (conjSubgroup V g ⊓ K) h⁻¹ := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hU hz
    exact hfirst.2 h⁻¹ (K.inv_mem hh) hmem
  have htwo : twoResidual K ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.Quasithin.E1.twoResidual_le_conjClosure ⟨j, hK⟩).trans hcl
  have hsup : (T ⊓ K) ⊔ twoResidual K = K :=
    CFSG.Quasithin.sup_twoResidual_eq hK.2.2.1
  rw [← hsup]
  exact sup_le (inf_le_left.trans (hT.le.trans inf_le_right)) htwo

theorem eight_seven_of_isCalH0 {V H T : Subgroup G} {i k : ℕ} (hV7 : Hyp7 V)
    (hH0 : IsCalH0 V H) (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hrank : k + i < rk ↥V) (hHE : E1.InE k H) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) := by
  have hV : IsElemAbelian 2 V := hV7.1
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V := hV7.2.2
  have hVne : V ≠ ⊥ := ne_bot_of_two_le_card (A := V) (le_of_lt hV7.2.1)
  have hH : IsCalH V H := hH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  let Ω : Set (Subgroup G) :=
    {A | A ≤ H ∧ ∃ g : G, A ≤ conjSubgroup V g ∧ E3.mQuot (conjSubgroup V g) A = i}
  have hΩ : E1.IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · intro A hA
      exact hA.1
    · intro A hA
      obtain ⟨g, hAg, -⟩ := hA.2
      exact CFSG.Open.IsElemAbelian.mono (isElemAbelian_conjSubgroup' hV g) hAg
    · intro A hA h hh
      obtain ⟨hAH, g, hAg, hm⟩ := hA
      have hconj : CFSG.Quasithin.A1b.conjSub h A = conjSubgroup A h⁻¹ := by
        ext x
        simp [CFSG.Quasithin.A1b.mem_conjSub_iff, mem_conjSubgroup_iff]
      rw [hconj]
      refine ⟨conjSubgroup_le_of_le hAH (H.inv_mem hh), g * h⁻¹, ?_, ?_⟩
      · rw [← conjSubgroup_conjSubgroup V g h⁻¹]
        exact Subgroup.map_mono hAg
      · rw [← conjSubgroup_conjSubgroup V g h⁻¹,
          E3.mQuot_conjSubgroup (conjSubgroup V g) A h⁻¹]
        exact hm
  have hweak : E1.weakClosure T Ω = E3.wClos V i T := by
    refine le_antisymm ?_ ?_
    · rw [E1.weakClosure]
      refine iSup₂_le fun A hAΩ => iSup_le fun hAT => ?_
      exact E3.le_wClos (show A ∈ E3.gammaSet V i T from ⟨hAT, hAΩ.2⟩)
    · refine E3.wClos_le_of_forall fun A hA => ?_
      have hAΩ : A ∈ Ω := ⟨hA.1.trans (hT.le.trans inf_le_left), hA.2⟩
      exact le_iSup₂_of_le A hAΩ (le_iSup (fun _ : A ≤ T => A) hA.1)
  have hegen : E1.eGen k H T Ω ≤ H ⊓ Subgroup.normalizer (V : Set G) := by
    rw [E1.eGen]
    refine iSup₂_le fun A hAΩ => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    have hAγ : A ∈ E3.gammaSet V i T := ⟨hAT, hAΩ.2⟩
    have hCA := inf_centralizer_eSub_ne_bot_of_isE hV hH0 hT hAγ hrank hK
    obtain ⟨g, hAg, -⟩ := hAΩ.2
    exact le_inf hK.1 (le_normalizer_of_isE hV hTI hVne hH0 hT hAT ⟨g, hAg⟩ hK hCA)
  have hmain := hHE T hTH Ω hΩ
  rw [hweak] at hmain
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  · calc H ≤ E1.eGen k H T Ω ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) := le_of_eq hmain.symm
      _ ≤ (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) := sup_le_sup_right hegen _

theorem eight_seven {V H T : Subgroup G} {i k : ℕ} (hV7 : Hyp7 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hW : E3.wClos V 0 T ≠ V) (hrank : k + i < rk ↥V) (hHE : E1.InE k H)
    (hNE : ¬ IsCalH0 V H →
      E1.InE k (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)))
    (hcond : CentralizersInM V H T ∨ NormalizersInM V H (E3.wClos V 0 T))
    (h86 : ¬ IsCalH0 V H → H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G))) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) := by
  by_cases hH0 : IsCalH0 V H
  · exact eight_seven_of_isCalH0 hV7 hH0 hT hrank hHE
  · have hV : IsElemAbelian 2 V := hV7.1
    have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
    set W₀ : Subgroup G := E3.wClos V 0 T with hW₀def
    set H₀ : Subgroup G := H ⊓ Subgroup.normalizer (W₀ : Set G) with hH₀def
    have hTleW₀ : T ≤ Subgroup.normalizer (W₀ : Set G) :=
      Subgroup.le_normalizer.trans
        (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) T)
    have hTleH₀ : T ≤ H₀ := le_inf (hT.le.trans inf_le_left) hTleW₀
    have hH₀leH : H₀ ≤ H := inf_le_left
    have hH₀cal : IsCalH V H₀ := isCalH_of_le hV hH hT hTleH₀ hH₀leH
    have hW₀leT : W₀ ≤ T := wClos_zero_le V T
    have hW₀leH : W₀ ≤ H := hW₀leT.trans (hT.le.trans inf_le_left)
    have hW₀leH₀ : W₀ ≤ H₀ := le_inf hW₀leH Subgroup.le_normalizer
    have hW₀p : IsPGroup 2 W₀ := hT.isPGroup.to_le hW₀leT
    have hH₀norm : H₀ ≤ Subgroup.normalizer (W₀ : Set G) := inf_le_right
    have hW₀core : W₀ ≤ pCoreOf 2 H₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hW₀leH₀ hH₀norm hW₀p
    have hVW₀ : V ≤ W₀ := by
      have h : conjSubgroup V 1 ≤ T := by rw [conjSubgroup_one]; exact le_of_isCalH hV hH hT
      have h' := conjSubgroup_le_wClos_zero (V := V) (X := T) (g := 1) h
      rwa [conjSubgroup_one, ← hW₀def] at h'
    have hH₀0 : IsCalH0 V H₀ := ⟨hH₀cal, hVW₀.trans hW₀core⟩
    have hT_sylow_H₀ : IsSylowIn 2 T (H₀ ⊓ Subgroup.normalizer (V : Set G)) := by
      have hTKle : T ≤ H₀ ⊓ Subgroup.normalizer (V : Set G) :=
        le_inf hTleH₀ (hT.le.trans inf_le_right)
      refine ⟨hTKle, hT.isPGroup, ?_⟩
      intro h2
      have hdiv : T.relIndex (H₀ ⊓ Subgroup.normalizer (V : Set G)) ∣
          T.relIndex (H ⊓ Subgroup.normalizer (V : Set G)) :=
        ⟨(H₀ ⊓ Subgroup.normalizer (V : Set G)).relIndex
            (H ⊓ Subgroup.normalizer (V : Set G)),
          (Subgroup.relIndex_mul_relIndex T (H₀ ⊓ Subgroup.normalizer (V : Set G))
            (H ⊓ Subgroup.normalizer (V : Set G)) hTKle
            (inf_le_inf hH₀leH le_rfl)).symm⟩
      exact hT.not_dvd_relIndex (h2.trans hdiv)
    have h4 : H₀ = (H₀ ⊓ Subgroup.normalizer (V : Set G)) ⊔
        (H₀ ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) :=
      eight_seven_of_isCalH0 hV7 hH₀0 hT_sylow_H₀ hrank (hNE hH0)
    have hH0le : H₀ ≤ (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) := by
      rw [h4]
      exact sup_le_sup (inf_le_inf hH₀leH le_rfl) (inf_le_inf hH₀leH le_rfl)
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    calc H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔ H₀ := h86 hH0
      _ ≤ (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (E3.wClos V i T : Set G)) :=
        sup_le le_sup_left hH0le

end CFSG.LocalAnalysis.WeakClosure81

end
