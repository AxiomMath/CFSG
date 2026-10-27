module

public import CFSG.Quasithin.Vol2.Ch11SecB24Two
public import CFSG.Quasithin.Vol2.Ch11SecB24Sym

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem transv24 (hI : In24) (h : Hyp24 T L I n V₁ V₂) (hSp4 : KindSp4 L (fsuV T I) n)
    {g k : G} (hAT : conjSubgroup (fsuV T I) g ≤ T)
    (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥) (hkT : conjSubgroup (fsuV T I) k ≤ T)
    (hkg : conjSubgroup (fsuV T I) k⁻¹ = conjSubgroup (fsuV T I) g)
    (hCA : conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G) =
      conjSubgroup V₂ k⁻¹)
    (hmA : E3.mQuot (conjSubgroup (fsuV T I) g)
      (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 2 * n)
    {a : G} (ha : a ∈ conjSubgroup (fsuV T I) g)
    (han : E3.mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer ({a} : Set G)) = n) :
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ := by
  have hfl := h.flag hI
  have hl2 := (line24 hI h hAT hnc).2
  have hm2 := h.mQuot_V₂ hI hSp4
  have hn2 := hfl.two_le
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  set W₀ := V ⊓ Subgroup.centralizer ({a} : Set G) with hW₀def
  have hV2W : V₂ ≤ W₀ := by
    rw [← hl2]
    exact inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hW0V : W₀ ≤ V := inf_le_left
  have hW0C : W₀ ⊓ Subgroup.centralizer (A : Set G) = V₂ := by
    apply le_antisymm
    · rw [← hl2]
      exact inf_le_inf_right _ hW0V
    · exact le_inf hV2W (hl2 ▸ inf_le_right)
  have hmW0 : E3.mQuot W₀ (W₀ ⊓ Subgroup.centralizer (A : Set G)) = n := by
    rw [hW0C]
    have := E3.mQuot_add hV2W hW0V
    omega
  have hAk : conjSubgroup A k = V := by rw [← hkg, E3.conjSubgroup_inv_conj]
  have hWR : conjSubgroup W₀ k ≤ ROf T L V₂ :=
    (E3.conjSubgroup_mono_left k hW0V).trans (le_ROf hI h hkT)
  have hW1 : E3.mQuot (conjSubgroup W₀ k)
      (conjSubgroup W₀ k ⊓ Subgroup.centralizer (V : Set G)) = n := by
    have := E3.mQuot_conjSubgroup W₀ (W₀ ⊓ Subgroup.centralizer (A : Set G)) k
    rw [conjSubgroup_inf_centralizer, hAk, hmW0] at this
    exact this
  have haW : a ∈ Subgroup.centralizer (W₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp hw.2 a (Set.mem_singleton a)).symm
  have hW2 : ¬ V ⊓ Subgroup.centralizer (conjSubgroup W₀ k : Set G) ≤ V₂ := by
    intro hle
    have hak : conjSubgroup (A ⊓ Subgroup.centralizer (W₀ : Set G)) k =
        V ⊓ Subgroup.centralizer (conjSubgroup W₀ k : Set G) := by
      rw [conjSubgroup_inf_centralizer, hAk]
    have h1 : a ∈ conjSubgroup (V ⊓ Subgroup.centralizer (conjSubgroup W₀ k : Set G)) k⁻¹ := by
      rw [← hak, E3.conjSubgroup_conj_inv]
      exact ⟨ha, haW⟩
    have h2 : a ∈ conjSubgroup V₂ k⁻¹ := E3.conjSubgroup_mono_left k⁻¹ hle h1
    rw [← hCA] at h2
    have haC : a ∈ Subgroup.centralizer (V : Set G) := h2.2
    have hW0eq : W₀ = V := by
      refine le_antisymm inf_le_left fun v hv => Subgroup.mem_inf.mpr ⟨hv, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact (Subgroup.mem_centralizer_iff.mp haC v hv).symm
    rw [hW0eq, E3.mQuot_self] at han
    omega
  obtain ⟨hWm, -⟩ :=
    hI.facts.sp4Root G L V ⊤ T V₁ V₂ n hfl hSp4 (conjSubgroup W₀ k) hWR hW1 hW2
  have hA3 : E3.mQuot A (A ⊓ Subgroup.centralizer (W₀ : Set G)) = n := by
    have := E3.mQuot_conjSubgroup A (A ⊓ Subgroup.centralizer (W₀ : Set G)) k
    rw [conjSubgroup_inf_centralizer, hAk, hWm] at this
    exact this.symm
  have hA2A3 : A ⊓ Subgroup.centralizer (V : Set G) ≤ A ⊓ Subgroup.centralizer (W₀ : Set G) :=
    inf_le_inf_left A (Subgroup.centralizer_le hW0V)
  have hA3C : A ⊓ Subgroup.centralizer (W₀ : Set G) ⊓ Subgroup.centralizer (V : Set G) =
      A ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hA2A3 inf_le_right)
  have hmA3 : E3.mQuot (A ⊓ Subgroup.centralizer (W₀ : Set G))
      (A ⊓ Subgroup.centralizer (W₀ : Set G) ⊓ Subgroup.centralizer (V : Set G)) = n := by
    rw [hA3C]
    have := E3.mQuot_add hA2A3 (inf_le_left : A ⊓ Subgroup.centralizer (W₀ : Set G) ≤ A)
    omega
  have hA3R : A ⊓ Subgroup.centralizer (W₀ : Set G) ≤ ROf T L V₂ :=
    inf_le_left.trans (le_ROf hI h hAT)
  have hA3V : ¬ V ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (W₀ : Set G) : Subgroup G) : Set G) ≤ V₂ := by
    intro hle
    have hW0le : W₀ ≤ V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (W₀ : Set G) : Subgroup G) : Set G) := by
      refine le_inf hW0V fun w hw => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hx.2 w hw).symm
    have hWV2 : W₀ = V₂ := le_antisymm (hW0le.trans hle) hV2W
    rw [hWV2, hm2] at han
    omega
  obtain ⟨-, hCVA3⟩ := hI.facts.sp4Root G L V ⊤ T V₁ V₂ n hfl hSp4
    (A ⊓ Subgroup.centralizer (W₀ : Set G)) hA3R hmA3 hA3V
  exact hCVA3.trans (Subgroup.commutator_mono le_rfl inf_le_left)

theorem case_lt24 (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g k : G}
    (hAT : conjSubgroup (fsuV T I) g ≤ T) (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥)
    (hkT : conjSubgroup (fsuV T I) k ≤ T)
    (hkg : conjSubgroup (fsuV T I) k⁻¹ = conjSubgroup (fsuV T I) g)
    (hCA : conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G) =
      conjSubgroup V₂ k⁻¹)
    (hcase : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ V₂) : False := by
  have hfl := h.flag hI
  have hl1 := (line24 hI h hAT hnc).1
  have hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro h0
    rw [h0, sup_bot_eq] at hl1
    exact hcase hl1
  have hSp4 : KindSp4 L (fsuV T I) n := by
    rcases (hI.s1103 G T L I n h.hyp).2.2.1 with ⟨h0, -⟩ | ⟨hk, -⟩
    · exact absurd h0 hCV
    · rcases hk with hk | hk
      · exact hk
      · exact absurd hk (h.notG2 hI)
  have hm2 := h.mQuot_V₂ hI hSp4
  have hmA : E3.mQuot (conjSubgroup (fsuV T I) g)
      (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 2 * n := by
    rw [hCA, ← hkg, E3.mQuot_conjSubgroup, hm2]
  have hCVle : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤
      ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ := by
    by_cases htr : ∃ a ∈ conjSubgroup (fsuV T I) g,
        E3.mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer ({a} : Set G)) = n
    · obtain ⟨a, ha, han⟩ := htr
      exact transv24 hI h hSp4 hAT hnc hkT hkg hCA hmA ha han
    · push Not at htr
      exact hI.facts.sp4NoTransv G L (fsuV T I) ⊤ T V₁ V₂ n hfl hSp4 _ (le_ROf hI h hAT) hmA
        htr
  apply hcase
  rw [← hl1]
  exact (sup_eq_left.mpr hCVle).symm

theorem not_le_normalizer24 (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g : G}
    (hAT : conjSubgroup (fsuV T I) g ≤ T) (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥) :
    ¬ fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
  intro hVN
  obtain ⟨k, hkT, hnck, -, hkg⟩ := exists_sym h hAT hnc hVN
  have hCA := inf_centralizer_sym hI h hkT hnck hkg
  by_cases hcase : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ = V₂
  · exact case_eq24 hI h hnc hVN hkg hCA hcase
  · exact case_lt24 hI h hAT hnc hkT hkg hCA hcase

end CFSG.Quasithin.Vol2.Ch11.SecB
