module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeW0
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSeven
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeTrans

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_conj_sup (P Q : Subgroup G) (g : G) :
    conjSubgroup (P ⊔ Q) g = conjSubgroup P g ⊔ conjSubgroup Q g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_sup _ _ _

private theorem nineThree_conj_iSup' {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

private theorem nineThree_mem_normalizer_of_le {P : Subgroup G} {n : G}
    (h1 : conjSubgroup P n ≤ P) (h2 : conjSubgroup P n⁻¹ ≤ P) : n ∈ normalizer (P : Set G) := by
  have h3 := E3.conjSubgroup_mono_left n h2
  rw [E3.conjSubgroup_inv_conj] at h3
  exact conjSubgroup_eq_iff_mem_normalizer.mp (le_antisymm h1 h3)

theorem nineDeltaStab_le_normalizer_nineW (V S : Subgroup G) :
    nineDeltaStab V S ≤ normalizer (nineW V S : Set G) := by
  have hle : ∀ n ∈ nineDeltaStab V S, conjSubgroup (nineW V S) n ≤ nineW V S := by
    intro n hn
    unfold nineW
    rw [nineThree_conj_iSup']
    refine iSup_le fun B => ?_
    rw [nineThree_conj_iSup']
    refine iSup_le fun hB => ?_
    exact le_iSup₂_of_le (conjSubgroup B n) ((mem_nineDeltaStab.mp hn B).mp hB) le_rfl
  intro n hn
  exact nineThree_mem_normalizer_of_le (hle n hn) (hle n⁻¹ ((nineDeltaStab V S).inv_mem hn))

namespace Nine3Choice

theorem x_ne_one (hc : Nine3Choice V T A K S X p g x) : x ≠ 1 := by
  intro h1
  have hX : X = ⊥ := by rw [hc.x_gen, h1, Subgroup.zpowers_one_eq_bot]
  have hcard := hc.core.card
  rw [hX, Subgroup.card_bot] at hcard
  exact hc.core.hyp.base.prime.one_lt.ne hcard

theorem nineD_le_nineDeltaStab (hc : Nine3Choice V T A K S X p g x) :
    nineD K A x ≤ nineDeltaStab V S :=
  (Nine3Core.nineD_le_pCoreOf.trans hc.core.pCoreOf_le_S).trans hc.core.S_le_nineDeltaStab

theorem conj_nineD_le_nineDeltaStab (hc : Nine3Choice V T A K S X p g x) :
    conjSubgroup (nineD K A x) g ≤ nineDeltaStab V S := by
  intro y hy
  have hd : g * y * g⁻¹ ∈ nineD K A x := mem_conjSubgroup_iff.mp hy
  have hyy : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [hyy]
  exact (nineDeltaStab V S).mul_mem ((nineDeltaStab V S).mul_mem
    ((nineDeltaStab V S).inv_mem hc.g_mem) (hc.nineD_le_nineDeltaStab hd)) hc.g_mem

theorem conj_nineD_le_centralizer (hc : Nine3Choice V T A K S X p g x) :
    conjSubgroup (nineD K A x) g ≤ centralizer (A : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hdn : g * n * g⁻¹ ∈ nineD K A x := mem_conjSubgroup_iff.mp hn
  have hv : g * a * g⁻¹ ∈ V := by
    rw [← mem_conjSubgroup_iff, hc.V_g]
    exact ha
  have hcomm := Subgroup.mem_centralizer_iff.mp (hc.core.nineD_le_centralizer hc.x_mem hdn) _ hv
  calc a * n = g⁻¹ * ((g * a * g⁻¹) * (g * n * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * n * g⁻¹) * (g * a * g⁻¹)) * g := by rw [hcomm]
    _ = n * a := by group

theorem conjSubgroup_nineW0_le_of_mem_nineD (hc : Nine3Choice V T A K S X p g x) {d : G}
    (hd : d ∈ nineD K A x) : conjSubgroup (nineW0 V K S g) d ≤ nineW0 V K S g := by
  have hdR : d ∈ pCoreOf 2 K := Nine3Core.nineD_le_pCoreOf hd
  have hdK : d ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hdR
  have hdV : d ∈ centralizer (V : Set G) := hc.core.nineD_le_centralizer hc.x_mem hd
  have hV1 : conjSubgroup (nineV1 V K g) d ≤ nineW0 V K S g := by
    have hd1 : d ∈ centralizer ((nineV1 V K g : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (s := ((nineV1 V K g : Subgroup G) : Set G)) (t := (V : Set G))
        inf_le_left hdV
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.centralizer_le_normalizer _ hd1)]
    exact le_sup_left
  have hB : ∀ B ∈ nineOmegaIn V K S, conjSubgroup (B ⊓ pCoreOf 2 K) d ≤ nineW0 V K S g := by
    intro B hB
    rw [E3.conjSubgroup_inf, Nine3Core.conjSubgroup_pCoreOf K hdK]
    exact le_trans (le_iSup₂_of_le (conjSubgroup B d) (hc.core.conjSubgroup_mem_nineOmegaIn hB hdR)
      le_rfl : conjSubgroup B d ⊓ pCoreOf 2 K ≤ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K)
      le_sup_right
  show conjSubgroup (nineV1 V K g ⊔ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) d ≤
    nineW0 V K S g
  rw [nineThree_conj_sup, nineThree_conj_iSup']
  refine sup_le hV1 (iSup_le fun B => ?_)
  rw [nineThree_conj_iSup']
  exact iSup_le fun hBΩ => hB B hBΩ

theorem conjSubgroup_nineW0_le_of_mem_conj (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) {n : G} (hn : n ∈ nineDeltaStab V S)
    (hnR : n ∈ conjSubgroup (pCoreOf 2 K) g) (hnA : n ∈ centralizer (A : Set G)) :
    conjSubgroup (nineW0 V K S g) n ≤ nineW0 V K S g := by
  have hnAA : conjSubgroup A n = A :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.centralizer_le_normalizer _ hnA)
  have hnRR : conjSubgroup (conjSubgroup (pCoreOf 2 K) g) n = conjSubgroup (pCoreOf 2 K) g :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hnR)
  have hgen : ∀ B ∈ nineDelta V S, B ≠ A →
      conjSubgroup (B ⊓ conjSubgroup (pCoreOf 2 K) g) n ≤ nineW0 V K S g := by
    intro B hB hBA
    rw [E3.conjSubgroup_inf, hnRR]
    have hB' : conjSubgroup B n ∈ nineDelta V S := (mem_nineDeltaStab.mp hn B).mp hB
    have hB'A : conjSubgroup B n ≠ A := fun e =>
      hBA (nineThree_conj_injective (e.trans hnAA.symm))
    rcases hc.core.mem_nineDelta_iff.mp hB' with hBV | hΩ
    · rw [hBV]
      exact le_sup_left
    · rw [← hc.inf_pCoreOf_eq_inf_conj hI hΩ hB'A]
      exact le_trans (le_iSup₂_of_le (conjSubgroup B n) hΩ le_rfl :
        conjSubgroup B n ⊓ pCoreOf 2 K ≤ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) le_sup_right
  have hnA₀ : n ∈ normalizer ((A ⊓ pCoreOf 2 K : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
      (s := ((A ⊓ pCoreOf 2 K : Subgroup G) : Set G)) (t := (A : Set G)) inf_le_left hnA)
  show conjSubgroup (nineV1 V K g ⊔ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) n ≤
    nineW0 V K S g
  rw [nineThree_conj_sup, nineThree_conj_iSup']
  refine sup_le (hgen V hc.core.V_mem_nineDelta hc.core.ne.symm) (iSup_le fun B => ?_)
  rw [nineThree_conj_iSup']
  refine iSup_le fun hBΩ => ?_
  by_cases hBA : B = A
  · rw [hBA, conjSubgroup_eq_iff_mem_normalizer.mpr hnA₀]
    exact le_trans (le_iSup₂_of_le A hc.core.A_mem_nineOmegaIn le_rfl :
      A ⊓ pCoreOf 2 K ≤ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) le_sup_right
  · rw [hc.inf_pCoreOf_eq_inf_conj hI hBΩ hBA]
    exact hgen B (hc.core.mem_nineDelta_iff.mpr (Or.inr hBΩ)) hBA

theorem nineD_le_normalizer_nineW0 (hc : Nine3Choice V T A K S X p g x) :
    nineD K A x ≤ normalizer (nineW0 V K S g : Set G) := fun d hd =>
  nineThree_mem_normalizer_of_le (hc.conjSubgroup_nineW0_le_of_mem_nineD hd)
    (hc.conjSubgroup_nineW0_le_of_mem_nineD ((nineD K A x).inv_mem hd))

theorem conj_nineD_le_normalizer_nineW0 (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) :
    conjSubgroup (nineD K A x) g ≤ normalizer (nineW0 V K S g : Set G) := by
  have hmem : ∀ n ∈ conjSubgroup (nineD K A x) g,
      conjSubgroup (nineW0 V K S g) n ≤ nineW0 V K S g := fun n hn => by
    refine hc.conjSubgroup_nineW0_le_of_mem_conj hI (hc.conj_nineD_le_nineDeltaStab hn) ?_
      (hc.conj_nineD_le_centralizer hn)
    have hd : g * n * g⁻¹ ∈ nineD K A x := mem_conjSubgroup_iff.mp hn
    exact mem_conjSubgroup_iff.mpr (Nine3Core.nineD_le_pCoreOf hd)
  exact fun n hn => nineThree_mem_normalizer_of_le (hmem n hn)
    (hmem n⁻¹ ((conjSubgroup (nineD K A x) g).inv_mem hn))

theorem nineL_le_normalizer_nineW0 (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) : nineL K A x g ≤ normalizer (nineW0 V K S g : Set G) :=
  sup_le hc.nineD_le_normalizer_nineW0 (hc.conj_nineD_le_normalizer_nineW0 hI)

theorem nineL_le_nineDeltaStab (hc : Nine3Choice V T A K S X p g x) :
    nineL K A x g ≤ nineDeltaStab V S :=
  sup_le hc.nineD_le_nineDeltaStab hc.conj_nineD_le_nineDeltaStab

theorem nineL_le_normalizer_nineW (hc : Nine3Choice V T A K S X p g x) :
    nineL K A x g ≤ normalizer (nineW V S : Set G) :=
  (hc.nineL_le_nineDeltaStab).trans (nineDeltaStab_le_normalizer_nineW V S)

theorem odd_card_nineDelta (hc : Nine3Choice V T A K S X p g x)
    (h3 : 3 ≤ Nat.card ↥(nineDelta V S)) : Odd (Nat.card ↥(nineDelta V S)) := by
  obtain ⟨n, -, hΔ⟩ := hc.core.card_nineOmegaIn
  rw [hΔ] at h3 ⊢
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h3
  exact (Nat.even_pow.mpr ⟨even_two, hn⟩).add_one

theorem nineL_transitive (hc : Nine3Choice V T A K S X p g x)
    (h3 : 3 ≤ Nat.card ↥(nineDelta V S)) :
    ∀ B ∈ nineDelta V S, ∀ B' ∈ nineDelta V S, ∃ l ∈ nineL K A x g, conjSubgroup B l = B' := by
  obtain ⟨C, hCΔ, hCV, hCA⟩ : ∃ C ∈ nineDelta V S, C ≠ V ∧ C ≠ A := by
    by_contra hcon
    push Not at hcon
    have hsub : nineDelta V S ⊆ {V, A} := fun C hC => by
      by_cases h1 : C = V
      · exact Or.inl h1
      · exact Or.inr (hcon C hC h1)
    have h2 : Nat.card ↥(nineDelta V S) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc (nineDelta V S).ncard ≤ ({V, A} : Set (Subgroup G)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le V {A}).trans ?_
          rw [Set.ncard_singleton]
    omega
  have hCΩ : C ∈ nineOmegaIn V K S := (hc.core.mem_nineDelta_iff.mp hCΔ).resolve_left hCV
  have hmove : ∀ B ∈ nineDelta V S, ∃ l ∈ nineL K A x g, conjSubgroup B l = C := by
    intro B hB
    by_cases hBV : B = V
    ·
      have hC' : conjSubgroup C g⁻¹ ∈ nineDelta V S := hc.conj_inv_mem_nineDelta hCΔ
      have hC'V : conjSubgroup C g⁻¹ ≠ V := by
        intro e
        apply hCA
        have h1 := congrArg (fun C => conjSubgroup C g) e
        simp only [E3.conjSubgroup_inv_conj] at h1
        rw [h1, hc.V_g]
      have hC'Ω : conjSubgroup C g⁻¹ ∈ nineOmegaIn V K S :=
        (hc.core.mem_nineDelta_iff.mp hC').resolve_left hC'V
      have hVA : conjSubgroup V g⁻¹ = A := by
        have := E3.conjSubgroup_conj_inv A g
        rwa [hc.A_g] at this
      obtain ⟨d, hd, hdC⟩ := hc.core.nineD_transitive hc.x_mem hc.x_ne_one
        hc.core.A_mem_nineOmegaIn hC'Ω
      refine ⟨g⁻¹ * d * g, ?_, ?_⟩
      · refine Subgroup.mem_sup_right (mem_conjSubgroup_iff.mpr ?_)
        have e : g * (g⁻¹ * d * g) * g⁻¹ = d := by group
        rw [e]
        exact hd
      · rw [hBV, ← CFSG.Quasithin.conjSubgroup_conjSubgroup,
          ← CFSG.Quasithin.conjSubgroup_conjSubgroup, hVA, ← hdC, E3.conjSubgroup_inv_conj]
    · have hBΩ : B ∈ nineOmegaIn V K S := (hc.core.mem_nineDelta_iff.mp hB).resolve_left hBV
      obtain ⟨d, hd, hdC⟩ := hc.core.nineD_transitive hc.x_mem hc.x_ne_one hBΩ hCΩ
      exact ⟨d, Subgroup.mem_sup_left hd, hdC.symm⟩
  intro B hB B' hB'
  obtain ⟨l₁, hl₁, h₁⟩ := hmove B hB
  obtain ⟨l₂, hl₂, h₂⟩ := hmove B' hB'
  refine ⟨l₁ * l₂⁻¹, Subgroup.mul_mem _ hl₁ (Subgroup.inv_mem _ hl₂), ?_⟩
  rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, h₁, ← h₂, E3.conjSubgroup_conj_inv]

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
