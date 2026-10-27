module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def s208Gen (D : Data G) (H : Subgroup G) : Subgroup G :=
  ⨆ K ∈ calLOf D.T D.M H, K

theorem s208a_le_gen (D : Data G) {H K : Subgroup G} (hK : K ∈ calLOf D.T D.M H) :
    K ≤ s208Gen D H :=
  le_iSup₂_of_le K hK le_rfl

theorem s208a_gen_le (D : Data G) (H : Subgroup G) : s208Gen D H ≤ H :=
  iSup₂_le fun _ hK => CFSG.Quasithin.A3.subnormal_le hK.2

theorem s208a_gen_le_cCompSpan (D : Data G) {H : Subgroup G} (hTH : D.T ≤ H) :
    s208Gen D H ≤ CFSG.Quasithin.cCompSpan H := by
  refine iSup₂_le fun L hL => ?_
  obtain ⟨⟨-, -, -, K, hK, hLK⟩, hsub⟩ := hL
  have hKH : K ∈ CFSG.Quasithin.cComp H :=
    CFSG.Quasithin.cComp_mem_of_subnormal hsub (uc22p20e_cComp_of_calC hK)
  rw [hLK]
  exact iSup_le fun t => CFSG.Quasithin.le_cCompSpan (uc22p20b_cj_mem_cComp hKH (hTH t.2))

theorem s208a_cCompSpan_le_normalizer_of_mem (D : Data G) {H L : Subgroup G} (hTH : D.T ≤ H)
    (hL : L ∈ calLOf D.T D.M H) : CFSG.Quasithin.cCompSpan H ≤ normalizer (L : Set G) := by
  obtain ⟨⟨-, -, -, K, hK, hLK⟩, hsub⟩ := hL
  have hKH : K ∈ CFSG.Quasithin.cComp H :=
    CFSG.Quasithin.cComp_mem_of_subnormal hsub (uc22p20e_cComp_of_calC hK)
  rw [hLK]
  exact uc22p20b_le_normalizer_iSup (fun t : D.T => uc22p20bCj (t : G) K)
    (CFSG.Quasithin.cCompSpan H) fun t =>
      uc22p20e_cCompSpan_le_normalizer (uc22p20b_cj_mem_cComp hKH (hTH t.2))

theorem s208a_pCoreOf_ne_bot_of_normal {N W : Subgroup G}
    (hF : N ⊓ centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N) (hWN : W ≤ N)
    (hNW : N ≤ normalizer (W : Set G)) (hW : W ≠ ⊥) : pCoreOf 2 W ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  set P := pCoreOf 2 N with hPdef
  have hPN : P ≤ N := uc22p20b_pCoreOf_le N
  have hNP : N ≤ normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hWP : W ⊓ P ≤ pCoreOf 2 W := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      (hP2.to_le inf_le_right)
    intro w hw
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hw, hNP (hWN hw)⟩
  rw [h2] at hWP
  have hcomm : W ≤ centralizer (P : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : w * x * w⁻¹ * x⁻¹ ∈ W := by
      have : x * w⁻¹ * x⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (hNW (hPN hx)) w⁻¹).1 (W.inv_mem hw)
      simpa [mul_assoc] using W.mul_mem hw this
    have h2' : w * x * w⁻¹ * x⁻¹ ∈ P := by
      have : w * x * w⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hNP (hWN hw)) x).1 hx
      exact P.mul_mem this (P.inv_mem hx)
    have h3 : w * x * w⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.1 (hWP ⟨h1, h2'⟩)
    have h4 : w * x = x * w := by
      have := congrArg (· * (x * w)) h3
      simpa [mul_assoc] using this
    exact h4.symm
  have hWP' : W ≤ P := fun w hw => hF ⟨hWN hw, hcomm hw⟩
  apply hW
  rw [eq_bot_iff]
  intro w hw
  exact hWP ⟨hw, hWP' hw⟩

theorem s208a_normalizer_eq_of_normal {N W : Subgroup G} (hmax : rankThreeIsMaxTwoLocal N)
    (hF : N ⊓ centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N) (hWN : W ≤ N)
    (hNW : N ≤ normalizer (W : Set G)) (hW : W ≠ ⊥) : normalizer (W : Set G) = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne := s208a_pCoreOf_ne_bot_of_normal hF hWN hNW hW
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 W : Set G)) :=
    ⟨pCoreOf 2 W, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W, rfl⟩
  have h1 : normalizer (W : Set G) ≤ normalizer (pCoreOf 2 W : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) W
  have h2 : normalizer (pCoreOf 2 W : Set G) = N := hmax.2 _ hloc (hNW.trans h1)
  exact le_antisymm (h1.trans h2.le) hNW

theorem s208a_pCoreOf_ne_bot_of_calL (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    pCoreOf 2 L ≠ ⊥ := by
  have hH : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  refine s208a_pCoreOf_ne_bot_of_normal hH.2.2 le_sup_left
    (sup_le Subgroup.le_normalizer hL.1) ?_
  rintro rfl
  exact uc22p20i_not_le_M D hL bot_le

theorem s208a_normalizer_mem_hSet (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    normalizer (L : Set G) ∈ hSet D.T D.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 L : Set G)) :=
    ⟨pCoreOf 2 L, s208a_pCoreOf_ne_bot_of_calL D hL,
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L, rfl⟩
  have hle : normalizer (L : Set G) ≤ normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L
  have hLM : ¬ normalizer (L : Set G) ≤ D.M := fun h =>
    uc22p20i_not_le_M D hL (Subgroup.le_normalizer.trans h)
  have hH : normalizer (pCoreOf 2 L : Set G) ∈ hSet D.T D.M :=
    ⟨hL.1.trans hle, fun h => hLM (hle.trans h), D.standing.charTwo _ hloc⟩
  exact uc22p20b_mem_hSet D hH hL.1 hle hLM

theorem s208a_mem_hSet_of_mem_calMOf (D : Data G) {L N : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hN : N ∈ calMOf (L ⊔ D.T)) : N ∈ hSet D.T D.M :=
  ⟨le_sup_right.trans hN.2,
    fun h => uc22p20i_not_le_M D hL (le_sup_left.trans (hN.2.trans h)),
    D.standing.charTwo N hN.1.1⟩

theorem s208a_mem_calLOf_of_calLStar (D : Data G) (h1930 : H1930 D) (h205 : S20_5 D)
    {L H : Subgroup G} (hL : L ∈ calLStar D.T D.M) (hH : H ∈ hSet D.T D.M) (hLH : L ≤ H) :
    L ∈ calLOf D.T D.M H := by
  obtain ⟨K, hK, hLK⟩ := h205 h1930 L hL.1 H hH hLH
  have hKL : K = L := le_antisymm (hL.2 hK.1 hLK) hLK
  exact hKL ▸ hK

theorem s208a_nonempty_calMOf (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    (calMOf (L ⊔ D.T)).Nonempty := by
  obtain ⟨N, hN, hle⟩ := uc22p20a_exists_mem_calMOf D hL.2.2.1
  exact ⟨N, hN.1, hle⟩

omit [Finite G] in
theorem s208a_cj_le_cj {g : G} {A B : Subgroup G} (h : A ≤ B) : uc22p20bCj g A ≤ uc22p20bCj g B :=
  Subgroup.map_mono h

theorem s208a_cj_inv_cj (g : G) (A : Subgroup G) : uc22p20bCj g⁻¹ (uc22p20bCj g A) = A := by
  rw [uc22p20b_cj_cj, inv_mul_cancel, uc22p20b_cj_one]

theorem s208a_cj_cj_inv (g : G) (A : Subgroup G) : uc22p20bCj g (uc22p20bCj g⁻¹ A) = A := by
  rw [uc22p20b_cj_cj, mul_inv_cancel, uc22p20b_cj_one]

omit [Finite G] in
theorem s208a_cj_sup (g : G) (A B : Subgroup G) :
    uc22p20bCj g (A ⊔ B) = uc22p20bCj g A ⊔ uc22p20bCj g B :=
  Subgroup.map_sup A B _

omit [Finite G] in
theorem s208a_cj_eq_of_mem_normalizer {g : G} {A : Subgroup G} (hg : g ∈ normalizer (A : Set G)) :
    uc22p20bCj g A = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 hg

theorem s208a_conj_mem_cj {g x : G} {A : Subgroup G} (hx : x ∈ A) : g * x * g⁻¹ ∈ uc22p20bCj g A :=
  uc22p20b_mem_cj.2 ⟨x, hx, rfl⟩

theorem s208a_cj_mem_hSet (D : Data G) {g : G} (hg : g ∈ normalizer (D.T : Set G))
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) : uc22p20bCj g H ∈ hSet D.T D.M := by
  have hgM : g ∈ D.M := D.normalizer_le hg
  have hT : uc22p20bCj g D.T = D.T := s208a_cj_eq_of_mem_normalizer hg
  have hM : uc22p20bCj g D.M = D.M := s208a_cj_eq_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hP : pCoreOf 2 (uc22p20bCj g H) = uc22p20bCj g (pCoreOf 2 H) :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) H
  refine ⟨?_, ?_, ?_⟩
  · rw [← hT]
    exact s208a_cj_le_cj hH.1
  · intro h
    apply hH.2.1
    have := s208a_cj_le_cj (g := g⁻¹) h
    rwa [s208a_cj_inv_cj, ← hM, s208a_cj_inv_cj] at this
  · rintro _ ⟨hx, hxc⟩
    obtain ⟨y, hy, rfl⟩ := uc22p20b_mem_cj.1 hx
    have hxc' : g * y * g⁻¹ ∈ centralizer (pCoreOf 2 (uc22p20bCj g H) : Set G) := hxc
    rw [hP]
    refine s208a_conj_mem_cj (hH.2.2 ⟨hy, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩)
    have hz' : g * z * g⁻¹ ∈ pCoreOf 2 (uc22p20bCj g H) := by
      rw [hP]
      exact s208a_conj_mem_cj hz
    have h1 := (Subgroup.mem_centralizer_iff.1 hxc') _ hz'
    have h2 : g * (z * y) * g⁻¹ = g * (y * z) * g⁻¹ := by
      simpa [mul_assoc] using h1
    simpa using h2

theorem s208a_cj_orb (D : Data G) {g : G} (hg : g ∈ normalizer (D.T : Set G)) (K : Subgroup G) :
    uc22p20bCj g (uc22p20bOrb D.T K) = uc22p20bOrb D.T (uc22p20bCj g K) := by
  have hmem : ∀ {h : G}, h ∈ normalizer (D.T : Set G) → ∀ t ∈ D.T, h * t * h⁻¹ ∈ D.T :=
    fun hh t ht => (Subgroup.mem_normalizer_iff.1 hh t).1 ht
  apply le_antisymm
  · show (⨆ t : D.T, uc22p20bCj (t : G) K).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun t => ?_
    have e : (uc22p20bCj (t : G) K).map (MulAut.conj g).toMonoidHom =
        uc22p20bCj (g * t * g⁻¹) (uc22p20bCj g K) := by
      show uc22p20bCj g (uc22p20bCj (t : G) K) = _
      rw [uc22p20b_cj_cj, uc22p20b_cj_cj]
      congr 1
      group
    rw [e]
    exact uc22p20b_cj_le_orb (hmem hg t t.2)
  · refine iSup_le fun t => ?_
    have e : uc22p20bCj (t : G) (uc22p20bCj g K) =
        uc22p20bCj g (uc22p20bCj (g⁻¹ * t * g) K) := by
      rw [uc22p20b_cj_cj, uc22p20b_cj_cj]
      congr 1
      group
    rw [e]
    refine s208a_cj_le_cj (uc22p20b_cj_le_orb ?_)
    have := hmem (inv_mem hg) t t.2
    simpa using this

omit [Finite G] in
theorem s208a_bar2_nonempty_equiv {A B : Subgroup G} (e : ↥A ≃* ↥B) :
    Nonempty (Bar2 A ≃* Bar2 B) :=
  ⟨QuotientGroup.congr (CFSG.pCore 2 ↥A) (CFSG.pCore 2 ↥B) e (CFSG.pCore_map_iso 2 e)⟩

omit [Finite G] in
theorem s208a_bar2_cj_equiv (g : G) (K : Subgroup G) : Nonempty (Bar2 (uc22p20bCj g K) ≃* Bar2 K) :=
  s208a_bar2_nonempty_equiv
    (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

theorem s208a_cj_mem_calL (D : Data G) {g : G} (hg : g ∈ normalizer (D.T : Set G))
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) : uc22p20bCj g L ∈ calL D.T D.M := by
  obtain ⟨hTL, hperf, hH, K, hK, hLK⟩ := hL
  have hT : uc22p20bCj g D.T = D.T := s208a_cj_eq_of_mem_normalizer hg
  have hTn : D.T ≤ normalizer (uc22p20bCj g L : Set G) := by
    intro t ht
    have ht' : g⁻¹ * t * g ∈ D.T := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) t).1 ht
      simpa using this
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 := s208a_cj_eq_of_mem_normalizer (hTL ht')
    have h2 : uc22p20bCj t (uc22p20bCj g L) = uc22p20bCj g (uc22p20bCj (g⁻¹ * t * g) L) := by
      rw [uc22p20b_cj_cj, uc22p20b_cj_cj]
      congr 1
      group
    exact h2.trans (by rw [h1])
  refine ⟨hTn, ?_, ?_, uc22p20bCj g K, ?_, ?_⟩
  · show ⁅L.map _, L.map _⁆ = L.map _
    rw [← Subgroup.map_commutator, hperf]
  · have := s208a_cj_mem_hSet D hg hH
    rwa [s208a_cj_sup, hT] at this
  · obtain ⟨hsub, hKperf, hq⟩ := hK
    refine ⟨CFSG.Quasithin.A3.subnormal_map _ hsub, ?_, ?_⟩
    · show ⁅K.map _, K.map _⁆ = K.map _
      rw [← Subgroup.map_commutator, hKperf]
    · obtain ⟨e⟩ := s208a_bar2_cj_equiv g K
      exact CFSG.Open.IsQuasisimple.of_mulEquiv e hq
  · show uc22p20bCj g L = uc22p20bOrb D.T (uc22p20bCj g K)
    rw [hLK]
    exact s208a_cj_orb D hg K

theorem s208a_cj_mem_calLStar (D : Data G) {g : G} (hg : g ∈ normalizer (D.T : Set G))
    {L : Subgroup G} (hL : L ∈ calLStar D.T D.M) : uc22p20bCj g L ∈ calLStar D.T D.M := by
  have hg' : g⁻¹ ∈ normalizer (D.T : Set G) := inv_mem hg
  refine ⟨s208a_cj_mem_calL D hg hL.1, fun L' hL' hle => ?_⟩
  have h1 : L ≤ uc22p20bCj g⁻¹ L' := by
    have := s208a_cj_le_cj (g := g⁻¹) hle
    rwa [s208a_cj_inv_cj] at this
  have h2 := hL.2 (s208a_cj_mem_calL D hg' hL') h1
  have := s208a_cj_le_cj (g := g) h2
  rwa [s208a_cj_cj_inv] at this

end CFSG.LocalAnalysis.UniquenessCase.UC22
