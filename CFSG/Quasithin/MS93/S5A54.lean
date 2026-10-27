module

public import CFSG.Quasithin.MS93.S5ACand
public import CFSG.Quasithin.MS93.S5ALift

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Transfer

variable (h : PUHyp M T L)

omit [Fintype F] in
theorem imM_le_vPre {K : Subgroup G} {Y : Subgroup ↥(StatedSp 2 F)} (hY : imSp a K ≤ Y) :
    imM h.le K ≤ vPre h.le a Y :=
  Subgroup.map_mono (Subgroup.map_le_iff_le_comap.1 hY)

omit [Fintype F] in
theorem vIm_imM (K : Subgroup G) : vIm h.le a (imM h.le K) = imSp a K := by
  rw [vIm, imM, Subgroup.comap_map_eq_self_of_injective (puAmalgam h.le).ofA_injective]
  rfl

omit [Fintype F] in
theorem card_offSet_baseA (q : ℕ) :
    Nat.card (offSet h.le L q (baseA _) (baseB _)) = Nat.card (offSetM M T L q) := by
  rw [offSet_baseA h q]
  refine Nat.card_image_of_injOn fun E hE E' hE' hEE' => ?_
  have hEM : E ≤ M := (offSetM_le q hE).trans h.le
  have hE'M : E' ≤ M := (offSetM_le q hE').trans h.le
  exact le_antisymm ((imM_le_imM_iff h.le hEM).1 hEE'.le) ((imM_le_imM_iff h.le hE'M).1 hEE'.ge)

end Transfer

theorem exists_isCandSp_ne_bot_of (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
    (hb : 0 < critDist (puAmalgam h.le)) : ∃ B, IsCandSp (imSp a T) B ∧ B ≠ ⊥ := by
  have := hd.charP
  obtain ⟨⟨E, hEβ, -, hEα, hEc⟩, -⟩ := ms22_vi (puAmalgam h.le) h.hyp20 hb h.centHyp
    (PU.isMVtx_baseA _) (adj_baseA_baseB _)
  rw [puAmalgam.qv_baseB] at hEβ
  obtain ⟨E₀, hE₀T, hE₀M, rfl⟩ := exists_eq_imM h.le hEβ
  rw [qv_baseA_eq h] at hEα hEc
  rw [puAmalgam.zm_baseA, relIndex_centralizer_imM h.le (Z0q_le M T) hE₀M,
    relIndex_imM h.le hE₀M] at hEc
  have hEα' : ¬ E₀ ≤ pCoreOf 2 M := fun hle => hEα (imM_mono h.le hle)
  have hAT : imSp a E₀ ≤ imSp a T := imSp_mono a hE₀T
  have hA1 : imSp a E₀ ≠ ⊥ := by
    intro hA
    apply hEα'
    have h1 : (pCoreOf 2 M).relIndex E₀ = 1 := by
      rw [← hd.card_imSp h hE₀T, hA, Subgroup.card_bot]
    exact Subgroup.relIndex_eq_one.1 h1
  refine exists_isCandSp_ne_bot (IsSp4Data.isPGroup_imSp (a := a) h) hAT hA1 ?_
  obtain ⟨nv⟩ := hd.nonempty_natVec
  calc Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp (imSp a E₀)) *
        (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) := nv.card_le_relIndex E₀
    _ ≤ Nat.card (MSP.fixSp (imSp a E₀)) *
        (Subgroup.centralizer (E₀ : Set G)).relIndex (Z0q M T) :=
      Nat.mul_le_mul_left _ (Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le)
        (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.1
          (Subgroup.isFiniteRelIndex_iff_finiteIndex.2 inferInstance)))
    _ ≤ Nat.card (MSP.fixSp (imSp a E₀)) * Nat.card (imSp a E₀) := by
      rw [hd.card_imSp h hE₀T]
      exact Nat.mul_le_mul_left _ hEc

theorem relIndex_eq_of_imSp_xPoint (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
    {E : Subgroup G} (hET : E ≤ T) {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hE : imSp a E = MSP.xPoint p) : (pCoreOf 2 M).relIndex E = 2 ^ k := by
  rw [← hd.card_imSp h hET, hE, MSP.card_xPoint hp, hd.nat_card_eq]

theorem relIndex_centralizer_eq_of_imSp_xPoint (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
    {E : Subgroup G} (hEM : E ≤ M) {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hE : imSp a E = MSP.xPoint p) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k := by
  have hl := (sp4Lift G M T L h k F _ _ a hd).2.2
  have hq : 0 < 2 ^ k := pow_pos two_pos k
  have hV := hd.card_eq_mul_relIndex hl hEM
  have h3 : Module.finrank F (MSP.fixSp (MSP.xPoint p)) = 3 := by
    have := MSP.finrank_perp p
    rw [MSP.fixSp_xPoint hp]
    unfold MSP.IsPoint at hp
    omega
  rw [hE, MSP.card_fixSp, h3, MSP.card_V4, hd.nat_card_eq] at hV
  refine Nat.eq_of_mul_eq_mul_left (pow_pos hq 3) ?_
  rw [← hV]
  ring

omit [Fintype F] in
theorem imM_sup_of_le (h : PUHyp M T L) {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM h.le (K ⊔ K') = imM h.le K ⊔ imM h.le K' := by
  rw [imM, imM, imM, Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

theorem liftT_sup (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
    {A B : Subgroup ↥(StatedSp 2 F)} (hA : A ≤ imSp a T) (hB : B ≤ imSp a T) :
    liftT T a (A ⊔ B) = liftT T a A ⊔ liftT T a B := by
  have hmono : ∀ {A' B' : Subgroup ↥(StatedSp 2 F)}, A' ≤ B' → liftT T a A' ≤ liftT T a B' :=
    fun hle => inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono hle))
  refine le_antisymm ?_ (sup_le (hmono le_sup_left) (hmono le_sup_right))
  have hQ : pCoreOf 2 M ≤ liftT T a A ⊔ liftT T a B :=
    (hd.pCoreOf_le_liftT h A).trans le_sup_left
  have hT : liftT T a A ⊔ liftT T a B ≤ T := sup_le (liftT_le A) (liftT_le B)
  have him : A ⊔ B ≤ imSp a (liftT T a A ⊔ liftT T a B) :=
    sup_le ((imSp_liftT hA).symm.le.trans (imSp_mono a le_sup_left))
      ((imSp_liftT hB).symm.le.trans (imSp_mono a le_sup_right))
  calc liftT T a (A ⊔ B) ≤ liftT T a (imSp a (liftT T a A ⊔ liftT T a B)) := hmono him
    _ = liftT T a A ⊔ liftT T a B := hd.liftT_imSp h hQ hT

theorem candMax_ne_xPoint (h51 : S51) (hd : IsSp4Data M T L k F a)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) :
    candMax (imSp a T) ≠ {MSP.xPoint p} := by
  intro hX
  have hl := (sp4Lift G M T L h k F _ _ a hd).2.2
  have hJ := hd.jOffM_eq_of_candMax_eq h hl hX
  have hA₀ : MSP.xPoint p ∈ candMax (imSp a T) := hX ▸ rfl
  have hE₀T : liftT T a (MSP.xPoint p) ≤ T := liftT_le _
  have hE₀M : liftT T a (MSP.xPoint p) ≤ M := hE₀T.trans h.le
  have himE : imSp a (liftT T a (MSP.xPoint p)) = MSP.xPoint p := imSp_liftT hA₀.1.1
  have hcard1 := relIndex_eq_of_imSp_xPoint hd h hE₀T hp himE
  have hcard2 := relIndex_centralizer_eq_of_imSp_xPoint hd h hE₀M hp himE
  refine h51 G M T L h hmin hb k F _ _ a hd (imM h.le (liftT T a (MSP.xPoint p)))
    (imM h.le (liftT T a (MSP.xPoint p))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [puAmalgam.qv_baseB]
    exact imM_mono h.le hE₀T
  · rw [puAmalgam.qv_baseB]
    exact imM_mono h.le hE₀T
  · rw [qv_baseA_eq h, relIndex_imM h.le hE₀M, hcard1]
  · rw [uSub_baseA h, relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M, hcard2]
  · rw [qv_baseA_eq h, relIndex_imM h.le hE₀M, hcard1]
  · rw [uSub_baseA h, relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M, hcard2]
  · rw [jOff_baseA h, hJ, sup_idem]

theorem jOffM_ne_xPoint_sup (h51 : S51) (hd : IsSp4Data M T L k F a)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    {p₁ p₂ : Submodule F (MSP.V4 F)} (hp₁ : MSP.IsPoint p₁) (hp₂ : MSP.IsPoint p₂)
    (hJ : imSp a (jOffM M T L (2 ^ k)) = MSP.xPoint p₁ ⊔ MSP.xPoint p₂) : False := by
  have hl := (sp4Lift G M T L h k F _ _ a hd).2.2
  have hJT : jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  obtain ⟨A₀, hA₀⟩ := candMax_nonempty (imSp a T)
  have hQJ : pCoreOf 2 M ≤ jOffM M T L (2 ^ k) :=
    (hd.pCoreOf_le_liftT h A₀).trans
      (le_iSup₂_of_le (liftT T a A₀) (hd.liftT_mem_offSetM h hl hA₀) le_rfl)
  have hX₁ : MSP.xPoint p₁ ≤ imSp a T := (hJ ▸ le_sup_left).trans (imSp_mono a hJT)
  have hX₂ : MSP.xPoint p₂ ≤ imSp a T := (hJ ▸ le_sup_right).trans (imSp_mono a hJT)
  have hJeq : jOffM M T L (2 ^ k) = liftT T a (MSP.xPoint p₁) ⊔ liftT T a (MSP.xPoint p₂) := by
    rw [← hd.liftT_imSp h hQJ hJT, hJ, liftT_sup hd h hX₁ hX₂]
  have hE₁T : liftT T a (MSP.xPoint p₁) ≤ T := liftT_le _
  have hE₂T : liftT T a (MSP.xPoint p₂) ≤ T := liftT_le _
  have hE₁M := hE₁T.trans h.le
  have hE₂M := hE₂T.trans h.le
  have him₁ : imSp a (liftT T a (MSP.xPoint p₁)) = MSP.xPoint p₁ := imSp_liftT hX₁
  have him₂ : imSp a (liftT T a (MSP.xPoint p₂)) = MSP.xPoint p₂ := imSp_liftT hX₂
  refine h51 G M T L h hmin hb k F _ _ a hd (imM h.le (liftT T a (MSP.xPoint p₁)))
    (imM h.le (liftT T a (MSP.xPoint p₂))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [puAmalgam.qv_baseB]
    exact imM_mono h.le hE₁T
  · rw [puAmalgam.qv_baseB]
    exact imM_mono h.le hE₂T
  · rw [qv_baseA_eq h, relIndex_imM h.le hE₁M, relIndex_eq_of_imSp_xPoint hd h hE₁T hp₁ him₁]
  · rw [uSub_baseA h, relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₁M,
      relIndex_centralizer_eq_of_imSp_xPoint hd h hE₁M hp₁ him₁]
  · rw [qv_baseA_eq h, relIndex_imM h.le hE₂M, relIndex_eq_of_imSp_xPoint hd h hE₂T hp₂ him₂]
  · rw [uSub_baseA h, relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₂M,
      relIndex_centralizer_eq_of_imSp_xPoint hd h hE₂M hp₂ him₂]
  · rw [jOff_baseA h, hJeq, imM_sup_of_le h hE₁M hE₂M]

theorem sp4_54M (h51 : S51) (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    (∃ (A₀ : Subgroup ↥(StatedSp 2 F)) (l : Submodule F (MSP.V4 F)),
      candMax (imSp a T) = {A₀} ∧ MSP.IsLine l ∧ imSp a T ≤ MSP.stab l ∧ A₀ ≤ MSP.qLine l ∧
      Nat.card F ^ 2 ≤ Nat.card A₀ ∧ jOffM M T L (2 ^ k) = liftT T a A₀) ∨
    (∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧ imSp a T = MSP.qPoint p ∧
      jOffM M T L (2 ^ k) = T) := by
  have hl := (sp4Lift G M T L h k F _ _ a hd).2.2
  have := hd.charP
  have hne := exists_isCandSp_ne_bot_of hd h (by omega)
  have hX : ∀ p, MSP.IsPoint p → candMax (imSp a T) ≠ {MSP.xPoint p} :=
    fun p hp => candMax_ne_xPoint h51 hd h hmin hb hp
  rcases sp4_54 (IsSp4Data.isPGroup_imSp (a := a) h) hne hX with
    ⟨A₀, l, hA, hl', hTl, hA₀l, hA₀card⟩ | ⟨-, p, hp, hTp, hsup⟩
  · exact Or.inl ⟨A₀, l, hA, hl', hTl, hA₀l, hA₀card, hd.jOffM_eq_of_candMax_eq h hl hA⟩
  · exact Or.inr ⟨p, hp, hTp, hd.jOffM_eq_of_iSup h hl hsup⟩

end S5

open S5 in
theorem s54_of (h51 : S51) : S54 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd
  have hl := (sp4Lift G M T L h k F _ _ a hd).2.2
  have := hd.charP
  have hne := exists_isCandSp_ne_bot_of hd h (by omega)
  have hX : ∀ p, MSP.IsPoint p → candMax (imSp a T) ≠ {MSP.xPoint p} :=
    fun p hp => candMax_ne_xPoint h51 hd h hmin hb hp
  rcases sp4_54 (IsSp4Data.isPGroup_imSp (a := a) h) hne hX with
    ⟨A₀, l, hA, hl', hTl, hA₀l, hA₀card⟩ | ⟨hcard, p, hp, hTp, hsup⟩
  · left
    have hJ := hd.jOffM_eq_of_candMax_eq h hl hA
    have hA₀ : A₀ ∈ candMax (imSp a T) := hA ▸ rfl
    have hA₀T : A₀ ≤ imSp a T := hA₀.1.1
    refine ⟨?_, ⟨l, hl', ?_, ?_⟩, ?_⟩
    · rw [card_offSet_baseA h, hd.card_offSetM h hl, hA, Nat.card_unique]
    · rw [puAmalgam.qv_baseB]
      exact imM_le_vPre h hTl
    · rw [jOff_baseA h, hJ]
      exact imM_le_vPre h (by rw [imSp_liftT hA₀T]; exact hA₀l)
    · rw [jOff_baseA h, hJ, qv_baseA_eq h, relIndex_imM h.le ((liftT_le _).trans h.le),
        ← hd.card_imSp h (liftT_le _), imSp_liftT hA₀T, ← hd.nat_card_eq]
      exact hA₀card
  · right
    have hJ := hd.jOffM_eq_of_iSup h hl hsup
    refine ⟨?_, ?_, p, hp, ?_⟩
    · rw [card_offSet_baseA h, hd.card_offSetM h hl, hcard, hd.nat_card_eq]
    · rw [jOff_baseA h, hJ, puAmalgam.qv_baseB]
    · rw [puAmalgam.qv_baseB, vIm_imM h, hTp]

end CFSG.Quasithin.MS93
