module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveInst
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeLStarClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20za
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rr
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_bot_of_perfect_of_isPGroup_two {H : Type*} [Group H] [Finite H]
    {B : Subgroup H} (hB : ⁅B, B⁆ = B) (hB2 : IsPGroup 2 B) : B = ⊥ := by
  have := Fact.mk Nat.prime_two
  have : Group.IsNilpotent B := hB2.isNilpotent
  have htop : _root_.commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

private theorem nontrivial_bar2_of_perfect {H : Type} [Group H] [Finite H] {Y : Subgroup H}
    (hperf : ⁅Y, Y⁆ = Y) (hne : Y ≠ ⊥) : Nontrivial (Bar2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have htop : CFSG.pCore 2 ↥Y = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk x : Bar2 Y) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp hx
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
  rw [htop] at hP
  exact hne (eq_bot_of_perfect_of_isPGroup_two hperf (hP.of_equiv Subgroup.topEquiv))

omit [Finite G] in
private theorem le_centralizer_of_barSub_eq_bot {A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A) (h : barSub (⊥ : Subgroup G) A hA X = ⊥) :
    X ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  have h1 : actTil (⊥ : Subgroup G) A hA ⟨x, hX hx⟩ = 1 := by
    have hmem := actTil_mem_barSub (⊥ : Subgroup G) A hA hx (hX hx)
    rwa [h, Subgroup.mem_bot] at hmem
  have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) A hA ⟨x, hX hx⟩).1 h1
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h3 : x * a * x⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.1 (h2 a ha)
  have h4 : x * a * x⁻¹ = a := mul_inv_eq_one.1 h3
  calc a * x = (x * a * x⁻¹) * x := by rw [h4]
    _ = x * a := by group

private noncomputable def bar2Map {A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A) :
    Bar2 X →* Bar2 (barSub (⊥ : Subgroup G) A hA X) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥X)
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥(barSub (⊥ : Subgroup G) A hA X))).comp
      (barSubHom hA X hX)) (by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have hle : (CFSG.pCore 2 ↥X).map (barSubHom hA X hX) ≤
          CFSG.pCore 2 ↥(barSub (⊥ : Subgroup G) A hA X) :=
        CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
          (Subgroup.Normal.map CFSG.pCore_normal _ (barSubHom_surjective hA X hX))
          (CFSG.pCore_isPGroup.map _)
      exact hle ⟨x, hx, rfl⟩)

private theorem bar2Map_surjective {A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A) : Function.Surjective (bar2Map hA hX) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := barSubHom_surjective hA X hX z
  exact ⟨QuotientGroup.mk x, rfl⟩

private theorem bar2Map_central {A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A) (hperf : ⁅X, X⁆ = X)
    (hne : barSub (⊥ : Subgroup G) A hA X ≠ ⊥) (hq : CFSG.Open.IsQuasisimple (Bar2 X)) :
    Nontrivial (Bar2 (barSub (⊥ : Subgroup G) A hA X)) ∧
      (bar2Map hA hX).ker ≤ Subgroup.center (Bar2 X) := by
  have hnt : Nontrivial (Bar2 (barSub (⊥ : Subgroup G) A hA X)) :=
    nontrivial_bar2_of_perfect (barSub_commutator hA hX hperf) hne
  refine ⟨hnt, CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 X)).2.2.1.mpr hq) ?_⟩
  obtain ⟨y, hy⟩ := exists_ne (1 : Bar2 (barSub (⊥ : Subgroup G) A hA X))
  obtain ⟨x, rfl⟩ := bar2Map_surjective hA hX y
  exact ⟨x, hy⟩

private theorem commutator_le_pCoreOf_of_ne' {M K K' : Subgroup G} (hK : K ∈ calC M)
    (hK' : K' ∈ calC M) (hne : K ≠ K') : ⁅K, K'⁆ ≤ pCoreOf 2 M := by
  have hcomm : ⁅barImage M K, barImage M K'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (uc22p22l_barImage_commute hK hK' hne a ha b hb).symm
  have hsub : ⁅K.subgroupOf M, K'.subgroupOf M⁆ ≤ CFSG.pCore 2 ↥M := by
    have h1 : (⁅K.subgroupOf M, K'.subgroupOf M⁆).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = ⊥ := by
      rw [Subgroup.map_commutator]
      exact hcomm
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  rw [CFSG.GroupTheory.commutator_subgroupOf_eq hK.1.le hK'.1.le] at hsub
  have hM : ⁅K, K'⁆ ≤ M := Subgroup.commutator_le_of_le hK.1.le hK'.1.le
  intro x hx
  exact ⟨⟨x, hM hx⟩, hsub hx, rfl⟩

omit [Finite G] in
private theorem barSub_commutator_eq {A X Y : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A) (hY : Y ≤ stabTil (⊥ : Subgroup G) A) :
    barSub (⊥ : Subgroup G) A hA ⁅X, Y⁆ =
      ⁅barSub (⊥ : Subgroup G) A hA X, barSub (⊥ : Subgroup G) A hA Y⁆ := by
  unfold barSub
  rw [← CFSG.GroupTheory.commutator_subgroupOf_eq hX hY, Subgroup.map_commutator]

omit [Finite G] in
private theorem isPGroup_barSub_two {A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A) (h : IsPGroup 2 X) :
    IsPGroup 2 (barSub (⊥ : Subgroup G) A hA X) := by
  unfold barSub
  exact (h.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm).map _

private theorem fixed_L0_eq_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    c.V ⊓ Subgroup.centralizer (c.L0 : Set G) = ⊥ := by
  by_contra hne
  have hTV : D.T ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)
  have hTL : D.T ≤ Subgroup.normalizer (c.L0 : Set G) := c.hL0.1.1
  have hTC : D.T ≤ Subgroup.normalizer (Subgroup.centralizer (c.L0 : Set G) : Set G) :=
    hTL.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.L0)
  have hT : D.T ≤ Subgroup.normalizer
      ((c.V ⊓ Subgroup.centralizer (c.L0 : Set G) : Subgroup G) : Set G) :=
    (le_inf hTV hTC).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨z, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Ctx23L.inf_Z_ne_bot c inf_le_left hne hT)
  have hzC : (z : G) ∈ Subgroup.centralizer (c.L0 : Set G) := z.2.1.2
  have hzZ : (z : G) ∈ D.Z := z.2.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hLz : c.L0 ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro l hl
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.mp hzC l hl).symm
  exact Ctx23L.L0_not_le_M c
    (hLz.trans (Ctx23.centralizer_le_M c.toCtx23 (Data.Z_le_U D hzZ) hz1'))

private theorem components_two_of_simple
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {D : Data G} (h207 : S20_7 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) :
    ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
      CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ := by
  have hS : IsSimpleGroup (Bar2 L) →
      ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
        CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ := fun h => by
    have := h
    exact ⟨⊤, ⊤, fun K' hq hsub => Or.inl (uc22p22r_eq_top_of_isSimple hq hsub)⟩
  have hQ : CFSG.Open.IsQuasisimple (Bar2 L) →
      ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
        CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ :=
    fun hX => ⟨⊤, ⊤, fun K' hq hsub => Or.inl (uc22p22r_eq_top_of_quasisimple hX hq hsub)⟩
  have hC : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ},
      t ∈ CFSG.Blueprint.classicalTags → LieModel (Bar2 L) t m 2 f →
      ∃ C₁ C₂ : Subgroup (Bar2 L), ∀ K' : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥K' →
        CFSG.Open.IsSubnormal K' ⊤ → K' = C₁ ∨ K' = C₂ :=
    fun ht h => hS (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h)
  rcases h207 h1930 L hL with ⟨n, -, h⟩ | h | h | h | h | h | ⟨n, -, h⟩ | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact hS (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h)
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hS (hG2 _ _ h)
    · exact hS (h3D4 _ _ h)
    · exact hS (h2F4 _ _ h)
    · exact hC (by decide) h
    · exact hQ h.1
    · exact hQ h.1
    · exact hC (by decide) h
    · exact hC (by decide) h
  · exact hC (by decide) h
  · exact hC (by decide) h
  · exact hC (by decide) h
  · exact hS (h3D4 _ _ h)
  · exact hS (h3D4 _ _ h)
  · exact uc22p22r_components_of_szL2Product h
  · exact uc22p22r_components_of_suCentralSquare h

private theorem calC_card_le_two_of_simple
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {D : Data G} (h207 : S20_7 D) (h1930 : H1930 D) {L K₁ K₂ K₃ : Subgroup G}
    (hL : L ∈ calL D.T D.M) (h₁ : K₁ ∈ calC L) (h₂ : K₂ ∈ calC L) (h₃ : K₃ ∈ calC L) :
    K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  obtain ⟨C₁, C₂, hC⟩ := components_two_of_simple hG2 h3D4 h2F4 h207 h1930 hL
  have himg : ∀ {K : Subgroup G}, K ∈ calC L → barImage L K = C₁ ∨ barImage L K = C₂ := by
    intro K hK
    obtain ⟨K', hK'eq, -, -, hq, hsub⟩ := uc22p22r_bar2_quasisimple_iso hK
    have hbar : barImage L K = K' := by
      rw [hK'eq]
      rfl
    rw [hbar]
    exact hC K' hq hsub
  rcases himg h₁ with e₁ | e₁ <;> rcases himg h₂ with e₂ | e₂ <;> rcases himg h₃ with e₃ | e₃ <;>
    first
    | exact Or.inl (uc22p22u_calC_ext h₁ h₂ (e₁.trans e₂.symm))
    | exact Or.inr (Or.inl (uc22p22u_calC_ext h₁ h₃ (e₁.trans e₃.symm)))
    | exact Or.inr (Or.inr (uc22p22u_calC_ext h₂ h₃ (e₂.trans e₃.symm)))

private theorem eq_L_or_eq_sup_conj_aux
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) (h207 : S20_7 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    K = c.L ∨ ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
  by_cases hKL : K = c.L
  · exact Or.inl hKL
  right
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hLcal : c.L ∈ calL D.T D.M := c.hL.1
  obtain ⟨t, htT, hKt⟩ : ∃ t ∈ D.T, K.map (MulAut.conj t).toMonoidHom ≠ K := by
    by_contra h
    push Not at h
    apply hKL
    rw [hgen]
    apply le_antisymm
    · exact le_iSup_of_le ⟨1, D.T.one_mem⟩ (h 1 D.T.one_mem).ge
    · exact iSup_le fun s => (h s s.2).le
  have hKtC : K.map (MulAut.conj t).toMonoidHom ∈ calC c.L :=
    calC_map_conj_of_mem_normalizer hK (hTL htT)
  have hsup : c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    apply le_antisymm
    · conv_lhs => rw [hgen]
      refine iSup_le fun s => ?_
      have hKs : K.map (MulAut.conj (s : G)).toMonoidHom ∈ calC c.L :=
        calC_map_conj_of_mem_normalizer hK (hTL s.2)
      rcases calC_card_le_two_of_simple hG2 h3D4 h2F4 h207 h1930 hLcal hK hKtC hKs with
        h | h | h
      · exact absurd h.symm hKt
      · exact h ▸ le_sup_left
      · exact h ▸ le_sup_right
    · exact sup_le (CFSG.Quasithin.A3.subnormal_le hK.1) (CFSG.Quasithin.A3.subnormal_le hKtC.1)
  refine ⟨t, htT, ?_, hsup⟩
  clear hG2 h3D4 h2F4
  intro heq
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) A :=
    (CFSG.Quasithin.A3.subnormal_le hK.1).trans hLstab
  have hKtstab : K.map (MulAut.conj t).toMonoidHom ≤ stabTil (⊥ : Subgroup G) A :=
    (CFSG.Quasithin.A3.subnormal_le hKtC.1).trans hLstab
  have hperfX : ⁅barSub (⊥ : Subgroup G) A hA K, barSub (⊥ : Subgroup G) A hA K⁆ =
      barSub (⊥ : Subgroup G) A hA K := barSub_commutator hA hKstab hK.2.1
  have hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    commutator_le_pCoreOf_of_ne' hK hKtC (Ne.symm hKt)
  have hX2 : IsPGroup 2 (barSub (⊥ : Subgroup G) A hA K) := by
    have hle : barSub (⊥ : Subgroup G) A hA K ≤
        barSub (⊥ : Subgroup G) A hA (CFSG.Open.pCoreOf 2 c.L) := by
      calc barSub (⊥ : Subgroup G) A hA K
          = ⁅barSub (⊥ : Subgroup G) A hA K, barSub (⊥ : Subgroup G) A hA K⁆ := hperfX.symm
        _ = ⁅barSub (⊥ : Subgroup G) A hA K,
            barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)⁆ := by
          rw [heq]
        _ = barSub (⊥ : Subgroup G) A hA ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ :=
          (barSub_commutator_eq hA hKstab hKtstab).symm
        _ ≤ barSub (⊥ : Subgroup G) A hA (CFSG.Open.pCoreOf 2 c.L) :=
          barSub_mono (⊥ : Subgroup G) A hA hcomm
    exact (isPGroup_barSub_two hA ((CFSG.LieType.BorelTits.pCoreOf_le 2 c.L).trans hLstab)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L)).to_le hle
  have hXbot : barSub (⊥ : Subgroup G) A hA K = ⊥ :=
    eq_bot_of_perfect_of_isPGroup_two hperfX hX2
  have hLbot : barSub (⊥ : Subgroup G) A hA c.L = ⊥ := by
    rw [(congrArg (barSub (⊥ : Subgroup G) A hA) hsup).trans (barSub_sup hA hKstab hKtstab),
      heq, hXbot, sup_bot_eq]
  have hcent := le_centralizer_of_barSub_eq_bot hA hLstab hLbot
  apply hAne
  rw [eq_bot_iff, ← Ctx23L.fixed_L_eq_bot c]
  intro a ha
  exact ⟨hAV ha, Subgroup.mem_centralizer_iff.mpr fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hcent hl) a ha).symm⟩

private theorem eq_bot_of_perfect_of_isSolvable {H : Type*} [Group H] {B : Subgroup H}
    (hB : ⁅B, B⁆ = B) [Group.IsSolvable B] : B = ⊥ := by
  have htop : _root_.commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

private theorem le_of_isPGroup_of_not_dvd_index' {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {N P : Subgroup H} [N.Normal] (hN : ¬ p ∣ N.index) (hP : IsPGroup p P) :
    P ≤ N := by
  have hQ : IsPGroup p (P.map (QuotientGroup.mk' N)) := hP.map _
  have hdvd : Nat.card (P.map (QuotientGroup.mk' N)) ∣ N.index :=
    Subgroup.card_subgroup_dvd_card _
  have h1 : Nat.card (P.map (QuotientGroup.mk' N)) = 1 := by
    rcases hQ.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (h.trans hdvd) hN
  rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

private theorem le_of_le_normalizer_of_odd {S P L : Subgroup G} (hS : IsPGroup 2 S)
    (hSL : S ≤ L) (hPL : P ≤ L) (hSN : S ≤ Subgroup.normalizer (P : Set G))
    (hodd : ¬ 2 ∣ P.relIndex L) : S ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : P ⊔ S ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hSN
  have : (P.subgroupOf (P ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hQN
  have hidx : ¬ 2 ∣ (P.subgroupOf (P ⊔ S)).index := by
    intro h
    apply hodd
    rw [← Subgroup.relIndex_mul_relIndex P (P ⊔ S) L le_sup_left (sup_le hPL hSL)]
    exact h.mul_right _
  have hS' : IsPGroup 2 (S.subgroupOf (P ⊔ S)) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hle := le_of_isPGroup_of_not_dvd_index' hidx hS'
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (show (⟨x, (le_sup_right : S ≤ P ⊔ S) hx⟩ : ↥(P ⊔ S)) ∈
    S.subgroupOf (P ⊔ S) from hx))

private theorem not_two_dvd_relIndex_of_parabolicOf {L P : Subgroup G} (hP : ParabolicOf L P) :
    ¬ 2 ∣ P.relIndex L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hO, -, S, hS⟩ := hP
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hSP : (S : Subgroup (Bar2 L)) ≤ (P.subgroupOf L).map π :=
    Subgroup.le_normalizer.trans hS
  have hO' : CFSG.pCore 2 ↥L ≤ P.subgroupOf L := fun z hz => hO ⟨z, hz, rfl⟩
  have hle : (S : Subgroup (Bar2 L)).comap π ≤ P.subgroupOf L := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hSP hx
    have hyx' : y⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq]
      exact hyx
    simpa using (P.subgroupOf L).mul_mem hy (hO' hyx')
  have hidx : ((S : Subgroup (Bar2 L)).comap π).index = (S : Subgroup (Bar2 L)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  intro h
  exact S.not_dvd_index (hidx ▸ h.trans (Subgroup.index_dvd_of_le hle))

private theorem shape_of_szL2Product {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSzL2Product X n) {C : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥C)
    (hsub : CFSG.Open.IsSubnormal C ⊤) : IsSz ↥C n ∨ IsL2 ↥C n := by
  obtain ⟨A, B, _, _, ⟨f⟩, hA, hB⟩ := h
  have hsimp : ∀ {Y : Type} [Group Y], (IsSz Y n ∨ IsL2 Y n) → IsSimpleGroup Y := by
    intro Y _ hY
    rcases hY with hY | hY
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hY
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY
  have : IsSimpleGroup A := hsimp hA
  have : IsSimpleGroup B := hsimp hB
  set N₁ : Subgroup X := ((MonoidHom.snd A B).comp f.toMonoidHom).ker with hN₁
  set N₂ : Subgroup X := ((MonoidHom.fst A B).comp f.toMonoidHom).ker with hN₂
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = f.symm ((f x).1, 1) * f.symm (1, (f x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · show (f (f.symm ((f x).1, 1))).2 = 1
      simp
    · show (f (f.symm (1, (f x).2))).1 = 1
      simp
  have hK' : CFSG.Open.IsComponentOf C ⊤ := ⟨le_top, hsub, hq⟩
  have hne : C ≠ ⊥ := uc22p22r_ne_bot_of_equiv (MulEquiv.refl _) hq
  have hsubM : C.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.mp hsub
  have hshape : ∀ {Y : Type} [Group Y], (IsSz Y n ∨ IsL2 Y n) → Nonempty (↥C ≃* Y) →
      IsSz ↥C n ∨ IsL2 ↥C n := by
    intro Y _ hY ⟨g⟩
    rcases hY with hY | hY
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv g.symm hY)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv g.symm hY)
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · exact hshape hA (uc22p22r_equiv_factor f hsubM hne hle)
  · exact hshape hB (uc22p22r_equiv_factor (f.trans MulEquiv.prodComm) hsubM hne
      (fun x hx => hle hx))

private theorem shape_of_suCentralSquare {X : Type} [Group X] [Finite X]
    (h : IsSU3CentralSquare X) {C : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥C)
    (hsub : CFSG.Open.IsSubnormal C ⊤) : IsSU3 ↥C 3 := by
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  have : K₁.Normal := uc22p22r_normal_of_commuting hsup hcomm
  have : K₂.Normal :=
    uc22p22r_normal_of_commuting (by rwa [sup_comm]) fun a ha b hb => (hcomm b hb a ha).symm
  have hc₁ : CFSG.Open.IsComponentOf K₁ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal ‹K₁.Normal›), hK₁.1⟩
  have hc₂ : CFSG.Open.IsComponentOf K₂ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal ‹K₂.Normal›), hK₂.1⟩
  have hK' : CFSG.Open.IsComponentOf C ⊤ := ⟨le_top, hsub, hq⟩
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · rw [CFSG.ComponentClassification.LocalComponents.eq_of_le C K₁ hK' hc₁ hle]
    exact hK₁
  · rw [CFSG.ComponentClassification.LocalComponents.eq_of_le C K₂ hK' hc₂ hle]
    exact hK₂

private theorem product_shapes_of_simple
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {D : Data G} (h207 : S20_7 D) (h1930 : H1930 D) {L K K' : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L) (hK' : K' ∈ calC L) (hne : K ≠ K') :
    ∃ n : ℕ, ∀ L' ∈ ({K, K'} : Set (Subgroup G)),
      IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3) := by
  have himg : ∀ {Y : Subgroup G}, Y ∈ calC L → ∃ e : Bar2 Y ≃* ↥(barImage L Y),
      CFSG.Open.IsQuasisimple ↥(barImage L Y) ∧ CFSG.Open.IsSubnormal (barImage L Y) ⊤ := by
    intro Y hY
    obtain ⟨Y', hY'eq, ⟨e, -⟩, -, hq, hsub⟩ := uc22p22r_bar2_quasisimple_iso hY
    have hbar : barImage L Y = Y' := by
      rw [hY'eq]
      rfl
    rw [hbar]
    exact ⟨e, hq, hsub⟩
  obtain ⟨eK, hqK, hsK⟩ := himg hK
  obtain ⟨eK', hqK', hsK'⟩ := himg hK'
  have hone : ∀ (hS : ∀ Y : Subgroup (Bar2 L), CFSG.Open.IsQuasisimple ↥Y →
      CFSG.Open.IsSubnormal Y ⊤ → Y = ⊤), False := fun hS =>
    hne (uc22p22u_calC_ext hK hK' ((hS _ hqK hsK).trans (hS _ hqK' hsK').symm))
  have hS : IsSimpleGroup (Bar2 L) → False := fun h => by
    have := h
    exact hone fun Y hq hsub => uc22p22r_eq_top_of_isSimple hq hsub
  have hQ : CFSG.Open.IsQuasisimple (Bar2 L) → False := fun hX =>
    hone fun Y hq hsub => uc22p22r_eq_top_of_quasisimple hX hq hsub
  have hC : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ},
      t ∈ CFSG.Blueprint.classicalTags → LieModel (Bar2 L) t m 2 f → False :=
    fun ht h => hS (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h)
  have hE : ∀ {f : ℕ}, (IsG2 (Bar2 L) f ∨ Is3D4 (Bar2 L) f ∨
      LieModel (Bar2 L) .twistedF4 0 2 f) → False := by
    intro f h
    rcases h with h | h | h
    · exact hS (hG2 _ _ h)
    · exact hS (h3D4 _ _ h)
    · exact hS (h2F4 _ _ h)
  clear hG2 h3D4 h2F4
  rcases h207 h1930 L hL with ⟨n, -, h⟩ | h | h | h | h | h | ⟨n, -, h⟩ | h
  · exfalso
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact hS (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h)
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hC (by decide) h
    · exact hE (Or.inl h)
    · exact hE (Or.inr (Or.inl h))
    · exact hE (Or.inr (Or.inr h))
    · exact hC (by decide) h
    · exact hQ h.1
    · exact hQ h.1
    · exact hC (by decide) h
    · exact hC (by decide) h
  · exact (hC (by decide) h).elim
  · exact (hC (by decide) h).elim
  · exact (hC (by decide) h).elim
  · exact (hE (Or.inr (Or.inl h))).elim
  · exact (hE (Or.inr (Or.inl h))).elim
  · refine ⟨n, fun L' hL' => ?_⟩
    rcases hL' with rfl | hL'
    · rcases shape_of_szL2Product h hqK hsK with h' | h'
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eK.symm h')
      · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eK.symm h'))
    · rw [Set.mem_singleton_iff] at hL'
      subst hL'
      rcases shape_of_szL2Product h hqK' hsK' with h' | h'
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eK'.symm h')
      · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eK'.symm h'))
  · refine ⟨3, fun L' hL' => Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    rcases hL' with rfl | hL'
    · exact isSU3_of_surjective_central (shape_of_suCentralSquare h hqK hsK)
        eK.symm.toMonoidHom eK.symm.surjective (by
          rw [(MonoidHom.ker_eq_bot_iff _).mpr eK.symm.injective]
          exact bot_le)
        (by
          have := CFSG.ComponentClassification.Quasisimple.nontrivial hqK
          exact eK.toEquiv.nontrivial)
    · rw [Set.mem_singleton_iff] at hL'
      subst hL'
      exact isSU3_of_surjective_central (shape_of_suCentralSquare h hqK' hsK')
        eK'.symm.toMonoidHom eK'.symm.surjective (by
          rw [(MonoidHom.ker_eq_bot_iff _).mpr eK'.symm.injective]
          exact bot_le)
        (by
          have := CFSG.ComponentClassification.Quasisimple.nontrivial hqK'
          exact eK'.toEquiv.nontrivial)

private theorem product_L0_eq_L_aux
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h207 : S20_7 D) (h209 : S20_9 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hK : K ∈ calC c.L)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    c.L0 = c.L := by
  obtain ⟨t, htT, hne, hsup⟩ := hprod
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hLcal : c.L ∈ calL D.T D.M := c.hL.1
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC c.L :=
    calC_map_conj_of_mem_normalizer hK (hTL htT)
  have hKne : K ≠ K.map (MulAut.conj t).toMonoidHom := fun h => hne (by rw [← h])
  obtain ⟨n, hsh⟩ := product_shapes_of_simple hG2 h3D4 h2F4 h207 h1930 hLcal hK hKt hKne
  clear hG2 h3D4 h2F4
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L hLcal c.L0).mp ⟨c.hL0, c.hL0L⟩
  have hTLsyl : IsSylowIn 2 (D.T ⊓ c.L) c.L :=
    Ctx23L.isSylowIn_inf_of_le_normalizer (D := D) (N := c.L) hTL
  have hPpar : ParabolicOf c.L P := hP.1.1
  have hTP : D.T ≤ Subgroup.normalizer (P : Set G) := hP.1.2.1
  have hSP : D.T ⊓ c.L ≤ P :=
    le_of_le_normalizer_of_odd hTLsyl.2.1 inf_le_right hPpar.2.1 (inf_le_left.trans hTP)
      (not_two_dvd_relIndex_of_parabolicOf hPpar)
  rcases RankOneBorel.holds_product hTLsyl hK hKt hsup hKne htT rfl hsh hSP hPpar.2.1 hTP with
    hN | hPL
  ·
    exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hL0P' : c.L0 ≤ P := hL0P ▸ uc22p21c_Hinf_le P
    have hL0N : c.L0 ≤ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) := hL0P'.trans hN
    set S := hTLsyl.toSylow
    have hsolv := CFSG.GH74.GLS.C3.Layer1.U1a.isSolvable_normalizer_sylow_two S
    have hBle : c.L0.subgroupOf c.L ≤ Subgroup.normalizer ((S : Subgroup ↥c.L) : Set ↥c.L) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      show y ∈ (S : Subgroup ↥c.L) ↔ x * y * x⁻¹ ∈ (S : Subgroup ↥c.L)
      rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp (hL0N (Subgroup.mem_subgroupOf.mp hx)) (y : G)
    have : Group.IsSolvable ↥(c.L0.subgroupOf c.L) :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hBle) (Subgroup.inclusion_injective _)
    have hperf : ⁅c.L0.subgroupOf c.L, c.L0.subgroupOf c.L⁆ = c.L0.subgroupOf c.L := by
      rw [CFSG.GroupTheory.commutator_subgroupOf_eq c.hL0L c.hL0L, c.hL0.1.2.1]
    have hbot := eq_bot_of_perfect_of_isSolvable hperf
    apply Ctx23L.L0_not_le_M c
    intro x hx
    have hx' : (⟨x, c.hL0L hx⟩ : ↥c.L) ∈ c.L0.subgroupOf c.L := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    have : x = 1 := congrArg Subtype.val hx'
    rw [this]
    exact D.M.one_mem
  · rw [hL0P, hPL]
    exact Hinf_eq_self_of_perfect c.L hLcal.2.1

private theorem not_isQuasisimple_of_isSzL2Product {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsSzL2Product X n) : False := by
  obtain ⟨A, B, _, _, ⟨f⟩, hA, hB⟩ := h
  have hsimp : ∀ {Y : Type} [Group Y], (IsSz Y n ∨ IsL2 Y n) → IsSimpleGroup Y := by
    intro Y _ hY
    rcases hY with hY | hY
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hY
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY
  have : IsSimpleGroup A := hsimp hA
  have : IsSimpleGroup B := hsimp hB
  have hqC : CFSG.IsQuasisimple X :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff X).2.2.1.mpr hq
  set N₁ : Subgroup X := ((MonoidHom.snd A B).comp f.toMonoidHom).ker
  set N₂ : Subgroup X := ((MonoidHom.fst A B).comp f.toMonoidHom).ker
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = f.symm ((f x).1, 1) * f.symm (1, (f x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · show (f (f.symm ((f x).1, 1))).2 = 1
      simp
    · show (f (f.symm (1, (f x).2))).1 = 1
      simp
  have hcen : ∀ {Y : Type} [Group Y] [IsSimpleGroup Y] (φ : X →* Y),
      Function.Surjective φ → φ.ker ≤ Subgroup.center X := by
    intro Y _ _ φ hφ
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqC
      φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨x, rfl⟩ := hφ y
      exact hy (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  have h₁ : N₁ ≤ Subgroup.center X :=
    hcen _ (fun b => ⟨f.symm (1, b), by simp⟩)
  have h₂ : N₂ ≤ Subgroup.center X :=
    hcen _ (fun a => ⟨f.symm (a, 1), by simp⟩)
  have htop : Subgroup.center X = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le h₁ h₂)
  obtain ⟨a, b, hab⟩ := uc22pw_exists_noncomm_of_quasisimple hq
  exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)

private theorem not_isQuasisimple_of_isSU3CentralSquare {X : Type} [Group X]
    (hq : CFSG.Open.IsQuasisimple X) (h : IsSU3CentralSquare X) : False := by
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  have : K₁.Normal := uc22p22r_normal_of_commuting hsup hcomm
  have hqC : CFSG.IsQuasisimple X :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff X).2.2.1.mpr hq
  have hnc : ∀ {K : Subgroup X}, CFSG.Open.IsQuasisimple ↥K → ¬ K ≤ Subgroup.center X := by
    intro K hK hle
    obtain ⟨a, b, hab⟩ := uc22pw_exists_noncomm_of_quasisimple hK
    apply hab
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) (b : X)).symm
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqC K₁ with h | h
  · exact hnc hK₁.1 h
  · apply hnc hK₂.1
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    exact hcomm z (h ▸ Subgroup.mem_top z) y hy

private theorem shape_K_A_of_single_aux
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D)
    (h1A : S23_1A D Ch) (hDeg : KMinDegLow) (h128 : W4Lem12_8) (hn2 : 2 < c.n)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : c.L ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, c.L.map (MulAut.conj (t : G)).toMonoidHom) :
    ∃ e : ℕ, ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
        IsSz ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
        IsU3 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
        IsSU3 ↥(barSub (⊥ : Subgroup G) A hA c.L) e) ∨
      (((barSub (⊥ : Subgroup G) A hA c.L).subgroupOf
          (Mbar c.N (⊥ : Subgroup G) A hA)).Normal ∧
        (IsL3 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
          IsSL3 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
          IsSp4 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
          IsU4 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
          IsG2 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
          Is3D4 ↥(barSub (⊥ : Subgroup G) A hA c.L) e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA c.L) .twistedF4 0 2 e ∨
          (e = 2 ∧ IsU5 ↥(barSub (⊥ : Subgroup G) A hA c.L) 2) ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA c.L) .PSL 4 2 e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA c.L) .PSp 3 2 e ∨
          IsOmega8m ↥(barSub (⊥ : Subgroup G) A hA c.L) e))) := by
  have hG2' : ∀ {f : ℕ}, IsG2 (Bar2 c.L) f → IsSimpleGroup (Bar2 c.L) := fun h => hG2 _ _ h
  have h3D4' : ∀ {f : ℕ}, Is3D4 (Bar2 c.L) f → IsSimpleGroup (Bar2 c.L) := fun h => h3D4 _ _ h
  have h2F4' : ∀ {f : ℕ}, LieModel (Bar2 c.L) .twistedF4 0 2 f → IsSimpleGroup (Bar2 c.L) :=
    fun h => h2F4 _ _ h
  clear hG2 h3D4 h2F4
  have hLcal : c.L ∈ calL D.T D.M := c.hL.1
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have h2 := barSub_pCoreOf_eq_bot_of_isComponentOf c h208 h1930 hA hAV hK
  have hcomp := isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  have hKAne : barSub (⊥ : Subgroup G) A hA c.L ≠ ⊥ := barSub_K_ne_bot hA hcomp
  have hq : CFSG.Open.IsQuasisimple (Bar2 c.L) := hK.2.2
  have hsim : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ},
      IsSimpleGroup (Bar2 c.L) → LieModel (Bar2 c.L) t m 2 f →
      LieModel ↥(barSub (⊥ : Subgroup G) A hA c.L) t m 2 f :=
    fun hs h => lieModel_barSub_of_isSimpleGroup hA hLstab h2 hKAne hs h
  have hcl : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ},
      t ∈ CFSG.Blueprint.classicalTags → LieModel (Bar2 c.L) t m 2 f →
      LieModel ↥(barSub (⊥ : Subgroup G) A hA c.L) t m 2 f :=
    fun ht h => hsim (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h) h
  have hnorm : ((barSub (⊥ : Subgroup G) A hA c.L).subgroupOf
      (Mbar c.N (⊥ : Subgroup G) A hA)).Normal := by
    obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L hLcal c.L0).mp ⟨c.hL0, c.hL0L⟩
    have hn : NParam (Hinf P) c.n := hL0P ▸ c.hn
    have hfixH : fixV (⨆ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA c.L)
        (Mbar c.N (⊥ : Subgroup G) A hA), X) = ⊥ := by
      rw [eq_bot_iff, ← fixV_barSub_eq_bot c hA hAV hAN]
      intro w hw
      rw [mem_fixV] at hw ⊢
      intro x hx
      refine hw x ?_
      refine Subgroup.mem_iSup_of_mem (barSub (⊥ : Subgroup G) A hA c.L) ?_
      refine Subgroup.mem_iSup_of_mem
        ⟨(1 : MulAut (Vtil (⊥ : Subgroup G) A hA)), (Mbar c.N (⊥ : Subgroup G) A hA).one_mem, ?_⟩ hx
      ext y
      simp
    have hTK : barSub (⊥ : Subgroup G) A hA D.T ≤
        Subgroup.normalizer (barSub (⊥ : Subgroup G) A hA c.L :
          Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) := by
      intro y hy
      obtain ⟨g, hgT, rfl⟩ := (mem_barSub (⊥ : Subgroup G) A hA D.T y).1 hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hgs : (g : G) ∈ stabTil (⊥ : Subgroup G) A := g.2
      have hconj := TwelveTwentyThree.barSub_map_conj hA hLstab hgs
      have hLg : c.L.map (MulAut.conj (g : G)).toMonoidHom = c.L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL hgT)
      rw [hLg] at hconj
      have hgg : (⟨(g : G), hgs⟩ : ↥(stabTil (⊥ : Subgroup G) A)) = g := Subtype.ext rfl
      rw [hgg] at hconj
      exact hconj.symm
    exact normal_of_higher_rank c h208 h1930 h1A h128 hDeg hA hAV hAne hAN hmin hK hgen hP
      hL0P hn hn2 (s20_7Shape_of h207 h1930 hLcal) rfl hfixH hTK (isSylowIn_T_Mbar c hA hAN)
  rcases s20_7Shape_of h207 h1930 hLcal with ⟨n, -, h⟩ | h | h | h | h | h | ⟨n, -, h⟩ | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨n, Or.inl (Or.inr (Or.inl (hsim
        (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h) h)))⟩
    · exact ⟨n, Or.inl (Or.inl (hcl (by decide) h))⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inl (hcl (by decide) h)⟩⟩
    · exact ⟨n, Or.inl (Or.inr (Or.inr (Or.inl (hcl (by decide) h))))⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (hcl (by decide) h)))))))))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inl (hcl (by decide) h))))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hsim (hG2' h) h)))))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hsim (h3D4' h) h))))))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hsim (h2F4' h) h)))))))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inl (hcl (by decide) h)))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inl (isSL3_barSub hA hLstab h2 hKAne h))⟩⟩
    · exact ⟨n, Or.inl (Or.inr (Or.inr (Or.inr (isSU3_barSub hA hLstab h2 hKAne h))))⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (hcl (by decide) h))))))))))⟩⟩
    · exact ⟨n, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (hcl (by decide) h))))))))))⟩⟩
  · exact ⟨2, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inl (hcl (by decide) h))))⟩⟩
  · exact ⟨2, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, hcl (by decide) h⟩)))))))⟩⟩
  · exact ⟨2, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (hcl (by decide) h))))))))))⟩⟩
  · exact ⟨2, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hsim (h3D4' h) h))))))⟩⟩
  · exact ⟨1, Or.inr ⟨hnorm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hsim (h3D4' h) h))))))⟩⟩
  · exact absurd (not_isQuasisimple_of_isSzL2Product hq h) id
  · exact absurd (not_isQuasisimple_of_isSU3CentralSquare hq h) id

theorem Ctx23L.eq_L_or_eq_sup_conj_of_mem_calC {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (_h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    K = c.L ∨ ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom :=
  eq_L_or_eq_sup_conj_aux hG2 h3D4 h2F4 c h207 h1930 hA hAV hAne hAN hK hgen

theorem Ctx23L.product_L0_eq_L {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h207 : S20_7 D) (h209 : S20_9 D) (_h2010 : S20_10 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (_hAV : A ≤ c.V) (_hAne : A ≠ ⊥)
    (_hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (_hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (_hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    c.L0 = c.L :=
  product_L0_eq_L_aux hG2 h3D4 h2F4 c h207 h209 h1930 hA hK hprod

theorem Ctx23L.nParam_barSub_L0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (_h208 : S20_8 D) (_h1930 : H1930 D) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (_hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    NParam (barSub (⊥ : Subgroup G) A hA c.L0) c.n := by
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A := c.hL0L.trans hLstab
  have hL0cal : c.L0 ∈ calL D.T D.M := c.hL0.1
  have hne_of : ∀ {X : Subgroup G}, X ≤ c.L0 → (X ≤ stabTil (⊥ : Subgroup G) A) →
      barSub (⊥ : Subgroup G) A hA c.L0 = barSub (⊥ : Subgroup G) A hA X →
      barSub (⊥ : Subgroup G) A hA X ≠ ⊥ := by
    intro X _ _ heq h
    rw [← heq] at h
    have hcent := le_centralizer_of_barSub_eq_bot hA hL0stab h
    apply hAne
    rw [eq_bot_iff, ← fixed_L0_eq_bot c]
    intro a ha
    refine ⟨hAV ha, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hcent hl) a ha).symm
  have hL0ne : barSub (⊥ : Subgroup G) A hA c.L0 ≠ ⊥ := hne_of le_rfl hL0stab rfl
  have hshape : ∀ {X : Subgroup G}, X ∈ calC c.L0 → barSub (⊥ : Subgroup G) A hA X ≠ ⊥ →
      (IsSz (Bar2 X) c.n ∨ IsL2 (Bar2 X) c.n ∨ (c.n = 3 ∧ IsSU3 (Bar2 X) 3)) →
      IsSz (Bar2 (barSub (⊥ : Subgroup G) A hA X)) c.n ∨
        IsL2 (Bar2 (barSub (⊥ : Subgroup G) A hA X)) c.n ∨
        (c.n = 3 ∧ IsSU3 (Bar2 (barSub (⊥ : Subgroup G) A hA X)) 3) := by
    intro X hX hXne h
    have hXstab : X ≤ stabTil (⊥ : Subgroup G) A :=
      (CFSG.Quasithin.A3.subnormal_le hX.1).trans hL0stab
    obtain ⟨hnt, hker⟩ := bar2Map_central hA hXstab hX.2.1 hXne hX.2.2
    rcases h with h | h | ⟨h3, h⟩
    · exact Or.inl (lieModel_of_surjective_of_isSimple
        (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h) _
        (bar2Map_surjective hA hXstab) hnt h)
    · exact Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
        (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h) _
        (bar2Map_surjective hA hXstab) hnt h))
    · exact Or.inr (Or.inr ⟨h3, isSU3_of_surjective_central h _
        (bar2Map_surjective hA hXstab) hker hnt⟩)
  have hsingle_of : ∀ {X : Subgroup G}, X ∈ calC c.L0 →
      barSub (⊥ : Subgroup G) A hA X ≠ ⊥ →
      (IsSz (Bar2 X) c.n ∨ IsL2 (Bar2 X) c.n ∨ (c.n = 3 ∧ IsSU3 (Bar2 X) 3)) →
      NParamSingle (Bar2 (barSub (⊥ : Subgroup G) A hA X)) c.n := by
    intro X hX hXne h
    rcases hshape hX hXne h with h | h | ⟨h3, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h3]
      exact Or.inr (Or.inr (Or.inl h))
  rcases c.hn with hsingle | ⟨L₁, L₂, h₁, h₂, hL, hne12, hsh⟩
  ·
    obtain ⟨hnt, hker⟩ := bar2Map_central hA hL0stab hL0cal.2.1 hL0ne
      (uc22pw_isQuasisimple_of_single D hL0cal hsingle)
    exact Or.inl (nParamSingle_of_surjective_central hsingle _ (bar2Map_surjective hA hL0stab)
      hker hnt)
  ·
    have hL₁stab : L₁ ≤ stabTil (⊥ : Subgroup G) A :=
      (CFSG.Quasithin.A3.subnormal_le h₁.1).trans hL0stab
    have hL₂stab : L₂ ≤ stabTil (⊥ : Subgroup G) A :=
      (CFSG.Quasithin.A3.subnormal_le h₂.1).trans hL0stab
    have hsupA : barSub (⊥ : Subgroup G) A hA c.L0 =
        barSub (⊥ : Subgroup G) A hA L₁ ⊔ barSub (⊥ : Subgroup G) A hA L₂ :=
      (congrArg (barSub (⊥ : Subgroup G) A hA) hL).trans (barSub_sup hA hL₁stab hL₂stab)
    have hsh₁ := hsh L₁ (by simp)
    have hsh₂ := hsh L₂ (by simp)
    by_cases hX₁ : barSub (⊥ : Subgroup G) A hA L₁ = ⊥
    · have hX₂ : barSub (⊥ : Subgroup G) A hA L₂ ≠ ⊥ := by
        intro h
        apply hL0ne
        rw [hsupA, hX₁, h, sup_bot_eq]
      rw [hsupA, hX₁, bot_sup_eq]
      exact Or.inl (hsingle_of h₂ hX₂ hsh₂)
    · by_cases hX₂ : barSub (⊥ : Subgroup G) A hA L₂ = ⊥
      · rw [hsupA, hX₂, sup_bot_eq]
        exact Or.inl (hsingle_of h₁ hX₁ hsh₁)
      · by_cases heq : barSub (⊥ : Subgroup G) A hA L₁ = barSub (⊥ : Subgroup G) A hA L₂
        ·
          exfalso
          set Y := barSub (⊥ : Subgroup G) A hA L₁ with hY
          have hperfY : ⁅Y, Y⁆ = Y := barSub_commutator hA hL₁stab h₁.2.1
          have hcomm : ⁅L₁, L₂⁆ ≤ CFSG.Open.pCoreOf 2 c.L0 :=
            commutator_le_pCoreOf_of_ne' h₁ h₂ hne12
          have hY2 : IsPGroup 2 Y := by
            have hYle : Y ≤ barSub (⊥ : Subgroup G) A hA (CFSG.Open.pCoreOf 2 c.L0) := by
              calc Y = ⁅Y, Y⁆ := hperfY.symm
                _ = ⁅barSub (⊥ : Subgroup G) A hA L₁, barSub (⊥ : Subgroup G) A hA L₂⁆ := by
                  rw [← heq]
                _ = barSub (⊥ : Subgroup G) A hA ⁅L₁, L₂⁆ :=
                  (barSub_commutator_eq hA hL₁stab hL₂stab).symm
                _ ≤ barSub (⊥ : Subgroup G) A hA (CFSG.Open.pCoreOf 2 c.L0) :=
                  barSub_mono (⊥ : Subgroup G) A hA hcomm
            exact (isPGroup_barSub_two hA
              ((CFSG.LieType.BorelTits.pCoreOf_le 2 c.L0).trans hL0stab)
              (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L0)).to_le hYle
          exact hX₁ (eq_bot_of_perfect_of_isPGroup_two hperfY hY2)
        · refine Or.inr ⟨barSub (⊥ : Subgroup G) A hA L₁, barSub (⊥ : Subgroup G) A hA L₂,
            ?_, ?_, hsupA, heq, ?_⟩
          · exact ⟨TwelveTwentyThree.isSubnormal_barSub (V₀ := ⊥) hA h₁.1,
              barSub_commutator hA hL₁stab h₁.2.1, by
                obtain ⟨hnt, -⟩ := bar2Map_central hA hL₁stab h₁.2.1 hX₁ h₁.2.2
                exact uc22br4_isQuasisimple_of_surjective h₁.2.2 _
                  (bar2Map_surjective hA hL₁stab)⟩
          · exact ⟨TwelveTwentyThree.isSubnormal_barSub (V₀ := ⊥) hA h₂.1,
              barSub_commutator hA hL₂stab h₂.2.1, by
                obtain ⟨hnt, -⟩ := bar2Map_central hA hL₂stab h₂.2.1 hX₂ h₂.2.2
                exact uc22br4_isQuasisimple_of_surjective h₂.2.2 _
                  (bar2Map_surjective hA hL₂stab)⟩
          · intro L' hL'
            rcases hL' with rfl | hL'
            · exact hshape h₁ hX₁ hsh₁
            · rw [Set.mem_singleton_iff] at hL'
              subst hL'
              exact hshape h₂ hX₂ hsh₂

theorem Ctx23L.rankOne_shape_barSub_K_of_product {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (_hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (_hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (_hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hL0L : c.L0 = c.L) :
    IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∨
      IsSz ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∨
      IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) c.n := by
  obtain ⟨t, htT, hne, hsup⟩ := hprod
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC c.L :=
    calC_map_conj_of_mem_normalizer hK (hTL htT)
  have hKne : K.map (MulAut.conj t).toMonoidHom ≠ K := fun h => hne (by rw [h])
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) A :=
    ((CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)).trans hNstab
  have hts : t ∈ stabTil (⊥ : Subgroup G) A := hNstab (Ctx23L.T_le_N c htT)
  have h2 := barSub_pCoreOf_eq_bot_of_isComponentOf c h208 h1930 hA hAV hK
  have hK1 : barSub (⊥ : Subgroup G) A hA K ≠ ⊥ := by
    intro h
    apply hne
    rw [TwelveTwentyThree.barSub_map_conj hA hKstab hts, h, Subgroup.map_bot]
  have hn := c.hn
  rw [hL0L] at hn
  rcases hn with hsingle | ⟨L₁, L₂, h₁, h₂, hL, -, hsh⟩
  · exact absurd (eq_of_mem_calC_of_isQuasisimple_bar2
      (uc22pw_isQuasisimple_of_single D c.hL.1 hsingle) hKt hK) hKne
  · have hshK : IsSz (Bar2 K) c.n ∨ IsL2 (Bar2 K) c.n ∨ (c.n = 3 ∧ IsSU3 (Bar2 K) 3) := by
      rcases eq_or_eq_of_mem_calC_of_sup_eq h₁ h₂ hL hK with rfl | rfl
      · exact hsh _ (by simp)
      · exact hsh _ (by simp)
    rcases hshK with h | h | ⟨h3, h⟩
    · exact Or.inr (Or.inl (lieModel_barSub_of_isSimpleGroup hA hKstab h2 hK1
        (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h) h))
    · exact Or.inl (lieModel_barSub_of_isSimpleGroup hA hKstab h2 hK1
        (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h) h)
    · rw [h3]
      exact Or.inr (Or.inr (isSU3_barSub hA hKstab h2 hK1 h))

theorem Ctx23L.nParam_barSub_K_of_product {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hL0L : c.L0 = c.L) :
    NParam (barSub (⊥ : Subgroup G) A hA K) c.n := by
  have hshape := Ctx23L.rankOne_shape_barSub_K_of_product c h208 h1930 hA hAV hAne hAN hmin hK
    hgen hprod hL0L
  obtain ⟨t, htT, hne, -⟩ := hprod
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) A :=
    ((CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)).trans hNstab
  have hts : t ∈ stabTil (⊥ : Subgroup G) A := hNstab (Ctx23L.T_le_N c htT)
  have h2 := barSub_pCoreOf_eq_bot_of_isComponentOf c h208 h1930 hA hAV hK
  have hK1 : barSub (⊥ : Subgroup G) A hA K ≠ ⊥ := by
    intro h
    apply hne
    rw [TwelveTwentyThree.barSub_map_conj hA hKstab hts, h, Subgroup.map_bot]
  have hO2 : CFSG.pCore 2 ↥(barSub (⊥ : Subgroup G) A hA K) = ⊥ :=
    pCore_barSub_eq_bot_of_quasisimple hA hKstab h2 hK1 hK.2.2
  let e : Bar2 (barSub (⊥ : Subgroup G) A hA K) ≃* ↥(barSub (⊥ : Subgroup G) A hA K) :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  refine Or.inl ?_
  rcases hshape with h | h | h
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h))
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
  · exact Or.inr (Or.inr (Or.inl (isSU3_of_surjective_central h e.symm.toMonoidHom
      e.symm.surjective (by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective]
        exact bot_le)
      (by
        have : Nontrivial ↥(barSub (⊥ : Subgroup G) A hA K) :=
          (Subgroup.nontrivial_iff_ne_bot _).2 hK1
        exact e.toEquiv.nontrivial))))

theorem Ctx23L.shape_K_A_of_single {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D)
    (h1A : S23_1A D Ch) (hDeg : KMinDegLow) (h128 : W4Lem12_8) (hn2 : 2 < c.n)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L) :
    ∃ e : ℕ, ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsSz ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsU3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) e) ∨
      (((barSub (⊥ : Subgroup G) A hA K).subgroupOf
          (Mbar c.N (⊥ : Subgroup G) A hA)).Normal ∧
        (IsL3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsSL3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsSp4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsU4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsG2 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          Is3D4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .twistedF4 0 2 e ∨
          (e = 2 ∧ IsU5 ↥(barSub (⊥ : Subgroup G) A hA K) 2) ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .PSL 4 2 e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .PSp 3 2 e ∨
          IsOmega8m ↥(barSub (⊥ : Subgroup G) A hA K) e))) := by
  subst hsingle
  exact shape_K_A_of_single_aux hG2 h3D4 h2F4 c h207 h208 h209 h1930 h1A hDeg h128 hn2 hA hAV
    hAne hAN hmin hK hgen

theorem Ctx23L.shape_K_A_of_product {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hnat : IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∨
      IsSz ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∨
      IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) c.n) :
    ∃ e : ℕ, ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsSz ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsU3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) e) ∨
      (((barSub (⊥ : Subgroup G) A hA K).subgroupOf
          (Mbar c.N (⊥ : Subgroup G) A hA)).Normal ∧
        (IsL3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsSL3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsSp4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsU4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsG2 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          Is3D4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .twistedF4 0 2 e ∨
          (e = 2 ∧ IsU5 ↥(barSub (⊥ : Subgroup G) A hA K) 2) ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .PSL 4 2 e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .PSp 3 2 e ∨
          IsOmega8m ↥(barSub (⊥ : Subgroup G) A hA K) e))) := by
  refine ⟨c.n, Or.inl ?_⟩
  rcases hnat with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.LocalAnalysis.UniquenessCase.UC22
