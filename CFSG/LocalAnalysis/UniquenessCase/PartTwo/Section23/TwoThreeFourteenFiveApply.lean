module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFive
public import CFSG.Quasithin.Background.B69Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commV_le_fixV_of_isDirSumOver {W : Type} [CommGroup W]
    {S : Set (Subgroup (MulAut W))} {K X : Subgroup (MulAut W)}
    (hsum : IsDirSumOver S (fun Y => commV Y)) (hK : K ∈ S) (hX : X ∈ S)
    (hne : X ≠ K) (hKX : K ≤ Subgroup.normalizer (X : Set (MulAut W))) :
    commV X ≤ fixV K := by
  classical
  have hdisj : Disjoint (commV X) (commV K) := by
    let X' : {Y // Y ∈ S} := ⟨X, hX⟩
    let K' : {Y // Y ∈ S} := ⟨K, hK⟩
    have hK'ne : K' ≠ X' := fun h => hne (congrArg Subtype.val h).symm
    have hind := (iSupIndep_def.mp hsum.1) X'
    have hle : commV K ≤
        ⨆ j : {Y // Y ∈ S}, ⨆ (_ : j ≠ X'), commV (j : Subgroup (MulAut W)) :=
      le_iSup_of_le K' (le_iSup_of_le hK'ne le_rfl)
    exact hind.mono_right hle
  intro v hv
  rw [mem_fixV]
  intro k hk
  have hmemX : k v * v⁻¹ ∈ commV X :=
    (commV X).mul_mem (CFSG.Quasithin.B15P4.map_commV_mem (hKX hk) v hv)
      ((commV X).inv_mem hv)
  have hmemK : k v * v⁻¹ ∈ commV K := Subgroup.subset_closure ⟨k, hk, v, rfl⟩
  have hbot : k v * v⁻¹ = 1 := by
    have hle := hdisj.le_bot ⟨hmemX, hmemK⟩
    simpa using hle
  exact mul_inv_eq_one.mp hbot

theorem fixV_sup_eq {W : Type} [CommGroup W] (K K' : Subgroup (MulAut W)) :
    fixV (K ⊔ K') = fixV K ⊓ fixV K' := by
  refine le_antisymm (le_inf (CFSG.Quasithin.fixV_anti le_sup_left)
    (CFSG.Quasithin.fixV_anti le_sup_right)) ?_
  intro w hw
  obtain ⟨hK, hK'⟩ := Subgroup.mem_inf.mp hw
  rw [mem_fixV]
  intro x hx
  have hstabK : K ≤ MulAction.stabilizer (MulAut W) w := fun k hk => by
    rw [MulAction.mem_stabilizer_iff]
    simpa using mem_fixV.mp hK k hk
  have hstabK' : K' ≤ MulAction.stabilizer (MulAut W) w := fun k hk => by
    rw [MulAction.mem_stabilizer_iff]
    simpa using mem_fixV.mp hK' k hk
  have hx' : x ∈ MulAction.stabilizer (MulAut W) w := (sup_le hstabK hstabK') hx
  rwa [MulAction.mem_stabilizer_iff] at hx'

theorem fixV_barSub_eq_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    fixV (barSub ⊥ A hA c.L) = ⊥ := by
  have hLstab : c.L ≤ stabTil ⊥ A :=
    le_inf ((Ctx23L.L_le_N c).trans hAN)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  rw [fixV_barSub_eq_imgTil_centralizer hA hLstab]
  have hbot : A ⊓ Subgroup.centralizer (c.L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ c.V ⊓ Subgroup.centralizer (c.L : Set G) := ⟨hAV hx.1, hx.2⟩
    rwa [Ctx23L.fixed_L_eq_bot c] at hxV
  rw [hbot, TwelveSeventeen.imgTil_bot]

theorem lieModel_of_surjective_of_isSimple {X Y : Type} [Group X] [Group Y] [Finite X]
    (hX : IsSimpleGroup X) (q : X →* Y) (hq : Function.Surjective q) (hY : Nontrivial Y)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ}
    (h : CFSG.Blueprint.LieModel X t m p f) : CFSG.Blueprint.LieModel Y t m p f := by
  have hker : q.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top q.ker with hb | ht
    · exact hb
    · exfalso
      have hsub : Subsingleton Y := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hq a
        obtain ⟨y, rfl⟩ := hq b
        have hx : x ∈ q.ker := ht ▸ Subgroup.mem_top x
        have hy : y ∈ q.ker := ht ▸ Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]⟩
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hY
  have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hker
  exact CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.ofBijective q ⟨hinj, hq⟩) h

theorem isSU3_of_surjective_central {X Y : Type} [Group X] [Group Y] [Finite X]
    {n : ℕ} (h : IsSU3 X n) (q : X →* Y) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center X) (hY : Nontrivial Y) : IsSU3 Y n := by
  have hqC : CFSG.IsQuasisimple X :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff X).2.2.1.mpr h.1
  have hnt : ∃ x : X, q x ≠ 1 := by
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨x, hy⟩
  refine ⟨(CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1.mp
    (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqC (φ := q) hq hnt), ?_⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqC hq hker) h.2

theorem isSL3_of_surjective_central {X Y : Type} [Group X] [Group Y] [Finite X]
    {n : ℕ} (h : IsSL3 X n) (q : X →* Y) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center X) (hY : Nontrivial Y) : IsSL3 Y n := by
  have hqC : CFSG.IsQuasisimple X :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff X).2.2.1.mpr h.1
  have hnt : ∃ x : X, q x ≠ 1 := by
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨x, hy⟩
  refine ⟨(CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1.mp
    (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqC (φ := q) hq hnt), ?_⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqC hq hker) h.2

theorem nParamSingle_of_surjective_central {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {n : ℕ} (h : NParamSingle X n) (q : X →* Y) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center X) (hY : Nontrivial Y) : NParamSingle Y n := by
  rcases h with h | h | h | h | h
  · exact Or.inl (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_twistedB2 h) q hq hY h)
  · exact Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_classical (Or.inl rfl) h) q hq hY h))
  · exact Or.inr (Or.inr (Or.inl (isSU3_of_surjective_central h q hq hker hY)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isSL3_of_surjective_central h q hq hker hY))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inl rfl))) h) q hq hY h))))

theorem le_normalizer_of_isComponentOf_ne {W : Type} [CommGroup W] [Finite W]
    {Y L X : Subgroup (MulAut W)} (hcompL : CFSG.Open.IsComponentOf L Y)
    (hcompX : CFSG.Open.IsComponentOf X Y) (hne : L ≠ X) :
    L ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
  have hcomm := CFSG.Quasithin.B69.components_mul_comm_of_ne
    (V := W) (X := Y) (L := L) (L' := X) hcompL hcompX hne
  have hcent : L ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx l hl
  exact hcent.trans (Subgroup.centralizer_le_normalizer (X : Set (MulAut W)))

theorem commV_ne_bot_of_faithful {W : Type} [CommGroup W] {Y X : Subgroup (MulAut W)}
    (hfaith : ∀ y ∈ Y, (∀ w : W, y w = w) → y = 1)
    (hXne : X ≠ ⊥) (hXY : X ≤ Y) : commV X ≠ ⊥ := by
  intro hc
  have htriv : ∀ x ∈ X, ∀ w : W, x w = w := by
    intro x hx w
    have htop : (⊤ : Subgroup W) ≤ fixV X := by
      rw [← commSub_eq_bot_iff, ← commV_eq_commSub]
      exact hc
    exact (mem_fixV.mp (htop (Subgroup.mem_top w))) x hx
  have hXbot : X ≤ ⊥ := by
    intro x hx
    rw [Subgroup.mem_bot]
    exact hfaith x (hXY hx) (htriv x hx)
  exact hXne (le_bot_iff.mp hXbot)

theorem false_of_case_one_of_fixV_eq_bot {W : Type} [CommGroup W] [Finite W]
    {Y L H : Subgroup (MulAut W)} (hcomp : CFSG.Open.IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) (hfix : fixV L = ⊥)
    (hfaith : ∀ y ∈ Y, (∀ w : W, y w = w) → y = 1)
    (hHne : H ≠ L) (hsum : IsDirSumOver (conjSet L Y) (fun X => commV X)) : False := by
  classical
  have hex : ∃ X ∈ conjSet L Y, X ≠ L := by
    by_contra h
    push Not at h
    apply hHne
    rw [hH]
    refine le_antisymm (iSup₂_le fun X hX => le_of_eq (h X hX)) ?_
    exact le_iSup₂_of_le L (s15_T7_mem_conjSet_self L Y) le_rfl
  obtain ⟨X, hXmem, hXne⟩ := hex
  have hXmem0 : X ∈ conjSet L Y := hXmem
  obtain ⟨g, hgY, rfl⟩ := hXmem
  have hXmem' : L.map (MulAut.conj g).toMonoidHom ∈ conjSet L Y := hXmem0
  set X : Subgroup (MulAut W) := L.map (MulAut.conj g).toMonoidHom with hXdef
  have hXcomp : CFSG.Open.IsComponentOf X Y := hXdef ▸
    CFSG.Quasithin.B113.isComponentOf_conj hcomp hgY
  have hXne_bot : X ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot X).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hXcomp.2.2))
  have hle : commV X ≤ fixV L :=
    commV_le_fixV_of_isDirSumOver hsum (s15_T7_mem_conjSet_self L Y) hXmem' hXne
      (le_normalizer_of_isComponentOf_ne hcomp hXcomp hXne.symm)
  rw [hfix] at hle
  exact commV_ne_bot_of_faithful hfaith hXne_bot hXcomp.1 (le_bot_iff.mp hle)

theorem false_of_case_one_of_three_conjugates {W : Type} [CommGroup W] [Finite W]
    {Y L K LA X : Subgroup (MulAut W)}
    (hcompL : CFSG.Open.IsComponentOf L Y) (hcompK : CFSG.Open.IsComponentOf K Y)
    (hcompX : CFSG.Open.IsComponentOf X Y)
    (hLA : L ⊔ K = LA) (hfixLA : fixV LA = ⊥)
    (hfaith : ∀ y ∈ Y, (∀ w : W, y w = w) → y = 1)
    (hsum : IsDirSumOver (conjSet L Y) (fun Z => commV Z))
    (hKmem : K ∈ conjSet L Y) (hXmem : X ∈ conjSet L Y)
    (hXL : X ≠ L) (hXK : X ≠ K) : False := by
  have hXleY : X ≤ Y := hcompX.1
  have hXne_bot : X ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot X).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcompX.2.2))
  have hleL : commV X ≤ fixV L :=
    commV_le_fixV_of_isDirSumOver hsum (s15_T7_mem_conjSet_self L Y) hXmem hXL
      (le_normalizer_of_isComponentOf_ne hcompL hcompX hXL.symm)
  have hleK : commV X ≤ fixV K :=
    commV_le_fixV_of_isDirSumOver hsum hKmem hXmem hXK
      (le_normalizer_of_isComponentOf_ne hcompK hcompX hXK.symm)
  have hle : commV X ≤ fixV LA := by
    rw [← hLA, fixV_sup_eq]
    exact le_inf hleL hleK
  rw [hfixLA] at hle
  exact commV_ne_bot_of_faithful hfaith hXne_bot hXleY (le_bot_iff.mp hle)

end CFSG.LocalAnalysis.UniquenessCase.UC22
