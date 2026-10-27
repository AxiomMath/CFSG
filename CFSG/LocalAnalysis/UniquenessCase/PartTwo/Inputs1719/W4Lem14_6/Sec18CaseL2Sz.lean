module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Common
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Family
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Bender
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4PlusUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise


private theorem concl_alt5 {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : IsOmegaPlus ↥X 4 n ∧ NatOmegaPlus X ⊤ (fixV X) 4 n) : Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem concl_alt6 {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧ NatOmegaMinus X ⊤ (fixV X) 4 (n / 2)) :
    Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

private theorem concl_alt7 {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : IsL2 ↥X n ∧ BinaryNaturalSL X ⊤ (fixV X) 2 n) : Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

private theorem concl_alt8c {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
        (π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →* ↥X),
        Nat.card K = 2 ^ (n / 2) ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
          SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))) X ⊤ ⊥ 2 π) :
    Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (Or.inr (Or.inr (Or.inl h))))))))))

private theorem concl_alt9b {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : IsOmegaMinus ↥X 4 2 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2) X ⊤ ⊥ 3) :
    Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))))))

private theorem concl_alt10 {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : X ≠ L ∧ ∀ g : MulAut W, g ∈ Y → g ∉ normIn Y L →
      commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥) :
    Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

private theorem concl_alt13a {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : Fstar Y = X ∧
      ((IsL2 ↥X 3 ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 8)) ∨
        (IsL2 ↥X 4 ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16)) ∨
        (IsL2 ↥X 6 ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16)))) :
    Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))

private theorem concl_alt13b {W : Type} [CommGroup W] {Y L X : Subgroup (MulAut W)} {n : ℕ}
    (h : IsZ3xL2_64 ↥(Fstar Y) ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16)) :
    Sec18Concl Y L X n := by
  unfold Sec18Concl
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))

private theorem centralizer_dichotomy {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) {M : ℕ}
    (hM : Nat.card ↥(Subgroup.centralizer
      (autSub L (⊤ : Subgroup W) : Set (MulAut ↥(⊤ : Subgroup W)))) ≤ M) (hM3 : M ≤ 3) :
    (Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥) ∨
      (Nat.card ↥(Y ⊓ Subgroup.centralizer (L : Set (MulAut W))) = 3 ∧
        Nat.card ↥(Y ⊓ Subgroup.centralizer (L : Set (MulAut W))) ≤ M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup (MulAut W) := Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hPdef
  have hPY : P ≤ Y := inf_le_left
  have hstep : ∀ a : MulAut W, a ∈ Y → ∀ b : MulAut W, b ∈ P → a * b * a⁻¹ ∈ P := by
    intro a ha b hb
    obtain ⟨hbY, hbC⟩ := Subgroup.mem_inf.mp hb
    refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem ha hbY) (Y.inv_mem ha), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hbC ⊢
    intro z hz
    have hzy : a⁻¹ * z * a ∈ L :=
      (Subgroup.normal_subgroupOf_iff hLY).mp hLn z a⁻¹ hz (Y.inv_mem ha)
    have h1 : b * (a⁻¹ * z * a) = (a⁻¹ * z * a) * b := (hbC _ hzy).symm
    exact (calc (a * b * a⁻¹) * z = a * (b * (a⁻¹ * z * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * z * a) * b) * a⁻¹ := by rw [h1]
      _ = z * (a * b * a⁻¹) := by group).symm
  have hPn : (P.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hstep (g : MulAut W) g.2 (n : MulAut W) hn
  have hle : Nat.card ↥P ≤ Nat.card ↥(Subgroup.centralizer
      (autSub L (⊤ : Subgroup W) : Set (MulAut ↥(⊤ : Subgroup W)))) := by
    have hstab : ∀ x : ↥P, (x : MulAut W) ∈ stabSub (⊤ : Subgroup W) := fun x => by
      rw [mem_stabSub]
      intro u
      exact ⟨fun _ => Subgroup.mem_top u, fun _ => Subgroup.mem_top _⟩
    have hmem : ∀ x : ↥P, resHom (⊤ : Subgroup W) ⟨(x : MulAut W), hstab x⟩ ∈
        Subgroup.centralizer (autSub L (⊤ : Subgroup W) : Set (MulAut ↥(⊤ : Subgroup W))) := by
      intro x
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨g, hgL, hgy⟩ := mem_autSub.mp hy
      have hxc : (g : MulAut W) * (x : MulAut W) = (x : MulAut W) * (g : MulAut W) :=
        Subgroup.mem_centralizer_iff.mp x.2.2 (g : MulAut W) hgL
      rw [← hgy]
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      simpa [MulAut.mul_apply, resHom_apply] using
        congrArg (fun φ : MulAut W => φ (u : W)) hxc
    refine Nat.card_le_card_of_injective
      (fun x : ↥P => (⟨resHom (⊤ : Subgroup W) ⟨(x : MulAut W), hstab x⟩, hmem x⟩ :
        ↥(Subgroup.centralizer (autSub L (⊤ : Subgroup W) :
          Set (MulAut ↥(⊤ : Subgroup W)))))) ?_
    intro x y hxy
    have h1 : resHom (⊤ : Subgroup W) ⟨(x : MulAut W), hstab x⟩ =
        resHom (⊤ : Subgroup W) ⟨(y : MulAut W), hstab y⟩ := congrArg Subtype.val hxy
    have h2 := resHom_top_injective h1
    exact Subtype.ext (congrArg (fun z : ↥(stabSub (⊤ : Subgroup W)) => (z : MulAut W)) h2)
  have hcard3 : Nat.card ↥P ≤ 3 := hle.trans (hM.trans hM3)
  by_cases hbot : P = ⊥
  · exact Or.inl hbot
  · right
    have hne1 : Nat.card ↥P ≠ 1 := fun h => hbot (Subgroup.card_eq_one.mp h)
    have hne2 : Nat.card ↥P ≠ 2 := by
      intro h2
      have hP2 : IsPGroup 2 P := IsPGroup.iff_card.mpr ⟨1, by rw [h2]; norm_num⟩
      exact hbot (hO2 P hPY hPn hP2)
    have hpos : 1 ≤ Nat.card ↥P := Nat.card_pos
    exact ⟨by omega, hle.trans hM⟩

private theorem mQuot_top_bot_eq_rk {W : Type} [CommGroup W] [Finite W] :
    E3.mQuot (⊤ : Subgroup W) (⊥ : Subgroup W) = rk W := by
  have h : (⊥ : Subgroup W).relIndex (⊤ : Subgroup W) = Nat.card W := by
    rw [Subgroup.relIndex]
    simp
  unfold E3.mQuot rk
  rw [h]

private theorem natOmegaMinus_of_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV)
    (hs : IsSimpleGroup ↥L) {I J : Subgroup W} (hI : I ∈ irrSet L) (hJ : J ∈ irrSet L)
    (hIfix : I ⊓ fixV L = ⊥) (hJfix : J ⊓ fixV L = ⊥) {k : ℕ}
    (h : NatOmegaMinus (autSub L I) ⊤ ⊥ 4 k) : NatOmegaMinus L J ⊥ 4 k := by
  obtain ⟨g, hgY, hsec⟩ :=
    exists_secIsoOn_of_mem_irrSet_of_basic hW hO2 hB hL hfixH hsum hI hJ
  have hg : L.map (MulAut.conj g).toMonoidHom = L :=
    Thm14_5.map_conj_eq_of_secIsoOn hL.1 hsum hI hJ hJfix hgY hsec
  have hLI : L ≤ stabSub I := Thm14_5.le_stabSub_of_mem_irrSet hI
  have hLJ : L ≤ stabSub J := Thm14_5.le_stabSub_of_mem_irrSet hJ
  obtain ⟨ψ, hψ⟩ := Thm14_5.exists_mulEquiv_autSub_eq_map hg hLI hLJ hsec
  have hJ' : NatOmegaMinus (autSub L J) ⊤ ⊥ 4 k := by
    refine natOmegaMinus_of_map_congrHom ψ.symm ?_ h
    rw [hψ, Subgroup.map_map, H.LU.congrHom_symm_comp, Subgroup.map_id]
  have hinjJ : ∀ l ∈ L, (∀ u ∈ J, l u = u) → l = 1 := by
    intro l hl hlu
    have hmem : l ∈ L ⊓ centSub J := ⟨hl, mem_centSub.mpr hlu⟩
    rw [inf_centSub_eq_bot_of_isSimpleGroup hs hLJ (Thm14_5.not_le_centSub_of_mem_irrSet hJ hJfix),
      Subgroup.mem_bot] at hmem
    exact hmem
  exact Thm14_5.natOmegaMinus_of_autSub hLJ hinjJ hJ'

private theorem sumOfNatVia_two_omegaMinus {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)}
    {I J : Subgroup W} {K : Type} [Field K] [Finite K] {b c : K}
    {π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →* ↥L}
    (hπ : (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))).RealizesVia L I ⊥ π)
    (hI : I ∈ irrSet L) (hIJ : I ⊓ J = ⊥) (hIJtop : I ⊔ J = ⊤)
    (hsec : SecIsoOn L I ⊥ J ⊥) :
    SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))) L ⊤ ⊥ 2 π := by
  let f : Fin 2 → Subgroup W := fun i => if i = 0 then I else J
  have hf0 : f 0 = I := by simp [f]
  have hf1 : f 1 = J := by simp [f]
  have hind : iSupIndep f := by
    apply (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
      (fun k => by fin_cases k <;> simp)).mpr
    rw [hf0, hf1]
    exact disjoint_iff.mpr hIJ
  have htop : (⨆ i, f i) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hIJtop]
    exact sup_le (hf0 ▸ le_iSup f 0) (hf1 ▸ le_iSup f 1)
  refine sumOfNatVia_of_secIsoOn hπ f ?_ hind htop
  intro i
  by_cases hi : i = 0
  · rw [hi, hf0]
    exact secIsoOn_refl hI.2.2.1 (fun x _ u hu => by
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]) bot_le
  · have hi1 : i = 1 := by fin_cases i <;> simp_all
    rw [hi1, hf1]
    exact hsec

private theorem sumOfNat_three {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {x y z : Subgroup W} (hx : x ⊓ (y ⊔ z) = ⊥) (hy : y ⊓ (x ⊔ z) = ⊥)
    (hz : z ⊓ (x ⊔ y) = ⊥) (hsup : x ⊔ y ⊔ z = ⊤)
    (hNx : NatOmegaMinus L x ⊥ 4 2) (hNy : NatOmegaMinus L y ⊥ 4 2)
    (hNz : NatOmegaMinus L z ⊥ 4 2) :
    SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2) L ⊤ ⊥ 3 := by
  have e0 : (⨆ (j : Fin 3) (_ : j ≠ 0), ![x, y, z] j) = y ⊔ z := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le ?_ ?_)
    · fin_cases j <;> simp_all
    · simpa using le_iSup₂ (f := fun j (_ : j ≠ 0) => ![x, y, z] j) 1 (by decide)
    · simpa using le_iSup₂ (f := fun j (_ : j ≠ 0) => ![x, y, z] j) 2 (by decide)
  have e1 : (⨆ (j : Fin 3) (_ : j ≠ 1), ![x, y, z] j) = x ⊔ z := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le ?_ ?_)
    · fin_cases j <;> simp_all
    · simpa using le_iSup₂ (f := fun j (_ : j ≠ 1) => ![x, y, z] j) 0 (by decide)
    · simpa using le_iSup₂ (f := fun j (_ : j ≠ 1) => ![x, y, z] j) 2 (by decide)
  have e2 : (⨆ (j : Fin 3) (_ : j ≠ 2), ![x, y, z] j) = x ⊔ y := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le ?_ ?_)
    · fin_cases j <;> simp_all
    · simpa using le_iSup₂ (f := fun j (_ : j ≠ 2) => ![x, y, z] j) 0 (by decide)
    · simpa using le_iSup₂ (f := fun j (_ : j ≠ 2) => ![x, y, z] j) 1 (by decide)
  have esup : (⨆ i, ![x, y, z] i) = x ⊔ y ⊔ z := by
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (sup_le ?_ ?_) ?_)
    · fin_cases i
      · exact le_trans le_sup_left le_sup_left
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right
    · simpa using le_iSup (fun i => ![x, y, z] i) 0
    · simpa using le_iSup (fun i => ![x, y, z] i) 1
    · simpa using le_iSup (fun i => ![x, y, z] i) 2
  refine ⟨![x, y, z], fun i => bot_le, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [e0] using hx
    · simpa [e1] using hy
    · simpa [e2] using hz
  · rw [bot_sup_eq, esup, hsup]
  · intro i
    fin_cases i
    · simpa using hNx
    · simpa using hNy
    · simpa using hNz

private theorem conjSet_eq_conjSet_of_ncard_le_two {W : Type} [CommGroup W] [Finite W]
    {Y L T : Subgroup (MulAut W)} (hT : IsSylowIn 2 T Y)
    (hc : (conjSet L Y).ncard ≤ 2) : conjSet L Y = conjSet L T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  refine Set.Subset.antisymm ?_ ?_
  · intro X hX
    obtain ⟨y, hy, rfl⟩ := hX
    by_cases hyL : L.map (MulAut.conj y).toMonoidHom = L
    · exact ⟨1, T.one_mem, by rw [hyL, CFSG.Timmesfeld.RankOne.map_conj_one]⟩
    · have hLy : L.map (MulAut.conj y).toMonoidHom ∈ conjSet L Y := ⟨y, hy, rfl⟩
      have hL : L ∈ conjSet L Y :=
        ⟨1, Y.one_mem, (CFSG.Timmesfeld.RankOne.map_conj_one L).symm⟩
      have hne : L ≠ L.map (MulAut.conj y).toMonoidHom := fun h => hyL h.symm
      have hpair : ({L, L.map (MulAut.conj y).toMonoidHom} : Set (Subgroup (MulAut W))) ⊆
          conjSet L Y := by
        intro Z hZ
        rcases hZ with rfl | rfl
        · exact hL
        · exact hLy
      have hS : conjSet L Y = {L, L.map (MulAut.conj y).toMonoidHom} := by
        refine (Set.eq_of_subset_of_ncard_le hpair ?_).symm
        rw [Set.ncard_pair hne]
        exact hc
      let H : Subgroup ↥Y :=
        { carrier := {x : ↥Y | L.map (MulAut.conj ((x : ↥Y) : MulAut W)).toMonoidHom = L}
          one_mem' := by simpa using CFSG.Timmesfeld.RankOne.map_conj_one L
          mul_mem' := by
            rintro x y hx hy
            change L.map (MulAut.conj ((x : MulAut W) * (y : MulAut W))).toMonoidHom = L
            rw [CFSG.Timmesfeld.RankOne.map_conj_mul, hy, hx]
          inv_mem' := by
            rintro x hx
            change L.map (MulAut.conj ((x : MulAut W))⁻¹).toMonoidHom = L
            have h := CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj L (x : MulAut W)
            rwa [hx] at h }
      have hHidx : H.index = 2 := by
        refine (Subgroup.index_eq_two_iff_exists_notMem_and').2 ⟨(⟨y, hy⟩ : ↥Y)⁻¹, ?_, ?_⟩
        · intro hmem
          have h1 : L.map (MulAut.conj ((y : MulAut W)⁻¹)).toMonoidHom = L := hmem
          have h2 := CFSG.Timmesfeld.RankOne.map_conj_map_conj_inv L y
          rw [h1] at h2
          exact hyL h2
        · intro b
          by_cases hb : b ∈ H
          · exact Or.inr hb
          · left
            have hbne : L.map (MulAut.conj ((b : ↥Y) : MulAut W)).toMonoidHom ≠ L := hb
            have hbmem : L.map (MulAut.conj ((b : ↥Y) : MulAut W)).toMonoidHom ∈ conjSet L Y :=
              ⟨b, b.2, rfl⟩
            rw [hS] at hbmem
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbmem
            have hbeq : L.map (MulAut.conj ((b : ↥Y) : MulAut W)).toMonoidHom =
                L.map (MulAut.conj y).toMonoidHom := by
              rcases hbmem with h | h
              · exact absurd h hbne
              · exact h
            change L.map (MulAut.conj ((y : MulAut W)⁻¹ * (b : MulAut W))).toMonoidHom = L
            rw [CFSG.Timmesfeld.RankOne.map_conj_mul, hbeq,
              CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj]
      have hnotle : ¬ (hT.toSylow : Subgroup ↥Y) ≤ H :=
        CFSG.QuasiDihedralFusion.sylow_not_le_of_index_two hHidx hT.toSylow
      obtain ⟨t, htQ, htH⟩ := Set.not_subset.1 hnotle
      have htT : (t : MulAut W) ∈ T := by
        have ht : t ∈ T.subgroupOf Y := by
          rwa [← hT.coe_toSylow]
        exact (Subgroup.mem_subgroupOf).1 ht
      have htL : L.map (MulAut.conj ((t : ↥Y) : MulAut W)).toMonoidHom ≠ L := htH
      have htmem : L.map (MulAut.conj ((t : ↥Y) : MulAut W)).toMonoidHom ∈ conjSet L Y :=
        ⟨t, t.2, rfl⟩
      rw [hS] at htmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htmem
      have hteq : L.map (MulAut.conj ((t : ↥Y) : MulAut W)).toMonoidHom =
          L.map (MulAut.conj y).toMonoidHom := by
        rcases htmem with h | h
        · exact absurd h htL
        · exact h
      exact ⟨(t : MulAut W), htT, hteq.symm⟩
  · rintro X ⟨t, ht, rfl⟩
    exact ⟨t, hT.le ht, rfl⟩

private theorem omegaPlus_of_case3 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L X R : Subgroup (MulAut W)} {n e : ℕ}
    (hO2 : O2Trivial Y) (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV X = ⊥)
    (hc : (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y).ncard ≤ 2)
    (hRY : R ≤ Y)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet R Y) commV)
    (hLR : CFSG.Open.IsSubnormal L R) (hnat : IsNaturalO4Plus R e) (hd : dMinDeg ↥L = 2 * n)
    (hL2 : IsL2 ↥L n) (hn : 2 < n) :
    IsOmegaPlus ↥X 4 n ∧ NatOmegaPlus X ⊤ (fixV X) 4 n := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨T, hT⟩ := CFSG.Quasithin.E1.exists_isSylowIn_two Y
  have hS : conjSet L Y = conjSet L T := conjSet_eq_conjSet_of_ncard_le_two hT hc
  have hncard : (conjSet L T).ncard ≤ 2 := by
    rw [← hS]
    exact hc
  have hfixT : fixV (⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) = ⊥ := by
    rw [← iSup_conjSet_eq_biSup_conj L T, ← hS, iSup_conjSet_eq_biSup_conj L Y, ← hX]
    exact hfix
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hR1 := Thm14_5.conjSet_eq_singleton_of_o4Plus hL hT hfixT hncard hRY hsum hLR hnat
  have he : e = n := Thm14_5.isL2_param_unique
    (Thm14_5.isL2_of_isSubnormal_isNaturalO4Plus hq hLR hnat) hL2
  have hRtop : commV R = ⊤ := by
    rw [eq_top_iff, ← hsum.2]
    refine iSup_le fun X' => ?_
    have hX' : (X' : Subgroup (MulAut W)) = R :=
      Set.mem_singleton_iff.mp ((Set.ext_iff.mp hR1 _).mp X'.2)
    rw [hX']
  have hres := Thm14_5.isOmegaPlus_natOmegaPlus_commutator hnat hRtop
  rw [he] at hres
  have hcom : (⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) = ⁅R, R⁆ :=
    Thm14_5.iSup_map_conj_eq_commutator hq hRY hLR hnat hR1
  refine ⟨?_, ?_⟩
  · rw [hX, hcom]
    exact hres.1
  · rw [hfix, hX, hcom]
    exact hres.2

theorem concl146_of_caseI_L2
    (hMod : K146ModL2) (hIso : K146NatIsoOm4m)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L X : Subgroup (MulAut W)} {n : ℕ} (hK : CFSG.IsKGroup ↥Y) (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hL2 : IsL2 ↥L n) (hn : 2 < n)
    (hc : (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y).ncard ≤ 2)
    (hfix : fixV X = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ max (bParam X Y) n + 2) : Sec18Concl Y L X n := by
  classical
  obtain ⟨i, e, hBe, hi⟩ := exists_benderType_of_shape hn (Or.inl hL2)
  have hb : bParam X Y ≤ n := bParam_le_of_benderType hW hL hX hBe hi
  have hmn : E3.mParam Y ≤ n + 2 := by
    have h : max (bParam X Y) n = n := max_eq_right hb
    omega
  have hd : dMinDeg ↥L = 2 * n := (dMinDeg_lower_bounds (L := ↥L)).1 hL2 (by omega)
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have hs : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  rcases w4Lem12_8_holds W hW Y hO2 hB L hL _ rfl with
    h1 | ⟨hsumQ, I, hI, hineqQ⟩ | ⟨R, e', hRY, hsumR, hLR, hnatR, hmY, hdL⟩
  · omega
  ·
    have hsum0 : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
        (fun X' => commV (autQuot X' (⊥ : Subgroup W))) := by
      rw [← hfixH]; exact hsumQ
    have hIm : (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
        (E3.mParam Y : ℚ) := by
      have key : ∀ N : Subgroup W, N = ⊥ →
          (E3.mParam (autSub (autQuot Y N) (Subgroup.map (QuotientGroup.mk' N) I)) : ℚ) *
              ((rk ↥(commV (autQuot L N)) : ℚ) /
                (rk ↥(Subgroup.map (QuotientGroup.mk' N) I) : ℚ)) ≤ (E3.mParam Y : ℚ) →
          (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
            (E3.mParam Y : ℚ) := by
        rintro N rfl h
        rwa [Thm14_5.mParam_autSub_autQuot_bot, Thm14_5.rk_commV_autQuot_bot,
          Thm14_5.rk_map_mk_bot] at h
      exact key _ hfixH hineqQ
    by_cases hXL : X = L
    · rw [hXL] at hX hfix ⊢
      have htop : commV L = ⊤ := commV_eq_top_of_basic hW hO2 hB hL hX
      have hLn : (L.subgroupOf Y).Normal :=
        (Thm14_5.iSup_map_conj_eq_self_iff hL.1).mp hX.symm
      obtain ⟨hle, hnorm, hirr, hrkI, hmul, hmN⟩ :=
        setup_of_case2 hW hL hX hfix hsum0 hI hIm
      have hLIstab : L ≤ stabSub I := Thm14_5.le_stabSub_of_mem_irrSet hI
      have hIfix : I ⊓ fixV L = ⊥ := by
        have hinf := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
        have hIc : I ≤ commV L := by
          rw [commV_eq_commSub, ← hI.1]
          exact commSub_mono le_top le_rfl
        exact le_bot_iff.mp (hinf ▸ inf_le_inf_right _ hIc)
      have hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1 := by
        intro l hl hlu
        have hmem : l ∈ L ⊓ centSub I := ⟨hl, mem_centSub.mpr hlu⟩
        rw [inf_centSub_eq_bot_of_isSimpleGroup hs hLIstab
          (Thm14_5.not_le_centSub_of_mem_irrSet hI hIfix), Subgroup.mem_bot] at hmem
        exact hmem
      have hW' : ∀ u : ↥I, u ^ 2 = 1 :=
        fun u => Subtype.ext (by simpa using hW (u : W))
      have hL2' : IsL2 ↥(autSub L I) n := lieModel_autSub hL hX hfix hsum0 hs hI hL2
      rcases hMod ↥I hW' (autSub Y I) (autSub L I) n hle hnorm hL2' hn hirr (hmN.trans hmn) with
        hcase1 | hcase2 | hcase3 | hcase4 | hcase5
      ·
        obtain ⟨hnat, hnle⟩ := hcase1
        have hnatL : BinaryNaturalSL L I ⊥ 2 n :=
          Thm14_5.binaryNaturalSL_of_autSub hLIstab hinj hnat
        have hrk : rk ↥I = n * 2 := by
          have h := s16c1610_rk_binaryNaturalSL hnat
          rwa [rk_top] at h
        have hrkW : rk ↥(commV L) < rk ↥I + dMinDeg ↥L := by
          have h1 : n * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
            Nat.mul_le_mul_right _ hnle
          have h2 : E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I := hmul
          have h3 : E3.mParam Y * rk ↥I ≤ (n + 2) * rk ↥I := Nat.mul_le_mul_right _ hmn
          have h4' : n * rk ↥(commV L) ≤ (n + 2) * rk ↥I := h1.trans (h2.trans h3)
          have h4 : n * rk ↥(commV L) ≤ (n + 2) * (n * 2) := by
            rw [hrk] at h4'
            exact h4'
          have h5 : (n + 2) * (n * 2) < n * (4 * n) := by nlinarith
          have h6 : rk ↥(commV L) < 4 * n := Nat.lt_of_mul_lt_mul_left (h4.trans_lt h5)
          rw [hd, hrk]
          omega
        have hLI : commV L = I := commV_eq_of_rk_lt_dMinDeg hW hL hI hrkW
        have hItop : I = ⊤ := hLI.symm.trans htop
        refine concl_alt7 ⟨hL2, ?_⟩
        rw [hfix]
        exact hItop ▸ hnatL
      ·
        obtain ⟨heven, hnat, hn2m⟩ := hcase2
        have hnatL : NatOmegaMinus L I ⊥ 4 (n / 2) :=
          Thm14_5.natOmegaMinus_of_autSub hLIstab hinj hnat
        have hOmL : IsOmegaMinus ↥L 4 (n / 2) := by
          have hAut : IsOmegaMinus ↥(autSub L I) 4 (n / 2) :=
            isOmegaMinus_of_natOmegaMinus_four hnat
          have hinjRes : Function.Injective (Thm14_5.resTo hLIstab) := by
            intro a b hab
            have h1 : Thm14_5.resTo hLIstab (a * b⁻¹) = 1 := by
              rw [map_mul, map_inv, hab, mul_inv_cancel]
            have h2 : ((a * b⁻¹ : ↥L) : MulAut W) = 1 :=
              hinj (a * b⁻¹) (a * b⁻¹).2 ((Thm14_5.resTo_eq_one_iff hLIstab _).mp h1)
            exact mul_inv_eq_one.mp (Subtype.ext h2)
          let eL : ↥L ≃* ↥(autSub L I) :=
            MulEquiv.ofBijective (Thm14_5.resTo hLIstab)
              ⟨hinjRes, Thm14_5.resTo_surjective hLIstab⟩
          exact IsOmegaMinus.of_mulEquiv eL.symm hAut
        have hrk : rk ↥I = (n / 2) * 4 := by
          have h := s16c1610_rk_natOmegaMinus (n := 4) (a := n / 2) (by norm_num) hnat
          rwa [rk_top] at h
        have hn2 : 2 * (n / 2) = n := by
          obtain ⟨k, hk⟩ := heven
          omega
        have hrk2 : rk ↥I = 2 * n := by omega
        have hsumC : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV :=
          Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
        obtain ⟨s, hIs, hsL, hsind, hsup⟩ :=
          exists_sSupIndep_irrSet_of_basic hW hO2 hB hL hfixH hsumC hI
        have hfin : ∑ᶠ U ∈ s, rk ↥U = s.ncard * rk ↥I :=
          s15_Two_finsum_mem_eq_ncard_mul s (fun U => rk ↥U) (rk ↥I) (Set.toFinite s)
            (fun U hU => rk_eq_of_mem_irrSet_of_basic hW hO2 hB hL hfixH hsumC hI (hsL hU))
        have hrkW : rk ↥(commV L) = s.ncard * rk ↥I := by
          rw [← hsup]
          exact (s15_Lin_rk_sSup_eq_finsum hsind).trans hfin
        have hmN2 : n / 2 ≤ E3.mParam (autSub Y I) := by omega
        have hbound : (n / 2) * rk ↥(commV L) ≤ (n + 2) * rk ↥I := by
          have h1 : (n / 2) * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
            Nat.mul_le_mul_right _ hmN2
          exact h1.trans (hmul.trans (Nat.mul_le_mul_right _ hmn))
        rw [hrkW, hrk2] at hbound
        have hsle : s.ncard ≤ 3 := by
          obtain ⟨k, hk⟩ := heven
          have hcm : ((n / 2) * s.ncard) * (2 * n) ≤ (n + 2) * (2 * n) := by
            rw [Nat.mul_assoc]
            exact hbound
          have h3 : n / 2 * s.ncard ≤ n + 2 := Nat.le_of_mul_le_mul_right hcm (by omega)
          have hdiv : n / 2 = k := by omega
          rw [hdiv] at h3
          have hk2 : 2 ≤ k := by omega
          nlinarith
        have hs1 : 1 ≤ s.ncard := by
          rw [Nat.one_le_iff_ne_zero, Ne]
          intro h
          rw [Set.ncard_eq_zero] at h
          rw [h] at hIs
          exact absurd hIs (Set.notMem_empty I)
        interval_cases hs3 : s.ncard
        ·
          have hsingle : s = {I} := by
            obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hs3
            rw [hx] at hIs ⊢
            rw [Set.mem_singleton_iff] at hIs
            rw [hIs.symm]
          have hItop : I = ⊤ := by
            rw [← htop, ← hsup, hsingle, sSup_singleton]
          refine concl_alt6 ⟨heven, hOmL, ?_⟩
          rw [hfix, ← hItop]
          exact hnatL
        ·
          obtain ⟨x, y, hxy, hsxy⟩ := Set.ncard_eq_two.mp hs3
          obtain ⟨-, K, hKfld, hKfin, b, c, hKcard, hirrK, hreal⟩ := hnatL
          obtain ⟨π, hπ⟩ := hreal
          have hstep : ∀ B : Subgroup W, s = {I, B} → B ≠ I →
              SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))) L ⊤ ⊥ 2 π := by
            intro B hBs hBI
            have hBs' : B ∈ s := by rw [hBs]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
            have hBirr : B ∈ irrSet L := hsL hBs'
            have hBfix : B ⊓ fixV L = ⊥ := by
              have hinf := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
              have hBc : B ≤ commV L := by
                rw [← hsup]
                exact le_sSup hBs'
              exact le_bot_iff.mp (hinf ▸ inf_le_inf_right _ hBc)
            have hnatB : NatOmegaMinus L B ⊥ 4 (n / 2) :=
              natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsumC hs hI hBirr hIfix hBfix hnat
            have hsec : SecIsoOn L I ⊥ B ⊥ :=
              hIso W hW L n I B hL2 heven hn (Thm14_5.natOmegaMinus_of_autSub hLIstab hinj hnat)
                hnatB
            have hdisj : I ⊓ B = ⊥ := by
              have h1 : ({I, B} : Set (Subgroup W)) ⊆ s := by
                intro A hA
                rw [hBs]
                exact hA
              have h2 : sSupIndep ({I, B} : Set (Subgroup W)) := hsind.mono h1
              exact disjoint_iff.mp ((sSupIndep_pair hBI.symm).1 h2)
            have htopB : I ⊔ B = ⊤ := by
              rw [← htop, ← hsup, hBs, sSup_pair]
            exact sumOfNatVia_two_omegaMinus hπ hI hdisj htopB hsec
          have hIxy : I = x ∨ I = y := by
            have h : I ∈ ({x, y} : Set (Subgroup W)) := hsxy ▸ hIs
            simpa using h
          rcases hIxy with hIx | hIy
          · exact concl_alt8c ⟨heven, hOmL, K, hKfld, hKfin, b, c, π, hKcard, hirrK,
              hstep y (hIx.symm ▸ hsxy) (fun h => hxy (h.trans hIx).symm)⟩
          · exact concl_alt8c ⟨heven, hOmL, K, hKfld, hKfin, b, c, π, hKcard, hirrK,
              hstep x (Set.pair_comm x I ▸ (hIy.symm ▸ hsxy)) (fun h => hxy (h.trans hIy))⟩
        ·
          have hhalf : n / 2 = 2 := by
            have hcm : ((n / 2) * 3) * (2 * n) ≤ (n + 2) * (2 * n) := by
              rw [Nat.mul_assoc]
              exact hbound
            have h3 : n / 2 * 3 ≤ n + 2 := Nat.le_of_mul_le_mul_right hcm (by omega)
            obtain ⟨k, hk⟩ := heven
            have hdiv : n / 2 = k := by omega
            rw [hdiv] at h3
            omega
          rw [hhalf] at hnat
          obtain ⟨x, y, z, hxy, hxz, hyz, hsxyz⟩ := Set.ncard_eq_three.mp hs3
          have hmem3 : ∀ A ∈ ({x, y, z} : Set (Subgroup W)), A ∈ s := by
            intro A hA
            rw [hsxyz]
            exact hA
          have hirr3 : ∀ A ∈ ({x, y, z} : Set (Subgroup W)), A ∈ irrSet L :=
            fun A hA => hsL (hmem3 A hA)
          have hfix3 : ∀ A ∈ ({x, y, z} : Set (Subgroup W)), A ⊓ fixV L = ⊥ := by
            intro A hA
            have hinf := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
            have hAc : A ≤ commV L := by
              rw [← hsup]
              exact le_sSup (hmem3 A hA)
            exact le_bot_iff.mp (hinf ▸ inf_le_inf_right _ hAc)
          have hnat3 : ∀ A ∈ ({x, y, z} : Set (Subgroup W)), NatOmegaMinus L A ⊥ 4 2 :=
            fun A hA => natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsumC hs hI
              (hirr3 A hA) hIfix (hfix3 A hA) hnat
          have hsind3 : sSupIndep ({x, y, z} : Set (Subgroup W)) := by
            refine hsind.mono ?_
            intro A hA
            rw [hsxyz]
            exact hA
          have hdisj3 : ∀ A ∈ ({x, y, z} : Set (Subgroup W)),
              A ⊓ sSup (({x, y, z} : Set (Subgroup W)) \ {A}) = ⊥ := by
            intro A hA
            exact disjoint_iff.mp (hsind3 hA)
          have hsetx : ({x, y, z} : Set (Subgroup W)) \ {x} = {y, z} := by
            ext A
            simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h1 with rfl | rfl | rfl
              · exact absurd rfl h2
              · exact Or.inl rfl
              · exact Or.inr rfl
            · intro h
              rcases h with rfl | rfl
              · exact ⟨Or.inr (Or.inl rfl), fun h' => hxy h'.symm⟩
              · exact ⟨Or.inr (Or.inr rfl), fun h' => hxz h'.symm⟩
          have hsety : ({x, y, z} : Set (Subgroup W)) \ {y} = {x, z} := by
            ext A
            simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h1 with rfl | rfl | rfl
              · exact Or.inl rfl
              · exact absurd rfl h2
              · exact Or.inr rfl
            · intro h
              rcases h with rfl | rfl
              · exact ⟨Or.inl rfl, fun h' => hxy h'⟩
              · exact ⟨Or.inr (Or.inr rfl), fun h' => hyz h'.symm⟩
          have hsetz : ({x, y, z} : Set (Subgroup W)) \ {z} = {x, y} := by
            ext A
            simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h1 with rfl | rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr rfl
              · exact absurd rfl h2
            · intro h
              rcases h with rfl | rfl
              · exact ⟨Or.inl rfl, fun h' => hxz h'⟩
              · exact ⟨Or.inr (Or.inl rfl), fun h' => hyz h'⟩
          have hsup3 : x ⊔ y ⊔ z = ⊤ := by
            rw [← htop, ← hsup, hsxyz, sSup_insert, sSup_pair, sup_assoc]
          have hOmL4 : IsOmegaMinus ↥L 4 2 := hhalf ▸ hOmL
          exact concl_alt9b ⟨hOmL4, sumOfNat_three
            (by
              rw [← sSup_pair, ← hsetx]
              exact hdisj3 x (Set.mem_insert x _))
            (by
              have h := hdisj3 y (Set.mem_insert_of_mem _ (Set.mem_insert y _))
              rwa [hsety, sSup_pair] at h)
            (by
              have h := hdisj3 z (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
                (Set.mem_singleton z)))
              rwa [hsetz, sSup_pair] at h)
            hsup3 (hnat3 x (Set.mem_insert x _))
            (hnat3 y (Set.mem_insert_of_mem _ (Set.mem_insert y _)))
            (hnat3 z (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton z))))⟩
      ·
        obtain ⟨hn3, hrk8, hm4, hcentS⟩ := hcase3
        subst hn3
        have hItop : I = ⊤ := by
          have hrkW : rk ↥(commV L) < rk ↥I + dMinDeg ↥L := by
            have h1 : 4 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
              Nat.mul_le_mul_right _ hm4
            have h3 : E3.mParam Y * rk ↥I ≤ 5 * rk ↥I := by
              simpa using Nat.mul_le_mul_right (rk ↥I) hmn
            have h4 : 4 * rk ↥(commV L) ≤ 5 * 8 := by
              calc 4 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) := h1
                _ ≤ E3.mParam Y * rk ↥I := hmul
                _ ≤ 5 * rk ↥I := h3
                _ = 5 * 8 := by rw [hrk8]
            rw [hd, hrk8]
            omega
          exact (commV_eq_of_rk_lt_dMinDeg hW hL hI hrkW).symm.trans htop
        have hirrTop : IsIrrOn L ⊤ ⊥ := by
          have h := hI.2
          rw [hItop, top_inf_eq, hfix] at h
          exact h
        have hrkW8 : rk W = 8 := by
          rw [← rk_top (G := W), ← hItop]
          exact hrk8
        have hquot : E3.mQuot (⊤ : Subgroup W) ⊥ = 8 := by
          rw [mQuot_top_bot_eq_rk, hrkW8]
        rw [hItop] at hcentS
        have hM1 : Nat.card ↥(Subgroup.centralizer
            (autSub L (⊤ : Subgroup W) : Set (MulAut ↥(⊤ : Subgroup W)))) ≤ 1 := by
          rw [hcentS]
          simp
        have hfs : Fstar Y = L := by
          rcases centralizer_dichotomy hW hO2 hL.1 hLn (M := 1) hM1 (by norm_num) with h | h
          · exact (fstar_eq_of_centralizer hL.1 hLn hs).1 h
          · omega
        exact concl_alt13a ⟨hfs, Or.inl ⟨hL2, hirrTop, hquot⟩⟩
      ·
        obtain ⟨hn4, hrk16, hm6, hcentS⟩ := hcase4
        subst hn4
        have hItop : I = ⊤ := by
          have hrkW : rk ↥(commV L) < rk ↥I + dMinDeg ↥L := by
            have h1 : 6 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
              Nat.mul_le_mul_right _ hm6
            have h3 : E3.mParam Y * rk ↥I ≤ 6 * rk ↥I := by
              simpa using Nat.mul_le_mul_right (rk ↥I) hmn
            have h4 : 6 * rk ↥(commV L) ≤ 6 * 16 := by
              calc 6 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) := h1
                _ ≤ E3.mParam Y * rk ↥I := hmul
                _ ≤ 6 * rk ↥I := h3
                _ = 6 * 16 := by rw [hrk16]
            rw [hd, hrk16]
            omega
          exact (commV_eq_of_rk_lt_dMinDeg hW hL hI hrkW).symm.trans htop
        have hirrTop : IsIrrOn L ⊤ ⊥ := by
          have h := hI.2
          rw [hItop, top_inf_eq, hfix] at h
          exact h
        have hrkW16 : rk W = 16 := by
          rw [← rk_top (G := W), ← hItop]
          exact hrk16
        have hquot : E3.mQuot (⊤ : Subgroup W) ⊥ = 16 := by
          rw [mQuot_top_bot_eq_rk, hrkW16]
        rw [hItop] at hcentS
        have hM1 : Nat.card ↥(Subgroup.centralizer
            (autSub L (⊤ : Subgroup W) : Set (MulAut ↥(⊤ : Subgroup W)))) ≤ 1 := by
          rw [hcentS]
          simp
        have hfs : Fstar Y = L := by
          rcases centralizer_dichotomy hW hO2 hL.1 hLn (M := 1) hM1 (by norm_num) with h | h
          · exact (fstar_eq_of_centralizer hL.1 hLn hs).1 h
          · omega
        exact concl_alt13a ⟨hfs, Or.inr (Or.inl ⟨hL2, hirrTop, hquot⟩)⟩
      ·
        obtain ⟨hn6, hrk16, hm8, hcentS⟩ := hcase5
        subst hn6
        have hItop : I = ⊤ := by
          have hrkW : rk ↥(commV L) < rk ↥I + dMinDeg ↥L := by
            have h1 : 8 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
              Nat.mul_le_mul_right _ hm8
            have h3 : E3.mParam Y * rk ↥I ≤ 8 * rk ↥I := by
              simpa using Nat.mul_le_mul_right (rk ↥I) hmn
            have h4 : 8 * rk ↥(commV L) ≤ 8 * 16 := by
              calc 8 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) := h1
                _ ≤ E3.mParam Y * rk ↥I := hmul
                _ ≤ 8 * rk ↥I := h3
                _ = 8 * 16 := by rw [hrk16]
            rw [hd, hrk16]
            omega
          exact (commV_eq_of_rk_lt_dMinDeg hW hL hI hrkW).symm.trans htop
        have hirrTop : IsIrrOn L ⊤ ⊥ := by
          have h := hI.2
          rw [hItop, top_inf_eq, hfix] at h
          exact h
        have hrkW16 : rk W = 16 := by
          rw [← rk_top (G := W), ← hItop]
          exact hrk16
        have hquot : E3.mQuot (⊤ : Subgroup W) ⊥ = 16 := by
          rw [mQuot_top_bot_eq_rk, hrkW16]
        rw [hItop] at hcentS
        rcases centralizer_dichotomy hW hO2 hL.1 hLn (M := 3)
          (Nat.le_of_dvd (by norm_num) hcentS) le_rfl with hbot | hcard
        · have hfs : Fstar Y = L := (fstar_eq_of_centralizer hL.1 hLn hs).1 hbot
          exact concl_alt13a ⟨hfs, Or.inr (Or.inr ⟨hL2, hirrTop, hquot⟩)⟩
        · have hz : IsZ3xL2_64 ↥(Fstar Y) :=
            (fstar_eq_of_centralizer hL.1 hLn hs).2 hL2 hcard.1
          exact concl_alt13b ⟨hz, hirrTop, hquot⟩
    ·
      exact concl_alt10 ⟨hXL, fun g hg hgN => commSub_commSub_eq_bot_of_dirSum hL hsum0 hg hgN⟩
  ·
    exact concl_alt5 (omegaPlus_of_case3 hW hO2 hL hX hfix hc hRY hsumR hLR hnatR hd hL2 hn)

theorem false_of_caseI_Sz
    (hMod : K146ModSz)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L X : Subgroup (MulAut W)} {n : ℕ} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hSz : IsSz ↥L n) (hn : 2 < n)
    (hfix : fixV X = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ max (bParam X Y) n + 2) : False := by
  classical
  obtain ⟨i, e, hBe, hi⟩ := exists_benderType_of_shape hn (Or.inr hSz)
  have hb : bParam X Y ≤ n := bParam_le_of_benderType hW hL hX hBe hi
  have hmn : E3.mParam Y ≤ n + 2 := by
    have h : max (bParam X Y) n = n := max_eq_right hb
    omega
  have hd4 : 4 * n ≤ dMinDeg ↥L := (dMinDeg_lower_bounds (L := ↥L)).2.1 hSz
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have hnL2 : ∀ e : ℕ, ¬ IsL2 ↥L e := fun e' he' => not_isL2_of_shape (Or.inl hSz) he'
  rcases w4Lem12_8_holds W hW Y hO2 hB L hL _ rfl with
    h1 | ⟨hsumQ, I, hI, hineqQ⟩ | ⟨R, e', -, -, hLR, hnatR, -, -⟩
  · omega
  · have hsum0 : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
        (fun X' => commV (autQuot X' (⊥ : Subgroup W))) := by
      rw [← hfixH]; exact hsumQ
    have hIm : (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
        (E3.mParam Y : ℚ) := by
      have key : ∀ N : Subgroup W, N = ⊥ →
          (E3.mParam (autSub (autQuot Y N) (Subgroup.map (QuotientGroup.mk' N) I)) : ℚ) *
              ((rk ↥(commV (autQuot L N)) : ℚ) /
                (rk ↥(Subgroup.map (QuotientGroup.mk' N) I) : ℚ)) ≤ (E3.mParam Y : ℚ) →
          (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
            (E3.mParam Y : ℚ) := by
        rintro N rfl h
        rwa [Thm14_5.mParam_autSub_autQuot_bot, Thm14_5.rk_commV_autQuot_bot,
          Thm14_5.rk_map_mk_bot] at h
      exact key _ hfixH hineqQ
    obtain ⟨hle, hnorm, hirr, hrkI, hmul, hmN⟩ :=
      setup_of_case2 hW hL hX hfix hsum0 hI hIm
    have hs : IsSimpleGroup ↥L := UC22.uc22p22r_lieModel_isSimple_twistedB2 hSz
    have hSsz : IsSz ↥(autSub L I) n := lieModel_autSub hL hX hfix hsum0 hs hI hSz
    have hm2 : 2 * n ≤ E3.mParam (autSub Y I) :=
      hMod ↥I (fun u => Subtype.ext (by simpa using hW (u : W)))
        (autSub Y I) (autSub L I) n hle hnorm hSsz hirr
    have hι : 0 < rk ↥I := by
      rcases Nat.eq_zero_or_pos (rk ↥I) with h0 | h0
      · exact absurd ((rk_eq_zero_iff hW).mp h0) (ne_bot_of_mem_irrSet hI)
      · exact h0
    have h1 : 2 * n * rk ↥I ≤ (n + 2) * rk ↥I := by
      have h2 : 2 * n * rk ↥I ≤ 2 * n * rk ↥(commV L) := Nat.mul_le_mul_left _ hrkI
      have h3 : 2 * n * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
        Nat.mul_le_mul_right _ hm2
      have h5 : E3.mParam Y * rk ↥I ≤ (n + 2) * rk ↥I := Nat.mul_le_mul_right _ hmn
      exact h2.trans (h3.trans (hmul.trans h5))
    have := Nat.le_of_mul_le_mul_right h1 hι
    omega
  · exact hnL2 e' (Thm14_5.isL2_of_isSubnormal_isNaturalO4Plus hL.2.2 hLR hnatR)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
