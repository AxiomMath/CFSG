module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAll
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Structure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.CaseTwoBasics
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNNat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.NaturalTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOneCase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.Quasithin.Background.FFC4Res
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

variable {W : Type} [CommGroup W]

private theorem commSub_sup_le (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X ≤ commSub A X ⊔ commSub B X := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  have h1 : x a * a⁻¹ ∈ commSub A X := Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩
  have h2 : x b * b⁻¹ ∈ commSub B X := Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩
  have he : x (a * b) * (a * b)⁻¹ = x a * a⁻¹ * (x b * b⁻¹) := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  rw [SetLike.mem_coe, he]
  exact Subgroup.mul_mem_sup h1 h2

private theorem fixV_le_sup {S : Subgroup (MulAut W)} {I J : Subgroup W} (hIJ : I ⊓ J = ⊥)
    (htop : I ⊔ J = ⊤) (hSI : StableUnder S I) (hSJ : StableUnder S J) :
    fixV S ≤ (I ⊓ fixV S) ⊔ (J ⊓ fixV S) := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top w)
  have hfa : ∀ s ∈ S, s a = a := by
    intro s hs
    have h := hw s hs
    rw [map_mul] at h
    have hmem : s a * a⁻¹ ∈ I ⊓ J := by
      refine ⟨I.mul_mem (hSI s hs a ha) (I.inv_mem ha), ?_⟩
      have he : s a * a⁻¹ = b * (s b)⁻¹ := by
        have h' : s a = a * b * (s b)⁻¹ := by
          rw [← h]
          group
        rw [mul_inv_eq_iff_eq_mul, h']
        ac_rfl
      rw [he]
      exact J.mul_mem hb (J.inv_mem (hSJ s hs b hb))
    rw [hIJ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hfb : ∀ s ∈ S, s b = b := by
    intro s hs
    have h := hw s hs
    rw [map_mul, hfa s hs] at h
    exact mul_left_cancel h
  exact Subgroup.mul_mem_sup ⟨ha, hfa⟩ ⟨hb, hfb⟩

private theorem map_conj_eq_of_normal {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) {g : MulAut W} (hg : g ∈ Y) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  have hle : ∀ y ∈ Y, L.map (MulAut.conj y).toMonoidHom ≤ L := by
    intro y hy
    rintro _ ⟨l, hl, rfl⟩
    have := hLn.conj_mem ⟨l, hLY hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.mp this
  refine le_antisymm (hle g hg) fun l hl => ?_
  refine ⟨g⁻¹ * l * g, hle g⁻¹ (Y.inv_mem hg) ⟨l, hl, ?_⟩, ?_⟩
  · simp
  · simp [MulAut.conj_apply, mul_assoc]

theorem inf_normalizer_le_of_isParabolicTwo [Finite W] {L S P R : Subgroup (MulAut W)}
    (hS : IsSylowIn 2 S L) (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hSR : S ≤ R)
    (hR : R ≤ normalizer (P : Set (MulAut W))) :
    L ⊓ normalizer (S : Set (MulAut W)) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have h2 : IsPGroup 2 ↥(S.subgroupOf L) :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  have hSN : S.subgroupOf L ≤ normalizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := Subgroup.mem_normalizer_iff.mp (hR (hSR (Subgroup.mem_subgroupOf.mp hs))) z
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have hSP := IsParabolicTwo.le_of_le_normalizer hpar h2 hSN
  have hNle : normalizer (((hS.toSylow : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L) ≤ P.subgroupOf L :=
    IsParabolicTwo.normalizer_le hpar hS.toSylow (by rw [IsSylowIn.coe_toSylow]; exact hSP)
  rw [normalizer_toSylow_eq hS] at hNle
  rintro x ⟨hxL, hxN⟩
  exact Subgroup.mem_subgroupOf.mp
    (hNle (Subgroup.mem_subgroupOf.mpr hxN : (⟨x, hxL⟩ : ↥L) ∈ _))

theorem natParNAll_autSub (hNPA : KNatParNAll) [Finite W] {L S P : Subgroup (MulAut W)}
    {X : Subgroup W} {k n : ℕ} (hq : CFSG.Open.IsQuasisimple ↥L) (hX : X ∈ irrSet L)
    (hXfix : X ⊓ fixV L = ⊥) (hnat : IsNaturalClassicalModule (autSub L X) k) (hk : 2 ≤ k)
    (hS : IsSylowIn 2 S L) (hBP : L ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPL : P ≤ L)
    (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n)
    (hcomm : commSub (X ⊓ fixV S) (Hinf P) ≠ ⊥) :
    n = k ∨ (IsOmegaMinus ↥(autSub L X) 4 k ∧ n = 2 * k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hLX := le_stabSub_of_mem_irrSet hX
  have hne := not_le_centSub_of_mem_irrSet hX hXfix
  have hqX := B1Red.isQuasisimple_autSub hLX hq hne
  have hSX : S ≤ stabSub X := hS.le.trans hLX
  have hPX : P ≤ stabSub X := hPL.trans hLX
  have hHX : Hinf P ≤ stabSub X := (uc22p21c_Hinf_le P).trans hPX
  obtain ⟨-, hN'⟩ := hinf_autSub_ne_bot_and_nParam hq hLX hne hPL hinf hN
  have hperf : ⁅autSub L X, autSub L X⁆ = autSub L X := by
    have h := congrArg (Subgroup.map (autSub L X).subtype) hqX.1
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hmapS : (S.subgroupOf L).map (resTo hLX) = (autSub S X).subgroupOf (autSub L X) := by
    ext φ
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_autSub]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : MulAut W), hLX l.2⟩, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    · rintro ⟨g, hgS, hg⟩
      exact ⟨⟨g, hS.le hgS⟩, Subgroup.mem_subgroupOf.mpr hgS, Subtype.ext hg⟩
  have hS' : IsSylowIn 2 (autSub S X) (autSub L X) := by
    refine ⟨autSub_mono hS.le X, hS.isPGroup.of_surjective (resTo hSX) (resTo_surjective hSX),
      fun h2 => hS.not_dvd_relIndex ?_⟩
    have h := Subgroup.index_map_dvd (S.subgroupOf L) (resTo_surjective hLX)
    rw [hmapS] at h
    exact h2.trans h
  obtain ⟨hparL, -⟩ := isParabolicTwo_subgroupOf hS hBP
  have hparX := isParabolicTwo_autSub hLX hPL hparL
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hBP' : autSub L X ⊓ normalizer (autSub S X : Set (MulAut ↥X)) ≤ autSub P X := by
    have hle : (hS'.toSylow : Subgroup ↥(autSub L X)) ≤ (autSub P X).subgroupOf (autSub L X) := by
      rw [IsSylowIn.coe_toSylow]
      exact fun φ hφ => Subgroup.mem_subgroupOf.mpr (autSub_mono hSP X (Subgroup.mem_subgroupOf.mp hφ))
    have hNle : normalizer (((hS'.toSylow : Sylow 2 ↥(autSub L X)) : Subgroup ↥(autSub L X)) :
        Set ↥(autSub L X)) ≤ (autSub P X).subgroupOf (autSub L X) :=
      IsParabolicTwo.normalizer_le hparX hS'.toSylow hle
    rw [normalizer_toSylow_eq hS'] at hNle
    rintro φ ⟨hφL, hφN⟩
    exact Subgroup.mem_subgroupOf.mp
      (hNle (Subgroup.mem_subgroupOf.mpr hφN : (⟨φ, hφL⟩ : ↥(autSub L X)) ∈ _))
  have hcomm' : commSub (fixV (autSub S X)) (Hinf (autSub P X)) ≠ ⊥ := by
    rw [hinf_autSub hPX]
    intro hbot
    apply hcomm
    have h := map_commSub_autSub hHX (fixV (autSub S X))
    rw [hbot, Subgroup.map_bot, map_subtype_fixV_autSub hSX] at h
    exact h.symm
  exact hNPA ↥X (autSub L X) (autSub S X) (autSub P X) k n hnat hk hperf hS' hBP'
    (autSub_mono hPL X) hcomm' hN'

private theorem center_eq_bot_of_isSimpleGroup_of_isQuasisimple {G : Type*} [Group G]
    [IsSimpleGroup G] (hq : CFSG.Open.IsQuasisimple G) : Subgroup.center G = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hbot : commutator G = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def, hcomm a b, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    rw [hq.1] at hbot
    obtain ⟨x, y, hxy⟩ := exists_pair_ne G
    have hx : x ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)

theorem isL2_of_two [Finite W] {L : Subgroup (MulAut W)} {I J : Subgroup W} {g : MulAut W}
    {k : ℕ} (hk : 1 ≤ k) (hq : CFSG.Open.IsQuasisimple ↥L) (hI : I ∈ irrSet L)
    (hJ : J ∈ irrSet L) (hfix : fixV L = ⊥) (htop : I ⊔ J = ⊤)
    (hg : L.map (MulAut.conj g).toMonoidHom = L)
    (hsec : SecIsoOn L (I.map g.toMonoidHom) ⊥ J ⊥)
    (hΩ : IsOmegaMinus ↥(autSub L I) 4 k ∨ IsOmegaMinus ↥(autSub L J) 4 k) :
    IsL2 ↥L (2 * k) := by
  have hLI := le_stabSub_of_mem_irrSet hI
  have hLJ := le_stabSub_of_mem_irrSet hJ
  have hIfix : I ⊓ fixV L = ⊥ := by rw [hfix, inf_bot_eq]
  have hJfix : J ⊓ fixV L = ⊥ := by rw [hfix, inf_bot_eq]
  have hneI := not_le_centSub_of_mem_irrSet hI hIfix
  have hneJ := not_le_centSub_of_mem_irrSet hJ hJfix
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_autSub_eq_map hg hLI hLJ hsec
  let eIJ : ↥(autSub L I) ≃* ↥(autSub L J) :=
    ((autSub L I).equivMapOfInjective (H.congrHom ψ) (H.congrHom_injective ψ)).trans
      (MulEquiv.subgroupCongr hψ.symm)
  have hIl2 : IsL2 ↥(autSub L I) (2 * k) := by
    rcases hΩ with h | h
    · exact isL2_two_mul_of_isOmegaMinus_four hk h
    · exact LieModel.of_mulEquiv eIJ.symm (isL2_two_mul_of_isOmegaMinus_four hk h)
  have hJl2 : IsL2 ↥(autSub L J) (2 * k) := LieModel.of_mulEquiv eIJ hIl2
  have := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hJl2
  have hZJ : Subgroup.center ↥(autSub L J) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_isQuasisimple (B1Red.isQuasisimple_autSub hLJ hq hneJ)
  have hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1 := by
    intro l hl hlI
    have hkI : (⟨l, hl⟩ : ↥L) ∈ (resTo hLI).ker := by
      rw [MonoidHom.mem_ker, resTo_eq_one_iff]
      exact hlI
    have hcen := ker_resTo_le_center hq hLI hneI hkI
    have hcJ : resTo hLJ ⟨l, hl⟩ ∈ Subgroup.center ↥(autSub L J) := by
      rw [Subgroup.mem_center_iff]
      intro φ
      obtain ⟨m, rfl⟩ := resTo_surjective hLJ φ
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hcen m)]
    rw [hZJ, Subgroup.mem_bot, resTo_eq_one_iff] at hcJ
    refine MulEquiv.ext fun w => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top w)
    rw [map_mul, hlI a ha, hcJ b hb]
    rfl
  exact LieModel.of_mulEquiv (FFC.resEquiv hLI hinj).symm hIl2

theorem normal_case
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    (hNPA : KNatParNAll) [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T P : Subgroup (MulAut W)} {n : ℕ}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y) (hTY : T ≤ Y)
    (hT : IsSylowIn 2 T Y) (hncard : (conjSet L T).ncard ≤ 2) (hLn : (L.subgroupOf Y).Normal)
    (hPL : P ≤ L) (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥)
    (hnorm : normIn T L ≤ normalizer (P : Set (MulAut W)))
    (hcomm : commSub (fixV T) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) (hn : 2 < n)
    (hmin : ∀ Q : Subgroup (MulAut W), Q < P → IsParabolicTwo ↥L (Q.subgroupOf L) →
      normIn T L ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥)
    {K : Subgroup (MulAut W)} (hK : K = ⨆ t ∈ T, (Hinf P).map (MulAut.conj t).toMonoidHom)
    {W₀ : Subgroup W} (hW₀ : W₀ = ⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom)
    (hma : E3.mParam Y ≤ E3.aParam (autSub (K ⊔ T) W₀) + 1) (hmY : E3.mParam Y ≤ n + 1)
    (hsum : IsDirSumOver (conjSet L Y) commV) (hfixH : fixV (⨆ X ∈ conjSet L Y, X) = ⊥)
    {I : Subgroup W} (hI : I ∈ irrSet L) (hIfix : I ⊓ fixV L = ⊥)
    (hineq : E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I)
    (hsmall : (∃ k : ℕ, IsNaturalClassicalModule (autSub L I) k ∧ (n = k ∨ n = 2 * k)) ∨
      (IsL2 ↥(autSub L I) 3 ∧ n = 3 ∧ E3.mParam (autSub Y I) = 4 ∧
        E3.aParam (autSub Y I) ≤ 1)) :
    IsNaturalClassicalModule L n ∨
      (Even n ∧ IsOmegaMinus ↥L 4 (n / 2) ∧ NatOmegaMinus L ⊤ ⊥ 4 (n / 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : L ≤ Y := hL.1
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLI := le_stabSub_of_mem_irrSet hI
  have hnormI : ∀ y ∈ Y, y ∈ stabSub I → y ∈ normalizer (L : Set (MulAut W)) :=
    fun y hy hyI => mem_normalizer_of_mem_stabSub hsum hI hy hyI
  have hconj : ∀ X ∈ conjSet L Y, X = L := by
    rintro _ ⟨g, hg, rfl⟩
    exact map_conj_eq_of_normal hLY hLn hg
  have htop : commV L = ⊤ := by
    rw [eq_top_iff, ← hsum.2]
    exact iSup_le fun X => (congrArg commV (hconj X X.2)).le
  have hfix : fixV L = ⊥ := by
    rw [eq_bot_iff, ← hfixH]
    intro v hv x hx
    exact hv x (iSup₂_le (fun X hX => (hconj X hX).le) hx)
  have hrank : ∀ e', (IsL2 ↥L e' ∨ IsSz ↥L e' ∨ IsU3 ↥L e' ∨ IsSU3 ↥L e') →
      IsNaturalClassicalModule L n ∨
        (Even n ∧ IsOmegaMinus ↥L 4 (n / 2) ∧ NatOmegaMinus L ⊤ ⊥ 4 (n / 2)) := by
    intro e' hsh
    rcases rankOne_case hSz hW hO2 hirr hL hTY hT hncard hsh hPL hinf hnorm hN hn hK
      hW₀ hma hmY hsum hfixH hI hIfix hineq hsmall with ⟨h1, h2⟩ | h
    · rw [htop] at h2
      exact Or.inl (Or.inl ⟨h1, h2⟩)
    · rw [htop] at h
      exact Or.inr h
  have hS : IsSylowIn 2 (T ⊓ L) L := F6.isSylowIn_inf_of_isSubnormal hL.2.1 hT
  have hBP : L ⊓ normalizer ((T ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) ≤ P :=
    inf_normalizer_le_of_isParabolicTwo hS hpar
      (fun x hx => by rw [normIn]; exact ⟨hx.1, Subgroup.le_normalizer hx.2⟩) hnorm
  have hcommS : commSub (fixV (T ⊓ L)) (Hinf P) ≠ ⊥ := fun h =>
    hcomm (eq_bot_iff.mpr (h ▸ commSub_mono (fun v hv x hx => hv x hx.1) le_rfl))
  have hι : 0 < rk ↥I := by
    rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff hW]
    exact WeakClosure81.ne_bot_of_mem_irrSet hI
  have hIc : I ≤ commV L := htop ▸ le_top
  rcases hsmall with ⟨k, hnat, hnk⟩ | ⟨hL8, hn3, hm4, -⟩
  · have hk2 : 2 ≤ k := by omega
    have hkm : k ≤ E3.mParam (autSub Y I) :=
      le_mParam_autSub_of_natural hW hL hI hIfix hnormI hnat
    have hineq' : k * rk ↥(commV L) ≤ (n + 1) * rk ↥I :=
      (Nat.mul_le_mul_right _ hkm).trans (hineq.trans (Nat.mul_le_mul_right _ hmY))
    rcases commV_eq_or_exists_two hW hO2 hirr hL hfixH hsum hI with hIeq | ⟨J, hJ, hIJ, h2, h3⟩
    ·
      have hItop : I = ⊤ := hIeq.symm.trans htop
      rw [hItop] at hnat
      have hnatL := isNaturalClassicalModule_of_autSub_top hnat
      have hperf : ⁅L, L⁆ = L := by
        have h := congrArg (Subgroup.map L.subtype) hq.1
        rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at h
        exact h
      have hRS : normIn T L ≤ normalizer ((T ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) := by
        intro x hx
        rw [normIn, Subgroup.mem_inf] at hx
        obtain ⟨hxT, hxN⟩ := hx
        rw [Subgroup.mem_normalizer_iff]
        intro z
        rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hxN z]
        constructor
        · rintro ⟨hzT, hzL⟩
          exact ⟨T.mul_mem (T.mul_mem hxT hzT) (T.inv_mem hxT), hzL⟩
        · rintro ⟨hzT, hzL⟩
          refine ⟨?_, hzL⟩
          have := T.mul_mem (T.mul_mem (T.inv_mem hxT) hzT) hxT
          simpa [mul_assoc] using this
      have hmin' : ∀ Q : Subgroup (MulAut W), Q < P →
          L ⊓ normalizer ((T ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) ≤ Q →
          normIn T L ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥ :=
        fun Q hQP hBQ hRQ => hmin Q hQP (isParabolicTwo_subgroupOf hS hBQ).1 hRQ
      rcases eq_or_natOmegaMinus_of_parN hnatL hk2 hperf hS (by rw [normIn]; exact inf_le_right)
          hRS hBP hPL hnorm
          hcommS hmin' hN with hnk' | ⟨hΩ, hNat, hn2⟩
      · left
        rw [hnk']
        exact hnatL
      · right
        have hk' : n / 2 = k := by omega
        exact ⟨⟨k, by omega⟩, hk' ▸ hΩ, hk' ▸ hNat⟩
    ·
      have h4 : k * (2 * rk ↥I) ≤ (n + 1) * rk ↥I := (Nat.mul_le_mul_left k h2).trans hineq'
      have hn2 : n = 2 * k := by
        rcases hnk with h | h
        · exfalso
          have h5 : 2 * k * rk ↥I ≤ (k + 1) * rk ↥I := by
            calc 2 * k * rk ↥I = k * (2 * rk ↥I) := by ring
              _ ≤ (n + 1) * rk ↥I := h4
              _ = (k + 1) * rk ↥I := by rw [h]
          have := Nat.le_of_mul_le_mul_right h5 hι
          omega
        · exact h
      have hlt3 : rk ↥(commV L) < 3 * rk ↥I := by
        by_contra hge
        push Not at hge
        have h5 : 3 * k * rk ↥I ≤ (2 * k + 1) * rk ↥I := by
          calc 3 * k * rk ↥I = k * (3 * rk ↥I) := by ring
            _ ≤ k * rk ↥(commV L) := Nat.mul_le_mul_left k hge
            _ ≤ (n + 1) * rk ↥I := hineq'
            _ = (2 * k + 1) * rk ↥I := by rw [hn2]
        have := Nat.le_of_mul_le_mul_right h5 hι
        omega
      have hIJt : I ⊔ J = ⊤ := (h3 hlt3).symm.trans htop
      obtain ⟨g, hgY, hsec⟩ := exists_secIsoOn_of_mem_irrSet hW hO2 hirr hL hfixH hsum hI hJ
      have hg : L.map (MulAut.conj g).toMonoidHom = L := map_conj_eq_of_normal hLY hLn hgY
      have hLJ := le_stabSub_of_mem_irrSet hJ
      have hJfix : J ⊓ fixV L = ⊥ := by rw [hfix, inf_bot_eq]
      have hnatJ := isNaturalClassicalModule_autSub_of_secIsoOn hg hLI hLJ hsec hnat
      have hSI : StableUnder (T ⊓ L) I := fun x hx => hI.2.2.1 x hx.2
      have hSJ : StableUnder (T ⊓ L) J := fun x hx => hJ.2.2.1 x hx.2
      have hsplit : commSub (I ⊓ fixV (T ⊓ L)) (Hinf P) ≠ ⊥ ∨
          commSub (J ⊓ fixV (T ⊓ L)) (Hinf P) ≠ ⊥ := by
        by_contra hboth
        push Not at hboth
        apply hcommS
        rw [eq_bot_iff]
        calc commSub (fixV (T ⊓ L)) (Hinf P)
            ≤ commSub ((I ⊓ fixV (T ⊓ L)) ⊔ (J ⊓ fixV (T ⊓ L))) (Hinf P) :=
              commSub_mono (fixV_le_sup hIJ hIJt hSI hSJ) le_rfl
          _ ≤ commSub (I ⊓ fixV (T ⊓ L)) (Hinf P) ⊔ commSub (J ⊓ fixV (T ⊓ L)) (Hinf P) :=
              commSub_sup_le _ _ _
          _ = ⊥ := by rw [hboth.1, hboth.2, sup_bot_eq]
      have hΩ : IsOmegaMinus ↥(autSub L I) 4 k ∨ IsOmegaMinus ↥(autSub L J) 4 k := by
        rcases hsplit with h | h
        · rcases natParNAll_autSub hNPA hq hI hIfix hnat hk2 hS hBP hPL hinf hN h with
            h' | ⟨h', -⟩
          · omega
          · exact Or.inl h'
        · rcases natParNAll_autSub hNPA hq hJ hJfix hnatJ hk2 hS hBP hPL hinf hN h with
            h' | ⟨h', -⟩
          · omega
          · exact Or.inr h'
      exact hrank (2 * k) (Or.inl (isL2_of_two (by omega) hq hI hJ hfix hIJt hg hsec hΩ))
  ·
    have hle : rk ↥(commV L) ≤ rk ↥I := by
      have h1 := hineq.trans (Nat.mul_le_mul_right (rk ↥I) (hmY.trans (by omega : n + 1 ≤ 4)))
      rw [hm4] at h1
      omega
    have hItop : I = ⊤ := (eq_of_le_of_rk_le hW hIc hle).trans htop
    rw [hItop] at hL8
    have hLtop : L ≤ stabSub (⊤ : Subgroup W) :=
      fun _ _ _ => ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩
    have hinj : ∀ l ∈ L, (∀ u ∈ (⊤ : Subgroup W), l u = u) → l = 1 :=
      fun _ _ hl => MulEquiv.ext fun u => hl u (Subgroup.mem_top u)
    exact hrank 3 (Or.inl (LieModel.of_mulEquiv (FFC.resEquiv hLtop hinj).symm hL8))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
