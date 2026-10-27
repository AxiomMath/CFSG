module

public import CFSG.Quasithin.H13.A6S1372L76W
public import CFSG.Quasithin.H13.A6S1372L76P4
public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Quasithin.EmptyFaithful.T1515dF
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFG2
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Quasithin.H13.A6S1372L76M
public import CFSG.Quasithin.H13.A6S1372L76O

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique.Bridge
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

namespace A6L76X

theorem l34NotL42 : L34NotL42Fact1515e := by
  intro X _ h3 h4
  obtain ⟨-, K₄, _, _, hK₄, ⟨e₄⟩⟩ := h3
  obtain ⟨-, K₂, _, _, hK₂, ⟨e₂⟩⟩ := h4
  exact (CFSG.ComponentClassification.SymmetricLocal.projectiveSL_three_four_not_equiv
    (by rw [hK₄]; norm_num) (by rw [hK₂]; norm_num)).false
    ((((Id2519.projectiveSLEquivStatedProj 3 K₄).trans e₄.symm).trans e₂).trans
      (Id2519.projectiveSLEquivStatedProj 4 K₂).symm)

theorem slMap_injective {d : ℕ} {F : Type} [Field F] (e : ZMod 2 ≃+* F) :
    Function.Injective (A6L76O.slMap (d := d) e) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h1 := congrArg (fun x : ↥(StatedSL d F) =>
    ((x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j) h
  simp only [A6L76O.slMap_val, Matrix.map_apply] at h1
  exact e.injective h1

@[expose] noncomputable def slEquivZMod {d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : ↥(StatedSL d F) ≃* ↥(StatedSL d (ZMod 2)) :=
  (MulEquiv.ofBijective (A6L76O.slMap (A6L76O.eps hF).symm)
    ⟨slMap_injective _, A6L76O.slMap_surjective _⟩).symm

theorem isPSL_of_statedSL {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {X : Type} [Group X] (E : X ≃* ↥(StatedSL n F)) : IsPSL n 2 1 X :=
  R3c2.isPSL_two_of_statedSL hn (E.trans (slEquivZMod hF))

@[expose] noncomputable def alt8Equiv :
    ↥(alternatingGroup (Fin 8)) ≃* ↥(StatedSL 4 (ZMod 2)) :=
  (MulEquiv.ofBijective B5FinS8.alphaHom B5FinS8.alphaHom_bijective).trans B5FinS8.slEquiv.symm

theorem mulVec_pow_eq {n : ℕ} {F : Type} [Field F] {g : ↥(StatedSL n F)} {v : Fin n → F}
    (h : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v = v) (i : ℕ) :
    (((g ^ i : ↥(StatedSL n F)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v = v := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, A6L76M.val_mul, ← Matrix.mulVec_mulVec, h, ih]

theorem three_le_pRank_statedSL {n : ℕ} (hn : 6 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL n F)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : F) = 0 := A6L76M.two_eq_zero hF
  set p : Fin 6 → Fin n := fun i => ⟨i, by omega⟩ with hp
  have hne : ∀ i j : Fin 6, i ≠ j → p i ≠ p j := fun i j hij h =>
    hij (Fin.ext (by simpa [hp] using congrArg Fin.val h))
  obtain ⟨hxy, hx3, hy3, hx1, hy1, hyx, hyxx⟩ := A6L76M.e9_rot (F := F) h2 (hne 0 1 (by decide))
    (hne 2 3 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide))
    (hne 1 3 (by decide))
  obtain ⟨hxz, -, hz3, -, -, -, -⟩ := A6L76M.e9_rot (F := F) h2 (hne 0 1 (by decide))
    (hne 4 5 (by decide)) (hne 0 4 (by decide)) (hne 0 5 (by decide)) (hne 1 4 (by decide))
    (hne 1 5 (by decide))
  obtain ⟨hyz, -, -, -, -, -, -⟩ := A6L76M.e9_rot (F := F) h2 (hne 2 3 (by decide))
    (hne 4 5 (by decide)) (hne 2 4 (by decide)) (hne 2 5 (by decide)) (hne 3 4 (by decide))
    (hne 3 5 (by decide))
  set x := A6L76M.slOf (A6L76M.rot (p 0) (p 1) : Matrix (Fin n) (Fin n) F)
    (A6L76M.det_rot (hne 0 1 (by decide)))
  set y := A6L76M.slOf (A6L76M.rot (p 2) (p 3) : Matrix (Fin n) (Fin n) F)
    (A6L76M.det_rot (hne 2 3 (by decide)))
  set z := A6L76M.slOf (A6L76M.rot (p 4) (p 5) : Matrix (Fin n) (Fin n) F)
    (A6L76M.det_rot (hne 4 5 (by decide)))
  have hfix : ∀ {a b : Fin 6}, a ≠ b → a ≠ 4 → a ≠ 5 → b ≠ 4 → b ≠ 5 →
      (A6L76M.rot (p a) (p b) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single (p 4) 1) =
        Pi.single (p 4) 1 := by
    intro a b hab ha4 ha5 hb4 hb5
    rw [A6L76M.rot_mulVec h2 (hne a b hab)]
    exact A6L76M.rotF_single_of_ne (hne 4 a (Ne.symm ha4)) (hne 4 b (Ne.symm hb4))
  refine CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens hx3 hy3 hz3 hxy hxz hyz hx1
    (fun i h => ?_) (fun i j h => ?_)
  · have hx : x ^ i = x ^ (i % 3) := by
      conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hx3, one_pow, one_mul]
    have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rw [hx] at h
    interval_cases (i % 3)
    · exact hy1 (by simpa using h.symm)
    · exact hyx (by simpa using h.symm)
    · exact hyxx (by rw [← h, sq])
  · have h1 := congrArg (fun g : ↥(StatedSL n F) =>
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single (p 4) 1) (p 4)) h
    simp only [A6L76M.val_mul, ← Matrix.mulVec_mulVec] at h1
    rw [mulVec_pow_eq (g := y) (hfix (by decide) (by decide) (by decide) (by decide) (by decide)),
      mulVec_pow_eq (g := x) (hfix (by decide) (by decide) (by decide) (by decide) (by decide)),
      A6L76M.slOf_val, A6L76M.rot_mulVec h2 (hne 4 5 (by decide)), A6L76M.rotF_p,
      Pi.single_eq_same, Pi.single_eq_of_ne (hne 5 4 (by decide))] at h1
    exact one_ne_zero h1

theorem not_isPerfect_statedSp_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ¬ Group.IsPerfect ↥(StatedSp 2 F) := by
  intro hp
  have hperf : commutator ↥(StatedSp 2 F) = ⊤ := Group.isPerfect_def.1 hp
  have h1 : Nat.card ↥(commutator ↥(StatedSp 2 F)) = 360 := by
    rw [Nat.card_congr (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hF).toEquiv,
      R3c2.card_alternatingGroup_six]
  have h2 : Nat.card ↥(StatedSp 2 F) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  rw [hperf, Subgroup.card_top, h2] at h1
  omega

theorem not_isPerfect_g2_two
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ¬ Group.IsPerfect ↥(CFSG.Open.quasithinG2 F) := by
  intro hp
  have hperf : ⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ = CFSG.Open.quasithinG2 F :=
    Subgroup.isPerfect_iff.1 hp
  have h1 : Nat.card ↥(CFSG.Open.quasithinG2 F) = 12096 := by
    rw [card_quasithinG2_1527d (n := 1) (by simpa using hF), hF]
    norm_num
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ = 6048 := by
    rw [Nat.card_congr ((Insp9.g2DerivedEquivZMod2 F hF).trans
      (Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm).toEquiv]
    exact CFSG.Quasithin.G11.P3G2.card_commutatorG2
  rw [hperf, h1] at h2
  omega

theorem isSimpleGroup_g2
    {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    IsSimpleGroup ↥(CFSG.Open.quasithinG2 F) := by
  have hZ := CFSG.Quasithin.H13.Ch4.FFG2.center_quasithinG2_eq_bot hn hF
  obtain ⟨-, hs⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 n (factG2Cayley_holds F n hn hF)
  have := hs
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end A6L76X

theorem lem1376L1K_of
    (hS : Lem1376L1KSmall) (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) : Lem1376L1K := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK hHyp
  have hX : ∀ {X : Type} [Group X] [Finite X], ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) →
      A318Exclusion X → S.L1 ≤ K := fun E hE => S.L1_le_of_quotEquiv hF h36 h38 hH hK E hE
  have hR : ∀ {D : FFModel}, D.Faithful →
      ∀ {U Z : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))},
      D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) U Z →
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* D.Gam) :=
    fun {_} hD {_ _} hRe => S.exists_quotEquiv_of_realizes hNS h13315 h1356two hH hK hD hRe
  have hr2 : ∀ {X : Type} [Group X] [Finite X], ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) →
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 :=
    fun E => Setting4.pRank_le_two_of_quotEquiv hH.1.2 hK E S.h13.qtke
  have hsmall := hS G T L V S hNS hNU H hH hab K hK
  rcases hHyp with ⟨n, hn, hSL⟩ | hX5 | ⟨n, hA⟩ | hX4 | ⟨α, hA7⟩ | ⟨n, hSL3⟩ | ⟨n, hSp⟩ |
    ⟨n, hG2⟩
  ·
    obtain ⟨F, _, _, hF2, hRe⟩ := id hSL
    have hF2' : Nat.card F = 2 := by simpa using hF2
    obtain ⟨E⟩ := hR (FFModel.nat_faithful _) hRe
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | h6
    · exact hsmall (Or.inl ⟨1, hSL⟩)
    · exact hX (MulEquiv.refl _) (a318Exclusion_psl42 A6L76X.l34NotL42
        (A6L76X.isPSL_of_statedSL (by norm_num) hF2' E))
    · exact hX (MulEquiv.refl _)
        (a318Exclusion_psl52 (A6L76X.isPSL_of_statedSL (by norm_num) hF2' E))
    · have h1 := hr2 (X := ↥(StatedSL n F)) E
      have h2 := A6L76X.three_le_pRank_statedSL h6 hF2'
      omega
  ·
    obtain ⟨E⟩ := hR (FFC.extSq_faithful (d := 5) (by norm_num)) hX5
    exact hX (MulEquiv.refl _) (a318Exclusion_psl52 (R3c2.isPSL_two_of_statedSL (by norm_num) E))
  ·
    rcases (show n ≤ 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n by omega) with
      hn | rfl | rfl | rfl | rfl | h9
    · exfalso
      obtain ⟨π, hπ⟩ := hA
      obtain ⟨e₀⟩ := S.exists_quotEquiv_tilde hNS h13315 h1356two hH hK
      have := Setting4.nontrivial_of_quotEquiv hK e₀
      have hcard : Nat.card (Fin n) ≤ 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        exact hn
      have : Group.IsSolvable (FFModel.altDn n).Gam := alternatingGroup.isSolvable hcard
      have hsolv : Group.IsSolvable ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := Group.isSolvable_of_surjective hπ.1
      have := S.isPerfect_tilde hH hK
      exact Group.IsPerfect.not_isSolvable _ hsolv
    · exact hsmall (Or.inr hA)
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by norm_num)) hA
      exact hX (X := ↥(alternatingGroup (Fin 6))) E a318Exclusion_alt6
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by norm_num)) hA
      exact hX (X := ↥(alternatingGroup (Fin 7))) E a318Exclusion_alt7
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by norm_num)) hA
      exact hX (MulEquiv.refl _) (a318Exclusion_psl42 A6L76X.l34NotL42
        (R3c2.isPSL_two_of_statedSL (by norm_num) (E.trans A6L76X.alt8Equiv)))
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by omega)) hA
      have h1 := hr2 (X := ↥(alternatingGroup (Fin n))) E
      have h2 := A6L76E.three_le_pRank_alt h9
      omega
  ·
    obtain ⟨E⟩ := hR (FFC.extSq_faithful (d := 4) (by norm_num)) hX4
    exact hX (MulEquiv.refl _) (a318Exclusion_psl42 A6L76X.l34NotL42
      (R3c2.isPSL_two_of_statedSL (by norm_num) E))
  ·
    obtain ⟨E⟩ := hR (FFC.a7Four_faithful α) hA7
    exact hX (X := ↥(alternatingGroup (Fin 7))) E a318Exclusion_alt7
  ·
    exact hsmall (Or.inl ⟨n, hSL3⟩)
  ·
    obtain ⟨F, _, _, hFn, hRe⟩ := id hSp
    obtain ⟨E⟩ := hR (FFModel.nat_faithful _) hRe
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hFn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · exact (A6L76X.not_isPerfect_statedSp_two (by simpa using hFn)
        (Setting4.isPerfect_of_quotEquiv hK E)).elim
    · have h4 : 4 ≤ Nat.card F := by
        rw [hFn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hq := CFSG.LocalCores.isQuasisimple_of_mulEquiv E.symm
        (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr h4)))
      exact hX (MulEquiv.refl _) (R3c2.exclusion_sp4 factA318Excl_holds hFn E hq)
  ·
    obtain ⟨F, _, _, hFn, hRe⟩ := id hG2
    have : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hFn
    obtain ⟨E⟩ := hR (FFC.zornQ_faithful _ le_rfl) hRe
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hFn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · exact (A6L76X.not_isPerfect_g2_two (by simpa using hFn)
        (Setting4.isPerfect_of_quotEquiv hK E)).elim
    · have : IsSimpleGroup (FFModel.zornQ (CFSG.Open.quasithinG2 F)).Gam :=
        A6L76X.isSimpleGroup_g2 hn2 hFn
      have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := E.isSimpleGroup
      have hq := isQuasisimple_of_perfect_of_isSimple1521d
        (Setting4.isPerfect_of_quotEquiv hK (MulEquiv.refl _)) this
      exact hX (MulEquiv.refl _) (R3c2.exclusion_g2 factA318Excl_holds hFn E hq)

end CFSG.Quasithin.H13.A6
