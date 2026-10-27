module

public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs
public import Certificates.Certificate13723
public import Certificates.Certificate13724
import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite
import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
import CFSG.RankThree.PartOne.KE.CTLang
import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsA
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.RankThree.Chevalley.G2CyclotomicTori

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.StandardType.LieCore (isExcTag nontoralMinRank IsSteinbergEndZ ratPoints)
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf)


private noncomputable abbrev excPayQ_Tp (p : ℕ) : Subgroup (ModGL Tag.E7 GGL) :=
  Subgroup.closure {z | ∃ a : Fin Tag.E7.rank → GGLˣ,
    (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E7 a = z}

private theorem excPayQ_pow_eq_inv_of_dvd_add_one {G : Type*} [Group G] {p m : ℕ} {x : G}
    (hx : x ^ p = 1) (h : p ∣ m + 1) : x ^ m = x⁻¹ := by
  obtain ⟨k, hk⟩ := h
  have h1 : x ^ (m + 1) = 1 := by rw [hk, pow_mul, hx, one_pow]
  rw [pow_add, pow_one] at h1
  exact mul_eq_one_iff_eq_inv.mp h1

private theorem excPayQ_weylAct_inv {τ : Tag} {K : Type} [Field K] (w : WeylGroup τ)
    (a : Fin τ.rank → Kˣ) : weylAct w a⁻¹ = (weylAct w a)⁻¹ := by
  apply eq_of_rootChar_eq
  intro v
  rw [rootChar_weylAct]
  rw [show rootChar ((weylAct w a)⁻¹) v = (rootChar (weylAct w a) v)⁻¹ by
    simp [rootChar, Finset.prod_inv_distrib, inv_zpow]]
  rw [rootChar_weylAct]
  simp [rootChar, Finset.prod_inv_distrib, inv_zpow]

private noncomputable abbrev excPayQ_muP (p : ℕ) : Subgroup (Fin Tag.E7.rank → GGLˣ) :=
  Subgroup.pi Set.univ fun _ => rootsOfUnity p GGL

private def excPayQ_muP_equiv (p : ℕ) :
    ↥(excPayQ_muP p) ≃ (∀ i : Fin Tag.E7.rank, rootsOfUnity p GGL) where
  toFun a i :=
    ⟨a.1 i, (Subgroup.mem_pi Set.univ).1 a.2 i (Set.mem_univ i)⟩
  invFun f := ⟨fun i => (f i : GGLˣ), by
    show (fun i => (f i : GGLˣ)) ∈ Subgroup.pi Set.univ
      (fun _ : Fin Tag.E7.rank => rootsOfUnity p GGL)
    rw [Subgroup.mem_pi]
    intro i _
    exact (f i).2⟩
  left_inv a := by ext i; rfl
  right_inv f := by ext i; rfl

private theorem excPayQ_card_rootsOfUnity {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (rootsOfUnity p GGL) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact IsPrimitiveRoot.card_rootsOfUnity'
    (IsPrimitiveRoot.iff_orderOf.2 (ggZeta_order p hp hp2))

private theorem excPayQ_card_muP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (excPayQ_muP p) = p ^ Tag.E7.rank := by
  have hroot : Nat.card (rootsOfUnity p GGL) = p := excPayQ_card_rootsOfUnity hp hp2
  calc Nat.card (excPayQ_muP p)
      = Nat.card (∀ i : Fin Tag.E7.rank, rootsOfUnity p GGL) :=
        Nat.card_congr (excPayQ_muP_equiv p)
    _ = ∏ i : Fin Tag.E7.rank, Nat.card (rootsOfUnity p GGL) := Nat.card_pi
    _ = p ^ Tag.E7.rank := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact congrArg (· ^ Tag.E7.rank) hroot

private theorem excPayQ_Tp_eq_map_muP (p : ℕ) :
    excPayQ_Tp p = (excPayQ_muP p).map (rootDiagUnitHom Tag.E7 GGL) := by
  have hset : {z : ModGL Tag.E7 GGL | ∃ a : Fin Tag.E7.rank → GGLˣ,
        (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E7 a = z}
      = ⇑(rootDiagUnitHom Tag.E7 GGL) ''
        {a : Fin Tag.E7.rank → GGLˣ | ∀ i, a i ^ p = 1} := by
    ext z
    exact ⟨fun h => by obtain ⟨a, ha, rfl⟩ := h; exact ⟨a, ha, rfl⟩,
      fun h => by obtain ⟨a, ha, rfl⟩ := h; exact ⟨a, ha, rfl⟩⟩
  rw [excPayQ_Tp, excPayQ_muP, hset, ← MonoidHom.map_closure]
  have hpi : Subgroup.pi Set.univ (fun _ : Fin Tag.E7.rank => rootsOfUnity p GGL)
      = Subgroup.closure {a : Fin Tag.E7.rank → GGLˣ | ∀ i, a i ^ p = 1} := by
    apply le_antisymm
    · intro a ha
      refine Subgroup.subset_closure fun i => ?_
      have h := (Subgroup.mem_pi Set.univ).1 ha i (Set.mem_univ i)
      exact (mem_rootsOfUnity p (a i)).1 h
    · rw [Subgroup.closure_le]
      intro a ha
      change a ∈ Subgroup.pi Set.univ
        (fun _ : Fin Tag.E7.rank => rootsOfUnity p GGL)
      rw [Subgroup.mem_pi]
      intro i _
      exact (mem_rootsOfUnity p (a i)).2 (ha i)
  rw [hpi]

private theorem excPayQ_card_Tp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (excPayQ_Tp p) = p ^ 7 := by
  rw [excPayQ_Tp_eq_map_muP]
  rw [Subgroup.card_map_of_injective (f := rootDiagUnitHom Tag.E7 GGL)
    (fun a b h => rootDiagUnit_injective
      (show rootDiagUnit Tag.E7 a = rootDiagUnit Tag.E7 b from h))]
  rw [excPayQ_card_muP hp hp2, show Tag.E7.rank = 7 from rfl]

private theorem excPayQ_coord_mod {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup Tag.E7}
    (h : ∀ a : Fin Tag.E7.rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w a = a⁻¹) :
    ∀ k j : Fin Tag.E7.rank,
      (p : ℤ) ∣ (w • (Pi.single k (1 : ℤ) : Fin Tag.E7.rank → ℤ)) j -
        (-1) * (Pi.single k (1 : ℤ) : Fin Tag.E7.rank → ℤ) j := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let ζ : GGLˣ := ggZeta p hp hp2
  have hζo : orderOf ζ = p := ggZeta_order p hp hp2
  have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  intro k j
  let e : Fin Tag.E7.rank → ℤ := Pi.single k 1
  change (p : ℤ) ∣ (w • e) j - (-1) * e j
  let a : Fin Tag.E7.rank → GGLˣ := Pi.mulSingle j ζ
  have ha : ∀ i, a i ^ p = 1 := by
    intro i
    dsimp [a]
    by_cases hij : i = j
    · subst hij; rw [Pi.mulSingle_eq_same, hζp]
    · rw [Pi.mulSingle_eq_of_ne hij, one_pow]
  have h1 : rootChar a e = rootChar a⁻¹ (w • e) := by
    have h2 : rootChar a (w⁻¹ • (w • e)) = rootChar a⁻¹ (w • e) := by
      rw [← rootChar_weylAct, h a ha]
    rwa [inv_smul_smul] at h2
  have hleft : rootChar a e = ζ ^ (e j) := by
    dsimp [a, e]
    rw [CFSG.LieType.Chevalley.RootTorus.rootChar_mulSingle]
  have hright : rootChar a⁻¹ (w • e) = ζ ^ (-((w • e) j)) := by
    have hainv : a⁻¹ = Pi.mulSingle j ζ⁻¹ := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [a]
      · simp [a, Pi.mulSingle_eq_of_ne hij]
    rw [hainv, CFSG.LieType.Chevalley.RootTorus.rootChar_mulSingle, inv_zpow']
  have hz : ζ ^ (e j) = ζ ^ (-((w • e) j)) := by
    rw [← hleft, h1, hright]
  have hmod' : (e j) ≡ -((w • e) j) [ZMOD orderOf ζ] :=
    (zpow_eq_zpow_iff_modEq (x := ζ)).mp hz
  rw [hζo] at hmod'
  have h2 : (p : ℤ) ∣ -((w • e) j) - e j := Int.modEq_iff_dvd.mp hmod'
  have h3 : (p : ℤ) ∣ (w • e) j + e j := by
    have h4 : (p : ℤ) ∣ -((w • e) j + e j) := by
      have h5 : -((w • e) j + e j) = -((w • e) j) - e j := by ring
      rw [h5]
      exact h2
    exact dvd_neg.mp h4
  simpa [e] using h3

private theorem excPayQ_smul_neg_of_weylAct_inv {p f : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup Tag.E7}
    (h : ∀ a : Fin Tag.E7.rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w a = a⁻¹) :
    ∀ u : Fin Tag.E7.rank → ℤ, w • u = -u := by
  have hmod := excPayQ_coord_mod hp hp2 hplus h
  have hbasis : ∀ k : Fin Tag.E7.rank,
      w • (Pi.single k (1 : ℤ) : Fin Tag.E7.rank → ℤ) =
        -(Pi.single k (1 : ℤ) : Fin Tag.E7.rank → ℤ) := by
    intro k
    have hroot := ggKGExc_root_eq_of_modEq (τ := Tag.E7)
      (Or.inr (Or.inl rfl)) hp (by omega)
      (IsRoot.smul (isRoot_single Tag.E7 k) w)
      (isRoot_single Tag.E7 k) (c := -1) (hmod k)
    rcases hroot with h | h
    · exfalso
      have h2 := hmod k k
      rw [h] at h2
      simp at h2
      norm_num at h2
      have hdiv : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
      have := Nat.le_of_dvd (by norm_num) hdiv
      omega
    · exact h
  intro u
  rw [smul_eq_sum_single w u]
  simp only [hbasis, smul_neg]
  rw [Finset.sum_neg_distrib]
  exact congrArg Neg.neg (eq_sum_single u).symm

private theorem excPayQ_weylAct_inv_of_mem_torus {p f : ℕ} (hp : p.Prime)
    (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup Tag.E7}
    {A' : Subgroup (ModGL Tag.E7 GGL)}
    (hT : A' ≤ twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) GGL w)
      (ggPhi .E7 f))
    (hA'eq : A' = excPayQ_Tp p) :
    ∀ a : Fin Tag.E7.rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w a = a⁻¹ := by
  intro a ha
  have hd : rootDiagUnit Tag.E7 a ∈ A' := by
    rw [hA'eq]
    exact Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hfix := (mem_twistedTorusOf.1 (hT hd)).2
  have hΦ : ggPhi .E7 f (rootDiagUnit Tag.E7 a) =
      rootDiagUnit Tag.E7 (a ^ 2 ^ f) := by
    change Units.map (entrywiseHom (ggFrobT f)) (rootDiagUnit Tag.E7 a) = _
    exact CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit
      (ggFrobT f) (ggFrobT_apply f) a
  have hpoweq : a ^ 2 ^ f = a⁻¹ := by
    funext i
    exact excPayQ_pow_eq_inv_of_dvd_add_one (ha i) hplus
  have h1 : rootDiagUnit Tag.E7 (weylAct w (a ^ 2 ^ f)) =
      rootDiagUnit Tag.E7 a := by
    rw [← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
      w (a ^ 2 ^ f), ← hΦ]
    exact hfix
  have h2 : weylAct w (a ^ 2 ^ f) = a := rootDiagUnit_injective h1
  rw [hpoweq] at h2
  rw [excPayQ_weylAct_inv w a] at h2
  simpa using congrArg (fun x => x⁻¹) h2

private theorem excPayQ_ggGraphLat_E7 (u : Fin (langTag .E7).rank → ℤ) :
    ggGraphLat .E7 u = u := rfl

private theorem excPayQ_weylLaw_of_smul_neg {p f : ℕ} {ht : GGExcFive .E7}
    {w : WeylGroup (langTag .E7)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) (h : ∀ u : Fin (langTag .E7).rank → ℤ, w • u = -u) :
    GGWeylLaw .E7 p f ht w := by
  have heps : eps p f = -1 :=
    (eps_eq_neg_one_iff hp hp2 f (Or.inr hplus)).2 hplus
  intro u
  rw [excPayQ_ggGraphLat_E7 u]
  have hperm : permLattice ((finCongr (rank_eq_langTag f ht)).permCongr
      (1 : Equiv.Perm (Fin ((ggU (absTag .E7) 6 f).D.rank)))) u = u := by
    change permLattice
      (Equiv.permCongr (finCongr (rank_eq_langTag f ht)) (Equiv.refl _)) u = u
    rw [Equiv.permCongr_refl]
    rfl
  change w • u = eps p f • permLattice
    ((finCongr (rank_eq_langTag f ht)).permCongr (piB .E7 p f)) u
  rw [piB_E7, hperm, h u, heps, neg_one_smul]

private theorem excPayQ_eq_Tp_of_torus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (ModGL Tag.E7 GGL)} (hAel : IsElemAbelian p A)
    (hcard : p ^ 7 ≤ Nat.card A) {w : WeylGroup Tag.E7} {g : ModGL Tag.E7 GGL}
    (hT : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) GGL w) (ggPhi .E7 f)) :
    A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ_Tp p := by
  let A' : Subgroup (ModGL Tag.E7 GGL) := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'card : p ^ 7 ≤ Nat.card A' := by
    rw [show A' = A.map (MulAut.conj g⁻¹).toMonoidHom from rfl]
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective]
    exact hcard
  have hAle : A' ≤ excPayQ_Tp p := by
    intro x hx
    have hxT := hT hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      (mem_twistedTorusOf.1 hxT).1
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hxp : (rootDiagUnit Tag.E7 a) ^ p = 1 := by
      rw [← hxy, ← map_pow, hAel.2 y hy, map_one]
    have ha1 : a ^ p = 1 := by
      apply rootDiagUnit_injective
      rw [← rootDiagUnit_pow, hxp, rootDiagUnit_one]
    exact Subgroup.subset_closure
      ⟨a, fun i => by simpa using congrFun ha1 i, rfl⟩
  have hA'eq : A' = excPayQ_Tp p := by
    haveI : Finite (excPayQ_Tp p) :=
      Nat.finite_of_card_ne_zero (by
        rw [excPayQ_card_Tp hp hp2]
        exact pow_ne_zero 7 hp.ne_zero)
    refine Subgroup.eq_of_le_of_card_ge hAle ?_
    rw [excPayQ_card_Tp hp hp2]
    exact hA'card
  exact hA'eq

private theorem excPayQ_phi_ratFinite {f : ℕ} (ht : GGExcFive .E7) (hf : 1 ≤ f) :
    IsSteinbergEndZ (langTag .E7) GGL (2 ^ f) (ggPhi .E7 f) ∧
      Finite ↥(ratPoints (ggPhi .E7 f)) := by
  have hΦ : IsSteinbergEnd (langTag .E7) GGL (2 ^ f) (ggPhi .E7 f) :=
    CFSG.StandardType.LieCore.isSteinbergEnd_ggPhi ht f
  have hΦZ : IsSteinbergEndZ (langTag .E7) GGL (2 ^ f) (ggPhi .E7 f) :=
    CFSG.StandardType.LieCore.isSteinbergEndZ_of_isSteinbergEnd hΦ
  exact ⟨hΦZ, CFSG.StandardType.LieCore.finite_ratPoints (q := 2 ^ f)
    (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2)) hΦZ⟩

private theorem excPayQ_toral_of_card {p f : ℕ} {ht : GGExcFive .E7}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (A : Subgroup (ModGL Tag.E7 GGL)) (hA : A ≤ ggFixGp .E7 f)
    (hAel : IsElemAbelian p A) (hcard : Nat.card A = p ^ 7) :
    IsToralSubgroup .E7 GGL A := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hΦZ, hfin⟩ := excPayQ_phi_ratFinite ht hf
  have hArat : A ≤ ratPoints (ggPhi .E7 f) := hA
  have halg : (letI := ZMod.algebra GGL 2; Algebra.IsAlgebraic (ZMod 2) GGL) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite
      (ZMod 2) 2
  refine CFSG.StandardType.LieCore.ggLieToralPosition_holds .E7 (isExcTag .E7) GGL
    halg f hf (ggPhi .E7 f) hΦZ hfin p hp hp2 A hArat hAel ?_
  rw [hcard]
  have hnt : 7 < nontoralMinRank .E7 p := by
    simp [nontoralMinRank, hp3]
  exact (Nat.pow_lt_pow_iff_right hp.one_lt).2 hnt

private theorem excPayQ_langPosition_of_toral {p f : ℕ} {ht : GGExcFive .E7}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (A : Subgroup (ModGL Tag.E7 GGL)) (hA : A ≤ ggFixGp .E7 f)
    (hAel : IsElemAbelian p A) (hcard : p ^ 7 ≤ Nat.card A)
    (htor : IsToralSubgroup .E7 GGL A) :
    ∃ (w : WeylGroup Tag.E7) (g : ModGL Tag.E7 GGL),
      g ∈ adjointGroup .E7 GGL ∧
      ggPhi .E7 f g = g * canonicalRep (coxeterSystem Tag.E7) GGL w ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom ≤
        twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) GGL w) (ggPhi .E7 f) ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ_Tp p := by
  obtain ⟨hΦZ, hfin⟩ := excPayQ_phi_ratFinite ht hf
  have hArat : A ≤ ratPoints (ggPhi .E7 f) := hA
  obtain ⟨w, g, hg, hlang, hT⟩ :=
    CFSG.StandardType.LieCore.ggLieLangPosition_holds .E7 (isExcTag .E7) GGL f hf
      (ggPhi .E7 f) hΦZ hfin p hp hp2 A hArat hAel htor
  refine ⟨w, g, hg, hlang, hT, ?_⟩
  exact excPayQ_eq_Tp_of_torus hp hp2 hAel hcard hT

private theorem excPayQ_weylLaw_of_position {p f : ℕ} {ht : GGExcFive .E7}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    {A : Subgroup (ModGL Tag.E7 GGL)} {w : WeylGroup Tag.E7} {g : ModGL Tag.E7 GGL}
    (hT : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) GGL w) (ggPhi .E7 f))
    (hA'eq : A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ_Tp p) :
    GGWeylLaw .E7 p f ht w := by
  have hweyl : ∀ a : Fin Tag.E7.rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w a = a⁻¹ :=
    excPayQ_weylAct_inv_of_mem_torus hp hplus hT hA'eq
  have hneg : ∀ u : Fin Tag.E7.rank → ℤ, w • u = -u :=
    excPayQ_smul_neg_of_weylAct_inv hp hp3 hp2 hplus hweyl
  let wL : WeylGroup (langTag .E7) := w
  have hnegL : ∀ u : Fin (langTag .E7).rank → ℤ, wL • u = -u := by
    intro u
    exact hneg u
  exact excPayQ_weylLaw_of_smul_neg hp hp2 hplus hnegL

theorem exists_datumModel_E7_of_toral {p f : ℕ} {ht : GGExcFive .E7} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1)
    (A : Subgroup (ModGL (langTag .E7) GGL)) (hA : A ≤ ggFixGp .E7 f)
    (hAel : IsElemAbelian p A) (hcard : p ^ 7 ≤ Nat.card A)
    (htor : IsToralSubgroup .E7 GGL A) :
    ∃ M : GGDatumModel .E7 f p ht,
      A.map (MulAut.conj M.D.g0⁻¹).toMonoidHom =
        Subgroup.closure {z | ∃ a : Fin (langTag .E7).rank → GGLˣ,
          (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .E7) a = z} := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨w, g, hg, hlang, hT, hA'eq⟩ :=
    excPayQ_langPosition_of_toral (ht := ht) hp hp2 hf A hA hAel hcard htor
  have hw : GGWeylLaw .E7 p f ht w :=
    excPayQ_weylLaw_of_position hp hp3 hp2 hplus hT hA'eq
  have hΦ : IsSteinbergEnd (langTag .E7) GGL (2 ^ f) (ggPhi .E7 f) :=
    CFSG.StandardType.LieCore.isSteinbergEnd_ggPhi ht f
  let D : LangDatum (langTag .E7) GGL :=
    CFSG.StandardType.LieCore.langDatumOfPosition hΦ w g hg hlang
  refine ⟨⟨w, hw, D, rfl, rfl, rfl⟩, ?_⟩
  show A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ_Tp p
  exact hA'eq

theorem exists_datumModel_E7_of_card {p f : ℕ} {ht : GGExcFive .E7} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1)
    (A : Subgroup (ModGL (langTag .E7) GGL)) (hA : A ≤ ggFixGp .E7 f)
    (hAel : IsElemAbelian p A) (hcard : Nat.card A = p ^ 7) :
    ∃ M : GGDatumModel .E7 f p ht,
      A.map (MulAut.conj M.D.g0⁻¹).toMonoidHom =
        Subgroup.closure {z | ∃ a : Fin (langTag .E7).rank → GGLˣ,
          (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .E7) a = z} :=
  exists_datumModel_E7_of_toral hp (by omega) hf hplus A hA hAel hcard.ge
    (excPayQ_toral_of_card (ht := ht) hp hp5 hf A hA hAel hcard)

end CFSG.StandardType.ExcPay
