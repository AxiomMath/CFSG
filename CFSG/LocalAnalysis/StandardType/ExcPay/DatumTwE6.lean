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
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusActPow
import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.TwistMap

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.StandardType.LieCore (isExcTag nontoralMinRank IsSteinbergEndZ ratPoints)
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf)

private noncomputable abbrev excPayQ6_Tp (p : ℕ) : Subgroup (ModGL (langTag .twistedE6) GGL) :=
  Subgroup.closure {z | ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
    (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z}

private theorem excPayQ6_pow_eq_inv_of_dvd_add_one {G : Type*} [Group G] {p m : ℕ} {x : G}
    (hx : x ^ p = 1) (h : p ∣ m + 1) : x ^ m = x⁻¹ := by
  obtain ⟨k, hk⟩ := h
  have h1 : x ^ (m + 1) = 1 := by rw [hk, pow_mul, hx, one_pow]
  rw [pow_add, pow_one] at h1
  exact mul_eq_one_iff_eq_inv.mp h1

private theorem excPayQ6_frobT_unit_eq_inv {p f : ℕ} {x : GGLˣ} (hx : x ^ p = 1)
    (hplus : p ∣ 2 ^ f + 1) :
    Units.map (ggFrobT f).toMonoidHom x = x⁻¹ := by
  have h1 : Units.map (ggFrobT f).toMonoidHom x = x ^ 2 ^ f := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact ggFrobT_apply f (x : GGL)
  rw [h1]
  exact excPayQ6_pow_eq_inv_of_dvd_add_one hx hplus

private noncomputable abbrev excPayQ6_muP (τ : Tag) (p : ℕ) :
    Subgroup (Fin τ.rank → GGLˣ) :=
  Subgroup.pi Set.univ fun _ => rootsOfUnity p GGL

private def excPayQ6_muP_equiv (τ : Tag) (p : ℕ) :
    ↥(excPayQ6_muP τ p) ≃ (∀ i : Fin τ.rank, rootsOfUnity p GGL) where
  toFun a i :=
    ⟨a.1 i, (Subgroup.mem_pi Set.univ).1 a.2 i (Set.mem_univ i)⟩
  invFun f := ⟨fun i => (f i : GGLˣ), by
    show (fun i => (f i : GGLˣ)) ∈ Subgroup.pi Set.univ
      (fun _ : Fin τ.rank => rootsOfUnity p GGL)
    rw [Subgroup.mem_pi]
    intro i _
    exact (f i).2⟩
  left_inv a := by ext i; rfl
  right_inv f := by ext i; rfl

private theorem excPayQ6_card_rootsOfUnity {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (rootsOfUnity p GGL) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact IsPrimitiveRoot.card_rootsOfUnity'
    (IsPrimitiveRoot.iff_orderOf.2 (ggZeta_order p hp hp2))

private theorem excPayQ6_card_muP (τ : Tag) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (excPayQ6_muP τ p) = p ^ τ.rank := by
  have hroot : Nat.card (rootsOfUnity p GGL) = p := excPayQ6_card_rootsOfUnity hp hp2
  calc Nat.card (excPayQ6_muP τ p)
      = Nat.card (∀ i : Fin τ.rank, rootsOfUnity p GGL) :=
        Nat.card_congr (excPayQ6_muP_equiv τ p)
    _ = ∏ i : Fin τ.rank, Nat.card (rootsOfUnity p GGL) := Nat.card_pi
    _ = p ^ τ.rank := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact congrArg (· ^ τ.rank) hroot

private theorem excPayQ6_Tp_eq_map_muP (p : ℕ) :
    excPayQ6_Tp p =
      (excPayQ6_muP (langTag .twistedE6) p).map
        (rootDiagUnitHom (langTag .twistedE6) GGL) := by
  have hset : {z : ModGL (langTag .twistedE6) GGL |
        ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
          (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z}
      = ⇑(rootDiagUnitHom (langTag .twistedE6) GGL) ''
        {a : Fin (langTag .twistedE6).rank → GGLˣ | ∀ i, a i ^ p = 1} := by
    ext z
    exact ⟨fun h => by obtain ⟨a, ha, rfl⟩ := h; exact ⟨a, ha, rfl⟩,
      fun h => by obtain ⟨a, ha, rfl⟩ := h; exact ⟨a, ha, rfl⟩⟩
  rw [excPayQ6_Tp, excPayQ6_muP, hset, ← MonoidHom.map_closure]
  have hpi : Subgroup.pi Set.univ
        (fun _ : Fin (langTag .twistedE6).rank => rootsOfUnity p GGL)
      = Subgroup.closure {a : Fin (langTag .twistedE6).rank → GGLˣ | ∀ i, a i ^ p = 1} := by
    apply le_antisymm
    · intro a ha
      refine Subgroup.subset_closure fun i => ?_
      have h := (Subgroup.mem_pi Set.univ).1 ha i (Set.mem_univ i)
      exact (mem_rootsOfUnity p (a i)).1 h
    · rw [Subgroup.closure_le]
      intro a ha
      change a ∈ Subgroup.pi Set.univ
        (fun _ : Fin (langTag .twistedE6).rank => rootsOfUnity p GGL)
      rw [Subgroup.mem_pi]
      intro i _
      exact (mem_rootsOfUnity p (a i)).2 (ha i)
  rw [hpi]

private theorem excPayQ6_card_Tp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (excPayQ6_Tp p) = p ^ 6 := by
  rw [excPayQ6_Tp_eq_map_muP]
  rw [Subgroup.card_map_of_injective (f := rootDiagUnitHom (langTag .twistedE6) GGL)
    (fun a b h => rootDiagUnit_injective
      (show rootDiagUnit (langTag .twistedE6) a =
        rootDiagUnit (langTag .twistedE6) b from h))]
  rw [excPayQ6_card_muP (langTag .twistedE6) hp hp2,
    show (langTag .twistedE6).rank = 6 from rfl]

private theorem excPayQ6_weylAct_inv_of_mem_torus {p f : ℕ} (hp : p.Prime)
    (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup (langTag .twistedE6)}
    {A' : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hT : A' ≤ twistedTorusOf (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
      (ggPhi .twistedE6 f))
    (hA'eq : A' = excPayQ6_Tp p) :
    ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = a := by
  intro a ha
  let ρ : Equiv.Perm (Fin (langTag .twistedE6).rank) := TwistTag.perm .E6
  have hd : rootDiagUnit (langTag .twistedE6) a ∈ A' := by
    rw [hA'eq]
    exact Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hfix := (mem_twistedTorusOf.1 (hT hd)).2
  have hΦ : ggPhi .twistedE6 f (rootDiagUnit (langTag .twistedE6) a) =
      rootDiagUnit (langTag .twistedE6)
        (fun i : Fin (langTag .twistedE6).rank => (a (ρ.symm i))⁻¹) := by
    have htw := twistHom_rootDiagUnit_eq (t := TwistTag.E6) (K := GGL) (σ := ggFrobT f) a
    rw [show ggPhi .twistedE6 f (rootDiagUnit (langTag .twistedE6) a) =
      twistHom TwistTag.E6 GGL (ggFrobT f) (rootDiagUnit TwistTag.E6.tag a) from rfl, htw]
    exact congrArg (rootDiagUnit (langTag .twistedE6)) (funext fun i =>
      excPayQ6_frobT_unit_eq_inv (ha (ρ.symm i)) hplus)
  have h1 : rootDiagUnit (langTag .twistedE6)
        (weylAct w (fun i : Fin (langTag .twistedE6).rank => (a (ρ.symm i))⁻¹)) =
      rootDiagUnit (langTag .twistedE6) a := by
    rw [← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w
      (fun i : Fin (langTag .twistedE6).rank => (a (ρ.symm i))⁻¹), ← hΦ]
    exact hfix
  exact rootDiagUnit_injective (τ := langTag .twistedE6) (K := GGL) h1

private theorem excPayQ6_dvd_smul_of_dvd {τ : Tag} {p : ℕ} (w : WeylGroup τ)
    {x : Fin τ.rank → ℤ} (hx : ∀ i, (p : ℤ) ∣ x i) :
    ∀ j, (p : ℤ) ∣ (w • x) j := by
  intro j
  rw [smul_eq_sum_single]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (hx i) _

private theorem excPayQ6_coord_rootChar {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup (langTag .twistedE6)}
    (h : ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = a)
    {b : Fin (langTag .twistedE6).rank → GGLˣ} (hb : ∀ i, b i ^ p = 1)
    (k : Fin (langTag .twistedE6).rank) :
    rootChar b (w⁻¹ • (Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ)) =
      (rootChar b (permLattice (TwistTag.perm .E6)
        (Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ)))⁻¹ := by
  let ρ : Equiv.Perm (Fin (langTag .twistedE6).rank) := TwistTag.perm .E6
  let e : Fin (langTag .twistedE6).rank → ℤ := Pi.single k 1
  let a : Fin (langTag .twistedE6).rank → GGLˣ := fun i => (b (ρ i))⁻¹
  have ha : ∀ i, a i ^ p = 1 := by
    intro i
    dsimp [a]
    rw [inv_pow, hb, inv_one]
  have h1 : weylAct w b = a := by
    have h2 := h a ha
    have hfun : (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = b := by
      funext i
      dsimp [a]
      rw [inv_inv]
      exact congrArg b (Equiv.apply_symm_apply ρ i)
    rwa [hfun] at h2
  calc rootChar b (w⁻¹ • e)
      = rootChar (weylAct w b) e := (rootChar_weylAct w b e).symm
    _ = rootChar a e := by rw [h1]
    _ = (rootChar (fun i => b (ρ i)) e)⁻¹ := by
          simp only [a, Pi.inv_apply, rootChar, Finset.prod_inv_distrib, inv_zpow]
    _ = (rootChar b (permLattice ρ e))⁻¹ := by rw [rootChar_permLattice]

private theorem excPayQ6_coord_mod_single {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup (langTag .twistedE6)}
    (h : ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = a)
    (k j : Fin (langTag .twistedE6).rank) :
    (p : ℤ) ∣ (w⁻¹ • (Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ)) j +
      (permLattice (TwistTag.perm .E6)
        (Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ)) j := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let ρ : Equiv.Perm (Fin (langTag .twistedE6).rank) := TwistTag.perm .E6
  let ζ : GGLˣ := ggZeta p hp hp2
  have hζo : orderOf ζ = p := ggZeta_order p hp hp2
  have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  let e : Fin (langTag .twistedE6).rank → ℤ := Pi.single k 1
  let b : Fin (langTag .twistedE6).rank → GGLˣ := Pi.mulSingle j ζ
  have hb : ∀ i, b i ^ p = 1 := by
    intro i
    dsimp [b]
    by_cases hij : i = j
    · subst hij; rw [Pi.mulSingle_eq_same, hζp]
    · rw [Pi.mulSingle_eq_of_ne hij, one_pow]
  have hroot : rootChar b (w⁻¹ • e) = (rootChar b (permLattice ρ e))⁻¹ :=
    excPayQ6_coord_rootChar hp hp2 hplus h hb k
  have hz : ζ ^ ((w⁻¹ • e) j) = ζ ^ (-((permLattice ρ e) j)) := by
    have hleft : rootChar b (w⁻¹ • e) = ζ ^ ((w⁻¹ • e) j) := by
      dsimp [b]
      rw [CFSG.LieType.Chevalley.RootTorus.rootChar_mulSingle]
    have hright : rootChar b (permLattice ρ e) = ζ ^ ((permLattice ρ e) j) := by
      dsimp [b]
      rw [CFSG.LieType.Chevalley.RootTorus.rootChar_mulSingle]
    rw [← hleft, hroot, hright, zpow_neg]
  have hmod' : ((w⁻¹ • e) j) ≡ -((permLattice ρ e) j) [ZMOD orderOf ζ] :=
    (zpow_eq_zpow_iff_modEq (x := ζ)).mp hz
  rw [hζo] at hmod'
  have h2 : (p : ℤ) ∣ -((permLattice ρ e) j) - (w⁻¹ • e) j :=
    Int.modEq_iff_dvd.mp hmod'
  have h4 : (p : ℤ) ∣ -(((w⁻¹ • e) j) + (permLattice ρ e) j) := by
    have h5 : -(((w⁻¹ • e) j) + (permLattice ρ e) j) =
        -((permLattice ρ e) j) - (w⁻¹ • e) j := by ring
    rw [h5]
    exact h2
  exact dvd_neg.mp h4

private theorem excPayQ6_coord_mod {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup (langTag .twistedE6)}
    (h : ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = a) :
    ∀ k j : Fin (langTag .twistedE6).rank,
      (p : ℤ) ∣ (w • (permLattice (TwistTag.perm .E6)
          (Pi.single k 1) : Fin (langTag .twistedE6).rank → ℤ)) j -
        (-1) * (Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ) j := by
  let ρ : Equiv.Perm (Fin (langTag .twistedE6).rank) := TwistTag.perm .E6
  intro k
  let e : Fin (langTag .twistedE6).rank → ℤ := Pi.single k 1
  have h3 : ∀ j : Fin (langTag .twistedE6).rank,
      (p : ℤ) ∣ (w⁻¹ • e) j + (permLattice ρ e) j := by
    intro j
    exact excPayQ6_coord_mod_single hp hp2 hplus h k j
  intro j
  have hx : ∀ i : Fin (langTag .twistedE6).rank,
      (p : ℤ) ∣ (((w⁻¹ • e) + permLattice ρ e) :
        Fin (langTag .twistedE6).rank → ℤ) i := by
    intro i
    simpa [Pi.add_apply] using h3 i
  have hw := excPayQ6_dvd_smul_of_dvd (p := p) w hx j
  have h6 : w • ((w⁻¹ • e) + permLattice ρ e) = e + w • permLattice ρ e := by
    rw [smul_add, ← mul_smul, mul_inv_cancel, one_smul]
  rw [h6] at hw
  have h7 : (p : ℤ) ∣ (w • permLattice ρ e) j + e j := by
    simpa [Pi.add_apply, add_comm] using hw
  show (p : ℤ) ∣ (w • permLattice ρ e) j - (-1) * e j
  convert h7 using 2 <;> ring

private theorem excPayQ6_smul_neg_of_weylAct_inv {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1) {w : WeylGroup (langTag .twistedE6)}
    (h : ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = a) :
    ∀ u : Fin (langTag .twistedE6).rank → ℤ, w • ggGraphLat .twistedE6 u = -u := by
  let ρ : Equiv.Perm (Fin (langTag .twistedE6).rank) := TwistTag.perm .E6
  have hmod := excPayQ6_coord_mod hp hp2 hplus h
  have hbasis : ∀ k : Fin (langTag .twistedE6).rank,
      w • (permLattice ρ (Pi.single k 1)) =
        -(Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ) := by
    intro k
    have hβ : IsRoot (langTag .twistedE6)
        (w • (permLattice ρ (Pi.single k 1))) := by
      rw [permLattice_single]
      exact IsRoot.smul (isRoot_single (langTag .twistedE6) (ρ k)) w
    have hroot := ggKGExc_root_eq_of_modEq (τ := langTag .twistedE6) (Or.inl rfl)
      hp (by omega) hβ (isRoot_single (langTag .twistedE6) k) (c := -1) (hmod k)
    rcases hroot with h' | h'
    · exfalso
      have h2 := hmod k k
      rw [h'] at h2
      simp at h2
      norm_num at h2
      have hdiv : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
      have := Nat.le_of_dvd (by norm_num) hdiv
      omega
    · exact h'
  intro u
  show w • permLattice ρ u = -u
  have hsum : permLattice ρ u = ∑ k, u k • permLattice ρ (Pi.single k 1) := by
    ext j
    simp only [permLattice, Function.comp_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single (ρ.symm j)]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (ρ.symm j)) h
  rw [hsum, Finset.smul_sum]
  have h2 : ∀ k : Fin (langTag .twistedE6).rank,
      w • (u k • permLattice ρ (Pi.single k 1)) =
        -(u k • (Pi.single k 1 : Fin (langTag .twistedE6).rank → ℤ)) := by
    intro k
    rw [smul_comm w (u k), hbasis k, smul_neg]
  refine Eq.trans (Finset.sum_congr rfl fun k _ => h2 k) ?_
  rw [Finset.sum_neg_distrib, ← eq_sum_single u]

private theorem excPayQ6_weylLaw_of_smul_neg {p f : ℕ} {ht : GGExcFive .twistedE6}
    {w : WeylGroup (langTag .twistedE6)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) (h : ∀ u : Fin (langTag .twistedE6).rank → ℤ,
      w • ggGraphLat .twistedE6 u = -u) :
    GGWeylLaw .twistedE6 p f ht w := by
  have heps : eps p f = -1 :=
    (eps_eq_neg_one_iff hp hp2 f (Or.inr hplus)).2 hplus
  intro u
  have hperm : permLattice ((finCongr (rank_eq_langTag f ht)).permCongr
      (piB .twistedE6 p f)) u = u := by
    rw [piB_twistedE6_of_dvd f hplus]
    change permLattice ((finCongr (rank_eq_langTag f ht)).permCongr
      (1 : Equiv.Perm (Fin ((ggU (absTag .twistedE6) 6 f).D.rank)))) u = u
    change permLattice
      (Equiv.permCongr (finCongr (rank_eq_langTag f ht)) (Equiv.refl _)) u = u
    rw [Equiv.permCongr_refl]
    rfl
  rw [h u, heps, neg_one_smul, hperm]

private theorem excPayQ6_eq_Tp_of_torus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (ModGL (langTag .twistedE6) GGL)} (hAel : IsElemAbelian p A)
    (hcard : Nat.card A = p ^ 6) {w : WeylGroup (langTag .twistedE6)}
    {g : ModGL (langTag .twistedE6) GGL}
    (hT : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
        (ggPhi .twistedE6 f)) :
    A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ6_Tp p := by
  let A' : Subgroup (ModGL (langTag .twistedE6) GGL) :=
    A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'card : Nat.card A' = p ^ 6 := by
    rw [show A' = A.map (MulAut.conj g⁻¹).toMonoidHom from rfl]
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective, hcard]
  have hAle : A' ≤ excPayQ6_Tp p := by
    intro x hx
    have hxT := hT hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      (mem_twistedTorusOf.1 hxT).1
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hxp : (rootDiagUnit (langTag .twistedE6) a) ^ p = 1 := by
      rw [← hxy, ← map_pow, hAel.2 y hy, map_one]
    have ha1 : a ^ p = 1 := by
      apply rootDiagUnit_injective
      rw [← rootDiagUnit_pow, hxp, rootDiagUnit_one]
    exact Subgroup.subset_closure
      ⟨a, fun i => by simpa using congrFun ha1 i, rfl⟩
  have hA'eq : A' = excPayQ6_Tp p := by
    haveI : Finite (excPayQ6_Tp p) :=
      Nat.finite_of_card_ne_zero (by
        rw [excPayQ6_card_Tp hp hp2]
        exact pow_ne_zero 6 hp.ne_zero)
    refine Subgroup.eq_of_le_of_card_ge hAle ?_
    rw [excPayQ6_card_Tp hp hp2, hA'card]
  exact hA'eq

private theorem excPayQ6_toralLangPosition {p f : ℕ} {ht : GGExcFive .twistedE6}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (A : Subgroup (ModGL (langTag .twistedE6) GGL)) (hA : A ≤ ggFixGp .twistedE6 f)
    (hAel : IsElemAbelian p A) (hcard : Nat.card A = p ^ 6) :
    ∃ (w : WeylGroup (langTag .twistedE6)) (g : ModGL (langTag .twistedE6) GGL),
      g ∈ adjointGroup (langTag .twistedE6) GGL ∧
      ggPhi .twistedE6 f g =
        g * canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom ≤
        twistedTorusOf (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
          (ggPhi .twistedE6 f) ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ6_Tp p := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hΦ : IsSteinbergEnd (langTag .twistedE6) GGL (2 ^ f) (ggPhi .twistedE6 f) :=
    CFSG.StandardType.LieCore.isSteinbergEnd_ggPhi ht f
  have hΦZ : IsSteinbergEndZ (langTag .twistedE6) GGL (2 ^ f) (ggPhi .twistedE6 f) :=
    CFSG.StandardType.LieCore.isSteinbergEndZ_of_isSteinbergEnd hΦ
  have hfin : Finite ↥(ratPoints (ggPhi .twistedE6 f)) :=
    CFSG.StandardType.LieCore.finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2)) hΦZ
  have hArat : A ≤ ratPoints (ggPhi .twistedE6 f) := hA
  have halg : (letI := ZMod.algebra GGL 2; Algebra.IsAlgebraic (ZMod 2) GGL) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite
      (ZMod 2) 2
  have htor : IsToralSubgroup (langTag .twistedE6) GGL A := by
    refine CFSG.StandardType.LieCore.ggLieToralPosition_holds (langTag .twistedE6)
      (isExcTag (langTag .twistedE6)) GGL halg f hf (ggPhi .twistedE6 f) hΦZ hfin p hp hp2 A
      hArat hAel ?_
    rw [hcard]
    have hnt : 6 < nontoralMinRank (langTag .twistedE6) p := by
      rw [show langTag .twistedE6 = Tag.E6 from rfl]
      simp [nontoralMinRank, hp3]
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).2 hnt
  obtain ⟨w, g, hg, hlang, hT⟩ :=
    CFSG.StandardType.LieCore.ggLieLangPosition_holds (langTag .twistedE6)
      (isExcTag (langTag .twistedE6)) GGL f hf (ggPhi .twistedE6 f) hΦZ hfin p hp hp2 A
      hArat hAel htor
  refine ⟨w, g, hg, hlang, hT, ?_⟩
  exact excPayQ6_eq_Tp_of_torus hp hp2 hAel hcard hT

theorem exists_datumModel_TwE6_of_card {p f : ℕ} {ht : GGExcFive .twistedE6} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1)
    (A : Subgroup (ModGL (langTag .twistedE6) GGL)) (hA : A ≤ ggFixGp .twistedE6 f)
    (hAel : IsElemAbelian p A) (hcard : Nat.card A = p ^ 6) :
    ∃ M : GGDatumModel .twistedE6 f p ht,
      A.map (MulAut.conj M.D.g0⁻¹).toMonoidHom =
        Subgroup.closure {z | ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
          (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z} := by
  obtain ⟨w, g, hg, hlang, hT, hA'eq⟩ :=
    excPayQ6_toralLangPosition (ht := ht) hp hp5 hf A hA hAel hcard
  have hp2 : p ≠ 2 := by omega
  have hweyl : ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      weylAct w (fun i : Fin (langTag .twistedE6).rank =>
        (a ((TwistTag.perm .E6).symm i))⁻¹) = a :=
    excPayQ6_weylAct_inv_of_mem_torus hp hplus hT hA'eq
  have hneg : ∀ u : Fin (langTag .twistedE6).rank → ℤ,
      w • ggGraphLat .twistedE6 u = -u :=
    excPayQ6_smul_neg_of_weylAct_inv hp hp5 hp2 hplus hweyl
  have hw : GGWeylLaw .twistedE6 p f ht w :=
    excPayQ6_weylLaw_of_smul_neg hp hp2 hplus hneg
  have hΦ : IsSteinbergEnd (langTag .twistedE6) GGL (2 ^ f) (ggPhi .twistedE6 f) :=
    CFSG.StandardType.LieCore.isSteinbergEnd_ggPhi ht f
  let D : LangDatum (langTag .twistedE6) GGL :=
    CFSG.StandardType.LieCore.langDatumOfPosition hΦ w g hg hlang
  refine ⟨⟨w, hw, D, rfl, rfl, rfl⟩, ?_⟩
  show A.map (MulAut.conj g⁻¹).toMonoidHom = excPayQ6_Tp p
  exact hA'eq

end CFSG.StandardType.ExcPay
