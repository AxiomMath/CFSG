module

public import CFSG.RankThree.PartOne.K1214.ActR
public import CFSG.RankThree.PartOne.LIT.RankProjective
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitRank
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product
public import CFSG.LieType.SeitzGeneration.LowNarrow

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open Matrix CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped MatrixGroups

theorem aut_trivial_mod_p_of_homocyclic {G : Type*} [Group G] {p r e : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : r = 1 ∨ r = 2) (he : 2 ≤ e) {Q : Subgroup G}
    (eQ : Q ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) (φ : MulAut G)
    (hQ : Q.map φ.toMonoidHom = Q) (hφ : φ ^ p = 1) {x : G} (hxQ : x ∈ Q) (hx : x ^ p = 1) :
    φ x = x := by
  let σ : MulAut Q := (φ.subgroupMap Q).trans (MulEquiv.subgroupCongr hQ)
  have hσ : ∀ y : Q, ((σ y : Q) : G) = φ y := fun y => rfl
  have hσk : ∀ k : ℕ, ∀ y : Q, (((σ ^ k) y : Q) : G) = (φ ^ k) y := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ', MulAut.mul_apply]
  have hσp : σ ^ p = 1 := by
    ext y
    rw [hσk, hφ]
    rfl
  have hfix := (CFSG.RankThree.PartOne.K1214.act_lemma_mul hp5 hr (by omega) (Or.inr he) eQ σ
    hσp).2 ⟨x, hxQ⟩ (Subtype.ext (by simpa using hx))
  have := congrArg Subtype.val hfix
  rwa [hσ] at this

theorem pRank_le_div_ordQ {K : Type*} [Field K] [Finite K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0) (H : Subgroup (GL ι K)) :
    CFSG.Open.pRank r (⊤ : Subgroup H) ≤
      Fintype.card ι / CFSG.StandardType.OrdPNS.ordQ K r := by
  refine CFSG.RankThree.PartOne.LIT.pRank_le_of_card_gl hr.one_lt H fun E _ hc he => ?_
  let f : GL ι K → Module.End K (ι → K) := fun g =>
    Matrix.toLinAlgEquiv' ((g : GL ι K) : Matrix ι ι K)
  have hf : Function.Injective f := fun a b h =>
    Units.ext (Matrix.toLinAlgEquiv'.injective h)
  have h := CFSG.StandardType.OrdPNS.card_le_pow_ordQ (V := ι → K) hr hrK
    (f '' (E : Set (GL ι K)))
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab := congrArg Units.val (hc a ha b hb)
      change Matrix.toLinAlgEquiv' (a : Matrix ι ι K) * Matrix.toLinAlgEquiv' (b : Matrix ι ι K) =
        Matrix.toLinAlgEquiv' (b : Matrix ι ι K) * Matrix.toLinAlgEquiv' (a : Matrix ι ι K)
      rw [← map_mul, ← map_mul]
      exact congrArg _ hab)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change (Matrix.toLinAlgEquiv' (a : Matrix ι ι K)) ^ r = 1
      rw [← map_pow, ← Units.val_pow_eq_pow_val, he a ha, Units.val_one, map_one])
  rwa [Nat.card_image_of_injective hf, Module.finrank_fintype_fun_eq_card] at h

theorem rankLE1_projImage_of_lt {K : Type*} [Field K] [Finite K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0) (H : Subgroup (GL ι K))
    (hN : ¬ r ∣ Nat.card ((Subgroup.center (GL ι K)).subgroupOf H))
    (hn : Fintype.card ι < 2 * CFSG.StandardType.OrdPNS.ordQ K r) :
    RankLE1 r (CFSG.PGLModel.projImage H) := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine RankLE1.of_pRank hr ?_
  rw [CFSG.RankThree.PartOne.LIT.pRank_projImage_eq H hN]
  refine (pRank_le_div_ordQ hr hrK H).trans ?_
  have hd := CFSG.StandardType.OrdPNS.ordQ_pos hr hrK
  have : Fintype.card ι / CFSG.StandardType.OrdPNS.ordQ K r < 2 :=
    (Nat.div_lt_iff_lt_mul hd).2 (by linarith)
  omega

theorem two_le_ordQ {K : Type*} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (h1 : ((Nat.card K : ℕ) : ZMod r) ≠ 1) : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K r := by
  have h0 := CFSG.StandardType.OrdPNS.ordQ_pos hr hrK
  by_contra h
  have h1' : CFSG.StandardType.OrdPNS.ordQ K r = 1 := by omega
  rw [CFSG.StandardType.OrdPNS.ordQ_def, orderOf_eq_one_iff] at h1'
  exact h1 h1'

theorem three_le_ordQ {K : Type*} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (h1 : ((Nat.card K : ℕ) : ZMod r) ≠ 1) (h2 : ((Nat.card K : ℕ) : ZMod r) ≠ -1) :
    3 ≤ CFSG.StandardType.OrdPNS.ordQ K r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h0 := two_le_ordQ hr hrK h1
  by_contra h
  have h2' : CFSG.StandardType.OrdPNS.ordQ K r = 2 := by omega
  rw [CFSG.StandardType.OrdPNS.ordQ_def] at h2'
  have hsq : ((Nat.card K : ℕ) : ZMod r) ^ 2 = 1 := by
    rw [← h2']
    exact pow_orderOf_eq_one _
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h1 h
  · exact h2 h

theorem rankLE1_projSL_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrK : (r : K) ≠ 0) : RankLE1 r (projSL 2 K) := by
  haveI : Fact r.Prime := ⟨hr⟩
  let H : Subgroup (GL (Fin 2) K) := (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker
  have hH : ∀ h ∈ H, (h : Matrix (Fin 2) (Fin 2) K).det = 1 := fun h hh => by
    have := MonoidHom.mem_ker.mp hh
    simpa [Units.ext_iff] using this
  have hN : ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin 2) K)).subgroupOf H) :=
    CFSG.RankThree.PartOne.LIT.not_dvd_card_scalars (m := Fintype.card (Fin 2)) hr
      (by simpa using CFSG.RankThree.PartOne.LIT.not_dvd_two hr hr2) H
      fun g hg hc => CFSG.RankThree.PartOne.LIT.pow_card_eq_one_of_det g hc (hH g hg)
  refine RankLE1.of_pRank hr ?_
  show CFSG.Open.pRank r (⊤ : Subgroup (CFSG.PGLModel.projImage H)) ≤ 1
  rw [CFSG.RankThree.PartOne.LIT.pRank_projImage_eq H hN]
  refine CFSG.RankThree.PartOne.LIT.pRank_le_of_card_gl hr.one_lt H fun E hEH hc he => ?_
  let ι : SL(2, K) →* GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL
  have hι : Function.Injective ι := fun a b hab => (Matrix.SpecialLinearGroup.toGL_inj a b).1 hab
  have hEι : E ≤ ι.range := fun g hg => by
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) K), hH g (hEH hg)⟩, ?_⟩
    ext i j
    rfl
  let F : Subgroup SL(2, K) := E.comap ι
  have hFE : Nat.card F = Nat.card E := by
    have hmap : F.map ι = E := Subgroup.map_comap_eq_self hEι
    rw [← hmap, Subgroup.card_map_of_injective hι]
  have hF : CFSG.Open.IsElemAbelian r F := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hι ?_)⟩⟩, fun y hy => hι ?_⟩
    · have := hc _ a.2 _ b.2
      simpa [map_mul] using this
    · rw [map_pow, map_one]
      exact he _ hy
  rw [← hFE, pow_one]
  exact CFSG.LieType.SeitzGeneration.ExcHigh.card_le_of_isElemAbelian_specialLinear_two hrK hF

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
