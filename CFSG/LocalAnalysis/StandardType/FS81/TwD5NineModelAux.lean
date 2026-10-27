module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Local
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Cent
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthCore
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.OmMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentDecomp
public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
public import CFSG.LieType.SeitzGeneration.OrthExLift

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
  CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
  CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.OrthBlk CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open scoped Matrix commutatorElement

private theorem realized_centralizer_subset_evenFix0_of_recOutTwD5 {G : Type} [Group G]
    [Finite G] {b₀ : G} {B : Basis3 G (5 + 1)} (hb0 : B.b 0 = b₀)
    (hrec : RecOutTwD5 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 5 := by
  intro A hA
  obtain ⟨g, hgC, hActs⟩ := hA
  have hgcomm : g * b₀ = b₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hconj : MulAut.conj g b₀ = b₀ := by
      rw [MulAut.conj_apply, hgcomm, mul_assoc, mul_inv_cancel, mul_one]
    simpa using congrArg Subgroup.zpowers hconj
  have hAall : A ∈ evenAll0 5 := by
    rw [← hrec.2.1]
    exact ⟨g, hgN, hActs⟩
  obtain ⟨σ, s, hsign, hσs, hAeq⟩ := hAall
  obtain ⟨hσ0, hprod⟩ := hσs
  have hcol : (fun i : Fin (5 + 1) => A i 0) =
      Pi.single (0 : Fin (5 + 1)) (s 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [hAeq, spMat, hσ0]
    · simp [hAeq, spMat, hσ0, hi]
  have hvec : B.vec (fun i : Fin (5 + 1) => A i 0) = b₀ := by
    rw [← hActs 0, hb0, hgcomm]
    group
  have hsingle : (Pi.single (0 : Fin (5 + 1)) (s 0) : Coords (5 + 1)) =
      Pi.single (0 : Fin (5 + 1)) (1 : ZMod 3) := by
    apply B.vec_injective
    rw [← hcol, hvec, B.vec_single, hb0]
  have hs0 : s 0 = 1 := by
    simpa using congrFun hsingle 0
  have hsprod : ∏ i : Fin 5, s i.succ = 1 := by
    have h := Fin.prod_univ_succ (fun i : Fin (5 + 1) => s i)
    rw [hprod, hs0, one_mul] at h
    exact h.symm
  rw [evenFix0, spSet]
  exact ⟨σ, s, hsign, ⟨hσ0, hs0, hsprod⟩, hAeq⟩

theorem realized_K_subset_evenFix0_of_recOutTwD5 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) (hrec : RecOutTwD5 B b₀) :
    B.realized K ⊆ evenFix0 5 :=
  fun _ hA => realized_centralizer_subset_evenFix0_of_recOutTwD5 hB.2.1 hrec
    (realized_mono B hKC hA)

theorem Basis3.b_ne_b_ne_inv {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    {a b : Fin k} (hab : a ≠ b) : B.b a ≠ B.b b ∧ B.b a ≠ (B.b b)⁻¹ := by
  constructor
  · intro h
    have h1 : B.vec (Pi.single a 1 - Pi.single b 1) = 1 := by
      have h2 : B.vec (Pi.single a 1 - Pi.single b 1) = B.b a * (B.b b)⁻¹ := by
        calc B.vec (Pi.single a 1 - Pi.single b 1)
            = B.vec (Pi.single a 1) * B.vec (-(Pi.single b 1 : Coords k)) := by
              rw [sub_eq_add_neg, B.vec_add]
          _ = B.b a * (B.b b)⁻¹ := by
              rw [B.vec_single, show B.vec (-(Pi.single b 1 : Coords k)) =
                (B.vec (Pi.single b 1 : Coords k))⁻¹ from Basis3.vec_neg B _, B.vec_single]
      rw [h2, h, mul_inv_cancel]
    have h0 : (Pi.single a 1 - Pi.single b 1 : Coords k) = 0 := B.indep _ h1
    have h2 : (Pi.single a 1 - Pi.single b 1 : Coords k) a = 0 := by rw [h0]; rfl
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, sub_zero] at h2
    exact one_ne_zero h2
  · intro h
    have h1 : B.vec (Pi.single a 1 + Pi.single b 1) = 1 := by
      have h2 : B.vec (Pi.single a 1 + Pi.single b 1) = B.b a * B.b b := by
        rw [B.vec_add, B.vec_single, B.vec_single]
      rw [h2, h, inv_mul_cancel]
    have h0 : (Pi.single a 1 + Pi.single b 1 : Coords k) = 0 := B.indep _ h1
    have h2 : (Pi.single a 1 + Pi.single b 1 : Coords k) a = 0 := by rw [h0]; rfl
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero] at h2
    exact one_ne_zero h2

abbrev V5 : Type := Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2

noncomputable abbrev Q5 : QuadraticForm (ZMod 2) V5 := quadMinus 5 (ZMod 2) 1 1

theorem nondegenerate_Q5 : (polarBilin Q5).Nondegenerate :=
  nondegenerate_polarBilin_quadMinus_of_finite 5 (ZMod 2)
    (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)

private theorem eq_or_eq_inv_cases {G : Type} [Group G] {x y z : G}
    (h1 : x = z ∨ x = z⁻¹) (h2 : y = z ∨ y = z⁻¹) : x = y ∨ x = y⁻¹ := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by rw [inv_inv])
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem exists_frame_coordinates_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    ∃ (φ : ↥K ≃* ↥(orthDerived Q5)) (B' : Basis3 G (5 + 1))
      (F : SevOm.Frame Q5 3
        (((E ⊓ K).subgroupOf K).map ((orthDerived Q5).subtype.comp φ.toMonoidHom)) 5)
      (j : Fin 5 → Fin 5),
      Adapted B' b₀ K E ∧ Function.Injective j ∧
      (∀ i : Fin 5, B.b i.succ = B'.b (j i).succ ∨
        B.b i.succ = (B'.b (j i).succ)⁻¹) ∧
      evenFix0 5 ⊆ B'.realized K ∧
      (∀ k : Fin 5, finrank (ZMod 2) (F.U k) = 2) ∧
      (∀ (k : Fin 5) (hk : B'.b k.succ ∈ K),
        ((φ ⟨B'.b k.succ, hk⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
          F.ι (Multiplicative.ofAdd (Pi.single k 1))) := by
  classical
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hcenter, hmark, -⟩ := hHyp
  obtain ⟨hdisj, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨-, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 5) (by norm_num)
    hmark hcenter
  have hdisj' : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  obtain ⟨B', F, hB', heven, hU, hφB'⟩ := exists_basis_frame_of_model (Q := Q5) nondegenerate_Q5
    (exists_totallySingular_three_quadMinus (n := 4) (by norm_num)) (n := 5) (by norm_num)
    φ hb₀ hKC hdisj' hsup hmax hcard
  have hR : B.realized K ⊆ evenFix0 5 :=
    realized_K_subset_evenFix0_of_recOutTwD5 hB hKC hrec
  let j : Fin 5 → Fin 5 := fun i =>
    Classical.choose (exists_eq_or_eq_inv_of_realized_evenFix0 (n := 5) (by norm_num) hdisj'
      hB hB' hR heven i)
  have hj : ∀ i : Fin 5, B.b i.succ = B'.b (j i).succ ∨
      B.b i.succ = (B'.b (j i).succ)⁻¹ := fun i =>
    Classical.choose_spec (exists_eq_or_eq_inv_of_realized_evenFix0 (n := 5) (by norm_num) hdisj'
      hB hB' hR heven i)
  have hjinj : Function.Injective j := by
    intro i k hjk
    by_contra hik
    have hne : i.succ ≠ k.succ := fun h => hik (Fin.succ_injective 5 h)
    have hk' : B.b k.succ = B'.b (j i).succ ∨ B.b k.succ = (B'.b (j i).succ)⁻¹ := by
      have := hj k
      rw [← hjk] at this
      exact this
    have hcases := eq_or_eq_inv_cases (hj i) hk'
    rcases hcases with h | h
    · exact (Basis3.b_ne_b_ne_inv B hne).1 h
    · exact (Basis3.b_ne_b_ne_inv B hne).2 h
  exact ⟨φ, B', F, j, hB', hjinj, hj, heven, hU, hφB'⟩

theorem centralizer_decomp_of_plane_commutator {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {U : Submodule (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hU : IsCompl U (perpOf Q U)) (hU2 : finrank (ZMod 2) U = 2)
    (hP : (polarBilin (Q.restrict (perpOf Q U))).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q U))
    (hT : ∃ T : Submodule (ZMod 2) (perpOf Q U), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q.restrict (perpOf Q U)) u = 0)
    {x : V ≃ₗ[ZMod 2] V} (hxΩ : x ∈ orthDerived Q) (hx3 : x ^ 3 = 1)
    (hxU : ∀ u ∈ U, x u ∈ U) (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q U) :
    (orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) ≤
        Subgroup.zpowers x ⊔ ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆) ∧
      ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
        orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ =
          ⁅fixW Q U, fixW Q U⁆ ∧
      ⁅⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆,
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆⁆ =
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ ∧
      Disjoint (Subgroup.zpowers x)
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ := by
  classical
  set C := orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) with hC
  set A := ⁅fixW Q U, fixW Q U⁆ with hA
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ hxΩ
  have hxP : ∀ w ∈ perpOf Q U, x w = w := fun w hw => (hxfix w).mpr hw
  have hfixC : fixW Q U ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_fixW hU hxU hxP hg)
  have hAfix : A ≤ fixW Q U := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hAC : A ≤ C :=
    le_inf (Subgroup.commutator_mono fixW_le_orthogonalGroup fixW_le_orthogonalGroup)
      (hAfix.trans hfixC)
  have hAA : ⁅A, A⁆ = A := commutator_commutator_fixW hU hP hT
  have hdec : ∀ g ∈ C, ∃ i : ℕ, (x ^ i)⁻¹ * g ∈ A := by
    intro g hg
    obtain ⟨hgΩ, hgx⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨i, hi⟩ := exists_pow_inv_mul_mem_fixW hU hU2 hxO hx3 hxU hxfix
      (Subgroup.commutator_le_self _ hgΩ) (Subgroup.mem_centralizer_singleton_iff.mp hgx)
    exact ⟨i, mem_commutator_fixW_of_mem_orthDerived hQ hU hP h6 hi
      (mul_mem (inv_mem (pow_mem hxΩ i)) hgΩ)⟩
  have hcomm : ∀ g ∈ C, ∀ i : ℕ, Commute (x ^ i) g := by
    intro g hg i
    have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
    exact hgx.symm.pow_left i
  have hCC : ⁅C, C⁆ = A := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg g' hg'
      obtain ⟨i, hi⟩ := hdec g hg
      obtain ⟨i', hi'⟩ := hdec g' hg'
      have key := commutatorElement_mul_mul_of_commute (c := x ^ i) (c' := x ^ i')
        (a := (x ^ i)⁻¹ * g) (a' := (x ^ i')⁻¹ * g') (hcomm _ (hAC hi) i)
        (hcomm _ (hAC hi') i) (hcomm _ (hAC hi) i') (hcomm _ (hAC hi') i')
        ((Commute.refl x).pow_pow i i')
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
      rw [key]
      have := Subgroup.commutator_mem_commutator hi hi'
      rwa [hAA] at this
    · calc A = ⁅A, A⁆ := hAA.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC hAC
  have hdisj : Disjoint (Subgroup.zpowers x) A := by
    rw [Subgroup.disjoint_def]
    intro y hyx hyA
    have hfix := (hAfix hyA).2
    have hUne : U ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hU2
      exact absurd hU2 (by norm_num)
    obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    have hdis : ∀ u ∈ U, x u = u → u = 0 := fun u hu hxu =>
      (Submodule.disjoint_def.mp hU.disjoint) u hu ((hxfix u).mp hxu)
    have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    obtain ⟨n, hn, rfl⟩ := (mem_zpowers_iff_mem_range_orderOf (y := y)).mp hyx |>
      Finset.mem_image.mp
    have hn3 : n < 3 := lt_of_lt_of_le (Finset.mem_range.mp hn) (Nat.le_of_dvd (by norm_num) hord)
    have hfu := hfix u₀ hu₀
    interval_cases n
    · rfl
    · exact absurd (hdis u₀ hu₀ (by simpa using hfu)) hu₀0
    · exfalso
      have h3 : x (x (x u₀)) = u₀ := by
        have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f u₀) hx3
        simpa [pow_succ, LinearEquiv.mul_apply] using this
      have h2 : x (x u₀) = u₀ := by simpa [pow_two, LinearEquiv.mul_apply] using hfu
      have : x u₀ = u₀ := by
        have := congrArg x h2
        rw [h3] at this
        exact this.symm
      exact hu₀0 (hdis u₀ hu₀ this)
  refine ⟨?_, hCC, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, hi⟩ := hdec g hg
    rw [← mul_inv_cancel_left (x ^ i) g]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i) (hCC ▸ hi)
  · rw [hCC, hAA]
  · rw [hCC]
    exact hdisj

abbrev frameRot {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) :
    V ≃ₗ[ZMod 2] V :=
  F.ι (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3))

theorem frameRot_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (F : SevOm.Frame Q 3 A r) (i : Fin r) : frameRot F i ∈ A := by
  have h : frameRot F i ∈ F.ι.range := ⟨_, rfl⟩
  rwa [F.range] at h

theorem frameRot_pow_three {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (F : SevOm.Frame Q 3 A r) (i : Fin r) : frameRot F i ^ 3 = 1 := by
  have h : (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3)) ^ 3 = 1 := by
    have hsum : (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) +
        (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) +
          (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) = 0 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply]
        decide
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, Pi.zero_apply, add_zero]
    calc (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3)) ^ 3
        = Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) ^ 2 *
            Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) := by
          rw [pow_three, pow_two, mul_assoc]
      _ = Multiplicative.ofAdd ((Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) +
            (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3)) *
            Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) := by
          rw [pow_two, ← ofAdd_add]
      _ = Multiplicative.ofAdd ((Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) +
            (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3) +
              (Pi.single i (1 : ZMod 3) : Fin r → ZMod 3)) := by
          rw [← ofAdd_add]
      _ = 1 := by rw [hsum, ofAdd_zero]
  rw [frameRot, ← map_pow, h, map_one]

theorem frameRot_fix_iff {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (F : SevOm.Frame Q 3 A r) (i : Fin r) (v : V) :
    frameRot F i v = v ↔ v ∈ perpOf Q (F.U i) := by
  rw [frameRot, F.fix, perpOf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h u hu
    exact h i (by simp) u hu
  · intro h j hj u hu
    have hji : j = i := by
      by_contra hne
      exact hj (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
    subst hji
    exact h u hu

theorem frameRot_facts_of_eq_or_eq_inv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (F : SevOm.Frame Q 3 A r) (i : Fin r) {y : V ≃ₗ[ZMod 2] V}
    (hy : y = frameRot F i ∨ y = (frameRot F i)⁻¹) :
    y ^ 3 = 1 ∧ (∀ u ∈ F.U i, y u ∈ F.U i) ∧ ∀ v, y v = v ↔ v ∈ perpOf Q (F.U i) := by
  rcases hy with rfl | rfl
  · exact ⟨frameRot_pow_three F i, fun u hu => F.mapsTo _ i u hu, frameRot_fix_iff F i⟩
  · have h3 : (frameRot F i)⁻¹ ^ 3 = 1 := by
      rw [inv_pow, frameRot_pow_three F i, inv_one]
    refine ⟨h3, ?_, ?_⟩
    · have h2 : frameRot F i ^ 2 = (frameRot F i)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, show (2 + 1 : ℕ) = 3 by norm_num,
          frameRot_pow_three]
      intro u hu
      rw [← h2, pow_two, LinearEquiv.mul_apply]
      exact F.mapsTo _ i _ (F.mapsTo _ i u hu)
    · intro v
      rw [← frameRot_fix_iff F i v]
      constructor
      · intro h
        have := congrArg (fun w => frameRot F i w) h
        simpa using this.symm
      · intro h
        have := congrArg (fun w => (frameRot F i)⁻¹ w) h
        simpa using this.symm

theorem perp_polarBilin_nondegenerate {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hU : PolarNondegOn Q U) :
    (polarBilin (Q.restrict (perpOf Q U))).Nondegenerate := by
  have hUc : IsCompl U (perpOf Q U) := isCompl_perp hU
  have hPnd : PolarNondegOn Q (perpOf Q U) := polarNondegOn_perp hQ hU
  have hrefl : (polarBilin (Q.restrict (perpOf Q U))).IsRefl :=
    (QuadraticMap.isSymm_polarBilin _).isRefl
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
  intro m hm
  refine Submodule.coe_eq_zero.mp (hPnd m m.2 fun y hy => ?_)
  have h := hm ⟨y, hy⟩
  rw [polarBilin_apply_apply] at h
  simpa [QuadraticMap.polar, QuadraticMap.restrict_apply] using h

theorem perp_exists_ts_three {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hU : PolarNondegOn Q U)
    (h8 : 8 ≤ finrank (ZMod 2) (perpOf Q U)) :
    ∃ T : Submodule (ZMod 2) (perpOf Q U), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q.restrict (perpOf Q U)) u = 0 :=
  CFSG.LieType.SeitzGeneration.OrthNS.exists_ts_three_comp (polarNondegOn_perp hQ hU) h8

theorem isSimpleGroup_orthDerived_of_ts {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hTs : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ u ∈ T, Q u = 0) :
    IsSimpleGroup ↥(orthDerived Q) := by
  have hTs' := hTs
  obtain ⟨T, hT3, -⟩ := hTs
  have hpos : 0 < finrank (ZMod 2) V := by
    have := Submodule.finrank_le T
    omega
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  have hq := CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ hTs'
  have hcenter := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hTs'
  have hsimple : IsSimpleGroup (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem exists_commutator_centralizer_equiv_restrict {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {U : Submodule (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hU : PolarNondegOn Q U) (hU2 : finrank (ZMod 2) U = 2)
    (hT : ∃ T : Submodule (ZMod 2) (perpOf Q U), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q.restrict (perpOf Q U)) u = 0)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q U)) {x : V ≃ₗ[ZMod 2] V}
    (hxΩ : x ∈ orthDerived Q) (hx3 : x ^ 3 = 1)
    (hxU : ∀ u ∈ U, x u ∈ U) (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q U) :
    ∃ ψ : ↥⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
        orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ ≃*
      ↥(orthDerived (Q.restrict (perpOf Q U))),
      (∀ g (w : perpOf Q U), ((((ψ g : ↥(orthDerived (Q.restrict (perpOf Q U)))) :
          perpOf Q U ≃ₗ[ZMod 2] perpOf Q U) w : perpOf Q U) : V) =
        (g : V ≃ₗ[ZMod 2] V) (w : V)) ∧
      ∀ g : ↥⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆,
        ∀ u ∈ U, (g : V ≃ₗ[ZMod 2] V) u = u := by
  classical
  obtain ⟨-, hCC, -, -⟩ := centralizer_decomp_of_plane_commutator hQ (isCompl_perp hU)
    hU2 (perp_polarBilin_nondegenerate hQ hU) h6 hT hxΩ hx3 hxU hxfix
  set O := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U)) with hO
  have hmap : (commutator ↥O).map O.subtype = orthDerived (Q.restrict (perpOf Q U)) := by
    rw [orthDerived, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hfix : ⁅fixW Q U, fixW Q U⁆ = (commutator ↥O).map (extG (isCompl_perp hU)) :=
    commutator_fixW_eq_map (isCompl_perp hU)
  let eExt : ↥((commutator ↥O).map (extG (isCompl_perp hU))) ≃* ↥(commutator ↥O) :=
    (Subgroup.equivMapOfInjective (commutator ↥O) (extG (isCompl_perp hU))
      (extG_injective (isCompl_perp hU))).symm
  let eO : ↥(commutator ↥O) ≃* ↥(orthDerived (Q.restrict (perpOf Q U))) :=
    (Subgroup.equivMapOfInjective (commutator ↥O) O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e : ↥((commutator ↥O).map (extG (isCompl_perp hU))) ≃*
      ↥(orthDerived (Q.restrict (perpOf Q U))) := eExt.trans eO
  have hmain : ∀ (y : ↥((commutator ↥O).map (extG (isCompl_perp hU)))) (w : perpOf Q U),
      ((((e y : ↥(orthDerived (Q.restrict (perpOf Q U)))) :
        perpOf Q U ≃ₗ[ZMod 2] perpOf Q U) w : perpOf Q U) : V) =
        (y : V ≃ₗ[ZMod 2] V) (w : V) := by
    intro y w
    have hy : extG (isCompl_perp hU) (↑(eExt y) : ↥O) = (y : V ≃ₗ[ZMod 2] V) :=
      congrArg Subtype.val (eExt.symm_apply_apply y)
    change ((((↑(eExt y) : ↥O) : perpOf Q U ≃ₗ[ZMod 2] perpOf Q U) w :
      perpOf Q U) : V) = (y : V ≃ₗ[ZMod 2] V) (w : V)
    rw [← hy]
    exact (extHom_apply_of_mem_U (isCompl_perp hU) (↑(eExt y) : ↥O) w.2).symm
  refine ⟨(MulEquiv.subgroupCongr (hCC.trans hfix)).trans e, ?_, ?_⟩
  · intro g w
    change ((((e (MulEquiv.subgroupCongr (hCC.trans hfix) g) :
      ↥(orthDerived (Q.restrict (perpOf Q U)))) :
      perpOf Q U ≃ₗ[ZMod 2] perpOf Q U) w : perpOf Q U) : V) =
      (g : V ≃ₗ[ZMod 2] V) (w : V)
    exact hmain (MulEquiv.subgroupCongr (hCC.trans hfix) g) w
  · intro g u hu
    have hg : (g : V ≃ₗ[ZMod 2] V) ∈ ⁅fixW Q U, fixW Q U⁆ := by
      rw [← hCC]
      exact g.2
    exact (mem_fixW.mp (Subgroup.commutator_le_self (fixW Q U) hg)).2 u hu

theorem commutator_centralizer_equiv_orthDerived {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {U : Submodule (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hU : PolarNondegOn Q U) (hU2 : finrank (ZMod 2) U = 2)
    (hT : ∃ T : Submodule (ZMod 2) (perpOf Q U), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q.restrict (perpOf Q U)) u = 0)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q U)) {x : V ≃ₗ[ZMod 2] V}
    (hxΩ : x ∈ orthDerived Q) (hx3 : x ^ 3 = 1)
    (hxU : ∀ u ∈ U, x u ∈ U) (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q U) :
    Nonempty (↥⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
        orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ ≃*
      ↥(orthDerived (Q.restrict (perpOf Q U)))) := by
  obtain ⟨ψ, -, -⟩ := exists_commutator_centralizer_equiv_restrict hQ hU hU2 hT h6 hxΩ hx3
    hxU hxfix
  exact ⟨ψ⟩

theorem phi_eq_or_eq_inv_frameRot {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B B' : Basis3 G (5 + 1)} (hB' : Adapted B' b₀ K E) {φ : ↥K ≃* ↥(orthDerived Q5)}
    {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)} {F : SevOm.Frame Q5 3 A 5} {j : Fin 5 → Fin 5}
    (hj : ∀ i, B.b i.succ = B'.b (j i).succ ∨ B.b i.succ = (B'.b (j i).succ)⁻¹)
    (hφB' : ∀ (k : Fin 5) (hk : B'.b k.succ ∈ K),
      ((φ ⟨B'.b k.succ, hk⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) = frameRot F k)
    (i : Fin 5) (hi : B.b i.succ ∈ K) :
    ((φ ⟨B.b i.succ, hi⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) = frameRot F (j i) ∨
      ((φ ⟨B.b i.succ, hi⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        (frameRot F (j i))⁻¹ := by
  rcases hj i with h | h
  · left
    have hz : (⟨B.b i.succ, hi⟩ : ↥K) =
        ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ := Subtype.ext h
    calc ((φ ⟨B.b i.succ, hi⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5)
        = ((φ ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ :
              ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) := by rw [hz]
      _ = frameRot F (j i) := hφB' (j i) (hB'.2.2 _ (Fin.succ_ne_zero (j i)))
  · right
    have hz : (⟨B.b i.succ, hi⟩ : ↥K) =
        (⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ : ↥K)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_inv]
      exact h
    calc ((φ ⟨B.b i.succ, hi⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5)
        = ((φ (⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ : ↥K)⁻¹ :
              ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) := by rw [hz]
      _ = ((φ ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ :
              ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5)⁻¹ := by simp
      _ = (frameRot F (j i))⁻¹ := by
          rw [hφB' (j i) (hB'.2.2 _ (Fin.succ_ne_zero (j i)))]

theorem exists_nineJ_equiv_commutator {G X : Type} [Group G] [Group X] {K : Subgroup G}
    {L : Subgroup X} (φ : ↥K ≃* ↥L) {a : G} (ha : a ∈ K) :
    ∃ e : ↥(nineJ K a) ≃* ↥⁅L ⊓ Subgroup.centralizer ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X),
        L ⊓ Subgroup.centralizer ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X)⁆,
      ∀ (g : ↥(nineJ K a)) (hg : (g : G) ∈ K), (e g : X) = ((φ ⟨g, hg⟩ : ↥L) : X) := by
  classical
  let Ck : Subgroup ↥K := Subgroup.centralizer ({⟨a, ha⟩} : Set ↥K)
  let Cl : Subgroup ↥L := Subgroup.centralizer ({φ ⟨a, ha⟩} : Set ↥L)
  have hCk : Ck = Subgroup.centralizer ({⟨a, ha⟩} : Set ↥K) := rfl
  have hCl : Cl = Subgroup.centralizer ({φ ⟨a, ha⟩} : Set ↥L) := rfl
  have hK : K ⊓ Subgroup.centralizer ({a} : Set G) = Ck.map K.subtype := by
    ext y
    constructor
    · rintro ⟨hyK, hyC⟩
      have hyC' : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact ⟨⟨y, hyK⟩, Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using hyC'), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hz' : z * ⟨a, ha⟩ = ⟨a, ha⟩ * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hz
      simpa using congrArg (fun w : ↥K => (w : G)) hz'
  have hL : L ⊓ Subgroup.centralizer ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X) =
      Cl.map L.subtype := by
    ext y
    constructor
    · rintro ⟨hyL, hyC⟩
      have hyC' : y * ((φ ⟨a, ha⟩ : ↥L) : X) = ((φ ⟨a, ha⟩ : ↥L) : X) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact ⟨⟨y, hyL⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext hyC'), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hz' : z * φ ⟨a, ha⟩ = φ ⟨a, ha⟩ * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hz
      simpa using congrArg (fun w : ↥L => (w : X)) hz'
  have hJ : nineJ K a = (⁅Ck, Ck⁆).map K.subtype := by
    unfold nineJ
    rw [Subgroup.map_commutator, hK]
  have hφ : Ck.map φ.toMonoidHom = Cl := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hCl, Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg (fun w : ↥K => φ w)
        (Subgroup.mem_centralizer_singleton_iff.mp hz)
    · intro hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      refine ⟨φ.symm y, ?_, by simp⟩
      rw [hCk]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply φ.injective
      simpa using hy
  have hJmap : (⁅Ck, Ck⁆).map φ.toMonoidHom = ⁅Cl, Cl⁆ := by
    rw [Subgroup.map_commutator, hφ]
  have hCCmap : (⁅Cl, Cl⁆).map L.subtype =
      ⁅L ⊓ Subgroup.centralizer ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X),
        L ⊓ Subgroup.centralizer ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X)⁆ := by
    rw [Subgroup.map_commutator, hL]
  let eJ : ↥⁅Ck, Ck⁆ ≃* ↥(nineJ K a) :=
    (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ.symm)
  let eC : ↥⁅Ck, Ck⁆ ≃* ↥⁅Cl, Cl⁆ :=
    (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hJmap)
  let eL : ↥⁅Cl, Cl⁆ ≃* ↥⁅L ⊓ Subgroup.centralizer
      ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X), L ⊓ Subgroup.centralizer
      ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X)⁆ :=
    (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hCCmap)
  have hval : ∀ (y : ↥⁅Ck, Ck⁆), ((eC y : ↥⁅Cl, Cl⁆) : ↥L) = φ (y : ↥K) := by
    intro y
    change ((Subgroup.equivMapOfInjective _ φ.toMonoidHom
      (show Function.Injective φ.toMonoidHom from φ.injective) y :
      ↥((⁅Ck, Ck⁆).map φ.toMonoidHom)) : ↥L) = φ (y : ↥K)
    rw [Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have hvalL : ∀ y : ↥⁅Cl, Cl⁆, ((eL y : ↥⁅L ⊓ Subgroup.centralizer
      ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X), L ⊓ Subgroup.centralizer
      ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X)⁆) : X) = ((y : ↥L) : X) := by
    intro y
    change ((Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective y :
      ↥((⁅Cl, Cl⁆).map L.subtype)) : X) = ((y : ↥L) : X)
    rw [Subgroup.coe_equivMapOfInjective_apply]
    rfl
  refine ⟨eJ.symm.trans (eC.trans eL), ?_⟩
  intro g hg
  have hxG : (((eJ.symm g : ↥⁅Ck, Ck⁆) : ↥K) : G) = (g : G) := by
    have h1 := congrArg (fun y : ↥(nineJ K a) => (y : G)) (eJ.apply_symm_apply g)
    simpa only [eJ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_subtype] using h1
  have hxK : (eJ.symm g : ↥K) = ⟨g, hg⟩ := Subtype.ext hxG
  calc ((((eJ.symm.trans (eC.trans eL)) g : ↥⁅L ⊓ Subgroup.centralizer
        ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X), L ⊓ Subgroup.centralizer
        ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X)⁆) : X))
      = ((eL (eC (eJ.symm g)) : ↥⁅L ⊓ Subgroup.centralizer
          ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X), L ⊓ Subgroup.centralizer
          ({((φ ⟨a, ha⟩ : ↥L) : X)} : Set X)⁆) : X) := rfl
    _ = (((eC (eJ.symm g) : ↥⁅Cl, Cl⁆) : ↥L) : X) := hvalL _
    _ = ((φ (eJ.symm g : ↥K) : ↥L) : X) := by rw [hval]
    _ = ((φ ⟨g, hg⟩ : ↥L) : X) := by rw [hxK]

theorem nineJ_simple_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    IsSimpleGroup ↥(nineJ K (B.b 2)) := by
  classical
  obtain ⟨φ, B', F, j, hB', hjinj, hj, heven, hU, hφB'⟩ :=
    exists_frame_coordinates_of_recOutTwD5 hstd hB hrec
  let i₂ : Fin 5 := 1
  let a : G := B.b i₂.succ
  have haK : a ∈ K := hB.2.2 _ (Fin.succ_ne_zero i₂)
  let x : ↥(orthDerived Q5) := φ ⟨a, haK⟩
  have hxval := phi_eq_or_eq_inv_frameRot hB' hj hφB' i₂ haK
  obtain ⟨hx3', hxU, hxfix⟩ := frameRot_facts_of_eq_or_eq_inv F (j i₂) hxval
  have hQ5 : (polarBilin Q5).Nondegenerate := nondegenerate_Q5
  have hUnd : PolarNondegOn Q5 (F.U (j i₂)) := fun u hu huv =>
    F.nondeg (j i₂) u hu fun v hv => by
      rw [polar_comm]
      exact huv v hv
  have hU2 : finrank (ZMod 2) (F.U (j i₂)) = 2 := hU (j i₂)
  have hUc : IsCompl (F.U (j i₂)) (perpOf Q5 (F.U (j i₂))) := isCompl_perp hUnd
  have hdimV : finrank (ZMod 2) V5 = 10 := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have hdimW : finrank (ZMod 2) (perpOf Q5 (F.U (j i₂))) = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hUc
    rw [hU2, hdimV] at this
    omega
  have hP : (polarBilin (Q5.restrict (perpOf Q5 (F.U (j i₂))))).Nondegenerate :=
    perp_polarBilin_nondegenerate hQ5 hUnd
  have hT : ∃ T : Submodule (ZMod 2) (perpOf Q5 (F.U (j i₂))), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q5.restrict (perpOf Q5 (F.U (j i₂)))) u = 0 :=
    perp_exists_ts_three hQ5 hUnd (by simp [hdimW])
  have hW6 : 6 ≤ finrank (ZMod 2) (perpOf Q5 (F.U (j i₂))) := by simp [hdimW]
  obtain ⟨eW⟩ := commutator_centralizer_equiv_orthDerived hQ5 hUnd hU2 hT hW6
    (show ((x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) ∈ orthDerived Q5 from x.2)
    hx3' hxU hxfix
  have hWsimple : IsSimpleGroup ↥(orthDerived (Q5.restrict (perpOf Q5 (F.U (j i₂))))) :=
    isSimpleGroup_orthDerived_of_ts hP hT
  have hCCsimple : IsSimpleGroup ↥⁅orthDerived Q5 ⊓ Subgroup.centralizer
      ({((x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5)} : Set (V5 ≃ₗ[ZMod 2] V5)),
        orthDerived Q5 ⊓ Subgroup.centralizer
          ({((x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5)} :
            Set (V5 ≃ₗ[ZMod 2] V5))⁆ := eW.isSimpleGroup
  obtain ⟨eJnine, -⟩ := exists_nineJ_equiv_commutator (φ := φ) (a := a) haK
  exact eJnine.isSimpleGroup

end CFSG.StandardType.FrameRoute.FS81

end
