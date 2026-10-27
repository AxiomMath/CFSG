module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ProofFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3BlockShape
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3BstarRank
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ZeroBlockCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Polynomial CoordSL CoordShape Multiplicative
  CFSG.RankThree.CALinearPlane

section Inputs

theorem two_le_dim_of_isUnit_rootMat_pow_sub {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {p : ℕ}
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1)) (hp1 : ¬ p ∣ 1) :
    2 ≤ (rootPB g).dim := by
  by_contra he
  have he1 : (rootPB g).dim = 1 := by have := rootPB_dim_pos g; omega
  have : Subsingleton (Fin (rootPB g).dim) := by rw [he1]; infer_instance
  have i0 : Fin (rootPB g).dim := ⟨0, by omega⟩
  have hu := hunit 1 hp1 (rootMat g i0 i0)
  have h0 : rootMat g ^ 1 - rootMat g i0 i0 •
      (1 : Matrix (Fin (rootPB g).dim) (Fin (rootPB g).dim) K) = 0 := by
    ext a b
    rw [Subsingleton.elim a i0, Subsingleton.elim b i0]
    simp
  rw [h0] at hu
  have : Nonempty (Fin (rootPB g).dim) := ⟨i0⟩
  exact not_isUnit_zero hu

theorem exists_a3_frame_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ}
    {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (hns : ¬ p ∣ 2 ^ f - 1) (hA : GGSixLSevenA3Case J) :
    ∃ (g : (GaloisField 2 f)[X]) (_ : Fact (Irreducible g)) (s r : ℕ)
      (ε : Fin (m + 1) ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))
      (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1) (_ : AdjoinRoot.root g ^ p = 1)
      (i j k l : Fin s), i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
        D ≤ Subgroup.closure {frameHom ψ A₀ ε hC hCp (ofAdd (Pi.single i 1)),
          frameHom ψ A₀ ε hC hCp (ofAdd (Pi.single j 1))} ∧
        frameHom ψ A₀ ε hC hCp (ofAdd (Pi.single k 1)) ∈ J ∧
        frameHom ψ A₀ ε hC hCp (ofAdd (Pi.single l 1)) ∈ J ∧
        m + 1 = 8 ∧ (rootPB g).dim = 2 ∧ s = 4 ∧ r = 0 ∧ Nat.card (GaloisField 2 f) = 2 := by
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hne : ¬ IsUnit (cyclotomic p (GaloisField 2 f)) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      degree_eq_natDegree (cyclotomic_ne_zero p (GaloisField 2 f)), natDegree_cyclotomic,
      Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p (GaloisField 2 f))
  have : Fact (Irreducible g) := ⟨hg⟩
  have hC : (rootMat g).det = 1 := det_rootMat hp hpF hpK hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK hgd
  have hprim := root_isPrimitiveRoot hp hpK hgd
  have hζ : AdjoinRoot.root g ^ p = 1 := hprim.pow_eq_one
  have hunit := isUnit_rootMat_pow_sub hp hpF hpK hgd
  obtain ⟨s, r, ε, A₀, hframe⟩ := ggA3_exists_frame_of_ctx hctx hns g hgd hC hCp
  have hs4 : 4 ≤ s := hctx.four_le_of_range_eq hframe
  obtain ⟨Q, hQ1, hQ2, hQN⟩ :=
    exists_isPGroup_two_normalized_by_frameHom hker A₀ ε hC hCp (by omega)
  have hBBs : B = Bs := hctx.eq_bstar_of_twoLocal hQ1 hQ2 (by rw [← hframe]; exact hQN)
  obtain ⟨A₁, hrange₁, hal⟩ := exists_jointAligned_frame (ψ := ψ) (A₀ := A₀) (ε := ε)
    (hC := hC) (hCp := hCp) hζ D
  have hframe₁ : (frameHom ψ A₁ ε hC hCp).range = Bs := hrange₁.trans hframe
  have hinj₁ : Function.Injective (frameHom ψ A₁ ε hC hCp) :=
    frameHom_injective ψ A₁ ε hC hCp hker (rootPB_dim_pos g) hunit
  have hDle : D ≤ (frameHom ψ A₁ ε hC hCp).range := hframe₁ ▸ hctx.d_le_bstar
  have hJcomp : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hctx.range_eq]
    exact hctx.j_isComponentOf_inf
  set T : Set (Fin s → ZMod p) := {t | frameHom ψ A₁ ε hC hCp (ofAdd t) ∈ D} with hTdef
  rcases eq_zeroBlock_or_classBlock_of_isComponentOf hp2 hpF hker hgd hDle hTdef hal hJcomp with
    hZ | ⟨j₀, -, hJC⟩
  ·
    classical
    haveI : NeZero p := ⟨hp.ne_zero⟩
    let Zs : Finset (Fin s) := Finset.univ.filter fun i => jointSupp T i = 0
    have hmemZs : ∀ i, i ∈ Zs ↔ ∀ t ∈ T, t i = 0 := fun i => by
      simp only [Zs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact jointSupp_eq_zero_iff
    have hrangeJ : ((SLRep.ggFrame ψ A₁).comp
        (blockSLOn (GaloisField 2 f) (zeroCoords ε (jointSupp T)))).range = J := by
      rw [MonoidHom.range_comp, range_blockSLOn, hZ]
    obtain ⟨hcZ, hK2⟩ := card_eq_four_of_range_eq _ hrangeJ hJcomp.2.2 hA
    rw [Fintype.card_fin] at hcZ
    have hcard1 : (zeroCoords ε (jointSupp T)).card = (rootPB g).dim * Zs.card + r :=
      card_zeroCoords ε (jointSupp T)
    have hss : s = Zs.card + 2 := by
      refine card_eq_add_two_of_eq_vanishing (frameHom ψ A₁ ε hC hCp) hinj₁ hDle hctx.card_d Zs
        (fun t ht i hi => (hmemZs i).mp hi t ht) fun t ht => ?_
      have hD' : D = B ⊓ Subgroup.centralizer (J : Set G) := hctx.stdSub.1.2.2.2.2.2.2
      show frameHom ψ A₁ ε hC hCp (ofAdd t) ∈ D
      rw [hD']
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      · rw [hBBs, ← hframe₁]
        exact ⟨_, rfl⟩
      · rw [hZ] at hy
        obtain ⟨M, hM, rfl⟩ := hy
        rw [frameHom_eq_ggFrame (ψ := ψ) (A₀ := A₁) (ε := ε) (hC := hC) (hCp := hCp), ← map_mul,
          ← map_mul]
        congr 1
        refine (comm_zeroBlock_of_torus (k := fun i => (t i).val) (fun i hi => ?_) hM).symm
        have hiZ : i ∈ Zs := by simp [Zs, hi]
        rw [ht i hiZ, ZMod.val_zero]
    have hdim : 2 ≤ (rootPB g).dim := two_le_dim_of_isUnit_rootMat_pow_sub hunit hp.not_dvd_one
    have hz2 : 2 ≤ Zs.card := by omega
    have hee : (rootPB g).dim = 2 := by nlinarith
    have hzz : Zs.card = 2 := by nlinarith
    have hrr : r = 0 := by nlinarith
    have hs4' : s = 4 := by omega
    have hn : m + 1 = (rootPB g).dim * s + r := by
      have := Fintype.card_congr ε
      simpa [Fintype.card_sum, Fintype.card_prod] using this
    have hn8 : m + 1 = 8 := by rw [hn, hee, hs4', hrr]
    obtain ⟨k, l, hkl, hZsKL⟩ := Finset.card_eq_two.mp hzz
    have hcompl : Zsᶜ.card = 2 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨i, j, hij, hZsIJ⟩ := Finset.card_eq_two.mp hcompl
    have hkZ : k ∈ Zs := by rw [hZsKL]; simp
    have hlZ : l ∈ Zs := by rw [hZsKL]; simp
    have hiZ : i ∉ Zs := by
      have : i ∈ Zsᶜ := by rw [hZsIJ]; simp
      simpa using this
    have hjZ : j ∉ Zs := by
      have : j ∈ Zsᶜ := by rw [hZsIJ]; simp
      simpa using this
    have hmemJ : ∀ k ∈ Zs, frameHom ψ A₁ ε hC hCp (ofAdd (Pi.single k 1)) ∈ J := by
      intro k hk
      rw [hZ, frameHom_eq_ggFrame (ψ := ψ) (A₀ := A₁) (ε := ε) (hC := hC) (hCp := hCp)]
      refine ⟨_, nsSL_mem_zeroBlock (fun i hi => ?_), rfl⟩
      by_cases hik : i = k
      · exfalso
        subst hik
        exact hi (Finset.mem_filter.mp hk).2
      · simp [Pi.single_apply, hik]
    refine ⟨g, inferInstance, s, r, ε, A₁, hC, hCp, hζ, i, j, k, l, hij,
      fun h => hiZ (h ▸ hkZ), fun h => hiZ (h ▸ hlZ), fun h => hjZ (h ▸ hkZ),
      fun h => hjZ (h ▸ hlZ), hkl, ?_, hmemJ k hkZ, hmemJ l hlZ, hn8, hee, hs4', hrr, hK2⟩
    intro d hd
    obtain ⟨u, rfl⟩ := hDle hd
    have hu : toAdd u ∈ T := by
      show frameHom ψ A₁ ε hC hCp (ofAdd (toAdd u)) ∈ D
      rwa [ofAdd_toAdd]
    have h := mem_closure_pair_of_forall_eq_zero (frameHom ψ A₁ ε hC hCp) hij (toAdd u)
      fun k' hki hkj => by
        refine (hmemZs k').mp ?_ _ hu
        by_contra hk'
        have : k' ∈ Zsᶜ := by simpa using hk'
        rw [hZsIJ] at this
        simp at this
        rcases this with rfl | rfl
        · exact hki rfl
        · exact hkj rfl
    rwa [ofAdd_toAdd] at h
  ·
    exfalso
    haveI : CharP (AdjoinRoot g) 2 :=
      charP_of_injective_algebraMap (algebraMap (GaloisField 2 f) (AdjoinRoot g)).injective 2
    haveI : Finite (AdjoinRoot g) := finite_adjoinRoot
    set X := classSet (jointClass T j₀) 1 with hX
    have hrange : (((SLRep.ggFrame ψ A₁).comp (theta g ε)).comp
        (blockSLOn (AdjoinRoot g) X)).range = J := by
      rw [MonoidHom.range_comp, range_blockSLOn, hJC, Subgroup.map_map]
    obtain ⟨-, hL⟩ := card_eq_four_of_range_eq _ hrange hJcomp.2.2 hA
    have h4 := four_le_natCard_adjoinRoot hprim hp3
    omega

end Inputs

end CFSG.StandardType
