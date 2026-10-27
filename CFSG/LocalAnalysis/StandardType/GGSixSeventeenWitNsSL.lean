module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitNsFixed
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestDefs

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

namespace WitNs

open CoordSL Multiplicative

theorem fixS_anti {n e s r : ℕ} (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {T T' : Finset (Fin s)}
    (h : T ⊆ T') : SLNS.fixS ε T' ⊆ SLNS.fixS ε T := by
  intro x hx
  rw [SLNS.mem_fixS] at hx ⊢
  intro hT
  apply hx
  rcases hε : ε x with ⟨a, i⟩ | j
  · rw [hε] at hT
    simp only [SLNS.inT, Sum.elim_inl] at hT ⊢
    exact h hT
  · rw [hε] at hT
    exact hT.elim

section Frame

variable {G : Type} [Group G] {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [NeZero p] {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}

omit [NeZero p] in
theorem two_le_dim (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    (hp1 : ¬ p ∣ 1) : 2 ≤ (rootPB g).dim := by
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

theorem eq_zero_of_mem_zeroBlock
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    {β : Fin s → ZMod p} (hβ : ∀ i, β i ≠ 0) {u : Fin s → ZMod p}
    (h : frameHom ψ A₀ ε hC hCp (ofAdd u) ∈
      (coordBlockSL K (zeroCoords ε β)).map (SLRep.ggFrame ψ A₀)) : u = 0 := by
  classical
  obtain ⟨M, hM, hMe⟩ := h
  set Y := SLNS.nsSL ε hC (fun i => (u i).val) with hY
  have hz : M⁻¹ * Y ∈ (SLRep.ggFrame ψ A₀).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hMe, frameHom_eq_ggFrame, inv_mul_cancel]
  obtain ⟨c, -, hc⟩ :=
    Matrix.SpecialLinearGroup.mem_center_iff.mp (SLRep.ker_ggFrame_le hker A₀ hz)
  have hYM : (Y : Matrix (Fin n) (Fin n) K) =
      (M : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) c := by
    rw [hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  funext i
  by_contra hui
  have hdvd : ¬ p ∣ (u i).val := fun h => hui (by
    rw [Pi.zero_apply, ← ZMod.natCast_zmod_val (u i), (ZMod.natCast_eq_zero_iff _ _).mpr h])
  have hblock : rootMat g ^ (u i).val = c • (1 : Matrix (Fin (rootPB g).dim)
      (Fin (rootPB g).dim) K) := by
    ext a a'
    have h1 := congrFun (congrFun hYM (ε.symm (Sum.inl (a, i)))) (ε.symm (Sum.inl (a', i)))
    have hx : ε.symm (Sum.inl (a, i)) ∉ zeroCoords ε β := by
      rw [mem_zeroCoords_inl (Equiv.apply_symm_apply ε _)]
      exact hβ i
    have hM1 := mem_coordBlockSL_iff.mp hM _ (ε.symm (Sum.inl (a', i))) (Or.inl hx)
    change SLNS.nsMat ε (rootMat g) (fun i => (u i).val) _ _ = _ at h1
    rw [SLNS.nsMat_block, Matrix.scalar_apply, Matrix.mul_diagonal, hM1] at h1
    rw [h1, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases haa : a = a'
    · subst haa
      simp
    · have hne : ε.symm (Sum.inl (a, i)) ≠ ε.symm (Sum.inl (a', i)) := fun h =>
        haa (congrArg Prod.fst (Sum.inl_injective (ε.symm.injective h)))
      simp [hne, haa]
  have hu := hunit _ hdvd c
  rw [hblock, sub_self] at hu
  have : Nonempty (Fin (rootPB g).dim) := ⟨⟨0, rootPB_dim_pos g⟩⟩
  exact not_isUnit_zero hu

end Frame

end WitNs

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CoordSL Multiplicative

section Inputs

theorem ggSixSeventeenWitnessOn_PSLNonsplit : GGSixSeventeenWitnessOn GGPSLNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  obtain ⟨rfl, hns⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
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
  have hζ : AdjoinRoot.root g ^ p = 1 := (root_isPrimitiveRoot hp hpK hgd).pow_eq_one
  have hunit := isUnit_rootMat_pow_sub hp hpF hpK hgd
  have hnsplit : ∀ c : GaloisField 2 f, c ^ p = 1 → c = 1 := fun c hc =>
    OrdPNS.eq_one_of_pow_eq_one hp hpF hc
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame_of_ctx hctx s1 hns g hgd hC
  have hrange : (frameHom ψ A₀ ε hC hCp).range = Bs :=
    range_frameHom ψ A₀ ε hC hCp hctx.bstar hframe
  have hker : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hG₀ : ψ.range = ggG0 p B x L D J := hctx.range_eq
  obtain ⟨hb, -, hcomp, -⟩ := hpair
  have hcomp₀ := hcomp
  have hb' := hb
  rw [← hrange] at hb'
  obtain ⟨β₀, rfl⟩ := hb'
  obtain ⟨A₁, η, hal, hι', hrange'⟩ :=
    WitNs.exists_aligned_frame (ψ := ψ) (A₀ := A₀) (ε := ε) (hC := hC) (hCp := hCp) hζ
      (toAdd β₀)
  set β : Fin s → ZMod p := fun i => (η i : ZMod p) * toAdd β₀ i with hβdef
  have hbβ : frameHom ψ A₁ ε hC hCp (ofAdd β) = frameHom ψ A₀ ε hC hCp β₀ := by
    rw [hι', ofAdd_toAdd]
  have hrange₁ : (frameHom ψ A₁ ε hC hCp).range = Bs := hrange'.trans hrange
  have hc₁ : SLNS.NSCtx ε hC p B Bs (ggG0 p B x L D J) ψ A₁ :=
    ⟨hctx.bstar, hker, hG₀, s1.1, hp, hnsplit, hCp, hunit, fun y hy => by
      rw [← hrange₁] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨fun i => (toAdd a i).val, rfl⟩⟩
  have hinj₁ : Function.Injective (frameHom ψ A₁ ε hC hCp) :=
    frameHom_injective ψ A₁ ε hC hCp hker (rootPB_dim_pos g) hunit
  have hmem₁ : ∀ u : Fin s → ZMod p, frameHom ψ A₁ ε hC hCp (ofAdd u) ∈ Bs := fun u =>
    hrange₁ ▸ ⟨_, rfl⟩
  have hne₁ : ∀ u : Fin s → ZMod p, u ≠ 0 → frameHom ψ A₁ ε hC hCp (ofAdd u) ≠ 1 :=
    fun u hu h => hu (ofAdd_eq_one.mp (hinj₁ (h.trans (map_one _).symm)))
  have hβ' := hctx.1.2.2.2.2.2.1
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ'.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hs4 : 4 ≤ s := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hc₁.card_bstar_le)
  have he2 : 2 ≤ (rootPB g).dim := WitNs.two_le_dim hunit (Nat.Prime.not_dvd_one hp)
  have hn : m + 1 = (rootPB g).dim * s + r := by
    have := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, mul_comm] using this
  have hse : 4 * (rootPB g).dim ≤ (rootPB g).dim * s := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hs4
  rw [← hbβ, ← hG₀] at hcomp
  rcases WitNs.eq_block_of_aligned hp2 hpF hker hgd hal hcomp with hZ | ⟨c, hc0, hS2, hcl⟩
  · by_cases hZe : ∃ i₀, β i₀ = 0
    ·
      obtain ⟨i₀, hi₀⟩ := hZe
      set t : Fin s → ZMod p := Pi.single i₀ 1 with htdef
      have ht0 : t ≠ 0 := fun h =>
        (one_ne_zero : (1 : ZMod p) ≠ 0) (by simpa [htdef] using congrFun h i₀)
      have hsupp : WitNs.supp t ⊆ {i₀} := fun i hi => by
        rw [WitNs.mem_supp] at hi
        rw [Finset.mem_singleton]
        by_contra hne
        exact hi (by simp [htdef, hne])
      have heL : frameHom ψ A₁ ε hC hCp (ofAdd t) ∈ L₁ := by
        rw [hZ]
        refine ⟨_, nsSL_mem_zeroBlock fun i hi => ?_, rfl⟩
        have hne : i ≠ i₀ := fun h => hi (h ▸ hi₀)
        simp [htdef, hne]
      have h3 : 3 ≤ (SLNS.fixS ε (WitNs.supp t)).card := by
        refine le_trans ?_ (Finset.card_le_card (WitNs.fixS_anti ε hsupp))
        rw [SLNS.card_fixS_single]
        omega
      obtain ⟨L₂, hL₂, hcard⟩ := WitNs.exists_comp_of_supp_le_two hp2 hpF hgd hζ hc₁ hrange₁ ht0
        ((Finset.card_le_card hsupp).trans (by simp)) h3
      exact Or.inr ⟨_, heL, Or.inl ⟨hmem₁ t, hne₁ t ht0, Or.inr ⟨L₂, hL₂, hcard⟩⟩⟩
    ·
      exfalso
      push Not at hZe
      have hLB : ∀ y ∈ Bs, ∀ l ∈ L₁, y * l = l * y := by
        intro y hy l hl
        rw [← hrange₁] at hy
        obtain ⟨a, rfl⟩ := hy
        rw [hZ] at hl
        obtain ⟨M, hM, rfl⟩ := hl
        show SLRep.ggFrame ψ A₁ (SLNS.nsSL ε hC fun i => (toAdd a i).val) * _ =
          _ * SLRep.ggFrame ψ A₁ (SLNS.nsSL ε hC fun i => (toAdd a i).val)
        rw [← map_mul, ← map_mul, comm_zeroBlock_of_torus (fun i hi => absurd hi (hZe i)) hM]
      have hpL : ¬ p ∣ Nat.card L₁ := by
        intro hdvd
        obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥L₁) p hdvd
        have hok : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe, hw]
        have hwp : (w : G) ^ p = 1 := hok ▸ pow_orderOf_eq_one _
        have hwBs : (w : G) ∈ Bs := hctx.bstar.2.2.2 _
          (Subgroup.mem_centralizer_iff.mpr fun y hy => hLB y hy w w.2) hwp
        rw [← hrange₁] at hwBs
        obtain ⟨u, hu⟩ := hwBs
        have hwL : frameHom ψ A₁ ε hC hCp (ofAdd (toAdd u)) ∈
            (coordBlockSL (GaloisField 2 f) (zeroCoords ε β)).map (SLRep.ggFrame ψ A₁) := by
          rw [ofAdd_toAdd, hu, ← hZ]
          exact w.2
        have hu0 := WitNs.eq_zero_of_mem_zeroBlock hker hunit hZe hwL
        have hw1 : (w : G) = 1 := by rw [← hu, ← ofAdd_toAdd u, hu0, ofAdd_zero, map_one]
        have h1 : orderOf (w : G) = 1 := by rw [hw1, orderOf_one]
        exact hp.one_lt.ne' (hok.symm.trans h1)
      exact hpL (WitNs.dvd_card_of_isComponentOf_PSL hctx hb hcomp₀)
  ·
    obtain ⟨j, hj, j', hj', hjj⟩ := Finset.one_lt_card.mp (show 1 < (classSet β c).card by omega)
    set t : Fin s → ZMod p := Pi.single j 1 - Pi.single j' 1 with htdef
    have htj : t j = 1 := by simp [htdef, hjj]
    have ht0 : t ≠ 0 := fun h => (one_ne_zero : (1 : ZMod p) ≠ 0) (htj.symm.trans (congrFun h j))
    have hsupp : WitNs.supp t ⊆ {j, j'} := fun i hi => by
      rw [WitNs.mem_supp] at hi
      by_contra hne
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
      exact hi (by simp [htdef, hne.1, hne.2])
    have hsupp' : ∀ i, β i ≠ c → t i = 0 := fun i hi => by
      have h1 : i ≠ j := fun h => hi (h ▸ mem_classSet.mp hj)
      have h2 : i ≠ j' := fun h => hi (h ▸ mem_classSet.mp hj')
      simp [htdef, h1, h2]
    have hsum : ∑ i, t i = 0 := by
      rw [Fintype.sum_eq_add j j' hjj fun i hi => by simp [htdef, hi.1, hi.2]]
      simp only [htdef, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjj,
        Pi.single_eq_of_ne (Ne.symm hjj)]
      ring
    obtain ⟨Dm, hDm, hθD⟩ := diag_mem_classBlock (ε := ε) (hC := hC) hζ hsupp' hsum
    have heL : frameHom ψ A₁ ε hC hCp (ofAdd t) ∈ L₁ := by
      rw [hcl]
      exact ⟨theta g ε Dm, ⟨Dm, hDm, rfl⟩, congrArg (SLRep.ggFrame ψ A₁) hθD⟩
    have h3 : 3 ≤ (SLNS.fixS ε (WitNs.supp t)).card := by
      refine le_trans ?_ (Finset.card_le_card (WitNs.fixS_anti ε hsupp))
      rw [SLNS.card_fixS_pair hjj]
      omega
    obtain ⟨L₂, hL₂, hcard⟩ := WitNs.exists_comp_of_supp_le_two hp2 hpF hgd hζ hc₁ hrange₁ ht0
      ((Finset.card_le_card hsupp).trans (Finset.card_le_two)) h3
    exact Or.inr ⟨_, heL, Or.inl ⟨hmem₁ t, hne₁ t ht0, Or.inr ⟨L₂, hL₂, hcard⟩⟩⟩

end Inputs

end CFSG.StandardType
