module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinFrameStatements
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwo
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
import CFSG.Assembly.GL83LieDefs

public section

open Polynomial

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.LinBlocks

private noncomputable def ec2 (t : ℕ) : Fin 2 × Fin t ≃ Fin t ⊕ Fin t where
  toFun p := WitSpNs.coord p.1 p.2
  invFun x := (WitSpNs.side x, WitSpNs.plane x)
  left_inv p := by
    ext <;> simp
  right_inv x := by
    apply WitSpNs.eq_of_plane_side <;> simp

@[simp] private theorem ec2_symm_inl (t : ℕ) (i : Fin t) :
    (ec2 t).symm (Sum.inl i) = (0, i) := rfl

@[simp] private theorem ec2_symm_inr (t : ℕ) (i : Fin t) :
    (ec2 t).symm (Sum.inr i) = (1, i) := rfl

private noncomputable def frameCoordEquiv {K : Type} [Field K] {g : Polynomial K} [Fact (Irreducible g)]
    (he0 : (CoordSL.rootPB g).dim = 2) (t : ℕ) :
    Fin (CoordSL.rootPB g).dim × Fin t ≃ Fin t ⊕ Fin t :=
  (Equiv.prodCongr (finCongr he0) (Equiv.refl (Fin t))).trans (ec2 t)

private theorem reindex_nsMat_eq_planeExtMat {K : Type} [Field K] [Finite K] {g : Polynomial K}
    [Fact (Irreducible g)] (he0 : (CoordSL.rootPB g).dim = 2) {d t r : ℕ} (ε : Fin 2)
    (εf : Fin d ≃ (Fin (CoordSL.rootPB g).dim × Fin t) ⊕ Fin r) (hrt : r = ε.val)
    (k : Fin t → ℕ) :
    Matrix.reindex (εf.trans (Equiv.sumCongr (frameCoordEquiv he0 t) (finCongr hrt)))
        (εf.trans (Equiv.sumCongr (frameCoordEquiv he0 t) (finCongr hrt)))
        (SLNS.nsMat εf (CoordSL.rootMat g) k) =
      planeExtMat t ε (WitSpNs.planeMat
        (fun i => (Matrix.reindex (finCongr he0) (finCongr he0)
          (CoordSL.rootMat g)) ^ k i)) := by
  classical
  let e2 : Fin (CoordSL.rootPB g).dim ≃ Fin 2 := finCongr he0
  let ec : Fin (CoordSL.rootPB g).dim × Fin t ≃ Fin t ⊕ Fin t := frameCoordEquiv he0 t
  let eIdx : Fin d ≃ LinIdx t ε := εf.trans (Equiv.sumCongr ec (finCongr hrt))
  let M0 : Matrix (Fin 2) (Fin 2) K := (Matrix.reindexAlgEquiv K K e2) (CoordSL.rootMat g)
  have hM0 : ∀ n, M0 ^ n = Matrix.reindex e2 e2 (CoordSL.rootMat g ^ n) := fun n => by
    change ((Matrix.reindexAlgEquiv K K e2) (CoordSL.rootMat g)) ^ n = _
    rw [← map_pow]
    rfl
  change Matrix.reindex eIdx eIdx (SLNS.nsMat εf (CoordSL.rootMat g) k) =
      planeExtMat t ε (WitSpNs.planeMat (fun i => M0 ^ k i))
  rw [show (fun i => M0 ^ k i) = fun i => Matrix.reindex e2 e2 (CoordSL.rootMat g ^ k i) from
    funext fun i => hM0 (k i)]
  ext x y
  rcases x with (i | i) | j <;> rcases y with (i' | i') | j'
  all_goals
    simp [eIdx, ec, frameCoordEquiv, e2, Matrix.reindex_apply, SLNS.nsMat, SLNS.nsCore,
      Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
      Matrix.blockDiagonal_apply, planeExtMat, WitSpNs.planeMat_apply, Matrix.one_apply,
      Fin.cast_inj]
    try (split_ifs with h <;> simp_all)

theorem existsLinFrame_of_cardEEq (h : LinCardEEq) : ExistsLinFrame := by
  intro G _ _ H E r t ε K _ _ _ θ h2t hK hHp hEab hEN hI hSC hC3 h33
  classical
  have hcardE : Nat.card E = 3 ^ t := h θ h2t hK hHp hEab hEN hI hSC hC3 h33
  have ht3 : 3 ≤ t := by
    have h1 : 3 ^ 3 ≤ 3 ^ t := by rwa [← hcardE]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
  have hd : 6 ≤ r + 1 := by
    have hε : ε.val ≤ 1 := by have := ε.isLt; omega
    omega
  have hkerGamma : (ggGamma H hEN).ker = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff] at hb
    have hb3 : (⟨(b : G), hb⟩ : ↥(Subgroup.centralizer (H : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      exact hEab.2 (b : G) b.2
    have hord : orderOf (⟨(b : G), hb⟩ : ↥(Subgroup.centralizer (H : Set G))) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hb3
    have hdiv : orderOf (⟨(b : G), hb⟩ : ↥(Subgroup.centralizer (H : Set G))) ∣
        Nat.card ↥(Subgroup.centralizer (H : Set G)) := orderOf_dvd_natCard _
    have hone : orderOf (⟨(b : G), hb⟩ : ↥(Subgroup.centralizer (H : Set G))) = 1 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hord with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hdiv) hC3
    have hb1 : (⟨(b : G), hb⟩ : ↥(Subgroup.centralizer (H : Set G))) = 1 :=
      orderOf_eq_one_iff.mp hone
    exact Subtype.ext (congrArg (fun x : ↥(Subgroup.centralizer (H : Set G)) => (x : G)) hb1)
  have hγinj : Function.Injective (ggGamma H hEN) := by
    rwa [← MonoidHom.ker_eq_bot_iff]
  let A : Subgroup (MulAut ↥H) := (ggGamma H hEN).range
  let eE : ↥E ≃* A := MonoidHom.ofInjective hγinj
  have hcardA : Nat.card A = Nat.card E := (Nat.card_congr eE.toEquiv).symm
  have hBp : ∀ b : ↥E, b ^ 3 = 1 := fun b =>
    Subtype.ext (by simpa using hEab.2 (b : G) b.2)
  have hBc : ∀ a b : ↥E, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hEab a.2 b.2)
  have hA : IsElemAbelian 3 A := by
    rw [show A = (ggGamma H hEN).range from rfl]
    exact isElemAbelian_range hBc hBp (ggGamma H hEN)
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ,
      ∀ l : ↥H, x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta H θ hEN b, hI b b.2, fun l => ggBeta_ggQuotHom H hEN θ b l⟩
  have hrA : 3 ^ ((r + 1) / 2) ≤ Nat.card A := by
    have hdt : (r + 1) / 2 = t := by omega
    rw [hdt, hcardA, hcardE]
  obtain ⟨φ₀, g, hg, s, r', εf, A₀, hC, hCp, hfr⟩ :=
    exists_frame_of_recipe (d := r + 1) hK hd (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hHp A hA hAI hrA
  let : Fact (Irreducible g) := hg
  have hp3K : (3 : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hpq3 : 3 ∣ Nat.card K + 1 := by
    rw [hK]
  have he0 : (CoordSL.rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) hp3K hfr.gd hpq3
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hunit : ∀ j : ℕ, ¬ 3 ∣ j → ∀ c : K, IsUnit (CoordSL.rootMat g ^ j - c • 1) :=
    fun j hj c => CoordSL.isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3K hfr.gd j hj c
  let ι : (Fin s → Multiplicative (ZMod 3)) →* ↥H :=
    CoordSL.frameHom φ₀ A₀ εf hC hCp
  have hφ0ker : φ₀.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [hfr.bij.1 (hx.trans (map_one φ₀).symm)]
    exact Subgroup.one_mem _
  have hιinj : Function.Injective ι :=
    CoordSL.frameHom_injective φ₀ A₀ εf hC hCp hφ0ker (by rw [he0]; norm_num) hunit
  have hcardι : Nat.card ι.range = 3 ^ s := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hAeq : A = ι.range.map (MulAut.conj : ↥H →* MulAut ↥H) := by
    ext a
    rw [hfr.mem_A a]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨ι (Multiplicative.ofAdd u), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  have hcardA3 : Nat.card A = 3 ^ s := by
    rw [hAeq, Subgroup.card_map_of_injective hfr.conj_inj, hcardι]
  have hs : s = t := by
    have h1 : 3 ^ s = 3 ^ t := by rw [← hcardA3, hcardA, hcardE]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hcardd : r + 1 = 2 * s + r' := by
    have h := Fintype.card_congr εf
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h
    rw [he0] at h
    omega
  have hrt : r' = ε.val := by omega
  subst s
  subst r'
  let e2 : Fin (CoordSL.rootPB g).dim ≃ Fin 2 := finCongr he0
  let R0 : Matrix (Fin (CoordSL.rootPB g).dim) (Fin (CoordSL.rootPB g).dim) K ≃ₐ[K]
      Matrix (Fin 2) (Fin 2) K := Matrix.reindexAlgEquiv K K e2
  let M0m : Matrix (Fin 2) (Fin 2) K := R0 (CoordSL.rootMat g)
  have hM0det : M0m.det = 1 := by
    change ((Matrix.reindex e2 e2) (CoordSL.rootMat g)).det = 1
    rw [Matrix.det_reindex_self, hC]
  have hM0powm : M0m ^ 3 = 1 := by
    change (R0 (CoordSL.rootMat g)) ^ 3 = 1
    rw [← map_pow, hCp, map_one]
  let M0 : SpecialLinearGroup (Fin 2) K := ⟨M0m, hM0det⟩
  have hM0pow : M0 ^ 3 = 1 := Subtype.ext hM0powm
  have hroot_ne : AdjoinRoot.root g ≠ 1 :=
    (CoordSL.root_isPrimitiveRoot Nat.prime_three hp3K hfr.gd).ne_one (by norm_num)
  have hrootMat_ne : CoordSL.rootMat g ≠ 1 := by
    intro h1
    apply hroot_ne
    apply Algebra.leftMulMatrix_injective (CoordSL.rootPB g).basis
    rw [← CoordSL.rootMat, h1, map_one]
  have hM0ne : M0m ≠ 1 := by
    intro h1
    apply hrootMat_ne
    have h2 : R0 (CoordSL.rootMat g) = R0 1 := by
      rw [show R0 (CoordSL.rootMat g) = M0m from rfl, h1, map_one]
    exact R0.injective h2
  have hM0ne' : M0 ≠ 1 := fun h1 => hM0ne (congrArg Subtype.val h1)
  let ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K :=
    TableBSymp.zmodPowHom hM0pow
  have hζne : ζ ≠ 1 := by
    intro h1
    apply hM0ne'
    have h2 := congrArg (fun f => f (Multiplicative.ofAdd (1 : ZMod 3))) h1
    change TableBSymp.zmodPowHom hM0pow (Multiplicative.ofAdd (1 : ZMod 3)) = 1 at h2
    rw [TableBSymp.zmodPowHom_apply] at h2
    change M0 ^ ((1 : ZMod 3).val) = 1 at h2
    have hv : (1 : ZMod 3).val = 1 := by decide
    rw [hv, pow_one] at h2
    exact h2
  have hζinj : Function.Injective ζ := by
    have hprimeD : Nat.Prime (Nat.card (Multiplicative (ZMod 3))) := by
      simpa using Nat.prime_three
    let : Fact (Nat.Prime (Nat.card (Multiplicative (ZMod 3)))) := ⟨hprimeD⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (MonoidHom.ker ζ) with hbot | htop
    · rwa [MonoidHom.ker_eq_bot_iff] at hbot
    · exfalso
      have hζ1 : ζ = 1 := by
        apply MonoidHom.ext
        intro a
        have ha : a ∈ (MonoidHom.ker ζ) := by
          rw [htop]
          exact Subgroup.mem_top a
        simpa [MonoidHom.mem_ker] using ha
      exact hζne hζ1
  let ec : Fin (CoordSL.rootPB g).dim × Fin t ≃ Fin t ⊕ Fin t := frameCoordEquiv he0 t
  let eIdx : Fin (r + 1) ≃ LinIdx t ε := εf.trans (Equiv.sumCongr ec (Equiv.refl (Fin ε.val)))
  let ρ : GL (Fin (r + 1)) K ≃* GL (LinIdx t ε) K :=
    Units.mapEquiv (Matrix.reindexAlgEquiv K K eIdx).toRingEquiv.toMulEquiv
  let Ψ : SpecialLinearGroup (Fin (r + 1)) K →* GL (LinIdx t ε) K :=
    ρ.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
  let φ₀e : SpecialLinearGroup (Fin (r + 1)) K ≃* ↥H := MulEquiv.ofBijective φ₀ hfr.bij
  let C : GL (LinIdx t ε) K := Ψ A₀
  let π : ↥H →* GL (LinIdx t ε) K :=
    (MulAut.conj C⁻¹).toMonoidHom.comp (Ψ.comp φ₀e.symm)
  have hρinj : Function.Injective ρ := ρ.injective
  have hΨsurj : Function.Surjective Ψ := by
    intro g
    refine ⟨TwoThree.toSLHom hK (ρ.symm g), ?_⟩
    change ρ (SpecialLinearGroup.toGL (TwoThree.toSLHom hK (ρ.symm g))) = g
    rw [TwoThree.toGL_toSLHom, ρ.apply_symm_apply]
  have hπsurj : Function.Surjective π :=
    (MulAut.conj C⁻¹).surjective.comp (hΨsurj.comp φ₀e.symm.surjective)
  have hπker : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have h1 : C⁻¹ * Ψ (φ₀e.symm h) * C = 1 := by simpa [π] using hh
    have h2 : Ψ (φ₀e.symm h) = 1 := by
      calc Ψ (φ₀e.symm h) = C * (C⁻¹ * Ψ (φ₀e.symm h) * C) * C⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h3 : φ₀e.symm h = 1 := by
      have h3' : ρ (SpecialLinearGroup.toGL (φ₀e.symm h)) = ρ (SpecialLinearGroup.toGL 1) := by
        simpa [Ψ] using h2
      have h3'' := hρinj h3'
      exact SpecialLinearGroup.toGL_injective h3''
    have h4 : h = 1 := by
      have := congrArg φ₀e h3
      simpa using this
    rw [h4]
    exact Subgroup.one_mem _
  have hΨns : ∀ u : Fin t → Multiplicative (ZMod 3),
      Ψ (SLNS.nsSL εf hC (fun i => (Multiplicative.toAdd (u i)).val)) =
        linTorus ζ t ε u := by
    intro u
    apply Units.ext
    have hmat := reindex_nsMat_eq_planeExtMat (he0 := he0) (ε := ε) (εf := εf) (hrt := rfl)
      (k := fun i => (Multiplicative.toAdd (u i)).val)
    have hleft : ((Ψ (SLNS.nsSL εf hC
        (fun i => (Multiplicative.toAdd (u i)).val)) : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) =
        Matrix.reindex eIdx eIdx (SLNS.nsMat εf (CoordSL.rootMat g)
          (fun i => (Multiplicative.toAdd (u i)).val)) := rfl
    rw [hleft]
    have hmat' : Matrix.reindex eIdx eIdx (SLNS.nsMat εf (CoordSL.rootMat g)
        (fun i => (Multiplicative.toAdd (u i)).val)) =
        planeExtMat t ε (WitSpNs.planeMat
          (fun i => (Matrix.reindex (finCongr he0) (finCongr he0)
            (CoordSL.rootMat g)) ^ (Multiplicative.toAdd (u i)).val)) := by
      simpa [eIdx, ec] using hmat
    rw [hmat']
    have hlin : ((linTorus ζ t ε u : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) =
        planeExtMat t ε (WitSpNs.planeMat
          (fun i => ((ζ (u i) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K))) := by
      change planeExtMat t ε ((((SpJoin.spPlaneTorus t ζ) u : CFSG.Open.StatedSp t K) :
        GL (Fin t ⊕ Fin t) K) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) = _
      rw [TorC.coe_spPlaneTorus]
    rw [hlin]
    congr 1
    exact congrArg WitSpNs.planeMat (by
      funext i
      have hu : u i = Multiplicative.ofAdd (Multiplicative.toAdd (u i)) :=
        (ofAdd_toAdd (u i)).symm
      rw [hu, TableBSymp.zmodPowHom_apply]
      rfl)
  let fι : (Fin t → Multiplicative (ZMod 3)) →* A :=
    { toFun := fun u => ⟨MulAut.conj (ι u), by
        rw [hfr.mem_A]
        exact ⟨Multiplicative.toAdd u, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        change MulAut.conj (ι (u * v)) = MulAut.conj (ι u) * MulAut.conj (ι v)
        rw [map_mul, map_mul] }
  have hfι : Function.Bijective fι := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      apply hιinj
      apply hfr.conj_inj
      exact congrArg Subtype.val huv
    · rintro ⟨a, ha⟩
      rw [hfr.mem_A] at ha
      obtain ⟨u, rfl⟩ := ha
      exact ⟨fun i => Multiplicative.ofAdd (u i), rfl⟩
  let eι : (Fin t → Multiplicative (ZMod 3)) ≃* A := MulEquiv.ofBijective fι hfι
  let τ : (Fin t → Multiplicative (ZMod 3)) ≃* ↥E := eι.trans eE.symm
  have hτ : ∀ u : Fin t → Multiplicative (ZMod 3),
      ggGamma H hEN (τ u) = MulAut.conj (ι u) := by
    intro u
    have h1 : eE (τ u) = eι u := by
      change eE (eE.symm (eι u)) = eι u
      rw [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1
  refine ⟨ζ, hζinj, hcardE, ⟨{
    π := π
    surj := hπsurj
    ker_le := by rw [hπker]; exact bot_le
    τ := τ
    intertwine := ?_ }⟩⟩
  intro u h
  have hb : H.normalizerMonoidHom ⟨((τ u : ↥E) : G), hEN (τ u).2⟩ h =
      ι u * h * (ι u)⁻¹ := by
    apply Subtype.ext
    have h1 := congrArg (fun f : MulAut ↥H => f h) (hτ u)
    have h1' : ((ggGamma H hEN (τ u)) h : G) = ((MulAut.conj (ι u)) h : G) :=
      congrArg (fun x : ↥H => (x : G)) h1
    rw [ggGamma_coe, MulAut.conj_apply] at h1'
    simpa using h1'
  rw [hb, map_mul, map_mul, map_inv]
  have hπι : π (ι u) = linTorus ζ t ε u := by
    let k : Fin t → ℕ := fun i => (Multiplicative.toAdd (u i)).val
    have hu : u = fun i => Multiplicative.ofAdd (Multiplicative.toAdd (u i)) := by
      funext i
      exact (ofAdd_toAdd (u i)).symm
    have hιu : ι u = φ₀ (A₀ * SLNS.nsSL εf hC
        (fun i => (Multiplicative.toAdd (u i)).val) * A₀⁻¹) := by
      rw [hu]
      change CoordSL.frameHom φ₀ A₀ εf hC hCp
        (Multiplicative.ofAdd (fun i => Multiplicative.toAdd (u i))) =
        φ₀ (A₀ * SLNS.nsSL εf hC (fun i => (Multiplicative.toAdd (u i)).val) * A₀⁻¹)
      rw [CoordSL.frameHom_apply]
    have hframe : φ₀ (A₀ * SLNS.nsSL εf hC k * A₀⁻¹) = ι u :=
      hιu.symm
    have h1 : φ₀e.symm (ι u) = A₀ * SLNS.nsSL εf hC k * A₀⁻¹ := by
      rw [← hframe]
      exact φ₀e.symm_apply_apply _
    change C⁻¹ * Ψ (φ₀e.symm (ι u)) * C = linTorus ζ t ε u
    rw [h1, map_mul, map_mul, map_inv, hΨns u]
    change C⁻¹ * (C * linTorus ζ t ε u * C⁻¹) * C = linTorus ζ t ε u
    group
  rw [hπι]

end CFSG.StandardType.GGQ2Frame.LinPlacement
