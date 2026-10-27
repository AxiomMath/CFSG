module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2123
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofLeviMat
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagE blockHom coe_blockHom blockMat)
open CFSG.Assembly.RankThreeEven (projImage projSL)

namespace Item2119End3Proof

section Matrices

variable {K : Type} [Field K]

theorem scalar_mem_statedScalars (u : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) u ∈ StatedScalars (Fin 3) K :=
  ⟨u, rfl⟩

theorem mem_centralizer_of_mk_conj {n : ℕ} {e₀ : Kˣ} (he3 : (e₀ : K) ^ 3 = 1)
    (h3 : (3 : K) ≠ 0) {g N : GL (Fin 3) K} (hN : N ∈ Sec4.slPi true 3 (2 ^ n) K)
    (h : ProjGenLinGroup.mk (g * diagE e₀ * g⁻¹) * ProjGenLinGroup.mk N *
      (ProjGenLinGroup.mk (g * diagE e₀ * g⁻¹))⁻¹ = ProjGenLinGroup.mk N) :
    N * (g * diagE e₀ * g⁻¹) = (g * diagE e₀ * g⁻¹) * N := by
  set D := diagE e₀ with hD
  set Y := g * D * g⁻¹ with hY
  rw [← map_inv, ← map_mul, ← map_mul] at h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  set s := GeneralLinearGroup.scalar (Fin 3) u with hs
  have hsc : ∀ X : GL (Fin 3) K, X * s = s * X := fun X => (SL3Lines.scalar_mul_comm u X).symm
  have e1 : Y * N * Y⁻¹ = N * s⁻¹ := by
    calc Y * N * Y⁻¹ = Y * N * Y⁻¹ * s * s⁻¹ := by group
      _ = N * s⁻¹ := by rw [hu]
  have e2 : N⁻¹ * Y * N = s⁻¹ * Y := by
    calc N⁻¹ * Y * N = N⁻¹ * (Y * N * Y⁻¹) * Y := by group
      _ = N⁻¹ * (N * s⁻¹) * Y := by rw [e1]
      _ = s⁻¹ * Y := by group
  have e3 : N * (s⁻¹ * Y) * N⁻¹ = Y := by rw [← e2]; group
  have hNY : N * Y * N⁻¹ = s * Y := by
    calc N * Y * N⁻¹ = N * s * (s⁻¹ * Y) * N⁻¹ := by group
      _ = s * N * (s⁻¹ * Y) * N⁻¹ := by rw [hsc N]
      _ = s * (N * (s⁻¹ * Y) * N⁻¹) := by group
      _ = s * Y := by rw [e3]
  set N' := g⁻¹ * N * g with hN'
  have hN'SL : N' ∈ Sec4.slPi true 3 (2 ^ n) K := by
    rw [Sec4.mem_slPi_true] at hN ⊢
    rw [hN', show g⁻¹ * N * g = g⁻¹ * N * g⁻¹⁻¹ by rw [inv_inv], SL3Lines.det_conj]
    exact hN
  have h2 : N' * D * N'⁻¹ = s * D := by
    calc N' * D * N'⁻¹ = g⁻¹ * (N * Y * N⁻¹) * g := by rw [hN', hY]; group
      _ = g⁻¹ * (s * Y) * g := by rw [hNY]
      _ = s * (g⁻¹ * Y * g) := by rw [← mul_assoc g⁻¹ s Y, hsc g⁻¹]; group
      _ = s * D := by rw [hY]; group
  have hmem : N' ∈ Sec4.centMod (Sec4.slPi true 3 (2 ^ n) K) D :=
    Sec4.mem_centMod_iff_scalar.mpr ⟨hN'SL, s, scalar_mem_statedScalars u, h2⟩
  rw [Sec4.centMod_diagE_eq (p := 2) (f := n) true he3 h3] at hmem
  have hc : N' * D = D * N' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2
  calc N * Y = g * (N' * D) * g⁻¹ := by rw [hN', hY]; group
    _ = g * (D * N') * g⁻¹ := by rw [hc]
    _ = Y * N := by rw [hN', hY]; group

theorem perfectResidual_centralizer_eq_levi [Finite K] {n : ℕ} (hPi : Sec4.PiField true 2 n K)
    (hK4 : 4 ≤ Nat.card K) {e₀ : Kˣ} (he₀ : e₀ ≠ 1) (g : GL (Fin 3) K) :
    inSubgroup perfectResidual
        (Sec4.slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {g * diagE e₀ * g⁻¹}) =
      (Item221ResProof.LeviMat.levi0 (K := K)).map (MulAut.conj g).toMonoidHom := by
  have h := Item221ResProof.LeviMat.perfectResidual_centralizer_conj_eq hPi hK4 he₀ g 1
  rwa [map_one, one_mul] at h

theorem eq_one_of_mem_levi_of_mk_eq_one {g N : GL (Fin 3) K}
    (hN : N ∈ (Item221ResProof.LeviMat.levi0 (K := K)).map (MulAut.conj g).toMonoidHom)
    (h1 : ProjGenLinGroup.mk N = 1) : N = 1 := by
  obtain ⟨M, ⟨B, rfl⟩, rfl⟩ := hN
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨u, hu⟩ := h1
  set M := (blockHom.comp (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →*
    GL (Fin 2) K)) B with hM
  have hMu : M = GeneralLinearGroup.scalar (Fin 3) u := by
    have h2 : (MulAut.conj g) M = GeneralLinearGroup.scalar (Fin 3) u := hu.symm
    rw [MulAut.conj_apply] at h2
    calc M = g⁻¹ * (g * M * g⁻¹) * g := by group
      _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) u * g := by rw [h2]
      _ = GeneralLinearGroup.scalar (Fin 3) u := by
          rw [mul_assoc, SL3Lines.scalar_mul_comm u g]; group
  have hdet : GeneralLinearGroup.det (SpecialLinearGroup.toGL B) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact B.2
  have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) hMu
  simp only [hM, MonoidHom.comp_apply, coe_blockHom, hdet, inv_one, Units.val_one] at h00
  have hu1 : u = 1 := by
    apply Units.ext
    rw [Units.val_one]
    have h3 :
        (blockMat (1 : K) (SpecialLinearGroup.toGL B : Matrix (Fin 2) (Fin 2) K)) 0 0 = 1 := by
      simp [blockMat]
    rw [h3] at h00
    rw [h00]
    simp [GeneralLinearGroup.scalar]
  rw [hMu, hu1, map_one, map_one]

theorem exists_levi_of_cube {n : ℕ} (hPi : Sec4.PiField true 2 n K) {e₀ : Kˣ} (he₀ : e₀ ≠ 1)
    {g N : GL (Fin 3) K}
    (hN : N ∈ Sec4.slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {g * diagE e₀ * g⁻¹})
    (hN3 : N ^ 3 = 1) :
    ∃ N'' ∈ (Item221ResProof.LeviMat.levi0 (K := K)).map (MulAut.conj g).toMonoidHom,
      ProjGenLinGroup.mk N'' = ProjGenLinGroup.mk N := by
  have h1 := SL3Lines.inf_centralizer_conj (2 ^ n) g (diagE e₀) 1
  rw [map_one, one_mul, Sec4.centralizer_diagE_eq hPi he₀] at h1
  rw [h1] at hN
  obtain ⟨M, ⟨B, -, rfl⟩, rfl⟩ := hN
  have hB3 : B ^ 3 = 1 := by
    have h3 : (MulAut.conj g) (blockHom B) ^ 3 = 1 := hN3
    rw [← map_pow, ← map_pow] at h3
    apply Sec4.blockHom_injective
    apply (MulAut.conj g).injective
    rw [h3, map_one, map_one]
  have hd3 : GeneralLinearGroup.det B ^ 3 = 1 := by rw [← map_pow, hB3, map_one]
  set c : Kˣ := GeneralLinearGroup.det B with hc
  have hdetB'' : ((c : K) • (B : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← GeneralLinearGroup.val_det_apply, ← hc,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, hd3, Units.val_one]
  set B'' : SpecialLinearGroup (Fin 2) K := ⟨(c : K) • (B : Matrix (Fin 2) (Fin 2) K), hdetB''⟩
    with hB''
  have hmemL : blockHom (SpecialLinearGroup.toGL B'') ∈ Item221ResProof.LeviMat.levi0 (K := K) :=
    ⟨B'', rfl⟩
  refine ⟨(MulAut.conj g) (blockHom (SpecialLinearGroup.toGL B'')),
    Subgroup.mem_map_of_mem _ hmemL, ?_⟩
  have hdet'' : GeneralLinearGroup.det (SpecialLinearGroup.toGL B'') = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact hdetB''
  have hblock : blockHom (SpecialLinearGroup.toGL B'') =
      GeneralLinearGroup.scalar (Fin 3) c * blockHom B := by
    apply Units.ext
    rw [coe_blockHom, hdet'', inv_one, Units.val_one, Units.val_mul,
      GeneralLinearGroup.coe_scalar, coe_blockHom,
      show ((SpecialLinearGroup.toGL B'' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (c : K) • (B : Matrix (Fin 2) (Fin 2) K) from rfl]
    have hcdet : (c : K) = (B : Matrix (Fin 2) (Fin 2) K).det := by
      rw [hc, GeneralLinearGroup.val_det_apply]
    have hdet0 : (B : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [← hcdet]
      exact c.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMat, Matrix.scalar_apply, Matrix.diagonal, Matrix.mul_apply, hcdet, hdet0]
  have hconj : (MulAut.conj g) (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    rw [MulAut.conj_apply, ← SL3Lines.scalar_mul_comm c g]; group
  rw [hblock, map_mul, hconj, map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  rfl

end Matrices

section KFact

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mul_mem {C I N₀ : Subgroup G} (hIC : I ≤ C) (hIn : (I.subgroupOf C).Normal)
    (hN₀C : N₀ ≤ C) (hN₀3 : ¬ 3 ∣ Nat.card N₀) {d i t : G} (hdC : d ∈ C) (hd3 : d ^ 3 = 1)
    (hi : i ∈ I) (ht : t ∈ N₀) (hdit : d = i * t) : d ∈ I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set q := QuotientGroup.mk' (I.subgroupOf C) with hq
  have htC : t ∈ C := hN₀C ht
  have hqi : q ⟨i, hIC hi⟩ = 1 := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hi
  have hqd : q ⟨d, hdC⟩ = q ⟨t, htC⟩ := by
    have hdit' : (⟨d, hdC⟩ : C) = ⟨i, hIC hi⟩ * ⟨t, htC⟩ := Subtype.ext hdit
    rw [hdit', map_mul, hqi, one_mul]
  have h3 : q ⟨d, hdC⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdC⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hm : q ⟨t, htC⟩ ^ Nat.card N₀ = 1 := by
    rw [← map_pow]
    have h1 : (⟨t, ht⟩ : N₀) ^ Nat.card N₀ = 1 := pow_card_eq_one'
    have h1' : t ^ Nat.card N₀ = 1 := by
      have h := congrArg Subtype.val h1
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
    have h2 : (⟨t, htC⟩ : C) ^ Nat.card N₀ = 1 := Subtype.ext (by simpa using h1')
    rw [h2, map_one]
  have hcop : Nat.Coprime 3 (Nat.card N₀) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN₀3
  have hord : orderOf (q ⟨d, hdC⟩) = 1 := by
    apply Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    rw [hqd]
    exact orderOf_dvd_of_pow_eq_one hm
  rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hord
  exact hord

end KFact

end Item2119End3Proof

open Item2119End3Proof

theorem kf2123TypeTwo : KF2123TypeTwo := by
  intro G _ _ L n hn0 hne hLn x hx3 hxT d hdL hd3 hdT hxd
  obtain ⟨eL⟩ := hLn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hne; omega
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, -, hy2, hact⟩ := hxT
  have hcard := Sec13.card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hK.prime hK.one_le
    (by omega) hq hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have h2 : (2 : K) = 0 := Item21Late2Proof.two_eq_zero_of_piField hK
  have : Finite K := hK.finite
  have hKcard : Nat.card K = 2 ^ f := by simpa [Sec4.piCard] using hK.card
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn2
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨e₀, he₀3, he₀1, z, hz, g, -, hD⟩ := hy2
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  obtain ⟨ζ, -, rfl⟩ := Sec4.exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  set y₀ := g * diagE e₀ * g⁻¹ with hy₀
  have hyy₀ : ProjGenLinGroup.mk y = ProjGenLinGroup.mk y₀ := by
    have h1 : y * GeneralLinearGroup.scalar (Fin 3) ζ = y₀ := by rw [hy₀, ← hD]; group
    rw [← h1, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  have : Finite (GL (Fin 3) K) := inferInstance
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set S : Subgroup (projImage (Sec4.slPi true 3 (2 ^ f) K)) :=
    fixedSubgroupOf (KFacts.inducedAutHom L e ⟨x, hx⟩) with hS
  have hSmem : ∀ w : projImage (Sec4.slPi true 3 (2 ^ f) K),
      w ∈ S ↔ KFacts.inducedAutHom L e ⟨x, hx⟩ w = w :=
    fun w => mem_fixedSubgroupOf _ w
  have hind : ∀ w : projImage (Sec4.slPi true 3 (2 ^ f) K),
      ((KFacts.inducedAutHom L e ⟨x, hx⟩ w : projImage (Sec4.slPi true 3 (2 ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y₀ * (w : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y₀)⁻¹ := by
    intro w
    have h1 := hact (e.symm w)
    rw [MulEquiv.apply_symm_apply, hyy₀] at h1
    rw [KFacts.inducedAutHom_apply, MulAut.congr_apply]
    exact h1
  set T := (Sec4.slPi true 3 (2 ^ f) K ⊓ Subgroup.centralizer {y₀}).map ProjGenLinGroup.mk
    with hT
  have hST : S.map (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype = T := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨N, hN, hNs⟩ := s.2
      have h1 := hind s
      rw [(hSmem s).mp hs] at h1
      refine ⟨N, ⟨hN, ?_⟩, hNs⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (mem_centralizer_of_mk_conj he₀3 h3 hN (by rw [hNs]; exact h1.symm))
    · rintro ⟨N, ⟨hN, hNc⟩, rfl⟩
      have hNM : ProjGenLinGroup.mk N ∈ projImage (Sec4.slPi true 3 (2 ^ f) K) := ⟨N, hN, rfl⟩
      refine ⟨⟨_, hNM⟩, (hSmem _).mpr ?_, rfl⟩
      apply Subtype.ext
      rw [hind]
      have hNc' : N * y₀ = y₀ * N := Subgroup.mem_centralizer_singleton_iff.mp hNc
      change ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk N * (ProjGenLinGroup.mk y₀)⁻¹ =
        ProjGenLinGroup.mk N
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [← hNc']
      group
  set I := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) with hI
  have hx3' : ∃ j : ℕ, x ^ 3 ^ j = 1 := ⟨1, by simpa using hx3⟩
  have hĪ := KFacts.imageModTheta_perfectResidual_centralizer_eq hx hx3'
  have hB := KFacts.map_barCentralizer_eq hx e S hSmem
  set ψ : lBar L →* ProjGenLinGroup (Fin 3) K :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype_injective.comp e.injective
  set Λ := (Item221ResProof.LeviMat.levi0 (K := K)).map (MulAut.conj g).toMonoidHom with hΛ
  have hΛ' : (Sec8.imageModTheta L I).map ψ = Λ.map ProjGenLinGroup.mk := by
    rw [hĪ, hψ, ← Subgroup.map_map, map_inSubgroup_perfectResidual, hB,
      GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
        (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype_injective,
      hST, hT, ← PartOne.KFU.map_inSubgroup_perfectResidual,
      perfectResidual_centralizer_eq_levi hK hK4 he₀1 g]
  have hmkinj : Function.Injective (ProjGenLinGroup.mk.comp Λ.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro N hN
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hN
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_levi_of_mk_eq_one N.2 hN)
  have hrange : (ProjGenLinGroup.mk.comp Λ.subtype).range = Λ.map ProjGenLinGroup.mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eΛ : Λ ≃* Λ.map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) :=
    (MonoidHom.ofInjective hmkinj).trans (MulEquiv.subgroupCongr hrange)
  let eSL : SpecialLinearGroup (Fin 2) K ≃* Λ :=
    Item221ResProof.LeviMat.levi0Equiv.trans
      ((Item221ResProof.LeviMat.levi0 (K := K)).equivMapOfInjective _ (MulAut.conj g).injective)
  let eĪ : Sec8.imageModTheta L I ≃* SpecialLinearGroup (Fin 2) K :=
    ((Sec8.imageModTheta L I).equivMapOfInjective ψ hψinj).trans
      ((MulEquiv.subgroupCongr hΛ').trans (eΛ.symm.trans eSL.symm))
  have hSLq : IsQuasisimple (SpecialLinearGroup (Fin 2) K) :=
    CALinearPlane.isQuasisimple_SL_of_two_le le_rfl hK4
  have hSLZ : Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have h' : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h')
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  have hĪq : IsQuasisimple (Sec8.imageModTheta L I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eĪ.symm hSLq
  have hĪθ : aschbacherSolvableCore 3 (Sec8.imageModTheta L I) = ⊥ :=
    Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hĪq
      (by rw [center_eq_bot_of_mulEquiv' eĪ hSLZ]; exact IsPGroup.of_bot)
  have hIL : I ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  let ρ : I →* Sec8.imageModTheta L I :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hIL)).codRestrict
      _ (fun i => ⟨Subgroup.inclusion hIL i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨w, l, hl, rfl⟩
    refine ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
    apply Subtype.ext
    rfl
  obtain ⟨hθs, hθ3⟩ := Sec6.theta_solvable_and_not_dvd L
  obtain ⟨hks, hk3⟩ := Sec13.ker_facts_of_injective ρ I.subtype I.subtype_injective
    (inSubgroup (aschbacherSolvableCore 3) L) (fun i hi => by
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hIL i) = 1 :=
        congrArg Subtype.val hi
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩) hθs hθ3
  obtain ⟨eI⟩ := Sec13.nonempty_quotTheta_equiv_of_surjective ρ hρ hks hk3 hĪθ
  have eISL : lBar I ≃* SpecialLinearGroup (Fin 2) K := eI.trans eĪ
  have hSLcard : Nat.card (SpecialLinearGroup (Fin 2) K) = 2 ^ f * (4 ^ f - 1) := by
    rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hKcard,
      show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton,
      show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one,
      show (2 ^ f) ^ 2 = 4 ^ f by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  have hdI : d ∈ I := by
    set D' : lBar L := ((⟨d, hdL⟩ : L) : lBar L) with hD'
    have hD'B : D' ∈ Sec8.barCentralizer (Subgroup.zpowers x) L := by
      rw [KFacts.mem_barCentralizer_zpowers_iff hx, hD', Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      show x * d * x⁻¹ = d
      rw [hxd, mul_inv_cancel_right]
    have heD'S : e D' ∈ S := by
      rw [← hB]
      exact ⟨D', hD'B, rfl⟩
    have heD'T : ψ D' ∈ T := by
      rw [← hST]
      exact ⟨_, heD'S, rfl⟩
    obtain ⟨N, hN, hND⟩ := heD'T
    obtain ⟨m₀, hm₀⟩ := Item21Late2Proof.exists_conj_inv_of_inducesTypeOn_one hn2 eL hdL hdT
    obtain ⟨R, -, hRm⟩ := (e m₀).2
    have hRN : ProjGenLinGroup.mk (R * N * R⁻¹) = ProjGenLinGroup.mk N⁻¹ := by
      have h1 := congrArg ψ hm₀
      rw [map_mul, map_mul, map_inv, map_inv] at h1
      have hψm : ψ m₀ = ProjGenLinGroup.mk R := hRm.symm
      rw [map_mul, map_mul, map_inv, map_inv, hND, ← hψm]
      exact h1
    obtain ⟨ν, hν⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hRN
    have hNdet : GeneralLinearGroup.det N = 1 :=
      Units.ext ((Sec4.mem_slPi_true _).mp hN.1)
    have hsc : ∀ (X : GL (Fin 3) K) (v : Kˣ), X * GeneralLinearGroup.scalar (Fin 3) v =
        GeneralLinearGroup.scalar (Fin 3) v * X := fun X v => (SL3Lines.scalar_mul_comm v X).symm
    have hν3 : ν ^ 3 = 1 := by
      have h1 := congrArg GeneralLinearGroup.det hν
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hNdet, GeneralLinearGroup.det_scalar,
        Fintype.card_fin, mul_one, mul_inv_cancel, one_mul, inv_one] at h1
      exact h1
    have hD3 : D' ^ 3 = 1 := by
      rw [hD', ← QuotientGroup.mk_pow]
      have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, QuotientGroup.mk_one]
    have hN3mk : ProjGenLinGroup.mk (N ^ 3) = 1 := by
      rw [map_pow, hND, ← map_pow, hD3, map_one]
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hN3mk
    obtain ⟨μ, hμ⟩ := hN3mk
    have hμ1 : μ = 1 := by
      have h1 : (N ^ 3)⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ := by
        have hc : Commute (R * N * R⁻¹) (GeneralLinearGroup.scalar (Fin 3) ν) := hsc _ ν
        calc (N ^ 3)⁻¹ = N⁻¹ ^ 3 := (inv_pow N 3).symm
          _ = (R * N * R⁻¹ * GeneralLinearGroup.scalar (Fin 3) ν) ^ 3 := by rw [hν]
          _ = (R * N * R⁻¹) ^ 3 * GeneralLinearGroup.scalar (Fin 3) ν ^ 3 := hc.mul_pow 3
          _ = R * N ^ 3 * R⁻¹ := by
              rw [conj_pow, ← map_pow, hν3, map_one, mul_one]
          _ = GeneralLinearGroup.scalar (Fin 3) μ := by
              rw [← hμ, mul_assoc, ← hsc R⁻¹ μ, ← mul_assoc, mul_inv_cancel, one_mul]
      have h2 : GeneralLinearGroup.scalar (Fin 3) (μ * μ) = 1 := by
        rw [map_mul]
        calc GeneralLinearGroup.scalar (Fin 3) μ * GeneralLinearGroup.scalar (Fin 3) μ =
            N ^ 3 * (N ^ 3)⁻¹ := by rw [h1, hμ]
          _ = 1 := mul_inv_cancel _
      have hμμ : μ * μ = 1 := by
        apply Units.ext
        have h3 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) h2
        simp only [GeneralLinearGroup.coe_scalar, Units.val_one] at h3
        rw [Units.val_one]
        rw [← map_one (Matrix.scalar (Fin 3) : K →+* Matrix (Fin 3) (Fin 3) K)] at h3
        exact Matrix.scalar_inj.mp h3
      have hμ3 : μ ^ 3 = 1 := by
        have h3' := congrArg GeneralLinearGroup.det hμ
        rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, hNdet, one_pow] at h3'
        exact h3'
      calc μ = μ ^ 3 * (μ * μ)⁻¹ := by group
        _ = 1 := by rw [hμ3, hμμ]; group
    have hN3 : N ^ 3 = 1 := by rw [← hμ, hμ1, map_one]
    obtain ⟨N'', hN''Λ, hN''⟩ := exists_levi_of_cube hK he₀1 hN hN3
    have hD'Ī : D' ∈ Sec8.imageModTheta L I := by
      have h1 : ψ D' ∈ (Sec8.imageModTheta L I).map ψ := by
        rw [hΛ']
        exact ⟨N'', hN''Λ, hN''.trans hND⟩
      obtain ⟨w, hw, hwD⟩ := h1
      rwa [hψinj hwD] at hw
    obtain ⟨l, hl, hlD⟩ := hD'Ī
    have hlI : (l : G) ∈ I := Subgroup.mem_subgroupOf.mp hl
    set C := L ⊓ Subgroup.centralizer ({x} : Set G) with hC
    have hIC : I ≤ C := Sec6.inSubgroup_perfectResidual_le _
    have hIsub : I.subgroupOf C = perfectResidual C := by
      rw [hI, inSubgroup, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    have hIn : (I.subgroupOf C).Normal := by
      rw [hIsub]
      infer_instance
    have hdC : d ∈ C := ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr hxd.symm⟩
    have hθ' : (l : G)⁻¹ * d ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      have h1 : ((l : L) : lBar L) = ((⟨d, hdL⟩ : L) : lBar L) := hlD
      rw [QuotientGroup.eq] at h1
      exact ⟨_, h1, rfl⟩
    have htC : (l : G)⁻¹ * d ∈ C := C.mul_mem (C.inv_mem (hIC hlI)) hdC
    have hN₀3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L ⊓ C : Subgroup G) :=
      fun h => hθ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact mem_of_mul_mem hIC hIn inf_le_right hN₀3 hdC hd3 hlI ⟨hθ', htC⟩ (by group)
  refine ⟨hdI, CFSG.LocalCores.isQuasisimple_of_mulEquiv eISL.symm hSLq, ?_⟩
  rw [Nat.card_congr eISL.toEquiv, hSLcard]

theorem item2123Field (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6) :
    Item2123Field :=
  item2123Field_of h45 h48 h66 kf2123TypeTwo

end CFSG.RankThree.PartTwo.Sec21
