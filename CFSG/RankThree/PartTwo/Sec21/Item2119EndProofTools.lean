module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item2113Proof
import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projImage projSL)

section TypeOne

variable {G : Type} [Group G] [Finite G]

theorem diagTau_inv {K : Type} [Field K] {τ : K} (hτ : τ ^ 3 = 1) (hτ2 : (τ ^ 2) ^ 3 = 1) :
    (Sec4.diagTau hτ)⁻¹ = Sec4.diagTau hτ2 := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, Sec4.coe_diagTau, Sec4.coe_diagTau, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination hτ
  · linear_combination (τ ^ 3 + 1) * hτ

theorem inducesTypeOn_one_inv {L : Subgroup G} {x : G} (h : Sec4.InducesTypeOn L x 1) :
    Sec4.InducesTypeOn L x⁻¹ 1 := by
  obtain ⟨hx, π, p, f, K, hF, hK, hq, e, y, hyGL, hy1, hact⟩ := h
  obtain ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ := hy1
  have hτ2 : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  have hτ21 : τ ^ 2 ≠ 1 := fun h2 => hτ1 (by linear_combination hτ - τ * h2)
  have hzy : z * y = y * z := by
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have := (Subgroup.mem_center_iff.mp hz₀) ⟨y, hyGL⟩
    exact (congrArg Subtype.val this).symm
  refine ⟨Subgroup.inv_mem _ hx, π, p, f, K, hF, hK, hq, e, y⁻¹, Subgroup.inv_mem _ hyGL,
    ⟨τ ^ 2, hτ2, hτ21, z⁻¹, Subgroup.inv_mem _ hz, g, hg, ?_⟩, ?_⟩
  · calc g⁻¹ * (y⁻¹ * z⁻¹) * g = (g⁻¹ * (z * y) * g)⁻¹ := by group
      _ = (Sec4.diagTau hτ)⁻¹ := by rw [hzy, hD]
      _ = Sec4.diagTau hτ2 := diagTau_inv hτ hτ2
  · intro w
    have e1 : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : Subgroup.normalizer (L : Set G)) = ⟨x, hx⟩⁻¹ := rfl
    rw [e1, map_inv, map_inv]
    set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) with hσ
    have h1 := hact (σ⁻¹ w)
    rw [MulAut.apply_inv_self] at h1
    rw [map_inv ProjGenLinGroup.mk, inv_inv, h1]
    group

theorem false_of_isIrreducibleOn {A : Subgroup G} {d : G} (hirr : IsIrreducibleOn (wStar A))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (h27 : Nat.card A = 27)
    (hnorm : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B : Subgroup A := Subgroup.zpowers ⟨d, hdA⟩ with hB
  have hBW : ∀ φ ∈ wStar A, B.map φ.toMonoidHom = B := by
    rintro _ ⟨w, rfl⟩
    rw [hB, Item2113Proof.map_eq_iff_mem_normalizer, Item2113Proof.map_subtype_zpowers]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers d).zpow_mem (hnorm w w.2) k
  have hd1' : (⟨d, hdA⟩ : A) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hd3' : (⟨d, hdA⟩ : A) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  rcases hirr B hBW with h | h
  · apply hd1'
    have hmem : (⟨d, hdA⟩ : A) ∈ B := Subgroup.mem_zpowers _
    rw [h] at hmem
    exact (Subgroup.mem_bot.mp hmem)
  · have hc : Nat.card B = 3 := by
      rw [hB, Nat.card_zpowers, orderOf_eq_prime hd3' hd1']
    rw [h, Subgroup.card_top, h27] at hc
    norm_num at hc

end TypeOne

section Matrices

variable {K : Type} [Field K]

theorem eq_diagonal_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {N : Matrix (Fin 3) (Fin 3) K}
    (hN : N * ((Sec4.diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((Sec4.diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N) :
    N = diagonal fun i => N i i := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hdiag : ((Sec4.diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![τ, τ ^ 2, 1] := by
    rw [Sec4.coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]
  rw [hdiag] at hN
  have h01 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have h' : τ * (τ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hτ0)
  have h12 : τ ^ 2 ≠ 1 := fun h2 => hτ1 (by linear_combination hτ - τ * h2)
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Sec4.entry_eq_zero_of_commute_diagonal hN (by simpa using h01)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hN (by simpa using hτ1)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hN (by simpa using h01.symm)
    · exact absurd rfl hij
    · exact Sec4.entry_eq_zero_of_commute_diagonal hN (by simpa using h12)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hN (by simpa using hτ1.symm)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hN (by simpa using h12.symm)
    · exact absurd rfl hij

theorem eq_one_of_scalar_eq_one {u : Kˣ} (h : GeneralLinearGroup.scalar (Fin 3) u = 1) : u = 1 := by
  have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [Item21Late2Proof.scalar_apply_self', Units.val_one, Matrix.one_apply_eq] at h00
  exact Units.ext (by rw [h00, Units.val_one])

theorem mk_eq_one_of_commute_diagTau (h2 : (2 : K) = 0) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Y s g : GL (Fin 3) K} (hY : g⁻¹ * Y * g = Sec4.diagTau hτ)
    (hc : ProjGenLinGroup.mk s * ProjGenLinGroup.mk Y =
      ProjGenLinGroup.mk Y * ProjGenLinGroup.mk s)
    (hs2 : ProjGenLinGroup.mk s ^ 2 = 1) : ProjGenLinGroup.mk s = 1 := by
  set D : GL (Fin 3) K := Sec4.diagTau hτ with hDdef
  set N : GL (Fin 3) K := g⁻¹ * s * g with hNdef
  have hsc : ∀ (X : GL (Fin 3) K) (v : Kˣ), X * GeneralLinearGroup.scalar (Fin 3) v =
      GeneralLinearGroup.scalar (Fin 3) v * X := fun X v => (SL3Lines.scalar_mul_comm v X).symm
  have h1 : ProjGenLinGroup.mk (s * Y * s⁻¹) = ProjGenLinGroup.mk Y := by
    rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
  have hND : N * D * N⁻¹ * GeneralLinearGroup.scalar (Fin 3) u = D := by
    calc N * D * N⁻¹ * GeneralLinearGroup.scalar (Fin 3) u
        = g⁻¹ * (s * Y * s⁻¹) * (g * GeneralLinearGroup.scalar (Fin 3) u) := by
          rw [hNdef, ← hY]
          group
      _ = g⁻¹ * (s * Y * s⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) * g := by
          rw [hsc g u]
          group
      _ = D := by rw [hu, hY]
  have hD3 : D ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hDdef, Sec4.coe_diagTau, Units.val_one, pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination hτ
    · linear_combination (τ ^ 3 + 1) * hτ
  have hND' : N * D * N⁻¹ = D * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
    calc N * D * N⁻¹ = N * D * N⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
          (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by group
      _ = D * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by rw [hND, map_inv]
  have hu3 : u ^ 3 = 1 := by
    have e1 : (N * D * N⁻¹) ^ 3 = 1 := by rw [conj_pow, hD3, mul_one, mul_inv_cancel]
    have e2 : (D * GeneralLinearGroup.scalar (Fin 3) u⁻¹) ^ 3 =
        D ^ 3 * GeneralLinearGroup.scalar (Fin 3) (u⁻¹ ^ 3) := by
      rw [map_pow, (Commute.mul_pow (hsc D u⁻¹) 3)]
    rw [hND', e2, hD3, one_mul] at e1
    have := eq_one_of_scalar_eq_one e1
    rw [inv_pow, inv_eq_one] at this
    exact this
  have hs2' : ProjGenLinGroup.mk (s ^ 2) = 1 := by rw [map_pow, hs2]
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs2'
  obtain ⟨μ, hμ⟩ := hs2'
  have hN2 : N ^ 2 = GeneralLinearGroup.scalar (Fin 3) μ := by
    have e1 : N ^ 2 = g⁻¹ * s ^ 2 * g := by
      rw [hNdef, pow_two, pow_two]
      group
    rw [e1, ← hμ, hsc g⁻¹ μ, inv_mul_cancel_right]
  have hu2 : u ^ 2 = 1 := by
    have e1 : N ^ 2 * D * (N ^ 2)⁻¹ = D := by
      rw [hN2, ← hsc D μ, mul_inv_cancel_right]
    have e2 : N ^ 2 * D * (N ^ 2)⁻¹ =
        D * GeneralLinearGroup.scalar (Fin 3) (u⁻¹ * u⁻¹) := by
      calc N ^ 2 * D * (N ^ 2)⁻¹ = N * (N * D * N⁻¹) * N⁻¹ := by rw [pow_two]; group
        _ = N * (D * GeneralLinearGroup.scalar (Fin 3) u⁻¹) * N⁻¹ := by rw [hND']
        _ = (N * D * N⁻¹) * (N * GeneralLinearGroup.scalar (Fin 3) u⁻¹ * N⁻¹) := by group
        _ = D * GeneralLinearGroup.scalar (Fin 3) u⁻¹ * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
            rw [hND', hsc N u⁻¹, mul_inv_cancel_right]
        _ = D * GeneralLinearGroup.scalar (Fin 3) (u⁻¹ * u⁻¹) := by rw [map_mul, mul_assoc]
    rw [e2] at e1
    have e3 : GeneralLinearGroup.scalar (Fin 3) (u⁻¹ * u⁻¹) = 1 := by
      have e4 := congrArg (D⁻¹ * ·) e1
      simpa using e4
    have e5 := eq_one_of_scalar_eq_one e3
    rw [← _root_.mul_inv_rev, inv_eq_one] at e5
    rw [pow_two]
    exact e5
  have hu : u = 1 := by
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu3, hu2]; group
  have hcomm : N * D = D * N := by
    have e1 := hND
    rw [hu, map_one, mul_one] at e1
    calc N * D = N * D * N⁻¹ * N := by group
      _ = D * N := by rw [e1]
  have hcommM : (N : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K) =
      (D : Matrix (Fin 3) (Fin 3) K) * (N : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hcomm]
  set n : Fin 3 → K := fun i => (N : Matrix (Fin 3) (Fin 3) K) i i with hn
  have hNdiag : (N : Matrix (Fin 3) (Fin 3) K) = diagonal n :=
    eq_diagonal_of_commute_diagTau hτ hτ1 hcommM
  have hsq : ∀ i, n i ^ 2 = μ := by
    intro i
    have e1 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i i) hN2
    simp only [pow_two, Units.val_mul, Item21Late2Proof.scalar_apply_self'] at e1
    rw [hNdiag, diagonal_mul_diagonal, diagonal_apply_eq] at e1
    rw [pow_two]
    exact e1
  have heq : ∀ i, n i = n 0 := by
    intro i
    have e1 : (n i - n 0) ^ 2 = 0 := by
      linear_combination hsq i - hsq 0 + (n 0 ^ 2 - n i * n 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp e1)
  have hNs : (N : Matrix (Fin 3) (Fin 3) K) = n 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hNdiag]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [heq i]
    · simp [hij]
  have hmkN : ProjGenLinGroup.mk N = 1 := by
    rw [ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
    intro X
    apply Units.ext
    rw [Units.val_mul X N, Units.val_mul N X, hNs, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hs : s = g * N * g⁻¹ := by
    rw [hNdef]
    group
  rw [hs, map_mul, map_mul, hmkN, mul_one, map_inv, mul_inv_cancel]

end Matrices

section Config

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_commute_of_inducesTypeOn_one {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar L ≃* projSL 3 (GaloisField 2 n)) {d : G} (hdL : d ∈ L)
    (hdT : Sec4.InducesTypeOn L d 1) (v : lBar L) (hv2 : v ^ 2 = 1)
    (hvd : v * ((⟨d, hdL⟩ : L) : lBar L) = ((⟨d, hdL⟩ : L) : lBar L) * v) : v = 1 := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, -, hy1, hact⟩ := hdT
  have hcard := Sec13.card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hK.prime hK.one_le
    (by omega) hq hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have h2 : (2 : K) = 0 := Item21Late2Proof.two_eq_zero_of_piField hK
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn
  set D' : lBar L := ((⟨d, hdL⟩ : L) : lBar L) with hD'
  have hey : (e D' : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk y := by
    refine Item21Late2Proof.coe_e_eq_mk_of_inner hK hq hq2 e D' y fun z => ?_
    rw [← Item21Late2Proof.thetaQuotMulAut_inner hdL hx z]
    exact hact z
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := hy1
  have hzs := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hmkz : ProjGenLinGroup.mk z = 1 := Item21Late2Proof.mk_eq_one_of_mem_statedScalars hzs
  obtain ⟨s, -, hsv⟩ := (e v).2
  have hc : ProjGenLinGroup.mk s * ProjGenLinGroup.mk (y * z) =
      ProjGenLinGroup.mk (y * z) * ProjGenLinGroup.mk s := by
    rw [map_mul ProjGenLinGroup.mk y z, hmkz, mul_one, hsv, ← hey]
    have e1 := congrArg (fun w => ((e w : projImage (Sec4.slPi true 3 (2 ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) hvd
    simpa only [map_mul, Subgroup.coe_mul] using e1
  have hs2 : ProjGenLinGroup.mk s ^ 2 = 1 := by
    rw [hsv]
    have e1 := congrArg (fun w => ((e w : projImage (Sec4.slPi true 3 (2 ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) hv2
    simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one] using e1
  have hmk := mk_eq_one_of_commute_diagTau h2 hτ hτ1 hD hc hs2
  apply e.injective
  apply Subtype.ext
  rw [map_one, ← hsv, hmk]
  rfl

theorem not_mem_sup_of_config2119End {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) :
    a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  intro haCD
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, hn0, hev, ⟨eL⟩⟩ := hcfg.lthree
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hn : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  obtain ⟨i, -, j, hj, haij⟩ := Item21Late2Proof.exists_pow_mul_pow_of_mem_sup
    (hcomm c hcA d hdA) (h3 c hcA) (h3 d hdA) haCD
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hE.not_mem_a
    rw [haij, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i
  have hdU : ∀ u ∈ U₀, u * d = d * u := by
    intro u hu
    have hua : u * a = a * u := Subgroup.mem_centralizer_iff.mp hE.mem_a.2 u hu
    have huc : u * c = c * u :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLC (hE.le_U₀ hu))
    have hdj : Commute u (d ^ j) := by
      have e1 : d ^ j = (c ^ i)⁻¹ * a := by rw [haij]; group
      rw [e1]
      exact ((Commute.pow_right huc i).inv_right).mul_right hua
    interval_cases j
    · exact absurd rfl hj0
    · simpa using hdj.eq
    · have e2 : d = (d ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3 d hdA, one_mul, pow_one]
      rw [e2]
      exact (hdj.pow_right 2).eq
  have hU₀θ : U₀ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    intro u hu
    have huL : u ∈ L := hE.le_U₀ hu
    have hu2 : u ^ 2 = 1 := hE.mem_U₀.1.2.1.2 u hu
    have hv := eq_one_of_commute_of_inducesTypeOn_one hn eL hdL hE.type_d
      ((⟨u, huL⟩ : L) : lBar L) ?_ ?_
    · rw [QuotientGroup.eq_one_iff] at hv
      exact ⟨⟨u, huL⟩, hv, rfl⟩
    · rw [← QuotientGroup.mk_pow,
        show (⟨u, huL⟩ : L) ^ 2 = 1 from Subtype.ext (by simpa using hu2), QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hdU u hu)
  have hT : U₀ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) :=
    hU₀θ.trans (theta_le_theta_centralizer hLc)
  obtain ⟨hU2, hU1⟩ := Sec6.isPGroup_two_and_ne_bot_of_mem_fourGroups hE.mem_U₀.1
  have hET : E ≤ Subgroup.normalizer (U₀ : Set G) := (mem_fourGroups_iff.mp hE.mem_U₀.1).1
  have hcomm' := Sec6.commutator_eq_bot_of_mem_partTwoS hpair.mem_S hcA hc1 hpair.mem_E.2 hT hU2
    hET
  apply hU1
  rw [hE.mem_U₀.2, hcomm']

end Config

end CFSG.RankThree.PartTwo.Sec21.Item2119EndProof
