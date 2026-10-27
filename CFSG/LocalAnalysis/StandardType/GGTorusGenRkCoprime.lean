module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

private theorem ggrkc_ne_six_one_of_not_dvd {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) : (d, n) ≠ (6, 1) := by
  rintro h
  have hd6 : d = 6 := congrArg Prod.fst h
  have hn1 : n = 1 := congrArg Prod.snd h
  have hp3 : p ∣ 3 := by
    have h' := hpq
    rw [hn1] at h'
    norm_num at h'
    exact h'
  have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  exact hpd (by rw [hd6, hp_eq]; norm_num)

private theorem ggrkc_mem_center_of_scalar {n d : ℕ} {K : Type} [Field K]
    {x : ↥(unitarySU 2 n K d)} {c : K}
    (hc : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    x ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hc, ← Matrix.scalar_apply]
  exact (Matrix.scalar_comm c (fun r' => mul_comm c r')
    (((y : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).symm

private theorem ggrkc_mem_center_of_commutator_mem_center {G : Type*} [Group G]
    (hG : commutator G = ⊤) {g : G} (hc : ∀ x : G, ⁅g, x⁆ ∈ Subgroup.center G) :
    g ∈ Subgroup.center G := by
  have hmul : ∀ x y : G, ⁅g, x * y⁆ = ⁅g, x⁆ * ⁅g, y⁆ := by
    intro x y
    have hxc : x * ⁅g, y⁆ = ⁅g, y⁆ * x := Subgroup.mem_center_iff.mp (hc y) x
    have hcx : ⁅g, y⁆ * x⁻¹ = x⁻¹ * ⁅g, y⁆ := by
      calc ⁅g, y⁆ * x⁻¹ = x⁻¹ * (x * ⁅g, y⁆) * x⁻¹ := by group
        _ = x⁻¹ * (⁅g, y⁆ * x) * x⁻¹ := by rw [hxc]
        _ = x⁻¹ * ⁅g, y⁆ := by group
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc g * (x * y) * g⁻¹ * (x * y)⁻¹
        = g * x * (g⁻¹ * (g * y * g⁻¹ * y⁻¹)) * x⁻¹ := by group
      _ = g * x * g⁻¹ * (⁅g, y⁆ * x⁻¹) := by rw [commutatorElement_def]; group
      _ = g * x * g⁻¹ * (x⁻¹ * ⁅g, y⁆) := by rw [hcx]
      _ = g * x * g⁻¹ * x⁻¹ * (g * y * g⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  have hinv : ∀ u : G, ⁅g, u⁻¹⁆ * ⁅g, u⁆ = 1 := by
    intro u
    have h := hmul u⁻¹ u
    rw [inv_mul_cancel, commutatorElement_one_right] at h
    exact h.symm
  have hpow : ∀ x : G, ⁅g, x⁆ = 1 := by
    intro x
    have hx : x ∈ commutator G := by rw [hG]; exact Subgroup.mem_top x
    change x ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, -, b, -, rfl⟩ := hw
      have hp : ⁅g, a⁆ * ⁅g, b⁆ = ⁅g, b⁆ * ⁅g, a⁆ :=
        Subgroup.mem_center_iff.mp (hc b) _
      have hpi : ⁅g, a⁻¹⁆ = ⁅g, a⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv a)
      have hqi : ⁅g, b⁻¹⁆ = ⁅g, b⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv b)
      rw [commutatorElement_def a b, hmul, hmul, hmul, hpi, hqi]
      calc ⁅g, a⁆ * ⁅g, b⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹
          = ⁅g, b⁆ * ⁅g, a⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ := by rw [hp]
        _ = 1 := by group
    | one => simp
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx =>
      have := hinv x
      rw [hx, mul_one] at this
      exact this
  refine Subgroup.mem_center_iff.mpr fun x => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hpow x)).symm

private theorem ggrkc_conjN_eq_self_of_diag {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t v : Fin d → K}
    (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    conjN D hD s = s := by
  refine Subtype.ext ?_
  rw [coe_conjN]
  have hcomm : D * (s : GL (Fin d) K) = (s : GL (Fin d) K) * D := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hDt, hs]
    exact Matrix.commute_diagonal t v
  rw [hcomm]
  group

private theorem ggrkc_commute_of_diag {d n : ℕ} {K : Type} [Field K]
    {x y : ↥(unitarySU 2 n K d)}
    (hx : ∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    (hy : ∃ w : Fin d → K, ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w) :
    Commute x y := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨w, hw⟩ := hy
  show x * y = y * x
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hv, hw]
  exact Matrix.commute_diagonal v w

private theorem ggrkc_exists_diag_pPart
    {d n p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hp : p.Prime) (s0 : ↥(unitarySU 2 n K d))
    (hs0 : ∃ v : Fin d → K, ((s0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    {c : L'} (hc : φ s0 = c) (hcp : ∃ k : ℕ, c ^ p ^ k = 1) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      (∃ k : ℕ, s ^ p ^ k = 1) ∧ φ s = c := by
  classical
  have : Finite ↥(unitarySU 2 n K d) := by infer_instance
  obtain ⟨m, hm⟩ := hcp
  have hN : orderOf s0 ≠ 0 := (orderOf_pos s0).ne'
  obtain ⟨e, n', hn'p, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hcop : p.Coprime n' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn'p
  have hc' : (p ^ m).Coprime n' := (hcop.symm.pow_right m).symm
  obtain ⟨t, ht⟩ := Nat.chineseRemainder hc' 1 0
  have ht1 : t ≡ 1 [MOD p ^ m] := ht.1
  have ht0 : t ≡ 0 [MOD n'] := ht.2
  refine ⟨s0 ^ t, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hs0
    exact ⟨v ^ t, by rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hv, diagonal_pow]⟩
  · obtain ⟨q, hq⟩ := Nat.modEq_zero_iff_dvd.mp ht0
    refine ⟨e, ?_⟩
    have hNpow : s0 ^ (p ^ e * n') = 1 := by rw [← hN, pow_orderOf_eq_one]
    calc (s0 ^ t) ^ p ^ e = s0 ^ (t * p ^ e) := by rw [pow_mul]
      _ = s0 ^ (n' * q * p ^ e) := by rw [hq]
      _ = s0 ^ (q * (p ^ e * n')) := by congr 1; ring
      _ = (s0 ^ (p ^ e * n')) ^ q := by rw [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hNpow, one_pow]
  · rw [map_pow, hc, pow_eq_pow_of_modEq ht1 hm, pow_one]

theorem exists_model_of_position_rowA_coprime
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    (hcov : UnitaryCoverAt n d K)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) θ hE) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', UnitTB.Model φ ∧
      ∀ e : E, ∃ t : Fin d → K, ActsDiagU φ (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t := by
  classical
  have hperf : commutator L' = ⊤ := hpos.1
  set A : Subgroup (MulAut L') := (ggGamma L' hE).range with hAdef
  have hAab : CFSG.Open.IsElemAbelian p A := by
    rw [hAdef]
    exact TableBBridge.isElemAbelian_range_gamma hpos
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggLAut L' θ ⟨b, hE b.2⟩, hpos.2.2.2.1 b,
      fun l => ggBeta_ggQuotHom L' hE θ b l⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime hK hn hd hp hpq hpd hcov
      (ggQuotHom_surjective θ) (ker_ggQuotHom θ).le hperf hAab hAI
  refine ⟨φ, ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩, ?_⟩
  intro e
  obtain ⟨t, ht⟩ := hdiag (ggGamma L' hE e) ⟨e, rfl⟩
  exact ⟨t, ht⟩

theorem centralizes_center_pElts_rowA_coprime
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    (hcov : UnitaryCoverAt n d K)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) θ hE) :
    ∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ p = 1 →
      z ∈ Subgroup.centralizer (E : Set M) := by
  classical
  intro z hz _
  obtain ⟨hzL, hzC⟩ := hz
  obtain ⟨φ, hmodel, hdiagE⟩ :=
    exists_model_of_position_rowA_coprime hK hn hd hp hpq hpd hcov hpos
  have hφs := hmodel.surj
  have hφker := hmodel.ker
  have hzcent : (⟨z, hzL⟩ : L') ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC l l.2
  obtain ⟨u, hu⟩ := hφs ⟨z, hzL⟩
  have hucen : u ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
    refine ggrkc_mem_center_of_commutator_mem_center (G := ↥(unitarySU 2 n K d)) ?_ fun v => ?_
    · exact hcov.1
    · have h1 : φ ⁅u, v⁆ = 1 := by
        rw [map_commutatorElement, hu, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hzcent (φ v)).symm
      obtain ⟨c, hc⟩ := hφker ⁅u, v⁆ h1
      exact ggrkc_mem_center_of_scalar hc
  have hcommSU : ∀ g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n),
      Commute (u : GL (Fin d) K) g := by
    intro g hg
    have hcntr := Subgroup.mem_center_iff.mp hucen (⟨g, hg⟩ : ↥(unitarySU 2 n K d))
    exact (congrArg Subtype.val hcntr).symm
  have hscal : (u : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    GGL45TG.SU.mem_scalars_of_commute_su (TableBU.unitaryFieldData_of_card hK hn) hd
      (u : GL (Fin d) K) hcommSU
  rw [largeEvenScalars_def] at hscal
  obtain ⟨cu, hcu⟩ := hscal
  have hconj : ∀ (D : GL (Fin d) K)
      (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      conjN D hD u = u := by
    intro D hD
    apply Subtype.ext
    have hDcomm : D * (u : GL (Fin d) K) = (u : GL (Fin d) K) * D := by
      rw [← hcu]
      exact (Matrix.GeneralLinearGroup.scalar_commute cu D).symm
    show D * (u : GL (Fin d) K) * D⁻¹ = (u : GL (Fin d) K)
    rw [hDcomm]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨t, ht⟩ := hdiagE ⟨e, he⟩
  obtain ⟨D, hD, -, hact⟩ := ht
  have hfix : (L'.normalizerMonoidHom ⟨e, hE he⟩) (⟨z, hzL⟩ : L') = ⟨z, hzL⟩ := by
    have h := hact u
    rw [hu] at h
    rw [hconj D hD, hu] at h
    exact h
  have hfixM : e * z * e⁻¹ = z := by
    have h := congrArg Subtype.val hfix
    rw [normalizerMonoidHom_coe] at h
    simpa using h
  calc e * z = e * z * e⁻¹ * e := by group
    _ = z * e := by rw [hfixM]

theorem ggTorusGenTableBRk_PSU_coprime
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    (hcov : UnitaryCoverAt n d K) :
    GGTorusGenTableBRk p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) := by
  intro M _ _ L' E E₁ D' J' dm θ hE hpos hr hC hE₁E hE₁C hcard hN hD'E hCD' hD'E₁ hd1 hJ
  classical
  refine ⟨centralizes_center_pElts_rowA_coprime hK hn hd hp hpq hpd hcov hpos, ?_⟩
  intro c hc hcp hdisj
  obtain ⟨φ, hmodel, hdiagE⟩ :=
    exists_model_of_position_rowA_coprime hK hn hd hp hpq hpd hcov hpos
  obtain ⟨hdec, hcent⟩ := exists_mul_of_complement_position hp hpos hC hE₁E hE₁C hcard
  have hdE : dm ∈ E := by
    have hdmem : dm ∈ D' ⊓ E₁ := by rw [hD'E₁]; exact Subgroup.mem_zpowers dm
    exact hD'E hdmem.1
  let cL : L' := ⟨c, hc.1⟩
  have hcpL : ∃ k : ℕ, cL ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, Subtype.ext (by simpa [Subgroup.coe_pow] using hk)⟩
  have hcE : c ∈ Subgroup.centralizer (E : Set M) := hcent hc
  have hc_comm : ∀ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) →
        s ^ p = 1 → cL * φ s = φ s * cL := by
    intro s hs hsp
    have hφsE : ((φ s : L') : M) ∈ E := map_diag_pTorsion_mem_E hpos hdiagE s hs hsp
    have h1 := Subgroup.mem_centralizer_iff.mp hcE ((φ s : L') : M) hφsE
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact h1.symm
  obtain ⟨s0, hs0diag, hs0eq⟩ :=
    mem_diagImage_of_commute_pTorsion_coprime hmodel hp hpq hpd cL hc_comm
  obtain ⟨sp, hspdiag, hspP, hspEq⟩ :=
    ggrkc_exists_diag_pPart (p := p) hp s0 hs0diag hs0eq hcpL
  have hcomp : IsComponentOf (J'.subgroupOf L') (ggFix (L'.normalizerMonoidHom ⟨dm, hE hdE⟩)) :=
    isComponentOf_subgroupOf_ggFix_of_decomp hE hdE hdec hD'E hCD' hD'E₁ hJ
  obtain ⟨t, ht⟩ := hdiagE ⟨dm, hdE⟩
  obtain ⟨i₀, hIcard, hJeq⟩ := exists_class_of_isComponentOf_ggFix hmodel ht hcomp
  let I : Finset (Fin d) := Finset.univ.filter fun i => t i = t i₀
  have hIcard' : 2 ≤ I.card := hIcard
  let Gen : Set ↥(unitarySU 2 n K d) :=
    {x | x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
      (∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      ∃ k : ℕ, x ^ p ^ k = 1}
  have hGen_mem : ∀ x : ↥(unitarySU 2 n K d), x ∈ Gen ↔
      x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
        (∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        ∃ k : ℕ, x ^ p ^ k = 1 := fun _ => Iff.rfl
  let A : Subgroup ↥(unitarySU 2 n K d) := Subgroup.closure Gen
  have hpair : Gen.Pairwise Commute := by
    intro x hx y hy _
    exact ggrkc_commute_of_diag ((hGen_mem x).mp hx).2.1 ((hGen_mem y).mp hy).2.1
  have hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
  let T : Subgroup ↥(unitarySU 2 n K d) :=
    { carrier := {x | x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1}
      one_mem' := ⟨A.one_mem, ⟨0, by simp⟩⟩
      mul_mem' := by
        rintro x y ⟨hxA, k, hxk⟩ ⟨hyA, l, hyl⟩
        refine ⟨A.mul_mem hxA hyA, ⟨max k l, ?_⟩⟩
        have hxy : Commute x y := by
          have h := (isMulCommutative_iff.mp hAcomm) ⟨x, hxA⟩ ⟨y, hyA⟩
          exact Subtype.ext_iff.mp h
        have hxk' : x ^ p ^ max k l = 1 := by
          have hd : orderOf x ∣ p ^ max k l :=
            (orderOf_dvd_iff_pow_eq_one.mpr hxk).trans (Nat.pow_dvd_pow p (le_max_left k l))
          exact orderOf_dvd_iff_pow_eq_one.mp hd
        have hyl' : y ^ p ^ max k l = 1 := by
          have hd : orderOf y ∣ p ^ max k l :=
            (orderOf_dvd_iff_pow_eq_one.mpr hyl).trans (Nat.pow_dvd_pow p (le_max_right k l))
          exact orderOf_dvd_iff_pow_eq_one.mp hd
        rw [hxy.mul_pow, hxk', hyl', mul_one]
      inv_mem' := by
        rintro x ⟨hxA, k, hxk⟩
        exact ⟨A.inv_mem hxA, ⟨k, by rw [inv_pow, hxk, inv_one]⟩⟩ }
  have hAT : A ≤ T := by
    rw [show A = Subgroup.closure Gen from rfl, Subgroup.closure_le]
    intro x hx
    exact ⟨Subgroup.subset_closure hx, ((hGen_mem x).mp hx).2.2⟩
  have hAP : IsPGroup p A := fun x => by
    obtain ⟨k, hk⟩ := (hAT x.2).2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  let ψ : ↥(unitarySU 2 n K d) →* M := L'.subtype.comp φ
  let S : Subgroup M := Subgroup.map ψ A
  let W : Set M := Set.range (fun σ : Equiv.Perm (Fin d) => ψ (permSU hmodel.field σ))
  have hS_pg : IsPGroup p S := IsPGroup.map (H := A) hAP ψ
  have hScent : S ≤ Subgroup.centralizer (E₁ : Set M) := by
    have hle : A ≤ Subgroup.comap ψ (Subgroup.centralizer (E₁ : Set M)) := by
      rw [show A = Subgroup.closure Gen from rfl, Subgroup.closure_le]
      intro x hx
      change ψ x ∈ Subgroup.centralizer (E₁ : Set M)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨v, hv⟩ := ((hGen_mem x).mp hx).2.1
      obtain ⟨t', D, hD, hDt, hact⟩ := hdiagE ⟨e, hE₁E he⟩
      have hconj := hact x
      rw [ggrkc_conjN_eq_self_of_diag D hD hDt x hv] at hconj
      have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE (hE₁E he)⟩ (φ x)
      have h1 : e * ((φ x : L') : M) * e⁻¹ = ((φ x : L') : M) := by
        rw [← hcoe, hconj]
      change e * ((φ x : L') : M) = ((φ x : L') : M) * e
      calc e * ((φ x : L') : M) = (e * ((φ x : L') : M) * e⁻¹) * e := by group
        _ = ((φ x : L') : M) * e := by rw [h1]
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
    exact hle hxA
  have hSJ : S ≤ J' := by
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
    have hxblock : x ∈ TableBUE.blockSU (K := K) (n := n) I :=
      (Subgroup.closure_le (TableBUE.blockSU (K := K) (n := n) I)).mpr
        (fun z hz => ((hGen_mem z).mp hz).1) hxA
    have hφmem : φ x ∈ (TableBUE.blockSU (K := K) (n := n) I).map φ :=
      Subgroup.mem_map.mpr ⟨x, hxblock, rfl⟩
    rw [← hJeq] at hφmem
    rw [Subgroup.mem_subgroupOf] at hφmem
    exact hφmem
  have hWN : W ⊆ Subgroup.normalizer (E₁ : Set M) := by
    rintro n ⟨σ, rfl⟩
    exact hN (permSU_lift_mem_normalizer_rowA hd hpos hmodel hdiagE σ)
  refine ⟨S, W, hS_pg, hScent, hSJ, hWN, ?_⟩
  have hs4 := diag_pElt_mem_closure_permConj (hKd := hmodel.field) I hIcard' sp hspdiag hspP
  have hψsp : ψ sp = c := by
    change L'.subtype (φ sp) = c
    rw [hspEq]
    rfl
  have hmem : ψ sp ∈ Subgroup.closure (ψ '' (⋃ σ : Equiv.Perm (Fin d),
      (fun x => permSU hmodel.field σ * x * (permSU hmodel.field σ)⁻¹) '' Gen)) := by
    have h0 : ψ sp ∈ Subgroup.map ψ (Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
        (fun x => permSU hmodel.field σ * x * (permSU hmodel.field σ)⁻¹) '' Gen)) :=
      Subgroup.mem_map.mpr ⟨sp, hs4, rfl⟩
    rwa [MonoidHom.map_closure] at h0
  have hsubset : ψ '' (⋃ σ : Equiv.Perm (Fin d),
        (fun x => permSU hmodel.field σ * x * (permSU hmodel.field σ)⁻¹) '' Gen) ⊆
      ⋃ n ∈ W, (fun s : M => n * s * n⁻¹) '' (S : Set M) := by
    rintro y ⟨z, hz, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image] at hz ⊢
    obtain ⟨σ, x, hxGen, rfl⟩ := hz
    refine ⟨ψ (permSU hmodel.field σ), ⟨σ, rfl⟩, ψ x, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨x, Subgroup.subset_closure hxGen, rfl⟩
    · rw [map_mul, map_mul, map_inv]
  rw [hψsp] at hmem
  exact Subgroup.closure_mono hsubset hmem

theorem largeEvenLabelAll_torusGenTableB_twA_coprime
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) (hl : 4 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n + 1)
    (hpd : ¬ p ∣ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  have hn : 1 ≤ lab.n := hlab.1
  have hd5 : 5 ≤ lab.rank + 1 := by omega
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn hpn hpd hl hd5 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) :=
    fun h => absurd (congrArg Prod.fst h) (by omega)
  have hr : 1 ≤ (l + 1) - 1 := by omega
  have hL : GGTorusLift p (((l + 1) - 1) - 1)
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) := by
    have h := ggTorusLift_unitary (p := p) (d := l + 1) hK hn (by omega) hdq hp hpn
    have hrank : ggUnitaryTorusRank p (l + 1) = ((l + 1) - 1) - 1 := by
      rw [ggUnitaryTorusRank, if_neg hpd]
      omega
    rw [hrank] at h
    exact h
  exact ⟨K, i1, i2, hK, ⟨hQ', ggTorusGenTableB_of_rk (r := (l + 1) - 1) hp hr hL
    (ggTorusGenTableBRk_PSU_coprime hK hn (by omega) hp hpn hpd
      (LineU.unitaryUniversalCover_holds n (l + 1) K hK hd5
        (ggrkc_ne_six_one_of_not_dvd hp hpn hpd)))⟩⟩

end CFSG.StandardType
