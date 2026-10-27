module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixModel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixLift
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixTorus
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixClosure
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkDiag
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

private def sixOneZ {M : Type} [Group M] (L' : Subgroup M) : Subgroup L' where
  carrier := {z | z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1}
  one_mem' := ⟨Subgroup.one_mem _, ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, k, hxk⟩ ⟨hy, l, hyl⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ⟨max k l, ?_⟩⟩
    have hcomm : Commute y x := Subgroup.mem_center_iff.mp hx y
    have hxk' : x ^ 2 ^ max k l = 1 := by
      have hd : orderOf x ∣ 2 ^ max k l :=
        (orderOf_dvd_iff_pow_eq_one.mpr hxk).trans (Nat.pow_dvd_pow 2 (le_max_left k l))
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hyl' : y ^ 2 ^ max k l = 1 := by
      have hd : orderOf y ∣ 2 ^ max k l :=
        (orderOf_dvd_iff_pow_eq_one.mpr hyl).trans (Nat.pow_dvd_pow 2 (le_max_right k l))
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    rw [hcomm.symm.mul_pow, hxk', hyl', mul_one]
  inv_mem' := by
    rintro x ⟨hx, k, hxk⟩
    exact ⟨Subgroup.inv_mem _ hx, ⟨k, by rw [inv_pow, hxk, inv_one]⟩⟩

private instance sixOneZ_normal {M : Type} [Group M] (L' : Subgroup M) : (sixOneZ L').Normal :=
  Subgroup.normal_of_le_center (fun _ hz => hz.1)

private theorem ggrk_mem_center_of_scalar {n d : ℕ} {K : Type} [Field K]
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

private theorem ggrk_mem_center_of_commutator_mem_center {G : Type*} [Group G]
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

private theorem mem_center_map_mulAut {G : Type*} [Group G] (e : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G) : e z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ : ∃ x, e x = y := ⟨e⁻¹ y, by simp⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]

private theorem ggtorus_exists_diag_pPart
    {d n p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hp : p.Prime) (s0 : ↥(unitarySU 2 n K d))
    (hs0 : ∃ v : Fin d → K, ((s0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    {c : L'} (hc : φ s0 = c) (hcp : ∃ k : ℕ, c ^ p ^ k = 1) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      (∃ k : ℕ, s ^ p ^ k = 1) ∧ φ s = c := by
  classical
  haveI : Finite ↥(unitarySU 2 n K d) := by infer_instance
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

private theorem isComponentOf_map_quot
    {M : Type} [Group M] {L' : Subgroup M} (Z : Subgroup L') [Z.Normal]
    (hZle : Z ≤ Subgroup.center L')
    {a : MulAut L'} (haZ : Z.map a.toMonoidHom = Z)
    {J' : Subgroup L'}
    (hJ : IsComponentOf J' (ggFix a)) :
    IsComponentOf (J'.map (QuotientGroup.mk' Z)) (ggFix (QuotientGroup.congr Z Z a haZ)) := by
  have hker : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    exact hZle
  have hφ : ∀ l, (QuotientGroup.congr Z Z a haZ) ((QuotientGroup.mk' Z) l) =
      (QuotientGroup.mk' Z) (a l) := fun l => QuotientGroup.congr_mk Z Z a haZ l
  have hperf : ⁅J', J'⁆ = J' := SCFourCover.commutator_eq_self_of_isComponentOf hJ
  exact (SCFourCover.isComponentOf_map_iff (QuotientGroup.mk'_surjective Z) hker hφ hperf).mp hJ

theorem ggTorusGenTableBRk_PSU_six_one
    {p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ 1 + 1) (hpd : p ∣ 6) :
    GGTorusGenTableBRk p (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) (6 - 1) := by
  intro M _ _ L' E E₁ D' J' dm θ hE hpos hr hC hE₁E hE₁C hcard hN hD'E hCD' hD'E₁ hd1 hJ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one le_rfl hpq
  let Z : Subgroup L' := sixOneZ L'
  have hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1 :=
    fun _ => Iff.rfl
  have hZle : Z ≤ Subgroup.center L' := fun _ hz => hz.1
  haveI : Z.Normal := Subgroup.normal_of_le_center hZle
  obtain ⟨φ, hmodel, hdiag⟩ :=
    exists_model_quotient_six_one hK hp hpq hpd hpos hr Z hZ
  have hZ2 : IsPGroup 2 Z := isPGroup_iff_pow_pow_eq_one.mpr (fun z => by
    obtain ⟨k, hk⟩ := z.2.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩)
  have hZnotdvd : ¬ p ∣ Nat.card Z := by
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    rw [hk]
    intro hdvd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hge : 2 ≤ p := hp.two_le
    omega
  have hZker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hZkerNotDvd : ¬ p ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [hZker]; exact hZnotdvd
  have hZkerCen : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L' := by
    rw [hZker]; exact hZle
  have hClauseA : ∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ p = 1 →
      z ∈ Subgroup.centralizer (E : Set M) := by
    intro z hz hzp
    obtain ⟨hzL, hzC⟩ := hz
    let zL : L' := ⟨z, hzL⟩
    have hzcent : zL ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC l l.2
    obtain ⟨u, hu⟩ := hmodel.surj (QuotientGroup.mk zL)
    have hzcentstar : φ u ∈ Subgroup.center (L' ⧸ Z) := by
      rw [hu]
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      change (QuotientGroup.mk' Z) l * (QuotientGroup.mk' Z) zL =
        (QuotientGroup.mk' Z) zL * (QuotientGroup.mk' Z) l
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hzcent l
    have hperfSU : commutator ↥(unitarySU 2 1 K 6) = ⊤ :=
      (LineU.unitaryCoverOddAt_six_two K (by rw [hK]; norm_num)).1
    have hucen : u ∈ Subgroup.center ↥(unitarySU 2 1 K 6) := by
      refine ggrk_mem_center_of_commutator_mem_center (G := ↥(unitarySU 2 1 K 6)) hperfSU
        (fun v => ?_)
      have h1 : φ ⁅u, v⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hzcentstar (φ v)).symm
      obtain ⟨cu, hcu⟩ := hmodel.ker ⁅u, v⁆ h1
      exact ggrk_mem_center_of_scalar hcu
    have hcommSU : ∀ g ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1),
        Commute (u : GL (Fin 6) K) g := by
      intro g hg
      have hcntr := Subgroup.mem_center_iff.mp hucen (⟨g, hg⟩ : ↥(unitarySU 2 1 K 6))
      exact (congrArg Subtype.val hcntr).symm
    have hscal : (u : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K :=
      GGL45TG.SU.mem_scalars_of_commute_su (TableBU.unitaryFieldData_of_card hK le_rfl)
        (by norm_num) (u : GL (Fin 6) K) hcommSU
    rw [largeEvenScalars_def] at hscal
    obtain ⟨cu, hcu⟩ := hscal
    have hconj : ∀ (D : GL (Fin 6) K)
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        conjN D hD u = u := by
      intro D hD
      apply Subtype.ext
      have hDcomm : D * (u : GL (Fin 6) K) = (u : GL (Fin 6) K) * D := by
        rw [← hcu]
        exact (Matrix.GeneralLinearGroup.scalar_commute cu D).symm
      show D * (u : GL (Fin 6) K) * D⁻¹ = (u : GL (Fin 6) K)
      rw [hDcomm]
      group
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨t, D, hD, hDt, hact⟩ := hdiag ⟨e, he⟩
    have hπ : (QuotientGroup.mk' Z) ((L'.normalizerMonoidHom ⟨e, hE he⟩) zL) =
        (QuotientGroup.mk' Z) zL := by
      have h := hact u zL hu.symm
      rw [hconj D hD, hu] at h
      exact h
    have haezOrd : ∃ n : ℕ, orderOf ((L'.normalizerMonoidHom ⟨e, hE he⟩) zL) = p ^ n := by
      have hpoweq : ((L'.normalizerMonoidHom ⟨e, hE he⟩) zL) ^ p = 1 := by
        rw [← map_pow, show zL ^ p = 1 from Subtype.ext (by simpa using hzp), map_one]
      exact CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (n := 1)
        (by simpa using hpoweq)
    have hzOrd : ∃ n : ℕ, orderOf zL = p ^ n := by
      have hpoweq : zL ^ p = 1 := Subtype.ext (by simpa using hzp)
      exact CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (n := 1)
        (by simpa using hpoweq)
    have hfix : (L'.normalizerMonoidHom ⟨e, hE he⟩) zL = zL :=
      CFSG.LieType.CentralExt.eq_of_pElement hZkerCen hZkerNotDvd hπ haezOrd hzOrd
    have hfixM : e * z * e⁻¹ = z := by
      have h := congrArg Subtype.val hfix
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      simpa using h
    calc e * z = e * z * e⁻¹ * e := by group
      _ = z * e := by rw [hfixM]
  refine ⟨hClauseA, ?_⟩
  intro c hc hcp hdisj
  obtain ⟨hdec, hcent⟩ := exists_mul_of_complement_position hp hpos hC hE₁E hE₁C hcard
  have hdE : dm ∈ E := by
    have hdmem : dm ∈ D' ⊓ E₁ := by rw [hD'E₁]; exact Subgroup.mem_zpowers dm
    exact hD'E hdmem.1
  let a : MulAut L' := L'.normalizerMonoidHom ⟨dm, hE hdE⟩
  let cL : L' := ⟨c, hc.1⟩
  have hcpL : ∃ k : ℕ, cL ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hcpOrd : ∃ k : ℕ, orderOf cL = p ^ k := exists_orderOf_eq_prime_pow_iff.mpr hcpL
  have hcE : c ∈ Subgroup.centralizer (E : Set M) := hcent hc
  have hc_comm : ∀ s : ↥(unitarySU 2 1 K 6),
      (∃ v : Fin 6 → K, ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) →
        s ^ p = 1 → (QuotientGroup.mk cL : L' ⧸ Z) * φ s = φ s * (QuotientGroup.mk cL : L' ⧸ Z) := by
    intro s hs hsp
    have hφsp : ∃ n : ℕ, orderOf (φ s) = p ^ n := by
      have h1 : (φ s) ^ p = 1 := by rw [← map_pow, hsp, map_one]
      exact CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (n := 1)
        (by simpa using h1)
    obtain ⟨ℓ, hℓ, hℓp⟩ :=
      CFSG.LieType.CentralExt.exists_pLift_aux (π := QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z) hZkerNotDvd hφsp
    have hℓE : (ℓ : M) ∈ E :=
      torus_lift_mem_E_six_one hpos hp Z hZ hp2 hdiag s hs hsp ℓ hℓ hℓp
    have hcomm : ℓ * c = c * ℓ := Subgroup.mem_centralizer_iff.mp hcE (ℓ : M) hℓE
    have hcommL : ℓ * cL = cL * ℓ := Subtype.ext hcomm
    calc (QuotientGroup.mk' Z) cL * φ s
        = (QuotientGroup.mk' Z) cL * (QuotientGroup.mk' Z) ℓ := by rw [← hℓ]
      _ = (QuotientGroup.mk' Z) (cL * ℓ) := by rw [← map_mul]
      _ = (QuotientGroup.mk' Z) (ℓ * cL) := by rw [hcommL]
      _ = (QuotientGroup.mk' Z) ℓ * (QuotientGroup.mk' Z) cL := by rw [map_mul]
      _ = φ s * (QuotientGroup.mk' Z) cL := by rw [hℓ]
  obtain ⟨s0, hs0diag, hs0eq⟩ :=
    mem_diagImage_of_commute_pTorsion hmodel (by norm_num : 5 ≤ 6) hp hpq
      (QuotientGroup.mk cL) hc_comm
  have hcpStar : ∃ k : ℕ, ((QuotientGroup.mk' Z) cL : L' ⧸ Z) ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcpL
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨sp, hspdiag, hspP, hspEq⟩ :=
    ggtorus_exists_diag_pPart (p := p) hp s0 hs0diag hs0eq hcpStar
  have hcomp : IsComponentOf (J'.subgroupOf L') (ggFix a) :=
    isComponentOf_subgroupOf_ggFix_of_decomp hE hdE hdec hD'E hCD' hD'E₁ hJ
  have haZ : Z.map a.toMonoidHom = Z := by
    apply le_antisymm
    · rintro - ⟨z, hz, rfl⟩
      refine ⟨mem_center_map_mulAut a hz.1, ?_⟩
      obtain ⟨k, hk⟩ := hz.2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · intro z hz
      refine ⟨a⁻¹ z, ⟨mem_center_map_mulAut a⁻¹ hz.1, ?_⟩, by simp⟩
      obtain ⟨k, hk⟩ := hz.2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨t, D, hD, hDt, hact⟩ := hdiag ⟨dm, hdE⟩
  have hActs : ActsDiagU φ (QuotientGroup.congr Z Z a haZ) t := by
    refine ⟨D, hD, hDt, fun s => ?_⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Z (φ s)
    calc (QuotientGroup.congr Z Z a haZ) (φ s)
        = (QuotientGroup.congr Z Z a haZ) ((QuotientGroup.mk' Z) l) := by rw [hl]
      _ = (QuotientGroup.mk' Z) (a l) := QuotientGroup.congr_mk Z Z a haZ l
      _ = φ (conjN D hD s) := hact s l hl
  have hcompMap : IsComponentOf ((J'.subgroupOf L').map (QuotientGroup.mk' Z))
      (ggFix (QuotientGroup.congr Z Z a haZ)) :=
    isComponentOf_map_quot Z hZle haZ hcomp
  obtain ⟨i₀, hIcard, hJeq⟩ :=
    exists_class_of_isComponentOf_ggFix hmodel hActs hcompMap
  let I : Finset (Fin 6) := Finset.univ.filter fun i => t i = t i₀
  have hIcard' : 2 ≤ I.card := hIcard
  have hJeq' : (J'.subgroupOf L').map (QuotientGroup.mk' Z) =
      (TableBUE.blockSU (K := K) (n := 1) I).map φ := hJeq
  have hJL : J' ≤ L' := fun x hx => (hJ.1 hx).1
  let S : Subgroup M := Subgroup.closure {ℓ : M | ∃ ℓ' : L', (ℓ' : M) = ℓ ∧
      (∃ k : ℕ, orderOf ℓ' = p ^ k) ∧
      ∃ x ∈ TableBUE.blockSU (K := K) (n := 1) I,
        (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
        (QuotientGroup.mk ℓ' : L' ⧸ Z) = φ x}
  have hS : S = Subgroup.closure {ℓ : M | ∃ ℓ' : L', (ℓ' : M) = ℓ ∧
      (∃ k : ℕ, orderOf ℓ' = p ^ k) ∧
      ∃ x ∈ TableBUE.blockSU (K := K) (n := 1) I,
        (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
        (QuotientGroup.mk ℓ' : L' ⧸ Z) = φ x} := rfl
  obtain ⟨hSpg, hSJ, hScent⟩ :=
    pLift_block_torus_props hpos hp hp2 Z hZ hdiag I hJL hJeq' S hS
  let W : Set M := {n : M | n ∈ Subgroup.normalizer (E : Set M) ∧
      ∃ (σ : Equiv.Perm (Fin 6)) (n' : L'), (n' : M) = n ∧
        (QuotientGroup.mk n' : L' ⧸ Z) = φ (permSU hmodel.field σ)}
  have hmem := mem_closure_conj_pLift_six_one hpos hp hp2 Z hZ hmodel hdiag I hIcard' S hS
    cL hcpOrd sp hspdiag hspP hspEq.symm
  refine ⟨S, W, hSpg, hScent.trans (Subgroup.centralizer_le hE₁E), hSJ, ?_, ?_⟩
  · intro n hn
    exact hN hn.1
  · exact hmem

end CFSG.StandardType
