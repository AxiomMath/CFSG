module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UEx
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UCard
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UNt
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UMain
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UCase60
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TOneB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Polynomial
open scoped IsMulCommutative
open CFSG.Quasithin.H13.L828T
open CFSG.Quasithin.H

section Final

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

set_option maxHeartbeats 400000 in
theorem ob5_main (c : S828Ctx T L I H h k)
    (hrow : ∃ n : ℕ, Row711L3Nine T L I n)
    (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    (e : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃* DihedralGroup 5)
    (hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h))
    {K : Subgroup G}
    (hK : quasithinIsCComponent K (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
    (hLUK : ch82LU L (ch82U (fsuV T I) h) ≤ K)
    (hKn : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
    (hLUC : ¬ ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G))
    (hfam : ch82LU L (ch82U (fsuV T I) h) ∈ lFamily T) :
    K = ch82LU L (ch82U (fsuV T I) h) := by
  classical
  have hKle : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    le_of_mem_cComp (mem_cComp_iff.mpr hK)
  have hperf : ⁅K, K⁆ = K := hK.2.1
  haveI := ob5_centralAbelian c
  have S := ob5_setup_of_c c
  obtain ⟨y, hyI, -, hyf, hfixy, hKP, hcommy⟩ :=
    ob5_K_normalizes_P c e hkerI hLUK hKle hKn hS hperf hq hLUC
  have hKN0 : K ≤ ob5N0 T I h := by
    intro κ hκ
    refine Subgroup.mem_inf.mpr ⟨?_, hKle hκ⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hKP κ hκ x hx
    · intro hx
      have := hKP κ⁻¹ (inv_mem hκ) _ hx
      simpa [mul_assoc] using this
  have hfP : ∀ g ∈ ch82I (fsuV T I) h,
      ob5dd (ob5dihHom c e hkerI) g = 1 ↔ g ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
    intro g hg
    rw [ob5dd_of_mem' _ hg]
    exact ob5dihHom_ker c e hkerI ⟨g, hg⟩
  obtain ⟨v, hvV, hvf⟩ := ob5_exists_v (ob5dihHom c e hkerI) (ob5dihHom_surj c e hkerI) hfP rfl
    c.hhI S.hPn S.hVh'
  have hvI : v ∈ ch82I (fsuV T I) h := S.hVI v hvV
  have hvP : v ∉ pCoreOf 2 (ch82I (fsuV T I) h) := fun hp => hvf ((hfP v hvI).mpr hp)
  have hv2 : v * v = 1 := by
    have := c.hV.2 v hvV
    rwa [pow_two] at this
  have hVc : ∀ x ∈ fsuV T I, ∀ y ∈ fsuV T I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(fsuV T I)) ⟨y, hy⟩)
  have hV512 : Nat.card ↥(fsuV T I) = 512 := ob5_card_V c hrow
  have hvB : v ∉ ch82B (fsuV T I) h := fun hb => hvP (Subgroup.mem_inf.mp hb).2
  have hcov : ∀ w ∈ fsuV T I, w ∈ ch82B (fsuV T I) h ∨ ∃ b ∈ ch82B (fsuV T I) h, w = v * b :=
    ob5_V_cover (ob5dihHom c e hkerI) hfP (fun x => Subgroup.mem_inf) (fun x hx => S.hVI x hx)
      (fun x hx => by
        have h2 := c.hV.2 x hx
        rwa [pow_two] at h2) hVc hvV hvf
  have hB256 : Nat.card ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I)) = 256 :=
    ob5_card_B c hV512 hvV hvB hcov
  have hrkU : rk ↥(ch82U (fsuV T I) h) = 4 := (c.hC5.2.2.2.1 hrow).2.2.2
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ x.2.1)⟩
  have hU16 : Nat.card ↥(ch82U (fsuV T I) h) = 16 := ob5_card_U_sixteen hU2 hrkU
  have hQB16 := ob5_card_QB c hB256 hU16
  have hM256 : Nat.card (ob5MM T I h) = 2 ^ 8 := ob5_card_M c hQB16
  haveI : Finite (ob5MM T I h) := Nat.finite_of_card_ne_zero (by rw [hM256]; norm_num)
  letI := ob5QBModule c
  have hyN : y ∈ ob5N0 T I h := s828_I_norm_PU c hyI
  have hvN : v ∈ ob5N0 T I h := s828_I_norm_PU c hvI
  have hy5I : y ^ 5 ∈ ch82I (fsuV T I) h := Subgroup.pow_mem _ hyI 5
  have hy5P : y ^ 5 ∈ pCoreOf 2 (ch82I (fsuV T I) h) :=
    (hfP (y ^ 5) hy5I).mp (by rw [ob5dd_pow _ hyI 5, hyf]; decide)
  have hy5N : y ^ 5 ∈ ob5N0 T I h := s828_I_norm_PU c hy5I
  have hρ5 : ob5rho c ⟨y ^ 5, hy5N⟩ = 1 :=
    (ob5_rho_one_iff c (y ^ 5) hy5N).mpr (fun p hp => c.hP2 _ hy5P p hp)
  have hpow : (⟨y, hyN⟩ : ↥(ob5N0 T I h)) ^ 5 = ⟨y ^ 5, hy5N⟩ :=
    Subtype.ext (Subgroup.coe_pow _ _ _)
  have hσ5 : ob5rho c ⟨y, hyN⟩ ^ 5 = 1 := by
    rw [← map_pow, hpow, hρ5]
  have hσ5L : (ob5L (ob5rho c ⟨y, hyN⟩)) ^ 5 = 1 := by
    rw [← ob5L_pow', hσ5]
    exact LinearMap.ext fun m => rfl
  have hfixσ : ∀ w, ob5L (ob5rho c ⟨y, hyN⟩) w = w → w = 0 :=
    fun m hm => ob5_fix_M c y hyN hfixy m hm
  have hσL : aeval (ob5L (ob5rho c ⟨y, hyN⟩)) (cyclotomic 5 (ZMod 2)) = 0 :=
    ob5_aeval_cyc5_zero _ hσ5L hfixσ
  letI : Module (GaloisField 2 4) (ob5MM T I h) :=
    Module.compHom _ (ob5_f16Hom (ob5L (ob5rho c ⟨y, hyN⟩)) hσL)
  haveI : Module.Finite (GaloisField 2 4) (ob5MM T I h) :=
    Module.finite_iff_finite.mpr inferInstance
  have hF : ∀ (a : GaloisField 2 4) (m : ob5MM T I h),
      a • m = ob5_f16Hom (ob5L (ob5rho c ⟨y, hyN⟩)) hσL a m := fun _ _ => rfl
  have hfin : Module.finrank (GaloisField 2 4) (ob5MM T I h) = 2 :=
    ob5_finrank_two hM256 (ob5L (ob5rho c ⟨y, hyN⟩)) hσL
  let R : ↥K →* AddMonoid.End (ob5MM T I h) := (ob5rho c).comp (Subgroup.inclusion hKN0)
  have hcomm : ∀ κ : ↥K, R κ * ob5rho c ⟨y, hyN⟩ = ob5rho c ⟨y, hyN⟩ * R κ := fun κ =>
    ob5_comm_of_commutator_mem_P c y κ hyN (hKN0 κ.2) (hcommy κ κ.2)
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨φ, θ, hθ, hφ⟩ := ob5_rep_of_module (ob5rho c ⟨y, hyN⟩) hσL hF hfin R hcomm
  have hθ_one : ∀ x : ↥K, θ x = 1 → ob5rho c ⟨(x : G), hKN0 x.2⟩ = 1 := by
    intro x hx
    have hφx : φ x = 1 := by
      have h1 := hθ x
      rw [hx] at h1
      apply Units.ext
      apply (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq (GaloisField 2 4)
        (ob5MM T I h) hfin)).injective
      rw [Units.val_one, map_one]
      exact h1.symm.trans Matrix.SpecialLinearGroup.coe_one
    refine AddMonoidHom.ext fun m => ?_
    have h2 := hφ x m
    rw [hφx, Units.val_one, Module.End.one_apply] at h2
    exact h2.symm
  have hnt := ob5_LU_nontriv c hMB2 hcard hrow hQB16
  obtain ⟨l, hl, hlL, hlne⟩ := hnt
  have hlK : l ∈ K := hLUK hlL
  have hψne : (θ.comp (Subgroup.inclusion hLUK)).range ≠ ⊥ := by
    intro hbot
    apply hlne
    have hmem : (θ.comp (Subgroup.inclusion hLUK)) ⟨l, hlL⟩ ∈
        (θ.comp (Subgroup.inclusion hLUK)).range := MonoidHom.mem_range.mpr ⟨⟨l, hlL⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hθ_one ⟨l, hlK⟩ hmem
  have hθbot : θ.range ≠ ⊥ := by
    intro hbot
    apply hψne
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have hmem : θ (Subgroup.inclusion hLUK x) ∈ θ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [MonoidHom.comp_apply, hmem]
    exact Subgroup.one_mem _
  haveI : Group.IsPerfect θ.range := Group.IsPerfect.range θ
  have hD := ob5_perfect_SL_card θ.range hθbot
  rcases hD with h60 | h4080
  ·
    have hLUperf : ⁅ch82LU L (ch82U (fsuV T I) h), ch82LU L (ch82U (fsuV T I) h)⁆ =
        ch82LU L (ch82U (fsuV T I) h) := perfectCore_perfect _
    exact ob5_case60 hLUperf hfam hK hLUK hKle hKn hS hq θ hψne h60
  ·
    exfalso
    have htop : θ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h4080, ob5_card_SL])
    have hsurj : Function.Surjective θ := MonoidHom.range_eq_top.mp htop
    have hKC : ∀ κ ∈ K, ∀ x ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G),
        κ * x * κ⁻¹ * x⁻¹ ∈ pCoreOf 2 K := fun κ hκ x hx =>
      (commutator_centralizer_le_828 hKle hKn hperf hq (fun hKC => hLUC (hLUK.trans hKC)))
        (Subgroup.commutator_mem_commutator hκ hx)
    exact ob5_not_4080 c hKN0 hKC hyN hyI hvN hvI hv2 (ob5dihHom c e hkerI)
      (fun g => ob5dihHom_ker c e hkerI g) hyf hvf hσL hF
      (Module.finBasisOfFinrankEq (GaloisField 2 4) (ob5MM T I h) hfin) φ θ hθ hsurj hφ

end Final

set_option maxHeartbeats 400000 in
theorem oneBL3Nine5_828_holds
    (hE214 : ASInputs.AS_E_2_14) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB3 : MB3_828) (hSyl : Sylow822VB_828) (hMB2 : MB2_828) :
    OneBL3Nine5_828 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hLrow hD10 K hK hLUK
  obtain ⟨e⟩ := hD10
  have c := s828_ctx hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB3 hSyl hyp h731
    h821 hrow hH hh hC
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨-, -, -, -, -, -, -, hkerI, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := id hC
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, -, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, -⟩ := lu_facts_828 hLU hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ x.2.1)⟩
  have hH2 : pCoreOf 2 (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hU2
  have hS : QuasithinUnique.IsSylowTwoOf T
      (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  have hKn := lemma_1_2_4_normal hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 hH2 hS
    hfam hLUK hK hLUT
  have hKle : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    le_of_mem_cComp (mem_cComp_iff.mpr hK)
  have hKn' : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤
      Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp hKn
  have hq := h827 G T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  exact ob5_main c hLrow hMB2 hcard e hkerI hK hLUK hKn' hq hS hLUC hfam

end CFSG.Quasithin.H13
