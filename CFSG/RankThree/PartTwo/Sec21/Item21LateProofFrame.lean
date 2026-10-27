module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofTypeTwo
import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21LateProof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 (blockHom diagE diagUnits coe_diagUnits slPi glPi)

theorem item2118Frame_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2118Frame := by
  intro G _ _ A E U c L hpair hnL hC h27 hS3
  obtain ⟨n, hn, hev, ⟨eL⟩⟩ := hnL
  obtain ⟨eS⟩ := hS3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hpair.mem_S.1.2.1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h3 : ∀ a ∈ A, a ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h3 c hcA) hc1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hLs : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hcA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩) ?_
    rw [Nat.card_zpowers, hc3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S L hLs)
      fun y hy => h3 y hy.1
  set T : Subgroup.normalizer (L : Set G) →* MulAut (lBar L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hT
  have hTmk : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : G) (hl : l ∈ L),
      T ⟨g, hg⟩ ((⟨l, hl⟩ : L) : lBar L) =
        ((⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp hl⟩ : L) : lBar L) :=
    fun _ _ _ _ => rfl
  have hTinner : ∀ (l₀ : G) (hl₀ : l₀ ∈ L) (z : lBar L),
      T ⟨l₀, Subgroup.le_normalizer hl₀⟩ z =
        ((⟨l₀, hl₀⟩ : L) : lBar L) * z * ((⟨l₀, hl₀⟩ : L) : lBar L)⁻¹ := by
    intro l₀ hl₀ z
    induction z using QuotientGroup.induction_on with
    | H l => rfl
  have hT1 : ∀ (a : G) (ha : a ∈ A), T ⟨a, hAL ha⟩ = 1 → a ∈ Subgroup.zpowers c := by
    intro a ha h
    rw [← hCA]
    exact ⟨ha, ⟨a, hAL ha⟩, h, rfl⟩
  have hTz : ∀ (v : G) (hv : v ∈ Subgroup.normalizer (L : Set G)),
      v ∈ Subgroup.zpowers c → T ⟨v, hv⟩ = 1 := by
    intro v hv hvc
    rw [← hCA] at hvc
    obtain ⟨-, ⟨v', hv'⟩, hker, rfl⟩ := hvc
    exact hker
  obtain ⟨-, -, hN3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hθ3 : ∀ l : L, l ∈ aschbacherSolvableCore 3 L → ∀ k : ℕ, l ^ 3 ^ k = 1 → l = 1 := by
    intro l hl k hlk
    have h1 := orderOf_dvd_natCard (⟨l, hl⟩ : aschbacherSolvableCore 3 L)
    have h2 : orderOf (⟨l, hl⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hlk))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact congrArg Subtype.val hj
    · exfalso
      apply hN3
      rw [hj] at h1
      exact (dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h1
  obtain ⟨π, p, f, K, _, hPi, hmod, ε, D, hD, hconj, hconj'⟩ := hC
  obtain ⟨rfl, rfl, rfl⟩ := SL3Lines.params_eq hn hev hPi hmod (eL.symm.trans ε)
  have := hPi.finite
  have hf2 : 2 ≤ f := by obtain ⟨k, hk⟩ := hev; omega
  have h2 : (2 : K) = 0 := SL3Lines.two_eq_zero_of_mulEquiv hf2
    (fun y hy => (Sec4.mem_slPi_true _).mp hy) (eL.symm.trans ε)
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  have hτ₀0 : τ₀ ≠ 0 := by
    rintro rfl
    norm_num at hτ₀
  set τu : Kˣ := Units.mk0 τ₀ hτ₀0 with hτudef
  have hτuv : (τu : K) = τ₀ := rfl
  have hτu3 : τu ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hτuv, hτ₀, Units.val_one])
  have hτu1 : τu ≠ 1 := fun h => hτ₀1 (by rw [← hτuv, h, Units.val_one])
  have hτu : τu ∈ rootsOfUnity 3 K := (mem_rootsOfUnity _ _).mpr hτu3
  set ψ : lBar L →* GL (Fin 3) K :=
    (slPi true 3 (2 ^ f) K).subtype.comp ε.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (slPi true 3 (2 ^ f) K).subtype_injective.comp ε.injective
  have hscal : ∀ N : GL (Fin 3) K, (∀ z, N * ψ z = ψ z * N) → N ∈ StatedScalars (Fin 3) K := by
    intro N hN
    refine Sec4.mem_statedScalars_of_commute (π := true) (p := 2) (f := f)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hτ₀ hτ₀1 fun M hM => ?_
    have := hN (ε.symm ⟨M, hM⟩)
    simpa [hψ] using this
  have hTone : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)) (N : GL (Fin 3) K),
      N ∈ StatedScalars (Fin 3) K → (∀ z, ψ (T ⟨a, ha⟩ z) = N * ψ z * N⁻¹) →
        T ⟨a, ha⟩ = 1 := by
    intro a ha N hNs hN
    ext z
    apply hψinj
    rw [hN, MulAut.one_apply, ← Sec4.commute_of_mem_statedScalars hNs (ψ z),
      mul_inv_cancel_right]
  have hyA : ∀ (a : G) (ha : a ∈ A), ∃ y ∈ D, ∀ z, ψ (T ⟨a, hAL ha⟩ z) = y * ψ z * y⁻¹ := by
    intro a ha
    obtain ⟨y, hyD, hy⟩ := hconj _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL ha, ha, rfl⟩)
    exact ⟨y, hyD, fun z => hy z⟩
  obtain ⟨g, -, hdiag, hsurj⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  have hAst : ∀ s ∈ rootsOfUnity 3 K, ∀ t ∈ rootsOfUnity 3 K, ∃ (a : G) (ha : a ∈ A)
      (y : GL (Fin 3) K) (l : Kˣ),
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t ∧
        ∀ z, ψ (T ⟨a, hAL ha⟩ z) = y * ψ z * y⁻¹ := by
    intro s hs t ht
    obtain ⟨y, hyD, l, hyl⟩ := hsurj s hs t ht
    obtain ⟨τ, hτ, hτy⟩ := hconj' y hyD
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    exact ⟨a, haA, y, l, hyl, fun z => hτy z⟩
  have htype1 : ∀ (b : G) (hb : b ∈ A ⊓ L) (y : GL (Fin 3) K) (l s t : Kˣ), s ^ 3 = 1 →
      t ^ 3 = 1 → g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t →
      (∀ z, ψ (T ⟨b, hAL hb.1⟩ z) = y * ψ z * y⁻¹) → ¬ (s = 1 ∧ t = 1) →
      (∃ μ : Kˣ, g⁻¹ * ψ ((⟨b, hb.2⟩ : L) : lBar L) * g =
        GeneralLinearGroup.scalar (Fin 3) μ * diagUnits 1 s t) ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t := by
    intro b hb y l s t hs ht hyg hy hst
    set bb : lBar L := ((⟨b, hb.2⟩ : L) : lBar L) with hbb
    have hbbT : ∀ z, ψ (T ⟨b, hAL hb.1⟩ z) = ψ bb * ψ z * (ψ bb)⁻¹ := by
      intro z
      have : T ⟨b, hAL hb.1⟩ z = bb * z * bb⁻¹ := hTinner b hb.2 z
      rw [this, map_mul, map_mul, map_inv]
    obtain ⟨lam, hlam⟩ := hscal (y⁻¹ * ψ bb) fun z => by
      calc y⁻¹ * ψ bb * ψ z = y⁻¹ * (ψ bb * ψ z * (ψ bb)⁻¹) * ψ bb := by group
        _ = y⁻¹ * (y * ψ z * y⁻¹) * ψ bb := by rw [← hbbT z, hy z]
        _ = ψ z * (y⁻¹ * ψ bb) := by group
    have hMb : g⁻¹ * ψ bb * g =
        GeneralLinearGroup.scalar (Fin 3) (l * lam) * diagUnits 1 s t := by
      have h1 : ψ bb = y * GeneralLinearGroup.scalar (Fin 3) lam := by
        rw [hlam]
        group
      calc g⁻¹ * ψ bb * g = g⁻¹ * y * g * GeneralLinearGroup.scalar (Fin 3) lam := by
            rw [h1]
            calc g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) lam) * g
                = g⁻¹ * y * (GeneralLinearGroup.scalar (Fin 3) lam * g) := by group
              _ = g⁻¹ * y * (g * GeneralLinearGroup.scalar (Fin 3) lam) := by
                rw [SL3Lines.scalar_mul_comm]
              _ = g⁻¹ * y * g * GeneralLinearGroup.scalar (Fin 3) lam := by group
        _ = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
            GeneralLinearGroup.scalar (Fin 3) lam := by rw [hyg]
        _ = GeneralLinearGroup.scalar (Fin 3) (l * lam) * diagUnits 1 s t := by
            rw [mul_assoc, ← SL3Lines.scalar_mul_comm lam, ← mul_assoc, ← map_mul]
    have hbb3 : ψ bb ^ 3 = 1 := by
      have : bb ^ 3 = 1 := by
        rw [hbb, ← QuotientGroup.mk_pow]
        have : (⟨b, hb.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using h3 b hb.1)
        rw [this, QuotientGroup.mk_one]
      rw [← map_pow, this, map_one]
    have hbbdet : ((ψ bb : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      (Sec4.mem_slPi_true _).mp (ε bb).2
    exact ⟨⟨l * lam, hMb⟩, distinct_of_conj_diag hs ht hMb hbbdet hbb3 hst⟩
  have hdistinct : ∀ (b : G) (hb : b ∈ A ⊓ L), b ∉ Subgroup.zpowers c →
      ∃ μ s t : Kˣ, g⁻¹ * ψ ((⟨b, hb.2⟩ : L) : lBar L) * g =
        GeneralLinearGroup.scalar (Fin 3) μ * diagUnits 1 s t ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t := by
    intro b hb hbc
    obtain ⟨y, hyD, hy⟩ := hyA b hb.1
    obtain ⟨l, s, t, hs, ht, hyg⟩ := hdiag y hyD
    have hst : ¬ (s = 1 ∧ t = 1) := by
      rintro ⟨rfl, rfl⟩
      rw [SL3Lines.diagUnits_one_one_one, mul_one] at hyg
      have hyS : y = GeneralLinearGroup.scalar (Fin 3) l := by
        calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          _ = GeneralLinearGroup.scalar (Fin 3) l := by rw [hyg, conj_scalar]
      exact hbc (hT1 b hb.1 (hTone b (hAL hb.1) y ⟨l, hyS.symm⟩ hy))
    obtain ⟨⟨μ, hμ⟩, hd⟩ := htype1 b hb y l s t ((mem_rootsOfUnity _ _).mp hs)
      ((mem_rootsOfUnity _ _).mp ht) hyg hy hst
    exact ⟨μ, s, t, hμ, hd⟩
  have hzmem : GeneralLinearGroup.scalar (Fin 3) τu ∈ slPi true 3 (2 ^ f) K :=
    Sec4.scalar_mem_slPi_of_cube hPi hmod hτ₀
  set zb : lBar L := ε.symm ⟨GeneralLinearGroup.scalar (Fin 3) τu, hzmem⟩ with hzb
  have hψz : ψ zb = GeneralLinearGroup.scalar (Fin 3) τu := by simp [hψ, hzb]
  have hzfix : ∀ (a : G) (ha : a ∈ A), T ⟨a, hAL ha⟩ zb = zb := by
    intro a ha
    obtain ⟨y, -, hy⟩ := hyA a ha
    apply hψinj
    rw [hy, hψz, conj_scalar]
  have hz3 : zb ^ 3 = 1 := by
    apply hψinj
    rw [map_pow, hψz, ← map_pow, hτu3, map_one, map_one]
  have hz1 : zb ≠ 1 := by
    intro h
    have h' := congrArg ψ h
    rw [hψz, map_one] at h'
    apply hτu1
    have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h'
    simp only [scalar_apply_self, Units.val_one, Matrix.one_apply_eq] at h00
    exact Units.ext h00
  have hzcent : ∀ x : lBar L, zb * x = x * zb := by
    intro x
    apply hψinj
    rw [map_mul, map_mul, hψz, SL3Lines.scalar_mul_comm]
  obtain ⟨y, hyL, hy3, hyAc, hy1, hycent⟩ : ∃ (y : G) (hyL : y ∈ L), y ^ 3 = 1 ∧
      (∀ a ∈ A, a * y = y * a) ∧ ((⟨y, hyL⟩ : L) : lBar L) ≠ 1 ∧
      ∀ x : lBar L, ((⟨y, hyL⟩ : L) : lBar L) * x = x * ((⟨y, hyL⟩ : L) : lBar L) := by
    set N := aschbacherSolvableCore 3 L with hNdef
    let α : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
    have hαN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
      intro a n hn
      show (α a) n ∈ aschbacherSolvableCore 3 L
      rw [← Sec4.map_aschbacherSolvableCore (α a)]
      exact Subgroup.mem_map_of_mem _ hn
    have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
    have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3 α N hαN hN3
    have hxmem : zb ∈ {q : L ⧸ N | ∀ a : A,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
      intro a
      have h1 := hzfix a a.2
      obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective N zb
      rw [← hx₀] at h1 ⊢
      exact h1
    rw [hlift] at hxmem
    obtain ⟨x₁, hx₁, hx₁x⟩ := hxmem
    obtain ⟨e, m, hm3, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₁).ne' 3 (by norm_num)
    set y₁ : L := x₁ ^ m with hy₁
    have hx₁A : ∀ a ∈ A, a * (x₁ : G) = x₁ * a := by
      intro a ha
      have h1 : (a : G) * x₁ * a⁻¹ = x₁ := congrArg Subtype.val (hx₁ ⟨a, ha⟩)
      calc a * (x₁ : G) = a * x₁ * a⁻¹ * a := by group
        _ = x₁ * a := by rw [h1]
    have hy₁A : ∀ a ∈ A, a * (y₁ : G) = (y₁ : G) * a := by
      intro a ha
      rw [hy₁, Subgroup.coe_pow]
      exact ((Commute.pow_right (hx₁A a ha) m)).eq
    have hy3e : y₁ ^ 3 ^ e = 1 := by
      rw [hy₁, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    have hπy : ((y₁ : L) : lBar L) = zb ^ m := by
      rw [hy₁, QuotientGroup.mk_pow]
      exact congrArg (· ^ m) hx₁x
    have hy3' : y₁ ^ 3 = 1 := by
      have hmemN : y₁ ^ 3 ∈ N := by
        have h1 : ((y₁ ^ 3 : L) : lBar L) = 1 := by
          rw [QuotientGroup.mk_pow, hπy, ← pow_mul, mul_comm, pow_mul, hz3, one_pow]
        exact (QuotientGroup.eq_one_iff _).mp h1
      exact hθ3 _ hmemN e (by rw [← pow_mul, mul_comm, pow_mul, hy3e, one_pow])
    have hzm : zb ^ m ≠ 1 := by
      intro hzm
      apply hz1
      rw [pow_eq_pow_mod_three hz3 m] at hzm
      rcases (show m % 3 = 1 ∨ m % 3 = 2 by omega) with h | h
      · rwa [h, pow_one] at hzm
      · rw [h] at hzm
        have e : zb ^ 3 = zb ^ 2 * zb := pow_succ zb 2
        rw [hz3, hzm, one_mul] at e
        exact e.symm
    refine ⟨(y₁ : G), y₁.2, by rw [← Subgroup.coe_pow, hy3', Subgroup.coe_one], hy₁A, ?_, ?_⟩
    · exact fun h => hzm (hπy.symm.trans h)
    · intro x
      exact hπy ▸ (Commute.pow_left (hzcent x) m).eq
  have hyAmem : y ∈ A := by
    have hE := Sec13.isElemAbelian_sup hAe (Sec13.isElemAbelian_zpowers hy3)
      (fun a ha z hz => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (Commute.zpow_right (hyAc a ha) k).eq)
    rw [← hmax _ hE le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hTy : T ⟨y, hAL hyAmem⟩ = 1 := by
    ext z
    rw [show T ⟨y, hAL hyAmem⟩ z = _ from hTinner y hyL z, hycent z, mul_inv_cancel_right,
      MulAut.one_apply]
  have hcL : c ∈ L := by
    have hyc := hT1 y hyAmem hTy
    have hy1' : y ≠ 1 := by
      rintro rfl
      exact hy1 (QuotientGroup.mk_one _)
    have heq : Subgroup.zpowers y = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyc)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, orderOf_eq_prime hy3 hy1'])
    have hcy : c ∈ Subgroup.zpowers y := by
      rw [heq]
      exact Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hyL) hcy
  set σ₀ : starOf A L := eS.symm (Equiv.swap 0 1 * Equiv.swap 1 2) with hσ₀
  have hσ₀3 : orderOf σ₀ = 3 := by
    rw [hσ₀, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  obtain ⟨⟨w, hwN⟩, hwL, hwσ⟩ := σ₀.2
  have hwL' : w ∈ L := Subgroup.mem_subgroupOf.mp hwL
  have hφ3 : orderOf (A.normalizerMonoidHom ⟨w, hwN⟩) = 3 := by
    rw [hwσ, Subgroup.orderOf_coe, hσ₀3]
  have hwnot : ¬ ∀ a ∈ A, w * a * w⁻¹ = a := by
    intro h
    have h1 : A.normalizerMonoidHom ⟨w, hwN⟩ = 1 := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
      exact h a a.2
    rw [h1, orderOf_one] at hφ3
    omega
  have hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a := by
    intro a ha
    have h1 : (A.normalizerMonoidHom ⟨w, hwN⟩) ^ 3 = 1 := by
      rw [← hφ3]
      exact pow_orderOf_eq_one _
    have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h1
    simp only [MulAut.one_apply] at h2
    rw [← map_pow] at h2
    have e : (⟨w, hwN⟩ : Subgroup.normalizer (A : Set G)) ^ 3 =
        ⟨w ^ 3, Subgroup.pow_mem _ hwN 3⟩ := Subtype.ext (by simp)
    rw [e, Sec4.normalizerMonoidHom_apply_coe] at h2
    exact h2
  have hwA : ∀ a ∈ A, w * a * w⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hwN a).mp ha
  set wb : lBar L := ((⟨w, hwL'⟩ : L) : lBar L) with hwb
  have hTw : ∀ z, T ⟨w, Subgroup.le_normalizer hwL'⟩ z = wb * z * wb⁻¹ :=
    fun z => hTinner w hwL' z
  set N : GL (Fin 3) K := g⁻¹ * ψ wb * g with hNdef
  have hdiagw : (∀ i j : Fin 3, i ≠ j → (N : Matrix (Fin 3) (Fin 3) K) i j = 0) → False := by
    intro hN
    apply hwnot
    intro a ha
    obtain ⟨ya, hyaD, hya⟩ := hyA a ha
    obtain ⟨la, sa, ta, -, -, hyag⟩ := hdiag ya hyaD
    have hNd : (N : Matrix (Fin 3) (Fin 3) K) =
        diagonal fun i => (N : Matrix (Fin 3) (Fin 3) K) i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij]
        exact hN i j hij
    have hNY : N * (g⁻¹ * ya * g) = (g⁻¹ * ya * g) * N := by
      rw [hyag, Sec4.scalar_mul_diagUnits_eq]
      apply Units.ext
      rw [Units.val_mul N, Units.val_mul _ N, Sec4.coe_diagHom, hNd, diagonal_mul_diagonal,
        diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hc : ψ wb * ya = ya * ψ wb := by
      have e1 : ψ wb * ya = g * (N * (g⁻¹ * ya * g)) * g⁻¹ := by
        rw [hNdef]
        group
      have e2 : ya * ψ wb = g * ((g⁻¹ * ya * g) * N) * g⁻¹ := by
        rw [hNdef]
        group
      rw [e1, e2, hNY]
    have hfix : T ⟨a, hAL ha⟩ wb = wb := by
      apply hψinj
      rw [hya wb, ← hc, mul_inv_cancel_right]
    rw [hwb, hTmk] at hfix
    have hθ := QuotientGroup.eq.mp hfix
    have hmem : (a * w * a⁻¹)⁻¹ * w ∈ A := by
      have e : (a * w * a⁻¹)⁻¹ * w = a * (w⁻¹ * a⁻¹ * w) := by group
      rw [e]
      refine A.mul_mem ha ?_
      have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) a⁻¹).mp (A.inv_mem ha)
      simpa using h'
    have hu3 : ((⟨a * w * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL ha) w).mp hwL'⟩ : L)⁻¹ *
        ⟨w, hwL'⟩) ^ 3 ^ 1 = 1 := by
      apply Subtype.ext
      simpa using h3 _ hmem
    have hu1 := hθ3 _ hθ 1 hu3
    have hu1' : (a * w * a⁻¹)⁻¹ * w = 1 := by simpa using congrArg Subtype.val hu1
    have haw : a * w * a⁻¹ = w := inv_mul_eq_one.mp hu1'
    have hc' : a * w = w * a := by
      calc a * w = a * w * a⁻¹ * a := by group
        _ = w * a := by rw [haw]
    calc w * a * w⁻¹ = a * w * w⁻¹ := by rw [hc']
      _ = a := by group
  have hfr : ∀ (y : GL (Fin 3) K) (l s t : Kˣ),
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t →
      ψ wb * y = y * ψ wb →
      (N : Matrix (Fin 3) (Fin 3) K) *
          diagonal ![(l : K), ((l * s : Kˣ) : K), ((l * t : Kˣ) : K)] =
        diagonal ![(l : K), ((l * s : Kˣ) : K), ((l * t : Kˣ) : K)] *
          (N : Matrix (Fin 3) (Fin 3) K) := by
    intro y l s t hyg hc
    have h1 : N * (g⁻¹ * y * g) = (g⁻¹ * y * g) * N := by
      rw [hNdef]
      calc g⁻¹ * ψ wb * g * (g⁻¹ * y * g) = g⁻¹ * (ψ wb * y) * g := by group
        _ = g⁻¹ * (y * ψ wb) * g := by rw [hc]
        _ = g⁻¹ * y * g * (g⁻¹ * ψ wb * g) := by group
    rw [hyg, Sec4.scalar_mul_diagUnits_eq] at h1
    have h2 := congrArg Units.val h1
    rw [Units.val_mul N, Units.val_mul _ N, Sec4.coe_diagHom] at h2
    exact h2
  have hmu : ∀ μ u v : Kˣ, u ≠ v → ((μ * u : Kˣ) : K) ≠ ((μ * v : Kˣ) : K) :=
    fun μ u v huv h => huv (mul_left_cancel (Units.ext h))
  have hcommy : ∀ (a : G) (ha : a ∈ A) (y₀ : GL (Fin 3) K),
      (∀ z, ψ (T ⟨a, hAL ha⟩ z) = y₀ * ψ z * y₀⁻¹) →
      ((y₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace ≠ 0 →
      a⁻¹ * (w * a * w⁻¹) ∈ Subgroup.zpowers c → ψ wb * y₀ = y₀ * ψ wb := by
    intro a ha y₀ hy₀ htr hac
    have hwaA : w * a * w⁻¹ ∈ A := hwA a ha
    have hTwa : T ⟨w * a * w⁻¹, hAL hwaA⟩ = T ⟨a, hAL ha⟩ := by
      have e1 : (⟨w * a * w⁻¹, hAL hwaA⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨a, hAL ha⟩ * ⟨a⁻¹ * (w * a * w⁻¹), hAL (A.mul_mem (A.inv_mem ha) hwaA)⟩ :=
        Subtype.ext (by
          show w * a * w⁻¹ = a * (a⁻¹ * (w * a * w⁻¹))
          group)
      rw [e1, map_mul, hTz _ _ hac, mul_one]
    have hTwa' : T ⟨w * a * w⁻¹, hAL hwaA⟩ = T ⟨w, Subgroup.le_normalizer hwL'⟩ *
        T ⟨a, hAL ha⟩ * (T ⟨w, Subgroup.le_normalizer hwL'⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have hcommT : T ⟨w, Subgroup.le_normalizer hwL'⟩ * T ⟨a, hAL ha⟩ =
        T ⟨a, hAL ha⟩ * T ⟨w, Subgroup.le_normalizer hwL'⟩ := by
      have h := hTwa'.symm.trans hTwa
      rwa [mul_inv_eq_iff_eq_mul] at h
    have heq : ∀ z, ψ wb * (y₀ * ψ z * y₀⁻¹) * (ψ wb)⁻¹ =
        y₀ * (ψ wb * ψ z * (ψ wb)⁻¹) * y₀⁻¹ := by
      intro z
      have h1 := congrArg (fun φ : MulAut (lBar L) => ψ (φ z)) hcommT
      simp only [MulAut.mul_apply, hTw, map_mul ψ, map_inv ψ, hy₀] at h1
      exact h1
    obtain ⟨lam, hlam⟩ := hscal ((ψ wb)⁻¹ * y₀⁻¹ * ψ wb * y₀) fun z => by
      calc (ψ wb)⁻¹ * y₀⁻¹ * ψ wb * y₀ * ψ z
          = (ψ wb)⁻¹ * y₀⁻¹ * (ψ wb * (y₀ * ψ z * y₀⁻¹) * (ψ wb)⁻¹) * ψ wb * y₀ := by group
        _ = (ψ wb)⁻¹ * y₀⁻¹ * (y₀ * (ψ wb * ψ z * (ψ wb)⁻¹) * y₀⁻¹) * ψ wb * y₀ := by
          rw [heq z]
        _ = ψ z * ((ψ wb)⁻¹ * y₀⁻¹ * ψ wb * y₀) := by group
    have hPy : ψ wb * y₀ * (ψ wb)⁻¹ = y₀ * GeneralLinearGroup.scalar (Fin 3) lam := by
      have e1 : ψ wb * y₀ = y₀ * ψ wb * GeneralLinearGroup.scalar (Fin 3) lam := by
        rw [hlam]
        group
      calc ψ wb * y₀ * (ψ wb)⁻¹ =
          y₀ * ψ wb * GeneralLinearGroup.scalar (Fin 3) lam * (ψ wb)⁻¹ := by rw [e1]
        _ = y₀ * (ψ wb * GeneralLinearGroup.scalar (Fin 3) lam * (ψ wb)⁻¹) := by group
        _ = y₀ * GeneralLinearGroup.scalar (Fin 3) lam := by rw [conj_scalar]
    have htr' : (lam : K) * ((y₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
        ((y₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
      rw [← Sec4.trace_mul_scalar, ← hPy]
      have := Sec4.trace_inv_conj (ψ wb)⁻¹ y₀
      rwa [inv_inv] at this
    have hlam1 : lam = 1 := by
      apply Units.ext
      rw [Units.val_one]
      have h0 : ((lam : K) - 1) * ((y₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
        rw [sub_mul, htr', one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right htr)
    rw [hlam1, map_one, mul_one] at hPy
    calc ψ wb * y₀ = ψ wb * y₀ * (ψ wb)⁻¹ * ψ wb := by group
      _ = y₀ * ψ wb := by rw [hPy]
  have htrace : ∀ (l s t : Kˣ),
      ((GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).trace = (l : K) * (1 + s + t) := by
    intro l s t
    rw [Sec4.scalar_mul_diagUnits_eq, Sec4.coe_diagHom, Matrix.trace_diagonal,
      Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_mul]
    ring
  have hP1 : ∃ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∉ Subgroup.zpowers c := by
    by_contra hno
    push Not at hno
    obtain ⟨a₁, ha₁, y₁, l₁, hy₁g, hy₁⟩ := hAst 1 (one_mem _) τu hτu
    obtain ⟨a₂, ha₂, y₂, l₂, hy₂g, hy₂⟩ := hAst τu hτu 1 (one_mem _)
    have htr1 : ((y₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace ≠ 0 := by
      rw [← Sec4.trace_inv_conj g y₁, hy₁g, htrace, Units.val_one, hτuv,
        show (1 : K) + 1 + τ₀ = τ₀ by linear_combination h2]
      exact mul_ne_zero l₁.ne_zero hτ₀0
    have htr2 : ((y₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace ≠ 0 := by
      rw [← Sec4.trace_inv_conj g y₂, hy₂g, htrace, Units.val_one, hτuv,
        show (1 : K) + τ₀ + 1 = τ₀ by linear_combination h2]
      exact mul_ne_zero l₂.ne_zero hτ₀0
    have hm₁ := hfr y₁ l₁ 1 τu hy₁g (hcommy a₁ ha₁ y₁ hy₁ htr1 (hno a₁ ha₁))
    have hm₂ := hfr y₂ l₂ τu 1 hy₂g (hcommy a₂ ha₂ y₂ hy₂ htr2 (hno a₂ ha₂))
    have hτ1' : (1 : Kˣ) ≠ τu := Ne.symm hτu1
    apply hdiagw
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm₂ (by simpa using hmu l₂ 1 τu hτ1')
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm₁ (by simpa using hmu l₁ 1 τu hτ1')
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm₂ (by simpa using (hmu l₂ 1 τu hτ1').symm)
    · exact absurd rfl hij
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm₁ (by simpa using hmu l₁ 1 τu hτ1')
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm₁ (by simpa using (hmu l₁ 1 τu hτ1').symm)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm₁ (by simpa using (hmu l₁ 1 τu hτ1').symm)
    · exact absurd rfl hij
  obtain ⟨a₀, ha₀, ha₀c⟩ := hP1
  have hb₁A : a₀⁻¹ * (w * a₀ * w⁻¹) ∈ A := A.mul_mem (A.inv_mem ha₀) (hwA a₀ ha₀)
  have hb₁L : a₀⁻¹ * (w * a₀ * w⁻¹) ∈ L := by
    have h1 : a₀⁻¹ * w * a₀⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL (A.inv_mem ha₀)) w).mp hwL'
    have e : a₀⁻¹ * (w * a₀ * w⁻¹) = a₀⁻¹ * w * a₀⁻¹⁻¹ * w⁻¹ := by group
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hwL')
  have hP2 : ∃ b ∈ A ⊓ L, w * b * w⁻¹ ≠ b := by
    by_contra hno
    push Not at hno
    have hwb₁ := hno _ ⟨hb₁A, hb₁L⟩
    obtain ⟨μ, s, t, hμ, hs1, ht1, hst⟩ := hdistinct _ ⟨hb₁A, hb₁L⟩ ha₀c
    have hc : ψ wb * ψ ((⟨_, hb₁L⟩ : L) : lBar L) = ψ ((⟨_, hb₁L⟩ : L) : lBar L) * ψ wb := by
      rw [← map_mul, ← map_mul]
      congr 1
      rw [hwb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show w * (a₀⁻¹ * (w * a₀ * w⁻¹)) = a₀⁻¹ * (w * a₀ * w⁻¹) * w
      calc w * (a₀⁻¹ * (w * a₀ * w⁻¹)) =
          w * (a₀⁻¹ * (w * a₀ * w⁻¹)) * w⁻¹ * w := by group
        _ = a₀⁻¹ * (w * a₀ * w⁻¹) * w := by rw [hwb₁]
    have hm := hfr _ μ s t hμ hc
    apply hdiagw
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm (by simpa using hmu μ 1 s (Ne.symm hs1))
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm (by simpa using hmu μ 1 t (Ne.symm ht1))
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm
        (by simpa using (hmu μ 1 s (Ne.symm hs1)).symm)
    · exact absurd rfl hij
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm (by simpa using hmu μ s t hst)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm
        (by simpa using (hmu μ 1 t (Ne.symm ht1)).symm)
    · exact Sec4.entry_eq_zero_of_commute_diagonal hm (by simpa using (hmu μ s t hst).symm)
    · exact absurd rfl hij
  have hcard9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    obtain ⟨a₃, ha₃, y₃, l₃, hy₃g, hy₃⟩ := hAst 1 (one_mem _) τu hτu
    have ha₃L : a₃ ∉ L := by
      intro ha₃L
      exact (htype1 a₃ ⟨ha₃, ha₃L⟩ y₃ l₃ 1 τu (one_pow 3) hτu3 hy₃g hy₃
        (fun h => hτu1 h.2)).2.1 rfl
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [← h27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases j
    · exfalso
      have hbot := Subgroup.eq_bot_of_card_eq (A ⊓ L) (by rw [hj, pow_zero])
      have hc' : c ∈ A ⊓ L := ⟨hcA, hcL⟩
      rw [hbot, Subgroup.mem_bot] at hc'
      exact hc1 hc'
    · exfalso
      have heq : Subgroup.zpowers c = A ⊓ L :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩)
          (by rw [hj, Nat.card_zpowers, hc3, pow_one])
      apply ha₀c
      rw [heq]
      exact ⟨hb₁A, hb₁L⟩
    · rw [hj]
      norm_num
    · exfalso
      have heq : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, h27])
      apply ha₃L
      have h' : a₃ ∈ A ⊓ L := by
        rw [heq]
        exact ha₃
      exact h'.2
  exact ⟨hcL, hcard9, w, ⟨hwL', hwN⟩, hw3, hP2, a₀, ha₀, ha₀c⟩

end CFSG.RankThree.PartTwo.Sec21.Item21LateProof

