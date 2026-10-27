module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IPerfect
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILongRootConj
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILemmaATI
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILongNotShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

private theorem rckK1Ila_map_conj_one {K : Type*} [Group K] (H : Subgroup K) :
    H.map (MulAut.conj (1 : K)).toMonoidHom = H := by
  ext y
  simp [MulAut.conj_apply]

private theorem rckK1Ila_map_conj_mul {K : Type*} [Group K] (H : Subgroup K) (a b : K) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem rckK1Ila_isPGroup_rootGroup_ggU
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f) :
    ∀ γ ∈ (ggU t n f).D.roots, IsPGroup 2 ((ggU t n f).D.rootGroup γ) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro γ hγ
    exact CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv (t := _) n 2 f
      Nat.prime_two (by simp [CFSG.ClassicalInvolution.ModelFacts.IsFundTag]) hadm γ hγ

theorem rckK1I_lemmaA
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X)
    {t : StatedLieTag} {n f : ℕ} (hnorm : RCKNormalizedModel t n f) (ψ : (ggU t n f).K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    {β : Fin (ggU t n f).D.rank → ℤ} (hβ : β ∈ (ggU t n f).D.roots) (hlong : GGLongRoot (ggU t n f).D β)
    {x₀ : (ggU t n f).K} (hx₀ : x₀ ∈ (ggU t n f).D.rootGroup β) (hx₀1 : ψ x₀ ≠ 1) (α : MulAut X)
    (hα : α (ψ x₀) = ψ x₀) :
    (((ggU t n f).D.rootGroup β).map ψ).map α.toMonoidHom = ((ggU t n f).D.rootGroup β).map ψ := by
  classical
  obtain ⟨ht, hadm⟩ := hnorm
  let D := (ggU t n f).D
  let K := (ggU t n f).K
  have hperfK : commutator K = ⊤ := rckK1I_ggU_perfect ht hadm
  haveI : Group.IsPerfect K := ⟨hperfK⟩
  have hperfX : Group.IsPerfect X := Group.IsPerfect.ofSurjective hψ
  have hcommX : commutator X = ⊤ := hperfX.commutator_eq_top
  have hnabX : ¬ IsMulCommutative X := by
    intro hcomm
    have hbot : commutator X = ⊥ := (commutator_eq_bot_iff X).mpr hcomm
    rw [hcommX] at hbot
    exact top_ne_bot hbot
  have hZX : Subgroup.center X = ⊥ := by
    rcases hX.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · rw [Subgroup.center_eq_top_iff] at h
      exact absurd h hnabX
  have hsimplequot : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hZX).trans (QuotientGroup.quotientBot (G := X)))
  have hQX : CFSG.Assembly.IsQuasisimple X := ⟨hcommX, hsimplequot⟩
  have hQtop : CFSG.Assembly.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hQX
  have hZoddTop : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup X))) := by
    have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup X)) =
        Nat.card (Subgroup.center X) :=
      Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv (G := X))).toEquiv
    rw [hcard, hZX, Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have hposα : GGRootPosJ (⊤ : Subgroup X)
      (((D.rootGroup β).map ψ).map α.toMonoidHom)
      (((D.rootGroup (-β)).map ψ).map α.toMonoidHom) := by
    refine Or.inl ⟨t, n, f, β, ht, hadm.2.1, hlong, ?_⟩
    refine ⟨α.toMonoidHom.comp ψ, ?_, ?_, 1, ?_, ?_⟩
    · apply MonoidHom.range_eq_top_of_surjective
      intro x
      obtain ⟨k, hk⟩ := hψ (α.symm x)
      exact ⟨k, by
        change α (ψ k) = x
        rw [hk, MulEquiv.apply_symm_apply]⟩
    · intro k hk
      apply hker
      apply α.injective
      simpa using hk
    · rw [ggRootSub, rckK1Ila_map_conj_one, Subgroup.map_map]
    · rw [ggRootSub, rckK1Ila_map_conj_one, Subgroup.map_map]
  obtain ⟨γ, u, hγ, hbranch, hαR, hαRm⟩ :=
    (hIRG X ⊤ (((D.rootGroup β).map ψ).map α.toMonoidHom)
      (((D.rootGroup (-β)).map ψ).map α.toMonoidHom)
      hQtop hZoddTop hposα).1 t n f ψ ⟨ht, hadm⟩
      (MonoidHom.range_eq_top_of_surjective ψ hψ) hker
  have hrootP : ∀ δ ∈ D.roots, IsPGroup 2 (D.rootGroup δ) :=
    rckK1Ila_isPGroup_rootGroup_ggU ht hadm
  have hx0R : ψ x₀ ∈ (D.rootGroup β).map ψ := Subgroup.mem_map_of_mem ψ hx₀
  have hx0αR : ψ x₀ ∈ ((D.rootGroup β).map ψ).map α.toMonoidHom :=
    ⟨ψ x₀, hx0R, hα⟩
  rw [hαR] at hx0αR
  rw [ggRootSub] at hx0αR
  obtain ⟨y, hy, hψy⟩ := Subgroup.mem_map.mp hx0αR
  have hPβ : IsPGroup 2 (D.rootGroup β) := hrootP β hβ
  have hPγ : IsPGroup 2 ((D.rootGroup γ).map (MulAut.conj u).toMonoidHom) :=
    (hrootP γ hγ).map _
  obtain ⟨a, ha⟩ := hPβ ⟨x₀, hx₀⟩
  obtain ⟨b, hb⟩ := hPγ ⟨y, hy⟩
  have ha' : x₀ ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : y ^ 2 ^ b = 1 := congrArg Subtype.val hb
  let z : K := x₀⁻¹ * y
  have hzker : ψ z = 1 := by
    change ψ (x₀⁻¹ * y) = 1
    rw [map_mul, map_inv, hψy, inv_mul_cancel]
  have hzcenter : z ∈ Subgroup.center K := hker hzker
  have hy_eq : y = x₀ * z := by
    change y = x₀ * (x₀⁻¹ * y)
    group
  have hcomm : Commute x₀ y := by
    rw [hy_eq]
    have hzc : Commute x₀ z := (Subgroup.mem_center_iff.mp hzcenter x₀)
    exact (Commute.refl x₀).mul_right hzc
  have hxapow : x₀ ^ 2 ^ (a + b) = 1 := by
    rw [pow_add, pow_mul, ha', one_pow]
  have hyapow : y ^ 2 ^ (a + b) = 1 := by
    rw [pow_add, mul_comm (2 ^ a) (2 ^ b), pow_mul, hb', one_pow]
  have hzpow : z ^ 2 ^ (a + b) = 1 := by
    change (x₀⁻¹ * y) ^ 2 ^ (a + b) = 1
    rw [hcomm.inv_left.mul_pow, inv_pow, hxapow, hyapow, inv_one, one_mul]
  have hZoddK : Odd (Nat.card (Subgroup.center K)) :=
    CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_ggU ht hadm
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ 2 ^ (a + b) := orderOf_dvd_of_pow_eq_one hzpow
    have h2 : orderOf z ∣ Nat.card (Subgroup.center K) :=
      Subgroup.orderOf_dvd_natCard _ hzcenter
    have hcop : Nat.Coprime (2 ^ (a + b)) (Nat.card (Subgroup.center K)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZoddK)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hx0y : x₀ = y := by
    have h : x₀⁻¹ * y = 1 := hz1
    have hyx : y = x₀ := by
      rw [← mul_inv_cancel_left x₀ y, h, mul_one]
    exact hyx.symm
  have hmemγ : x₀ ∈ (D.rootGroup γ).map (MulAut.conj u).toMonoidHom := by
    rwa [hx0y]
  by_cases hlongγ : GGLongRoot D γ
  ·
    obtain ⟨v, hv⟩ := rckK1I_longRootConj ht hadm hγ hlongγ hβ hlong
    have hγeq : D.rootGroup γ =
        (D.rootGroup β).map (MulAut.conj v⁻¹).toMonoidHom := by
      have h := congrArg (Subgroup.map (MulAut.conj v⁻¹).toMonoidHom) hv
      rw [← rckK1Ila_map_conj_mul, inv_mul_cancel, rckK1Ila_map_conj_one] at h
      exact h
    have hmemn : x₀ ∈ (D.rootGroup β).map (MulAut.conj (u * v⁻¹)).toMonoidHom := by
      rw [hγeq] at hmemγ
      rwa [← rckK1Ila_map_conj_mul] at hmemγ
    obtain ⟨yβ, hyβ, hyβeq⟩ := Subgroup.mem_map.mp hmemn
    have hyβeq' : (u * v⁻¹) * yβ * (u * v⁻¹)⁻¹ = x₀ := by
      simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hyβeq
    have hconj_x : (u * v⁻¹)⁻¹ * x₀ * ((u * v⁻¹)⁻¹)⁻¹ = yβ := by
      calc (u * v⁻¹)⁻¹ * x₀ * ((u * v⁻¹)⁻¹)⁻¹
          = (u * v⁻¹)⁻¹ * ((u * v⁻¹) * yβ * (u * v⁻¹)⁻¹) *
              ((u * v⁻¹)⁻¹)⁻¹ := by rw [hyβeq']
        _ = yβ := by group
    have hx₀1K : x₀ ≠ 1 := by
      intro h; exact hx₀1 (by rw [h, map_one])
    have hTI := rckK1I_lemmaHTI_ggU ht hadm hβ hlong
    have hN : u * v⁻¹ ∈ Subgroup.normalizer (D.rootGroup β : Set K) := by
      have hk : (u * v⁻¹)⁻¹ ∈ Subgroup.normalizer (D.rootGroup β : Set K) :=
        hTI x₀ hx₀ hx₀1K ((u * v⁻¹)⁻¹) (by rw [hconj_x]; exact hyβ)
      simpa using Subgroup.inv_mem _ hk
    have hγu : (D.rootGroup γ).map (MulAut.conj u).toMonoidHom = D.rootGroup β := by
      rw [hγeq, ← rckK1Ila_map_conj_mul]
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hN)
    calc ((D.rootGroup β).map ψ).map α.toMonoidHom
        = ggRootSub D ψ γ u := hαR
      _ = (D.rootGroup β).map ψ := by rw [ggRootSub, hγu]
  ·
    have hshortcase : (((t = .PSp ∧ n = 2) ∨ t = .F4) ∧
        2 • γ ∉ D.roots) := by
      rcases hbranch with h | h
      · exact (hlongγ h).elim
      · exact h
    obtain ⟨hshorttag, h2γ⟩ := hshortcase
    have hdisj : D.rootGroup β ⊓
        (D.rootGroup γ).map (MulAut.conj u).toMonoidHom = ⊥ :=
      rckK1I_longNotShort hshorttag hadm hβ hlong hγ hlongγ h2γ u
    have hmem : x₀ ∈ D.rootGroup β ⊓
        (D.rootGroup γ).map (MulAut.conj u).toMonoidHom := ⟨hx₀, hmemγ⟩
    rw [hdisj] at hmem
    have hx₀1K : x₀ ≠ 1 := by
      intro h; exact hx₀1 (by rw [h, map_one])
    exact absurd (Subgroup.mem_bot.mp hmem) hx₀1K

end CFSG.StandardType.RCKK1I
