module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDn
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoRTwoLocal
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem false_of_parabolic (hKF2 : L3EvenParabolic)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N : Subgroup G}
    (hN : CFSG.Open.IsTwoLocal N) (hNM : ¬ N ≤ c.S.M) (hKN : t.Ky ≤ N)
    (hO : t.On N ≤ c.S.M) (hDM : ¬ t.Dn N ≤ c.S.M) {J : Subgroup G} (hJD : J ≤ t.Dn N)
    (hJM : J ≤ c.S.M) (hKJ : t.Ky ≤ J)
    (hpar : CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup (t.Dhat N))
      ((J.subgroupOf (t.Dn N)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N)))))
    (hL3 : (∃ f : ℕ, 2 ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel (t.Dhat N) .PSL 3 2 f) ∨
      (∃ f : ℕ, 2 ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel (t.Dhat N) .PSU 3 2 f)) : False := by
  classical
  let π : ↥(t.Dn N) →* t.Dhat N :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N))
  let Jhat : Subgroup (t.Dhat N) := (J.subgroupOf (t.Dn N)).map π
  let Khat : Subgroup (t.Dhat N) := (t.Ky.subgroupOf (t.Dn N)).map π
  have hπker : π.ker = CFSG.pPrimeCore 3 ↥(t.Dn N) := by
    dsimp only [π]
    exact QuotientGroup.ker_mk' _
  have h3On : ¬ 3 ∣ Nat.card (t.On N) := t.not_three_dvd_card_On N
  have hZKy : t.Z ≤ t.Ky := t.Z_le_Ky
  have hKyD : t.Ky ≤ t.Dn N := hKJ.trans hJD
  have hJhat_ne_top : Jhat ≠ ⊤ := by
    intro htop
    exact hDM (t.Dn_le_of_map_eq_top hJM hO (by simpa [Jhat, π] using htop))
  have hKhat_le_J : Khat ≤ Jhat := by
    dsimp only [Khat, Jhat]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hKJ)
  have hKhat_perf : ⁅Khat, Khat⁆ = Khat := by
    dsimp only [Khat]
    rw [← Subgroup.map_commutator,
      CFSG.GroupTheory.commutator_subgroupOf_eq hKyD hKyD, t.commutator_Ky]
  have hKhat_ne_bot : Khat ≠ ⊥ := by
    intro hbot
    have hZhat_le : (t.Z.subgroupOf (t.Dn N)).map π ≤ Khat := by
      dsimp only [Khat]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hZKy)
    have hZhat_bot : (t.Z.subgroupOf (t.Dn N)).map π = ⊥ :=
      eq_bot_iff.mpr (hbot ▸ hZhat_le)
    have hZleOn : t.Z ≤ t.On N := by
      intro z hz
      have hzD : z ∈ t.Dn N := t.Z_le_Dn (hZKy.trans hKN) hz
      have hzsub : (⟨z, hzD⟩ : ↥(t.Dn N)) ∈ t.Z.subgroupOf (t.Dn N) := hz
      have hmap : π ⟨z, hzD⟩ ∈ (t.Z.subgroupOf (t.Dn N)).map π :=
        Subgroup.mem_map.mpr ⟨⟨z, hzD⟩, hzsub, rfl⟩
      rw [hZhat_bot] at hmap
      have hker : (⟨z, hzD⟩ : ↥(t.Dn N)) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa using hmap
      have hmemP : (⟨z, hzD⟩ : ↥(t.Dn N)) ∈
          CFSG.pPrimeCore 3 ↥(t.Dn N) := by
        rwa [hπker] at hker
      exact ⟨⟨z, hzD⟩, hmemP, rfl⟩
    have h3Z : 3 ∣ Nat.card t.Z := by
      rw [t.card_Z]
    exact t.not_three_dvd_card_On N (h3Z.trans (Subgroup.card_dvd_of_le hZleOn))
  obtain ⟨ghat, hghatJ, r, hr, hr5, hordg, hrdvdK, hcomm⟩ :=
    hKF2 (t.Dhat N) hL3 Jhat Khat hJhat_ne_top hpar hKhat_le_J hKhat_perf
      hKhat_ne_bot
  obtain ⟨x, hxK, hπx⟩ := Subgroup.mem_map.mp hghatJ
  have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.mp hxK
  have hdvd : r ∣ orderOf x := by
    have h := orderOf_map_dvd π x
    rwa [hπx, hordg] at h
  have hdvdG : r ∣ orderOf ((x : ↥(t.Dn N)) : G) := by
    simpa only [Subgroup.orderOf_coe] using hdvd
  let m : ℕ := orderOf ((x : ↥(t.Dn N)) : G) / r
  let f : G := ((x : ↥(t.Dn N)) : G) ^ m
  have hf : orderOf f = r := by
    dsimp only [f, m]
    exact orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos _)) hdvdG
  have hxM : (x : G) ∈ c.S.M := hJM hxJ
  have hfM : f ∈ c.S.M := by
    dsimp only [f]
    exact c.S.M.pow_mem hxM m
  have hfN : f ∈ N := by
    dsimp only [f]
    exact N.pow_mem (t.Dn_le N x.property) m
  let ψ : ↥J →* t.Dhat N := π.comp (Subgroup.inclusion hJD)
  let FJ : Subgroup ↥J := (CFSG.Open.pCoreOf 2 Jhat).comap ψ
  let F : Subgroup G := FJ.map J.subtype
  have hFJ_le : F ≤ J := Subgroup.map_subtype_le FJ
  have hJhat_norm : Jhat ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Jhat : Set (t.Dhat N)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Jhat
  have hψ_range : Jhat = Subgroup.map ψ ⊤ := by
    rw [Subgroup.map_top]
    ext y
    constructor
    · intro hy
      obtain ⟨y', hy'K, rfl⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨(y' : G), Subgroup.mem_subgroupOf.mp hy'K⟩, ?_⟩
      have hy'' : Subgroup.inclusion hJD
          (⟨(y' : G), Subgroup.mem_subgroupOf.mp hy'K⟩ : ↥J) = y' :=
        Subtype.ext rfl
      show π (Subgroup.inclusion hJD _) = π y'
      rw [hy'']
    · rintro ⟨j, -, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJD j,
        Subgroup.mem_subgroupOf.mpr (by simpa using j.property), rfl⟩
  have hψ_Jhat : ∀ j : ↥J, ψ j ∈ Jhat := by
    intro j
    rw [hψ_range]
    exact Subgroup.mem_map.mpr ⟨j, Subgroup.mem_top _, rfl⟩
  have hFJ_normal : FJ.Normal := by
    refine ⟨?_⟩
    intro y hy j
    rw [Subgroup.mem_comap] at hy ⊢
    have hj : ψ j ∈ Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 Jhat : Set (t.Dhat N)) := hJhat_norm (hψ_Jhat j)
    have hconj := (Subgroup.mem_normalizer_iff.mp hj (ψ y)).mp hy
    simpa only [map_mul, map_inv] using hconj
  have hFsub_eq : F.subgroupOf J = FJ := by
    dsimp only [F]
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective FJ
  have hFJ_norm : J ≤ Subgroup.normalizer (F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFJ_le).mp
      (hFsub_eq ▸ hFJ_normal)
  have hF_mem : ∀ {y : G} (hyJ : y ∈ J), y ∈ F ↔
      ψ ⟨y, hyJ⟩ ∈ CFSG.Open.pCoreOf 2 Jhat := by
    intro y hyJ
    dsimp only [F, FJ]
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have hy'' : (⟨y, hyJ⟩ : ↥J) = y' := Subtype.ext (by simpa using hyy'.symm)
      rwa [hy'']
    · intro hy
      exact ⟨⟨y, hyJ⟩, hy, rfl⟩
  have hFM : F ≤ c.S.M := hFJ_le.trans hJM
  have hKF : t.Ky ≤ Subgroup.normalizer (F : Set G) := hKJ.trans hFJ_norm
  have hF_le_D : F ≤ t.Dn N := hFJ_le.trans hJD
  let φ : ↥F →* t.Dhat N := π.comp (Subgroup.inclusion hF_le_D)
  have hφ_ker : φ.ker = (F ⊓ t.On N).subgroupOf F := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hy
      have hker : Subgroup.inclusion hF_le_D y ∈ π.ker := hy
      have hmem : Subgroup.inclusion hF_le_D y ∈
          CFSG.pPrimeCore 3 ↥(t.Dn N) := by
        rwa [hπker] at hker
      exact ⟨y.property, ⟨Subgroup.inclusion hF_le_D y, hmem, rfl⟩⟩
    · rintro ⟨-, y', hy', hyy'⟩
      have hyval : Subgroup.inclusion hF_le_D y = y' :=
        Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hyy'.symm)
      have hπy : π y' = 1 := by
        have : y' ∈ π.ker := by rwa [hπker]
        exact this
      show π (Subgroup.inclusion hF_le_D y) = 1
      rw [hyval]
      exact hπy
  have h3ker : ¬ 3 ∣ Nat.card ↥φ.ker := by
    rw [hφ_ker]
    have hcard : Nat.card ↥((F ⊓ t.On N).subgroupOf F) =
        Nat.card ↥(F ⊓ t.On N) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := F ⊓ t.On N) (K := F)
        inf_le_left).toEquiv
    rw [hcard]
    exact fun h3 => t.not_three_dvd_card_On N (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hφ_range : φ.range ≤ CFSG.Open.pCoreOf 2 Jhat := by
    rintro - ⟨y, rfl⟩
    have hyJ : (y : G) ∈ J := hFJ_le y.property
    have hψ : ψ ⟨(y : G), hyJ⟩ ∈ CFSG.Open.pCoreOf 2 Jhat :=
      (hF_mem hyJ).mp y.property
    have hincl : Subgroup.inclusion hF_le_D y =
        Subgroup.inclusion hJD ⟨(y : G), hyJ⟩ := Subtype.ext rfl
    show π (Subgroup.inclusion hF_le_D y) ∈ CFSG.Open.pCoreOf 2 Jhat
    rw [hincl]
    exact hψ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPJ : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Jhat) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := Jhat)).map Jhat.subtype
  have hP_range : IsPGroup 2 ↥φ.range := hPJ.to_le hφ_range
  have h3range : ¬ 3 ∣ Nat.card ↥φ.range := by
    intro h3
    obtain ⟨n, hn⟩ := hP_range.exists_card_eq
    rw [hn] at h3
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h32
  have h3F : ¬ 3 ∣ Nat.card F := by
    intro h3
    have hcard := card_ker_mul_card_range φ
    rw [← hcard] at h3
    rcases (Nat.prime_three.dvd_mul).mp h3 with h | h
    · exact h3ker h
    · exact h3range h
  have hfF : ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ F := by
    intro k hk
    have hkJ : k ∈ J := hKJ hk
    have hkD : k ∈ t.Dn N := hJD hkJ
    have hkKhat : π (⟨k, hkD⟩ : ↥(t.Dn N)) ∈ Khat := by
      dsimp only [Khat]
      exact Subgroup.mem_map.mpr
        ⟨⟨k, hkD⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hcin : ghat * π ⟨k, hkD⟩ * ghat⁻¹ * (π ⟨k, hkD⟩)⁻¹ ∈
        CFSG.Open.pCoreOf 2 Jhat := hcomm _ hkKhat
    have hxk : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ F := by
      have hJcomm : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem (J.mul_mem hxJ hkJ) (J.inv_mem hxJ))
          (J.inv_mem hkJ)
      rw [hF_mem hJcomm]
      show π (⟨(x : G) * k * (x : G)⁻¹ * k⁻¹, hJD hJcomm⟩ :
        ↥(t.Dn N)) ∈ CFSG.Open.pCoreOf 2 Jhat
      have heq : (⟨(x : G) * k * (x : G)⁻¹ * k⁻¹, hJD hJcomm⟩ :
          ↥(t.Dn N)) = ⁅x, (⟨k, hkD⟩ : ↥(t.Dn N))⁆ := by
        apply Subtype.ext
        rw [commutatorElement_def]
        simp
      rw [heq, map_commutatorElement, hπx]
      simpa only [commutatorElement_def] using hcin
    have hxpow : ∀ n : ℕ,
        (x : G) ^ n * k * ((x : G) ^ n)⁻¹ * k⁻¹ ∈ F := by
      intro n
      induction n with
      | zero => simpa using F.one_mem
      | succ n ih =>
        have hstep : (x : G) ^ (n + 1) * k * ((x : G) ^ (n + 1))⁻¹ * k⁻¹ =
            (x : G) * ((x : G) ^ n * k * ((x : G) ^ n)⁻¹ * k⁻¹) *
              (x : G)⁻¹ * ((x : G) * k * (x : G)⁻¹ * k⁻¹) := by
          group
        rw [hstep]
        exact F.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hFJ_norm hxJ) _).mp ih) hxk
    exact hxpow m
  have hcommL : ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ c.L ⊓ t.d.N :=
    t.commutator_mem_inf_N_of_mem hK32 hGA hSp hFM hKF h3F hfM hfF
  have hrdvdKy : r ∣ Nat.card t.Ky := by
    refine hrdvdK.trans ?_
    have hcard := Subgroup.card_map_dvd (t.Ky.subgroupOf (t.Dn N)) π
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKyD).toEquiv] at hcard
  exact hNM (t.le_M_of_commutator_mem hK32 hGA hSp hr hr5 hrdvdKy hfM hf hcommL
    hN hKN hfN)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
