module

public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Local
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Two
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Class
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.Quasithin.Background.A318PC7

public section

namespace CFSG.StandardType.NbrU63

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType CFSG.StandardType.Line63.H5

variable {F : Type} [Field F] {n : ℕ}

theorem mem_zpowers_of_mem_center_of_cover (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1)
    {K P : Type*} [Group K] [Group P] (ψ : K →* P) (h2 : IsPGroup 2 ψ.ker)
    (φ : ↥(unitarySU 2 n F 6) →* P) (hφ : Function.Injective φ) (hφr : ∀ s, φ s ∈ ψ.range)
    (hφs : ∀ k, ∃ s, φ s = ψ k) {z : K} (hzc : z ∈ Subgroup.center K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) {c : K} (hcc : c ∈ Subgroup.center K) (hc3 : c ^ 3 = 1) :
    c ∈ Subgroup.zpowers z := by
  haveI : Finite F := hKd.finite
  have hcube1 : ∀ g ∈ ψ.ker, g ^ 3 = 1 → g = 1 := by
    intro g hg hg3
    obtain ⟨k, hk⟩ := h2 ⟨g, hg⟩
    have hk' : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have := pow_gcd_eq_one.mpr ⟨hk', hg3⟩
    rwa [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, pow_one] at this
  have hscal : ∀ c ∈ Subgroup.center K, ∃ s, φ s = ψ c ∧ ∃ w : Fˣ, w ^ 3 = 1 ∧
      (s : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) w := by
    intro c hc
    obtain ⟨s, hs⟩ := hφs c
    refine ⟨s, hs, ?_⟩
    have hcent : ∀ t : ↥(unitarySU 2 n F 6), s * t = t * s := by
      intro t
      apply hφ
      obtain ⟨k, hk⟩ := hφr t
      rw [map_mul, map_mul, hs, ← hk, ← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_center_iff.mp hc k).symm
    have hsc := TableBUE.mem_scalars_of_commute hKd Nat.prime_three hpq fun g hg =>
      congrArg Subtype.val (hcent ⟨g, hg⟩)
    rw [largeEvenScalars_def] at hsc
    obtain ⟨w, hw⟩ := hsc
    exact ⟨w, pow_three_eq_one_of_scalar_mem_unitarySU hKd hpq (hw ▸ s.2), hw.symm⟩
  obtain ⟨sz, hsz, wz, hwz3, hwz⟩ := hscal z hzc
  obtain ⟨sc, hsc, wc, hwc3, hwc⟩ := hscal c hcc
  have hwz1 : wz ≠ 1 := by
    rintro rfl
    apply hz1
    have hsz1 : sz = 1 := Subtype.ext (by rw [hwz, map_one]; rfl)
    have hz : z ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hsz, hsz1, map_one]
    exact hcube1 z hz hz3
  haveI : IsCyclic (⊤ : Subgroup Fˣ) := (Subgroup.topEquiv (G := Fˣ)).isCyclic.mpr inferInstance
  have hmem : wc ∈ Subgroup.zpowers wz :=
    mem_zpowers_of_isCyclic_of_pow_three (S := (⊤ : Subgroup Fˣ)) inferInstance trivial trivial
      hwz3 hwz1 hwc3
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hscj : sc = sz ^ j := by
    apply Subtype.ext
    rw [hwc, ← hj, Subgroup.coe_zpow, hwz, ← map_zpow]
  have hker : c * (z ^ j)⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hsc, hscj, map_zpow, hsz, map_zpow, mul_inv_cancel]
  have hcube : (c * (z ^ j)⁻¹) ^ 3 = 1 := by
    have hcomm : Commute c (z ^ j)⁻¹ := (Subgroup.mem_center_iff.mp hcc _).symm
    rw [hcomm.mul_pow, hc3, one_mul, inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hz3, _root_.one_zpow, inv_one]
  have h1 := hcube1 _ hker hcube
  rw [mul_inv_eq_one] at h1
  rw [h1]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j

theorem isCyclic_of_le_centralizer_of_cover (hKd : UnitaryFieldData 2 n F)
    (hpq : 3 ∣ 2 ^ n + 1) {G : Type} [Group G] [Finite G] (hrank : LargeEvenTwoLocalRank 3 G ≤ 4)
    {K : Subgroup G} {P : Type*} [Group P] (ψ : ↥K →* P) (h2 : IsPGroup 2 ψ.ker)
    (φ : ↥(unitarySU 2 n F 6) →* P) (hφ : Function.Injective φ) (hφr : ∀ s, φ s ∈ ψ.range)
    (hφs : ∀ k, ∃ s, φ s = ψ k) {z : G} (hzK : z ∈ K) (hzc : ∀ k ∈ K, z * k = k * z)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S := by
  haveI : Finite F := hKd.finite
  have := Fact.mk Nat.prime_three
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ :=
    exists_twoLocal_four_of_injective hKd hpq ψ h2 φ hφ hφr
  have hin : ∀ c ∈ Subgroup.centralizer (K : Set G), c ^ 3 = 1 → c ∈ K := by
    intro c hc hc3
    by_contra hcK
    have hc1 : c ≠ 1 := fun h => hcK (h ▸ K.one_mem)
    have := succ_le_twoLocalRank_of_outside hc3 hc1 hcK
      (fun h hh => (Subgroup.mem_centralizer_iff.mp hc h hh).symm) hU hU2 hEU hE hcard
    omega
  have hzc' : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
  have hzK3 : (⟨z, hzK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hzK1 : (⟨z, hzK⟩ : ↥K) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  intro S hS hS3
  have hZ : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  refine CFSG.Quasithin.A318P.isCyclic_of_unique_three hS3 hZ fun r hr hro => ?_
  have hr3 : r ^ 3 = 1 := hro ▸ pow_orderOf_eq_one r
  have hrC := hS hr
  have hrK := hin r hrC hr3
  have hrc : (⟨r, hrK⟩ : ↥K) ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hrC g g.2)
  have hrK3 : (⟨r, hrK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hr3)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_mem_center_of_cover hKd hpq ψ h2 φ hφ hφr hφs hzc' hzK3 hzK1 hrc hrK3)
  exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem card_eq_of_isCyclic_centralizer {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hγ : Nat.card (ggGamma K hN).range = 3 ^ 3) (h4 : 3 ^ 4 ≤ Nat.card Bs) :
    Nat.card Bs = 3 ^ 4 := by
  have hC3 : ∀ c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)), c ^ 3 = 1 := fun c =>
    Subtype.ext (by simpa using hBs.2 c c.2.1)
  have hCp : IsPGroup 3 ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := fun c =>
    ⟨1, by simpa using hC3 c⟩
  haveI := hcyc _ inf_le_right hCp
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 := by
    have hexp := Monoid.exponent_dvd_of_forall_pow_eq_one hC3
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  have h := card_range_ggGamma_mul_card_inf hN
  rw [hγ] at h
  have e3 : (3 : ℕ) ^ 3 = 27 := by norm_num
  have e4 : (3 : ℕ) ^ 4 = 81 := by norm_num
  rw [e3] at h
  rw [e4] at h4 ⊢
  omega

theorem false_of_central_three_of_two_le
    {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} (hF : Nat.card F = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hK : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (unitarySU 2 n F 6))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hγ : Nat.card (ggGamma K hN).range = 3 ^ 3) (h4 : 3 ^ 4 ≤ Nat.card Bs)
    (hrank : LargeEvenTwoLocalRank 3 G ≤ 4) {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hyK : ∀ k ∈ K, y * k = k * y) {z : G} (hzK : z ∈ K) (hzc : ∀ k ∈ K, z * k = k * z)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : False := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hKd : UnitaryFieldData 2 n F := TableBU.unitaryFieldData_of_card hF (by omega)
  have hcov : LineU.UnitaryCoverAt n 6 F :=
    LineU.unitaryUniversalCover_holds n 6 F hF (by norm_num) (by
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega)
  obtain ⟨φ, hφK, hφs, hφZ, -, hact⟩ := exists_cover_actsAs hKd hcov hK θ hN hBI
  have hrange : (φ.range : Subgroup G) = K := by
    ext l
    exact ⟨fun ⟨s, hs⟩ => hs ▸ hφK s, fun hl => hφs l hl⟩
  have hZ' : ∀ s, (∀ l ∈ φ.range, φ s * l = l * φ s) ↔
      LargeEvenProjMk (unitarySU 2 n F 6) s = 1 := by
    intro s
    rw [← hφZ s, hrange]
  have hφinj : Function.Injective φ :=
    injective_of_central_three hKd hpq φ hZ' (hrange ▸ hzK) (fun l hl => hzc l (hrange ▸ hl)) hz1
  have h2 : IsPGroup 2 K.subtype.ker := by
    rw [Subgroup.ker_subtype]
    exact IsPGroup.of_bot
  have hcyc := isCyclic_of_le_centralizer_of_cover hKd hpq hrank K.subtype h2 φ hφinj
    (fun s => ⟨⟨φ s, hφK s⟩, rfl⟩) (fun k => hφs k k.2) hzK hzc hz3 hz1
  have hBcard := card_eq_of_isCyclic_centralizer hN hBs hcyc hγ h4
  exact false_of_injective_cover_class hKd hpq φ hφinj hBs hBcard hrank hSC
    (fun S hS hSp => hcyc S (by rwa [hrange] at hS) hSp) hyBs hy1 (fun s => hyK _ (hφK s)) hact

theorem false_of_central_three_of_eq_one
    {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} (hF : Nat.card F = (2 ^ 1) ^ 2) (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (unitarySU 2 1 F 6))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hγ : Nat.card (ggGamma K hN).range = 3 ^ 3) (h4 : 3 ^ 4 ≤ Nat.card Bs)
    (hrank : LargeEvenTwoLocalRank 3 G ≤ 4) {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hyK : ∀ k ∈ K, y * k = k * y) {z : G} (hzK : z ∈ K) (hzc : ∀ k ∈ K, z * k = k * z)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : False := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have hKd : UnitaryFieldData 2 1 F := TableBU.unitaryFieldData_of_card hF le_rfl
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h9 : ¬ 9 ∣ 2 ^ 1 + 1 := by norm_num
  have hcov := LineU.unitaryCoverOddAt_six_two F hF4
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := exists_redCover hcov hK θ
  have hker : ∀ s, φ s = 1 → LargeEvenProjMk (unitarySU 2 1 F 6) s = 1 := by
    intro s hs
    have h1 := hφ3 s 1 (by rw [hs, map_one])
    rw [← h1, map_one]
  obtain ⟨s₀, hs₀⟩ := hφ2 ⟨z, hzK⟩
  have hzcent : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
  have hs₀p : LargeEvenProjMk (unitarySU 2 1 F 6) s₀ = 1 := by
    rw [← hφ3 s₀ ⟨z, hzK⟩ hs₀]
    rw [← ker_ggQuotHom θ] at hzcent
    exact hzcent
  have hs₀1 : φ s₀ ≠ 1 := by
    rw [hs₀]
    intro h
    exact hz1 (Line63.eq_one_of_cube (isPGroup_twoCenter K)
      ((redMkL_eq_one_iff K ⟨z, hzK⟩).mp h) hz3)
  have hinj : Function.Injective φ := injective_of_scalar_ne_one hKd hpq φ hker hs₀p hs₀1
  have h2 : IsPGroup 2 (redMkL K).ker := fun g =>
    ⟨Nat.card G, Subtype.ext (Subtype.ext
      (by simpa using ((redMkL_eq_one_iff K g.1).mp g.2).2.2))⟩
  have hcycK := isCyclic_of_le_centralizer_of_cover hKd hpq hrank (redMkL K) h2 φ hinj hφ1 hφ2
    hzK hzc hz3 hz1
  have hBcard : Nat.card (redMkB hN).range = 3 ^ 4 := by
    rw [card_redB hN hBs, card_eq_of_isCyclic_centralizer hN hBs hcycK hγ h4]
  set ny : ↥(Subgroup.normalizer (K : Set G)) := ⟨y, hN hyBs⟩
  have hyB : redMk K ny ∈ (redMkB hN).range := ⟨⟨y, hyBs⟩, rfl⟩
  have hy1' : redMk K ny ≠ 1 := fun h =>
    hy1 (Line63.eq_one_of_cube (isPGroup_twoCenter K) ((redMk_eq_one_iff K ny).mp h)
      (hBs.2 y hyBs))
  have hyC : ∀ s, redMk K ny * φ s = φ s * redMk K ny := by
    intro s
    obtain ⟨l, hl⟩ := hφ1 s
    rw [← hl]
    have h1 : ny * Subgroup.inclusion Subgroup.le_normalizer l =
        Subgroup.inclusion Subgroup.le_normalizer l * ny := Subtype.ext (hyK l l.2)
    show redMk K ny * redMk K (Subgroup.inclusion _ l) =
      redMk K (Subgroup.inclusion _ l) * redMk K ny
    rw [← map_mul, ← map_mul, h1]
  have hact : ∀ b ∈ (redMkB hN).range,
      ∃ M, M ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1) ∧ ActsAs φ b M := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨M, hM, hMA⟩ := redActsAs hcov hKd θ hφ1 hφ3 hN hBI b
    exact ⟨M, hM, hMA⟩
  exact false_of_injective_cover_class_of_not_nine hKd hpq h9 φ hinj (isElemAbelian_redB hN hBs)
    hBcard (redSC hN hBs hSC) (redCyc θ hK hcycK hφ2) hyB hy1' hyC hact

theorem nbrU63_stepOne
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hM : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K)
    (hlt : Nat.card (ggGamma K hN).range < 3 ^ 4) :
    ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z ^ 3 = 1 → z = 1 := by
  intro z hzK hzc hz3
  by_contra hz1
  obtain ⟨hK, n, F, _, _, hF, hn, hpq, θ, -, hBI⟩ :=
    config_marking_data (innerDiagOnLab_of_label hM)
  obtain ⟨hB4, hrank, hγ⟩ := card_rank_of_lt hcfg hnb hN hlt
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have h4 : 3 ^ 4 ≤ Nat.card Bs := hB4 ▸ Subgroup.card_le_of_le hBBs
  have hyBs : y ∈ Bs := hBBs hnb.1.2.1
  have hyK : ∀ k ∈ K, y * k = k * y := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)).symm
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · exact false_of_central_three_of_eq_one hF hK θ hN hBI hBs hcfg.2.1.2.2.2 hγ h4 hrank hyBs
      hnb.1.2.2.1 hyK hzK hzc hz3 hz1
  · exact false_of_central_three_of_two_le hF hn2 hpq hK θ hN hBI hBs hcfg.2.1.2.2.2 hγ h4 hrank
      hyBs hnb.1.2.2.1 hyK hzK hzc hz3 hz1

end CFSG.StandardType.NbrU63

end
