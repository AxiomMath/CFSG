module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFixT
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFixS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open CFSG.SignalizerFunctorTheorem.Quadratic (LGL)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem w16c_odd_card_fusionOddCore (H : Type) [Group H] [Finite H] :
    Odd (Nat.card (fusionOddCore H)) := by
  have h : fusionOddCore H = CFSG.pPrimeCore 2 H := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))

private theorem w16c_pow_mem_center_of_isExtraspecial {Y : Type} [Group Y] {N : Subgroup Y}
    {q : ℕ} (hN : CFSG.IsExtraspecial q ↥N) {x : Y} (hx : x ∈ N) :
    x ^ q ∈ (Subgroup.center ↥N).map N.subtype := by
  haveI := hN
  haveI : CFSG.IsElementaryAbelian q (↥N ⧸ Subgroup.center ↥N) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian q ↥N
  have h1 : ((⟨x, hx⟩ : ↥N) : ↥N ⧸ Subgroup.center ↥N) ^ q = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p q (↥N ⧸ Subgroup.center ↥N))
      ((⟨x, hx⟩ : ↥N) : ↥N ⧸ Subgroup.center ↥N)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : ↥N) ^ q, h1, by simp⟩

private theorem w16c_mem_map_comap_subtype_iff {K : Subgroup G} {Y : Type} [Group Y]
    {N : Subgroup Y} (φ : ↥K →* Y) {k : ↥K} :
    (k : G) ∈ Subgroup.map K.subtype (Subgroup.comap φ N) ↔ φ k ∈ N := by
  constructor
  · intro hk
    obtain ⟨a, ha, haval⟩ := Subgroup.mem_map.mp hk
    have hak : a = k := K.subtype_injective haval
    have hmem := Subgroup.mem_comap.mp ha
    rwa [hak] at hmem
  · intro hk
    exact Subgroup.mem_map.mpr ⟨k, Subgroup.mem_comap.mpr hk, rfl⟩

namespace ExCfg

variable {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X} {p : ℕ}

theorem false_of_kernel (c : ExCfg M V₀ V U S H φ p)
    (hZ : ∀ q : ↥(conjClosure V H),
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G))
    (hK : ∀ q : ↥(conjClosure V H), φ q ∈ fusionOddCore X →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) →
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype) :
    False := by
  classical
  haveI : Finite ↥(conjClosure V H) := Subtype.finite
  haveI : Finite X := Finite.of_surjective φ c.bar.surjective
  let K : Subgroup G := conjClosure V H
  let N : Subgroup X := fusionOddCore X
  let Z : Subgroup X := (Subgroup.center ↥N).map N.subtype
  let I' : Subgroup G := conjClosure V₀ K
  let Kn : Subgroup G := Subgroup.map K.subtype (Subgroup.comap φ N)
  have hI'elem : IsElemAbelian 2 I' := by
    have h := isElemAbelian_conjClosure_V₀_conjClosure c.one c.five c.std c.cex c.min.1 c.not_le
    simpa [K, I'] using h
  have hI'norm : K ≤ Subgroup.normalizer (I' : Set G) := by
    simpa [K, I'] using conjClosure_le_normalizer_conjClosure_V₀
  obtain ⟨D⟩ := exists_modDataE hI'elem hI'norm
  let Sstar : Subgroup (LGL 2 D.W) := D.img Kn
  have hp2 : p ≠ 2 := by
    intro hp_eq
    have hodd := w16c_odd_card_fusionOddCore X
    rw [c.card, hp_eq] at hodd
    norm_num at hodd
  have hbar_card : Nat.card (SevenK.barSub K φ V) = 2 := by
    simpa [K] using c.shape.1
  have hbar_ne_bot : SevenK.barSub K φ V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hbar_card
    omega
  obtain ⟨y, hy_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbar_ne_bot
  obtain ⟨t, htV, hφt⟩ := SevenK.mem_barSub.mp y.2
  have ht1 : φ t ≠ 1 := by
    intro h
    exact hy_ne (Subtype.ext (hφt.symm.trans h))
  have hmemKn : ∀ {k : ↥(conjClosure V H)}, (k : G) ∈ Kn → φ k ∈ N := by
    intro k hk
    exact (w16c_mem_map_comap_subtype_iff (K := K) (N := N) φ).mp hk
  have hu : D.ρ t * D.ρ t = 1 := by
    have ht2 : t * t = 1 := by
      apply Subtype.ext
      change (t : G) * (t : G) = 1
      have h := c.cex.hyp.h6.elemAbelian.2 (t : G) htV
      simpa [pow_two] using h
    have h1 : D.ρ (t * t) = 1 := by rw [ht2, map_one]
    rwa [map_mul] at h1
  have hS : ∀ s ∈ Sstar, s ^ p = 1 := by
    intro s hs
    obtain ⟨k, hkKn, hsk⟩ := D.mem_img.mp hs
    have hφk : φ k ∈ N := hmemKn hkKn
    rw [← hsk, ← map_pow]
    exact (D.ρ_eq_one_iff (k ^ p)).mpr (hZ (k ^ p) (by
      rw [map_pow]
      exact w16c_pow_mem_center_of_isExtraspecial c.extra hφk))
  have hY : IsElemAbelian 2 (SevenK.barSub K φ V) := by
    have hsub : IsElemAbelian 2 (V.subgroupOf K) := c.cex.hyp.h6.elemAbelian.subgroupOf K
    have hmap : IsElemAbelian 2 ((V.subgroupOf K).map φ) := hsub.map φ
    simpa [SevenK.barSub] using hmap
  have hgen : Subgroup.normalClosure ((SevenK.barSub K φ V : Subgroup X) : Set X) = ⊤ := by
    have h := IsMinFam16.normalClosure_barSub_eq_top c.one c.std c.cex c.min c.not_le c.bar
    simpa [K] using h
  have hinv : ∀ s ∈ Sstar, D.ρ t * s * (D.ρ t)⁻¹ = s⁻¹ := by
    intro s hs
    obtain ⟨k, hkKn, hsk⟩ := D.mem_img.mp hs
    have hφk : φ k ∈ N := hmemKn hkKn
    rw [← hsk]
    have hmemZ : φ (t * k * t⁻¹ * k) ∈ Z := by
      rw [map_mul, map_mul, map_mul, map_inv]
      exact Shape166.mul_mem_center_of_extraspecial hY hgen c.shape c.prime c.extra c.card
        (SevenK.mem_barSub.mpr ⟨t, htV, rfl⟩) ht1 hφk
    have h1 : D.ρ (t * k * t⁻¹ * k) = 1 :=
      (D.ρ_eq_one_iff (t * k * t⁻¹ * k)).mpr (hZ (t * k * t⁻¹ * k) hmemZ)
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hne : traceSpace (tautRep D.W) (D.ρ t) ≠ ⊥ :=
    traceSpace_ne_bot c D hK htV ht1
  have hTI : ∀ y ∈ Sstar, traceSpace (tautRep D.W) (D.ρ t) ⊓
      (traceSpace (tautRep D.W) (D.ρ t)).map (tautRep D.W y) ≠ ⊥ →
      y * D.ρ t = D.ρ t * y := by
    intro y hy hyt
    obtain ⟨k, _, hyk⟩ := D.mem_img.mp hy
    rw [← hyk] at hyt ⊢
    exact commute_of_traceSpace_inf_ne_bot c D htV k hyt
  have hle : Nat.card Sstar ≤ p :=
    inverted_card_le_of_representation (tautRep D.W) c.prime hp2 hS hu hinv hne hTI
  have hcard : Nat.card Sstar = p ^ 2 := by
    simpa [Sstar, Kn, K, N] using card_img_comap_eq c D hZ hK
  rw [hcard] at hle
  have hp_two : 2 ≤ p := c.prime.two_le
  have hlt : p < p * p := by
    calc p = p * 1 := (mul_one p).symm
      _ < p * p := Nat.mul_lt_mul_of_pos_left (by omega) c.prime.pos
  have hpp : p * p ≤ p := by simpa [pow_two] using hle
  omega

end ExCfg

end CFSG.LocalAnalysis.WeakClosure81

end
