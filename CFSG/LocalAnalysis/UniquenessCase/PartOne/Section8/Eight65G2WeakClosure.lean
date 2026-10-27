module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Assembly
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2WeakClosureCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2WeakClosureData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley

theorem sylowCenterWeaklyClosed_of_center_generator
    {Y : Type} [Group Y] [Finite Y] (Q₀ : Subgroup Y)
    (hQ₀ : ∃ P : Sylow 3 Y, (P : Subgroup Y) = Q₀) (z : ↥Q₀)
    (hcenter : Subgroup.center ↥Q₀ = Subgroup.zpowers z) (hz3 : orderOf (z : Y) = 3)
    (hweak : ∀ y : Y, y * (z : Y) * y⁻¹ ∈ Q₀ → y * (z : Y) * y⁻¹ ∈ Subgroup.zpowers (z : Y)) :
    SylowCenterWeaklyClosed Y := by
  classical
  obtain ⟨P, rfl⟩ := hQ₀
  refine sylowCenterWeaklyClosed_of_exists_sylow P ?_
  intro Z hZQ hZc hZcard g hconj
  have hZle : Z ≤ Subgroup.zpowers (z : Y) := by
    intro a ha
    have hcent : (⟨a, hZQ ha⟩ : ↥(P : Subgroup Y)) ∈ Subgroup.center ↥(P : Subgroup Y) := by
      rw [Subgroup.mem_center_iff]
      intro q
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZc ha) (q : Y) q.2)
    rw [hcenter] at hcent
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcent
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hcardz : Nat.card (Subgroup.zpowers (z : Y)) = 3 := by rw [Nat.card_zpowers, hz3]
  have hZeq : Z = Subgroup.zpowers (z : Y) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hcardz, hZcard])
  have hc : g⁻¹ * (z : Y) * g⁻¹⁻¹ ∈ Subgroup.zpowers (z : Y) := by
    apply hweak g⁻¹
    apply hconj
    exact Subgroup.mem_map_of_mem _ (hZeq ▸ Subgroup.mem_zpowers (z : Y))
  have hle : CFSG.conjugate Z g ≤ Z := by
    rintro x ⟨a, ha, rfl⟩
    rw [hZeq] at ha ⊢
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h : (MulAut.conj g⁻¹).toMonoidHom ((z : Y) ^ n) = (g⁻¹ * (z : Y) * g⁻¹⁻¹) ^ n := by
      simp [map_zpow]
    rw [h]
    exact Subgroup.zpow_mem _ hc n
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

private theorem weakClosed_of_map_eq_conj {G H : Type} [Group G] [Group H] (φ : G →* H)
    (hinj : Function.Injective φ) (Q₀ : Subgroup G) (z₀ : G) (g z : H) (T : Subgroup H)
    (hmap : Q₀.map φ = T.map (MulAut.conj g).toMonoidHom) (hφz : φ z₀ = g * z * g⁻¹)
    (hT : ∀ c : H, c * z * c⁻¹ ∈ T → c * z * c⁻¹ ∈ Subgroup.zpowers z) :
    ∀ y : G, y * z₀ * y⁻¹ ∈ Q₀ → y * z₀ * y⁻¹ ∈ Subgroup.zpowers z₀ := by
  intro y hy
  have h1 : φ (y * z₀ * y⁻¹) ∈ Q₀.map φ := Subgroup.mem_map_of_mem φ hy
  rw [hmap] at h1
  obtain ⟨e, he, hee⟩ := Subgroup.mem_map.1 h1
  have hφx : φ (y * z₀ * y⁻¹) = φ y * (g * z * g⁻¹) * (φ y)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hφz]
  have he' : g * e * g⁻¹ = φ y * (g * z * g⁻¹) * (φ y)⁻¹ := by
    rw [← hφx, ← hee]
    simp [MulAut.conj_apply]
  have hc : (g⁻¹ * φ y * g) * z * (g⁻¹ * φ y * g)⁻¹ = e := by
    have h : e = g⁻¹ * (g * e * g⁻¹) * g := by group
    rw [h, he']
    group
  have h4 := hT (g⁻¹ * φ y * g) (by rw [hc]; exact he)
  rw [hc] at h4
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h4
  refine Subgroup.mem_zpowers_iff.2 ⟨n, hinj ?_⟩
  rw [map_zpow, hφz, hφx, ← he', ← hn, conj_zpow]

theorem g2_exists_sylow_center_generator_weakClosed
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    ∃ (Q0 : Subgroup (adjointGroup .G2 K)) (z0 : ↥Q0),
      (∃ P : Sylow 3 (adjointGroup .G2 K), (P : Subgroup (adjointGroup .G2 K)) = Q0) ∧
      Subgroup.center ↥Q0 = Subgroup.zpowers z0 ∧
      orderOf (z0 : adjointGroup .G2 K) = 3 ∧
      ∀ y : adjointGroup .G2 K, y * (z0 : adjointGroup .G2 K) * y⁻¹ ∈ Q0 →
        y * (z0 : adjointGroup .G2 K) * y⁻¹ ∈ Subgroup.zpowers (z0 : adjointGroup .G2 K) := by
  obtain ⟨Q0, z0, hsyl, hcen, hord, L, hL, φ, g, ω, m, hω1, hinj, h3L, hω3, hmap, hφz⟩ :=
    g2_exists_sylow_weakClosure_data (K := K) h3 hq3
  exact ⟨Q0, z0, hsyl, hcen, hord, weakClosed_of_map_eq_conj φ hinj Q0 z0 g _ _ hmap hφz
    fun c hc => g2_conj_tz_mem_zpowers_of_mem_extSub h3L hω3 hω1
      (ext3_tzPart (L := L) (m := m) hω1) c hc⟩

theorem sylowCenterWeaklyClosed_of_adjointGroup_g2
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    SylowCenterWeaklyClosed (adjointGroup .G2 K) := by
  obtain ⟨Q0, z0, hsyl, hcen, hord, hweak⟩ :=
    g2_exists_sylow_center_generator_weakClosed h3 hq3
  have : Finite (adjointGroup .G2 K) := CFSG.LieType.Chevalley.generated_group_finite .G2 K
  exact sylowCenterWeaklyClosed_of_center_generator Q0 hsyl z0 hcen hord hweak

theorem sylowCenterWeaklyClosed_of_lieModel_g2
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr3 : r ≠ 3)
    (hY : CFSG.Blueprint.LieModel Y .G2 0 r f) : SylowCenterWeaklyClosed Y := by
  classical
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 r f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨⟨hrp, -, -, hrf3⟩, hm⟩ := hc
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eY⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  have : Finite (adjointGroup .G2 K) := CFSG.LieType.Chevalley.generated_group_finite .G2 K
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq3 : 3 ≤ Nat.card K := by
    rw [hKcard]
    exact hrf3
  exact sylowCenterWeaklyClosed_of_mulEquiv eY (sylowCenterWeaklyClosed_of_adjointGroup_g2 h3 hq3)

theorem g2SylowCenterWeakClosure_holds :
    G2SylowCenterWeakClosure :=
  fun _ _ _ _ _ hr3 hY => sylowCenterWeaklyClosed_of_lieModel_g2 hr3 hY

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
