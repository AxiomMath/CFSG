module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F13 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s13f_cMStar_le (M X : Subgroup G) : cMStar M X ≤ M :=
  Subgroup.map_subtype_le _

theorem uc22s13f_lift {M K : Subgroup G} (hKM : K ≤ M) (hKn : (K.subgroupOf M).Normal) {y : G}
    (hy : y ∈ M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1) {f : Bar2 M}
    (hfK : f ∈ barImage M K)
    (hfy : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩ : Bar2 M) * f =
      f * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩) :
    ∃ c ∈ K ⊓ centralizer ({y} : Set G), ∃ hc : c ∈ M,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hc⟩ : Bar2 M) = f := by
  obtain ⟨⟨k, hkM⟩, hkK, rfl⟩ := hfK
  have hkK' : k ∈ K := hkK
  set A := zpowers y with hA
  have hAM : A ≤ M := (zpowers_le).2 hy
  have hAp : IsPGroup r A := IsPGroup.of_card_dvd_pow (n := 1)
    (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one hyr)
  set B := K ⊓ cMStar M A with hB
  have hBM : B ≤ M := inf_le_left.trans hKM
  have hMK : M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKM).1 hKn
  have hconjB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have haM : a ∈ M := hAM ha
    obtain ⟨hbM, hbc⟩ := uc22s13b_of_mem_cMStar hb.2
    have hmem : a * b * a⁻¹ ∈ M := M.mul_mem (M.mul_mem haM hbM) (M.inv_mem haM)
    refine ⟨(mem_normalizer_iff.1 (hMK haM) b).1 hb.1, uc22s13b_mem_cMStar hmem ?_⟩
    have he : (⟨a * b * a⁻¹, hmem⟩ : ↥M) = ⟨a, haM⟩ * ⟨b, hbM⟩ * (⟨a, haM⟩ : ↥M)⁻¹ := rfl
    rw [he, map_mul, map_mul, map_inv,
      mem_centralizer_iff.1 hbc _ (uc22s13b_mk_mem_barImage haM ha), mul_inv_cancel_right]
    exact hbc
  have hAB : A ≤ normalizer (B : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro b
    refine ⟨hconjB a ha b, fun hb => ?_⟩
    have h1 := hconjB a⁻¹ (A.inv_mem ha) _ hb
    rwa [show a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b by group] at h1
  have hc : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    intro a ha b hb
    obtain ⟨hbM, hbc⟩ := uc22s13b_of_mem_cMStar hb.2
    exact uc22s13b_commutator_mem (hAM ha) hbM
      (mem_centralizer_iff.1 hbc _ (uc22s13b_mk_mem_barImage (hAM ha) ha))
  have hkB : k ∈ B := by
    refine ⟨hkK', uc22s13b_mem_cMStar hkM ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨a, haM⟩, haA, rfl⟩
    have haA' : a ∈ zpowers y := haA
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 haA'
    have he : (⟨y ^ i, haM⟩ : ↥M) = ⟨y, hy⟩ ^ i := Subtype.ext (by simp)
    rw [he, map_zpow]
    exact (Commute.zpow_left hfy i).eq
  obtain ⟨c, ⟨hcB, hcA⟩, hck⟩ := uc22s13b_exists_cent hr hr2 hAp hBM hAB hc hkB
  refine ⟨c, ⟨hcB.1, ?_⟩, hBM hcB, ?_⟩
  · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hcA y (mem_zpowers y)).symm
  · have hmem : c⁻¹ * k ∈ M := M.mul_mem (M.inv_mem (hBM hcB)) hkM
    have h1 := (uc22s13b_mem_pCoreOf_iff hmem).1 hck
    have he : (⟨c⁻¹ * k, hmem⟩ : ↥M) = (⟨c, hBM hcB⟩ : ↥M)⁻¹ * ⟨k, hkM⟩ := rfl
    rw [he, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

theorem uc22s13f_two {M : Subgroup G} {c : G} (hc : c ∈ M) {k : ℕ}
    (h : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hc⟩ : Bar2 M) ^ (2 ^ k) = 1) :
    ∃ j : ℕ, c ^ (2 ^ j) = 1 := by
  have hmem : c ^ (2 ^ k) ∈ M := M.pow_mem hc _
  have h1 : c ^ (2 ^ k) ∈ CFSG.Open.pCoreOf 2 M := by
    rw [uc22s13b_mem_pCoreOf_iff hmem]
    have he : (⟨c ^ (2 ^ k), hmem⟩ : ↥M) = ⟨c, hc⟩ ^ (2 ^ k) := Subtype.ext (by simp)
    rw [he, map_pow, h]
  obtain ⟨i, hi⟩ := uc22s13b_isPGroup_pCoreOf M ⟨_, h1⟩
  refine ⟨k + i, ?_⟩
  have h2 : (c ^ (2 ^ k)) ^ (2 ^ i) = 1 := by
    have h3 := congrArg Subtype.val hi
    simpa using h3
  rw [pow_add, pow_mul, h2]

theorem uc22s13f_exists_perfect {M K : Subgroup G} (hKM : K ≤ M) (hKn : (K.subgroupOf M).Normal)
    {y : G} (hy : y ∈ M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1)
    {F : Subgroup (Bar2 M)} (hFK : F ≤ barImage M K)
    (hFy : ∀ f ∈ F, (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩ : Bar2 M) * f =
      f * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩)
    (hF : ⁅F, F⁆ = F) {z : Bar2 M} (hz : z ∈ F) :
    ∃ w ∈ ⁅⁅K ⊓ centralizer ({y} : Set G), K ⊓ centralizer ({y} : Set G)⁆,
        ⁅K ⊓ centralizer ({y} : Set G), K ⊓ centralizer ({y} : Set G)⁆⁆,
      ∃ hw : w ∈ M, (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hw⟩ : Bar2 M) = z := by
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set H₀ := K ⊓ centralizer ({y} : Set G) with hH₀
  set H₂ := H₀.subgroupOf M with hH₂
  have hFH : F ≤ H₂.map π := by
    intro f hf
    obtain ⟨c, hc, hcM, hcf⟩ := uc22s13f_lift hKM hKn hy hr hr2 hyr (hFK hf) (hFy f hf)
    exact ⟨⟨c, hcM⟩, hc, hcf⟩
  have hz2 : z ∈ ⁅⁅F, F⁆, ⁅F, F⁆⁆ := by
    rw [hF, hF]
    exact hz
  have hz' : z ∈ (⁅⁅H₂, H₂⁆, ⁅H₂, H₂⁆⁆).map π := by
    simp only [map_commutator]
    exact commutator_mono (commutator_mono hFH hFH) (commutator_mono hFH hFH) hz2
  obtain ⟨h, hh, rfl⟩ := hz'
  refine ⟨h, ?_, h.2, rfl⟩
  have h1 : (h : G) ∈ (⁅⁅H₂, H₂⁆, ⁅H₂, H₂⁆⁆).map M.subtype := mem_map_of_mem _ hh
  simp only [map_commutator, hH₂, subgroupOf_map_subtype] at h1
  exact commutator_mono (commutator_mono inf_le_left inf_le_left)
    (commutator_mono inf_le_left inf_le_left) h1

theorem uc22s13f_conj_mem_centralizer {x₀ g c : G}
    (hc : c ∈ centralizer ({g * x₀ * g⁻¹} : Set G)) :
    g⁻¹ * c * g ∈ centralizer ({x₀} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hc ⊢
  calc g⁻¹ * c * g * x₀ = g⁻¹ * (c * (g * x₀ * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * x₀ * g⁻¹) * c) * g := by rw [hc]
    _ = x₀ * (g⁻¹ * c * g) := by group

theorem uc22s13f_mem_cMStar_of_derived {M K L : Subgroup G} {x₀ g : G} (hx₀M : x₀ ∈ M)
    (hCM : centralizer ({x₀} : Set G) ≤ M)
    (hP : ⁅⁅centralizer ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ : Bar2 M)} :
          Set (Bar2 M)),
        centralizer ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ : Bar2 M)} :
          Set (Bar2 M))⁆,
      ⁅centralizer ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ : Bar2 M)} :
          Set (Bar2 M)),
        centralizer ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ : Bar2 M)} :
          Set (Bar2 M))⁆⁆ ≤
      centralizer (barImage M L : Set (Bar2 M)))
    {w : G} (hw : w ∈ ⁅⁅K ⊓ centralizer ({g * x₀ * g⁻¹} : Set G),
        K ⊓ centralizer ({g * x₀ * g⁻¹} : Set G)⁆,
      ⁅K ⊓ centralizer ({g * x₀ * g⁻¹} : Set G), K ⊓ centralizer ({g * x₀ * g⁻¹} : Set G)⁆⁆) :
    g⁻¹ * w * g ∈ cMStar M L := by
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set C := centralizer ({π ⟨x₀, hx₀M⟩} : Set (Bar2 M)) with hC
  set H₀ := K ⊓ centralizer ({g * x₀ * g⁻¹} : Set G) with hH₀
  set A₀ := centralizer ({x₀} : Set G) with hA₀
  set A₂ := A₀.subgroupOf M with hA₂
  have hconj : ∀ u : G, (MulAut.conj g⁻¹).toMonoidHom u = g⁻¹ * u * g := fun u => by
    simp [MulAut.conj_apply]
  have hH₀A : H₀.map (MulAut.conj g⁻¹).toMonoidHom ≤ A₀ := by
    rintro _ ⟨c, ⟨-, hc⟩, rfl⟩
    rw [hconj]
    exact uc22s13f_conj_mem_centralizer hc
  have hw' : g⁻¹ * w * g ∈ ⁅⁅A₀, A₀⁆, ⁅A₀, A₀⁆⁆ := by
    have h1 := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hw
    simp only [map_commutator] at h1
    rw [hconj] at h1
    exact commutator_mono (commutator_mono hH₀A hH₀A) (commutator_mono hH₀A hH₀A) h1
  have h1 : g⁻¹ * w * g ∈ (⁅⁅A₂, A₂⁆, ⁅A₂, A₂⁆⁆).map M.subtype := by
    simp only [map_commutator, hA₂, subgroupOf_map_subtype, inf_of_le_left hCM]
    exact hw'
  obtain ⟨h, hh, hhw⟩ := h1
  have hA₂C : A₂.map π ≤ C := by
    rintro _ ⟨⟨a, haM⟩, ha, rfl⟩
    have ha' : a ∈ A₀ := ha
    have h2 : (⟨a, haM⟩ : ↥M) * ⟨x₀, hx₀M⟩ = ⟨x₀, hx₀M⟩ * ⟨a, haM⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 ha')
    rw [hC, mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h2]
  have hπh : π h ∈ ⁅⁅C, C⁆, ⁅C, C⁆⁆ := by
    have h2 := mem_map_of_mem π hh
    simp only [map_commutator] at h2
    exact commutator_mono (commutator_mono hA₂C hA₂C) (commutator_mono hA₂C hA₂C) h2
  exact ⟨h, hP hπh, hhw⟩

theorem uc22s13f_exists_two {M K L : Subgroup G} (hKM : K ≤ M) (hKn : (K.subgroupOf M).Normal)
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {x₀ g : G} (hx₀M : x₀ ∈ M)
    (hyM : g * x₀ * g⁻¹ ∈ M) (hCM : centralizer ({x₀} : Set G) ≤ M) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hyr : (g * x₀ * g⁻¹) ^ r = 1)
    (hT : ∀ t : Bar2 M, t * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x₀, hx₀M⟩ * t → ∀ k : ℕ, t ^ (2 ^ k) = 1 →
      t ∈ centralizer (barImage M L : Set (Bar2 M)))
    {z t : Bar2 M} (hzK : z ∈ barImage M K) (htK : t ∈ barImage M K)
    (hzy : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * x₀ * g⁻¹, hyM⟩ : Bar2 M) * z =
      z * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * x₀ * g⁻¹, hyM⟩)
    (hty : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * x₀ * g⁻¹, hyM⟩ : Bar2 M) * t =
      t * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g * x₀ * g⁻¹, hyM⟩)
    {k : ℕ} (htk : t ^ (2 ^ k) = 1) :
    ∃ w ∈ K, ∃ hw : w ∈ M,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hw⟩ : Bar2 M) = ⁅z, t⁆ ∧
        g⁻¹ * w * g ∈ cMStar M L := by
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  obtain ⟨h, ⟨hhK, hhC⟩, hhM, hhz⟩ := uc22s13f_lift hKM hKn hyM hr hr2 hyr hzK hzy
  obtain ⟨t₁, ⟨ht₁K, ht₁C⟩, ht₁M, ht₁t⟩ := uc22s13f_lift hKM hKn hyM hr hr2 hyr htK hty
  obtain ⟨j, hj⟩ := uc22s13f_two ht₁M (k := k) (by rw [ht₁t]; exact htk)
  have hh'C := uc22s13f_conj_mem_centralizer hhC
  have ht'C := uc22s13f_conj_mem_centralizer ht₁C
  have hh'M : g⁻¹ * h * g ∈ M := hCM hh'C
  have ht'M : g⁻¹ * t₁ * g ∈ M := hCM ht'C
  have ht'j : (g⁻¹ * t₁ * g) ^ (2 ^ j) = 1 := by
    have h1 : (MulAut.conj g⁻¹) t₁ = g⁻¹ * t₁ * g := by simp [MulAut.conj_apply]
    rw [← h1, ← map_pow, hj, map_one]
  have ht'L : g⁻¹ * t₁ * g ∈ cMStar M L := by
    refine uc22s13b_mem_cMStar ht'M (hT _ ?_ j ?_)
    · have h2 : (⟨g⁻¹ * t₁ * g, ht'M⟩ : ↥M) * ⟨x₀, hx₀M⟩ = ⟨x₀, hx₀M⟩ * ⟨g⁻¹ * t₁ * g, ht'M⟩ :=
        Subtype.ext (mem_centralizer_singleton_iff.1 ht'C)
      rw [← map_mul, ← map_mul, h2]
    · have h2 : (⟨g⁻¹ * t₁ * g, ht'M⟩ : ↥M) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using ht'j)
      rw [← map_pow, h2, map_one]
  have hwK : ⁅h, t₁⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hhK ht₁K) (K.inv_mem hhK)) (K.inv_mem ht₁K)
  have hwM : ⁅h, t₁⁆ ∈ M := hKM hwK
  refine ⟨⁅h, t₁⁆, hwK, hwM, ?_, ?_⟩
  · have he : (⟨⁅h, t₁⁆, hwM⟩ : ↥M) = ⁅(⟨h, hhM⟩ : ↥M), ⟨t₁, ht₁M⟩⁆ := rfl
    rw [he, map_commutatorElement, hhz, ht₁t]
  · have he : g⁻¹ * ⁅h, t₁⁆ * g =
        (g⁻¹ * h * g) * (g⁻¹ * t₁ * g) * (g⁻¹ * h * g)⁻¹ * (g⁻¹ * t₁ * g)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact (cMStar M L).mul_mem (uc22s13b_conj_mem_cMStar hLM hLn hh'M ht'L)
      ((cMStar M L).inv_mem ht'L)

end CFSG.LocalAnalysis.UniquenessCase.UC22
