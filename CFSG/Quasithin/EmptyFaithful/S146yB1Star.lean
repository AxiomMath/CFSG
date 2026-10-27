module

public import CFSG.Quasithin.EmptyFaithful.S146xB2C2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Star

variable {G : Type} [Group G]

@[expose] def starMk (Iz I : Subgroup G) : ↥I →* E2.StarQuot Iz I :=
  QuotientGroup.mk' ((kerIn Iz I).subgroupOf I)

theorem mem_star_iff {Iz I X : Subgroup G} {y : E2.StarQuot Iz I} :
    y ∈ E2.star Iz I X ↔ ∃ x : ↥I, (x : G) ∈ X ∧ starMk Iz I x = y := by
  unfold E2.star starMk
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem starMk_eq_one_iff {Iz I : Subgroup G} {x : ↥I} : starMk Iz I x = 1 ↔ (x : G) ∈ kerIn Iz I := by
  unfold starMk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem starMk_mem_normalizer {Iz I K : Subgroup G} {z : G} (hzI : z ∈ I)
    (hzK : z ∈ Subgroup.normalizer (K : Set G)) :
    starMk Iz I ⟨z, hzI⟩ ∈ Subgroup.normalizer ((E2.star Iz I K : Subgroup _) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨x, hxK, rfl⟩ := mem_star_iff.mp hy
    refine mem_star_iff.mpr ⟨⟨z, hzI⟩ * x * ⟨z, hzI⟩⁻¹, ?_, ?_⟩
    · show z * (x : G) * z⁻¹ ∈ K
      exact (Subgroup.mem_normalizer_iff.mp hzK _).mp hxK
    · simp [map_mul, map_inv]
  · intro hy
    obtain ⟨x, hxK, hx⟩ := mem_star_iff.mp hy
    refine mem_star_iff.mpr ⟨⟨z, hzI⟩⁻¹ * x * ⟨z, hzI⟩, ?_, ?_⟩
    · show z⁻¹ * (x : G) * z ∈ K
      have h1 : z * (z⁻¹ * (x : G) * z) * z⁻¹ ∈ K := by simpa [mul_assoc] using hxK
      exact (Subgroup.mem_normalizer_iff.mp hzK _).mpr h1
    · rw [map_mul, map_mul, map_inv, hx]
      group

theorem starMk_sq {Iz I : Subgroup G} {z : G} (hzI : z ∈ I) (hz2 : z ^ 2 = 1) :
    starMk Iz I ⟨z, hzI⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have : (⟨z, hzI⟩ : ↥I) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  rw [this, map_one]

theorem starMk_comm_of_mem {Iz I K : Subgroup G} {z : G} (hzI : z ∈ I)
    (hc : ∀ m ∈ Iz, m * z = z * m) {b : E2.StarQuot Iz I}
    (hb : b ∈ E2.star Iz I (Iz ⊓ K)) : starMk Iz I ⟨z, hzI⟩ * b = b * starMk Iz I ⟨z, hzI⟩ := by
  obtain ⟨x, hx, rfl⟩ := mem_star_iff.mp hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc _ hx.1).symm


theorem false_of_star_comm {Iz I K : Subgroup G} {z : G} (hzI : z ∈ I)
    (hIz : Iz = I ⊓ Subgroup.centralizer ({z} : Set G)) (hKz : ⁅K, Subgroup.zpowers z⁆ = K)
    (hKne : K ≠ ⊥) (hKI : K ≤ I)
    (hcomm : ∀ x ∈ E2.star Iz I K,
      starMk Iz I ⟨z, hzI⟩ * x = x * starMk Iz I ⟨z, hzI⟩) : False := by
  have hzp : Subgroup.zpowers z ≤ I := Subgroup.zpowers_le.mpr hzI
  have hker : ⁅K, Subgroup.zpowers z⁆ ≤ kerIn Iz I := by
    rw [Subgroup.commutator_le]
    intro k hk w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hkx : starMk Iz I ⟨k, hKI hk⟩ ∈ E2.star Iz I K := mem_star_iff.mpr ⟨⟨k, hKI hk⟩, hk, rfl⟩
    have h1 := hcomm _ hkx
    have h2 : starMk Iz I ⟨z ^ m, hzp (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)⟩ =
        (starMk Iz I ⟨z, hzI⟩) ^ m := by
      rw [← map_zpow]
      rfl
    have h3 : starMk Iz I ⟨z ^ m, hzp (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)⟩ *
        starMk Iz I ⟨k, hKI hk⟩ = starMk Iz I ⟨k, hKI hk⟩ *
          starMk Iz I ⟨z ^ m, hzp (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)⟩ := by
      rw [h2]
      exact ((Commute.zpow_left (show Commute (starMk Iz I ⟨z, hzI⟩) (starMk Iz I ⟨k, hKI hk⟩) from h1) m)).eq
    have h4 : starMk Iz I ⁅(⟨k, hKI hk⟩ : ↥I), ⟨z ^ m, hzp (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h3.symm
    exact starMk_eq_one_iff.mp h4
  have hKker : K ≤ kerIn Iz I := hKz ▸ hker
  have hKc : K ≤ Subgroup.centralizer ({z} : Set G) := by
    intro k hk
    have := (hIz ▸ kerIn_le_self Iz I (hKker hk) : k ∈ I ⊓ Subgroup.centralizer ({z} : Set G))
    exact this.2
  apply hKne
  rw [← hKz, eq_bot_iff, Subgroup.commutator_le]
  intro k hk w hw
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcz : Commute k z := (Subgroup.mem_centralizer_iff.mp (hKc hk) z rfl).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcz.zpow_right m).eq]
  exact Subgroup.one_mem _

theorem nonempty_star_mulEquiv_center {Iz I K : Subgroup G} (hKI : K ≤ I)
    (hq : CFSG.IsQuasisimple ↥K) (hs : IsSimpleGroup ↥(E2.star Iz I K)) :
    Nonempty (↥(E2.star Iz I K) ≃* ↥K ⧸ Subgroup.center ↥K) := by
  classical
  have := hs
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  have hperf : Group.IsPerfect ↥K := hq.1
  let f : ↥K →* E2.StarQuot Iz I := (starMk Iz I).comp (Subgroup.inclusion hKI)
  have hrange : f.range = E2.star Iz I K := by
    ext y
    rw [MonoidHom.mem_range, mem_star_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hKI x.2⟩, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let φ : ↥K →* ↥(E2.star Iz I K) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp f.rangeRestrict
  have hφs : Function.Surjective φ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp f.rangeRestrict_surjective
  have hφker : φ.ker = f.ker := by
    ext x
    have hval : ((φ x : ↥(E2.star Iz I K)) : E2.StarQuot Iz I) = f x := rfl
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hval]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have hnc : ¬ ∀ a b : ↥(E2.star Iz I K), a * b = b * a := by
    intro hab
    have hcomm : (commutator ↥K) ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hab _ _)
    rw [hperf.commutator_eq_top] at hcomm
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(E2.star Iz I K))
    obtain ⟨x, rfl⟩ := hφs y
    exact hy (MonoidHom.mem_ker.mp (hcomm (Subgroup.mem_top x)))
  have hcen : Subgroup.center ↥(E2.star Iz I K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(E2.star Iz I K)) with h | h
    · exact h
    · exfalso
      apply hnc
      intro a b
      have : a ∈ Subgroup.center ↥(E2.star Iz I K) := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  have hZ : Subgroup.center ↥K ≤ φ.ker := by
    intro c hc
    have hcc : φ c ∈ Subgroup.center ↥(E2.star Iz I K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨k, rfl⟩ := hφs w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc k]
    rw [hcen, Subgroup.mem_bot] at hcc
    exact hcc
  have hN : φ.ker ≤ Subgroup.center ↥K := by
    intro n hn
    set N' : Subgroup (↥K ⧸ Subgroup.center ↥K) := φ.ker.map (QuotientGroup.mk' (Subgroup.center ↥K)) with hN'
    have : N'.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h | h
    · have hmem : (QuotientGroup.mk' (Subgroup.center ↥K)) n ∈ N' := Subgroup.mem_map_of_mem _ hn
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    · exfalso
      have hall : ∀ k : ↥K, φ k = 1 := by
        intro k
        have hk : (QuotientGroup.mk' (Subgroup.center ↥K)) k ∈ N' := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨n', hn', hnk⟩ := Subgroup.mem_map.mp hk
        have hzk : n'⁻¹ * k ∈ Subgroup.center ↥K := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnk
          exact QuotientGroup.eq.mp hnk
        have h1 : φ (n'⁻¹ * k) = 1 := MonoidHom.mem_ker.mp (hZ hzk)
        have h2 : φ n' = 1 := MonoidHom.mem_ker.mp hn'
        rw [map_mul, map_inv, h2, inv_one, one_mul] at h1
        exact h1
      apply hnc
      intro a b
      obtain ⟨x, rfl⟩ := hφs a
      obtain ⟨y, rfl⟩ := hφs b
      rw [hall x, hall y]
  have hker : φ.ker = Subgroup.center ↥K := le_antisymm hN hZ
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

end Star

end CFSG.Quasithin
