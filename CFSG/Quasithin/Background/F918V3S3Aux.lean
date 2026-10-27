module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Aux

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F918V3S3

variable {G : Type*} [Group G]

theorem mem_cComp_of_isComponentOf {K M : Subgroup G} (hK : IsComponentOf K M) :
    K ∈ cComp M := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, hK.2.1, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hsubK : IsSubnormal K' K := A3.subnormal_of_le_of_le hsub hlt.le hK.1
    obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

theorem mem_map_conj_iff {a x : G} {K : Subgroup G} :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨a⁻¹ * x * a, h, by simp [MulAut.conj_apply, mul_assoc]⟩

variable [Finite G]

theorem commutator_eq_bot_of_isSolvable {M K B : Subgroup G} (hK : IsComponentOf K M)
    (hBM : B ≤ M) (hsolv : Group.IsSolvable ↥⁅K, B⁆) : ⁅K, B⁆ = ⊥ := by
  have hKc : K ∈ cComp M := mem_cComp_of_isComponentOf hK
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hnorm : B ≤ Subgroup.normalizer (K : Set G) :=
    SBc13.le_normalizer_of_commutator_solvable_J1 hBM hKc hsolv
  have hDK : ⁅K, B⁆ ≤ K := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm
  have hDn : (⁅K, B⁆.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (A3.le_normalizer_commutator_left K B)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hDn with htop | hcen
  · exfalso
    have hKD : K ≤ ⁅K, B⁆ := Subgroup.subgroupOf_eq_top.mp htop
    exact not_isSolvable_of_mem_cComp hKc
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKD)
        (Subgroup.inclusion_injective hKD))
  · have h1 : ⁅⁅K, B⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hxc := Subgroup.mem_center_iff.mp
        (hcen (show (⟨x, hDK hx⟩ : ↥K) ∈ ⁅K, B⁆.subgroupOf K from hx))
      exact congrArg Subtype.val (hxc ⟨y, hy⟩)
    have h2 : ⁅⁅B, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm B K]
      exact h1
    have h3 : ⁅⁅K, K⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hperf] at h3

theorem le_commutator_of_ne_bot {M K B : Subgroup G} (hK : IsComponentOf K M) (hBM : B ≤ M)
    (h : ⁅K, B⁆ ≠ ⊥) : K ≤ ⁅K, B⁆ := by
  rcases cComp_commutator_dichotomy_of_le (mem_cComp_of_isComponentOf hK) hBM with
    ⟨-, hsolv⟩ | hconj
  · exact absurd (commutator_eq_bot_of_isSolvable hK hBM hsolv) h
  · exact hconj ▸ le_conjClosure K B

theorem component_case_of_group {M L A B₀ K X : Subgroup G} (hAM : A ≤ M)
    (hAL : ∀ a ∈ A, ∀ y ∈ L, a⁻¹ * y * a ∈ L)
    (hB₀A : B₀ ≤ A) (hB₀n : ∀ a ∈ A, ∀ b ∈ B₀, a * b * a⁻¹ ∈ B₀)
    (hK : IsComponentOf K M) (hKL : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x) (hKB : ⁅K, B₀⁆ ≠ ⊥)
    (hX : X = ⨆ a ∈ A, K.map (MulAut.conj a).toMonoidHom) :
    X ≠ ⊥ ∧ X ≤ M ∧ (∀ x ∈ X, ∀ y ∈ L, x * y = y * x) ∧
      A ≤ Subgroup.normalizer (X : Set G) ∧ ⁅X, B₀⁆ = X := by
  have hKle : ∀ a ∈ A, K.map (MulAut.conj a).toMonoidHom ≤ X := fun a ha =>
    hX ▸ le_iSup₂_of_le (f := fun a (_ : a ∈ A) => K.map (MulAut.conj a).toMonoidHom) a ha le_rfl
  have hXle : ∀ {Y : Subgroup G}, (∀ a ∈ A, K.map (MulAut.conj a).toMonoidHom ≤ Y) → X ≤ Y :=
    fun h => hX ▸ iSup₂_le h
  have hKX : K ≤ X := by
    intro k hk
    exact hKle 1 A.one_mem (mem_map_conj_iff.mpr (by simpa using hk))
  have hB₀M : B₀ ≤ M := hB₀A.trans hAM
  have hXM : X ≤ M := by
    refine hXle fun a ha x hx => ?_
    have hx' : a⁻¹ * x * a ∈ K := mem_map_conj_iff.mp hx
    have := M.mul_mem (M.mul_mem (hAM ha) (hK.1 hx')) (M.inv_mem (hAM ha))
    simpa [mul_assoc] using this
  have hXL : X ≤ Subgroup.centralizer (L : Set G) := by
    refine hXle fun a ha x hx => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hx' : a⁻¹ * x * a ∈ K := mem_map_conj_iff.mp hx
    have hz' : a⁻¹ * z * a ∈ L := hAL a ha z hz
    have hcomm := hKL _ hx' _ hz'
    calc z * x = a * ((a⁻¹ * z * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * x * a) * (a⁻¹ * z * a)) * a⁻¹ := by rw [← hcomm]
      _ = x * z := by group
  have key : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X := by
    intro a ha
    have hle : X ≤ X.comap (MulAut.conj a).toMonoidHom := by
      refine hXle fun b hb x hx => ?_
      have hx' : b⁻¹ * x * b ∈ K := mem_map_conj_iff.mp hx
      refine hKle (a * b) (A.mul_mem ha hb) (mem_map_conj_iff.mpr ?_)
      simpa [mul_assoc] using hx'
    intro x hx
    exact hle hx
  have hAN : A ≤ Subgroup.normalizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key a ha x hx, fun hx => ?_⟩
    have := key a⁻¹ (A.inv_mem ha) _ hx
    simpa [mul_assoc] using this
  have hXB : ⁅X, B₀⁆ ≤ X := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hB₀A.trans hAN)
  have hKXB : K ≤ ⁅X, B₀⁆ :=
    (le_commutator_of_ne_bot hK hB₀M hKB).trans (Subgroup.commutator_mono hKX le_rfl)
  have hXXB : X ≤ ⁅X, B₀⁆ := by
    refine hXle fun a ha => ?_
    have hXa : X.map (MulAut.conj a).toMonoidHom ≤ X := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using key a ha x hx
    have hBa : B₀.map (MulAut.conj a).toMonoidHom ≤ B₀ := by
      rintro _ ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using hB₀n a ha b hb
    calc K.map (MulAut.conj a).toMonoidHom ≤ (⁅X, B₀⁆).map (MulAut.conj a).toMonoidHom :=
          Subgroup.map_mono hKXB
      _ = ⁅X.map (MulAut.conj a).toMonoidHom, B₀.map (MulAut.conj a).toMonoidHom⁆ :=
          Subgroup.map_commutator _ _ _
      _ ≤ ⁅X, B₀⁆ := Subgroup.commutator_mono hXa hBa
  refine ⟨?_, hXM, ?_, hAN, le_antisymm hXB hXXB⟩
  · intro hXb
    apply hKB
    have hKb : K = ⊥ := le_bot_iff.mp (hXb ▸ hKX)
    rw [hKb, Subgroup.commutator_bot_left]
  · intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hXL hx) y hy).symm

end F918V3S3

end CFSG.Quasithin
