module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Two
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5LiftB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem w183br4_hasQuotShape_of_mulEquiv {K L L' : Subgroup G} (e : ↥L ≃* ↥L')
    (hK : ∀ l : ↥L, (l : G) ∈ K ↔ (e l : G) ∈ K) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape L' K P := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  refine ⟨X, hX, φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_, hPX⟩
  intro k
  change φ (e.symm k) = 1 ↔ (k : G) ∈ K
  rw [hφk (e.symm k)]
  have h := hK (e.symm k)
  rwa [show e (e.symm k) = k from e.apply_symm_apply k] at h

private theorem w183br4_isComponentModN_map_mulEquiv {K H L : Subgroup G} (e : G ≃* G)
    (hK : K.map e.toMonoidHom = K) (hH : H.map e.toMonoidHom = H)
    (h : IsComponentModN K H L) :
    IsComponentModN K H (L.map e.toMonoidHom) := by
  have hfe : Function.Injective e.toMonoidHom := fun a _b hab => e.injective (by simpa using hab)
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : e.symm k ∈ K := by
      rw [← hK] at hk
      obtain ⟨k', hk'K, hk'eq⟩ := Subgroup.mem_map.1 hk
      have hkk : k' = e.symm k := by
        rw [← hk'eq]
        change k' = e.symm (e k')
        rw [e.symm_apply_apply]
      rwa [hkk] at hk'K
    exact Subgroup.mem_map.2 ⟨e.symm k, h.2.1 hk', by simp⟩
  · rintro x ⟨l, hl, rfl⟩
    rw [← hH]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.2.2.1 hl)
  · have hsub := h.2.2.2.1.map e.toMonoidHom
    rwa [hH] at hsub
  · refine w183br4_hasQuotShape_of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom hfe) ?_ h.2.2.2.2
    intro l
    constructor
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hl
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK] at hl
      obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.1 hl
      have hkl : k = l := e.injective hkeq
      rwa [hkl] at hkK

theorem br4_conj_eq_of_good {H K L : Subgroup G}
    (hr : CFSG.Open.pRank 3 H ≤ 3) (hL : IsComponentModN K H L)
    (hX : HasQuotShape L (K : Set G) (fun X _ => Br4Good X)) :
    ∀ h ∈ H, conjSubgroup L h = L := by
  intro h hh
  by_contra hne
  let L₂ : Subgroup G := conjSubgroup L h
  have hHnorm : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.2.1.trans hL.2.2.1)).mp hL.1
  have hKmap : K.map (MulAut.conj h⁻¹).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnorm (H.inv_mem hh))
  have hHmap : H.map (MulAut.conj h⁻¹).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H.inv_mem hh))
  have hL₂ : IsComponentModN K H L₂ :=
    w183br4_isComponentModN_map_mulEquiv (MulAut.conj h⁻¹) hKmap hHmap hL
  have hmem : ∀ x : G, (MulAut.conj h⁻¹) x ∈ K ↔ x ∈ K := by
    intro x
    constructor
    · intro hx
      rw [← hKmap] at hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
      rwa [(MulAut.conj h⁻¹).injective hkx] at hk
    · intro hx
      have hx' : (MulAut.conj h⁻¹) x ∈ K.map (MulAut.conj h⁻¹).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hKmap] at hx'
  have hQ₂ : HasQuotShape L₂ (K : Set G) (fun X _ => Br4Good X) :=
    w183br4_hasQuotShape_of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj h⁻¹).toMonoidHom
        (MulAut.conj h⁻¹).injective)
      (fun l => (hmem (l : G)).symm) hX
  have hcomm := w183_components_commute hL hL₂ (Ne.symm hne)
  let K0 : Subgroup ↥H := K.subgroupOf H
  haveI hK0n : K0.Normal := hL.1
  let π : ↥H →* ↥H ⧸ K0 := QuotientGroup.mk' K0
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective K0
  have hker : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ K := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let A₁ : Subgroup (↥H ⧸ K0) := (L.subgroupOf H).map π
  let A₂ : Subgroup (↥H ⧸ K0) := (L₂.subgroupOf H).map π
  obtain ⟨X₁, _, hX₁, ⟨e₁⟩⟩ := exists_mulEquiv_map_of_hasQuotShape hL.2.2.1 π hker hX
  obtain ⟨X₂, _, hX₂, ⟨e₂⟩⟩ := exists_mulEquiv_map_of_hasQuotShape hL₂.2.2.1 π hker hQ₂
  have hgood₁ : Br4Good ↥A₁ := Br4Good.of_mulEquiv e₁.symm hX₁
  have hgood₂ : Br4Good ↥A₂ := Br4Good.of_mulEquiv e₂.symm hX₂
  have hcommA : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have hcommG : ((a' : G) * (b' : G) * (a' : G)⁻¹ * (b' : G)⁻¹) ∈ K :=
      hcomm (a' : G) (Subgroup.mem_subgroupOf.mp ha') (b' : G)
        (Subgroup.mem_subgroupOf.mp hb')
    have h1 : π a' * π b' * (π a')⁻¹ * (π b')⁻¹ = 1 := by
      have h0 : π (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
        rw [hker]
        simpa using hcommG
      simpa only [map_mul, map_inv] using h0
    calc π a' * π b'
        = (π a' * π b' * (π a')⁻¹ * (π b')⁻¹) * (π b' * π a') := by group
      _ = 1 * (π b' * π a') := by rw [h1]
      _ = π b' * π a' := by group
  have hcenter₁ : Subgroup.center ↥A₁ = ⊥ := by
    haveI : IsSimpleGroup ↥A₁ := hgood₁.1
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
    intro hc
    obtain ⟨a, b, hab⟩ := hgood₁.nonabelian
    exact hab (hc.is_comm.comm a b)
  have hdisj : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzcenter : (⟨z, hz.1⟩ : ↥A₁) ∈ Subgroup.center ↥A₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hcommA (g : ↥H ⧸ K0) g.2 z hz.2
    have hz1 : (⟨z, hz.1⟩ : ↥A₁) = 1 := by
      rw [← Subgroup.mem_bot, ← hcenter₁]
      exact hzcenter
    exact congrArg Subtype.val hz1
  let S : Subgroup (↥H ⧸ K0) := A₁ ⊔ A₂
  let A₁' : Subgroup ↥S := A₁.subgroupOf S
  let A₂' : Subgroup ↥S := A₂.subgroupOf S
  have hA₂cent : A₂ ≤ Subgroup.centralizer (A₁ : Set (↥H ⧸ K0)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommA a ha b hb
  have hA₁cent : A₁ ≤ Subgroup.centralizer (A₂ : Set (↥H ⧸ K0)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcommA a ha b hb).symm
  have hA₁'normal : A₁'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (hA₂cent.trans (Subgroup.centralizer_le_normalizer _)))
  have hA₂'normal : A₂'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le (hA₁cent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)
  have hdisj' : A₁' ⊓ A₂' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxinf : (x : ↥H ⧸ K0) ∈ A₁ ⊓ A₂ :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
    rw [hdisj, Subgroup.mem_bot] at hxinf
    exact Subtype.ext hxinf
  have hsup' : A₁' ⊔ A₂' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (A₁ ⊔ A₂)
  have hgood₁' : Br4Good ↥A₁' :=
    Br4Good.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm hgood₁
  have hgood₂' : Br4Good ↥A₂' :=
    Br4Good.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm hgood₂
  have hnonab₁ : ∃ a ∈ A₁', ∃ b ∈ A₁', a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hgood₁'.nonabelian
    exact ⟨(x : ↥S), x.2, (y : ↥S), y.2, fun h => hxy (Subtype.ext (by simpa using h))⟩
  have hnonab₂ : ∃ a ∈ A₂', ∃ b ∈ A₂', a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hgood₂'.nonabelian
    exact ⟨(x : ↥S), x.2, (y : ↥S), y.2, fun h => hxy (Subtype.ext (by simpa using h))⟩
  have htwo : Br4TwoSimple ↥S A₁' A₂' :=
    ⟨hA₁'normal, hA₂'normal, hgood₁'.1, hgood₂'.1, hnonab₁, hnonab₂, hdisj', hsup'⟩
  let P : Subgroup ↥H := S.comap π
  have hmaps : Set.MapsTo π (P : Set ↥H) (S : Set (↥H ⧸ K0)) :=
    fun _ hx => Subgroup.mem_comap.mp hx
  let θ : ↥P →* ↥S := π.restrict hmaps
  have hθ : Function.Surjective θ := by
    intro s
    obtain ⟨x, hx⟩ := hπsurj (s : ↥H ⧸ K0)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · exact Subgroup.mem_comap.mpr (hx ▸ s.2)
    · apply Subtype.ext
      exact hx
  have hrank : CFSG.pRank 3 ↥P ≤ 3 := by
    have hle : CFSG.pRank 3 ↥P ≤ CFSG.pRank 3 ↥H := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥P,
        CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥H]
      exact CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) P.subtype
        P.subtype_injective
    exact hle.trans ((CFSG.SectionRank.pRank_coe_eq_openPRank 3 H).trans_le hr)
  exact br4_false_of_two_good hrank θ hθ htwo hgood₁' hgood₂'

end CFSG.LocalAnalysis.WeakClosure81

end
