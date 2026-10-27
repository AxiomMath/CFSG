module

public import CFSG.Quasithin.EmptyFaithful.S146zRPair
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Pkg
public import CFSG.Quasithin.EmptyFaithful.S146zUF3Triv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace S146zU

namespace UF4

section Groups

variable {G : Type} [Group G] [Finite G]

theorem commutator_conjSub_le_pCoreOf {G₁ K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp G₁)
    (hK₂ : conjSub s K₁ ∈ cComp G₁) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ⁅K₁, conjSub s K₁⁆ ≤ pCoreOf 2 G₁ := by
  classical
  obtain ⟨e'⟩ := e
  obtain ⟨eimg⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  have : IsSimpleGroup SBc16.L216 := SBc16.isSimpleGroup_L216
  have hs : IsSimpleGroup ↥(imageOTwoQuot G₁ K₁) := (eimg.symm.trans e').isSimpleGroup
  have hne : K₁ ≠ conjSub s K₁ := fun h => hsN (CosetGeom.mem_normalizer_of_conjSub_eq h.symm)
  have h12 : conjSub s K₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₁ hK₂)
  have h21 : K₁ ≤ Subgroup.normalizer (conjSub s K₁ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₂ hK₁)
  obtain ⟨hcomm, -⟩ := q_pair_comm_disjoint hK₁ hK₂ hne hs h12 h21
  have hK₁G : K₁ ≤ G₁ := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ G₁ := le_of_mem_cComp hK₂
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  set a' : ↥G₁ := ⟨a, hK₁G ha⟩ with ha'def
  set b' : ↥G₁ := ⟨b, hK₂G hb⟩ with hb'def
  have ha' : qPi G₁ a' ∈ imageOTwoQuot G₁ K₁ := ⟨a', Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hb' : qPi G₁ b' ∈ imageOTwoQuot G₁ (conjSub s K₁) :=
    ⟨b', Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have h1 : qPi G₁ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm _ ha' _ hb']
    group
  have h2 : a' * b' * a'⁻¹ * b'⁻¹ ∈ CFSG.Open.pCore 2 ↥G₁ := (QuotientGroup.eq_one_iff _).mp h1
  exact (UF1.mem_openPCore_iff_mem_pCoreOf _).mp h2

theorem perm_of_conjSub {G₁ K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp G₁)
    (hK₂ : conjSub s K₁ ∈ cComp G₁)
    (hn : G₁ ≤ Subgroup.normalizer ((K₁ ⊔ conjSub s K₁ : Subgroup G) : Set G)) :
    ∀ x ∈ G₁,
      x ∈ Subgroup.normalizer (K₁ : Set G) ∨ s⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set G) := by
  intro x hx
  have hC : conjSub x K₁ ∈ cComp G₁ := conjSub_mem_cComp_of_mem hK₁ hx
  have hCle : conjSub x K₁ ≤ K₁ ⊔ conjSub s K₁ := by
    intro z hz
    have hz' : x⁻¹ * z * x ∈ K₁ ⊔ conjSub s K₁ := Subgroup.mem_sup_left (mem_conjSub.mp hz)
    have h3 := (Subgroup.mem_normalizer_iff.mp (hn hx) _).mp hz'
    have e : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
    rwa [e] at h3
  rcases SBc13.eq_or_eq_of_mem_cComp_of_le_sup hK₁ hK₂ hC hCle with h | h
  · exact Or.inl (CosetGeom.mem_normalizer_of_conjSub_eq h)
  · refine Or.inr (CosetGeom.mem_normalizer_of_conjSub_eq ?_)
    ext z
    rw [mem_conjSub]
    have h1 : s * z * s⁻¹ ∈ conjSub x K₁ ↔ s * z * s⁻¹ ∈ conjSub s K₁ := by rw [h]
    rw [mem_conjSub, mem_conjSub] at h1
    have e1 : x⁻¹ * (s * z * s⁻¹) * x = (s⁻¹ * x)⁻¹ * z * (s⁻¹ * x) := by group
    have e2 : s⁻¹ * (s * z * s⁻¹) * s = z := by group
    rw [e1, e2] at h1
    exact h1

end Groups

section Sections

variable {G : Type} [Group G]

theorem not_le_ker_actH {V₁ IH H K₀ : Subgroup G} (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (hK₀H : K₀ ≤ H) (hnt : ¬ ⁅IH, K₀⁆ ≤ V₁) :
    ¬ K₀.subgroupOf H ≤ (actH hV₁ hIH).ker := by
  intro h
  apply hnt
  refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
  have h1 : actH hV₁ hIH ⟨k, hK₀H hk⟩ = 1 :=
    h (Subgroup.mem_subgroupOf.mpr hk : (⟨k, hK₀H hk⟩ : ↥H) ∈ K₀.subgroupOf H)
  have h2 := (S146zU.UF3.actH_eq_one_iff hV₁ hIH hIHN ⟨k, hK₀H hk⟩).mp h1 u hu
  have h3 := V₁.inv_mem h2
  have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ := by rw [commutatorElement_def]; group
  exact e ▸ h3

end Sections

section FF

variable {G : Type} [Group G]

theorem isFFModule_of_isFFInt {W₀ J₀ X H : Subgroup G} (hX : X = H)
    (hWN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hJN : H ≤ Subgroup.normalizer (J₀ : Set G))
    (hel : IsElemAbelian 2 (tildeOf W₀ J₀))
    (h : IsFFInt (tildeOf W₀ X) (tildeOf W₀ J₀) hel) :
    @IsFFModule ↥(tildeOf W₀ J₀) (commGroupOfElemAbelian hel) (actH hWN hJN).range := by
  rw [hX] at h
  have h1 : @IsFFModule ↥(tildeOf W₀ J₀) (commGroupOfElemAbelian hel)
      (autOn (tildeOf W₀ H) (tildeOf W₀ J₀)) := h
  rw [autOn_tilde_eq_map_actH hWN hJN le_rfl, Subgroup.subgroupOf_self,
    ← MonoidHom.range_eq_map] at h1
  exact h1

theorem isStrongFFModule_of_isStrongFFInt {W₀ J₀ X H : Subgroup G} (hX : X = H)
    (hWN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hJN : H ≤ Subgroup.normalizer (J₀ : Set G))
    (hel : IsElemAbelian 2 (tildeOf W₀ J₀))
    (h : F9.IsStrongFFInt (tildeOf W₀ X) (tildeOf W₀ J₀) hel) :
    @IsStrongFFModule ↥(tildeOf W₀ J₀) (commGroupOfElemAbelian hel) (actH hWN hJN).range := by
  rw [hX] at h
  have h1 : @IsStrongFFModule ↥(tildeOf W₀ J₀) (commGroupOfElemAbelian hel)
      (autOn (tildeOf W₀ H) (tildeOf W₀ J₀)) := h
  rw [autOn_tilde_eq_map_actH hWN hJN le_rfl, Subgroup.subgroupOf_self,
    ← MonoidHom.range_eq_map] at h1
  exact h1

end FF

end UF4

end S146zU

end CFSG.Quasithin
