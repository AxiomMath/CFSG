module

public import CFSG.Quasithin.EmptyFaithful.SzPS8PLift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

namespace SzPS8

section XSub

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem centerOf_le_pCoreOf (h : Hyp1281Two G T M (yOfL22 T M)) :
    centerOf (uOfL22 T M) ≤ pCoreOf 2 (mcOf T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 (centerOf (uOfL22 T M)) :=
    h.sylow.1.to_le ((inf_le_left : centerOf (uOfL22 T M) ≤ uOfL22 T M).trans h.uOfL22_le_T)
  refine le_pCoreOf_of_le_normalizer 2 ((centerOf_uOfL22_le_cZU h).trans cZU_le) ?_ hZ2
  intro x hx
  exact normalizer_le_normalizer_centerOf _ (h.g1_le_normalizer_uOfL22 hx)

theorem rhoΓ_centerOf (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {z : ↥(mcOf T)} (hz : (z : G) ∈ centerOf (uOfL22 T M)) : rhoΓ h D z = 1 :=
  rhoΓ_eq_one_of_mem_pCoreOf h D (centerOf_le_pCoreOf h hz)

@[expose] noncomputable def xSub (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    (F : Subgroup ↥(D.img (mcOf T))) : Subgroup G :=
  (((cZU T M).subgroupOf (mcOf T)) ⊓ F.comap (rhoΓ h D)).map (mcOf T).subtype

variable {h : Hyp1281Two G T M (yOfL22 T M)} {D : HatModel T M}
  {F : Subgroup ↥(D.img (mcOf T))}

theorem mem_xSub {x : G} :
    x ∈ xSub h D F ↔ ∃ hx : x ∈ mcOf T, x ∈ cZU T M ∧ rhoΓ h D ⟨x, hx⟩ ∈ F := by
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨y.2, hy1, hy2⟩
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨x, hx⟩, ⟨h1, h2⟩, rfl⟩

theorem xSub_le_cZU : xSub h D F ≤ cZU T M := fun _ hx => (mem_xSub.mp hx).2.1

theorem centerOf_le_xSub : centerOf (uOfL22 T M) ≤ xSub h D F := fun z hz =>
  mem_xSub.mpr ⟨cZU_le (centerOf_uOfL22_le_cZU h hz), centerOf_uOfL22_le_cZU h hz, by
    rw [rhoΓ_centerOf h D hz]
    exact F.one_mem⟩

theorem xSub_normal (hFn : F.Normal) :
    ∀ x ∈ mcOf T, ∀ p ∈ xSub h D F, x * p * x⁻¹ ∈ xSub h D F := by
  intro x hx p hp
  obtain ⟨hpH, hpP, hpF⟩ := mem_xSub.mp hp
  refine mem_xSub.mpr ⟨(mcOf T).mul_mem ((mcOf T).mul_mem hx hpH) ((mcOf T).inv_mem hx),
    cZU_normal h x hx p hpP, ?_⟩
  have e : (⟨x * p * x⁻¹, (mcOf T).mul_mem ((mcOf T).mul_mem hx hpH) ((mcOf T).inv_mem hx)⟩ :
      ↥(mcOf T)) = ⟨x, hx⟩ * ⟨p, hpH⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact hFn.conj_mem _ hpF _

theorem xSub_isSubnormal (hFn : F.Normal) : IsSubnormal (xSub h D F) (mcOf T) :=
  IsSubnormal.step (xSub_le_cZU.trans cZU_le) ⟨fun n hn g => xSub_normal hFn (g : G) g.2 (n : G) hn⟩
    (IsSubnormal.refl _)

theorem imgΓ_xSub (hFP : F ≤ imgΓ h D (cZU T M)) : imgΓ h D (xSub h D F) = F := by
  have hsub : (xSub h D F).subgroupOf (mcOf T) =
      (cZU T M).subgroupOf (mcOf T) ⊓ F.comap (rhoΓ h D) := by
    unfold xSub
    exact Subgroup.comap_map_eq_self_of_injective (mcOf T).subtype_injective _
  unfold imgΓ
  rw [hsub]
  apply le_antisymm
  · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    exact hy
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := hFP hf
    exact ⟨p, ⟨hp, hf⟩, rfl⟩

theorem exists_lift_xSub (hyp : Hyp1421 G T M) (h39 : A39ForSQTK)
    (hFP : F ≤ imgΓ h D (cZU T M)) {A : Subgroup ↥(D.img (mcOf T))} (hAF : A ≤ F)
    (hAn : (A.subgroupOf F).Normal) (hAs : IsSimpleGroup ↥A) (hAnc : ¬ IsMulCommutative ↥A) :
    ∃ L : Subgroup G, L ∈ cComp (xSub h D F) ∧
      (L.subgroupOf (mcOf T)).map (rhoΓ h D) = A := by
  have hX := imgΓ_xSub (h := h) (D := D) hFP
  exact exists_cZU_lift hyp h h39 D centerOf_le_xSub xSub_le_cZU (by rw [hX]; exact hAF)
    (by rw [hX]; exact hAn) hAs hAnc

end XSub

section Unique

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem eq_of_cZU_lift_eq (hyp : Hyp1421 G T M) (h : Hyp1281Two G T M (yOfL22 T M))
    (h37 : A37ForSQTK) (D : HatModel T M) {X L L' : Subgroup G}
    (hX1 : centerOf (uOfL22 T M) ≤ X) (hX2 : X ≤ cZU T M) (hL : L ∈ cComp X)
    (hL' : L' ∈ cComp X) {K : Subgroup ↥(D.img (mcOf T))}
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = K)
    (hL'ρ : (L'.subgroupOf (mcOf T)).map (rhoΓ h D) = K) (hKs : IsSimpleGroup ↥K)
    (hKnc : ¬ IsMulCommutative ↥K) : L = L' := by
  classical
  by_contra hne
  have hXH : X ≤ mcOf T := hX2.trans cZU_le
  have hHX : pCoreOf 2 X ≠ ⊥ := pCoreOf_ne_bot_of_le_cZU h hX1 hX2
  have hc2 := lemma_1_2_1_two hyp.qtke hyp.simple hyp.nonabelian h37 hHX hL hL' hne
  have hcomm : ⁅L, L'⁆ ≤ pCoreOf 2 X := hc2.1.trans hc2.2
  set ρ := rhoΓ h D with hρ
  have hLρ' : ∀ k ∈ K, ∃ a : ↥(mcOf T), (a : G) ∈ L ∧ ρ a = k := by
    intro k hk
    rw [← hLρ] at hk
    obtain ⟨a, ha, hak⟩ := hk
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, hak⟩
  have hL'ρ' : ∀ k ∈ K, ∃ a : ↥(mcOf T), (a : G) ∈ L' ∧ ρ a = k := by
    intro k hk
    rw [← hL'ρ] at hk
    obtain ⟨a, ha, hak⟩ := hk
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, hak⟩
  set Q : Subgroup ↥(D.img (mcOf T)) := ((pCoreOf 2 X).subgroupOf (mcOf T)).map ρ with hQ
  have hQ2 : IsPGroup 2 ↥Q := by
    have h1 : IsPGroup 2 ↥((pCoreOf 2 X).subgroupOf (mcOf T)) :=
      (pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXH)).symm
    exact h1.map ρ
  have hKQ : K ≤ Q := by
    calc K = ⁅K, K⁆ := (commutator_self_of_simple hKs hKnc).symm
      _ ≤ Q := by
        refine Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => ?_
        obtain ⟨a₁, ha₁, rfl⟩ := hLρ' k₁ hk₁
        obtain ⟨a₂, ha₂, rfl⟩ := hL'ρ' k₂ hk₂
        have hmem : (⁅a₁, a₂⁆ : ↥(mcOf T)) ∈ (pCoreOf 2 X).subgroupOf (mcOf T) :=
          Subgroup.mem_subgroupOf.mpr (hcomm (Subgroup.commutator_mem_commutator ha₁ ha₂))
        exact ⟨_, hmem, map_commutatorElement ρ a₁ a₂⟩
  have hK2 : IsPGroup 2 ↥K := hQ2.to_le hKQ
  have := hK2.isNilpotent
  have hs : Group.IsSolvable ↥K := inferInstance
  exact hKnc ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b⟩⟩

theorem conj_cZU_lift (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) {X L : Subgroup G}
    (hXn : ∀ x ∈ mcOf T, ∀ p ∈ X, x * p * x⁻¹ ∈ X) (hL : L ∈ cComp X) {t : G}
    (ht : t ∈ mcOf T) {K : Subgroup ↥(D.img (mcOf T))}
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = K) :
    L.map (MulAut.conj t).toMonoidHom ∈ cComp X ∧
      ((L.map (MulAut.conj t).toMonoidHom).subgroupOf (mcOf T)).map (rhoΓ h D) =
        K.map (MulAut.conj (rhoΓ h D ⟨t, ht⟩)).toMonoidHom := by
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun p => ⟨fun hp => hXn t ht p hp, fun hp => by
      have := hXn t⁻¹ ((mcOf T).inv_mem ht) _ hp
      simpa [mul_assoc] using this⟩
  refine ⟨?_, ?_⟩
  · have h1 := cComp_map_mulEquiv (MulAut.conj t) hL
    rwa [A38.map_conj_eq_iff.mpr htX] at h1
  · rw [← hLρ]
    ext γ
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_subgroupOf.mp hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hlx
      have hlH : l ∈ mcOf T := by
        have : l = t⁻¹ * (x : G) * t := by
          rw [← hlx]
          group
        rw [this]
        exact (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem ht) x.2) ht
      refine ⟨rhoΓ h D ⟨l, hlH⟩, ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, ?_⟩
      have e : x = ⟨t, ht⟩ * ⟨l, hlH⟩ * ⟨t, ht⟩⁻¹ := by
        apply Subtype.ext
        exact hlx.symm
      rw [e]
      simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨⟨t, ht⟩ * y * ⟨t, ht⟩⁻¹, ?_, ?_⟩
      · show (⟨t, ht⟩ * y * ⟨t, ht⟩⁻¹ : ↥(mcOf T)) ∈
          (L.map (MulAut.conj t).toMonoidHom).subgroupOf (mcOf T)
        rw [Subgroup.mem_subgroupOf]
        exact ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, by simp [MulAut.conj_apply]⟩
      · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end Unique

section Fix

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem not_le_M_of_normal_image (h : Hyp1281Two G T M (yOfL22 T M))
    (hnab : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) {L : Subgroup G}
    {N : Subgroup ↥(D.img (mcOf T))} (hNn : N.Normal)
    (hNL : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = N) (hN : N ≠ ⊥) : ¬ L ≤ M := by
  intro hLM
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  have hN' := eq_bot_of_normal_fix h hnab hg D haV haZ
    (N := N.map (D.img (mcOf T)).subtype)
    (fun γ hγ n hn => by
      obtain ⟨k, hk, rfl⟩ := hn
      exact ⟨(⟨γ, hγ⟩ : ↥(D.img (mcOf T))) * k * (⟨γ, hγ⟩ : ↥(D.img (mcOf T)))⁻¹,
        hNn.conj_mem k hk _, rfl⟩)
    (fun n hn => by
      obtain ⟨k, hk, rfl⟩ := hn
      rw [← hNL] at hk
      obtain ⟨l, hl, rfl⟩ := hk
      exact S143V.rhoH_fix_of_mem_M h hnab D haV haZ
        (hLM (Subgroup.mem_subgroupOf.mp hl)))
  apply hN
  rw [eq_bot_iff]
  intro k hk
  have : (k : D.V ≃ₗ[ZMod 2] D.V) ∈ N.map (D.img (mcOf T)).subtype := ⟨k, hk, rfl⟩
  rw [hN', Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact Subtype.ext this

end Fix

end SzPS8

end CFSG.Quasithin
