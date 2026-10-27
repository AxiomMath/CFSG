module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieTau
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

section AlmostSimple

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem almostSimple_subgroupOf {L K : Subgroup G} (h : AlmostSimple L) (hLK : L ≤ K) :
    AlmostSimple (L.subgroupOf K) := by
  have hLn := h.normal
  have hs := h.simple
  let e : ↥(L.subgroupOf K) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLK
  refine ⟨inferInstance, ?_, ?_, ?_, fun x => ?_⟩
  · have : Nontrivial ↥(L.subgroupOf K) := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
    simpa using congrArg e hc
  · refine le_bot_iff.mp fun x hx => ?_
    have hxC : (x : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_centralizer_iff.mp hx ⟨y, hLK hy⟩ hy
      exact congrArg Subtype.val h1
    rw [h.centralizer_eq, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr (Subtype.ext hxC)
  · obtain ⟨k, hk⟩ := h.two (x : G)
    exact ⟨k, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hk⟩

theorem solvableRadical_eq_bot_of_le {L K : Subgroup G} (h : AlmostSimple L) (hLK : L ≤ K) :
    CFSG.solvableRadical ↥K = ⊥ :=
  (almostSimple_subgroupOf h hLK).solvableRadical_eq_bot

theorem card_barRad_of_le {L K A : Subgroup G} (h : AlmostSimple L) (hLK : L ≤ K)
    (hAK : A ≤ K) : Nat.card ↥(barRad ↥K (A.subgroupOf K)) = Nat.card A := by
  have hR := solvableRadical_eq_bot_of_le h hLK
  unfold barRad
  rw [Subgroup.card_map_of_injective ?_]
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  · rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hR]

omit [Finite G] in
theorem le_normalizer_inf {T L : Subgroup G} [L.Normal] :
    T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxT, hxL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), ‹L.Normal›.conj_mem x hxL t⟩
  · rintro ⟨hxT, hxL⟩
    have e : x = t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) (T.inv_mem (T.inv_mem ht))
    · rw [e]
      exact ‹L.Normal›.conj_mem _ hxL t⁻¹

omit [Finite G] in
theorem map_conjSub {X : Type*} [Group X] (ψ : X →* G) (M : X) (P : Subgroup X) :
    (A1b.conjSub M P).map ψ = A1b.conjSub (ψ M) (P.map ψ) := by
  unfold A1b.conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

omit [Finite G] in
theorem card_conjSub (g : G) (H : Subgroup G) : Nat.card (A1b.conjSub g H) = Nat.card H := by
  unfold A1b.conjSub
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [Finite G] in
theorem conjSub_le_of_mem {K U : Subgroup G} {g : G} (hg : g ∈ K) (hU : U ≤ K) :
    A1b.conjSub g U ≤ K := by
  rintro _ ⟨u, hu, rfl⟩
  show g * u * g⁻¹ ∈ K
  exact K.mul_mem (K.mul_mem hg (hU hu)) (K.inv_mem hg)

theorem le_nParam_of_almostSimple {L T U A : Subgroup G} {f : ℕ} (h : AlmostSimple L)
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) (hUT : U ≤ T) (hAU : A ≤ U) (hUL : U ≤ L)
    (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥) (hcard : Nat.card A = 2 ^ f) (hf : 2 ≤ f)
    (hUA : U ≤ Subgroup.centralizer (A : Set G))
    (huniq : ∀ g : G, A1b.conjSub g A ≤ T → A1b.conjSub g A = A)
    (hTU : T ≤ Subgroup.normalizer (U : Set G))
    (hNA : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hgen : ∀ l ∈ L, A1b.conjSub l U ≠ U → L ≤ U ⊔ A1b.conjSub l U) :
    (f : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have hLn := h.normal
  refine le_nParam_of_tau (U := U) hT (hAU.trans hUT) hA hf (fun g _ hg => huniq g hg) ?_ ?_ ?_
  ·
    intro u hu
    refine ⟨hUT hu, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤ (Subgroup.mem_top u),
      fun a ha => ?_⟩
    have hua : a * u = u * a := Subgroup.mem_centralizer_iff.mp (hUA hu) a ha
    rw [commutatorElement_def, ← hua]
    simp
  ·
    intro hN
    have hAL : A ≤ L := hAU.trans hUL
    have hAn : A.Normal :=
      ⟨fun a ha g => (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_top g)) a).mp ha⟩
    have hs := h.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf L) with h1 | h1
    · rw [Subgroup.subgroupOf_eq_bot] at h1
      exact hA1 (le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h1) hx (hAL hx))
    · rw [Subgroup.subgroupOf_eq_top] at h1
      obtain ⟨a, b, hab⟩ := h.nonabelian
      exact hab (Subtype.ext (B2F.isElemAbelian_comm hA (h1 a.2) (h1 b.2)))
  ·
    intro K _ hUK hAK hKN
    have hKU : ¬ K ≤ Subgroup.normalizer (U : Set G) := fun hle => hKN (hle.trans hNA)
    obtain ⟨k, hkK, hk⟩ : ∃ k ∈ K, A1b.conjSub k U ≠ U := by
      by_contra hc
      push Not at hc
      exact hKU fun k hk => A1b.conjSub_eq_iff_mem_normalizer.mp (hc k hk)
    have hk' : k ∈ L ⊔ T := hLT ▸ Subgroup.mem_top k
    obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk'
    have hcl : A1b.conjSub (l * t) U = A1b.conjSub l U := by
      rw [A1b.conjSub_mul, A1b.conjSub_eq_iff_mem_normalizer.mpr (hTU ht)]
    rw [hcl] at hk
    have hLK : L ≤ K := by
      refine (hgen l hl hk).trans (sup_le hUK ?_)
      rw [← hcl]
      exact conjSub_le_of_mem hkK hUK
    refine ⟨fun hsol => h.not_isSolvable ?_, ?_⟩
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLK)
    · rw [card_barRad_of_le h hLK hAK, hcard]

end AlmostSimple

end CFSG.Quasithin.Vol2.Ch11.SecE3
