module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLiftFusion
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftF4
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type*} [Group G]

section Generic

variable [Finite G]

theorem commute_of_mem_oddCore_of_commute_of_centralizes {L' X : Subgroup G} {s z : G}
    (hsN : centralizer ({s} : Set G) ≤ normalizer (L' : Set G)) (hzL' : z ∈ L')
    (hzX : z ∈ centralizer (X : Set G)) (hz : orderOf z = 2) (hzs : z * s = s * z)
    (hA : (oddCore (L' ⊓ centralizer (X : Set G) : Subgroup G)).map
      (L' ⊓ centralizer (X : Set G)).subtype ≤ centralizer ({z} : Set G)) :
    ∀ c ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      c * s = s * c → c * z = z * c := by
  set H := centralizer (X : Set G) with hH
  set O : Subgroup G := (oddCore H).map H.subtype with hO
  set S : Subgroup G := O ⊓ centralizer ({s} : Set G) with hS
  have hOodd : Odd (Nat.card O) := by
    rw [hO, card_map_of_injective H.subtype_injective]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hSodd : Odd (Nat.card S) := hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzs' : z⁻¹ * s = s * z⁻¹ := by
    calc z⁻¹ * s = z⁻¹ * (s * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * s) * z⁻¹ := by rw [hzs]
      _ = s * z⁻¹ := by group
  have hzS : ∀ x ∈ S, z * x * z⁻¹ ∈ S := by
    intro x hx
    refine mem_inf.2 ⟨LinearPilot.conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) hzX hx.1,
      ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hxs : x * s = s * x := mem_centralizer_singleton_iff.1 hx.2
    calc z * x * z⁻¹ * s = z * x * (z⁻¹ * s) := by group
      _ = z * x * (s * z⁻¹) := by rw [hzs']
      _ = z * (x * s) * z⁻¹ := by group
      _ = z * (s * x) * z⁻¹ := by rw [hxs]
      _ = (z * s) * x * z⁻¹ := by group
      _ = (s * z) * x * z⁻¹ := by rw [hzs]
      _ = s * (z * x * z⁻¹) := by group
  have hc : ∀ x ∈ S, Commute z (x⁻¹ * (z * x * z⁻¹)) := by
    intro x hx
    have hwL' : x⁻¹ * (z * x * z⁻¹) ∈ L' := by
      have hxN : x⁻¹ ∈ normalizer (L' : Set G) := hsN (inv_mem hx.2)
      have h1 : x⁻¹ * z * x⁻¹⁻¹ ∈ L' := (mem_normalizer_iff.1 hxN z).1 hzL'
      have e : x⁻¹ * (z * x * z⁻¹) = (x⁻¹ * z * x⁻¹⁻¹) * z⁻¹ := by group
      rw [e]
      exact L'.mul_mem h1 (L'.inv_mem hzL')
    have hwO : x⁻¹ * (z * x * z⁻¹) ∈ O :=
      O.mul_mem (O.inv_mem hx.1)
        (LinearPilot.conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) hzX hx.1)
    have hwX : x⁻¹ * (z * x * z⁻¹) ∈ centralizer (X : Set G) := map_subtype_le _ hwO
    set M : Subgroup G := L' ⊓ centralizer (X : Set G) with hM
    have hnormal : (O.subgroupOf M).Normal := ⟨fun m hm g => by
      rw [mem_subgroupOf] at hm ⊢
      exact LinearPilot.conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) g.2.2 hm⟩
    have hodd : Odd (Nat.card (O.subgroupOf M)) := by
      have h1 : Nat.card (O.subgroupOf M) = Nat.card (O ⊓ M : Subgroup G) := by
        rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective M.subtype_injective]
      rw [h1]
      exact hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
    have hle := CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ hnormal hodd
    have hwcore : x⁻¹ * (z * x * z⁻¹) ∈ (oddCore M).map M.subtype :=
      ⟨⟨_, hwL', hwX⟩, hle (mem_subgroupOf.2 hwO), rfl⟩
    exact (mem_centralizer_singleton_iff.1 (hA hwcore)).symm
  have hiter := LinearPilot.commute_of_conj_mul_mem_of_coprime (S := S) hz2
    (Nat.coprime_two_left.2 hSodd) hzS hc
  intro c hc' hcs
  exact (hiter c ⟨hc', mem_centralizer_singleton_iff.2 hcs⟩).symm

omit [Finite G] in
theorem centralizer_mul_le_normalizer_conjugate {L : Subgroup G} {t z g : G}
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hg : g⁻¹ * t * g = t * z) :
    centralizer ({t * z} : Set G) ≤ normalizer (conjugate L g : Set G) := by
  intro x hx
  have hx' : g * x * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    rw [← hg] at hx
    calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hx]
      _ = t * (g * x * g⁻¹) := by group
  have hxN := hLt hx'
  rw [mem_normalizer_iff]
  intro y
  have hmem : ∀ w : G, w ∈ conjugate L g ↔ g * w * g⁻¹ ∈ L := by
    intro w
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hl
    · intro hw
      exact ⟨g * w * g⁻¹, hw, by simp [mul_assoc]⟩
  rw [hmem, hmem, mem_normalizer_iff.1 hxN]
  have e1 : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by group
  rw [e1]

theorem le_centralizer_oddCore_of_fused_of_centralizes {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {X : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hZD : Odd (Nat.card (center D))) {z g : G} (hzD : z ∈ D) (hz : orderOf z = 2)
    (hg : g⁻¹ * t * g = t * z) (hzg : z ∈ conjugate L g)
    (hA : (oddCore (conjugate L g ⊓ centralizer (X : Set G) : Subgroup G)).map
      (conjugate L g ⊓ centralizer (X : Set G)).subtype ≤ centralizer ({z} : Set G)) :
    ∀ c ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      ∀ d ∈ D, c * d = d * c := by
  set H := centralizer (X : Set G) with hH
  set O : Subgroup G := (oddCore H).map H.subtype with hO
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hzL : z ∈ L := (hDLX hzD).1
  have hzH : z ∈ H := (hDLX hzD).2
  have htz : t * z = z * t := (mem_centralizer_iff.1 htC z hzL).symm
  have hnotcen : ∀ y ∈ D, orderOf y = 2 → ¬ (∀ d ∈ D, y * d = d * y) := by
    intro y hyD hy hcen
    have hyZ : (⟨y, hyD⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro d
      exact Subtype.ext (hcen d d.2).symm
    have h2 := (center D).orderOf_dvd_natCard hyZ
    rw [orderOf_mk, hy] at h2
    exact (Nat.not_even_iff_odd.2 hZD) (even_iff_two_dvd.2 h2)
  have hne : t ≠ z := by
    rintro rfl
    exact hnotcen t hzD ht fun d hd => (mem_centralizer_iff.1 htC d (hDLX hd).1).symm
  have h₁ : ∀ c ∈ O, c * t = t * c → c * z = z * c := by
    rintro _ ⟨c, hc, rfl⟩ hct
    have hcD := F4Pilot.mem_centralizer_of_mem_oddCore_of_commute htX (hDLX.trans inf_le_right)
      (fun d hd => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1))
      hDq (fun m hm d hd => by
        have hd' : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := hD ▸ hd
        have := layer_centralizer_normalized hLt hm hd'
        rwa [← hD] at this) hc (Subtype.ext hct)
    exact (mem_centralizer_iff.1 hcD z hzD).symm
  have h₃ := commute_of_mem_oddCore_of_commute_of_centralizes
    (centralizer_mul_le_normalizer_conjugate hLt hg) hzg hzH hz
    (by rw [← mul_assoc, ← htz, mul_assoc]) hA
  have hzO := LinearPilot.commute_of_mem_oddCore_of_four_group (mem_centralizer_iff.2 fun x hx =>
    (mem_centralizer_iff.1 htX x hx)) hzH ht hz htz hne h₁ h₃
  set C : Subgroup G := D ⊓ centralizer (O : Set G) with hC
  have hzC : z ∈ C := ⟨hzD, mem_centralizer_iff.2 fun c hc => hzO c hc⟩
  have hCn : (C.subgroupOf D).Normal := ⟨fun m hm d => by
    rw [mem_subgroupOf] at hm ⊢
    refine ⟨D.mul_mem (D.mul_mem d.2 hm.1) (D.inv_mem d.2), mem_centralizer_iff.2 fun o ho => ?_⟩
    have hdN := LinearPilot.mem_normalizer_map_oddCore (H := H) (hDLX.trans inf_le_right d.2)
    have ho' : (d : G)⁻¹ * o * (d : G)⁻¹⁻¹ ∈ O := (mem_normalizer_iff.1 (inv_mem hdN) o).1 ho
    have h1 := mem_centralizer_iff.1 hm.2 _ ho'
    calc o * ((d : G) * m * (d : G)⁻¹) =
        (d : G) * (((d : G)⁻¹ * o * (d : G)⁻¹⁻¹) * m) * (d : G)⁻¹ := by group
      _ = (d : G) * (m * ((d : G)⁻¹ * o * (d : G)⁻¹⁻¹)) * (d : G)⁻¹ := by rw [h1]
      _ = (d : G) * m * (d : G)⁻¹ * o := by group⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hDq hCn with htop | hcen
  · intro c hc d hd
    have hdC : (⟨d, hd⟩ : D) ∈ C.subgroupOf D := htop ▸ mem_top _
    exact (mem_centralizer_iff.1 (mem_subgroupOf.1 hdC).2 c hc)
  · exfalso
    refine hnotcen z hzD hz fun d hd => ?_
    have h1 := mem_center_iff.1 (hcen (mem_subgroupOf.2 (show ((⟨z, hzD⟩ : D) : G) ∈ C from hzC)))
      ⟨d, hd⟩
    exact (congrArg Subtype.val h1).symm

theorem layer_le_centralizer_oddCore (C : Type*) [Group C] [Finite C] :
    layer C ≤ centralizer (oddCore C : Set C) := by
  have hsolv : Group.IsSolvable (oddCore C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  exact commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.LocalCores.component_solvable_centralizer hsolv
      (CFSG.oddCore_normal C).isSubnormal).2

theorem map_oddCore_le_centralizer_of_mem_layer {C : Subgroup G} {z : G}
    (hz : z ∈ inSubgroup layer C) :
    (oddCore C).map C.subtype ≤ centralizer ({z} : Set G) := by
  obtain ⟨w, hw, rfl⟩ := hz
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (mem_centralizer_iff.1 (layer_le_centralizer_oddCore C hw) c hc)

theorem le_centralizer_oddCore_of_fused_of_mem_layer {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {X : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hZD : Odd (Nat.card (center D))) {z g : G} (hzD : z ∈ D) (hz : orderOf z = 2)
    (hg : g⁻¹ * t * g = t * z) (hzg : z ∈ conjugate L g)
    (hzE : z ∈ inSubgroup layer (conjugate L g ⊓ centralizer (X : Set G))) :
    ∀ c ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      ∀ d ∈ D, c * d = d * c :=
  le_centralizer_oddCore_of_fused_of_centralizes htC ht hLt htX hD hDq hZD hzD hz hg hzg
    (map_oddCore_le_centralizer_of_mem_layer hzE)

end Generic

section Unitary

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ}

omit [Finite G] in
theorem mem_layer_inf_centralizer_of_le_rootSU2 {L' : Subgroup G} (e : L' ≃* unitaryPSU h n)
    (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (unitaryPSU h n)}
    (hX₀ : X₀ ≤ rootSU2 h a b) (hX₀o : Odd (Nat.card X₀)) (hX₀1 : X₀ ≠ ⊥) {X : Subgroup G}
    (hX : X = (X₀.map e.symm.toMonoidHom).map L'.subtype) {z : G} (hzL : z ∈ L')
    (hzX : z ∈ centralizer (X : Set G)) (hz : IsPGroup 2 (zpowers z)) :
    z ∈ inSubgroup layer (L' ⊓ centralizer (X : Set G)) := by
  subst hX
  rw [layer_inf_centralizer_of_le_rootSU2 h e hn hab hX₀ hX₀o hX₀1]
  exact mem_map_blockSU_of_isPGroup_of_mem_inf_centralizer h e (by omega) hab hX₀ hX₀o hX₀1 hz
    ⟨hzL, hzX⟩

theorem map_oddCore_inf_centralizer_le_centralizer_of_le_rootSU2 {L' : Subgroup G}
    (e : L' ≃* unitaryPSU h n) (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (unitaryPSU h n)} (hX₀ : X₀ ≤ rootSU2 h a b) (hX₀o : Odd (Nat.card X₀))
    (hX₀1 : X₀ ≠ ⊥) {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L'.subtype)
    {z : G} (hzL : z ∈ L') (hzX : z ∈ centralizer (X : Set G)) (hz : IsPGroup 2 (zpowers z)) :
    (oddCore (L' ⊓ centralizer (X : Set G) : Subgroup G)).map
      (L' ⊓ centralizer (X : Set G)).subtype ≤ centralizer ({z} : Set G) :=
  map_oddCore_le_centralizer_of_mem_layer
    (mem_layer_inf_centralizer_of_le_rootSU2 h e hn hab hX₀ hX₀o hX₀1 hX hzL hzX hz)

omit [Finite G] in
theorem map_symm_rangeEquiv_map_subtype {A : Type*} [Group A] {φ : A →* G}
    (hφ : Function.Injective φ) {L' : Subgroup G} (hφL : φ.range = L') (H : Subgroup A) :
    (H.map
        ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφL)).symm.symm.toMonoidHom).map
      L'.subtype = H.map φ := by
  rw [Subgroup.map_map]
  rfl

theorem map_oddCore_range_inf_centralizer_le_centralizer {φ : unitaryPSU h n →* G}
    (hφ : Function.Injective φ) {L' : Subgroup G} (hφL : φ.range = L') (hn : 6 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (unitaryPSU h n)} (hX₀ : X₀ ≤ rootSU2 h a b)
    (hX₀o : Odd (Nat.card X₀)) (hX₀1 : X₀ ≠ ⊥) {X : Subgroup G} (hX : X = X₀.map φ) {z : G}
    (hzL : z ∈ L') (hzX : z ∈ centralizer (X : Set G)) (hz : IsPGroup 2 (zpowers z)) :
    (oddCore (L' ⊓ centralizer (X : Set G) : Subgroup G)).map
      (L' ⊓ centralizer (X : Set G)).subtype ≤ centralizer ({z} : Set G) :=
  map_oddCore_inf_centralizer_le_centralizer_of_le_rootSU2 h
    ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφL)).symm hn hab hX₀ hX₀o hX₀1
    (hX.trans (map_symm_rangeEquiv_map_subtype hφ hφL X₀).symm) hzL hzX hz

end Unitary

end CFSG.SeitzReduction.UnitaryPilot
