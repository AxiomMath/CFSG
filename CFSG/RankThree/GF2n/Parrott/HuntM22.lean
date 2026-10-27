module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerBridge
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsNonsplit

public section

namespace CFSG.RankThree.GF2n.Parrott

open Subgroup CFSG

variable {G : Type} [Group G] [Finite G]

theorem center_facts_of_selfCentralizing {L : Subgroup G} {z : G}
    (hL : L = Subgroup.centralizer ({z} : Set G)) (hz : orderOf z = 2)
    (h2 : Nat.card (Subgroup.center L) = 2) :
    z ∈ L ∧ (⟨z, hL.symm ▸ mem_centralizer_singleton_iff.mpr rfl⟩ : L) ∈
        Subgroup.center L ∧
      Subgroup.centralizer (L : Set G) = Subgroup.zpowers z ∧
      Subgroup.normalizer (L : Set G) = L ∧
      Subgroup.centralizer ({z} : Set G) = Subgroup.normalizer (L : Set G) := by
  subst hL
  have hzL : z ∈ Subgroup.centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hzZ : (⟨z, hzL⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      Subgroup.center (Subgroup.centralizer ({z} : Set G)) := by
    refine Subgroup.mem_center_iff.mpr fun l => ?_
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp l.2
  have hzZmap : z ∈ (Subgroup.center (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype := ⟨⟨z, hzL⟩, hzZ, rfl⟩
  have hCL : Subgroup.centralizer (Subgroup.centralizer ({z} : Set G) : Set G) =
      (Subgroup.center (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype := by
    apply le_antisymm
    · intro x hx
      have hxL : x ∈ Subgroup.centralizer ({z} : Set G) := by
        have hxz : x * z = z * x :=
          (mem_centralizer_iff.mp hx z hzL).symm
        exact mem_centralizer_singleton_iff.mpr hxz
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr fun l => ?_
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx l l.2
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_centralizer_iff.mpr fun l hl => congrArg
        (fun u : Subgroup.centralizer ({z} : Set G) => ((u : Subgroup.centralizer ({z} : Set G)) : G))
        (Subgroup.mem_center_iff.mp hy ⟨l, hl⟩)
  have hZeq : (Subgroup.center (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype = Subgroup.zpowers z := by
    have hle : Subgroup.zpowers z ≤ (Subgroup.center
        (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype :=
      Subgroup.zpowers_le.mpr hzZmap
    have hcard1 : Nat.card (Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers, hz]
    have hcard2 : Nat.card ((Subgroup.center (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) = 2 := by
      rw [Subgroup.card_map_of_injective
        (Subgroup.centralizer ({z} : Set G)).subtype_injective, h2]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])).symm
  have hCLz : Subgroup.centralizer (Subgroup.centralizer ({z} : Set G) : Set G) =
      Subgroup.zpowers z := hCL.trans hZeq
  have hNL : Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
    apply le_antisymm
    · intro g hg
      have hgZ : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hg z).1 hzL
      have hgZc : (⟨g * z * g⁻¹, hgZ⟩ : Subgroup.centralizer ({z} : Set G)) ∈
          Subgroup.center (Subgroup.centralizer ({z} : Set G)) := by
        refine Subgroup.mem_center_iff.mpr fun l => ?_
        apply Subtype.ext
        have hgl : g⁻¹ * (l : G) * g ∈ Subgroup.centralizer ({z} : Set G) :=
          (Subgroup.mem_normalizer_iff''.mp hg l).1 l.2
        have hzcomm : (g⁻¹ * (l : G) * g) * z =
            z * (g⁻¹ * (l : G) * g) :=
          mem_centralizer_singleton_iff.mp hgl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (l : G) * (g * z * g⁻¹) =
            g * ((g⁻¹ * (l : G) * g) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * (l : G) * g)) * g⁻¹ := by rw [hzcomm]
          _ = (g * z * g⁻¹) * (l : G) := by group
      have hgZ1 : (⟨⟨g * z * g⁻¹, hgZ⟩, hgZc⟩ :
          Subgroup.center (Subgroup.centralizer ({z} : Set G))) ≠ 1 := by
        intro h
        have h1 : g * z * g⁻¹ = 1 := congrArg
          (fun u : Subgroup.center (Subgroup.centralizer ({z} : Set G)) =>
            ((u : Subgroup.centralizer ({z} : Set G)) : G)) h
        have hz1 : z = 1 := by
          have := congrArg (fun t => g⁻¹ * t * g) h1
          simpa [mul_assoc] using this
        rw [hz1, orderOf_one] at hz
        exact absurd hz (by norm_num)
      have hzZ1 : (⟨⟨z, hzL⟩, hzZ⟩ :
          Subgroup.center (Subgroup.centralizer ({z} : Set G))) ≠ 1 := by
        intro h
        have h1 : z = 1 := congrArg
          (fun u : Subgroup.center (Subgroup.centralizer ({z} : Set G)) =>
            ((u : Subgroup.centralizer ({z} : Set G)) : G)) h
        rw [h1, orderOf_one] at hz
        exact absurd hz (by norm_num)
      obtain ⟨w, hw1, hwu⟩ :=
        (Nat.card_eq_two_iff' (1 : Subgroup.center (Subgroup.centralizer ({z} : Set G)))).1 h2
      have h1 := hwu _ hzZ1
      have h2' := hwu _ hgZ1
      have heq : (⟨⟨g * z * g⁻¹, hgZ⟩, hgZc⟩ :
          Subgroup.center (Subgroup.centralizer ({z} : Set G))) =
          ⟨⟨z, hzL⟩, hzZ⟩ := h2'.trans h1.symm
      have hval : g * z * g⁻¹ = z := congrArg
        (fun u : Subgroup.center (Subgroup.centralizer ({z} : Set G)) =>
          ((u : Subgroup.centralizer ({z} : Set G)) : G)) heq
      have hgz : g * z = z * g := by
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [hval]
      exact mem_centralizer_singleton_iff.mpr hgz
    · exact Subgroup.le_normalizer
  refine ⟨hzL, hzZ, hCLz, hNL, ?_⟩
  rw [hNL]

open Subgroup CFSG CFSG.RankThree.GF2n.Parrott
open CFSG.EvenSmallLie.UnitarySix CFSG.EvenSmallLie.UnitarySix.ToddOrbit CFSG.Fischer

theorem davisSolomon_of_quasisimple_centralizer
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G} {L : Subgroup G}
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hL : L = Subgroup.centralizer ({z} : Set G)) (hz : orderOf z = 2)
    (hLq : CFSG.IsQuasisimple L) (h2 : Nat.card (Subgroup.center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 6 2 1) :
    ∃ (p : L →* Equiv.Perm (Fin 693)) (E : Subgroup G),
      (∀ y, p y ∈ T46) ∧ (∀ x ∈ T46, ∃ y, p y = x) ∧
      (∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = z) ∧
      E = ToddOrbit.toddLift p ∧
      ToddOrbit.Hyp z L E p ∧ DavisSolomonFacts G z L E ∧
      Subgroup.centralizer (E : Set G) ≤ E ⊔ Subgroup.centralizer (L : Set G) := by
  subst hL
  have hzL : z ∈ Subgroup.centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hzZ : (⟨z, hzL⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      Subgroup.center (Subgroup.centralizer ({z} : Set G)) := by
    refine Subgroup.mem_center_iff.mpr fun l => ?_
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp l.2
  obtain ⟨_, _, hCLz, hNL, _⟩ :=
    center_facts_of_selfCentralizing rfl hz h2
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨p, hpT46, hpsurj, hpker⟩ :=
    exists_hom_T46 hzL hzZ hz1 h2 hQ
  let π : Subgroup.centralizer ({z} : Set G) →* T46 := p.codRestrict T46 hpT46
  have hπsurj : Function.Surjective π := by
    intro x
    obtain ⟨y, hy⟩ := hpsurj x x.2
    exact ⟨y, Subtype.ext hy⟩
  have hπker : ∀ y : Subgroup.centralizer ({z} : Set G),
      π y = 1 ↔ (y : G) = 1 ∨ (y : G) = z := by
    intro y
    have hπy : π y = 1 ↔ p y = 1 := by
      simp [π]
    exact hπy.trans (hpker y)
  have hH : IsDoubleCover z (Subgroup.centralizer ({z} : Set G)) π :=
    ⟨hπsurj, hπker, hzL, fun _ hx => hx, hz⟩
  let D : ToddParabolic T46 := toddT46
  let E : Subgroup G := liftSub π D.A
  have hEp : E = ToddOrbit.toddLift p := by
    dsimp [E, D, π, ToddOrbit.toddLift]
    exact (map_comap_uA_eq_liftSub hpT46).symm
  have hzZmap : z ∈ (Subgroup.center (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype := ⟨⟨z, hzL⟩, hzZ, rfl⟩
  have hker : π.ker = Subgroup.center (Subgroup.centralizer ({z} : Set G)) :=
    ker_eq_center h2 hz hzZmap hH
  have hperfect : Group.IsPerfect (Subgroup.centralizer ({z} : Set G)) := hLq.1
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := hH.toddLift_sq D hker hQ
  have hEcard : Nat.card E = 2 ^ 10 := hH.card_toddLift D
  have hzE : z ∈ E := hH.t_mem_liftSub D.A
  have hCE : Subgroup.centralizer (E : Set G) ≤ E ⊔
      Subgroup.centralizer (Subgroup.centralizer ({z} : Set G) : Set G) := by
    intro x hx
    have hxL : x ∈ Subgroup.centralizer ({z} : Set G) := by
      have hxz : x * z = z * x := (mem_centralizer_iff.mp hx z hzE).symm
      exact mem_centralizer_singleton_iff.mpr hxz
    have hxE : x ∈ E := hH.mem_toddLift_of_commute D hxL
      (fun e he => (mem_centralizer_iff.mp hx e he).symm)
    exact mem_sup_left hxE
  have hsup : Subgroup.centralizer ({z} : Set G) ⊔
      Subgroup.centralizer (Subgroup.centralizer ({z} : Set G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
    apply sup_eq_left.mpr
    rw [hCLz]
    exact Subgroup.zpowers_le.mpr hzL
  have hDs : DavisSolomonFacts G z (Subgroup.centralizer ({z} : Set G)) E := by
    refine ⟨fun _ hl => hl, ?_, liftSub_le π D.A, hE2, hEcard, ?_, ?_, ?_, ?_,
      hH.toddLift_gen D, hH.toddLift_odd_index D,
      (fun B hB hB2 hcard => hH.toddLift_unique D hB hB2 hcard), ?_⟩
    · rw [hNL]
    · intro τ hτ hτ2 hτF
      exfalso
      apply hτF
      rw [hsup]
      exact hτ
    · intro y hy hy2
      rwa [hsup] at hy
    · intro B hBL hB2 hB
      exact hH.toddLift_conj_class D hBL hB2 hB
    · intro s hs hs2
      exact hH.toddLift_fuse D hs hs2
    · have hsupz : Subgroup.centralizer ({z} : Set G) ⊔ Subgroup.zpowers z =
          Subgroup.centralizer ({z} : Set G) :=
        sup_eq_left.mpr (Subgroup.zpowers_le.mpr hzL)
      rw [hCLz, hsupz]
      exact ((Subgroup.relIndex_eq_one.mpr
        (le_refl (Subgroup.centralizer ({z} : Set G)))).le).trans (by norm_num)
  have hTodd : ToddOrbit.Hyp z (Subgroup.centralizer ({z} : Set G)) E p := by
    refine ⟨hpT46, hpsurj, hpker, hzL, (fun _ hx => hx), hz,
      ?_, hE2, ?_, ?_, ?_, ?_⟩
    · intro g
      rw [hEp]
      exact ToddOrbit.mem_toddLift
    · intro g hg hodd
      exact hg
    · exact fun g hg => hDs.fusion (g := g) hg
    · exact hDs.exists_normalizer_conj_ne hnonab hz
    · rw [hEp]
      exact toddLift_nonsplit hpT46 hpsurj hpker hzL (fun _ hx => hx) hz
  exact ⟨p, E, hpT46, hpsurj, hpker, hEp, hTodd, hDs, hCE⟩

open CFSG.RankThree.GF2n.Parrott

theorem huntM22_of_centralizer
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (hLq : CFSG.IsQuasisimple (Subgroup.centralizer ({z} : Set G)))
    (h2 : Nat.card (Subgroup.center (Subgroup.centralizer ({z} : Set G))) = 2)
    (hQ : CFSG.Blueprint.LieModel
      (Subgroup.centralizer ({z} : Set G) ⧸
        Subgroup.center (Subgroup.centralizer ({z} : Set G))) .PSU 6 2 1) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  obtain ⟨p, E, -, -, -, -, hTodd, hDs, hCE⟩ :=
    davisSolomon_of_quasisimple_centralizer hnonab (L := Subgroup.centralizer ({z} : Set G))
      rfl hz hLq h2 hQ
  have hCLz : Subgroup.centralizer (Subgroup.centralizer ({z} : Set G) : Set G) =
      Subgroup.zpowers z := by
    obtain ⟨-, -, hCLz, -, -⟩ :=
      center_facts_of_selfCentralizing (L := Subgroup.centralizer ({z} : Set G)) rfl hz h2
    exact hCLz
  exact CFSG.EvenSmallLie.UnitarySix.Fischer.fi22_of_davisSolomon hnonab hTodd hDs hCE hCLz

end CFSG.RankThree.GF2n.Parrott
