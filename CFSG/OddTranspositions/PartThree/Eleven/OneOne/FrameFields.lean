module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameLift
import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure
import CFSG.OddTranspositions.PartThree.HalphaCentralizer

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private theorem s11f4a_card_closure_le_comm {X : Type*} [CommGroup X] {ι : Type*}
    (s : Finset ι) (f : ι → X) (hsq : ∀ i ∈ s, f i ^ 2 = 1) :
    Nat.card (Subgroup.closure (f '' (↑s : Set ι))) ≤ 2 ^ s.card := by
  have hset := TauCeti.closure_image_eq_image_powerset s f hsq
  have hmain : ((fun S : Finset ι => ∏ i ∈ S, f i) '' (↑s.powerset : Set (Finset ι))).ncard
      ≤ 2 ^ s.card := by
    calc ((fun S : Finset ι => ∏ i ∈ S, f i) '' (↑s.powerset : Set (Finset ι))).ncard
        ≤ ((↑s.powerset : Set (Finset ι))).ncard := Set.ncard_image_le s.powerset.finite_toSet
      _ = 2 ^ s.card := by rw [Set.ncard_coe_finset, Finset.card_powerset]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset]
  exact hmain

private theorem s11f4a_injOn_of_card_map_eq {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (A : Subgroup X) (hcard : Nat.card (A.map f) = Nat.card A) :
    Set.InjOn f (A : Set X) := by
  let g : A →* Y := f.comp A.subtype
  have hrange : g.range = A.map f := by
    rw [show g = f.comp A.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card g.ker = 1 := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hrange, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (one_mul _).symm)
  have hinj : Function.Injective g := g.ker_eq_bot_iff.mp (Subgroup.eq_bot_of_card_eq g.ker hker)
  intro x hx y hy hxy
  have hxy' : g ⟨x, hx⟩ = g ⟨y, hy⟩ := hxy
  exact Subtype.ext_iff.mp (hinj hxy')

private theorem s11f4a_subtype_image (w : Fin 4 → Halpha D hC.alpha) (i : Fin 4) :
    (Halpha D hC.alpha).subtype '' (Set.range w \ {w i})
      = Set.range (fun j => (w j : G)) \ {(w i : G)} := by
  rw [Set.image_sdiff (Subgroup.subtype_injective (Halpha D hC.alpha)), Set.image_singleton]
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨y, ⟨j, rfl⟩, rfl⟩ := hx1
    exact ⟨⟨j, rfl⟩, by simpa using hx2⟩
  · rintro ⟨⟨j, rfl⟩, hx2⟩
    exact ⟨⟨w j, ⟨j, rfl⟩, rfl⟩, by simpa using hx2⟩

private theorem s11f4a_frameLift_map {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (i : Fin 4) :
    (Subgroup.closure (Set.range w \ {w i})).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      = Subgroup.closure (Set.range r \ {r i}) := by
  classical
  have hw_inj : Function.Injective w := by
    intro j k hjk
    apply hr.injective
    rw [← hwr j, ← hwr k, hjk]
  have hset : (↑(Finset.univ.erase i) : Set (Fin 4)) = Set.univ \ {i} := by
    ext j
    simp [Finset.mem_erase]
  have hw_image : w '' (↑(Finset.univ.erase i) : Set (Fin 4)) = Set.range w \ {w i} := by
    rw [hset, Set.image_sdiff hw_inj, Set.image_univ, Set.image_singleton]
  have hr_image : r '' (↑(Finset.univ.erase i) : Set (Fin 4)) = Set.range r \ {r i} := by
    rw [hset, Set.image_sdiff hr.injective, Set.image_univ, Set.image_singleton]
  have hpi_image : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) ''
      (Set.range w \ {w i}) = Set.range r \ {r i} := by
    rw [← hw_image, Set.image_image]
    rw [show (fun x => (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (w x)) = r
      from funext hwr]
    exact hr_image
  rw [MonoidHom.map_closure, hpi_image]

private theorem s11f4a_frameLift_card {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) (i : Fin 4) :
    Nat.card (Subgroup.closure (Set.range w \ {w i})) = 8 := by
  classical
  have hw_mem : ∀ j, w j ∈ (T : Set (Halpha D hC.alpha)) ∩ DstarH hC := by
    intro j; rw [hw]; exact ⟨j, rfl⟩
  have hw_inj : Function.Injective w := by
    intro j k hjk
    apply hr.injective
    rw [← hwr j, ← hwr k, hjk]
  have hset : (↑(Finset.univ.erase i) : Set (Fin 4)) = Set.univ \ {i} := by
    ext j
    simp [Finset.mem_erase]
  have hw_image : w '' (↑(Finset.univ.erase i) : Set (Fin 4)) = Set.range w \ {w i} := by
    rw [hset, Set.image_sdiff hw_inj, Set.image_univ, Set.image_singleton]
  let k : Set (Halpha D hC.alpha) := Set.range w \ {w i}
  let CH : Subgroup (Halpha D hC.alpha) := Subgroup.closure k
  have hcommk : k.Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨⟨j, rfl⟩, -⟩ := hx
    obtain ⟨⟨l, rfl⟩, -⟩ := hy
    exact (DstarH_isOddTransp hC).commute_of_isPGroup T.isPGroup'
      (hw_mem j).2 (hw_mem l).2 (hw_mem j).1 (hw_mem l).1
  letI : CommGroup CH := Subgroup.closureCommGroupOfComm hcommk
  let f : Fin 4 → CH := fun j => if hj : j = i then 1 else
    ⟨w j, Subgroup.subset_closure ⟨⟨j, rfl⟩, by
      simp only [Set.mem_singleton_iff]
      intro hji; exact hj (hw_inj hji)⟩⟩
  have hf_coe : ∀ j ∈ Finset.univ.erase i, ((f j : CH) : Halpha D hC.alpha) = w j := by
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [f, dif_neg hj.1]
  have hsq : ∀ j ∈ Finset.univ.erase i, f j ^ 2 = 1 := by
    intro j hj
    have hwj := (DstarH_isOddTransp hC).mul_self_eq_one (hw_mem j).2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hf_coe j hj, pow_two]
    exact hwj
  have hk_eq : k = CH.subtype '' (f '' (↑(Finset.univ.erase i) : Set (Fin 4))) := by
    change Set.range w \ {w i} = _
    rw [← hw_image]
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨f j, ⟨j, hj, rfl⟩, hf_coe j hj⟩
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, (hf_coe j hj).symm⟩
  have hupper : Nat.card CH ≤ 8 := by
    have hle := s11f4a_card_closure_le_comm (Finset.univ.erase i) f hsq
    have hcard : (Finset.univ.erase i).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      norm_num
    have hcard_eq : Nat.card CH =
        Nat.card (Subgroup.closure (f '' (↑(Finset.univ.erase i) : Set (Fin 4)))) := by
      change Nat.card (Subgroup.closure k) = _
      rw [hk_eq, ← MonoidHom.map_closure,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective CH)]
    rw [← hcard_eq, hcard] at hle
    norm_num at hle
    exact hle
  have hmap : CH.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      = Subgroup.closure (Set.range r \ {r i}) := by
    change (Subgroup.closure k).map _ = _
    exact s11f4a_frameLift_map hr hwr i
  have hlower : 8 ≤ Nat.card CH := by
    have hdvd := Subgroup.card_map_dvd CH
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
    have h1 : Nat.card (CH.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))))
        ≤ Nat.card CH := Nat.le_of_dvd Nat.card_pos hdvd
    rw [hmap, hr.card_closure i] at h1
    exact h1
  exact le_antisymm hupper hlower

theorem card_closure_frameLift (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) (i : Fin 4) :
    Nat.card (Subgroup.closure (Set.range (fun j => (w j : G)) \ {(w i : G)})) = 8 := by
  have hCH := s11f4a_frameLift_card hr hwr hw i
  have hCG : Subgroup.closure (Set.range (fun j => (w j : G)) \ {(w i : G)})
      = (Subgroup.closure (Set.range w \ {w i})).map (Halpha D hC.alpha).subtype := by
    rw [MonoidHom.map_closure, s11f4a_subtype_image]
  rw [hCG, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hCH]

theorem d_not_mem_closure_frameLift (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) (i : Fin 4) :
    hC.d ∉ Subgroup.closure (Set.range (fun j => (w j : G)) \ {(w i : G)}) := by
  intro hu
  have hCH := s11f4a_frameLift_card hr hwr hw i
  have hmap := s11f4a_frameLift_map hr hwr i
  have hcard_map : Nat.card ((Subgroup.closure (Set.range w \ {w i})).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) =
      Nat.card (Subgroup.closure (Set.range w \ {w i})) := by
    rw [hmap, hCH, hr.card_closure i]
  have hinj := s11f4a_injOn_of_card_map_eq
    (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
    (Subgroup.closure (Set.range w \ {w i})) hcard_map
  have hCG : Subgroup.closure (Set.range (fun j => (w j : G)) \ {(w i : G)})
      = (Subgroup.closure (Set.range w \ {w i})).map (Halpha D hC.alpha).subtype := by
    rw [MonoidHom.map_closure, s11f4a_subtype_image]
  rw [hCG] at hu
  obtain ⟨x, hxCH, hx_eq⟩ := hu
  have hx_central : x ∈ Subgroup.center (Halpha D hC.alpha) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : G) * (x : G) = (x : G) * (y : G)
    have hx_eq' : (x : G) = hC.d := hx_eq
    rw [hx_eq']
    exact Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC y.2)
  have hxM : x ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [h.center]; exact hx_central
  have hpi_x : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hxM
  have hx1 : x = 1 := by
    refine hinj hxCH (Subgroup.one_mem _) ?_
    rw [hpi_x, map_one]
  have hd1 : hC.d = 1 := by
    rw [← hx_eq, hx1]
    exact map_one _
  have hord : orderOf hC.d = 2 := hC.setup.oddT.1 hC.d hC.hd
  rw [hd1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem even_frameLift {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i) :
    ∀ g ∈ Halpha D hC.alpha, ∀ σ : Equiv.Perm (Fin 4),
      (∀ i, g * (w i : G) * g⁻¹ = w (σ i)) → σ ∈ alternatingGroup (Fin 4) := by
  intro g hg σ hconj
  let gH : Halpha D hC.alpha := ⟨g, hg⟩
  have hgH : ∀ i, gH * w i * gH⁻¹ = w (σ i) := by
    intro i
    apply Subtype.ext
    show ((gH * w i * gH⁻¹ : Halpha D hC.alpha) : G) = (w (σ i) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj i
  have hπ : ∀ i, (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) gH * r i *
      ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) gH)⁻¹ = r (σ i) := by
    intro i
    have h1 : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
        (gH * w i * gH⁻¹) = (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
        (w (σ i)) := by rw [hgH i]
    simpa [map_mul, map_inv, hwr i, hwr (σ i)] using h1
  exact hr.even _ σ hπ

theorem alternating_frameLift (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) :
    ∀ σ ∈ alternatingGroup (Fin 4), ∃ g ∈ Halpha D hC.alpha,
      ∀ i, g * (w i : G) * g⁻¹ = w (σ i) := by
  intro σ hσ
  obtain ⟨gbar, hgbar⟩ := hr.alternating σ hσ
  obtain ⟨gH, hgH⟩ := QuotientGroup.mk'_surjective
    (CFSG.solvableRadical (Halpha D hC.alpha)) gbar
  have hw_mem : ∀ j, w j ∈ (T : Set (Halpha D hC.alpha)) ∩ DstarH hC := by
    intro j; rw [hw]; exact ⟨j, rfl⟩
  refine ⟨(gH : G), gH.2, ?_⟩
  intro i
  have hconjH : gH * w i * gH⁻¹ = w (σ i) := by
    refine h.injOn (DstarH_conj_mem hC (h := gH) (x := w i) (hw_mem i).2) (hw_mem (σ i)).2 ?_
    have h1 : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
        (gH * w i * gH⁻¹) = (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
        (w (σ i)) := by
      rw [map_mul, map_mul, map_inv, hgH, hwr i, hgbar i, hwr (σ i)]
    exact h1
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hconjH

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
