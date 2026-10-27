module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.GroupTheory.SteinbergCEFixedResidual

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.EmbeddingTransport CFSG.LocalCores

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_normal {K N M : Subgroup G} (hKN : K ≤ N)
    (hK : (K.subgroupOf N).Normal) (hN : (N.subgroupOf M).IsSubnormal) :
    (K.subgroupOf M).IsSubnormal := by
  refine Subgroup.IsSubnormal.trans (H := K.subgroupOf M) (K := N.subgroupOf M)
    (fun x hx => hKN hx) ?_ hN
  refine Subgroup.Normal.isSubnormal ⟨fun x hx y => ?_⟩
  have hx' : ((x : ↥M) : G) ∈ K := hx
  have hxN : ((x : ↥M) : G) ∈ N := hKN hx'
  have hyN : ((y : ↥M) : G) ∈ N := y.2
  exact hK.conj_mem ⟨((x : ↥M) : G), hxN⟩ hx' ⟨((y : ↥M) : G), hyN⟩

theorem isSubnormal_kLayer_centralizer {L : Subgroup G} {b c : G}
    (hL : (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).IsSubnormal) :
    ((kLayer L b).subgroupOf
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal := by
  set N := L ⊓ Subgroup.centralizer ({b} : Set G) with hN
  set M := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) with hM
  have hKN : kLayer L b ≤ N := Subgroup.map_subtype_le _
  have hK : ((kLayer L b).subgroupOf N).Normal := by
    have h1 : (kLayer L b).subgroupOf N = CFSG.layer ↥N :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [h1]
    have := layer_characteristic (G := ↥N)
    infer_instance
  have hNM : (N.subgroupOf M).IsSubnormal := by
    have := hL.comap (Subgroup.inclusion (show M ≤ Subgroup.centralizer ({c} : Set G) from
      inf_le_right))
    convert this using 1
    ext m
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion, hN,
      Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, m.2.1⟩⟩
  exact isSubnormal_subgroupOf_of_normal hKN hK hNM

theorem eq_perfectResidual_of_isSubnormal [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hKq : CFSG.IsQuasisimple ↥K) (hsn : (K.subgroupOf H).IsSubnormal)
    (hRq : CFSG.IsQuasisimple ↥(inSubgroup perfectResidual H)) :
    K = inSubgroup perfectResidual H := by
  set R := inSubgroup perfectResidual H with hR
  have hKR : K ≤ R := le_inSubgroup_perfectResidual_of_isPerfect hKH hKq.1
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hK'q : CFSG.IsQuasisimple ↥(K.subgroupOf H) :=
    isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hKq
  have hR'q : CFSG.IsQuasisimple ↥(R.subgroupOf H) :=
    isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRH).symm hRq
  have hR'n : (R.subgroupOf H).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact conj_mem_inSubgroup_perfectResidual g.2 hx⟩
  have hKc : CFSG.IsComponent (K.subgroupOf H) := ⟨hK'q, hsn⟩
  have hRc : CFSG.IsComponent (R.subgroupOf H) := ⟨hR'q, hR'n.isSubnormal⟩
  rcases distinct_components_commute hKc hRc with h | h
  · have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hKH, Subgroup.map_subgroupOf_eq_of_le hRH] at this
  · exfalso
    have hle : K.subgroupOf H ≤ R.subgroupOf H := fun x hx => hKR hx
    have h1 : ⁅K.subgroupOf H, K.subgroupOf H⁆ = ⊥ :=
      le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hle)
    have h2 : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H :=
      Subgroup.isPerfect_iff.mp hK'q.1
    have h3 : K.subgroupOf H = ⊥ := h2.symm.trans h1
    have : Nontrivial ↥(K.subgroupOf H) := isQuasisimple_nontrivial hK'q
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this h3

theorem kLayer_eq_fixedResidual [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) {b : G} {K I : Subgroup G}
    (hL : Layer1212 p A c L E b K I)
    (hRq : CFSG.IsQuasisimple
      ↥(inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G)))) :
    K = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have hLmem : L ∈ thetaComponentsAt p c := ctx.hyp.L_mem.2
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLmem).1
  have hLsn := isSubnormal_of_mem_thetaComponentsAt hLmem
  have hIb : I ≤ Subgroup.centralizer ({b} : Set G) :=
    (mem_thetaComponentsAt_iff.mp hL.I_mem).1
  have hKL : K ≤ L := by
    rw [hL.K_eq]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  set H := I ⊓ Subgroup.centralizer ({c} : Set G) with hH
  have hKH : K ≤ H := fun x hx => ⟨hL.K_le hx, hLc (hKL hx)⟩
  have hHM : H ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) :=
    fun x hx => ⟨hIb hx.1, hx.2⟩
  have hsn : (K.subgroupOf H).IsSubnormal := by
    have h1 := isSubnormal_kLayer_centralizer (b := b) hLsn
    rw [← hL.K_eq] at h1
    have h2 := h1.comap (Subgroup.inclusion hHM)
    convert h2 using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
  exact eq_perfectResidual_of_isSubnormal hKH hL.K_qs hsn hRq

end CFSG.RankThree.PartOne.S12K
