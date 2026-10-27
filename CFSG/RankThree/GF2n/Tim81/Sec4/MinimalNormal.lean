module

public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjRep
public import CFSG.RankThree.GF2n.Tim81.Sec4.QEqP
public import CFSG.RankThree.GF2n.Tim81.Sec4.Inputs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem xOf_inf_centralizer_Pc_eq_V (h : RootHyp M V) :
    Tim79a.xOf V H ⊓ Subgroup.centralizer (Pc M V : Set G) = V := by
  rw [h.toHyp.centralizer_Pc]
  exact inf_eq_right.mpr (le_xOf_self V H)

theorem mem_M_and_mem_normalizer_inf_of_mem_normalizer_imgK (h : RootHyp M V)
    (hPH : Pc M V ≤ H) {z : ↥H}
    (hz : piK V H z ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))) :
    (z : G) ∈ M ∧ (z : G) ∈ Subgroup.normalizer (Pc M V ⊓ kOf V H : Set G) := by
  have hcomap : (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).comap (piK V H) =
      Subgroup.normalizer (((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H :
        Subgroup ↥H) : Set ↥H) := by
    rw [imgK, Subgroup.comap_normalizer_eq_of_le_range
      (Subgroup.map_le_range (piK V H) ((Pc M V).subgroupOf H))]
    rw [Subgroup.comap_map_eq (piK V H) ((Pc M V).subgroupOf H)]
    have hker : (piK V H).ker = (kOf V H).subgroupOf H := by
      simpa [piK] using (QuotientGroup.ker_mk' ((kOf V H).subgroupOf H))
    rw [hker]
  have hz' : z ∈ (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).comap
      (piK V H) := Subgroup.mem_comap.mpr hz
  rw [hcomap] at hz'
  have hzG : (z : G) ∈ Subgroup.normalizer
      ((((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H : Subgroup ↥H).map
        H.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map H.subtype ⟨z, hz', rfl⟩
  have hmap : (((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H : Subgroup ↥H).map
      H.subtype) = Pc M V ⊔ kOf V H := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPH,
      Subgroup.map_subgroupOf_eq_of_le (kOf_le V H)]
  rw [hmap] at hzG
  have hV_cent_P : V ≤ Subgroup.centralizer (Pc M V : Set G) :=
    (Subgroup.le_centralizer_iff).mpr inf_le_right
  have hK_cent_V : kOf V H ≤ Subgroup.centralizer (V : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 v (le_xOf_self V H hv)
  have hV_cent_K : V ≤ Subgroup.centralizer (kOf V H : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hK_cent_V
  have hV_eq : V = Tim79a.xOf V H ⊓
      Subgroup.centralizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by
    refine le_antisymm (le_inf (le_xOf_self V H) ?_) ?_
    · exact (Subgroup.le_centralizer_iff).mpr (sup_le inf_le_right hK_cent_V)
    · intro x hx
      have hle : Subgroup.centralizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) ≤
          Subgroup.centralizer (Pc M V : Set G) :=
        Subgroup.centralizer_le fun y hy => Subgroup.mem_sup_left hy
      have hx' : x ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (Pc M V : Set G) :=
        ⟨hx.1, hle hx.2⟩
      rwa [xOf_inf_centralizer_Pc_eq_V h] at hx'
  have hzV : (z : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [hV_eq]
    exact mem_normalizer_inf (Tim79a.H_le_normalizer_xOf V H z.2)
      (mem_normalizer_centralizer hzG)
  have hzM : (z : G) ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact hzV
  exact ⟨hzM, mem_normalizer_inf (h.toHyp.le_normalizer_Pc hzM) (le_normalizer_kOf V H z.2)⟩

@[expose] def TransitiveFixed (hPH : Pc M V ≤ H) (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {X : Type} [Group X] (ψ : HBar V H ≃* X)
    (hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))) : Prop :=
  letI := hmod
  ∀ v ∈ fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ),
    ∀ w ∈ fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ), v ≠ 0 → w ≠ 0 →
      ∃ n ∈ Subgroup.normalizer (((imgK V H (Pc M V)).map ψ : Subgroup X) : Set X),
        repW hW ψ n v = w

theorem eq_bot_or_eq_of_transitiveFixed (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {X : Type} [Group X] (ψ : HBar V H ≃* X)
    (hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)))
    (htrans : TransitiveFixed (V := V) (H := H) hPH hW ψ hmod) :
    MinimalInvariant M V := by
  letI := hmod
  intro U hUV hUN
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · right
    obtain ⟨⟨u, huU⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have hu1 : u ≠ 1 := fun h1 => hu1' (Subtype.ext h1)
    have huV : u ∈ V := hUV huU
    have huW : u ∈ Tim79a.xOf V H := le_xOf_self V H huV
    let uW : ↥(Tim79a.xOf V H) := ⟨u, huW⟩
    have huW1 : uW ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
    have hofu_ne : ofW hW uW ≠ 0 := by
      intro h0
      have h1 : toW hW (ofW hW uW) = toW hW 0 := congrArg (toW hW) h0
      rw [toW_ofW, toW_zero] at h1
      exact huW1 h1
    have hfixu : ofW hW uW ∈ fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ) := by
      rw [fixedSub_repW hW ψ hPH, mem_subW_iff, xOf_inf_centralizer_Pc_eq_V h]
      exact huV
    refine le_antisymm hUV ?_
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact U.one_mem
    · have hvW : v ∈ Tim79a.xOf V H := le_xOf_self V H hv
      let vW : ↥(Tim79a.xOf V H) := ⟨v, hvW⟩
      have hvW1 : vW ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
      have hofv_ne : ofW hW vW ≠ 0 := by
        intro h0
        have h1 : toW hW (ofW hW vW) = toW hW 0 := congrArg (toW hW) h0
        rw [toW_ofW, toW_zero] at h1
        exact hvW1 h1
      have hfixv : ofW hW vW ∈ fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ) := by
        rw [fixedSub_repW hW ψ hPH, mem_subW_iff, xOf_inf_centralizer_Pc_eq_V h]
        exact hv
      obtain ⟨n, hn, hnv⟩ := htrans _ hfixu _ hfixv hofu_ne hofv_ne
      have hn' : ψ.symm n ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
        have hmapN : (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).map
            ψ.toMonoidHom =
            Subgroup.normalizer (((imgK V H (Pc M V)).map ψ.toMonoidHom : Subgroup X) : Set X) :=
          Subgroup.map_normalizer_eq_of_bijective (imgK V H (Pc M V)) ψ.bijective
        have hnmap : n ∈ (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).map
            ψ.toMonoidHom := by
          rw [hmapN]
          exact hn
        obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hnmap
        have hsymm : ψ.symm n = m := by
          rw [← hmn]
          simpa using (MulEquiv.symm_apply_apply ψ m)
        rwa [hsymm]
      obtain ⟨z, hz⟩ := piK_surjective V H (ψ.symm n)
      have hzN : piK V H z ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
        rw [hz]
        exact hn'
      obtain ⟨hzM, -⟩ := mem_M_and_mem_normalizer_inf_of_mem_normalizer_imgK h hPH hzN
      have hzu : (z : G) * u * (z : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hUN hzM) u).mp huU
      have hpsi : ψ (piK V H z) = n := by
        rw [hz, MulEquiv.apply_symm_apply]
      have hrep : repW hW ψ n (ofW hW uW) = ofW hW (conjH V H z uW) := by
        rw [← hpsi, repW_apply_piK, toW_ofW]
      have hveq : ofW hW vW = ofW hW (conjH V H z uW) := by
        rw [← hnv, hrep]
      have hv_eq : v = (z : G) * u * (z : G)⁻¹ := by
        have h1 : vW = conjH V H z uW := congrArg (toW hW) hveq
        have h2 : (vW : G) = ((conjH V H z uW : ↥(Tim79a.xOf V H)) : G) :=
          congrArg Subtype.val h1
        rw [conjH_apply_coe] at h2
        exact h2
      rwa [hv_eq]

theorem pCore_eq_Pc_and_of_transitiveFixed (h : RootHyp M V)
    {H : Subgroup G} (hHmem : IsHMember M V H)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {X : Type} [Group X] (ψ : HBar V H ≃* X)
    (hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)))
    (htrans : TransitiveFixed (V := V) (H := H) hHmem.2.1 hW ψ hmod) :
    inSubgroup (pCore 2) M = Pc M V ∧
      inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V ∧
      inSubgroup frattini (inSubgroup (pCore 2) M) = V ∧
      inSubgroup commutator (inSubgroup (pCore 2) M) = V :=
  RootHyp.pCore_eq_Pc_and h
    (eq_bot_or_eq_of_transitiveFixed h hHmem.2.1 hW ψ hmod htrans)

end RootHyp

end CFSG.RankThree.GF2n.Tim81
