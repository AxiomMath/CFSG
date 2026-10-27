module

public import CFSG.Monster.Tri.ASegFactsBase
public import CFSG.Monster.GMS.Fi23Fusion
public import CFSG.Monster.GMS.S365
public import CFSG.Monster.GMS.S46Basic

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Monster.GMS.S46 CFSG.Blueprint.NativeSporadic
  CFSG.Blueprint.Fischer CFSG.Fischer

section Adjacent

variable {G : Type*} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem isConj_mul_of_commute_dSet (hG : GMSF1Type d₀ a z₀) (hE : EightGroupLines a z₀)
    (hCls : ThreeAInvolutionClasses a z₀) {x y u v : G} (hx : IsConj a x)
    (hy : y ∈ typeSet a z₀ x .threeA) (hu : u ∈ twoANbr a x ∩ twoANbr a y)
    (hv : v ∈ twoANbr a x ∩ twoANbr a y) (huv : u ≠ v) (hc : u * v = v * u) :
    IsConj a (u * v) := by
  have ha : orderOf a = 2 := hG.1.1
  have hnc : ¬ IsConj a z₀ := GMSF1Type.not_isConj hG
  have hyA : IsConj a y := isConj_of_mem_typeSet hy
  have hxx := S36Lines.sq_eq_one_of_isConj ha hx
  have huu := S36Lines.sq_eq_one_of_isConj ha hu.1.1
  have hvv := S36Lines.sq_eq_one_of_isConj ha hv.1.1
  have hxu : x * u = u * x := S36Lines.mul_comm_of_isConj_mul ha hx hu.1.1 hu.1.2
  have hxv : x * v = v * x := S36Lines.mul_comm_of_isConj_mul ha hx hv.1.1 hv.1.2
  have hyu : y * u = u * y := S36Lines.mul_comm_of_isConj_mul ha hyA hu.2.1 hu.2.2
  have hyv : y * v = v * y := S36Lines.mul_comm_of_isConj_mul ha hyA hv.2.1 hv.2.2
  have hxy : x * y ≠ y * x := by
    intro h
    have h3 : orderOf (x * y) = 3 := S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 hy
    have h2 : (x * y) ^ 2 = 1 := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
        _ = x * (x * y) * y := by rw [← h]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hxx, S36Lines.sq_eq_one_of_isConj ha hyA, mul_one]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    omega
  have hl : IsLineTriple a x u := ⟨hx, hu.1.1, hu.1.2⟩
  have he : IsEightExt x u v := by
    refine ⟨hvv, hxv.symm, hc.symm, S36Lines.ne_one_of_isConj ha hv.1.1, ?_, huv.symm, ?_⟩
    · intro e
      refine S36Lines.ne_one_of_isConj ha hv.1.2 ?_
      rw [← e]
      exact hvv
    · intro e
      apply hxy
      have h1 : y * (x * u) = (x * u) * y := by rw [← e]; exact hyv
      have h2 : y * x * u = x * y * u := by
        calc y * x * u = y * (x * u) := mul_assoc _ _ _
          _ = (x * u) * y := h1
          _ = x * (u * y) := mul_assoc _ _ _
          _ = x * (y * u) := by rw [hyu]
          _ = x * y * u := (mul_assoc _ _ _).symm
      exact (mul_right_cancel h2).symm
  have hcount := hE.1 x u v hl he
  have hvA : ¬ IsConj z₀ v := fun h => hnc (hv.1.1.trans h.symm)
  have hvxA : ¬ IsConj z₀ (v * x) := fun h => by
    have : IsConj a (v * x) := by rw [← hxv]; exact hv.1.2
    exact hnc (this.trans h.symm)
  rw [twoBCount_eq_ite, ite_eq_right hvA, ite_eq_right hvxA] at hcount
  by_contra hnot
  have huv1 : u * v ≠ 1 := by
    intro h
    apply huv
    have h' : v = u⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [h', inv_eq_of_mul_eq_one_right huu]
  have huvsq : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← hc]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [huu, hvv, mul_one]
  have hcomm_x : u * v * x = x * (u * v) := by
    calc u * v * x = u * (v * x) := mul_assoc _ _ _
      _ = u * (x * v) := by rw [hxv]
      _ = (u * x) * v := (mul_assoc _ _ _).symm
      _ = (x * u) * v := by rw [hxu]
      _ = x * (u * v) := mul_assoc _ _ _
  have hcomm_y : u * v * y = y * (u * v) := by
    calc u * v * y = u * (v * y) := mul_assoc _ _ _
      _ = u * (y * v) := by rw [hyv]
      _ = (u * y) * v := (mul_assoc _ _ _).symm
      _ = (y * u) * v := by rw [hyu]
      _ = y * (u * v) := mul_assoc _ _ _
  have hJ : u * v ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hcomm_x,
      Subgroup.mem_centralizer_singleton_iff.2 hcomm_y⟩
  have hord : orderOf (u * v) = 2 := orderOf_eq_two_of_mul_self huvsq huv1
  rcases (hCls x y hx hy).1 (u * v) hJ hord with h | h | h
  · exact hnot h.1.1
  · exact hnot h.1.1
  ·
    obtain ⟨⟨hB1, hB2⟩, -⟩ := h
    have h1 : IsConj z₀ (v * u) := by rw [← hc]; exact hB1
    have h2 : IsConj z₀ (v * x * u) := by
      have e : v * x * u = x * (u * v) := by
        calc v * x * u = x * v * u := by rw [← hxv]
          _ = x * (v * u) := mul_assoc _ _ _
          _ = x * (u * v) := by rw [hc]
      rw [e]
      exact hB2
    rw [ite_eq_left h1, ite_eq_left h2] at hcount
    omega

end Adjacent

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem mem_gbx_of_mem {b x w : G} (ha : orderOf a = 2) (hb : IsConj a b) (hx : IsConj a x)
    (hw : w ∈ twoANbr a b ∩ twoANbr a x) :
    w ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (S36Lines.mul_comm_of_isConj_mul ha hb hw.1.1 hw.1.2).symm,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (S36Lines.mul_comm_of_isConj_mul ha hx hw.2.1 hw.2.2).symm⟩

theorem threeACommonNbrs_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) : ThreeACommonNbrs a z₀ := by
  intro x y hy
  have ha : orderOf a = 2 := hG.1.1
  have hyA : IsConj a (y : G) := isConj_of_mem_typeSet hy
  have hord : orderOf ((x : G) * y) = 3 := S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 hy
  obtain ⟨hcls, htr, hinv, hprod, hloc, hZ⟩ :=
    Fi23Local.fi23Local_hypotheses I hG hS x.2 hyA hord
  obtain ⟨d, hd⟩ := commonNbr_threeA_nonempty I hG hS x.2 hy
  have hdH := mem_gbx_of_mem ha x.2 hyA hd
  have hne : (Fi23Local.Dset a (x : G) y).Nonempty := ⟨⟨d, hdH⟩, hd⟩
  obtain ⟨hconn, -, -⟩ := CFSG.Fischer.fi23_of_localPoints_full _ hcls htr hne hinv hprod hloc hZ
  have hCls := threeAInvolutionClasses_of I hG hS
  have hE := eightGroupLines_of I hG
  have hmem : ∀ w : ConjVert a, w ∈ (twoAGraph a).commonNeighbors x y ↔
      (w : G) ∈ twoANbr a (x : G) ∩ twoANbr a (y : G) := by
    intro w
    rw [SimpleGraph.mem_commonNeighbors, S57.adj_iff_mem_twoANbr ha x w,
      S57.adj_iff_mem_twoANbr ha y w]
    rfl
  let f : ↥(Fi23Local.Dset a (x : G) y) → ConjVert a := fun t =>
    ⟨((t : Fi23Local.Gbx (x : G) y) : G), t.2.1.1⟩
  have hf : ∀ t, f t ∈ (twoAGraph a).commonNeighbors x y := fun t => (hmem _).2 t.2
  let ψ : commGraph (Fi23Local.Dset a (x : G) y) →g
      (twoAGraph a).induce ((twoAGraph a).commonNeighbors x y) :=
    { toFun := fun t => ⟨f t, hf t⟩
      map_rel' := by
        intro t t' h
        have hne' : ((t : Fi23Local.Gbx (x : G) y) : G) ≠ ((t' : Fi23Local.Gbx (x : G) y) : G) :=
          fun e => h.1 (Subtype.ext (Subtype.ext e))
        have hc' : ((t : Fi23Local.Gbx (x : G) y) : G) * ((t' : Fi23Local.Gbx (x : G) y) : G) =
            ((t' : Fi23Local.Gbx (x : G) y) : G) * ((t : Fi23Local.Gbx (x : G) y) : G) :=
          congrArg Subtype.val h.2
        show (twoAGraph a).Adj (f t) (f t')
        exact ⟨fun e => hne' (congrArg (fun p : ConjVert a => (p : G)) e),
          isConj_mul_of_commute_dSet hG hE hCls x.2 hy t.2 t'.2 hne' hc'⟩ }
  have hsurj : Function.Surjective ψ := by
    intro w
    have hwD := (hmem _).1 w.2
    exact ⟨⟨⟨(w : ConjVert a), mem_gbx_of_mem ha x.2 hyA hwD⟩, hwD⟩,
      Subtype.ext (Subtype.ext rfl)⟩
  refine ⟨?_, hconn.preconnected.map ψ hsurj⟩
  obtain ⟨L⟩ := hloc ⟨d, hdH⟩ hd
  obtain ⟨f, hfD, hfne, -⟩ := Rec23.exists_mem_localClass_of_localPoints L
  have hfJ := mem_gbx_of_mem ha x.2 hyA hfD
  rw [Nat.succ_le_iff]
  rw [Set.one_lt_ncard_iff (Set.toFinite _)]
  refine ⟨⟨d, hd.1.1⟩, ⟨(f : G), hfD.1.1⟩, (hmem _).2 hd, (hmem _).2 hfD, fun e => hfne ?_⟩
  exact Subtype.ext (congrArg Subtype.val e).symm

end Main

end CFSG.Monster.Tri
