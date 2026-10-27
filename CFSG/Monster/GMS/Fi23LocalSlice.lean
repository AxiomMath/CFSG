module

public import CFSG.Monster.GMS.Fi23LocalStar
public import CFSG.Fischer.Uniq.LocalHyperoval
public import CFSG.Sporadic.Fi22.Classes
public import CFSG.Monster.GMS.S342

public section

namespace CFSG.Monster.GMS.Fi23Local

open CFSG.Blueprint.NativeSporadic
open CFSG.Blueprint.Fischer (LocalClass)
open CFSG.Fischer (LocalPoints pairModel pairModel_tv)

section DSet

variable {G : Type} [Group G]

abbrev Gbx (b x : G) : Type :=
  ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))

abbrev Dset (a b x : G) : Set (Gbx b x) := {h | (h : G) ∈ twoANbr a b ∩ twoANbr a x}

theorem coe_mem_localClass {a b x : G} {d f : Gbx b x}
    (hf : f ∈ LocalClass (Dset a b x) d) :
    (f : G) ∈ LocalClass (twoANbr a b ∩ twoANbr a x) (d : G) :=
  ⟨hf.1, fun e => hf.2.1 (Subtype.ext e), congrArg Subtype.val hf.2.2⟩

theorem mem_localClass_of_coe {a b x : G} {d : Gbx b x} (f : Gbx b x)
    (hf : (f : G) ∈ LocalClass (twoANbr a b ∩ twoANbr a x) (d : G)) :
    f ∈ LocalClass (Dset a b x) d :=
  ⟨hf.1, fun e => hf.2.1 (congrArg Subtype.val e), Subtype.ext hf.2.2⟩

end DSet

section Pair

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem orderOf_eq_two_of_mem_dSet
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    {e : Gbx b x} (he : e ∈ Dset a b x) : orderOf e = 2 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_two_of_isConj_a h he.1.1

theorem orderOf_mul_mem_dSet
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {e f : Gbx b x}
    (he : e ∈ Dset a b x) (hf : f ∈ Dset a b x) : orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ) := by
  rw [← Subgroup.orderOf_coe]
  exact threeTransposition I hG hb hx hbx he hf

omit [Finite G] in
theorem conj_mem_dSet {a b x : G} {g e : Gbx b x} (he : e ∈ Dset a b x) :
    g * e * g⁻¹ ∈ Dset a b x :=
  conj_mem_twoANbr_inter (a := a) (x := b) (c := x) g.2 he

theorem exists_conj_of_mem_dSet
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {e f : Gbx b x}
    (he : e ∈ Dset a b x) (hf : f ∈ Dset a b x) : ∃ g : Gbx b x, g * e * g⁻¹ = f := by
  obtain ⟨g, hg, hge⟩ := (s342_three I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
    I.leechPair hG hb hx hbx).1 e he f hf
  exact ⟨⟨g, hg⟩, Subtype.ext hge⟩

end Pair

section Slice

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem babyData
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) {φ : Subgroup.centralizer ({d} : Set G) →* B}
    (hφ : IsBabyCover d φ) :
    BabyInv 0 (coverMap φ b) ∧ BabyInv 0 (coverMap φ x) ∧
      orderOf (coverMap φ b * coverMap φ x) = 3 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hbC : b ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h hb hd.1)
  have hxC : x ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h hx hd.2)
  refine ⟨babyInv_zero_of_mem_twoANbr I hG hd.1.1 hφ (mem_twoANbr_symm h hb hd.1),
    babyInv_zero_of_mem_twoANbr I hG hd.1.1 hφ (mem_twoANbr_symm h hx hd.2), ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← coverMap_mul hbC hxC]
  apply orderOf_eq_prime
  · rw [← coverMap_pow (Subgroup.mul_mem _ hbC hxC) 3, ← hbx, pow_orderOf_eq_one, coverMap_one]
  · intro h1
    rcases (hφ.coverMap_eq_one_iff (Subgroup.mul_mem _ hbC hxC)).mp h1 with h2 | h2
    · rw [h2, orderOf_one] at hbx
      omega
    · rw [h2, orderOf_eq_two_of_isConj_a h hd.1.1] at hbx
      omega

end Slice

section Final

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem localPoints_of_babyFi22Slice
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) {b x : G} (hb : IsConj a b) (hx : IsConj a x)
    (hbx : orderOf (b * x) = 3) :
    ∀ d ∈ Dset a b x,
      Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) (Dset a b x) d) := by
  intro d hd
  have hd' : (d : G) ∈ twoANbr a b ∩ twoANbr a x := hd
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG hd'.1.1).exists_cover
  obtain ⟨hr, hs, hrs⟩ := babyData I hG hb hx hbx hd' hφ
  obtain ⟨⟨χ, hχc, hχt⟩, -⟩ := hS _ _ hr hs hrs
  have hbij := babyStar_bijOn I hG hb hx hbx hd' hφ
  let F : LocalClass (Dset a b x) d → babyStar (coverMap φ b) (coverMap φ x) := fun f =>
    ⟨coverMap φ (f.1 : G), hbij.mapsTo (coe_mem_localClass f.2)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun f g hfg => ?_, fun t => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hbij.injOn (coe_mem_localClass f.2) (coe_mem_localClass g.2) (congrArg Subtype.val hfg)
    · obtain ⟨f, hf, hft⟩ := hbij.surjOn t.2
      have hfH := mem_inf_of_mem h hb hx hf.1
      exact ⟨⟨⟨f, hfH⟩, mem_localClass_of_coe _ hf⟩, Subtype.ext hft⟩
  let e := Equiv.ofBijective F hF
  refine ⟨{ χ := e.trans χ, comm := fun f g => ?_, tau := fun f g hfg => ?_ }⟩
  · have h1 : (f : Gbx b x) * g = g * f ↔ (f : G) * g = g * f := by
      constructor
      · intro e
        exact congrArg Subtype.val e
      · intro e
        exact Subtype.ext e
    rw [h1, commute_iff_coverMap I hG hb hx hbx hd' hφ (coe_mem_localClass f.2)
      (coe_mem_localClass g.2)]
    exact hχc (e f) (e g)
  · have hfC := mem_centralizer_of_mem_localClass (coe_mem_localClass f.2)
    have hgC := mem_centralizer_of_mem_localClass (coe_mem_localClass g.2)
    have hfgf : ((e ⟨(f : Gbx b x) * g * f, hfg⟩ : babyStar (coverMap φ b) (coverMap φ x)) : B) =
        ((e f : babyStar (coverMap φ b) (coverMap φ x)) : B) * (e g) * (e f) :=
      coverMap_mul_mul hfC hgC
    have hmem : ((e f : babyStar (coverMap φ b) (coverMap φ x)) : B) * (e g) * (e f) ∈
        babyStar (coverMap φ b) (coverMap φ x) := by
      rw [← hfgf]
      exact (e ⟨(f : Gbx b x) * g * f, hfg⟩).2
    have heq : e ⟨(f : Gbx b x) * g * f, hfg⟩ = ⟨_, hmem⟩ := Subtype.ext hfgf
    apply Subtype.ext
    rw [pairModel_tv]
    show ((χ (e ⟨(f : Gbx b x) * g * f, hfg⟩) : CFSG.Sporadic.Fi22.D) : CFSG.Sporadic.Fi22.J) = _
    rw [heq]
    exact hχt (e f) (e g) hmem

theorem center_of_babyFi22Slice
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) {b x : G} (hb : IsConj a b) (hx : IsConj a x)
    (hbx : orderOf (b * x) = 3) :
    ∀ d ∈ Dset a b x, ∀ g : Gbx b x,
      (∀ f ∈ insert d (LocalClass (Dset a b x) d), g * f = f * g) → g = 1 ∨ g = d := by
  intro d hd g hg
  have hd' : (d : G) ∈ twoANbr a b ∩ twoANbr a x := hd
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG hd'.1.1).exists_cover
  obtain ⟨hr, hs, hrs⟩ := babyData I hG hb hx hbx hd' hφ
  obtain ⟨-, hcen⟩ := hS _ _ hr hs hrs
  have hbij := babyStar_bijOn I hG hb hx hbx hd' hφ
  have hgd : (g : G) * d = d * g := congrArg Subtype.val (hg d (Set.mem_insert _ _))
  have hgC : (g : G) ∈ Subgroup.centralizer ({(d : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgd
  obtain ⟨hgb, hgx⟩ := Subgroup.mem_inf.mp g.2
  have hbC : b ∈ Subgroup.centralizer ({(d : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h hb hd'.1)
  have hxC : x ∈ Subgroup.centralizer ({(d : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h hx hd'.2)
  have hg1 : coverMap φ (g : G) = 1 := by
    refine hcen _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff, ← coverMap_mul hgC hbC,
        ← coverMap_mul hbC hgC, Subgroup.mem_centralizer_singleton_iff.mp hgb]
    · rw [Subgroup.mem_centralizer_singleton_iff, ← coverMap_mul hgC hxC,
        ← coverMap_mul hxC hgC, Subgroup.mem_centralizer_singleton_iff.mp hgx]
    · intro t ht
      obtain ⟨f, hf, rfl⟩ := hbij.surjOn ht
      have hfH := mem_inf_of_mem h hb hx hf.1
      have hfg : (g : G) * f = f * g :=
        congrArg Subtype.val
          (hg ⟨f, hfH⟩ (Set.mem_insert_of_mem _ (mem_localClass_of_coe _ hf)))
      have hfC := mem_centralizer_of_mem_localClass hf
      rw [← coverMap_mul hgC hfC, ← coverMap_mul hfC hgC, hfg]
  rcases (hφ.coverMap_eq_one_iff hgC).mp hg1 with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem fi23Local_hypotheses
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) {b x : G} (hb : IsConj a b) (hx : IsConj a x)
    (hbx : orderOf (b * x) = 3) :
    (∀ g : Gbx b x, ∀ d ∈ Dset a b x, g * d * g⁻¹ ∈ Dset a b x) ∧
      (∀ d ∈ Dset a b x, ∀ e ∈ Dset a b x, ∃ g : Gbx b x, g * d * g⁻¹ = e) ∧
      (∀ d ∈ Dset a b x, orderOf d = 2) ∧
      (∀ d ∈ Dset a b x, ∀ e ∈ Dset a b x, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∧
      (∀ d ∈ Dset a b x,
        Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) (Dset a b x) d)) ∧
      ∀ d ∈ Dset a b x, ∀ g : Gbx b x,
        (∀ f ∈ insert d (LocalClass (Dset a b x) d), g * f = f * g) → g = 1 ∨ g = d :=
  ⟨fun _ _ hd => conj_mem_dSet hd,
    fun _ hd _ he => exists_conj_of_mem_dSet I hG hb hx hbx hd he,
    fun _ hd => orderOf_eq_two_of_mem_dSet I hG hd,
    fun _ hd _ he => orderOf_mul_mem_dSet I hG hb hx hbx hd he,
    localPoints_of_babyFi22Slice I hG hS hb hx hbx,
    center_of_babyFi22Slice I hG hS hb hx hbx⟩

end Final

end CFSG.Monster.GMS.Fi23Local
