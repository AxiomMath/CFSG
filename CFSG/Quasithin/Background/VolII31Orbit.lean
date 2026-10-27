module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Main

public section

namespace CFSG.Quasithin.VolI.I31

open CFSG.ComponentClassification CFSG.QuasithinUnique CFSG.QuasithinUnique.I32
open scoped commutatorElement

section Fixed

variable {Y : Type*} [Group Y]

theorem commutator_mul_mul_central {a b z w : Y} (hzb : Commute z b) (hwa : Commute w a)
    (hzw : Commute z w) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb.eq]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw.eq, mul_inv_cancel_right]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa.inv_right.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem inv_mul_conj_mem_inf {A B : Subgroup Y} {p a b : Y}
    (hpA : p ∈ Subgroup.normalizer (A : Set Y)) (hpB : p ∈ Subgroup.normalizer (B : Set Y))
    (ha : a ∈ A) (hb : b ∈ B) (hfix : p * (a * b) * p⁻¹ = a * b) :
    a⁻¹ * (p * a * p⁻¹) ∈ A ⊓ B := by
  have hpa : p * a * p⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hpA a).mp ha
  have hpb : p * b * p⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hpB b).mp hb
  have h2 : (p * a * p⁻¹) * (p * b * p⁻¹) = a * b := by
    rw [← hfix]
    group
  have e : a⁻¹ * (p * a * p⁻¹) = b * (p * b * p⁻¹)⁻¹ := by
    calc a⁻¹ * (p * a * p⁻¹) =
          a⁻¹ * ((p * a * p⁻¹) * (p * b * p⁻¹)) * (p * b * p⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * b) * (p * b * p⁻¹)⁻¹ := by rw [h2]
      _ = b * (p * b * p⁻¹)⁻¹ := by group
  exact ⟨A.mul_mem (A.inv_mem ha) hpa, by rw [e]; exact B.mul_mem hb (B.inv_mem hpb)⟩

theorem derived_fixed_conj {A B P : Subgroup Y} (hAB : ⁅A, B⁆ = ⊥)
    (hPA : P ≤ Subgroup.normalizer (A : Set Y)) (hPB : P ≤ Subgroup.normalizer (B : Set Y)) :
    ⁅(A ⊔ B) ⊓ Subgroup.centralizer (P : Set Y), (A ⊔ B) ⊓ Subgroup.centralizer (P : Set Y)⁆ ≤
      (A ⊓ Subgroup.centralizer (P : Set Y)) ⊔ (B ⊓ Subgroup.centralizer (P : Set Y)) := by
  have hAC : A ≤ Subgroup.centralizer (B : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAC ha) b hb).symm
  have hAN : A ≤ Subgroup.normalizer (B : Set Y) :=
    hAC.trans (Subgroup.centralizer_le_normalizer _)
  have hdecomp : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    intro x hx
    have hx' : x ∈ ((A ⊔ B : Subgroup Y) : Set Y) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAN] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, b, hb, hab⟩
  have hfixc : ∀ p ∈ P, ∀ x ∈ Subgroup.centralizer (P : Set Y), p * x * p⁻¹ = x := by
    intro p hp x hx
    rw [Subgroup.mem_centralizer_iff.mp hx p hp, mul_inv_cancel_right]
  have hfixA : ∀ a₁ ∈ A, ∀ b₁ ∈ B, a₁ * b₁ ∈ Subgroup.centralizer (P : Set Y) →
      ∀ a₂ ∈ A, ∀ b₂ ∈ B, a₂ * b₂ ∈ Subgroup.centralizer (P : Set Y) →
        ⁅a₁, a₂⁆ ∈ A ⊓ Subgroup.centralizer (P : Set Y) := by
    intro a₁ ha₁ b₁ hb₁ h₁ a₂ ha₂ b₂ hb₂ h₂
    refine ⟨(Subgroup.commutator_le_self A) (Subgroup.commutator_mem_commutator ha₁ ha₂),
      Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hz₁ := inv_mul_conj_mem_inf (hPA hp) (hPB hp) ha₁ hb₁ (hfixc p hp _ h₁)
    have hz₂ := inv_mul_conj_mem_inf (hPA hp) (hPB hp) ha₂ hb₂ (hfixc p hp _ h₂)
    have e : p * ⁅a₁, a₂⁆ * p⁻¹ =
        ⁅a₁ * (a₁⁻¹ * (p * a₁ * p⁻¹)), a₂ * (a₂⁻¹ * (p * a₂ * p⁻¹))⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 := commutator_mul_mul_central (a := a₁) (b := a₂)
      ((hcomm a₂ ha₂ _ hz₁.2).symm) ((hcomm a₁ ha₁ _ hz₂.2).symm) ((hcomm _ hz₂.1 _ hz₁.2).symm)
    rw [e2] at e
    calc p * ⁅a₁, a₂⁆ = p * ⁅a₁, a₂⁆ * p⁻¹ * p := by group
      _ = ⁅a₁, a₂⁆ * p := by rw [e]
  rw [Subgroup.commutator_le]
  rintro x ⟨hxAB, hxC⟩ y ⟨hyAB, hyC⟩
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdecomp x hxAB
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdecomp y hyAB
  have hBA : ⁅B, A⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, Commute b a := fun b hb a ha => (hcomm a ha b hb).symm
  have hxC' : b₁ * a₁ ∈ Subgroup.centralizer (P : Set Y) := by
    rw [← (hcomm a₁ ha₁ b₁ hb₁).eq]
    exact hxC
  have hyC' : b₂ * a₂ ∈ Subgroup.centralizer (P : Set Y) := by
    rw [← (hcomm a₂ ha₂ b₂ hb₂).eq]
    exact hyC
  have hA := hfixA a₁ ha₁ b₁ hb₁ hxC a₂ ha₂ b₂ hb₂ hyC
  have hB : ⁅b₁, b₂⁆ ∈ B ⊓ Subgroup.centralizer (P : Set Y) := by
    refine ⟨(Subgroup.commutator_le_self B) (Subgroup.commutator_mem_commutator hb₁ hb₂),
      Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hz₁ := inv_mul_conj_mem_inf (hPB hp) (hPA hp) hb₁ ha₁ (hfixc p hp _ hxC')
    have hz₂ := inv_mul_conj_mem_inf (hPB hp) (hPA hp) hb₂ ha₂ (hfixc p hp _ hyC')
    have e : p * ⁅b₁, b₂⁆ * p⁻¹ =
        ⁅b₁ * (b₁⁻¹ * (p * b₁ * p⁻¹)), b₂ * (b₂⁻¹ * (p * b₂ * p⁻¹))⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 := commutator_mul_mul_central (a := b₁) (b := b₂)
      ((hcomm' b₂ hb₂ _ hz₁.2).symm) ((hcomm' b₁ hb₁ _ hz₂.2).symm)
      ((hcomm' _ hz₂.1 _ hz₁.2).symm)
    rw [e2] at e
    calc p * ⁅b₁, b₂⁆ = p * ⁅b₁, b₂⁆ * p⁻¹ * p := by group
      _ = ⁅b₁, b₂⁆ * p := by rw [e]
  have hsplit : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ :=
    FixedCommutingProduct.commutator_mul_mul A B hAB ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩
  rw [hsplit]
  exact Subgroup.mul_mem_sup hA hB

end Fixed

section Orbit

variable {Y : Type*} [Group Y] [Finite Y]

@[expose] def orbitSubP (P K : Subgroup Y) : Subgroup Y := ⨆ p ∈ P, CFSG.conjugate K p

@[expose] def orbitFamilyP (P : Subgroup Y) : Set (Subgroup Y) :=
  {A | ∃ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ ∧ A = orbitSubP P K}

omit [Finite Y] in
theorem conjugate_le_orbitSubP {P K : Subgroup Y} {p : Y} (hp : p ∈ P) :
    CFSG.conjugate K p ≤ orbitSubP P K :=
  le_iSup₂_of_le (f := fun p (_ : p ∈ P) => CFSG.conjugate K p) p hp le_rfl

omit [Finite Y] in
theorem le_orbitSubP (P K : Subgroup Y) : K ≤ orbitSubP P K := by
  have h := conjugate_le_orbitSubP (K := K) (P := P) P.one_mem
  rwa [BenderBranch.conjugate_one] at h

omit [Finite Y] in
theorem orbitSubP_conjugate {P K : Subgroup Y} {g : Y} (hg : g ∈ P) :
    orbitSubP P (CFSG.conjugate K g) = orbitSubP P K := by
  apply le_antisymm
  · refine iSup₂_le fun p hp => ?_
    rw [BenderBranch.conjugate_conjugate]
    exact conjugate_le_orbitSubP (P.mul_mem hg hp)
  · refine iSup₂_le fun p hp => ?_
    have e : CFSG.conjugate K p = CFSG.conjugate (CFSG.conjugate K g) (g⁻¹ * p) := by
      rw [BenderBranch.conjugate_conjugate, mul_inv_cancel_left]
    rw [e]
    exact conjugate_le_orbitSubP (P.mul_mem (P.inv_mem hg) hp)

omit [Finite Y] in
theorem le_normalizer_orbitSubP (P K : Subgroup Y) :
    P ≤ Subgroup.normalizer (orbitSubP P K : Set Y) := by
  intro q hq
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  unfold orbitSubP
  rw [conjugate_iSup]
  apply le_antisymm
  · refine iSup_le fun p => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hp => ?_
    rw [BenderBranch.conjugate_conjugate]
    exact le_iSup₂_of_le (f := fun p (_ : p ∈ P) => CFSG.conjugate K p) (p * q) (P.mul_mem hp hq)
      le_rfl
  · refine iSup₂_le fun p hp => ?_
    have e : CFSG.conjugate K p = CFSG.conjugate (CFSG.conjugate K (p * q⁻¹)) q := by
      rw [BenderBranch.conjugate_conjugate, inv_mul_cancel_right]
    rw [e]
    refine le_iSup_of_le (p * q⁻¹) ?_
    rw [conjugate_iSup]
    exact le_iSup_of_le (P.mul_mem hp (P.inv_mem hq)) le_rfl

omit [Finite Y] in
theorem orbitSubP_le_layer {P K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) :
    orbitSubP P K ≤ Layer.subgroup Y :=
  iSup₂_le fun p _ => Layer.component_le (isComponentOf_conjugate hK p)

omit [Finite Y] in
theorem mem_normalizer_iSup {ι : Sort*} {H : ι → Subgroup Y} {y : Y}
    (h : ∀ i, y ∈ Subgroup.normalizer (H i : Set Y)) :
    y ∈ Subgroup.normalizer ((⨆ i, H i : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.mp (h i)

theorem layer_le_normalizer_orbitSubP {P K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) :
    Layer.subgroup Y ≤ Subgroup.normalizer (orbitSubP P K : Set Y) := fun _ hy =>
  mem_normalizer_iSup fun p => mem_normalizer_iSup fun _ =>
    layer_le_normalizer (isComponentOf_conjugate hK p) hy

omit [Finite Y] in
theorem le_layer_of_mem_orbitFamilyP {P A : Subgroup Y} (hA : A ∈ orbitFamilyP P) :
    A ≤ Layer.subgroup Y := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact orbitSubP_le_layer hK

theorem layer_le_normalizer_of_mem_orbitFamilyP {P A : Subgroup Y} (hA : A ∈ orbitFamilyP P) :
    Layer.subgroup Y ≤ Subgroup.normalizer (A : Set Y) := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact layer_le_normalizer_orbitSubP hK

omit [Finite Y] in
theorem le_normalizer_of_mem_orbitFamilyP {P A : Subgroup Y} (hA : A ∈ orbitFamilyP P) :
    P ≤ Subgroup.normalizer (A : Set Y) := by
  obtain ⟨K, -, rfl⟩ := hA
  exact le_normalizer_orbitSubP P K

theorem isSubnormal_of_mem_orbitFamilyP {P A : Subgroup Y} (hA : A ∈ orbitFamilyP P) :
    CFSG.Open.IsSubnormal A ⊤ :=
  isSubnormal_of_le_layer (le_layer_of_mem_orbitFamilyP hA)
    (layer_le_normalizer_of_mem_orbitFamilyP hA)

theorem isSubnormal_sSup_orbitFamilyP {P : Subgroup Y} {S : Set (Subgroup Y)}
    (hS : S ⊆ orbitFamilyP P) : CFSG.Open.IsSubnormal (sSup S) ⊤ := by
  refine isSubnormal_of_le_layer (sSup_le fun B hB => le_layer_of_mem_orbitFamilyP (hS hB)) ?_
  intro y hy
  rw [sSup_eq_iSup']
  exact mem_normalizer_iSup fun B => layer_le_normalizer_of_mem_orbitFamilyP (hS B.2) hy

theorem commutator_eq_bot_of_ne_orbitP {P A B : Subgroup Y} (hA : A ∈ orbitFamilyP P)
    (hB : B ∈ orbitFamilyP P) (hne : A ≠ B) : ⁅A, B⁆ = ⊥ := by
  obtain ⟨K, hK, rfl⟩ := hA
  obtain ⟨K', hK', rfl⟩ := hB
  have hpair : ∀ p ∈ P, ∀ p' ∈ P, ⁅CFSG.conjugate K p, CFSG.conjugate K' p'⁆ = ⊥ := by
    intro p hp p' hp'
    refine commute_of_ne_component (isComponentOf_conjugate hK p)
      (isComponentOf_conjugate hK' p') fun h => hne ?_
    have hK'eq : K' = CFSG.conjugate K (p * p'⁻¹) := by
      have := congrArg (fun S => CFSG.conjugate S p'⁻¹) h
      simp only [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one]
        at this
      exact this.symm
    rw [hK'eq, orbitSubP_conjugate (P.mul_mem hp (P.inv_mem hp'))]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun p hp => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun p' hp' => ?_
  rw [← Subgroup.le_centralizer_iff]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hpair p hp p' hp')

omit [Finite Y] in
theorem layer_le_sSup_orbitFamilyP (P : Subgroup Y) : Layer.subgroup Y ≤ sSup (orbitFamilyP P) :=
  sSup_le fun K hK => (le_orbitSubP P K).trans (le_sSup ⟨K, hK, rfl⟩)

theorem exists_orbitSubP_le {P C : Subgroup Y} (hC : C = Subgroup.centralizer (P : Set Y))
    {Lc : Subgroup C} (hLc : TwoComponents.IsTwoComponent Lc) :
    ∀ S : Set (Subgroup Y), S.Finite → S ⊆ orbitFamilyP P →
      Lc.map C.subtype ≤ sSup S → ∃ A ∈ S, Lc.map C.subtype ≤ A := by
  classical
  have : Group.IsPerfect Lc := ⟨TwoComponents.perfect hLc⟩
  have : Group.IsPerfect (Lc.map C.subtype) := Group.IsPerfect.map C.subtype
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _ hle
    exfalso
    rw [sSup_empty, le_bot_iff] at hle
    have hLcBot : Lc = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective Lc C.subtype_injective).mp hle
    have : Nontrivial Lc := TwoComponents.nontrivial hLc
    exact (Lc.nontrivial_iff_ne_bot.mp inferInstance) hLcBot
  | @insert A S' hAS' hS'fin ih =>
    intro hsub hle
    have hA : A ∈ orbitFamilyP P := hsub (Set.mem_insert A S')
    have hS'sub : S' ⊆ orbitFamilyP P := fun B hB => hsub (Set.mem_insert_of_mem A hB)
    have hcomm : ⁅A, sSup S'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      refine sSup_le fun B hB => ?_
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_ne_orbitP (hS'sub hB) hA (fun h => hAS' (h ▸ hB)))
    have hPA : P ≤ Subgroup.normalizer (A : Set Y) := le_normalizer_of_mem_orbitFamilyP hA
    have hPT : P ≤ Subgroup.normalizer ((sSup S' : Subgroup Y) : Set Y) := by
      intro q hq
      rw [sSup_eq_iSup']
      exact mem_normalizer_iSup fun B => le_normalizer_of_mem_orbitFamilyP (hS'sub B.2) hq
    have hderived := derived_fixed_conj hcomm hPA hPT
    rw [← hC] at hderived
    have hle' : Lc.map C.subtype ≤ A ⊔ sSup S' := by rwa [sSup_insert] at hle
    have hle'' : Lc.map C.subtype ≤ (A ⊔ sSup S') ⊓ C := le_inf hle' (Subgroup.map_subtype_le Lc)
    have hprod : Lc.map C.subtype ≤ (A ⊓ C) ⊔ (sSup S' ⊓ C) :=
      calc Lc.map C.subtype = ⁅Lc.map C.subtype, Lc.map C.subtype⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ ⁅(A ⊔ sSup S') ⊓ C, (A ⊔ sSup S') ⊓ C⁆ := Subgroup.commutator_mono hle'' hle''
        _ ≤ (A ⊓ C) ⊔ (sSup S' ⊓ C) := hderived
    have hlocal : Lc ≤ A.subgroupOf C ⊔ (sSup S').subgroupOf C := by
      have hmap : Lc.map C.subtype ≤
          (A.subgroupOf C ⊔ (sSup S').subgroupOf C).map C.subtype := by
        rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        exact hprod
      have hcomap := Subgroup.map_le_iff_le_comap.mp hmap
      rwa [Subgroup.comap_map_eq_self_of_injective C.subtype_injective] at hcomap
    have hasub : CFSG.Open.IsSubnormal (A.subgroupOf C) ⊤ :=
      Components.chain_of_mathlib_subnormal
        ((Components.mathlib_subnormal_of_chain (isSubnormal_of_mem_orbitFamilyP hA)
          Subgroup.IsSubnormal.top).subgroupOf)
    have hTlocalsub : CFSG.Open.IsSubnormal ((sSup S').subgroupOf C) ⊤ :=
      Components.chain_of_mathlib_subnormal
        ((Components.mathlib_subnormal_of_chain (isSubnormal_sSup_orbitFamilyP hS'sub)
          Subgroup.IsSubnormal.top).subgroupOf)
    have hpairJoin : sSup ({A.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)) =
        A.subgroupOf C ⊔ (sSup S').subgroupOf C := by simp
    have hpairSub : ∀ s' ∈ ({A.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)),
        CFSG.Open.IsSubnormal s' ⊤ := by
      intro s' hs'
      rcases Set.mem_insert_iff.mp hs' with rfl | hs'
      · exact hasub
      · rw [Set.mem_singleton_iff.mp hs']
        exact hTlocalsub
    obtain ⟨cont, hcont, hcontle⟩ := TwoComponentJoins.exists_le_of_le_sSup Lc hLc
      ({A.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)) hpairSub
      (by rwa [hpairJoin])
    rcases Set.mem_insert_iff.mp hcont with rfl | hcont
    · refine ⟨A, Set.mem_insert A S', ?_⟩
      calc Lc.map C.subtype ≤ (A.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
        _ = A ⊓ C := Subgroup.subgroupOf_map_subtype A C
        _ ≤ A := inf_le_left
    · rw [Set.mem_singleton_iff.mp hcont] at hcontle
      have hT : Lc.map C.subtype ≤ sSup S' :=
        calc Lc.map C.subtype ≤ ((sSup S').subgroupOf C).map C.subtype :=
              Subgroup.map_mono hcontle
          _ = sSup S' ⊓ C := Subgroup.subgroupOf_map_subtype _ C
          _ ≤ sSup S' := inf_le_left
      obtain ⟨B, hB, hBle⟩ := ih hS'sub hT
      exact ⟨B, Set.mem_insert_of_mem A hB, hBle⟩

theorem exists_component_orbitP_le {P C : Subgroup Y} (hC : C = Subgroup.centralizer (P : Set Y))
    {Lc : Subgroup C} (hLc : TwoComponents.IsTwoComponent Lc)
    (hle : Lc.map C.subtype ≤ Layer.subgroup Y) :
    ∃ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ ∧ Lc.map C.subtype ≤ orbitSubP P K := by
  obtain ⟨A, hA, hLA⟩ := exists_orbitSubP_le hC hLc (orbitFamilyP P) (Set.toFinite _) subset_rfl
    (hle.trans (layer_le_sSup_orbitFamilyP P))
  obtain ⟨K, hK, rfl⟩ := hA
  exact ⟨K, hK, hLA⟩

theorem normalClosure_layer_eqP {P Kb Lb : Subgroup Y} (hK : CFSG.Open.IsComponentOf Kb ⊤)
    (hLperf : ⁅Lb, Lb⁆ = Lb) (hLne : Lb ≠ ⊥)
    (hLfix : Lb ≤ Subgroup.centralizer (P : Set Y)) (hLA : Lb ≤ orbitSubP P Kb) :
    (⨆ y ∈ Layer.subgroup Y, CFSG.conjugate Lb y) = orbitSubP P Kb := by
  set M : Subgroup Y := ⨆ y ∈ Layer.subgroup Y, CFSG.conjugate Lb y with hM
  have hPC : P ≤ Subgroup.centralizer (Lb : Set Y) := Subgroup.le_centralizer_iff.mp hLfix
  have hfix : ∀ p ∈ P, CFSG.conjugate Lb p = Lb := fun p hp =>
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.centralizer_le_normalizer _ (hPC hp))
  have hLM : Lb ≤ M := by
    have : Lb = CFSG.conjugate Lb 1 := (BenderBranch.conjugate_one Lb).symm
    rw [this]
    exact le_iSup₂_of_le (1 : Y) (Subgroup.one_mem _) le_rfl
  have hMA : M ≤ orbitSubP P Kb :=
    iSup₂_le fun y hy => conjugate_le_of_mem_normalizer hLA (layer_le_normalizer_orbitSubP hK hy)
  refine le_antisymm hMA ?_
  have hMlayer : M ≤ Layer.subgroup Y := hMA.trans (orbitSubP_le_layer hK)
  have hMconj : ∀ z ∈ Layer.subgroup Y, CFSG.conjugate M z ≤ M := by
    intro z hz
    rw [hM, conjugate_iSup]
    refine iSup_le fun y => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hy => ?_
    rw [BenderBranch.conjugate_conjugate]
    exact le_iSup₂_of_le (y * z) (Subgroup.mul_mem _ hy hz) le_rfl
  have hMsub : CFSG.Open.IsSubnormal M ⊤ :=
    isSubnormal_of_le_layer hMlayer (le_normalizer_of_conjugate_le hMconj)
  have hMP : ∀ p ∈ P, CFSG.conjugate M p ≤ M := by
    intro p hp
    rw [hM, conjugate_iSup]
    refine iSup_le fun y => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hy => ?_
    rw [BenderBranch.conjugate_conjugate]
    have e : CFSG.conjugate Lb (y * p) = CFSG.conjugate Lb (p * (p⁻¹ * y * p)) := by
      congr 1
      group
    rw [e, ← BenderBranch.conjugate_conjugate, hfix p hp]
    refine le_iSup₂_of_le (p⁻¹ * y * p) ?_ le_rfl
    have := (Layer.normal Y).conj_mem y hy p⁻¹
    simpa using this
  have hKM : Kb ≤ M := by
    rcases LocalComponents.subnormal_contains_or_commutes Kb M hK hMsub with hle | hcomm
    · exact hle
    · exfalso
      have h1 : ⁅Lb, Kb⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono le_rfl hLM)
      have h2 : ∀ p ∈ P, ⁅Lb, CFSG.conjugate Kb p⁆ = ⊥ := by
        intro p hp
        have e : ⁅Lb, CFSG.conjugate Kb p⁆ = CFSG.conjugate ⁅Lb, Kb⁆ p := by
          conv_lhs => rw [← hfix p hp]
          unfold CFSG.conjugate
          rw [Subgroup.map_commutator]
        rw [e, h1]
        unfold CFSG.conjugate
        exact Subgroup.map_bot _
      have h3 : ⁅Lb, orbitSubP P Kb⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
        refine iSup₂_le fun p hp => ?_
        rw [← Subgroup.le_centralizer_iff]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h2 p hp)
      have h4 : Lb = ⊥ := by
        rw [← hLperf]
        exact le_bot_iff.mp (h3 ▸ Subgroup.commutator_mono le_rfl hLA)
      exact hLne h4
  exact iSup₂_le fun p hp => (BenderBranch.conjugate_mono hKM p).trans (hMP p hp)

end Orbit

end CFSG.Quasithin.VolI.I31
