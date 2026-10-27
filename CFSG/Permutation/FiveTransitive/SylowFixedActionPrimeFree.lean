module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.SylowFixedActionPrimeFree

open MulAction Subgroup
open FiveTransitive.SylowFixedActionCore

theorem base_subset_fixedPoints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ} (S : Sylow p (fixingSubgroup P s)) :
    s ⊆ (sylowFixedPoints X P s S : Set X) := by
  intro x hx
  rw [MulAction.mem_fixedPoints]
  intro z
  obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.prop
  have hfix := (mem_fixingSubgroup_iff P).mp u.prop x hx
  change ((z : sylowNormalizer X P s S) : P) • x = x
  rw [show ((z : sylowNormalizer X P s S) : P) =
    (u : fixingSubgroup P s) by exact hu.symm]
  exact hfix

theorem prime_not_dvd_fixedAction_stabilizer_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s)) :
    let N := sylowNormalizer X P s S
    let F := sylowFixedPoints X P s S
    let J := (MulAction.toPermHom N F).range
    let sF : Set F := {x | (x : X) ∈ s}
    ¬ p ∣ Nat.card (fixingSubgroup J sF) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let rho : N →* Equiv.Perm F := MulAction.toPermHom N F
  let J : Subgroup (Equiv.Perm F) := rho.range
  let sF : Set F := {x | (x : X) ∈ s}
  let K : Subgroup J := fixingSubgroup J sF
  let L : Subgroup H := N.comap H.subtype
  let toN : L →* N :=
    { toFun := fun z ↦ ⟨((z : L) : H), z.prop⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let phi : L →* Equiv.Perm F := rho.comp toN
  have hsF : s ⊆ (F : Set X) := base_subset_fixedPoints X P s S
  have hSL : (S : Subgroup H) ≤ L := by
    intro z hz
    change ((z : H) : P) ∈ N
    exact SP.le_normalizer (Subgroup.mem_map_of_mem H.subtype hz)
  let SL : Sylow p L := S.subtype hSL
  have hSLker : (SL : Subgroup L) ≤ phi.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hzSP : (((z : L) : H) : P) ∈ SP :=
      Subgroup.mem_map_of_mem H.subtype hz
    let zN : N := ⟨(((z : L) : H) : P), SP.le_normalizer hzSP⟩
    let zSN : SN := ⟨zN, hzSP⟩
    exact MulAction.mem_fixedPoints.mp x.prop zSN
  let i : K →* Equiv.Perm F := J.subtype.comp K.subtype
  have hi : Function.Injective i :=
    J.subtype_injective.comp K.subtype_injective
  have hiRange : i.range ≤ phi.range := by
    rintro q ⟨a, rfl⟩
    obtain ⟨n, hn⟩ := a.val.property
    have hnH : ((n : N) : P) ∈ H := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      let xF : F := ⟨x, hsF hx⟩
      have happ := congrArg (fun q : Equiv.Perm F ↦ q xF) hn
      have hiFix : i a xF = xF :=
        (mem_fixingSubgroup_iff J).mp a.property xF hx
      have happ' := congrArg Subtype.val (happ.trans hiFix)
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at happ'
      rw [coe_smul_fixedPoints_of_normal] at happ'
      simpa [rho, xF, Subgroup.smul_def, Equiv.Perm.smul_def] using happ'
    let l : L := ⟨⟨((n : N) : P), hnH⟩, n.prop⟩
    refine ⟨l, ?_⟩
    apply Equiv.ext
    intro x
    have happ := congrArg (fun q : Equiv.Perm F ↦ q x) hn
    simpa [phi, rho, toN, l, i] using happ
  have hcardRange : Nat.card i.range = Nat.card K :=
    Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm
  change ¬ p ∣ Nat.card K
  intro hp
  apply prime_not_dvd_range_card_of_sylow_le_ker SL phi hSLker
  exact hp.trans (by
    rw [← hcardRange]
    exact Subgroup.card_dvd_of_le hiRange)

theorem fixed_degree_modEq
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s)) :
    Nat.card X ≡ Nat.card (sylowFixedPoints X P s S) [MOD p] := by
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  have hSP : IsPGroup p SP := S.isPGroup'.map H.subtype
  let e : SN ≃* SP := Subgroup.subgroupOfEquivOfLe SP.le_normalizer
  have hSN : IsPGroup p SN := hSP.of_injective e.toMonoidHom e.injective
  exact hSN.card_modEq_card_fixedPoints X

theorem base_card_le_fixed_degree
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ} (S : Sylow p (fixingSubgroup P s)) :
    s.ncard ≤ Nat.card (sylowFixedPoints X P s S) := by
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (base_subset_fixedPoints X P s S)

end FiveTransitive.SylowFixedActionPrimeFree

end CFSG
