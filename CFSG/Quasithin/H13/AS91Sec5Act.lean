module

public import CFSG.Quasithin.H13.AS91Sec8Pt
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.AS91

open MulAction

variable {G : Type*} [Group G]

private theorem smul_basePt_eq_iff {A : Subgroup G} (h : G) :
    h • basePt A = basePt A ↔ h ∈ A := by
  show h • ((1 : G) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ h ∈ A
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  simp

theorem smul_mem_objOf_base {A B : Subgroup G} {g : G} (hg : g ∈ B) {p : G ⧸ A}
    (hp : p ∈ objOf A B (basePt B)) : g • p ∈ objOf A B (basePt B) := by
  have hgb : g • basePt B = basePt B := by
    show g • ((1 : G) : G ⧸ B) = ((1 : G) : G ⧸ B)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    simpa using hg
  have h := (cInc_smul A B g p (basePt B)).mpr (mem_objOf.mp hp)
  rw [hgb] at h
  exact mem_objOf.mpr h

theorem basePt_mem_objOf_base (A B : Subgroup G) : basePt A ∈ objOf A B (basePt B) :=
  cInc_mk A B 1

noncomputable def residuePerm (A B : Subgroup G) :
    ↥B →* Equiv.Perm ↥(objOf A B (basePt B)) where
  toFun g :=
    { toFun := fun p => ⟨(g : G) • (p : G ⧸ A), smul_mem_objOf_base g.2 p.2⟩
      invFun := fun p => ⟨(g : G)⁻¹ • (p : G ⧸ A), smul_mem_objOf_base (inv_mem g.2) p.2⟩
      left_inv := fun p => Subtype.ext (inv_smul_smul (g : G) (p : G ⧸ A))
      right_inv := fun p => Subtype.ext (smul_inv_smul (g : G) (p : G ⧸ A)) }
  map_one' := Equiv.ext fun p => Subtype.ext (by simp)
  map_mul' := fun g h => Equiv.ext fun p => Subtype.ext (by simp [mul_smul])

theorem residuePerm_apply (A B : Subgroup G) (g : ↥B) (p : ↥(objOf A B (basePt B))) :
    ((residuePerm A B g p : ↥(objOf A B (basePt B))) : G ⧸ A) = (g : G) • (p : G ⧸ A) := by
  simp [residuePerm]

theorem exists_mem_smul_eq_perm [Finite G] (A B S N : Subgroup G) (hSB : S ≤ B) {n : ℕ}
    (hcard : Nat.card (objOf A B (basePt B)) = n)
    (hker : ∀ g ∈ S, (∀ p ∈ objOf A B (basePt B), g • p = p) → g ∈ N)
    (hidx : (N.subgroupOf S).index = n.factorial)
    (σ : Equiv.Perm ↥(objOf A B (basePt B))) :
    ∃ s ∈ S, ∀ p : ↥(objOf A B (basePt B)),
      s • (p : G ⧸ A) = ((σ p : ↥(objOf A B (basePt B))) : G ⧸ A) := by
  let ρ : ↥S →* Equiv.Perm ↥(objOf A B (basePt B)) :=
    (residuePerm A B).comp (Subgroup.inclusion hSB)
  have hρ : ∀ (s : ↥S) (p : ↥(objOf A B (basePt B))),
      ((ρ s p : ↥(objOf A B (basePt B))) : G ⧸ A) = (s : G) • (p : G ⧸ A) :=
    fun s p => residuePerm_apply A B (Subgroup.inclusion hSB s) p
  have hle : ρ.ker ≤ N.subgroupOf S := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    rw [Subgroup.mem_subgroupOf]
    refine hker (s : G) s.2 fun p hp => ?_
    have h2 : ρ s ⟨p, hp⟩ = ⟨p, hp⟩ := by
      rw [hs, Equiv.Perm.one_apply]
    have h1 := hρ s ⟨p, hp⟩
    rw [h2] at h1
    exact h1.symm
  have hdvd1 : (N.subgroupOf S).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker, hidx] at hdvd1
  have hdvd2 : Nat.card ρ.range ∣ Nat.card (Equiv.Perm ↥(objOf A B (basePt B))) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  have hperm : Nat.card (Equiv.Perm ↥(objOf A B (basePt B))) = n.factorial := by
    rw [Nat.card_perm, hcard]
  have heq : Nat.card ρ.range = Nat.card (Equiv.Perm ↥(objOf A B (basePt B))) := by
    apply Nat.dvd_antisymm hdvd2
    rw [hperm]
    exact hdvd1
  have htop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq ρ.range heq
  have hσ : σ ∈ ρ.range := by
    rw [htop]
    exact Subgroup.mem_top σ
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hσ
  refine ⟨(s : G), s.2, fun p => ?_⟩
  rw [← hs]
  exact (hρ s p).symm

private theorem exists_perm_pair {α : Type*} [DecidableEq α] {a b a' b' : α} (hab : a ≠ b)
    (hab' : a' ≠ b') : ∃ σ : Equiv.Perm α, σ a = a' ∧ σ b = b' := by
  have hac : a' ≠ Equiv.swap a a' b := by
    have h := (Equiv.swap a a').injective.ne hab
    rwa [Equiv.swap_apply_left] at h
  refine ⟨(Equiv.swap a a').trans (Equiv.swap (Equiv.swap a a' b) b'), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hac hab'
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem exists_mem_smul_pair [Finite G] (A B S N : Subgroup G) (hSB : S ≤ B) {n : ℕ}
    (hcard : Nat.card (objOf A B (basePt B)) = n)
    (hker : ∀ g ∈ S, (∀ p ∈ objOf A B (basePt B), g • p = p) → g ∈ N)
    (hidx : (N.subgroupOf S).index = n.factorial)
    {a b a' b' : G ⧸ A} (ha : a ∈ objOf A B (basePt B)) (hb : b ∈ objOf A B (basePt B))
    (ha' : a' ∈ objOf A B (basePt B)) (hb' : b' ∈ objOf A B (basePt B)) (hab : a ≠ b)
    (hab' : a' ≠ b') : ∃ s ∈ S, s • a = a' ∧ s • b = b' := by
  classical
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_pair (a := (⟨a, ha⟩ : ↥(objOf A B (basePt B))))
    (b := ⟨b, hb⟩) (a' := ⟨a', ha'⟩) (b' := ⟨b', hb'⟩)
    (fun h => hab (congrArg Subtype.val h)) (fun h => hab' (congrArg Subtype.val h))
  obtain ⟨s, hs, hsp⟩ := exists_mem_smul_eq_perm A B S N hSB hcard hker hidx σ
  exact ⟨s, hs, (hsp ⟨a, ha⟩).trans (congrArg Subtype.val hσa),
    (hsp ⟨b, hb⟩).trans (congrArg Subtype.val hσb)⟩

theorem gamma5_of_transitive (A B C E : Subgroup G) (hE : E ≤ A ⊓ B ⊓ C)
    (htr : ∀ y y' : G ⧸ A, y ∈ objOf A B (basePt B) → y' ∈ objOf A B (basePt B) →
      y ≠ basePt A → y' ≠ basePt A → ∃ e ∈ E, e • y = y')
    {y : G ⧸ A} (hy : y ∈ objOf A B (basePt B)) (hyx : y ≠ basePt A) :
    A ⊓ B ≤ A ⊓ B ⊓ stabilizer G y ⊔ A ⊓ B ⊓ C := by
  intro g hg
  obtain ⟨hgA, hgB⟩ := Subgroup.mem_inf.mp hg
  have hgx : g • basePt A = basePt A := (smul_basePt_eq_iff g).mpr hgA
  have hgy : g • y ∈ objOf A B (basePt B) := smul_mem_objOf_base hgB hy
  have hgyx : g • y ≠ basePt A := by
    intro h
    apply hyx
    apply smul_left_cancel g
    rw [h, hgx]
  obtain ⟨e, he, hey⟩ := htr y (g • y) hy hgy hyx hgyx
  have heA : e ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hE he)).1).1
  have heB : e ∈ B := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hE he)).1).2
  have hh : (e⁻¹ * g) • y = y := by
    rw [mul_smul, ← hey, inv_smul_smul]
  have hmem : e⁻¹ * g ∈ A ⊓ B ⊓ stabilizer G y :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem heA) hgA,
      mul_mem (inv_mem heB) hgB⟩, mem_stabilizer_iff.mpr hh⟩
  have key : e * (e⁻¹ * g) ∈ (A ⊓ B ⊓ stabilizer G y) ⊔ (A ⊓ B ⊓ C) :=
    mul_mem (Subgroup.mem_sup_right (hE he)) (Subgroup.mem_sup_left hmem)
  rwa [mul_inv_cancel_left] at key

end CFSG.Quasithin.H13.AS91
