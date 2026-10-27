module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLines
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDef

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

section Config

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem map_conjNormal_subgroupOf {B : Subgroup A} [L.Normal] {t : A}
    (ht : t ∈ Subgroup.normalizer (B : Set A)) :
    (B.subgroupOf L).map (MulAut.conjNormal t).toMonoidHom = B.subgroupOf L := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h : (((MulAut.conjNormal t).symm x : L) : A) = t⁻¹ * x * t := by
    have : (MulAut.conjNormal t).symm x = MulAut.conjNormal t⁻¹ x := by
      rw [map_inv]
      rfl
    rw [this, MulAut.conjNormal_apply, inv_inv]
  rw [h]
  exact ((Subgroup.mem_normalizer_iff''.1 ht) x).symm

theorem commutator_eq_bot_of_comm {B : Subgroup A} (h : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ⁅B, B⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 (h a ha b hb)

theorem false_of_torusProp [Fact p.Prime] (h : OddCfg p L P T)
    (hX : PTorusProp p ↥L) : False := by
  have hLn := h.normal
  have hPL := h.le
  have hexp : ∀ x ∈ P.subgroupOf L, x ^ p = 1 := fun x hx =>
    Subtype.ext (by simpa using h.exp x (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨hab, hodd⟩ := hX (P.subgroupOf L) hexp
  have hab' : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => by
    have := hab ⟨a, hPL ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨b, hPL hb⟩
      (Subgroup.mem_subgroupOf.2 hb)
    exact congrArg Subtype.val this
  have hP2 : Nat.card P = p ^ 2 := by
    rcases h.card with h2 | h3
    · exact h2
    · obtain ⟨a, ha, b, hb, hne⟩ := h.nonab h3
      exact absurd (hab' a ha b hb) hne
  have hP' : Nat.card (P.subgroupOf L) = p ^ 2 := by
    rw [← hP2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  set N : Subgroup A := T ⊓ Subgroup.normalizer (P : Set A) with hNdef
  have hN2 : IsPGroup 2 N := h.sylow.2.1.to_le inf_le_left
  let ρ : N →* MulAut L := (MulAut.conjNormal : A →* MulAut L).comp N.subtype
  obtain ⟨Q', hQ'P, hQ'p, hQ'⟩ := exists_fixed_line hN2 ρ
    (fun n => map_conjNormal_subgroupOf n.2.2) (hodd hP')
  set Q := Q'.map L.subtype with hQdef
  have hQP : Q ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ'P hx)
  have hQp : Nat.card Q = p := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQ'p]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (Q : Set A) := by
    rintro t ht
    have hα : Q'.map (MulAut.conjNormal t : MulAut L).toMonoidHom = Q' := hQ' ⟨t, ht⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : MulAut.conjNormal t x ∈ Q' := by
        rw [← hα]
        exact ⟨x, hx, rfl⟩
      exact ⟨_, hx', by simp [MulAut.conjNormal_apply]⟩
    · rintro ⟨y, hy, hyg⟩
      have hyg' : (y : A) = t * g * t⁻¹ := hyg
      have hgL : g ∈ L := by
        have := hLn.conj_mem _ y.2 t⁻¹
        rwa [hyg', show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at this
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      rw [← hα] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hxg : x = ⟨g, hgL⟩ := by
        apply Subtype.ext
        have h1 : t * (x : A) * t⁻¹ = (y : A) := by
          rw [← MulAut.conjNormal_apply]
          exact congrArg Subtype.val hxy
        rw [hyg'] at h1
        simpa using h1
      rw [← hxg]
      exact hx
  have hcomm : ⁅P, P⁆ = ⊥ := commutator_eq_bot_of_comm hab'
  rcases h.irred Q (by rw [hcomm]; exact bot_le) hQP hnorm with h' | h'
  · rw [h', hcomm, Subgroup.card_bot] at hQp
    have := (Fact.out : p.Prime).one_lt
    omega
  · rw [h', hP2] at hQp
    have h1 := (Fact.out : p.Prime).one_lt
    have : p ^ 2 > p := by nlinarith
    omega

end Config

end CFSG.Quasithin.H13.NQCore.U3O
