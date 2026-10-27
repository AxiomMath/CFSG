module

public import CFSG.Sporadic.Schreier.TitsQTConj
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.Sporadic.Schreier.TitsQT

open CFSG.Sporadic.Schreier.Tits

theorem eq_bot_of_abelian_stronglyClosed {G : Type*} [Group G] [Finite G] (P Q : Sylow 2 G)
    (z : G) (hcen : ∀ w ∈ (P : Subgroup G), (∀ p ∈ (P : Subgroup G), p * w = w * p) →
      w = 1 ∨ w = z)
    (g h : G) (hg : g * z * g⁻¹ ∈ (P : Subgroup G)) (hh : h * z * h⁻¹ ∈ (P : Subgroup G))
    (hgh : (g * z * g⁻¹) * (h * z * h⁻¹) ≠ (h * z * h⁻¹) * (g * z * g⁻¹))
    (A : Subgroup G) (hAQ : A ≤ (Q : Subgroup G)) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsc : ∀ a ∈ A, ∀ k : G, k⁻¹ * a * k ∈ (Q : Subgroup G) → k⁻¹ * a * k ∈ A) : A = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  have hPQ : (P : Subgroup G) = (Q : Subgroup G).map (MulAut.conj c).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hc
    exact this.symm
  have hmem : ∀ x : G, x ∈ (P : Subgroup G) ↔ c⁻¹ * x * c ∈ (Q : Subgroup G) := by
    intro x
    rw [hPQ]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e : c⁻¹ * (MulAut.conj c).toMonoidHom y * c = y := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hy
    · intro hx
      refine ⟨c⁻¹ * x * c, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hQ2 : IsPGroup 2 (Q : Subgroup G) := Q.isPGroup'
  have hAn : ∀ a ∈ A, ∀ q ∈ (Q : Subgroup G), q⁻¹ * a * q ∈ A := fun a ha q hq =>
    hsc a ha q (mul_mem (mul_mem (inv_mem hq) (hAQ ha)) hq)
  obtain ⟨a₀, ha₀A, ha₀1, ha₀c⟩ : ∃ a ∈ A, a ≠ 1 ∧ ∀ q ∈ (Q : Subgroup G), q * a = a * q := by
    have hnil : Group.IsNilpotent (Q : Subgroup G) := hQ2.isNilpotent
    let A' : Subgroup (Q : Subgroup G) := A.subgroupOf (Q : Subgroup G)
    have hA'n : A'.Normal := ⟨fun a ha q => by
      have h := hAn (a : G) ha (q : G)⁻¹ ((Q : Subgroup G).inv_mem q.2)
      simpa [A', Subgroup.mem_subgroupOf, mul_assoc] using h⟩
    have hA'ne : A' ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro a ha
      have : (⟨a, hAQ ha⟩ : (Q : Subgroup G)) ∈ A' := ha
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hcen' := Group.IsNilpotent.inf_center_ne_bot_of_normal hA'ne
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcen'
    have hxA : (x : (Q : Subgroup G)) ∈ A' := x.2.1
    have hxc : (x : (Q : Subgroup G)) ∈ Subgroup.center (Q : Subgroup G) := x.2.2
    refine ⟨((x : (Q : Subgroup G)) : G), hxA, ?_, fun q hq => ?_⟩
    · intro h
      apply hx1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · have := Subgroup.mem_center_iff.mp hxc ⟨q, hq⟩
      exact congrArg Subtype.val this
  have hwP : c * a₀ * c⁻¹ ∈ (P : Subgroup G) := by
    rw [hmem]
    simpa [mul_assoc] using hAQ ha₀A
  have hwc : ∀ p ∈ (P : Subgroup G), p * (c * a₀ * c⁻¹) = (c * a₀ * c⁻¹) * p := by
    intro p hp
    have hq : c⁻¹ * p * c ∈ (Q : Subgroup G) := (hmem p).1 hp
    have h1 := ha₀c _ hq
    calc p * (c * a₀ * c⁻¹) = c * ((c⁻¹ * p * c) * a₀) * c⁻¹ := by group
      _ = c * (a₀ * (c⁻¹ * p * c)) * c⁻¹ := by rw [h1]
      _ = (c * a₀ * c⁻¹) * p := by group
  have hw1 : c * a₀ * c⁻¹ ≠ 1 := by
    intro h
    apply ha₀1
    have : a₀ = c⁻¹ * (c * a₀ * c⁻¹) * c := by group
    rw [this, h]
    group
  have hwz : c * a₀ * c⁻¹ = z := (hcen _ hwP hwc).resolve_left hw1
  have ha₀z : a₀ = c⁻¹ * z * c := by
    rw [← hwz]
    group
  have hx : c⁻¹ * (g * z * g⁻¹) * c ∈ A := by
    have e : (c⁻¹ * g⁻¹ * c)⁻¹ * a₀ * (c⁻¹ * g⁻¹ * c) = c⁻¹ * (g * z * g⁻¹) * c := by
      rw [ha₀z]
      group
    have := hsc a₀ ha₀A (c⁻¹ * g⁻¹ * c) (by rw [e]; exact (hmem _).1 hg)
    rwa [e] at this
  have hy : c⁻¹ * (h * z * h⁻¹) * c ∈ A := by
    have e : (c⁻¹ * h⁻¹ * c)⁻¹ * a₀ * (c⁻¹ * h⁻¹ * c) = c⁻¹ * (h * z * h⁻¹) * c := by
      rw [ha₀z]
      group
    have := hsc a₀ ha₀A (c⁻¹ * h⁻¹ * c) (by rw [e]; exact (hmem _).1 hh)
    rwa [e] at this
  have hcomm := hab _ hx _ hy
  apply hgh
  have : c⁻¹ * ((g * z * g⁻¹) * (h * z * h⁻¹)) * c =
      c⁻¹ * ((h * z * h⁻¹) * (g * z * g⁻¹)) * c := by
    calc c⁻¹ * ((g * z * g⁻¹) * (h * z * h⁻¹)) * c
        = (c⁻¹ * (g * z * g⁻¹) * c) * (c⁻¹ * (h * z * h⁻¹) * c) := by group
      _ = (c⁻¹ * (h * z * h⁻¹) * c) * (c⁻¹ * (g * z * g⁻¹) * c) := hcomm
      _ = c⁻¹ * ((h * z * h⁻¹) * (g * z * g⁻¹)) * c := by group
  simpa using this

@[expose] def titsZD : titsD := ⟨titsZ, titsZ_mem_titsD⟩

theorem titsSylow_central_eq
    (w : titsD) (hw : w ∈ (titsSylow : Subgroup titsD))
    (hc : ∀ p ∈ (titsSylow : Subgroup titsD), p * w = w * p) : w = 1 ∨ w = titsZD := by
  rw [coe_titsSylow] at hw hc
  have hwS : (w : Equiv.Perm (Fin 1755)) ∈ titsS := Subgroup.mem_subgroupOf.1 hw
  have hcen : (⟨(w : Equiv.Perm (Fin 1755)), hwS⟩ : titsS) ∈ Subgroup.center titsS := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h := hc ⟨(s : Equiv.Perm (Fin 1755)), titsS_le_titsD s.2⟩
      (Subgroup.mem_subgroupOf.2 s.2)
    have h2 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hmem : (w : Equiv.Perm (Fin 1755)) ∈
      ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) :=
    SetLike.mem_coe.2 (Subgroup.mem_map.2 ⟨_, hcen, rfl⟩)
  rw [titsS_center] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem QT_unique_Tits_no_abelian_strong_closure
    (Q : Sylow 2 titsD) (A : Subgroup titsD)
    (hA : CFSG.IsStronglyClosedIn (Q : Subgroup titsD) (A : Set titsD))
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  obtain ⟨hgD, hhD⟩ := conjugators_mem_titsD
  set g : Equiv.Perm (Fin 1755) :=
    (titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 ^ 2 with hg
  set h : Equiv.Perm (Fin 1755) := (titsDGen 0)⁻¹ with hh
  obtain ⟨hxS, hyS, hxy, -, -⟩ :=
    QT_unique_Tits_central_involution_noncommuting_Sylow_conjugates g h hg hh
  have hmemS : ∀ w : titsD, w ∈ (titsSylow : Subgroup titsD) ↔
      (w : Equiv.Perm (Fin 1755)) ∈ titsS := fun w => by
    rw [coe_titsSylow]
    exact Subgroup.mem_subgroupOf
  exact eq_bot_of_abelian_stronglyClosed titsSylow Q titsZD
    (fun w hw hc => titsSylow_central_eq w hw hc) ⟨g, hgD⟩ ⟨h, hhD⟩
    ((hmemS _).2 hxS) ((hmemS _).2 hyS) (fun hE => hxy (congrArg Subtype.val hE)) A
    (fun a ha => hA.1 ha) hab (fun a ha k hk => hA.2 a ha k hk)

end CFSG.Sporadic.Schreier.TitsQT
