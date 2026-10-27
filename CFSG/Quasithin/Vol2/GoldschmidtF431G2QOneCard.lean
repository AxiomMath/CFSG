module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOne
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Bil

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

section Orders

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem card_Xc : Nat.card (Xc K) = Nat.card K :=
  (Nat.card_congr (Equiv.ofInjective (xe (K := K) rC) (xe_injective rC))).symm

theorem card_Q1 : Nat.card (Q1 K) = Nat.card K ^ 5 := by
  let f : K × K × K × K × K → Q1 K :=
    fun c => ⟨nf c.1 0 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2, mem_Q1_iff.2 ⟨_, _, _, _, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩ h
      have h' := congrArg Subtype.val h
      dsimp only [f] at h'
      obtain ⟨h1, -, h2, h3, h4, h5⟩ := nf_injective h'
      rw [h1, h2, h3, h4, h5]
    · intro g
      obtain ⟨α, μ, ν, β, γ, hg⟩ := mem_Q1_iff.1 g.2
      exact ⟨(α, μ, ν, β, γ), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp only [Nat.card_prod]
  ring

theorem card_abelian_le_Q1 [Finite K] {E : Subgroup (C K)} (hE : E ≤ Q1 K)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ Nat.card K ^ 3 := by
  classical
  let nq : K × K × K × K × K → C K := fun c => nf c.1 0 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
  have hnq : Function.Injective nq := by
    rintro ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩ h
    dsimp only [nq] at h
    obtain ⟨h1, -, h2, h3, h4, h5⟩ := nf_injective h
    rw [h1, h2, h3, h4, h5]
  let T : Set (K × K × K × K × K) := {c | nq c ∈ E}
  have hET : Nat.card T = Nat.card E := by
    refine Nat.card_congr (Equiv.ofBijective (fun c : T => (⟨nq c.1, c.2⟩ : E)) ⟨?_, ?_⟩)
    · intro c d h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (hnq h')
    · intro x
      obtain ⟨α, μ, ν, β, γ, hx⟩ := mem_Q1_iff.1 (hE x.2)
      refine ⟨⟨(α, μ, ν, β, γ), ?_⟩, Subtype.ext hx.symm⟩
      show nf α 0 μ ν β γ ∈ E
      rw [← hx]
      exact x.2
  let proj : K × K × K × K × K → K × K × K × K := fun c => (c.1, c.2.1, c.2.2.1, c.2.2.2.1)
  let P : Set (K × K × K × K) := proj '' T
  have h1 : Nat.card T ≤ Nat.card P * Nat.card K := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun c : T => ((⟨proj c.1, Set.mem_image_of_mem proj c.2⟩ : P), c.1.2.2.2.2)) ?_
    rintro ⟨⟨a1, a2, a3, a4, a5⟩, ha⟩ ⟨⟨b1, b2, b3, b4, b5⟩, hb⟩ h
    have h' := Prod.mk.inj h
    have e1 := congrArg Subtype.val h'.1
    have e2 : a5 = b5 := h'.2
    simp only [proj, Prod.mk.injEq] at e1
    obtain ⟨c1, c2, c3, c4⟩ := e1
    subst c1 c2 c3 c4 e2
    rfl
  have h2 : Nat.card P ≤ Nat.card K ^ 2 := by
    refine card_isotropic_le P ?_
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    have hcd : nq c * nq d = nq d * nq c := hab _ hc _ hd
    have := bil_eq_zero_of_comm hcd
    rw [bil_apply]
    linear_combination this
  calc Nat.card E = Nat.card T := hET.symm
    _ ≤ Nat.card P * Nat.card K := h1
    _ ≤ Nat.card K ^ 2 * Nat.card K := Nat.mul_le_mul_right _ h2
    _ = Nat.card K ^ 3 := by ring

end Orders

end CFSG.Quasithin.H13.F431.G2
