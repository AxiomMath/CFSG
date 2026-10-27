module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442XCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.Shult CFSG.Quasithin.Loc442 MulAction


theorem acoreGCop {G : Type} [Group G] [Finite G] {K X V : Subgroup G} (hXK : X ≤ K) (hne : ¬ K ≤ X)
    (hVX : V ≤ X) (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hV4 : Nat.card V = 4)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hfix : ∀ v ∈ V, v ≠ 1 → ∀ g ∈ K, g⁻¹ * v * g ∈ X → g ∈ X)
    {q : G} (hqX : q ∈ X) (hqV : ∀ v ∈ V, q * v = v * q) (hq2 : q ^ 2 ∈ V) (hq2' : q ^ 2 ≠ 1)
    (hXc : Nat.Coprime (Nat.card X) 65) : False := by
  have hVK : V ≤ K := hVX.trans hXK
  have hX' : X.subgroupOf K ≠ ⊤ := by
    intro h
    apply hne
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ X.subgroupOf K := by rw [h]; trivial
    exact this
  have hVX' : V.subgroupOf K ≤ X.subgroupOf K := fun v hv => hVX hv
  have hVn' : ((V.subgroupOf K).subgroupOf (X.subgroupOf K)).Normal :=
    ⟨fun n hn g => hVn _ g.2 _ hn⟩
  have hV4' : Nat.card (V.subgroupOf K) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hfix' : ShultFixedPoint (X.subgroupOf K) (V.subgroupOf K) := by
    intro v hv hv1
    refine ⟨((1 : ↥K) : ↥K ⧸ X.subgroupOf K), ?_, ?_⟩
    · show ((v * 1 : ↥K) : ↥K ⧸ X.subgroupOf K) = ((1 : ↥K) : ↥K ⧸ X.subgroupOf K)
      rw [mul_one]
      exact (mk_eq_one_iff _).2 (hVX' hv)
    · intro c hc
      induction c using QuotientGroup.induction_on with
      | H g =>
        have h' : ((v * g : ↥K) : ↥K ⧸ X.subgroupOf K) = (g : ↥K ⧸ X.subgroupOf K) := hc
        rw [QuotientGroup.eq] at h'
        have hg : (g : G)⁻¹ * (v : G) * (g : G) ∈ X := by
          have := X.inv_mem (Subgroup.mem_subgroupOf.1 h')
          simpa [mul_assoc] using this
        have hgX := hfix v hv (fun h => hv1 (Subtype.ext h)) g g.2 hg
        exact ((mk_eq_one_iff (X := X.subgroupOf K) g).2 hgX).trans rfl
  refine acoreCop (K := ↥K) (X := X.subgroupOf K) (V := V.subgroupOf K)
    (q := ⟨q, hXK hqX⟩) hX' hVX' hVn' hV4' (fun a ha b hb => Subtype.ext (hVab a ha b hb))
    (fun a ha => Subtype.ext (hV2 a ha)) hfix' hqX
    (fun v hv => Subtype.ext (hqV v hv)) hq2 (fun h => hq2' (congrArg Subtype.val h)) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  exact hXc

end CFSG.Quasithin
