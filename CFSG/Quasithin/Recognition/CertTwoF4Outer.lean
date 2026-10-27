module

public import CFSG.Quasithin.Recognition.CertTwoF4Lattice

public noncomputable section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Sporadic.Schreier.Tits

@[expose] def TitsOutBound : Prop := Nat.card (Outer CFSG.Open.quasithinTits) ≤ 2

theorem card_mulAut_le_of_outer {G H : Type*} [Group G] [Group H] [Finite G] {k : ℕ}
    (hout : Nat.card (Outer G) ≤ k) (f : G ≃* H) : Nat.card (MulAut H) ≤ k * Nat.card G := by
  rw [← Nat.card_congr (MulAut.congr f).toEquiv,
    (inner G).card_eq_card_quotient_mul_card_subgroup]
  have hinn : Nat.card (inner G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  exact Nat.mul_le_mul hout hinn

instance finite_mulAut_titsD : Finite (MulAut titsD) :=
  Finite.of_injective (fun α : MulAut titsD => (α : titsD → titsD)) fun _ _ h =>
    MulEquiv.ext fun x => congrFun h x

instance finite_quasithinTits :
    Finite CFSG.Open.quasithinTits :=
  Finite.of_equiv titsD quasithinTitsEquivD.symm.toEquiv

theorem card_mulAut_titsD_le
    (h : TitsOutBound) : Nat.card (MulAut titsD) ≤ 2 * Nat.card titsD := by
  have h1 := card_mulAut_le_of_outer h quasithinTitsEquivD
  rwa [Nat.card_congr quasithinTitsEquivD.toEquiv] at h1

theorem card_twoF4M
    : Nat.card twoF4M = 2 * Nat.card titsD := by
  have h := Subgroup.card_mul_index (titsD.subgroupOf twoF4M)
  rw [index_titsD_twoF4M, card_subgroupOf_eq titsD_le_twoF4M] at h
  omega

theorem twoF4D_normal
    : (titsD.subgroupOf twoF4M).Normal :=
  Subgroup.normal_of_index_eq_two index_titsD_twoF4M

@[expose] def twoF4ConjD
    : twoF4M →* MulAut titsD :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe titsD_le_twoF4M)).toMonoidHom.comp
    (@MulAut.conjNormal _ _ (titsD.subgroupOf twoF4M) twoF4D_normal)

theorem twoF4ConjD_apply
    (x : twoF4M) (g : titsD) :
    ((twoF4ConjD x g : titsD) : Equiv.Perm (Fin 1755)) = x * g * (x : Equiv.Perm (Fin 1755))⁻¹ :=
  rfl

theorem twoF4ConjD_injective
    : Function.Injective twoF4ConjD := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply centralizer_titsD_eq_one
  intro g hg
  have e := congrArg (fun α : MulAut titsD => ((α ⟨g, hg⟩ : titsD) : Equiv.Perm (Fin 1755)))
    (MonoidHom.mem_ker.1 hx)
  simp only [twoF4ConjD_apply, MulAut.one_apply] at e
  calc (x : Equiv.Perm (Fin 1755)) * g
      = (x * g * (x : Equiv.Perm (Fin 1755))⁻¹) * x := by group
    _ = g * x := by rw [e]

theorem twoF4ConjD_bijective
    (h : TitsOutBound) : Function.Bijective twoF4ConjD :=
  twoF4ConjD_injective.bijective_of_nat_card_le (by
    rw [card_twoF4M]
    exact card_mulAut_titsD_le h)

@[expose] def twoF4MulEquiv
    (h : TitsOutBound) : MulAut titsD ≃* twoF4M :=
  (MulEquiv.ofBijective twoF4ConjD (twoF4ConjD_bijective h)).symm

@[expose] def twoF4AutEquiv
    (h : TitsOutBound) :
    MulAut CFSG.Open.quasithinTits ≃* twoF4M :=
  (MulAut.congr quasithinTitsEquivD).trans (twoF4MulEquiv h)

end CFSG.Quasithin
