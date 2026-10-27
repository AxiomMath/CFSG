module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmWeights
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

private theorem coe_subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (x : H.subgroupOf K) :
    ((Subgroup.subgroupOfEquivOfLe h x : H) : G) = (x : K) :=
  rfl

theorem exists_mulEquiv_eq_map_omPlusTorus {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {E : Subgroup (StatedOmega (StatedQuadPlus m K))} (hE : IsElemAbelian p E)
    (hcard : p ^ m ≤ Nat.card E) :
    ∃ α : StatedOmega (StatedQuadPlus m K) ≃* StatedOmega (StatedQuadPlus m K),
      E = (omPlusTorus hζ).range.map α.toMonoidHom := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  let Q : (Fin m ⊕ Fin m → K) → K := StatedQuadPlus m K
  let O : Subgroup (GL (Fin m ⊕ Fin m) K) := LargeEvenOrthGroup Q
  let Ω : Subgroup (GL (Fin m ⊕ Fin m) K) := StatedOmega Q
  let A : Subgroup (GL (Fin m ⊕ Fin m) K) := E.map Ω.subtype
  have hAO : A ≤ O := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    exact TableBOrth.omega_le_orth Q y.2
  have hAab : IsElemAbelian p A := IsElemAbelian.map hE Ω.subtype
  have hAcard_ge : p ^ m ≤ Nat.card A := by
    change p ^ m ≤ Nat.card (E.map Ω.subtype)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Ω)]
    exact hcard
  obtain ⟨g, hgO, χ, hχ⟩ := OrdPOm.exists_orth_conj_plus_le (m := m) hp2 hζo hAO hAab
  let ψ : A → (Fin m → Kˣ) := fun x k => χ k x
  have hψp : ∀ x k, ψ x k ^ p = 1 := by
    intro x k
    have hxp : (x : ↥A) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hAab.2 x x.2)
    rw [show ψ x k = χ k x from rfl, ← map_pow, hxp, map_one]
  have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  have hζroot : ∀ u : Kˣ, u ^ p = 1 → ∃ a : Multiplicative (ZMod p),
      TableBSymp.zmodPowHom hζ a = u := by
    intro u hu
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p u).mpr hu)
    exact ⟨Multiplicative.ofAdd (n : ZMod p), by rw [TableBSymp.zmodPowHom_natCast, hn]⟩
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ (omPlusTorusGL hζ).range := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    choose f hf using fun k => hζroot (ψ ⟨x, hx⟩ k) (hψp ⟨x, hx⟩ k)
    refine ⟨f, ?_⟩
    rw [omPlusTorusGL_eq_spTorusGL, TableBSymp.spTorusGL_apply]
    have hfun : (fun k => TableBSymp.zmodPowHom hζ (f k)) = fun k => χ k ⟨x, hx⟩ :=
      funext hf
    rw [hfun]
    change TauCeti.diagGL (TableBSymp.pairedUnits fun k => χ k ⟨x, hx⟩) =
      (MulAut.conj g) x
    rw [MulAut.conj_apply]
    exact (hχ ⟨x, hx⟩).symm
  have hAcard : Nat.card A = p ^ m :=
    le_antisymm (OrdPOm.card_le_plus hp2 hζo hAO hAab) hAcard_ge
  have htorcard : Nat.card (omPlusTorusGL (m := m) hζ).range = p ^ m := by
    rw [omPlusTorusGL_eq_spTorusGL]
    exact OrdPOm.card_range_spTorusGL hζ hζo hpodd
  have hAconj : A.map (MulAut.conj g).toMonoidHom = (omPlusTorusGL hζ).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAcard, htorcard]
  have hΩO : Ω ≤ O := by
    intro x hx
    exact TableBOrth.omega_le_orth Q hx
  have hNormal : (Ω.subgroupOf O).Normal := by
    have h := Subgroup.normal_subgroupOf_commutator_sup (H₁ := O) (H₂ := O)
    rw [sup_idem] at h
    rwa [show Ω = ⁅O, O⁆ from rfl]
  haveI : (Ω.subgroupOf O).Normal := hNormal
  let gO : O := ⟨g, hgO⟩
  let β : Ω ≃* Ω :=
    (Subgroup.subgroupOfEquivOfLe hΩO).symm.trans
      ((MulAut.conjNormal gO).trans (Subgroup.subgroupOfEquivOfLe hΩO))
  have hβcoe : ∀ x : Ω,
      ((β x : Ω) : GL (Fin m ⊕ Fin m) K) = g * (x : GL (Fin m ⊕ Fin m) K) * g⁻¹ := by
    intro x
    have hxO : (⟨x.1, hΩO x.2⟩ : O) ∈ Ω.subgroupOf O :=
      Subgroup.mem_subgroupOf.mpr x.2
    have h1 : (Subgroup.subgroupOfEquivOfLe hΩO).symm x =
        (⟨⟨x.1, hΩO x.2⟩, hxO⟩ : Ω.subgroupOf O) := rfl
    dsimp only [β]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, coe_subgroupOfEquivOfLe,
      MulAut.conjNormal_apply]
    rfl
  have htorGL : (omPlusTorus hζ).range.map Ω.subtype = (omPlusTorusGL hζ).range := by
    have h : Ω.subtype.comp (omPlusTorus hζ) = omPlusTorusGL hζ :=
      MonoidHom.ext fun f => coe_omPlusTorus hζ f
    rw [MonoidHom.map_range, h]
  have hmapβ : E.map β.toMonoidHom = (omPlusTorus hζ).range := by
    apply Subgroup.map_injective (Subgroup.subtype_injective Ω)
    rw [Subgroup.map_map]
    have hcomp : Ω.subtype.comp β.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp Ω.subtype :=
      MonoidHom.ext fun x => hβcoe x
    rw [hcomp, ← Subgroup.map_map, show E.map Ω.subtype = A from rfl, hAconj, htorGL]
  refine ⟨β.symm, ?_⟩
  rw [← hmapβ, Subgroup.map_map]
  have hcomp : β.symm.toMonoidHom.comp β.toMonoidHom = MonoidHom.id Ω :=
    MonoidHom.ext fun x => by simp
  rw [hcomp, Subgroup.map_id]

end CFSG.StandardType

end
