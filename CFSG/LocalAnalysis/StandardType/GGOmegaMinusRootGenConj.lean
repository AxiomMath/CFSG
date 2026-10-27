module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.SeitzReduction.SymplecticPilot

variable {K : Type} [Field K]

private theorem kOmMDiag_eq_diagGL_minusUnits {m : ℕ} (t : Fin m → Kˣ) :
    kOmMDiag K m t = TauCeti.diagGL (OrdPOm.minusUnits t) :=
  rfl

private theorem coe_subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (x : H.subgroupOf K) :
    ((Subgroup.subgroupOfEquivOfLe h x : H) : G) = (x : K) :=
  rfl

theorem exists_mulEquiv_eq_map_omMinusTorus {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {E : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))} (hE : IsElemAbelian p E)
    (hcard : p ^ m ≤ Nat.card E) :
    ∃ α : StatedOmega (StatedQuadMinus (m + 1) K b c) ≃*
        StatedOmega (StatedQuadMinus (m + 1) K b c),
      E = (omMinusTorus b c hζ).range.map α.toMonoidHom := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let Q : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) → K :=
    StatedQuadMinus (m + 1) K b c
  let O : Subgroup (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :=
    LargeEvenOrthGroup Q
  let Ω : Subgroup (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :=
    StatedOmega Q
  let A : Subgroup (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :=
    E.map Ω.subtype
  have hAO : A ≤ O := by
    intro x hx
    have hx' : x ∈ E.map Ω.subtype := hx
    obtain ⟨y, -, rfl⟩ := hx'
    exact TableBOrth.omega_le_orth Q y.2
  have hAab : IsElemAbelian p A := IsElemAbelian.map hE Ω.subtype
  have hAcard_ge : p ^ m ≤ Nat.card A := by
    change p ^ m ≤ Nat.card (E.map Ω.subtype)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Ω)]
    exact hcard
  have hpn : 1 ≤ m + 1 := by omega
  obtain ⟨g, hgO, χ, hχ⟩ := OrdPOm.exists_orth_conj_minus_le (n := m + 1)
    (b := b) (c := c) hp2 hζo hirr hpn hAO hAab
  let ψ : A → (Fin (m + 1 - 1) → Kˣ) := fun x k => χ k x
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
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ (omMinusTorusGL hζ).range := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    choose f hf using fun k => hζroot (ψ ⟨x, hx⟩ k) (hψp ⟨x, hx⟩ k)
    refine ⟨f, ?_⟩
    have hpar : (omMinusTorusParam m hζ) f =
        fun k => TableBSymp.zmodPowHom hζ (f k) := by
      funext k
      rw [omMinusTorusParam_apply]
    have hfun : (fun k => TableBSymp.zmodPowHom hζ (f k)) = fun k => χ k ⟨x, hx⟩ :=
      funext hf
    rw [omMinusTorusGL_apply, hpar, hfun, kOmMDiag_eq_diagGL_minusUnits]
    change TauCeti.diagGL (OrdPOm.minusUnits fun k => (χ k) ⟨x, hx⟩) =
      (MulAut.conj g) x
    rw [MulAut.conj_apply]
    exact (hχ ⟨x, hx⟩).symm
  have hAcard : Nat.card A = p ^ m := by
    refine le_antisymm ?_ hAcard_ge
    have h := OrdPOm.card_le_minus (n := m + 1) hp2 hζo hirr hpn hAO hAab
    calc Nat.card A ≤ p ^ (m + 1 - 1) := h
      _ = p ^ m := by rw [Nat.add_sub_cancel]
  have htorcard : Nat.card (omMinusTorusGL (m := m) hζ).range = p ^ m := by
    rw [← Nat.card_congr
        (MonoidHom.ofInjective (omMinusTorusGL_injective hζ hζo)).toEquiv,
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hAconj : A.map (MulAut.conj g).toMonoidHom = (omMinusTorusGL hζ).range := by
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
      ((β x : Ω) : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) =
        g * (x : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) * g⁻¹ := by
    intro x
    have hxO : (⟨x.1, hΩO x.2⟩ : O) ∈ Ω.subgroupOf O :=
      Subgroup.mem_subgroupOf.mpr x.2
    have h1 : (Subgroup.subgroupOfEquivOfLe hΩO).symm x =
        (⟨⟨x.1, hΩO x.2⟩, hxO⟩ : Ω.subgroupOf O) := rfl
    dsimp only [β]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, coe_subgroupOfEquivOfLe,
      MulAut.conjNormal_apply]
    rfl
  have htorGL : (omMinusTorus b c hζ).range.map Ω.subtype = (omMinusTorusGL hζ).range := by
    have h : Ω.subtype.comp (omMinusTorus b c hζ) = omMinusTorusGL hζ :=
      MonoidHom.ext fun f => coe_omMinusTorus b c hζ f
    rw [MonoidHom.map_range, h]
  have hmapβ : E.map β.toMonoidHom = (omMinusTorus b c hζ).range := by
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
