module

public import CFSG.RankThree.GF2n.Tim79a34BigDirectTrans
public import CFSG.RankThree.GF2n.Tim79a34TwWSplit

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

theorem bigDirect_card_inf_wOf {G : Type} [Group G] {V H P : Subgroup G} {n f : ℕ}
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (ha : a ≠ 0)
    (hiff : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0) :
    Nat.card ↥(P ⊓ wOf V H) = Nat.card (GaloisField 2 f) ^ (2 * n - 1) := by
  rw [← natCard_ker_spFormL ha]
  symm
  refine Nat.card_eq_of_bijective (fun w : LinearMap.ker (spFormL a) =>
    (⟨psiElt ψ w.1, Subgroup.mem_inf.mpr ⟨(hiff w.1).mpr (LinearMap.mem_ker.mp w.2),
      psiElt_mem ψ w.1⟩⟩ : ↥(P ⊓ wOf V H))) ⟨?_, ?_⟩
  · intro w w' h
    have h0 := congrArg Subtype.val h
    have h' : psiElt ψ w.1 = psiElt ψ w'.1 := h0
    exact Subtype.ext (psiElt_injective ψ h')
  · rintro ⟨x, hx⟩
    obtain ⟨hxP, hxW⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, rfl⟩ := exists_psiElt ψ hxW
    exact ⟨⟨w, LinearMap.mem_ker.mpr ((hiff w).mp hxP)⟩, rfl⟩

theorem bigDirect_sup_eq_spRad {K : Type} [Field K] [CharP K 2] [Finite K] {n : ℕ}
    {a : Fin n ⊕ Fin n → K} (ha : a ≠ 0) {T S : Subgroup (StatedSp n K)} (hS : S ≤ spRad a)
    (hT : T ≤ spRad a) (hinf : S ⊓ T = ⊥)
    (hcard : Nat.card S * Nat.card T = Nat.card (spRad a)) : S ⊔ T = spRad a := by
  have hcomm : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    spRadCommStmt_holds ha x (hS hx) y (hT hy)
  have hle : S ⊔ T ≤ spRad a := sup_le hS hT
  have hc := twistedWSplit_card_eq_mul (W := S ⊔ T) le_sup_left le_sup_right hcomm rfl hinf
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard])

theorem bigDirect_transport {G : Type} [Group G] [Finite G] {V H P : Subgroup G} {n f : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (ha : a ≠ 0)
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))} (hT : CaseM.IsTransGroup a T)
    (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom)
    {Fe : Subgroup G} (hFeP : Fe ≤ P) (hPX : P ≤ xOf V H)
    (hbar : barOf V H Fe ⊓ barOf V H V = ⊥)
    (hcard : Nat.card ↥(barOf V H Fe) * Nat.card ↥(barOf V H V) = Nat.card ↥(spRad a)) :
    ∃ S : Subgroup ↥(StatedSp n (GaloisField 2 f)), S ≤ spRad a ∧ S ⊔ T = spRad a ∧
      S ⊓ T = ⊥ ∧ ∀ x, x ∈ S ↔ ((Φ x : Xbar V H) : Hbar V H) ∈ barOf V H Fe := by
  have hFeX : barOf V H Fe ≤ barOf V H (xOf V H) := barOf_mono (hFeP.trans hPX)
  set SX : Subgroup (Xbar V H) := (barOf V H Fe).subgroupOf (barOf V H (xOf V H)) with hSX
  set S : Subgroup ↥(StatedSp n (GaloisField 2 f)) := SX.map Φ.symm.toMonoidHom with hS
  have hmem : ∀ x, x ∈ S ↔ ((Φ x : Xbar V H) : Hbar V H) ∈ barOf V H Fe := by
    intro x
    rw [hS, Subgroup.mem_map_equiv, MulEquiv.symm_symm, hSX, Subgroup.mem_subgroupOf]
  have hSle : S ≤ spRad a := by
    intro x hx
    have h1 : ((Φ x : Xbar V H) : Hbar V H) ∈ barOf V H P := barOf_mono hFeP ((hmem x).mp hx)
    have h2 : Φ x ∈ Rbar V H P := mem_Rbar.mpr h1
    rw [hRbar] at h2
    have h3 := Subgroup.mem_map_equiv.mp h2
    simpa using h3
  have hinf : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxT⟩ := Subgroup.mem_inf.mp hx
    have h1 : Φ x ∈ Vy V H := by
      rw [← hTV]
      exact Subgroup.mem_map.mpr ⟨x, hxT, rfl⟩
    have h2 : ((Φ x : Xbar V H) : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.mp h1
    have h3 : ((Φ x : Xbar V H) : Hbar V H) ∈ barOf V H Fe ⊓ barOf V H V :=
      Subgroup.mem_inf.mpr ⟨(hmem x).mp hxS, h2⟩
    rw [hbar, Subgroup.mem_bot] at h3
    have h4 : Φ x = 1 := Subtype.ext h3
    rw [Subgroup.mem_bot]
    exact Φ.injective (by rw [h4, map_one])
  have hcS : Nat.card S = Nat.card (barOf V H Fe) := by
    rw [hS, Subgroup.card_map_of_injective Φ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFeX).toEquiv
  have hcT : Nat.card T = Nat.card (barOf V H V) := by
    have h1 : Nat.card (T.map Φ.toMonoidHom) = Nat.card T :=
      Subgroup.card_map_of_injective Φ.injective
    rw [← h1, hTV]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (barOf_V_le V H)).toEquiv
  refine ⟨S, hSle, bigDirect_sup_eq_spRad ha hSle (le_spRad_of_isTransGroup hT) hinf ?_, hinf,
    hmem⟩
  rw [hcS, hcT]
  exact hcard

theorem bigDirect_invariant {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hc : MinCex M V Q P H) {n f : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
    (hNat : ∀ (x : ↥(xOf V H)) (v : Fin n ⊕ Fin n → GaloisField 2 f),
      psiElt ψ (SpExtras.mat n (GaloisField 2 f) (Φ.symm (xToXbar hc.V_le_H x)) *ᵥ v) =
        (x : G) * psiElt ψ v * (x : G)⁻¹)
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (ha : a ≠ 0)
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))} (hT : CaseM.IsTransGroup a T)
    {Fe : Subgroup G}
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
      (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c))
    (hRFe : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ x ∈ Fe, r * x * r⁻¹ ∈ Fe)
    {S : Subgroup ↥(StatedSp n (GaloisField 2 f))} (hS : S ≤ spRad a)
    (hSmem : ∀ x, x ∈ S ↔ ((Φ x : Xbar V H) : Hbar V H) ∈ barOf V H Fe) :
    ∀ (w : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f)
      (g : ↥(StatedSp n (GaloisField 2 f))), spForm a w = 0 →
      SpExtras.mat n (GaloisField 2 f) g = spTrans w μ → ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
  intro w μ g hw hg x hx
  by_cases hwa : ∃ l : GaloisField 2 f, w = l • a
  · obtain ⟨l, rfl⟩ := hwa
    have hgT : g ∈ T := by
      rw [hT.1]
      exact ⟨l * l * μ, by rw [hg, spTrans_smul]⟩
    have hcomm := spRadCommStmt_holds ha g (le_spRad_of_isTransGroup hT hgT) x (hS hx)
    rw [hcomm, mul_inv_cancel_right]
    exact hx
  · push Not at hwa
    by_cases hμ : μ = 0
    · have hg1 : g = 1 := by
        apply SpExtras.mat_injective
        rw [hg, hμ, spTrans_zero, map_one]
      rw [hg1]
      simpa using hx
    · obtain ⟨r, hr, hact⟩ := hroot w μ hw hwa hμ
      have hrX : r ∈ xOf V H := (Subgroup.mem_inf.mp hr).1
      have hgr : g = Φ.symm (xToXbar hc.V_le_H ⟨r, hrX⟩) := by
        apply SpExtras.mat_injective
        rw [hg]
        refine Matrix.ext_iff_mulVec.2 fun v => ?_
        apply psiElt_injective ψ
        rw [spTrans_mulVec, ← hact v]
        exact (hNat ⟨r, hrX⟩ v).symm
      have hΦg : Φ g = xToXbar hc.V_le_H ⟨r, hrX⟩ := by
        rw [hgr]
        exact Φ.apply_symm_apply _
      rw [hSmem] at hx ⊢
      obtain ⟨x₁, hx₁, hx₁x⟩ := mem_barOf_iff.mp hx
      refine mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hc.V_le_H) ⟨r, hrX⟩ * x₁ *
        (Subgroup.inclusion (xOf_le_H hc.V_le_H) ⟨r, hrX⟩)⁻¹, ?_, ?_⟩
      · simpa using hRFe r hr _ hx₁
      · rw [map_mul, map_mul, map_inv, hx₁x, map_mul, map_mul, map_inv, hΦg]
        rfl

end CFSG.RankThree.GF2n.Tim79a
