module

public import CFSG.RankThree.GF2n.Tim79a34Local
public import CFSG.RankThree.GF2n.Tim79a34TwDefs
public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim78Frattini
public import CFSG.RankThree.GF2n.Tim79a34Natural

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

theorem lemma11b_psi_mul {G : Type} [Group G] {V H : Subgroup G} {n : ℕ}
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (u v : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ (u + v)) : ↥(wOf V H)) : G) := by
  rw [map_add]
  rfl

theorem lemma11b_holds (hN : NaturalModuleStatement) (h11a : Lemma11aStatement)
    (hB4 : SpRadFactsStatement) : Lemma11bStatement := by
  intro G _ _ M V Q P H hH hZ hcP
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨n, Φ, ψ, hn2, hNat, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  have hNC : NatCfg V H hVH Φ ψ := ⟨hNat, hpoint⟩
  obtain ⟨hiff, hRbar, hxOf, -⟩ := h11a G M V Q P H hH hZ hcP Φ ψ hNC a T ha hT hTV
  have hn : 1 ≤ n := by omega
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hB4' := hB4 n hn (GaloisField 2 1) hF2 a ha
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hPH : P ≤ H := hc.PleH
  have hPX : P ≤ xOf V H := by
    rw [hxOf]
    exact hPH
  have hmemR : ∀ p : G, ∀ hp : p ∈ P, xToXbar hVH ⟨p, hPX hp⟩ ∈ Rbar V H P := by
    intro p hp
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨⟨p, hPH hp⟩, hp, rfl⟩
  have hsurj : ∀ r ∈ Rbar V H P, ∃ p : G, ∃ hp : p ∈ P, xToXbar hVH ⟨p, hPX hp⟩ = r := by
    intro r hr
    obtain ⟨x, hxP, hxr⟩ := mem_barOf_iff.mp (mem_Rbar.mp hr)
    refine ⟨(x : G), hxP, Subtype.ext ?_⟩
    rw [coe_xToXbar]
    exact hxr
  have hsp : ∀ p : G, ∀ hp : p ∈ P, ∃ g ∈ spRad a,
      Φ.toMonoidHom g = xToXbar hVH ⟨p, hPX hp⟩ := by
    intro p hp
    have h := hmemR p hp
    rw [hRbar] at h
    exact Subgroup.mem_map.mp h
  have hker : ∀ z : ↥(xOf V H), xToXbar hVH z = 1 ↔ (z : G) ∈ wOf V H := by
    intro z
    constructor
    · intro h
      have h1 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) z) = 1 := by
        rw [← coe_xToXbar hVH z, h]
        rfl
      exact (piBar_eq_one_iff _).mp h1
    · intro h
      apply Subtype.ext
      rw [coe_xToXbar hVH z]
      exact (piBar_eq_one_iff _).mpr h
  have hcommW : ∀ p : G, ∀ hp : p ∈ P, ∀ q : G, ∀ hq : q ∈ P, ⁅p, q⁆ ∈ wOf V H := by
    intro p hp q hq
    obtain ⟨g, hg, hgp⟩ := hsp p hp
    obtain ⟨h, hh, hhq⟩ := hsp q hq
    have hgh : Φ.toMonoidHom g * Φ.toMonoidHom h = Φ.toMonoidHom h * Φ.toMonoidHom g := by
      rw [← map_mul, ← map_mul, hB4'.1 g hg h hh]
    have h1 : xToXbar hVH ⁅(⟨p, hPX hp⟩ : ↥(xOf V H)), ⟨q, hPX hq⟩⁆ = 1 := by
      rw [map_commutatorElement, ← hgp, ← hhq, commutatorElement_eq_one_iff_mul_comm]
      exact hgh
    exact (hker _).mp h1
  have hsqW : ∀ p : G, ∀ hp : p ∈ P, p * p ∈ wOf V H := by
    intro p hp
    obtain ⟨g, hg, hgp⟩ := hsp p hp
    have h1 : xToXbar hVH ((⟨p, hPX hp⟩ : ↥(xOf V H)) * ⟨p, hPX hp⟩) = 1 := by
      rw [map_mul, ← hgp, ← map_mul, hB4'.2.1 g hg, map_one]
    exact (hker _).mp h1
  have hPPV : ⁅P, P⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    exact hc.commutator_mem_V_of_mem_P hp hq
  have hPPW : ⁅P, P⁆ ≤ wOf V H := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    exact hcommW p hp q hq
  have hwex : ∃ w : Fin n ⊕ Fin n → GaloisField 2 1, CaseM.spForm a w = 0 ∧
      ∀ c : GaloisField 2 1, w ≠ c • a := by
    obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
    have hba : CaseM.spForm b a = -1 := by
      rw [CaseM.spForm_comm, hb]
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b]
      (by rw [Fintype.card_fin]; omega)
    refine ⟨w, hw 0, fun c hc => hw0 ?_⟩
    have h1 : CaseM.spForm b w = 0 := hw 1
    rw [hc, spForm_smul_right', hba] at h1
    have hc0 : c = 0 := by linear_combination -h1
    rw [hc, hc0, zero_smul]
  obtain ⟨w, haw, hwa⟩ := hwex
  obtain ⟨u, hau, hwu⟩ := exists_dual ha haw hwa
  have huw : CaseM.spForm u w = 1 := by
    rw [CaseM.spForm_comm, hwu, CharTwo.neg_eq]
  have hτ : Φ.toMonoidHom (spTau a u 0 hau) ∈ Rbar V H P := by
    rw [hRbar]
    exact Subgroup.mem_map_of_mem _ (spTau_mem a u 0 hau)
  obtain ⟨p, hp, hpτ⟩ := hsurj _ hτ
  have hsymm : Φ.symm (xToXbar hVH ⟨p, hPX hp⟩) = spTau a u 0 hau := by
    rw [hpτ]
    exact Φ.symm_apply_apply _
  have hτw : SpExtras.mat n (GaloisField 2 1) (spTau a u 0 hau) *ᵥ w = w + a := by
    rw [spTau_mulVec, haw, huw]
    simp
  have hact : ((Additive.toMul (ψ (w + a)) : ↥(wOf V H)) : G) =
      p * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * p⁻¹ := by
    have h := hNat ⟨p, hPX hp⟩ w
    rw [hsymm, hτw] at h
    exact h
  have hconj : p * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * p⁻¹ =
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := by
    rw [← hact, lemma11b_psi_mul ψ w a]
  have hxaG : ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) *
      ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) := by
    rw [lemma11b_psi_mul ψ w a, lemma11b_psi_mul ψ a w, add_comm w a]
  have hPaG : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ ⁅P, P⁆ := by
    have hxP : ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P := (hiff w).mpr haw
    have hcm := Subgroup.commutator_mem_commutator hp hxP
    have heq : ⁅p, ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)⁆ =
        ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := by
      rw [commutatorElement_def, hconj, hxaG, mul_inv_cancel_right]
    rw [← heq]
    exact hcm
  have haW : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ wOf V H :=
    (Additive.toMul (ψ a) : ↥(wOf V H)).2
  have haV : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V := hpoint a T ha hT hTV
  have haG1 : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ≠ 1 := by
    intro h
    have h1 : (Additive.toMul (ψ a) : ↥(wOf V H)) = 1 := Subtype.ext h
    have h2 : ψ a = 0 := Additive.toMul.injective (show Additive.toMul (ψ a) =
      Additive.toMul (0 : Additive ↥(wOf V H)) from h1)
    exact ha (ψ.injective (h2.trans (map_zero ψ).symm))
  have hsa : a + a = 0 := by
    funext i
    simp [CharTwo.add_self_eq_zero]
  have haG2 : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ^ 2 = 1 := by
    rw [pow_two, lemma11b_psi_mul ψ a a, hsa, map_zero]
    rfl
  have haord : orderOf ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) = 2 :=
    orderOf_eq_prime haG2 haG1
  have hVWeq : V ⊓ wOf V H = Subgroup.zpowers ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨haV, haW⟩
    · exact le_of_eq (by rw [Nat.card_zpowers, haord, hVW])
  have hcomm_eq : ⁅P, P⁆ = V ⊓ wOf V H := by
    apply le_antisymm
    · exact le_inf hPPV hPPW
    · rw [hVWeq, Subgroup.zpowers_le]
      exact hPaG
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hP2 : IsPGroup 2 P := hc.isPGroup_P
  have hfr_le : inSubgroup frattini P ≤ V ⊓ wOf V H := by
    have hle : frattini ↥P ≤ (V ⊓ wOf V H).subgroupOf P := by
      rw [frattini_eq_closure_commutator_union_powers (p := 2)]
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | ⟨y, rfl⟩)
      · have hcomm_le : _root_.commutator ↥P ≤ (V ⊓ wOf V H).subgroupOf P := by
          show ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ ≤ _
          refine Subgroup.commutator_le.mpr ?_
          intro g₁ _ g₂ _
          rw [Subgroup.mem_subgroupOf, ← hcomm_eq]
          exact Subgroup.commutator_mem_commutator g₁.2 g₂.2
        exact hcomm_le hx
      · simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_pow]
        exact ⟨hc.frattini_P_le (Tim78.sq_mem_inSubgroup_frattini hP2 y.2),
          by rw [pow_two]; exact hsqW _ y.2⟩
    exact Subgroup.map_le_iff_le_comap.mpr hle
  refine ⟨hcomm_eq, ?_, hc.centralizer_P_eq⟩
  apply le_antisymm hfr_le
  rw [← hcomm_eq]
  exact Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    Tim78.commutatorElement_mem_inSubgroup_frattini hP2 hg₁ hg₂

end CFSG.RankThree.GF2n.Tim79a
