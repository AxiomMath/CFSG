module

public import CFSG.RankThree.GF2n.Tim79a34BigDirectCount
public import CFSG.RankThree.GF2n.Tim79a34BigDirectGroup
public import CFSG.RankThree.GF2n.Tim79a34BigEpsGe
public import CFSG.RankThree.GF2n.Tim79a34BigNoInvComp
public import CFSG.RankThree.GF2n.Tim79a34BigRoot
public import CFSG.RankThree.GF2n.Tim79a34TwBound
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.SupMulCommutative

public section

namespace CFSG.RankThree.GF2n.Tim79a

section BigEpsStatements

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

@[expose] def BigEpsFConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ e : ↥M, (e : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) →
      conjSubgroup (e : G) (P ⊓ wOf V H) = P ⊓ wOf V H

@[expose] def BigEpsilonFaithfulTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ x ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)) ⊓
        Subgroup.centralizer (WbarM M V H : Set (Mbar M)),
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ WbarM M V H

end BigEpsStatements

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection.ModelRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigFConj_conj_mem_RQ [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) (e : ↥M)
    (he : (e : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M))) :
    ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
      ∃ r' ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∃ k ∈ Q,
        (e : G)⁻¹ * r * (e : G) = r' * k := by
  intro r hr
  have hrM : r ∈ M := by
    rw [← hc.normalizer_eq]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hr).2
  have hmem : ((⟨r, hrM⟩ : ↥M) : Mbar M) ∈ RbarM M V H :=
    ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  obtain ⟨y, hy, hye⟩ := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ he) _).mp hmem
  have hq : ((y : ↥M) : Mbar M) = ((e⁻¹ * ⟨r, hrM⟩ * e⁻¹⁻¹ : ↥M) : Mbar M) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hye
  have hmemN := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hq)
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (y : G)⁻¹ * ((e : G)⁻¹ * r * (e : G)), ?_,
    by group⟩
  rw [hc.hQ]
  simpa using hmemN

theorem bigFConj_comm_mem_of_le_sup [Finite G] {M V Q P H K : Subgroup G}
    (hc : MinCex M V Q P H) (hKP : K ≤ P)
    (hKR : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ x ∈ K, r * x * r⁻¹ ∈ K)
    (hFK : P ⊓ wOf V H ≤ K ⊔ V) :
    ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ f ∈ P ⊓ wOf V H,
      r * f * r⁻¹ * f⁻¹ ∈ K := by
  intro r hr f hf
  obtain ⟨k, hk, v, hv, rfl⟩ := exists_mul_of_mem_sup
    (fun k hk v hv => (hc.commute_of_mem_P (hKP hk) hv).symm) (hFK hf)
  have hrv : r * v * r⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 v hv
    rw [← this]
    group
  have e : r * (k * v) * r⁻¹ * (k * v)⁻¹ = (r * k * r⁻¹) * k⁻¹ := by
    calc r * (k * v) * r⁻¹ * (k * v)⁻¹
        = (r * k * r⁻¹) * (r * v * r⁻¹) * v⁻¹ * k⁻¹ := by group
      _ = (r * k * r⁻¹) * k⁻¹ := by rw [hrv]; group
  rw [e]
  exact K.mul_mem (hKR r hr k hk) (K.inv_mem hk)

theorem bigFConj_le_of_comm_mem [Finite G] {M V Q P H K : Subgroup G} (hc : MinCex M V Q P H)
    {n f : ℕ} (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (ha : a ≠ 0) (hn2 : 2 ≤ n)
    (hiff : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
      (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c))
    (hcomm : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ f ∈ P ⊓ wOf V H,
      r * f * r⁻¹ * f⁻¹ ∈ K) :
    P ⊓ wOf V H ≤ K := by
  have hWab : ∀ x ∈ wOf V H, ∀ y ∈ wOf V H, x * y = y * x := fun x hx y hy =>
    hc.wOf_isElemAbelian.comm hx hy
  have h1 : ∀ x, spForm a x = 0 → (∀ l : GaloisField 2 f, x ≠ l • a) → psiElt ψ x ∈ K := by
    intro x hx hxa
    obtain ⟨u, hau, hxu⟩ := exists_dual ha hx hxa
    obtain ⟨r, hr, hact⟩ := hroot x 1 hx hxa one_ne_zero
    have huF : psiElt ψ u ∈ P ⊓ wOf V H :=
      Subgroup.mem_inf.mpr ⟨(hiff u).mpr hau, psiElt_mem ψ u⟩
    have h2 := hcomm r hr _ huF
    have h3 : r * psiElt ψ u * r⁻¹ = psiElt ψ u * psiElt ψ x := by
      rw [hact u, hxu, one_mul, one_smul, psiElt_add]
    have h4 : psiElt ψ u * psiElt ψ x * (psiElt ψ u)⁻¹ = psiElt ψ x := by
      rw [hWab _ (psiElt_mem ψ u) _ (psiElt_mem ψ x)]
      group
    rw [h3, h4] at h2
    exact h2
  have h2 : ∀ x, spForm a x = 0 → psiElt ψ x ∈ K := by
    intro x hx
    by_cases hxa : ∀ l : GaloisField 2 f, x ≠ l • a
    · exact h1 x hx hxa
    · push Not at hxa
      obtain ⟨l, hl⟩ := hxa
      obtain ⟨x₁, -, hax₁, hx₁a⟩ := exists_perp_vec_not_smul hn2 ha
      have hx₂ : spForm a (x - x₁) = 0 := by rw [spForm_sub_right, hx, hax₁, sub_zero]
      have hx₂a : ∀ m : GaloisField 2 f, x - x₁ ≠ m • a := by
        intro m hm
        apply hx₁a (l - m)
        rw [sub_smul, ← hl, ← hm]
        abel
      have hsum : x = x₁ + (x - x₁) := by abel
      rw [hsum, psiElt_add]
      exact K.mul_mem (h1 x₁ hax₁ hx₁a) (h1 _ hx₂ hx₂a)
  intro z hz
  obtain ⟨hzP, hzW⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨x, rfl⟩ := exists_psiElt ψ hzW
  exact h2 x ((hiff x).mp hzP)

theorem bigFConj_R_centralizes {V H : Subgroup G} :
    ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ v ∈ V,
      r * v * r⁻¹ = v := fun r hr v hv => by
  have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 v hv
  rw [← this]
  group

theorem bigFConj_R_normalizes [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) :
    ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ f ∈ P ⊓ wOf V H,
      r * f * r⁻¹ ∈ P ⊓ wOf V H := fun r hr f hf => by
  have hrM : r ∈ M := by
    rw [← hc.normalizer_eq]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hr).2
  have hrN : r ∈ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G) :=
    mem_normalizer_inf (hc.M_le_normalizer_P hrM)
      (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H (Subgroup.mem_inf.mp hr).1))
  exact (Subgroup.mem_normalizer_iff.mp hrN f).mp hf

theorem bigFConj_conj_le_P [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {e : G}
    (he : e ∈ M) : conjSubgroup e (P ⊓ wOf V H) ≤ P := fun x hx => by
  have h1 : e⁻¹ * x * e ∈ P ⊓ wOf V H := mem_conjSubgroup.mp hx
  have h2 := (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P he) _).mp
    (Subgroup.mem_inf.mp h1).1
  have e1 : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
  rwa [e1] at h2

theorem bigFConj_conj_eq_of_le_sup [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    {n f : ℕ} (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (ha : a ≠ 0) (hn2 : 2 ≤ n)
    (hiff : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
      (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c))
    {e : G} (he : e ∈ M)
    (hRFe : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ x ∈ conjSubgroup e (P ⊓ wOf V H),
      r * x * r⁻¹ ∈ conjSubgroup e (P ⊓ wOf V H))
    (hle : conjSubgroup e (P ⊓ wOf V H) ≤ (P ⊓ wOf V H) ⊔ V) :
    conjSubgroup e (P ⊓ wOf V H) = P ⊓ wOf V H := by
  set F : Subgroup G := P ⊓ wOf V H
  set Fe : Subgroup G := conjSubgroup e F
  have heV : conjSubgroup e V = V :=
    mem_normalizer_iff_conjSubgroup_eq.mp (by rw [hc.normalizer_eq]; exact he)
  have hcard : Nat.card ↥(Fe ⊔ V) = Nat.card ↥(F ⊔ V) := by
    have : Fe ⊔ V = conjSubgroup e (F ⊔ V) := by
      rw [conjSubgroup_sup_eq_sup, heV]
    rw [this]
    exact card_conjSubgroup e _
  have heq : Fe ⊔ V = F ⊔ V :=
    Subgroup.eq_of_le_of_card_ge (sup_le hle le_sup_right) hcard.ge
  have hFK : F ≤ Fe ⊔ V := heq ▸ le_sup_left
  have hcomm := bigFConj_comm_mem_of_le_sup hc (bigFConj_conj_le_P hc he) hRFe hFK
  have hFFe : F ≤ Fe := bigFConj_le_of_comm_mem hc ψ ha hn2 hiff hroot hcomm
  exact (Subgroup.eq_of_le_of_card_ge hFFe (card_conjSubgroup e F).le).symm

theorem bigFConj_complement_data [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    {e : G} (he : e ∈ M)
    (hPD : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V ⊓ wOf V H) (hAP : V ⊓ wOf V H ≤ ⁅P, P⁆)
    (hRFe : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ x ∈ conjSubgroup e (P ⊓ wOf V H),
      r * x * r⁻¹ ∈ conjSubgroup e (P ⊓ wOf V H))
    (htrans : ∀ x ∈ P ⊓ wOf V H, x ∉ V → ∀ y ∈ P ⊓ wOf V H, y ∉ V →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∃ α ∈ V ⊓ wOf V H,
        r * x * r⁻¹ = y * α)
    (hnle : ¬ conjSubgroup e (P ⊓ wOf V H) ≤ (P ⊓ wOf V H) ⊔ V) :
    conjSubgroup e (P ⊓ wOf V H) ⊓ wOf V H = V ⊓ wOf V H ∧
      barOf V H (conjSubgroup e (P ⊓ wOf V H)) ⊓ barOf V H V = ⊥ := by
  set F : Subgroup G := P ⊓ wOf V H
  have hFW : F ≤ wOf V H := inf_le_right
  have hRV := bigFConj_R_centralizes (V := V) (H := H)
  have hRF := bigFConj_R_normalizes hc
  have hS5 := bigDirect_inf_sup_le hc he hRV hRF hRFe htrans hnle
  have hVnorm : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv => by
    have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hg
    exact (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  have hcomm_le : ⁅P, P⁆ ≤ V ⊓ wOf V H := Subgroup.commutator_le.mpr hPD
  have hAnorm : ∀ g ∈ M, ∀ x ∈ V ⊓ wOf V H, g * x * g⁻¹ ∈ V ⊓ wOf V H := fun g hg x hx =>
    hcomm_le (bigDirect_conj_mem_commutator hc.M_le_normalizer_P g hg x (hAP hx))
  have hAF : V ⊓ wOf V H ≤ F := inf_le_inf_right _ hc.V_le_P
  have hFeP : conjSubgroup e F ≤ P := bigFConj_conj_le_P hc he
  have hFeW : conjSubgroup e F ⊓ wOf V H = V ⊓ wOf V H := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxFe, hxW⟩ := Subgroup.mem_inf.mp hx
      have hxF : x ∈ F := Subgroup.mem_inf.mpr ⟨hFeP hxFe, hxW⟩
      have hxV : x ∈ V := hS5 (Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_sup_left hxF, Subgroup.mem_sup_left hxFe⟩)
      exact Subgroup.mem_inf.mpr ⟨hxV, hxW⟩
    · intro x hx
      have h1 : e⁻¹ * x * e ∈ V ⊓ wOf V H := by
        have := hAnorm e⁻¹ (M.inv_mem he) x hx
        simpa using this
      exact Subgroup.mem_inf.mpr ⟨mem_conjSubgroup.mpr (hAF h1), (Subgroup.mem_inf.mp hx).2⟩
  have hFeV : conjSubgroup e F ⊓ V ≤ wOf V H := by
    intro x hx
    obtain ⟨hxFe, hxV⟩ := Subgroup.mem_inf.mp hx
    have h1 : e⁻¹ * x * e ∈ F := mem_conjSubgroup.mp hxFe
    have h2 : e⁻¹ * x * e ∈ V := by
      have := hVnorm e⁻¹ (M.inv_mem he) x hxV
      simpa using this
    have h3 : e⁻¹ * x * e ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨h2, hFW h1⟩
    have h4 := hAnorm e he _ h3
    have e1 : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
    rw [e1] at h4
    exact (Subgroup.mem_inf.mp h4).2
  refine ⟨hFeW, ?_⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨x₁, hx₁, rfl⟩ := mem_barOf_iff.mp hy1
  obtain ⟨x₂, hx₂, hx₂y⟩ := mem_barOf_iff.mp hy2
  have h1 : piBar V H (x₂⁻¹ * x₁) = 1 := by
    rw [map_mul, map_inv, hx₂y, inv_mul_cancel]
  have hw' : ((x₂⁻¹ * x₁ : ↥H) : G) ∈ wOf V H := (piBar_eq_one_iff _).mp h1
  have hw'P : ((x₂⁻¹ * x₁ : ↥H) : G) ∈ P := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact P.mul_mem (P.inv_mem (hc.V_le_P hx₂)) (hFeP hx₁)
  have hw'F : ((x₂⁻¹ * x₁ : ↥H) : G) ∈ F := Subgroup.mem_inf.mpr ⟨hw'P, hw'⟩
  have hx₁' : (x₁ : G) ∈ F ⊔ V := by
    have e1 : (x₁ : G) = (x₂ : G) * ((x₂⁻¹ * x₁ : ↥H) : G) := by simp
    rw [e1]
    exact (F ⊔ V).mul_mem (Subgroup.mem_sup_right hx₂) (Subgroup.mem_sup_left hw'F)
  have hx₁V : (x₁ : G) ∈ V := hS5 (Subgroup.mem_inf.mpr ⟨hx₁', Subgroup.mem_sup_left hx₁⟩)
  have hx₁W : (x₁ : G) ∈ wOf V H := hFeV (Subgroup.mem_inf.mpr ⟨hx₁, hx₁V⟩)
  rw [Subgroup.mem_bot]
  exact (piBar_eq_one_iff _).mpr hx₁W

theorem bigEpsFConjStatement_direct (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hLoc : BigPLocalStatement)
    (hPQ : BigPQCommStatement) (hPD : BigPDerivedStatement) (hroot : BigRootElementStatement)
    : BigEpsFConjStatement := by
  have hcomp := @spNoInvCompGeneralStatement_holds
  intro G _ _ M V Q P H hH e he
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hZ' : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ'
  obtain ⟨n, f, Φ, ψ, hn2, hf, hNat, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ'
  have hcfg : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hNat, hpoint⟩
  obtain ⟨hiff, hRbar, hxOf, -⟩ := hLoc G M V Q P H hH hZ' hcP hf Φ ψ hcfg a T ha hT hTV
  have hroot' := hroot G M V Q P H hH hZ' hcP hf Φ ψ hcfg a T ha hT hTV
  obtain ⟨hPQ1, -⟩ := hPQ G M V Q P H hH
  obtain ⟨hPD1, hPD2⟩ := hPD G M V Q P H hH
  have hiff' : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0 := hiff
  have hroot'' : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := hroot'
  have hRQ := bigFConj_conj_mem_RQ hc e he
  have hRFe := bigDirect_conj_invariant hRQ (inf_le_left : P ⊓ wOf V H ≤ P)
    (inf_le_inf_right _ hc.V_le_P) hPQ1 (bigFConj_R_normalizes hc)
  by_cases hle : conjSubgroup (e : G) (P ⊓ wOf V H) ≤ (P ⊓ wOf V H) ⊔ V
  · exact bigFConj_conj_eq_of_le_sup hc ψ ha hn2 hiff' hroot'' e.2 hRFe hle
  · exfalso
    have hq4 : 4 ≤ qBar V H := hH.q_big
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hf
      omega
    have hqK : Nat.card (GaloisField 2 f) = qBar V H := by
      rw [GaloisField.card 2 f hf0, hf]
    have hAcard : Nat.card ↥(V ⊓ wOf V H) = Nat.card (GaloisField 2 f) := by
      rw [hH.module, hqK]
    have hFcard : Nat.card ↥(P ⊓ wOf V H) = Nat.card (GaloisField 2 f) ^ (2 * n - 1) :=
      bigDirect_card_inf_wOf ψ ha hiff'
    have hAV : ∀ l : GaloisField 2 f, psiElt ψ (l • a) ∈ V := by
      intro l
      by_cases hl : l = 0
      · rw [hl, zero_smul, psiElt_zero]
        exact V.one_mem
      · have hla : l • a ≠ 0 := smul_ne_zero hl ha
        have hTla : CaseM.IsTransGroup (l • a) T :=
          CaseM.IsTransGroup.of_smul (v := l • a) (l := l⁻¹) (inv_ne_zero hl)
            (by rwa [inv_smul_smul₀ hl])
        exact hpoint (l • a) T hla hTla hTV
    have htrans := bigDirect_htrans ψ ha hiff' hAV hroot''
    obtain ⟨hFeW, hbar⟩ := bigFConj_complement_data hc e.2 hPD1 hPD2 hRFe htrans hle
    have hFeP := bigFConj_conj_le_P hc e.2 (P := P) (V := V) (H := H) (Q := Q)
    have hFecard : Nat.card ↥(conjSubgroup (e : G) (P ⊓ wOf V H)) =
        Nat.card (GaloisField 2 f) ^ (2 * n - 1) := by
      rw [card_conjSubgroup, hFcard]
    have hPH : P ≤ H := hc.PleH
    have hFeH : conjSubgroup (e : G) (P ⊓ wOf V H) ≤ H := hFeP.trans hPH
    have hcardbar : Nat.card ↥(barOf V H (conjSubgroup (e : G) (P ⊓ wOf V H))) *
        Nat.card ↥(barOf V H V) = Nat.card ↥(spRad a) := by
      have h1 := twb_card_barOf_mul (V := V) (H := H)
        (K := conjSubgroup (e : G) (P ⊓ wOf V H)) hFeH
      rw [hFeW, hAcard, hFecard] at h1
      have h2 : Nat.card ↥(barOf V H V) = Nat.card (GaloisField 2 f) := hqK.symm
      have h3 : Nat.card ↥(spRad a) = Nat.card (GaloisField 2 f) ^ (2 * n - 1) := by
        rw [spRad_card_eq_ker ha, natCard_ker_spFormL ha]
      rw [h2, h3]
      exact h1
    obtain ⟨S, hSle, hsup, hinf, hSmem⟩ := bigDirect_transport Φ ha hT hTV hRbar hFeP
      (by rw [hxOf]; exact hPH) hbar hcardbar
    have hinv := bigDirect_invariant hc Φ ψ hNat ha hT hroot'' hRFe hSle hSmem
    exact hcomp hn2 (by rw [hqK]; omega) ha hT hSle hsup hinf hinv

theorem bigEpsFConjStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigEpsFConjStatement :=
  bigEpsFConjStatement_direct hZ hN hIW bigPLocalStatement_holds
    (bigPQCommStatement_of_natural hZ hN hIW hγ) (bigPDerivedStatement_of_natural hZ hN hIW)
    (bigRootElement_holds bigPLocalStatement_holds)

theorem bigLe_mk_comm {M Q : Subgroup G} (hQ : Q = inSubgroup (pCore 2) M) {x y : ↥M}
    (h : ⁅(x : G), (y : G)⁆ ∈ Q) :
    (x : Mbar M) * (y : Mbar M) = (y : Mbar M) * (x : Mbar M) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
    Subgroup.mem_subgroupOf]
  have e : (((x * y) / (y * x) : ↥M) : G) = ⁅(x : G), (y : G)⁆ := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  rw [e, ← hQ]
  exact h

theorem bigLe_Wbar_rep [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H) {t : Mbar M}
    (ht : t ∈ WbarM M V H) : ∃ b : ↥M, (b : G) ∈ B ∧ (b : Mbar M) = t := by
  obtain ⟨w, hwW, rfl⟩ := mem_WbarM_iff.mp ht
  have hwFB : (w : G) ∈ (P ⊓ wOf V H) ⊔ B := by
    rw [hPB]
    exact hwW
  obtain ⟨p, hp, b, hb, hpb⟩ := exists_mul_of_mem_sup
    (fun p hp b hb => hc.wOf_isElemAbelian.comm (Subgroup.mem_inf.mp hp).2 (hBW hb)) hwFB
  have hpM : p ∈ M := bigAlpha_P_le_M hc (Subgroup.mem_inf.mp hp).1
  have hbM : b ∈ M := wOf_le_M_of_minCex hc (hBW hb)
  refine ⟨⟨b, hbM⟩, hb, ?_⟩
  have hpQ : p ∈ inSubgroup (pCore 2) M := by
    rw [← hc.hQ]
    exact hc.P_le_Q (Subgroup.mem_inf.mp hp).1
  have hp1 : ((⟨p, hpM⟩ : ↥M) : Mbar M) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hpQ
  have hprod : w = ⟨p, hpM⟩ * ⟨b, hbM⟩ := Subtype.ext hpb
  rw [hprod, QuotientGroup.mk_mul, hp1, one_mul]

theorem bigLe_Wbar_sq [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {t : Mbar M}
    (ht : t ∈ WbarM M V H) : t * t = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_WbarM_iff.mp ht
  have hw2 : (w : G) * (w : G) = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hw
  have : w * w = 1 := Subtype.ext hw2
  rw [← QuotientGroup.mk_mul, this, QuotientGroup.mk_one]

theorem bigLe_comm_conj_le [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hCP : Subgroup.centralizer (P : Set G) = V) {e : G} (he : e ∈ M)
    (hFe : conjSubgroup e (P ⊓ wOf V H) = P ⊓ wOf V H) :
    ⁅B, conjSubgroup e B⁆ ≤ V := by
  have hWab : ∀ x ∈ wOf V H, ∀ y ∈ wOf V H, x * y = y * x := fun x hx y hy =>
    hc.wOf_isElemAbelian.comm hx hy
  have hFinv : ∀ f ∈ P ⊓ wOf V H, e⁻¹ * f * e ∈ P ⊓ wOf V H := fun f hf => by
    rw [← mem_conjSubgroup, hFe]
    exact hf
  have hFBe : ∀ f ∈ P ⊓ wOf V H, ∀ y ∈ conjSubgroup e B, ⁅f, y⁆ = 1 := by
    intro f hf y hy
    have hb : e⁻¹ * y * e ∈ B := mem_conjSubgroup.mp hy
    have e1 : ⁅f, y⁆ = e * ⁅e⁻¹ * f * e, e⁻¹ * y * e⁆ * e⁻¹ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅e⁻¹ * f * e, e⁻¹ * y * e⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hWab _ (Subgroup.mem_inf.mp (hFinv f hf)).2 _ (hBW hb))
    rw [e1, e2]
    group
  have hPB : ⁅P, B⁆ ≤ P ⊓ wOf V H :=
    Subgroup.commutator_le.mpr fun p hp b hb => bigGe_comm_mem hc hBW hp hb
  have hPBe : ∀ p ∈ P, ∀ y ∈ conjSubgroup e B, ⁅p, y⁆ ∈ P ⊓ wOf V H := by
    intro p hp y hy
    have hb : e⁻¹ * y * e ∈ B := mem_conjSubgroup.mp hy
    have hp' : e⁻¹ * p * e ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P (M.inv_mem he)) p).mp hp
      simpa using this
    have h1 := bigGe_comm_mem hc hBW hp' hb
    have e1 : ⁅p, y⁆ = e * ⁅e⁻¹ * p * e, e⁻¹ * y * e⁆ * e⁻¹ := by
      simp only [commutatorElement_def]
      group
    have h2 : e * ⁅e⁻¹ * p * e, e⁻¹ * y * e⁆ * e⁻¹ ∈ conjSubgroup e (P ⊓ wOf V H) := by
      rw [mem_conjSubgroup]
      have e2 : e⁻¹ * (e * ⁅e⁻¹ * p * e, e⁻¹ * y * e⁆ * e⁻¹) * e = ⁅e⁻¹ * p * e, e⁻¹ * y * e⁆ := by
        group
      rw [e2]
      exact h1
    rw [e1]
    rwa [hFe] at h2
  have hBeP : ⁅conjSubgroup e B, P⁆ ≤ P ⊓ wOf V H :=
    Subgroup.commutator_le.mpr fun y hy p hp => by
      rw [← commutatorElement_inv]
      exact (P ⊓ wOf V H).inv_mem (hPBe p hp y hy)
  have h1 : ⁅⁅conjSubgroup e B, P⁆, B⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun z hz b hb => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hWab _ (Subgroup.mem_inf.mp (hBeP hz)).2 _ (hBW hb))
  have h2 : ⁅⁅P, B⁆, conjSubgroup e B⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun z hz y hy => ?_
    rw [Subgroup.mem_bot]
    exact hFBe z (hPB hz) y hy
  have h3 : ⁅⁅B, conjSubgroup e B⁆, P⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  intro z hz
  rw [← hCP, Subgroup.mem_centralizer_iff]
  intro p hp
  have h4 : ⁅z, p⁆ ∈ (⊥ : Subgroup G) := h3 ▸ Subgroup.commutator_mem_commutator hz hp
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h4)).symm

theorem bigLe_mem_normalizer_Wbar [Finite G] {M V Q P H B : Subgroup G}
    (hc : MinCex M V Q P H) (hBW : B ≤ wOf V H) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hWR : WbarM M V H ≤ Subgroup.centralizer (RbarM M V H : Set (Mbar M)))
    (hF : ∀ x ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)) ⊓
        Subgroup.centralizer (WbarM M V H : Set (Mbar M)),
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ WbarM M V H)
    {e : ↥M} (he : (e : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)))
    (hBB : ⁅B, conjSubgroup (e : G) B⁆ ≤ V) :
    (e : Mbar M) ∈ Subgroup.normalizer (WbarM M V H : Set (Mbar M)) := by
  haveI : Finite (Mbar M) := inferInstance
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine conjSubgroup_eq_of_le fun z hz => ?_
  have ht : (e : Mbar M)⁻¹ * z * (e : Mbar M) ∈ WbarM M V H := mem_conjSubgroup.mp hz
  obtain ⟨b, hbB, hbt⟩ := bigLe_Wbar_rep hc hBW hPB ht
  have hbW : (b : Mbar M) ∈ WbarM M V H := by
    rw [hbt]
    exact ht
  have hzeq : z = (e : Mbar M) * (b : Mbar M) * (e : Mbar M)⁻¹ := by
    rw [hbt]
    group
  set y : ↥M := e * b * e⁻¹ with hy
  have hyM : (y : Mbar M) = (e : Mbar M) * (b : Mbar M) * (e : Mbar M)⁻¹ := by
    rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hzeq, ← hyM]
  have hyB : (y : G) ∈ conjSubgroup (e : G) B := by
    rw [mem_conjSubgroup]
    have e1 : (e : G)⁻¹ * (y : G) * (e : G) = (b : G) := by
      rw [hy]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact hbB
  refine hF _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩) ⟨1, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hρ := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ he) s).mp hs
    have hcomm := Subgroup.mem_centralizer_iff.mp (hWR hbW) _ hρ
    rw [hyM]
    calc s * ((e : Mbar M) * (b : Mbar M) * (e : Mbar M)⁻¹)
        = (e : Mbar M) * (((e : Mbar M)⁻¹ * s * (e : Mbar M)⁻¹⁻¹) * (b : Mbar M)) *
            (e : Mbar M)⁻¹ := by group
      _ = (e : Mbar M) * ((b : Mbar M) * ((e : Mbar M)⁻¹ * s * (e : Mbar M)⁻¹⁻¹)) *
            (e : Mbar M)⁻¹ := by rw [hcomm]
      _ = ((e : Mbar M) * (b : Mbar M) * (e : Mbar M)⁻¹) * s := by group
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨b', hb'B, rfl⟩ := bigLe_Wbar_rep hc hBW hPB hs
    refine bigLe_mk_comm hc.hQ ?_
    exact hc.P_le_Q (hc.V_le_P (hBB (Subgroup.commutator_mem_commutator hb'B hyB)))
  · rw [pow_one, pow_two, hyM]
    calc ((e : Mbar M) * (b : Mbar M) * (e : Mbar M)⁻¹) *
          ((e : Mbar M) * (b : Mbar M) * (e : Mbar M)⁻¹)
        = (e : Mbar M) * ((b : Mbar M) * (b : Mbar M)) * (e : Mbar M)⁻¹ := by group
      _ = 1 := by rw [bigLe_Wbar_sq hc hbW]; group

theorem bigEpsilonNormalizerLeStatement_of_faithfulTwo (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement)
    (hF : BigEpsilonFaithfulTwoStatement) : BigEpsilonNormalizerLeStatement := by
  intro G _ _ M V Q P H hH x hx
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨B, hBW, -, hPB, -⟩ := bigBStatement_of_local hZ hN hIW G M V Q P H hH
  have hCP : Subgroup.centralizer (P : Set G) = V :=
    (bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP).2.2
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
  have hFe := bigEpsFConjStatement_of_natural hZ hN hIW hγ G M V Q P H hH e hx
  exact bigLe_mem_normalizer_Wbar hc hBW hPB (bigWbarCentralizesStatement_holds G M V Q P H hH)
    (hF G M V Q P H hH) hx (bigLe_comm_conj_le hc hBW hCP e.2 hFe)

end CFSG.RankThree.GF2n.Tim79a
