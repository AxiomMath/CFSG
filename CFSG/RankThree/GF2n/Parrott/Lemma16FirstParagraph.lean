module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.QuadraticV
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.GroupTheory.Extraspecial2PG
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.SylowIntersectionControl.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.RankThree.GF2n.Parrott.Parrott77Lemma6
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem conj_mem_J_of_mem_H {s j : G} (hsH : s ∈ H z) (hj : j ∈ J z) : s * j * s⁻¹ ∈ J z := by
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  exact (Subgroup.mem_normalizer_iff.mp (hHN hsH) j).mp hj

theorem exists_jconj_commute_of_orderOf_three (hJp : IsPGroup 2 (J z)) {s x₀ : G} (hsH : s ∈ H z)
    (hs3 : orderOf s = 3) {j₀ : G} (hj₀ : j₀ ∈ J z) (hsx : s * x₀ * s⁻¹ = j₀ * x₀ * j₀⁻¹) :
    ∃ j ∈ J z, s * (j * x₀ * j⁻¹) = (j * x₀ * j⁻¹) * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J' : Subgroup (ConjAct G) := (J z).map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
  have hJ'p : IsPGroup 2 J' := hJp.map _
  have hmem : ∀ y : G, y ∈ MulAction.orbit J' x₀ ↔ ∃ j ∈ J z, j * x₀ * j⁻¹ = y := by
    intro y
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hc
      exact ⟨j, hj, by
        change j * x₀ * j⁻¹ = ConjAct.toConjAct j • x₀
        rw [ConjAct.toConjAct_smul]⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨ConjAct.toConjAct j, Subgroup.mem_map.mpr ⟨j, hj, rfl⟩⟩, ?_⟩
      change ConjAct.toConjAct j • x₀ = j * x₀ * j⁻¹
      rw [ConjAct.toConjAct_smul]
  obtain ⟨n, hn⟩ := hJ'p.card_orbit x₀
  have hstep : ∀ y ∈ MulAction.orbit J' x₀, s * y * s⁻¹ ∈ MulAction.orbit J' x₀ := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := (hmem y).mp hy
    refine (hmem _).mpr ⟨s * j * s⁻¹ * j₀, (J z).mul_mem (conj_mem_J_of_mem_H hsH hj) hj₀, ?_⟩
    calc (s * j * s⁻¹ * j₀) * x₀ * (s * j * s⁻¹ * j₀)⁻¹
        = (s * j * s⁻¹) * (j₀ * x₀ * j₀⁻¹) * (s * j * s⁻¹)⁻¹ := by group
      _ = (s * j * s⁻¹) * (s * x₀ * s⁻¹) * (s * j * s⁻¹)⁻¹ := by rw [hsx]
      _ = s * (j * x₀ * j⁻¹) * s⁻¹ := by group
  have hs3' : s * s * s = 1 := by
    rw [← pow_three', ← hs3]
    exact pow_orderOf_eq_one s
  have hsinv : s⁻¹ = s * s := (eq_inv_of_mul_eq_one_left hs3').symm
  have hsinv2 : s⁻¹ * s⁻¹ = s := by
    calc s⁻¹ * s⁻¹ = (s * s)⁻¹ := by group
      _ = s := by rw [← hsinv, inv_inv]
  let O := MulAction.orbit J' x₀
  let f : Equiv.Perm O :=
    { toFun := fun y => ⟨s * y * s⁻¹, hstep y y.2⟩
      invFun := fun y => ⟨s⁻¹ * y * s, by
        have h1 := hstep _ (hstep y y.2)
        have h2 : s * (s * (y : G) * s⁻¹) * s⁻¹ = s⁻¹ * y * s := by
          calc s * (s * (y : G) * s⁻¹) * s⁻¹ = (s * s) * y * (s⁻¹ * s⁻¹) := by group
            _ = s⁻¹ * y * s := by rw [← hsinv, hsinv2]
        rwa [h2] at h1⟩
      left_inv := fun y => Subtype.ext (by
        change s⁻¹ * (s * (y : G) * s⁻¹) * s = y
        group)
      right_inv := fun y => Subtype.ext (by
        change s * (s⁻¹ * (y : G) * s) * s⁻¹ = y
        group) }
  have hf3 : f ^ 3 ^ 1 = 1 := by
    have h3 : f ^ 3 ^ 1 = f * f * f := by rw [pow_one, pow_three']
    rw [h3]
    refine Equiv.ext fun y => Subtype.ext ?_
    change s * (s * (s * (y : G) * s⁻¹) * s⁻¹) * s⁻¹ = (y : G)
    calc s * (s * (s * (y : G) * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * y * (s * s * s)⁻¹ := by group
      _ = y := by rw [hs3']; group
  have : Fintype O := Fintype.ofFinite _
  have hnd : ¬ 3 ∣ Fintype.card O := by
    rw [← Nat.card_eq_fintype_card]
    change ¬ 3 ∣ Nat.card ↥(MulAction.orbit J' x₀)
    rw [hn]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  obtain ⟨⟨x, hxO⟩, hfx⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hf3
  obtain ⟨j, hj, hjx⟩ := (hmem x).mp hxO
  refine ⟨j, hj, ?_⟩
  have h1 : s * x * s⁻¹ = x := congrArg Subtype.val hfx
  rw [hjx]
  calc s * x = (s * x * s⁻¹) * s := by group
    _ = x * s := by rw [h1]

theorem isElemAbelian_CJ_of_isConj
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)
    (hz2 : orderOf z = 2) (hJ' : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) (hJp : IsPGroup 2 (J z))
    (hsqJ : ∀ a ∈ J z, a * a ∈ Subgroup.zpowers z)
    (hPH : ∀ g : G, g * z * g⁻¹ ∈ (P_H D).map (H z).subtype → g * z * g⁻¹ = z)
    {x : G} (hxH : x ∈ H z) (hxJ : x ∉ J z) (hconj : IsConj z x) :
    IsElemAbelian 2 (CJ z x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz_or : ∀ {y : G}, y ∈ Subgroup.zpowers z → y = 1 ∨ y = z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← zpow_mod_orderOf, hz2]
      exact_mod_cast (by rw [h0, zpow_zero] : z ^ (k % 2) = 1)
    · right
      rw [← zpow_mod_orderOf, hz2]
      exact_mod_cast (by rw [h1, zpow_one] : z ^ (k % 2) = z)
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hcommP : ∀ a ∈ H z, ∀ b ∈ H z, ⁅a, b⁆ ∈ (P_H D).map (H z).subtype := by
    intro a ha b hb
    have hidx := index_P_H D
    refine ⟨⁅(⟨a, ha⟩ : ↥(H z)), ⟨b, hb⟩⁆, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    tauto
  have hsqP : ∀ h ∈ H z, h * h ∈ (P_H D).map (H z).subtype := by
    intro h hh
    exact ⟨⟨h, hh⟩ * ⟨h, hh⟩, Subgroup.mul_self_mem_of_index_two (index_P_H D) _, rfl⟩
  by_contra hne
  have hzS : (∃ a ∈ CJ z x, ∃ b ∈ CJ z x, a * b * a⁻¹ * b⁻¹ = z) ∨ ∃ a ∈ CJ z x, a * a = z := by
    by_cases hc : ∀ a ∈ CJ z x, ∀ b ∈ CJ z x, a * b = b * a
    · right
      by_contra hsq
      push Not at hsq
      apply hne
      refine ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun a ha => ?_⟩
      rw [pow_two]
      rcases hz_or (hsqJ a (mem_CJ.mp ha).2) with h1 | h1
      · exact h1
      · exact absurd h1 (hsq a ha)
    · left
      push Not at hc
      obtain ⟨a, ha, b, hb, hab⟩ := hc
      refine ⟨a, ha, b, hb, ?_⟩
      have hcomm : ⁅a, b⁆ ∈ Subgroup.zpowers z :=
        hJ' ▸ Subgroup.commutator_mem_commutator (mem_CJ.mp ha).2 (mem_CJ.mp hb).2
      rcases hz_or hcomm with h1 | h1
      · exfalso
        apply hab
        rw [commutatorElement_def] at h1
        calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
          _ = b * a := by rw [h1, one_mul]
      · rwa [commutatorElement_def] at h1
  let M : Subgroup G := H z ⊓ Subgroup.centralizer ({x} : Set G)
  have hCJM : CJ z x ≤ M := fun y hy =>
    ⟨J_le_H (mem_CJ.mp hy).2, (mem_CJ.mp hy).1⟩
  have hCJp : IsPGroup 2 (CJ z x) := hJp.to_le inf_le_right
  obtain ⟨Q, hCJQ⟩ := (hCJp.comap_subtype : IsPGroup 2 ((CJ z x).subgroupOf M)).exists_le_sylow
  let X : Subgroup G := (Q : Subgroup ↥M).map M.subtype
  have hX : IsSylowOf 2 X M := ⟨Q, rfl⟩
  have hCJX : CJ z x ≤ X := by
    calc CJ z x = ((CJ z x).subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hCJM).symm
      _ ≤ (Q : Subgroup ↥M).map M.subtype := Subgroup.map_mono hCJQ
  have hXH : X ≤ H z := hX.le.trans inf_le_left
  have hNX : ∀ g ∈ Subgroup.centralizer ({x} : Set G),
      g ∈ Subgroup.normalizer (X : Set G) → IsPGroup 2 (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer ({z} : Set G) := by
    intro g _ hgN _
    have hgX : ∀ w ∈ X, g * w * g⁻¹ ∈ X := fun w hw => (Subgroup.mem_normalizer_iff.mp hgN w).mp hw
    have hgz : g * z * g⁻¹ = z := by
      apply hPH
      rcases hzS with ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, haa⟩
      · have heq : g * z * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
          rw [commutatorElement_def]
          calc g * z * g⁻¹ = g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by rw [hab]
            _ = g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
        rw [heq]
        exact hcommP _ (hXH (hgX a (hCJX ha))) _ (hXH (hgX b (hCJX hb)))
      · have heq : g * z * g⁻¹ = (g * a * g⁻¹) * (g * a * g⁻¹) := by
          calc g * z * g⁻¹ = g * (a * a) * g⁻¹ := by rw [haa]
            _ = (g * a * g⁻¹) * (g * a * g⁻¹) := by group
        rw [heq]
        exact hsqP _ (hXH (hgX a (hCJX ha)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  have hJx : ¬ J z ≤ Subgroup.centralizer ({x} : Set G) := by
    intro hle
    apply hxJ
    refine hCJ ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hdvd : 2 ∣ (Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)).relIndex (Subgroup.centralizer ({z} : Set G)) :=
    dvd_relIndex_inf_centralizer_of_normal_pGroup (p := 2) (H := H z) (J := J z)
      (J_le_H (z := z)) hHN hJp hJx
  exact not_isConj_of_isSylowOf_inf_centralizer (p := 2) (z := z) (y := x) (K := X) hX hNX hdvd
    hconj

theorem uvt_mul_sigma1_mul_sigma2_inv :
    u * v * t * (sigma1 * sigma2⁻¹) = sigma1 * sigma2⁻¹ * (u * v * t) := by
  have hu2 : u⁻¹ = u := inv_eq_of_mul_eq_one_left u_sq
  have hus2 : u * sigma2 * u⁻¹ = sigma1 := by
    rw [← sigma1_conj_u]
    calc u * (u * sigma1 * u⁻¹) * u⁻¹ = (u * u) * sigma1 * (u * u)⁻¹ := by group
      _ = sigma1 := by rw [u_sq]; group
  have ht : t * (sigma1 * sigma2⁻¹) * t⁻¹ = sigma1 * sigma2⁻¹ := by
    have h2 : t * sigma2⁻¹ = sigma2⁻¹ * t := by
      calc t * sigma2⁻¹ = sigma2⁻¹ * (sigma2 * t) * sigma2⁻¹ := by group
        _ = sigma2⁻¹ * (t * sigma2) * sigma2⁻¹ := by rw [t_commute_sigma2]
        _ = sigma2⁻¹ * t := by group
    calc t * (sigma1 * sigma2⁻¹) * t⁻¹ = (t * sigma1) * sigma2⁻¹ * t⁻¹ := by group
      _ = sigma1 * (t * sigma2⁻¹) * t⁻¹ := by rw [t_commute_sigma1]; group
      _ = sigma1 * sigma2⁻¹ := by rw [h2]; group
  have hv : v * (sigma1 * sigma2⁻¹) * v⁻¹ = sigma1⁻¹ * sigma2 := by
    calc v * (sigma1 * sigma2⁻¹) * v⁻¹ = (v * sigma1 * v⁻¹) * (v * sigma2 * v⁻¹)⁻¹ := by group
      _ = sigma1⁻¹ * sigma2 := by rw [sigma1_conj_v, sigma2_conj_v, inv_inv]
  have hu : u * (sigma1⁻¹ * sigma2) * u⁻¹ = sigma1 * sigma2⁻¹ := by
    have hc : sigma2⁻¹ * sigma1 = sigma1 * sigma2⁻¹ := by
      calc sigma2⁻¹ * sigma1 = sigma2⁻¹ * (sigma1 * sigma2) * sigma2⁻¹ := by group
        _ = sigma2⁻¹ * (sigma2 * sigma1) * sigma2⁻¹ := by rw [sigma1_commute_sigma2]
        _ = sigma1 * sigma2⁻¹ := by group
    calc u * (sigma1⁻¹ * sigma2) * u⁻¹ = (u * sigma1 * u⁻¹)⁻¹ * (u * sigma2 * u⁻¹) := by group
      _ = sigma2⁻¹ * sigma1 := by rw [sigma1_conj_u, hus2]
      _ = sigma1 * sigma2⁻¹ := hc
  calc u * v * t * (sigma1 * sigma2⁻¹)
      = u * (v * (t * (sigma1 * sigma2⁻¹) * t⁻¹) * v⁻¹) * u⁻¹ * (u * v * t) := by group
    _ = sigma1 * sigma2⁻¹ * (u * v * t) := by rw [ht, hv, hu]

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_conj_mem_uvtJ_centralizer_of_conj_mem_vJ
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z)
    {σ : ↥(H z)} (hσ3 : orderOf σ = 3)
    (hqσ : qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹)
    (hPH : ∀ g : G, g * z * g⁻¹ ∈ (P_H D).map (H z).subtype → g * z * g⁻¹ = z)
    (hcls : ∃ x₁ x₂ : G, ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      IsElemAbelian 2 (CJ z x) → ∃ j ∈ J z, j * x * j⁻¹ = x₁ ∨ j * x * j⁻¹ = x₂)
    (hstar : ∀ g : G, CFSG.conjugate (Subgroup.zpowers (σ : G)) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (Subgroup.zpowers (σ : G)) g =
        CFSG.conjugate (Subgroup.zpowers (σ : G)) h)
    (hNP : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G),
      ∃ h ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G) ⊓ H z,
        ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G), h * c = n) :
    ∀ x' : G, cosetJ (z := z) (vH D) x' → orderOf x' = 2 → (∃ g : G, g * z * g⁻¹ = x') →
      ∃ x : G, cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2 ∧
        x ∈ Subgroup.centralizer ({(σ : G)} : Set G) ∧ IsElemAbelian 2 (CJ z x) ∧
        ∃ c ∈ Subgroup.centralizer ({(σ : G)} : Set G), c * z * c⁻¹ = x := by
  classical
  intro x' hx' hx'2 ⟨g, hg⟩
  obtain ⟨hz2, hJ', hCJ, hJp, hsqJ⟩ : orderOf z = 2 ∧ ⁅J z, J z⁆ = Subgroup.zpowers z ∧
      H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z ∧ IsPGroup 2 (J z) ∧
      ∀ a ∈ J z, a * a ∈ Subgroup.zpowers z := by
    rcases h with h | h
    · exact ⟨h.1, h.2.2.1, h.2.2.2.1, isPGroup_J h, fun a ha => sq_mem_zpowers_z h ha⟩
    · refine ⟨orderOf_z_A h, h.commutator, h.centralizer_le, isPGroup_J_A h, fun a ha => ?_⟩
      have hsq := IsExtraspecial2.pow_two_mem_center h.extraspecial ⟨a, ha⟩
      have hmap : a * a ∈ (Subgroup.center ↥(J z)).map (J z).subtype :=
        ⟨⟨a, ha⟩ ^ 2, hsq, by simp [pow_two]⟩
      rw [← h.extraspecial.2.1, h.commutator] at hmap
      exact hmap
  set s : G := (σ : G) with hs_def
  have hsH : s ∈ H z := σ.2
  have hs3 : orderOf s = 3 := by rw [hs_def, Subgroup.orderOf_coe]; exact hσ3
  have hcos : ∀ (r : ↥(H z)) (y : ↥(H z)), qH D y = qH D r → cosetJ (z := z) r (y : G) := by
    intro r y hy
    refine ⟨((r⁻¹ * y : ↥(H z)) : G), ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr (by rw [map_mul, map_inv, hy,
      inv_mul_cancel]))
  have hcos_qH : ∀ {r : ↥(H z)} {y : G} (hy : cosetJ (z := z) r y), ∃ hyH : y ∈ H z,
      qH D ⟨y, hyH⟩ = qH D r := by
    intro r y hy
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨(H z).mul_mem r.2 (J_le_H hj), ?_⟩
    have hjq : qH D ⟨j, J_le_H hj⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    have : (⟨(r : G) * j, (H z).mul_mem r.2 (J_le_H hj)⟩ : ↥(H z)) = r * ⟨j, J_le_H hj⟩ := rfl
    rw [this, map_mul, hjq, mul_one]
  obtain ⟨hx'H, hqx'⟩ := hcos_qH hx'
  let b : ↥(H z) := betaH D
  let x₀ : ↥(H z) := b * ⟨x', hx'H⟩ * b⁻¹
  have hx₀ : cosetJ (z := z) (uH D * vH D * tH D) (x₀ : G) := by
    apply hcos
    simp only [x₀, map_mul, map_inv, hqx', qH_vH, qH_uH, qH_tH, b, qH_betaH]
    exact conj_v_uvt_QA45
  have hx₀2 : orderOf (x₀ : G) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (b : G)) x'
    rw [MulAut.conj_apply, hx'2] at this
    simpa [x₀] using this
  have hx₀conj : IsConj z (x₀ : G) := isConj_iff.mpr ⟨(b : G) * g, by
    simp only [x₀, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hg]
    group⟩
  have hx₀J : (x₀ : G) ∉ J z := by
    intro hmem
    obtain ⟨hyH, hq⟩ := hcos_qH hx₀
    have h1 : qH D ⟨(x₀ : G), hyH⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hmem)
    rw [h1] at hq
    have hq' : qH D (uH D * vH D * tH D) = 1 := hq.symm
    rw [map_mul, map_mul, qH_uH, qH_vH, qH_tH] at hq'
    apply vH_not_mem_P_H D
    rw [mem_P_H_iff, qH_vH]
    have hv : (⟨v, v_mem_A⟩ : QA45.originalSubgroup) =
        (⟨u, u_mem_A⟩ : QA45.originalSubgroup)⁻¹ * (⟨t, t_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
      calc (⟨v, v_mem_A⟩ : QA45.originalSubgroup)
          = (⟨u, u_mem_A⟩ : QA45.originalSubgroup)⁻¹ *
              ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) *
              (⟨t, t_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by group
        _ = _ := by rw [hq']; group
    rw [hv, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem u_mem_Q)
      (QP45.originalSubgroup.inv_mem t_mem_Q)
  have hx₀E : IsElemAbelian 2 (CJ z (x₀ : G)) :=
    isElemAbelian_CJ_of_isConj D hz2 hJ' hCJ hJp hsqJ hPH x₀.2 hx₀J hx₀conj
  have hconjCJ : ∀ {w y : G}, w ∈ H z →
      CJ z (w * y * w⁻¹) = (CJ z y).map (MulAut.conj w).toMonoidHom := by
    intro w y hw
    ext c
    constructor
    · intro hc
      refine ⟨w⁻¹ * c * w, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      obtain ⟨hcy, hcJ⟩ := mem_CJ.mp hc
      refine mem_CJ.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hcy ⊢
        calc w⁻¹ * c * w * y = w⁻¹ * (c * (w * y * w⁻¹)) * w := by group
          _ = w⁻¹ * ((w * y * w⁻¹) * c) * w := by rw [hcy]
          _ = y * (w⁻¹ * c * w) := by group
      · have := conj_mem_J_of_mem_H ((H z).inv_mem hw) hcJ
        simpa using this
    · rintro ⟨c', hc', rfl⟩
      obtain ⟨hcy, hcJ⟩ := mem_CJ.mp hc'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine mem_CJ.mpr ⟨?_, conj_mem_J_of_mem_H hw hcJ⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hcy ⊢
      calc w * c' * w⁻¹ * (w * y * w⁻¹) = w * (c' * y) * w⁻¹ := by group
        _ = w * (y * c') * w⁻¹ := by rw [hcy]
        _ = w * y * w⁻¹ * (w * c' * w⁻¹) := by group
  let I : G → Prop := fun y =>
    cosetJ (z := z) (uH D * vH D * tH D) y ∧ orderOf y = 2 ∧ IsElemAbelian 2 (CJ z y)
  have hqs : qH D σ * qH D (uH D * vH D * tH D) = qH D (uH D * vH D * tH D) * qH D σ := by
    rw [hqσ, map_mul, map_mul, qH_uH, qH_vH, qH_tH]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact uvt_mul_sigma1_mul_sigma2_inv.symm
  have hIs : ∀ w : ↥(H z), qH D w * qH D (uH D * vH D * tH D) =
      qH D (uH D * vH D * tH D) * qH D w → ∀ {y : G}, I y → I ((w : G) * y * (w : G)⁻¹) := by
    intro w hwq y ⟨hyc, hy2, hyE⟩
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨hyH, hqy⟩ := hcos_qH hyc
      exact hcos (uH D * vH D * tH D) (w * ⟨y, hyH⟩ * w⁻¹) (by
        rw [map_mul, map_mul, map_inv, hqy, hwq]; group)
    · have := MulEquiv.orderOf_eq (MulAut.conj (w : G)) y
      rwa [MulAut.conj_apply, hy2] at this
    · rw [hconjCJ w.2]
      exact hyE.map _
  have hIsσ : ∀ {y : G}, I y → I (s * y * s⁻¹) := fun hy => hIs σ hqs hy
  have hIj : ∀ {j : G}, j ∈ J z → ∀ {y : G}, I y → I (j * y * j⁻¹) := by
    intro j hj y hy
    refine hIs ⟨j, J_le_H hj⟩ ?_ hy
    have hjq : qH D ⟨j, J_le_H hj⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    rw [hjq, one_mul, mul_one]
  let R : G → G → Prop := fun a c => ∃ j ∈ J z, j * a * j⁻¹ = c
  have hRsymm : ∀ {a c : G}, R a c → R c a := by
    rintro a c ⟨j, hj, rfl⟩
    exact ⟨j⁻¹, (J z).inv_mem hj, by group⟩
  have hRtrans : ∀ {a c d : G}, R a c → R c d → R a d := by
    rintro a c d ⟨j, hj, rfl⟩ ⟨k, hk, rfl⟩
    exact ⟨k * j, (J z).mul_mem hk hj, by group⟩
  have hRconj : ∀ {w : G}, w ∈ H z → ∀ {a c : G}, R a c → R (w * a * w⁻¹) (w * c * w⁻¹) := by
    rintro w hw a c ⟨j, hj, rfl⟩
    exact ⟨w * j * w⁻¹, conj_mem_J_of_mem_H hw hj, by group⟩
  obtain ⟨x₁, x₂, hx₁₂⟩ := hcls
  have hcl : ∀ {y : G}, I y → R y x₁ ∨ R y x₂ := by
    intro y hy
    obtain ⟨j, hj, h1 | h1⟩ := hx₁₂ y hy.1 hy.2.1 hy.2.2
    · exact Or.inl ⟨j, hj, h1⟩
    · exact Or.inr ⟨j, hj, h1⟩
  have hI₀ : I (x₀ : G) := ⟨hx₀, hx₀2, hx₀E⟩
  have hI₁ : I (s * x₀ * s⁻¹) := hIsσ hI₀
  have hI₂ : I (s * (s * x₀ * s⁻¹) * s⁻¹) := hIsσ hI₁
  have hs3' : s * s * s = 1 := by
    rw [← pow_three', ← hs3]
    exact pow_orderOf_eq_one s
  have hsinvH : s⁻¹ ∈ H z := (H z).inv_mem hsH
  have hR01 : R (x₀ : G) (s * x₀ * s⁻¹) := by
    have same : ∀ {a c : G}, (R a x₁ ∧ R c x₁) ∨ (R a x₂ ∧ R c x₂) → R a c := by
      rintro a c (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hRtrans h1 (hRsymm h2)
      · exact hRtrans h1 (hRsymm h2)
    have h02 : R (x₀ : G) (s * (s * x₀ * s⁻¹) * s⁻¹) → R (x₀ : G) (s * x₀ * s⁻¹) := by
      intro h
      have h' := hRconj hsH h
      have heq : s * (s * (s * (x₀ : G) * s⁻¹) * s⁻¹) * s⁻¹ = x₀ := by
        calc s * (s * (s * (x₀ : G) * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * x₀ * (s * s * s)⁻¹ := by
              group
          _ = x₀ := by rw [hs3']; group
      rw [heq] at h'
      exact hRsymm h'
    have h12 : R (s * x₀ * s⁻¹) (s * (s * x₀ * s⁻¹) * s⁻¹) → R (x₀ : G) (s * x₀ * s⁻¹) := by
      intro h
      have h' := hRconj hsinvH h
      have heq1 : s⁻¹ * (s * (x₀ : G) * s⁻¹) * s⁻¹⁻¹ = x₀ := by group
      have heq2 : s⁻¹ * (s * (s * (x₀ : G) * s⁻¹) * s⁻¹) * s⁻¹⁻¹ = s * x₀ * s⁻¹ := by group
      rw [heq1, heq2] at h'
      exact h'
    rcases hcl hI₀ with a0 | a0 <;> rcases hcl hI₁ with a1 | a1 <;> rcases hcl hI₂ with a2 | a2
    · exact same (Or.inl ⟨a0, a1⟩)
    · exact same (Or.inl ⟨a0, a1⟩)
    · exact h02 (same (Or.inl ⟨a0, a2⟩))
    · exact h12 (same (Or.inr ⟨a1, a2⟩))
    · exact h12 (same (Or.inl ⟨a1, a2⟩))
    · exact h02 (same (Or.inr ⟨a0, a2⟩))
    · exact same (Or.inr ⟨a0, a1⟩)
    · exact same (Or.inr ⟨a0, a1⟩)
  obtain ⟨j₀, hj₀, hj₀x⟩ := hR01
  obtain ⟨j, hj, hjs⟩ := exists_jconj_commute_of_orderOf_three hJp hsH hs3 hj₀ hj₀x.symm
  set x : G := j * (x₀ : G) * j⁻¹ with hx_def
  have hIx : I x := hIj hj hI₀
  have hxσ : x ∈ Subgroup.centralizer ({(σ : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hjs.symm
  have hxH : x ∈ H z := (H z).mul_mem ((H z).mul_mem (J_le_H hj) x₀.2) ((H z).inv_mem (J_le_H hj))
  have hxconj : IsConj z x := hx₀conj.trans (isConj_iff.mpr ⟨j, rfl⟩)
  have hP3 : IsPGroup 3 (Subgroup.zpowers (σ : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hσ3, pow_one])
  have hPne : Subgroup.zpowers (σ : G) ≠ ⊥ := by
    intro hbot
    have h1 : (σ : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers (σ : G))
    have h2 : orderOf (σ : G) = 1 := by rw [h1, orderOf_one]
    rw [Subgroup.orderOf_coe, hσ3] at h2
    omega
  have hPH' : Subgroup.zpowers (σ : G) ≤ H z := Subgroup.zpowers_le.mpr σ.2
  have hxP : ∀ y ∈ Subgroup.zpowers (σ : G), x * y = y * x := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute x (σ : G) from
      Subgroup.mem_centralizer_singleton_iff.mp hxσ).zpow_right k).eq
  obtain ⟨c, hcC, hcz⟩ := (prop4_fusion_centralizer (p := 3) Nat.prime_three (by norm_num) hP3 hPne
    hPH' hstar hNP hIx.2.1 hxH hxP).mp (by
      obtain ⟨g', hg'⟩ := isConj_iff.mp hxconj
      exact ⟨g', by rw [← hg']; group⟩)
  refine ⟨x, hIx.1, hIx.2.1, hxσ, hIx.2.2, c⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hcσ : c * (σ : G) = (σ : G) * c :=
      (Subgroup.mem_centralizer_iff.mp hcC (σ : G) (Subgroup.mem_zpowers _)).symm
    calc c⁻¹ * (σ : G) = c⁻¹ * ((σ : G) * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * (σ : G)) * c⁻¹ := by rw [hcσ]
      _ = (σ : G) * c⁻¹ := by group
  · calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hcz, inv_inv]
      _ = x := by group

end CFSG.RankThree.GF2n.Parrott
