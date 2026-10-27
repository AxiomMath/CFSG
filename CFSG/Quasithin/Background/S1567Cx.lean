module

public import CFSG.Quasithin.Background.S1567Xe

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section General

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left (X J : Subgroup G) :
    X ≤ Subgroup.normalizer ((⁅X, J⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_def]
  refine le_normalizer_closure_of_conj fun g hg x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have h1 : ⁅g * a, b⁆ ∈ Subgroup.closure {g | ∃ g₁ ∈ X, ∃ g₂ ∈ J, ⁅g₁, g₂⁆ = g} :=
    Subgroup.subset_closure ⟨g * a, X.mul_mem hg ha, b, hb, rfl⟩
  have h2 : ⁅g, b⁆ ∈ Subgroup.closure {g | ∃ g₁ ∈ X, ∃ g₂ ∈ J, ⁅g₁, g₂⁆ = g} :=
    Subgroup.subset_closure ⟨g, hg, b, hb, rfl⟩
  have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅g, b⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

theorem commutator_le_of_le_normalizer {X J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (X : Set G)) : ⁅X, J⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx j hj
  have h1 : j * x⁻¹ * j⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hJ hj) x⁻¹).mp (X.inv_mem hx)
  have e : ⁅x, j⁆ = x * (j * x⁻¹ * j⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact X.mul_mem hx h1

theorem le_normalizer_conjClosure_of_le {Z H K : Subgroup G}
    (hZ : K ≤ Subgroup.normalizer (Z : Set G)) (hH : K ≤ Subgroup.normalizer (H : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  refine le_normalizer_closure_of_conj fun g hg x hx => ?_
  obtain ⟨h, hh, z, hz, rfl⟩ := hx
  refine Subgroup.subset_closure ⟨g * h * g⁻¹, ?_, g * z * g⁻¹, ?_, by group⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hH hg) h).mp hh
  · exact (Subgroup.mem_normalizer_iff.mp (hZ hg) z).mp hz

end General

section Cx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem not_commutator_le_pCore_XE {J : Subgroup G} (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3)
    (hJTE : J ≤ TE153 T E) (hTJ : TE153 T E ≤ Subgroup.normalizer (J : Set G))
    (hYJ : Y153 Mc M ≤ Subgroup.normalizer (J : Set G))
    (hPJ : ∀ P : Subgroup G, J ≤ P → P ≤ TE153 T E →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hNJM : Subgroup.normalizer (J : Set G) ≤ M) :
    ¬ ⁅XE153 E, J⁆ ≤ pCoreOf 2 (XE153 E) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  intro hNP
  have hP₂GE : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (pCoreOf 2 (XE153 E) : Set G) :=
    (XE_normal_153 E).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hP₂TE : pCoreOf 2 (XE153 E) ≤ TE153 T E :=
    A4.le_of_normal_of_isSylowTwoOf k.r2.sylow_GE
      ((pCoreOf_le 2 _).trans ((oTwoUpper_le _).trans hCN))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        ((pCoreOf_le 2 _).trans ((oTwoUpper_le _).trans hCN))).mpr hP₂GE)
      (pCoreOf_isPGroup 2 _)
  have hconj : ∀ c ∈ Subgroup.centralizer (E : Set G), ∀ z ∈ J,
      c * z * c⁻¹ ∈ pCoreOf 2 (XE153 E) ⊔ J := by
    intro c hc z hz
    have hc' : c ∈ XE153 E ⊔ (T ⊓ Subgroup.centralizer (E : Set G)) := by
      rw [CE_eq_XE_sup_SE k hidx]; exact hc
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (XE153 E)
      (T ⊓ Subgroup.centralizer (E : Set G)) (SE_le_normalizer_XE E)
    have hc'' : c ∈ (XE153 E : Set G) * ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
      rw [← hmul]; exact hc'
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_mul.mp hc''
    have hsJ : s * z * s⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hTJ ⟨hs.1, hCN hs.2⟩) z).mp hz
    have hcomm : ⁅x, s * z * s⁻¹⁆ ∈ pCoreOf 2 (XE153 E) :=
      hNP (Subgroup.commutator_mem_commutator hx hsJ)
    have e : x * s * z * (x * s)⁻¹ = ⁅x, s * z * s⁻¹⁆ * (s * z * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hsJ)
  set I' : Subgroup G := conjClosure J (Subgroup.centralizer (E : Set G)) with hI'
  have hI'le : I' ≤ pCoreOf 2 (XE153 E) ⊔ J := conjClosure_le hconj
  have hI'TE : I' ≤ TE153 T E := hI'le.trans (sup_le hP₂TE hJTE)
  have hI'M : I' ≤ M := hI'TE.trans (inf_le_left.trans k.c.hyp.T_le)
  have hGEI' : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (I' : Set G) := by
    rw [k.r66.GE_eq]
    refine sup_le (sup_le ?_ ?_) (le_normalizer_conjClosure _ _)
    · refine le_normalizer_conjClosure_of_le (K := YE153 Mc M E) (fun y hy => hYJ ?_)
        (fun y hy => normalizer_le_normalizer_CE E
          ((oTwoUpper_le _).trans inf_le_right hy))
      exact ((oTwoUpper_le _).trans inf_le_left) hy
    · exact le_normalizer_conjClosure_of_le (hTJ) (fun y hy => normalizer_le_normalizer_CE E hy.2)
  have hI'GE : I' ≤ Subgroup.normalizer (E : Set G) := hI'TE.trans inf_le_right
  have hsyl : IsSylowTwoOf (TE153 T E ⊓ I') I' := A4.isSylowTwoOf_inf_normal k.r2.sylow_GE hI'GE hGEI'
  have hJI' : J ≤ I' := le_conjClosure J _
  have hJP : J ≤ TE153 T E ⊓ I' := le_inf hJTE hJI'
  apply k.L.not_le_M
  intro y hy
  obtain ⟨x, hx, n, hn, rfl⟩ := frattini_two hI'GE hGEI' hsyl hy
  have hnJ : n ∈ Subgroup.normalizer (J : Set G) := hPJ _ hJP inf_le_left hn.2
  exact M.mul_mem (hI'M hx) (hNJM hnJ)

theorem XE_eq_commutator_of {J : Subgroup G} (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3)
    (hJTE : J ≤ TE153 T E) (hTJ : TE153 T E ≤ Subgroup.normalizer (J : Set G))
    (hYJ : Y153 Mc M ≤ Subgroup.normalizer (J : Set G))
    (hPJ : ∀ P : Subgroup G, J ≤ P → P ≤ TE153 T E →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hNJM : Subgroup.normalizer (J : Set G) ≤ M) :
    XE153 E = ⁅XE153 E, J⁆ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hJGE : J ≤ Subgroup.normalizer (E : Set G) := hJTE.trans inf_le_right
  have hJXE : J ≤ Subgroup.normalizer (XE153 E : Set G) := hJGE.trans (XE_normal_153 E)
  have hN_le : ⁅XE153 E, J⁆ ≤ XE153 E := commutator_le_of_le_normalizer hJXE
  have hN_norm : XE153 E ≤ Subgroup.normalizer ((⁅XE153 E, J⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_left _ _
  have hnot := not_commutator_le_pCore_XE k hidx hJTE hTJ hYJ hPJ hNJM
  have hcard : Nat.card (OTwoQuot (XE153 E)) = 3 := by
    obtain ⟨e⟩ := XE_quot_153 k hidx
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hidx3 : (pCoreOf 2 (XE153 E)).relIndex (XE153 E) = 3 := by
    rw [C1Pack153.relIndex_pCoreOf_eq_card_quot]; exact hcard
  have hUle : ⁅XE153 E, J⁆ ⊔ pCoreOf 2 (XE153 E) ≤ XE153 E := sup_le hN_le (pCoreOf_le 2 _)
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (XE153 E))
    (⁅XE153 E, J⁆ ⊔ pCoreOf 2 (XE153 E)) (XE153 E) le_sup_right hUle
  rw [hidx3] at hmul
  have hUX : (⁅XE153 E, J⁆ ⊔ pCoreOf 2 (XE153 E)).relIndex (XE153 E) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ hmul) with h1 | h3
    · exact h1
    · exfalso
      have h1 : (pCoreOf 2 (XE153 E)).relIndex (⁅XE153 E, J⁆ ⊔ pCoreOf 2 (XE153 E)) = 1 := by
        rw [h3] at hmul; omega
      exact hnot (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1))
  have hXU : XE153 E ≤ ⁅XE153 E, J⁆ ⊔ pCoreOf 2 (XE153 E) := Subgroup.relIndex_eq_one.mp hUX
  have hP₂N : pCoreOf 2 (XE153 E) ≤ Subgroup.normalizer ((⁅XE153 E, J⁆ : Subgroup G) : Set G) :=
    (pCoreOf_le 2 _).trans hN_norm
  have hmulN := Subgroup.coe_mul_of_right_le_normalizer_left ⁅XE153 E, J⁆ (pCoreOf 2 (XE153 E)) hP₂N
  have hO2 : oTwoUpper (XE153 E) ≤ ⁅XE153 E, J⁆ := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    have hx' : x ∈ ((⁅XE153 E, J⁆ : Subgroup G) : Set G) * (pCoreOf 2 (XE153 E) : Set G) := by
      rw [← hmulN]; exact hXU hx
    obtain ⟨n, hn, p, hp, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (XE153 E) ⟨p, hp⟩
    obtain ⟨n', hn', hnp⟩ := A4.exists_pow_mul_eq hn (hP₂N hp) (2 ^ j)
    refine ⟨j, ?_⟩
    have hp1 : p ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [hnp, hp1, mul_one]
    exact hn'
  have hXX : oTwoUpper (XE153 E) = XE153 E := oTwoUpper_oTwoUpper _
  have hO2' : XE153 E ≤ ⁅XE153 E, J⁆ := by
    calc XE153 E = oTwoUpper (XE153 E) := hXX.symm
      _ ≤ ⁅XE153 E, J⁆ := hO2
  exact le_antisymm hO2' hN_le

end Cx

end S1567

end CFSG.Quasithin
