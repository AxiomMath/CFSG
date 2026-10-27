module

public import CFSG.RankThree.PartTwo.Late.Defs

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree.PartTwo

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa [mul_assoc] using this
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ Subgroup.normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem pCoreOf_le_pCore_of_isSubnormal {K : Type*} [Group K] [Finite K] (p : ℕ) [Fact p.Prime]
    {W : Subgroup K} (hW : W.IsSubnormal) : CFSG.Open.pCoreOf p W ≤ CFSG.Open.pCore p K := by
  induction hW with
  | top =>
    refine CFSG.LieType.BorelTits.le_pCore p ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p ⊤)
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    calc (⊤ : Subgroup K) = Subgroup.normalizer ((⊤ : Subgroup K) : Set K) :=
          (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm
      _ ≤ _ := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p ⊤
  | step W V hWV hV hN ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      ((CFSG.LieType.BorelTits.pCoreOf_le p W).trans hWV) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p W)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hWV).mp hN).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p W)

theorem eq_of_mutual_le (h : Hyp191 G) {A₁ A₂ M₁ M₂ : Subgroup G} (hA₁ : IsE27 A₁)
    (hA₂ : IsE27 A₂) (hM₁ : M₁ ∈ scriptM (gamma 2 A₁ : Set G))
    (hM₂ : M₂ ∈ scriptM (gamma 2 A₂ : Set G)) (h₁ : A₁ ≤ M₂) (h₂ : A₂ ≤ M₁) : M₁ = M₂ := by
  have e₁ := h A₁ M₁ M₂ hA₁ hM₁ h₁ (pCoreOf_ne_bot_of_isMaximalTwoLocal hM₂.1)
  have e₂ := h A₂ M₂ M₁ hA₂ hM₂ h₂ (pCoreOf_ne_bot_of_isMaximalTwoLocal hM₁.1)
  have hO : CFSG.Open.pCoreOf 2 M₁ = CFSG.Open.pCoreOf 2 M₂ := by
    rw [← e₁, ← e₂, inf_comm]
  rw [← normalizer_pCoreOf_of_isMaximalTwoLocal hM₁.1, hO,
    normalizer_pCoreOf_of_isMaximalTwoLocal hM₂.1]

theorem le_of_mem_scriptM_gamma {A M : Subgroup G} (hA : IsE27 A)
    (hM : M ∈ scriptM (gamma 2 A : Set G)) : A ≤ M :=
  hA.le_gamma.trans hM.2

theorem rank3II_19_2 (h : Hyp191 G) {A₁ A₂ M₁ M₂ : Subgroup G} (hA₁ : IsE27 A₁)
    (hA₂ : IsE27 A₂) (hM₁ : M₁ ∈ scriptM (gamma 2 A₁ : Set G))
    (hM₂ : M₂ ∈ scriptM (gamma 2 A₂ : Set G)) (hle : A₁ ≤ M₂) : M₁ = M₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₁M₁ : A₁ ≤ M₁ := le_of_mem_scriptM_gamma hA₁ hM₁
  obtain ⟨P, hA₁P, hPmax⟩ := Finite.exists_le_maximal
    (p := fun P : Subgroup G => IsPGroup 3 P ∧ A₁ ≤ P ∧ P ≤ M₁ ⊓ M₂) (a := A₁)
    ⟨hA₁.isPGroup, le_rfl, le_inf hA₁M₁ hle⟩
  obtain ⟨hP3, -, hPM⟩ := hPmax.prop
  have hmax : ∀ Q : Subgroup G, IsPGroup 3 Q → P ≤ Q → Q ≤ M₂ → Q = P := by
    intro Q hQ hPQ hQM
    by_contra hne
    obtain ⟨x, hxQ, hxP, hxN⟩ :=
      exists_mem_normalizer_not_mem_of_lt hQ (lt_of_le_of_ne hPQ (Ne.symm hne))
    have hPx : P.map (MulAut.conj x).toMonoidHom = P := map_conj_eq_of_mem_normalizer hxN
    have hxM₁ : x ∈ M₁ := by
      have hc := map_conj_mem_scriptM_gamma hM₁ x
      have heq : M₁ = M₁.map (MulAut.conj x).toMonoidHom := by
        refine eq_of_mutual_le h hA₁ (hA₁.map (MulAut.conj x)) hM₁ hc ?_ ?_
        · calc A₁ ≤ P := hA₁P
            _ = P.map (MulAut.conj x).toMonoidHom := hPx.symm
            _ ≤ M₁.map (MulAut.conj x).toMonoidHom :=
              Subgroup.map_mono (hPM.trans inf_le_left)
        · calc A₁.map (MulAut.conj x).toMonoidHom ≤ P.map (MulAut.conj x).toMonoidHom :=
                Subgroup.map_mono hA₁P
            _ = P := hPx
            _ ≤ M₁ := hPM.trans inf_le_left
      exact mem_of_map_conj_eq_of_isMaximalTwoLocal hM₁.1 heq.symm
    have hmem : IsPGroup 3 (P ⊔ Subgroup.zpowers x : Subgroup G) ∧ A₁ ≤ P ⊔ Subgroup.zpowers x ∧
        P ⊔ Subgroup.zpowers x ≤ M₁ ⊓ M₂ := by
      have hle : P ⊔ Subgroup.zpowers x ≤ Q := sup_le hPQ ((Subgroup.zpowers_le).mpr hxQ)
      refine ⟨hQ.to_le hle, hA₁P.trans le_sup_left, sup_le hPM ?_⟩
      exact (Subgroup.zpowers_le).mpr ⟨hxM₁, hQM hxQ⟩
    exact hxP (hPmax.le_of_ge hmem le_sup_left
      ((le_sup_right : Subgroup.zpowers x ≤ P ⊔ Subgroup.zpowers x) (Subgroup.mem_zpowers x)))
  have hPM₂ : P ≤ M₂ := hPM.trans inf_le_right
  obtain ⟨S, hS⟩ := (hP3.comap_subtype (K := M₂)).exists_le_sylow
  have hSP : (S : Subgroup M₂).map M₂.subtype = P := by
    refine hmax _ (S.isPGroup'.map _) ?_ (Subgroup.map_subtype_le _)
    rw [← Subgroup.map_subgroupOf_eq_of_le hPM₂]
    exact Subgroup.map_mono hS
  have hA₂M₂ : A₂ ≤ M₂ := le_of_mem_scriptM_gamma hA₂ hM₂
  obtain ⟨Q, hQ⟩ := (hA₂.isPGroup.comap_subtype (K := M₂)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M₂ Q S
  have hconj : A₂.map (MulAut.conj (g : G)).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have haQ : (⟨a, hA₂M₂ ha⟩ : M₂) ∈ (Q : Subgroup M₂) := hQ (Subgroup.mem_subgroupOf.mpr ha)
    have hgaS : MulAut.conj g • (⟨a, hA₂M₂ ha⟩ : M₂) ∈ ((g • Q : Sylow 3 M₂) : Subgroup M₂) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ haQ
    rw [hg] at hgaS
    have hmemP : ((MulAut.conj g • (⟨a, hA₂M₂ ha⟩ : M₂) : M₂) : G) ∈ P := by
      rw [← hSP]
      exact Subgroup.mem_map_of_mem _ hgaS
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmemP
  have hgM₂ : M₂.map (MulAut.conj (g : G)).toMonoidHom = M₂ :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer g.2)
  have hM₂' : M₂ ∈ scriptM (gamma 2 (A₂.map (MulAut.conj (g : G)).toMonoidHom) : Set G) := by
    have := map_conj_mem_scriptM_gamma hM₂ (g : G)
    rwa [hgM₂] at this
  exact eq_of_mutual_le h hA₁ (hA₂.map (MulAut.conj (g : G))) hM₁ hM₂' hle
    (hconj.trans (hPM.trans inf_le_left))

theorem mem_of_map_conj_le (h : Hyp191 G) {A M : Subgroup G} (hA : IsE27 A)
    (hM : M ∈ scriptM (gamma 2 A : Set G)) {y : G}
    (hy : A.map (MulAut.conj y).toMonoidHom ≤ M) : y ∈ M := by
  have heq := rank3II_19_2 h (hA.map (MulAut.conj y)) hA (map_conj_mem_scriptM_gamma hM y) hM hy
  exact mem_of_map_conj_eq_of_isMaximalTwoLocal hM.1 heq

theorem rank3II_19_3 (h : Hyp191 G) {A M X : Subgroup G} (hA : IsE27 A)
    (hM : M ∈ scriptM (gamma 2 A : Set G)) (hAX : A ≤ X) (hsn : (A.subgroupOf X).IsSubnormal) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup G := CFSG.Open.pCoreOf 3 X with hRdef
  have hR3 : IsPGroup 3 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X
  have hAR : A ≤ R := by
    have hW : A.subgroupOf X ≤ CFSG.Open.pCore 3 X :=
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer
        hA.isPGroup.comap_subtype).trans (pCoreOf_le_pCore_of_isSubnormal 3 hsn)
    rw [← Subgroup.map_subgroupOf_eq_of_le hAX]
    exact Subgroup.map_mono hW
  have hRM : R ≤ M := by
    by_contra hRM
    have hlt : R ⊓ M < R := lt_of_le_of_ne inf_le_left fun heq => hRM (heq ▸ inf_le_right)
    obtain ⟨y, hyR, hyRM, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hR3 hlt
    have hyM : y ∈ M := by
      refine mem_of_map_conj_le h hA hM ?_
      calc A.map (MulAut.conj y).toMonoidHom ≤ (R ⊓ M).map (MulAut.conj y).toMonoidHom :=
            Subgroup.map_mono (le_inf hAR (le_of_mem_scriptM_gamma hA hM))
        _ = R ⊓ M := map_conj_eq_of_mem_normalizer hyN
        _ ≤ M := inf_le_right
    exact hyRM ⟨hyR, hyM⟩
  intro g hg
  have hgR : g ∈ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 X hg
  refine mem_of_map_conj_le h hA hM ?_
  calc A.map (MulAut.conj g).toMonoidHom ≤ R.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hAR
    _ = R := map_conj_eq_of_mem_normalizer hgR
    _ ≤ M := hRM

end CFSG.RankThree.PartTwo.Late
