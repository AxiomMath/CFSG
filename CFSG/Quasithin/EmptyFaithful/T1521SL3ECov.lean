module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.T1521SL3ERed

public section

namespace CFSG.Quasithin.L31521E

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin257
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_red_of_quotient {L P : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) {M : Type}
    [Group M] [Finite M] {U R₁ R₂ : Subgroup M} (hM : ModelData M U R₁ R₂)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* M) (hP : IsSylowTwoOf P L) :
    ∃ π : ↥L →* M, Red257 L P (pre π (Subgroup.normalizer (R₁ : Set M)))
      (pre π (Subgroup.normalizer (R₂ : Set M))) (pre π R₁) (pre π R₂) π U R₁ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial M := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hM.ne (Subgroup.ext fun x => by simp [Subsingleton.elim x 1])
  set π₀ := quotMap L e with hπ₀def
  have hπ₀ : Function.Surjective π₀ := quotMap_surjective L e
  have hker0 : ∀ x, π₀ x = 1 ↔ x ∈ CFSG.pCore 2 ↥L := quotMap_eq_one_iff L e
  have hcen : ∀ x : ↥L, (∀ y, x * y = y * x) → π₀ x = 1 := fun x hx =>
    center_le_ker hM.center_trivial π₀ hπ₀ x hx
  have hkc : ∀ x : ↥L, π₀ x = 1 → ∀ y, x * y = y * x :=
    ker_central_of_quasisimple hq π₀ hπ₀ hcen
  have hk2 : IsPGroup 2 π₀.ker := by
    have : π₀.ker = CFSG.pCore 2 ↥L := by
      ext x
      exact hker0 x
    rw [this]
    exact CFSG.pCore_isPGroup
  set P' := P.subgroupOf L with hP'def
  have hkerP : ∀ x : ↥L, π₀ x = 1 → x ∈ P' := by
    intro x hx
    have hx' : x ∈ CFSG.pCore 2 ↥L := (hker0 x).mp hx
    have h1 : (x : G) ∈ pCoreOf 2 L := ⟨x, hx', rfl⟩
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP h1
  have hP2 : IsPGroup 2 P' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  set S := P'.map π₀ with hSdef
  have hPS : P' = S.comap π₀ := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨p, hp, hpx⟩
      have h1 : π₀ (p⁻¹ * x) = 1 := by rw [map_mul, map_inv, hpx, inv_mul_cancel]
      have h2 : p⁻¹ * x ∈ P' := hkerP _ h1
      have h3 : p * (p⁻¹ * x) ∈ P' := P'.mul_mem hp h2
      simpa using h3
  have hSp : IsPGroup 2 S := hP2.map π₀
  have hSi : ¬ 2 ∣ S.index := by
    rw [← Subgroup.index_comap_of_surjective S hπ₀, ← hPS]
    exact hP.2.2
  have hUi : ¬ 2 ∣ U.index := by
    have := hM.sylow.2.2
    change ¬ 2 ∣ U.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨m, hm⟩ := exists_conj_sylow hSp hSi hM.sylow.2.1 hUi
  set π : ↥L →* M := (MulAut.conj m).toMonoidHom.comp π₀ with hπdef
  have hπx : ∀ x : ↥L, π x = m * π₀ x * m⁻¹ := fun x => rfl
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := hπ₀ (m⁻¹ * y * m)
    exact ⟨x, by rw [hπx, hx]; group⟩
  have hπ1 : ∀ x : ↥L, π x = 1 ↔ π₀ x = 1 := fun x => by
    rw [hπx]
    exact conj_eq_one_iff m _
  have hkerπ : π.ker = π₀.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    exact hπ1 x
  have hπU : ∀ x : ↥L, π x ∈ U ↔ (x : G) ∈ P := by
    intro x
    rw [hm, hπx]
    have e : m⁻¹ * (m * π₀ x * m⁻¹) * m = π₀ x := by group
    rw [e]
    have h1 : π₀ x ∈ S ↔ x ∈ P' := by
      rw [hPS]
      rfl
    rw [h1, hP'def, Subgroup.mem_subgroupOf]
  refine ⟨π, ?_⟩
  exact
    { surj := hπ
      ker_central := fun x hx => hkc x ((hπ1 x).mp hx)
      ker_two := hkerπ ▸ hk2
      center_le := fun x hx => (hπ1 x).mpr (hcen x hx)
      hP := by
        ext x
        rw [mem_pre]
        constructor
        · intro hx
          exact ⟨hP.1 hx, (hπU ⟨x, hP.1 hx⟩).mpr hx⟩
        · rintro ⟨h, hU⟩
          exact (hπU ⟨x, h⟩).mp hU
      hK₁ := rfl
      hK₂ := rfl
      hV := rfl
      hV' := rfl }

theorem rankBound1521_l3_cover {S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) (hq : CFSG.IsQuasisimple ↥L)
    (hZ : IsElemAbelian 2 (L ⊓ Subgroup.centralizer (L : Set G))) (hSyl : IsSylowTwoOf (S ⊓ L) L) :
    ∃ V V' : Subgroup G, RankBound1521 S L V V' := by
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := hL
  have hchar : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hpkg := L3.modelPkg_L3 (F := F) hn hF
  obtain ⟨π, hred⟩ := exists_red_of_quotient hq hpkg.data (e.trans (statedSLEquiv F)) hSyl
  have hVe := (geom_of_red hq hred hpkg hZ).V_elem
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : 2 < Nat.card (L3.V1 : Subgroup (projectiveSL 3 F)) := by
    rw [L3.card_V1]
    nlinarith
  exact ⟨_, _, rankBound1521_of_red hq hred (L3.maxRankModel_L3 hn hF) hVe hpkg.data.le₁
    hpkg.data.le₂ hcard⟩

end CFSG.Quasithin.L31521E
