module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1_exists_E81 (hstd : s16c4v1_Std D) (h3 : 3 ∈ D.sig) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have hp : 1 < 3 := by norm_num
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := hstd.dataExt.four_le hstd.rank 3 h3
  obtain ⟨E, hEM, hE, hcardE⟩ := CFSG.SectionRank.exists_pRank hp D.M
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 4 ∣ Nat.card ↥E := by
    rw [hcardE]
    exact Nat.pow_dvd_pow 3 h4
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 4) hdvd
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEM,
    CFSG.Open.IsElemAbelian.mono hE (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

private theorem s16c4v1_cov_vec_inv (S : s16c4v1_Sit D V L hV) {v : G} (hv : v ∈ V) :
    s16c4v1_vec S v⁻¹ = -s16c4v1_vec S v := by
  have h := s16c4v1_vec_mul S hv (V.inv_mem hv)
  rw [mul_inv_cancel, s16c4v1_vec_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem s16c4v1_cov_odd_orderOf {E : Subgroup G} (hE : IsElemAbelian 3 E) (e : ↥E) :
    Odd (orderOf (e : G)) :=
  Odd.of_dvd_nat (by norm_num : Odd 3)
    (orderOf_dvd_of_pow_eq_one (hE.2 (e : G) e.2))

theorem s16c4v1_three_inner (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D)
    (hno : ¬ ∃ (z : G) (ω : S.F.K), s16c4v1_ScalarOf S z ω) {m : G} (hm : m ∈ D.M)
    (hodd : Odd (orderOf m)) : ∃ l ∈ L, s16c4v1_ActsLike V m l := by
  obtain ⟨c, γ, hc, hlin⟩ := s16c4v1_odd_lin S h1217 hm hodd
  obtain ⟨l₀, hl₀L, hl₀⟩ := s16c4v1_exists_induces S γ⁻¹
  have hl₀M : l₀ ∈ D.M := S.sect.setting.hyp151.le hl₀L
  have hm' : m * l₀ ∈ D.M := D.M.mul_mem hm hl₀M
  have hscal : ∀ v ∈ V, s16c4v1_vec S ((m * l₀) * v * (m * l₀)⁻¹) = c • s16c4v1_vec S v := by
    intro v hv
    have hconj : (m * l₀) * v * (m * l₀)⁻¹ = m * (l₀ * v * l₀⁻¹) * m⁻¹ := by group
    rw [hconj, hlin _ (s16c4v1_conj_mem S hl₀M hv), hl₀ v hv, smul_inv_smul]
  by_cases hc1 : c = 1
  · have hcent : ∀ v ∈ V, (m * l₀) * v * (m * l₀)⁻¹ = v := by
      apply (s16c4v1_centralizes_iff S h1217 hm').1
      intro v hv
      have hz : s16c4v1_vec S ((m * l₀) * v * (m * l₀)⁻¹ * v⁻¹) = 0 := by
        rw [s16c4v1_vec_mul S (s16c4v1_conj_mem S hm' hv) (V.inv_mem hv),
          hscal v hv, hc1, one_smul, s16c4v1_cov_vec_inv S hv, add_neg_cancel]
      exact (s16c4v1_vec_eq_zero_iff S
        (V.mul_mem (s16c4v1_conj_mem S hm' hv) (V.inv_mem hv))).mp hz
    refine ⟨l₀⁻¹, L.inv_mem hl₀L, fun v hv => ?_⟩
    have hu : l₀⁻¹ * v * l₀ ∈ V := by
      simpa using s16c4v1_conj_mem S (D.M.inv_mem hl₀M) hv
    have hconj : m * v * m⁻¹ = (m * l₀) * (l₀⁻¹ * v * l₀) * (m * l₀)⁻¹ := by group
    rw [hconj, hcent (l₀⁻¹ * v * l₀) hu, inv_inv]
  · exfalso
    exact hno ⟨m * l₀, c, hm', hc1, hscal⟩

theorem s16c4v1_inner_hom (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D)
    (hno : ¬ ∃ (z : G) (ω : S.F.K), s16c4v1_ScalarOf S z ω) {E : Subgroup G} (hEM : E ≤ D.M)
    (hE : IsElemAbelian 3 E) :
    ∃ φ : ↥E →* ↥(SUid S.F.σ 4),
      (∀ e : ↥E, s16c4v1_Induces S (e : G) (φ e)) ∧
      (∀ e : ↥E, φ e = 1 → ∀ v ∈ V, (e : G) * v * (e : G)⁻¹ = v) ∧
      (∀ e : ↥E, ∀ x ∈ v1Sub D.M ⊥ V hV L, (e : G) * x * (e : G)⁻¹ = x) ∧
      IsElemAbelian 3 φ.range := by
  have hex : ∀ e : ↥E, ∃ (l : G) (γ : ↥(SUid S.F.σ 4)),
      l ∈ L ∧ s16c4v1_ActsLike V (e : G) l ∧ s16c4v1_Induces S (e : G) γ := by
    intro e
    obtain ⟨l, hlL, hl⟩ :=
      s16c4v1_three_inner S h1217 hno (hEM e.2) (s16c4v1_cov_odd_orderOf hE e)
    obtain ⟨γ, hγ⟩ := s16c4v1_induces_of_mem_L S hlL
    exact ⟨l, γ, hlL, hl, fun v hv => by rw [hl v hv]; exact hγ v hv⟩
  let lf : ↥E → G := fun e => Classical.choose (hex e)
  let f : ↥E → ↥(SUid S.F.σ 4) := fun e => Classical.choose (Classical.choose_spec (hex e))
  have hf_acts : ∀ e : ↥E, s16c4v1_ActsLike V (e : G) (lf e) :=
    fun e => (Classical.choose_spec (Classical.choose_spec (hex e))).2.1
  have hfL : ∀ e : ↥E, lf e ∈ L :=
    fun e => (Classical.choose_spec (Classical.choose_spec (hex e))).1
  have hf_ind : ∀ e : ↥E, s16c4v1_Induces S (e : G) (f e) :=
    fun e => (Classical.choose_spec (Classical.choose_spec (hex e))).2.2
  have hf_one : f 1 = 1 := by
    refine s16c4v1_induces_unique S (hf_ind 1) ?_
    intro v hv
    simp [s16c4v1_Induces]
  have hf_mul : ∀ a b : ↥E, f (a * b) = f a * f b := by
    intro a b
    refine s16c4v1_induces_unique S (hf_ind (a * b)) ?_
    exact s16c4v1_induces_mul S (hEM a.2) (hEM b.2) (hf_ind a) (hf_ind b)
  let φ : ↥E →* ↥(SUid S.F.σ 4) :=
    { toFun := f, map_one' := hf_one, map_mul' := hf_mul }
  refine ⟨φ, fun e => hf_ind e, ?_, ?_, ?_⟩
  · intro e he
    apply (s16c4v1_centralizes_iff S h1217 (hEM e.2)).1
    intro v hv
    have hvec : s16c4v1_vec S ((e : G) * v * (e : G)⁻¹) = s16c4v1_vec S v := by
      have h := hf_ind e v hv
      rw [h, show f e = 1 from he, one_smul]
    have hz : s16c4v1_vec S ((e : G) * v * (e : G)⁻¹ * v⁻¹) = 0 := by
      rw [s16c4v1_vec_mul S (s16c4v1_conj_mem S (hEM e.2) hv) (V.inv_mem hv),
        hvec, s16c4v1_cov_vec_inv S hv, add_neg_cancel]
    exact (s16c4v1_vec_eq_zero_iff S
      (V.mul_mem (s16c4v1_conj_mem S (hEM e.2) hv) (V.inv_mem hv))).mp hz
  · intro e x hx
    rw [hf_acts e x (s16c4v1_v1_le S hx)]
    exact s16c4v1_L_centralizes_V1 S (hfL e) hx
  · refine ⟨?_, ?_⟩
    · haveI : IsMulCommutative ↥E := hE.1
      exact Subgroup.range_isMulCommutative φ
    · intro x hx
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [← map_pow]
      have he3 : e ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hE.2 (e : G) e.2
      rw [he3, map_one]

theorem s16c4v1_cover_vec (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    (hno : ¬ ∃ (z : G) (ω : S.F.K), s16c4v1_ScalarOf S z ω) {E : Subgroup G} (hEM : E ≤ D.M)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4) {w : G} (hw : w ∈ V) :
    2 ≤ CFSG.Open.pRank 3 (D.M ⊓ Subgroup.centralizer ({w} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφind, hφker, hφV1, hφea⟩ :=
    s16c4v1_inner_hom S hstd.r1217 hno hEM hE
  have hcardφ : Nat.card ↥φ.ker * Nat.card ↥φ.range = 3 ^ 4 := by
    rw [Subgroup.card_ker_mul_card_range φ, hcard]
  have hrange_le : Nat.card ↥φ.range ≤ 3 ^ 3 :=
    s16c4v1_card_le_27 S.F.σ S.F.card_K S.F.isUnitary φ.range hφea
  have hker3 : 3 ≤ Nat.card ↥φ.ker := by
    by_contra h
    have h2 : Nat.card ↥φ.ker ≤ 2 := by omega
    have hle : Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ 2 * 3 ^ 3 :=
      Nat.mul_le_mul h2 hrange_le
    have h81 : (3 : ℕ) ^ 4 ≤ 2 * 3 ^ 3 := by rw [← hcardφ]; exact hle
    norm_num at h81
  have hK₁_le : (φ.ker.map E.subtype) ≤ D.M ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine le_inf ((Subgroup.map_subtype_le φ.ker).trans hEM) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    calc (k : G) * w = (k : G) * w * (k : G)⁻¹ * (k : G) := by group
      _ = w * (k : G) := by rw [hφker k (MonoidHom.mem_ker.mp hk) w hw]
  have hK₁ea : IsElemAbelian 3 (φ.ker.map E.subtype) :=
    CFSG.Open.IsElemAbelian.mono hE (Subgroup.map_subtype_le φ.ker)
  have hK₁p : IsPGroup 3 (φ.ker.map E.subtype) := CFSG.Open.IsElemAbelian.isPGroup hK₁ea
  have hK₁card : Nat.card (φ.ker.map E.subtype) = Nat.card ↥φ.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  by_cases hw1 : w ∈ v1Sub D.M ⊥ V hV L
  · have hE_le : E ≤ D.M ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine le_inf hEM ?_
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hφV1 ⟨e, he⟩ w hw1
      calc e * w = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [h]
    have h4 : 4 ≤ CFSG.Open.pRank 3 (D.M ⊓ Subgroup.centralizer ({w} : Set G)) :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hE_le hE hcard
    omega
  · by_cases h9 : 9 ≤ Nat.card ↥φ.ker
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK₁p
      have hk2 : 2 ≤ k := by
        have h : 3 ^ 2 ≤ 3 ^ k := by
          rw [← hk, hK₁card]
          norm_num
          exact h9
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
      exact le_trans hk2
        (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hK₁_le hK₁ea hk)
    · have hker_dvd : Nat.card ↥φ.ker ∣ 3 ^ 4 := ⟨Nat.card ↥φ.range, hcardφ.symm⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hker_dvd
      have hker_eq : Nat.card ↥φ.ker = 3 := by
        have hj1 : 1 ≤ j := by
          have h : 3 ^ 1 ≤ 3 ^ j := by rw [← hj]; simpa using hker3
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
        have hj2 : j < 2 := by
          have h : 3 ^ j < 3 ^ 2 := by
            rw [← hj]
            norm_num
            exact not_le.1 h9
          exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h
        have hj1' : j = 1 := by omega
        rw [hj, hj1']
        norm_num
      have hrange_eq : Nat.card ↥φ.range = 3 ^ 3 := by
        rw [hker_eq] at hcardφ
        norm_num at hcardφ ⊢
        omega
      have hw0 : s16c4v1_vec S w ≠ 0 := by
        intro h0
        exact hw1 ((s16c4v1_vec_eq_zero_iff S hw).mp h0)
      obtain ⟨g, e', he'E, he'1, hfix'⟩ :=
        s16c4v1_cover_model S.F.σ S.F.card_K S.F.isUnitary φ.range hφea hrange_eq hw0
      obtain ⟨e, he⟩ := MonoidHom.mem_range.mp he'E
      obtain ⟨l, hlL, hl⟩ := s16c4v1_exists_induces S g
      have hlM : l ∈ D.M := S.sect.setting.hyp151.le hlL
      set w' : G := l * w * l⁻¹ with hw'def
      have hw' : w' ∈ V := by rw [hw'def]; exact s16c4v1_conj_mem S hlM hw
      have hvecw' : s16c4v1_vec S w' = g • s16c4v1_vec S w := by
        rw [hw'def]; exact hl w hw
      have hfixe : (φ e) • s16c4v1_vec S w' = s16c4v1_vec S w' := by
        rw [he, hvecw', hfix']
      have hfixw' : (e : G) * w' * (e : G)⁻¹ = w' :=
        s16c4v1_fix_of_induces_fix S (hEM e.2) (s16c4v1_cov_odd_orderOf hE e)
          (hφV1 e) (hφind e) hw' hfixe
      set X₀ : Subgroup G := Subgroup.zpowers (e : G) ⊔ (φ.ker.map E.subtype) with hX₀def
      have hX₀E : X₀ ≤ E := by
        rw [hX₀def]
        refine sup_le ?_ (Subgroup.map_subtype_le φ.ker)
        rw [Subgroup.zpowers_le]
        exact e.2
      have hX₀ea : IsElemAbelian 3 X₀ := CFSG.Open.IsElemAbelian.mono hE hX₀E
      have heK₁ : (e : G) ∉ (φ.ker.map E.subtype) := by
        intro heK
        obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp heK
        have hke : k = e := Subtype.ext hk_eq
        have h1 : φ e = 1 := by
          rw [← hke]
          exact MonoidHom.mem_ker.mp hk
        rw [he] at h1
        exact he'1 h1
      have heX₀ : (e : G) ∈ X₀ := by
        rw [hX₀def]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers (e : G))
      have hlt : (φ.ker.map E.subtype) < X₀ := by
        refine lt_of_le_of_ne le_sup_right ?_
        intro hEq
        rw [hEq] at heK₁
        exact heK₁ heX₀
      have hX₀card_lt : 3 < Nat.card X₀ := by
        have h := Subgroup.card_lt_of_lt hlt
        rw [hK₁card, hker_eq] at h
        exact h
      have hzpC : Subgroup.zpowers (e : G) ≤ Subgroup.centralizer ({w'} : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        calc (e : G) * w' = (e : G) * w' * (e : G)⁻¹ * (e : G) := by group
          _ = w' * (e : G) := by rw [hfixw']
      have hK₁C : (φ.ker.map E.subtype) ≤ Subgroup.centralizer ({w'} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
        calc (k : G) * w' = (k : G) * w' * (k : G)⁻¹ * (k : G) := by group
          _ = w' * (k : G) := by rw [hφker k (MonoidHom.mem_ker.mp hk) w' hw']
      have hX₀C : X₀ ≤ Subgroup.centralizer ({w'} : Set G) := by
        rw [hX₀def]
        exact sup_le hzpC hK₁C
      have hX₀M : X₀ ≤ D.M := hX₀E.trans hEM
      set X : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup l⁻¹ X₀ with hXdef
      have hXea : IsElemAbelian 3 X := by
        rw [hXdef]
        exact CFSG.Open.IsElemAbelian.map hX₀ea (MulAut.conj l⁻¹).toMonoidHom
      have hXp : IsPGroup 3 X := CFSG.Open.IsElemAbelian.isPGroup hXea
      have hXcard : Nat.card X = Nat.card X₀ := by
        rw [hXdef]
        exact Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective
      have hw_eq : w = l⁻¹ * w' * l := by rw [hw'def]; group
      have hXle : X ≤ D.M ⊓ Subgroup.centralizer ({w} : Set G) := by
        refine le_inf ?_ ?_
        · intro x hx
          rw [hXdef, CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv] at hx
          have hx_eq : x = l⁻¹ * (l * x * l⁻¹) * l := by group
          rw [hx_eq]
          exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hlM) (hX₀M hx)) hlM
        · intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          rw [hXdef, CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv] at hx
          have hx₀c : (l * x * l⁻¹) * w' = w' * (l * x * l⁻¹) :=
            Subgroup.mem_centralizer_singleton_iff.mp (hX₀C hx)
          have hx_eq : x = l⁻¹ * (l * x * l⁻¹) * l := by group
          rw [hx_eq, hw_eq]
          calc (l⁻¹ * (l * x * l⁻¹) * l) * (l⁻¹ * w' * l)
              = l⁻¹ * ((l * x * l⁻¹) * w') * l := by group
            _ = l⁻¹ * (w' * (l * x * l⁻¹)) * l := by rw [hx₀c]
            _ = (l⁻¹ * w' * l) * (l⁻¹ * (l * x * l⁻¹) * l) := by group
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
      have hk2 : 2 ≤ k := by
        have h : 3 ^ 1 < 3 ^ k := by
          rw [← hk, hXcard]
          simpa using hX₀card_lt
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h
        omega
      exact le_trans hk2 (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hXle hXea hk)

theorem s16c4v1_noScalar_false (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    (hno : ¬ ∃ (z : G) (ω : S.F.K), s16c4v1_ScalarOf S z ω) : False := by
  have h3 : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  obtain ⟨E, hEM, hE, hcard⟩ := s16c4v1_exists_E81 hstd h3
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V :=
    s16_TI_of_pRank D hstd.r61 hV S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
      (fun w hw _ => ⟨3, h3, s16c4v1_cover_vec S hstd hno hEM hE hcard hw⟩)
  exact hstd.r129 ⊥ V S.sect.setting.hyp16.hyp125 hTI

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
