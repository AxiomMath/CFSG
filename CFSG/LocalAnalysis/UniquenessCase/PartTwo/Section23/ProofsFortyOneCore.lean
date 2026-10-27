module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFortyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneSteps
public import CFSG.GroupTheory.CardCommutatorTwo
public import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private theorem conj_pow_eq_inv_pow {t y : G} (h : t * y * t⁻¹ = y⁻¹) (k : ℕ) :
    t * y ^ k * t⁻¹ = (y ^ k)⁻¹ := by
  have hc : MulAut.conj t y = y⁻¹ := by
    simpa only [MulAut.conj_apply] using h
  calc t * y ^ k * t⁻¹ = (MulAut.conj t) (y ^ k) := by simp only [MulAut.conj_apply]
    _ = ((MulAut.conj t) y) ^ k := map_pow _ _ _
    _ = (y⁻¹) ^ k := by rw [hc]
    _ = (y ^ k)⁻¹ := inv_pow y k

private theorem map_normalizerMonoidHom_subgroupOf {E K : Subgroup G} {m : G}
    (hmE : m ∈ Subgroup.normalizer (E : Set G))
    (hmK : m ∈ Subgroup.normalizer (K : Set G)) :
    (K.subgroupOf E).map (↑(Subgroup.normalizerMonoidHom E ⟨m, hmE⟩) : ↥E →* ↥E) =
      K.subgroupOf E := by
  ext e
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzK : (z : G) ∈ K := Subgroup.mem_subgroupOf.mp hz
    rw [Subgroup.mem_subgroupOf]
    change (↑((Subgroup.normalizerMonoidHom E ⟨m, hmE⟩) z) : G) ∈ K
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hmK (z : G)).mp hzK
  · intro he
    rw [Subgroup.mem_subgroupOf] at he
    have hmK' : m⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).inv_mem hmK
    have hmE' : m⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer (E : Set G)).inv_mem hmE
    have hzK : m⁻¹ * (e : G) * m ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp hmK' (e : G)).mp he
    have hzE : m⁻¹ * (e : G) * m ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp hmE' (e : G)).mp e.2
    refine ⟨⟨m⁻¹ * (e : G) * m, hzE⟩, Subgroup.mem_subgroupOf.mpr hzK, ?_⟩
    apply Subtype.ext
    change (↑((Subgroup.normalizerMonoidHom E ⟨m, hmE⟩)
      ⟨m⁻¹ * (e : G) * m, hzE⟩) : G) = (e : G)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show m * (m⁻¹ * (e : G) * m) * m⁻¹ = (e : G)
    group

private def quotientConjAut {E K : Subgroup G} [(K.subgroupOf E).Normal] {m : G}
    (hmE : m ∈ Subgroup.normalizer (E : Set G))
    (hmK : m ∈ Subgroup.normalizer (K : Set G)) :
    MulAut (↥E ⧸ K.subgroupOf E) :=
  QuotientGroup.congr (K.subgroupOf E) (K.subgroupOf E)
    (Subgroup.normalizerMonoidHom E ⟨m, hmE⟩)
    (map_normalizerMonoidHom_subgroupOf hmE hmK)

private theorem quotientConjAut_apply_mk {E K : Subgroup G} [(K.subgroupOf E).Normal] {m : G}
    (hmE : m ∈ Subgroup.normalizer (E : Set G))
    (hmK : m ∈ Subgroup.normalizer (K : Set G)) (e : ↥E) :
    quotientConjAut hmE hmK (QuotientGroup.mk e) =
      QuotientGroup.mk ((Subgroup.normalizerMonoidHom E ⟨m, hmE⟩) e) := by
  rw [quotientConjAut, QuotientGroup.congr_mk]

private theorem quotientConjAut_mul {E K : Subgroup G} [(K.subgroupOf E).Normal] {m₁ m₂ : G}
    (h1E : m₁ ∈ Subgroup.normalizer (E : Set G))
    (h2E : m₂ ∈ Subgroup.normalizer (E : Set G))
    (h1K : m₁ ∈ Subgroup.normalizer (K : Set G))
    (h2K : m₂ ∈ Subgroup.normalizer (K : Set G)) :
    quotientConjAut (E := E) (K := K) (Subgroup.mul_mem _ h1E h2E)
        (Subgroup.mul_mem _ h1K h2K) =
      quotientConjAut h1E h1K * quotientConjAut h2E h2K := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H e =>
    simp only [MulAut.mul_apply, quotientConjAut_apply_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    group

private theorem quotientConjAut_one {E K : Subgroup G} [(K.subgroupOf E).Normal] :
    quotientConjAut (E := E) (K := K) (Subgroup.one_mem _) (Subgroup.one_mem _) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H e =>
    rw [quotientConjAut_apply_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    group

private def quotientConjHom (M E K : Subgroup G) (hE : M ≤ Subgroup.normalizer (E : Set G))
    (hK : M ≤ Subgroup.normalizer (K : Set G)) [(K.subgroupOf E).Normal] :
    M →* MulAut (↥E ⧸ K.subgroupOf E) where
  toFun m := quotientConjAut (hE m.2) (hK m.2)
  map_one' := quotientConjAut_one
  map_mul' m₁ m₂ := quotientConjAut_mul (hE m₁.2) (hE m₂.2) (hK m₁.2) (hK m₂.2)

private theorem quotientConjHom_apply_mk {M E K : Subgroup G} [(K.subgroupOf E).Normal]
    (hE : M ≤ Subgroup.normalizer (E : Set G)) (hK : M ≤ Subgroup.normalizer (K : Set G))
    (m : M) (e : E) :
    quotientConjHom M E K hE hK m (QuotientGroup.mk e) =
      QuotientGroup.mk (⟨(m : G) * (e : G) * (m : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hE m.2) (e : G)).mp e.2⟩ : E) := by
  change quotientConjAut (hE m.2) (hK m.2) (QuotientGroup.mk e) = _
  rw [quotientConjAut_apply_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem quotient_sq_eq_one {E K : Subgroup G} [(K.subgroupOf E).Normal]
    (hE : ∀ e ∈ E, e ^ 2 = 1) (q : ↥E ⧸ K.subgroupOf E) : q ^ 2 = 1 := by
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf E) q
  have he2 : e ^ 2 = 1 := Subtype.ext (by simpa using hE (e : G) e.2)
  rw [← map_pow, he2, map_one]

namespace S2341Frame

private theorem inv_sq_eq_conj_mul {x v : G} (hv2 : v * v = 1)
    (hinv : v * x * v⁻¹ = x⁻¹) : x⁻¹ ^ 2 = (x⁻¹ * v * x) * v := by
  have hvx : v * x = x⁻¹ * v := by
    have := congrArg (fun y => y * v) hinv
    simpa [mul_assoc] using this
  rw [pow_two]
  calc x⁻¹ * x⁻¹ = x⁻¹ * (x⁻¹ * (v * v)) := by rw [hv2]; group
    _ = x⁻¹ * (v * x) * v := by rw [hvx]; group
    _ = (x⁻¹ * v * x) * v := by group

private theorem mem_centralizer_Z_of_sq_eq_one {D : Data G} {u : G}
    (hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G))
    (huM : u ∈ D.M) (hu2 : u ^ 2 = 1) : u ∈ Subgroup.centralizer (D.Z : Set G) := by
  obtain ⟨k, hk⟩ : ∃ k, orderOf u = 2 ^ k := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hu2) with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  exact D.mem_centralizer_Z_of_two_element hMZ huM hk

private theorem mem_centralizer_Z_of_odd_inverted {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D) {x v : G} (hxM : x ∈ D.M)
    (hxodd : Odd (orderOf x)) (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹) :
    x ∈ Subgroup.centralizer (D.Z : Set G) := by
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]
    exact (h4 h1930 c).2.2
  have hvM : v ∈ D.M := s2341_W_le_M X h4 h23 h39 h40 h1930 hvW
  have hv2 : v ^ 2 = 1 := (X.isElemAbelian_W h4 h1930).2 v hvW
  have hv2' : v * v = 1 := by simpa [pow_two] using hv2
  have hconj2 : (x⁻¹ * v * x) ^ 2 = 1 := by
    rw [pow_two]
    calc (x⁻¹ * v * x) * (x⁻¹ * v * x) = x⁻¹ * (v * v) * x := by group
      _ = 1 := by rw [hv2']; group
  have hconjM : x⁻¹ * v * x ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) hvM) hxM
  have hvC : v ∈ Subgroup.centralizer (D.Z : Set G) :=
    mem_centralizer_Z_of_sq_eq_one hMZ hvM hv2
  have hconjC : x⁻¹ * v * x ∈ Subgroup.centralizer (D.Z : Set G) :=
    mem_centralizer_Z_of_sq_eq_one hMZ hconjM hconj2
  have hx2C : x ^ 2 ∈ Subgroup.centralizer (D.Z : Set G) := by
    have h1 : x⁻¹ ^ 2 ∈ Subgroup.centralizer (D.Z : Set G) := by
      rw [inv_sq_eq_conj_mul hv2' hinv]
      exact Subgroup.mul_mem _ hconjC hvC
    have h2 : (x ^ 2)⁻¹ ∈ Subgroup.centralizer (D.Z : Set G) := by
      rw [← inv_pow]
      exact h1
    simpa using (Subgroup.centralizer (D.Z : Set G)).inv_mem h2
  have hxmem : x ∈ Subgroup.zpowers (x ^ 2) :=
    mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hxodd)
  exact Subgroup.zpowers_le.mpr hx2C hxmem

private theorem quadratic_fixed {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {e v w : G}
    (heE : e ∈ c.E) (hvW : v ∈ X.W) (hwW : w ∈ X.W) :
    w * (e * v * e⁻¹ * v⁻¹) * w⁻¹ = e * v * e⁻¹ * v⁻¹ := by
  have hquad := s2341_quadratic X h4 h23 h39 h40 h1930 hneq
  have hcent : ⁅c.E, X.W⁆ ≤ Subgroup.centralizer (X.W : Set G) := by
    rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at hquad
  have hmem : e * v * e⁻¹ * v⁻¹ ∈ ⁅c.E, X.W⁆ :=
    Subgroup.commutator_mem_commutator heE hvW
  have hcomm := Subgroup.mem_centralizer_iff.mp (hcent hmem) w hwW
  calc w * (e * v * e⁻¹ * v⁻¹) * w⁻¹ = (e * v * e⁻¹ * v⁻¹) * w * w⁻¹ := by
        rw [← hcomm]
    _ = e * v * e⁻¹ * v⁻¹ := by group

private theorem quotientConjAut_eq_one_of_mem_centModE {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {m : G} (hmE : m ∈ Subgroup.normalizer (c.E : Set G))
    (hmZ : m ∈ Subgroup.normalizer (D.Z : Set G)) (hm : m ∈ centModE D Ch c)
    [(D.Z.subgroupOf c.E).Normal] :
    quotientConjAut (E := c.E) (K := D.Z) hmE hmZ = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H e =>
    rw [MulAut.one_apply, quotientConjAut_apply_mk, QuotientGroup.eq_iff_div_mem]
    rw [div_eq_mul_inv]
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using hm.2.2 (e : G) e.2)

private theorem quotientConjHom_fixes_mul_inv {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {v w : ↥D.M} (hvW : (v : G) ∈ X.W) (hwW : (w : G) ∈ X.W) :
    ∀ q, quotientConjHom D.M c.E D.Z hM_E hM_Z w
        (q * (quotientConjHom D.M c.E D.Z hM_E hM_Z v q)⁻¹) =
      q * (quotientConjHom D.M c.E D.Z hM_E hM_Z v q)⁻¹ := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H e =>
    have hve : (v : G) * (e : G) * (v : G)⁻¹ ∈ c.E :=
      (Subgroup.mem_normalizer_iff.mp (hM_E v.2) (e : G)).mp e.2
    have hmemE : (e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹ ∈ c.E :=
      c.E.mul_mem e.2 (c.E.inv_mem hve)
    have h1 : QuotientGroup.mk e *
        (quotientConjHom D.M c.E D.Z hM_E hM_Z v (QuotientGroup.mk e))⁻¹ =
        QuotientGroup.mk
          (⟨(e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹, hmemE⟩ : ↥c.E) := by
      rw [quotientConjHom_apply_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      rfl
    have hwmemE : (w : G) *
        ((e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹) * (w : G)⁻¹ ∈ c.E :=
      (Subgroup.mem_normalizer_iff.mp (hM_E w.2)
        ((e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹)).mp hmemE
    have h2 : quotientConjHom D.M c.E D.Z hM_E hM_Z w
        (QuotientGroup.mk
          (⟨(e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹, hmemE⟩ : ↥c.E)) =
        QuotientGroup.mk
          (⟨(w : G) * ((e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹) * (w : G)⁻¹,
            hwmemE⟩ : ↥c.E) :=
      quotientConjHom_apply_mk hM_E hM_Z w ⟨_, hmemE⟩
    rw [h1, h2]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    have hq := quadratic_fixed X h4 h23 h39 h40 h1930 hneq e.2 hvW hwW
    calc (w : G) * ((e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹) * (w : G)⁻¹
        = (w : G) * ((e : G) * (v : G) * (e : G)⁻¹ * (v : G)⁻¹) * (w : G)⁻¹ := by
            group
      _ = (e : G) * (v : G) * (e : G)⁻¹ * (v : G)⁻¹ := hq
      _ = (e : G) * ((v : G) * (e : G) * (v : G)⁻¹)⁻¹ := by
            group

private theorem quotientConjHom_fixed_F_le_fixed_v {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {v w : ↥D.M} (hvW : (v : G) ∈ X.W) (hwW : (w : G) ∈ X.W)
    (hwZh : (w : G) ∉ X.Zh) :
    ∀ q ∈ (X.F.subgroupOf c.E).map (QuotientGroup.mk' (D.Z.subgroupOf c.E)),
      quotientConjHom D.M c.E D.Z hM_E hM_Z w q = q →
      quotientConjHom D.M c.E D.Z hM_E hM_Z v q = q := by
  intro q hq hwq
  obtain ⟨f, hfF, rfl⟩ := Subgroup.mem_map.mp hq
  have hfF' : (f : G) ∈ X.F := Subgroup.mem_subgroupOf.mp hfF
  have hcommZ : (w : G) * (f : G) * (w : G)⁻¹ * (f : G)⁻¹ ∈ D.Z := by
    change quotientConjAut (hM_E w.2) (hM_Z w.2) (QuotientGroup.mk f) =
      QuotientGroup.mk f at hwq
    rw [quotientConjAut_apply_mk] at hwq
    have hmem := (QuotientGroup.eq_iff_div_mem).mp hwq
    rw [div_eq_mul_inv] at hmem
    exact Subgroup.mem_subgroupOf.mp (by
      simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem)
  have hfp := s2341_P X h4 h23 h39 h1930 hneq hwW hwZh hfF' hcommZ
  change quotientConjAut (hM_E v.2) (hM_Z v.2) (QuotientGroup.mk f) = QuotientGroup.mk f
  rw [quotientConjAut_apply_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  have hfv : (f : G) * (v : G) = (v : G) * (f : G) :=
    (Subgroup.mem_centralizer_iff.mp hfp.2 (v : G) hvW).symm
  show (v : G) * (f : G) * (v : G)⁻¹ = (f : G)
  calc (v : G) * (f : G) * (v : G)⁻¹ = ((f : G) * (v : G)) * (v : G)⁻¹ := by rw [← hfv]
    _ = (f : G) := by group

private theorem quotientConjAut_hypotheses₁ {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {x v w : G} (hxM : x ∈ D.M) (hxodd : Odd (orderOf x))
    (hvM : v ∈ D.M) (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹)
    (hwM : w ∈ D.M) (hwW : w ∈ X.W) :
    let xQ := quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM)
    let vQ := quotientConjAut (E := c.E) (K := D.Z) (hM_E hvM) (hM_Z hvM)
    let wQ := quotientConjAut (E := c.E) (K := D.Z) (hM_E hwM) (hM_Z hwM)
    Odd (orderOf xQ) ∧ vQ * vQ = 1 ∧ wQ * wQ = 1 ∧ vQ * xQ * vQ⁻¹ = xQ⁻¹ := by
  let Q := ↥c.E ⧸ (D.Z.subgroupOf c.E)
  let Φ : D.M →* MulAut Q := quotientConjHom D.M c.E D.Z hM_E hM_Z
  let xQ : MulAut Q := Φ ⟨x, hxM⟩
  let vQ : MulAut Q := Φ ⟨v, hvM⟩
  let wQ : MulAut Q := Φ ⟨w, hwM⟩
  have hv2G : v * v = 1 := by
    simpa [pow_two] using (X.isElemAbelian_W h4 h1930).2 v hvW
  have hw2G : w * w = 1 := by
    simpa [pow_two] using (X.isElemAbelian_W h4 h1930).2 w hwW
  have hxoddQ : Odd (orderOf xQ) :=
    hxodd.of_dvd_nat (by
      have := orderOf_map_dvd Φ ⟨x, hxM⟩
      simpa [xQ] using this)
  have hvQ2 : vQ * vQ = 1 := by
    have h2 : (⟨v, hvM⟩ : D.M) * ⟨v, hvM⟩ = 1 := Subtype.ext hv2G
    change Φ ⟨v, hvM⟩ * Φ ⟨v, hvM⟩ = 1
    rw [← map_mul, h2, map_one]
  have hwQ2 : wQ * wQ = 1 := by
    have h2 : (⟨w, hwM⟩ : D.M) * ⟨w, hwM⟩ = 1 := Subtype.ext hw2G
    change Φ ⟨w, hwM⟩ * Φ ⟨w, hwM⟩ = 1
    rw [← map_mul, h2, map_one]
  have hxvQ : vQ * xQ * vQ⁻¹ = xQ⁻¹ := by
    have h2 : (⟨v, hvM⟩ : D.M) * ⟨x, hxM⟩ * ⟨v, hvM⟩⁻¹ = ⟨x, hxM⟩⁻¹ :=
      Subtype.ext (by simpa using hinv)
    change Φ ⟨v, hvM⟩ * Φ ⟨x, hxM⟩ * (Φ ⟨v, hvM⟩)⁻¹ = (Φ ⟨x, hxM⟩)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, h2, map_inv]
  exact ⟨hxoddQ, hvQ2, hwQ2, hxvQ⟩

private theorem quotientConjAut_hypotheses₂ {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {x v w : G} (hxM : x ∈ D.M) (hvM : v ∈ D.M) (hvW : v ∈ X.W) (hwM : w ∈ D.M)
    (hwW : w ∈ X.W) (hxw : x * w * x⁻¹ * w⁻¹ ∈ centModE D Ch c) :
    let xQ := quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM)
    let vQ := quotientConjAut (E := c.E) (K := D.Z) (hM_E hvM) (hM_Z hvM)
    let wQ := quotientConjAut (E := c.E) (K := D.Z) (hM_E hwM) (hM_Z hwM)
    vQ * wQ = wQ * vQ ∧ wQ * xQ = xQ * wQ := by
  let Q := ↥c.E ⧸ (D.Z.subgroupOf c.E)
  let Φ : D.M →* MulAut Q := quotientConjHom D.M c.E D.Z hM_E hM_Z
  let xQ : MulAut Q := Φ ⟨x, hxM⟩
  let vQ : MulAut Q := Φ ⟨v, hvM⟩
  let wQ : MulAut Q := Φ ⟨w, hwM⟩
  have hvwQ : vQ * wQ = wQ * vQ := by
    have h2 : (⟨v, hvM⟩ : D.M) * ⟨w, hwM⟩ = ⟨w, hwM⟩ * ⟨v, hvM⟩ :=
      Subtype.ext (by
        simpa using congrArg Subtype.val
          ((X.isElemAbelian_W h4 h1930).1.is_comm.comm ⟨v, hvW⟩ ⟨w, hwW⟩))
    change Φ ⟨v, hvM⟩ * Φ ⟨w, hwM⟩ = Φ ⟨w, hwM⟩ * Φ ⟨v, hvM⟩
    rw [← map_mul, h2, map_mul]
  have hg1 : Φ (⟨x * w * x⁻¹ * w⁻¹, hxw.1⟩ : D.M) = 1 :=
    quotientConjAut_eq_one_of_mem_centModE (hM_E hxw.1) (hM_Z hxw.1) hxw
  have hwxQ : wQ * xQ = xQ * wQ := by
    have h1 : xQ * wQ * xQ⁻¹ * wQ⁻¹ = 1 := by
      have hΦ : Φ (⟨x * w * x⁻¹ * w⁻¹, hxw.1⟩ : D.M) = xQ * wQ * xQ⁻¹ * wQ⁻¹ := by
        rw [show (⟨x * w * x⁻¹ * w⁻¹, hxw.1⟩ : D.M) =
          ⟨x, hxM⟩ * ⟨w, hwM⟩ * ⟨x, hxM⟩⁻¹ * ⟨w, hwM⟩⁻¹ from Subtype.ext rfl]
        simp only [map_mul, map_inv, xQ, wQ]
      rw [← hΦ]
      exact hg1
    have h2 : xQ * wQ * xQ⁻¹ = wQ := mul_inv_eq_one.mp h1
    calc wQ * xQ = (xQ * wQ * xQ⁻¹) * xQ := by nth_rewrite 1 [← h2]; rfl
      _ = xQ * wQ := by group
  exact ⟨hvwQ, hwxQ⟩

private theorem quotientConjAut_card_le_four_mul_card_fixed {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {x v w : G} (hxM : x ∈ D.M) (hxodd : Odd (orderOf x))
    (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹) (hwW : w ∈ X.W) (hwZh : w ∉ X.Zh)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ centModE D Ch c) :
    Nat.card (↥c.E ⧸ (D.Z.subgroupOf c.E)) ≤
      4 * Nat.card {q : ↥c.E ⧸ (D.Z.subgroupOf c.E) //
        quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM) q = q} := by
  classical
  have hvM : v ∈ D.M := s2341_W_le_M X h4 h23 h39 h40 h1930 hvW
  have hwM : w ∈ D.M := s2341_W_le_M X h4 h23 h39 h40 h1930 hwW
  let Q := ↥c.E ⧸ (D.Z.subgroupOf c.E)
  let xQ : MulAut Q := quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM)
  let vQ : MulAut Q := quotientConjAut (E := c.E) (K := D.Z) (hM_E hvM) (hM_Z hvM)
  let wQ : MulAut Q := quotientConjAut (E := c.E) (K := D.Z) (hM_E hwM) (hM_Z hwM)
  obtain ⟨hxoddQ, hvQ2, hwQ2, hxvQ⟩ := quotientConjAut_hypotheses₁ X h4 h1930
    (hM_E := hM_E) (hM_Z := hM_Z) hxM hxodd hvM hvW hinv hwM hwW
  obtain ⟨hvwQ, hwxQ⟩ := quotientConjAut_hypotheses₂ X h4 h1930
    (hM_E := hM_E) (hM_Z := hM_Z) hxM hvM hvW hwM hwW hxw
  haveI hQcomm : IsMulCommutative Q := by
    constructor
    constructor
    intro a b
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (D.Z.subgroupOf c.E) a
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (D.Z.subgroupOf c.E) b
    rw [← map_mul, ← map_mul, (h39 h1930 c).1.is_comm.comm e f]
  have hBvw := quotientConjHom_fixes_mul_inv X h4 h23 h39 h40 h1930 hneq
    (hM_E := hM_E) (hM_Z := hM_Z) (v := ⟨v, hvM⟩) (w := ⟨w, hwM⟩) hvW hwW
  have hF0 := quotientConjHom_fixed_F_le_fixed_v X h4 h23 h39 h40 h1930 hneq
    (hM_E := hM_E) (hM_Z := hM_Z) (v := ⟨v, hvM⟩) (w := ⟨w, hwM⟩) hvW hwW
    (by simpa using hwZh)
  have hmodule := CFSG.GroupTheory.card_le_four_mul_card_fixed (B := Q)
    (fun q => quotient_sq_eq_one (fun e he => (c.isElemAbelian_E h4 h39 h1930).2 e he) q)
    ((X.F.subgroupOf c.E).map (QuotientGroup.mk' (D.Z.subgroupOf c.E)))
    (by
      have hdvd := Subgroup.index_map_dvd (H := X.F.subgroupOf c.E)
        (f := QuotientGroup.mk' (D.Z.subgroupOf c.E)) (QuotientGroup.mk'_surjective _)
      have hpos : 0 < (X.F.subgroupOf c.E).index :=
        Nat.pos_of_dvd_of_pos (Subgroup.index_dvd_card _) Nat.card_pos
      exact (Nat.le_of_dvd hpos hdvd).trans X.hFindex)
    xQ vQ wQ hxoddQ hvQ2 hwQ2
    (by rwa [show vQ⁻¹ = vQ from inv_eq_of_mul_eq_one_right hvQ2] at hxvQ)
    hvwQ hwxQ hBvw hF0
  have hxQeq : xQ = quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM) := rfl
  rw [hxQeq] at hmodule
  simpa [Q] using hmodule
private theorem quotientConjAut_fixed_index_le_four {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {x v w : G} (hxM : x ∈ D.M) (hxodd : Odd (orderOf x))
    (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹) (hwW : w ∈ X.W) (hwZh : w ∉ X.Zh)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ centModE D Ch c)
    (C : Subgroup (↥c.E ⧸ (D.Z.subgroupOf c.E)))
    (hC : ∀ q, q ∈ C ↔
      quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM) q = q) :
    C.index ≤ 4 := by
  have hcardQ := quotientConjAut_card_le_four_mul_card_fixed X h4 h23 h39 h40 h1930 hneq
    (hM_E := hM_E) (hM_Z := hM_Z) hxM hxodd hvW hinv hwW hwZh hxw
  have hcardC : Nat.card {q : ↥c.E ⧸ (D.Z.subgroupOf c.E) //
      quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM) q = q} = Nat.card C :=
    Nat.card_congr
      { toFun := fun q => ⟨q.1, (hC q.1).mpr q.2⟩
        invFun := fun q => ⟨q.1, (hC q.1).mp q.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcardC] at hcardQ
  have hI := C.index_mul_card
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hle : C.index * Nat.card C ≤ 4 * Nat.card C := by
    rw [hI]
    exact hcardQ
  exact Nat.le_of_mul_le_mul_right hle hpos

private theorem card_map_Zh_subgroupOf {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} [(D.Z.subgroupOf c.E).Normal] (X : S2341Frame D Ch c)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hZhE : X.Zh ≤ c.E) :
    Nat.card ((X.Zh.subgroupOf c.E).map (QuotientGroup.mk' (D.Z.subgroupOf c.E))) =
      2 ^ CFSG.Open.pRank 2 D.Z := by
  have hker : (X.Zh.subgroupOf c.E) ⊓ (QuotientGroup.mk' (D.Z.subgroupOf c.E)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    ext x
    constructor
    · rintro ⟨hxZh, hxZ⟩
      have hxZhG : (x : G) ∈ X.Zh := Subgroup.mem_subgroupOf.mp hxZh
      have hxZG : (x : G) ∈ D.Z := Subgroup.mem_subgroupOf.mp hxZ
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← s2341_Z_inf X h4 h39 h1930 hneq]
        exact ⟨hxZG, hxZhG⟩
      rw [Subgroup.mem_bot] at hxbot ⊢
      exact Subtype.ext hxbot
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  calc Nat.card ((X.Zh.subgroupOf c.E).map (QuotientGroup.mk' (D.Z.subgroupOf c.E)))
      = Nat.card ↥(X.Zh.subgroupOf c.E) :=
        CFSG.card_map_eq_card_of_inf_ker_eq_bot
          (QuotientGroup.mk' (D.Z.subgroupOf c.E)) hker
    _ = Nat.card X.Zh := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZhE).toEquiv
    _ = 2 ^ CFSG.Open.pRank 2 D.Z := X.card_Zh h4 h1930

private theorem two_le_card_inf_of_index_le_four {Q : Type*} [Group Q] [Finite Q]
    (C Z : Subgroup Q) (hC : C.index ≤ 4) (hZ : 8 ≤ Nat.card Z) :
    2 ≤ Nat.card ↥(C ⊓ Z) := by
  have hrel := Subgroup.relIndex_mul_card C Z
  have hrel_le : C.relIndex Z ≤ 4 := by
    have h0 : C.relIndex (⊤ : Subgroup Q) ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact (Nat.pos_of_dvd_of_pos (Subgroup.index_dvd_card C) Nat.card_pos).ne'
    have h := Subgroup.relIndex_le_of_le_right (H := C) (K := Z) (L := ⊤) le_top h0
    rw [Subgroup.relIndex_top_right] at h
    exact h.trans hC
  by_contra hlt
  push Not at hlt
  have hle1 : Nat.card ↥(C ⊓ Z) ≤ 1 := by omega
  have hle := Nat.mul_le_mul hrel_le hle1
  rw [hrel] at hle
  omega

private theorem exists_mem_Zh_of_fixed {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G)}
    {hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G)} [(D.Z.subgroupOf c.E).Normal]
    {x : G} (hxM : x ∈ D.M)
    (C : Subgroup (↥c.E ⧸ (D.Z.subgroupOf c.E)))
    (hC : ∀ q, q ∈ C ↔
      quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM) q = q)
    (hCindex : C.index ≤ 4) :
    ∃ y ∈ X.Zh, y ≠ 1 ∧ x * y * x⁻¹ * y⁻¹ ∈ D.Z := by
  let Q := ↥c.E ⧸ (D.Z.subgroupOf c.E)
  let Zb : Subgroup Q := (X.Zh.subgroupOf c.E).map (QuotientGroup.mk' (D.Z.subgroupOf c.E))
  have hZbcard : Nat.card Zb = 2 ^ CFSG.Open.pRank 2 D.Z :=
    card_map_Zh_subgroupOf X h4 h39 h1930 hneq
      (s2341_comm_eq X h4 h23 h39 h40 h1930 hneq).2.2
  have hZb8 : 8 ≤ Nat.card Zb := by
    rw [hZbcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) hn3
  have h2 := two_le_card_inf_of_index_le_four C Zb hCindex hZb8
  haveI hnt : Nontrivial ↥(C ⊓ Zb) :=
    (Finite.one_lt_card_iff_nontrivial).mp (by omega : 1 < Nat.card ↥(C ⊓ Zb))
  obtain ⟨q, hq1⟩ := exists_ne (1 : ↥(C ⊓ Zb))
  obtain ⟨hqC, hqZb⟩ := q.2
  obtain ⟨e, heK, heq⟩ := Subgroup.mem_map.mp hqZb
  have hy1 : (e : G) ≠ 1 := by
    intro h1
    apply hq1
    apply Subtype.ext
    have he1 : e = 1 := Subtype.ext h1
    rw [← heq, he1, map_one]
    rfl
  have hxq : quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM)
      (QuotientGroup.mk e) = QuotientGroup.mk e :=
    (hC (QuotientGroup.mk e)).mp (by rwa [← heq] at hqC)
  have hcommZ : x * (e : G) * x⁻¹ * (e : G)⁻¹ ∈ D.Z := by
    have h := hxq
    rw [quotientConjAut_apply_mk] at h
    have hmem := (QuotientGroup.eq_iff_div_mem).mp h
    rw [div_eq_mul_inv] at hmem
    exact Subgroup.mem_subgroupOf.mp (by
      simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem)
  exact ⟨(e : G), Subgroup.mem_subgroupOf.mp heK, hy1, hcommZ⟩

private theorem exists_mem_Zh_commutator_mem_Z_of_not_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {x v w : G} (hxM : x ∈ D.M) (hxodd : Odd (orderOf x))
    (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹)
    (hwW : w ∈ X.W) (hwZh : w ∉ X.Zh)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ centModE D Ch c)
    (_hxcent : x ∉ centModE D Ch c) :
    ∃ y ∈ X.Zh, y ≠ 1 ∧ x * y * x⁻¹ * y⁻¹ ∈ D.Z := by
  classical
  have hM_E : D.M ≤ Subgroup.normalizer (c.E : Set G) := by
    rw [c.normalizer_E_eq h4 h39 h1930]
  have hM_Z : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]
    exact (h4 h1930 c).2.2
  have hE_Z : c.E ≤ Subgroup.normalizer (D.Z : Set G) :=
    (c.E_le_pCoreOf_M h39 h1930).trans ((CFSG.openPCoreOf_le 2 D.M).trans hM_Z)
  haveI : (D.Z.subgroupOf c.E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hE_Z
  let Q := ↥c.E ⧸ (D.Z.subgroupOf c.E)
  let Cq : Subgroup Q :=
    { carrier := {q | quotientConjAut (E := c.E) (K := D.Z) (hM_E hxM) (hM_Z hxM) q = q}
      mul_mem' := by
        intro a b ha hb
        change quotientConjAut (hM_E hxM) (hM_Z hxM) (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one (quotientConjAut (hM_E hxM) (hM_Z hxM))
      inv_mem' := by
        intro a ha
        change quotientConjAut (hM_E hxM) (hM_Z hxM) a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hCq : ∀ q, q ∈ Cq ↔ quotientConjAut (E := c.E) (K := D.Z)
      (hM_E hxM) (hM_Z hxM) q = q := fun _ => Iff.rfl
  have hCindex := quotientConjAut_fixed_index_le_four X h4 h23 h39 h40 h1930 hneq
    (hM_E := hM_E) (hM_Z := hM_Z) hxM hxodd hvW hinv hwW hwZh hxw Cq hCq
  exact exists_mem_Zh_of_fixed X h4 h23 h39 h40 h1930 hneq hn3
    (hM_E := hM_E) (hM_Z := hM_Z) hxM Cq hCq hCindex

private theorem conj_pow_eq_of_conj_eq {x z : G} (h : x * z * x⁻¹ = z) (k : ℕ) :
    x * z ^ k * x⁻¹ = z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x * z ^ (k + 1) * x⁻¹ = (x * z ^ k * x⁻¹) * (x * z * x⁻¹) := by
          rw [pow_succ]; group
      _ = z ^ k * z := by rw [ih, h]
      _ = z ^ (k + 1) := by rw [pow_succ]

private theorem pow_conj_eq_mul_pow {x y z : G} (hzy : z * y = y * z)
    (hxyeq : x * y * x⁻¹ = y * z) (hxzeq : x * z * x⁻¹ = z) (k : ℕ) :
    x ^ k * y * (x ^ k)⁻¹ = y * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x ^ (k + 1) * y * (x ^ (k + 1))⁻¹
        = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by group
      _ = x * (y * z ^ k) * x⁻¹ := by rw [ih]
      _ = (x * y * x⁻¹) * (x * z ^ k * x⁻¹) := by group
      _ = (y * z) * z ^ k := by rw [hxyeq, conj_pow_eq_of_conj_eq hxzeq]
      _ = y * z ^ (k + 1) := by rw [pow_succ]; group

private theorem pow_eq_one_of_pow_conj {x y z : G}
    (hzpow : ∀ k : ℕ, x ^ k * y * (x ^ k)⁻¹ = y * z ^ k) : z ^ orderOf x = 1 := by
  have hk := hzpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
  have h1 : y * 1 = y * z ^ orderOf x := by
    rw [mul_one]
    exact hk
  have h2 : (1 : G) = z ^ orderOf x := mul_left_cancel h1
  exact h2.symm

private theorem commute_of_commutator_mem_Z {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D) {x y : G}
    (hxodd : Odd (orderOf x)) (hxZ : x ∈ Subgroup.centralizer (D.Z : Set G))
    (hyE : y ∈ c.E) (hzZ : x * y * x⁻¹ * y⁻¹ ∈ D.Z) : x * y = y * x := by
  classical
  set z : G := x * y * x⁻¹ * y⁻¹ with hzdef
  have hzE : z ∈ c.E :=
    (uc22p22v_le_conjClosure D.M c.V) (uc22p22v_le_conjClosure c.N D.Z hzZ)
  have hzy : z * y = y * z := by
    have hEcomm := c.isMulCommutative_E h39 h1930
    exact congrArg Subtype.val (hEcomm.is_comm.comm ⟨z, hzE⟩ ⟨y, hyE⟩)
  have hxz : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hxZ z hzZ).symm
  have hxzeq : x * z * x⁻¹ = z := by
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [hxz]
      _ = z := by group
  have hxyeq : x * y * x⁻¹ = y * z := by
    have h1 : x * y * x⁻¹ = z * y := by
      rw [hzdef]
      group
    rwa [hzy] at h1
  have hzo : z ^ orderOf x = 1 :=
    pow_eq_one_of_pow_conj fun k => pow_conj_eq_mul_pow hzy hxyeq hxzeq k
  have hz2 : z ^ 2 = 1 := (c.isElemAbelian_Z h4 h1930).2 z hzZ
  have hdvd2 : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
  have hdvdo : orderOf z ∣ orderOf x := orderOf_dvd_iff_pow_eq_one.mpr hzo
  have hz1 : z = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hxodd)
      hdvd2 hdvdo)
  rw [hzdef] at hz1
  have h1 : x * y * x⁻¹ = y := by
    have h2 : (x * y * x⁻¹) * y⁻¹ = 1 := by simpa [mul_assoc] using hz1
    exact mul_inv_eq_one.mp h2
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h1]

private theorem exists_mem_Zh_commutator_mem_Z_of_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {x : G}
    (hxcent : x ∈ centModE D Ch c) :
    ∃ y ∈ X.Zh, y ≠ 1 ∧ x * y * x⁻¹ * y⁻¹ ∈ D.Z := by
  have hZhE : X.Zh ≤ c.E := (s2341_comm_eq X h4 h23 h39 h40 h1930 hneq).2.2
  have hcard : 2 ≤ Nat.card X.Zh := by
    rw [X.card_Zh h4 h1930]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Nontrivial X.Zh := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨y, hy⟩ := exists_ne (1 : X.Zh)
  refine ⟨(y : G), y.2, ?_, hxcent.2.2 (y : G) (hZhE y.2)⟩
  intro h1
  exact hy (Subtype.ext h1)

private theorem exists_mem_Zh_commutator_mem_Z {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {x v w : G} (hxM : x ∈ D.M) (hxodd : Odd (orderOf x))
    (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹)
    (hwW : w ∈ X.W) (hwZh : w ∉ X.Zh)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ centModE D Ch c) :
    ∃ y ∈ X.Zh, y ≠ 1 ∧ x * y * x⁻¹ * y⁻¹ ∈ D.Z := by
  by_cases hxcent : x ∈ centModE D Ch c
  · exact exists_mem_Zh_commutator_mem_Z_of_mem X h4 h23 h39 h40 h1930 hneq hn3 hxcent
  · exact exists_mem_Zh_commutator_mem_Z_of_not_mem X h4 h23 h39 h40 h1930 hneq hn3 hxM
      hxodd hvW hinv hwW hwZh hxw hxcent

private theorem eq_one_of_inv_sq_mem_conj_pCore {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h1930 : H1930 D) {x : G}
    (hxodd : Odd (orderOf x))
    (hx2O : x⁻¹ ^ 2 ∈ conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h) : x = 1 := by
  have hO2p : IsPGroup 2 (CFSG.Open.pCoreOf 2 D.M) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)) D.M.subtype
  have hO2h : IsPGroup 2 (conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h) :=
    IsPGroup.map hO2p (MulAut.conj X.h⁻¹).toMonoidHom
  have hodd2 : Odd (orderOf (x⁻¹ ^ 2)) := by
    have hdvd : orderOf (x⁻¹ ^ 2) ∣ orderOf x := by
      rw [inv_pow, orderOf_inv]
      exact orderOf_pow_dvd (x := x) 2
    exact hxodd.of_dvd_nat hdvd
  obtain ⟨k, hk⟩ := hO2h ⟨x⁻¹ ^ 2, hx2O⟩
  have hkg : (x⁻¹ ^ 2) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hone : orderOf (x⁻¹ ^ 2) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hodd2.coprime_two_right.pow_right k)
      (dvd_refl _) (orderOf_dvd_of_pow_eq_one hkg)
  have hx2 : x ^ 2 = 1 := by
    have h1 : x⁻¹ ^ 2 = 1 := orderOf_eq_one_iff.mp hone
    rw [inv_pow] at h1
    simpa using congrArg Inv.inv h1
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rcases hxodd with ⟨j, hj⟩
    omega

theorem s2341_core {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {x v w : G} (hxM : x ∈ D.M) (hx1 : x ≠ 1)
    (hxodd : Odd (orderOf x)) (hvW : v ∈ X.W) (hinv : v * x * v⁻¹ = x⁻¹)
    (hwW : w ∈ X.W) (hwZh : w ∉ X.Zh)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ centModE D Ch c) : False := by
  classical
  obtain ⟨y, hyZh, hy1, hxy⟩ :=
    exists_mem_Zh_commutator_mem_Z X h4 h23 h39 h40 h1930 hneq hn3 hxM hxodd hvW hinv
      hwW hwZh hxw
  have hxZ : x ∈ Subgroup.centralizer (D.Z : Set G) :=
    mem_centralizer_Z_of_odd_inverted X h4 h23 h39 h40 h1930 hxM hxodd hvW hinv
  have hyE : y ∈ c.E := (s2341_comm_eq X h4 h23 h39 h40 h1930 hneq).2.2 hyZh
  have hxy1 : x * y = y * x :=
    commute_of_commutator_mem_Z h4 h39 h1930 hxodd hxZ hyE hxy
  have hxMh : x ∈ conjSubgroup D.M X.h :=
    X.centralizer_le h4 h1930 hyZh hy1 (Subgroup.mem_centralizer_singleton_iff.mpr hxy1)
  have hvO : v ∈ conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h := X.W_le_pCore h39 h1930 hvW
  have hM_op : D.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 D.M : Set G) := by
    have hsub : ((CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal := by
      rw [CFSG.openPCoreOf_subgroupOf]
      exact CFSG.pCore_normal (p := 2) (G := ↥D.M)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.openPCoreOf_le 2 D.M)).mp hsub
  have hMh_Op : conjSubgroup D.M X.h ≤
      Subgroup.normalizer (conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact E3.conjSubgroup_mono_left X.h hM_op
  have hxinv_norm : x⁻¹ ∈ Subgroup.normalizer
      (conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h : Set G) :=
    ((Subgroup.normalizer _).inv_mem (hMh_Op hxMh))
  have hxvO : x⁻¹ * v * x ∈ conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h := by
    have := (Subgroup.mem_normalizer_iff.mp hxinv_norm v).mp hvO
    simpa using this
  have hv2 : v * v = 1 := by
    simpa [pow_two] using (X.isElemAbelian_W h4 h1930).2 v hvW
  have hx2O : x⁻¹ ^ 2 ∈ conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h := by
    rw [inv_sq_eq_conj_mul hv2 hinv]
    exact Subgroup.mul_mem _ hxvO hvO
  exact hx1 (eq_one_of_inv_sq_mem_conj_pCore X h1930 hxodd hx2O)

private theorem pCoreOf_le_centModE {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    CFSG.Open.pCoreOf 2 D.M ≤ centModE D Ch c := by
  intro m hm
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]
    exact (h4 h1930 c).2.2
  refine ⟨CFSG.openPCoreOf_le 2 D.M hm, hMZ (CFSG.openPCoreOf_le 2 D.M hm), ?_⟩
  intro e he
  have hmem : ⁅e, m⁆ ∈ D.Z :=
    (h39 h1930 c).2.2.1 (Subgroup.commutator_mem_commutator he hm)
  have hinv := D.Z.inv_mem hmem
  have h1 : ⁅e, m⁆⁻¹ = m * e * m⁻¹ * e⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h1] at hinv

private theorem conj_lift_eq_inv {x0 v : G} (hv2 : v * v = 1) :
    v * (x0⁻¹ * v * x0 * v) * v⁻¹ = (x0⁻¹ * v * x0 * v)⁻¹ := by
  have ha2 : (x0⁻¹ * v * x0) ^ 2 = 1 := by
    rw [pow_two]
    calc (x0⁻¹ * v * x0) * (x0⁻¹ * v * x0) = x0⁻¹ * (v * v) * x0 := by group
      _ = 1 := by rw [hv2]; group
  have hainv : (x0⁻¹ * v * x0)⁻¹ = x0⁻¹ * v * x0 :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [show x0⁻¹ * v * x0 * v = (x0⁻¹ * v * x0) * v from rfl]
  rw [_root_.mul_inv_rev, hainv, hvinv]
  calc v * ((x0⁻¹ * v * x0) * v) * v
      = (v * (x0⁻¹ * v * x0)) * (v * v) := by group
    _ = v * (x0⁻¹ * v * x0) := by rw [hv2]; group

private theorem noOddInverted_lift {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D) {x : Bar2 D.M} {v : ↥D.M}
    (hvW : (v : G) ∈ X.W)
    (hvinv : (QuotientGroup.mk v : Bar2 D.M) * x * (QuotientGroup.mk v)⁻¹ = x⁻¹) :
    ∃ (y0 : G) (hy0M : y0 ∈ D.M), (v : G) * y0 * (v : G)⁻¹ = y0⁻¹ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y0, hy0M⟩ = (x ^ 2)⁻¹ := by
  classical
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M) x
  let y0 : G := (x0 : G)⁻¹ * (v : G) * (x0 : G) * (v : G)
  have hy0M : y0 ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem (D.M.mul_mem (D.M.inv_mem x0.2) v.2) x0.2) v.2
  let y0M : ↥D.M := ⟨y0, hy0M⟩
  have hv2 : (v : G) * (v : G) = 1 := by
    simpa [pow_two] using (X.isElemAbelian_W h4 h1930).2 (v : G) hvW
  have hv2M : v * v = 1 := Subtype.ext hv2
  have hv2bar : π v * π v = 1 := by
    rw [← map_mul, hv2M, map_one]
  have hvinv' : π v * x * (π v)⁻¹ = x⁻¹ := hvinv
  have hkey : x⁻¹ * π v * x * π v = x⁻¹ * x⁻¹ := by
    calc x⁻¹ * π v * x * π v = x⁻¹ * (π v * x * (π v)⁻¹) * (π v * π v) := by
          group
      _ = x⁻¹ * x⁻¹ * 1 := by rw [hvinv', hv2bar]
      _ = x⁻¹ * x⁻¹ := by group
  have hx2inv : x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by
    rw [← pow_two (x⁻¹), inv_pow]
  have hy0map : π y0M = (x ^ 2)⁻¹ := by
    have hy0eq : y0M = x0⁻¹ * v * x0 * v := Subtype.ext rfl
    rw [hy0eq, map_mul, map_mul, map_mul, map_inv, hx0, hkey, hx2inv]
  exact ⟨y0, hy0M, conj_lift_eq_inv hv2, hy0map⟩

private theorem noOddInverted_oddPart {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h1930 : H1930 D) {x : Bar2 D.M} {v : ↥D.M} {y0 : G}
    (hy0M : y0 ∈ D.M) (hvy0 : (v : G) * y0 * (v : G)⁻¹ = y0⁻¹)
    (hy0map : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y0, hy0M⟩ = (x ^ 2)⁻¹)
    (x1 : x ≠ 1) (xodd : Odd (orderOf x)) :
    ∃ (a : ℕ) (x' : G) (hx'M : x' ∈ D.M), x' ≠ 1 ∧ Odd (orderOf x') ∧
      (v : G) * x' * (v : G)⁻¹ = x'⁻¹ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x', hx'M⟩ = (x ^ (2 ^ (a + 1)))⁻¹ := by
  classical
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  obtain ⟨a, m, _hm_odd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y0).ne'
  let x' : G := y0 ^ (2 ^ a)
  have hx'M : x' ∈ D.M := D.M.pow_mem hy0M _
  have hx'odd : Odd (orderOf x') := by
    have hdvd : 2 ^ a ∣ orderOf y0 := ⟨m, hord⟩
    have h2apos : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
    have hx'ord : orderOf x' = m := by
      rw [show x' = y0 ^ (2 ^ a) from rfl, orderOf_pow_of_dvd h2apos hdvd, hord,
        Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
    rwa [hx'ord]
  have hx'inv : (v : G) * x' * (v : G)⁻¹ = x'⁻¹ := by
    have := conj_pow_eq_inv_pow hvy0 (2 ^ a)
    simpa [x'] using this
  have hx'π : π ⟨x', hx'M⟩ = (x ^ (2 ^ (a + 1)))⁻¹ := by
    have h1 : (⟨x', hx'M⟩ : ↥D.M) = ⟨y0, hy0M⟩ ^ (2 ^ a) := Subtype.ext rfl
    have harith : 2 * 2 ^ a = 2 ^ (a + 1) := by
      rw [pow_succ]
      ring
    rw [h1, map_pow, show π ⟨y0, hy0M⟩ = (x ^ 2)⁻¹ from hy0map, inv_pow, ← pow_mul, harith]
  have hx'1 : x' ≠ 1 := by
    intro h1
    have hzero : (x ^ (2 ^ (a + 1)))⁻¹ = 1 := by
      rw [← hx'π]
      have hx'eq : (⟨x', hx'M⟩ : ↥D.M) = 1 := Subtype.ext h1
      rw [hx'eq, map_one]
    have h3 : x ^ (2 ^ (a + 1)) = 1 := inv_eq_one.mp hzero
    have hdvd : orderOf x ∣ 2 ^ (a + 1) := orderOf_dvd_iff_pow_eq_one.mpr h3
    have hcop : Nat.Coprime (orderOf x) (2 ^ (a + 1)) :=
      xodd.coprime_two_right.pow_right (a + 1)
    have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd
    exact x1 (orderOf_eq_one_iff.mp hone)
  exact ⟨a, x', hx'M, hx'1, hx'odd, hx'inv, hx'π⟩

private theorem noOddInverted_centModE {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D) {x : Bar2 D.M} {w : ↥D.M}
    (hwcomm : Commute (QuotientGroup.mk w : Bar2 D.M) x) {a : ℕ} {x' : G} (hx'M : x' ∈ D.M)
    (hx'π : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x', hx'M⟩ =
      (x ^ (2 ^ (a + 1)))⁻¹) :
    x' * (w : G) * x'⁻¹ * (w : G)⁻¹ ∈ centModE D Ch c := by
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let g : ↥D.M := ⟨x', hx'M⟩ * w * ⟨x', hx'M⟩⁻¹ * w⁻¹
  have hgπ : π g = 1 := by
    have hg : g = ⟨x', hx'M⟩ * w * ⟨x', hx'M⟩⁻¹ * w⁻¹ := rfl
    rw [hg, map_mul, map_mul, map_mul, map_inv, map_inv, hx'π]
    have hcomm : Commute (π w) (x ^ (2 ^ (a + 1))) := hwcomm.pow_right _
    have hcomm' : Commute (π w) ((x ^ (2 ^ (a + 1)))⁻¹) := hcomm.inv_right
    rw [hcomm'.symm.eq]
    group
  have hgp : g ∈ CFSG.pCore 2 ↥D.M := (QuotientGroup.eq_one_iff g).mp hgπ
  have hgOpen : (g : G) ∈ CFSG.Open.pCoreOf 2 D.M :=
    (CFSG.mem_openPCoreOf_iff g).mpr hgp
  exact pCoreOf_le_centModE h4 h39 h1930 hgOpen

theorem noOddInverted {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥)
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z) : X.NoOddInverted := by
  classical
  intro x x1 xodd v w hvW hwW hwZh hvinv hwcomm
  obtain ⟨y0, hy0M, hvy0, hy0map⟩ := noOddInverted_lift X h4 h1930 hvW hvinv
  obtain ⟨a, x', hx'M, hx'1, hx'odd, hx'inv, hx'π⟩ :=
    noOddInverted_oddPart X h1930 hy0M hvy0 hy0map x1 xodd
  exact s2341_core X h4 h23 h39 h40 h1930 hneq hn3 hx'M hx'1 hx'odd hvW hx'inv hwW hwZh
    (noOddInverted_centModE h4 h39 h1930 hwcomm hx'M hx'π)

end S2341Frame

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
