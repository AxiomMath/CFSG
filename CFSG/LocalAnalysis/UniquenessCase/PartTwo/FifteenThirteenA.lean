module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (centralizer (V : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx v hv
    have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.1 hg v).1 hv
    have h1 := hx (g⁻¹ * v * g) hv'
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * v := by group
  · intro hx v hv
    have hv' : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hg v).1 hv
    have h1 := hx (g * v * g⁻¹) hv'
    calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h1]
      _ = x * v := by group

private theorem le_normalizer_inf {H K L : Subgroup G} (hH : L ≤ normalizer (H : Set G))
    (hK : L ≤ normalizer (K : Set G)) : L ≤ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  have h1 := Subgroup.mem_normalizer_iff.1 (hH hg)
  have h2 := Subgroup.mem_normalizer_iff.1 (hK hg)
  exact ⟨fun hx => ⟨(h1 x).1 hx.1, (h2 x).1 hx.2⟩,
    fun hx => ⟨(h1 x).2 hx.1, (h2 x).2 hx.2⟩⟩

private theorem card_le_of_isCyclic_of_isElemAbelian {H : Type*} [Group H] [Finite H] {p : ℕ}
    {E : Subgroup H} (hE : IsElemAbelian p E) (hp : 0 < p) (hc : IsCyclic ↥E) :
    Nat.card ↥E ≤ p := by
  have h1 : Monoid.exponent ↥E = Nat.card E := IsCyclic.exponent_eq_card
  have h2 : Monoid.exponent ↥E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2)
  rw [← h1]
  exact Nat.le_of_dvd hp h2

private theorem mem_normalizer_iff_conjSubgroup_eq {T : Subgroup G} {g : G} :
    g ∈ normalizer (T : Set G) ↔ CFSG.CGT.Timmesfeld75.conjSubgroup g T = T := by
  constructor
  · intro h
    ext x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have hx := Subgroup.mem_normalizer_iff.1 h (g⁻¹ * x * g)
    simpa [mul_assoc] using hx
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h2 : g * y * g⁻¹ ∈ T ↔ y ∈ T := by
      have h3 : g * y * g⁻¹ ∈ T ↔ g⁻¹ * (g * y * g⁻¹) * g ∈ T := by
        rw [← CFSG.CGT.Timmesfeld75.mem_conjSubgroup, h]
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h3
    exact h2.symm

theorem s15_13A_le_T {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) : V ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hN : (V.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.pairFacts.le_M).mpr
      h.pairFacts.le_normalizer
  exact hS.le_of_normal h.pairFacts.le_M hN h.isElemAbelian.isPGroup

theorem s15_13A_le_wClos {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    V ≤ E3.wClos V 0 D.T := by
  refine E3.le_wClos (V := V) (i := 0) (X := D.T) ?_
  rw [E3.mem_gammaSet_iff]
  refine ⟨s15_13A_le_T h, 1, ?_, ?_⟩
  · rw [conjSubgroup_one]
  · rw [conjSubgroup_one, E3.mQuot_self]

theorem s15_13A_isSylowOf_inf_centralizer (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) :
    CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ centralizer (V : Set G))
      (D.M ⊓ centralizer (V : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : centralizer (V : Set G) ≤ D.M := centralizer_le_of_inCalV D h.inCalV
  have hMN : D.M ≤ normalizer (centralizer (V : Set G) : Set G) :=
    h.pairFacts.le_normalizer.trans (normalizer_le_normalizer_centralizer V)
  rw [inf_eq_right.mpr hCM]
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hCM hMN

theorem s15_13A_normalizer_le_normalizer_wClos (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G)) :
    normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤
      normalizer (E3.wClos V 0 D.T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hYH : D.T ⊓ centralizer (V : Set G) ≤ D.M :=
    fun _ hx => D.sylowM.le hx.1
  have hY : IsPGroup 2 (D.T ⊓ centralizer (V : Set G) : Subgroup G) :=
    (s15_13A_isSylowOf_inf_centralizer D h).isPGroup
  have hWY : E3.wClos V 0 D.T ≤ D.T ⊓ centralizer (V : Set G) :=
    le_inf (E3.wClos_le 0 D.T) hW
  exact E3.e3_15_normalizer (V := V) (i := 0) (H := D.M) (S := D.T)
    (Y := D.T ⊓ centralizer (V : Set G)) hS hYH hY hWY

theorem s15_13A_isTI_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G} (hPM : P ≤ D.M)
    (hPC : P ≤ centralizer (V : Set G)) (hP : IsPGroup p P) (hPc : ¬ IsCyclic P) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  intro g
  by_cases hbot : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x₀, hx₀, hx₀1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hbot
  have hx₀V : x₀ ∈ V := hx₀.1
  have hx₀2 : x₀ ^ 2 = 1 := h.isElemAbelian.2 x₀ hx₀V
  have hyV : g⁻¹ * x₀ * g ∈ V := (CFSG.CGT.Timmesfeld75.mem_conjSubgroup.1 hx₀.2)
  have hPx : P ≤ centralizer ({x₀} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.1 (hPC hx) x₀ hx₀V
  have hCx : centralizer ({x₀} : Set G) ≤ D.M :=
    centralizer_le_of_noncyclic D h61 hp hPM hP hPc hx₀1 ⟨1, by simpa using hx₀2⟩ hPx
  have hPle : P ≤ uniqueFourConj g D.M := by
    intro x hx
    rw [UC6.mem_uniqueFourConj_iff]
    apply hCx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxy : (g⁻¹ * x₀ * g) * x = x * (g⁻¹ * x₀ * g) :=
      Subgroup.mem_centralizer_iff.1 (hPC hx) (g⁻¹ * x₀ * g) hyV
    calc x₀ * (g * x * g⁻¹) = g * ((g⁻¹ * x₀ * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * x₀ * g)) * g⁻¹ := by rw [← hxy]
      _ = (g * x * g⁻¹) * x₀ := by group
  have hN := h61 p hp P hPM hP hPc
  have hmem : uniqueFourConj g D.M ∈ calMOf P :=
    ⟨UC6.isMaxTwoLocal_conj D.maxLocal g, hPle⟩
  rw [hN] at hmem
  have heq : uniqueFourConj g D.M = D.M := Set.mem_singleton_iff.mp hmem
  have hgM : g ∈ D.M := by
    have hgN : g ∈ normalizer (D.M : Set G) := UC6.uniqueFourConj_eq_self_iff.1 heq
    rwa [UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal] at hgN
  have hconjV : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V :=
    mem_normalizer_iff_conjSubgroup_eq.1 (h.pairFacts.le_normalizer hgM)
  rw [hconjV, inf_idem]

theorem s15_13A_isCyclic_of_le_centralizer (D : Data G) (h129 : R129_1 D) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G}
    (hPM : P ≤ D.M) (hPC : P ≤ centralizer (V : Set G)) (hP : IsPGroup p P) : IsCyclic P := by
  by_contra hPc
  exact h129 V₀ V h (s15_13A_isTI_of_noncyclic D h61 h hp hPM hPC hP hPc)

theorem s15_13A_not_cyclic_of_card {Q C E R : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hCQ : C ≤ Q) (hn : Q ≤ normalizer (C : Set G)) (hEQ : E ≤ Q)
    (hE : IsElemAbelian p E) (hEC : Nat.card ↥(E ⊓ C) ≤ p)
    (hcard : p ^ 3 ≤ Nat.card ↥E) (hRQ : R ≤ Q) (hQR : Q ≤ C ⊔ R) :
    ¬ IsCyclic ↥R := by
  intro hRcyc
  set CQ : Subgroup Q := C.subgroupOf Q with hCQdef
  set EQ : Subgroup Q := E.subgroupOf Q with hEQdef
  set RQ : Subgroup Q := R.subgroupOf Q with hRQdef
  haveI hCQn : CQ.Normal := by
    rw [hCQdef]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCQ).mpr hn
  set π : Q →* Q ⧸ CQ := QuotientGroup.mk' CQ with hπdef
  have hCQmap : CQ.map π = ⊥ := by
    rw [hπdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hRQcyc : IsCyclic RQ := by
    have e := Subgroup.subgroupOfEquivOfLe hRQ
    haveI : IsCyclic R := hRcyc
    exact isCyclic_of_surjective (e.symm : R →* RQ) e.symm.surjective
  have hRQmap : IsCyclic (RQ.map π) :=
    isCyclic_of_surjective (π.subgroupMap RQ) (π.subgroupMap_surjective RQ)
  have hEQle : EQ ≤ CQ ⊔ RQ := by
    rw [hEQdef, hCQdef, hRQdef, ← Subgroup.subgroupOf_sup hCQ hRQ]
    exact fun x hx => hQR x.2
  have hmap_le : EQ.map π ≤ RQ.map π := by
    calc EQ.map π ≤ (CQ ⊔ RQ).map π := Subgroup.map_mono hEQle
      _ = CQ.map π ⊔ RQ.map π := Subgroup.map_sup _ _ _
      _ = ⊥ ⊔ RQ.map π := by rw [hCQmap]
      _ = RQ.map π := bot_sup_eq _
  have hEQmapcyc : IsCyclic (EQ.map π) := by
    haveI : IsCyclic (RQ.map π) := hRQmap
    exact Subgroup.isCyclic_of_le hmap_le
  have hEQmapel : IsElemAbelian p (EQ.map π) := by
    rw [hEQdef]
    exact (hE.subgroupOf Q).map π
  have hcardmap : Nat.card (EQ.map π) ≤ p :=
    card_le_of_isCyclic_of_isElemAbelian hEQmapel hp.pos hEQmapcyc
  let φ : EQ →* Q ⧸ CQ := π.comp EQ.subtype
  have hrange : φ.range = EQ.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = CQ.subgroupOf EQ := by
    rw [show φ.ker = π.ker.comap EQ.subtype from MonoidHom.comap_ker π EQ.subtype,
      show π.ker = CQ from by rw [hπdef]; exact QuotientGroup.ker_mk' CQ,
      Subgroup.comap_subtype]
  have hcardker : Nat.card φ.ker = Nat.card ↥(E ⊓ C) := by
    rw [hker, show CQ.subgroupOf EQ = (CQ ⊓ EQ).subgroupOf EQ from
      (Subgroup.inf_subgroupOf_right CQ EQ).symm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show CQ ⊓ EQ ≤ EQ from fun _ hx => hx.2)).toEquiv]
    have e3 : CQ ⊓ EQ = (E ⊓ C).subgroupOf Q := by
      rw [hCQdef, hEQdef]
      change C.comap Q.subtype ⊓ E.comap Q.subtype = (E ⊓ C).comap Q.subtype
      rw [← Subgroup.comap_inf, inf_comm]
    rw [e3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show E ⊓ C ≤ Q from fun _ hx => hEQ hx.1)).toEquiv
  have hcardE : Nat.card EQ = Nat.card E := by
    rw [hEQdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv
  have hmain : Nat.card E = Nat.card ↥(E ⊓ C) * Nat.card (EQ.map π) := by
    have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card EQ :=
      Subgroup.card_ker_mul_card_range φ
    rw [hcardker, hrange] at h1
    rw [← hcardE, ← h1]
  have hle : Nat.card E ≤ p * p := by
    rw [hmain]
    exact Nat.mul_le_mul hEC hcardmap
  have hp3 : p ^ 3 ≤ p ^ 2 := by
    calc p ^ 3 ≤ Nat.card E := hcard
      _ ≤ p * p := hle
      _ = p ^ 2 := by ring
  have hple1 : p ≤ 1 := by
    have h2 : p ^ 2 * p ≤ p ^ 2 * 1 := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ ≤ p ^ 2 := hp3
        _ = p ^ 2 * 1 := by ring
    exact Nat.le_of_mul_le_mul_left h2 (pow_pos hp.pos 2)
  have hp2le : 2 ≤ p := hp.two_le
  omega

theorem s15_13A_relIndex_sup {C E : Subgroup G} (hn : E ≤ normalizer (C : Set G)) :
    C.relIndex (C ⊔ E) = (E ⊓ C).relIndex E := by
  have hCE : C ≤ C ⊔ E := le_sup_left
  have hEE : E ≤ C ⊔ E := le_sup_right
  have hCX : (C.subgroupOf (C ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCE).mpr
      (sup_le Subgroup.le_normalizer hn)
  haveI := hCX
  have hsup : E.subgroupOf (C ⊔ E) ⊔ C.subgroupOf (C ⊔ E) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hEE hCE, sup_comm, Subgroup.subgroupOf_self]
  calc C.relIndex (C ⊔ E)
      = (C.subgroupOf (C ⊔ E)).relIndex ⊤ := by
        rw [← Subgroup.subgroupOf_self (C ⊔ E)]
        exact (Subgroup.relIndex_subgroupOf (L := C ⊔ E) (K := C ⊔ E) (H := C) le_rfl).symm
    _ = (C.subgroupOf (C ⊔ E)).relIndex
          (E.subgroupOf (C ⊔ E) ⊔ C.subgroupOf (C ⊔ E)) := by rw [hsup]
    _ = (C.subgroupOf (C ⊔ E)).relIndex (E.subgroupOf (C ⊔ E)) :=
        Subgroup.relIndex_sup_right (H := E.subgroupOf (C ⊔ E))
          (K := C.subgroupOf (C ⊔ E))
    _ = C.relIndex E := Subgroup.relIndex_subgroupOf (L := C ⊔ E) (K := E) (H := C) hEE
    _ = (E ⊓ C).relIndex E := by rw [inf_comm, Subgroup.inf_relIndex_right]

theorem s15_13A_le_sup_inf_normalizer {C Q S : Subgroup G}
    (hCQ : C ≤ Q) (hn : Q ≤ normalizer (C : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S C) :
    Q ≤ C ⊔ (Q ⊓ normalizer (S : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q hq
  have hqN : q ∈ normalizer (C : Set G) := hn hq
  have hS'le : CFSG.Quasithin.conjSubgroup S q ≤ C := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    exact (Subgroup.mem_normalizer_iff.1 hqN x).2 (hS.le hx)
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Quasithin.conjSubgroup S q) C := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hS'le ?_
    have hcard : Nat.card (CFSG.Quasithin.conjSubgroup S q) = Nat.card S :=
      Subgroup.card_map_of_injective (f := (MulAut.conj q⁻¹).toMonoidHom)
        (MulAut.conj q⁻¹).injective
    rw [hcard]
    exact hS.card_eq
  obtain ⟨c, hcC, hconj⟩ := hS.exists_mem_conj hS'
  have hconj' : ∀ x : G, q * x * q⁻¹ ∈ S ↔ c⁻¹ * x * c ∈ S := by
    intro x
    rw [← CFSG.Quasithin.mem_conjSubgroup_iff (A := S) (g := q)]
    exact hconj x
  have hconj_eq : CFSG.Quasithin.conjSubgroup S q = CFSG.Quasithin.conjSubgroup S c⁻¹ := by
    ext x
    rw [CFSG.Quasithin.mem_conjSubgroup_iff, CFSG.Quasithin.mem_conjSubgroup_iff, inv_inv]
    exact hconj' x
  have hqcN : q * c ∈ normalizer (S : Set G) := by
    rw [← CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer]
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hconj_eq,
      CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one]
  have hqcn : q * c ∈ Q ⊓ normalizer (S : Set G) :=
    ⟨Q.mul_mem hq (hCQ hcC), hqcN⟩
  have hqeq : q = (q * c) * c⁻¹ := by group
  rw [hqeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hqcn)
    (Subgroup.mem_sup_left (C.inv_mem hcC))

theorem s15_13A_le_sup_of_isSylowOf {C Y Q R : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hCQ : C ≤ Q) (hn : Q ≤ normalizer (C : Set G)) (hYQ : Y ≤ Q) (hQ : Q ≤ C ⊔ Y)
    (hidx : ∃ k : ℕ, C.relIndex Q = p ^ k) (hR : CFSG.ABGLocalTools.IsSylowOf p R Y) :
    Q ≤ C ⊔ R := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQeq : Q = C ⊔ Y := le_antisymm hQ (sup_le hCQ hYQ)
  obtain ⟨k, hk⟩ := hidx
  have hCY : (Y ⊓ C).relIndex Y = p ^ k := by
    rw [← hk, hQeq]
    exact (s15_13A_relIndex_sup (C := C) (E := Y) (hYQ.trans hn)).symm
  set Y' : Subgroup G := R ⊔ (Y ⊓ C) with hY'def
  have hRY' : R ≤ Y' := by rw [hY'def]; exact le_sup_left
  have hCY' : Y ⊓ C ≤ Y' := by rw [hY'def]; exact le_sup_right
  have hY'Y : Y' ≤ Y := by rw [hY'def]; exact sup_le hR.le inf_le_left
  have hdivR : Y'.relIndex Y ∣ R.relIndex Y := by
    refine ⟨R.relIndex Y', ?_⟩
    have h := Subgroup.relIndex_mul_relIndex (H := R) (K := Y') (L := Y) hRY' hY'Y
    rw [mul_comm] at h
    exact h.symm
  have hdivC : Y'.relIndex Y ∣ (Y ⊓ C).relIndex Y := by
    refine ⟨(Y ⊓ C).relIndex Y', ?_⟩
    have h := Subgroup.relIndex_mul_relIndex (H := Y ⊓ C) (K := Y') (L := Y) hCY' hY'Y
    rw [mul_comm] at h
    exact h.symm
  have hcop : Nat.Coprime p (Y'.relIndex Y) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2
      (CFSG.ABGLocalTools.isSylowOf_iff.1 hR).2.2).coprime_dvd_right hdivR
  have hdiv1 : Y'.relIndex Y ∣ 1 := by
    have hcopk : Nat.Coprime (p ^ k) (Y'.relIndex Y) := hcop.pow_left k
    have hdvd : Y'.relIndex Y ∣ p ^ k := by
      rw [← hCY]
      exact hdivC
    rw [← hcopk.gcd_eq_one]
    exact Nat.dvd_gcd hdvd (dvd_refl _)
  have hrel1 : Y'.relIndex Y = 1 := Nat.dvd_one.1 hdiv1
  have hYle : Y ≤ Y' := Subgroup.relIndex_eq_one.1 hrel1
  have hYeq : Y = Y' := le_antisymm hYle hY'Y
  have hfinal : C ⊔ Y = C ⊔ R := by
    rw [hYeq, hY'def, ← sup_assoc, sup_eq_left.mpr (inf_le_right.trans le_sup_left)]
  exact le_of_eq (hQeq.trans hfinal)

theorem s15_13A_exists_noncyclic (D : Data G) (h129 : R129_1 D) (h61 : UC6.R6_1 D)
    (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ pRank p D.M) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (D.M ⊓ centralizer (V : Set G))) :
    ∃ p ∈ D.sig, ∃ R : Subgroup G, R ≤ D.M ⊓ normalizer (S : Set G) ∧ IsPGroup p R ∧
      ¬ IsCyclic R := by
  obtain ⟨p, hp⟩ := hne
  have hp2 : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp2⟩
  set C : Subgroup G := D.M ⊓ centralizer (V : Set G) with hCdef
  have hCM : C ≤ D.M := inf_le_left
  have hCCV : C ≤ centralizer (V : Set G) := inf_le_right
  have hMN : D.M ≤ normalizer (C : Set G) := by
    rw [hCdef]
    exact le_normalizer_inf Subgroup.le_normalizer
      (h.pairFacts.le_normalizer.trans (normalizer_le_normalizer_centralizer V))
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp2 D.M
  have hcard3 : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp2.pos (UC6.groupPRank_eq_pRank p D.M ▸ hrk p hp)
  set Q : Subgroup G := C ⊔ E with hQdef
  have hCQ : C ≤ Q := le_sup_left
  have hEQ : E ≤ Q := le_sup_right
  have hQM : Q ≤ D.M := sup_le hCM hEM
  have hQN : Q ≤ normalizer (C : Set G) := by
    rw [hQdef]
    exact sup_le Subgroup.le_normalizer (hEM.trans hMN)
  have hidx : ∃ k : ℕ, C.relIndex Q = p ^ k := by
    rw [hQdef, s15_13A_relIndex_sup (hEM.trans hMN)]
    have hdvd : (E ⊓ C).relIndex E ∣ p ^ Open.pRank p D.M := by
      rw [← hEcard]
      exact Subgroup.relIndex_dvd_card (H := E ⊓ C) (K := E)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp2).1 hdvd
    exact ⟨k, hk⟩
  have hEC : Nat.card ↥(E ⊓ C) ≤ p := by
    have hcyc : IsCyclic ↥(E ⊓ C) :=
      s15_13A_isCyclic_of_le_centralizer D h129 h61 h hp
        (le_trans inf_le_left hEM) (le_trans inf_le_right hCCV)
        (hEel.mono inf_le_left).isPGroup
    exact card_le_of_isCyclic_of_isElemAbelian (hEel.mono inf_le_left) hp2.pos hcyc
  have hQsup : Q ≤ C ⊔ (Q ⊓ normalizer (S : Set G)) :=
    s15_13A_le_sup_inf_normalizer hCQ hQN hS
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (Q ⊓ normalizer (S : Set G))
  have hQR : Q ≤ C ⊔ R :=
    s15_13A_le_sup_of_isSylowOf hp2 hCQ hQN inf_le_left hQsup hidx hR
  refine ⟨p, hp, R, ?_, hR.isPGroup, ?_⟩
  · exact le_inf (hR.le.trans inf_le_left |>.trans hQM) (hR.le.trans inf_le_right)
  · exact s15_13A_not_cyclic_of_card hp2 hCQ hQN hEQ hEel hEC hcard3
      (hR.le.trans inf_le_left) hQR

theorem fifteen_thirteen_a (D : Data G) (h129 : R129_1 D) (h61 : UC6.R6_1 D)
    (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ pRank p D.M) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G)) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVX : V ≤ E3.wClos V 0 D.T := s15_13A_le_wClos h
  have hXne : E3.wClos V 0 D.T ≠ ⊥ := fun hbot =>
    h.pairFacts.ne_bot (le_bot_iff.1 (hVX.trans_eq hbot))
  have hX2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ centralizer (V : Set G))
      (D.M ⊓ centralizer (V : Set G)) := s15_13A_isSylowOf_inf_centralizer D h
  obtain ⟨p, hp, R, hRle, hRp, hRc⟩ :=
    s15_13A_exists_noncyclic D h129 h61 hne hrk h hS
  have hRM : R ≤ D.M := hRle.trans inf_le_left
  have hRN : R ≤ normalizer (E3.wClos V 0 D.T : Set G) :=
    hRle.trans (inf_le_right.trans (s15_13A_normalizer_le_normalizer_wClos D h hW))
  exact normalizer_le_of_noncyclic D h61 hp hRM hRp hRc hXne hX2 hRN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
