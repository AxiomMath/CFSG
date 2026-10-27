module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofField
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofMono
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

section Elementary

variable {M : Type*} [Group M]

theorem mulAut_congr_conj {X X' : Type*} [Group X] [Group X'] (φ : X ≃* X') (x : X) :
    MulAut.congr φ (MulAut.conj x) = MulAut.conj (φ x) := by
  ext m
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem conj_pow_eq_pow_pow {g δ : M} {j : ℕ} (h : g * δ * g⁻¹ = δ ^ j) (i : ℕ) :
    g ^ i * δ * (g ^ i)⁻¹ = δ ^ (j ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : ∀ n : ℕ, g * δ ^ n * g⁻¹ = (δ ^ j) ^ n := by
      intro n
      rw [← h, conj_pow]
    calc g ^ (i + 1) * δ * (g ^ (i + 1))⁻¹ = g * (g ^ i * δ * (g ^ i)⁻¹) * g⁻¹ := by
          rw [pow_succ']
          group
      _ = g * δ ^ (j ^ i) * g⁻¹ := by rw [ih]
      _ = δ ^ (j ^ (i + 1)) := by rw [h1, ← pow_mul, pow_succ, mul_comm]

theorem pow_three_pow_mod_three (x a : ℕ) : x ^ (3 ^ a) % 3 = x % 3 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, Sec4.pow_three_mod_three, ih]

theorem exists_conj_eq_pow {g δ : M} (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hδ3 : ∃ k : ℕ, δ ^ 3 ^ k = 1) (hδ9 : δ ^ 3 ≠ 1)
    (hgδ : g * δ * g⁻¹ ∈ Subgroup.zpowers δ) :
    ∃ j : ℕ, j % 3 = 1 ∧ g * δ * g⁻¹ = δ ^ j := by
  obtain ⟨a, ha⟩ := hg3
  obtain ⟨b, hb⟩ := hδ3
  have hfin : IsOfFinOrder δ := isOfFinOrder_iff_pow_eq_one.mpr ⟨3 ^ b, by positivity, hb⟩
  rw [← hfin.mem_powers_iff_mem_zpowers] at hgδ
  obtain ⟨j, hj⟩ := hgδ
  refine ⟨j, ?_, hj.symm⟩
  have h1 := conj_pow_eq_pow_pow hj.symm (3 ^ a)
  rw [ha, one_mul, inv_one, mul_one] at h1
  have h2 : δ ^ (j ^ 3 ^ a) = δ ^ 1 := by rw [← h1, pow_one]
  rw [pow_eq_pow_iff_modEq] at h2
  have h3 : 3 ∣ orderOf δ := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb)
    rcases i with _ | i
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hδ9 (by rw [hi, one_pow])
    · rw [hi, pow_succ]
      exact dvd_mul_left 3 _
  have h4 := Nat.ModEq.of_dvd h3 h2
  rw [Nat.ModEq, pow_three_pow_mod_three] at h4
  exact h4

end Elementary

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_of_normalizes {Y K : Subgroup G} {c g δ : G}
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y))
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    (hgY : g ∈ Y) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hδK : δ ∈ K) (hδ3 : ∃ k : ℕ, δ ^ 3 ^ k = 1) (hδ9 : δ ^ 3 ≠ 1)
    (hgδ : g * δ * g⁻¹ ∈ Subgroup.zpowers δ) :
    g * c * g⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
  have hgN : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hgY
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hδY : δ ∈ Y := hKY hδK
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := exists_model hY hcN hc3 hK
  set τg := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨g, hgN⟩) with hτg
  set τc := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hτc
  have hsuff : MulAut.congr φ τg * MulAut.congr φ τc = MulAut.congr φ τc * MulAut.congr φ τg →
      g * c * g⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
    intro h
    refine commutator_mem_thetaQuotCentralizer_of_commute hgN hcN ?_
    apply (MulAut.congr φ).injective
    simpa only [MonoidHom.comp_apply, map_mul] using h
  have hτg' : τg = MulAut.conj ((⟨g, hgY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :=
    thetaQuotMulAut_of_mem hgY hgN
  rcases core_cases hcN hc3 hK hKf hq hq2 φ with hc1 | ⟨f₀, hf, σ, hσ, g₀, hg₀, hα⟩ |
      ⟨h, hh, e, -, -, hαc, hKblock⟩
  ·
    apply hsuff
    obtain ⟨y, hy, hyc⟩ := hc1
    obtain rfl : y = ⟨c, hcN⟩ := Subtype.ext hyc
    have hτ1 : τc = 1 := hy
    rw [hτ1, map_one, one_mul, mul_one]
  · exact (false_of_field hcN hc3 hK hT hKf hq hq2 φ hf hσ hg₀ hα).elim
  apply hsuff
  have hπ : π = false → UnitaryFieldData p f Kf := fun h => by subst h; exact hKf.unitary
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) Kf)) :=
    Sec13.isPerfect_projImage_slPi hKf hq2
  set δ' : Y := ⟨δ, hδY⟩ with hδ'
  set g' : Y := ⟨g, hgY⟩ with hg'
  obtain ⟨B, -, hBdet, hBe⟩ := hKblock δ' hδK
  obtain ⟨⟨s, hs⟩, hsg⟩ := projOf_surjective _ (φ (g' : Y ⧸ aschbacherSolvableCore 3 Y))
  set d := h * blockHom B * h⁻¹ with hd
  obtain ⟨j, hj, hgδj⟩ := exists_conj_eq_pow hg3 hδ3 hδ9 hgδ
  have hgδ' : g' * δ' * g'⁻¹ = δ' ^ j := Subtype.ext (by simpa using hgδj)
  have himg : φ (g' : Y ⧸ aschbacherSolvableCore 3 Y) *
      φ (δ' : Y ⧸ aschbacherSolvableCore 3 Y) * (φ (g' : Y ⧸ aschbacherSolvableCore 3 Y))⁻¹ =
        φ (δ' : Y ⧸ aschbacherSolvableCore 3 Y) ^ j := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hgδ']
  have hgs : (φ (g' : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk s := by rw [← hsg]; rfl
  have himg' := congrArg (fun x : projImage (slPi π 3 (p ^ f) Kf) =>
    (x : ProjGenLinGroup (Fin 3) Kf)) himg
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, hgs, hBe] at himg'
  have hsd : s * d * s⁻¹ * (d ^ j)⁻¹ ∈ StatedScalars (Fin 3) Kf := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow,
      himg', mul_inv_cancel]
  obtain ⟨ζ, hζ⟩ := hsd
  set S := h⁻¹ * s * h with hS
  have hSconj : S * blockHom B * S⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * blockHom B ^ j := by
    have h1 : s * d * s⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * d ^ j := by
      rw [hζ]
      group
    have hdj : d ^ j = h * blockHom B ^ j * h⁻¹ := by rw [hd, conj_pow_gl]
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ h⁻¹).eq
    calc S * blockHom B * S⁻¹ = h⁻¹ * (s * d * s⁻¹) * h := by rw [hS, hd]; group
      _ = h⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ * (h * blockHom B ^ j * h⁻¹)) * h := by
          rw [h1, hdj]
      _ = (h⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ) * h * blockHom B ^ j := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * blockHom B ^ j := by
          rw [hc]
          group
  obtain ⟨k, hk⟩ := hδ3
  have hBk : B ^ 3 ^ k = 1 := by
    have h1 : φ (δ' : Y ⧸ aschbacherSolvableCore 3 Y) ^ 3 ^ k = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow]
      have : δ' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, QuotientGroup.mk_one, map_one]
    have h2 : (ProjGenLinGroup.mk d) ^ 3 ^ k = 1 := by
      have := congrArg (fun x : projImage (slPi π 3 (p ^ f) Kf) =>
        (x : ProjGenLinGroup (Fin 3) Kf)) h1
      simpa only [SubgroupClass.coe_pow, hBe, Subgroup.coe_one] using this
    rw [← map_pow, hd, conj_pow_gl, ← map_pow] at h2
    have h3 : blockHom (B ^ 3 ^ k) ∈ StatedScalars (Fin 3) Kf := by
      have h4 := mk_eq_one_iff_mem_statedScalars.mp h2
      have h5 : blockHom (B ^ 3 ^ k) = h⁻¹ * (h * blockHom (B ^ 3 ^ k) * h⁻¹) * h := by group
      rw [h5]
      obtain ⟨z, hz⟩ := h4
      rw [← hz]
      refine ⟨z, ?_⟩
      have hc := commute_of_mem_statedScalars ⟨z, rfl⟩ h⁻¹
      rw [hc]
      group
    exact eq_one_of_blockHom_mem_statedScalars (det_pow_eq_one hBdet _) h3
  have hB3 : B ^ 3 ≠ 1 := by
    intro hB3
    apply hδ9
    have h1 : φ (δ' : Y ⧸ aschbacherSolvableCore 3 Y) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, hBe, Subgroup.coe_one]
      rw [← map_pow, hd, conj_pow_gl, ← map_pow, hB3, map_one, mul_one, mul_inv_cancel, map_one]
    rw [← map_pow, MulEquiv.map_eq_one_iff, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      at h1
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := k) (by
      rw [← pow_mul, mul_comm, pow_mul]
      have : δ' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, one_pow])
    have := congrArg Subtype.val h2
    simpa using this
  have h3 : (3 : Kf) ≠ 0 := hKf.three_ne_zero hq
  have hSe := commute_diagE_of_conj_eq hBdet h3 hBk hB3 hj hSconj e
  have hsy : s * (h * diagE e * h⁻¹) = (h * diagE e * h⁻¹) * s := by
    have hs' : s = h * S * h⁻¹ := by rw [hS]; group
    rw [hs']
    calc h * S * h⁻¹ * (h * diagE e * h⁻¹) = h * (S * diagE e) * h⁻¹ := by group
      _ = h * (diagE e * S) * h⁻¹ := by rw [hSe]
      _ = h * diagE e * h⁻¹ * (h * S * h⁻¹) := by group
  have hαc' : ∀ m, (MulAut.congr φ τc m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h * diagE e * h⁻¹) * m *
        (ProjGenLinGroup.mk (h * diagE e * h⁻¹))⁻¹ := hαc
  rw [hτg', mulAut_congr_conj]
  ext m
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hαc', hgs]
  have hmk : ProjGenLinGroup.mk s * ProjGenLinGroup.mk (h * diagE e * h⁻¹) =
      ProjGenLinGroup.mk (h * diagE e * h⁻¹) * ProjGenLinGroup.mk s := by
    rw [← map_mul, hsy, map_mul]
  calc ProjGenLinGroup.mk s * (ProjGenLinGroup.mk (h * diagE e * h⁻¹) * (m :
        ProjGenLinGroup (Fin 3) Kf) * (ProjGenLinGroup.mk (h * diagE e * h⁻¹))⁻¹) *
        (ProjGenLinGroup.mk s)⁻¹ =
      (ProjGenLinGroup.mk s * ProjGenLinGroup.mk (h * diagE e * h⁻¹)) * (m :
        ProjGenLinGroup (Fin 3) Kf) *
          (ProjGenLinGroup.mk s * ProjGenLinGroup.mk (h * diagE e * h⁻¹))⁻¹ := by group
    _ = (ProjGenLinGroup.mk (h * diagE e * h⁻¹) * ProjGenLinGroup.mk s) * (m :
        ProjGenLinGroup (Fin 3) Kf) *
          (ProjGenLinGroup.mk (h * diagE e * h⁻¹) * ProjGenLinGroup.mk s)⁻¹ := by rw [hmk]
    _ = _ := by group

section KFacts

theorem isLThreePi_of_sec11YA {A Y : Subgroup G} {a : G} (hY : Y ∈ thetaComponentsAt 3 a)
    (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hYA : Sec8.IsZ3LThreePi (sec11YA a Y A) ∨ Sec8.IsZ3PGLThreePi (sec11YA a Y A)) :
    Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) := by
  have hbar : ∀ (X : Type) [Group X], (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := fun X _ e =>
    Item1116Proof.nonempty_thetaQuot_equiv_commutator hY hAC hAY hA e
  have hperf : ∀ (X : Type) [Group X], Group.IsPerfect X →
      (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* X) := by
    intro X _ hX e
    obtain ⟨φ⟩ := hbar X e
    exact ⟨φ.trans ((MulEquiv.subgroupCongr (Group.isPerfect_def.mp hX)).trans
      Subgroup.topEquiv)⟩
  have hQS := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY
  have hsolv : ∀ (X : Type) [Group X], Group.IsSolvable X →
      (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) → False := by
    intro X _ hXs e
    obtain ⟨φ⟩ := hbar X e
    have : Group.IsSolvable (Y ⧸ aschbacherSolvableCore 3 Y) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (_root_.commutator X).subtype.comp φ.toMonoidHom)
        ((_root_.commutator X).subtype_injective.comp φ.injective)
    exact fieldCent_not_isSolvable hQS inferInstance
  rcases hYA with hL3 | hPGL
  · obtain ⟨p, f, hp, hf1, ⟨hpf, ⟨e⟩⟩ | ⟨hpf, ⟨e⟩⟩⟩ := hL3
    · obtain ⟨φ⟩ := hperf _ (Sec13.isPerfect_center_projSL p f hf1 hpf).1 e
      exact ⟨p, f, hp, hf1, Or.inl ⟨hpf, ⟨φ⟩⟩⟩
    · by_cases hq2 : 2 < p ^ f
      · obtain ⟨φ⟩ := hperf _ (Sec13.isPerfect_center_projSU p f hf1 hpf hq2).1 e
        exact ⟨p, f, hp, hf1, Or.inr ⟨hpf, ⟨φ⟩⟩⟩
      · exfalso
        have h2 : p ^ f = 2 := by
          have : 2 ≤ p ^ f := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
          omega
        obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
        exact hsolv _ Sec13.isSolvable_projSU_two e
  · obtain ⟨π, p, f, K, _, hK, hmod, ⟨e⟩⟩ := hPGL
    have hq2 : 2 < p ^ f := by
      by_contra hle
      have h2 : p ^ f = 2 := by
        have hf : f ≠ 0 := by have := hK.one_le; omega
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact hsolv _ (Sec13.isSolvable_projImage_glPi_two hK h2) e
      · change p ^ f % 3 = 1 at hmod
        omega
    obtain ⟨φ⟩ := hbar _ e
    have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi fun hπ => by subst hπ; exact hK.unitary)
    exact Sec13.isLThreePi_of_mulEquiv
      (φ.trans ((MulEquiv.subgroupCongr (Sec13.commutator_projImage_glPi hK hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP)))
      (Sec13.isLThreePi_projImage_slPi hK hmod)

theorem kFact1117CubeL3 : KFact1117CubeL3 := by
  intro G _ _ A a c d Y K g y hAe hA27 hAcl hYa hAY hCA hK hT hYA _ hyK hyk hy3 hdy hgYW hg3 hgy
    hgc hgc'
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := by rw [hAcl]; exact Subgroup.subset_closure (by simp)
  have haA : a ∈ A := by rw [hAcl]; exact Subgroup.subset_closure (by simp)
  have hdA : d ∈ A := by rw [hAcl]; exact Subgroup.subset_closure (by simp)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu a haA)
  have hY := isLThreePi_of_sec11YA hYa hAC hAY hAc hYA
  have hcomm := commutator_mem_of_normalizes hY (hAY hcA) (hA3 c hcA) hK hT hgYW.1 hg3 hyK hyk
    hy3 hgy
  set x := g * c * g⁻¹ * c⁻¹ with hx
  have hxd : x ∈ Subgroup.zpowers d := hgc
  have hxA : x ∈ A := Subgroup.zpowers_le.mpr hdA hxd
  have hxa : x ∈ Subgroup.zpowers a := by
    have h1 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer hxA hcomm
    rw [hCA] at h1
    exact h1
  have hx1 : x = 1 := by
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hA3 x hxA
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hx1 (by simpa using hxa)
    have hao : orderOf a = 3 := orderOf_eq_prime (hA3 a haA) ha1
    have hza : Subgroup.zpowers x = Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxa) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hao]
    have hacd : a ∈ Subgroup.closure ({c, d} : Set G) := by
      have h1 : a ∈ Subgroup.zpowers x := hza ▸ Subgroup.mem_zpowers a
      have h2 : Subgroup.zpowers x ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hxd
      have h3 : Subgroup.zpowers d ≤ Subgroup.closure ({c, d} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      exact h3 (h2 h1)
    have hle : A ≤ Subgroup.closure ({c, d} : Set G) := by
      rw [hAcl, Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hacd
      · exact Subgroup.subset_closure (by simp)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hAc c hcA d hdA) (hA3 c hcA) (hA3 d hdA)
    omega
  apply hgc'
  calc g * c * g⁻¹ = x * c := by rw [hx]; group
    _ = c := by rw [hx1, one_mul]

end KFacts

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
