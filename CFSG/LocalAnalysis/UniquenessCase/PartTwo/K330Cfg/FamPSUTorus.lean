module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

private theorem k330c_not_dvd_three_pow_add_one {q k : ℕ} (hq : q % 3 = 1) :
    ¬ 3 ∣ q ^ k + 1 := by
  have h1 : q ^ k % 3 = 1 := by
    rw [Nat.pow_mod, hq]
    norm_num
  have h : (q ^ k + 1) % 3 = 2 := by
    rw [Nat.add_mod, h1]
  intro hd
  have h0 := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem k330c_not_dvd_three_pow {q k : ℕ} (hq : q % 3 = 1) : ¬ 3 ∣ q ^ k := by
  intro hd
  have h3q : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow hd
  have : q % 3 = 0 := Nat.mod_eq_zero_of_dvd h3q
  omega

private theorem k330c_card_hypSU_four {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (hypSU h 2 0) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
  have hZ := (card_hypSU h (r := 2) (ε := 0) (by norm_num : 1 ≤ 2 * 2 + 0)).1
  have hIcc : Finset.Icc 2 (2 * 2 + 0) = {2, 3, 4} := by decide
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton] at hZ
  have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow 2 (p ^ f) (pow_pos h.prime.pos f)
  have h3 : 1 ≤ (p ^ f) ^ 3 := Nat.one_le_pow 3 (p ^ f) (pow_pos h.prime.pos f)
  have h4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow 4 (p ^ f) (pow_pos h.prime.pos f)
  apply Nat.cast_injective (R := ℤ)
  rw [hZ]
  push_cast
  rw [Nat.cast_sub h2, Nat.cast_sub h4]
  push_cast
  ring

private theorem k330c_card_hypSU_five {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (hypSU h 2 1) =
      (p ^ f) ^ 10 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) *
        ((p ^ f) ^ 5 + 1) := by
  have hZ := (card_hypSU h (r := 2) (ε := 1) (by norm_num : 1 ≤ 2 * 2 + 1)).1
  have hIcc : Finset.Icc 2 (2 * 2 + 1) = {2, 3, 4, 5} := by decide
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton] at hZ
  have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow 2 (p ^ f) (pow_pos h.prime.pos f)
  have h3 : 1 ≤ (p ^ f) ^ 3 := Nat.one_le_pow 3 (p ^ f) (pow_pos h.prime.pos f)
  have h4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow 4 (p ^ f) (pow_pos h.prime.pos f)
  have h5 : 1 ≤ (p ^ f) ^ 5 := Nat.one_le_pow 5 (p ^ f) (pow_pos h.prime.pos f)
  apply Nat.cast_injective (R := ℤ)
  rw [hZ]
  push_cast
  rw [Nat.cast_sub h2, Nat.cast_sub h4]
  push_cast
  ring

private theorem k330c_hypDiagHom_injective_on_hypTorus {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {ε : ℕ}
    (hε : ε ≤ 1) : Function.Injective fun t : hypTorus h 2 ε =>
      hypDiagHom h 2 ε hε ⟨t, hypTorus_le_hypBorel h t.2⟩ := by
  intro t t' heq
  obtain ⟨a, d, hd, hp, hg⟩ := t.2
  obtain ⟨a', d', hd', hp', hg'⟩ := t'.2
  have ha : a = a' := by
    funext i
    have h1 := congrArg (fun f : Fin 2 → Kˣ => (f i : K)) heq
    simp only [coe_hypDiagHom] at h1
    rw [hg, hg'] at h1
    exact Units.ext (by simpa [torusEntries] using h1)
  have hd_eq : d = d' := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · funext k
      exact k.elim0
    · funext k
      have hk : k = 0 := Subsingleton.elim k 0
      subst hk
      have h1 : (d 0 : K) = (∏ i : Fin 2, (a i : K) / h.bar (a i))⁻¹ := by
        have := hp
        rw [torusRatio, Fin.prod_univ_one] at this
        exact eq_inv_of_mul_eq_one_right this
      have h2 : (d' 0 : K) = (∏ i : Fin 2, (a' i : K) / h.bar (a' i))⁻¹ := by
        have := hp'
        rw [torusRatio, Fin.prod_univ_one] at this
        exact eq_inv_of_mul_eq_one_right this
      exact Units.ext (by rw [h1, h2, ha])
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [hg, hg', ha, hd_eq]

private theorem k330c_card_hypTorus_two_zero {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (hypTorus h 2 0) = ((p ^ f) - 1) ^ 2 * ((p ^ f) + 1) := by
  let incl : hypTorus h 2 0 →* hypBorel h 2 0 := Subgroup.inclusion (hypTorus_le_hypBorel h)
  let φ : hypTorus h 2 0 →* (Fin 2 → Kˣ) := (hypDiagHom h 2 0 (Nat.zero_le 1)).comp incl
  have hrange : φ.range = evenDiagGroup h 2 := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      have hx : φ y ∈ (hypDiagHom h 2 0 (Nat.zero_le 1)).range := ⟨incl y, rfl⟩
      rwa [range_hypDiagHom_even] at hx
    · intro a ha
      rw [← range_hypDiagHom_even (h := h)] at ha
      obtain ⟨t, htB, htT, ht⟩ :=
        CFSG.Quasithin.H13.Sec53F.Unit.exists_mem_hypTorus_diag h (Nat.zero_le 1) ha
          (by norm_num)
      refine ⟨⟨t, htT⟩, ?_⟩
      show hypDiagHom h 2 0 (Nat.zero_le 1) ⟨t, hypTorus_le_hypBorel h htT⟩ = a
      rw [show (⟨t, hypTorus_le_hypBorel h htT⟩ : hypBorel h 2 0) = ⟨t, htB⟩ from
        Subtype.ext rfl]
      exact ht
  have hinj : Function.Injective φ := k330c_hypDiagHom_injective_on_hypTorus h (Nat.zero_le 1)
  have hcard : Nat.card (hypTorus h 2 0) = Nat.card (evenDiagGroup h 2) := by
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard, card_evenDiagGroup (h := h) (r := 2) (by norm_num)]
  set q := p ^ f
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
  have hq1 : 0 < q + 1 := by omega
  rw [hsq, mul_pow]
  rw [show (q + 1) ^ 2 = (q + 1) * (q + 1) by ring]
  rw [← mul_assoc, Nat.mul_div_left _ hq1]

private theorem k330c_card_hypTorus_two_one {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (hypTorus h 2 1) = ((p ^ f) ^ 2 - 1) ^ 2 := by
  let incl : hypTorus h 2 1 →* hypBorel h 2 1 := Subgroup.inclusion (hypTorus_le_hypBorel h)
  let φ : hypTorus h 2 1 →* (Fin 2 → Kˣ) := (hypDiagHom h 2 1 le_rfl).comp incl
  have hrange : φ.range = ⊤ := by
    refine eq_top_iff.mpr ?_
    intro a _
    have ha : a ∈ (hypDiagHom h 2 1 le_rfl).range := by
      rw [range_hypDiagHom_odd (h := h) (r := 2) (by norm_num : 1 ≤ 2)]
      trivial
    obtain ⟨t, htB, htT, ht⟩ :=
      CFSG.Quasithin.H13.Sec53F.Unit.exists_mem_hypTorus_diag h le_rfl ha (by norm_num)
    refine ⟨⟨t, htT⟩, ?_⟩
    show hypDiagHom h 2 1 le_rfl ⟨t, hypTorus_le_hypBorel h htT⟩ = a
    rw [show (⟨t, hypTorus_le_hypBorel h htT⟩ : hypBorel h 2 1) = ⟨t, htB⟩ from
      Subtype.ext rfl]
    exact ht
  have hinj : Function.Injective φ := k330c_hypDiagHom_injective_on_hypTorus h le_rfl
  have hcard : Nat.card (hypTorus h 2 1) = Nat.card (Fin 2 → Kˣ) := by
    have h1 : Nat.card (hypTorus h 2 1) = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1, hrange]
    exact Subgroup.card_top
  rw [hcard, card_fun_units h 2]

private theorem k330c_index_hypTorus_two_zero {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) :
    ¬ 3 ∣ (hypTorus h 2 0).index := by
  have hT := k330c_card_hypTorus_two_zero h
  have hS := k330c_card_hypSU_four h
  have hidx := Subgroup.card_mul_index (hypTorus h 2 0)
  have h2 : (p ^ f) ^ 2 - 1 = ((p ^ f) - 1) * ((p ^ f) + 1) := by
    rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
  have h4 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 + 1) := by
    rw [show (p ^ f) ^ 4 = ((p ^ f) ^ 2) ^ 2 by ring, mul_comm, ← Nat.sq_sub_sq, one_pow]
  have hM : Nat.card (hypTorus h 2 0) *
      ((p ^ f) ^ 6 * ((p ^ f) + 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 2 + 1)) =
      Nat.card (hypSU h 2 0) := by
    rw [hT, hS, h4, h2]
    ring
  have hidx_eq : (hypTorus h 2 0).index =
      (p ^ f) ^ 6 * ((p ^ f) + 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 2 + 1) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hidx.trans hM.symm)
  rw [hidx_eq]
  intro hd
  rcases Nat.prime_three.dvd_mul.mp hd with h | h4'
  · rcases Nat.prime_three.dvd_mul.mp h with h | h3'
    · rcases Nat.prime_three.dvd_mul.mp h with h | h2'
      · exact k330c_not_dvd_three_pow hq (k := 6) h
      · exact k330c_not_dvd_three_pow_add_one hq (k := 1) (by simpa using h2')
    · exact k330c_not_dvd_three_pow_add_one hq (k := 3) h3'
  · exact k330c_not_dvd_three_pow_add_one hq (k := 2) h4'

private theorem k330c_index_hypTorus_two_one {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) :
    ¬ 3 ∣ (hypTorus h 2 1).index := by
  have hT := k330c_card_hypTorus_two_one h
  have hS := k330c_card_hypSU_five h
  have hidx := Subgroup.card_mul_index (hypTorus h 2 1)
  have h4 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 + 1) := by
    rw [show (p ^ f) ^ 4 = ((p ^ f) ^ 2) ^ 2 by ring, mul_comm, ← Nat.sq_sub_sq, one_pow]
  have hM : Nat.card (hypTorus h 2 1) *
      ((p ^ f) ^ 10 * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 2 + 1) * ((p ^ f) ^ 5 + 1)) =
      Nat.card (hypSU h 2 1) := by
    rw [hT, hS, h4]
    ring
  have hidx_eq : (hypTorus h 2 1).index =
      (p ^ f) ^ 10 * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 2 + 1) * ((p ^ f) ^ 5 + 1) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hidx.trans hM.symm)
  rw [hidx_eq]
  intro hd
  rcases Nat.prime_three.dvd_mul.mp hd with h | h5'
  · rcases Nat.prime_three.dvd_mul.mp h with h | h2'
    · rcases Nat.prime_three.dvd_mul.mp h with h | h3'
      · exact k330c_not_dvd_three_pow hq (k := 10) h
      · exact k330c_not_dvd_three_pow_add_one hq (k := 3) h3'
    · exact k330c_not_dvd_three_pow_add_one hq (k := 2) h2'
  · exact k330c_not_dvd_three_pow_add_one hq (k := 5) h5'

private theorem k330c_card_map_hypProj_ge {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {ε n : ℕ} (hnpos : 0 < n)
    (hker : Nat.card ((hypProj h 2 ε).ker) ≤ n) :
    Nat.card (hypTorus h 2 ε) / n ≤
      Nat.card ((hypTorus h 2 ε).map (hypProj h 2 ε)) := by
  have hcard := Subgroup.card_ker_mul_card_range ((hypProj h 2 ε).subgroupMap (hypTorus h 2 ε))
  rw [Subgroup.ker_subgroupMap] at hcard
  have hrange : ((hypProj h 2 ε).subgroupMap (hypTorus h 2 ε)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MonoidHom.subgroupMap_surjective _ _)
  rw [hrange, Subgroup.card_top] at hcard
  have hle : Nat.card ((hypProj h 2 ε).ker.subgroupOf (hypTorus h 2 ε)) ≤ n := by
    have hinj : Function.Injective (fun x : (hypProj h 2 ε).ker.subgroupOf (hypTorus h 2 ε) =>
        (⟨x.1.1, x.2⟩ : (hypProj h 2 ε).ker)) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : (hypProj h 2 ε).ker => (x : hypSU h 2 ε)) hab
    exact (Nat.card_le_card_of_injective _ hinj).trans hker
  refine Nat.div_le_of_le_mul ?_
  rw [← hcard]
  exact Nat.mul_le_mul_right _ hle

private theorem k330c_exists_conj_map_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ c : G, E.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : x ∈ ((g • P : Sylow p G) : Subgroup G) := by rw [hg]; exact hEQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hsx
  have hconj : (MulAut.conj g⁻¹).toMonoidHom x = s := by rw [← hsx]; simp; group
  rw [hconj]; exact hs

private theorem k330c_exists_conj_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (M : Subgroup G) (hM : ¬ p ∣ M.index) {R : Subgroup G} (hR : IsPGroup p R) :
    ∃ c : G, R.map (MulAut.conj c).toMonoidHom ≤ M := by
  obtain ⟨S0⟩ : Nonempty (Sylow p M) := inferInstance
  set S1 : Subgroup G := (S0 : Subgroup M).map M.subtype with hS1def
  have hS1 : IsPGroup p S1 := S0.isPGroup'.map M.subtype
  have hidx : ¬ p ∣ S1.index := by
    rw [hS1def, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact S0.not_dvd_index h
    · exact hM h
  obtain ⟨c, hc⟩ := k330c_exists_conj_map_le_sylow (hS1.toSylow hidx) hR
  refine ⟨c, hc.trans ?_⟩
  rw [IsPGroup.toSylow_coe]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem torusBig_PSU (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSU n p f) (hq : p ^ f % 3 = 1) : TorusBig J (torusLow n (p ^ f)) := by
  obtain ⟨hp, hf, -, -⟩ := e.admissible
  rcases hn with rfl | rfl
  ·
    obtain ⟨-, K, hfield, hfin, hKcard, ⟨eJ⟩⟩ := e.statedClassicalModel (by decide)
    letI : Field K := hfield
    letI : Finite K := hfin
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hKcard, ← pow_mul, show f * 2 = 2 * f by omega]
    have h : UnitaryFieldData p f K := ⟨hp, hf, hcard⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
    let e' : J ≃* hypPSU h 2 0 := eJ.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
    intro Z hZ hZ9
    let T : Subgroup (hypPSU h 2 0) := (hypTorus h 2 0).map (hypProj h 2 0)
    have hTidx : ¬ 3 ∣ T.index := by
      have hdvd : T.index ∣ (hypTorus h 2 0).index :=
        Subgroup.index_map_dvd (hypTorus h 2 0) (hypProj_surjective h 2 0)
      exact fun h3 => k330c_index_hypTorus_two_zero h hq (h3.trans hdvd)
    let TJ : Subgroup J := T.map e'.symm.toMonoidHom
    have hTJidx : ¬ 3 ∣ TJ.index := by
      rw [show TJ.index = T.index from Subgroup.index_map_equiv T e'.symm]
      exact hTidx
    have hTJcard : Nat.card TJ = Nat.card T :=
      Subgroup.card_map_of_injective e'.symm.injective
    have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h ha' hb']
    have hTJcomm : ∀ a ∈ TJ, ∀ b ∈ TJ, a * b = b * a := by
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hTcomm a' ha' b' hb']
    obtain ⟨y, hy⟩ := k330c_exists_conj_le_of_not_dvd_index TJ hTJidx hZ.isPGroup
    have hTJcent : TJ ≤ Subgroup.centralizer ((Z.map (MulAut.conj y).toMonoidHom) : Set J) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hTJcomm z (hy hz) t ht
    have hTJnorm : TJ ≤ Subgroup.normalizer ((Z.map (MulAut.conj y).toMonoidHom) : Set J) :=
      hTJcent.trans (Subgroup.centralizer_le_normalizer _)
    have hbound : Nat.card TJ ≤ Nat.card (Subgroup.normalizer (Z : Set J)) := by
      have h1 : Nat.card TJ ≤ Nat.card (Subgroup.normalizer
          ((Z.map (MulAut.conj y).toMonoidHom) : Set J)) := Subgroup.card_le_of_le hTJnorm
      have h2 : Nat.card (Subgroup.normalizer
          ((Z.map (MulAut.conj y).toMonoidHom) : Set J)) =
          Nat.card (Subgroup.normalizer (Z : Set J)) := by
        rw [show Subgroup.normalizer ((Z.map (MulAut.conj y).toMonoidHom) : Set J) =
            (Subgroup.normalizer (Z : Set J)).map (MulAut.conj y).toMonoidHom from
          (Subgroup.map_equiv_normalizer_eq Z (MulAut.conj y)).symm]
        exact Subgroup.card_map_of_injective (MulAut.conj y).injective
      exact h2 ▸ h1
    have hker : Nat.card ((hypProj h 2 0).ker) ≤ 4 := by
      rw [ker_hypProj, card_hypScalars h (by norm_num : 1 ≤ 2 * 2 + 0)]
      exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 4 _)
    have hge := k330c_card_map_hypProj_ge h (ε := 0) (n := 4) (by norm_num) hker
    rw [k330c_card_hypTorus_two_zero h] at hge
    have h3 : (p ^ f - 1) ^ 3 ≤ (p ^ f - 1) ^ 2 * (p ^ f + 1) := by
      calc (p ^ f - 1) ^ 3 = (p ^ f - 1) ^ 2 * (p ^ f - 1) := by ring
        _ ≤ (p ^ f - 1) ^ 2 * (p ^ f + 1) := Nat.mul_le_mul_left _ (by omega)
    have hlow : (p ^ f - 1) ^ 3 / 4 ≤ Nat.card T := (Nat.div_le_div_right h3).trans hge
    have hlowT : torusLow 4 (p ^ f) ≤ Nat.card T := by simpa [torusLow] using hlow
    calc torusLow 4 (p ^ f) ≤ Nat.card T := hlowT
      _ = Nat.card TJ := hTJcard.symm
      _ ≤ Nat.card (Subgroup.normalizer (Z : Set J)) := hbound
  ·
    obtain ⟨-, K, hfield, hfin, hKcard, ⟨eJ⟩⟩ := e.statedClassicalModel (by decide)
    letI : Field K := hfield
    letI : Finite K := hfin
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hKcard, ← pow_mul, show f * 2 = 2 * f by omega]
    have h : UnitaryFieldData p f K := ⟨hp, hf, hcard⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    let e' : J ≃* hypPSU h 2 1 := eJ.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
    intro Z hZ hZ9
    let T : Subgroup (hypPSU h 2 1) := (hypTorus h 2 1).map (hypProj h 2 1)
    have hTidx : ¬ 3 ∣ T.index := by
      have hdvd : T.index ∣ (hypTorus h 2 1).index :=
        Subgroup.index_map_dvd (hypTorus h 2 1) (hypProj_surjective h 2 1)
      exact fun h3 => k330c_index_hypTorus_two_one h hq (h3.trans hdvd)
    let TJ : Subgroup J := T.map e'.symm.toMonoidHom
    have hTJidx : ¬ 3 ∣ TJ.index := by
      rw [show TJ.index = T.index from Subgroup.index_map_equiv T e'.symm]
      exact hTidx
    have hTJcard : Nat.card TJ = Nat.card T :=
      Subgroup.card_map_of_injective e'.symm.injective
    have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h ha' hb']
    have hTJcomm : ∀ a ∈ TJ, ∀ b ∈ TJ, a * b = b * a := by
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hTcomm a' ha' b' hb']
    obtain ⟨y, hy⟩ := k330c_exists_conj_le_of_not_dvd_index TJ hTJidx hZ.isPGroup
    have hTJcent : TJ ≤ Subgroup.centralizer ((Z.map (MulAut.conj y).toMonoidHom) : Set J) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hTJcomm z (hy hz) t ht
    have hTJnorm : TJ ≤ Subgroup.normalizer ((Z.map (MulAut.conj y).toMonoidHom) : Set J) :=
      hTJcent.trans (Subgroup.centralizer_le_normalizer _)
    have hbound : Nat.card TJ ≤ Nat.card (Subgroup.normalizer (Z : Set J)) := by
      have h1 : Nat.card TJ ≤ Nat.card (Subgroup.normalizer
          ((Z.map (MulAut.conj y).toMonoidHom) : Set J)) := Subgroup.card_le_of_le hTJnorm
      have h2 : Nat.card (Subgroup.normalizer
          ((Z.map (MulAut.conj y).toMonoidHom) : Set J)) =
          Nat.card (Subgroup.normalizer (Z : Set J)) := by
        rw [show Subgroup.normalizer ((Z.map (MulAut.conj y).toMonoidHom) : Set J) =
            (Subgroup.normalizer (Z : Set J)).map (MulAut.conj y).toMonoidHom from
          (Subgroup.map_equiv_normalizer_eq Z (MulAut.conj y)).symm]
        exact Subgroup.card_map_of_injective (MulAut.conj y).injective
      exact h2 ▸ h1
    have hker : Nat.card ((hypProj h 2 1).ker) ≤ 5 := by
      rw [ker_hypProj, card_hypScalars h (by norm_num : 1 ≤ 2 * 2 + 1)]
      exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 5 _)
    have hge := k330c_card_map_hypProj_ge h (ε := 1) (n := 5) (by norm_num) hker
    rw [k330c_card_hypTorus_two_one h] at hge
    have hlowT : torusLow 5 (p ^ f) ≤ Nat.card T := by simpa [torusLow, T] using hge
    calc torusLow 5 (p ^ f) ≤ Nat.card T := hlowT
      _ = Nat.card TJ := hTJcard.symm
      _ ≤ Nat.card (Subgroup.normalizer (Z : Set J)) := hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
