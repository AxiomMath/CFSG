module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6R77

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {X : Subgroup G} {g : G} (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [card_map_of_injective (MulAut.conj g).injective]

theorem card_le_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H] {p : ℕ} (hp : 0 < p)
    (h : ∀ x : H, x ^ p = 1) : Nat.card H ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (h g))

section PowAut

variable {E : Subgroup G}

@[expose] noncomputable def powAut (hc : ∀ a b : E, a * b = b * a) {k : ℕ}
    (hk : (Nat.card E).Coprime k) : MulAut E :=
  MulEquiv.ofBijective
    ({ toFun := fun e => e ^ k
       map_one' := one_pow k
       map_mul' := fun a b => Commute.mul_pow (hc a b) k } : E →* E)
    hk.pow_left_bijective

theorem powAut_apply (hc : ∀ a b : E, a * b = b * a) {k : ℕ} (hk : (Nat.card E).Coprime k)
    (e : E) : powAut hc hk e = e ^ k :=
  rfl

theorem mul_comm_of_pow {z : MulAut E} {k : ℕ} (hz : ∀ e : E, z e = e ^ k) (σ : MulAut E) :
    σ * z = z * σ :=
  MulEquiv.ext fun e => by rw [MulAut.mul_apply, MulAut.mul_apply, hz, hz, map_pow]

theorem pow_apply_of_pow {z : MulAut E} {k : ℕ} (hz : ∀ e : E, z e = e ^ k) (j : ℕ) (e : E) :
    (z ^ j) e = e ^ (k ^ j) := by
  induction j generalizing e with
  | zero => simp
  | succ j ih => rw [pow_succ, MulAut.mul_apply, ih, hz, ← pow_mul, ← pow_succ']

theorem exists_powAut {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime] (hpr1 : p ∣ r - 1)
    (hE : IsElemAbelian r E) {n : ℕ} (hEcard : Nat.card E = r ^ n) (hn : n ≠ 0) :
    ∃ z : MulAut E, z ≠ 1 ∧ z ^ p = 1 ∧ ∃ k : ℕ, ∀ e : E, z e = e ^ k := by
  haveI : IsMulCommutative E := hE.1
  have hrE : ∀ e : E, e ^ r = 1 := fun e => Subtype.ext (by simpa using hE.2 e e.2)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (ZMod r)ˣ) p (by
    rwa [Nat.card_eq_fintype_card, ZMod.card_units])
  set k := (u : ZMod r).val with hk
  have hku : ((k : ℕ) : ZMod r) = u := ZMod.natCast_zmod_val _
  have hrk : ¬ r ∣ k := by
    intro h
    have h0 : ((k : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff k r).2 h
    rw [hku] at h0
    exact u.ne_zero h0
  have hcop : (Nat.card E).Coprime k := by
    rw [hEcard]
    exact ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hrk).pow_left n
  have hz : ∀ e : E, powAut (fun a b => mul_comm' a b) hcop e = e ^ k := fun e => rfl
  refine ⟨powAut (fun a b => mul_comm' a b) hcop, fun h1 => ?_, ?_, k, hz⟩
  · haveI : Nontrivial E := by
      rw [← Finite.one_lt_card_iff_nontrivial, hEcard]
      exact Nat.one_lt_pow hn hr.out.one_lt
    obtain ⟨e, he⟩ := exists_ne (1 : E)
    have hord : orderOf e = r := orderOf_eq_prime (hrE e) he
    have hek : e ^ k = e ^ 1 := by
      rw [pow_one, ← hz e, h1, MulAut.one_apply]
    rw [pow_eq_pow_iff_modEq, hord, ← ZMod.natCast_eq_natCast_iff, hku, Nat.cast_one] at hek
    have hu1 : u = 1 := Units.ext hek
    rw [hu1, orderOf_one] at hu
    exact hp.out.one_lt.ne hu
  · have hkp : k ^ p ≡ 1 [MOD r] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hku, ← Units.val_pow_eq_pow_val, ← hu,
        pow_orderOf_eq_one, Units.val_one, Nat.cast_one]
    refine MulEquiv.ext fun e => ?_
    rw [pow_apply_of_pow hz, MulAut.one_apply]
    have h := (pow_eq_pow_iff_modEq (x := e) (n := k ^ p) (m := 1)).2
      (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (hrE e)) hkp)
    rwa [pow_one] at h

end PowAut

section Aut

variable {r : ℕ} [hr : Fact r.Prime] {E : Subgroup G}

theorem nonempty_mulAut_mulEquiv_GL (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    Nonempty (MulAut E ≃* GL (Fin 2) (ZMod r)) := by
  haveI : IsMulCommutative E := hE.1
  obtain ⟨φ⟩ := CFSG.Sporadic.RuSchreier.ru_nonempty_mulEquiv_of_elementary (p := r)
    (fun a b : E => mul_comm' a b) (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hEcard
  exact ⟨(MulAut.congr φ).trans (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL 2)⟩

theorem card_le_sq_of_mulAut {p : ℕ} (hp : p.Prime) (hpr : p ≠ r) (hE : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) {B : Subgroup (MulAut E)} (hB : IsElemAbelian p B) :
    Nat.card B ≤ p ^ 2 := by
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_GL hE hEcard
  have hpK : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq hr.out hp).1 h).symm
  have h := CFSG.RankThree.PartOne.LIT.card_le_pow_card_gl (K := ZMod r) (ι := Fin 2) hp hpK
    (B.map e.toMonoidHom) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hB.comm ha hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hB.2 a ha, map_one])
  rwa [card_map_of_injective e.injective, Fintype.card_fin] at h

theorem isCyclic_of_mulAut {p : ℕ} [Fact p.Prime] (hpr : p ≠ r) (hpr1 : ¬ p ∣ r - 1)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) {B : Subgroup (MulAut E)}
    (hB : IsPGroup p B) : IsCyclic B := by
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_GL hE hEcard
  haveI := CFSG.AGLEmbeddingD2.CyclicSylowGL.isCyclic_of_isPGroup_GL (k := ZMod r) (m := 2)
    (d := 2) (by norm_num) le_rfl (by
      rw [ZMod.card]
      exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq Fact.out hr.out).1 h))
    (fun j hj1 hj2 hj => by
      obtain rfl : j = 1 := by omega
      rwa [ZMod.card, pow_one])
    (B.map e.toMonoidHom) (hB.map e.toMonoidHom)
  let e' : B ≃* B.map e.toMonoidHom := B.equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

end Aut

theorem rankThreeGamma_le_of_two_lt_pRank {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hpr : p ≠ r) {M E : Subgroup G} (h76 : PartOne.Section7.Conclusion76 M p) (hEM : E ≤ M)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (h2 : 2 < CFSG.Open.pRank p (M ⊓ normalizer (E : Set G))) : rankThreeGamma 1 r E ≤ M := by
  obtain ⟨P, hPN, hPel, hPcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.out.one_lt (M ⊓ normalizer (E : Set G))
  set m := CFSG.Open.pRank p (M ⊓ normalizer (E : Set G)) with hm
  have hPM : P ≤ M := hPN.trans inf_le_left
  have hPE : P ≤ normalizer (E : Set G) := hPN.trans inf_le_right
  have hPc : ∀ a b : P, a * b = b * a := fun a b => Subtype.ext (hPel.comm a.2 b.2)
  have hPp : ∀ a : P, a ^ p = 1 := fun a => Subtype.ext (by simpa using hPel.2 a a.2)
  let φ : P →* MulAut E := E.normalizerMonoidHom.comp (inclusion hPE)
  have hφ : ∀ (a : P) (e : E), ((φ a e : E) : G) = a * e * (a : G)⁻¹ := fun _ _ => rfl
  have hker : ∀ a : P, φ a = 1 ↔ (a : G) ∈ centralizer (E : Set G) := by
    intro a
    rw [mem_centralizer_iff]
    constructor
    · intro h e he
      have h1 := congrArg (fun f : MulAut E => ((f ⟨e, he⟩ : E) : G)) h
      simp only [hφ, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    · intro h
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hφ, MulAut.one_apply, ← h e e.2, mul_inv_cancel_right]
  set K : Subgroup G := P ⊓ centralizer (E : Set G) with hK
  have hKel : IsElemAbelian p K := hPel.mono inf_le_left
  have hKM : K ≤ M ⊓ centralizer (E : Set G) := inf_le_inf_right _ hPM
  have hcardK : Nat.card φ.ker = Nat.card K := by
    have : φ.ker = K.subgroupOf P := by
      ext a
      rw [MonoidHom.mem_ker, hker, mem_subgroupOf, mem_inf]
      exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
    rw [this]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hPKA : Nat.card P = Nat.card K * Nat.card φ.range := by
    rw [← hcardK, ← index_ker, card_mul_index]
  have hAel : IsElemAbelian p φ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      rw [coe_mul, coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hPc a b]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow, hPp a, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1
    (show Nat.card φ.range ∣ p ^ m from ⟨Nat.card K, by rw [← hPcard, hPKA, mul_comm]⟩)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1
    (show Nat.card K ∣ p ^ m from ⟨Nat.card φ.range, by rw [← hPcard, hPKA]⟩)
  have hij : i + j = m := Nat.pow_right_injective hp.out.two_le
    (show p ^ (i + j) = p ^ m by rw [pow_add, ← hi, ← hj, ← hPKA, hPcard])
  have hj2 : j ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1
    (hj ▸ card_le_sq_of_mulAut hp.out hpr hE hEcard hAel)
  have hi1 : 1 ≤ i := by omega
  have hC : 0 < CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) :=
    lt_of_lt_of_le hi1 (CFSG.SectionRank.le_pRank hp.out.one_lt hKM hKel hi)
  refine h76 r hr.out E hEM hE hEcard hC fun X hXE hXcard => ?_
  have hCN : M ⊓ centralizer (E : Set G) ≤ M ⊓ normalizer (X : Set G) :=
    inf_le_inf_left _ ((centralizer_le hXE).trans (centralizer_le_normalizer _))
  by_cases hi2 : 2 ≤ i
  · exact le_trans hi2 (CFSG.SectionRank.le_pRank hp.out.one_lt (hKM.trans hCN) hKel hi)
  have hi1' : i = 1 := by omega
  have hj2' : j = 2 := by omega
  have hpr1 : p ∣ r - 1 := by
    by_contra hpr1
    haveI := isCyclic_of_mulAut hpr hpr1 hE hEcard hAel.isPGroup
    have h := card_le_of_isCyclic hp.out.pos fun x : φ.range =>
      Subtype.ext (by simpa using hAel.2 x x.2)
    rw [hj, hj2'] at h
    nlinarith [hp.out.two_le]
  obtain ⟨z, hz1, hzp, k, hzk⟩ := exists_powAut hpr1 hE hEcard two_ne_zero
  have hBel : IsElemAbelian p (φ.range ⊔ zpowers z) :=
    hAel.sup_of_commute (isElemAbelian_zpowers hzp) fun a _ b hb => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (mul_comm_of_pow hzk a) n).eq
  have hAB : φ.range = φ.range ⊔ zpowers z :=
    eq_of_le_of_card_ge le_sup_left (by
      rw [hj, hj2']
      exact card_le_sq_of_mulAut hp.out hpr hE hEcard hBel)
  have hzA : z ∈ φ.range := by
    rw [hAB]
    exact mem_sup_right (mem_zpowers z)
  obtain ⟨a, ha⟩ := hzA
  have haE : ∀ e : E, (a : G) * e * (a : G)⁻¹ = ((e ^ k : E) : G) := fun e => by
    rw [← hφ, ha, hzk]
  have haC : (a : G) ∉ centralizer (E : Set G) := fun h => hz1 (ha ▸ (hker a).2 h)
  have hap : orderOf (a : G) = p :=
    orderOf_eq_prime (hPel.2 a a.2) fun h => haC (h ▸ one_mem _)
  have haN : (a : G) ∈ M ⊓ normalizer (X : Set G) := by
    refine mem_inf.2 ⟨hPM a.2, mem_normalizer_of_conj_mem fun x hx => ?_⟩
    rw [haE ⟨x, hXE hx⟩, coe_pow]
    exact X.pow_mem hx k
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, card_bot, hi1', pow_one] at hi
    exact hp.out.one_lt.ne hi
  obtain ⟨c, hcK, hc1⟩ := (bot_or_exists_ne_one K).resolve_left hK1
  have hcP : c ∈ P := (mem_inf.1 hcK).1
  have hcp : orderOf c = p := orderOf_eq_prime (hKel.2 c hcK) hc1
  have hca : Commute c (a : G) := hPel.comm hcP a.2
  have hac : (a : G) ∉ zpowers c := fun h =>
    haC ((zpowers_le.2 (mem_inf.1 hcK).2 : zpowers c ≤ centralizer (E : Set G)) h)
  exact CFSG.GroupTheory.two_le_pRank_of_commute (hCN (hKM hcK)) haN hcp hap hca hac

end CFSG.LocalAnalysis.UniquenessCase.UC6R77

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem r77E2_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G) :
    UC22.F07.R77E2 (dataOfSetup4 hS hU S) := by
  intro _ p hp _ hsp r hr _ hrσ E hEM hEel hEcard h2
  haveI : Fact p.Prime := ⟨((dataOfSetup4 hS hU S).sig_prime p hp).1⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  exact UC6R77.rankThreeGamma_le_of_two_lt_pRank hpr
    (conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp) hEM hEel hEcard h2

end CFSG.LocalAnalysis.UniquenessCase.UC6
