module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Ua
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Uc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.UniqueSetOfCentralizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.RankThree.PartOne.S12.Sec15Frattini
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.Sec53F.BA (BorelAutData)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ABGLocalTools (IsSylowOf)

section CentMod

variable {Y : Type} [Group Y] {n E : ℕ} {U H : Subgroup Y} {F : Subgroup (MulAut Y)}

open scoped Classical in
private noncomputable def barN (V : Subgroup Y) (x : Y) :
    normalizer (V : Set Y) ⧸ V.subgroupOf (normalizer (V : Set Y)) :=
  if hx : x ∈ normalizer (V : Set Y) then QuotientGroup.mk ⟨x, hx⟩ else 1

private theorem barN_of_mem {x : Y} (hx : x ∈ normalizer (U : Set Y)) :
    barN U x = QuotientGroup.mk ⟨x, hx⟩ := dif_pos hx

private theorem barN_mul {x y : Y} (hx : x ∈ normalizer (U : Set Y))
    (hy : y ∈ normalizer (U : Set Y)) : barN U (x * y) = barN U x * barN U y := by
  rw [barN_of_mem (mul_mem hx hy), barN_of_mem hx, barN_of_mem hy]
  exact QuotientGroup.mk_mul _ (⟨x, hx⟩ : normalizer (U : Set Y)) ⟨y, hy⟩

private theorem barN_one : barN U (1 : Y) = 1 := by
  rw [barN_of_mem (one_mem _)]
  exact QuotientGroup.mk_one _

private theorem barN_inv {x : Y} (hx : x ∈ normalizer (U : Set Y)) :
    barN U x⁻¹ = (barN U x)⁻¹ := by
  rw [barN_of_mem (inv_mem hx), barN_of_mem hx]
  exact QuotientGroup.mk_inv _ (⟨x, hx⟩ : normalizer (U : Set Y))

private theorem barN_pow {x : Y} (hx : x ∈ normalizer (U : Set Y)) (k : ℕ) :
    barN U (x ^ k) = barN U x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, barN_one]
  | succ k ih => rw [pow_succ, barN_mul (pow_mem hx k) hx, ih, pow_succ]

private theorem barN_eq_iff {x y : Y} (hx : x ∈ normalizer (U : Set Y))
    (hy : y ∈ normalizer (U : Set Y)) : barN U x = barN U y ↔ x * y⁻¹ ∈ U := by
  rw [barN_of_mem hx, barN_of_mem hy, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simp [div_eq_mul_inv]

private theorem barN_of_mem_U {u : Y} (hu : u ∈ U) : barN U u = 1 := by
  rw [← barN_one (U := U), barN_eq_iff (le_normalizer hu) (one_mem _)]
  simpa using hu

private theorem barN_mul_comm (D : BorelAutData U H F) {x y : Y}
    (hx : x ∈ normalizer (U : Set Y)) (hy : y ∈ normalizer (U : Set Y)) :
    barN U x * barN U y = barN U y * barN U x := by
  rw [barN_of_mem hx, barN_of_mem hy]
  exact D.quot_comm _ _

private theorem stab_iff' {α : MulAut Y} (hα : U.map α.toMonoidHom = U) (x : Y) :
    α x ∈ U ↔ x ∈ U := by
  have : α x ∈ U ↔ α x ∈ U.map α.toMonoidHom := by rw [hα]
  rw [this]
  exact CFSG.Quasithin.H13.Sec53F.BA.mem_map_equiv_iff' α U x

private theorem pow_action_two (D : FieldBorelData n E U H F) {α : MulAut Y}
    (hα : U.map α.toMonoidHom = U) :
    ∃ j : ℕ, ∀ b ∈ normalizer (U : Set Y), α b ∈ normalizer (U : Set Y) ∧
      barN U (α b) = barN U b ^ 2 ^ j := by
  obtain ⟨g, hg, σ, hσ, hασ⟩ := D.borel.normal_form α (stab_iff' hα)
  obtain ⟨j, hj⟩ := D.pow σ hσ
  refine ⟨j, fun b hb => ?_⟩
  have hαN := CFSG.Quasithin.H13.L32A.C.SkPf.map_mem_normalizer hα hb
  refine ⟨hαN, ?_⟩
  obtain ⟨u, hu, h, hh, rfl⟩ := D.borel.B_eq b hb
  have hhN : h ∈ normalizer (U : Set Y) := D.borel.H_le hh
  have huN : u ∈ normalizer (U : Set Y) := le_normalizer hu
  have hσb : σ (u * h) = σ u * h ^ 2 ^ j := by rw [map_mul, hj h hh]
  have hσuU : σ u ∈ U := (D.borel.F_U σ hσ u).2 hu
  have hσbN : σ (u * h) ∈ normalizer (U : Set Y) := by
    rw [hσb]; exact mul_mem (le_normalizer hσuU) (pow_mem hhN _)
  have hαb : α (u * h) = g * σ (u * h) * g⁻¹ := by rw [hασ]; rfl
  rw [hαb, barN_mul (mul_mem hg hσbN) (inv_mem hg), barN_mul hg hσbN, barN_inv hg,
    barN_mul_comm D.borel hg hσbN, mul_assoc, mul_inv_cancel, mul_one, hσb,
    barN_mul (le_normalizer hσuU) (pow_mem hhN _), barN_pow hhN, barN_of_mem_U hσuU, one_mul,
    barN_mul huN hhN, barN_of_mem_U hu, one_mul]

theorem FieldBorelData.mem_centMod_of_mem (D : FieldBorelData n E U H F) {x : Y} (hx : x ∈ H)
    {s : ℕ} (hs : Odd s) (hxs : x ^ (2 ^ s - 1) = 1) (α : MulAut Y) (hα2 : ∃ e : ℕ, α ^ 2 ^ e = 1)
    (hα : U.map α.toMonoidHom = U) : x ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod U α := by
  obtain ⟨e, he⟩ := hα2
  have hxN : x ∈ normalizer (U : Set Y) := D.borel.H_le hx
  obtain ⟨j, hj⟩ := pow_action_two D hα
  have hiter : ∀ m : ℕ, (α ^ m) x ∈ normalizer (U : Set Y) ∧
      barN U ((α ^ m) x) = barN U x ^ (2 ^ j) ^ m := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using hxN, by simp⟩
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := hj _ h1
      refine ⟨by rw [pow_succ', MulAut.mul_apply]; exact h3, ?_⟩
      rw [pow_succ', MulAut.mul_apply, h4, h2, ← pow_mul, pow_succ]
  obtain ⟨-, h2⟩ := hiter (2 ^ e)
  rw [he, MulAut.one_apply, ← pow_mul] at h2
  have hK1 : x * (x ^ 2 ^ (j * 2 ^ e))⁻¹ ∈ U :=
    (barN_eq_iff hxN (pow_mem hxN _)).1 (by rw [barN_pow hxN]; exact h2)
  have hK2 : x * (x ^ 2 ^ (j * 2 ^ e))⁻¹ = 1 :=
    D.borel.U_inf_H _ hK1 (mul_mem hx (inv_mem (pow_mem hx _)))
  have hK3 : x ^ 2 ^ (j * 2 ^ e) = x := (mul_inv_eq_one.1 hK2).symm
  have hKpos : 1 ≤ 2 ^ (j * 2 ^ e) := Nat.one_le_two_pow
  have hK4 : x ^ (2 ^ (j * 2 ^ e) - 1) = 1 := by
    have h5 : x ^ (2 ^ (j * 2 ^ e) - 1 + 1) = x := by rwa [Nat.sub_add_cancel hKpos]
    rw [pow_succ] at h5
    simpa using h5
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 s (j * 2 ^ e)
  have hdvd : orderOf x ∣ 2 ^ Nat.gcd s (j * 2 ^ e) - 1 := by
    rw [← hg]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxs) (orderOf_dvd_of_pow_eq_one hK4)
  have hgj : Nat.gcd s (j * 2 ^ e) ∣ j := by
    have h1 : Nat.Coprime (Nat.gcd s (j * 2 ^ e)) (2 ^ e) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
        (Nat.Coprime.pow_right e hs.coprime_two_right)
    exact h1.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
  have hx2j : x ^ 2 ^ j = x := by
    have h1 : x ^ (2 ^ j - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1
      (hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hgj))
    have h3 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    calc x ^ 2 ^ j = x ^ (2 ^ j - 1 + 1) := by rw [Nat.sub_add_cancel h3]
      _ = x := by rw [pow_succ, h1, one_mul]
  rw [CFSG.Quasithin.H13.L32A.C.SkPf.mem_centMod]
  refine ⟨hxN, ?_⟩
  exact (barN_eq_iff (hj x hxN).1 hxN).1 (by rw [(hj x hxN).2, ← barN_pow hxN, hx2j])

theorem outer_comm_of_borel [Finite Y] (D : BorelAutData U H F) (a b : Outer Y) :
    a * b = b * a := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner Y) a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (inner Y) b
  obtain ⟨y, σ, hσ, rfl⟩ := exists_conj_mul_of_borel D α
  obtain ⟨z, τ, hτ, rfl⟩ := exists_conj_mul_of_borel D β
  have hy : QuotientGroup.mk' (inner Y) (MulAut.conj y) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨y, rfl⟩
  have hz : QuotientGroup.mk' (inner Y) (MulAut.conj z) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨z, rfl⟩
  rw [map_mul, map_mul, hy, hz, one_mul, one_mul, ← map_mul, ← map_mul, D.F_comm σ hσ τ hτ]

end CentMod

@[expose] def Levi218 {Y : Type} [Group Y] [Finite Y] (n E : ℕ) (U : Subgroup Y) (p : ℕ) : Prop :=
  ∃ (H : Subgroup Y) (F : Subgroup (MulAut Y)), FieldBorelData n E U H F ∧
    ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 →
      ∃ x ∈ H, orderOf x = r ∧ ∃ (S : Subgroup Y) (m : ℕ), S ≤ centralizer {x} ∧ 3 ≤ m ∧
        (IsL2 ↥S m ∨ IsSz ↥S m) ∧
        ((CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 ∧ p ∣ Nat.card S) ∨
          ((∃ Q : Subgroup Y, Q ≤ centralizer {x} ∧ IsElemAbelian p Q ∧ Nat.card Q = p ^ 2) ∧
            ∀ A : Subgroup Y, IsElemAbelian r A → Nat.card A = r ^ 2 →
              p ∣ Nat.card (centralizer (A : Set Y))))

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem map_le_centralizer_singleton (e : Y ≃* Y') {x : Y} {K : Subgroup Y}
    (hK : K ≤ centralizer {x}) : K.map e.toMonoidHom ≤ centralizer {e x} := by
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ rfl
  have h1 := mem_centralizer_iff.1 (hK hk) x rfl
  show e x * e k = e k * e x
  rw [← map_mul, ← map_mul, h1]

theorem centralizer_map_mulEquiv (e : Y ≃* Y') (A : Subgroup Y') :
    centralizer (A : Set Y') =
      (centralizer ((A.map e.symm.toMonoidHom : Subgroup Y) : Set Y)).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    show e.symm a * e.symm y = e.symm y * e.symm a
    rw [← map_mul, ← map_mul, h a ha]
  · intro h a ha
    have h1 := h (e.symm a) ⟨a, ha, rfl⟩
    have h2 := congrArg e h1
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

theorem Levi218.map [Finite Y] [Finite Y'] {n E p : ℕ} (hp : p.Prime) {U : Subgroup Y}
    (h : Levi218 n E U p) (e : Y ≃* Y') : Levi218 n E (U.map e.toMonoidHom) p := by
  obtain ⟨H, F, D, hD⟩ := h
  refine ⟨_, _, D.map e, fun {s r} hs hsn hr hrs => ?_⟩
  obtain ⟨x, hxH, hxo, S, m, hSC, hm, hSt, hmode⟩ := hD hs hsn hr hrs
  refine ⟨e x, mem_map_of_mem _ hxH, by rw [MulEquiv.orderOf_eq, hxo], S.map e.toMonoidHom, m,
    map_le_centralizer_singleton e hSC, hm, ?_, ?_⟩
  · have e' : ↥S ≃* ↥(S.map e.toMonoidHom) := S.equivMapOfInjective e.toMonoidHom e.injective
    rcases hSt with h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e' h)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e' h)
  · rcases hmode with ⟨hrk, hpS⟩ | ⟨⟨Q, hQC, hQe, hQc⟩, hA⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      · rwa [card_map_of_injective e.injective]
    · refine Or.inr ⟨⟨Q.map e.toMonoidHom, map_le_centralizer_singleton e hQC, hQe.map _,
        by rw [card_map_of_injective e.injective, hQc]⟩, fun A hAe hAc => ?_⟩
      have h1 := hA (A.map e.symm.toMonoidHom) (hAe.map _)
        (by rw [card_map_of_injective e.symm.injective, hAc])
      rw [centralizer_map_mulEquiv e A, card_map_of_injective e.injective]
      exact h1

theorem Levi218.of_sylow [Finite Y] {n E p : ℕ} (hp : p.Prime) {U₀ U : Subgroup Y}
    (h : Levi218 n E U₀ p) (hU : IsSylowTwoOf U ⊤) : Levi218 n E U p := by
  obtain ⟨H, F, D, -⟩ := id h
  obtain ⟨k, -, hk⟩ := D.borel.sylow.exists_conj hU
  have := h.map hp (MulAut.conj k)
  rwa [← hk] at this

end Transport

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_zpowers_of_le_centralizer {Y : Type*} [Group Y] {S : Subgroup Y} {a b : Y}
    (hS : S ≤ centralizer {a}) (hb : b ∈ zpowers a) :
    S ≤ centralizer ((zpowers b : Subgroup Y) : Set Y) := by
  refine hS.trans ?_
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (zpowers_le.2 hb))

theorem exists_lift_of_le_centralizer_barInf {L : Subgroup G}
    (hK2 : IsPGroup 2 (CFSG.solvableRadical ↥L)) {A : Subgroup ↥L} {r : ℕ} [Fact r.Prime]
    (hA : IsPGroup r A) (hr2 : r ≠ 2) {S : Subgroup (BarInf L)}
    (hS : S ≤ centralizer ((A.map (piInf L) : Subgroup (BarInf L)) : Set (BarInf L))) :
    ∃ P : Subgroup G, P ≤ L ⊓ centralizer ((A.map L.subtype : Subgroup G) : Set G) ∧
      ∃ φ : ↥P →* ↥S, Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hK2 Fact.out hr2
  have hC : centralizer ((A.map (piInf L) : Subgroup (BarInf L)) : Set (BarInf L)) =
      (centralizer (A : Set ↥L)).map (piInf L) :=
    CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hrK hA
  set C' : Subgroup ↥L := centralizer (A : Set ↥L) ⊓ S.comap (piInf L) with hC'
  have hmem : ∀ c : ↥C', piInf L (c : ↥L) ∈ S := fun c => (mem_inf.1 c.2).2
  let f : ↥C' →* ↥S := ((piInf L).comp C'.subtype).codRestrict S hmem
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    have h1 : s ∈ (centralizer (A : Set ↥L)).map (piInf L) := by
      rw [← hC]
      exact hS hs
    obtain ⟨c, hcC, hce⟩ := mem_map.1 h1
    exact ⟨⟨c, mem_inf.2 ⟨hcC, by rw [mem_comap, hce]; exact hs⟩⟩, Subtype.ext hce⟩
  let e := C'.equivMapOfInjective L.subtype L.subtype_injective
  refine ⟨C'.map L.subtype, ?_, f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    refine mem_inf.2 ⟨c.2, mem_centralizer_iff.2 fun h hh => ?_⟩
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hh
    exact congrArg Subtype.val (mem_centralizer_iff.1 (mem_inf.1 hc).1 a ha)
  · intro k
    have h1 : piInf L ((e.symm (k : ↥(C'.map L.subtype)) : ↥C') : ↥L) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 k.2)
    have h2 : ((e.symm (k : ↥(C'.map L.subtype)) : ↥C') : ↥L) ∈ CFSG.solvableRadical ↥L :=
      (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨n, hn⟩ := hK2 ⟨_, h2⟩
    refine ⟨n, ?_⟩
    have h4 : ((e.symm (k : ↥(C'.map L.subtype)) : ↥C') : ↥L) ^ 2 ^ n = 1 := by
      have h3 := congrArg (fun y : ↥(CFSG.solvableRadical ↥L) => (y : ↥L)) hn
      simpa using h3
    have h5 : e.symm (k : ↥(C'.map L.subtype)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using h4)
    have h6 : (k : ↥(C'.map L.subtype)) ^ 2 ^ n = 1 := by
      apply e.symm.injective
      rw [map_pow, h5, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h6)

theorem exists_orderOf_mem_centralizer_of_barInf {L : Subgroup G}
    (hK2 : IsPGroup 2 (CFSG.solvableRadical ↥L)) {A : Subgroup ↥L} {r : ℕ} [Fact r.Prime]
    (hA : IsPGroup r A) (hr2 : r ≠ 2) {S : Subgroup (BarInf L)}
    (hS : S ≤ centralizer ((A.map (piInf L) : Subgroup (BarInf L)) : Set (BarInf L)))
    {q : ℕ} (hq : q.Prime) (hqS : q ∣ Nat.card S) :
    ∃ z ∈ L ⊓ centralizer ((A.map L.subtype : Subgroup G) : Set G), orderOf z = q := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP, φ, hφ, -⟩ := exists_lift_of_le_centralizer_barInf hK2 hA hr2 hS
  obtain ⟨zb, hzb⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) q hqS
  obtain ⟨z₀, rfl⟩ := hφ zb
  have h1 : q ∣ orderOf z₀ := hzb ▸ orderOf_map_dvd φ z₀
  have h2 : orderOf (z₀ ^ (orderOf z₀ / q)) = q := orderOf_pow_orderOf_div (orderOf_pos z₀).ne' h1
  refine ⟨((z₀ ^ (orderOf z₀ / q) : ↥P) : G), hP (z₀ ^ (orderOf z₀ / q)).2, ?_⟩
  rw [Subgroup.orderOf_coe, h2]

theorem two_le_pRank_of_le_centralizer_barInf {L : Subgroup G}
    (hK2 : IsPGroup 2 (CFSG.solvableRadical ↥L)) {A : Subgroup ↥L} {r : ℕ} [Fact r.Prime]
    (hA : IsPGroup r A) (hr2 : r ≠ 2) {Q : Subgroup (BarInf L)}
    (hQ : Q ≤ centralizer ((A.map (piInf L) : Subgroup (BarInf L)) : Set (BarInf L)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQe : IsElemAbelian p Q) (hQc : Nat.card Q = p ^ 2) :
    2 ≤ CFSG.Open.pRank p (L ⊓ centralizer ((A.map L.subtype : Subgroup G) : Set G)) := by
  obtain ⟨P, hP, φ, hφ, hker⟩ := exists_lift_of_le_centralizer_barInf hK2 hA hr2 hQ
  have h1 : 2 ≤ CFSG.Open.pRank p Q := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hQe hQc
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) = CFSG.Open.pRank p (⊤ : Subgroup ↥Q) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel p hp φ hφ
      ((Nat.Prime.coprime_iff_not_dvd hp).2
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup hker hp hp2))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Q, ← h2,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) P] at h1
  exact h1.trans (CFSG.SectionRank.pRank_mono hp.one_lt hP)

end Lift

section NormalizerLift

variable {G : Type} [Group G] [Finite G]

open scoped Pointwise

theorem exists_lift_mem_normalizer_of_centMod {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T ⊓ L) L) {xb : BarInf L} {r : ℕ}
    (hxb : orderOf xb = r)
    (hcent : ∀ α : MulAut (BarInf L), (∃ e : ℕ, α ^ 2 ^ e = 1) →
      (((T ⊓ L).subgroupOf L).map (piInf L)).map α.toMonoidHom =
        ((T ⊓ L).subgroupOf L).map (piInf L) →
      xb ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod (((T ⊓ L).subgroupOf L).map (piInf L)) α) :
    ∃ x : ↥L, orderOf (x : G) = r ∧ zpowers (x : G) ≤ normalizer (T : Set G) ∧
      ∃ m : ℕ, piInf L x = xb ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := id hS
  have hQ' : (T ⊓ L).subgroupOf L = (Q : Subgroup ↥L) := by
    rw [← hQ]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [hQ'] at hcent
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) xb
  have hd' : piInf L d = xb := hd
  have hTK : T ≤ normalizer (OInf L : Set G) := hTL.trans (normalizer_le_normalizer_OInf L)
  have hdL : (d : G) ∈ L := d.2
  have hcomm : ∀ y ∈ zpowers (d : G), ∀ t ∈ normalizer (L : Set G),
      t ∈ normalizer (((T ⊓ L) ⊔ OInf L : Subgroup G) : Set G) → (∃ a : ℕ, t ^ 2 ^ a = 1) →
        t * y * t⁻¹ * y⁻¹ ∈ (T ⊓ L) ⊔ OInf L := by
    intro y hy t htL htS ⟨a, ha⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← hQ] at htS ⊢
    have h1 : piInf L (d ^ m) ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod
        ((Q : Subgroup ↥L).map (piInf L)) (rhoInf L ⟨t, htL⟩) := by
      rw [map_zpow, hd']
      exact zpow_mem (hcent _ ⟨a, rhoInf_pow_eq_one L htL ha⟩
        (rhoInf_map_eq L (Q : Subgroup ↥L) htL htS)) m
    have h2 := conj_mul_inv_mem_of_mem_centMod L (Q : Subgroup ↥L) htL h1
    rwa [Subgroup.coe_zpow] at h2
  have key : ∀ x ∈ zpowers (d : G), ∀ h ∈ T, x * h * x⁻¹ ∈ T ⊔ OInf L := by
    intro x hx h hh
    have hhL : h⁻¹ ∈ normalizer (L : Set G) := hTL (inv_mem hh)
    have hhS₀ : h⁻¹ ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 (le_normalizer (inv_mem hh)) y,
        ← mem_normalizer_iff.1 hhL y]
    have hhS : h⁻¹ ∈ normalizer (((T ⊓ L) ⊔ OInf L : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_mem hhS₀ (hTK (inv_mem hh))
    obtain ⟨a, ha⟩ := hT ⟨h⁻¹, inv_mem hh⟩
    have h1 := hcomm x hx h⁻¹ hhL hhS ⟨a, congrArg Subtype.val ha⟩
    have e : x * h * x⁻¹ = h * (h⁻¹ * x * h⁻¹⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left hh)
      ((sup_le_sup_right (inf_le_left : T ⊓ L ≤ T) (OInf L) : (T ⊓ L) ⊔ OInf L ≤ T ⊔ OInf L) h1)
  have hdN : (d : G) ∈ normalizer ((T ⊔ OInf L : Subgroup G) : Set G) := by
    have hW : T ⊔ OInf L = Subgroup.closure ((T : Set G) ∪ OInf L) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hle : zpowers (d : G) ≤ normalizer ((T ⊔ OInf L : Subgroup G) : Set G) := by
      rw [hW, Subgroup.le_normalizer_closure_iff]
      intro x hx y hy
      rw [← hW]
      rcases hy with hy | hy
      · exact key x hx y hy
      · have hxL : x ∈ L := by
          obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
          exact zpow_mem hdL m
        exact mem_sup_right ((mem_normalizer_iff.1 (le_normalizer_OInf L hxL) y).1 hy)
    exact hle (mem_zpowers _)
  have hK : IsSylowOf 2 ((T ⊓ L) ⊓ OInf L) (OInf L) :=
    hS.inf_of_le_normalizer (OInf_le L) (le_normalizer_OInf L)
  rw [inf_assoc, inf_eq_right.2 (OInf_le L)] at hK
  have hTsyl : IsSylowOf 2 T (T ⊔ OInf L) := isSylowOf_sup_of_inf hT hTK hK
  obtain ⟨a, ha, hn⟩ := CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf
    hTsyl hdN
  have ha' : a ∈ (OInf L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (OInf L) T hTK]
    exact (sup_comm T (OInf L)) ▸ ha
  obtain ⟨k, hk, h, hh, rfl⟩ := Set.mem_mul.mp ha'
  have hy1N : (k⁻¹ * (d : G)) ∈ normalizer (T : Set G) := by
    have h1 : (h⁻¹ : G) * (k⁻¹ * (d : G)) ∈ normalizer (T : Set G) := by
      simpa [mul_assoc] using hn
    have h2 := mul_mem (le_normalizer hh) h1
    simpa [mul_assoc] using h2
  have hkL : k ∈ L := OInf_le L hk
  have hy1L : k⁻¹ * (d : G) ∈ L := mul_mem (inv_mem hkL) hdL
  set y₁ : ↥L := ⟨k⁻¹ * (d : G), hy1L⟩ with hy₁
  have hpi : piInf L y₁ = xb := by
    have : y₁ = (⟨k, hkL⟩ : ↥L)⁻¹ * d := rfl
    rw [this, map_mul, map_inv, hd']
    have hk1 : piInf L ⟨k, hkL⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_OInf_iff.1 hk)
    rw [hk1, inv_one, one_mul]
  have hrd : r ∣ orderOf y₁ := by
    have h1 : orderOf (piInf L y₁) ∣ orderOf y₁ := orderOf_map_dvd _ _
    rwa [hpi, hxb] at h1
  have h0 : orderOf y₁ ≠ 0 := (orderOf_pos _).ne'
  refine ⟨y₁ ^ (orderOf y₁ / r), ?_, ?_, orderOf y₁ / r, by rw [map_pow, hpi]⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div h0 hrd
  · rw [Subgroup.coe_pow]
    exact zpowers_le.2 (pow_mem hy1N _)

end NormalizerLift

section TrivialAction

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem exists_trivial_action_barInf (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hML : D.M ≤ normalizer (L : Set G))
    (hcomm : ∀ a b : Outer (BarInf L), a * b = b * a)
    (hZ : ∀ y : BarInf L, (∀ x : BarInf L, y * x = x * y) → y = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M) (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (h2 : CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) ≤ 2) :
    ∃ y ∈ D.M, orderOf y = p ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ OInf L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : ↥D.M →* MulAut (BarInf L) := (rhoInf L).comp (inclusion hML) with hρ
  set ψ : ↥D.M →* Outer (BarInf L) := (QuotientGroup.mk' (inner (BarInf L))).comp ρ with hψ
  have hψp : ¬ p ∣ Nat.card ψ.range := by
    intro hdvd
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.range) p hdvd
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨m', hm'T, hm'⟩ := uc22s218u_exists_normalizer_of_comm D.sylowM ψ hcomm m
    have h1 : p ∣ orderOf (m' : G) := by
      rw [Subgroup.orderOf_coe, ← ha, ← Subgroup.orderOf_coe a, ← hm, ← hm']
      exact orderOf_map_dvd ψ m'
    have hyo : orderOf ((m' : G) ^ (orderOf (m' : G) / p)) = p :=
      orderOf_pow_orderOf_div (orderOf_pos _).ne' h1
    have hy1 : zpowers ((m' : G) ^ (orderOf (m' : G) / p)) ≠ ⊥ := by
      intro h
      rw [zpowers_eq_bot.1 h, orderOf_one] at hyo
      exact hp.one_lt.ne hyo
    exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hp hp2 hyo
      (uc22p22r_mem_uniqueSet_of_sp D hp hsp (zpowers_le.2 (pow_mem m'.2 _))
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])) hy1)
      (zpowers_le.2 (pow_mem hm'T _))
  by_contra hno
  push Not at hno
  obtain ⟨E, hEM, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h3
  set ρE : ↥E →* MulAut (BarInf L) := ρ.comp (inclusion hEM) with hρE
  have hEp : ∀ e : ↥E, e ^ p = 1 := fun e =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hEel.2 e e.2)
  have hρEi : Function.Injective ρE := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra he1
    have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
    obtain ⟨l, hl, hl'⟩ := hno e (hEM e.2) (orderOf_eq_prime (hEel.2 e e.2) he1')
    apply hl'
    have h0 : rhoInf L (inclusion hML (inclusion hEM e)) = 1 := he
    have h1 : rhoInf L (inclusion hML (inclusion hEM e)) (piInf L ⟨l, hl⟩) =
        piInf L ⟨l, hl⟩ := by
      rw [h0]
      rfl
    rw [rhoInf_mk] at h1
    have h4 : piInf L (Subgroup.normalizerMonoidHom L (inclusion hML (inclusion hEM e)) ⟨l, hl⟩ *
        (⟨l, hl⟩ : ↥L)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h5 := mem_OInf_iff.2 ((QuotientGroup.eq_one_iff _).1 h4)
    rwa [Subgroup.coe_mul, rhoInf_mk_coe, Subgroup.coe_inv] at h5
  have hρEr : ∀ e, ρE e ∈ inner (BarInf L) := by
    intro e
    have h1 : ψ (inclusion hEM e) = 1 := by
      have h2 : orderOf (ψ (inclusion hEM e)) ∣ p := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow, ← map_pow, hEp e, map_one, map_one]
      rcases (Nat.dvd_prime hp).1 h2 with h | h
      · exact orderOf_eq_one_iff.1 h
      · exfalso
        apply hψp
        have h4 := orderOf_dvd_natCard
          (⟨ψ (inclusion hEM e), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ↥ψ.range)
        rwa [Subgroup.orderOf_mk, h] at h4
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hι : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    refine hZ y fun x => ?_
    have h1 : MulAut.conj y x = x := by rw [hy]; rfl
    rw [MulAut.conj_apply] at h1
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [h1]
  let f : ↥E →* BarInf L := (MonoidHom.ofInjective hι).symm.toMonoidHom.comp
    (ρE.codRestrict (inner (BarInf L)) hρEr)
  have hf : Function.Injective f := (MonoidHom.ofInjective hι).symm.injective.comp
    fun a b h => hρEi (congrArg Subtype.val h)
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) :=
    CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => hEel.1.is_comm.comm a b) hEp hEc
      f hf le_top
  omega

end TrivialAction

section Main

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

theorem le_of_elemAbelian_of_facts {Tor Out : ℕ → Prop} {L M : Subgroup G} {n s r : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G)) (hrM : CFSG.Open.pRank r M ≤ 2)
    {E : Subgroup G} (hEM : E ≤ M) (hEel : IsElemAbelian r E) (hEc : Nat.card E = r ^ 2) :
    E ≤ L := by
  have : Fact r.Prime := ⟨hr⟩
  have hrL : CFSG.Open.pRank r L = 2 := by
    rw [pRank_eq_pRank_barInf hr hrK, hF.pRank_eq_two hs hsn hr hrs]
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  obtain ⟨E₀, hE₀L, hE₀el, hE₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL.ge
  obtain ⟨R₀, hR₀, hE₀R₀⟩ := UC6.exists_isSylowOf_ge (hE₀L.trans hLM) hE₀el.isPGroup
  obtain ⟨k, hkM, hk⟩ := hR₀.exists_mem_conj hR
  have hE₁R : E₀.map (MulAut.conj k).toMonoidHom ≤ R := by
    rintro _ ⟨e, he, rfl⟩
    rw [hk, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show k⁻¹ * (k * e * k⁻¹) * k = e by group]
    exact hE₀R₀ he
  have hE₁L : E₀.map (MulAut.conj k).toMonoidHom ≤ L := by
    rintro _ ⟨e, he, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.1 (hML hkM) e).1 (hE₀L he)
  have hE₁el : IsElemAbelian r (E₀.map (MulAut.conj k).toMonoidHom) := hE₀el.map _
  have hE₁c : Nat.card (E₀.map (MulAut.conj k).toMonoidHom) = r ^ 2 := by
    rw [card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective, hE₀c]
  have hE₁C := le_centralizer_of_facts hF hs hsn hr hr2 hrs hrK hML hR hE₁R hE₁L hE₁el.2
  have hsup : IsElemAbelian r (E ⊔ E₀.map (MulAut.conj k).toMonoidHom) :=
    hEel.sup_of_commute hE₁el fun a ha b hb => mem_centralizer_iff.1 (hE₁C hb) a (hER ha)
  obtain ⟨j, hj⟩ := hsup.isPGroup.exists_card_eq
  have hj2 : j ≤ 2 := (UC6S846.le_pRank' hr (sup_le hEM (hE₁L.trans hLM)) hsup hj).trans hrM
  have hle : Nat.card (E ⊔ E₀.map (MulAut.conj k).toMonoidHom : Subgroup G) ≤ r ^ 2 := by
    rw [hj]
    exact Nat.pow_le_pow_right hr.pos hj2
  have h1 := Subgroup.eq_of_le_of_card_ge le_sup_left (hle.trans hEc.ge)
  have h2 := Subgroup.eq_of_le_of_card_ge le_sup_right (hle.trans hE₁c.ge)
  exact (h1.trans h2.symm).le.trans hE₁L

theorem uc22s218x_false_of_levi {Tor Out : ℕ → Prop} (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h71 : F07.R71 D)
    (h72 : F07.R72 D) (hKf : PartTwo.S19.K_19_25_noL2SzSection)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n E : ℕ} (hn : ¬ IsPowTwo n)
    (hF : TorusFacts218 (BarInf L) n Tor Out) (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hLevi : ∀ {U : Subgroup (BarInf L)}, IsSylowTwoOf U ⊤ → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
      ¬ Tor p → (Out p → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L))) →
        Levi218 n E U p) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hZ1 : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ hdvd => by
    rw [hZ, Subgroup.card_bot] at hdvd
    exact hℓ.not_dvd_one hdvd
  have hZ' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center (Bar2 L)) → ¬ Tor ℓ ∧ ¬ Out ℓ :=
    fun ℓ hℓ hdvd => (hZ1 ℓ hℓ hdvd).elim
  have hK : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    fun ℓ hℓ hℓ2 => not_dvd_card_solvableRadical hL.2.2 hℓ hℓ2 (hZ1 ℓ hℓ)
  have hK2 : IsPGroup 2 (CFSG.solvableRadical ↥L) :=
    IsPGroup.of_card
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {ℓ} hℓ hdvd => by
        by_contra hℓ2
        exact hK ℓ hℓ hℓ2 hdvd)
  have : (L.subgroupOf D.M).Normal := normal_of_facts D Ch hSg h211 hH c hL hF hZ' hn
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hp⟩
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hpσ
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpσ
  obtain ⟨s, hs, hs1, hsn⟩ := PartTwo.s13_exists_odd_divisor hn
  have hCL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded q D.M :=
    fun q hq hq2 hqs => not_stronglyEmbedded_of_facts D Ch h211 hH c hLM hML hF hs hsn hq hq2 hqs
  have hps : ¬ p ∣ 2 ^ s - 1 := fun h => hCL p hp hp2 h hsp
  have hs3 : 3 ≤ s := by
    obtain ⟨k, rfl⟩ := hs
    omega
  have h8 : 8 ≤ 2 ^ s :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ s - 1 ≠ 1 by omega)
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrs
  have hrσ : r ∉ D.sig := fun hrσ => hCL r hr hr2 hrs (UC6S846.sp_of_mem_sig hSg hns hrσ)
  have hpr : p ≠ r := by
    rintro rfl
    exact hps hrs
  have hrK := hK r hr hr2
  have hpK := hK p hp hp2
  have hrM : CFSG.Open.pRank r D.M ≤ 2 := by
    by_contra h
    exact hrσ (hσ r hr (uc22s218u_seven_le hs hr hrs) (by omega))
  have hrL : CFSG.Open.pRank r L = 2 := by
    rw [pRank_eq_pRank_barInf hr hrK, hF.pRank_eq_two hs hsn hr hrs]
  have hTp : ¬ Tor p := by
    intro hTp
    obtain ⟨E₁, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
      exists_pair_of_tor hF hs hsn hr hrs hp hTp hpr hpK hrK
    exact hCL r hr hr2 hrs (stronglyEmbedded_of_torus_of_facts D hSg h614 hL hML hF hs hsn hp
      (h76 p hpσ hsp) hr hr2 hrs hrK hrσ hEL hEel hEc (hQL.trans hLM) hQel hQc hpow)
  have hOp : Out p → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
    intro hOp
    by_contra hlt
    have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
      rw [pRank_eq_pRank_barInf hp hpK]
      omega
    obtain ⟨E₁, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ :=
      exists_pair_of_out hLM hF hs hsn hp hp2 hOp hpK hr hr2 hrs hrK hpr hrank
    exact hCL r hr hr2 hrs (stronglyEmbedded_of_torus_of_facts D hSg h614 hL hML hF hs hsn hp
      (h76 p hpσ hsp) hr hr2 hrs hrK hrσ hEL hEel hEc hQM hQel hQc hpow)
  have hTL : IsSylowOf 2 (D.T ⊓ L) L := D.sylowM.inf_of_le_normalizer hLM hML
  obtain ⟨Q₀, hQ₀⟩ := id hTL
  have hU : IsSylowTwoOf (((D.T ⊓ L).subgroupOf L).map (piInf L)) ⊤ := by
    have h1 : (D.T ⊓ L).subgroupOf L = (Q₀ : Subgroup ↥L) := by
      rw [← hQ₀]
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [h1]
    exact isSylowTwoOf_map_piInf L Q₀
  obtain ⟨H, F, hD, hLev⟩ := hLevi hU hp hp2 hTp hOp
  obtain ⟨xb, hxbH, hxbo, S, m, hSC, hm3, hSt, hmode⟩ := hLev hs hsn hr hrs
  have hxbs : xb ^ (2 ^ s - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hxbo ▸ hrs)
  obtain ⟨x, hxo, hxT, k, hxk⟩ := exists_lift_mem_normalizer_of_centMod D.sylowM.isPGroup
    (D.sylowM.le.trans hML) hTL hxbo
    (fun α hα2 hα => hD.mem_centMod_of_mem hxbH hs hxbs α hα2 hα)
  set X : Subgroup G := zpowers (x : G) with hXdef
  have hxo' : orderOf x = r := by rw [← Subgroup.orderOf_coe, hxo]
  have hAp : IsPGroup r (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo', pow_one])
  have hAmap : (zpowers x).map L.subtype = X := MonoidHom.map_zpowers _ _
  have hπx : piInf L x ∈ zpowers xb := by
    rw [hxk]
    exact pow_mem (mem_zpowers xb) k
  have hSC' : S ≤ centralizer (((zpowers x).map (piInf L) : Subgroup (BarInf L)) :
      Set (BarInf L)) := by
    rw [MonoidHom.map_zpowers]
    exact le_centralizer_zpowers_of_le_centralizer hSC hπx
  have hsec : PartTwo.S19.HasL2SzSection m (L ⊓ centralizer (X : Set G)) := by
    obtain ⟨P, hP, φ, hφ, -⟩ := exists_lift_of_le_centralizer_barInf hK2 hAp hr2 hSC'
    rw [hAmap] at hP
    exact PartTwo.S19.hasL2SzSection_of_surjective hP hSt φ hφ
  have hXM : X ≤ D.M := zpowers_le.2 (hLM x.2)
  have hXL : X ≤ L := zpowers_le.2 x.2
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [hXdef, zpowers_eq_bot] at h
    rw [h, orderOf_one] at hxo
    exact hr.one_lt.ne hxo
  have hXp : IsPGroup r X :=
    IsPGroup.of_card (n := 1) (by rw [hXdef, Nat.card_zpowers, hxo, pow_one])
  have hCN : L ⊓ centralizer (X : Set G) ≤ normalizer (X : Set G) ⊓ D.M :=
    le_inf (inf_le_right.trans (centralizer_le_normalizer _)) (inf_le_left.trans hLM)
  have hEL : ∀ E' : Subgroup G, E' ≤ D.M → IsElemAbelian r E' → Nat.card E' = r ^ 2 → E' ≤ L :=
    fun E' hE'M hE'el hE'c =>
      le_of_elemAbelian_of_facts hF hs hsn hr hr2 hrs hrK hLM hML hrM hE'M hE'el hE'c
  obtain ⟨hrank, hE⟩ : 1 < CFSG.Open.pRank p (normalizer (X : Set G) ⊓ D.M) ∧
      ∀ E' : Subgroup G, E' ≤ D.M → IsElemAbelian r E' → Nat.card E' = r ^ 2 →
        p ∣ Nat.card (D.M ⊓ centralizer (E' : Set G) : Subgroup G) := by
    rcases hmode with ⟨hY2, hpS⟩ | ⟨⟨Qb, hQbC, hQbe, hQbc⟩, hAll⟩
    ·
      obtain ⟨y, hyM, hyo, hyL⟩ := exists_trivial_action_barInf D Ch h211 hH c hML
        (outer_comm_of_borel hD.borel) hD.borel.center hp hp2 hsp h3 hY2
      have hO : IsPGroup 2 (OInf L) := hK2.map L.subtype
      have hOL : OInf L ≤ L := OInf_le L
      have hLO : L ≤ normalizer (OInf L : Set G) := le_normalizer_OInf L
      have hyp : IsPGroup p (zpowers y) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
      obtain ⟨w, hwL, hwC⟩ :=
        uc22s218u_exists_conj_commute hp hp2 hr hr2 hO hOL hLO hXp hXL hyp (hML hyM) hyL
      set y' : G := w⁻¹ * y * w with hy'
      have hy'M : y' ∈ D.M := mul_mem (mul_mem (inv_mem (hLM hwL)) hyM) (hLM hwL)
      have hy'o : orderOf y' = p := by
        have h1 : orderOf (MulAut.conj w⁻¹ y) = p := by rw [MulEquiv.orderOf_eq, hyo]
        rw [MulAut.conj_apply, inv_inv] at h1
        exact h1
      have hy'L : ∀ l ∈ L, y' * l * y'⁻¹ * l⁻¹ ∈ OInf L := by
        intro l hl
        have h1 := hyL _ (mul_mem (mul_mem hwL hl) (inv_mem hwL))
        have h2 := (mem_normalizer_iff.1 (hLO (inv_mem hwL)) _).1 h1
        have e : y' * l * y'⁻¹ * l⁻¹ =
            w⁻¹ * (y * (w * l * w⁻¹) * y⁻¹ * (w * l * w⁻¹)⁻¹) * w⁻¹⁻¹ := by
          rw [hy']
          group
        rw [e]
        exact h2
      have hy'nL : y' ∉ L := by
        intro hy'L0
        have hz : ∀ g : BarInf L, piInf L ⟨y', hy'L0⟩ * g = g * piInf L ⟨y', hy'L0⟩ := by
          intro g
          obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) g
          have h1 : (⟨y', hy'L0⟩ * l * (⟨y', hy'L0⟩ : ↥L)⁻¹ * l⁻¹ : ↥L) ∈
              CFSG.solvableRadical ↥L := mem_OInf_iff.1 (by simpa using hy'L l l.2)
          have h2 : piInf L (⟨y', hy'L0⟩ * l * (⟨y', hy'L0⟩ : ↥L)⁻¹ * l⁻¹) = 1 :=
            (QuotientGroup.eq_one_iff _).2 h1
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
            mul_inv_eq_iff_eq_mul] at h2
          exact h2
        have h1 := hD.borel.center _ hz
        have h2 : (⟨y', hy'L0⟩ : ↥L) ∈ CFSG.solvableRadical ↥L := (QuotientGroup.eq_one_iff _).1 h1
        obtain ⟨j, hj⟩ := hK2 ⟨_, h2⟩
        have h3 : y' ^ 2 ^ j = 1 := by
          simpa using congrArg (fun z : ↥(CFSG.solvableRadical ↥L) => ((z : ↥L) : G)) hj
        have h4 : p ∣ 2 ^ j := by
          rw [← hy'o]
          exact orderOf_dvd_of_pow_eq_one h3
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
      obtain ⟨z, hzLC, hzo⟩ := exists_orderOf_mem_centralizer_of_barInf hK2 hAp hr2 hSC' hp hpS
      rw [hAmap] at hzLC
      have hzp : IsPGroup p (zpowers z) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
      obtain ⟨w', hw'L, hw'C⟩ := uc22s218u_exists_conj_commute (L := L ⊓ centralizer (X : Set G))
        (O := OInf L ⊓ centralizer (X : Set G)) hp hp2 hp hp2 (hO.to_le inf_le_left)
        (inf_le_inf_right _ hOL)
        (fun l hl => uc22s218u_mem_normalizer_inf (hLO (mem_inf.1 hl).1)
          (le_normalizer (mem_inf.1 hl).2))
        hzp (zpowers_le.2 hzLC)
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'o, pow_one]))
        (uc22s218u_mem_normalizer_inf (hML hy'M) (le_normalizer hwC))
        (fun l hl => mem_inf.2 ⟨hy'L l (mem_inf.1 hl).1,
          mul_mem (mul_mem (mul_mem hwC (mem_inf.1 hl).2) (inv_mem hwC))
            (inv_mem (mem_inf.1 hl).2)⟩)
      set z₁ : G := w' * z * w'⁻¹ with hz₁
      have hz₁LC : z₁ ∈ L ⊓ centralizer (X : Set G) :=
        mul_mem (mul_mem hw'L hzLC) (inv_mem hw'L)
      have hz₁o : orderOf z₁ = p := by
        have h1 : orderOf (MulAut.conj w' z) = p := by rw [MulEquiv.orderOf_eq, hzo]
        rw [MulAut.conj_apply] at h1
        exact h1
      have hz₁y' : z₁ * y' = y' * z₁ := by
        have h1 := mem_centralizer_iff.1 hw'C z (mem_zpowers z)
        calc z₁ * y' = w' * (z * (w'⁻¹ * y' * w')) * w'⁻¹ := by rw [hz₁]; group
          _ = w' * ((w'⁻¹ * y' * w') * z) * w'⁻¹ := by rw [h1]
          _ = y' * z₁ := by rw [hz₁]; group
      have hz₁1 : z₁ ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hz₁o
        exact hp.one_lt.ne hz₁o
      obtain ⟨hEel, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp
        (by rw [← hz₁o]; exact pow_orderOf_eq_one z₁) (by rw [← hy'o]; exact pow_orderOf_eq_one y')
        hz₁1 (fun h => hy'nL (zpowers_le.2 (mem_inf.1 hz₁LC).1 h)) hz₁y'
      have hEN : zpowers z₁ ⊔ zpowers y' ≤ normalizer (X : Set G) ⊓ D.M :=
        sup_le (zpowers_le.2 (mem_inf.2 ⟨centralizer_le_normalizer _ (mem_inf.1 hz₁LC).2,
            hLM (mem_inf.1 hz₁LC).1⟩))
          (zpowers_le.2 (mem_inf.2 ⟨centralizer_le_normalizer _ hwC, hy'M⟩))
      refine ⟨by have := UC6S846.le_pRank' hp hEN hEel hEc; omega, ?_⟩
      intro E' hE'M hE'el hE'c
      obtain ⟨w₂, hw₂L, hw₂C⟩ := uc22s218u_exists_conj_commute hp hp2 hr hr2 hO hOL hLO
        hE'el.isPGroup (hEL E' hE'M hE'el hE'c) hyp (hML hyM) hyL
      have hmem : w₂⁻¹ * y * w₂ ∈ D.M ⊓ centralizer (E' : Set G) :=
        mem_inf.2 ⟨mul_mem (mul_mem (inv_mem (hLM hw₂L)) hyM) (hLM hw₂L), hw₂C⟩
      have ho : orderOf (w₂⁻¹ * y * w₂) = p := by
        have h3 : orderOf (MulAut.conj w₂⁻¹ y) = p := by rw [MulEquiv.orderOf_eq, hyo]
        rw [MulAut.conj_apply, inv_inv] at h3
        exact h3
      rw [← ho, ← Subgroup.orderOf_mk (w₂⁻¹ * y * w₂) hmem]
      exact orderOf_dvd_natCard _
    ·
      refine ⟨?_, fun E' hE'M hE'el hE'c => ?_⟩
      · have hQbC' : Qb ≤ centralizer (((zpowers x).map (piInf L) : Subgroup (BarInf L)) :
            Set (BarInf L)) := by
          rw [MonoidHom.map_zpowers]
          exact le_centralizer_zpowers_of_le_centralizer hQbC hπx
        have h2 := two_le_pRank_of_le_centralizer_barInf hK2 hAp hr2 hQbC' hp hp2 hQbe hQbc
        rw [hAmap] at h2
        have h4 := CFSG.SectionRank.pRank_mono hp.one_lt hCN
        omega
      · have hE'L := hEL E' hE'M hE'el hE'c
        have hA'p : IsPGroup r (E'.subgroupOf L) := (hE'el.subgroupOf L).isPGroup
        have hA'map : (E'.subgroupOf L).map L.subtype = E' := by
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_eq_left.2 hE'L
        have hinj : Function.Injective ((piInf L).comp (E'.subgroupOf L).subtype) :=
          CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hrK hA'p
        have hA'c : Nat.card ((E'.subgroupOf L).map (piInf L)) = r ^ 2 := by
          have h1 : ((piInf L).comp (E'.subgroupOf L).subtype).range =
              (E'.subgroupOf L).map (piInf L) := by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]
          rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'L).toEquiv, hE'c]
        have hpC := hAll _ ((hE'el.subgroupOf L).map _) hA'c
        obtain ⟨z, hzLC, hzo⟩ :=
          exists_orderOf_mem_centralizer_of_barInf hK2 hA'p hr2 le_rfl hp hpC
        rw [hA'map] at hzLC
        have hmem : z ∈ D.M ⊓ centralizer (E' : Set G) :=
          mem_inf.2 ⟨hLM (mem_inf.1 hzLC).1, (mem_inf.1 hzLC).2⟩
        rw [← hzo, ← Subgroup.orderOf_mk z hmem]
        exact orderOf_dvd_natCard _
  have hNX : normalizer (X : Set G) ≤ D.M :=
    uc22s218u_normalizer_le D hp hp2 hsp h71 h72 hKf hXM hX1 hrank hm3
      (PartTwo.S19.hasL2SzSection_of_le hsec hCN)
  have hrankM : 2 ≤ CFSG.Open.pRank r D.M := by
    rw [← hrL]
    exact CFSG.SectionRank.pRank_mono hr.one_lt hLM
  have hXc : Nat.card X = r := by rw [hXdef, Nat.card_zpowers, hxo]
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hxo
    (PartTwo.mem_uniqueSet_of_centralizer hp hsp hr hXM hXc
      ((centralizer_le_normalizer _).trans hNX) hrankM hE) hxT

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
