module

public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGXInLUF2Aux2
import CFSG.LieType.SemisimpleCentralizers.HeldLangUnitFix
import CFSG.RankThree.PartOne.KF.UnitaryDiag
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.StandardType.PZOrderNine

open Matrix CFSG.Open CFSG.LieType.Universal.Unitary

section Transvection

variable {G : Type} [Group G]

theorem false_of_commutator_mem_of_noTransvection {p : ℕ} (hp : p.Prime) {Bs E : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {x k : G} (hx : x ∈ Bs)
    (hEB : E ≤ Bs) (hgen : Bs ≤ Subgroup.zpowers x ⊔ E) (hkE : ∀ e ∈ E, k * e = e * k)
    (hc : k * x * k⁻¹ * x⁻¹ ∈ E) (hc1 : k * x * k⁻¹ * x⁻¹ ≠ 1) : False := by
  have key : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g * x * g⁻¹ * x⁻¹ ∈ E → ∀ b ∈ Bs,
      g * b * g⁻¹ ∈ Bs ∧ b * g * b⁻¹ * g⁻¹ ∈ Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) := by
    intro g hgE hgc
    have hzc : Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) ≤ Bs := Subgroup.zpowers_le.mpr (hEB hgc)
    let S : Subgroup G :=
      { carrier := {b | b ∈ Bs ∧ b * g * b⁻¹ * g⁻¹ ∈ Subgroup.zpowers (g * x * g⁻¹ * x⁻¹)}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨Bs.mul_mem ha hb, ?_⟩
          have e : a * b * g * (a * b)⁻¹ * g⁻¹ =
              a * (b * g * b⁻¹ * g⁻¹) * a⁻¹ * (a * g * a⁻¹ * g⁻¹) := by group
          rw [e, hBs.comm ha (hzc hb'), mul_inv_cancel_right]
          exact Subgroup.mul_mem _ hb' ha'
        one_mem' := ⟨Bs.one_mem, by simp⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨Bs.inv_mem ha, ?_⟩
          have e : a⁻¹ * g * a⁻¹⁻¹ * g⁻¹ = a⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * a := by group
          rw [e, hBs.comm (Bs.inv_mem ha) (hzc (Subgroup.inv_mem _ ha')), inv_mul_cancel_right]
          exact Subgroup.inv_mem _ ha' }
    have hxS : x ∈ S := by
      refine ⟨hx, ?_⟩
      have e : x * g * x⁻¹ * g⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have hES : E ≤ S := fun e he => by
      refine ⟨hEB he, ?_⟩
      have e' : e * g * e⁻¹ * g⁻¹ = 1 := by rw [← hgE e he]; group
      rw [e']
      exact Subgroup.one_mem _
    have hBS : Bs ≤ S := hgen.trans (sup_le (Subgroup.zpowers_le.mpr hxS) hES)
    intro b hb
    refine ⟨?_, (hBS hb).2⟩
    have e : g * b * g⁻¹ = b * (b⁻¹ * g * b⁻¹⁻¹ * g⁻¹) := by group
    rw [e]
    exact Bs.mul_mem hb (hzc (hBS (Bs.inv_mem hb)).2)
  have hkE' : ∀ e ∈ E, k⁻¹ * e = e * k⁻¹ := fun e he =>
    (Commute.inv_left (show Commute k e from hkE e he)).eq
  have hc' : k⁻¹ * x * k⁻¹⁻¹ * x⁻¹ ∈ E := by
    have e : k⁻¹ * x * k⁻¹⁻¹ * x⁻¹ = k⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * k := by group
    rw [e, hkE' _ (E.inv_mem hc), inv_mul_cancel_right]
    exact E.inv_mem hc
  have hkN : k ∈ Subgroup.normalizer (Bs : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => (key k hkE hc b hb).1, fun hb => ?_⟩
    have h := (key k⁻¹ hkE' hc' _ hb).1
    have e : k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b := by group
    rw [e] at h
    exact h
  have hall := GGXInL.lup8f_f2_commute_of_noTransvection hp hBs hNT (hEB hc) hkN (hkE _ hc)
    (fun b hb => (key k hkE hc b hb).2)
  apply hc1
  rw [hall x hx]
  group

end Transvection

section Native

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def diagCubeTorus (m : ℕ) : Subgroup (SUid σ m) where
  carrier := {u | ∃ d : Fin m → F, ((u : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal d ∧
    ∀ i, d i ^ 3 = 1}
  mul_mem' := by
    rintro u v ⟨d, hd, hd3⟩ ⟨e, he, he3⟩
    refine ⟨fun i => d i * e i, ?_, fun i => by rw [mul_pow, hd3, he3, one_mul]⟩
    rw [Subgroup.coe_mul, Units.val_mul, hd, he, diagonal_mul_diagonal]
  one_mem' := ⟨fun _ => 1, by rw [OneMemClass.coe_one, Units.val_one, diagonal_one],
    fun _ => one_pow 3⟩
  inv_mem' := by
    rintro u ⟨d, hd, hd3⟩
    have hd0 : ∀ i, d i ≠ 0 := fun i h => by simpa [h] using hd3 i
    refine ⟨fun i => (d i)⁻¹, ?_, fun i => by rw [inv_pow, hd3, inv_one]⟩
    show (((u : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      diagonal fun i => (d i)⁻¹
    have hu : ((u : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        (((u : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hd] at hu
    calc (((u : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
        = (diagonal (fun i => (d i)⁻¹) * diagonal d) *
            (((u : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
          rw [diagonal_mul_diagonal,
            show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : F) from
              funext fun i => inv_mul_cancel₀ (hd0 i),
            diagonal_one, Matrix.one_mul]
      _ = diagonal fun i => (d i)⁻¹ := by rw [Matrix.mul_assoc, hu, Matrix.mul_one]

variable {σ}

theorem ne_zero_of_norm_eq_one {c : F} (hc : σ c * c = 1) : c ≠ 0 := fun h => by
  simp [h] at hc

variable (σ) in
@[expose] def diagSU {m : ℕ} (d : Fin m → F) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) : SUid σ m :=
  ⟨⟨diagonal d, diagonal fun i => (d i)⁻¹,
      by
        rw [diagonal_mul_diagonal, show (fun i => d i * (d i)⁻¹) = fun _ => (1 : F) from
          funext fun i => mul_inv_cancel₀ (ne_zero_of_norm_eq_one (hd i)), diagonal_one],
      by
        rw [diagonal_mul_diagonal, show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : F) from
          funext fun i => inv_mul_cancel₀ (ne_zero_of_norm_eq_one (hd i)), diagonal_one]⟩,
    mem_SUid.2 ⟨det_diagonal.trans hdet, by
      show conjTr σ (diagonal d) * diagonal d = 1
      rw [conjTr, diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul_diagonal,
        show (fun i => σ (d i) * d i) = fun _ => (1 : F) from funext hd, diagonal_one]⟩⟩

@[expose] def pairDiag {m : ℕ} (a b : Fin m) (c : F) : Fin m → F :=
  fun i => if i = a then c else if i = b then c⁻¹ else 1

section PairDiag

variable {m : ℕ} {a b : Fin m} (hab : a ≠ b)
include hab

theorem pairDiag_eq_mul (c : F) (i : Fin m) :
    pairDiag a b c i = (if i = a then c else 1) * (if i = b then c⁻¹ else 1) := by
  unfold pairDiag
  rcases eq_or_ne i a with rfl | h1
  · simp [hab]
  · rcases eq_or_ne i b with rfl | h2 <;> simp [*]

theorem prod_pairDiag {c : F} (hc : c ≠ 0) : ∏ i, pairDiag a b c i = 1 := by
  rw [Finset.prod_congr rfl fun i _ => pairDiag_eq_mul hab c i, Finset.prod_mul_distrib]
  simp [hc]

theorem pairDiag_norm {c : F} (hc : σ c * c = 1) (i : Fin m) :
    σ (pairDiag a b c i) * pairDiag a b c i = 1 := by
  unfold pairDiag
  rcases eq_or_ne i a with rfl | h1
  · simpa using hc
  · rcases eq_or_ne i b with rfl | h2
    · simp only [h1, if_false, if_true, map_inv₀]
      rw [← mul_inv, hc, inv_one]
    · simp [h1, h2]

theorem pairDiag_cube {c : F} (hc : c ^ 3 = 1) (i : Fin m) : pairDiag a b c i ^ 3 = 1 := by
  unfold pairDiag
  rcases eq_or_ne i a with rfl | h1
  · simpa using hc
  · rcases eq_or_ne i b with rfl | h2
    · simp [h1, inv_pow, hc]
    · simp [h1, h2]

omit hab in
theorem map_pairDiag (φ : F ≃+* F) (c : F) (i : Fin m) :
    φ (pairDiag a b c i) = pairDiag a b (φ c) i := by
  unfold pairDiag
  split_ifs <;> simp [map_inv₀]

theorem pairDiag_mul_inv (c e : F) (i : Fin m) :
    pairDiag a b c i * (pairDiag a b e i)⁻¹ = pairDiag a b (c * e⁻¹) i := by
  unfold pairDiag
  rcases eq_or_ne i a with rfl | h1
  · simp
  · rcases eq_or_ne i b with rfl | h2
    · simp [h1, mul_comm]
    · simp [h1, h2]

end PairDiag

theorem exists_diag_witness (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ) {m : ℕ}
    (hm : 3 ≤ m) (φ : F ≃+* F) {lam : F} (hlam : σ lam * lam = 1)
    (hlamφ : σ (φ lam) * φ lam = 1) (hc3 : (lam * (φ lam)⁻¹) ^ 3 = 1)
    (hc1 : lam * (φ lam)⁻¹ ≠ 1) :
    ∃ k k' : SUid σ m,
      ((k' : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ ∧
      (∀ d ∈ diagCubeTorus σ m, k * d = d * k) ∧ k * k'⁻¹ ∈ diagCubeTorus σ m ∧
      k * k'⁻¹ ∉ Subgroup.center (SUid σ m) := by
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let e : Fin m := ⟨2, by omega⟩
  have hab : a ≠ b := fun h => by simp [a, b, Fin.ext_iff] at h
  have hea : e ≠ a := fun h => by simp [a, e, Fin.ext_iff] at h
  have heb : e ≠ b := fun h => by simp [b, e, Fin.ext_iff] at h
  let k := diagSU σ (pairDiag a b lam) (pairDiag_norm hab hlam)
    (prod_pairDiag hab (ne_zero_of_norm_eq_one hlam))
  let k' := diagSU σ (pairDiag a b (φ lam)) (pairDiag_norm hab hlamφ)
    (prod_pairDiag hab (ne_zero_of_norm_eq_one hlamφ))
  have hkk : (((k * k'⁻¹ : SUid σ m) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      diagonal (pairDiag a b (lam * (φ lam)⁻¹)) := by
    show diagonal (pairDiag a b lam) * diagonal (fun i => (pairDiag a b (φ lam) i)⁻¹) = _
    rw [diagonal_mul_diagonal]
    exact congrArg diagonal (funext (pairDiag_mul_inv hab lam (φ lam)))
  refine ⟨k, k', ?_, ?_, ⟨_, hkk, pairDiag_cube hab hc3⟩, ?_⟩
  · show diagonal (pairDiag a b (φ lam)) = (diagonal (pairDiag a b lam)).map φ
    rw [diagonal_map (map_zero φ)]
    exact congrArg diagonal (funext fun i => (map_pairDiag φ lam i).symm)
  · rintro d ⟨t, ht, -⟩
    apply Subtype.ext
    apply Units.ext
    show diagonal (pairDiag a b lam) * ((d : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((d : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * diagonal (pairDiag a b lam)
    rw [ht, diagonal_mul_diagonal, diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  · intro hz
    obtain ⟨u, hu⟩ := CFSG.ClassicalInvolution.Phan.exists_scalar_of_mem_center hσ hm hz
    rw [hkk] at hu
    have h1 := congrFun (congrFun hu a) a
    have h2 := congrFun (congrFun hu e) e
    simp only [diagonal_apply_eq, scalar_apply, pairDiag, if_true, hea, heb, if_false] at h1 h2
    exact hc1 (h1.trans h2.symm)

end Native

section Frobenius

private theorem exists_pow_nine_eq_one_pow_three_ne {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 64) : ∃ t : K, t ^ 9 = 1 ∧ t ^ 3 ≠ 1 := by
  have hcard : Nat.card Kˣ = 63 := by simp only [Nat.card_units, hK]
  by_contra hne
  have hall : ∀ x : Kˣ, x ^ 21 = 1 := fun x => by
    have h63 : (x : K) ^ 63 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hcard, pow_card_eq_one', Units.val_one]
    have h9 : ((x : K) ^ 7) ^ 9 = 1 := by rw [← pow_mul]; exact h63
    have h3 : ((x : K) ^ 7) ^ 3 = 1 := by
      by_contra h3
      exact hne ⟨(x : K) ^ 7, h9, h3⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show (21 : ℕ) = 7 * 3 from rfl, pow_mul]
    exact h3
  have hexp : Monoid.exponent Kˣ ∣ 21 := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hall
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  norm_num at hexp

variable {G : Type} [Group G]

theorem false_of_frobenius_orderNine {F : Type} [Field F] [Finite F] (hF : Nat.card F = 64)
    {σ : F ≃+* F} (hσ8 : ∀ c, σ c = c ^ 8) {m : ℕ} (hm : 3 ≤ m) (ψ : SUid σ m →* G)
    (hker : ψ.ker ≤ Subgroup.center (SUid σ m)) {φ : F ≃+* F}
    (hφ : (∀ c, φ c = c ^ 4) ∨ ∀ c, φ c = c ^ 16) {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {x : G} (hx : x ∈ Bs)
    (hxψ : ∀ u v : SUid σ m, ((v : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((u : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ → x * ψ u * x⁻¹ = ψ v)
    (hEB : (diagCubeTorus σ m).map ψ ≤ Bs)
    (hgen : Bs ≤ Subgroup.zpowers x ⊔ (diagCubeTorus σ m).map ψ) : False := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hσU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    have hσu : σ = CFSG.LieType.BorelTits.unitaryInvolution F 2 3 := RingEquiv.ext fun c => by
      rw [hσ8, CFSG.LieType.BorelTits.unitaryInvolution_apply]
      norm_num
    rw [hσu]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (by rw [hF]; norm_num)
  obtain ⟨lam, h9, h3⟩ := exists_pow_nine_eq_one_pow_three_ne hF
  have hlam0 : lam ≠ 0 := fun h => by simp [h] at h9
  have hlam : σ lam * lam = 1 := by
    rw [hσ8, ← pow_succ]
    exact h9
  have hlamφ : σ (φ lam) * φ lam = 1 := by
    rw [hσ8, ← pow_succ, ← map_pow, show lam ^ (8 + 1) = 1 from h9, map_one]
  obtain ⟨hc3, hc1⟩ : (lam * (φ lam)⁻¹) ^ 3 = 1 ∧ lam * (φ lam)⁻¹ ≠ 1 := by
    rcases hφ with h4 | h16
    · have e : lam * (φ lam)⁻¹ = (lam ^ 3)⁻¹ := by
        rw [h4, pow_succ' lam 3, mul_inv, mul_inv_cancel_left₀ hlam0]
      rw [e]
      refine ⟨?_, fun h => h3 (inv_eq_one.mp h)⟩
      rw [inv_pow, ← pow_mul]
      rw [show lam ^ (3 * 3) = 1 from h9, inv_one]
    · have h7 : lam ^ 16 = lam ^ 7 := by
        rw [show (16 : ℕ) = 9 + 7 from rfl, pow_add, h9, one_mul]
      have e : lam * (φ lam)⁻¹ = (lam ^ 6)⁻¹ := by
        rw [h16, h7, pow_succ' lam 6, mul_inv, mul_inv_cancel_left₀ hlam0]
      rw [e]
      refine ⟨?_, fun h => h3 ?_⟩
      · rw [inv_pow, ← pow_mul, show (6 * 3 : ℕ) = 9 * 2 from rfl, pow_mul, h9, one_pow, inv_one]
      · have h6 : lam ^ 6 = 1 := inv_eq_one.mp h
        calc lam ^ 3 = lam ^ 6 * lam ^ 3 := by rw [h6, one_mul]
          _ = 1 := by rw [← pow_add]; exact h9
  obtain ⟨k, k', hk', hkD, hkk, hnc⟩ := exists_diag_witness hσU hm φ hlam hlamφ hc3 hc1
  have e : ψ k * x * (ψ k)⁻¹ * x⁻¹ = ψ (k * k'⁻¹) := by
    rw [map_mul, map_inv, ← hxψ k k' hk']
    group
  refine false_of_commutator_mem_of_noTransvection Nat.prime_three hBs hNT hx hEB hgen ?_
    (by rw [e]; exact ⟨_, hkk, rfl⟩) ?_
  · rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, hkD d hd]
  · intro h1
    exact hnc (hker (by rw [MonoidHom.mem_ker, ← e, h1]))

theorem false_of_frobenius_orderNine_chart {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 64) {σ : F ≃+* F} (hσ8 : ∀ c, σ c = c ^ 8) {m : ℕ} (hm : 3 ≤ m)
    {G0 : Subgroup G} (Θ : ↥G0 ≃* ↥(SUid σ m)) {φ : F ≃+* F}
    (hφ : (∀ c, φ c = c ^ 4) ∨ ∀ c, φ c = c ^ 16) {x : G}
    (hxN : x ∈ Subgroup.normalizer (G0 : Set G))
    (hΘx : ∀ (g : ↥G0) (hg : x * (g : G) * x⁻¹ ∈ G0),
      ((Θ ⟨x * g * x⁻¹, hg⟩ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((Θ g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ)
    {Bs E : Subgroup G} (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hx : x ∈ Bs)
    (hEB : E ≤ Bs) (hgen : Bs ≤ Subgroup.zpowers x ⊔ E) (hEG : E ≤ G0)
    (hE : ∀ g : ↥G0, (g : G) ∈ E ↔ Θ g ∈ diagCubeTorus σ m) : False := by
  let ψ : SUid σ m →* G := G0.subtype.comp Θ.symm.toMonoidHom
  have hψE : (diagCubeTorus σ m).map ψ = E := by
    ext g
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (hE (Θ.symm d)).mpr (by rw [MulEquiv.apply_symm_apply]; exact hd)
    · intro hg
      refine ⟨Θ ⟨g, hEG hg⟩, (hE ⟨g, hEG hg⟩).mp hg, ?_⟩
      show ((Θ.symm (Θ ⟨g, hEG hg⟩) : ↥G0) : G) = g
      rw [MulEquiv.symm_apply_apply]
  refine false_of_frobenius_orderNine hF hσ8 hm ψ ?_ hφ hBs hNT hx ?_ (by rw [hψE]; exact hEB)
    (by rw [hψE]; exact hgen)
  · intro u hu
    have h1 : Θ.symm u = 1 := Subtype.ext hu
    rw [MulEquiv.symm_apply_eq, map_one] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · intro u v huv
    have hg : x * ((Θ.symm u : ↥G0) : G) * x⁻¹ ∈ G0 :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (Θ.symm u).2
    have h := hΘx (Θ.symm u) hg
    rw [MulEquiv.apply_symm_apply, ← huv] at h
    have hv : Θ ⟨x * ((Θ.symm u : ↥G0) : G) * x⁻¹, hg⟩ = v := Subtype.ext (Units.ext h)
    show x * ((Θ.symm u : ↥G0) : G) * x⁻¹ = ((Θ.symm v : ↥G0) : G)
    rw [← hv, MulEquiv.symm_apply_apply]

end Frobenius

section Position

open CFSG.LieType.SemisimpleCentralizers.HeldLang CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {F : Type} [Field F]

theorem card_diagCubeTorus_le (σ : F ≃+* F) {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (diagCubeTorus σ m) ≤ 3 ^ (m - 1) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  let R : Finset F := Polynomial.nthRootsFinset 3 (1 : F)
  have hR : ∀ c : F, c ∈ R ↔ c ^ 3 = 1 := fun c => Polynomial.mem_nthRootsFinset (by norm_num) 1
  have hRcard : R.card ≤ 3 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  have hent : ∀ (u : diagCubeTorus σ (n + 1)) (i : Fin (n + 1)),
      ((((u : SUid σ (n + 1)) : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i i) ^ 3
        = 1 := by
    rintro ⟨u, d, hd, hd3⟩ i
    simp only [hd, diagonal_apply_eq, hd3]
  let f : diagCubeTorus σ (n + 1) → (Fin n → R) := fun u i =>
    ⟨(((u : SUid σ (n + 1)) : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
      i.castSucc i.castSucc, (hR _).2 (hent u _)⟩
  have hf : Function.Injective f := by
    rintro ⟨u, d, hd, hd3⟩ ⟨v, e, he, he3⟩ huv
    have hde : ∀ i : Fin n, d i.castSucc = e i.castSucc := fun i => by
      have h := congrArg Subtype.val (congrFun huv i)
      simpa only [f, hd, he, diagonal_apply_eq] using h
    have hdet : ∀ (w : SUid σ (n + 1)) (t : Fin (n + 1) → F),
        ((w : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) = diagonal t →
          (∏ i : Fin n, t i.castSucc) * t (Fin.last n) = 1 := fun w t hw => by
      rw [← Fin.prod_univ_castSucc, ← det_diagonal, ← hw]
      exact (mem_SUid.1 w.2).1
    have hd0 : (∏ i : Fin n, d i.castSucc) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ h => by simpa [h] using hd3 i.castSucc
    have hlast : d (Fin.last n) = e (Fin.last n) := by
      have h1 := hdet u d hd
      have h2 := hdet v e he
      rw [show (∏ i : Fin n, e i.castSucc) = ∏ i : Fin n, d i.castSucc from
        Finset.prod_congr rfl fun i _ => (hde i).symm] at h2
      exact mul_left_cancel₀ hd0 (h1.trans h2.symm)
    have hdeq : d = e := funext fun i => Fin.lastCases hlast (fun j => hde j) i
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    show ((u : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      ((v : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    rw [hd, he, hdeq]
  calc Nat.card (diagCubeTorus σ (n + 1)) ≤ Nat.card (Fin n → R) :=
        Nat.card_le_card_of_injective f hf
    _ = R.card ^ n := by simp [Nat.card_eq_fintype_card]
    _ ≤ 3 ^ n := Nat.pow_le_pow_left hRcard n

theorem exists_conj_eq_diagCubeTorus [Finite F] (hF : Nat.card F = 64) {σ : F ≃+* F}
    (hσ8 : ∀ c, σ c = c ^ 8) {φ : F ≃+* F} (hφ : (∀ c, φ c = c ^ 4) ∨ ∀ c, φ c = c ^ 16)
    {m : ℕ} (hm : 1 ≤ m) {E0 : Subgroup (SUid σ m)} (hE0 : IsElemAbelian 3 E0)
    (hcard : Nat.card E0 = 3 ^ (m - 1))
    (hfix : ∀ u ∈ E0, ((u : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ =
      (u : GL (Fin m) F)) :
    ∃ k : SUid σ m, ((k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ = (k : GL (Fin m) F) ∧
      E0.map (MulAut.conj k).toMonoidHom = diagCubeTorus σ m := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hpow64 : ∀ c : F, c ^ 64 = c := fun c => by
    rw [← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hfix4 : ∀ c : F, φ c = c → c ^ 4 = c := by
    rcases hφ with h4 | h16
    · intro c hc
      rw [← h4]
      exact hc
    · intro c hc
      have h1 : c ^ 16 = c := (h16 c).symm.trans hc
      calc c ^ 4 = (c ^ 16) ^ 4 := by rw [h1]
        _ = c := by rw [← pow_mul]; exact hpow64 c
  obtain ⟨lam, h9, h3⟩ := exists_pow_nine_eq_one_pow_three_ne hF
  have hlam0 : lam ≠ 0 := fun h => by simp [h] at h9
  have hφ3 : φ ^ 3 = 1 := by
    ext c
    rw [pow_succ, pow_succ, pow_one, RingAut.mul_apply, RingAut.mul_apply, RingAut.one_apply]
    rcases hφ with h4 | h16
    · rw [h4, h4, h4, ← pow_mul, ← pow_mul]
      exact hpow64 c
    · rw [h16, h16, h16, ← pow_mul, ← pow_mul, show (16 * 16 * 16 : ℕ) = 64 * 64 from rfl,
        pow_mul, hpow64, hpow64]
  have hφ1 : φ ≠ 1 := fun h => by
    have h4 := hfix4 lam (by rw [h, RingAut.one_apply])
    apply h3
    have : lam * lam ^ 3 = lam * 1 := by rw [mul_one, ← pow_succ', h4]
    exact mul_left_cancel₀ hlam0 this
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hK₀ : Nat.card (fixField φ) = 4 := by
    rw [card_fixField Nat.prime_two (by norm_num) (by rw [hF]; norm_num : Nat.card F = 2 ^ 6) φ,
      hord]
    norm_num
  let h₀ : UnitaryFieldData 2 1 (fixField φ) := ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
  have hbar : ∀ c : fixField φ, ((h₀.bar c : fixField φ) : F) = σ (c : F) := by
    intro c
    have hc4 := hfix4 (c : F) (mem_fixField.1 c.2)
    rw [UnitaryFieldData.bar_apply, hσ8, SubmonoidClass.coe_pow]
    calc (c : F) ^ 2 ^ 1 = ((c : F) ^ 4) ^ 2 := by rw [hc4]; norm_num
      _ = (c : F) ^ 8 := by rw [← pow_mul]
  have hinj : Function.Injective fun N : Matrix (Fin m) (Fin m) (fixField φ) =>
      N.map (fixField φ).subtype := Matrix.map_injective (fixField φ).subtype_injective
  have hcoe : ∀ x : GL (Fin m) (fixField φ), ((glFixEmb φ x : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = (x : Matrix (Fin m) (Fin m) (fixField φ)).map
        (fixField φ).subtype := fun x => by
    ext i j
    rw [glFixEmb_apply]
    rfl
  have hU : ∀ x : GL (Fin m) (fixField φ), x ∈ primeFormUnitary h₀ (idGram (fixField φ) m) ↔
      conjTr σ ((glFixEmb φ x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        ((glFixEmb φ x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    intro x
    have key : ((((x : Matrix (Fin m) (Fin m) (fixField φ)).map h₀.bar)ᵀ *
        idGram (fixField φ) m * (x : Matrix (Fin m) (Fin m) (fixField φ))).map
          (fixField φ).subtype) =
        conjTr σ ((glFixEmb φ x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          ((glFixEmb φ x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
      rw [hcoe, idGram, Units.val_one, Matrix.mul_one, Matrix.map_mul, Matrix.transpose_map,
        Matrix.map_map, conjTr, Matrix.map_map]
      congr 2
      ext i j
      exact hbar _
    have hone : ((idGram (fixField φ) m).map (fixField φ).subtype) =
        (1 : Matrix (Fin m) (Fin m) F) := by
      rw [idGram, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [mem_primeFormUnitary, ← key, ← hone]
    exact hinj.eq_iff.symm
  let ι : primeFormUnitary h₀ (idGram (fixField φ) m) →* GL (Fin m) F :=
    (glFixEmb φ).comp (primeFormUnitary h₀ (idGram (fixField φ) m)).subtype
  have hι : Function.Injective ι := (glFixEmb_injective φ).comp Subtype.val_injective
  let E0₀ : Subgroup (primeFormUnitary h₀ (idGram (fixField φ) m)) :=
    (E0.map (SUid σ m).subtype).comap ι
  have hcomm₀ : ∀ x ∈ E0₀, ∀ y ∈ E0₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hy)
    apply hι
    rw [map_mul, map_mul, ← hax, ← hby, ← map_mul, ← map_mul, hE0.comm ha hb]
  have hpow₀ : ∀ x ∈ E0₀, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    apply hι
    rw [map_pow, ← hax, ← map_pow, hE0.2 a ha, map_one, map_one]
  obtain ⟨P₀, hP₀⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h₀ Nat.prime_three
    (by norm_num) E0₀ hcomm₀ hpow₀
  set P : GL (Fin m) F := glFixEmb φ (P₀ : GL (Fin m) (fixField φ)) with hPdef
  have hPσ : conjTr σ (P : Matrix (Fin m) (Fin m) F) * (P : Matrix (Fin m) (Fin m) F) = 1 :=
    (hU _).1 P₀.2
  have hPφ : P ∈ glFix φ := glFixEmb_mem φ _
  set δ := (P : Matrix (Fin m) (Fin m) F).det with hδdef
  have hδσ : σ δ * δ = 1 := by
    have h := congrArg Matrix.det hPσ
    rw [det_mul, conjTr, det_transpose, ← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det,
      det_one] at h
    exact h
  have hδφ : φ δ = δ := by
    rw [hδdef, RingEquiv.map_det, RingEquiv.mapMatrix_apply]
    have h := mem_glFix.1 hPφ
    rw [Units.ext_iff, coe_glMap] at h
    rw [h]
  have hδ0 : δ ≠ 0 := ne_zero_of_norm_eq_one hδσ
  let a : Fin m := ⟨0, by omega⟩
  let dfun : Fin m → F := fun i => if i = a then δ⁻¹ else 1
  have hdfun0 : ∀ i, dfun i ≠ 0 := fun i => by
    by_cases h : i = a <;> simp [dfun, h, hδ0]
  let D : GL (Fin m) F :=
    ⟨diagonal dfun, diagonal fun i => (dfun i)⁻¹,
      by rw [diagonal_mul_diagonal, show (fun i => dfun i * (dfun i)⁻¹) = fun _ => (1 : F) from
        funext fun i => mul_inv_cancel₀ (hdfun0 i), diagonal_one],
      by rw [diagonal_mul_diagonal, show (fun i => (dfun i)⁻¹ * dfun i) = fun _ => (1 : F) from
        funext fun i => inv_mul_cancel₀ (hdfun0 i), diagonal_one]⟩
  have hDφ : D ∈ glFix φ := by
    rw [mem_glFix_iff]
    intro i j
    show φ (diagonal dfun i j) = diagonal dfun i j
    by_cases hij : i = j
    · subst hij
      by_cases h : i = a <;> simp [dfun, diagonal_apply_eq, h, map_inv₀, hδφ]
    · simp [diagonal_apply_ne _ hij]
  have hQ : P * D ∈ SUid σ m := by
    refine mem_SUid.2 ⟨?_, ?_⟩
    · show ((P : Matrix (Fin m) (Fin m) F) * diagonal dfun).det = 1
      rw [det_mul, ← hδdef, det_diagonal, Finset.prod_ite_eq' Finset.univ a,
        if_pos (Finset.mem_univ a), mul_inv_cancel₀ hδ0]
    · show conjTr σ ((P : Matrix (Fin m) (Fin m) F) * diagonal dfun) *
        ((P : Matrix (Fin m) (Fin m) F) * diagonal dfun) = 1
      rw [conjTr_mul, show conjTr σ (diagonal dfun) * conjTr σ (P : Matrix (Fin m) (Fin m) F) *
          ((P : Matrix (Fin m) (Fin m) F) * diagonal dfun) = conjTr σ (diagonal dfun) *
            (conjTr σ (P : Matrix (Fin m) (Fin m) F) * (P : Matrix (Fin m) (Fin m) F)) *
              diagonal dfun by simp only [Matrix.mul_assoc],
        hPσ, Matrix.mul_one, conjTr, diagonal_map (map_zero σ), diagonal_transpose,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = a
      · simp only [dfun, h, if_true, map_inv₀]
        rw [← mul_inv, hδσ, inv_one]
      · simp [dfun, h]
  let k : SUid σ m := (⟨P * D, hQ⟩ : SUid σ m)⁻¹
  have hkGL : (k : GL (Fin m) F) = (P * D)⁻¹ := rfl
  refine ⟨k, ?_, ?_⟩
  · have h := mem_glFix.1 (Subgroup.inv_mem _ (Subgroup.mul_mem _ hPφ hDφ))
    rw [Units.ext_iff, coe_glMap] at h
    rw [hkGL]
    exact h
  · apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u, hu, rfl⟩
      have hu_fix : (u : GL (Fin m) F) ∈ glFix φ := by
        rw [mem_glFix, Units.ext_iff, coe_glMap]
        exact hfix u hu
      obtain ⟨x₁, hx₁⟩ : (u : GL (Fin m) F) ∈ (glFixEmb φ).range := by
        rwa [glFixEmb_range]
      have hx₁U : x₁ ∈ primeFormUnitary h₀ (idGram (fixField φ) m) := by
        rw [hU, hx₁]
        exact (mem_SUid.1 u.2).2
      have hxE : (⟨x₁, hx₁U⟩ : primeFormUnitary h₀ (idGram (fixField φ) m)) ∈ E0₀ :=
        Subgroup.mem_comap.mpr ⟨u, hu, hx₁.symm⟩
      have hdiag := hP₀ _ hxE
      set N : Matrix (Fin m) (Fin m) F :=
        ((P⁻¹ * (u : GL (Fin m) F) * P : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hNdef
      have hN : N = ((((P₀⁻¹ * ⟨x₁, hx₁U⟩ * P₀ : primeFormUnitary h₀ (idGram (fixField φ) m)) :
          GL (Fin m) (fixField φ)) : Matrix (Fin m) (Fin m) (fixField φ))).map
            (fixField φ).subtype := by
        rw [← hcoe, hNdef, hPdef]
        congr 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hx₁]
      have hNd : N.IsDiag := by
        rw [hN]
        exact hdiag.map (map_zero _)
      have hk : ((((MulAut.conj k).toMonoidHom u : SUid σ m) : GL (Fin m) F) :
          Matrix (Fin m) (Fin m) F) = N := by
        show (((P * D)⁻¹ * (u : GL (Fin m) F) * ((P * D)⁻¹)⁻¹ : GL (Fin m) F) :
          Matrix (Fin m) (Fin m) F) = N
        rw [inv_inv, _root_.mul_inv_rev,
          show D⁻¹ * P⁻¹ * (u : GL (Fin m) F) * (P * D) = D⁻¹ * (P⁻¹ * (u : GL (Fin m) F) * P) * D
            by group,
          Units.val_mul, Units.val_mul, ← hNdef, ← hNd.diagonal_diag]
        show diagonal (fun i => (dfun i)⁻¹) * diagonal N.diag * diagonal dfun = diagonal N.diag
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        rw [mul_comm (dfun i)⁻¹, mul_assoc, inv_mul_cancel₀ (hdfun0 i), mul_one]
      refine ⟨N.diag, by rw [hk, hNd.diagonal_diag], fun i => ?_⟩
      have h3 : ((MulAut.conj k).toMonoidHom u) ^ 3 = 1 := by
        rw [← map_pow, hE0.2 u hu, map_one]
      have h3' := congrArg (fun z : SUid σ m => ((z : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
        h3
      simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hk, OneMemClass.coe_one,
        Units.val_one] at h3'
      rw [← hNd.diagonal_diag, diagonal_pow] at h3'
      have := congrFun (congrFun h3' i) i
      simpa [diagonal_apply_eq, Matrix.one_apply_eq] using this
    · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hcard]
      exact card_diagCubeTorus_le σ hm

end Position

section Chart

open CFSG.LieType.SemisimpleCentralizers.HeldLang

variable {G : Type} [Group G] {F : Type} [Field F]

private theorem map_mul_ringEquiv {n : ℕ} (φ : F ≃+* F) (A B : Matrix (Fin n) (Fin n) F) :
    (A * B).map φ = A.map φ * B.map φ :=
  Matrix.map_mul (f := (φ : F →+* F))

theorem false_of_frobenius_orderNine_chart_of_card [Finite F] (hF : Nat.card F = 64)
    {σ : F ≃+* F} (hσ8 : ∀ c, σ c = c ^ 8) {m : ℕ} (hm : 3 ≤ m) {G0 : Subgroup G}
    (Θ : ↥G0 ≃* ↥(SUid σ m)) {φ : F ≃+* F} (hφ : (∀ c, φ c = c ^ 4) ∨ ∀ c, φ c = c ^ 16)
    {x : G} (hxN : x ∈ Subgroup.normalizer (G0 : Set G))
    (hΘx : ∀ (g : ↥G0) (hg : x * (g : G) * x⁻¹ ∈ G0),
      ((Θ ⟨x * g * x⁻¹, hg⟩ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((Θ g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ)
    {Bs E : Subgroup G} (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hx : x ∈ Bs)
    (hEB : E ≤ Bs) (hgen : Bs ≤ Subgroup.zpowers x ⊔ E) (hEG : E ≤ G0)
    (hcard : Nat.card E = 3 ^ (m - 1)) : False := by
  let E0 : Subgroup (SUid σ m) := (E.subgroupOf G0).map Θ.toMonoidHom
  have hE0 : IsElemAbelian 3 E0 := ((hBs.mono hEB).subgroupOf G0).map Θ.toMonoidHom
  have hcard0 : Nat.card E0 = 3 ^ (m - 1) := by
    rw [Subgroup.card_map_of_injective Θ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv, hcard]
  have hfix : ∀ u ∈ E0, ((u : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ =
      (u : GL (Fin m) F) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgE : (g : G) ∈ E := Subgroup.mem_subgroupOf.mp hg
    have hxg : x * (g : G) * x⁻¹ = g := by
      rw [hBs.comm hx (hEB hgE), mul_inv_cancel_right]
    have hg' : x * (g : G) * x⁻¹ ∈ G0 := by
      rw [hxg]
      exact g.2
    have h := hΘx g hg'
    rw [show (⟨x * (g : G) * x⁻¹, hg'⟩ : ↥G0) = g from Subtype.ext hxg] at h
    exact h.symm
  obtain ⟨k, hkφ, hkE⟩ := exists_conj_eq_diagCubeTorus hF hσ8 hφ (by omega) hE0 hcard0 hfix
  have hkφ' : (((k⁻¹ : SUid σ m) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map φ =
      ((k⁻¹ : SUid σ m) : GL (Fin m) F) := by
    have hk : (k : GL (Fin m) F) ∈ glFix φ := by
      rw [mem_glFix, Units.ext_iff, coe_glMap]
      exact hkφ
    have h := mem_glFix.1 (Subgroup.inv_mem _ hk)
    rw [Units.ext_iff, coe_glMap] at h
    exact h
  let Θ' : ↥G0 ≃* ↥(SUid σ m) := Θ.trans (MulAut.conj k)
  refine false_of_frobenius_orderNine_chart hF hσ8 hm Θ' hφ hxN ?_ hBs hNT hx hEB hgen hEG ?_
  · intro g hg
    show ((((k * Θ ⟨x * g * x⁻¹, hg⟩ * k⁻¹ : SUid σ m) : GL (Fin m) F)) :
        Matrix (Fin m) (Fin m) F) =
      ((((k * Θ g * k⁻¹ : SUid σ m) : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F).map φ
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hΘx g hg, map_mul_ringEquiv, map_mul_ringEquiv, hkφ, hkφ']
  · intro g
    rw [← hkE]
    constructor
    · intro hg
      exact ⟨Θ g, ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨g', hg', rfl⟩, hu⟩
      have hu' : MulAut.conj k (Θ g') = MulAut.conj k (Θ g) := hu
      have : g' = g := Θ.injective ((MulAut.conj k).injective hu')
      rw [← this]
      exact Subgroup.mem_subgroupOf.mp hg'

end Chart

end CFSG.StandardType.PZOrderNine

end
