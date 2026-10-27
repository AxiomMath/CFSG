module

public import CFSG.Quasithin.Vol2.Ch11SecAKDc
public import CFSG.Quasithin.Vol2.Ch11SecAKDd
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open Matrix CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

namespace C10KH


section Long

variable {F : Type} [Field F]

open CFSG.QuasithinUnique.Vol2Native.A312L in
theorem gAFun_embMat_zmk {B : Matrix (Fin 2) (Fin 2) F} (hB : B.det = 1)
    (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    gAFun (embMat 0 B) (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk r u₀ (B 0 0 * u₁ + B 0 1 * u₂) (B 1 0 * u₁ + B 1 1 * u₂) v₀
        (B 1 1 * v₁ - B 1 0 * v₂) (-(B 0 1 * v₁) + B 0 0 * v₂) s := by
  rw [Matrix.det_fin_two] at hB
  simp only [gAFun, zmk, Prod.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i <;> simp [embMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [embMat, Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · linear_combination v₀ * hB
    · ring

variable [CharP F 2]

open CFSG.QuasithinUnique.Vol2Native.A312L in
theorem gAFun_embMat_qFun_zmk {B : Matrix (Fin 2) (Fin 2) F} (hB : B.det = 1)
    (g : Matrix (Fin 2) (Fin 2) F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    gAFun (embMat 0 B) (qFun g (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s)) =
      qFun g (gAFun (embMat 0 B) (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [qFun_zmk, gAFun_embMat_zmk hB]
  generalize g 0 0 = a
  generalize g 0 1 = b
  generalize g 1 0 = c
  generalize g 1 1 = d
  generalize B 0 0 = k
  generalize B 0 1 = l
  generalize B 1 0 = m
  generalize B 1 1 = n
  apply zmk_congr
  · ring
  · ring
  · linear_combination (c * v₁ * l) * h2
  · linear_combination (c * v₂ * m) * h2
  · ring
  · linear_combination (-b * u₁ * m) * h2
  · linear_combination (-b * u₂ * l) * h2
  · ring

theorem commute_zHom_g2A (g B : SpecialLinearGroup (Fin 2) F) :
    Commute (zHom g) (g2A (CFSG.QuasithinUnique.Vol2Native.A312L.embSL 0 B)) := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change qFun (g : Matrix (Fin 2) (Fin 2) F)
      (gAFun (CFSG.QuasithinUnique.Vol2Native.A312L.embMat 0 (B : Matrix (Fin 2) (Fin 2) F)) x) =
    gAFun (CFSG.QuasithinUnique.Vol2Native.A312L.embMat 0 (B : Matrix (Fin 2) (Fin 2) F))
      (qFun (g : Matrix (Fin 2) (Fin 2) F) x)
  rw [zorn_eta x]
  exact (gAFun_embMat_qFun_zmk B.2 _ _ _ _ _ _ _ _ _).symm

end Long

section Rank

variable {F : Type} [Field F]

theorem eq_one_of_entries {g : SpecialLinearGroup (Fin 2) F}
    (h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) (h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1) :
    g = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]

theorem pow_apply_of_apply {h : ↥(cayleyGroup F)} {q : quasithinZorn F}
    (hq : (h : quasithinZorn F ≃ₗ[F] quasithinZorn F) q = q) (n : ℕ) :
    ((h ^ n : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) q = q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, hq, ih]

open CFSG.QuasithinUnique.Vol2Native.A312L in
theorem two_le_pRank_cayley [CharP F 2] [Finite F] {p : ℕ} [hp : Fact p.Prime]
    {g : SpecialLinearGroup (Fin 2) F} (hg : orderOf g = p) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(cayleyGroup F)) := by
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.out.one_lt.ne hg
  have hx : ∀ z : quasithinZorn F, ((g2A (embSL 0 g) : ↥(cayleyGroup F)) :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) z =
        gAFun (embMat 0 (g : Matrix (Fin 2) (Fin 2) F)) z :=
    fun _ => rfl
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (x := g2A (embSL 0 g))
    (y := zHom g) ?_ ?_ (commute_zHom_g2A g g).symm ?_ ?_
  · rw [← map_pow, ← map_pow, ← hg, pow_orderOf_eq_one, map_one, map_one]
  · rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  · intro h
    apply hg1
    have e1 := congrArg (fun y : ↥(cayleyGroup F) =>
      (y : quasithinZorn F ≃ₗ[F] quasithinZorn F) (zmk 0 0 1 0 0 0 0 0)) h
    have e2 := congrArg (fun y : ↥(cayleyGroup F) =>
      (y : quasithinZorn F ≃ₗ[F] quasithinZorn F) (zmk 0 0 0 1 0 0 0 0)) h
    simp only [hx, gAFun_embMat_zmk g.2] at e1 e2
    obtain ⟨-, -, a1, a2, -⟩ := zmk_inj e1
    obtain ⟨-, -, b1, b2, -⟩ := zmk_inj e2
    simp only [mul_one, mul_zero, add_zero, zero_add] at a1 a2 b1 b2
    exact eq_one_of_entries a1 b1 a2 b2
  · intro m h
    apply hg1
    have hq : ∀ q : quasithinZorn F, (q = zmk 0 1 0 0 0 0 0 0 ∨ q = zmk 0 0 0 0 1 0 0 0) →
        ((zHom g : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) q = q := by
      rintro q hq
      rw [← h]
      refine pow_apply_of_apply ?_ m
      rw [hx]
      rcases hq with rfl | rfl <;> rw [gAFun_embMat_zmk g.2] <;> simp
    have e1 := hq _ (Or.inl rfl)
    have e2 := hq _ (Or.inr rfl)
    rw [zHom_apply, qFun_zmk] at e1 e2
    obtain ⟨-, a1, -, -, a4, -⟩ := zmk_inj e1
    obtain ⟨-, b1, -, -, b4, -⟩ := zmk_inj e2
    simp only [mul_one, mul_zero, add_zero, zero_add] at a1 a4 b1 b4
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := CharTwo.sq_inj.1 (by rw [a1, one_pow])
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := CharTwo.sq_inj.1 (by rw [b4, one_pow])
    exact eq_one_of_entries h00 ((pow_eq_zero_iff two_ne_zero).1 b1)
      ((pow_eq_zero_iff two_ne_zero).1 a4) h11

end Rank

theorem two_le_pRank_g2 {K : Type} [Field K] [Finite K] {n p : ℕ} [hp : Fact p.Prime]
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {g : SpecialLinearGroup (Fin 2) K}
    (hg : orderOf g = p) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥⁅quasithinG2 K, quasithinG2 K⁆) := by
  have : CharP K 2 := Vol2.KGNat.charP_two_of_card (by omega) hK
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := Vol2.KGNat.exists_ne_zero_ne_one (K := K) (by rw [hK]; omega)
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      cayley_commutator_eq hc0 hc1]
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt (MulEquiv.subgroupCongr hc)]
  exact two_le_pRank_cayley hg

end C10KH

theorem factTorusRank_holds : FactTorusRank := by
  intro K _ _ n hn hK p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h => C10KH.two_le_pRank_sl3 (by rw [hK]; exact h), fun h => ?_⟩
  obtain ⟨g, hg⟩ := C10KH.exists_orderOf_sl2 hK h
  exact ⟨C10KH.two_le_pRank_sp4 hg, C10KH.two_le_pRank_g2 hn hK hg⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
