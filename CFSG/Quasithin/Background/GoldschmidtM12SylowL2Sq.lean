module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.F6CatRecogOut

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

namespace M12Sylow

theorem false_of_orderOf_two_pow {D : Type} [Group D] [Finite D] {T : Type} [Group T]
    (hT : ∀ x : T, x ^ 8 = 1) (S : Sylow 2 D) (eT : ↥(S : Subgroup D) ≃* T) {g : D} {k : ℕ}
    (hk : 4 ≤ k) (hg : orderOf g = 2 ^ k) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hg])
  obtain ⟨S', hgS'⟩ := hgp.exists_le_sylow
  let y : ↥(S' : Subgroup D) := ⟨g, hgS' (Subgroup.mem_zpowers g)⟩
  let z : ↥(S : Subgroup D) := Sylow.equiv S' S y
  have hz : orderOf z = 2 ^ k := by
    rw [MulEquiv.orderOf_eq]
    show orderOf y = 2 ^ k
    rw [← hg, ← Subgroup.orderOf_coe]
  have h8 : z ^ 8 = 1 := by
    have := hT (eT z)
    rw [← map_pow] at this
    exact eT.injective (by rw [this, map_one])
  have h3 := orderOf_dvd_of_pow_eq_one h8
  rw [hz] at h3
  have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem exists_pow_orderOf_two_pow {D : Type} [Group D] [Finite D] {d : D}
    (h : 16 ∣ orderOf d) : ∃ (g : D) (k : ℕ), 4 ≤ k ∧ orderOf g = 2 ^ k := by
  obtain ⟨k, u, hu, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hcop : Nat.Coprime (2 ^ 4) u :=
    Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hu)
  have h16 : 2 ^ 4 ∣ 2 ^ k * u := by
    rw [← hord]
    exact h
  have h4 : 2 ^ 4 ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right h16
  have hk : 4 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h4
  have hudvd : u ∣ orderOf d := by rw [hord]; exact Dvd.intro_left _ rfl
  refine ⟨d ^ u, k, hk, ?_⟩
  rw [orderOf_pow_of_dvd hu.pos.ne' hudvd, hord, Nat.mul_div_cancel _ hu.pos]

variable {D : Type} [Group D] [Finite D]

theorem false_of_l2sq (hS : F618RecogSetting D) {T : Type} [Group T] (hT : ∀ x : T, x ^ 8 = 1)
    (S : Sylow 2 D) (eT : ↥(S : Subgroup D) ≃* T) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel (TwoResidualQuot D) .PSL 2 p 2)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 4)
    (Q : Sylow 2 (TwoResidualQuot D)) (hQ : Nat.card ↥(Q : Subgroup (TwoResidualQuot D)) = 16) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hF⟩
  have h3 : 3 < Nat.card F := by
    rw [hF]
    have := hp.two_le
    nlinarith
  let ε := projectiveSpecialLinearGroupEquivStatedProj 2 F
  let φ : TwoResidualQuot D ≃* PSL2 F := e.trans ε.symm
  have hAutc : Nat.card (MulAut (TwoResidualQuot D)) =
      Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index := by
    rw [hidx, Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_psl_two_sq F hp2 hF,
      Nat.card_congr e.toEquiv]
    ring
  have hsurj : Function.Surjective (conjQuotHom D) := by
    rw [← MonoidHom.range_eq_top, ← Subgroup.card_eq_iff_eq_top, card_range_conjQuotHom hS, hAutc]
  have hPSL : (Nat.card (PSL2 F)).factorization 2 = 4 := by
    have h1 : 2 ^ (Nat.card (TwoResidualQuot D)).factorization 2 = 16 := by
      rw [← Sylow.card_eq_multiplicity Q, hQ]
    have h2 : (Nat.card (TwoResidualQuot D)).factorization 2 = 4 :=
      Nat.pow_right_injective le_rfl (h1.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
    rw [← h2, Nat.card_congr φ.toEquiv]
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hPGL : (Nat.card (PGL2 F)).factorization 2 = 5 := by
    rw [← two_mul_card_psl2 F hodd, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
      Finsupp.add_apply, hPSL, Nat.Prime.factorization_self Nat.prime_two]
  obtain ⟨P⟩ : Nonempty (Sylow 2 (PGL2 F)) := inferInstance
  obtain ⟨m, hm1, ⟨θ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd P
  have hPc : Nat.card ↥(P : Subgroup (PGL2 F)) = 2 ^ (m + 1) := by
    rw [Nat.card_congr θ.toEquiv, DihedralGroup.nat_card]
    ring
  have hm4 : m = 4 := by
    have : 2 ^ (m + 1) = 2 ^ 5 := by rw [← hPc, Sylow.card_eq_multiplicity P, hPGL]
    have := Nat.pow_right_injective le_rfl this
    omega
  subst hm4
  let g : ↥(P : Subgroup (PGL2 F)) := θ.symm (DihedralGroup.r 1)
  have hg : orderOf g = 2 ^ 4 := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hx : orderOf (g : PGL2 F) = 2 ^ 4 := by rw [Subgroup.orderOf_coe, hg]
  let σ : MulAut (PSL2 F) := pgl2InnerAutPSL2 F hodd h3 (g : PGL2 F)
  have hσ : orderOf σ = 2 ^ 4 := by
    rw [orderOf_injective (pgl2InnerAutPSL2 F hodd h3) (pgl2InnerAutPSL2_injective F hodd h3), hx]
  let σ' : MulAut (TwoResidualQuot D) := (MulAut.congr φ.symm) σ
  have hσ' : orderOf σ' = 2 ^ 4 := by rw [MulEquiv.orderOf_eq, hσ]
  obtain ⟨d, hd⟩ := hsurj σ'
  have hdvd : 16 ∣ orderOf d := by
    have := orderOf_map_dvd (conjQuotHom D) d
    rw [hd, hσ'] at this
    simpa using this
  obtain ⟨g', k, hk, hg'⟩ := exists_pow_orderOf_two_pow hdvd
  exact false_of_orderOf_two_pow hT S eT hk hg'

end M12Sylow

end CFSG.Quasithin.F6
