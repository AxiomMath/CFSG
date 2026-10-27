module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure
import CFSG.RankThree.S4Free.StellmacherSzModels
import CFSG.RankThree.S4Free.StellmacherSzSylow
import CFSG.Quasithin.Background.F918Z8Op4d
import CFSG.Quasithin.Vol2.Ch8Sec2L829NKSz
import CFSG.CGT.T75M.SzOut
import CFSG.SignalizerFunctorTheorem.McBride.Models.SchurFamilies.Even
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig

public section

namespace CFSG.RankThree.S4Free.Suzuki

open CFSG.Blueprint CFSG.LieType.Ree Subgroup

variable {a : ℕ} {K : Type} [Field K] [Finite K]
  {X : Type*} [Group X]

theorem mem_suzukiZ0_of_sq_eq_one (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : suzukiGroup a K}
    (hx : x ∈ suzukiU a K) (hx2 : x ^ 2 = 1) : x ∈ suzukiZ0 a K := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).mp hx
  rw [pow_two, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at hx2
  have hu : u ^ 2 ^ (a + 1) * u = 0 := by linear_combination hx2.2 - v * h2
  have hu0 : u = 0 := by
    rcases mul_eq_zero.mp hu with h | h
    · exact (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h
    · exact h
  rw [hu0]
  exact (mem_suzukiZ0_iff hK).mpr ⟨v, rfl⟩

theorem card_le_of_sq_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 2 ^ (2 * a + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hE2 : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE x x.2)⟩
  obtain ⟨S, hES⟩ := hE2.exists_le_sylow
  obtain ⟨φ, hSφ, -⟩ := exists_mulEquiv_sylow_eq hK e S
  have hle : E ≤ (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) := by
    rw [inf_centralizer_eq_comap ha hK φ hSφ]
    intro x hx
    rw [Subgroup.mem_comap]
    have hxU : φ.toMonoidHom x ∈ suzukiU a K := by
      have h := hES hx
      rw [hSφ, Subgroup.mem_comap] at h
      exact h
    refine mem_suzukiZ0_of_sq_eq_one hK hxU ?_
    rw [← map_pow, hE x hx, map_one]
  calc Nat.card E ≤ Nat.card ((S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) :
        Subgroup X) := Subgroup.card_le_of_le hle
    _ = 2 ^ (2 * a + 1) := (card_sylow_and_center ha hK e S).2.1

theorem exists_eq_conj_of_mul_self_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) {σ : MulAut X} (hσ : σ * σ = 1) : ∃ g : X, σ = MulAut.conj g := by
  obtain ⟨f⟩ := SzModels.nonempty_mulEquiv_sz ha hK
  set e' : X ≃* CFSG.Open.Sz a := e.trans f with he'
  have hodd := CFSG.CGT.T75M.sz_outer_odd ha (MulEquiv.refl (CFSG.Open.Sz a))
  set σ' : MulAut (CFSG.Open.Sz a) := (e'.symm.trans σ).trans e' with hσ'def
  have hσ' : σ' * σ' = 1 := by
    ext x
    have h := congrArg (fun τ : MulAut X => e' (τ (e'.symm x))) hσ
    simp only [MulAut.mul_apply, MulAut.one_apply, MulEquiv.apply_symm_apply] at h
    simp only [hσ'def, MulAut.mul_apply, MulAut.one_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [h]
  obtain ⟨g', hg'⟩ := CFSG.CGT.T75M.exists_conj_of_mul_self_eq_one hodd hσ'
  refine ⟨e'.symm g', ?_⟩
  ext x
  have h := congrArg (fun τ : MulAut (CFSG.Open.Sz a) => e'.symm (τ (e' x))) hg'
  simp only [hσ'def, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
    map_mul, map_inv] at h
  rw [MulAut.conj_apply]
  exact h

theorem exists_prime_orderOf_two_eq_four_mul {n : ℕ} (hn : 1 ≤ n) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf (2 : ZMod ℓ) = 4 * n :=
  CFSG.RankThree.GF2n.Stroth80.exists_prime_orderOf_two_eq (by omega) (by omega)

theorem dvd_card_of_orderOf_two_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hord : orderOf (2 : ZMod ℓ) = 4 * (2 * a + 1)) :
    ℓ ∣ Nat.card X := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [Nat.card_congr e.toEquiv, suzuki_order hK]
  set t : ZMod ℓ := 2 ^ (2 * (2 * a + 1)) with ht
  have ht1 : t ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    omega
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← pow_mul, show 2 * (2 * a + 1) * 2 = 4 * (2 * a + 1) by ring, ← hord,
      pow_orderOf_eq_one]
  have htm : t + 1 = 0 := by
    have h0 : (t - 1) * (t + 1) = 0 := by rw [← sub_eq_zero.mpr ht2]; ring
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) ht1
    · exact h1
  have hdvd : ℓ ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 * (2 * a + 1) by ring]
    exact htm
  exact Dvd.dvd.mul_left hdvd _

theorem exists_orderOf_eq_and_inv (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card X)
    {t : X} (ht : orderOf t = 2) : ∃ y : X, orderOf y = ℓ ∧ t * y * t⁻¹ = y⁻¹ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨f⟩ := SzModels.nonempty_mulEquiv_suzukiMatrixGroup ha hK
  set g : X ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a := e.trans f with hg
  have hdvd' : ℓ ∣ Nat.card (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := by
    rwa [← Nat.card_congr g.toEquiv]
  let P : Sylow ℓ (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := default
  have hP1 := P.ne_bot_of_dvd_card hdvd'
  obtain ⟨s, hs2, hsP⟩ :=
    CFSG.Quasithin.opq4d_suzuki_exists_involution_inverts ha hℓ hℓ2 P hP1
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' ℓ (P.dvd_card_of_dvd_card hdvd')
  set y₀ : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a := y₁.val with hy₀def
  have hsy : s * y₀ * s⁻¹ = y₀⁻¹ := hsP y₀ y₁.2
  have hy₀' : orderOf y₀ = ℓ := by
    rw [hy₀def, Subgroup.orderOf_coe, hy₁]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [one_mul, inv_one, mul_one] at hsy
    have h2 : y₀ ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hsy]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy₀'] at this
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  have hs : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  set s' : X := g.symm s with hs'
  set y' : X := g.symm y₀ with hy'
  have hs'2 : orderOf s' = 2 := by rw [hs', MulEquiv.orderOf_eq, hs]
  have hy'ℓ : orderOf y' = ℓ := by rw [hy', MulEquiv.orderOf_eq, hy₀']
  have hsy' : s' * y' * s'⁻¹ = y'⁻¹ := by
    rw [hs', hy', ← map_inv, ← map_mul, ← map_mul, hsy, map_inv]
  have hc1 := CFSG.Quasithin.H13.L829NK.nk_suzuki_involution_isConj a K hK (e t)
    (by rw [MulEquiv.orderOf_eq, ht])
  have hc2 := CFSG.Quasithin.H13.L829NK.nk_suzuki_involution_isConj a K hK (e s')
    (by rw [MulEquiv.orderOf_eq, hs'2])
  obtain ⟨c, hc⟩ := isConj_iff.mp (hc1.trans hc2.symm)
  have hct : (e.symm c) * t * (e.symm c)⁻¹ = s' := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
  refine ⟨(e.symm c)⁻¹ * y' * (e.symm c), ?_, ?_⟩
  · rw [show (e.symm c)⁻¹ * y' * (e.symm c) = MulAut.conj (e.symm c)⁻¹ y' by
      rw [MulAut.conj_apply, inv_inv], MulEquiv.orderOf_eq, hy'ℓ]
  · have ht' : t = (e.symm c)⁻¹ * s' * (e.symm c) := by rw [← hct]; group
    calc t * ((e.symm c)⁻¹ * y' * e.symm c) * t⁻¹
        = (e.symm c)⁻¹ * (s' * y' * s'⁻¹) * e.symm c := by rw [ht']; group
      _ = ((e.symm c)⁻¹ * y' * e.symm c)⁻¹ := by rw [hsy']; group

theorem center_eq_bot_of_quotient (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* suzukiGroup a K) (hodd : Odd (Nat.card (center E))) :
    center E = ⊥ := by
  obtain ⟨f⟩ := SzModels.nonempty_mulEquiv_sz ha hK
  have h := CFSG.SignalizerFunctorTheorem.McBride.schur_odd_sz (n := a) (by omega) ⟨e.trans f⟩
    (QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (by rwa [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk'] at h

end CFSG.RankThree.S4Free.Suzuki
