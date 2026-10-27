module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective

public section

namespace CFSG.Walter

open scoped MatrixGroups
open CFSG.GorensteinWalter

section Map

variable {R S : Type*} [Field R] [Field S]

theorem sl2_map_mem_center (φ : R →+* S) {A : SL(2, R)} (hA : A ∈ Subgroup.center SL(2, R)) :
    Matrix.SpecialLinearGroup.map φ A ∈ Subgroup.center SL(2, S) := by
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨φ c, by rw [← map_pow, hc, map_one], ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe, ← hcA]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, h]

@[expose] noncomputable def psl2Map (φ : R →+* S) : PSL(2, R) →* PSL(2, S) :=
  QuotientGroup.map _ _ (Matrix.SpecialLinearGroup.map φ) (fun _ hA => sl2_map_mem_center φ hA)

theorem psl2Map_mk (φ : R →+* S) (A : SL(2, R)) :
    psl2Map φ (QuotientGroup.mk A) = QuotientGroup.mk (Matrix.SpecialLinearGroup.map φ A) :=
  rfl

theorem psl2Map_injective (φ : R →+* S) : Function.Injective (psl2Map φ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, psl2Map_mk, QuotientGroup.eq_one_iff] at hx
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hentry : ∀ i j, φ (A i j) = Matrix.scalar (Fin 2) c i j := by
    intro i j
    rw [hcA, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have h00 : φ (A 0 0) = c := by
    rw [hentry]
    simp [Matrix.scalar_apply]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨A 0 0, φ.injective ?_, ?_⟩
  · rw [map_pow, h00, map_one]
    simpa using hc
  · ext i j
    apply φ.injective
    rw [hentry]
    by_cases h : i = j
    · subst h
      simp [Matrix.scalar_apply, h00]
    · simp [Matrix.scalar_apply, h]

theorem psl2FieldAut_eq_psl2Map {K : Type*} [Field K] (σ : K ≃+* K) (y : PSL(2, K)) :
    psl2FieldAut K σ y = psl2Map σ.toRingHom y := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  rw [psl2FieldAut_apply]
  exact psl2RingEquiv_mk σ A

end Map

section Fixed

variable {K : Type*} [Field K]

theorem mem_fixedSubfield_iff (σ : K ≃+* K) (a : K) :
    a ∈ FixedPoints.subfield (Subgroup.zpowers σ) K ↔ σ a = a := by
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h m
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (RingAut K) a := by
      rw [Subgroup.zpowers_le]
      exact h
    exact hle m.2

theorem mem_zpowers_sq_of_odd {G : Type*} [Group G] {g : G} (hg : Odd (orderOf g)) :
    g ∈ Subgroup.zpowers (g ^ 2) := by
  obtain ⟨k, hk⟩ := hg
  refine ⟨(k + 1 : ℕ), ?_⟩
  simp only [zpow_natCast]
  rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem psl2Map_eq_self_iff (σ : K ≃+* K) (hσ : Odd (orderOf σ)) (y : PSL(2, K)) :
    psl2Map σ.toRingHom y = y ↔
      y ∈ (psl2Map (FixedPoints.subfield (Subgroup.zpowers σ) K).subtype).range := by
  set F0 := FixedPoints.subfield (Subgroup.zpowers σ) K with hF0
  constructor
  · intro hy
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
    rw [psl2Map_mk] at hy
    have hc := QuotientGroup.eq.mp hy
    obtain ⟨c, hc2, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hcc : c * c = 1 := by simpa [sq] using hc2
    have hσc : σ c = c := by
      have : c = 1 ∨ c = -1 := mul_self_eq_one_iff.mp hcc
      rcases this with rfl | rfl <;> simp
    have hentry : ∀ i j, A i j = σ (A i j) * c := by
      intro i j
      have h1 : (A : Matrix (Fin 2) (Fin 2) K) =
          ((Matrix.SpecialLinearGroup.map σ.toRingHom A : SL(2, K)) :
            Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) c := by
        rw [hcA, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
      calc A i j = (((Matrix.SpecialLinearGroup.map σ.toRingHom A : SL(2, K)) :
            Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) c) i j :=
            congrFun (congrFun h1 i) j
        _ = σ (A i j) * c := by
          simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.SpecialLinearGroup.map_apply_coe]
    have hfix : ∀ i j, σ (A i j) = A i j := by
      intro i j
      have hσa : σ (A i j) = A i j * c := by
        calc σ (A i j) = σ (A i j) * (c * c) := by rw [hcc, mul_one]
          _ = (σ (A i j) * c) * c := by ring
          _ = A i j * c := by rw [← hentry i j]
      have h2 : (σ ^ 2) • A i j = A i j := by
        rw [RingAut.smul_def, pow_two, RingAut.mul_apply, hσa, map_mul, hσa, hσc, mul_assoc,
          hcc, mul_one]
      have hle : Subgroup.zpowers (σ ^ 2) ≤ MulAction.stabilizer (RingAut K) (A i j) := by
        rw [Subgroup.zpowers_le]
        exact h2
      have := hle (mem_zpowers_sq_of_odd hσ)
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at this
    let B : SL(2, F0) :=
      ⟨Matrix.of fun i j => ⟨A i j, (mem_fixedSubfield_iff σ _).mpr (hfix i j)⟩, by
        apply F0.subtype.injective
        rw [map_one, RingHom.map_det]
        convert A.2
        ext i j
        rfl⟩
    refine ⟨QuotientGroup.mk B, ?_⟩
    rw [psl2Map_mk]
    congr 1
  · rintro ⟨B, rfl⟩
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective B
    rw [psl2Map_mk, psl2Map_mk]
    congr 1
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (mem_fixedSubfield_iff σ _).mp (B i j).2

theorem card_fixedSubfield_galoisField {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0)
    (σ : GaloisField p f ≃+* GaloisField p f) :
    orderOf σ ∣ f ∧ Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) (GaloisField p f)) =
      p ^ (f / orderOf σ) := by
  set K := GaloisField p f
  set F0 := FixedPoints.subfield (Subgroup.zpowers σ) K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) (fun a b h => RingEquiv.ext (congrFun h))
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have hfin : Module.finrank F0 K = orderOf σ := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers]
  have hcard : Nat.card K = Nat.card F0 ^ orderOf σ := by
    rw [← hfin]
    exact Module.natCard_eq_pow_finrank
  rw [GaloisField.card p f hf] at hcard
  have hr : 0 < orderOf σ := orderOf_pos σ
  have hdvd : Nat.card F0 ∣ p ^ f := by
    rw [hcard]
    exact dvd_pow_self _ hr.ne'
  obtain ⟨m, -, hF0⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  rw [hF0, ← pow_mul] at hcard
  have hfm : f = m * orderOf σ := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard
  exact ⟨⟨m, hfm.trans (mul_comm _ _)⟩, by rw [hF0, Nat.div_eq_of_eq_mul_left hr hfm]⟩

end Fixed

theorem pow_mod_eight_of_odd {p f : ℕ} (hp : Odd p) (hf : Odd f) : p ^ f % 8 = p % 8 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, sq_mod_eight_of_odd hp, one_pow]
  simp

section FourGroup

variable {p f : ℕ} [Fact p.Prime]

theorem psl2FieldAut_psl2Map_zmod (τ : GaloisField p f ≃+* GaloisField p f)
    (x : PSL(2, ZMod p)) :
    psl2FieldAut _ τ (psl2Map (algebraMap (ZMod p) (GaloisField p f)) x) =
      psl2Map (algebraMap (ZMod p) (GaloisField p f)) x := by
  rw [psl2FieldAut_eq_psl2Map]
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [psl2Map_mk, psl2Map_mk]
  congr 1
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact DFunLike.congr_fun (RingHom.ext_zmod (τ.toRingHom.comp (algebraMap (ZMod p) _))
    (algebraMap (ZMod p) _)) (A i j)

theorem exists_kleinFour_fieldAut_fixed (hp : Odd p) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    ∃ V : Subgroup PSL(2, GaloisField p f), IsKleinFour V ∧
      ∀ τ : GaloisField p f ≃+* GaloisField p f, ∀ v ∈ V, psl2FieldAut _ τ v = v := by
  have hp8 : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by
    rw [pow_one, ← pow_mod_eight_of_odd hp (odd_of_pow_mod_eight hp h8)]
    exact h8
  have hZ : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨P0⟩ : Nonempty (Sylow 2 PSL(2, ZMod p)) := inferInstance
  have hP0 := psl2_sylow_two_isKleinFour (ZMod p) hZ hp one_pos hp8 P0
  refine ⟨(P0 : Subgroup _).map (psl2Map (algebraMap (ZMod p) (GaloisField p f))),
    isKleinFour_map_of_injective _ hP0 _ (psl2Map_injective _), ?_⟩
  rintro τ _ ⟨x, -, rfl⟩
  exact psl2FieldAut_psl2Map_zmod τ x

end FourGroup

theorem psl2_mulAut_of_centralizes_sylow_two
    {p f r : ℕ} [Fact p.Prime] (hp : Odd p)
    (hf : 0 < f) (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (hr : r.Prime)
    (hr2 : r ≠ 2) (α : MulAut PSL(2, GaloisField p f)) (hα : orderOf α = r)
    (S : Sylow 2 PSL(2, GaloisField p f))
    (hαS : ∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x) :
    (∃ σ : GaloisField p f ≃+* GaloisField p f, orderOf σ = r ∧
      ∃ k : PSL(2, GaloisField p f),
        α = MulAut.conj k * psl2FieldAut (GaloisField p f) σ * (MulAut.conj k)⁻¹) ∧
    r ∣ f ∧
    Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id _) ≃* PSL(2, GaloisField p (f / r))) := by
  classical
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK hp hf
  have hcard : 3 < Nat.card K := by omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨V0, hV0, hV0fix⟩ := exists_kleinFour_fieldAut_fixed hp h8
  have hScard : Nat.card (S : Subgroup PSL(2, K)) = 4 :=
    psl2_sylow_two_card_eq_four K hK hp hf h8 S
  let V0S : Sylow 2 PSL(2, K) :=
    Sylow.ofCard V0 (by rw [hV0.card_four, ← hScard, S.card_eq_multiplicity])
  have hV0S : (V0S : Subgroup PSL(2, K)) = V0 := Sylow.coe_ofCard _ _
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, K) S V0S
  set α' := MulAut.conj k * α * (MulAut.conj k)⁻¹ with hα'
  have hα'V : ∀ v ∈ V0, α' v = v := by
    intro v hv
    have hv' : v ∈ ((k • S : Sylow 2 PSL(2, K)) : Subgroup PSL(2, K)) := by
      rw [hk, hV0S]
      exact hv
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hv'
    have h := hαS _ hv'
    change (MulAut.conj k) (α ((MulAut.conj k)⁻¹ v)) = v
    rw [← MulAut.smul_def ((MulAut.conj k)⁻¹) v, h, MulAut.smul_def, ← MulAut.mul_apply,
      mul_inv_cancel, MulAut.one_apply]
  have hα'ord : orderOf α' = r := by
    rw [hα', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hα]
  have hψinj := pGammaL2ToMulAutPSL2_injective K hK' hcard
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K hK hK' hcard α'
  set g := x.left
  set σ := x.right
  have hα'gσ : α' = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
    rw [← hx, ← SemidirectProduct.inl_left_mul_inr_right x, map_mul, pGammaL2ToMulAutPSL2_inl,
      pGammaL2ToMulAutPSL2_inr]
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V0.map toPGL) := isKleinFour_map_of_injective V0 hV0 toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V0.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      have h := hα'V v hv
      rw [hα'gσ, MulAut.mul_apply, hV0fix σ v hv] at h
      exact h
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  have hα'2 : α' = MulAut.conj g0 * psl2FieldAut K σ := by
    rw [hα'gσ, ← hg0]
    exact congrArg (· * psl2FieldAut K σ) (pgl2InnerAutPSL2_toPGL K hK' hcard g0)
  have hfix0 : psl2FieldAut K σ g0 = g0 := hV0fix σ g0 hg0V
  have hcomm : Commute (MulAut.conj g0) (psl2FieldAut K σ) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix0]
  have hg02 : g0 ^ 2 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨g0, hg0V⟩ : V0)
    rw [hV0.exponent_two] at h
    exact congrArg Subtype.val h
  have hg0r : g0 ^ r = g0 := by
    obtain ⟨j, hj⟩ := hrodd
    rw [hj, pow_succ, pow_mul, hg02, one_pow, one_mul]
  have hpow : α' ^ r = 1 := by rw [← hα'ord, pow_orderOf_eq_one]
  rw [hα'2, hcomm.mul_pow, ← map_pow, hg0r, ← map_pow] at hpow
  have hinl : pGammaL2ToMulAutPSL2 K hK' hcard
      (SemidirectProduct.inl (toPGL g0) * SemidirectProduct.inr (σ ^ r)) =
      pGammaL2ToMulAutPSL2 K hK' hcard 1 := by
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
      pgl2InnerAutPSL2_toPGL, map_one]
    exact hpow
  have h1 := hψinj hinl
  have hleft := congrArg SemidirectProduct.left h1
  have hright := congrArg SemidirectProduct.right h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inr,
    SemidirectProduct.right_inl, SemidirectProduct.one_left, map_one, mul_one] at hleft
  simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
    SemidirectProduct.right_inr, SemidirectProduct.one_right, one_mul] at hright
  have hg01 : g0 = 1 := htoPGL (by rw [hleft, map_one])
  have hα'σ : α' = psl2FieldAut K σ := by rw [hα'2, hg01, map_one, one_mul]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, map_one] at hα'σ
    rw [hα'σ, orderOf_one] at hα'ord
    exact hr.one_lt.ne hα'ord
  have hσord : orderOf σ = r := by
    have : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime hright hσ1
  obtain ⟨hrf, hF0card⟩ := card_fixedSubfield_galoisField hf.ne' σ
  rw [hσord] at hrf hF0card
  refine ⟨⟨σ, hσord, k⁻¹, ?_⟩, hrf, ?_⟩
  · rw [← hα'σ, hα', map_inv]
    group
  set F0 := FixedPoints.subfield (Subgroup.zpowers σ) K with hF0
  have hfixα' : α'.toMonoidHom.eqLocus (MonoidHom.id _) = (psl2Map F0.subtype).range := by
    ext y
    change α' y = y ↔ _
    rw [hα'σ, psl2FieldAut_eq_psl2Map]
    exact psl2Map_eq_self_iff σ (hσord ▸ hrodd) y
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id _)).map (MulAut.conj k).toMonoidHom =
      α'.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext y
    rw [Subgroup.mem_map_equiv]
    change α ((MulAut.conj k).symm y) = (MulAut.conj k).symm y ↔ α' y = y
    change _ ↔ (MulAut.conj k) (α ((MulAut.conj k).symm y)) = y
    exact MulEquiv.eq_symm_apply (MulAut.conj k)
  let e1 : α.toMonoidHom.eqLocus (MonoidHom.id _) ≃* (psl2Map F0.subtype).range :=
    ((MulAut.conj k).subgroupMap _).trans (MulEquiv.subgroupCongr (hmap.trans hfixα'))
  let e2 : (psl2Map F0.subtype).range ≃* PSL(2, F0) :=
    (MonoidHom.ofInjective (psl2Map_injective _)).symm
  have hfr : f / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hf hrf) hr.pos).ne'
  have : Fintype F0 := Fintype.ofFinite F0
  have : Fintype (GaloisField p (f / r)) := Fintype.ofFinite _
  let e3 : F0 ≃+* GaloisField p (f / r) := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF0card, GaloisField.card p _ hfr])
  exact ⟨e1.trans (e2.trans (psl2RingEquiv e3))⟩

end CFSG.Walter
