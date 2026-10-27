module

public import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreLemmaSPrime
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup

theorem orderOf_le_finrank_of_conj_of_ne_one {k M : Type*} [Field k] [AddCommGroup M]
    [Module k M] [FiniteDimensional k M] {p lam : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0)
    {c T : Module.End k M} (hcp : c ^ p = 1) (hc1 : c ≠ 1) (hT : Function.Surjective T)
    (hTc : T * c = c ^ lam * T) : orderOf (lam : ZMod p) ≤ Module.finrank k M := by
  classical
  set W := LinearMap.range (c - 1)
  have hcW : ∀ x ∈ W, c x ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨c v, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub]
  have hTW : ∀ x ∈ W, T x ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(∑ i ∈ Finset.range lam, c ^ i) (T v), ?_⟩
    rw [← Module.End.mul_apply, mul_geom_sum, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.sub_apply, Module.End.one_apply, map_sub, ← Module.End.mul_apply T c, hTc,
      Module.End.mul_apply]
  have hcWp : c.restrict hcW ^ p = 1 := by
    rw [Module.End.pow_restrict]
    exact LinearMap.ext fun w => Subtype.ext (by simp [hcp])
  have hfix : ∀ w : W, c.restrict hcW w = w → w = 0 := by
    rintro ⟨_, v, rfl⟩ hw
    have hw' : c ((c - 1) v) = (c - 1) v := congrArg Subtype.val hw
    have hpow : ∀ i : ℕ, (c ^ i) ((c - 1) v) = (c - 1) v := fun i => by
      induction i with
      | zero => rw [pow_zero, Module.End.one_apply]
      | succ i ih => rw [pow_succ, Module.End.mul_apply, hw', ih]
    have h0 : (∑ i ∈ Finset.range p, c ^ i) ((c - 1) v) = 0 := by
      rw [← Module.End.mul_apply, geom_sum_mul, hcp, sub_self, LinearMap.zero_apply]
    rw [LinearMap.sum_apply, Finset.sum_congr rfl fun i _ => hpow i, Finset.sum_const,
      Finset.card_range, ← Nat.cast_smul_eq_nsmul k] at h0
    exact Subtype.ext ((smul_eq_zero.mp h0).resolve_left hpk)
  have hTinj : Function.Injective T := LinearMap.injective_iff_surjective.mpr hT
  have hTWs : Function.Surjective (T.restrict hTW) :=
    LinearMap.injective_iff_surjective.mp fun x y h =>
      Subtype.ext (hTinj (congrArg Subtype.val h))
  have hTWc : T.restrict hTW * c.restrict hcW = c.restrict hcW ^ lam * T.restrict hTW := by
    rw [Module.End.pow_restrict]
    exact LinearMap.ext fun w => Subtype.ext (by simpa using LinearMap.congr_fun hTc (w : M))
  obtain ⟨v, hv⟩ : ∃ v, c v ≠ v := by
    by_contra h
    push Not at h
    exact hc1 (LinearMap.ext fun v => by rw [h v, Module.End.one_apply])
  haveI : Nontrivial W := ⟨⟨⟨(c - 1) v, LinearMap.mem_range_self _ v⟩, 0, fun h => hv (by
    have h' : (c - 1) v = 0 := congrArg Subtype.val h
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h')⟩⟩
  calc orderOf (lam : ZMod p) ≤ Module.finrank k W :=
        CFSG.AGLEmbeddingD2.orderOf_le_finrank_of_conj hp hcWp hfix hTWs hTWc
    _ ≤ Module.finrank k M := Submodule.finrank_le W

theorem orderOf_le_of_conj_statedProj {K : Type} [Field K] {n q k : ℕ} (hq : q.Prime)
    (hqK : (q : K) ≠ 0) (hqn : q.Coprime n) {H : Subgroup (GL (Fin n) K)}
    (hH : H ≤ StatedSL n K) {a b : StatedProj H} (ha : orderOf a = q)
    (hab : b * a * b⁻¹ = a ^ k) : orderOf (k : ZMod q) ≤ n := by
  classical
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hsc : ∀ z : ↥H, z ∈ (StatedScalars (Fin n) K).subgroupOf H →
      z ^ n = 1 ∧ ∀ g : ↥H, z * g = g * z := by
    intro z hz
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
    have hdet := StatedAPI.det_of_mem_statedSL (hH z.2)
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hcn : c ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    have hcen : (z : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, hc⟩
    refine ⟨Subtype.ext ?_, fun g => Subtype.ext ?_⟩
    · rw [Subgroup.coe_pow, ← hc, ← map_pow, hcn, map_one, Subgroup.coe_one]
    · exact ((Subgroup.mem_center_iff.mp hcen) g).symm
  have hxq : x ^ q ∈ (StatedScalars (Fin n) K).subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← ha, pow_orderOf_eq_one]
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hqn.symm hq.one_lt
  set x' := x ^ (n * m) with hx'
  have hx'mk : ((x' : ↥H) : StatedProj H) = (x : StatedProj H) := by
    rw [hx', QuotientGroup.mk_pow, ← pow_mod_orderOf, ha, hm, pow_one]
  have hx'q : x' ^ q = 1 := by
    rw [hx', ← pow_mul, show n * m * q = q * n * m by ring, pow_mul, pow_mul, (hsc _ hxq).1,
      one_pow]
  set z := (x' ^ k)⁻¹ * (y * x' * y⁻¹) with hzdef
  have hz : z ∈ (StatedScalars (Fin n) K).subgroupOf H := by
    rw [hzdef, ← QuotientGroup.eq, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx'mk, hab]
  have hzq : z ^ q = 1 := by
    have h1 : (y * x' * y⁻¹) ^ q = 1 := by rw [conj_pow, hx'q, mul_one, mul_inv_cancel]
    rw [show y * x' * y⁻¹ = x' ^ k * z by rw [hzdef, mul_inv_cancel_left],
      (Commute.mul_pow ((hsc z hz).2 (x' ^ k)).symm q), ← pow_mul, mul_comm k q, pow_mul, hx'q,
      one_pow, one_mul] at h1
    exact h1
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hqn
    (orderOf_dvd_of_pow_eq_one hzq) (orderOf_dvd_of_pow_eq_one (hsc z hz).1))
  have hyx : y * x' = x' ^ k * y := by
    rw [hzdef, inv_mul_eq_one] at hz1
    rw [hz1, inv_mul_cancel_right]
  let φ : ↥H →* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp H.subtype)
  have hφ : Function.Injective φ := fun g h hgh => Subtype.ext (Units.ext
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _).injective hgh))
  have hc1 : φ x' ≠ 1 := fun h => by
    have h1 : x' = 1 := hφ (by rw [h, map_one])
    have h2 : (x : StatedProj H) = 1 := by rw [← hx'mk, h1, QuotientGroup.mk_one]
    rw [h2, orderOf_one] at ha
    exact hq.one_lt.ne ha
  have hT : Function.Surjective (φ y) := fun v => ⟨φ y⁻¹ v, by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  calc orderOf (k : ZMod q) ≤ Module.finrank K (Fin n → K) :=
        orderOf_le_finrank_of_conj_of_ne_one hq hqK (by rw [← map_pow, hx'q, map_one]) hc1 hT
          (by rw [← map_mul, hyx, map_mul, map_pow])
    _ = n := Module.finrank_fin_fun K

theorem orderOf_le_of_conj_of_mulEquiv {Q : Type} [Group Q] {K : Type} [Field K] [Finite K]
    {n p m q k : ℕ} {T : Subgroup (GL (Fin n) K)} (hT : T ≤ StatedSL n K)
    (e : Q ≃* StatedProj T) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hK : Nat.card K = p ^ m)
    (hn : 0 < n) (hnq : n < q) {a b : Q} (ha : orderOf a = q) (hab : b * a * b⁻¹ = a ^ k) :
    orderOf (k : ZMod q) ≤ n := by
  have hqK : (q : K) ≠ 0 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.natCast_ne_zero_of_not_dvd_card hq
      (by
        rw [hK]
        exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.not_dvd_pow_of_ne hq hp hpq)
  have hqn : q.Coprime n := (Nat.Prime.coprime_iff_not_dvd hq).mpr
    fun h => absurd (Nat.le_of_dvd hn h) (by omega)
  exact orderOf_le_of_conj_statedProj hq hqK hqn hT (a := e a) (b := e b)
    (by rw [MulEquiv.orderOf_eq, ha]) (by rw [← map_inv, ← map_mul, ← map_mul, hab, map_pow])

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
