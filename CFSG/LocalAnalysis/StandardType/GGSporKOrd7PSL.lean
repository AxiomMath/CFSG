module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Lift
public import CFSG.LieType.ChevTwo.OppCl.SL
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

open CFSG.LieType.ChevTwo.OppCl CFSG.LieType.BorelTits in
private theorem lr2opsl_hlin {n f : ℕ} (h7q : ¬ 7 ∣ 2 ^ f - 1) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (r : Equiv.Perm (Fin n → K))
    (hr : r ∈ semilinGroup K (Fin n → K))
    (hc : ∀ (c : K) (v : Fin n → K), r (c • v) = c • r v)
    (hp : IsPGroup 7 (Subgroup.zpowers r)) :
    ∃ h : StatedSL n K, ∀ v, r v = natRep (StatedSL n K) h v := by
  classical
  let φ : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    { toFun := r
      map_add' := hr.1
      map_smul' := hc
      invFun := r.symm
      left_inv := r.left_inv
      right_inv := r.right_inv }
  let M : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' φ.toLinearMap
  let N : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' φ.symm.toLinearMap
  have hcomp : φ.toLinearMap.comp φ.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun v => φ.apply_symm_apply v
  have hMN : M * N = 1 := by
    dsimp only [M, N]
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  have hdet0 : M.det ≠ 0 := by
    intro hM0
    have h := congrArg Matrix.det hMN
    rw [Matrix.det_mul, Matrix.det_one, hM0, zero_mul] at h
    exact one_ne_zero h.symm
  obtain ⟨k, hk⟩ := hp ⟨r, Subgroup.mem_zpowers r⟩
  have hrpow : r ^ (7 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hφpow : φ.toLinearMap ^ (7 ^ k) = 1 := by
    apply LinearMap.ext
    intro v
    have h1 : ((φ.toLinearMap) ^ (7 ^ k)) v = (φ.toLinearMap)^[7 ^ k] v :=
      Module.End.pow_apply φ.toLinearMap (7 ^ k) v
    rw [h1]
    have h2 : (⇑φ.toLinearMap : (Fin n → K) → (Fin n → K)) = ⇑r := rfl
    rw [h2, ← Equiv.Perm.coe_pow, hrpow]
    rfl
  have hMpow : M ^ (7 ^ k) = 1 := by
    exact Matrix.toLin'.injective (by
      calc Matrix.toLin' (M ^ (7 ^ k)) = (Matrix.toLin' M) ^ (7 ^ k) :=
            Matrix.toLin'_pow M (7 ^ k)
        _ = φ.toLinearMap ^ (7 ^ k) := by simp [M]
        _ = 1 := hφpow
        _ = Matrix.toLin' (1 : Matrix (Fin n) (Fin n) K) := (Matrix.toLin'_one).symm)
  let d : Kˣ := Units.mk0 M.det hdet0
  have hd7 : d ^ (7 ^ k) = 1 := by
    apply Units.ext
    change M.det ^ (7 ^ k) = 1
    rw [← Matrix.det_pow, hMpow, Matrix.det_one]
  have hd2 : d ^ (2 ^ f - 1) = 1 := by
    have hcard : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
    rw [← hcard]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime (7 ^ k) (2 ^ f - 1) := by
    rcases k with _ | k
    · simp
    · exact (Nat.coprime_pow_left_iff (Nat.succ_pos k) 7 (2 ^ f - 1)).mpr
        (Nat.prime_seven.coprime_iff_not_dvd.mpr h7q)
  have hd1 : d = 1 := by
    have hm : orderOf d ∣ 7 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hd7
    have hn : orderOf d ∣ 2 ^ f - 1 := orderOf_dvd_iff_pow_eq_one.mpr hd2
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hm hn)
  have hdet1 : M.det = 1 := by
    change (d : K) = 1
    rw [hd1]
    rfl
  let g : StatedSL n K :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0,
      Subgroup.subset_closure (by
        show (Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0 :
            Matrix (Fin n) (Fin n) K).det = 1
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
        exact hdet1)⟩
  refine ⟨g, fun v => ?_⟩
  have hgval : ((g : StatedSL n K) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0 := rfl
  rw [natRep_apply, hgval, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [show M = LinearMap.toMatrix' φ.toLinearMap from rfl, LinearMap.toMatrix'_mulVec]
  rfl

open CFSG.LieType.ChevTwo.OppCl CFSG.LieType.BorelTits in
private theorem lr2opsl_h7k {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (h7q : ¬ 7 ∣ 2 ^ f - 1) :
    ¬ 7 ∣ Nat.card
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).ker := by
  rw [QuotientGroup.ker_mk']
  intro hdvd
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hscal : Nat.card (StatedScalars (Fin n) K) = Nat.card Kˣ := by
    have hinj : Function.Injective
        (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
      intro a b hab
      apply Units.ext
      have h := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) hab
      have h' := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using h'
    rw [StatedScalars]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hdvdz : Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) ∣ Nat.card Kˣ := by
    have h := Subgroup.card_comap_dvd_of_injective (StatedScalars (Fin n) K)
      (StatedSL n K).subtype (StatedSL n K).subtype_injective
    rw [hscal] at h
    exact h
  have h7K : ¬ 7 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact h7q
  exact h7K (hdvd.trans hdvdz)

open CFSG.LieType.ChevTwo.OppCl CFSG.LieType.BorelTits in
theorem ord7Param_PSL {n f : ℕ} (h7 : ¬ 7 ∣ f) (h7q : ¬ 7 ∣ 2 ^ f - 1) (hn : 3 ≤ n) :
    Ord7Param .PSL n 2 f := by
  unfold Ord7Param
  intro R _ _ hR hmodel
  have hcm : StatedClassicalModel R .PSL n 2 f :=
    hmodel.statedClassicalModel_of_ne_zero (by omega)
  obtain ⟨-, K, _, _, hK, hIso⟩ := hcm
  obtain ⟨e⟩ := hIso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Nontrivial (Fin n → K) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne K
    refine ⟨fun _ => a, fun _ => b, ?_⟩
    intro h
    exact hab (congrFun h ⟨0, by omega⟩)
  have hcardAut : Nat.card (RingAut K) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hK).1
  have h7F : ¬ 7 ∣ Nat.card (K ≃+* K) := by
    rw [show Nat.card (K ≃+* K) = f from hcardAut]
    exact h7
  have h7k : ¬ 7 ∣ Nat.card
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).ker :=
    lr2opsl_h7k (n := n) (f := f) (K := K) hn hK h7q
  have hind : ∀ R' : Subgroup (MulAut (StatedProj (StatedSL n K))), IsPGroup 7 R' →
      ∀ α ∈ R', ∃ r : Equiv.Perm (Fin n → K),
        r ∈ semilinGroup K (Fin n → K) ∧ True ∧
          Induces (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)))
            (natRep (StatedSL n K)) r α := by
    intro R' hR' α hα
    exact induced_PSL n K hn 7 (by norm_num) R' hR' α hα
  have hlin : ∀ r : Equiv.Perm (Fin n → K), r ∈ semilinGroup K (Fin n → K) → True →
      (∀ (c : K) (v : Fin n → K), r (c • v) = c • r v) →
      IsPGroup 7 (Subgroup.zpowers r) →
        ∃ h : StatedSL n K, ∀ v, r v = natRep (StatedSL n K) h v := by
    intro r hr _ hc hp
    exact lr2opsl_hlin (n := n) (f := f) (K := K) h7q hK r hr hc hp
  have hbound := ord7_factorization_le_of_lift
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)))
    (QuotientGroup.mk'_surjective _)
    (natRep (StatedSL n K)) (natRep_injective (StatedSL n K))
    (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    h7F h7k hind hlin
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (MulAut.congr e).toEquiv]
  simpa only [StatedProj] using hbound

end CFSG.StandardType.SporadicShape
