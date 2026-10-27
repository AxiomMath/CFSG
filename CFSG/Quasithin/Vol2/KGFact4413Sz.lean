module

public import CFSG.Quasithin.Vol2.KGFact4413L2
public import CFSG.Quasithin.H13.KGFact22TorSz

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.QuasithinUnique CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
  CFSG.BenderSuzuki.PFAppendixIII CFSG.Quasithin.H13.KG22
open scoped Matrix LinearAlgebra.Projectivization

theorem suzukiWeylGL_mul_self (m : ℕ) : SuzukiWeylGL m * SuzukiWeylGL m = 1 := by
  apply Units.ext
  change SuzukiWeylMatrix m * SuzukiWeylMatrix m = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem not_dvd_sq_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) : ¬ p ∣ q ^ 2 + 1 := by
  intro h
  obtain ⟨k, hk⟩ := hpq
  have hq' : q = p * k + 1 := by omega
  have h2 : p ∣ q ^ 2 + 1 - p * (k * (p * k + 2)) := Nat.dvd_sub h (Dvd.intro _ rfl)
  have e : q ^ 2 + 1 - p * (k * (p * k + 2)) = 2 := by
    rw [hq']
    have : (p * k + 1) ^ 2 + 1 = p * (k * (p * k + 2)) + 2 := by ring
    omega
  rw [e] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem weylOut_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) :
    ∃ S₀ D₀ : Subgroup (SuzukiMatrixGroup m), IsSylowTwoOf S₀ ⊤ ∧
      D₀ ≤ Subgroup.normalizer (S₀ : Set (SuzukiMatrixGroup m)) ∧
      Subgroup.normalizer (S₀ : Set (SuzukiMatrixGroup m)) ≤ D₀ ⊔ S₀ ∧ D₀ ⊓ S₀ = ⊥ ∧
      WeylOut S₀ D₀ (2 * m + 1) ∧ IsCyclic ↥D₀ ∧
      ∃ w : SuzukiMatrixGroup m, w ∉ Subgroup.normalizer (S₀ : Set (SuzukiMatrixGroup m)) ∧
        ∀ d ∈ D₀, w * d * w⁻¹ = d⁻¹ := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := fun x =>
    iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  let F : Subgroup (GL (Fin 4) K) := Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) := Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hpi_unique, hpi_formula, hFp, _hF_pow_four, _hF_order_four, _hF_class, hFcard,
      _hF_typeA, _hroot_mul, _hcommutator, _hcommutator_coordinates, htorus_equiv,
      _htorus_conjugation, _hdisjoint, _hfixed_point_free⟩
  rcases htorus_equiv with ⟨eH, heH⟩
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨hpres, _hrecognition, _hfaithful, _htwo_raw, _hthree, hOcard_raw, hGcard, hstabilizer_raw⟩
  have hKcard : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using GaloisField.card 2 (2 * m + 1) (by omega)
  have hFcard' : Nat.card F = q ^ 2 := by simpa [F, q] using hFcard
  have hHcard : Nat.card H = q - 1 := by
    calc Nat.card H = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
      _ = Nat.card K - 1 := Nat.card_units K
      _ = q - 1 := by rw [hKcard]
  have hF_le_G : F ≤ G := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ G := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let R : Subgroup G := F.subgroupOf G
  let T : Subgroup G := H.subgroupOf G
  let U : Subgroup G := (F ⊔ H).subgroupOf G
  have hRT_sup : R ⊔ T = U := (Subgroup.subgroupOf_sup hF_le_G hH_le_G).symm
  have hH_le_normalizerF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    External.suzukiTorusClosure_le_normalizer_rootClosure m pi hpi_sq hpi_formula
  have hFH_le_normalizerF : F ⊔ H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    sup_le Subgroup.le_normalizer hH_le_normalizerF
  have hU_le_normalizerR : U ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hg' : ((g : G) : GL (Fin 4) K) ∈ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
      hFH_le_normalizerF hg
    rw [Subgroup.mem_normalizer_iff] at hg' ⊢
    intro r
    exact hg' ((r : G) : GL (Fin 4) K)
  let eR : R ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_G
  let eT : T ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G
  have hRp : IsPGroup 2 R := hFp.of_equiv eR.symm
  have hRcard : Nat.card R = q ^ 2 := (Nat.card_congr eR.toEquiv).trans hFcard'
  have hTcard : Nat.card T = q - 1 := (Nat.card_congr eT.toEquiv).trans hHcard
  let linRep : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (SuzukiMatrixGroup m).subtype
  let : MulAction G (ℙ K (Fin 4 → K)) := MulAction.compHom (ℙ K (Fin 4 → K)) linRep
  let ovoid : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact hpres g z hz }
  let : MulAction G Omega := ovoid.mulAction
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  have hU_eq_stabilizer : U = MulAction.stabilizer G pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ F ⊔ H ↔
      (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (hstabilizer_raw g).symm
  have hRregular : ∀ a b : Omega, a ≠ pinfO → b ≠ pinfO → ∃! r : R, (r : G) • a = b := by
    intro a b ha hb
    have ha_raw : (a : ℙ K (Fin 4 → K)) ≠ pinf := fun h => ha (Subtype.ext h)
    have hb_raw : (b : ℙ K (Fin 4 → K)) ≠ pinf := fun h => hb (Subtype.ext h)
    rcases External.suzukiRootClosure_regular_on_ovoid_complement m pi hpi
        (a : ℙ K (Fin 4 → K)) b a.property b.property ha_raw hb_raw with ⟨r, hr, hr_unique⟩
    let rR : R := ⟨⟨(r : GL (Fin 4) K), hF_le_G r.property⟩, r.property⟩
    refine ⟨rR, ?_, ?_⟩
    · apply Subtype.ext
      change (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K)).toLinearEquiv •
        (a : ℙ K (Fin 4 → K)) = b
      exact hr
    · intro s hs
      let sF : F := ⟨((s : G) : GL (Fin 4) K), s.property⟩
      have hs_raw : (Matrix.GeneralLinearGroup.toLin (sF : GL (Fin 4) K)).toLinearEquiv •
          (a : ℙ K (Fin 4 → K)) = b := congrArg Subtype.val hs
      have hsF_eq : sF = r := hr_unique sF hs_raw
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : F => (x : GL (Fin 4) K)) hsF_eq
  have hq_pos : 0 < q := by positivity
  have hq2 : 2 ≤ q := by
    show 2 ≤ 2 ^ (2 * m + 1)
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : ∃ b c : Omega, b ≠ pinfO ∧ c ≠ pinfO ∧ b ≠ c := by
    classical
    have := Fintype.ofFinite Omega
    have hOcard : Fintype.card Omega = q ^ 2 + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hOcard_raw
    have h2 : 2 < Fintype.card Omega := by
      rw [hOcard]
      nlinarith
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h2
    by_cases ha : a = pinfO
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = pinfO
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  have hNR : Subgroup.normalizer (R : Set G) ≤ R ⊔ T := by
    rw [hRT_sup, hU_eq_stabilizer]
    refine normalizer_le_stabilizer_of_regular ?_ hRregular h3
    rw [← hU_eq_stabilizer]
    exact le_sup_left.trans hRT_sup.le
  have hTN : T ≤ Subgroup.normalizer (R : Set G) :=
    fun t ht => hU_le_normalizerR (le_sup_right.trans hRT_sup.le ht)
  have hNeq : Subgroup.normalizer (R : Set G) = R ⊔ T :=
    le_antisymm hNR (sup_le Subgroup.le_normalizer hTN)
  have hTodd : Odd (Nat.card T) := by
    rw [hTcard]
    have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd hq_pos hqe odd_one
  have hTR : T ⊓ R = ⊥ := E2.BorelLift.inf_eq_bot_of_odd hTodd hRp
  have hNcard : Nat.card (Subgroup.normalizer (R : Set G)) = q ^ 2 * (q - 1) := by
    have h1 := E2.BorelLift.card_sup_mul_card_inf hTN
    rw [hTR, Subgroup.card_bot, mul_one, sup_comm, ← hNeq, hTcard, hRcard] at h1
    rw [h1, mul_comm]
  have hNidx : (Subgroup.normalizer (R : Set G)).index = q ^ 2 + 1 := by
    have h1 := (Subgroup.normalizer (R : Set G)).card_mul_index
    rw [hNcard, show Nat.card G = Nat.card (SuzukiMatrixGroup m) from rfl, hGcard] at h1
    have hpos : 0 < q ^ 2 * (q - 1) := by
      have : 0 < q - 1 := by omega
      positivity
    have h2 : q ^ 2 * (q - 1) * (Subgroup.normalizer (R : Set G)).index =
        q ^ 2 * (q - 1) * (q ^ 2 + 1) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hidx : ¬ 2 ∣ R.index := by
    have h1 := R.index_mul_card
    rw [hRcard, show Nat.card G = Nat.card (SuzukiMatrixGroup m) from rfl, hGcard] at h1
    have h2 : R.index = (q ^ 2 + 1) * (q - 1) := by
      have hq2' : 0 < q ^ 2 := by positivity
      have : R.index * q ^ 2 = (q ^ 2 + 1) * (q - 1) * q ^ 2 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hq2' this
    rw [h2]
    have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have ho : Odd ((q ^ 2 + 1) * (q - 1)) :=
      (Even.add_one (hqe.pow_of_ne_zero (by norm_num))).mul
        (Nat.Even.sub_odd hq_pos hqe odd_one)
    exact fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
  have hRS : IsSylowTwoOf R ⊤ := by
    refine ⟨le_top, hRp, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact hidx
  have hW : SuzukiWeylGL m ∈ G := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  let w : G := ⟨SuzukiWeylGL m, hW⟩
  have hwinf : w • pinfO ≠ pinfO := by
    intro h
    have h1 := congrArg Subtype.val h
    change (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv • pinf = pinf at h1
    rw [Projectivization.smul_mk] at h1
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 h1
    have h0 := congrFun hc 0
    simp [SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0
    rw [Units.smul_def, smul_eq_mul, mul_one] at h0
    exact c.ne_zero h0
  have hTexp : ∀ d ∈ T, d ^ (q - 1) = 1 := by
    intro d hd
    have := pow_card_eq_one' (G := T) (x := ⟨d, hd⟩)
    rw [hTcard] at this
    exact congrArg Subtype.val this
  have hwinv : ∀ d ∈ T, w * d * w⁻¹ = d⁻¹ := by
    intro y hy
    have hyH : ((y : G) : GL (Fin 4) K) ∈ H := hy
    obtain ⟨x, hx⟩ := eH.surjective ⟨_, hyH⟩
    have hyx : ((y : G) : GL (Fin 4) K) = SuzukiTorusGL m x := by
      rw [← heH x, hx]
    have hyx' : ((y⁻¹ : G) : GL (Fin 4) K) = SuzukiTorusGL m x⁻¹ := by
      rw [← heH, map_inv, Subgroup.coe_inv, Subgroup.coe_inv, hx]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hyx', hyx]
    exact suzukiWeyl_conj_torus m x
  have hwN : w ∉ Subgroup.normalizer (R : Set G) := by
    intro hw
    have h1 : w ∈ MulAction.stabilizer G pinfO := by
      rw [← hU_eq_stabilizer, ← hRT_sup]
      exact hNR hw
    exact hwinf h1
  have hTcyc : IsCyclic T := eT.isCyclic.mpr (eH.isCyclic.mp (inferInstance : IsCyclic Kˣ))
  refine ⟨R, T, hRS, hTN, by rw [hNeq, sup_comm], hTR, ⟨?_, ?_, w, hwN, ?_, ?_⟩, hTcyc, w, hwN,
    hwinv⟩
  · intro p' hp' hp2 hpq
    rw [hNidx]
    exact not_dvd_sq_add_one hp' hp2 (by omega) hpq
  · intro d hd
    rw [pow_mul, hTexp d hd, one_pow]
  · exact Subtype.ext (suzukiWeylGL_mul_self m)
  · intro d hd
    refine ⟨fun _ => hwinv d hd, fun h1 => ?_⟩
    have h2 := hTexp d hd
    have hd2 : d ^ 2 ^ 1 = 1 := by
      have e : q + 1 = (q - 1) + 2 := by omega
      rw [e, pow_add, h2, one_mul] at h1
      rw [pow_one]
      exact h1
    have hdo : Odd (orderOf d) := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : T)
      rw [Subgroup.orderOf_mk] at this
      exact hTodd.of_dvd_nat this
    rw [eq_one_of_odd_of_pow_two_pow hdo hd2, mul_one, mul_inv_cancel]

theorem cartanWeyl_of_isSz {X : Type} [Group X] {n : ℕ} (hX : IsSz n X) : CartanWeyl X n := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hX
  have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
  let e' : X ≃* SuzukiMatrixGroup a :=
    ((e.trans (MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K))).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard)).trans
      ((MulEquiv.subgroupCongr hmodel.symm).trans
        (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a)))
  obtain ⟨S₀, D₀, hS₀, h1, h2, h3, hW, -⟩ := weylOut_suzukiMatrixGroup a (by omega)
  exact cartanWeyl_of_mulEquiv (cartanWeyl_of_exists hS₀ h1 h2 h3 hW) e'.symm

end CFSG.Quasithin.H13.KG4413
