module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.Blueprint

section AtFrame


noncomputable def ggKGTc_w0
    (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd ((RootOps.longestWord τ).map τ.idx)

private theorem ggKGTc_symm_0
    :
    TwistTag.E6.perm.symm (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨5, by decide⟩ := by
  decide +kernel

private theorem ggKGTc_symm_1
    :
    TwistTag.E6.perm.symm (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨1, by decide⟩ := by
  decide +kernel

private theorem ggKGTc_symm_2
    :
    TwistTag.E6.perm.symm (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨4, by decide⟩ := by
  decide +kernel

private theorem ggKGTc_symm_3
    :
    TwistTag.E6.perm.symm (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨3, by decide⟩ := by
  decide +kernel

private theorem ggKGTc_symm_4
    :
    TwistTag.E6.perm.symm (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨2, by decide⟩ := by
  decide +kernel

private theorem ggKGTc_symm_5
    :
    TwistTag.E6.perm.symm (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨0, by decide⟩ := by
  decide +kernel

theorem ggKGTc_w0_smul_E6
    (i : Fin TwistTag.E6.tag.rank) :
    ggKGTc_w0 (TwistTag.E6.tag) • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      -Pi.single (TwistTag.E6.perm i) 1 := by
  rw [ggKGTc_w0, wordProd_smul]
  funext j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem ggKGTc_height_neg_single
    (k : Fin TwistTag.E6.tag.rank) :
    height (-Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) < 0 := by
  rw [height]
  simp

private theorem ggKGTc_w0_reversesSigns_E6 :
    ReversesSigns (ggKGTc_w0 (TwistTag.E6.tag)) := by
  have hsingle : ∀ i : Fin TwistTag.E6.tag.rank,
      height (ggKGTc_w0 (TwistTag.E6.tag) • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
        < 0 := by
    intro i
    rw [ggKGTc_w0_smul_E6 i]
    exact ggKGTc_height_neg_single (TwistTag.E6.perm i)
  intro α hα hpos
  exact height_smul_neg_of_forall_single hsingle hα hpos

theorem ggKGTc_w0_inv_E6 :
    (ggKGTc_w0 (TwistTag.E6.tag))⁻¹ = ggKGTc_w0 (TwistTag.E6.tag) :=
  (ReversesSigns.eq (ggKGTc_w0_reversesSigns_E6)
    (ReversesSigns.inv (ggKGTc_w0_reversesSigns_E6))).symm

theorem ggKGTc_eq_w0_E6
    {w : WeylGroup TwistTag.E6.tag}
      (hw : ExcIsLongest TwistTag.E6.tag w) :
    w = ggKGTc_w0 (TwistTag.E6.tag) := by
  refine ReversesSigns.eq ?_ (ggKGTc_w0_reversesSigns_E6)
  refine fun α hα hpos => (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun j =>
    hw α hα ((IsRoot.height_pos_iff hα).1 hpos) j

private theorem ggKGTc_rootChar_neg_single
    {L : Type} [Field L]
    (c : Fin TwistTag.E6.tag.rank → Lˣ) (k : Fin TwistTag.E6.tag.rank) :
    rootChar c (-Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) = (c k)⁻¹ := by
  rw [show -Pi.single k 1 = (-1 : ℤ) • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) by simp,
    rootChar_zsmul,
    show rootChar c (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) = c k from by
      simpa using rootChar_nsmul_single c k 1]
  rw [zpow_neg_one]

theorem ggKGTc_weylTuple_w0_perm
    {K : Type} [Field K]
    (c : Fin TwistTag.E6.tag.rank → Kˣ) :
    weylTuple (ggKGTc_w0 (TwistTag.E6.tag)) c = fun i => (c (TwistTag.E6.perm i))⁻¹ := by
  funext i
  rw [weylTuple, ggKGTc_w0_inv_E6, ggKGTc_w0_smul_E6 i]
  exact ggKGTc_rootChar_neg_single c (TwistTag.E6.perm i)

theorem ggKGTc_units_map_fr_eq_pow
    {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (u : (AlgebraicClosure K)ˣ) :
    Units.map Fr.toMonoidHom u = u ^ (2 ^ n) := by
  apply Units.ext
  rw [Units.coe_map]
  change Fr ↑u = ↑u ^ (2 ^ n)
  rw [hFr]

theorem ggKGTc_fr_inv_eq_self
    {K : Type} [Field K] {n : ℕ} {p : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {b : (AlgebraicClosure K)ˣ} (hb : b ^ p = 1)
    (hpq : p ∣ 2 ^ n + 1) : (Units.map Fr.toMonoidHom b)⁻¹ = b := by
  obtain ⟨k, hk⟩ := hpq
  have hpk : 1 ≤ p * k := by rw [← hk]; exact Nat.succ_le_succ (Nat.zero_le _)
  have hq : 2 ^ n = p * k - 1 := (Nat.sub_eq_of_eq_add hk.symm).symm
  have h1 : b ^ (p * k) = 1 := by rw [pow_mul, hb, one_pow]
  have h2 : b ^ (p * k - 1) = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hpk, h1]
  rw [ggKGTc_units_map_fr_eq_pow Fr hFr b, hq, h2, inv_inv]

theorem ggKGTc_fr_eq_self
    {K : Type} [Field K] {n : ℕ} {p : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {b : (AlgebraicClosure K)ˣ} (hb : b ^ p = 1)
    (hpq : p ∣ 2 ^ n - 1) : Units.map Fr.toMonoidHom b = b := by
  obtain ⟨k, hk⟩ := hpq
  have hq : 2 ^ n = p * k + 1 := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [← hk, Nat.sub_add_cancel h1]
  rw [ggKGTc_units_map_fr_eq_pow Fr hFr b, hq, pow_add, pow_mul, hb, one_pow, one_mul, pow_one]

theorem ggKGTc_coe_mem_adjointGroup
    {K : Type} [Field K] {σ : K ≃+* K}
    (y : twistedE6RootGroup K σ) :
    (y : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
  ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
    (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom y.2)).1

theorem ggKGTc_mem_torus_of_weylTuple
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E)
    {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (hact : weylTuple F.v
        (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b) :
    rootDiagUnit TwistTag.E6.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) := by
  refine mem_twistedTorusOf.2 ⟨?_, ?_⟩
  · exact rootDiagUnit_mem_torusGroup b
  · have h1 : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr (rootDiagUnit TwistTag.E6.tag b) =
        rootDiagUnit TwistTag.E6.tag
          (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) :=
      twistHom_rootDiagUnit_eq (t := TwistTag.E6) b
    rw [h1, canonicalRep_conj_rootDiagUnit, hact]

theorem ggKGTc_mem_image_of_fixed_pow
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {r : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hr : r ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hrF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr r = r) (hrp : r ^ p = 1) :
    r ∈ (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hc : Nat.card K = 1 := by rw [hK, hn0]; norm_num
    haveI : Fintype K := Fintype.ofFinite K
    have : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      Nat.prime_two hn1 K hK σ.toRingHom hσ (AlgebraicClosure K) Fr hFr
  have hder' : ⁅twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
      (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := hder
  set R := twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr with hR
  set C' := (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))
    with hC'
  have hle : C' ≤ R := by
    rw [← hder']
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder', h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]; infer_instance
  haveI : (C'.subgroupOf R).Normal := hnormal
  have hrR : r ∈ R := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
    ⟨hr, hrF⟩
  let P : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) := Subgroup.zpowers r
  have hPR : P ≤ R := Subgroup.zpowers_le.2 hrR
  have hPfin : Finite P := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hrp) hp.pos).ne')
  haveI : Finite P := hPfin
  have hPp : IsPGroup p P := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hrp) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hPC' : P ≤ C' :=
    le_of_isPGroup_of_index_eq_pow hPR hp Nat.prime_three (by omega) hk hPp
  exact hPC' (Subgroup.mem_zpowers r)

theorem ggKGTc_torus_pow_eq_image
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E) :
    ∀ d ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr), d ^ p = 1 →
      ∃ x ∈ E, d = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * F.g0 := by
  intro d hd hdp
  have hg0 : F.g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := F.g0_mem
  have hdT : d ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := (mem_twistedTorusOf.1 hd).1
  have hdG : d ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    torusGroup_le_adjointGroup' hdT
  set r : ModGL TwistTag.E6.tag (AlgebraicClosure K) := F.g0 * d * F.g0⁻¹ with hrdef
  have hrG : r ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (mul_mem hg0 hdG) (inv_mem hg0)
  have hrF : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr r = r := by
    have hg0' : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0 =
        F.g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v := F.lang
    have hd' : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr d =
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ * d *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v := by
      have h := (mem_twistedTorusOf.1 hd).2
      calc twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr d
          = (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v *
                twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr d *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹) *
              canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v := by group
        _ = (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ * d *
              canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v := by rw [h]
    calc twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr r
        = twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr (F.g0 * d * F.g0⁻¹) := by rw [hrdef]
      _ = twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0 *
            twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr d *
            (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = (F.g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v) *
            ((canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ * d *
              canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v) *
            (F.g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ := by
            rw [hg0', hd']
      _ = F.g0 * d * F.g0⁻¹ := by group
      _ = r := by rw [hrdef]
  have hrp : r ^ p = 1 := by rw [hrdef, conj_pow, hdp, mul_one, mul_inv_cancel]
  obtain ⟨x, hxC, hxr⟩ := Subgroup.mem_map.1
    (ggKGTc_mem_image_of_fixed_pow hK hσ hp hp5 F.Fr F.fr_eq hrG hrF hrp)
  refine ⟨⟨x, hxC⟩, ?_, ?_⟩
  · rw [F.mem_iff]
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [map_pow, map_one, hxr, hrp]
    · rw [hxr, hrdef]
      convert hd using 1
      group
  · rw [hxr, hrdef]
    group

theorem ggKGTc_twistHom_baseChange_eq_self
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (y : twistedE6RootGroup K σ) :
    twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) := by
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      F.Fr.comp (algebraMap K (AlgebraicClosure K)) := by
    ext c
    change algebraMap K (AlgebraicClosure K) (σ c) =
      F.Fr (algebraMap K (AlgebraicClosure K) c)
    rw [hσ, F.fr_eq, map_pow]
  rw [twistHom_baseChangeGL (algebraMap K (AlgebraicClosure K)) hcomm,
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom y.2)).2]

theorem ggKGTc_exists_conj_of_hact
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ} (hb : ∀ j, b j ^ p = 1)
    (hact : weylTuple F.v
        (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b) :
    ∃ e ∈ E, rootDiagUnit TwistTag.E6.tag b =
      F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) *
        F.g0 := by
  have hd : rootDiagUnit TwistTag.E6.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) :=
    ggKGTc_mem_torus_of_weylTuple F hact
  have hdp : (rootDiagUnit TwistTag.E6.tag b) ^ p = 1 := by
    rw [rootDiagUnit_pow]
    have hbp : b ^ p = 1 := by
      funext j
      simp [Pi.pow_apply, hb j]
    rw [hbp, rootDiagUnit_one]
  exact ggKGTc_torus_pow_eq_image hK hσ hp hp5 F (rootDiagUnit TwistTag.E6.tag b) hd hdp

theorem ggKGTc_hact_w_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (hvn : F.v = 1)
    (hpq : p ∣ 2 ^ n - 1) {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (hb : ∀ j, b j ^ p = 1)
    (h05 : b ⟨0, by decide⟩ = b ⟨5, by decide⟩)
    (h24 : b ⟨2, by decide⟩ = b ⟨4, by decide⟩) :
    weylTuple F.v (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b := by
  rw [hvn, weylTuple_one]
  funext k
  rw [ggKGTc_fr_eq_self F.Fr F.fr_eq (hb (TwistTag.E6.perm.symm k)) hpq]
  fin_cases k
  · rw [ggKGTc_symm_0]; exact h05.symm
  · rw [ggKGTc_symm_1]
  · rw [ggKGTc_symm_2]; exact h24.symm
  · rw [ggKGTc_symm_3]
  · rw [ggKGTc_symm_4]; exact h24
  · rw [ggKGTc_symm_5]; exact h05

theorem ggKGTc_hact_w_w0
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (hlong : ExcIsLongest TwistTag.E6.tag F.v) (hpq : p ∣ 2 ^ n + 1)
    {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ} (hb : ∀ j, b j ^ p = 1) :
    weylTuple F.v (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b := by
  rw [ggKGTc_eq_w0_E6 hlong, ggKGTc_weylTuple_w0_perm]
  funext k
  rw [Equiv.symm_apply_apply]
  exact ggKGTc_fr_inv_eq_self F.Fr F.fr_eq (hb k) hpq

theorem ggKGTwE6_centralizer_eq
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v))
    (x : twistedE6RootGroup K σ) :
    x ∈ Subgroup.centralizer (E : Set (twistedE6RootGroup K σ)) ↔
      F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * F.g0 ∈
        twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) := by
  let Y : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (MulAut.conj (F.g0⁻¹)).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6RootGroup K σ).subtype)
  have hYapp : ∀ y, Y y = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (y : ModGL TwistTag.E6.tag K) * F.g0 := fun y => rfl
  have hYinj : Function.Injective Y :=
    (MulAut.conj (F.g0⁻¹)).injective.comp
      ((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
        (Subgroup.subtype_injective _))
  constructor
  · intro hxcent
    rw [Subgroup.mem_centralizer_iff] at hxcent
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
    obtain ⟨ζu, hζu⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
      (by norm_num) hp (by omega)
    let ζ : AlgebraicClosure K := ζu
    have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.2 hζu
    have hxG : Y x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
      have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
        CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _
          (ggKGTc_coe_mem_adjointGroup x)
      rw [hYapp x]
      exact mul_mem (mul_mem (inv_mem F.g0_mem) hbc) F.g0_mem
    have hmem_of : ∀ {ι : Type} (a : ι → Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ),
        (∀ i, ∃ e ∈ E, rootDiagUnit TwistTag.E6.tag (a i) = Y e) →
        Y x ∈ familyCentralizer TwistTag.E6.tag (AlgebraicClosure K) a := by
      intro ι a hroot
      rw [mem_familyCentralizer]
      refine ⟨hxG, fun i => ?_⟩
      obtain ⟨e, heE, heq⟩ := hroot i
      have hxe : e * x = x * e := hxcent e heE
      have hcomm : Y e * Y x = Y x * Y e := by
        calc Y e * Y x = Y (e * x) := (map_mul Y e x).symm
          _ = Y (x * e) := by rw [hxe]
          _ = Y x * Y e := map_mul Y x e
      rw [heq, hcomm]
      group
    have hT : Y x ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
      rcases hv with ⟨hpq, hvn⟩ | ⟨hpq, hlong⟩
      · let a : {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ //
            (∀ j, b j ^ p = 1) ∧
              b (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨5, by decide⟩ ∧
              b (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨4, by decide⟩} →
            Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ := Subtype.val
        have hall : ∀ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
            (∀ j, b j ^ p = 1) →
            b (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨5, by decide⟩ →
            b (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨4, by decide⟩ →
            ∃ i, a i = b := by
          intro b hb h05 h24
          exact ⟨⟨b, hb, h05, h24⟩, rfl⟩
        have hker : familyKernel a = ∅ := ggKGExc_familyKernel_phi (ζ := ζ) hp hp5 hζ a hall
        have hstab : familyStabilizer a = {1} :=
          ggKGExc_familyStabilizer_phi (ζ := ζ) hp hp5 hζ a hall
        exact ggKGEx_familyCentralizer_le_torus a hker hstab
          (hmem_of a fun i => ggKGTc_exists_conj_of_hact hK hσ hp hp5 F i.property.1
            (ggKGTc_hact_w_one F hvn hpq i.property.1 i.property.2.1 i.property.2.2))
      · let a : {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ //
            ∀ j, b j ^ p = 1} → Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ := Subtype.val
        have hall : ∀ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
            (∀ j, b j ^ p = 1) → ∃ i, a i = b := fun b hb => ⟨⟨b, hb⟩, rfl⟩
        have hker : familyKernel a = ∅ := ggKGExc_familyKernel_allPTorsion hp (by omega) hζ a hall
        have hstab : familyStabilizer a = {1} :=
          ggKGExc_familyStabilizer_allPTorsion (Or.inl rfl) hp (by omega) hζ a hall
        exact ggKGEx_familyCentralizer_le_torus a hker hstab
          (hmem_of a fun i => ggKGTc_exists_conj_of_hact hK hσ hp hp5 F i.property
            (ggKGTc_hact_w_w0 F hlong hpq i.property))
    have hbx : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) :=
      ggKGTc_twistHom_baseChange_eq_self F hσ x
    have hFix : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v *
        twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr (Y x) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ = Y x := by
      rw [hYapp x]
      rw [show twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
            (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * F.g0) =
          (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0)⁻¹ *
            twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
              (baseChangeGL (algebraMap K (AlgebraicClosure K))
                (x : ModGL TwistTag.E6.tag K)) *
            twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0 by
          rw [map_mul, map_mul, map_inv]]
      rw [F.lang, hbx]
      group
    exact mem_twistedTorusOf.2 ⟨hT, hFix⟩
  · intro hx e he
    have hYe : Y e ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag)
        (AlgebraicClosure K) F.v) (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) :=
      ((F.mem_iff e).1 he).2
    have hcomm : Y e * Y x = Y x * Y e := by
      have h1 : Y e ∈ diagonalGroup :=
        torusGroup_le_diagonalGroup (mem_twistedTorusOf.1 hYe).1
      have h2 : Y x ∈ diagonalGroup :=
        torusGroup_le_diagonalGroup (mem_twistedTorusOf.1 hx).1
      exact mul_comm_of_mem_diagonalGroup h1 h2
    apply hYinj
    rw [map_mul, map_mul, hcomm]

end AtFrame

end CFSG.StandardType
