module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.Blueprint CFSG.RankThree.Chevalley.EvenF4QPlus

theorem ggKGTn_conj_y_apply
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (a e : twistedE6RootGroup K σ) :
    (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (a : ModGL TwistTag.E6.tag K) * F.g0) *
      (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e : ModGL TwistTag.E6.tag K) * F.g0) *
      (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (a : ModGL TwistTag.E6.tag K) * F.g0)⁻¹ =
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a * e * a⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 := by
  have hcoe : ((a * e * a⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (a : ModGL TwistTag.E6.tag K) * (e : ModGL TwistTag.E6.tag K) *
        (a : ModGL TwistTag.E6.tag K)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe, map_mul, map_mul, map_inv]
  group

theorem ggKGTn_conj_y_inv_apply
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (a e : twistedE6RootGroup K σ) :
    (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (a : ModGL TwistTag.E6.tag K) * F.g0)⁻¹ *
      (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e : ModGL TwistTag.E6.tag K) * F.g0) *
      (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (a : ModGL TwistTag.E6.tag K) * F.g0) =
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a⁻¹ * e * a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 := by
  have hcoe : ((a⁻¹ * e * a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (a : ModGL TwistTag.E6.tag K)⁻¹ * (e : ModGL TwistTag.E6.tag K) *
        (a : ModGL TwistTag.E6.tag K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe, map_mul, map_mul, map_inv]
  group

theorem ggKGTn_eq_one_of_canonicalRep_mem_torusGroup
    {L : Type} [Field L] {w : WeylGroup TwistTag.E6.tag}
    (h : canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∈ torusGroup TwistTag.E6.tag L) :
    w = 1 :=
  ((mapsRootLines_of_mem_torusGroup h).unique (mapsRootLines_canonicalRep w)).symm

theorem ggKGTn_w0_smul
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    ggKGTc_w0 (TwistTag.E6.tag) • v = -permLattice TwistTag.E6.perm v := by
  have hdecomp : v = ∑ i, v i • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hdecomp, Finset.smul_sum]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, permLattice,
    Function.comp_apply]
  rw [Finset.sum_eq_single (TwistTag.E6.perm.symm j)]
  · rw
    [smul_comm, ggKGTc_w0_smul_E6, Pi.smul_apply, Pi.neg_apply, Equiv.apply_symm_apply,
    Pi.single_eq_same]
    ring
  · intro i _ hi
    rw [smul_comm, ggKGTc_w0_smul_E6, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_of_ne]
    · ring
    · intro h
      exact hi (by rw [h, Equiv.symm_apply_apply TwistTag.E6.perm i])
  · intro hj
    simp at hj

theorem ggKGTn_w0_conj_eq_weylTwist
    (u : WeylGroup TwistTag.E6.tag) :
    ggKGTc_w0 (TwistTag.E6.tag) * u * (ggKGTc_w0 (TwistTag.E6.tag))⁻¹ =
      weylTwist TwistTag.E6 u := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.E6.tag.rank → ℤ) fun v => ?_
  rw [mul_smul, mul_smul, ggKGTc_w0_inv_E6, weylTwist_smul, ggKGTn_w0_smul]
  rw [show TwistTag.E6.perm.symm = TwistTag.E6.perm from by
    ext i; fin_cases i <;> rfl]
  rw [ggKGTn_w0_smul]
  have hneg : ∀ x : Fin TwistTag.E6.tag.rank → ℤ,
      permLattice TwistTag.E6.perm (-x) = -(permLattice TwistTag.E6.perm x) := fun x => rfl
  simp only [smul_neg, hneg, neg_neg]

theorem ggKGTn_normalizer_weyl
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v))
    {x : twistedE6RootGroup K σ}
    (hx : x ∈ Subgroup.normalizer (E : Set (twistedE6RootGroup K σ))) :
    ∃ u : WeylGroup TwistTag.E6.tag,
      (p ∣ 2 ^ n - 1 → ∀ w₀ : WeylGroup TwistTag.E6.tag, ExcIsLongest TwistTag.E6.tag w₀ →
        u * w₀ = w₀ * u) ∧
      ∀ e ∈ E,
        F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x * e * x⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
            (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ := by
  classical
  let L := AlgebraicClosure K
  let nv : ModGL TwistTag.E6.tag L :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) L F.v
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  let y : ModGL TwistTag.E6.tag L :=
    F.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * F.g0
  let V : Set (ModGL TwistTag.E6.tag L) :=
    {z | ∃ e ∈ E, z = F.g0⁻¹ * baseChangeGL (algebraMap K L)
      (e : ModGL TwistTag.E6.tag K) * F.g0}
  have hVH : V ⊆ torusGroup TwistTag.E6.tag L := by
    rintro z ⟨e, he, rfl⟩
    exact (mem_twistedTorusOf.1 ((F.mem_iff e).1 he).2).1
  have hCV : adjointGroup TwistTag.E6.tag L ⊓ Subgroup.centralizer V =
      torusGroup TwistTag.E6.tag L :=
    ggKGTn_adjoint_inf_centralizer_eq hK hσ hp hp5 F hv
  have hg_mem : y ∈ adjointGroup TwistTag.E6.tag L ⊓ Subgroup.normalizer V := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem F.g0_mem)
        (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L)
          (ggKGTc_coe_mem_adjointGroup x))) F.g0_mem
    · rw [Subgroup.mem_set_normalizer_iff]
      intro z
      constructor
      · intro hz
        obtain ⟨e, he, rfl⟩ := hz
        refine ⟨x * e * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx e).1 he, ?_⟩
        exact ggKGTn_conj_y_apply F x e
      · intro hz
        obtain ⟨e, he, heq⟩ := hz
        have hxinv : x⁻¹ ∈ Subgroup.normalizer (E : Set (twistedE6RootGroup K σ)) :=
          Subgroup.inv_mem _ hx
        refine ⟨x⁻¹ * e * x, (Subgroup.mem_normalizer_iff.1 hxinv e).1 he, ?_⟩
        have hz_eq : z = y⁻¹ *
            (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) * y := by
          calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
            _ = y⁻¹ *
                (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0)
                  * y := by
                  rw [heq]
        rw [hz_eq]
        change (F.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * F.g0)⁻¹ *
            (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
            (F.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * F.g0) =
          F.g0⁻¹ * baseChangeGL (algebraMap K L)
            ((x⁻¹ * e * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0
        exact ggKGTn_conj_y_inv_apply F x e
  obtain ⟨h, hhT, u, hyv⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer hVH hCV hg_mem
  have hΦy : twistHom TwistTag.E6 L F.Fr y = nv⁻¹ * y * nv := by
    have hBx : twistHom TwistTag.E6 L F.Fr
        (baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K)) =
        baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) :=
      ggKGTc_twistHom_baseChange_eq_self F hσ x
    have hΦg : twistHom TwistTag.E6 L F.Fr F.g0 = F.g0 * nv := F.lang
    change twistHom TwistTag.E6 L F.Fr
      (F.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * F.g0) =
      nv⁻¹ * (F.g0⁻¹ * baseChangeGL (algebraMap K L)
        (x : ModGL TwistTag.E6.tag K) * F.g0) * nv
    rw [map_mul, map_mul, map_inv, hΦg, hBx]
    group
  have hstep : nv * twistHom TwistTag.E6 L F.Fr y * nv⁻¹ = y := by
    rw [hΦy]
    group
  have hstepH : nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹ ∈ torusGroup TwistTag.E6.tag L := by
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hΦnu : twistHom TwistTag.E6 L F.Fr
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (weylTwist TwistTag.E6 u) :=
    twistHom_canonicalRep TwistTag.E6 L F.Fr u
  have hconj : nv * twistHom TwistTag.E6 L F.Fr
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) * nv⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) := by
    rw [hΦnu]
    change canonicalRep (coxeterSystem TwistTag.E6.tag) L F.v *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L (weylTwist TwistTag.E6 u) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L F.v)⁻¹ = _
    rw [canonicalRep_inv_of_charTwo (M := L) F.v,
      ← canonicalRep_mul_of_charTwo (M := L) F.v (weylTwist TwistTag.E6 u),
      ← canonicalRep_mul_of_charTwo (M := L) (F.v * weylTwist TwistTag.E6 u) F.v⁻¹]
  have hstep_h : y = (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹) *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) := by
    calc y = nv * twistHom TwistTag.E6 L F.Fr y * nv⁻¹ := hstep.symm
      _ = nv * twistHom TwistTag.E6 L F.Fr
            (h * canonicalRep (coxeterSystem TwistTag.E6.tag) L u) * nv⁻¹ := by rw [hyv]
      _ = nv * (twistHom TwistTag.E6 L F.Fr h *
            twistHom TwistTag.E6 L F.Fr (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)) *
            nv⁻¹ := by rw [map_mul]
      _ = (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹) *
          (nv * twistHom TwistTag.E6 L F.Fr
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) * nv⁻¹) := by group
      _ = (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L
            (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) := by rw [hconj]
  have hHcanon : canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((F.v * weylTwist TwistTag.E6 u * F.v⁻¹) * u⁻¹) ∈ torusGroup TwistTag.E6.tag L := by
    have hh_eq : h * canonicalRep (coxeterSystem TwistTag.E6.tag) L u =
        (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L
            (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) :=
      hyv.symm.trans hstep_h
    have hHn' : canonicalRep (coxeterSystem TwistTag.E6.tag) L
        (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ ∈ torusGroup TwistTag.E6.tag L := by
      have hcalc : (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹)⁻¹ * h =
          canonicalRep (coxeterSystem TwistTag.E6.tag) L
            (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by
        calc (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹)⁻¹ * h
            = (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹)⁻¹ * h *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
                  (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹) := by group
          _ = (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹)⁻¹ *
                (h * canonicalRep (coxeterSystem TwistTag.E6.tag) L u) *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by group
          _ = (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹)⁻¹ *
                ((nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹) *
                  canonicalRep (coxeterSystem TwistTag.E6.tag) L
                    (F.v * weylTwist TwistTag.E6 u * F.v⁻¹)) *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by rw [hh_eq]
          _ = canonicalRep (coxeterSystem TwistTag.E6.tag) L
                (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by group
      have hmem : (nv * twistHom TwistTag.E6 L F.Fr h * nv⁻¹)⁻¹ * h ∈
          torusGroup TwistTag.E6.tag L :=
        mul_mem (inv_mem hstepH) hhT
      rw [hcalc] at hmem
      exact hmem
    have hrew : canonicalRep (coxeterSystem TwistTag.E6.tag) L
        ((F.v * weylTwist TwistTag.E6 u * F.v⁻¹) * u⁻¹) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) L
          (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by
      rw [canonicalRep_mul_of_charTwo (M := L) (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) u⁻¹,
        canonicalRep_inv_of_charTwo (M := L) u]
    rw [hrew]
    exact hHn'
  have hwu : (F.v * weylTwist TwistTag.E6 u * F.v⁻¹) * u⁻¹ = 1 :=
    ggKGTn_eq_one_of_canonicalRep_mem_torusGroup hHcanon
  have hcomm : F.v * weylTwist TwistTag.E6 u * F.v⁻¹ = u := by
    have := congrArg (fun z => z * u) hwu
    simpa [mul_assoc] using this
  refine ⟨u, ?_, ?_⟩
  · intro hpq w₀ hw₀
    have hvn : F.v = 1 := by
      rcases hv with ⟨_, hvn⟩ | ⟨hpq', _⟩
      · exact hvn
      · exfalso
        have h2 : p ∣ 2 := by
          have h := Nat.dvd_sub hpq' hpq
          rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 from by
            have := Nat.one_le_two_pow (n := n); omega] at h
        have hp2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
        omega
    have hwu : weylTwist TwistTag.E6 u = u := by
      have h := hcomm
      rw [hvn, one_mul, inv_one, mul_one] at h
      exact h
    have hw0 : w₀ = ggKGTc_w0 (TwistTag.E6.tag) := ggKGTc_eq_w0_E6 hw₀
    have hconj := ggKGTn_w0_conj_eq_weylTwist u
    rw [hwu] at hconj
    have hcomm' : ggKGTc_w0 (TwistTag.E6.tag) * u = u * ggKGTc_w0 (TwistTag.E6.tag) := by
      have h := congrArg (fun z => z * ggKGTc_w0 (TwistTag.E6.tag)) hconj
      simpa [mul_assoc] using h
    rw [hw0]
    exact hcomm'.symm
  · intro e he
    have hconj_e : y *
        (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) * y⁻¹ =
        F.g0⁻¹ * baseChangeGL (algebraMap K L)
          ((x * e * x⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 :=
      ggKGTn_conj_y_apply F x e
    have hyeH : F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0 ∈
        torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 ((F.mem_iff e).1 he).2).1
    have hnvH : canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
        (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ ∈ torusGroup TwistTag.E6.tag L :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) u) _).1 hyeH
    have hcentral : y *
        (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) * y⁻¹ =
        canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
          (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by
      calc y * (F.g0⁻¹ * baseChangeGL (algebraMap K L)
              (e : ModGL TwistTag.E6.tag K) * F.g0) * y⁻¹
          = (h * canonicalRep (coxeterSystem TwistTag.E6.tag) L u) *
              (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
              (h * canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by rw [hyv]
        _ = h * (canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
              (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹) * h⁻¹ := by group
        _ = (canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
              (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹) * h * h⁻¹ := by
            rw [mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hhT)
              (torusGroup_le_diagonalGroup hnvH)]
        _ = canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
              (F.g0⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL TwistTag.E6.tag K) * F.g0) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ := by group
    exact hconj_e.symm.trans hcentral

theorem ggKGTn_normalizer_faithful
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v))
    {u : WeylGroup TwistTag.E6.tag}
    (hu : ∀ e ∈ E,
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
          (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ =
      F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) :
    u = 1 := by
  classical
  let L := AlgebraicClosure K
  obtain ⟨ι, a, hstab, hker, hroot⟩ := ggKGTn_family_data hK hσ hp hp5 F hv
  have hu_stab : u ∈ familyStabilizer a := by
    refine fun i => ?_
    show ∀ v : Fin TwistTag.E6.tag.rank → ℤ, rootChar (a i) (u • v) = rootChar (a i) v
    intro v
    obtain ⟨e, he, heq⟩ := hroot i
    have hfix : canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
        rootDiagUnit TwistTag.E6.tag (a i) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ =
        rootDiagUnit TwistTag.E6.tag (a i) := by
      rw [heq]
      exact hu e he
    have htuple : weylTuple u (a i) = a i := by
      apply rootDiagUnit_injective
      rw [← canonicalRep_conj_rootDiagUnit]
      exact hfix
    have h := congrArg (fun t => rootChar t (u • v)) htuple
    rw [rootChar_weylTuple, inv_smul_smul] at h
    exact h.symm
  have : u ∈ ({1} : Set (WeylGroup TwistTag.E6.tag)) := hstab ▸ hu_stab
  simpa using this

end CFSG.StandardType

end
