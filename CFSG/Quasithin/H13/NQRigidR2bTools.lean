module

public import CFSG.Quasithin.H13.NQRigidSp4Graph
public import CFSG.Quasithin.H13.NQSetupPlaneAction
public import CFSG.Quasithin.SteinbergCCLocalSylowAction
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spSemilinearAutGroup)
open scoped Pointwise IsMulCommutative

theorem exists_centerPreimage_central {H : Type*} [Group H] [Finite H] (K : Subgroup H)
    (hK : K.Normal) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ∃ (N : Subgroup K) (_ : N.Characteristic), ¬ p ∣ Nat.card N ∧
      (∀ x : K, x ∈ N ↔ QuotientGroup.mk' (CFSG.pCore 2 K) x ∈ center (K ⧸ CFSG.pCore 2 K)) ∧
      ∃ ι : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* K ⧸ N,
        ∀ (h : H) (x : (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)),
          ι (cpuSAut K hK h x) =
            CFSG.SectionRank.Ccomm.autQuotient N (@MulAut.conjNormal H _ K hK h) (ι x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := CFSG.pCore 2 K with hM
  set Z := center (K ⧸ M) with hZdef
  set N : Subgroup K := Z.comap (QuotientGroup.mk' M) with hNdef
  have hMN : M ≤ N := fun x hx => by
    have h1 : QuotientGroup.mk' M x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hNdef, mem_comap, h1]
    exact one_mem Z
  have hNc : N.Characteristic := by
    refine characteristic_iff_le_comap.mpr fun φ x hx => ?_
    change QuotientGroup.mk' M (φ x) ∈ Z
    have h1 : QuotientGroup.mk' M (φ x) =
        CFSG.SectionRank.Ccomm.autQuotient M φ (QuotientGroup.mk' M x) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, CFSG.SectionRank.Ccomm.autQuotient_mk]
    rw [h1]
    exact (characteristic_iff_le_comap.mp (inferInstance : Z.Characteristic) _) hx
  have hNp : ¬ p ∣ Nat.card N := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    set z : Z := ⟨QuotientGroup.mk' M (x : K), x.2⟩ with hz
    have hzp : z ^ p = 1 := Subtype.ext (show QuotientGroup.mk' M (x : K) ^ p = 1 by
      rw [← map_pow, ← SubgroupClass.coe_pow, hxp, OneMemClass.coe_one, map_one])
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hzp) with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      have hxM : (x : K) ∈ M := by
        have h2 : QuotientGroup.mk' M (x : K) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup) (⟨x, hxM⟩ : M)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at hk
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ k by rw [hk])
      have := Nat.le_of_dvd (by norm_num) h2
      have h3 := hp.two_le
      omega
    · exact hZ (h1 ▸ orderOf_dvd_natCard z)
  have hmap : N.map (QuotientGroup.mk' M) = Z :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) Z
  refine ⟨N, hNc, hNp, fun x => Iff.rfl, (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient M N hMN), fun h x => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : cpuSAut K hK h (((y : K ⧸ M) : (K ⧸ M) ⧸ Z)) =
      (((@MulAut.conjNormal H _ K hK h y : K) : K ⧸ M) : (K ⧸ M) ⧸ Z) := by
    unfold cpuSAut
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, CFSG.SectionRank.Ccomm.autQuotient_mk,
      CFSG.SectionRank.Ccomm.autQuotient_mk]
  rw [h1]
  change ((@MulAut.conjNormal H _ K hK h y : K) : K ⧸ N) =
    CFSG.SectionRank.Ccomm.autQuotient N (@MulAut.conjNormal H _ K hK h) ((y : K) : K ⧸ N)
  rw [CFSG.SectionRank.Ccomm.autQuotient_mk]

theorem exists_centerPreimage_compat {H : Type*} [Group H] [Finite H] (K : Subgroup H)
    (hK : K.Normal) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ∃ (N : Subgroup K) (_ : N.Characteristic), ¬ p ∣ Nat.card N ∧
      ∃ ι : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* K ⧸ N,
        ∀ (h : H) (x : (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)),
          ι (cpuSAut K hK h x) =
            CFSG.SectionRank.Ccomm.autQuotient N (@MulAut.conjNormal H _ K hK h) (ι x) := by
  obtain ⟨N, hNc, hNp, -, ι, hι⟩ := exists_centerPreimage_central K hK hp hp2 hZ
  exact ⟨N, hNc, hNp, ι, hι⟩

variable {H : Type*} [Group H] [Finite H]

theorem normalizerFrattiniConj_eq_pow {p : ℕ} [Fact p.Prime] {X P : Subgroup H}
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hP : IsSylowOf p P X)
    (n : normalizer (X : Set H)) (m : ℕ)
    (hm : ∀ x ∈ P, (n : H) * x * (n : H)⁻¹ = x ^ m) :
    ∀ w, normalizerFrattiniConj X n w = w ^ m := by
  classical
  obtain ⟨hPX, -, hPmax⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hsurj : ∀ z : X ⧸ CFSG.pCore 2 X, ∃ x ∈ P, ∃ hx : x ∈ X,
      ((⟨x, hx⟩ : X) : X ⧸ CFSG.pCore 2 X) = z := by
    set Pbar : Subgroup (X ⧸ CFSG.pCore 2 X) :=
      (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) with hPbar
    have hPbar_top : Pbar = ⊤ := by
      have hdvd : Pbar.index ∣ P.relIndex X :=
        index_map_dvd (P.subgroupOf X) (QuotientGroup.mk'_surjective _)
      obtain ⟨j, hj⟩ := hXA.index Pbar
      rcases j with _ | j
      · rw [pow_zero] at hj
        exact index_eq_one.mp hj
      · exfalso
        apply hPmax
        rw [hj] at hdvd
        exact (dvd_pow_self p (Nat.succ_ne_zero j)).trans hdvd
    intro z
    have hz : z ∈ Pbar := hPbar_top ▸ mem_top z
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨(y : H), mem_subgroupOf.mp hy, y.2, rfl⟩
  intro w
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, hxP, hxX, rfl⟩ := hsurj z
  have h1 : (X.normalizerMonoidHom n ⟨x, hxX⟩ : X) = ⟨x, hxX⟩ ^ m := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact hm x hxP
  calc normalizerFrattiniConj X n (((⟨x, hxX⟩ : X) : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
      (((X.normalizerMonoidHom n ⟨x, hxX⟩ : X) : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := rfl
    _ = _ := by rw [h1]; rfl

theorem sq_eq_one_of_pow_of_det_eq_one {p : ℕ} [Fact p.Prime] {W : Type*} [Group W] [Finite W]
    [CFSG.IsElementaryAbelian p W] (hW : Nat.card W = p ^ 2) (γ : MulAut W) (m : ℕ)
    (hm : ∀ w, γ w = w ^ m)
    (hdet : LinearEquiv.det (NQSetup.mulAutLinear p W γ) = 1) : γ * γ = 1 := by
  classical
  have hdim : Module.finrank (ZMod p) (Additive W) = 2 := NQSetup.finrank_additive_eq_two hW
  have hlin : (NQSetup.mulAutLinear p W γ : Additive W →ₗ[ZMod p] Additive W) =
      (m : ZMod p) • LinearMap.id := by
    ext x
    rw [LinearEquiv.coe_coe, NQSetup.mulAutLinear_apply, hm, LinearMap.smul_apply,
      LinearMap.id_apply, ofMul_pow, Nat.cast_smul_eq_nsmul]
    rfl
  have hdet' : LinearMap.det (NQSetup.mulAutLinear p W γ : Additive W →ₗ[ZMod p] Additive W) =
      1 := by
    have h := congrArg Units.val hdet
    rw [LinearEquiv.coe_det, Units.val_one] at h
    exact h
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one, hdim] at hdet'
  have hexp : ∀ w : W, w ^ p = 1 := fun w => by
    have := CFSG.IsElementaryAbelian.exponent_dvd_p (p := p) (G := W)
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp this w
  have hmod : (m * m) % p = 1 % p := by
    have h1 : ((m * m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      rw [← sq]
      exact hdet'
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  ext w
  rw [MulAut.mul_apply, hm, hm, MulAut.one_apply, ← pow_mul]
  rw [← Nat.mod_add_div (m * m) p, pow_add, pow_mul, hexp, one_pow, mul_one, hmod]
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Nat.mod_eq_of_lt hp1, pow_one]

omit [Finite H] in
theorem det_normalizerFrattiniConj_eq_one {p : ℕ} [Fact p.Prime] {X L : Subgroup H}
    [CFSG.IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))]
    (hLN : L ≤ normalizer (X : Set H)) (hL : Group.IsPerfect L) (l : H) (hl : l ∈ L) :
    LinearEquiv.det (NQSetup.mulAutLinear p _ (normalizerFrattiniConj X ⟨l, hLN hl⟩)) = 1 := by
  set χ : L →* (ZMod p)ˣ := LinearEquiv.det.comp ((NQSetup.mulAutLinear p _).comp
    ((normalizerFrattiniConj X).comp (inclusion hLN))) with hχ
  have hperf : commutator L ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : commutator L = ⊤ := hL.commutator_eq_top
  have h1 : (⟨l, hl⟩ : L) ∈ χ.ker := hperf (htop ▸ mem_top _)
  exact h1

end CFSG.Quasithin.H13.NQRigid
