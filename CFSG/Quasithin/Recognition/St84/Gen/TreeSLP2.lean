module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAP2
public import CFSG.Quasithin.Recognition.St84.Gen.OTwoResL2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLieL2
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.Quasithin.Recognition.St84.L2Group
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.AppTreeSAB
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXA

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GorensteinWalter
  CFSG.ASVolI CFSG.Quasithin.H13.P31X
open scoped Pointwise MatrixGroups

variable {H : Type} [Group H] [Finite H]

private theorem f112sl_diag_mem_upperUnipotent_iff {n : ℕ}
    (l : (GaloisField 2 n)ˣ) :
    psl2QuotientMap (GaloisField 2 n) (burnsideAut_sl2DiagHom (GaloisField 2 n) l) ∈
        psl2UpperUnipotentSubgroup (GaloisField 2 n) ↔ l = 1 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ :=
      (mem_psl2UpperUnipotentSubgroup_iff
        (psl2QuotientMap (GaloisField 2 n)
          (burnsideAut_sl2DiagHom (GaloisField 2 n) l))).1 h
    have hker : (burnsideAut_sl2DiagHom (GaloisField 2 n) l)⁻¹ * sl2UpperUnipotent y ∈
        Subgroup.center (SL(2, GaloisField 2 n)) := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (Subgroup.center (SL(2, GaloisField 2 n)))
        ((burnsideAut_sl2DiagHom (GaloisField 2 n) l)⁻¹ * sl2UpperUnipotent y) = 1
      rw [map_mul, map_inv]
      rw [show QuotientGroup.mk' (Subgroup.center (SL(2, GaloisField 2 n)))
            (burnsideAut_sl2DiagHom (GaloisField 2 n) l) =
          psl2QuotientMap (GaloisField 2 n)
            (burnsideAut_sl2DiagHom (GaloisField 2 n) l) from rfl,
        show QuotientGroup.mk' (Subgroup.center (SL(2, GaloisField 2 n)))
            (sl2UpperUnipotent y) =
          psl2QuotientMap (GaloisField 2 n) (sl2UpperUnipotent y) from rfl]
      rw [hy, inv_mul_cancel]
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo] at hker
    have h1 : (burnsideAut_sl2DiagHom (GaloisField 2 n) l)⁻¹ * sl2UpperUnipotent y = 1 := by
      simpa using hker
    have heq : burnsideAut_sl2DiagHom (GaloisField 2 n) l = sl2UpperUnipotent y := by
      calc burnsideAut_sl2DiagHom (GaloisField 2 n) l
          = (burnsideAut_sl2DiagHom (GaloisField 2 n) l) *
              ((burnsideAut_sl2DiagHom (GaloisField 2 n) l)⁻¹ * sl2UpperUnipotent y) := by
            rw [h1, mul_one]
        _ = sl2UpperUnipotent y := by group
    have h00 := congrArg (fun A : SL(2, GaloisField 2 n) =>
      (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 0) heq
    simp [burnsideAut_sl2DiagHom, sl2UpperUnipotent] at h00
    exact Units.ext h00
  · rintro rfl
    rw [show burnsideAut_sl2DiagHom (GaloisField 2 n) (1 : (GaloisField 2 n)ˣ) = 1 from
      map_one _]
    simp [psl2QuotientMap]

theorem f112sl_mulAut_eq_conj_of_mem_borel {n : ℕ} (hn : 2 ≤ n)
    (σ : MulAut (PSL2 (GaloisField 2 n))) (hσ2 : ∃ k, σ ^ 2 ^ k = 1)
    (hfix : ∀ x ∈ psl2Borel (GaloisField 2 n),
      σ x * x⁻¹ ∈ psl2UpperUnipotentSubgroup (GaloisField 2 n)) :
    ∃ u ∈ psl2UpperUnipotentSubgroup (GaloisField 2 n),
      σ = MulAut.conj u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 n
  let U : Subgroup (PSL2 K) := psl2UpperUnipotentSubgroup K
  let B : Subgroup (PSL2 K) := psl2Borel K
  have hUB : U ≤ B := psl2UpperUnipotent_le_borel (K := K)
  have hσU : U.map σ.toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hxB : x ∈ B := hUB hx
      have h := hfix x hxB
      have hx' : σ x = (σ x * x⁻¹) * x := by group
      have hmem : σ x ∈ U := by
        rw [hx']
        exact U.mul_mem h hx
      simpa using hmem
    · rw [Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
  haveI hInn : (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range.Normal :=
    burnsideAut_inn_normal (PSL2 K)
  obtain ⟨c, hc, f, hf, hcf⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (burnsideAut_psl2_aut_mem σ)
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc
  obtain ⟨τ, rfl⟩ := MonoidHom.mem_range.mp hf
  have hfU : U.map (psl2FieldAut K τ).toMonoidHom = U :=
    burnsideAut_map_psl2FieldAut_upper τ
  have hxU : U.map (MulAut.conj x).toMonoidHom = U := by
    calc U.map (MulAut.conj x).toMonoidHom
        = (U.map (psl2FieldAut K τ).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
          rw [hfU]
      _ = U.map ((MulAut.conj x).toMonoidHom.comp
            (psl2FieldAut K τ).toMonoidHom) := Subgroup.map_map _ _ _
      _ = U.map (MulAut.conj x * psl2FieldAut K τ).toMonoidHom := rfl
      _ = U := by rw [hcf]; exact hσU
  have hxB : x ∈ B := by
    change x ∈ psl2Borel K
    rw [← psl2UpperUnipotent_normalizer_eq_borel K]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxU
  have hfB : ∀ b ∈ B, psl2FieldAut K τ b ∈ B := by
    intro b hb
    have hmapB : B.map (psl2FieldAut K τ).toMonoidHom = B := by
      rw [show B = psl2Borel K from rfl, burnsideAut_psl2Borel_eq_sup, Subgroup.map_sup,
        burnsideAut_map_psl2FieldAut_upper τ, burnsideAut_map_psl2FieldAut_diag τ]
    rw [← hmapB]
    exact Subgroup.mem_map_of_mem _ hb
  have hfieldfix : ∀ b ∈ B, psl2FieldAut K τ b * b⁻¹ ∈ U := by
    intro b hb
    have hfb : psl2FieldAut K τ b ∈ B := hfB b hb
    have hcomm : x * psl2FieldAut K τ b * x⁻¹ * (psl2FieldAut K τ b)⁻¹ ∈ U :=
      l2_borel_comm hxB hfb
    have h := hfix b hb
    have hsig : σ b * b⁻¹ = (x * psl2FieldAut K τ b * x⁻¹) * b⁻¹ := by
      rw [← hcf]
      rfl
    rw [hsig] at h
    have hprod : psl2FieldAut K τ b * b⁻¹ =
        (x * psl2FieldAut K τ b * x⁻¹ * (psl2FieldAut K τ b)⁻¹)⁻¹ *
          ((x * psl2FieldAut K τ b * x⁻¹) * b⁻¹) := by
      group
    rw [hprod]
    exact U.mul_mem (U.inv_mem hcomm) h
  have hτ : τ = 1 := by
    ext a
    by_cases ha : a = 0
    · simp [ha]
    · let l : Kˣ := Units.mk0 a ha
      have hb : psl2QuotientMap K (burnsideAut_sl2DiagHom K l) ∈ B :=
        burnsideAut_psl2Diag_le_borel (K := K) (MonoidHom.mem_range.mpr ⟨l, rfl⟩)
      have h := hfieldfix _ hb
      have hdiag : psl2FieldAut K τ
            (psl2QuotientMap K (burnsideAut_sl2DiagHom K l)) =
          psl2QuotientMap K (burnsideAut_sl2DiagHom K (Units.map (τ : K →* K) l)) :=
        burnsideAut_psl2FieldAut_diag τ l
      rw [hdiag] at h
      have hμ : psl2QuotientMap K
          (burnsideAut_sl2DiagHom K (Units.map (τ : K →* K) l * l⁻¹)) ∈ U := by
        rw [map_mul (burnsideAut_sl2DiagHom K), map_mul (psl2QuotientMap K),
          map_inv (burnsideAut_sl2DiagHom K), map_inv (psl2QuotientMap K)]
        exact h
      have hμ1 : Units.map (τ : K →* K) l * l⁻¹ = 1 :=
        (f112sl_diag_mem_upperUnipotent_iff (Units.map (τ : K →* K) l * l⁻¹)).1 hμ
      have hval : (Units.map (τ : K →* K) l : K) = (l : K) := by
        have h1 : Units.map (τ : K →* K) l = l := by
          calc Units.map (τ : K →* K) l = (Units.map (τ : K →* K) l * l⁻¹) * l := by group
            _ = 1 * l := by rw [hμ1]
            _ = l := one_mul l
        rw [h1]
      simpa [l, Units.coe_map, Units.val_mk0] using hval
  have hσ_eq : σ = MulAut.conj x := by
    rw [← hcf, hτ, map_one, mul_one]
  have hxpow : ∃ k, x ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hσ2
    refine ⟨k, ?_⟩
    have h2 : (MulAut.conj x) ^ 2 ^ k = 1 := by rw [← hσ_eq]; exact hk
    exact burnsideAut_conj_injective (S := PSL2 (GaloisField 2 n))
      (psl2_center_eq_bot) (by simpa [map_pow] using h2)
  have hxU' : x ∈ U := by
    by_contra hxnot
    haveI hUN : (U.subgroupOf B).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (le_of_eq (psl2UpperUnipotent_normalizer_eq_borel K).symm)
    let πB : ↥B →* ↥B ⧸ (U.subgroupOf B) := QuotientGroup.mk' _
    let b : ↥B := ⟨x, hxB⟩
    have hπne : πB b ≠ 1 := by
      intro h
      apply hxnot
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff b).mp h)
    obtain ⟨m, hm⟩ := hxpow
    have hpow : (πB b) ^ 2 ^ m = 1 := by
      have hbpow : b ^ 2 ^ m = 1 := by
        apply Subtype.ext
        exact hm
      rw [← map_pow, hbpow, map_one]
    have hdvd1 : orderOf (πB b) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
    have hdvd2 : orderOf (πB b) ∣ (U.subgroupOf B).index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hKcard : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
    have hidx : (U.subgroupOf B).index = 2 ^ n - 1 := by
      have hmul := Subgroup.card_mul_index (U.subgroupOf B)
      have hcardU : Nat.card (U.subgroupOf B) = 2 ^ n := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv,
          psl2UpperUnipotentSubgroup_card K, hKcard]
      have hcardB : Nat.card B = 2 ^ n * (2 ^ n - 1) := by
        rw [show B = psl2Borel K from rfl, l2_psl2Borel_card K, hKcard]
      rw [hcardU, hcardB] at hmul
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n) hmul
    have hodd : Odd (U.subgroupOf B).index := by
      rw [hidx]
      have heven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd (Nat.two_pow_pos n) heven odd_one
    have hcop : Nat.gcd (2 ^ m) (U.subgroupOf B).index = 1 := by
      have h2 : Nat.Coprime 2 (U.subgroupOf B).index := hodd.coprime_two_left
      exact h2.pow_left m
    have hdvd : orderOf (πB b) ∣ Nat.gcd (2 ^ m) (U.subgroupOf B).index :=
      Nat.dvd_gcd hdvd1 hdvd2
    have hone : orderOf (πB b) = 1 := by
      rw [hcop] at hdvd
      exact Nat.dvd_one.mp hdvd
    exact hπne (orderOf_eq_one_iff.mp hone)
  exact ⟨x, hxU', hσ_eq⟩

theorem f112sl_P2_le_normalizer {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) :
    f112P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
  sup_le Subgroup.le_normalizer (f112sa_bigB_le_normalizer_L2 hF.toW)

theorem f112sl_conjModPCore_ker_le_pCore {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) {n : ℕ}
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (CFSG.GroupTheory.conjModPCore 2 L2 (f112P2 L1 L2 S)
      (f112sl_P2_le_normalizer hF)).ker ≤
      CFSG.pCore 2 ↥(f112P2 L1 L2 S) := by
  classical
  let P := f112P2 L1 L2 S
  let ρ : ↥P →* MulAut (↥L2 ⧸ CFSG.pCore 2 ↥L2) :=
    CFSG.GroupTheory.conjModPCore 2 L2 P (f112sl_P2_le_normalizer hF)
  change ρ.ker ≤ CFSG.pCore 2 ↥P
  refine CFSG.LieType.BorelTits.le_pCore (r := 2) (MonoidHom.normal_ker ρ) ?_
  refine CFSG.Quasithin.St84.isPGroup_two_of_odd_eq_one ?_
  intro c hc
  have hcrho : CFSG.GroupTheory.conjModPCore 2 L2 P (f112sl_P2_le_normalizer hF)
      (c : ↥P) = 1 := by
    have h := MonoidHom.mem_ker.mp c.2
    simpa [ρ] using h
  have hcoddP : Odd (orderOf (c : ↥P)) := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hcoddH : Odd (orderOf ((c : ↥P) : H)) := by
    rw [Subgroup.orderOf_coe]
    exact hcoddP
  have hcL : ((c : ↥P) : H) ∈ L2 :=
    f112sa_mem_L2_of_odd hF h1 (c : ↥P).2 hcoddH
  let q : ↥L2 →* ↥L2 ⧸ CFSG.pCore 2 ↥L2 := QuotientGroup.mk' _
  let x : ↥L2 ⧸ CFSG.pCore 2 ↥L2 := q ⟨((c : ↥P) : H), hcL⟩
  have hxcenter : x ∈ Subgroup.center (↥L2 ⧸ CFSG.pCore 2 ↥L2) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hfix : x * q z * x⁻¹ = q z := by
      have hconj : x * q z * x⁻¹ =
          q ⟨((c : ↥P) : H) * (z : H) * (((c : ↥P) : H))⁻¹, by
            exact (Subgroup.mem_normalizer_iff.mp
              (Subgroup.le_normalizer hcL) (z : H)).mp z.2⟩ := by
        rw [show x = q ⟨((c : ↥P) : H), hcL⟩ from rfl]
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
      have hρz : q ⟨((c : ↥P) : H) * (z : H) * (((c : ↥P) : H))⁻¹, by
            exact (Subgroup.mem_normalizer_iff.mp
              (Subgroup.le_normalizer hcL) (z : H)).mp z.2⟩ =
          q z := by
        have h := congrArg (fun φ : MulAut (↥L2 ⧸ CFSG.pCore 2 ↥L2) =>
          φ (QuotientGroup.mk z)) hcrho
        rw [CFSG.GroupTheory.conjModPCore_mk] at h
        simpa [q] using h
      rw [hconj, hρz]
    change q z * x = x * q z
    calc q z * x = (x * q z * x⁻¹) * x := by rw [hfix]
      _ = x * q z := by group
  have hx1 : x = 1 := by
    obtain ⟨e0⟩ := show Nonempty (↥L2 ⧸ CFSG.pCore 2 ↥L2 ≃* PSL2 (GaloisField 2 n)) from h2
    have hcen : e0 x ∈ Subgroup.center (PSL2 (GaloisField 2 n)) := by
      rw [Subgroup.mem_center_iff] at hxcenter ⊢
      intro g
      obtain ⟨y, rfl⟩ := e0.surjective g
      simpa using congrArg e0 (hxcenter y)
    rw [CFSG.Quasithin.St84.psl2_center_eq_bot] at hcen
    have h1 : e0 x = 1 := by simpa using hcen
    exact e0.injective (by rw [h1, map_one])
  have hcmem : (⟨((c : ↥P) : H), hcL⟩ : ↥L2) ∈ CFSG.pCore 2 ↥L2 := by
    rw [← QuotientGroup.eq_one_iff]
    exact hx1
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥L2) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥L2)
  obtain ⟨k, hk⟩ := hp ⟨⟨((c : ↥P) : H), hcL⟩, hcmem⟩
  have hdvd : orderOf ((c : ↥P) : H) ∣ 2 ^ k := by
    have hord : orderOf (⟨⟨((c : ↥P) : H), hcL⟩, hcmem⟩ : ↥(CFSG.pCore 2 ↥L2)) =
        orderOf ((c : ↥P) : H) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf ((c : ↥P) : H)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hcoddH)
  have hone : ((c : ↥P) : H) = 1 := by
    have h1 : orderOf ((c : ↥P) : H) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    rwa [orderOf_eq_one_iff] at h1
  exact Subtype.ext (Subtype.ext hone)

theorem f112sl_mem_sup_of_normalized {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) {n : ℕ} (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) {R : Subgroup H} (hR : IsPGroup 2 R)
    (hRB : R ≤ bigB L1 L2 S)
    (hXR : oTwoRes L2 ⊓ bigB L1 L2 S ≤ Subgroup.normalizer (R : Set H))
    {t : H} (ht : t ∈ R) :
    t ∈ oTwoRes L2 ⊔ pCoreOf 2 (f112P2 L1 L2 S) := by
  classical
  let M := oTwoRes L2
  let B := bigB L1 L2 S
  let P := f112P2 L1 L2 S
  let Q := pCoreOf 2 L2
  let K := GaloisField 2 n
  let Qbar := ↥L2 ⧸ CFSG.pCore 2 ↥L2
  let q : ↥L2 →* Qbar := QuotientGroup.mk' (CFSG.pCore 2 ↥L2)
  let S2 : Subgroup H := S ⊓ L2
  let B2 : Subgroup H := borelOf L2 S
  let V : Subgroup H := f112saP2_V L2 S
  let X2 : Subgroup H := M ⊓ B
  let T : Subgroup Qbar := (S2.subgroupOf L2).map q
  let ρ : ↥P →* MulAut Qbar :=
    CFSG.GroupTheory.conjModPCore 2 L2 P (f112sl_P2_le_normalizer hF)
  have hR1 : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hBP : B ≤ P := f112saP2_bigB_le_P2 hF h1
  have htB : t ∈ B := hRB ht
  have htP : t ∈ P := hBP htB
  have hMsup : Q ⊔ M = L2 := by
    rw [sup_comm]
    exact f112sl_oTwoRes_sup_pCoreOf hn h2
  have hQleS2 : Q ≤ S2 := B6.pCoreOf_two_le_of_isSylowTwoOf hF.1.h2.sylow
  have hQleB2 : Q ≤ B2 := hQleS2.trans (F1.sylow_le_borelOf L2 S)
  have hVleM : V ≤ M := f112saP2_V_le_M L2 S
  have hVleS : V ≤ S := by intro x hx; exact hx.1.1
  have hVleL2 : V ≤ L2 := by intro x hx; exact hx.1.2
  have hVleS2 : V ≤ S2 := le_inf hVleS hVleL2
  have hVleP : V ≤ P := by
    rw [show P = L2 ⊔ S from f112sa_P2_eq_sup hF h1]
    exact hVleL2.trans le_sup_left
  have hX2leM : X2 ≤ M := inf_le_left
  have hX2leL2 : X2 ≤ L2 := hX2leM.trans (oTwoRes_le L2)
  have hL2B : L2 ⊓ B = B2 := by
    have h := F1.inf_bigB_eq_borelOf hR1.symm
    rw [← bigB_comm L2 L1 S] at h
    exact h
  have hB2leB : B2 ≤ B := by
    rw [← hL2B]
    exact inf_le_right
  have hX2leB2 : X2 ≤ B2 := by
    rw [← hL2B]
    exact le_inf hX2leL2 inf_le_right
  have hMV : M ⊓ S2 = V := by
    refine le_antisymm ?_ (le_inf hVleM hVleS2)
    intro x hx
    change x ∈ S ⊓ L2 ⊓ oTwoRes L2
    exact ⟨hx.2, hx.1⟩
  have hMB2 : M ⊓ B2 = X2 := by
    calc M ⊓ B2 = M ⊓ (L2 ⊓ B) := by rw [← hL2B]
      _ = (M ⊓ L2) ⊓ B := by rw [← inf_assoc]
      _ = M ⊓ B := by rw [inf_eq_left.mpr (oTwoRes_le L2)]
  have hQM : (↑(Q ⊔ M) : Set H) = (Q : Set H) * (M : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q M
      ((oTwoRes_le L2).trans (le_normalizer_pCoreOf 2 L2))
  have hQV : (↑(Q ⊔ V) : Set H) = (Q : Set H) * (V : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q V
      (hVleL2.trans (le_normalizer_pCoreOf 2 L2))
  have hQX : (↑(Q ⊔ X2) : Set H) = (Q : Set H) * (X2 : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q X2
      (hX2leL2.trans (le_normalizer_pCoreOf 2 L2))
  have hS2eq : S2 = Q ⊔ V := by
    have hded := Subgroup.mul_inf_assoc Q M S2 hQleS2
    have hset : (Q : Set H) * (V : Set H) = (S2 : Set H) := by
      rw [← hMV, hded, ← hQM, hMsup]
      exact Set.inter_eq_right.mpr (fun x hx => hx.2)
    have hset' : (S2 : Set H) = (↑(Q ⊔ V) : Set H) := by
      rw [hQV]
      exact hset.symm
    exact Subgroup.ext (Set.ext_iff.mp hset')
  have hB2eq : B2 = Q ⊔ X2 := by
    have hded := Subgroup.mul_inf_assoc Q M B2 hQleB2
    have hset : (Q : Set H) * (X2 : Set H) = (B2 : Set H) := by
      rw [← hMB2, hded, ← hQM, hMsup]
      exact Set.inter_eq_right.mpr (fun x hx => (F1.borelOf_le L2 S) hx)
    have hset' : (B2 : Set H) = (↑(Q ⊔ X2) : Set H) := by
      rw [hQX]
      exact hset.symm
    exact Subgroup.ext (Set.ext_iff.mp hset')
  have hQmap : (Q.subgroupOf L2).map q = ⊥ := by
    rw [f112saP2_pCoreOf_subgroupOf_eq L2, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hS2sub : S2.subgroupOf L2 = (Q.subgroupOf L2) ⊔ (V.subgroupOf L2) := by
    rw [hS2eq, Subgroup.subgroupOf_sup (pCoreOf_le 2 L2) hVleL2]
  have hT_eq : T = (V.subgroupOf L2).map q := by
    calc T = (S2.subgroupOf L2).map q := rfl
      _ = ((Q.subgroupOf L2) ⊔ (V.subgroupOf L2)).map q := by rw [hS2sub]
      _ = (Q.subgroupOf L2).map q ⊔ (V.subgroupOf L2).map q := Subgroup.map_sup _ _ _
      _ = ⊥ ⊔ (V.subgroupOf L2).map q := by rw [hQmap]
      _ = (V.subgroupOf L2).map q := bot_sup_eq _
  have hNborel : (B2.subgroupOf L2).map q = Subgroup.normalizer (T : Set Qbar) :=
    (F1.map_borelOf_eq_normalizer hF.1.h2.sylow).2.2
  have hB2sub : B2.subgroupOf L2 = (Q.subgroupOf L2) ⊔ (X2.subgroupOf L2) := by
    rw [hB2eq, Subgroup.subgroupOf_sup (pCoreOf_le 2 L2) hX2leL2]
  have hXimg : (X2.subgroupOf L2).map q = (B2.subgroupOf L2).map q := by
    rw [hB2sub, Subgroup.map_sup, hQmap, bot_sup_eq]
  have hNX : Subgroup.normalizer (T : Set Qbar) = (X2.subgroupOf L2).map q := by
    rw [← hNborel, ← hXimg]
  have hT2 : IsPGroup 2 T := (F1.map_borelOf_eq_normalizer hF.1.h2.sylow).1
  have hTodd : ¬ 2 ∣ T.index := (F1.map_borelOf_eq_normalizer hF.1.h2.sylow).2.1
  have hcond : ∀ y ∈ Subgroup.normalizer (T : Set Qbar),
      ρ ⟨t, htP⟩ y * y⁻¹ ∈ T := by
    intro y hy
    have hyX : y ∈ (X2.subgroupOf L2).map q := by rw [← hNX]; exact hy
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hyX
    have hdX : (d : H) ∈ X2 := Subgroup.mem_subgroupOf.mp hd
    have hdL : (d : H) ∈ L2 := hX2leL2 hdX
    let c : H := (t : H) * (d : H) * (t : H)⁻¹ * (d : H)⁻¹
    have hcX2 : c ∈ X2 := by
      have h1 : (t : H) * (d : H) * (t : H)⁻¹ ∈ X2 :=
        (Subgroup.mem_normalizer_iff.mp (f112saP2_bigB_normal_X2 hF h1 htB) (d : H)).mp hdX
      exact X2.mul_mem h1 (X2.inv_mem hdX)
    have hcR : c ∈ R := by
      have h1 : (d : H) * (t : H) * (d : H)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hXR hdX) (t : H)).mp ht
      have h2 : ((d : H) * (t : H) * (d : H)⁻¹)⁻¹ ∈ R := R.inv_mem h1
      have heq : (t : H) * ((d : H) * (t : H) * (d : H)⁻¹)⁻¹ = c := by
        simp [c]; group
      rw [← heq]
      exact R.mul_mem ht h2
    have hcV : c ∈ V :=
      f112saP2_le_V_of_isPGroup_of_hyp111R hF hR1 (hR.to_le inf_le_left) inf_le_right
        ⟨hcR, hcX2⟩
    have hcS2 : c ∈ S2 := hcV.1
    have hcL2 : c ∈ L2 := hcV.1.2
    have hval : ρ ⟨t, htP⟩ (q d) * (q d)⁻¹ = q ⟨c, hcL2⟩ := by
      have hρd : ρ ⟨t, htP⟩ (q d) =
          q ⟨(t : H) * (d : H) * (t : H)⁻¹, by
            exact (Subgroup.mem_normalizer_iff.mp
              (f112sl_P2_le_normalizer hF htP) (d : H)).mp hdL⟩ := by
        change CFSG.GroupTheory.conjModPCore 2 L2 P (f112sl_P2_le_normalizer hF)
          ⟨t, htP⟩ (q d) = _
        exact CFSG.GroupTheory.conjModPCore_mk 2 L2 P
          (f112sl_P2_le_normalizer hF) ⟨t, htP⟩ d
      rw [hρd, ← map_inv, ← map_mul]
      congr 1
    rw [← hdy, hval]
    exact Subgroup.mem_map.mpr ⟨⟨c, hcL2⟩, Subgroup.mem_subgroupOf.mpr hcS2, rfl⟩
  obtain ⟨e0⟩ := show Nonempty (Qbar ≃* PSL2 K) from h2
  let Ps : Sylow 2 Qbar := hT2.toSylow hTodd
  have hPscoe : (Ps : Subgroup Qbar) = T := rfl
  obtain ⟨U, hU⟩ := psl2UpperUnipotent_isSylow (K := K) (p := 2) (f := n)
    (GaloisField.card 2 n (by omega))
  have he0surj : Function.Surjective (e0 : Qbar →* PSL2 K) := e0.surjective
  let Ps' : Sylow 2 (PSL2 K) := Ps.mapSurjective he0surj
  have hPs'coe : (Ps' : Subgroup (PSL2 K)) = T.map e0.toMonoidHom := by
    change (Ps.mapSurjective he0surj : Subgroup (PSL2 K)) = T.map e0.toMonoidHom
    rw [Sylow.coe_mapSurjective]
    rfl
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 K) Ps' U
  have hh' : psl2UpperUnipotentSubgroup K =
      (T.map e0.toMonoidHom).map (MulAut.conj h).toMonoidHom := by
    have h1 := congrArg (fun S : Sylow 2 (PSL2 K) => (S : Subgroup (PSL2 K))) hh
    rw [Sylow.coe_subgroup_smul, hPs'coe, hU, Subgroup.pointwise_smul_def] at h1
    exact h1.symm
  let e : Qbar ≃* PSL2 K := e0.trans (MulAut.conj h)
  have heT : T.map e.toMonoidHom = psl2UpperUnipotentSubgroup K := by
    change T.map ((MulAut.conj h).toMonoidHom.comp e0.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hh'.symm
  have heN : (Subgroup.normalizer (T : Set Qbar)).map e.toMonoidHom = psl2Borel K := by
    rw [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) T e.bijective, heT,
      psl2UpperUnipotent_normalizer_eq_borel K]
  let σ : MulAut (PSL2 K) := MulAut.congr e (ρ ⟨t, htP⟩)
  have hfixσ : ∀ y ∈ psl2Borel K,
      σ y * y⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
    intro y hy
    have hy' : y ∈ (Subgroup.normalizer (T : Set Qbar)).map e.toMonoidHom := by
      rw [heN]; exact hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
    rw [← hxy]
    change σ (e x) * (e x)⁻¹ ∈ psl2UpperUnipotentSubgroup K
    have h := hcond x hx
    have hσx : σ (e x) = e (ρ ⟨t, htP⟩ x) := by
      simp [σ, MulAut.congr_apply]
    rw [hσx, ← map_inv, ← map_mul]
    have hmem : ρ ⟨t, htP⟩ x * x⁻¹ ∈ T := h
    have := Subgroup.mem_map_of_mem e.toMonoidHom hmem
    rwa [heT] at this
  have hσ2 : ∃ k, σ ^ 2 ^ k = 1 := by
    obtain ⟨a, ha⟩ := hR ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have h1 : (⟨t, htP⟩ : ↥P) ^ 2 ^ a = 1 := Subtype.ext hta
    have hdvd : orderOf (ρ ⟨t, htP⟩) ∣ 2 ^ a :=
      (orderOf_map_dvd ρ ⟨t, htP⟩).trans (orderOf_dvd_of_pow_eq_one h1)
    have hσord : orderOf σ = orderOf (ρ ⟨t, htP⟩) := by
      rw [show σ = MulAut.congr e (ρ ⟨t, htP⟩) from rfl, MulEquiv.orderOf_eq]
    exact ⟨a, orderOf_dvd_iff_pow_eq_one.mp (by rw [hσord]; exact hdvd)⟩
  obtain ⟨u, huU, hσconj⟩ :=
    f112sl_mulAut_eq_conj_of_mem_borel hn σ hσ2 hfixσ
  let x0 : Qbar := e.symm u
  have hx0T : x0 ∈ T := by
    rw [← Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective, heT]
    show e x0 ∈ psl2UpperUnipotentSubgroup K
    rw [show e x0 = u from e.apply_symm_apply u]
    exact huU
  have hx0V : x0 ∈ (V.subgroupOf L2).map q := by rw [← hT_eq]; exact hx0T
  obtain ⟨v0, hv0sub, hv0q⟩ := Subgroup.mem_map.mp hx0V
  have hv0V : (v0 : H) ∈ V := Subgroup.mem_subgroupOf.mp hv0sub
  have hv0P : (v0 : H) ∈ P := hVleP hv0V
  have hρv0 : ρ ⟨(v0 : H), hv0P⟩ = MulAut.conj x0 := by
    rw [← hv0q]
    exact CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 L2 P
      (f112sl_P2_le_normalizer hF) hv0P hv0V.1.2
  have hρt : ρ ⟨t, htP⟩ = MulAut.conj x0 := by
    have h1 : MulAut.congr e (ρ ⟨t, htP⟩) = MulAut.conj u := hσconj
    have h2 : (MulAut.congr e).symm (MulAut.conj u) = MulAut.conj x0 := by
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply, x0]
    calc ρ ⟨t, htP⟩ = (MulAut.congr e).symm (MulAut.congr e (ρ ⟨t, htP⟩)) :=
          (MulEquiv.symm_apply_apply (MulAut.congr e) _).symm
      _ = (MulAut.congr e).symm (MulAut.conj u) := by rw [h1]
      _ = MulAut.conj x0 := h2
  have hker : (⟨(t : H) * (v0 : H)⁻¹, by
      exact P.mul_mem htP (P.inv_mem hv0P)⟩ : ↥P) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    have hsplit : (⟨(t : H) * (v0 : H)⁻¹, by
        exact P.mul_mem htP (P.inv_mem hv0P)⟩ : ↥P) =
        ⟨t, htP⟩ * ⟨(v0 : H), hv0P⟩⁻¹ := by ext; rfl
    rw [hsplit, map_mul, map_inv, hρt, hρv0, mul_inv_cancel]
  have hmemKer : (⟨(t : H) * (v0 : H)⁻¹, by
      exact P.mul_mem htP (P.inv_mem hv0P)⟩ : ↥P) ∈ CFSG.pCore 2 ↥P :=
    f112sl_conjModPCore_ker_le_pCore hF h1 h2 hker
  have hmemPC : (t : H) * (v0 : H)⁻¹ ∈ pCoreOf 2 P :=
    Subgroup.mem_map_of_mem _ hmemKer
  have hv0M : (v0 : H) ∈ M := hVleM hv0V
  have ht_eq : (t : H) = ((t : H) * (v0 : H)⁻¹) * (v0 : H) := by group
  rw [ht_eq]
  exact (M ⊔ pCoreOf 2 P).mul_mem (Subgroup.mem_sup_right hmemPC)
    (Subgroup.mem_sup_left hv0M)

theorem f112sl_le_sup_pCoreOf_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) {n : ℕ} (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) {R : Subgroup H} (hR : IsPGroup 2 R)
    (hRB : R ≤ bigB L1 L2 S)
    (hXR : oTwoRes L2 ⊓ bigB L1 L2 S ≤ Subgroup.normalizer (R : Set H)) :
    R ≤ oTwoRes L2 ⊔ pCoreOf 2 (f112P2 L1 L2 S) := by
  intro t ht
  exact f112sl_mem_sup_of_normalized hF h1 hn h2 hR hRB hXR ht

end CFSG.Quasithin.F112R.St84
