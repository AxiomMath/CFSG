module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NN
public import CFSG.Quasithin.EmptyFaithful.SzN18Case
public import CFSG.Quasithin.Background.C2Six
public import CFSG.LieType.SteinbergBRUnitaryThreePerfect
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Nq

open scoped Pointwise

variable {G : Type} [Group G]

theorem mul_comm_of_le_normalizer {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    (R : Set G) * (K : Set G) = (K : Set G) * (R : Set G) := by
  ext x
  constructor
  · rintro ⟨r, hr, k, hk, rfl⟩
    exact ⟨r * k * r⁻¹, (Subgroup.mem_normalizer_iff.mp (hRK hr) k).mp hk, r, hr, by group⟩
  · rintro ⟨k, hk, r, hr, rfl⟩
    refine ⟨r, hr, r⁻¹ * k * r, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hRK hr)) k).mp hk
    simpa using this

theorem exists_pow_mem_of_mem_sup [Finite G] {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR : IsPGroup 2 R) {x : G} (hx : x ∈ K ⊔ R) :
    ∃ j : ℕ, x ^ 2 ^ j ∈ K := by
  have hset := A4.coe_sup_eq_mul_of_mul_comm (mul_comm_of_le_normalizer hRK)
  have hx' : x ∈ ((K ⊔ R : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨k, hk, r, hr, rfl⟩ := hx'
  exact A4.exists_pow_mem_of_mul (sup_le Subgroup.le_normalizer hRK) hR hx hk hr rfl le_sup_left

theorem mem_of_orderOf_three [Finite G] {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR : IsPGroup 2 R) {x : G} (hx : x ∈ K ⊔ R)
    (h3 : orderOf x = 3) : x ∈ K := by
  obtain ⟨j, hj⟩ := exists_pow_mem_of_mem_sup hRK hR hx
  have e : 2 ^ j * 2 ^ j % 3 = 1 := by
    rw [← mul_pow, Nat.pow_mod]
    norm_num
  have h1 : (x ^ 2 ^ j) ^ 2 ^ j = x := by
    rw [← pow_mul, ← pow_mod_orderOf, h3, e, pow_one]
  rw [← h1]
  exact K.pow_mem hj _

theorem pCoreOf_le_sup [Finite G] {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    ((sup_le Subgroup.le_normalizer hRK).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem charTwo_sup [Finite G] {K R : Subgroup G} (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hR : IsPGroup 2 R) (hK : CharTwo K) : CharTwo (K ⊔ R) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hK hR hRK

theorem isNilpotent_subgroupOf {Y : Type*} [Group Y] (N K : Subgroup Y) [Group.IsNilpotent ↥N] :
    Group.IsNilpotent ↥(N.subgroupOf K) := by
  let ι : ↥(N.subgroupOf K) →* ↥N :=
    { toFun := fun x => ⟨((x : ↥K) : Y), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h => by
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h1)
  exact Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hι).symm

theorem three_dvd_card_SL {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
  have : NeZero m := ⟨by omega⟩
  rw [Matrix.card_SL_field (𝔽 := ZMod 2) m, ZMod.card]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hmem : (⟨k, by omega⟩ : Fin (k + 2)) ∈ Finset.univ := Finset.mem_univ _
  refine dvd_trans ?_
    (Finset.dvd_prod_of_mem (fun i : Fin (k + 2) => 2 ^ (k + 2) - 2 ^ (i : ℕ)) hmem)
  show 3 ∣ 2 ^ (k + 2) - 2 ^ k
  have e : 2 ^ (k + 2) - 2 ^ k = 3 * 2 ^ k := Nat.sub_eq_of_eq_add (by ring)
  rw [e]
  exact dvd_mul_right 3 _

end Sec1211Nq

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

variable (S) in
theorem isQuasisimple_of_lt (h331 : Stmt3_3_1) (h129 : ASC129Statement G)
    (h36 : Vol2Native.A36CoreForSQTKCat) (F : Frame S m) (hm : 3 ≤ m)
    (hchar : CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K)
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := S.hyp.simple
  have hqtke : QTKECore G := qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hlvK : Lv ≤ K := hlt.le
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hQMv : Q ≤ M ⊓ H := le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hR2 : IsPGroup 2 R := hR.2.1
  have hRH : R ≤ H := hR.1.trans inf_le_right
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := hRH.trans hKn
  set X := K ⊔ R with hXdef
  have hKX : K ≤ X := le_sup_left
  have hXH : X ≤ H := sup_le hKH hRH
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hKc : CharTwo K := A4.charTwo_of_normal hKH hKn hchar
  have hXc : CharTwo X := Sec1211Nq.charTwo_sup hRK hR2 hKc
  have hKcX : K ∈ cComp X := by
    refine ⟨hK.1, hK.2.1, IsSubnormal.step hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN) (IsSubnormal.refl X),
      fun K' hK'K hK'1 hK'p hsub => ?_⟩
    exact hK.2.2.2 K' hK'K hK'1 hK'p
      (A3.subnormal_trans (A3.subnormal_of_le_of_le hsub hK'K.le hKX) hK.2.2.1)
  have hX1 : pCoreOf 2 X ≠ ⊥ := by
    intro hb
    have hO := Sec1211Nq.pCoreOf_le_sup hRK
    rw [← hXdef, hb, le_bot_iff] at hO
    apply hK.1
    rw [eq_bot_iff]
    intro k hk
    have hc : k ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [hO, SetLike.mem_coe, Subgroup.mem_bot] at hg
      rw [hg, one_mul, mul_one]
    have h1 : k ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) := Subgroup.mem_inf.mpr ⟨hk, hc⟩
    have h2 := hKc h1
    rwa [hO] at h2
  have hyp := S.hypC23_of_le h331 F hm hXH (hlvK.trans hKX) hR le_sup_right hQR
  obtain ⟨hconc, -, -⟩ := Vol2Native.lemma_1_2_1_four_core hqtke.1 h36 hX1 hKcX
  rcases hconc with hcomp | h34
  ·
    obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection hKcX
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm hcomp.1
  exfalso
  obtain ⟨hgf, hF6⟩ := SzN18.fitting_primes_of_case34 h34
  set Kb := modO2Image X K with hKbdef
  set φ := SzN18.toBar hKX with hφdef
  have hφs : Function.Surjective φ := by
    rintro ⟨x, ⟨y, hyK, hyx⟩⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hyK⟩, Subtype.ext hyx⟩
  have hφk : ∀ k : ↥K, φ k = 1 → ∃ a : ℕ, (k : G) ^ 2 ^ a = 1 := by
    intro k hk
    have h1 : (QuotientGroup.mk (⟨k, hKX k.2⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) = 1 := by
      have := congrArg Subtype.val hk
      rwa [SzN18.toBar_coe] at this
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, h1⟩
    refine ⟨a, ?_⟩
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥X) => ((y : ↥X) : G)) ha
    simpa using this
  set Fb := CFSG.fittingSubgroup ↥Kb with hFbdef
  set Q₀ : Subgroup ↥K := Fb.comap φ with hQ₀def
  have hFodd : ∀ f : ↥Fb, ∀ a : ℕ, f ^ 2 ^ a = 1 → f = 1 := by
    intro f a hf
    have h2 : ¬ 2 ∣ Nat.card ↥Fb := fun h => (hF6 2 Nat.prime_two h).1 rfl
    have hcop : Nat.Coprime (Nat.card ↥Fb) (2 ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
    have h3 : Nat.Coprime (orderOf f) (2 ^ a) :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard f) hcop
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 (orderOf_dvd_of_pow_eq_one hf))
  have hcop3 : ∀ q ∈ Q₀, Nat.Coprime (orderOf q) 3 := by
    intro q hq
    have hqF : φ q ∈ Fb := hq
    set k := Nat.card ↥Fb with hk
    have h3k : ¬ 3 ∣ k := fun h => (hF6 3 Nat.prime_three h).2 rfl
    have hpow : φ (q ^ k) = 1 := by
      rw [map_pow]
      have := pow_card_eq_one' (G := ↥Fb) (x := ⟨φ q, hqF⟩)
      exact congrArg Subtype.val this
    obtain ⟨j, hj⟩ := hφk _ hpow
    have hqj : q ^ (k * 2 ^ j) = 1 := by
      apply Subtype.ext
      rw [pow_mul]
      simpa using hj
    have hc : Nat.Coprime (k * 2 ^ j) 3 :=
      Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3k).symm
        (Nat.Coprime.pow_left j (by decide))
    exact hc.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hqj)
  have hKbn : Kb.Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN).map _
      (QuotientGroup.mk'_surjective _)
  have hFmapN : (Fb.map Kb.subtype).Normal := by
    constructor
    rintro _ ⟨f, hf, rfl⟩ g
    refine ⟨MulAut.conjNormal g f, ?_, ?_⟩
    · exact (Subgroup.characteristic_iff_map_le.mp inferInstance (MulAut.conjNormal g))
        ⟨f, hf, rfl⟩
    · simp [MulAut.conjNormal_apply]
  have hFmapNil : Group.IsNilpotent ↥(Fb.map Kb.subtype) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective Fb Kb.subtype Kb.subtype_injective)
  have hFle : Fb.map Kb.subtype ≤ CFSG.fittingSubgroup (↥X ⧸ CFSG.pCore 2 ↥X) := by
    unfold CFSG.fittingSubgroup
    exact le_sSup ⟨hFmapN, hFmapNil⟩
  have hFXle : (CFSG.fittingSubgroup (↥X ⧸ CFSG.pCore 2 ↥X)).subgroupOf Kb ≤ Fb := by
    have hn : ((CFSG.fittingSubgroup (↥X ⧸ CFSG.pCore 2 ↥X)).subgroupOf Kb).Normal :=
      CFSG.fittingSubgroup_normal.subgroupOf Kb
    have hnil := Sec1211Nq.isNilpotent_subgroupOf
      (CFSG.fittingSubgroup (↥X ⧸ CFSG.pCore 2 ↥X)) Kb
    rw [hFbdef]
    unfold CFSG.fittingSubgroup
    exact le_sSup ⟨hn, hnil⟩
  have hQ₀F : ∀ q ∈ Q₀, (q : G) ∈ oTwoFIn X := by
    intro q hq
    refine C2Six.mem_oTwoFIn.mpr ⟨hKX q.2, ?_⟩
    rw [← SzN18.toBar_coe hKX q]
    exact hFle ⟨φ q, hq, rfl⟩
  have hFQ₀ : ∀ k : ↥K, (k : G) ∈ oTwoFIn X → k ∈ Q₀ := by
    intro k hk
    obtain ⟨hkX', hmem⟩ := C2Six.mem_oTwoFIn.mp hk
    show φ k ∈ Fb
    apply hFXle
    rw [Subgroup.mem_subgroupOf, SzN18.toBar_coe]
    exact hmem
  have hFM : oTwoFIn X ≤ M ⊓ H ⊓ X := by
    by_contra hnot
    have hFc : CharTwo (oTwoFIn X) :=
      A4.charTwo_of_normal C2Six.oTwoFIn_le C2Six.le_normalizer_oTwoFIn hXc
    obtain ⟨r, Lb, hLb, hdec⟩ := c2_6_two h129 hyp hFc hnot
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      apply hnot
      intro x hx
      obtain ⟨mm, hmm, y, -, rfl⟩ := hdec x hx
      simpa using hmm.1
    · obtain ⟨hblk, h3, -⟩ := hLb ⟨0, hr0⟩
      have h3d : 3 ∣ Nat.card ↥(Lb ⟨0, hr0⟩) := by
        have hc := C2Six.natCard_pCore_quotient_of_isAltType_three h3
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (CFSG.pCore 2 ↥(Lb ⟨0, hr0⟩))
        rw [hc] at h1
        exact ⟨_, h1⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Lb ⟨0, hr0⟩)) 3 h3d
      have hyF : (y : G) ∈ oTwoFIn X := hblk.2.1 y.2
      have hyX : (y : G) ∈ X := C2Six.oTwoFIn_le hyF
      have hyo : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
      have hyK : (y : G) ∈ K := Sec1211Nq.mem_of_orderOf_three hRK hR2 hyX hyo
      have hc := hcop3 _ (hFQ₀ ⟨y, hyK⟩ hyF)
      rw [Subgroup.orderOf_mk, hyo] at hc
      exact absurd hc (by decide)
  have hQ₀N : ∀ q ∈ Q₀, (q : G) ∈ Subgroup.normalizer (Lv : Set G) := by
    intro q hq
    have h1 := hFM (hQ₀F q hq)
    exact Sec1216Lv.le_normalizer_lv (X := M ⊓ H) inf_le_left inf_le_right ⟨h1.1.1, h1.1.2⟩
  have hNL : ∀ l ∈ Lv, l ∈ Q₀.map K.subtype → ∃ a : ℕ, l ^ 2 ^ a = 1 := by
    have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
      Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hm
    set ψ := psi F S.lv_le_Xv with hψdef
    have hψs : Function.Surjective ψ := psi_lv_surjective F
    set NL : Subgroup ↥Lv := (Q₀.map K.subtype).comap Lv.subtype with hNLdef
    have hQ₀n : Q₀.Normal := Subgroup.Normal.comap inferInstance φ
    have hNLn : NL.Normal := by
      constructor
      intro x hx l
      obtain ⟨q, hq, hqx⟩ := hx
      refine ⟨⟨(l : G), hlvK l.2⟩ * q * ⟨(l : G), hlvK l.2⟩⁻¹, hQ₀n.conj_mem q hq _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hqx ⊢
      rw [hqx]
    have hNLm : (NL.map ψ).Normal := hNLn.map ψ hψs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (NL.map ψ) with hb | ht
    · intro l hl hlQ
      have h1 : ψ ⟨l, hl⟩ ∈ NL.map ψ := ⟨⟨l, hl⟩, hlQ, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      obtain ⟨a, ha⟩ := isPGroup_ker_psi_lv F ⟨⟨l, hl⟩, h1⟩
      refine ⟨a, ?_⟩
      have := congrArg (fun z : ↥(psi F S.lv_le_Xv).ker => ((z : ↥Lv) : G)) ha
      simpa using this
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
        (G := Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) 3
        (Sec1211Nq.three_dvd_card_SL (by omega))
      have hgm : g ∈ NL.map ψ := ht ▸ Subgroup.mem_top g
      obtain ⟨l, hlN, rfl⟩ := hgm
      obtain ⟨q, hq, hql⟩ := hlN
      have hc := hcop3 q hq
      have h1 : orderOf (ψ l) ∣ orderOf l := orderOf_map_dvd ψ l
      have h2 : orderOf l = orderOf q := by
        rw [← Subgroup.orderOf_coe l, ← Subgroup.orderOf_coe q]
        simp only [Subgroup.coe_subtype] at hql
        rw [hql]
      rw [hg, h2] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc.symm h1
  set Λ : Subgroup ↥Kb := (Lv.subgroupOf K).map φ with hΛdef
  have hFΛ : ∀ x ∈ Fb, x ∈ Λ → x = 1 := by
    intro x hxF hxΛ
    obtain ⟨k, hk, rfl⟩ := hxΛ
    have hkQ : k ∈ Q₀ := hxF
    obtain ⟨a, ha⟩ := hNL (k : G) hk ⟨k, hkQ, rfl⟩
    have hka : k ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha)
    have hx := hFodd ⟨φ k, hxF⟩ a (Subtype.ext (by
      rw [Subgroup.coe_pow]
      show (φ k) ^ 2 ^ a = 1
      rw [← map_pow, hka, map_one]))
    exact congrArg Subtype.val hx
  have hcomm : ∀ f ∈ Fb, ∀ y ∈ Λ, f * y = y * f := by
    intro f hf y hy
    obtain ⟨q, rfl⟩ := hφs f
    obtain ⟨k, hk, rfl⟩ := hy
    have hq : q ∈ Q₀ := hf
    have hc1 : φ q * φ k * (φ q)⁻¹ * (φ k)⁻¹ ∈ Fb := by
      have h1 : φ k * (φ q)⁻¹ * (φ k)⁻¹ ∈ Fb :=
        CFSG.fittingSubgroup_normal.conj_mem _ (Fb.inv_mem hf) _
      have e : φ q * φ k * (φ q)⁻¹ * (φ k)⁻¹ = φ q * (φ k * (φ q)⁻¹ * (φ k)⁻¹) := by group
      rw [e]
      exact Fb.mul_mem hf h1
    have hc2 : φ q * φ k * (φ q)⁻¹ * (φ k)⁻¹ ∈ Λ := by
      have hkL : (k : G) ∈ Lv := hk
      have h1 : (q : G) * k * (q : G)⁻¹ ∈ Lv :=
        (Subgroup.mem_normalizer_iff.mp (hQ₀N q hq) k).mp hkL
      have hqk : q * k * q⁻¹ * k⁻¹ ∈ Lv.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        simpa using Lv.mul_mem h1 (Lv.inv_mem hkL)
      exact ⟨q * k * q⁻¹ * k⁻¹, hqk, by simp⟩
    have h0 := hFΛ _ hc1 hc2
    calc φ q * φ k = (φ q * φ k * (φ q)⁻¹ * (φ k)⁻¹) * (φ k * φ q) := by group
      _ = φ k * φ q := by rw [h0, one_mul]
  have hΛF : Λ ≤ Fb := by
    intro y hy
    have h1 := CFSG.centralizer_generalizedFitting_le ↥Kb
    rw [hgf] at h1
    apply h1
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact hcomm f hf y hy
  have hLv2 : IsPGroup 2 ↥Lv := by
    intro l
    have hlK : (l : G) ∈ K := hlvK l.2
    have hmem : φ ⟨l, hlK⟩ ∈ Λ := ⟨⟨l, hlK⟩, l.2, rfl⟩
    obtain ⟨a, ha⟩ := hφk _ (hFΛ _ (hΛF hmem) hmem)
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  have : Group.IsNilpotent ↥Lv := hLv2.isNilpotent
  have hbot : Lv = ⊥ :=
    CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable (Sec1216Lv.lv_perfect L (a₀ * c₀))
  obtain ⟨a, haW, ha1⟩ := exists_ne_one_W₁ F (by omega)
  have := S.W₁_le_lv haW
  rw [← hLvdef, hbot, Subgroup.mem_bot] at this
  exact ha1 this

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
