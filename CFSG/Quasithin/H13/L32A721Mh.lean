module

public import CFSG.Quasithin.H13.L32A721Mg
public import CFSG.Quasithin.Background.A1cA132Aux

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def q8GL : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {u | (u : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 ∧ u ^ 4 = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha4⟩ ⟨hb, hb4⟩
    refine ⟨by rw [Units.val_mul, Matrix.det_mul, ha, hb, one_mul], Units.ext ?_⟩
    have ha4' : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha4, Units.val_one]
    have hb4' : (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hb4, Units.val_one]
    rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
    exact sl23_mul_pow_four _ _ ha ha4' hb hb4'
  one_mem' := ⟨by simp, one_pow 4⟩
  inv_mem' := by
    rintro a ⟨ha, ha4⟩
    have e : a⁻¹ = a ^ 3 := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, ha4]
    refine ⟨?_, by rw [inv_pow, ha4, inv_one]⟩
    rw [e, Units.val_pow_eq_pow_val, Matrix.det_pow, ha, one_pow]

theorem q8GL_normal : q8GL.Normal := by
  refine ⟨fun a ha g => ⟨?_, ?_⟩⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, ha.1, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · rw [conj_pow, ha.2, mul_one, mul_inv_cancel]

theorem mem_q8GL_of_pow {u : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)}
    (hdet : (u : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1) {k : ℕ} (hk : u ^ 2 ^ k = 1) :
    u ∈ q8GL := by
  refine ⟨hdet, Units.ext ?_⟩
  have h16 : u ^ 16 = 1 := by
    have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf u ∣ 48 := orderOf_dvd_of_pow_eq_one (gl23_pow_48 u)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have h3 : 2 ^ j ∣ 16 := by
      have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left _ (by norm_num)
      have h48 : 2 ^ j ∣ 16 * 3 := by rw [← hj]; simpa using h2
      exact hcop.dvd_of_dvd_mul_right h48
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ h3)
  have h16' : (u : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 16 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h16, Units.val_one]
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact sl23_pow_four _ hdet h16'

section Rho

variable {Γ : Type} [Group Γ] [Finite Γ] {X : Subgroup Γ} [X.Normal] (hX : IsPOnePlusTwo 3 ↥X)
include hX

omit [X.Normal] in
theorem center_le_frattini_721 : Subgroup.center ↥X ≤ frattini ↥X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥X := inferInstance
  obtain ⟨a, b, hab⟩ := Heis.exists_comm_ne_one hX
  have hc := Heis.comm_mem_center hX a b
  rw [← Heis.center_eq_zpowers hX hc hab, Subgroup.zpowers_le]
  exact CFSG.SectionRank.Ccomm.commutator_mem_frattini (IsPGroup.of_card hX.2.1) a b

theorem exists_rho_721 : ∃ ρ : Γ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3),
    (∀ g, ρ g = 1 → g ∈ X ⊔ Subgroup.centralizer (X : Set Γ)) ∧ (∀ x ∈ X, ρ x = 1) ∧
    (∀ g, (∀ z ∈ (Subgroup.center ↥X).map X.subtype, g * z * g⁻¹ = z) →
      (ρ g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (↥X ⧸ Subgroup.center ↥X) = 3 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)
    rw [hX.2.1, Heis.card_center hX] at h1
    omega
  have hpow : ∀ q : ↥X ⧸ Subgroup.center ↥X, q ^ 3 = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, Heis.pow_three_eq hX, QuotientGroup.mk_one]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3)
    (Heis.quot_comm hX) hpow hcard
  set f := e.symm with hf
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (f (Multiplicative.ofAdd (Pi.single 0 1)))
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (f (Multiplicative.ofAdd (Pi.single 1 1)))
  refine ⟨(He8.repGL f).comp ((He8.quotAut (Subgroup.center ↥X)).comp
    (MulAut.conjNormal : Γ →* MulAut ↥X)), ?_, ?_, ?_⟩
  · intro g hg
    have h1 : He8.quotAut (Subgroup.center ↥X) (MulAut.conjNormal g) = 1 :=
      He8.repGL_injective f (by rw [map_one]; exact hg)
    apply A1c.mem_sup_centralizer_of_isPOnePlusTwo hX
    rw [CFSG.SectionRank.Ccomm.mem_ker_autQuotient]
    intro x
    apply center_le_frattini_721 hX
    have h2 := congrArg (fun φ : MulAut (↥X ⧸ Subgroup.center ↥X) =>
      φ (x : ↥X ⧸ Subgroup.center ↥X)) h1
    simp only [He8.quotAut_mk, MulAut.one_apply] at h2
    rw [QuotientGroup.eq] at h2
    have h3 := Subgroup.inv_mem _ h2
    rwa [mul_inv_rev, inv_inv] at h3
  · intro x hx
    have h1 : He8.quotAut (Subgroup.center ↥X) (MulAut.conjNormal x) = 1 := by
      ext q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      rw [He8.quotAut_mk, MulAut.one_apply]
      have e1 : (MulAut.conjNormal x y : ↥X) = ⟨x, hx⟩ * y * (⟨x, hx⟩ : ↥X)⁻¹ :=
        Subtype.ext (by simp)
      rw [e1, QuotientGroup.eq]
      have e2 : (⟨x, hx⟩ * y * (⟨x, hx⟩ : ↥X)⁻¹)⁻¹ * y = ⁅(⟨x, hx⟩ : ↥X), y⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e2]
      exact Heis.comm_mem_center hX _ _
    simp only [MonoidHom.comp_apply, h1, map_one]
  · intro g hg
    have hfix : MulAut.conjNormal g ⁅a, b⁆ = ⁅a, b⁆ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hg _ ⟨_, Heis.comm_mem_center hX a b, rfl⟩
    exact Heis.det_eq_one_of_fix hX ha hb hfix

end Rho

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

theorem isSylowTwoOf_tbar : IsSylowTwoOf (modO2Image (mK T V) T)
    (⊤ : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top,
    (E.S.hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe E.t_le_mK).symm).map _, ?_⟩
  have htop : modO2Image (mK T V) (mK T V) = ⊤ := by
    rw [modO2Image, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  show ¬ 2 ∣ (modO2Image (mK T V) T).relIndex ⊤
  rw [← htop, relIndex_modO2Image' le_rfl
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf E.isSylowTwoOf_mK)]
  exact E.isSylowTwoOf_mK.2.2

theorem centralizer_kbar_le (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) :
    Subgroup.centralizer ((modO2Image (mK T V) (kz T V) :
      Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) ≤ modO2Image (mK T V) (l1 T L V) := by
  have hO := E.pCoreOf_mK_eq hF hC137 h56 h1338
  have hP := E.isPGroup_centralizer_kbar hF hC137 h56 h1338
  intro c hc
  have hcN : c ∈ Subgroup.normalizer
      ((modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) :
        Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
          Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun r hr => ?_)
    have e := E.comm_r1bar_centralizer hO hP hr hc
    calc r * c = r * c * r⁻¹ * r := by group
      _ = c * r := by rw [e]
  obtain ⟨k, hk⟩ := hP ⟨c, hc⟩
  exact E.mem_l1bar_of_normalizes hF hC137 hO hcN (m := k) (by simpa using congrArg Subtype.val hk)

theorem mem_kbar_of_pow_three (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8)
    {g : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)} {m : ℕ} (hgm : g ^ 3 ^ m = 1) :
    g ∈ modO2Image (mK T V) (kz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := E.pCoreOf_mK_eq hF hC137 h56 h1338
  have hX := E.isPOnePlusTwo_kbar
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  have hL1n := E.l1bar_normal
  set X := modO2Image (mK T V) (kz T V) with hXdef
  set R := modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) with hRdef
  set L1b := modO2Image (mK T V) (l1 T L V) with hL1b
  have hCL := E.centralizer_kbar_le hF hC137 h56 h1338
  have hL1X : L1b ≤ X := modO2Image_mono E.l1_le_kz_ctx
  obtain ⟨ρ, hρker, hρX, hρdet⟩ := exists_rho_721 hX
  set Y := Subgroup.centralizer (L1b : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) with hY
  have hYn : (⊤ : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) ≤
      Subgroup.normalizer (Y : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    intro x _
    refine mem_normalizer_of_conj_mem_721 fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : x⁻¹ * l * x⁻¹⁻¹ ∈ L1b := hL1n.conj_mem l hl x⁻¹
    have e := Subgroup.mem_centralizer_iff.mp hy _ hl'
    calc l * (x * y * x⁻¹) = x * ((x⁻¹ * l * x⁻¹⁻¹) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * l * x⁻¹⁻¹)) * x⁻¹ := by rw [e]
      _ = x * y * x⁻¹ * l := by group
  have hdetY : ∀ y ∈ Y, (ρ y : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    intro y hy
    refine hρdet y fun z hz => ?_
    rw [E.center_kbar_eq hO] at hz
    rw [← Subgroup.mem_centralizer_iff.mp hy z hz, mul_inv_cancel_right]
  have hQn := q8GL_normal
  set P := Y ⊓ q8GL.comap ρ with hP
  have hPn : (⊤ : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) ≤
      Subgroup.normalizer (P : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    intro x _
    refine mem_normalizer_of_conj_mem_721 fun y hy => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hYn trivial) y).mp hy.1
    · show ρ (x * y * x⁻¹) ∈ q8GL
      rw [map_mul, map_mul, map_inv]
      exact hQn.conj_mem _ hy.2 _
  have hRY : R ≤ Y := by
    rw [hRdef, E.r1bar_eq hO]
    exact inf_le_right
  have hR2 : IsPGroup 2 ↥R := ((pCoreOf_isPGroup 2 (l1 T L V ⊔ T)).of_equiv
    (Subgroup.subgroupOfEquivOfLe (E.r1_le_hz.trans E.hz_le_mK)).symm).map _
  have hRP : R ≤ P := by
    intro r hr
    refine ⟨hRY hr, ?_⟩
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    have hk' : ρ r ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this, map_one]
    exact mem_q8GL_of_pow (hdetY r (hRY hr)) hk'
  have hsylY : IsSylowTwoOf R Y := by
    have h1 := A4.isSylowTwoOf_inf_normal E.isSylowTwoOf_tbar le_top hYn
    rwa [← E.r1bar_eq hO] at h1
  have hodd : ¬ 2 ∣ R.relIndex P := by
    intro h2
    apply hsylY.2.2
    exact h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex R P Y hRP inf_le_left))
  obtain ⟨n, hn, c, hcP, hgnc⟩ := exists_mul_of_sylow (M := ⊤) le_top hPn hRP hR2 hodd g trivial
  have hnN : n ∈ Subgroup.normalizer (R : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := hn.2
  have hN2 : IsPGroup 2
      ↥((Subgroup.normalizer (R : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))).map ρ) := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    suffices hw16 : ρ w ^ 2 ^ 4 = 1 from ⟨4, Subtype.ext (by simpa using hw16)⟩
    set w' := w ^ 16 with hw'
    have h3 : ρ w' ^ 3 = 1 := by
      rw [hw', map_pow, ← pow_mul]
      exact gl23_pow_48 _
    obtain ⟨e, s, hs3, hse⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w').ne' 3
      (by norm_num)
    have hws : (w' ^ s) ^ 3 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hse, pow_orderOf_eq_one]
    have hwN : w' ^ s ∈ Subgroup.normalizer (R : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :=
      Subgroup.pow_mem _ (Subgroup.pow_mem _ hw _) _
    have hwL := E.mem_l1bar_of_normalizes hF hC137 hO hwN hws
    have h1 : ρ w' ^ s = 1 := by rw [← map_pow]; exact hρX _ (hL1X hwL)
    have hcop : Nat.Coprime 3 s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs3
    have h2 := pow_gcd_eq_one.mpr ⟨h3, h1⟩
    rw [hcop.gcd_eq_one, pow_one] at h2
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← map_pow]
    exact h2
  have hP2 : IsPGroup 2 ↥(P.map ρ) := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact ⟨2, Subtype.ext (by simpa using hw.2.2)⟩
  have hNP : (Subgroup.normalizer (R : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))).map ρ ≤
      Subgroup.normalizer (((P.map ρ : Subgroup _)) : Set (Matrix.GeneralLinearGroup (Fin 2)
        (ZMod 3))) := by
    rintro _ ⟨w, -, rfl⟩
    refine mem_normalizer_of_conj_mem_721 fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨w * p * w⁻¹, (Subgroup.mem_normalizer_iff.mp (hPn trivial) p).mp hp,
      by rw [map_mul, map_mul, map_inv]⟩
  have hNP2 := hN2.to_sup_of_normal_right' hP2 hNP
  have hρg : ρ g ∈ (Subgroup.normalizer
      (R : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))).map ρ ⊔ P.map ρ := by
    rw [hgnc, map_mul]
    exact Subgroup.mul_mem_sup ⟨n, hnN, rfl⟩ ⟨c, hcP, rfl⟩
  obtain ⟨k, hk⟩ := hNP2 ⟨_, hρg⟩
  have hk' : ρ g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hg3 : ρ g ^ 3 ^ m = 1 := by rw [← map_pow, hgm, map_one]
  have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  have h1 := pow_gcd_eq_one.mpr ⟨hk', hg3⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  have h2 := hρker g h1
  exact (sup_le le_rfl (hCL.trans hL1X)) h2

theorem mK_le_hz (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) : mK T V ≤ hz T V := by
  have hO := E.pCoreOf_mK_eq hF hC137 h56 h1338
  have hX := E.isPOnePlusTwo_kbar
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  set X := modO2Image (mK T V) (kz T V) with hXdef
  set J := modO2Image (mK T V) (kz T V ⊔ T) with hJ
  have hKTH : kz T V ⊔ T ≤ hz T V := sup_le (oTwoUpper_le _) E.t_le_hz
  have hXJ : X ≤ J := modO2Image_mono le_sup_left
  have hTJ : modO2Image (mK T V) T ≤ J := modO2Image_mono le_sup_right
  have hJtop : J = ⊤ := by
    by_contra hne
    have hidx : J.index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hidx
    have hpG : p ∣ Nat.card (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) :=
      hpd.trans (Subgroup.index_dvd_card J)
    by_cases hp2 : p = 2
    · subst hp2
      apply E.isSylowTwoOf_tbar.2.2
      show 2 ∣ (modO2Image (mK T V) T).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hpd.trans (Subgroup.index_dvd_of_le hTJ)
    by_cases hp3 : p = 3
    · subst hp3
      have h3X : 3 ∣ X.index := hpd.trans (Subgroup.index_dvd_of_le hXJ)
      rw [Subgroup.index_eq_card] at h3X
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨q, hq⟩ :=
        exists_prime_orderOf_dvd_card' (G := (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ⧸ X) 3 h3X
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx3 : x ^ 3 ∈ X := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
      have hx9 : x ^ 3 ^ 2 = 1 := by
        rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
        have := Heis.pow_three_eq hX ⟨_, hx3⟩
        simpa using congrArg Subtype.val this
      have hxX := E.mem_kbar_of_pow_three hF hC137 h56 h1338 hx9
      have hq1 : (x : (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ⧸ X) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hxX
      rw [hq1, orderOf_one] at hq
      norm_num at hq
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) p hpG
    have hwp : w ^ p ^ 1 = 1 := by rw [pow_one, ← hw]; exact pow_orderOf_eq_one w
    have hwC : w ∈ Subgroup.centralizer (X : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => by
        have e := comm_of_pow_prime hX hp hp5 hwp x hx
        calc x * w = w * x * w⁻¹ * w := by rw [e]
          _ = w * x := by group
    have hwL := E.centralizer_kbar_le hF hC137 h56 h1338 hwC
    have hw3 : orderOf w ∣ 3 := by
      rw [← E.card_l1dot]
      have hc : Nat.card ↥(modO2Image (mK T V) (l1 T L V)) = Nat.card ↥(modO2Image (hz T V)
          (l1 T L V)) := by
        rw [card_modO2Image' (E.l1_le_hz.trans E.hz_le_mK), card_modO2Image' E.l1_le_hz, hO]
      rw [← hc]
      exact Subgroup.orderOf_dvd_natCard _ hwL
    rw [hw] at hw3
    have := Nat.le_of_dvd (by norm_num) hw3
    omega
  intro x hx
  have hxJ : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨x, hx⟩ ∈ J := by
    rw [hJtop]; trivial
  obtain ⟨y, hy, hye⟩ := mem_modO2Image_iff.mp hxJ
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (y⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hye, inv_mul_cancel]
  rw [mk_eq_one_iff_mK, hO] at h2
  have e : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥(mK T V)) : G) := by simp
  rw [e]
  exact mul_mem (hKTH hy) (pCoreOf_le 2 _ h2)

end Ctx7153

theorem Ctx7153.max_two_local {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}
    (E : Ctx7153 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) :
    quasithinIsMaxTwoLocal (hz T V) := by
  obtain ⟨rfl, -⟩ := E.lemma14_7_15_three_of hF
  exact E.max_two_local_of_le (E.mK_le_hz hF hC137 h56 h1338)

end CFSG.Quasithin.H13.L32A
