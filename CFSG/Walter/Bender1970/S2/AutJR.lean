module

public import CFSG.Walter.Bender1970.S2.Basic
import CFSG.Walter.Bender1970.S2.PGroup
import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem isQuasisimple_of_isSimpleGroup' {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) :
    GorensteinWalter.IsQuasisimple Q ∧ Subgroup.center Q = ⊥ := by
  obtain ⟨a, b, hab⟩ := hQ
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a) hab
  have hP : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · refine absurd ?_ hab
      rw [← commutatorElement_eq_one_iff_mul_comm, ← Subgroup.mem_bot, ← h, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    · exact h
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hne : a ≠ b := fun h => hab (by rw [h])
  exact ⟨⟨nontrivial_of_ne a b hne, hP, e.isSimpleGroup⟩, hZ⟩

theorem exists_pow_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {g : G} (hg : g ≠ 1)
    (hodd : Odd (orderOf g)) : ∃ (k r : ℕ), r.Prime ∧ r ≠ 2 ∧ orderOf (g ^ k) = r := by
  have h1 : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
  set r := (orderOf g).minFac with hr
  have hrp : r.Prime := Nat.minFac_prime h1
  have hrd : r ∣ orderOf g := Nat.minFac_dvd _
  refine ⟨orderOf g / r, r, hrp, ?_, orderOf_pow_orderOf_div (orderOf_pos g).ne' hrd⟩
  intro h2
  rw [h2] at hrd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)

theorem psl2_card_dvd_of_fixed
    {p f r : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f)
    (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (hr : r.Prime) (hr2 : r ≠ 2)
    (α : MulAut PSL(2, GaloisField p f)) (hα : orderOf α = r)
    (S : Sylow 2 PSL(2, GaloisField p f))
    (hαS : ∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x)
    {H : Subgroup PSL(2, GaloisField p f)} (hH : ∀ x ∈ H, α x = x) :
    p ^ f = (p ^ (f / r)) ^ r ∧ 0 < f / r ∧
      Nat.card H ∣ p ^ (f / r) * ((p ^ (f / r)) ^ 2 - 1) / 2 := by
  obtain ⟨-, hrf, ⟨eα⟩⟩ := psl2_mulAut_of_centralizes_sylow_two hp hf h5 h8 hr hr2 α hα S hαS
  have hf' : 0 < f / r := Nat.div_pos (Nat.le_of_dvd hf hrf) hr.pos
  have hpow : p ^ f = (p ^ (f / r)) ^ r := by
    rw [← pow_mul, Nat.div_mul_cancel hrf]
  refine ⟨hpow, hf', ?_⟩
  have hK : Nat.card (GaloisField p (f / r)) = p ^ (f / r) := GaloisField.card p (f / r) hf'.ne'
  have hle : H ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) := fun x hx => hH x hx
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr eα.toEquiv] at h1
  have h2 := psl2_card_formula (GaloisField p (f / r)) (isOddPrimePower_of_card hK hp hf')
  rw [hK] at h2
  rw [← h2]
  exact h1

variable {L : Type} [Group L] [Finite L]

theorem IsTypeJR.mulAut_eq_one
    (hL : IsTypeJR L) (φ : MulAut L) (hφ : Odd (orderOf φ)) {ℓ : L}
    (hℓ : orderOf ℓ = 2) (hφC : ∀ x ∈ Subgroup.centralizer ({ℓ} : Set L), φ x = x) :
    φ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup L := hL.1
  have h2 : 2 ∣ Nat.card L := hℓ ▸ orderOf_dvd_natCard ℓ
  set C := Subgroup.centralizer ({ℓ} : Set L) with hC
  have hℓp : IsPGroup 2 (Subgroup.zpowers ℓ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hℓ, pow_one])
  obtain ⟨S, hS⟩ := hℓp.exists_le_sylow
  have hℓS : ℓ ∈ (S : Subgroup L) := hS (Subgroup.mem_zpowers ℓ)
  obtain ⟨hSel, hScard⟩ := hL.sylow_two h2 S
  have hSab' := hL.2.1 S
  have hSab : ∀ x ∈ (S : Subgroup L), ∀ y ∈ (S : Subgroup L), x * y = y * x :=
    fun x hx y hy => setLike_mul_comm hx hy
  have hSC : ∀ {u : L}, u ∈ (S : Subgroup L) →
      (S : Subgroup L) ≤ Subgroup.centralizer ({u} : Set L) := fun hu x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hSab _ hx _ hu)
  obtain ⟨s, hsS, hs1, hsℓ⟩ : ∃ s ∈ (S : Subgroup L), s ≠ 1 ∧ s ≠ ℓ := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ha1, hb1, hab⟩ :=
      exists_ne_one_ne_of_three_le_card (H := (S : Subgroup L)) (by rw [hScard]; norm_num)
    by_cases haℓ : a = ℓ
    · exact ⟨b, hb, fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext (show a = b by rw [haℓ, h]))⟩
    · exact ⟨a, ha, fun h => ha1 (Subtype.ext h), haℓ⟩
  have hs2 : orderOf s = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (S : Subgroup L)) s hsS) hs1
  obtain ⟨-, p, f, hp, M, hpodd, hf, h5, hMC, hMn, ⟨eM⟩, hCM⟩ := hL.2.2 s hs2
  have h8 := hL.mod_eight hs2 M hpodd hf h5 hMC hMn eM hCM
  obtain ⟨hSMcard, -, -, -⟩ := hL.sylow_two_of_mem S hsS hs2 M hpodd hf h5 hMC hMn eM hCM
  have hcardF : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  have : IsSimpleGroup M := eM.isSimpleGroup
  have hMnab : ∃ a b : M, a * b ≠ b * a := exists_mul_ne_mul_of_mulEquiv_psl2 hcardF eM
  obtain ⟨hMq, hZM⟩ := isQuasisimple_of_isSimpleGroup' hMnab
  set Cs := Subgroup.centralizer ({s} : Set L) with hCs
  have hMnormC : Cs ≤ Subgroup.normalizer (M : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMC).mp hMn
  have hφs : φ s = s := hφC s (hSC hℓS hsS)
  have hCsφ : Cs.map φ.toMonoidHom = Cs := by
    rw [hCs, map_centralizer_singleton_mulEquiv, hφs]
  set M' := M.map φ.toMonoidHom with hM'
  have hM'C : M' ≤ Cs := by
    rw [← hCsφ]
    exact Subgroup.map_mono hMC
  have hCM' : Cs ≤ Subgroup.normalizer (M' : Set L) := by
    rw [hM', ← Subgroup.map_equiv_normalizer_eq, ← hCsφ]
    exact Subgroup.map_mono hMnormC
  have hMM' : M' = M := by
    have hn : ((M ⊓ M').subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      exact (le_inf M.le_normalizer (hMC.trans hCM')).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ M').subgroupOf M) with h | h
    · exfalso
      have hbot : M ⊓ M' = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 : (⟨x, hx.1⟩ : M) ∈ (M ⊓ M').subgroupOf M := hx
        rw [h, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
      have hcomm : ⁅M', M⁆ = ⊥ := by
        rw [← le_bot_iff, ← hbot, Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        refine ⟨?_, ?_⟩
        · have h1 : x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ := rfl
          rw [h1]
          exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMnormC (hM'C hx)) y).mp hy)
            (M.inv_mem hy)
        · have h1 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [h1]
          exact M'.mul_mem hx
            ((Subgroup.mem_normalizer_iff.mp (hCM' (hMC hy)) x⁻¹).mp (M'.inv_mem hx))
      have hM'le : M' ≤ Subgroup.zpowers s := by
        rw [← hCM]
        exact le_inf hM'C (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      obtain ⟨a, b, hab⟩ := hMnab
      apply hab
      apply Subtype.ext
      apply φ.injective
      have ha : φ a ∈ Subgroup.zpowers s := hM'le ⟨a, a.2, rfl⟩
      have hb : φ b ∈ Subgroup.zpowers s := hM'le ⟨b, b.2, rfl⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← hi, ← hj, ← zpow_add,
        ← zpow_add, add_comm]
    · have h1 : M ≤ M' := by
        intro x hx
        have h2 : (⟨x, hx⟩ : M) ∈ (M ⊓ M').subgroupOf M := by
          rw [h]
          exact Subgroup.mem_top _
        exact h2.2
      have hcard : Nat.card M' = Nat.card M := Subgroup.card_map_of_injective φ.injective
      exact (Subgroup.eq_of_le_of_card_ge h1 hcard.le).symm
  have hℓM : ¬ M ≤ C := by
    intro h
    have h1 : ℓ ∈ Cs ⊓ Subgroup.centralizer (M : Set L) := by
      refine ⟨hSC hsS hℓS, ?_⟩
      show ℓ ∈ Subgroup.centralizer (M : Set L)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (h hx)
    rw [hCM] at h1
    rcases eq_one_or_eq_of_mem_zpowers hs2 h1 with h1 | h1
    · rw [h1, orderOf_one] at hℓ
      omega
    · exact hsℓ h1.symm
  have hSN : (S : Subgroup L) ≤ Subgroup.normalizer (M : Set L) := (hSC hsS).trans hMnormC
  obtain ⟨m, hmM, hm⟩ := exists_inner_of_isQuasisimple hL.2.1 M hMq S hSN ℓ hℓS
  have hℓℓ : ℓ * ℓ = 1 := by rw [← pow_two, ← hℓ, pow_orderOf_eq_one]
  have hm2 : (⟨m, hmM⟩ : M) ^ 2 = 1 := by
    have hc : (⟨m, hmM⟩ : M) ^ 2 ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hy1 := hm y y.2
      have hmy : m * (y : L) * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hmM y.2) (M.inv_mem hmM)
      have hy3 : ℓ * (ℓ * (y : L) * ℓ⁻¹) * ℓ⁻¹ = y := by
        calc ℓ * (ℓ * (y : L) * ℓ⁻¹) * ℓ⁻¹ = (ℓ * ℓ) * y * (ℓ * ℓ)⁻¹ := by group
          _ = y := by rw [hℓℓ]; group
      have hy2 : m * (m * (y : L) * m⁻¹) * m⁻¹ = y := by
        rw [← hm _ hmy, ← hy1]
        exact hy3
      simp only [Subgroup.coe_mul, pow_two]
      calc (y : L) * (m * m) = (m * (m * y * m⁻¹) * m⁻¹) * (m * m) := by rw [hy2]
        _ = m * m * y := by group
    rw [hZM, Subgroup.mem_bot] at hc
    exact hc
  have hm1 : (⟨m, hmM⟩ : M) ≠ 1 := by
    intro h1
    apply hℓM
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := hm x hx
    have h3 : m = 1 := congrArg Subtype.val h1
    rw [h3, one_mul, inv_one, mul_one] at h2
    calc x * ℓ = (ℓ * x * ℓ⁻¹) * ℓ := by rw [h2]
      _ = ℓ * x := by group
  have hmo : orderOf (⟨m, hmM⟩ : M) = 2 := orderOf_eq_prime hm2 hm1
  have hCMℓ : ∀ x : M, (x : L) ∈ C ↔ x ∈ Subgroup.centralizer ({⟨m, hmM⟩} : Set M) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hm x x.2
    constructor
    · intro h
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have h2 : ℓ * (x : L) * ℓ⁻¹ = x := by rw [← h, mul_inv_cancel_right]
      rw [h2] at h1
      calc (x : L) * m = (m * x * m⁻¹) * m := by rw [← h1]
        _ = m * x := by group
    · intro h
      have h2 : (x : L) * m = m * x := by
        have := congrArg Subtype.val h
        rwa [Subgroup.coe_mul, Subgroup.coe_mul] at this
      have h3 : m * (x : L) * m⁻¹ = x := by rw [← h2, mul_inv_cancel_right]
      rw [h3] at h1
      calc (x : L) * ℓ = (ℓ * x * ℓ⁻¹) * ℓ := by rw [h1]
        _ = ℓ * x := by group
  have hφM : ∀ x : M, φ x ∈ M := by
    intro x
    have h : φ x ∈ M' := ⟨x, x.2, rfl⟩
    rwa [hMM'] at h
  have hφM' : ∀ x : M, φ⁻¹ x ∈ M := by
    intro x
    have : (x : L) ∈ M' := hMM'.symm ▸ x.2
    obtain ⟨y, hy, hyx⟩ := this
    rw [← hyx, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
    exact hy
  let φM : MulAut M :=
    { toFun := fun x => ⟨φ x, hφM x⟩
      invFun := fun x => ⟨φ⁻¹ x, hφM' x⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ φ (x : L))
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ φ (x : L))
      map_mul' := fun x y => Subtype.ext (map_mul φ (x : L) (y : L)) }
  have hφMapply : ∀ x : M, ((φM x : M) : L) = φ x := fun x => rfl
  have hpowM : ∀ (k : ℕ) (x : M), (((φM ^ k) x : M) : L) = (φ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply, hφMapply, ih]
  have hφMord : Odd (orderOf φM) := by
    refine Odd.of_dvd_nat hφ (orderOf_dvd_of_pow_eq_one ?_)
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hpowM, pow_orderOf_eq_one]
    rfl
  have hφMC : ∀ x : M, x ∈ Subgroup.centralizer ({⟨m, hmM⟩} : Set M) → φM x = x := by
    intro x hx
    apply Subtype.ext
    rw [hφMapply]
    exact hφC (x : L) ((hCMℓ x).mpr hx)
  have hφM1 : φM = 1 := by
    by_contra hne
    obtain ⟨k, r, hr, hr2, hrk⟩ := exists_pow_orderOf_eq_prime hne hφMord
    set α := MulAut.congr eM (φM ^ k) with hα
    have hαord : orderOf α = r := by rw [hα, MulEquiv.orderOf_eq, hrk]
    have hαfix : ∀ x : M, (∀ j : ℕ, ((φM ^ j) x : M) = x) → α (eM x) = eM x := by
      intro x hx
      rw [hα]
      show eM ((φM ^ k) (eM.symm (eM x))) = eM x
      rw [MulEquiv.symm_apply_apply, hx k]
    have hpowfix : ∀ x : M, φM x = x → ∀ j : ℕ, (φM ^ j) x = x := by
      intro x hx j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ, MulAut.mul_apply, hx, ih]
    set SM := ((S : Subgroup L) ⊓ M).subgroupOf M with hSM
    have hSMcard' : Nat.card SM = 4 := by
      rw [hSM, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact hSMcard
    set SP := SM.map eM.toMonoidHom with hSP
    have hSPcard : Nat.card SP = 4 := by
      rw [hSP, Subgroup.card_map_of_injective eM.injective, hSMcard']
    have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
    obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField p f)))
    have hS₀ := psl2_sylow_two_card_eq_four (GaloisField p f) hK hpodd hf h8 S₀
    let SP' : Sylow 2 PSL(2, GaloisField p f) :=
      Sylow.ofCard SP (by rw [hSPcard, ← hS₀, S₀.card_eq_multiplicity])
    have hαSP : ∀ x ∈ (SP' : Subgroup PSL(2, GaloisField p f)), α x = x := by
      intro x hx
      rw [Sylow.coe_ofCard] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      apply hαfix
      apply hpowfix
      apply hφMC
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyS : (y : L) ∈ (S : Subgroup L) := (Subgroup.mem_subgroupOf.mp hy).1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have h1 : (y : L) ∈ C := hSC hℓS hyS
      have h2 := (hCMℓ y).mp h1
      have h3 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp h2)
      rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h3
    set H := (Subgroup.centralizer ({⟨m, hmM⟩} : Set M)).map eM.toMonoidHom with hH
    have hαH : ∀ x ∈ H, α x = x := by
      rintro _ ⟨y, hy, rfl⟩
      exact hαfix y (hpowfix y (hφMC y hy))
    obtain ⟨hpow, hf', hdvd⟩ := psl2_card_dvd_of_fixed hpodd hf h5 h8 hr hr2 α hαord SP' hαSP
      hαH
    have hHcard : p ^ f - 1 ≤ Nat.card H := by
      have hmo' : orderOf (eM ⟨m, hmM⟩) = 2 := by rw [MulEquiv.orderOf_eq, hmo]
      have hHeq : H = Subgroup.centralizer ({eM ⟨m, hmM⟩} : Set PSL(2, GaloisField p f)) :=
        map_centralizer_singleton_mulEquiv eM _
      rw [hHeq]
      have h1 := psl2_odd_centralizer_involution hpodd hf hmo'
      have hq : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
        have := Nat.odd_iff.mp (hpodd.pow (n := f))
        omega
      rcases hq with hq | hq
      · rw [(h1.1 hq).1]
      · rw [(h1.2 hq).1]
        omega
    set q₀ := p ^ (f / r) with hq₀
    have hq₀3 : 3 ≤ q₀ := by
      have h1 : 3 ≤ p := by
        have := (Fact.out : p.Prime).two_le
        rcases hpodd with ⟨k, hk⟩
        omega
      calc 3 ≤ p := h1
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (f / r) := Nat.pow_le_pow_right (by omega) hf'
    have hr3 : 3 ≤ r := by
      have := hr.two_le
      omega
    have hcube : q₀ ^ 3 ≤ p ^ f := by
      rw [hpow]
      exact Nat.pow_le_pow_right (by omega) hr3
    have hHpos : 0 < q₀ * (q₀ ^ 2 - 1) / 2 := by
      apply Nat.div_pos _ (by norm_num)
      have : 2 ≤ q₀ ^ 2 - 1 := by
        have : 9 ≤ q₀ ^ 2 := by nlinarith
        omega
      nlinarith
    have hle := Nat.le_of_dvd hHpos hdvd
    have hbound : q₀ * (q₀ ^ 2 - 1) ≤ q₀ ^ 3 := by
      have : q₀ * (q₀ ^ 2 - 1) ≤ q₀ * q₀ ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      calc q₀ * (q₀ ^ 2 - 1) ≤ q₀ * q₀ ^ 2 := this
        _ = q₀ ^ 3 := by ring
    have h27 : 27 ≤ q₀ ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ q₀ ^ 3 := Nat.pow_le_pow_left hq₀3 3
    omega
  have hφMfix : ∀ x ∈ M, φ x = x := by
    intro x hx
    have := congrArg (fun ψ : MulAut M => ((ψ ⟨x, hx⟩ : M) : L)) hφM1
    rw [hφMapply, MulAut.one_apply] at this
    exact this
  have hco := (hL.2.2 ℓ hℓ).1
  have htop : C ⊔ M = ⊤ :=
    hco.2 _ (lt_of_le_of_ne le_sup_left fun h => hℓM (le_sup_right.trans h.symm.le))
  have hle : C ⊔ M ≤ φ.toMonoidHom.eqLocus (MonoidHom.id L) :=
    sup_le (fun x hx => hφC x hx) (fun x hx => hφMfix x hx)
  apply MulEquiv.ext
  intro x
  have hx : x ∈ φ.toMonoidHom.eqLocus (MonoidHom.id L) := hle (htop ▸ Subgroup.mem_top x)
  exact hx

end CFSG.Walter
