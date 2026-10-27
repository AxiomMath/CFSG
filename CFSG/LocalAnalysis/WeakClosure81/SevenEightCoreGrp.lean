module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.ClassicalInvolution.SubnormalCommutator

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement Pointwise

variable {Q : Type*} [Group Q] [Finite Q]

private theorem seven_eight_core_grp_map_subtype_top (X : Subgroup Q) :
    (⊤ : Subgroup ↥X).map X.subtype = X := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

private theorem seven_eight_core_grp_dvd_sum_range_id {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ ∑ i ∈ Finset.range p, i := by
  have hcop : Nat.Coprime p 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact (hp.odd_of_ne_two hp2).not_two_dvd_nat
  have h2 : p ∣ (∑ i ∈ Finset.range p, i) * 2 := by
    rw [Finset.sum_range_id_mul_two]
    exact dvd_mul_right p (p - 1)
  exact hcop.dvd_of_dvd_mul_right h2

private theorem seven_eight_core_grp_mul_pow_of_commutator_central {G : Type*} [Group G]
    {x y z : G} (hyx : y * x = x * y * z) (hzx : z * x = x * z) (hzy : z * y = y * z) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * z ^ (∑ i ∈ Finset.range n, i) := by
  have hz : ∀ m : ℕ, y ^ m * x = x * y ^ m * z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * x = y * (y ^ m * x) := by rw [pow_succ', mul_assoc]
        _ = y * (x * y ^ m * z ^ m) := by rw [ih]
        _ = (y * x) * y ^ m * z ^ m := by group
        _ = x * y * z * y ^ m * z ^ m := by rw [hyx]
        _ = x * y * (z * y ^ m) * z ^ m := by group
        _ = x * y * (y ^ m * z) * z ^ m := by
            rw [(Commute.pow_right (show Commute z y from hzy) m).eq]
        _ = x * y ^ (m + 1) * z ^ (m + 1) := by rw [pow_succ', pow_succ']; group
  induction n with
  | zero => simp
  | succ n ih =>
    set t := ∑ i ∈ Finset.range n, i with ht
    have hzxt : Commute (z ^ t) x := Commute.pow_left hzx _
    have hzyt : Commute (z ^ (n + t)) y := Commute.pow_left hzy _
    rw [Finset.sum_range_succ, ← ht]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * z ^ t * (x * y) := by rw [ih]
      _ = x ^ n * y ^ n * (z ^ t * x) * y := by group
      _ = x ^ n * y ^ n * (x * z ^ t) * y := by rw [hzxt.eq]
      _ = x ^ n * (y ^ n * x) * z ^ t * y := by group
      _ = x ^ n * (x * y ^ n * z ^ n) * z ^ t * y := by rw [hz n]
      _ = x ^ (n + 1) * y ^ n * z ^ (n + t) * y := by rw [pow_succ, pow_add]; group
      _ = x ^ (n + 1) * y ^ n * (z ^ (n + t) * y) := by group
      _ = x ^ (n + 1) * y ^ n * (y * z ^ (n + t)) := by rw [hzyt.eq]
      _ = x ^ (n + 1) * y ^ (n + 1) * z ^ (t + n) := by rw [pow_succ, add_comm n t]; group

private theorem seven_eight_core_grp_conj_commutator_inv {v y : Q} (hv2 : v * v = 1) :
    v * ⁅y, v⁆ * v⁻¹ = (⁅y, v⁆)⁻¹ := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hmain : v * (y * v * y⁻¹ * v) * v = v * y * v * y⁻¹ := by
    calc v * (y * v * y⁻¹ * v) * v
        = v * y * v * y⁻¹ * (v * v) := by group
      _ = v * y * v * y⁻¹ := by rw [hv2, mul_one]
  rw [commutatorElement_inv, commutatorElement_def, hvinv, hmain, commutatorElement_def, hvinv]

private theorem seven_eight_core_grp_map_conj_eq_self {Z : Subgroup Q} {l : Q}
    (hl : l ∈ Subgroup.normalizer (Z : Set Q)) :
    Z.map (MulAut.conj l) = Z := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hl
  exact hl

private theorem seven_eight_core_grp_normalizer_le_normalizer_map {M : Subgroup Q}
    (K : Subgroup M) [K.Characteristic] :
    Subgroup.normalizer (M : Set Q) ≤ Subgroup.normalizer (K.map M.subtype : Set Q) := by
  have key : ∀ g ∈ Subgroup.normalizer (M : Set Q), ∀ x ∈ K.map M.subtype,
      g * x * g⁻¹ ∈ K.map M.subtype := by
    rintro g hg _ ⟨k, hk, rfl⟩
    set φ : MulAut M := M.normalizerMonoidHom ⟨g, hg⟩
    have hφ : K.map φ.toMonoidHom = K := characteristic_iff_map_eq.mp inferInstance φ
    have hk' : φ k ∈ K := by
      rw [← hφ]
      exact ⟨k, hk, rfl⟩
    exact ⟨φ k, hk', rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

private theorem seven_eight_core_grp_commutator_conj (Z : Subgroup Q) (v l : Q)
    (hl : l ∈ Subgroup.normalizer (Z : Set Q)) :
    ⁅Z, Subgroup.zpowers (l * v * l⁻¹)⁆ =
      (⁅Z, Subgroup.zpowers v⁆).map (MulAut.conj l) := by
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers,
    seven_eight_core_grp_map_conj_eq_self hl]
  show ⁅Z, Subgroup.zpowers (l * v * l⁻¹)⁆ = ⁅Z, Subgroup.zpowers (MulAut.conj l v)⁆
  rw [MulAut.conj_apply]

private def seven_eight_core_grp_fam (Lb Xb : Subgroup Q) (v : Q) : Lb → Subgroup Q :=
  fun l => ⁅Xb, Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹)⁆

private theorem seven_eight_core_grp_commutator_conj_Lb {Lb X : Subgroup Q} {v : Q}
    (hn : Lb ≤ Subgroup.normalizer (X : Set Q)) {l' : Q} (hl' : l' ∈ Lb) (l : Lb) :
    (seven_eight_core_grp_fam Lb X v l).map (MulAut.conj l') =
      seven_eight_core_grp_fam Lb X v (⟨l', hl'⟩ * l) := by
  show (⁅X, Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹)⁆).map
      (MulAut.conj l') =
    ⁅X, Subgroup.zpowers (((⟨l', hl'⟩ * l : Lb) : Q) * v *
      (((⟨l', hl'⟩ * l : Lb) : Q))⁻¹)⁆
  rw [← seven_eight_core_grp_commutator_conj (Z := X)
    (v := ((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹) (l := l') (hn hl')]
  rw [show (((⟨l', hl'⟩ * l : Lb) : Q) * v * (((⟨l', hl'⟩ * l : Lb) : Q))⁻¹) =
      l' * (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹) * l'⁻¹ from by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group]

private theorem seven_eight_core_grp_le_normalizer_commutator (H : Subgroup Q) :
    H ≤ Subgroup.normalizer (⁅H, H⁆ : Subgroup Q) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator,
    seven_eight_core_grp_map_conj_eq_self (Z := H) (Subgroup.le_normalizer hx)]

private theorem seven_eight_core_grp_commutator_commutator_le (H : Subgroup Q) :
    ⁅⁅H, H⁆, H⁆ ≤ ⁅H, H⁆ :=
  (Subgroup.le_normalizer_iff_commutator_le_left (H := H) (K := ⁅H, H⁆)).mp
    (seven_eight_core_grp_le_normalizer_commutator H)

private theorem seven_eight_core_grp_commutator_zpowers_eq_bot_iff (Z : Subgroup Q) (v : Q) :
    ⁅Z, Subgroup.zpowers v⁆ = ⊥ ↔ ∀ z ∈ Z, v * z = z * v := by
  constructor
  · intro h z hz
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hz)) v (Subgroup.mem_zpowers v)
  · intro h
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (h z hz) n).eq

structure IsMinCommInvariant (Lb Xb : Subgroup Q) (v : Q) : Prop where
  normalizes : Lb ≤ Subgroup.normalizer (Xb : Set Q)
  ne_bot : ⁅Xb, Subgroup.zpowers v⁆ ≠ ⊥
  minimal : ∀ Zb : Subgroup Q, Zb < Xb → Lb ≤ Subgroup.normalizer (Zb : Set Q) →
    ⁅Zb, Subgroup.zpowers v⁆ = ⊥

theorem exists_isMinCommInvariant_le {Lb Nb : Subgroup Q} {v : Q}
    (hN : Lb ≤ Subgroup.normalizer (Nb : Set Q)) (hne : ⁅Nb, Subgroup.zpowers v⁆ ≠ ⊥) :
    ∃ Xb : Subgroup Q, Xb ≤ Nb ∧ IsMinCommInvariant Lb Xb v := by
  classical
  have hex : ∃ n : ℕ, ∃ X : Subgroup Q,
      X ≤ Nb ∧ Lb ≤ Subgroup.normalizer (X : Set Q) ∧
        ⁅X, Subgroup.zpowers v⁆ ≠ ⊥ ∧ Nat.card X = n :=
    ⟨Nat.card Nb, Nb, le_rfl, hN, hne, rfl⟩
  obtain ⟨Xb, hXb_le, hXb_n, hXb_ne, hXb_card⟩ := Nat.find_spec hex
  refine ⟨Xb, hXb_le, hXb_n, hXb_ne, ?_⟩
  intro Zb hZ hZn
  by_contra hZne
  have hlt : Nat.card Zb < Nat.find hex := by
    rw [← hXb_card]
    exact Subgroup.card_lt_of_lt hZ
  exact Nat.find_min hex hlt ⟨Zb, hZ.le.trans hXb_le, hZn, hZne, rfl⟩

theorem IsMinCommInvariant.commutator_conj_eq_bot {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) {Zb : Subgroup Q} (hZ : Zb < Xb)
    (hZn : Lb ≤ Subgroup.normalizer (Zb : Set Q)) {l : Q} (hl : l ∈ Lb) :
    ⁅Zb, Subgroup.zpowers (l * v * l⁻¹)⁆ = ⊥ := by
  rw [seven_eight_core_grp_commutator_conj Zb v l (hZn hl), h.minimal Zb hZ hZn,
    Subgroup.map_bot]

theorem IsMinCommInvariant.commutator_conj_ne_bot {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) {l : Q} (hl : l ∈ Lb) :
    ⁅Xb, Subgroup.zpowers (l * v * l⁻¹)⁆ ≠ ⊥ := by
  rw [seven_eight_core_grp_commutator_conj Xb v l (h.normalizes hl)]
  exact fun hbot => h.ne_bot
    ((Subgroup.map_eq_bot_iff_of_injective (⁅Xb, Subgroup.zpowers v⁆)
      (MulAut.conj l).injective).mp hbot)

theorem IsMinCommInvariant.exists_prime_isPGroup {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) (hv2 : v * v = 1)
    (hodd : Odd (Nat.card Xb)) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p Xb := by
  classical
  have hXb_ne : Xb ≠ ⊥ := by
    intro hbot
    exact h.ne_bot (by rw [hbot]; simp)
  have hsolv : Group.IsSolvable ↥Xb := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let φ : MulAut ↥Xb := Xb.normalizerMonoidHom ⟨v, h.normalizes hv⟩
  have hφcoe : ∀ x : ↥Xb, ((φ x : ↥Xb) : Q) = v * (x : Q) * v⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Xb ⟨v, h.normalizes hv⟩ x
  have hφ2 : φ ^ 2 = 1 := by
    change (Xb.normalizerMonoidHom ⟨v, h.normalizes hv⟩) ^ 2 = 1
    have hvv : (⟨v, h.normalizes hv⟩ : Subgroup.normalizer (Xb : Set Q)) ^ 2 = 1 :=
      Subtype.ext (by simp [pow_two, hv2])
    rw [← map_pow, hvv, map_one]
  have hcoprime : Nat.Coprime 2 (Nat.card (fittingSubgroup ↥Xb)) := by
    rw [Nat.coprime_two_left]
    exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (fittingSubgroup ↥Xb))
  have hfit_top : fittingSubgroup ↥Xb = ⊤ := by
    by_contra hfit
    have hflt : fittingSubgroup ↥Xb < ⊤ := lt_of_le_of_ne le_top hfit
    have hFlt : (fittingSubgroup ↥Xb).map Xb.subtype < Xb := by
      have hh := (Subgroup.map_subtype_lt_map_subtype (G' := Xb)
        (H := fittingSubgroup ↥Xb) (K := ⊤)).mpr hflt
      rwa [seven_eight_core_grp_map_subtype_top] at hh
    have hFn : Lb ≤ Subgroup.normalizer
        (((fittingSubgroup ↥Xb).map Xb.subtype : Subgroup Q) : Set Q) :=
      h.normalizes.trans (seven_eight_core_grp_normalizer_le_normalizer_map (M := Xb)
        (fittingSubgroup ↥Xb))
    have hminF : ⁅(fittingSubgroup ↥Xb).map Xb.subtype, Subgroup.zpowers v⁆ = ⊥ :=
      h.minimal _ hFlt hFn
    have hfixed : ∀ x ∈ fittingSubgroup ↥Xb, φ x = x := by
      intro x hx
      have hxmem : (x : Q) ∈ (fittingSubgroup ↥Xb).map Xb.subtype :=
        Subgroup.mem_map_of_mem Xb.subtype hx
      have hcomm : v * (x : Q) = (x : Q) * v :=
        (Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hminF) hxmem))
          v (Subgroup.mem_zpowers v)
      refine Subtype.ext ?_
      rw [hφcoe]
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hphi1 : φ = 1 := CFSG.mulAut_eq_one_of_fixes_fittingSubgroup ↥Xb hsolv φ 2 hφ2
      hcoprime hfixed
    apply h.ne_bot
    rw [seven_eight_core_grp_commutator_zpowers_eq_bot_iff]
    intro x hx
    have hxfix : v * x * v⁻¹ = x := by
      have h1 : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hphi1]; rfl
      have h2 := congrArg Subtype.val h1
      rwa [hφcoe] at h2
    calc v * x = v * x * v⁻¹ * v := by group
      _ = x * v := by rw [hxfix]
  have hjoin : (⊤ : Subgroup ↥Xb) =
      ⨆ p : (Nat.card ↥Xb).primeFactors.attach, CFSG.pCore p.1.1 ↥Xb := by
    rw [← hfit_top, CFSG.fitting_eq_sup_pCore]
  by_cases hs : ∃ p : (Nat.card ↥Xb).primeFactors.attach,
      CFSG.pCore p.1.1 ↥Xb = ⊤
  · obtain ⟨p, hp_top⟩ := hs
    refine ⟨p.1.1, Nat.prime_of_mem_primeFactors p.1.2, ?_, ?_⟩
    · intro h2
      exact hodd.not_two_dvd_nat (h2 ▸ Nat.dvd_of_mem_primeFactors p.1.2)
    · haveI : Fact p.1.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
      have h1 : IsPGroup p.1.1 (⊤ : Subgroup ↥Xb) :=
        hp_top ▸ (CFSG.pCore_isPGroup : IsPGroup p.1.1 (CFSG.pCore p.1.1 ↥Xb))
      exact h1.of_equiv Subgroup.topEquiv
  · push Not at hs
    exfalso
    have hmap_join : (⨆ p : (Nat.card ↥Xb).primeFactors.attach,
        (CFSG.pCore p.1.1 ↥Xb).map Xb.subtype) = Xb := by
      rw [← Subgroup.map_iSup, ← hjoin, seven_eight_core_grp_map_subtype_top]
    apply h.ne_bot
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hmap_join]
    refine iSup_le fun p => ?_
    have hFne : (CFSG.pCore p.1.1 ↥Xb).map Xb.subtype ≠ Xb := by
      intro hEq
      refine hs p ?_
      apply Subgroup.map_injective Xb.subtype_injective
      rw [hEq, seven_eight_core_grp_map_subtype_top]
    have hFlt : (CFSG.pCore p.1.1 ↥Xb).map Xb.subtype < Xb :=
      lt_of_le_of_ne (Subgroup.map_subtype_le _) hFne
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.minimal _ hFlt (h.normalizes.trans (seven_eight_core_grp_normalizer_le_normalizer_map
      (M := Xb) (CFSG.pCore p.1.1 ↥Xb)))

theorem IsMinCommInvariant.conj_mem_centralizer_commutator {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) {p : ℕ} (hp : p.Prime) (hX : IsPGroup p Xb) {l : Q}
    (hl : l ∈ Lb) : l * v * l⁻¹ ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
  classical
  have hXb_ne : Xb ≠ ⊥ := by
    intro hbot
    exact h.ne_bot (by rw [hbot]; simp)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial ↥Xb := (Subgroup.nontrivial_iff_ne_bot Xb).mpr hXb_ne
  haveI : Group.IsNilpotent ↥Xb := hX.isNilpotent
  have hcomm : _root_.commutator ↥Xb < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Xb
  have hDlt : ⁅Xb, Xb⁆ < Xb := by
    have hh := (Subgroup.map_subtype_lt_map_subtype (G' := Xb)
      (H := _root_.commutator ↥Xb) (K := ⊤)).mpr hcomm
    simpa only [_root_.commutator, Subgroup.map_commutator,
      seven_eight_core_grp_map_subtype_top] using hh
  have hDn : Lb ≤ Subgroup.normalizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
    intro l' hl'
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simp only [Subgroup.map_commutator]
    rw [seven_eight_core_grp_map_conj_eq_self (h.normalizes hl')]
  have hDw : ⁅(⁅Xb, Xb⁆ : Subgroup Q), Subgroup.zpowers (l * v * l⁻¹)⁆ = ⊥ :=
    h.commutator_conj_eq_bot hDlt hDn hl
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hDw
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact ((Subgroup.mem_centralizer_iff.mp (hDw hd)) (l * v * l⁻¹)
    (Subgroup.mem_zpowers _)).symm

private theorem seven_eight_core_grp_T_le {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) :
    (⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l) ≤ Xb := by
  refine iSup_le fun l => ?_
  show ⁅Xb, Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹)⁆ ≤ Xb
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hlN : ((l : Lb) : Q) ∈ Subgroup.normalizer (Xb : Set Q) := h.normalizes l.2
  have hvN : v ∈ Subgroup.normalizer (Xb : Set Q) := h.normalizes hv
  have hdN : ((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹ ∈
      Subgroup.normalizer (Xb : Set Q) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hvN) (Subgroup.inv_mem _ hlN)
  have hmem : b * a⁻¹ * b⁻¹ ∈ Xb :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hdN hb) a⁻¹).mp
      (Xb.inv_mem ha)
  have : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [this]
  exact Xb.mul_mem ha hmem

private theorem seven_eight_core_grp_T_normalizer {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) :
    Lb ≤ Subgroup.normalizer
      (((⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l) : Subgroup Q) : Set Q) := by
  intro l' hl'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun l => ?_
    rw [seven_eight_core_grp_commutator_conj_Lb (v := v) h.normalizes hl' l]
    exact le_iSup _ _
  · refine iSup_le fun l => ?_
    have hmap := seven_eight_core_grp_commutator_conj_Lb (v := v) h.normalizes hl'
      (⟨l', hl'⟩⁻¹ * l)
    rw [show (⟨l', hl'⟩ * (⟨l', hl'⟩⁻¹ * l) : Lb) = l from by group] at hmap
    rw [← hmap]
    let g : Lb → Subgroup Q := fun i => (seven_eight_core_grp_fam Lb Xb v i).map (MulAut.conj l')
    change g (⟨l', hl'⟩⁻¹ * l) ≤ ⨆ i, g i
    exact le_iSup g _

private theorem seven_eight_core_grp_T_eq {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) (hv2 : v * v = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p Xb) :
    (⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l) = Xb := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hoddX : Odd (Nat.card Xb) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hzv : Subgroup.zpowers v ≤ Subgroup.normalizer (Xb : Set Q) :=
    Subgroup.zpowers_le.mpr (h.normalizes hv)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers v)) (Nat.card Xb) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv2))
      (Nat.coprime_two_left.mpr hoddX)
  by_contra hne
  have hlt : (⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l) < Xb :=
    lt_of_le_of_ne (seven_eight_core_grp_T_le h hv) hne
  have hminT : ⁅(⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l), Subgroup.zpowers v⁆ = ⊥ :=
    h.minimal _ hlt (seven_eight_core_grp_T_normalizer h hv)
  have hle : ⁅Xb, Subgroup.zpowers v⁆ ≤ ⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l := by
    have h := le_iSup (seven_eight_core_grp_fam Lb Xb v) (1 : Lb)
    rw [show seven_eight_core_grp_fam Lb Xb v 1 = ⁅Xb, Subgroup.zpowers v⁆ from by
      simp [seven_eight_core_grp_fam]] at h
    exact h
  have hbot : ⁅Xb, Subgroup.zpowers v⁆ = ⊥ := by
    have h1 : ⁅Xb, Subgroup.zpowers v⁆ ≤
        ⁅⁅Xb, Subgroup.zpowers v⁆, Subgroup.zpowers v⁆ :=
      CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime Xb
        (Subgroup.zpowers v) hzv hcop
    have h2 : ⁅⁅Xb, Subgroup.zpowers v⁆, Subgroup.zpowers v⁆ ≤
        ⁅(⨆ l : Lb, seven_eight_core_grp_fam Lb Xb v l), Subgroup.zpowers v⁆ :=
      Subgroup.commutator_mono hle le_rfl
    rw [hminT] at h2
    exact le_bot_iff.mp (h1.trans h2)
  exact h.ne_bot hbot

private theorem seven_eight_core_grp_commutator_central {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) (hv2 : v * v = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p Xb) :
    Xb ≤ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hXb_ne : Xb ≠ ⊥ := by
    intro hbot
    exact h.ne_bot (by rw [hbot]; simp)
  have hTeq := seven_eight_core_grp_T_eq h hv hv2 hp hp2 hX
  have hDlt : ⁅Xb, Xb⁆ < Xb := by
    haveI : Nontrivial ↥Xb := (Subgroup.nontrivial_iff_ne_bot Xb).mpr hXb_ne
    haveI : Group.IsNilpotent ↥Xb := hX.isNilpotent
    have hcomm : _root_.commutator ↥Xb < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Xb
    have hh := (Subgroup.map_subtype_lt_map_subtype (G' := Xb)
      (H := _root_.commutator ↥Xb) (K := ⊤)).mpr hcomm
    simpa only [_root_.commutator, Subgroup.map_commutator,
      seven_eight_core_grp_map_subtype_top] using hh
  have hDn : Lb ≤ Subgroup.normalizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
    intro l' hl'
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simp only [Subgroup.map_commutator]
    rw [seven_eight_core_grp_map_conj_eq_self (h.normalizes hl')]
  conv_lhs => rw [← hTeq]
  refine iSup_le fun l => ?_
  change ⁅Xb, Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹)⁆ ≤
    Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q)
  have hdcent : ((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹ ∈
      Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) :=
    h.conj_mem_centralizer_commutator hp hX l.2
  have hzd : ⁅Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹),
      (⁅Xb, Xb⁆ : Subgroup Q)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hdcent)
  have hDd : ⁅(⁅Xb, Xb⁆ : Subgroup Q),
      Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left
      (Subgroup.mem_centralizer_iff.mp hdcent z hz).symm n).eq
  have h1 : ⁅⁅Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹),
      (⁅Xb, Xb⁆ : Subgroup Q)⁆, Xb⁆ = ⊥ := by
    rw [hzd, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅(⁅Xb, Xb⁆ : Subgroup Q), Xb⁆,
      Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹)⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono
      (seven_eight_core_grp_commutator_commutator_le Xb) le_rfl).trans hDd.le)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := Xb) (H₂ := Subgroup.zpowers (((l : Lb) : Q) * v * (((l : Lb) : Q))⁻¹))
      (H₃ := (⁅Xb, Xb⁆ : Subgroup Q)) h1 h2)

theorem IsMinCommInvariant.commutator_commutator_eq_one {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) (hv2 : v * v = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : IsPGroup p Xb) :
    ∀ x ∈ Xb, ∀ y ∈ Xb, ∀ z ∈ Xb, ⁅⁅x, y⁆, z⁆ = 1 := by
  have hcentral := seven_eight_core_grp_commutator_central h hv hv2 hp hp2 hX
  intro x hx y hy z hz
  have hzD : z ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := hcentral hz
  have hmem : ⁅x, y⁆ ∈ (⁅Xb, Xb⁆ : Subgroup Q) := Subgroup.commutator_mem_commutator hx hy
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_centralizer_iff.mp hzD) ⁅x, y⁆ hmem)

theorem IsMinCommInvariant.pow_eq_one {Lb Xb : Subgroup Q} {v : Q}
    (h : IsMinCommInvariant Lb Xb v) (hv : v ∈ Lb) (hv2 : v * v = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : IsPGroup p Xb) (hcl : ∀ x ∈ Xb, ∀ y ∈ Xb, ∀ z ∈ Xb, ⁅⁅x, y⁆, z⁆ = 1) :
    ∀ x ∈ Xb, x ^ p = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Ω : Subgroup Q :=
    { carrier := {x | x ∈ Xb ∧ x ^ p = 1},
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨hxX, hxp⟩ := hx
        obtain ⟨hyX, hyp⟩ := hy
        refine ⟨Xb.mul_mem hxX hyX, ?_⟩
        set z : Q := ⁅y⁻¹, x⁻¹⁆ with hz
        have hyx : y * x = x * y * z := by rw [hz, commutatorElement_def]; group
        have hzx : z * x = x * z := by
          have h1 : ⁅z, x⁆ = 1 := by
            rw [hz]
            exact hcl y⁻¹ (Xb.inv_mem hyX) x⁻¹ (Xb.inv_mem hxX) x hxX
          exact commutatorElement_eq_one_iff_mul_comm.mp h1
        have hzy : z * y = y * z := by
          have h1 : ⁅z, y⁆ = 1 := by
            rw [hz]
            exact hcl y⁻¹ (Xb.inv_mem hyX) x⁻¹ (Xb.inv_mem hxX) y hyX
          exact commutatorElement_eq_one_iff_mul_comm.mp h1
        have hformula := seven_eight_core_grp_mul_pow_of_commutator_central hyx hzx hzy p
        have hzp : z ^ p = 1 := by
          have hcomm : Commute x⁻¹ z := by
            rw [hz]
            have h1 : Commute x ⁅y⁻¹, x⁻¹⁆ :=
              (commutatorElement_eq_one_iff_mul_comm.mp
                (hcl y⁻¹ (Xb.inv_mem hyX) x⁻¹ (Xb.inv_mem hxX) x hxX)).symm
            exact h1.inv_left
          rw [hz, Commute.commutatorElement_pow_right hcomm p, inv_pow, hxp, inv_one,
            commutatorElement_one_right]
        obtain ⟨t, ht⟩ := seven_eight_core_grp_dvd_sum_range_id hp hp2
        rw [hformula, hxp, hyp, one_mul, one_mul, ht, pow_mul, hzp, one_pow]
      one_mem' := ⟨Xb.one_mem, one_pow p⟩,
      inv_mem' := fun {x} hx => by
        obtain ⟨hxX, hxp⟩ := hx
        exact ⟨Xb.inv_mem hxX, by rw [inv_pow, hxp, inv_one]⟩ }
  have hΩ_le : Ω ≤ Xb := fun _ hx => hx.1
  have hΩn : Lb ≤ Subgroup.normalizer (Ω : Set Q) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨hyX, hyp⟩ := hy
      refine ⟨(Subgroup.mem_normalizer_iff.mp (h.normalizes hl) y).mp hyX, ?_⟩
      rw [← MulAut.conj_apply, ← map_pow, hyp, map_one]
    · intro hy
      obtain ⟨hyX, hyp⟩ := hy
      refine ⟨(Subgroup.mem_normalizer_iff.mp (h.normalizes hl) y).mpr hyX, ?_⟩
      have hyeq : y = MulAut.conj l⁻¹ (l * y * l⁻¹) := by rw [MulAut.conj_apply]; group
      rw [hyeq, ← map_pow, hyp, map_one]
  by_cases hΩX : Ω = Xb
  · intro x hx
    have hxΩ : x ∈ Ω := by rwa [hΩX]
    exact hxΩ.2
  · have hΩlt : Ω < Xb := lt_of_le_of_ne hΩ_le hΩX
    have hvΩ : ∀ x ∈ Ω, v * x = x * v :=
      (seven_eight_core_grp_commutator_zpowers_eq_bot_iff Ω v).mp (h.minimal Ω hΩlt hΩn)
    have hex : ∃ y ∈ Xb, v * y ≠ y * v := by
      by_contra hnot
      push Not at hnot
      exact h.ne_bot ((seven_eight_core_grp_commutator_zpowers_eq_bot_iff Xb v).mpr hnot)
    obtain ⟨y, hyX, hvy⟩ := hex
    set w : Q := ⁅y, v⁆ with hw
    have hwne : w ≠ 1 := by
      intro h1
      exact hvy (commutatorElement_eq_one_iff_mul_comm.mp (by rwa [hw] at h1)).symm
    have hwX : w ∈ Xb := by
      have hb : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
      have hmem : v * y⁻¹ * v⁻¹ ∈ Xb :=
        (Subgroup.mem_normalizer_iff.mp
          (Subgroup.zpowers_le.mpr (h.normalizes hv) hb) y⁻¹).mp (Xb.inv_mem hyX)
      have : ⁅y, v⁆ = y * (v * y⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
      rw [hw, this]
      exact Xb.mul_mem hyX hmem
    have hwinv : v * w * v⁻¹ = w⁻¹ := by
      rw [hw]
      exact seven_eight_core_grp_conj_commutator_inv hv2
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hX ⟨w, hwX⟩
    have hkw : orderOf w = p ^ k := by
      rw [← Subgroup.orderOf_mk w hwX]
      exact hk
    have hkpos : 0 < k := by
      by_contra hk0
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkz, pow_zero] at hkw
      exact hwne (orderOf_eq_one_iff.mp hkw)
    have hpk : p ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ' p (k - 1), Nat.sub_add_cancel hkpos]
    have hwp : (w ^ p ^ (k - 1)) ^ p = 1 := by
      rw [← pow_mul, show p ^ (k - 1) * p = p ^ k from by rw [mul_comm, ← hpk],
        ← hkw, pow_orderOf_eq_one]
    have hw'ne : w ^ p ^ (k - 1) ≠ 1 := by
      intro h1
      have hdvd : p ^ k ∣ p ^ (k - 1) := by
        rw [← hkw]
        exact orderOf_dvd_of_pow_eq_one h1
      exact Nat.not_dvd_of_pos_of_lt (pow_pos hp.pos (k - 1))
        (Nat.pow_lt_pow_right hp.one_lt (Nat.sub_lt hkpos one_pos)) hdvd
    have hord' : orderOf (w ^ p ^ (k - 1)) = p := orderOf_eq_prime hwp hw'ne
    have hmemΩ : w ^ p ^ (k - 1) ∈ Ω := ⟨Xb.pow_mem hwX _, hwp⟩
    have hcentral' : v * (w ^ p ^ (k - 1)) = (w ^ p ^ (k - 1)) * v := hvΩ _ hmemΩ
    have hinv' : v * (w ^ p ^ (k - 1)) * v⁻¹ = (w ^ p ^ (k - 1))⁻¹ := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hwinv, inv_pow]
    have hw'eq : w ^ p ^ (k - 1) = (w ^ p ^ (k - 1))⁻¹ :=
      (show w ^ p ^ (k - 1) = v * (w ^ p ^ (k - 1)) * v⁻¹ from by
        rw [hcentral']; group).trans hinv'
    have horder : orderOf (w ^ p ^ (k - 1)) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      nth_rewrite 2 [hw'eq]
      rw [mul_inv_cancel]
    have hp2' : p = 2 := by
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) (hord' ▸ horder)
      exact le_antisymm hle hp.two_le
    exact (hp2 hp2').elim

end CFSG.LocalAnalysis.WeakClosure81
