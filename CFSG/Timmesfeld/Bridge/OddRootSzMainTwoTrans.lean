module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
public import CFSG.Open.LocalVocabulary
import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {Ω : Type} [Finite Ω] {X T : Subgroup (Equiv.Perm Ω)} {α : Ω}

structure TwoTransHyp (X T : Subgroup (Equiv.Perm Ω)) (α : Ω) : Prop where
  two_trans : ∀ β γ β' γ' : Ω, β ≠ γ → β' ≠ γ' → ∃ x ∈ X, x β = β' ∧ x γ = γ'
  le : T ≤ X
  fix : ∀ t ∈ T, t α = α
  normal : ∀ x ∈ X, x α = α → ∀ t ∈ T, x * t * x⁻¹ ∈ T
  elemAb : CFSG.Open.IsElemAbelian 2 T
  four_le : 4 ≤ Nat.card T
  semireg : ∀ t ∈ T, ∀ β : Ω, β ≠ α → t β = β → t = 1

@[expose] def twoTransD (X T : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {s | s ≠ 1 ∧ ∃ x ∈ X, ∃ t ∈ T, s = x * t * x⁻¹}

@[expose] def twoTransY (X T : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure (twoTransD X T)

omit [Finite Ω] in
theorem le_twoTransY : T ≤ twoTransY X T := by
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]
    exact (twoTransY X T).one_mem
  · exact Subgroup.subset_closure ⟨ht1, 1, X.one_mem, t, ht, by simp⟩

omit [Finite Ω] in
private lemma conj_mem_twoTransD {x s : Equiv.Perm Ω} (hx : x ∈ X)
    (hs : s ∈ twoTransD X T) : x * s * x⁻¹ ∈ twoTransD X T := by
  obtain ⟨hs1, y, hy, t, ht, rfl⟩ := hs
  refine ⟨?_, x * y, X.mul_mem hx hy, t, ht, by group⟩
  intro h1
  apply hs1
  have := congrArg (fun z => x⁻¹ * z * x) h1
  simpa [mul_assoc] using this

omit [Finite Ω] in
theorem conj_mem_twoTransY {x y : Equiv.Perm Ω} (hx : x ∈ X)
    (hy : y ∈ twoTransY X T) : x * y * x⁻¹ ∈ twoTransY X T := by
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact Subgroup.subset_closure (conj_mem_twoTransD hx hs)
  | one => simpa using (twoTransY X T).one_mem
  | mul a b ha hb iha ihb =>
      have he : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [he]
      exact (twoTransY X T).mul_mem iha ihb
  | inv a ha iha =>
      have he : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [he]
      exact (twoTransY X T).inv_mem iha

namespace TwoTransHyp

private lemma t_mul_self (h : TwoTransHyp X T α) {t : Equiv.Perm Ω} (ht : t ∈ T) :
    t * t = 1 := by
  have := h.elemAb.2 t ht
  simpa [pow_two] using this

private lemma isPGroup_T (h : TwoTransHyp X T α) : IsPGroup 2 T :=
  CFSG.Timmesfeld.Bridge.OddLocal.isPGroup_two_of_mul_self fun t ht => h.t_mul_self ht

private lemma conj_unique_fixed (h : TwoTransHyp X T α) {x : Equiv.Perm Ω}
    {t : Equiv.Perm Ω} (ht : t ∈ T) (ht1 : t ≠ 1) :
    ∃! β : Ω, (x * t * x⁻¹) β = β := by
  refine ⟨x α, ?_, ?_⟩
  · simp [mul_assoc, h.fix t ht]
  · intro β hβ
    have h1 : t (x⁻¹ β) = x⁻¹ β := by
      have := congrArg (⇑x⁻¹) hβ
      simpa [Equiv.Perm.mul_apply] using this
    by_cases hxα : x⁻¹ β = α
    · calc β = x (x⁻¹ β) := (x.apply_symm_apply β).symm
        _ = x α := by rw [hxα]
    · exact absurd (h.semireg t ht (x⁻¹ β) hxα h1) ht1

lemma exists_ne_one (h : TwoTransHyp X T α) : ∃ t ∈ T, t ≠ 1 := by
  have hnt : Nontrivial T :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (by norm_num) h.four_le)
  obtain ⟨t, ht1⟩ := exists_ne (1 : T)
  exact ⟨t, t.2, fun h1 => ht1 (Subtype.ext h1)⟩

private lemma exists_mem_X_map_alpha (h : TwoTransHyp X T α) (β : Ω) :
    ∃ x ∈ X, x α = β := by
  by_cases hβ : β = α
  · exact ⟨1, X.one_mem, by simp [hβ]⟩
  · obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
    obtain ⟨δ, hδ⟩ : ∃ δ, t δ ≠ δ := by
      by_contra hc
      push Not at hc
      exact ht1 (Equiv.ext hc)
    have hδα : δ ≠ α := fun he => hδ (he ▸ h.fix t ht)
    obtain ⟨x, hx, hxα, -⟩ := h.two_trans α δ β α (Ne.symm hδα) hβ
    exact ⟨x, hx, hxα⟩

noncomputable def pointRep (h : TwoTransHyp X T α) (β : Ω) : Equiv.Perm Ω :=
  Classical.choose (h.exists_mem_X_map_alpha β)

lemma pointRep_mem (h : TwoTransHyp X T α) (β : Ω) : h.pointRep β ∈ X :=
  (Classical.choose_spec (h.exists_mem_X_map_alpha β)).1

lemma pointRep_alpha (h : TwoTransHyp X T α) (β : Ω) : h.pointRep β α = β :=
  (Classical.choose_spec (h.exists_mem_X_map_alpha β)).2

lemma mul_self_of_mem_twoTransD (h : TwoTransHyp X T α) {s : Equiv.Perm Ω}
    (hs : s ∈ twoTransD X T) : s * s = 1 := by
  obtain ⟨-, x, hx, t, ht, rfl⟩ := hs
  rw [show (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, h.t_mul_self ht]
  group

private lemma twoTransD_subset_X (h : TwoTransHyp X T α) : twoTransD X T ⊆ X := by
  rintro s ⟨-, x, hx, t, ht, rfl⟩
  exact X.mul_mem (X.mul_mem hx (h.le ht)) (X.inv_mem hx)

lemma twoTransY_le_X (h : TwoTransHyp X T α) : twoTransY X T ≤ X :=
  (Subgroup.closure_le X).mpr h.twoTransD_subset_X

noncomputable def tSub (h : TwoTransHyp X T α) (β : Ω) : Subgroup (Equiv.Perm Ω) :=
  T.map (MulAut.conj (h.pointRep β)).toMonoidHom

lemma mem_tSub_iff (h : TwoTransHyp X T α) {s : Equiv.Perm Ω} {β : Ω} :
    s ∈ h.tSub β ↔ ∃ t ∈ T, h.pointRep β * t * (h.pointRep β)⁻¹ = s := by
  simp [tSub, Subgroup.mem_map, MulAut.conj_apply]

lemma tSub_eq_conj (h : TwoTransHyp X T α) {β : Ω} {x : Equiv.Perm Ω} (hx : x ∈ X)
    (hxα : x α = β) : h.tSub β = T.map (MulAut.conj x).toMonoidHom := by
  let g := h.pointRep β
  have hgX : g ∈ X := h.pointRep_mem β
  have hgα : g α = β := h.pointRep_alpha β
  let n := x⁻¹ * g
  have hnX : n ∈ X := X.mul_mem (X.inv_mem hx) hgX
  have hnα : n α = α := by
    calc n α = x⁻¹ (g α) := rfl
      _ = x⁻¹ β := by rw [hgα]
      _ = x⁻¹ (x α) := by rw [hxα]
      _ = α := x.symm_apply_apply α
  have hninvα : (n⁻¹) α = α := by
    have := congrArg (⇑n⁻¹) hnα
    simpa using this.symm
  have hmap : T.map (MulAut.conj n).toMonoidHom = T := by
    apply le_antisymm
    · intro t ht
      rw [Subgroup.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact h.normal n hnX hnα u hu
    · intro t ht
      have hmem : n⁻¹ * t * (n⁻¹)⁻¹ ∈ T :=
        h.normal n⁻¹ (X.inv_mem hnX) hninvα t ht
      exact Subgroup.mem_map.mpr ⟨n⁻¹ * t * (n⁻¹)⁻¹, hmem, by
        change n * (n⁻¹ * t * (n⁻¹)⁻¹) * n⁻¹ = t
        group⟩
  have hg_eq : h.pointRep β = x * n := by
    show h.pointRep β = x * (x⁻¹ * h.pointRep β)
    group
  rw [tSub, hg_eq]
  calc
    T.map (MulAut.conj (x * n)).toMonoidHom
        = T.map ((MulAut.conj x).toMonoidHom.comp (MulAut.conj n).toMonoidHom) := rfl
    _ = (T.map (MulAut.conj n).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = T.map (MulAut.conj x).toMonoidHom := by rw [hmap]

private lemma tSub_fix (h : TwoTransHyp X T α) {s : Equiv.Perm Ω} {β : Ω}
    (hs : s ∈ h.tSub β) : s β = β := by
  rw [mem_tSub_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hg : (h.pointRep β)⁻¹ β = α := by
    simpa [h.pointRep_alpha β] using (h.pointRep β).symm_apply_apply α
  calc (h.pointRep β * t * (h.pointRep β)⁻¹) β
      = h.pointRep β (t ((h.pointRep β)⁻¹ β)) := rfl
    _ = h.pointRep β (t α) := by rw [hg]
    _ = h.pointRep β α := by rw [h.fix t ht]
    _ = β := h.pointRep_alpha β

lemma tSub_unique_fixed (h : TwoTransHyp X T α) {s : Equiv.Perm Ω} {β : Ω}
    (hs : s ∈ h.tSub β) (hs1 : s ≠ 1) : ∀ γ : Ω, s γ = γ → γ = β := by
  rw [mem_tSub_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hs1
    rw [ht1, mul_one]
    group
  intro γ hγ
  have h1 : t ((h.pointRep β)⁻¹ γ) = (h.pointRep β)⁻¹ γ := by
    have := congrArg (⇑(h.pointRep β)⁻¹) hγ
    simpa [Equiv.Perm.mul_apply] using this
  by_cases hg : (h.pointRep β)⁻¹ γ = α
  · calc γ = h.pointRep β ((h.pointRep β)⁻¹ γ) := ((h.pointRep β).apply_symm_apply γ).symm
      _ = h.pointRep β α := by rw [hg]
      _ = β := h.pointRep_alpha β
  · exact absurd (h.semireg t ht _ hg h1) ht1

lemma tSub_subset_twoTransD (h : TwoTransHyp X T α) {s : Equiv.Perm Ω} {β : Ω}
    (hs : s ∈ h.tSub β) (hs1 : s ≠ 1) : s ∈ twoTransD X T := by
  rw [mem_tSub_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨hs1, h.pointRep β, h.pointRep_mem β, t, ht, rfl⟩

private lemma mem_tSub_of_mem_twoTransD_of_fixed (h : TwoTransHyp X T α) {s : Equiv.Perm Ω}
    {β : Ω} (hs : s ∈ twoTransD X T) (hβ : s β = β) : s ∈ h.tSub β := by
  obtain ⟨hs1, x, hx, t, ht, rfl⟩ := hs
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hs1
    rw [ht1, mul_one]
    group
  rcases h.conj_unique_fixed ht ht1 with ⟨γ, hγ, huniq⟩
  have hfix : (x * t * x⁻¹) (x α) = x α := by
    simp [mul_assoc, h.fix t ht]
  have hxβ : x α = β :=
    (huniq (x α) hfix).trans (huniq β (by simpa using hβ)).symm
  rw [tSub_eq_conj h hx hxβ]
  exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩

theorem odd_card (h : TwoTransHyp X T α) : Odd (Nat.card Ω) := by
  have hfix : MulAction.fixedPoints T Ω = {α} := by
    ext β
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hβ
      by_contra hne
      obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
      exact ht1 (h.semireg t ht β hne (by simpa using hβ ⟨t, ht⟩))
    · intro hβ t
      subst hβ
      simpa [Subgroup.smul_def] using h.fix (t : Equiv.Perm Ω) t.2
  have hcard : Nat.card (MulAction.fixedPoints T Ω) = 1 := by
    rw [hfix]
    simp
  have hmod := h.isPGroup_T.card_modEq_card_fixedPoints (α := Ω)
  rw [hcard] at hmod
  rw [Nat.odd_iff]
  simpa [Nat.ModEq] using hmod

theorem exists_unique_fixed (h : TwoTransHyp X T α) {s : Equiv.Perm Ω}
    (hs : s ∈ twoTransD X T) : ∃! β : Ω, s β = β := by
  obtain ⟨hs1, x, hx, t, ht, rfl⟩ := hs
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hs1
    rw [ht1, mul_one]
    group
  exact h.conj_unique_fixed ht ht1

private lemma commute_of_mem_tSub (h : TwoTransHyp X T α) {β : Ω} {s s' : Equiv.Perm Ω}
    (hs : s ∈ h.tSub β) (hs' : s' ∈ h.tSub β) : Commute s s' := by
  rw [mem_tSub_iff] at hs hs'
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨t', ht', rfl⟩ := hs'
  have hc : Commute t t' := by
    have := h.elemAb.1.is_comm.comm ⟨t, ht⟩ ⟨t', ht'⟩
    exact congrArg Subtype.val this
  exact hc.conj (h.pointRep β)

lemma conj_mem_tSub (h : TwoTransHyp X T α) {x s : Equiv.Perm Ω} (hx : x ∈ X)
    {β : Ω} (hs : s ∈ h.tSub β) : x * s * x⁻¹ ∈ h.tSub (x β) := by
  rw [mem_tSub_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [tSub_eq_conj h (X.mul_mem hx (h.pointRep_mem β)) (by simp [h.pointRep_alpha β])]
  exact Subgroup.mem_map.mpr ⟨t, ht, by
    change (x * h.pointRep β) * t * (x * h.pointRep β)⁻¹ =
      x * (h.pointRep β * t * (h.pointRep β)⁻¹) * x⁻¹
    group⟩

private lemma commute_of_mem_twoTransD_of_same_fixed (h : TwoTransHyp X T α)
    {s s' : Equiv.Perm Ω} {β : Ω} (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T)
    (hβ : s β = β) (hβ' : s' β = β) : Commute s s' :=
  h.commute_of_mem_tSub (h.mem_tSub_of_mem_twoTransD_of_fixed hs hβ)
    (h.mem_tSub_of_mem_twoTransD_of_fixed hs' hβ')

private lemma even_order_conj_data (h : TwoTransHyp X T α) {s s' : Equiv.Perm Ω}
    (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T)
    (hodd : Even (orderOf (s * s'))) :
    ∃ (b k : ℕ) (u' : Equiv.Perm Ω),
      Odd b ∧ b = 2 * k + 1 ∧ u' = s * (s * s') ^ b ∧
      u' = (s * s') ^ (-(k : ℤ)) * s' * ((s * s') ^ (-(k : ℤ)))⁻¹ ∧
      orderOf ((s * s') ^ b) = ordProj[2] (orderOf (s * s')) ∧
      ((s * s') ^ b) ^ (2 ^ (orderOf (s * s')).factorization 2) = 1 ∧
      s * s = 1 ∧ s' * s' = 1 := by
  have hs2 : s * s = 1 := h.mul_self_of_mem_twoTransD hs
  have hs'2 : s' * s' = 1 := h.mul_self_of_mem_twoTransD hs'
  set ρ : Equiv.Perm Ω := s * s' with hρdef
  set m : ℕ := orderOf ρ with hmdef
  set b : ℕ := ordCompl[2] m with hbdef
  have hm0 : m ≠ 0 := by rw [hmdef]; exact (orderOf_pos ρ).ne'
  have hb_odd : Odd b := by
    rw [hbdef]
    exact Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact Nat.not_dvd_ordCompl Nat.prime_two hm0)
  have hb_dvd : b ∣ m := by rw [hbdef]; exact Nat.ordCompl_dvd m 2
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (by
    intro hb0
    rw [hb0] at hb_dvd
    exact hm0 (Nat.eq_zero_of_zero_dvd hb_dvd))
  have hfac : 0 < m.factorization 2 := by
    rw [hmdef]
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm0 (even_iff_two_dvd.mp hodd)
  have hproj_ge : 2 ≤ ordProj[2] m := by
    rw [show ordProj[2] m = 2 ^ m.factorization 2 from rfl]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m.factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  have hord_pow : orderOf (ρ ^ b) = ordProj[2] m := by
    rw [orderOf_pow, Nat.gcd_eq_right hb_dvd, ← hmdef]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m 2, ← hbdef]
    rw [Nat.mul_div_left _ hb_pos]
  have hpow2 : (ρ ^ b) ^ (2 ^ m.factorization 2) = 1 := by
    rw [show 2 ^ m.factorization 2 = ordProj[2] m from rfl, ← hord_pow]
    exact pow_orderOf_eq_one _
  set u' : Equiv.Perm Ω := s * ρ ^ b with hu'def
  set k : ℕ := b / 2 with hkdef
  have hb_eq : b = 2 * k + 1 := by
    rw [hkdef]
    have := Nat.div_two_mul_two_add_one_of_odd hb_odd
    omega
  have hu'_conj : u' = ρ ^ (-(k : ℤ)) * s' * (ρ ^ (-(k : ℤ)))⁻¹ := by
    have hstep : s * ρ ^ b = ρ ^ (-(((2 * k : ℕ) : ℤ))) * s' := by
      rw [hb_eq]
      calc s * ρ ^ (2 * k + 1)
          = s * ρ ^ (2 * k) * ρ := by rw [pow_succ, mul_assoc]
        _ = s * ρ ^ (2 * k) * s * s' := by rw [hρdef]; group
        _ = (s * ρ ^ (2 * k) * s) * s' := by group
        _ = ((ρ ^ (-(((2 * k : ℕ) : ℤ))) * s) * s) * s' := by
              rw [show s * ρ ^ (2 * k) = ρ ^ (-(((2 * k : ℕ) : ℤ))) * s by
                rw [← zpow_natCast ρ (2 * k)]
                simpa [hρdef] using CFSG.Timmesfeld.mul_zpow_mul_eq_zpow_neg_mul hs2 hs'2
                  (((2 * k : ℕ) : ℤ))]
        _ = ρ ^ (-(((2 * k : ℕ) : ℤ))) * s' := by
              rw [mul_assoc (ρ ^ (-(((2 * k : ℕ) : ℤ)))) s s, hs2, mul_one]
    rw [hu'def, hstep]
    rw [show ρ = s * s' from hρdef]
    rw [CFSG.Timmesfeld.Bridge.Asc72.zpow_mul_conj_eq hs2 hs'2 (-(k : ℤ))]
    congr 1
    push_cast
    ring_nf
  refine ⟨b, k, u', hb_odd, hb_eq, ?_, ?_, ?_, ?_, hs2, hs'2⟩
  · rw [hu'def, hρdef]
  · simpa [hρdef] using hu'_conj
  · simpa [hρdef] using hord_pow
  · simpa [hρdef] using hpow2

private lemma even_order_u_involution (h : TwoTransHyp X T α) {s s' u' : Equiv.Perm Ω}
    (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T) {b k : ℕ}
    (hconj : u' = (s * s') ^ (-(k : ℤ)) * s' * ((s * s') ^ (-(k : ℤ)))⁻¹)
    (hdef : u' = s * (s * s') ^ b)
    (hpow2 : ((s * s') ^ b) ^ (2 ^ (orderOf (s * s')).factorization 2) = 1) :
    u' * u' = 1 ∧ s * u' = (s * s') ^ b ∧
      IsPGroup 2 (Subgroup.closure ({s, u'} : Set (Equiv.Perm Ω))) := by
  have hs2 : s * s = 1 := h.mul_self_of_mem_twoTransD hs
  have hs'2 : s' * s' = 1 := h.mul_self_of_mem_twoTransD hs'
  have hu'2 : u' * u' = 1 := by
    rw [hconj]
    calc ((s * s') ^ (-(k : ℤ)) * s' * ((s * s') ^ (-(k : ℤ)))⁻¹) *
          ((s * s') ^ (-(k : ℤ)) * s' * ((s * s') ^ (-(k : ℤ)))⁻¹)
        = (s * s') ^ (-(k : ℤ)) * (s' * s') * ((s * s') ^ (-(k : ℤ)))⁻¹ := by group
      _ = 1 := by rw [hs'2]; group
  have hsu' : s * u' = (s * s') ^ b := by
    rw [hdef]
    calc s * (s * (s * s') ^ b) = (s * s) * (s * s') ^ b := by group
      _ = (s * s') ^ b := by rw [hs2, one_mul]
  have hP : IsPGroup 2 (Subgroup.closure ({s, u'} : Set (Equiv.Perm Ω))) :=
    CFSG.Timmesfeld.isPGroup_two_closure_pair hs2 hu'2
      (k := (orderOf (s * s')).factorization 2) (by rw [hsu']; exact hpow2)
  exact ⟨hu'2, hsu', hP⟩

private lemma even_order_u_fixed (h : TwoTransHyp X T α) {s u' : Equiv.Perm Ω} {β : Ω}
    (hs : s ∈ twoTransD X T) (hβ : s β = β)
    (hP : IsPGroup 2 (Subgroup.closure ({s, u'} : Set (Equiv.Perm Ω)))) :
    u' β = β := by
  have hnotdvd : ¬ 2 ∣ Nat.card Ω := fun h2 =>
    (Nat.not_even_iff_odd.mpr h.odd_card) (even_iff_two_dvd.mpr h2)
  obtain ⟨δ, hδ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Ω hnotdvd
  have hs_mem : s ∈ Subgroup.closure ({s, u'} : Set (Equiv.Perm Ω)) :=
    Subgroup.subset_closure (by simp)
  have hu'_mem : u' ∈ Subgroup.closure ({s, u'} : Set (Equiv.Perm Ω)) :=
    Subgroup.subset_closure (by simp)
  have hsδ : s δ = δ := by
    simpa [Subgroup.smul_def] using hδ ⟨s, hs_mem⟩
  have hu'δ : u' δ = δ := by
    simpa [Subgroup.smul_def] using hδ ⟨u', hu'_mem⟩
  have hs_tSub : s ∈ h.tSub β := h.mem_tSub_of_mem_twoTransD_of_fixed hs hβ
  have hδβ : (δ : Ω) = β := h.tSub_unique_fixed hs_tSub hs.1 δ hsδ
  rw [← hδβ]
  exact hu'δ

private lemma even_order_u_contradiction (h : TwoTransHyp X T α) {s s' u' : Equiv.Perm Ω}
    {β γ : Ω} (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T)
    (hβ : s β = β) (hγ : s' γ = γ) (hne : β ≠ γ) (hodd : Even (orderOf (s * s')))
    {b k : ℕ}
    (hconj : u' = (s * s') ^ (-(k : ℤ)) * s' * ((s * s') ^ (-(k : ℤ)))⁻¹)
    (hsu' : s * u' = (s * s') ^ b)
    (hord_pow : orderOf ((s * s') ^ b) = ordProj[2] (orderOf (s * s')))
    (hu'β : u' β = β) : False := by
  have hs2 : s * s = 1 := h.mul_self_of_mem_twoTransD hs
  have hs'2 : s' * s' = 1 := h.mul_self_of_mem_twoTransD hs'
  set ρ : Equiv.Perm Ω := s * s' with hρdef
  have hρX : ρ ∈ X := X.mul_mem (h.twoTransD_subset_X hs) (h.twoTransD_subset_X hs')
  have hρkX : ρ ^ (-(k : ℤ)) ∈ X := X.zpow_mem hρX _
  have hu'D : u' ∈ twoTransD X T := by
    rw [show u' = ρ ^ (-(k : ℤ)) * s' * (ρ ^ (-(k : ℤ)))⁻¹ by simpa [hρdef] using hconj]
    exact conj_mem_twoTransD hρkX hs'
  have hu'tSub : u' ∈ h.tSub β := h.mem_tSub_of_mem_twoTransD_of_fixed hu'D hu'β
  have hs_tSub : s ∈ h.tSub β := h.mem_tSub_of_mem_twoTransD_of_fixed hs hβ
  have hρb_eq : ρ ^ b = s * u' := by
    rw [hρdef, ← hsu']
  have hρbtSub : ρ ^ b ∈ h.tSub β := by
    rw [hρb_eq]
    exact (h.tSub β).mul_mem hs_tSub hu'tSub
  have hord_pow' : orderOf (ρ ^ b) = ordProj[2] (orderOf ρ) := by
    simpa [hρdef] using hord_pow
  have hρb_ne_one : ρ ^ b ≠ 1 := by
    intro h1
    have h1ord : orderOf (ρ ^ b) = 1 := by rw [h1, orderOf_one]
    rw [hord_pow'] at h1ord
    have hρeven : Even (orderOf ρ) := by simpa [hρdef] using hodd
    have hfac : 0 < (orderOf ρ).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two (orderOf_pos ρ).ne'
        (even_iff_two_dvd.mp hρeven)
    have h2 : 2 ≤ ordProj[2] (orderOf ρ) := by
      rw [show ordProj[2] (orderOf ρ) = 2 ^ (orderOf ρ).factorization 2 from rfl]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (orderOf ρ).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
    omega
  have hρbD : ρ ^ b ∈ twoTransD X T := h.tSub_subset_twoTransD hρbtSub hρb_ne_one
  have hρb_fix : (ρ ^ b) β = β := h.tSub_fix hρbtSub
  have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'2
  have hs'ρ : s' * ρ * s'⁻¹ = ρ⁻¹ := by
    rw [hρdef, hs'inv]
    calc s' * (s * s') * s' = s' * s * (s' * s') := by group
      _ = s' * s := by rw [hs'2, mul_one]
      _ = (s * s')⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs2,
              inv_eq_of_mul_eq_one_right hs'2]
  have hs'ρb : s' * ρ ^ b * s'⁻¹ = ρ ^ (-(b : ℤ)) := by
    rw [← conj_pow, hs'ρ, inv_pow, ← zpow_natCast ρ b, ← zpow_neg]
  have hs'X : s' ∈ X := h.twoTransD_subset_X hs'
  have hρb_inv_D : ρ ^ (-(b : ℤ)) ∈ twoTransD X T := by
    rw [← hs'ρb]
    exact conj_mem_twoTransD hs'X hρbD
  have hρb_inv_eq : ρ ^ (-(b : ℤ)) = (ρ ^ b)⁻¹ := by
    rw [zpow_neg, ← zpow_natCast]
  have hρb_inv_fix : (ρ ^ (-(b : ℤ))) β = β := by
    rw [hρb_inv_eq]
    show (ρ ^ b).symm β = β
    rw [Equiv.symm_apply_eq]
    exact hρb_fix.symm
  have hρb_inv_ne_one : ρ ^ (-(b : ℤ)) ≠ 1 := by
    rw [hρb_inv_eq]
    exact inv_ne_one.mpr hρb_ne_one
  have hρb_inv_tSub : ρ ^ (-(b : ℤ)) ∈ h.tSub β :=
    h.mem_tSub_of_mem_twoTransD_of_fixed hρb_inv_D hρb_inv_fix
  have hconj_tSub : s' * ρ ^ b * s'⁻¹ ∈ h.tSub (s' β) :=
    h.conj_mem_tSub hs'X hρbtSub
  have hρb_inv_tSub' : ρ ^ (-(b : ℤ)) ∈ h.tSub (s' β) := by
    rw [← hs'ρb]
    exact hconj_tSub
  have hs'β : s' β = β :=
    h.tSub_unique_fixed hρb_inv_tSub hρb_inv_ne_one (s' β) (h.tSub_fix hρb_inv_tSub')
  have hs'_tSub : s' ∈ h.tSub γ := h.mem_tSub_of_mem_twoTransD_of_fixed hs' hγ
  exact hne (h.tSub_unique_fixed hs'_tSub hs'.1 β hs'β)

private lemma odd_orderOf_mul_of_ne_fixed (h : TwoTransHyp X T α)
    {s s' : Equiv.Perm Ω} (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T)
    {β γ : Ω} (hβ : s β = β) (hγ : s' γ = γ) (hne : β ≠ γ) :
    Odd (orderOf (s * s')) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨b, k, u', -, hb_eq, hdef, hconj, hord_pow, hpow2, -, -⟩ :=
    h.even_order_conj_data hs hs' hodd
  obtain ⟨-, hsu', hP⟩ := h.even_order_u_involution hs hs' hconj hdef hpow2
  have hu'β : u' β = β := h.even_order_u_fixed hs hβ hP
  exact h.even_order_u_contradiction hs hs' hβ hγ hne hodd hconj hsu' hord_pow hu'β

private lemma orderOf_mul_dvd_two_of_commute (h : TwoTransHyp X T α)
    {s s' : Equiv.Perm Ω} (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T)
    (hc : Commute s s') : orderOf (s * s') ∣ 2 := by
  apply orderOf_dvd_iff_pow_eq_one.mpr
  rw [hc.mul_pow, pow_two, pow_two, h.mul_self_of_mem_twoTransD hs,
    h.mul_self_of_mem_twoTransD hs', one_mul]

private lemma isOddTransp_twoTransD (h : TwoTransHyp X T α) :
    Asc72.IsOddTransp (twoTransD X T) := by
  constructor
  · intro s hs
    exact orderOf_eq_prime (by simpa [pow_two] using h.mul_self_of_mem_twoTransD hs) hs.1
  · intro s hs s' hs'
    rcases h.exists_unique_fixed hs with ⟨β, hβ, -⟩
    rcases h.exists_unique_fixed hs' with ⟨γ, hγ, -⟩
    by_cases hβγ : β = γ
    · left
      subst hβγ
      exact h.orderOf_mul_dvd_two_of_commute hs hs'
        (h.commute_of_mem_twoTransD_of_same_fixed hs hs' hβ hγ)
    · exact Or.inr (h.odd_orderOf_mul_of_ne_fixed hs hs' hβ hγ hβγ)

private lemma eq_fix_of_commute (h : TwoTransHyp X T α) {s s' : Equiv.Perm Ω} {β γ : Ω}
    (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T) (hβ : s β = β) (hγ : s' γ = γ)
    (hc : Commute s s') : β = γ := by
  by_contra hne
  have hodd := h.odd_orderOf_mul_of_ne_fixed hs hs' hβ hγ hne
  have hdvd : orderOf (s * s') ∣ 2 := h.orderOf_mul_dvd_two_of_commute hs hs' hc
  have hone : orderOf (s * s') = 1 := by
    have hpos := orderOf_pos (s * s')
    have hle : orderOf (s * s') ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hne2 : orderOf (s * s') ≠ 2 := by
      intro h2
      rw [h2] at hodd
      norm_num at hodd
    omega
  have heq : s * s' = 1 := orderOf_eq_one_iff.mp hone
  have hss' : s' = s := by
    have := eq_inv_of_mul_eq_one_right heq
    rwa [inv_eq_of_mul_eq_one_right (h.mul_self_of_mem_twoTransD hs)] at this
  have hs_tSub : s ∈ h.tSub β := h.mem_tSub_of_mem_twoTransD_of_fixed hs hβ
  exact hne (h.tSub_unique_fixed hs_tSub hs.1 γ (hss' ▸ hγ)).symm

private def twoTransDY (h : TwoTransHyp X T α) : Set ↥(twoTransY X T) :=
  {s | (s : Equiv.Perm Ω) ∈ twoTransD X T}

private lemma reach_fixed_eq (h : TwoTransHyp X T α) {x y : ↥(twoTransY X T)}
    (hx : x ∈ h.twoTransDY) (hr : Reach h.twoTransDY x y) :
    ∀ {β γ : Ω}, (x : Equiv.Perm Ω) β = β → (y : Equiv.Perm Ω) γ = γ → β = γ := by
  induction hr with
  | refl =>
      intro β γ hβ hγ
      rcases h.exists_unique_fixed hx with ⟨δ, -, huniq⟩
      exact (huniq β hβ).trans (huniq γ hγ).symm
  | tail hxz hzy ih =>
      intro β γ hβ hγ
      rcases h.exists_unique_fixed hzy.1 with ⟨δ, hδ, -⟩
      have hβδ : β = δ := ih hβ hδ
      have hc := congrArg Subtype.val hzy.2.2
      exact hβδ.trans (h.eq_fix_of_commute hzy.1 hzy.2.1 hδ hγ hc)

private lemma isOddTransp_twoTransDY (h : TwoTransHyp X T α) :
    Asc72.IsOddTransp h.twoTransDY := by
  constructor
  · intro s hs
    have hsD : (s : Equiv.Perm Ω) ∈ twoTransD X T := hs
    have h2 : (s : Equiv.Perm Ω) * (s : Equiv.Perm Ω) = 1 :=
      h.mul_self_of_mem_twoTransD hsD
    have h1 : (s : Equiv.Perm Ω) ≠ 1 := hsD.1
    have hord : orderOf (s : Equiv.Perm Ω) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using h2) h1
    rwa [← Subgroup.orderOf_coe]
  · intro s hs s' hs'
    have hsD : (s : Equiv.Perm Ω) ∈ twoTransD X T := hs
    have hs'D : (s' : Equiv.Perm Ω) ∈ twoTransD X T := hs'
    have hmain := h.isOddTransp_twoTransD.2 (s : Equiv.Perm Ω) hsD
      (s' : Equiv.Perm Ω) hs'D
    rwa [← Subgroup.orderOf_coe]

private lemma isNormalSet_twoTransDY (h : TwoTransHyp X T α) :
    IsNormalSet h.twoTransDY := by
  intro g s hs
  have hgX : (g : Equiv.Perm Ω) ∈ X := h.twoTransY_le_X g.2
  have hsD : (s : Equiv.Perm Ω) ∈ twoTransD X T := hs
  show ((g * s * g⁻¹ : ↥(twoTransY X T)) : Equiv.Perm Ω) ∈ twoTransD X T
  simpa using conj_mem_twoTransD hgX hsD

private lemma closure_twoTransDY (h : TwoTransHyp X T α) :
    Subgroup.closure h.twoTransDY = ⊤ :=
  Subgroup.closure_preimage_eq_top (twoTransD X T)

private lemma meetsSq_twoTransDY (h : TwoTransHyp X T α) :
    ∃ u ∈ h.twoTransDY, ∃ v ∈ h.twoTransDY, u ≠ v ∧ Commute u v ∧
      u * v ∈ h.twoTransDY := by
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  haveI : Fintype T := Fintype.ofFinite T
  have hcard : 4 ≤ Fintype.card T := by
    simpa [Nat.card_eq_fintype_card] using h.four_le
  have h3 : 3 ≤ ENat.card T := by
    rw [ENat.card_eq_coe_fintype_card]
    exact_mod_cast (by omega : 3 ≤ Fintype.card T)
  obtain ⟨t', ht'1, ht't⟩ := ENat.exists_ne_ne_of_three_le h3 (1 : T) ⟨t, ht⟩
  have htD : t ∈ twoTransD X T := ⟨ht1, 1, X.one_mem, t, ht, by simp⟩
  have ht'D : (t' : Equiv.Perm Ω) ∈ twoTransD X T :=
    ⟨fun h1 => ht'1 (Subtype.ext h1), 1, X.one_mem, t', t'.2, by simp⟩
  have htprod1 : t * (t' : Equiv.Perm Ω) ≠ 1 := by
    intro h1
    apply ht't
    apply Subtype.ext
    have := eq_inv_of_mul_eq_one_right h1
    rwa [inv_eq_of_mul_eq_one_right (h.t_mul_self ht)] at this
  have htprodD : t * (t' : Equiv.Perm Ω) ∈ twoTransD X T :=
    ⟨htprod1, 1, X.one_mem, t * t', T.mul_mem ht t'.2, by simp⟩
  let u : ↥(twoTransY X T) := ⟨t, le_twoTransY ht⟩
  let v : ↥(twoTransY X T) := ⟨t * (t' : Equiv.Perm Ω),
    le_twoTransY (T.mul_mem ht t'.2)⟩
  have huD : u ∈ h.twoTransDY := htD
  have hvD : v ∈ h.twoTransDY := htprodD
  have huv : u ≠ v := by
    intro h1
    have h2 : (t : Equiv.Perm Ω) = t * (t' : Equiv.Perm Ω) := congrArg Subtype.val h1
    have h3 : (t' : Equiv.Perm Ω) = 1 := by
      have := congrArg (fun x => (t : Equiv.Perm Ω) * x) h2
      rw [h.t_mul_self ht, ← mul_assoc, h.t_mul_self ht, one_mul] at this
      exact this.symm
    exact ht'1 (Subtype.ext h3)
  have hcPerm : Commute (t : Equiv.Perm Ω) (t * (t' : Equiv.Perm Ω)) := by
    have htSub : h.tSub α = T := by
      have h1 := h.tSub_eq_conj (x := 1) X.one_mem (by simp : (1 : Equiv.Perm Ω) α = α)
      rw [h1]
      ext s
      simp [Subgroup.mem_map, MulAut.conj_apply]
    exact h.commute_of_mem_tSub (by rw [htSub]; exact ht)
      (by rw [htSub]; exact T.mul_mem ht t'.2)
  have hc : Commute u v := Subtype.ext hcPerm
  have huvD : u * v ∈ h.twoTransDY := by
    have hco : ((u * v : ↥(twoTransY X T)) : Equiv.Perm Ω) = (t' : Equiv.Perm Ω) := by
      show t * (t * (t' : Equiv.Perm Ω)) = (t' : Equiv.Perm Ω)
      rw [← mul_assoc, h.t_mul_self ht, one_mul]
    show ((u * v : ↥(twoTransY X T)) : Equiv.Perm Ω) ∈ twoTransD X T
    rw [hco]
    exact ht'D
  exact ⟨u, huD, v, hvD, huv, hc, huvD⟩

private lemma twoTransY_transitive (h : TwoTransHyp X T α) (β : Ω) :
    ∃ y ∈ twoTransY X T, y α = β := by
  by_cases hβ : β = α
  · exact ⟨1, (twoTransY X T).one_mem, by simp [hβ]⟩
  · obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
    obtain ⟨g, hg, hgα⟩ := h.exists_mem_X_map_alpha β
    let s := g * t * g⁻¹
    have hsD : s ∈ twoTransD X T :=
      conj_mem_twoTransD hg ⟨ht1, 1, X.one_mem, t, ht, by simp⟩
    have htD : t ∈ twoTransD X T := ⟨ht1, 1, X.one_mem, t, ht, by simp⟩
    have hfixs : s β = β := by
      change (g * t * g⁻¹) β = β
      rw [← hgα]
      change g (t (g⁻¹ (g α))) = g α
      have hgg : g⁻¹ (g α) = α := by simp
      rw [hgg, h.fix t ht]
    have hfixα : t α = α := h.fix t ht
    have hodd : Odd (orderOf (t * s)) :=
      h.odd_orderOf_mul_of_ne_fixed htD hsD hfixα hfixs (Ne.symm hβ)
    have hs2 : s * s = 1 := h.mul_self_of_mem_twoTransD hsD
    obtain ⟨y, hy, hyconj⟩ :=
      CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul (h.t_mul_self ht) hs2 hodd
    have hyY : y ∈ twoTransY X T :=
      (Subgroup.closure_le (twoTransY X T)).mpr (by
        intro z hz
        rcases hz with rfl | rfl
        · exact le_twoTransY ht
        · exact Subgroup.subset_closure hsD) hy
    have hys : s (y α) = y α := by
      calc s (y α) = (y * t * y⁻¹) (y α) := by rw [hyconj]
        _ = y (t α) := by simp [mul_assoc]
        _ = y α := by rw [hfixα]
    have hs1 : s ≠ 1 := by
      intro h1
      apply ht1
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [s, mul_assoc] using this
    have hs_sub : s ∈ h.tSub β := h.mem_tSub_of_mem_twoTransD_of_fixed hsD hfixs
    have hyα : y α = β := h.tSub_unique_fixed hs_sub hs1 (y α) hys
    exact ⟨y, hyY, hyα⟩

private lemma disconnected_twoTransDY (h : TwoTransHyp X T α) :
    Disconnected h.twoTransDY := by
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  obtain ⟨δ, hδ⟩ : ∃ δ, t δ ≠ δ := by
    by_contra hc
    push Not at hc
    exact ht1 (Equiv.ext hc)
  have hδα : δ ≠ α := fun he => hδ (he ▸ h.fix t ht)
  obtain ⟨g, hg, hgα⟩ := h.exists_mem_X_map_alpha δ
  let s := g * t * g⁻¹
  have htD : t ∈ twoTransD X T := ⟨ht1, 1, X.one_mem, t, ht, by simp⟩
  have hsD : s ∈ twoTransD X T := conj_mem_twoTransD hg htD
  let u : ↥(twoTransY X T) := ⟨t, le_twoTransY ht⟩
  let v : ↥(twoTransY X T) := ⟨s, Subgroup.subset_closure hsD⟩
  have huD : u ∈ h.twoTransDY := htD
  have hvD : v ∈ h.twoTransDY := hsD
  have hfixu : (u : Equiv.Perm Ω) α = α := h.fix t ht
  have hfixv : (v : Equiv.Perm Ω) δ = δ := by
    change (g * t * g⁻¹) δ = δ
    rw [← hgα]
    change g (t (g⁻¹ (g α))) = g α
    have hgg : g⁻¹ (g α) = α := by simp
    rw [hgg, h.fix t ht]
  refine ⟨u, huD, v, hvD, ?_⟩
  intro hreach
  have heq : α = δ := h.reach_fixed_eq huD hreach hfixu hfixv
  exact hδα heq.symm

private lemma pCore_twoTransY_eq_bot (h : TwoTransHyp X T α) :
    ∀ N : Subgroup ↥(twoTransY X T), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hP
  rw [eq_bot_iff]
  intro n hn
  have hnotdvd : ¬ 2 ∣ Nat.card Ω := fun h2 =>
    (Nat.not_even_iff_odd.mpr h.odd_card) (even_iff_two_dvd.mpr h2)
  obtain ⟨γ, hγ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Ω hnotdvd
  ext β
  obtain ⟨y1, hy1, hy1α⟩ := h.twoTransY_transitive γ
  obtain ⟨y2, hy2, hy2α⟩ := h.twoTransY_transitive β
  let y : ↥(twoTransY X T) := ⟨y2 * y1⁻¹,
    (twoTransY X T).mul_mem hy2 ((twoTransY X T).inv_mem hy1)⟩
  have hyγ : (y : Equiv.Perm Ω) γ = β := by
    change (y2 : Equiv.Perm Ω) ((y1 : Equiv.Perm Ω)⁻¹ γ) = β
    have h1 : (y1 : Equiv.Perm Ω)⁻¹ γ = α := by
      have := congrArg (⇑((y1 : Equiv.Perm Ω)⁻¹)) hy1α
      simpa using this.symm
    rw [h1, hy2α]
  have hconj : (y : ↥(twoTransY X T))⁻¹ * n * y ∈ N := by
    have := hN.conj_mem n hn (y : ↥(twoTransY X T))⁻¹
    simpa using this
  have hfixγ : (((⟨(y : ↥(twoTransY X T))⁻¹ * n * y, hconj⟩ : N) : ↥(twoTransY X T)) :
      Equiv.Perm Ω) γ = γ := by
    simpa [Subgroup.smul_def] using hγ ⟨(y : ↥(twoTransY X T))⁻¹ * n * y, hconj⟩
  have h2 : (n : Equiv.Perm Ω) ((y : Equiv.Perm Ω) γ) = (y : Equiv.Perm Ω) γ := by
    have := congrArg (fun z => (y : Equiv.Perm Ω) z) hfixγ
    simpa [mul_assoc] using this
  rwa [hyγ] at h2

private lemma center_twoTransY_eq_bot (h : TwoTransHyp X T α) :
    Subgroup.center ↥(twoTransY X T) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨β, hβ⟩ : ∃ β, (z : Equiv.Perm Ω) β ≠ β := by
    by_contra hc
    push Not at hc
    exact hz1 (Subtype.ext (Equiv.ext hc))
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  obtain ⟨g, hg, hgα⟩ := h.exists_mem_X_map_alpha β
  let tβ := g * t * g⁻¹
  have htβD : tβ ∈ twoTransD X T :=
    conj_mem_twoTransD hg ⟨ht1, 1, X.one_mem, t, ht, by simp⟩
  have htβY : tβ ∈ twoTransY X T := Subgroup.subset_closure htβD
  have htβfix : tβ β = β := by
    change (g * t * g⁻¹) β = β
    rw [← hgα]
    change g (t (g⁻¹ (g α))) = g α
    have hgg : g⁻¹ (g α) = α := by simp
    rw [hgg, h.fix t ht]
  have htβ1 : tβ ≠ 1 := by
    intro h1
    apply ht1
    have := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [tβ, mul_assoc] using this
  have hcomm : Commute (⟨tβ, htβY⟩ : ↥(twoTransY X T)) z :=
    Subgroup.mem_center_iff.mp hz _
  have hfixzβ : tβ ((z : Equiv.Perm Ω) β) = (z : Equiv.Perm Ω) β := by
    have := congrArg (fun w : ↥(twoTransY X T) => (w : Equiv.Perm Ω) β) hcomm.eq
    simpa [htβfix] using this
  have htβ_sub : tβ ∈ h.tSub β := h.mem_tSub_of_mem_twoTransD_of_fixed htβD htβfix
  exact hβ (h.tSub_unique_fixed htβ_sub htβ1 ((z : Equiv.Perm Ω) β) hfixzβ)

private lemma zStar_twoTransY_eq_bot (h : TwoTransHyp X T α) :
    zStar ↥(twoTransY X T) = ⊥ := by
  rw [CFSG.Timmesfeld.Bridge.OddLocal.zStar_eq_center h.pCore_twoTransY_eq_bot,
    h.center_twoTransY_eq_bot]

theorem commute_iff (h : TwoTransHyp X T α) {s s' : Equiv.Perm Ω}
    (hs : s ∈ twoTransD X T) (hs' : s' ∈ twoTransD X T) :
    Commute s s' ↔ ∃ β : Ω, s β = β ∧ s' β = β := by
  constructor
  · intro hc
    rcases h.exists_unique_fixed hs with ⟨β, hβ, -⟩
    rcases h.exists_unique_fixed hs' with ⟨γ, hγ, -⟩
    have hβγ : β = γ := h.eq_fix_of_commute hs hs' hβ hγ hc
    exact ⟨β, hβ, by simpa [hβγ] using hγ⟩
  · rintro ⟨β, hβ, hβ'⟩
    exact h.commute_of_mem_twoTransD_of_same_fixed hs hs' hβ hβ'

theorem isBenderGroup (h : TwoTransHyp X T α) :
    CFSG.BenderSuzuki.IsBenderGroup ↥(twoTransY X T) := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup
      (↥(twoTransY X T) ⧸ zStar ↥(twoTransY X T)) :=
    CFSG.Timmesfeld.Bridge.OddTransp.oddTranspZStar (↥(twoTransY X T)) h.twoTransDY
      h.isOddTransp_twoTransDY h.isNormalSet_twoTransDY h.closure_twoTransDY
      h.meetsSq_twoTransDY h.disconnected_twoTransDY
  let e : (↥(twoTransY X T) ⧸ zStar ↥(twoTransY X T)) ≃* ↥(twoTransY X T) :=
    (QuotientGroup.quotientMulEquivOfEq h.zStar_twoTransY_eq_bot).trans
      QuotientGroup.quotientBot
  exact CFSG.Timmesfeld.Bridge.OddLocal.isBenderGroup_of_mulEquiv' e hB

end TwoTransHyp
