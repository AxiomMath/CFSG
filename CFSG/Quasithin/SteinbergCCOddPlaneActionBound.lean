module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup

variable {V : Type*} [Group V]

theorem zpow_eq_self_or_inv_of_zpow_sq {p : ℕ} (hp : p.Prime) {u : V} (hu : orderOf u = p)
    {k : ℤ} (hk : u ^ (k * k) = u) : u ^ k = u ∨ u ^ k = u⁻¹ := by
  have h1 : u ^ (k * k - 1) = 1 := by rw [zpow_sub_one, hk, mul_inv_cancel]
  have h2 : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← hu, orderOf_dvd_iff_zpow_eq_one]
    rw [show (k - 1) * (k + 1) = k * k - 1 by ring]
    exact h1
  rcases (Int.Prime.dvd_mul' hp h2) with h | h
  · left
    have h3 : u ^ (k - 1) = 1 := by rw [← orderOf_dvd_iff_zpow_eq_one, hu]; exact h
    rw [show k = (k - 1) + 1 by ring, zpow_add, h3, one_mul, zpow_one]
  · right
    have h3 : u ^ (k + 1) = 1 := by rw [← orderOf_dvd_iff_zpow_eq_one, hu]; exact h
    rw [show k = (k + 1) - 1 by ring, zpow_sub, h3, one_mul, zpow_one]

theorem forall_zpowers_apply_eq_or_inv {p : ℕ} (hp : p.Prime) {u : V} (hu : orderOf u = p)
    (s : MulAut V) (hss : ∀ v, s (s v) = v) (hsu : s u ∈ zpowers u) :
    (∀ v ∈ zpowers u, s v = v) ∨ (∀ v ∈ zpowers u, s v = v⁻¹) := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hsu
  have hkk : u ^ (k * k) = u := by
    have h1 := hss u
    rw [← hk, map_zpow, ← hk, ← zpow_mul] at h1
    exact h1
  rcases zpow_eq_self_or_inv_of_zpow_sq hp hu hkk with h | h
  · left
    rintro v ⟨j, rfl⟩
    change s (u ^ j) = u ^ j
    rw [map_zpow, ← hk, h]
  · right
    rintro v ⟨j, rfl⟩
    change s (u ^ j) = (u ^ j)⁻¹
    rw [map_zpow, ← hk, h, inv_zpow]

theorem pm_of_commuting_involutions [Finite V] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hV : ∀ a b : V, a * b = b * a) (hexp : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ 2)
    {s t : MulAut V} (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s) :
    ((∀ v, s v = v) ∨ (∀ v, s v = v⁻¹)) ∨ ((∀ v, t v = v) ∨ (∀ v, t v = v⁻¹)) ∨
      ((∀ v, (s * t) v = v) ∨ (∀ v, (s * t) v = v⁻¹)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases htpm : (∀ v, t v = v) ∨ (∀ v, t v = v⁻¹)
  · exact Or.inr (Or.inl htpm)
  rw [not_or] at htpm
  obtain ⟨htid, htinv⟩ := htpm
  have htt : ∀ v, t (t v) = v := fun v => by rw [← MulAut.mul_apply, ht, MulAut.one_apply]
  have hss : ∀ v, s (s v) = v := fun v => by rw [← MulAut.mul_apply, hs, MulAut.one_apply]
  have hstv : ∀ v, s (t v) = t (s v) := fun v => by
    rw [← MulAut.mul_apply, hst, MulAut.mul_apply]
  let Vp : Subgroup V :=
    { carrier := {v | t v = v}
      mul_mem' := fun {a b} ha hb => by
        change t a = a at ha
        change t b = b at hb
        change t (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one t
      inv_mem' := fun {a} ha => by
        change t a = a at ha
        change t a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let Vm : Subgroup V :=
    { carrier := {v | t v = v⁻¹}
      mul_mem' := fun {a b} ha hb => by
        change t a = a⁻¹ at ha
        change t b = b⁻¹ at hb
        change t (a * b) = (a * b)⁻¹
        rw [map_mul, ha, hb, mul_inv_rev, hV]
      one_mem' := by
        change t 1 = 1⁻¹
        rw [map_one, inv_one]
      inv_mem' := fun {a} ha => by
        change t a = a⁻¹ at ha
        change t a⁻¹ = a⁻¹⁻¹
        rw [map_inv, ha] }
  have hVp : ∀ v, v ∈ Vp ↔ t v = v := fun _ => Iff.rfl
  have hVm : ∀ v, v ∈ Vm ↔ t v = v⁻¹ := fun _ => Iff.rfl
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hdec : ∀ v, ∃ a ∈ Vp, ∃ b ∈ Vm, v = a * b := by
    intro v
    have hw : v ^ (m + 1) * v ^ (m + 1) = v := by
      rw [← pow_add, show m + 1 + (m + 1) = p + 1 by omega, pow_succ, hexp, one_mul]
    refine ⟨v ^ (m + 1) * t (v ^ (m + 1)), ?_, v ^ (m + 1) * (t (v ^ (m + 1)))⁻¹, ?_, ?_⟩
    · rw [hVp, map_mul, htt, hV]
    · rw [hVm, map_mul, map_inv, htt, mul_inv_rev, inv_inv]
    · rw [show v ^ (m + 1) * t (v ^ (m + 1)) * (v ^ (m + 1) * (t (v ^ (m + 1)))⁻¹) =
        v ^ (m + 1) * v ^ (m + 1) by
          rw [hV (v ^ (m + 1)) (t (v ^ (m + 1)))⁻¹]
          group, hw]
  have hinter : ∀ v, v ∈ Vp → v ∈ Vm → v = 1 := by
    intro v hp' hm'
    rw [hVp] at hp'
    rw [hVm, hp'] at hm'
    have h2 : v ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 2 [hm']
      exact mul_inv_cancel v
    have h1 := orderOf_dvd_of_pow_eq_one h2
    have h3 := orderOf_dvd_of_pow_eq_one (hexp v)
    have h4 : orderOf v ∣ Nat.gcd 2 p := Nat.dvd_gcd h1 h3
    rw [(Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hline : ∀ L : Subgroup V, L ≠ ⊥ → L ≠ ⊤ → Nat.card L = p := by
    intro L hbot htop
    obtain ⟨i, hi, hiL⟩ := (Nat.dvd_prime_pow hp).mp (hcard ▸ card_subgroup_dvd_card L)
    interval_cases i
    · exact absurd (card_eq_one.mp (by rw [hiL, pow_zero])) hbot
    · rw [hiL, pow_one]
    · exact absurd ((card_eq_iff_eq_top L).mp (by rw [hiL, hcard])) htop
  have hVpbot : Vp ≠ ⊥ := by
    intro h
    apply htinv
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [h, mem_bot] at ha
    rw [ha, one_mul]
    exact hb
  have hVmbot : Vm ≠ ⊥ := by
    intro h
    apply htid
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [h, mem_bot] at hb
    rw [hb, mul_one]
    exact ha
  have hVptop : Vp ≠ ⊤ := fun h => htid fun v => (hVp v).mp (h ▸ mem_top v)
  have hVmtop : Vm ≠ ⊤ := fun h => htinv fun v => (hVm v).mp (h ▸ mem_top v)
  have hact : ∀ L : Subgroup V, L ≠ ⊥ → L ≠ ⊤ → (∀ v ∈ L, s v ∈ L) →
      (∀ v ∈ L, s v = v) ∨ (∀ v ∈ L, s v = v⁻¹) := by
    intro L hbot htop hsL
    obtain ⟨⟨u, huL⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hu : orderOf u = p := orderOf_eq_prime (hexp u) hu1'
    have hLu : zpowers u = L := eq_of_le_of_card_ge (zpowers_le.mpr huL)
      (by rw [hline L hbot htop, Nat.card_zpowers, hu])
    rw [← hLu] at hsL ⊢
    exact forall_zpowers_apply_eq_or_inv hp hu s hss (hsL u (mem_zpowers u))
  have hsp := hact Vp hVpbot hVptop fun v hv => by
    rw [hVp] at hv ⊢
    rw [← hstv, hv]
  have hsm := hact Vm hVmbot hVmtop fun v hv => by
    rw [hVm] at hv ⊢
    rw [← hstv, hv, map_inv]
  rcases hsp with hsp | hsp <;> rcases hsm with hsm | hsm
  · refine Or.inl (Or.inl fun v => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [map_mul, hsp a ha, hsm b hb]
  · refine Or.inr (Or.inr (Or.inl fun v => ?_))
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [MulAut.mul_apply, map_mul, map_mul, (hVp a).mp ha, (hVm b).mp hb, map_inv, hsp a ha,
      hsm b hb, inv_inv]
  · refine Or.inr (Or.inr (Or.inr fun v => ?_))
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [MulAut.mul_apply, map_mul, map_mul, (hVp a).mp ha, (hVm b).mp hb, map_inv, hsp a ha,
      hsm b hb, mul_inv_rev, hV]
  · refine Or.inl (Or.inr fun v => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [map_mul, hsp a ha, hsm b hb, mul_inv_rev, hV]

variable {H : Type*} [Group H] [Finite H]

theorem characteristic_odd_plane_action_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup H} [Q.Characteristic] (hQ : IsPGroup p Q)
    (hdim : Nat.card (Q ⧸ frattini Q) = p ^ 2)
    (hker : ((CFSG.SectionRank.Ccomm.autQuotient (frattini Q)).comp
      (MulAut.conjNormal : H →* MulAut Q)).ker ≤ CFSG.solvableRadical H)
    {A : Subgroup (MulAut H)} (hA : IsMulCommutative A) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card (A.map (CFSG.SectionRank.Ccomm.autQuotient (CFSG.solvableRadical H))) ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set ρ : H →* MulAut (Q ⧸ frattini Q) :=
    (CFSG.SectionRank.Ccomm.autQuotient (frattini Q)).comp MulAut.conjNormal with hρ
  set α := CFSG.SectionRank.Ccomm.frattiniAction Q with hα
  set φ := CFSG.SectionRank.Ccomm.autQuotient (CFSG.solvableRadical H) with hφ
  obtain ⟨-, hVc, hVpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hV : ∀ a b : Q ⧸ frattini Q, a * b = b * a := fun a b => hVc.is_comm.comm a b
  have hequiv : ∀ (a : MulAut H) (h : H), ρ (a h) = α a * ρ h * (α a)⁻¹ := by
    intro a h
    ext v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    rw [MulAut.mul_apply, MulAut.mul_apply, ← map_inv]
    change ((MulAut.conjNormal (a h) x : Q) : Q ⧸ frattini Q) =
      ((MulAut.characteristic Q a (MulAut.conjNormal h (MulAut.characteristic Q a⁻¹ x)) : Q) :
        Q ⧸ frattini Q)
    congr 1
    apply Subtype.ext
    change a h * x * (a h)⁻¹ = a (h * a⁻¹ x * h⁻¹)
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  have hpm : ∀ a : MulAut H, a * a = 1 → ((∀ v, α a v = v) ∨ (∀ v, α a v = v⁻¹)) →
      φ a = 1 := by
    intro a ha2 hpm
    have hcomm : ∀ h, ρ (a h) = ρ h := by
      intro h
      rw [hequiv]
      have hαinv : (α a)⁻¹ = α a := by
        rw [← map_inv, inv_eq_of_mul_eq_one_right ha2]
      ext v
      rw [MulAut.mul_apply, MulAut.mul_apply, hαinv]
      rcases hpm with h1 | h1
      · rw [h1, h1]
      · rw [h1, h1, map_inv, inv_inv]
    apply MonoidHom.mem_ker.mp
    rw [CFSG.SectionRank.Ccomm.mem_ker_autQuotient]
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
  have hkey : ∀ a ∈ A, ∀ b ∈ A, φ a ≠ 1 → φ b ≠ 1 → φ a = φ b := by
    intro a ha b hb hφa hφb
    have hab : a * b = b * a := congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
    have hb2 : b * b = 1 := by rw [← pow_two]; exact hA2 b hb
    have hab2 : a * b * (a * b) = 1 := by
      rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab,
        show a * (a * b) * b = (a * a) * (b * b) by group, ha2, hb2, one_mul]
    rcases pm_of_commuting_involutions hp hp2 hV hVpow hdim (s := α a) (t := α b)
        (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one])
        (by rw [← map_mul, ← map_mul, hab]) with h | h | h
    · exact absurd (hpm a ha2 h) hφa
    · exact absurd (hpm b hb2 h) hφb
    · rw [← map_mul] at h
      have h1 := hpm (a * b) hab2 h
      rw [map_mul] at h1
      have hφb2 : φ b * φ b = 1 := by rw [← map_mul, hb2, map_one]
      calc φ a = (φ b)⁻¹ := eq_inv_of_mul_eq_one_left h1
        _ = φ b := inv_eq_of_mul_eq_one_right hφb2
  have hinj : Function.Injective
      (fun x : A.map φ => decide ((x : MulAut (H ⧸ CFSG.solvableRadical H)) = 1)) := by
    rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩ hxy
    simp only [decide_eq_decide] at hxy
    apply Subtype.ext
    by_cases h1 : φ a = 1
    · change φ a = φ b
      rw [h1, hxy.mp h1]
    · exact hkey a ha b hb h1 (fun h => h1 (hxy.mpr h))
  calc Nat.card (A.map φ) ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]

end CFSG.Quasithin.SteinbergCC
