module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8211A
public import CFSG.Quasithin.Background.F918M1
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.L8211

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem finite_mulAut [Finite V] : Finite (MulAut V) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := MulAut V))

theorem mem_normalizer_centSub {W : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub W) :
    g ∈ Subgroup.normalizer (centSub W : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx w hw
    show g (x (g⁻¹ w)) = w
    rw [hx _ (inv_apply_mem_of_stabSub hg hw), MulAut.apply_inv_self]
  · intro hx w hw
    have h1 := hx (g w) (apply_mem_of_stabSub hg hw)
    have h2 : g (x w) = g w := by simpa [MulAut.mul_apply] using h1
    exact g.injective h2

structure Hyp (P : Subgroup (MulAut V)) (z : V) (e : ℕ) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  ne : z ≠ 1
  fixz : P ≤ centSub (Subgroup.zpowers z)
  cardW : Nat.card ↥(commV (pCoreOf 2 P)) = 2 ^ (e + 1)
  cardR : Nat.card ↥(pCoreOf 2 P) = 2 ^ e
  min : ∀ N : Subgroup (MulAut V), N ≤ pCoreOf 2 P → N ≠ ⊥ →
    P ≤ Subgroup.normalizer (N : Set (MulAut V)) → N = pCoreOf 2 P
  irrW : ∀ Y : Subgroup V, Subgroup.zpowers z < Y → Y ≤ commV (pCoreOf 2 P) → P ≤ stabSub Y →
    Y = commV (pCoreOf 2 P)
  fixW : commV (pCoreOf 2 P) ⊓ fixV (pCoreOf 2 P) = Subgroup.zpowers z
  commP : commV P = ⊤

namespace Hyp

variable [Finite V] {P : Subgroup (MulAut V)} {z : V} {e : ℕ}

omit [Finite V] in
theorem rad_le (_ : Hyp P z e) : pCoreOf 2 P ≤ P := CFSG.openPCoreOf_le 2 P

omit [Finite V] in
theorem le_normalizer_rad (_ : Hyp P z e) :
    P ≤ Subgroup.normalizer (pCoreOf 2 P : Set (MulAut V)) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P

theorem isPGroup_rad (_ : Hyp P z e) : IsPGroup 2 ↥(pCoreOf 2 P) := by
  have := finite_mulAut (V := V)
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P

variable (h : Hyp P z e)
include h

omit [Finite V] in
theorem card_zpowers : Nat.card ↥(Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (h.sq z) h.ne

omit [Finite V] in
theorem zpowers_le : Subgroup.zpowers z ≤ commV (pCoreOf 2 P) := by
  rw [← h.fixW]
  exact inf_le_left

omit [Finite V] in
theorem four_le : 4 ≤ Nat.card ↥(commV (pCoreOf 2 P)) := by
  rw [h.cardW]
  rcases Nat.eq_zero_or_pos e with he | he
  · exfalso
    have hR : pCoreOf 2 P = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [h.cardR, he, pow_zero])
    have hW : commV (pCoreOf 2 P) = ⊥ := by
      rw [hR, commV, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨x, hx, v, rfl⟩
      rw [Subgroup.mem_bot] at hx
      simp [hx]
    have := h.cardW
    rw [hW, Subgroup.card_bot, he] at this
    norm_num at this
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite V] in
theorem le_stabSub_W : P ≤ stabSub (commV (pCoreOf 2 P)) :=
  fun _ hp => mem_stabSub_commV (h.le_normalizer_rad hp)

omit [Finite V] in
theorem le_stabSub_Z : P ≤ stabSub (Subgroup.zpowers z) :=
  fun _ hp => centSub_le_stabSub _ (h.fixz hp)

theorem commSub_rad_le : commSub (commV (pCoreOf 2 P)) (pCoreOf 2 P) ≤ Subgroup.zpowers z :=
  commSub_le_of_irr h.sq h.zpowers_le h.card_zpowers h.four_le h.isPGroup_rad
    (fun _ hr => h.le_stabSub_W (h.rad_le hr)) (fun _ hr => h.fixz (h.rad_le hr))
    h.le_normalizer_rad h.le_stabSub_W h.le_stabSub_Z h.irrW

theorem W_ne_top : commV (pCoreOf 2 P) ≠ ⊤ := by
  intro hW
  have h1 := h.commSub_rad_le
  rw [hW, ← commV_eq_commSub, hW] at h1
  have h2 := Subgroup.card_le_of_le h1
  rw [Subgroup.card_top, h.card_zpowers] at h2
  have h3 := h.four_le
  rw [hW, Subgroup.card_top] at h3
  omega

omit [Finite V] in
theorem rad_inf_centSub : pCoreOf 2 P ⊓ centSub (commV (pCoreOf 2 P)) = ⊥ := by
  by_contra hne
  have hN := h.min _ inf_le_left hne fun p hp => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_rad hp) x)
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centSub (h.le_stabSub_W hp)) x)
  have hRW : pCoreOf 2 P ≤ centSub (commV (pCoreOf 2 P)) := by
    have h1 := (inf_le_right : pCoreOf 2 P ⊓ centSub (commV (pCoreOf 2 P)) ≤ _)
    rwa [hN] at h1
  have hWfix : commV (pCoreOf 2 P) ≤ fixV (pCoreOf 2 P) := fun w hw r hr => hRW hr w hw
  have hWZ : commV (pCoreOf 2 P) = Subgroup.zpowers z := by
    rw [← h.fixW]
    exact (inf_eq_left.mpr hWfix).symm
  have h4 := h.four_le
  rw [hWZ, h.card_zpowers] at h4
  omega

theorem eq_of_stab {Y : Subgroup V} (hY : Y ≤ commV (pCoreOf 2 P)) (hPY : P ≤ stabSub Y) :
    Y = ⊥ ∨ Y = Subgroup.zpowers z ∨ Y = commV (pCoreOf 2 P) := by
  by_cases hZY : Subgroup.zpowers z ≤ Y
  · rcases eq_or_lt_of_le hZY with heq | hlt
    · exact Or.inr (Or.inl heq.symm)
    · exact Or.inr (Or.inr (h.irrW Y hlt hY hPY))
  · left
    by_contra hYne
    have hYZ : Y ⊓ Subgroup.zpowers z = ⊥ := by
      have hd : Nat.card ↥(Y ⊓ Subgroup.zpowers z) ∣ 2 :=
        h.card_zpowers ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hZY
        have : Y ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, h.card_zpowers])
        rw [← this]
        exact inf_le_left
    have hlt : Subgroup.zpowers z < Y ⊔ Subgroup.zpowers z := by
      refine lt_of_le_of_ne le_sup_right fun heq => hYne ?_
      have h5 : Y ≤ Subgroup.zpowers z := heq ▸ le_sup_left
      have h6 : Y = Y ⊓ Subgroup.zpowers z := (inf_eq_left.mpr h5).symm
      rw [h6, hYZ]
    have hYW : Y ⊔ Subgroup.zpowers z = commV (pCoreOf 2 P) :=
      h.irrW _ hlt (sup_le hY h.zpowers_le) fun p hp =>
        sup_mem_stabSub (hPY hp) (h.le_stabSub_Z hp)
    have hRY : commSub Y (pCoreOf 2 P) = ⊥ := by
      rw [eq_bot_iff, ← hYZ]
      refine le_inf (commSub_le_self fun r hr => hPY (h.rad_le hr)) ?_
      exact (commSub_mono hY le_rfl).trans h.commSub_rad_le
    have hWfix : commV (pCoreOf 2 P) ≤ fixV (pCoreOf 2 P) := by
      rw [← hYW]
      exact sup_le (commSub_eq_bot_iff.mp hRY) fun u hu r hr => h.fixz (h.rad_le hr) u hu
    have hWZ : commV (pCoreOf 2 P) = Subgroup.zpowers z := by
      rw [← h.fixW]
      exact (inf_eq_left.mpr hWfix).symm
    have h4 := h.four_le
    rw [hWZ, h.card_zpowers] at h4
    omega

theorem faith_of_irr (hirr : ∀ Y : Subgroup V, commV (pCoreOf 2 P) < Y → P ≤ stabSub Y → Y = ⊤)
    {Q : Subgroup (MulAut V)} (hQ : IsPGroup 2 ↥Q)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (MulAut V)))
    (hQN : Q ≤ Subgroup.normalizer (P : Set (MulAut V))) :
    ∀ q ∈ Q, q ∈ centSub (commV (pCoreOf 2 P)) → (∀ p ∈ P, p * q = q * p) → q = 1 := by
  intro q hqQ hqW hqP
  have hQW : Q ≤ stabSub (commV (pCoreOf 2 P)) := fun q hq =>
    mem_stabSub_commV (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (hQN hq))
  have hVQ : commV Q ≤ commV (pCoreOf 2 P) :=
    commV_le_of_irr h.sq h.W_ne_top hQ hQW hPQ h.le_stabSub_W hirr
  let D : V →* V :=
    { toFun := fun v => q v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hD : ∀ v, D v = q v * v⁻¹ := fun _ => rfl
  have hDW : ∀ v, D v ∈ commV (pCoreOf 2 P) := fun v => hVQ (G6.mem_commV_of_mem hqQ v)
  have hDP : ∀ p ∈ P, ∀ v, D (p v) = p (D v) := by
    intro p hp v
    have e1 : q (p v) = p (q v) := by
      have := congrArg (fun φ : MulAut V => φ v) (hqP p hp)
      simpa [MulAut.mul_apply] using this.symm
    rw [hD, hD, map_mul, map_inv, e1]
  have hq1 : (∀ v, D v = 1) → q = 1 := by
    intro h1
    ext v
    have := h1 v
    rw [hD, mul_inv_eq_one] at this
    exact this
  have hPY : P ≤ stabSub D.range := by
    intro p hp
    refine mem_stabSub_of ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact ⟨p v, hDP p hp v⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨p⁻¹ v, hDP p⁻¹ (P.inv_mem hp) v⟩
  have hYW : D.range ≤ commV (pCoreOf 2 P) := by
    rintro _ ⟨v, rfl⟩
    exact hDW v
  rcases h.eq_of_stab hYW hPY with hY | hY | hY
  ·
    exact hq1 fun v => by
      have : D v ∈ D.range := ⟨v, rfl⟩
      rwa [hY, Subgroup.mem_bot] at this
  ·
    have hker : commV P ≤ D.ker := by
      rw [G6.commV_le_iff]
      intro p hp v
      rw [MonoidHom.mem_ker, map_mul, map_inv, hDP p hp]
      have hvz : D v ∈ Subgroup.zpowers z := hY ▸ ⟨v, rfl⟩
      rw [h.fixz hp _ hvz, mul_inv_cancel]
    rw [h.commP] at hker
    exact hq1 fun v => hker (Subgroup.mem_top v)
  ·
    exfalso
    have hW1 : ∀ w ∈ commV (pCoreOf 2 P), D w = 1 := fun w hw => by
      rw [hD, hqW w hw, mul_inv_cancel]
    have hPY' : P ≤ stabSub ((Subgroup.zpowers z).comap D) := by
      intro p hp
      refine mem_stabSub_of ?_ ?_
      · intro v hv
        show D (p v) ∈ Subgroup.zpowers z
        rw [hDP p hp]
        exact apply_mem_of_stabSub (h.le_stabSub_Z hp) hv
      · intro v hv
        show D (p⁻¹ v) ∈ Subgroup.zpowers z
        rw [hDP p⁻¹ (P.inv_mem hp)]
        exact apply_mem_of_stabSub (h.le_stabSub_Z (P.inv_mem hp)) hv
    have hlt : commV (pCoreOf 2 P) < (Subgroup.zpowers z).comap D := by
      refine lt_of_le_of_ne (fun w hw => ?_) fun heq => ?_
      · show D w ∈ Subgroup.zpowers z
        rw [hW1 w hw]
        exact Subgroup.one_mem _
      · have hzW : z ∈ D.range := hY ▸ h.zpowers_le (Subgroup.mem_zpowers z)
        obtain ⟨v, hv⟩ := hzW
        have hvY : v ∈ (Subgroup.zpowers z).comap D := by
          show D v ∈ Subgroup.zpowers z
          rw [hv]
          exact Subgroup.mem_zpowers z
        rw [← heq] at hvY
        exact h.ne (by rw [← hv, hW1 v hvY])
    have htop := hirr _ hlt hPY'
    have hWZ : commV (pCoreOf 2 P) ≤ Subgroup.zpowers z := by
      rw [← hY]
      rintro _ ⟨v, rfl⟩
      have : v ∈ (Subgroup.zpowers z).comap D := htop ▸ Subgroup.mem_top v
      exact this
    have h1 := Subgroup.card_le_of_le hWZ
    rw [h.card_zpowers] at h1
    have h4 := h.four_le
    omega

theorem eq_rad_of {Q : Subgroup (MulAut V)} (hQ : IsPGroup 2 ↥Q) (hRQ : pCoreOf 2 P ≤ Q)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (MulAut V)))
    (hQN : Q ≤ Subgroup.normalizer (P : Set (MulAut V)))
    (hQP : ∀ q ∈ Q, ∀ p ∈ P, q * p * q⁻¹ * p⁻¹ ∈ pCoreOf 2 P)
    (hQz : Q ≤ centSub (Subgroup.zpowers z))
    (hfaith : ∀ q ∈ Q, q ∈ centSub (commV (pCoreOf 2 P)) → (∀ p ∈ P, p * q = q * p) → q = 1) :
    Q = pCoreOf 2 P := by
  have : Finite (MulAut V) := finite_mulAut
  have hQW : Q ≤ stabSub (commV (pCoreOf 2 P)) := fun q hq =>
    mem_stabSub_commV (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (hQN hq))
  have hWQ : commSub (commV (pCoreOf 2 P)) Q ≤ Subgroup.zpowers z :=
    commSub_le_of_irr h.sq h.zpowers_le h.card_zpowers h.four_le hQ hQW hQz hPQ h.le_stabSub_W
      h.le_stabSub_Z h.irrW
  have hQC : Q ⊓ centSub (commV (pCoreOf 2 P)) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨hqQ, hqW⟩ := Subgroup.mem_inf.mp hq
    rw [Subgroup.mem_bot]
    have hqP : ∀ p ∈ P, p * q = q * p := by
      intro p hp
      have hc : q * p * q⁻¹ * p⁻¹ ∈ pCoreOf 2 P ⊓ centSub (commV (pCoreOf 2 P)) := by
        refine ⟨hQP q hqQ p hp, fun w hw => ?_⟩
        have hpw : p⁻¹ w ∈ commV (pCoreOf 2 P) := inv_apply_mem_of_stabSub (h.le_stabSub_W hp) hw
        have hq' : q⁻¹ (p⁻¹ w) = p⁻¹ w := by
          calc q⁻¹ (p⁻¹ w) = q⁻¹ (q (p⁻¹ w)) := by rw [hqW _ hpw]
            _ = p⁻¹ w := MulAut.inv_apply_self _ q _
        simp only [MulAut.mul_apply]
        rw [hq', MulAut.apply_inv_self, hqW w hw]
      rw [h.rad_inf_centSub, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
      exact hc.symm
    exact hfaith q hqQ hqW hqP
  have hcard := card_autSub_mul hQW
  rw [hQC, Subgroup.card_bot, mul_one] at hcard
  set z' : ↥(commV (pCoreOf 2 P)) := ⟨z, h.zpowers_le (Subgroup.mem_zpowers z)⟩ with hz'def
  have hz' : z' ≠ 1 := fun e1 => h.ne (congrArg Subtype.val e1)
  have htr : ∀ φ ∈ autSub Q (commV (pCoreOf 2 P)), IsTransvectionWith φ z' := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    refine ⟨hz', fun w => ?_⟩
    have hm : (g : MulAut V) w * (w : V)⁻¹ ∈ Subgroup.zpowers z :=
      hWQ (Subgroup.subset_closure ⟨g, hg, w, w.2, rfl⟩)
    rcases eq_one_or_eq_of_mem_zpowers (h.sq z) hm with h1 | h1
    · left
      apply Subtype.ext
      rw [resHom_apply]
      exact mul_inv_eq_one.mp h1
    · right
      apply Subtype.ext
      rw [resHom_apply]
      show (g : MulAut V) w = (w : V) * z
      rw [mul_inv_eq_iff_eq_mul] at h1
      rw [h1, mul_comm]
  have : Finite (MulAut ↥(commV (pCoreOf 2 P))) := finite_mulAut
  have hle : Nat.card ↥(autSub Q (commV (pCoreOf 2 P))) ≤
      Nat.card {t : MulAut ↥(commV (pCoreOf 2 P)) // IsTransvectionWith t z'} :=
    Nat.card_le_card_of_injective (fun φ => ⟨φ.1, htr φ.1 φ.2⟩) fun a b hab =>
      Subtype.ext (congrArg (fun s : {t : MulAut ↥(commV (pCoreOf 2 P)) //
        IsTransvectionWith t z'} => s.1) hab)
  rw [card_transvections h.sq _ z' hz'] at hle
  have hrk : rk ↥(commV (pCoreOf 2 P)) = e + 1 := by
    unfold rk
    rw [h.cardW, padicValNat.prime_pow]
  rw [hrk, Nat.add_sub_cancel] at hle
  exact (Subgroup.eq_of_le_of_card_ge hRQ (by rw [h.cardR, ← hcard]; exact hle)).symm

theorem sup_zpowers_spec {t : MulAut V} (ht : t ∈ Subgroup.normalizer (P : Set (MulAut V)))
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (htP : ∀ p ∈ P, t * p * t⁻¹ * p⁻¹ ∈ pCoreOf 2 P)
    (htz : t z = z) :
    IsPGroup 2 ↥(pCoreOf 2 P ⊔ Subgroup.zpowers t) ∧
      P ≤ Subgroup.normalizer ((pCoreOf 2 P ⊔ Subgroup.zpowers t : Subgroup (MulAut V)) :
        Set (MulAut V)) ∧
      pCoreOf 2 P ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set (MulAut V)) ∧
      (∀ q ∈ pCoreOf 2 P ⊔ Subgroup.zpowers t, ∀ p ∈ P, q * p * q⁻¹ * p⁻¹ ∈ pCoreOf 2 P) ∧
      pCoreOf 2 P ⊔ Subgroup.zpowers t ≤ centSub (Subgroup.zpowers z) := by
  have : Finite (MulAut V) := finite_mulAut
  set R := pCoreOf 2 P with hRdef
  have htR : t ∈ Subgroup.normalizer (R : Set (MulAut V)) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P ht
  let K : Subgroup (MulAut V) :=
    { carrier := {q | q ∈ Subgroup.normalizer (R : Set (MulAut V)) ∧
        ∀ p ∈ P, q * p * q⁻¹ * p⁻¹ ∈ R}
      one_mem' := ⟨Subgroup.one_mem _, fun p _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, fun p hp => ?_⟩
        have e : a * b * p * (a * b)⁻¹ * p⁻¹ =
            (a * (b * p * b⁻¹ * p⁻¹) * a⁻¹) * (a * p * a⁻¹ * p⁻¹) := by group
        rw [e]
        exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb p hp)) (ha p hp)
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨Subgroup.inv_mem _ haN, fun p hp => ?_⟩
        have e : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ = a⁻¹ * (a * p * a⁻¹ * p⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp
          (R.inv_mem (ha p hp)) }
  have hRK : R ≤ K := by
    intro r hr
    refine ⟨Subgroup.le_normalizer hr, fun p hp => ?_⟩
    have e : r * p * r⁻¹ * p⁻¹ = r * (p * r⁻¹ * p⁻¹) := by group
    rw [e]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer_rad hp) _).mp
      (R.inv_mem hr))
  have htK : t ∈ K := ⟨htR, htP⟩
  set Q := R ⊔ Subgroup.zpowers t with hQdef
  have hQK : Q ≤ K := sup_le hRK (Subgroup.zpowers_le.mpr htK)
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    obtain ⟨k, hk⟩ := ht2
    have hd : Nat.card ↥(Subgroup.zpowers t) ∣ 2 ^ k := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card hj
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hQdef, sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hT2 h.isPGroup_rad
      (Subgroup.zpowers_le.mpr htR)
  have hPQ : P ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
    have key : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q := by
      intro p hp x hx
      have hle : Q ≤ Q.comap (MulAut.conj p).toMonoidHom := by
        refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)
        · exact Subgroup.mem_sup_left
            ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer_rad hp) r).mp hr)
        · show p * t * p⁻¹ ∈ Q
          have hc : p * t * p⁻¹ * t⁻¹ ∈ R := by
            have := R.inv_mem (htP p hp)
            have e : (t * p * t⁻¹ * p⁻¹)⁻¹ = p * t * p⁻¹ * t⁻¹ := by group
            rwa [e] at this
          have e : p * t * p⁻¹ = (p * t * p⁻¹ * t⁻¹) * t := by group
          rw [e]
          exact Q.mul_mem (Subgroup.mem_sup_left hc)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      exact hle hx
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key p hp x, fun hx => ?_⟩
    have := key p⁻¹ (P.inv_mem hp) _ hx
    rwa [show p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x by group] at this
  have hQN : Q ≤ Subgroup.normalizer (P : Set (MulAut V)) :=
    sup_le (fun r hr => Subgroup.le_normalizer (h.rad_le hr)) (Subgroup.zpowers_le.mpr ht)
  have hQz : Q ≤ centSub (Subgroup.zpowers z) := by
    refine sup_le (fun r hr => h.fixz (h.rad_le hr)) (Subgroup.zpowers_le.mpr ?_)
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, htz]
  exact ⟨hQ2, hPQ, hQN, fun q hq => (hQK hq).2, hQz⟩

theorem mem_rad_of {t : MulAut V} (ht : t ∈ Subgroup.normalizer (P : Set (MulAut V)))
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (htP : ∀ p ∈ P, t * p * t⁻¹ * p⁻¹ ∈ pCoreOf 2 P)
    (htz : t z = z)
    (hfaith : ∀ q ∈ pCoreOf 2 P ⊔ Subgroup.zpowers t, q ∈ centSub (commV (pCoreOf 2 P)) →
      (∀ p ∈ P, p * q = q * p) → q = 1) : t ∈ pCoreOf 2 P := by
  obtain ⟨hQ2, hPQ, hQN, hQP, hQz⟩ := h.sup_zpowers_spec ht ht2 htP htz
  have hQR := h.eq_rad_of hQ2 le_sup_left hPQ hQN hQP hQz hfaith
  have htQ : t ∈ pCoreOf 2 P ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rw [hQR] at htQ
  exact htQ

theorem mem_rad (hirr : ∀ Y : Subgroup V, commV (pCoreOf 2 P) < Y → P ≤ stabSub Y → Y = ⊤)
    {t : MulAut V} (ht : t ∈ Subgroup.normalizer (P : Set (MulAut V)))
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (htP : ∀ p ∈ P, t * p * t⁻¹ * p⁻¹ ∈ pCoreOf 2 P)
    (htz : t z = z) : t ∈ pCoreOf 2 P := by
  obtain ⟨hQ2, hPQ, hQN, -, -⟩ := h.sup_zpowers_spec ht ht2 htP htz
  exact h.mem_rad_of ht ht2 htP htz (h.faith_of_irr hirr hQ2 hPQ hQN)

end Hyp

end CFSG.Quasithin.H13.L8211
