module

public import CFSG.Quasithin.Background.InternalSecB4

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_sec_cube (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)}
    {A C : Subgroup V} (hKA : K ≤ stabSub A ⊓ stabSub C)
    (hirr : XMod.IsIrrSec ↥(autSec K A C) (⊥ : Subgroup (Sec A C)) ⊤)
    (hnc : ∃ a b : ↥(autSec K A C), a * b ≠ b * a) {y s : MulAut V} (hy3 : y ^ 3 = 1)
    (hcube : ∀ v ∈ A, v * y v * y (y v) = 1) (hyK : ∀ k ∈ K, k * y = y * k)
    (hsK : ∀ k ∈ K, k * s = s * k) {e : ℕ} (hs2 : s ^ 2 ^ e = 1) (hsy : s * y * s⁻¹ = y⁻¹)
    (hyA : y ∈ stabSub A ⊓ stabSub C) (hsA : s ∈ stabSub A ⊓ stabSub C) : False := by
  classical
  set Y : Subgroup (MulAut V) := stabSub A ⊓ stabSub C with hY
  have hYW : Y ≤ stabSub A := inf_le_left
  have hYU : Y ≤ stabSub C := inf_le_right
  set φ := B5.secHom Y hYW hYU with hφ
  set B := autSec K A C with hB
  have hBmap : (K.subgroupOf Y).map φ = B := B5.map_secHom_eq_autSec Y hYW hYU hKA
  have hcommB : ∀ g : ↥Y, (∀ k ∈ K, k * (g : MulAut V) = (g : MulAut V) * k) →
      φ g ∈ XMod.eqvAut ↥B (Sec A C) := by
    intro g hg a p
    have ha : (a : MulAut (Sec A C)) ∈ (K.subgroupOf Y).map φ := by
      rw [hBmap]
      exact a.2
    obtain ⟨k, hk, hka⟩ := ha
    have hkg : k * g = g * k := Subtype.ext (hg k (Subgroup.mem_subgroupOf.mp hk))
    show φ g ((a : MulAut (Sec A C)) p) = (a : MulAut (Sec A C)) (φ g p)
    rw [← hka, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hkg]
  have hP : ∀ p : Sec A C, p ^ 2 = 1 := by
    intro p
    induction p using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_pow]
      have : v ^ 2 = 1 := Subtype.ext (by simpa using hV v)
      rw [this, QuotientGroup.mk_one]
  have hodd := odd_card_eqvAut_of_irr hP hirr hnc
  set sb : ↥(XMod.eqvAut ↥B (Sec A C)) := ⟨φ ⟨s, hsA⟩, hcommB _ hsK⟩ with hsb
  have hsb2 : sb ^ 2 ^ e = 1 := by
    apply Subtype.ext
    show (φ ⟨s, hsA⟩) ^ 2 ^ e = 1
    rw [← map_pow]
    have : (⟨s, hsA⟩ : ↥Y) ^ 2 ^ e = 1 := Subtype.ext hs2
    rw [this, map_one]
  have hsb1 : sb = 1 := by
    have h1 : orderOf sb ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hsb2
    have h2 : orderOf sb ∣ Nat.card ↥(XMod.eqvAut ↥B (Sec A C)) := orderOf_dvd_natCard sb
    have hcop : Nat.Coprime (2 ^ e) (Nat.card ↥(XMod.eqvAut ↥B (Sec A C))) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rwa [orderOf_eq_one_iff] at h3
  have hs1 : φ ⟨s, hsA⟩ = 1 := congrArg Subtype.val hsb1
  have h1 : φ ⟨y, hyA⟩ = (φ ⟨y, hyA⟩)⁻¹ := by
    have e' : (⟨s, hsA⟩ : ↥Y) * ⟨y, hyA⟩ * (⟨s, hsA⟩ : ↥Y)⁻¹ = (⟨y, hyA⟩ : ↥Y)⁻¹ :=
      Subtype.ext hsy
    have h2 := congrArg φ e'
    rw [map_mul, map_mul, map_inv, map_inv, hs1, one_mul, inv_one, mul_one] at h2
    exact h2
  have h3 : (φ ⟨y, hyA⟩) ^ 3 = 1 := by
    have e' : (⟨y, hyA⟩ : ↥Y) ^ 3 = 1 := Subtype.ext hy3
    rw [← map_pow, e', map_one]
  have h2 : φ ⟨y, hyA⟩ * φ ⟨y, hyA⟩ = 1 := by
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  have hy1 : φ ⟨y, hyA⟩ = 1 := by
    have e' : φ ⟨y, hyA⟩ = (φ ⟨y, hyA⟩) ^ 3 * (φ ⟨y, hyA⟩ * φ ⟨y, hyA⟩)⁻¹ := by group
    rw [e', h3, h2, inv_one, one_mul]
  have hyker : (⟨y, hyA⟩ : ↥Y) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact hy1
  have hyV : ∀ v ∈ A, y v * v⁻¹ ∈ C := fun v hv =>
    ((B5.mem_ker_secHom Y hYW hYU _).1 hyker).2 v hv
  have hall : ∀ v ∈ A, v ∈ C := by
    intro v hv
    have hyvA : y v ∈ A := ((hyA.1) v).2 hv
    set a := y v * v⁻¹ with ha
    set b := y (y v) * (y v)⁻¹ with hb
    have haC : a ∈ C := hyV v hv
    have hbC : b ∈ C := hyV (y v) hyvA
    have hya : y v = a * v := by rw [ha, inv_mul_cancel_right]
    have hyb : y (y v) = b * (a * v) := by rw [hb, ← hya, inv_mul_cancel_right]
    have hvv : v * v = 1 := by rw [← sq]; exact hV v
    have hc := hcube v hv
    rw [hyb, hya] at hc
    have e' : a * a * b * v = 1 := by
      calc a * a * b * v = a * a * b * v * (v * v) := by rw [hvv, mul_one]
        _ = v * (a * v) * (b * (a * v)) := by
          simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = 1 := hc
    have e'' : v = (a * a * b)⁻¹ := eq_inv_of_mul_eq_one_right e'
    rw [e'']
    exact C.inv_mem (C.mul_mem (C.mul_mem haC haC) hbC)
  apply hirr.1.ne
  refine eq_top_iff.mpr fun p _ => ?_
  induction p using QuotientGroup.induction_on with
  | H v =>
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hall v v.2

theorem false_of_qsec_cube (hV : ∀ v : V, v ^ 2 = 1) {X K : Subgroup (MulAut V)}
    {C : Subgroup V} (hQ : QSec X K C) {y s : MulAut V} (hy3 : y ^ 3 = 1)
    (hcube : ∀ v, v * y v * y (y v) = 1) (hyK : ∀ k ∈ K, k * y = y * k)
    (hsK : ∀ k ∈ K, k * s = s * k) {e : ℕ} (hs2 : s ^ 2 ^ e = 1) (hsy : s * y * s⁻¹ = y⁻¹)
    (hyC : y ∈ stabSub C) (hsC : s ∈ stabSub C) : False :=
  false_of_sec_cube hV hQ.stabK hQ.isIrrSec_autSec hQ.exists_noncomm_autSec hy3
    (fun v _ => hcube v) hyK hsK hs2 hsy ⟨mem_stabSub_top y, hyC⟩ ⟨mem_stabSub_top s, hsC⟩

end CFSG.Quasithin.H13.A6.A6S20
