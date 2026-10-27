module

public import CFSG.RankThree.PartOne.ZR7.Core
public import CFSG.RankThree.PartOne.K1214.CycFinal
public import CFSG.RankThree.PartOne.SP4GA.Irred
public import CFSG.RankThree.PartOne.SP4GA.Lift
public import CFSG.RankThree.PartOne.SP4GA.RSide
import CFSG.RankThree.PartOne.KF.FratRows
import CFSG.RankThree.PartOne.SP4C.Row7

public section

namespace CFSG.RankThree.PartOne.ZR7

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SP4GA
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

variable {G : Type} [Group G]

theorem comm_of_isCyclic_subgroup {H : Subgroup G} (hH : IsCyclic ↥H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  intro x hx y hy
  let _ : CommGroup ↥H := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥H) ⟨y, hy⟩)

theorem exists_mul_of_mem_sup {R Z : Subgroup G} (h : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) {q : G}
    (hq : q ∈ Z ⊔ R) : ∃ x ∈ R, ∃ z ∈ Z, q = x * z := by
  let T : Subgroup G :=
    { carrier := {q | ∃ x ∈ R, ∃ z ∈ Z, q = x * z}
      mul_mem' := by
        rintro _ _ ⟨x, hx, z, hz, rfl⟩ ⟨x', hx', z', hz', rfl⟩
        refine ⟨x * x', R.mul_mem hx hx', z * z', Z.mul_mem hz hz', ?_⟩
        calc x * z * (x' * z') = x * (z * x') * z' := by group
          _ = x * (x' * z) * z' := by rw [h z hz x' hx']
          _ = x * x' * (z * z') := by group
      one_mem' := ⟨1, R.one_mem, 1, Z.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨x, hx, z, hz, rfl⟩
        refine ⟨x⁻¹, R.inv_mem hx, z⁻¹, Z.inv_mem hz, ?_⟩
        calc (x * z)⁻¹ = z⁻¹ * x⁻¹ := by group
          _ = x⁻¹ * z⁻¹ := h z⁻¹ (Z.inv_mem hz) x⁻¹ (R.inv_mem hx) }
  have hle : Z ⊔ R ≤ T :=
    sup_le (fun z hz => ⟨1, R.one_mem, z, hz, (one_mul z).symm⟩)
      (fun x hx => ⟨x, hx, 1, Z.one_mem, (mul_one x).symm⟩)
  exact hle hq

theorem conj_eq_of_conj_eq {β u : G} (h : u * β * u⁻¹ = β) : β * u * β⁻¹ = u := by
  have h2 : u * β = β * u := mul_inv_eq_iff_eq_mul.1 h
  calc β * u * β⁻¹ = (u * β) * β⁻¹ := by rw [h2]
    _ = u := mul_inv_cancel_right u β

section Frame

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {b : G}
  {K I X P Q : Subgroup G}

theorem exists_swap (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) (hC : Choice1212 p E b I X P Q)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) {β β' : G} (hβ : β ∈ E ⊓ L) (hβ1 : β ≠ 1)
    (hβ' : β' ∈ E ⊓ L) (hβ'n : β' ∉ Subgroup.zpowers β) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), n * β * n⁻¹ ∉ Subgroup.zpowers β ∧
      ∀ x ∈ P, c * (n * x * n⁻¹) * c⁻¹ = n * (c * x * c⁻¹) * n⁻¹ := by
  classical
  obtain ⟨w, hwL, hwE, hwnot⟩ := exists_not_invariant ctx hβ hβ1 hβ' hβ'n
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := ctx.hyp.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hwc : w * c = c * w := Subgroup.mem_centralizer_singleton_iff.1 (hLc hwL)
  have hwcw : w * c * w⁻¹ = c := by rw [hwc]; group
  have hcE : c ∈ E := c_mem_E ctx
  obtain ⟨n, hnP, -, hnmod, hnfix⟩ := exists_lift ctx hnH hC hPE hwE
  have hwβ : w * β * w⁻¹ ∈ E ⊓ L :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hwE _).1 (Subgroup.mem_inf.1 hβ).1,
      L.mul_mem (L.mul_mem hwL (Subgroup.mem_inf.1 hβ).2) (L.inv_mem hwL)⟩
  refine ⟨n, hnP, ?_, ?_⟩
  · rw [hnfix β hβ hwβ]
    exact hwnot
  ·
    have h1 := hnmod c hcE
    rw [hwcw] at h1
    intro x hx
    have hy : n * x * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hnP x).1 hx
    have hcP : c ∈ P := E_le_P hC hcE
    have hu : c * (n * x * n⁻¹) * c⁻¹ ∈ P := P.mul_mem (P.mul_mem hcP hy) (P.inv_mem hcP)
    have hfix := fix_B ctx hnH hC hPE hu h1
    have e1 : n * (c * x * c⁻¹) * n⁻¹ = (n * c * n⁻¹ * c⁻¹) * (c * (n * x * n⁻¹) * c⁻¹) *
        (n * c * n⁻¹ * c⁻¹)⁻¹ := by group
    rw [e1]
    exact (conj_eq_of_conj_eq hfix).symm

theorem clauses_of_base (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) (hC : Choice1212 p E b I X P Q)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) {R Z : Subgroup G}
    (hcd : CycBase p c b E P Q R Z) (hQn : (Q.subgroupOf P).Normal) (hbL : b ∈ L)
    [IsCyclic ↥R] [IsCyclic ↥Z] (hpR : p ∣ Nat.card ↥R) (hRc : ∃ r ∈ R, c * r ≠ r * c)
    (hRE : ∀ x ∈ R, x ^ p = 1 → x ∈ E ⊓ L) :
    Nat.card Z = Nat.card R ∧
      Nat.card Z = p * Nat.card ↥(Z ⊓ Subgroup.centralizer ({c} : Set G)) := by
  classical
  have hp := hcd.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hfP, hPf⟩ := hcd.P_gen
  have hRZ := hcd.ZR
  have hRab := hcd.R_ab
  have hZab := comm_of_isCyclic_subgroup (H := Z) inferInstance
  have hRQ : R ≤ Q := by rw [hcd.Q_eq]; exact le_sup_right
  have hZQ : Z ≤ Q := by rw [hcd.Q_eq]; exact le_sup_left
  have hQRZ : ∀ q ∈ Q, ∃ x ∈ R, ∃ z ∈ Z, q = x * z := fun q hq =>
    exists_mul_of_mem_sup hRZ (hcd.Q_eq ▸ hq)
  have hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := hQRZ q hq
    obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := hQRZ q' hq'
    calc x₁ * z₁ * (x₂ * z₂) = x₁ * (z₁ * x₂) * z₂ := by group
      _ = (x₁ * x₂) * (z₁ * z₂) := by rw [hRZ z₁ hz₁ x₂ hx₂]; group
      _ = (x₂ * x₁) * (z₂ * z₁) := by rw [hRab x₁ hx₁ x₂ hx₂, hZab z₁ hz₁ z₂ hz₂]
      _ = x₂ * (x₁ * z₂) * z₁ := by group
      _ = x₂ * z₂ * (x₁ * z₁) := by rw [← hRZ z₂ hz₂ x₁ hx₁]; group
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpR
  have hb'R : (x : G) ∈ R := x.2
  have hb'p : (x : G) ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hb'1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hbEL : b ∈ E ⊓ L := ⟨hcd.b_E, hbL⟩
  have hb'EL : (x : G) ∈ E ⊓ L := hRE _ hb'R hb'p
  have hbn : b ∉ Subgroup.zpowers (x : G) := by
    intro h
    have h1 : b ∈ R ⊓ Z := ⟨Subgroup.zpowers_le.2 hb'R h, hcd.b_Z⟩
    rw [hcd.ZR_bot, Subgroup.mem_bot] at h1
    exact hcd.b_ne h1
  have hb'n : (x : G) ∉ Subgroup.zpowers b := by
    intro h
    have h1 : (x : G) ∈ R ⊓ Z := ⟨hb'R, Subgroup.zpowers_le.2 hcd.b_Z h⟩
    rw [hcd.ZR_bot, Subgroup.mem_bot] at h1
    exact hb'1 h1
  obtain ⟨n₁, hn₁P, hn₁b, hn₁c⟩ := exists_swap ctx hnH hC hPE hb'EL hb'1 hbEL hbn
  obtain ⟨n₂, hn₂P, hn₂b, -⟩ := exists_swap ctx hnH hC hPE hbEL hcd.b_ne hb'EL hb'n
  have hZc := exists_noncomm_Z hp hcd.P_p hcd.Q_le hQn hfP hPf hcd.c_P hcd.c_Q hcd.c_p hRQ hQab
    hQRZ hcd.R_norm hRc hb'R hb'p hb'1 hn₁P hn₁b hn₁c
  refine ⟨card_Z_eq hp hcd.P_p hcd.Q_le hQn hfP hPf hcd.c_P hcd.c_Q hcd.c_p hRQ hZQ hQab hQRZ
    hcd.R_norm hcd.Z_norm hRc hZc hb'R hb'p hb'1 hcd.b_Z hcd.b_p hcd.b_ne hn₁P hn₁b hn₂P hn₂b, ?_⟩
  refine card_Z_eq_mul hp hcd.Z_norm hcd.c_P hcd.b_Z hcd.b_p hcd.b_ne ?_ hZc
  intro z hz
  have h1 := mod_B ctx hnH hC hPE (hcd.Z_le hz) hcd.c_E
  have h2 : c * z * c⁻¹ * z⁻¹ = (z * c * z⁻¹ * c⁻¹)⁻¹ := by group
  rw [h2]
  exact Sec12Three.pow_eq_one_of_mem_E ctx.hyp (E.inv_mem h1.1)

theorem zr7_clauses
    (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes) (hU5 : KF1214U5)
    (hFix : FieldFixedPElements) (ctx : Fus12Ctx G p A c L E) (h7 : RowModel p L 7)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) (hgen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) :
    (∀ z ∈ Subgroup.centralizer (I : Set G) ⊓ P, ∀ z' ∈ Subgroup.centralizer (I : Set G) ⊓ P,
      z * z' = z' * z) ∧
    Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) = Monoid.exponent ↥(P ⊓ I) ∧
    Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) =
      p * Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P ⊓
        Subgroup.centralizer ({c} : Set G)) := by
  classical
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Fact p.Prime := ⟨hp⟩
  have hKR' := hKR G p A c L E ctx b K I X P Q hL hC hF
  obtain ⟨r, e, hr, he2, hEcard, ⟨φ⟩⟩ := R_equiv hRig h112 ctx hL hC hF hKR'
  have hE3 : Nat.card E = p ^ 3 := by
    obtain ⟨K', hKf, hKfin, hζ, ⟨S⟩⟩ := SP4C.exists_r7ctx_core ctx.table_core h7
    have h1 := KFU.D8Ctx.card_F S hp.pos hζ
    rw [ctx.ten.2.1, h1]
    ring
  have hr1 : r = 1 := by
    have h1 : p ^ (r + 2) = p ^ 3 := hEcard.symm.trans hE3
    have := Nat.pow_right_injective hp.two_le h1
    omega
  subst hr1
  have hout := kf1214Struct_holds h112 hRig hKR hU5 G p A c L E ctx b K I X P Q hL hC hF
  have hcd := cycBase_of_ctx h112 ctx hL hC hF hgen hr he2 hEcard φ
  have hexp : Monoid.exponent ↥(P ⊓ I) = p ^ e := by
    rw [Monoid.exponent_eq_of_mulEquiv φ]
    exact exponent_pi_eq (by omega) le_rfl
  have hRcyc : IsCyclic ↥(P ⊓ I) := by
    have φ' : ↥(P ⊓ I) ≃* Multiplicative (ZMod (p ^ e)) := φ.trans (MulEquiv.piUnique _)
    exact isCyclic_of_surjective φ'.symm φ'.symm.surjective
  have hRcard : Nat.card ↥(P ⊓ I) = p ^ e := by
    rw [← IsCyclic.exponent_eq_card, hexp]
  have hZcyc : IsCyclic ↥(Subgroup.centralizer (I : Set G) ⊓ P) := hout.C_cyc
  have hRc := c_not_centralize_R h112 hRig hKR hFix ctx hL hC hF
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := P_le_normalizer_of_omega hout.omega
  have hnH := not_dvd_torusImage ctx (hU5 G p A c L E ctx)
  have hpR : p ∣ Nat.card ↥(P ⊓ I) := by
    rw [hRcard]
    exact dvd_pow_self p (by omega)
  have hRE : ∀ x ∈ P ⊓ I, x ^ p = 1 → x ∈ E ⊓ L := by
    intro x hx hxp
    have hxQ : x ∈ Q := by
      rw [hC.Q_eq]
      exact Subgroup.mem_sup_right hx
    have hxE : x ∈ E := by
      rw [← hout.omega]
      exact Subgroup.subset_closure ⟨hx.1, hxp⟩
    rw [← hout.QE]
    exact ⟨hxQ, hxE⟩
  obtain ⟨hcard, hmul⟩ := clauses_of_base ctx hnH hC hPE hcd hout.Q_norm.2 hL.b_mem.2.1 hpR hRc hRE
  exact ⟨comm_of_isCyclic_subgroup hZcyc, hcard.trans IsCyclic.exponent_eq_card.symm, hmul⟩

end Frame

end CFSG.RankThree.PartOne.ZR7
