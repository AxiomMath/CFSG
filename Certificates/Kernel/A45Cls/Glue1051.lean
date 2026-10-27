
module

public import Certificates.Kernel.A45Cls.Glue107
public import Certificates.Kernel.A45Cls.CheckInv
public import Certificates.Kernel.A45Cls.Checks10
public import CFSG.LocalAnalysis.OddStandard.ONan76Sylow
public import Certificates.Data.OmegaF1051Facts
public import CFSG.Quasithin.H13.J4Core

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.BfsPin
  CFSG.KC.ConjOrb Certificates.OmegaS107 CFSG.ComponentClassification.GSThmB CFSG.ABGLocalTools

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

local notation "tA" => Certificates.P43Twin.tA ()

local notation "cC" => wvA czW

local notation "fU" => wvA (uW.getD 0 [])

abbrev CZ : Subgroup P45 := A ⊓ centralizer ({Certificates.OmegaT0.z0 ()} : Set P45)

@[expose] def Zc (z q x : P45) : Prop := q * x * q⁻¹ * x⁻¹ = 1 ∨ q * x * q⁻¹ * x⁻¹ = z

theorem zc_mul {z a b x : P45} (hz : z * z = 1) (ha : a * z = z * a) (hax : Zc z a x)
    (hbx : Zc z b x) : Zc z (a * b) x := by
  have e : a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by
    group
  have haz : a * z * a⁻¹ = z := by rw [ha]; group
  unfold Zc at *
  rw [e]
  rcases hbx with h1 | h1 <;> rcases hax with h2 | h2 <;> rw [h1, h2]
  · left
    group
  · right
    group
  · right
    rw [mul_one, haz]
  · left
    rw [haz, hz]

theorem zc_inv {z a x : P45} (hz : z * z = 1) (ha : a * z = z * a) (hax : Zc z a x) :
    Zc z a⁻¹ x := by
  have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a := by group
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have haz : a⁻¹ * z * a = z := by
    calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
      _ = a⁻¹ * (a * z) := by rw [ha]
      _ = z := by group
  unfold Zc at *
  rw [e]
  rcases hax with h | h <;> rw [h]
  · left
    group
  · right
    rw [hzi, haz]

theorem zc_symm {z a b : P45} (hz : z * z = 1) (h : Zc z a b) : Zc z b a := by
  have e : b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  unfold Zc at *
  rw [e]
  rcases h with h | h <;> rw [h]
  · left
    exact inv_one
  · right
    exact hzi

theorem zc_coset {z q r v : P45} (hz : z * z = 1) (hrz : r * z = z * r) (hqr : Zc z q r)
    (hqv : Zc z q v) : Zc z q (r * v) := by
  have e : q * (r * v) * q⁻¹ * (r * v)⁻¹ =
      (q * r * q⁻¹ * r⁻¹) * (r * (q * v * q⁻¹ * v⁻¹) * r⁻¹) := by group
  have hrz' : r * z * r⁻¹ = z := by rw [hrz]; group
  unfold Zc at *
  rw [e]
  rcases hqr with h1 | h1 <;> rcases hqv with h2 | h2 <;> rw [h1, h2]
  · left
    group
  · right
    rw [hrz']
    group
  · right
    group
  · left
    rw [hrz', hz]

theorem mul_inv_mem_of_card {H K : Subgroup P45} (hHK : H ≤ K) (hc : Nat.card K = 2 * Nat.card H)
    {t x : P45} (ht : t ∈ K) (htH : t ∉ H) (hx : x ∈ K) (hxH : x ∉ H) : x * t⁻¹ ∈ H := by
  have hH : (H.subgroupOf K).index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := H) (K := K)
    rw [inf_eq_left.2 hHK, hc] at h
    change H.relIndex K = 2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have h := (Subgroup.mul_mem_iff_of_index_two hH (a := (⟨x, hx⟩ : K)) (b := (⟨t, ht⟩ : K)⁻¹)).2
  have h1 : (⟨x, hx⟩ : K) ∈ H.subgroupOf K ↔ False :=
    iff_false_intro fun h => hxH (Subgroup.mem_subgroupOf.1 h)
  have h2 : (⟨t, ht⟩ : K)⁻¹ ∈ H.subgroupOf K ↔ False := by
    refine iff_false_intro fun h => htH ?_
    have := (H.subgroupOf K).inv_mem h
    simpa using Subgroup.mem_subgroupOf.1 this
  exact Subgroup.mem_subgroupOf.1 (h (by rw [h1, h2]))

theorem card_two {H K : Subgroup P45} {f : P45} (hf : f ∈ K) (hfH : f ∉ H)
    (hmul : ∀ b ∈ K, b ∉ H → b * f⁻¹ ∈ H) : Nat.card K = 2 * Nat.card ↥(H ⊓ K) := by
  have hidx : (H.subgroupOf K).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨(⟨f, hf⟩ : K)⁻¹, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    by_cases hb : (b : P45) ∈ H
    · refine Or.inr ⟨hb, fun h' => hfH ?_⟩
      have h := H.mul_mem (H.inv_mem h') hb
      have e : ((b : P45) * f⁻¹)⁻¹ * b = f := by group
      rwa [e] at h
    · exact Or.inl ⟨hmul b b.2 hb, hb⟩
  have h := Subgroup.relIndex_mul_card (H := H) (K := K)
  change (H.subgroupOf K).index * _ = _ at h
  rw [hidx] at h
  exact h.symm

theorem conj_mem_of_gens {s : Set P45} {H : Subgroup P45} (hH : closure s = H) {g : P45}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ H) : ∀ x ∈ H, g * x * g⁻¹ ∈ H := by
  intro x hx
  rw [← hH] at hx
  have hle : closure s ≤ H.comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    intro y hy
    exact h y hy
  exact hle hx

theorem card_le_of_imp {p q : P45 → Prop} (h : ∀ x, p x → q x) :
    Nat.card {x : P45 // p x} ≤ Nat.card {x : P45 // q x} :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1, h x.1 x.2⟩) fun a b e => by
    have e' := congrArg Subtype.val e
    exact Subtype.ext e'

theorem factorization_1152 : (1152 : ℕ).factorization 2 = 7 := by
  rw [show (1152 : ℕ) = 2 ^ 7 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem prep_z : PRep 45 6 zP z0 := prep_cOf _

theorem T0_le_A : T0 ≤ A := fun _ h =>
  CFSG.OddStandard.SmallF3.Omega.QP45_le_QA45 (X11.QT0_le h)

theorem z_conj : cC ∈ A ∧ PRep 45 6 czP cC ∧ PRep 45 6 cziP cC⁻¹ ∧ z0 = cC * tA * cC⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlet⟩ := binds3
  simp only [Bool.and_eq_true] at hlet
  obtain ⟨⟨hlc, hlci⟩, -⟩ := hlet
  have hcz : PRep 45 6 czP cC := (prep_wvA hlc).1
  have hczi : PRep 45 6 cziP (wvA cziW) := (prep_wvA hlci).1
  have hci : wvA cziW = cC⁻¹ := by
    have h := zFacts.2.1
    rw [isIdK_iff (prep_pcomp hn45 hcz hczi)] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [hci] at hczi
  have htA : PRep 45 6 (KA.T KA.r0) tA := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
    rw [← bt]
    exact prep_cOf _
  refine ⟨(prep_wvA hlc).2, hcz, hczi, ?_⟩
  rw [mul_assoc]
  exact eqP_sound zFacts.1 prep_z (prep_pcomp hn45 hcz (prep_pcomp hn45 htA hczi))

theorem z_sq : z0 * z0 = 1 := by
  rw [z_conj.2.2.2]
  calc cC * tA * cC⁻¹ * (cC * tA * cC⁻¹) = cC * (tA * tA) * cC⁻¹ := by group
    _ = 1 := by rw [tA_facts.2.1]; group

theorem z_ne : z0 ≠ 1 := by
  intro h
  apply tA_facts.2.2
  have e : tA = cC⁻¹ * z0 * cC := by rw [z_conj.2.2.2]; group
  rw [e, h]
  group

theorem mem_zpowers_z {x : P45} : x ∈ zpowers z0 ↔ x = 1 ∨ x = z0 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h2 : orderOf z0 = 2 := orderOf_eq_prime (by rw [sq]; exact z_sq) z_ne
    rw [← zpow_mod_orderOf, h2, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem z_T0 : z0 ∈ T0 ∧ ∀ t ∈ T0, t * z0 = z0 * t := by
  obtain ⟨c0, hc0, -⟩ := t0_enum
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨i, hi, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) zFacts.2.2.2.2.2.2.2 prep_z
    exact e ▸ (hc0 i hi).2
  · rw [← closure_t0g] at ht
    have hle : closure (t0g '' {k | k < 3}) ≤ centralizer ({z0} : Set P45) := by
      rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact mem_centralizer_singleton_iff.2
        (eq22_sound (PK.allN_iff.1 zFacts.2.2.2.2.1 k hk) prep_z (prep_t0g k hk) (prep_t0g k hk)
          prep_z).symm
    exact mem_centralizer_singleton_iff.1 (hle ht)

theorem q_z : ∀ q ∈ Q0, q * z0 = z0 * q :=
  fun q hq => z_T0.2 q (q0_le hq)

theorem card_CZ : Nat.card CZ = 1152 := by
  change Nat.card ↥(A ⊓ centralizer ({z0} : Set P45)) = 1152
  rw [z_conj.2.2.2, card_cent_conj z_conj.1]
  exact centA_eq.2.1

theorem conj_mem_centA {y : P45} (hy : y ∈ CZ) :
    cC⁻¹ * y * cC ∈ A ⊓ centralizer ({tA} : Set P45) := by
  obtain ⟨hyA, hyz⟩ := mem_inf.1 hy
  have hyz' := mem_centralizer_singleton_iff.1 hyz
  refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem z_conj.1) hyA) z_conj.1,
    mem_centralizer_singleton_iff.2 ?_⟩
  have htz : tA = cC⁻¹ * z0 * cC := by rw [z_conj.2.2.2]; group
  rw [htz]
  calc cC⁻¹ * y * cC * (cC⁻¹ * z0 * cC) = cC⁻¹ * (y * z0) * cC := by group
    _ = cC⁻¹ * (z0 * y) * cC := by rw [hyz']
    _ = cC⁻¹ * z0 * cC * (cC⁻¹ * y * cC) := by group

theorem ctz_sound {Q W : ℕ} {q w : P45} (h : f1051ctz zP Q W = true) (hq : PRep 45 6 Q q)
    (hw : PRep 45 6 W w) : Zc z0 q w := by
  unfold f1051ctz at h
  rw [Bool.or_eq_true] at h
  unfold Zc
  rcases h with h | h
  · left
    rw [eq22_sound h hq hw hw hq]
    group
  · right
    rw [eq22_sound h hq hw prep_z (prep_pcomp hn45 hw hq)]
    group

theorem ctz_of {Q W : ℕ} {q w : P45} (h : Zc z0 q w) (hq : PRep 45 6 Q q) (hw : PRep 45 6 W w) :
    f1051ctz zP Q W = true := by
  unfold f1051ctz
  rw [Bool.or_eq_true]
  unfold Zc at h
  rcases h with h | h
  · left
    refine eq22_of_eq hq hw hw hq ?_
    calc q * w = q * w * q⁻¹ * w⁻¹ * (w * q) := by group
      _ = w * q := by rw [h, one_mul]
  · right
    refine eq22_of_eq hq hw prep_z (prep_pcomp hn45 hw hq) ?_
    calc q * w = q * w * q⁻¹ * w⁻¹ * (w * q) := by group
      _ = z0 * (w * q) := by rw [h]

theorem q_zc : ∀ q ∈ Q0, ∀ r ∈ Q0, Zc z0 q r := by
  have h := f1051qcomm
  unfold f1051qcommK at h
  simp only [strictB_eq', Bool.and_eq_true] at h
  have hgen : ∀ i < 4, ∀ j < 4, Zc z0 (qg i) (qg j) := fun i hi j hj =>
    ctz_sound (PK.allN_iff.1 (PK.allN_iff.1 h.2 i hi) j hj) (prep_qg i hi) (prep_qg j hj)
  have h1 : ∀ q ∈ Q0, ∀ j < 4, Zc z0 q (qg j) := by
    intro q hq j hj
    rw [← closure_qg] at hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hgen i hi j hj
    | one =>
      left
      group
    | mul a b ha _ iha ihb =>
      exact zc_mul z_sq (q_z a (closure_qg ▸ ha)) iha ihb
    | inv a ha iha => exact zc_inv z_sq (q_z a (closure_qg ▸ ha)) iha
  intro q hq r hr
  apply zc_symm z_sq
  rw [← closure_qg] at hr
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact zc_symm z_sq (h1 q hq j hj)
  | one =>
    left
    group
  | mul a b ha _ iha ihb => exact zc_mul z_sq (q_z a (closure_qg ▸ ha)) iha ihb
  | inv a ha iha => exact zc_inv z_sq (q_z a (closure_qg ▸ ha)) iha

theorem card_Q0 : Nat.card Q0 = 32 := by
  obtain ⟨-, -, -, hcard⟩ := enum_A prep_qg QZ.cl QZ.tr (by decide) ids3.2.1 QZ.k
  rwa [closure_qg] at hcard

theorem q_words {c : ℕ → P45} (hc : ∀ i < 32, PRep 45 6 (QZ.T i) (c i)) (hc0 : c 0 = 1) :
    ∀ d, ∀ i < 32, tDep (QZ.D i) = d →
      ∃ l : List P45, (∀ g ∈ l, g ∈ [Certificates.OmegaF1051.gq1 (),
        Certificates.OmegaF1051.gq2 (), Certificates.OmegaF1051.gq3 (),
        Certificates.OmegaF1051.gq4 ()]) ∧ l.length ≤ d ∧ l.prod = c i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi hd
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨[], by simp, by simp, by rw [hc0]; rfl⟩
    · have htr : treePt 4 32 0 QZ.E QZ.D i = true := QZ.tr i hi
      obtain ⟨hp, hlab, he, hdep⟩ := treePt_spec htr hi0
      obtain ⟨l, hl, hlen, hprod⟩ := ih _ (by omega) _ hp rfl
      have hcl : closPtL 45 6 4 32 QZ.G QZ.T QZ.E (tPar (QZ.D i)) = true := QZ.cl _ hp
      obtain ⟨-, hstep⟩ := closPtL_spec hcl
      obtain ⟨-, hT⟩ := hstep _ hlab
      rw [he] at hT
      have hpr := prep_pcomp hn45 (prep_qg _ hlab) (hc _ hp)
      rw [hT] at hpr
      refine ⟨qg (tLab (QZ.D i)) :: l, fun g hg => ?_, by simp; omega, ?_⟩
      · rcases List.mem_cons.1 hg with rfl | hg
        · generalize tLab (QZ.D i) = k at hlab
          interval_cases k <;> simp [qg]
        · exact hl g hg
      · rw [List.prod_cons, hprod]
        exact prep_eq hpr (hc i hi)

theorem mem_q0l {g : P45} : g ∈ Certificates.OmegaF1051.q0l () ↔ g ∈ Q0 := by
  constructor
  · intro hx
    refine CFSG.OddStandard.SmallF3.Omega.Mo107.closeL_mem (fun g hg => ?_) 6 [1]
      (fun s hs => ?_) g hx
    · unfold Q0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> exact subset_closure (by simp)
    · rw [List.mem_singleton.1 hs]
      exact one_mem _
  · intro hx
    obtain ⟨c, hc, hall⟩ := q_enum
    obtain ⟨i, hi, rfl⟩ := hall g hx
    have hc0 : c 0 = 1 := prep_eq (ids3.2.1 ▸ (hc 0 (by norm_num)).1) prep_pid
    obtain ⟨l, hl, hlen, hprod⟩ := q_words (fun i hi => (hc i hi).1) hc0 _ i hi rfl
    rw [← hprod]
    have hdep := PK.allN_iff.1 f1051qdep i hi
    exact i7close_word _ l hl 6 (by have := Nat.le_of_ble_eq_true hdep; omega)

theorem nodup_q0l : (Certificates.OmegaF1051.q0l ()).Nodup :=
  i7close_nodup _ 6 [1] (List.nodup_singleton _)

theorem q_normal_of {c : P45} (hcz : PRep 45 6 czP c) (hczi : PRep 45 6 cziP c⁻¹)
    (hcent : ∀ y ∈ CZ, c⁻¹ * y * c ∈ closure (cg '' {k | k < 3})) :
    ∀ y ∈ CZ, ∀ q ∈ Q0, y * q * y⁻¹ ∈ Q0 := by
  have h := f1051qnorm
  unfold f1051qnormK at h
  simp only [strictB_eq'] at h
  have hgen : ∀ k < 3, ∀ q ∈ Q0, (c * cg k * c⁻¹) * q * (c * cg k * c⁻¹)⁻¹ ∈ Q0 := by
    intro k hk
    have hG : PRep 45 6 (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.G k) cziP))
        (c * cg k * c⁻¹) := by
      rw [mul_assoc]
      exact prep_pcomp hn45 hcz (prep_pcomp hn45 (prep_cg k hk).1 hczi)
    obtain ⟨cq, hcq, -⟩ := q_enum
    refine conj_mem_of_gens closure_qg ?_
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := exN_spec (PK.allN_iff.1 (PK.allN_iff.1 h k hk) i hi)
    rw [eq22_sound e hG (prep_qg i hi) (hcq j hj).1 hG, mul_inv_cancel_right]
    exact (hcq j hj).2
  intro y hy q hq
  have hs : ∀ g ∈ cg '' {k | k < 3}, ∀ x ∈ {x : P45 | c * x * c⁻¹ ∈ Q0},
      g * x * g⁻¹ ∈ {x : P45 | c * x * c⁻¹ ∈ Q0} := by
    rintro _ ⟨k, hk, rfl⟩ x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    have h' := hgen k hk (c * x * c⁻¹) hx
    have e : c * cg k * c⁻¹ * (c * x * c⁻¹) * (c * cg k * c⁻¹)⁻¹ =
        c * (cg k * x * (cg k)⁻¹) * c⁻¹ := by group
    rw [e] at h'
    exact h'
  have hx : c⁻¹ * q * c ∈ {x : P45 | c * x * c⁻¹ ∈ Q0} := by
    rw [Set.mem_setOf_eq, show c * (c⁻¹ * q * c) * c⁻¹ = q by group]
    exact hq
  have h' := conj_closed_A hs _ (hcent y hy) _ hx
  rw [Set.mem_setOf_eq,
    show c * (c⁻¹ * y * c * (c⁻¹ * q * c) * (c⁻¹ * y * c)⁻¹) * c⁻¹ = y * q * y⁻¹ by group] at h'
  exact h'

theorem q_normal : ∀ y ∈ CZ, ∀ q ∈ Q0, y * q * y⁻¹ ∈ Q0 :=
  q_normal_of z_conj.2.1 z_conj.2.2.1 fun y hy => by
    rw [centA_eq.1]
    exact conj_mem_centA hy

theorem q_le_oTwo : Q0 ≤ closure
    {x : P45 | x ∈ QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45) ∧ Odd (orderOf x)} := by
  have h := f1051otwo
  unfold f1051otwoK at h
  simp only [strictB_eq'] at h
  have hmem : ∀ {B : ℕ} {b : P45}, PRep 45 6 B b → b ∈ A → f1051o3 zP B = true →
      b ∈ {x : P45 | x ∈ QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45) ∧
        Odd (orderOf x)} := by
    intro B b hB hbA ho
    unfold f1051o3 at ho
    rw [Bool.and_eq_true] at ho
    have h3 : b * (b * b) = 1 :=
      (isIdK_iff (prep_pcomp hn45 hB (prep_pcomp hn45 hB hB))).1 ho.1
    have hbz : b * z0 = z0 * b := eq22_sound ho.2 hB prep_z prep_z hB
    have hbP : b ∈ QP45.originalSubgroup := by
      by_contra hn
      have hsq := mul_mem_P hbA hbA hn hn
      apply hn
      have e : b = b * b * (b * b) := by
        calc b = b * (b * (b * b)) := by rw [h3, mul_one]
          _ = b * b * (b * b) := by group
      rw [e]
      exact mul_mem hsq hsq
    refine ⟨mem_inf.2 ⟨hbP, mem_centralizer_singleton_iff.2 hbz⟩, ?_⟩
    have hd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three]; exact h3)
    exact Odd.of_dvd_nat (by decide) hd
  rw [← closure_qg, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' := PK.allN_iff.1 h k hk
  simp only [Bool.and_eq_true] at hk'
  obtain ⟨⟨hlb, hlc⟩, ⟨hob, hoc⟩, he⟩ := hk'
  obtain ⟨hb, hbA⟩ := prep_wvA hlb
  obtain ⟨hc, hcA⟩ := prep_wvA hlc
  rw [← eqP_sound he (prep_pcomp hn45 hb hc) (prep_qg k hk)]
  exact mul_mem (subset_closure (hmem hb hbA hob)) (subset_closure (hmem hc hcA hoc))

theorem prep_f : PRep 45 6 (uP 0) fU ∧ fU ∈ A := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlet⟩ := binds3
  simp only [Bool.and_eq_true] at hlet
  have h := PK.allN_iff.1 hlet.2 0 (by norm_num)
  rw [Bool.and_eq_true] at h
  exact prep_wvA h.1

theorem t_ex : ∃ v : P45, PRep 45 6 (TZ.T f1051tI) v ∧ v ∈ T0 := by
  obtain ⟨c, hc, -⟩ := t0_enum
  exact ⟨c f1051tI, hc _ (by decide)⟩

noncomputable def tT : P45 := t_ex.choose

theorem prep_t : PRep 45 6 (TZ.T f1051tI) tT ∧ tT ∈ T0 := t_ex.choose_spec

theorem syl_facts : (∀ k < 3, fU * t0g k * fU⁻¹ ∈ T0) ∧ fU * fU ∈ T0 ∧ fU ∉ T0 ∧
    fU * z0 = z0 * fU ∧ tT ∉ Q0 := by
  obtain ⟨c0, hc0, hc0all⟩ := t0_enum
  obtain ⟨cq, hcq, hcqall⟩ := q_enum
  have hf := prep_f.1
  have h := f1051syl
  unfold f1051sylK at h
  simp only [strictB_eq', Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hn, hsq⟩, hout⟩, hz⟩, ht⟩ := h
  refine ⟨fun k hk => ?_, ?_, ?_, eq22_sound hz hf prep_z prep_z hf, ?_⟩
  · obtain ⟨j, hj, e⟩ := exN_spec (PK.allN_iff.1 hn k hk)
    rw [eq22_sound e hf (prep_t0g k hk) (hc0 j hj).1 hf, mul_inv_cancel_right]
    exact (hc0 j hj).2
  · obtain ⟨i, hi, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) hsq (prep_pcomp hn45 hf hf)
    exact e ▸ (hc0 i hi).2
  · intro hm
    obtain ⟨i, hi, e⟩ := hc0all _ hm
    rw [inPts_of hi (e ▸ (hc0 i hi).1) hf] at hout
    exact absurd hout (by decide)
  · intro hm
    obtain ⟨i, hi, e⟩ := hcqall _ hm
    rw [inPts_of hi (e ▸ (hcq i hi).1) prep_t.1] at ht
    exact absurd ht (by decide)

theorem f_norm : ∀ x ∈ T0, fU * x * fU⁻¹ ∈ T0 :=
  conj_mem_of_gens closure_t0g (by rintro _ ⟨k, hk, rfl⟩; exact syl_facts.1 k hk)

noncomputable def sylF : Subgroup P45 where
  carrier := {x | x ∈ T0 ∨ x * fU⁻¹ ∈ T0}
  one_mem' := Or.inl T0.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (T0.mul_mem ha hb)
    · refine Or.inr ?_
      have h := T0.mul_mem ha hb
      rwa [← mul_assoc] at h
    · refine Or.inr ?_
      have h := T0.mul_mem ha (f_norm b hb)
      have e : a * fU⁻¹ * (fU * b * fU⁻¹) = a * b * fU⁻¹ := by group
      rwa [e] at h
    · refine Or.inl ?_
      have h := T0.mul_mem (T0.mul_mem ha (f_norm _ hb)) syl_facts.2.1
      have e : a * fU⁻¹ * (fU * (b * fU⁻¹) * fU⁻¹) * (fU * fU) = a * b := by group
      rwa [e] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (T0.inv_mem ha)
    · refine Or.inr ?_
      have h := T0.inv_mem (T0.mul_mem (f_norm _ ha) syl_facts.2.1)
      have e : (fU * (a * fU⁻¹) * fU⁻¹ * (fU * fU))⁻¹ = a⁻¹ * fU⁻¹ := by group
      rwa [e] at h

theorem T0_le_sylF : T0 ≤ sylF := fun _ h => Or.inl h

theorem f_mem_sylF : fU ∈ sylF := Or.inr (by rw [mul_inv_cancel]; exact T0.one_mem)

theorem card_sylF : Nat.card sylF = 128 := by
  have h := card_two f_mem_sylF syl_facts.2.2.1 fun b _ hb => by
    rcases (show b ∈ T0 ∨ b * fU⁻¹ ∈ T0 from ‹b ∈ sylF›) with h | h
    · exact absurd h hb
    · exact h
  rw [inf_eq_left.2 T0_le_sylF, CFSG.OddStandard.SmallF3.Omega.card_QT0] at h
  exact h

theorem sylF_le : sylF ≤ CZ := by
  have hT : ∀ x ∈ T0, x ∈ CZ := fun x hx =>
    mem_inf.2 ⟨T0_le_A hx, mem_centralizer_singleton_iff.2 (z_T0.2 x hx)⟩
  have hf : fU ∈ CZ := mem_inf.2 ⟨prep_f.2, mem_centralizer_singleton_iff.2 syl_facts.2.2.2.1⟩
  rintro x (hx | hx)
  · exact hT x hx
  · have e : x = x * fU⁻¹ * fU := by group
    rw [e]
    exact mul_mem (hT _ hx) hf

theorem sylow_sylF :
    IsSylowOf 2 sylF CZ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_card sylF_le (by rw [card_sylF, card_CZ, factorization_1152]; norm_num)

theorem f_not_P :
    fU ∉ QP45.originalSubgroup := by
  intro hP
  have hle : sylF ≤ QP45.originalSubgroup := by
    rintro x (hx | hx)
    · exact X11.QT0_le hx
    · have e : x = x * fU⁻¹ * fU := by group
      rw [e]
      exact mul_mem (X11.QT0_le hx) hP
  have h := Subgroup.card_dvd_of_le hle
  rw [card_sylF, card_P] at h
  norm_num at h

theorem card_CPZ :
    Nat.card ↥(QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45)) = 576 := by
  have hf : fU ∈ CZ := sylF_le f_mem_sylF
  have h := card_two hf f_not_P fun b hb hbP =>
    mul_mem_P (mem_inf.1 hb).1 (inv_mem prep_f.2) hbP fun h => f_not_P (by simpa using inv_mem h)
  have e : QP45.originalSubgroup ⊓ CZ = QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45) := by
    rw [CZ, ← inf_assoc, inf_eq_left.2 CFSG.OddStandard.SmallF3.Omega.QP45_le_QA45]
  rw [e, card_CZ] at h
  omega

abbrev DQ (w : P45) : Type := {q : P45 // q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0}

theorem zc_iff {q w : P45} : q * w * q⁻¹ * w⁻¹ ∈ zpowers z0 ↔ Zc z0 q w := mem_zpowers_z

theorem card_D_le {W : ℕ} {w : P45} (hW : PRep 45 6 W w) : Nat.card (DQ w) ≤ f1051cnt zP W := by
  obtain ⟨cq, hcq, hcqall⟩ := q_enum
  rw [f1051cnt, cntN_eq]
  set F := (Finset.range 32).filter fun i => f1051ctz zP (QZ.T i) W = true
  have hsub : {q : P45 | q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0} ⊆ (F.image cq : Set P45) := by
    rintro q ⟨hq, hz⟩
    obtain ⟨i, hi, rfl⟩ := hcqall q hq
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_filter.2
      ⟨Finset.mem_range.2 hi, ctz_of (zc_iff.1 hz) (hcq i hi).1 hW⟩, rfl⟩)
  calc Nat.card (DQ w) = Set.ncard {q : P45 | q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0} :=
        Nat.card_coe_set_eq _
    _ ≤ (F.image cq : Set P45).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (F.image cq).card := Set.ncard_coe_finset _
    _ ≤ F.card := Finset.card_image_le

theorem card_D2_le {W V : ℕ} {w v : P45} (hW : PRep 45 6 W w) (hV : PRep 45 6 V v) :
    Nat.card {q : P45 // q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0 ∧
      q * v * q⁻¹ * v⁻¹ ∈ zpowers z0} ≤ f1051cnt2 zP W V := by
  obtain ⟨cq, hcq, hcqall⟩ := q_enum
  rw [f1051cnt2, cntN_eq]
  set F := (Finset.range 32).filter fun i =>
    (f1051ctz zP (QZ.T i) W && f1051ctz zP (QZ.T i) V) = true
  have hsub : {q : P45 | q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0 ∧
      q * v * q⁻¹ * v⁻¹ ∈ zpowers z0} ⊆ (F.image cq : Set P45) := by
    rintro q ⟨hq, hz, hz'⟩
    obtain ⟨i, hi, rfl⟩ := hcqall q hq
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_filter.2
      ⟨Finset.mem_range.2 hi, ?_⟩, rfl⟩)
    rw [Bool.and_eq_true]
    exact ⟨ctz_of (zc_iff.1 hz) (hcq i hi).1 hW, ctz_of (zc_iff.1 hz') (hcq i hi).1 hV⟩
  calc Nat.card {q : P45 // q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0 ∧
        q * v * q⁻¹ * v⁻¹ ∈ zpowers z0} =
        Set.ncard {q : P45 | q ∈ Q0 ∧ q * w * q⁻¹ * w⁻¹ ∈ zpowers z0 ∧
          q * v * q⁻¹ * v⁻¹ ∈ zpowers z0} := Nat.card_coe_set_eq _
    _ ≤ (F.image cq : Set P45).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (F.image cq).card := Set.ncard_coe_finset _
    _ ≤ F.card := Finset.card_image_le

theorem card_D_coset {r w : P45} (hr : r ∈ Q0) :
    Nat.card (DQ (r * w)) = Nat.card (DQ w) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
  refine and_congr_right fun hq => ?_
  rw [zc_iff, zc_iff]
  constructor
  · intro h
    have e : w = r⁻¹ * (r * w) := by group
    rw [e]
    exact zc_coset z_sq (q_z _ (inv_mem hr)) (q_zc q hq _ (inv_mem hr)) h
  · exact zc_coset z_sq (q_z r hr) (q_zc q hq r hr)

theorem sylF_cosets {v : P45} (hv : v ∈ sylF) (hvQ : v ∉ Q0) :
    ∃ r ∈ Q0, v = r * tT ∨ v = r * fU ∨ v = r * (tT * fU) := by
  have hc : Nat.card T0 = 2 * Nat.card Q0 := by
    rw [CFSG.OddStandard.SmallF3.Omega.card_QT0, card_Q0]
  have hidx := fun {x : P45} (hx : x ∈ T0) (hxQ : x ∉ Q0) =>
    mul_inv_mem_of_card q0_le hc prep_t.2 syl_facts.2.2.2.2 hx hxQ
  rcases hv with hv | hv
  · exact ⟨v * tT⁻¹, hidx hv hvQ, Or.inl (by group)⟩
  · by_cases ha : v * fU⁻¹ ∈ Q0
    · exact ⟨v * fU⁻¹, ha, Or.inr (Or.inl (by group))⟩
    · exact ⟨v * fU⁻¹ * tT⁻¹, hidx hv ha, Or.inr (Or.inr (by group))⟩

theorem card_D_lt {v : P45} (hv : v ∈ sylF) (hvQ : v ∉ Q0) :
    Nat.card (DQ v) < 16 := by
  have h := f1051bounds
  unfold f1051bndK at h
  simp only [strictB_eq', Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
  obtain ⟨r, hr, e | e | e⟩ := sylF_cosets hv hvQ <;> rw [e, card_D_coset hr]
  · exact lt_of_le_of_lt (card_D_le prep_t.1) (Nat.blt_eq.mp h1)
  · exact lt_of_le_of_lt (card_D_le prep_f.1) (Nat.blt_eq.mp h2)
  · exact lt_of_le_of_lt (card_D_le (prep_pcomp hn45 prep_t.1 prep_f.1)) (Nat.blt_eq.mp h3)

theorem card_D2_lt : Nat.card {q : P45 // q ∈ Q0 ∧ q * tT * q⁻¹ * tT⁻¹ ∈ zpowers z0 ∧
    q * fU * q⁻¹ * fU⁻¹ ∈ zpowers z0} < 8 := by
  have h := f1051bounds
  unfold f1051bndK at h
  simp only [strictB_eq', Bool.and_eq_true] at h
  exact lt_of_le_of_lt (card_D2_le prep_t.1 prep_f.1) (Nat.blt_eq.mp h.2)

theorem ext1051 (U : Subgroup P45)
    (hUA : U ≤ A) (hUz : ∀ u ∈ U, u * z0 = z0 * u) (hQU : Q0 ≤ U) (n : ℕ) (hn : 1 ≤ n)
    (hidx : Q0.relIndex U = 2 ^ n) : n ≤ 2 ∧
      2 ^ n * Nat.card {q : P45 // q ∈ Q0 ∧ ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ zpowers z0} < 32 := by
  have hcard : Nat.card U = 2 ^ n * 32 := by
    have h := Subgroup.relIndex_mul_card (H := Q0) (K := U)
    rw [inf_eq_left.2 hQU, hidx, card_Q0] at h
    exact h.symm
  have hUC : U ≤ CZ := fun u hu => mem_inf.2 ⟨hUA hu, mem_centralizer_singleton_iff.2 (hUz u hu)⟩
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := n + 5) (by rw [hcard]; ring)
  obtain ⟨g, hgC, hg⟩ := CFSG.OddStandard.ONan76.exists_conj_le sylow_sylF hUC hU2
  set V := U.map (MulAut.conj g).toMonoidHom with hV
  have hVcard : Nat.card V = Nat.card U :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))
  have hVle : V ≤ sylF := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u hu
  have hn2 : n ≤ 2 := by
    have h := Subgroup.card_le_of_le hVle
    rw [hVcard, hcard, card_sylF] at h
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨hn2, ?_⟩
  have hgz : g * z0 * g⁻¹ = z0 := by
    rw [(mem_centralizer_singleton_iff.1 (mem_inf.1 hgC).2)]
    group
  have hinj : Nat.card {q : P45 // q ∈ Q0 ∧ ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ zpowers z0} ≤
      Nat.card {q : P45 // q ∈ Q0 ∧ ∀ u ∈ U,
        q * (g * u * g⁻¹) * q⁻¹ * (g * u * g⁻¹)⁻¹ ∈ zpowers z0} := by
    refine Nat.card_le_card_of_injective (fun q => ⟨g * q.1 * g⁻¹, q_normal g hgC q.1 q.2.1,
      fun u hu => ?_⟩) fun a b e => ?_
    · have h := q.2.2 u hu
      rw [mem_zpowers_z] at h ⊢
      have e : g * q.1 * g⁻¹ * (g * u * g⁻¹) * (g * q.1 * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ =
          g * (q.1 * u * q.1⁻¹ * u⁻¹) * g⁻¹ := by group
      rw [e]
      rcases h with h | h <;> rw [h]
      · left
        group
      · right
        exact hgz
    · have e' : g * a.1 * g⁻¹ = g * b.1 * g⁻¹ := congrArg Subtype.val e
      exact Subtype.ext (mul_left_cancel (mul_right_cancel e'))
  interval_cases n
  ·
    obtain ⟨u, huU, huQ⟩ : ∃ u ∈ U, u ∉ Q0 := by
      by_contra hcon
      push Not at hcon
      have h1 : Q0.relIndex U = 1 := Subgroup.relIndex_eq_one.2 hcon
      rw [hidx] at h1
      norm_num at h1
    have hvQ : g * u * g⁻¹ ∉ Q0 := by
      intro h
      apply huQ
      have h' := q_normal g⁻¹ (inv_mem hgC) _ h
      rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group] at h'
    have hle := card_le_of_imp (p := fun q => q ∈ Q0 ∧ ∀ u ∈ U,
      q * (g * u * g⁻¹) * q⁻¹ * (g * u * g⁻¹)⁻¹ ∈ zpowers z0)
      (q := fun q => q ∈ Q0 ∧ q * (g * u * g⁻¹) * q⁻¹ * (g * u * g⁻¹)⁻¹ ∈ zpowers z0)
      fun q hq => ⟨hq.1, hq.2 u huU⟩
    have hlt : Nat.card {q : P45 // q ∈ Q0 ∧
        q * (g * u * g⁻¹) * q⁻¹ * (g * u * g⁻¹)⁻¹ ∈ zpowers z0} < 16 :=
      card_D_lt (hg u huU) hvQ
    omega
  ·
    have hVeq : V = sylF :=
      Subgroup.eq_of_le_of_card_ge hVle (by rw [hVcard, hcard, card_sylF]; norm_num)
    have hmemV : ∀ x ∈ sylF, ∃ u ∈ U, g * u * g⁻¹ = x := by
      intro x hx
      rw [← hVeq] at hx
      obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 hx
      exact ⟨u, hu, e⟩
    obtain ⟨ut, hut, et⟩ := hmemV tT (T0_le_sylF prep_t.2)
    obtain ⟨uf, huf, ef⟩ := hmemV fU f_mem_sylF
    have hle := card_le_of_imp (p := fun q => q ∈ Q0 ∧ ∀ u ∈ U,
      q * (g * u * g⁻¹) * q⁻¹ * (g * u * g⁻¹)⁻¹ ∈ zpowers z0)
      (q := fun q => q ∈ Q0 ∧ q * tT * q⁻¹ * tT⁻¹ ∈ zpowers z0 ∧
        q * fU * q⁻¹ * fU⁻¹ ∈ zpowers z0)
      fun q hq => ⟨hq.1, et ▸ hq.2 ut hut, ef ▸ hq.2 uf huf⟩
    have hlt := card_D2_lt
    omega

theorem facts1051 :
    Certificates.OmegaF1051.Facts :=
  ⟨z_sq, z_ne, z_T0.1, z_T0.2, card_CZ, card_CPZ, card_Q0, fun _ => mem_q0l, nodup_q0l,
    q_le_oTwo, q_normal, fun U hUA hUz hQU _ n hn hidx => ext1051 U hUA hUz hQU n hn hidx⟩

end CertificateChecks.KernelA45

end
