module

public import Certificates.Kernel.A45Cls.Glue218
public import Certificates.Kernel.A45Cls.Checks3
public import CFSG.Certificates.Kernel.A45Cls.PockSound
public import Certificates.Data.OmegaTypesFacts

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup
  Certificates.OmegaTypes

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def kx (j : ℕ) : P45 := (kaList ()).getD j 1

@[expose] def ky (j : ℕ) : P45 :=
  (Certificates.OmegaPk.kbList (Certificates.OmegaPk.g0 ()) (kaList ())).getD j 1

theorem len_ka : (kaList ()).length = 24 := by decide

theorem len_kb : (Certificates.OmegaPk.kbList (Certificates.OmegaPk.g0 ()) (kaList ())).length =
    24 := by
  rw [Certificates.OmegaPk.kbList, List.length_map, len_ka]

theorem prep_kx : ∀ j < 24, PRep 45 6 (kaN j) (kx j) := fun _ _ => prep_cOf _

theorem prep_ky : ∀ j < 24, PRep 45 6 (kbN j) (ky j) := fun _ _ => prep_cOf _

theorem mem_KAs {x : P45} : x ∈ KAs ↔ ∃ j < 24, kx j = x := by
  change x ∈ kaList () ↔ _
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, len_ka ▸ hj, by rw [kx, List.getD_eq_getElem]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, len_ka ▸ hj, by rw [kx, List.getD_eq_getElem]⟩

theorem mem_KBs {x : P45} : x ∈ KBs ↔ ∃ j < 24, ky j = x := by
  change x ∈ Certificates.OmegaPk.kbList (Certificates.OmegaPk.g0 ()) (kaList ()) ↔ _
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, len_kb ▸ hj, by rw [ky, List.getD_eq_getElem]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, len_kb ▸ hj, by rw [ky, List.getD_eq_getElem]⟩

theorem prep_tA : PRep 45 6 (KA.T KA.r0) (Certificates.P43Twin.tA ()) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  rw [← bt]
  exact prep_cOf _

theorem fix5_of_tauFix {m : ℕ} (h : tauFix m = 192) : m = 5 := by
  unfold tauFix at h
  split_ifs at h <;> omega

theorem fix7_of_tauFix {m : ℕ} (h : tauFix m = 96) : m = 7 := by
  unfold tauFix at h
  split_ifs at h <;> omega

theorem ca_point {u : P45} {n : ℕ} (hu : InvC n u)
    (hc : u * Certificates.P43Twin.tA () = Certificates.P43Twin.tA () * u) :
    ∃ i < CA.N, PRep 45 6 (CA.T i) u ∧ tauFix (fixC u) = n := by
  obtain ⟨huA, hu2, hu1, hcard⟩ := hu
  obtain ⟨i, hi, hp⟩ := centA_eq.2.2 u (mem_inf.2 ⟨huA, mem_centralizer_singleton_iff.2 hc⟩)
  refine ⟨i, by rw [orders.2.2.2.2.2.2.2.2.2.2.1]; exact hi, hp, ?_⟩
  rw [← card_cent_eq huA hu2 hu1, hcard]

theorem invC_mul_tA {u : P45} {P : ℕ} {f : ℕ}
    (huA : u ∈ A) (hp : PRep 45 6 P u)
    (h : invFixK 45 6 f (pcomp 45 6 (mask 6) P (KA.T KA.r0)) = true) :
    InvC (tauFix f) (u * Certificates.P43Twin.tA ()) := by
  obtain ⟨⟨h2, h1⟩, hf⟩ := (invFixK_iff (prep_pcomp hn45 hp prep_tA)).1 h
  have hA : u * Certificates.P43Twin.tA () ∈ A := mul_mem huA tA_facts.1
  exact ⟨hA, h2, h1, by rw [card_cent_eq hA h2 h1, hf]⟩

theorem pock_at {i : ℕ} (hi : i < CA.N) :
    pockD 45 6 24 kaN kbN (KA.T KA.r0) (CA.T i) = true ∧
      pockE 45 6 24 kaN kbN (KA.T KA.r0) (CA.T i) = true := by
  have h := allN_spec pockA i hi
  rw [strictB_eq', Bool.and_eq_true] at h
  exact h

theorem fact_d (u : P45) (hu : InvC 192 u)
    (hc : u * Certificates.P43Twin.tA () = Certificates.P43Twin.tA () * u) :
    ((∀ k ∈ KAs, u * k * u⁻¹ ∈ KAs) ∧ (∀ k ∈ KBs, u * k * u⁻¹ ∈ KBs) ∧
        (∃ k ∈ KAs, k * u * k⁻¹ = u * Certificates.P43Twin.tA ()) ∧
        ∃ k ∈ KBs, k * u * k⁻¹ = u * Certificates.P43Twin.tA ()) ∨
      ((∀ k ∈ KAs, u * k * u⁻¹ ∈ KBs) ∧ (∀ k ∈ KBs, u * k * u⁻¹ ∈ KAs) ∧
        InvC 1152 (u * Certificates.P43Twin.tA ())) := by
  obtain ⟨i, hi, hp, hf⟩ := ca_point hu hc
  obtain ⟨huA, hu2, hu1, -⟩ := hu
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h5 : invFixK 45 6 5 (CA.T i) = true :=
    (invFixK_iff hp).2 ⟨⟨hu2, hu1⟩, fix5_of_tauFix hf⟩
  have hpt := prep_pcomp hn45 hp prep_tA
  have hD := (pock_at hi).1
  unfold pockD at hD
  rw [h5] at hD
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at hD
  have hconj : ∀ {X Y : ℕ → ℕ} {x y : ℕ → P45}, (∀ j < 24, PRep 45 6 (X j) (x j)) →
      (∀ j < 24, PRep 45 6 (Y j) (y j)) → cjAll 45 6 24 X Y (CA.T i) = true →
      ∀ j < 24, ∃ m < 24, y m = u * x j * u⁻¹ := by
    intro X Y x y hx hy h j hj
    rw [hinv]
    exact cjAll_spec h hp hx hy j hj
  have hby : ∀ {X : ℕ → ℕ} {x : ℕ → P45}, (∀ j < 24, PRep 45 6 (X j) (x j)) →
      cjBy 45 6 24 X (CA.T i) (pcomp 45 6 (mask 6) (CA.T i) (KA.T KA.r0)) = true →
      ∃ k < 24, x k * u * (x k)⁻¹ = u * Certificates.P43Twin.tA () := by
    intro X x hx h
    obtain ⟨k, hk, e⟩ := cjBy_spec h hp hpt hx
    refine ⟨k, hk, ?_⟩
    rw [e]
    group
  rcases hD with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨h1, h2⟩, h3⟩
  · left
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := mem_KAs.1 hk
      obtain ⟨m, hm, e⟩ := hconj prep_kx prep_kx h1 j hj
      exact mem_KAs.2 ⟨m, hm, e⟩
    · obtain ⟨j, hj, rfl⟩ := mem_KBs.1 hk
      obtain ⟨m, hm, e⟩ := hconj prep_ky prep_ky h2 j hj
      exact mem_KBs.2 ⟨m, hm, e⟩
    · obtain ⟨k, hk, e⟩ := hby prep_kx h3
      exact ⟨kx k, mem_KAs.2 ⟨k, hk, rfl⟩, e⟩
    · obtain ⟨k, hk, e⟩ := hby prep_ky h4
      exact ⟨ky k, mem_KBs.2 ⟨k, hk, rfl⟩, e⟩
  · right
    refine ⟨fun k hk => ?_, fun k hk => ?_, invC_mul_tA huA hp h3⟩
    · obtain ⟨j, hj, rfl⟩ := mem_KAs.1 hk
      obtain ⟨m, hm, e⟩ := hconj prep_kx prep_ky h1 j hj
      exact mem_KBs.2 ⟨m, hm, e⟩
    · obtain ⟨j, hj, rfl⟩ := mem_KBs.1 hk
      obtain ⟨m, hm, e⟩ := hconj prep_ky prep_kx h2 j hj
      exact mem_KAs.2 ⟨m, hm, e⟩

theorem tA_pock : Certificates.P43Twin.tA () ∈ KAs ∧
    ∀ k ∈ KBs, k * k = 1 → k ≠ 1 → k = Certificates.P43Twin.tA () := by
  refine ⟨?_, fun k hk hk2 hk1 => ?_⟩
  · obtain ⟨j, hj, e⟩ := exN_spec pockT.1
    exact mem_KAs.2 ⟨j, hj, prep_eq (Nat.eq_of_beq_eq_true e ▸ prep_kx j hj) prep_tA⟩
  · obtain ⟨m, hm, rfl⟩ := mem_KBs.1 hk
    have h := allN_spec pockT.2 m hm
    have hi : isInvK 45 6 (kbN m) = true := by
      rw [isInvK_iff hn45 (prep_ky m hm), orderOf_eq_prime_iff, sq]
      exact ⟨hk2, hk1⟩
    rw [hi, Bool.not_true, Bool.false_or] at h
    exact prep_eq (Nat.eq_of_beq_eq_true h ▸ prep_ky m hm) prep_tA

theorem fact_e (u : P45) (hu : InvC 96 u)
    (hAB : ∀ k ∈ KAs, u * k * u⁻¹ ∈ KBs) (hBA : ∀ k ∈ KBs, u * k * u⁻¹ ∈ KAs) :
    u * Certificates.P43Twin.tA () = Certificates.P43Twin.tA () * u ∧
      InvC 1440 (u * Certificates.P43Twin.tA ()) := by
  set t := Certificates.P43Twin.tA ()
  obtain ⟨huA, hu2, hu1, hcard⟩ := hu
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hc : u * t = t * u := by
    have h1 := hAB t tA_pock.1
    have hsq : u * t * u⁻¹ * (u * t * u⁻¹) = 1 := by
      calc u * t * u⁻¹ * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
        _ = 1 := by rw [tA_facts.2.1]; group
    have hne : u * t * u⁻¹ ≠ 1 := by
      intro h0
      apply tA_facts.2.2
      calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
        _ = 1 := by rw [h0]; group
    have e := tA_pock.2 _ h1 hsq hne
    calc u * t = u * t * u⁻¹ * u := by group
      _ = t * u := by rw [e]
  refine ⟨hc, ?_⟩
  obtain ⟨i, hi, hp, hf⟩ := ca_point ⟨huA, hu2, hu1, hcard⟩ hc
  have h7 : invFixK 45 6 7 (CA.T i) = true :=
    (invFixK_iff hp).2 ⟨⟨hu2, hu1⟩, fix7_of_tauFix hf⟩
  have hE := (pock_at hi).2
  unfold pockE at hE
  rw [h7] at hE
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hE
  rcases hE with h | h
  · exact invC_mul_tA huA hp h
  · exfalso
    obtain ⟨j, hj, hall⟩ := exN_spec h
    obtain ⟨m, hm, e⟩ := mem_KBs.1 (hAB (kx j) (mem_KAs.2 ⟨j, hj, rfl⟩))
    rw [hinv] at e
    have h3 := eq3_of_eq (prep_ky m hm) hp (prep_kx j hj) hp e
    have h4 := allN_spec hall m hm
    rw [h3] at h4
    exact absurd h4 (by decide)

end CertificateChecks.KernelA45

end
