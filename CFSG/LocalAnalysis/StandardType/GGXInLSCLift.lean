module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.StandardType.GGXInL

private lemma lup8d_conj_mem {G : Type*} [Group G] (E J : Subgroup G)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) (e k : G) (he : e ∈ E) (hk : k ∈ J) :
    e * k * e⁻¹ ∈ J :=
  ((Subgroup.mem_normalizer_iff.mp (hEJ he)) k).mp hk

private def lup8d_P {G : Type*} [Group G] (E J : Subgroup G)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) : Subgroup G where
  carrier := {j | j ∈ J ∧ ∃ e ∈ E, ∀ k ∈ J, e * k * e⁻¹ = j * k * j⁻¹}
  one_mem' := by
    refine ⟨J.one_mem, 1, E.one_mem, ?_⟩
    intro k hk
    simp
  mul_mem' := by
    intro j1 j2
    rintro ⟨hj1J, e1, he1, hc1⟩ ⟨hj2J, e2, he2, hc2⟩
    refine ⟨J.mul_mem hj1J hj2J, e1 * e2, E.mul_mem he1 he2, ?_⟩
    intro k hk
    have hk3 : j2 * k * j2⁻¹ ∈ J := J.mul_mem (J.mul_mem hj2J hk) (J.inv_mem hj2J)
    calc (e1 * e2) * k * (e1 * e2)⁻¹
        = e1 * (e2 * k * e2⁻¹) * e1⁻¹ := by group
      _ = e1 * (j2 * k * j2⁻¹) * e1⁻¹ := by rw [hc2 k hk]
      _ = j1 * (j2 * k * j2⁻¹) * j1⁻¹ := hc1 (j2 * k * j2⁻¹) hk3
      _ = (j1 * j2) * k * (j1 * j2)⁻¹ := by group
  inv_mem' := by
    rintro j ⟨hjJ, e, he, hc⟩
    refine ⟨J.inv_mem hjJ, e⁻¹, E.inv_mem he, ?_⟩
    intro k hk
    have hk' : e⁻¹ * k * e ∈ J := by
      simpa using lup8d_conj_mem E J hEJ e⁻¹ k (E.inv_mem he) hk
    have h := hc (e⁻¹ * k * e) hk'
    have h' : k = j * (e⁻¹ * k * e) * j⁻¹ := by
      rw [show e * (e⁻¹ * k * e) * e⁻¹ = k by group] at h
      exact h
    conv_rhs => rw [h']
    group

private lemma lup8d_P_le_J {G : Type*} [Group G] (E J : Subgroup G)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) : lup8d_P E J hEJ ≤ J := fun _ h => h.1

private def lup8d_Z {G : Type*} [Group G] (J : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥J).map J.subtype

private lemma lup8d_mem_Z_iff {G : Type*} [Group G] {J : Subgroup G} {x : G} :
    x ∈ lup8d_Z J ↔ x ∈ J ∧ ∀ k ∈ J, k * x = x * k := by
  constructor
  · intro hx
    rw [lup8d_Z, Subgroup.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨z.property, ?_⟩
    intro k hk
    have h := Subgroup.mem_center_iff.mp hz (⟨k, hk⟩ : ↥J)
    simpa using congrArg (fun t : ↥J => (t : G)) h
  · rintro ⟨hxJ, hxcent⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hxcent (g : G) g.property

private lemma lup8d_mem_Z_of_central {G : Type*} [Group G] {J : Subgroup G} {x : G}
    (hxJ : x ∈ J) (hcent : ∀ k ∈ J, k * x = x * k) : x ∈ lup8d_Z J :=
  lup8d_mem_Z_iff.mpr ⟨hxJ, hcent⟩

private lemma lup8d_card_Z {G : Type*} [Group G] (J : Subgroup G) :
    Nat.card ↥(lup8d_Z J) = Nat.card ↥(Subgroup.center ↥J) :=
  Subgroup.card_map_of_injective J.subtype_injective

private lemma lup8d_mem_Z_of_pow_eq_one {G : Type*} [Group G] {J : Subgroup G} {p : ℕ}
    (hcop : Nat.Coprime p (Nat.card ↥(Subgroup.center ↥J)))
    {z : G} (hz : z ∈ lup8d_Z J) (hzpow : z ^ p = 1) : z = 1 := by
  have horder_p : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzpow
  have horder_card : orderOf z ∣ Nat.card ↥(Subgroup.center ↥J) := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(lup8d_Z J))
    rw [lup8d_card_Z] at h
    rwa [← Subgroup.orderOf_coe ⟨z, hz⟩] at h
  have hgcd : orderOf z ∣ Nat.gcd (Nat.card ↥(Subgroup.center ↥J)) p :=
    Nat.dvd_gcd horder_card horder_p
  rw [Nat.Coprime.gcd_eq_one hcop.symm] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)

private lemma lup8d_P_pow_mem_Z {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (E J : Subgroup G) (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hEexp : ∀ e ∈ E, e ^ p = 1) {j : G} (hj : j ∈ lup8d_P E J hEJ) :
    j ^ p ∈ lup8d_Z J := by
  obtain ⟨hjJ, e, he, hc⟩ := hj
  have hjpowJ : j ^ p ∈ J := J.pow_mem hjJ p
  apply lup8d_mem_Z_of_central hjpowJ
  intro k hk
  have hpow : ∀ n : ℕ, j ^ n * k * (j ^ n)⁻¹ = e ^ n * k * (e ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hk' : e ^ n * k * (e ^ n)⁻¹ ∈ J := by
          simpa using lup8d_conj_mem E J hEJ (e ^ n) k (E.pow_mem he n) hk
        calc j ^ (n + 1) * k * (j ^ (n + 1))⁻¹
            = j * (j ^ n * k * (j ^ n)⁻¹) * j⁻¹ := by group
          _ = j * (e ^ n * k * (e ^ n)⁻¹) * j⁻¹ := by rw [ih]
          _ = e * (e ^ n * k * (e ^ n)⁻¹) * e⁻¹ := (hc _ hk').symm
          _ = e ^ (n + 1) * k * (e ^ (n + 1))⁻¹ := by group
  have hp := hpow p
  rw [hEexp e he] at hp
  have hcomm : j ^ p * k = k * j ^ p := by
    calc j ^ p * k = (j ^ p * k * (j ^ p)⁻¹) * j ^ p := by group
      _ = k * j ^ p := by rw [hp]; group
  exact hcomm.symm

private lemma lup8d_P_conj_mem {G : Type*} [Group G] (E J : Subgroup G)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) {e j : G} (he : e ∈ E)
    (hj : j ∈ lup8d_P E J hEJ) : e * j * e⁻¹ ∈ lup8d_P E J hEJ := by
  obtain ⟨hjJ, e0, he0, hc⟩ := hj
  refine ⟨lup8d_conj_mem E J hEJ e j he hjJ, e0, he0, ?_⟩
  intro k hk
  have hk' : e⁻¹ * k * e ∈ J := by
    simpa using lup8d_conj_mem E J hEJ e⁻¹ k (E.inv_mem he) hk
  have hcomm : e * e0 = e0 * e := hEab e he e0 he0
  have hcomm' : Commute e e0 := hcomm
  have hact : e * (e0 * (e⁻¹ * k * e) * e0⁻¹) * e⁻¹ = e0 * k * e0⁻¹ := by
    calc e * (e0 * (e⁻¹ * k * e) * e0⁻¹) * e⁻¹
        = (e * e0) * (e⁻¹ * k * e) * (e0⁻¹ * e⁻¹) := by group
      _ = (e0 * e) * (e⁻¹ * k * e) * (e0⁻¹ * e⁻¹) := by rw [hcomm]
      _ = (e0 * e) * (e⁻¹ * k * e) * (e⁻¹ * e0⁻¹) := by rw [hcomm'.inv_inv.eq.symm]
      _ = e0 * k * e0⁻¹ := by group
  calc e0 * k * e0⁻¹
      = e * (e0 * (e⁻¹ * k * e) * e0⁻¹) * e⁻¹ := hact.symm
    _ = e * (j * (e⁻¹ * k * e) * j⁻¹) * e⁻¹ := by rw [hc _ hk']
    _ = (e * j * e⁻¹) * k * (e * j * e⁻¹)⁻¹ := by group

private lemma lup8d_E_le_normalizer_P {G : Type*} [Group G] (E J : Subgroup G)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    E ≤ Subgroup.normalizer (lup8d_P E J hEJ : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    exact lup8d_P_conj_mem E J hEab hEJ he hj
  · intro hj
    have h := lup8d_P_conj_mem E J hEab hEJ (E.inv_mem he) hj
    have heq : e⁻¹ * (e * j * e⁻¹) * e = j := by group
    simpa [heq] using h

private lemma lup8d_isComplement_inf_bot {G : Type*} [Group G] {A B : Subgroup G}
    (h : A.IsComplement' B) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hinj := (Subgroup.isComplement'_def.mp h).1
  have h1 : ((⟨x, hx.1⟩ : A) : G) * ((1 : B) : G) = x := by simp
  have h2 : ((1 : A) : G) * ((⟨x, hx.2⟩ : B) : G) = x := by simp
  have e1 : ((⟨x, hx.1⟩ : A), (1 : B)) = ((1 : A), (⟨x, hx.2⟩ : B)) := by
    apply hinj
    simp
  have := congrArg (fun q : A × B => ((q.1 : A) : G)) e1
  simpa using this

private lemma lup8d_isComplement_exists {G : Type*} [Group G] {A B : Subgroup G}
    (h : A.IsComplement' B) (g : G) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  obtain ⟨⟨a, b⟩, hprod, -⟩ := h.existsUnique g
  exact ⟨a, a.property, b, b.property, hprod⟩

private lemma lup8d_conj_sandwich {G : Type*} [Group G] {e e0 k : G}
    (hcomm : e * e0 = e0 * e) :
    e * (e0 * (e⁻¹ * k * e) * e0⁻¹) * e⁻¹ = e0 * k * e0⁻¹ := by
  have hcomm' : Commute e e0 := hcomm
  calc e * (e0 * (e⁻¹ * k * e) * e0⁻¹) * e⁻¹
      = (e * e0) * (e⁻¹ * k * e) * (e0⁻¹ * e⁻¹) := by group
    _ = (e0 * e) * (e⁻¹ * k * e) * (e0⁻¹ * e⁻¹) := by rw [hcomm]
    _ = (e0 * e) * (e⁻¹ * k * e) * (e⁻¹ * e0⁻¹) := by rw [hcomm'.inv_inv.eq.symm]
    _ = e0 * k * e0⁻¹ := by group

private lemma lup8d_P_action_conj {G : Type*} [Group G] (E J : Subgroup G)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) {q : G}
    (hq : q ∈ lup8d_P E J hEJ) {e : G} (he : e ∈ E) :
    ∀ k ∈ J, (e * q * e⁻¹) * k * (e * q * e⁻¹)⁻¹ = q * k * q⁻¹ := by
  obtain ⟨hqJ, e0, he0, hc⟩ := hq
  intro k hk
  have hk' : e⁻¹ * k * e ∈ J := by
    simpa using lup8d_conj_mem E J hEJ e⁻¹ k (E.inv_mem he) hk
  have hcomm : e * e0 = e0 * e := hEab e he e0 he0
  calc (e * q * e⁻¹) * k * (e * q * e⁻¹)⁻¹
      = e * (q * (e⁻¹ * k * e) * q⁻¹) * e⁻¹ := by group
    _ = e * (e0 * (e⁻¹ * k * e) * e0⁻¹) * e⁻¹ := by rw [hc _ hk']
    _ = e0 * k * e0⁻¹ := lup8d_conj_sandwich hcomm
    _ = q * k * q⁻¹ := hc k hk

private lemma lup8d_quotient_centralizes {G : Type*} [Group G] (E J : Subgroup G)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) {q : G}
    (hq : q ∈ lup8d_P E J hEJ) {e : G} (he : e ∈ E) :
    ∀ k ∈ J, ((e * q * e⁻¹) * q⁻¹) * k * ((e * q * e⁻¹) * q⁻¹)⁻¹ = k := by
  have hact := lup8d_P_action_conj E J hEab hEJ hq he
  intro k hk
  have hqJ : q ∈ J := hq.1
  have hk' : q⁻¹ * k * q ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hqJ) hk) hqJ
  calc ((e * q * e⁻¹) * q⁻¹) * k * ((e * q * e⁻¹) * q⁻¹)⁻¹
      = (e * q * e⁻¹) * (q⁻¹ * k * q) * (e * q * e⁻¹)⁻¹ := by group
    _ = q * (q⁻¹ * k * q) * q⁻¹ := hact (q⁻¹ * k * q) hk'
    _ = k := by group

private lemma lup8d_Q_pow_one {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (E J : Subgroup G) (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hEexp : ∀ e ∈ E, e ^ p = 1)
    (Q : Subgroup ↥(lup8d_P E J hEJ))
    (hQcomp : ((lup8d_Z J).subgroupOf (lup8d_P E J hEJ)).IsComplement' Q)
    {q : ↥(lup8d_P E J hEJ)} (hq : q ∈ Q) :
    ((q : ↥(lup8d_P E J hEJ)) : G) ^ p = 1 := by
  have hqpowZ : (((q : ↥(lup8d_P E J hEJ)) : G) ^ p) ∈ lup8d_Z J :=
    lup8d_P_pow_mem_Z E J hEJ hEexp q.property
  have hqpowZ' : q ^ p ∈ (lup8d_Z J).subgroupOf (lup8d_P E J hEJ) := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hqpowZ
  have hqpowQ : q ^ p ∈ Q := Q.pow_mem hq p
  have hinf : (lup8d_Z J).subgroupOf (lup8d_P E J hEJ) ⊓ Q = ⊥ :=
    lup8d_isComplement_inf_bot hQcomp
  have hmem : q ^ p ∈ (lup8d_Z J).subgroupOf (lup8d_P E J hEJ) ⊓ Q :=
    ⟨hqpowZ', hqpowQ⟩
  rw [hinf] at hmem
  have hqpowP : q ^ p = 1 := by simpa using hmem
  have := congrArg (fun x : ↥(lup8d_P E J hEJ) => (x : G)) hqpowP
  simpa using this

private lemma lup8d_Q_centralizes {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (E J : Subgroup G) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hEexp : ∀ e ∈ E, e ^ p = 1)
    (hcop : Nat.Coprime p (Nat.card ↥(Subgroup.center ↥J)))
    (Q : Subgroup ↥(lup8d_P E J hEJ))
    (hQcomp : ((lup8d_Z J).subgroupOf (lup8d_P E J hEJ)).IsComplement' Q)
    {q : ↥(lup8d_P E J hEJ)} (hq : q ∈ Q) :
    ∀ e ∈ E, e * ((q : ↥(lup8d_P E J hEJ)) : G) = ((q : ↥(lup8d_P E J hEJ)) : G) * e := by
  have hqpow : ((q : ↥(lup8d_P E J hEJ)) : G) ^ p = 1 :=
    lup8d_Q_pow_one E J hEJ hEexp Q hQcomp hq
  intro e he
  have haP : e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹ ∈ lup8d_P E J hEJ :=
    ((Subgroup.mem_normalizer_iff.mp
      (lup8d_E_le_normalizer_P E J hEab hEJ he)) ((q : ↥(lup8d_P E J hEJ)) : G)).mp
      q.property
  have hapow : (e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) ^ p = 1 := by
    have hc : ((MulAut.conj e) ((q : ↥(lup8d_P E J hEJ)) : G)) ^ p = 1 := by
      rw [← map_pow, hqpow, map_one]
    simpa [MulAut.conj_apply] using hc
  let r : G := (e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
    ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹
  have hrP : r ∈ lup8d_P E J hEJ :=
    (lup8d_P E J hEJ).mul_mem haP ((lup8d_P E J hEJ).inv_mem q.property)
  have hrZ : r ∈ lup8d_Z J := by
    apply lup8d_mem_Z_of_central (lup8d_P_le_J E J hEJ hrP)
    intro k hk
    have h := lup8d_quotient_centralizes E J hEab hEJ q.property he k hk
    have hcomm : ((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
        ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹) * k =
        k * ((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
        ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹) := by
      calc ((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
            ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹) * k
          = (((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
              ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹) * k *
              ((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
              ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹)⁻¹) *
              ((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
              ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹) := by group
        _ = k * (((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
              ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹)) := by rw [h]
    exact hcomm.symm
  have hrqcomm : Commute r ((q : ↥(lup8d_P E J hEJ)) : G) := by
    have hcent := (lup8d_mem_Z_iff.mp hrZ).2
      ((q : ↥(lup8d_P E J hEJ)) : G) (lup8d_P_le_J E J hEJ q.property)
    exact hcent.symm
  have harq : e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹ =
      r * ((q : ↥(lup8d_P E J hEJ)) : G) := by
    dsimp [r]
    group
  have hrpow : r ^ p = 1 := by
    rw [harq, hrqcomm.mul_pow p, hqpow, mul_one] at hapow
    exact hapow
  have hr1 : r = 1 := lup8d_mem_Z_of_pow_eq_one hcop hrZ hrpow
  have haq : e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹ =
      ((q : ↥(lup8d_P E J hEJ)) : G) := by
    dsimp [r] at hr1
    calc e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹
        = ((e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) *
            ((q : ↥(lup8d_P E J hEJ)) : G)⁻¹) *
            ((q : ↥(lup8d_P E J hEJ)) : G) := by group
      _ = 1 * ((q : ↥(lup8d_P E J hEJ)) : G) := by rw [hr1]
      _ = ((q : ↥(lup8d_P E J hEJ)) : G) := by group
  calc e * ((q : ↥(lup8d_P E J hEJ)) : G)
      = (e * ((q : ↥(lup8d_P E J hEJ)) : G) * e⁻¹) * e := by group
    _ = ((q : ↥(lup8d_P E J hEJ)) : G) * e := by rw [haq]

private lemma lup8d_Z_le_P {G : Type*} [Group G] (E J : Subgroup G)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) : lup8d_Z J ≤ lup8d_P E J hEJ := by
  intro z hz
  obtain ⟨hzJ, hzcent⟩ := lup8d_mem_Z_iff.mp hz
  refine ⟨hzJ, 1, E.one_mem, ?_⟩
  intro k hk
  have hzk : z * k = k * z := (hzcent k hk).symm
  rw [hzk]
  group

private lemma lup8d_Z_subgroupOf_normal {G : Type*} [Group G] (E J : Subgroup G)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    ((lup8d_Z J).subgroupOf (lup8d_P E J hEJ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (lup8d_Z_le_P E J hEJ)]
  intro h k hh hk
  have hhZ : h ∈ lup8d_Z J := hh
  have hkJ : k ∈ J := lup8d_P_le_J E J hEJ hk
  have hcent := (lup8d_mem_Z_iff.mp hhZ).2 k hkJ
  rwa [show k * h * k⁻¹ = h by rw [hcent]; group]

private lemma lup8d_index_subgroupOf_Z_eq_pow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime]
    (E J : Subgroup G) (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hEexp : ∀ e ∈ E, e ^ p = 1) :
    ∃ n, ((lup8d_Z J).subgroupOf (lup8d_P E J hEJ)).index = p ^ n := by
  let P := lup8d_P E J hEJ
  let Z' := (lup8d_Z J).subgroupOf P
  have hZnormal : Z'.Normal := lup8d_Z_subgroupOf_normal E J hEJ
  let _ : Z'.Normal := hZnormal
  have : Finite ↥P := inferInstance
  have : Finite (↥P ⧸ Z') := QuotientGroup.finite
  have hquot : IsPGroup p (↥P ⧸ Z') := by
    rw [IsPGroup.iff_orderOf]
    intro x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
    have hmem : j ^ p ∈ Z' := by
      dsimp [Z']
      rw [Subgroup.mem_subgroupOf]
      simpa using lup8d_P_pow_mem_Z E J hEJ hEexp j.property
    have hpow : (QuotientGroup.mk j : ↥P ⧸ Z') ^ p = 1 := by
      rw [← QuotientGroup.mk_pow Z' j p, QuotientGroup.eq_one_iff]
      exact hmem
    have hdvd : orderOf (QuotientGroup.mk j : ↥P ⧸ Z') ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr hpow
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
  refine ⟨n, ?_⟩
  rw [Subgroup.index_eq_card, hn]

private lemma lup8d_card_subgroupOf_Z {G : Type*} [Group G] (E J : Subgroup G)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card ↥((lup8d_Z J).subgroupOf (lup8d_P E J hEJ)) =
      Nat.card ↥(Subgroup.center ↥J) := by
  let P := lup8d_P E J hEJ
  let Z' := (lup8d_Z J).subgroupOf P
  have hmap : Subgroup.map P.subtype Z' = lup8d_Z J := by
    dsimp [Z']
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (lup8d_Z_le_P E J hEJ)
  have h := Subgroup.card_map_of_injective (K := Z') (f := P.subtype) P.subtype_injective
  rw [hmap, lup8d_card_Z] at h
  exact h.symm

theorem sc_lift {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (E J : Subgroup G)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEexp : ∀ e ∈ E, e ^ p = 1)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center J)))
    (hinner : ∀ e ∈ E, ∃ j ∈ J, ∀ k ∈ J, e * k * e⁻¹ = j * k * j⁻¹)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ p = 1 → g ∈ E) :
    (E ⊓ J) ⊔ (E ⊓ Subgroup.centralizer (J : Set G)) = E ∧
      (E ⊓ J) ⊓ (E ⊓ Subgroup.centralizer (J : Set G)) = ⊥ := by
  classical
  let P := lup8d_P E J hEJ
  let Z' := (lup8d_Z J).subgroupOf P
  have hZnormal : Z'.Normal := lup8d_Z_subgroupOf_normal E J hEJ
  let _ : Z'.Normal := hZnormal
  have hcardZ' : Nat.card ↥Z' = Nat.card ↥(Subgroup.center ↥J) := by
    dsimp [Z', P]
    exact lup8d_card_subgroupOf_Z E J hEJ
  have hidx : ∃ n, Z'.index = p ^ n := by
    dsimp [Z', P]
    exact lup8d_index_subgroupOf_Z_eq_pow E J hEJ hEexp
  obtain ⟨n, hn⟩ := hidx
  have hcopZ : Nat.Coprime (Nat.card ↥Z') Z'.index := by
    rw [hcardZ', hn]
    exact Nat.Coprime.pow_right n hcop.symm
  obtain ⟨Q, hQcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := Z') hcopZ
  have hq_cent : ∀ q ∈ Q, ((q : P) : G) ∈ Subgroup.centralizer (E : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact lup8d_Q_centralizes E J hEab hEJ hEexp hcop Q hQcomp hq e he
  have hq_pow : ∀ q ∈ Q, ((q : P) : G) ^ p = 1 := by
    intro q hq
    exact lup8d_Q_pow_one E J hEJ hEexp Q hQcomp hq
  have hqE : ∀ q ∈ Q, ((q : P) : G) ∈ E := by
    intro q hq
    exact hSC ((q : P) : G) (hq_cent q hq) (hq_pow q hq)
  have hE_le_sup : E ≤ (E ⊓ J) ⊔ (E ⊓ Subgroup.centralizer (J : Set G)) := by
    intro e he
    obtain ⟨j, hjJ, hjact⟩ := hinner e he
    have hjP : j ∈ P := by
      dsimp [P]
      exact ⟨hjJ, e, he, hjact⟩
    obtain ⟨z, hzZ', q, hqQ, hzq⟩ :=
      lup8d_isComplement_exists hQcomp (⟨j, hjP⟩ : P)
    have hzZ : ((z : P) : G) ∈ lup8d_Z J := by
      have h := hzZ'
      rw [Subgroup.mem_subgroupOf] at h
      exact h
    have hqJ : ((q : P) : G) ∈ J := lup8d_P_le_J E J hEJ q.property
    have hqE' : ((q : P) : G) ∈ E := hqE q hqQ
    have hzcent : ∀ k ∈ J, k * ((z : P) : G) = ((z : P) : G) * k :=
      (lup8d_mem_Z_iff.mp hzZ).2
    have hj_eq : j = ((z : P) : G) * ((q : P) : G) := by
      have h := congrArg (fun x : P => (x : G)) hzq
      simpa using h.symm
    have hqact : ∀ k ∈ J, ((q : P) : G) * k * ((q : P) : G)⁻¹ = j * k * j⁻¹ := by
      intro k hk
      have hyz : (j * k * j⁻¹) * ((z : P) : G) =
          ((z : P) : G) * (j * k * j⁻¹) :=
        hzcent (j * k * j⁻¹)
          (J.mul_mem (J.mul_mem hjJ hk) (J.inv_mem hjJ))
      calc ((q : P) : G) * k * ((q : P) : G)⁻¹
          = ((z : P) : G)⁻¹ * (j * k * j⁻¹) * ((z : P) : G) := by
              rw [hj_eq]
              group
        _ = j * k * j⁻¹ := by
              calc ((z : P) : G)⁻¹ * (j * k * j⁻¹) * ((z : P) : G)
                  = ((z : P) : G)⁻¹ * ((j * k * j⁻¹) * ((z : P) : G)) := by group
                _ = ((z : P) : G)⁻¹ * (((z : P) : G) * (j * k * j⁻¹)) := by
                      rw [hyz]
                _ = j * k * j⁻¹ := by group
    have heq_act : ∀ k ∈ J, e * k * e⁻¹ = ((q : P) : G) * k * ((q : P) : G)⁻¹ := by
      intro k hk
      rw [hjact k hk, hqact k hk]
    have hc_central : ∀ k ∈ J,
        (e * ((q : P) : G)⁻¹) * k * (e * ((q : P) : G)⁻¹)⁻¹ = k := by
      intro k hk
      have hk' : ((q : P) : G)⁻¹ * k * ((q : P) : G) ∈ J :=
        J.mul_mem (J.mul_mem (J.inv_mem hqJ) hk) hqJ
      have h := heq_act (((q : P) : G)⁻¹ * k * ((q : P) : G)) hk'
      calc (e * ((q : P) : G)⁻¹) * k * (e * ((q : P) : G)⁻¹)⁻¹
          = e * (((q : P) : G)⁻¹ * k * ((q : P) : G)) * e⁻¹ := by group
        _ = ((q : P) : G) * (((q : P) : G)⁻¹ * k * ((q : P) : G)) *
              ((q : P) : G)⁻¹ := h
        _ = k := by group
    have hc_mem : e * ((q : P) : G)⁻¹ ∈
        E ⊓ Subgroup.centralizer (J : Set G) := by
      refine ⟨E.mul_mem he (E.inv_mem hqE'), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro k hk
      have h := hc_central k hk
      have hcomm : (e * ((q : P) : G)⁻¹) * k =
          k * (e * ((q : P) : G)⁻¹) := by
        calc (e * ((q : P) : G)⁻¹) * k
            = ((e * ((q : P) : G)⁻¹) * k * (e * ((q : P) : G)⁻¹)⁻¹) *
                (e * ((q : P) : G)⁻¹) := by group
          _ = k * (e * ((q : P) : G)⁻¹) := by rw [h]
      exact hcomm.symm
    have hcq : ((q : P) : G) * (e * ((q : P) : G)⁻¹) = e := by
      have hcomm_cq : (e * ((q : P) : G)⁻¹) * ((q : P) : G) =
          ((q : P) : G) * (e * ((q : P) : G)⁻¹) := by
        have h := hc_central ((q : P) : G) hqJ
        calc (e * ((q : P) : G)⁻¹) * ((q : P) : G)
            = ((e * ((q : P) : G)⁻¹) * ((q : P) : G) *
                (e * ((q : P) : G)⁻¹)⁻¹) * (e * ((q : P) : G)⁻¹) := by group
          _ = ((q : P) : G) * (e * ((q : P) : G)⁻¹) := by rw [h]
      calc ((q : P) : G) * (e * ((q : P) : G)⁻¹)
          = (e * ((q : P) : G)⁻¹) * ((q : P) : G) := hcomm_cq.symm
        _ = e := by group
    rw [← hcq]
    exact Subgroup.mul_mem_sup ⟨hqE', hqJ⟩ hc_mem
  have hsup_le : (E ⊓ J) ⊔ (E ⊓ Subgroup.centralizer (J : Set G)) ≤ E :=
    sup_le inf_le_left inf_le_left
  have hsup_eq : (E ⊓ J) ⊔ (E ⊓ Subgroup.centralizer (J : Set G)) = E :=
    le_antisymm hsup_le hE_le_sup
  have hinf_eq : (E ⊓ J) ⊓ (E ⊓ Subgroup.centralizer (J : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxE : x ∈ E := hx.1.1
    have hxJ : x ∈ J := hx.1.2
    have hxC : x ∈ Subgroup.centralizer (J : Set G) := hx.2.2
    have hxZ : x ∈ lup8d_Z J := by
      apply lup8d_mem_Z_of_central hxJ
      intro k hk
      exact Subgroup.mem_centralizer_iff.mp hxC k hk
    exact lup8d_mem_Z_of_pow_eq_one hcop hxZ (hEexp x hxE)
  exact ⟨hsup_eq, hinf_eq⟩

end CFSG.StandardType.GGXInL

end
