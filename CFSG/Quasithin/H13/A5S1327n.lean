module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.A5S1327d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem isElementaryAbelian_of_forall {R : Type*} [Group R] {p : ℕ}
    (hcomm : ∀ a b : R, a * b = b * a) (hpow : ∀ a : R, a ^ p = 1) : IsElementaryAbelian p R :=
  { toIsMulCommutative := ⟨⟨hcomm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }

theorem pow_eq_one_zmod (p : ℕ) (m : Multiplicative (ZMod p)) : m ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem pow_eq_one_zmod_pi (p n : ℕ) (m : Multiplicative (Fin n → ZMod p)) : m ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp [nsmul_eq_mul]

theorem frattini_eq_bot_of_forall {R : Type*} [Group R] [Finite R] {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ a b : R, a * b = b * a) (hpow : ∀ a : R, a ^ p = 1) : frattini R = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p R := isElementaryAbelian_of_forall hcomm hpow
  have : Fact (IsPGroup p R) := ⟨fun a => ⟨1, by rw [pow_one]; exact hpow a⟩⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := p)

section Extraspecial

variable {Y : Type*} [Group Y] {p : ℕ} {P : Subgroup Y}

abbrev centerIn (P : Subgroup Y) : Subgroup Y := (Subgroup.center ↥P).map P.subtype

theorem mem_centerIn {z : Y} : z ∈ centerIn P ↔ ∃ hz : z ∈ P, ∀ x : ↥P, x * ⟨z, hz⟩ = ⟨z, hz⟩ * x :=
  by
  constructor
  · rintro ⟨z', hz', rfl⟩
    exact ⟨z'.2, fun x => (Subgroup.mem_center_iff.mp hz' x)⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr h, rfl⟩

theorem centerIn_le : centerIn P ≤ P := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem comm_of_mem_centerIn {z x : Y} (hz : z ∈ centerIn P) (hx : x ∈ P) : z * x = x * z := by
  obtain ⟨hzP, h⟩ := mem_centerIn.mp hz
  have := congrArg Subtype.val (h ⟨x, hx⟩)
  exact this.symm

theorem commutator_mem_centerIn (h : IsPOnePlusTwo p ↥P) {x y : Y} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ centerIn P := by
  obtain ⟨hex, -, -⟩ := h
  have hab := hex.quotient_elementary_abelian
  have hcomm : (QuotientGroup.mk (⟨x, hx⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P) *
      QuotientGroup.mk ⟨y, hy⟩ = QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨x, hx⟩ :=
    hab.toIsMulCommutative.is_comm.comm _ _
  have h1 : (QuotientGroup.mk ((⟨x, hx⟩ : ↥P) * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ * (⟨y, hy⟩)⁻¹) :
      ↥P ⧸ Subgroup.center ↥P) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hcomm]
    group
  rw [QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem card_centerIn (h : IsPOnePlusTwo p ↥P) : Nat.card (centerIn P) = p := by
  obtain ⟨hex, -, -⟩ := h
  rw [Subgroup.card_map_of_injective P.subtype_injective]
  exact hex.center_order_p

theorem exists_not_comm (h : IsPOnePlusTwo p ↥P) : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨hex, -, -⟩ := h
  have hnt := hex.quotient_nontrivial
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center ↥P = ⊤ := by
    refine eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => ?_
    exact Subtype.ext (hcon y y.2 x x.2)
  rw [htop] at hnt
  obtain ⟨a, b, hab⟩ := hnt
  apply hab
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  rw [QuotientGroup.eq]
  exact Subgroup.mem_top _

theorem pow_eq_one_of_pOnePlusTwo (h : IsPOnePlusTwo p ↥P) {x : Y} (hx : x ∈ P) : x ^ p = 1 :=
  congrArg Subtype.val (h.2.2 ⟨x, hx⟩)

theorem frattini_le_center [Finite Y] (hp : p.Prime) (h : IsPOnePlusTwo p ↥P) :
    frattini ↥P ≤ Subgroup.center ↥P := by
  obtain ⟨hex, -, hpow⟩ := h
  have hab := hex.quotient_elementary_abelian
  have hfr : frattini (↥P ⧸ Subgroup.center ↥P) = ⊥ := by
    refine frattini_eq_bot_of_forall hp (fun a b => hab.toIsMulCommutative.is_comm.comm a b)
      (fun a => ?_)
    induction a using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hpow x, QuotientGroup.mk_one]
  have h1 := frattini_le_comap_frattini_of_surjective
    (QuotientGroup.mk'_surjective (Subgroup.center ↥P))
  rw [hfr, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h1
  exact h1

theorem commutator_mul_left_of_comm {z x v : Y} (h : z * (x * v * x⁻¹) = (x * v * x⁻¹) * z) :
    (z * x) * v * (z * x)⁻¹ * v⁻¹ = x * v * x⁻¹ * v⁻¹ := by
  calc (z * x) * v * (z * x)⁻¹ * v⁻¹ = z * (x * v * x⁻¹) * z⁻¹ * v⁻¹ := by group
    _ = (x * v * x⁻¹) * z * z⁻¹ * v⁻¹ := by rw [h]
    _ = x * v * x⁻¹ * v⁻¹ := by group

theorem commutator_mul_right_of_comm {z u w : Y} (h : u * z = z * u)
    (h' : z * (u * w * u⁻¹ * w⁻¹) = (u * w * u⁻¹ * w⁻¹) * z) :
    u * (z * w) * u⁻¹ * (z * w)⁻¹ = u * w * u⁻¹ * w⁻¹ := by
  calc u * (z * w) * u⁻¹ * (z * w)⁻¹ = (u * z) * w * u⁻¹ * w⁻¹ * z⁻¹ := by group
    _ = (z * u) * w * u⁻¹ * w⁻¹ * z⁻¹ := by rw [h]
    _ = z * (u * w * u⁻¹ * w⁻¹) * z⁻¹ := by group
    _ = (u * w * u⁻¹ * w⁻¹) * z * z⁻¹ := by rw [h']
    _ = u * w * u⁻¹ * w⁻¹ := by group

theorem commutator_inv_right_of_comm {x y : Y}
    (h : y * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * y) :
    x * y⁻¹ * x⁻¹ * y = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have h1 : c⁻¹ * y = y * c⁻¹ := by
    calc c⁻¹ * y = c⁻¹ * (y * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * y) * c⁻¹ := by rw [h]
      _ = y * c⁻¹ := by group
  calc x * y⁻¹ * x⁻¹ * y = y⁻¹ * (c⁻¹ * y) := by rw [hc]; group
    _ = y⁻¹ * (y * c⁻¹) := by rw [h1]
    _ = c⁻¹ := by group

theorem false_of_fix_inv (h : IsPOnePlusTwo p ↥P) (hp : p.Prime) (hp2 : p ≠ 2) {a x y : Y}
    (hx : x ∈ P) (hy : y ∈ P) (haZ : ∀ z ∈ centerIn P, a * z * a⁻¹ = z)
    (hax : a * x * a⁻¹ * x⁻¹ ∈ centerIn P) (hay : a * y * a⁻¹ * y ∈ centerIn P)
    (hgen : ∀ g ∈ P, ∃ i j : ℤ, (x ^ i * y ^ j)⁻¹ * g ∈ centerIn P) : False := by
  have hZP : centerIn P ≤ P := centerIn_le
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcZ : c ∈ centerIn P := commutator_mem_centerIn h hx hy
  have hcP : c ∈ P := hZP hcZ
  set z₁ := a * x * a⁻¹ * x⁻¹ with hz₁
  set z₂ := a * y * a⁻¹ * y with hz₂
  have hax' : a * x * a⁻¹ = z₁ * x := by rw [hz₁]; group
  have hay' : a * y * a⁻¹ = z₂ * y⁻¹ := by rw [hz₂]; group
  have hcomm : ∀ z ∈ centerIn P, ∀ g ∈ P, z * g = g * z := fun z hz g hg =>
    comm_of_mem_centerIn hz hg
  have hyinv : y⁻¹ ∈ P := P.inv_mem hy
  have h1 : a * c * a⁻¹ = (z₁ * x) * (z₂ * y⁻¹) * (z₁ * x)⁻¹ * (z₂ * y⁻¹)⁻¹ := by
    rw [← hax', ← hay', hc]; group
  have h2 : (z₁ * x) * (z₂ * y⁻¹) * (z₁ * x)⁻¹ * (z₂ * y⁻¹)⁻¹ =
      x * (z₂ * y⁻¹) * x⁻¹ * (z₂ * y⁻¹)⁻¹ := by
    refine commutator_mul_left_of_comm (hcomm z₁ hax _ ?_)
    exact P.mul_mem (P.mul_mem hx (P.mul_mem (hZP hay) hyinv)) (P.inv_mem hx)
  have h3 : x * (z₂ * y⁻¹) * x⁻¹ * (z₂ * y⁻¹)⁻¹ = x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ := by
    refine commutator_mul_right_of_comm (hcomm z₂ hay x hx).symm (hcomm z₂ hay _ ?_)
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hyinv) (P.inv_mem hx)) (P.inv_mem hyinv)
  have h4 : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = c⁻¹ := by
    rw [inv_inv]
    exact commutator_inv_right_of_comm (hcomm c hcZ y hy).symm
  have hc2 : c * c = 1 := by
    have h5 : a * c * a⁻¹ = c⁻¹ := by rw [h1, h2, h3, h4]
    rw [haZ c hcZ] at h5
    calc c * c = c * c⁻¹ := by rw [← h5]
      _ = 1 := mul_inv_cancel c
  have hcp : c ^ p = 1 := pow_eq_one_of_pOnePlusTwo h hcP
  have hc1 : c = 1 := by
    have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    refine eq_one_of_pow_coprime (m := p) (n := 2) hcp ?_ hcop
    rw [sq]; exact hc2
  have hxy : x * y = y * x := by
    have : x * y * x⁻¹ * y⁻¹ = 1 := hc1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [this, one_mul]
  have hform : ∀ g ∈ P, ∃ i j : ℤ, ∃ z ∈ centerIn P, g = x ^ i * y ^ j * z := by
    intro g hg
    obtain ⟨i, j, hz⟩ := hgen g hg
    exact ⟨i, j, _, hz, by group⟩
  obtain ⟨u, hu, v, hv, huv⟩ := exists_not_comm h
  apply huv
  obtain ⟨i, j, z, hz, rfl⟩ := hform u hu
  obtain ⟨k, l, z', hz', rfl⟩ := hform v hv
  have hcx : ∀ m n : ℤ, Commute (x ^ m) (y ^ n) := fun m n => (Commute.zpow_zpow hxy m n)
  have hxyP : ∀ m n : ℤ, x ^ m * y ^ n ∈ P := fun m n =>
    P.mul_mem (P.zpow_mem hx m) (P.zpow_mem hy n)
  have hA := hxyP i j
  have hB := hxyP k l
  have e1 : x ^ i * y ^ j * z * (x ^ k * y ^ l * z') =
      (x ^ i * y ^ j) * (x ^ k * y ^ l) * (z * z') := by
    calc x ^ i * y ^ j * z * (x ^ k * y ^ l * z') =
          (x ^ i * y ^ j) * (z * (x ^ k * y ^ l)) * z' := by group
      _ = (x ^ i * y ^ j) * ((x ^ k * y ^ l) * z) * z' := by rw [hcomm z hz _ hB]
      _ = (x ^ i * y ^ j) * (x ^ k * y ^ l) * (z * z') := by group
  have e2 : x ^ k * y ^ l * z' * (x ^ i * y ^ j * z) =
      (x ^ k * y ^ l) * (x ^ i * y ^ j) * (z' * z) := by
    calc x ^ k * y ^ l * z' * (x ^ i * y ^ j * z) =
          (x ^ k * y ^ l) * (z' * (x ^ i * y ^ j)) * z := by group
      _ = (x ^ k * y ^ l) * ((x ^ i * y ^ j) * z') * z := by rw [hcomm z' hz' _ hA]
      _ = (x ^ k * y ^ l) * (x ^ i * y ^ j) * (z' * z) := by group
  have e3 : Commute (x ^ i * y ^ j) (x ^ k * y ^ l) :=
    ((Commute.zpow_zpow_self x i k).mul_right (hcx i l)).mul_left
      ((hcx k j).symm.mul_right (Commute.zpow_zpow_self y j l))
  rw [e1, e2, e3.eq, hcomm z hz z' (hZP hz')]

end Extraspecial

theorem E2_1_pOnePlusTwo {X : Type*} [Group X] [Finite X] {T M : Subgroup X}
    (h : MinParabolic (⊤ : Subgroup X) T M)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hsolv : Group.IsSolvable X)
    (hR : ∃ t ∈ T, (∀ j ∈ kerIn M ⊤, t * j * t⁻¹ * j⁻¹ ∈ pCoreOf 2 (kerIn M ⊤)) ∧
        t ∉ CFSG.Open.pCore 2 X)
    (hK : ¬ kerIn M ⊤ ≤ CFSG.Open.pCore 2 X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      IsPOnePlusTwo p ↥(twoResidual (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X))) ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
        centerIn (twoResidual (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X))) := by
  obtain ⟨p, hp, hp2, hcases⟩ := E2_1 h hSQT hsolv (Or.inr hR)
  obtain ⟨p', hp', hp2', hO2p2, hJbar, -, -⟩ := h.solvable_structure hsolv
  have : Fact p'.Prime := ⟨hp'⟩
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  have h2P : ∀ y : X ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore p' (X ⧸ Q) := by
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p X p')).mp hO2p2 x
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  have hKP : twoResidual (⊤ : Subgroup (X ⧸ Q)) = CFSG.Open.pCore p' (X ⧸ Q) :=
    E2.twoResidual_eq_pCore hp' hp2' h2P
  set P := twoResidual (⊤ : Subgroup (X ⧸ Q)) with hP
  rw [← hKP] at hJbar
  have hJ1 : (kerIn M ⊤).map φ ≠ ⊥ := by
    intro hbot
    apply hK
    intro j hj
    have : φ j = 1 := by
      have : φ j ∈ (kerIn M ⊤).map φ := ⟨j, hj, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    rwa [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hEA : ∀ (Mo : Type) [CommGroup Mo], (∀ m : Mo, m ^ p = 1) → Nonempty (↥P ≃* Mo) →
      False := by
    intro Mo _ hMo ⟨e⟩
    apply hJ1
    rw [hJbar, frattini_eq_bot_of_forall hp
      (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm]))
      (fun a => e.injective (by rw [map_pow, hMo, map_one])), Subgroup.map_bot]
  rcases hcases with h1 | h2 | h3
  · exact (hEA _ (pow_eq_one_zmod p) h1).elim
  · exact (hEA _ (pow_eq_one_zmod_pi p 2) h2).elim
  · refine ⟨p, hp, hp2, h3, ?_⟩
    have hle : (kerIn M ⊤).map φ ≤ centerIn P := by
      rw [hJbar]
      exact Subgroup.map_mono (frattini_le_center hp h3)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_centerIn h3]
    have hdvd : Nat.card ↥((kerIn M ⊤).map φ) ∣ p := by
      rw [← card_centerIn h3]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hJ1
    · exact h1.ge

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff {H : Subgroup G} (g : ↥H) :
    g ∈ CFSG.Open.pCore 2 ↥H ↔ (g : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff_open g).symm

theorem mem_pCoreOf_of_commutator_mem {H T M : Subgroup G} (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable ↥H) {a : G} (haT : a ∈ T)
    (hca : ∀ x ∈ twoResidual H, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 H) : a ∈ pCoreOf 2 H := by
  have := hsolv
  have hX := h.subgroupOf
  obtain ⟨p', hp', hp2', hO2p2, -, -, -⟩ := hX.solvable_structure hsolv
  have : Fact p'.Prime := ⟨hp'⟩
  set Q := CFSG.Open.pCore 2 ↥H with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have h2P : ∀ y : ↥H ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore p' (↥H ⧸ Q) := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p ↥H p')).mp hO2p2 x
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  have hKP : twoResidual (⊤ : Subgroup (↥H ⧸ Q)) = CFSG.Open.pCore p' (↥H ⧸ Q) :=
    E2.twoResidual_eq_pCore hp' hp2' h2P
  have hO2 : CFSG.Open.pCore 2 (↥H ⧸ Q) = ⊥ := B6.pCore_quotient_pCore
  have hTH : T ≤ H := h.isSylow.1
  have haH : a ∈ H := hTH haT
  obtain ⟨k, hk⟩ := h.isSylow.2.1 ⟨a, haT⟩
  have hak : π ⟨a, haH⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨a, haH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hPmap : twoResidual (⊤ : Subgroup (↥H ⧸ Q)) = ((twoResidual H).subgroupOf H).map π := by
    rw [← B6.twoResidual_top_eq_subgroupOf, E1.map_twoResidual,
      Subgroup.map_top_of_surjective π hπs]
  have hcent : π ⟨a, haH⟩ ∈ Subgroup.centralizer (CFSG.Open.pCore p' (↥H ⧸ Q) : Set (↥H ⧸ Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hKP, hPmap] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxH : (x : G) ∈ twoResidual H := hx
    have h1 : π (⟨a, haH⟩ * x * (⟨a, haH⟩)⁻¹ * x⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff]
      exact hca _ hxH
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π x * π ⟨a, haH⟩ = (π ⟨a, haH⟩ * π x * (π ⟨a, haH⟩)⁻¹ * (π x)⁻¹)⁻¹ *
          (π ⟨a, haH⟩ * π x) := by group
      _ = π ⟨a, haH⟩ * π x := by rw [h1, inv_one, one_mul]
  have h1 := E2.eq_one_of_mem_centralizer hp' hp2' h2P hO2 inferInstance hak hcent
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff] at h1
  exact h1

theorem plusTwo_of {H T M : Subgroup G} (h : MinParabolic H T M) (hsolv : Group.IsSolvable ↥H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2) {r : G} (hrT : r ∈ T)
    (hrO : r ∉ pCoreOf 2 H) (hrK : ∀ k ∈ kerIn M H, r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hK : ¬ kerIn M H ≤ pCoreOf 2 H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∀ k ∈ kerIn M H, k ^ p ∈ pCoreOf 2 H) ∧
      ∀ a x y : G, a ∈ H → x ∈ twoResidual H → y ∈ twoResidual H →
        (∀ k ∈ kerIn M H, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
        a * x * a⁻¹ * x⁻¹ ∈ kerIn M H → a * y * a⁻¹ * y ∈ kerIn M H →
        (∀ g ∈ twoResidual H, ∃ i j : ℤ, (x ^ i * y ^ j)⁻¹ * g ∈ kerIn M H) → False := by
  have := hsolv
  have hX := h.subgroupOf
  have hTH : T ≤ H := h.isSylow.1
  set Q := CFSG.Open.pCore 2 ↥H with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set K' := kerIn (M.subgroupOf H) (⊤ : Subgroup ↥H) with hK'
  have hK'eq : K' = (kerIn M H).subgroupOf H := B6.kerIn_subgroupOf_top M H
  have hmemK' : ∀ g : ↥H, g ∈ K' ↔ (g : G) ∈ kerIn M H := fun g => by
    rw [hK'eq, Subgroup.mem_subgroupOf]
  have hQK' : Q ≤ K' := by
    rw [hQ, ← pCoreOf_top]
    exact hX.pCoreOf_le_kerIn
  have hO2K' : pCoreOf 2 K' = Q := by
    rw [hQ, ← pCoreOf_top, hX.pCoreOf_eq_pCoreOf_kerIn]
  have hSQT' : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ 2 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    rw [pRank_top_subtype]
    exact hSQT p hp hp2
  have hR : ∃ t ∈ T.subgroupOf H, (∀ j ∈ K', t * j * t⁻¹ * j⁻¹ ∈ pCoreOf 2 K') ∧ t ∉ Q := by
    refine ⟨⟨r, hTH hrT⟩, Subgroup.mem_subgroupOf.mpr hrT, fun j hj => ?_, ?_⟩
    · rw [hO2K', mem_pCore_iff]
      exact hrK _ ((hmemK' j).1 hj)
    · rw [mem_pCore_iff]
      exact hrO
  have hK'Q : ¬ K' ≤ Q := by
    intro hle
    apply hK
    intro k hk
    have hkH : k ∈ H := h.kerIn_le_H hk
    have := hle ((hmemK' ⟨k, hkH⟩).2 hk)
    rwa [mem_pCore_iff] at this
  obtain ⟨p, hp, hp2, hP3, hKeq⟩ := E2_1_pOnePlusTwo hX hSQT' hsolv hR hK'Q
  have hPmap : twoResidual (⊤ : Subgroup (↥H ⧸ Q)) = ((twoResidual H).subgroupOf H).map π := by
    rw [← B6.twoResidual_top_eq_subgroupOf, E1.map_twoResidual,
      Subgroup.map_top_of_surjective π hπs]
  have hZ : ∀ (g : G) (hg : g ∈ H), g ∈ kerIn M H →
      π ⟨g, hg⟩ ∈ centerIn (twoResidual (⊤ : Subgroup (↥H ⧸ Q))) := fun g hg hgK => by
    rw [← hKeq]
    exact ⟨⟨g, hg⟩, (hmemK' _).2 hgK, rfl⟩
  have hP : ∀ (g : G) (hg : g ∈ H), g ∈ twoResidual H →
      π ⟨g, hg⟩ ∈ twoResidual (⊤ : Subgroup (↥H ⧸ Q)) := fun g hg hgR => by
    rw [hPmap]
    exact ⟨⟨g, hg⟩, hgR, rfl⟩
  have hone : ∀ (g : G) (hg : g ∈ H), π ⟨g, hg⟩ = 1 ↔ g ∈ pCoreOf 2 H := fun g hg => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff]
  refine ⟨p, hp, hp2, fun k hk => ?_, ?_⟩
  · have hkH : k ∈ H := h.kerIn_le_H hk
    have h1 : π ⟨k, hkH⟩ ^ p = 1 := pow_eq_one_of_pOnePlusTwo hP3 (centerIn_le (hZ k hkH hk))
    rw [← map_pow] at h1
    exact (hone _ (H.pow_mem hkH p)).1 h1
  · intro a x y haH hx hy haK hax hay hgen
    have hxH : x ∈ H := twoResidual_le H hx
    have hyH : y ∈ H := twoResidual_le H hy
    refine false_of_fix_inv hP3 hp hp2 (a := π ⟨a, haH⟩) (hP x hxH hx) (hP y hyH hy) ?_ ?_ ?_ ?_
    · intro z hz
      rw [← hKeq] at hz
      obtain ⟨k, hk, rfl⟩ := hz
      have hkK := (hmemK' k).1 hk
      have h1 : π (⟨a, haH⟩ * k * (⟨a, haH⟩)⁻¹ * k⁻¹) = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff]
        exact haK _ hkK
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc π ⟨a, haH⟩ * π k * (π ⟨a, haH⟩)⁻¹ =
            (π ⟨a, haH⟩ * π k * (π ⟨a, haH⟩)⁻¹ * (π k)⁻¹) * π k := by group
        _ = π k := by rw [h1, one_mul]
    · have h1 := hZ _ (H.mul_mem (H.mul_mem (H.mul_mem haH hxH) (H.inv_mem haH)) (H.inv_mem hxH))
        hax
      have e : (⟨a * x * a⁻¹ * x⁻¹, H.mul_mem (H.mul_mem (H.mul_mem haH hxH) (H.inv_mem haH))
          (H.inv_mem hxH)⟩ : ↥H) = ⟨a, haH⟩ * ⟨x, hxH⟩ * (⟨a, haH⟩)⁻¹ * (⟨x, hxH⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact h1
    · have h1 := hZ _ (H.mul_mem (H.mul_mem (H.mul_mem haH hyH) (H.inv_mem haH)) hyH) hay
      have e : (⟨a * y * a⁻¹ * y, H.mul_mem (H.mul_mem (H.mul_mem haH hyH) (H.inv_mem haH))
          hyH⟩ : ↥H) = ⟨a, haH⟩ * ⟨y, hyH⟩ * (⟨a, haH⟩)⁻¹ * ⟨y, hyH⟩ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv] at h1
      exact h1
    · intro g hg
      rw [hPmap] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      obtain ⟨i, j, hij⟩ := hgen (g' : G) hg'
      refine ⟨i, j, ?_⟩
      have hmem : (x ^ i * y ^ j)⁻¹ * (g' : G) ∈ H :=
        H.mul_mem (H.inv_mem (H.mul_mem (H.zpow_mem hxH i) (H.zpow_mem hyH j))) g'.2
      have h1 := hZ _ hmem hij
      have e : (⟨(x ^ i * y ^ j)⁻¹ * (g' : G), hmem⟩ : ↥H) =
          ((⟨x, hxH⟩ : ↥H) ^ i * (⟨y, hyH⟩ : ↥H) ^ j)⁻¹ * g' := Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_mul, map_zpow, map_zpow] at h1
      exact h1

end Transport

end CFSG.Quasithin.H13.A5
