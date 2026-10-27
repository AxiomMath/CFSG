module

public import CFSG.Assembly.Defs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4

open Subgroup

@[expose] def E81InvAt (X : Type*) [Group X] : Prop :=
  ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → 81 ≤ Nat.card B →
    ∃ t ∈ Subgroup.normalizer (B : Set X), t ≠ 1 ∧ t ^ 2 = 1 ∧
      Nat.card (B ⊓ Subgroup.centralizer {t} : Subgroup X) = 9

section General

variable {X Y : Type*} [Group X] [Group Y]

theorem isElemAbelian_map {p : ℕ} (f : X →* Y) {B : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian p B) : CFSG.Assembly.IsElemAbelian p (B.map f) :=
  CFSG.Open.IsElemAbelian.map hB _

theorem isPGroup_of_isElemAbelian {p : ℕ} {B : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian p B) : IsPGroup p B := CFSG.Open.IsElemAbelian.isPGroup hB

theorem isElemAbelian_of_le {p : ℕ} {B C : Subgroup X} (hC : CFSG.Assembly.IsElemAbelian p C)
    (hBC : B ≤ C) : CFSG.Assembly.IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hC hBC

theorem e81InvAt_of_mulEquiv (φ : X ≃* Y) (h : E81InvAt Y) : E81InvAt X := by
  intro B hB h81
  have hmem : ∀ x : X, x ∈ B ↔ φ x ∈ B.map φ.toMonoidHom := fun x =>
    (Subgroup.mem_map_iff_mem φ.injective).symm
  obtain ⟨t, htN, ht1, ht2, htC⟩ := h (B.map φ.toMonoidHom) (isElemAbelian_map _ hB)
    (by rw [Subgroup.card_map_of_injective φ.injective]; exact h81)
  have hφt : φ (φ.symm t) = t := φ.apply_symm_apply t
  refine ⟨φ.symm t, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem x, hmem (φ.symm t * x * (φ.symm t)⁻¹), map_mul, map_mul, map_inv, hφt]
    exact Subgroup.mem_normalizer_iff.mp htN (φ x)
  · intro h1
    apply ht1
    rw [← hφt, h1, map_one]
  · rw [← map_pow, ht2, map_one]
  · rw [← htC, ← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    refine congrArg (fun S : Subgroup _ => Nat.card S) ?_
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, ⟨hxB, hxc⟩, rfl⟩
      refine ⟨⟨x, hxB, rfl⟩, ?_⟩
      rw [← hφt, ← map_mul, ← map_mul, hxc]
    · rintro ⟨⟨x, hxB, rfl⟩, hxc⟩
      refine ⟨x, ⟨hxB, ?_⟩, rfl⟩
      apply φ.injective
      rw [map_mul, map_mul, hφt, hxc]

theorem exists_inv_of_map_conj {D : Subgroup X} (g : X) {t : X}
    (htN : t ∈ Subgroup.normalizer (D : Set X)) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htC : Nat.card (D ⊓ Subgroup.centralizer {t} : Subgroup X) = 9) :
    ∃ t' ∈ Subgroup.normalizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X),
      t' ≠ 1 ∧ t' ^ 2 = 1 ∧
      Nat.card (D.map (MulAut.conj g).toMonoidHom ⊓ Subgroup.centralizer {t'} : Subgroup X) =
        9 := by
  set φ : X ≃* X := MulAut.conj g with hφ
  have hmem : ∀ x : X, x ∈ D ↔ φ x ∈ D.map φ.toMonoidHom := fun x =>
    (Subgroup.mem_map_iff_mem φ.injective).symm
  refine ⟨φ t, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← hmem x, ← map_inv, ← map_mul, ← map_mul, ← hmem]
    exact Subgroup.mem_normalizer_iff.mp htN x
  · intro h1
    apply ht1
    apply φ.injective
    rw [h1, map_one]
  · rw [← map_pow, ht2, map_one]
  · rw [← htC, ← Subgroup.card_map_of_injective (K := D ⊓ Subgroup.centralizer {t})
      (f := φ.toMonoidHom) φ.injective]
    refine congrArg (fun S : Subgroup _ => Nat.card S) ?_
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨⟨x, hxD, rfl⟩, hxc⟩
      refine ⟨x, ⟨hxD, ?_⟩, rfl⟩
      apply φ.injective
      rw [map_mul, map_mul, hxc]
    · rintro ⟨x, ⟨hxD, hxc⟩, rfl⟩
      refine ⟨⟨x, hxD, rfl⟩, ?_⟩
      rw [← map_mul, ← map_mul, hxc]

end General

section Sylow

variable {X : Type*} [Group X] [Finite X]

theorem exists_le_map_conj {p : ℕ} [Fact p.Prime] {T E : Subgroup X}
    (hT : Nat.card T = p ^ (Nat.card X).factorization p) (hE : IsPGroup p E) :
    ∃ g : X, E ≤ T.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard T hT) P
  refine ⟨g, hP.trans ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  rfl

theorem exists_eq_map_conj {T A : Subgroup X}
    (hT : Nat.card T = 3 ^ (Nat.card X).factorization 3)
    (hA : ∀ B : Subgroup X, B ≤ T → IsMulCommutative B → 81 ≤ Nat.card B → B = A)
    {B : Subgroup X} (hB : CFSG.Assembly.IsElemAbelian 3 B) (h81 : 81 ≤ Nat.card B) :
    ∃ g : X, B = A.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_le_map_conj hT (isPGroup_of_isElemAbelian hB)
  set B' := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hB'T : B' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hg hx
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' := isElemAbelian_map _ hB
  have hB'card : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'A : B' = A := hA B' hB'T hB'e.1 (hB'card ▸ h81)
  refine ⟨g, ?_⟩
  rw [← hB'A, hB', Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem le_of_abelian_card_ge {T A : Subgroup X}
    (hAT : A ≤ T) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcardT : Nat.card ↥T = 729) (hcardA : Nat.card ↥A = 81)
    (hC : ∀ t ∈ T, t ∉ A → Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set X)) ≤ 9)
    (hZ : Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set X)) ≤ 3) {B : Subgroup X} (hBT : B ≤ T)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB : 81 ≤ Nat.card ↥B) : B ≤ A := by
  by_contra hBA
  obtain ⟨b, hbB, hbA⟩ := IsConcreteLE.not_le_iff_exists.1 hBA
  have hDle : A ⊓ B ≤ A ⊓ Subgroup.centralizer ({b} : Set X) := by
    intro d hd
    exact mem_inf.2 ⟨(mem_inf.1 hd).1,
      mem_centralizer_singleton_iff.2 (hBab d (mem_inf.1 hd).2 b hbB)⟩
  have hD9 : Nat.card ↥(A ⊓ B) ≤ 9 := (card_le_of_le hDle).trans (hC b (hBT hbB) hbA)
  have hAC : A ≤ T ⊓ Subgroup.centralizer ((A ⊓ B : Subgroup X) : Set X) := fun a ha =>
    mem_inf.2 ⟨hAT ha, mem_centralizer_iff.2 fun d hd => hAab d (mem_inf.1 hd).1 a ha⟩
  have hBC : B ≤ T ⊓ Subgroup.centralizer ((A ⊓ B : Subgroup X) : Set X) := fun c hc =>
    mem_inf.2 ⟨hBT hc, mem_centralizer_iff.2 fun d hd => hBab d (mem_inf.1 hd).2 c hc⟩
  set C : Subgroup X := T ⊓ Subgroup.centralizer ((A ⊓ B : Subgroup X) : Set X) with hCdef
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := C)
  rw [inf_of_le_left hBC] at h2
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hne : B.relIndex C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    omega
  have hle := Subgroup.relIndex_le_of_le_right hAC hne
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm] at h1
  have hkey : Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥C * Nat.card ↥(A ⊓ B) := by
    calc Nat.card ↥A * Nat.card ↥B
        = (B.relIndex A * Nat.card ↥(A ⊓ B)) * Nat.card ↥B := by rw [h1]
      _ ≤ (B.relIndex C * Nat.card ↥(A ⊓ B)) * Nat.card ↥B := by gcongr
      _ = (B.relIndex C * Nat.card ↥B) * Nat.card ↥(A ⊓ B) := by ring
      _ = Nat.card ↥C * Nat.card ↥(A ⊓ B) := by rw [h2]
  have hC729 : Nat.card ↥C ≤ 729 := hcardT ▸ card_le_of_le (inf_le_left : C ≤ T)
  have h6561 : 6561 ≤ Nat.card ↥C * Nat.card ↥(A ⊓ B) := by
    calc 6561 = 81 * 81 := by norm_num
      _ ≤ Nat.card ↥A * Nat.card ↥B := by rw [hcardA]; exact Nat.mul_le_mul_left 81 hB
      _ ≤ _ := hkey
  have hCeq : Nat.card ↥C = 729 := by
    by_contra hne'
    have h728 : Nat.card ↥C ≤ 728 := by omega
    have := Nat.mul_le_mul h728 hD9
    omega
  have hDeq : Nat.card ↥(A ⊓ B) = 9 := by
    by_contra hne'
    have h8 : Nat.card ↥(A ⊓ B) ≤ 8 := by omega
    have := Nat.mul_le_mul hC729 h8
    omega
  have hCT : C = T :=
    Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ T) (by rw [hCeq, hcardT])
  have hDZ : A ⊓ B ≤ T ⊓ Subgroup.centralizer (T : Set X) := by
    intro d hd
    refine mem_inf.2 ⟨hAT (mem_inf.1 hd).1, mem_centralizer_iff.2 fun t ht => ?_⟩
    have htC : t ∈ C := hCT ▸ ht
    exact (mem_centralizer_iff.1 (mem_inf.1 htC).2 d hd).symm
  have := card_le_of_le hDZ
  omega

theorem e81InvAt_of_unique {T A : Subgroup X}
    (hT : Nat.card T = 3 ^ (Nat.card X).factorization 3)
    (hA : ∀ B : Subgroup X, B ≤ T → IsMulCommutative B → 81 ≤ Nat.card B → B = A)
    {D : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D) {t : X}
    (htN : t ∈ Subgroup.normalizer (D : Set X)) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htC : Nat.card (D ⊓ Subgroup.centralizer {t} : Subgroup X) = 9) : E81InvAt X := by
  intro B hB h81
  obtain ⟨g, rfl⟩ := exists_eq_map_conj hT hA hB h81
  obtain ⟨h, rfl⟩ := exists_eq_map_conj hT hA hD hD81
  obtain ⟨t', ht'⟩ := exists_inv_of_map_conj (g * h⁻¹) htN ht1 ht2 htC
  refine ⟨t', ?_⟩
  have e : (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj (g * h⁻¹)).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e] at ht'
  exact ht'

end Sylow

section Involution

variable {X : Type*} [Group X]

theorem conj_pow_odd_eq {s d : X} (hs : s ^ 2 * d = d * s ^ 2) {b : ℕ} (hb : Odd b) :
    s ^ b * d * (s ^ b)⁻¹ = s * d * s⁻¹ := by
  obtain ⟨k, rfl⟩ := hb
  have hc : Commute (s ^ 2) d := hs
  have hk : Commute ((s ^ 2) ^ k) d := hc.pow_left k
  rw [pow_succ, pow_mul]
  rw [show (s ^ 2) ^ k * s * d * ((s ^ 2) ^ k * s)⁻¹ =
      (s ^ 2) ^ k * (s * d * s⁻¹) * ((s ^ 2) ^ k)⁻¹ by group]
  have hk' : Commute ((s ^ 2) ^ k) (s * d * s⁻¹) := by
    have h1 : Commute ((s ^ 2) ^ k) s := (Commute.self_pow s 2).symm.pow_left k
    exact (h1.mul_right hk).mul_right h1.inv_right
  rw [hk'.eq, mul_inv_cancel_right]

variable [Finite X]

theorem exists_involution_of_sq {D : Subgroup X} {s : X}
    (hsq : ∀ d ∈ D, s ^ 2 * d = d * s ^ 2) {d₀ : X} (hd₀ : d₀ ∈ D) (hmove : s * d₀ * s⁻¹ ≠ d₀)
    (hno : ∀ u : X, u ≠ 1 → u ^ 2 = 1 → ¬ ∀ d ∈ D, u * d = d * u) :
    ∃ t : X, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ d ∈ D, t * d * t⁻¹ = s * d * s⁻¹ := by
  obtain ⟨a, b, hb, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  obtain ⟨w, hw⟩ : ∃ w, w = s ^ b := ⟨_, rfl⟩
  have hwd : ∀ d ∈ D, w * d * w⁻¹ = s * d * s⁻¹ := fun d hd => by
    rw [hw]
    exact conj_pow_odd_eq (hsq d hd) hb
  have hwo : orderOf w = 2 ^ a := by
    rw [hw, orderOf_pow' s hb.pos.ne', hn, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ hb.pos]
  have hw2 : ∀ d ∈ D, w ^ 2 * d = d * w ^ 2 := fun d hd => by
    have e : w ^ 2 = (s ^ 2) ^ b := by rw [hw, ← pow_mul, ← pow_mul, mul_comm]
    rw [e]
    exact ((show Commute (s ^ 2) d from hsq d hd).pow_left b).eq
  rcases Nat.lt_or_ge a 1 with ha | ha
  ·
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero, orderOf_eq_one_iff] at hwo
    exfalso
    apply hmove
    rw [← hwd d₀ hd₀, hwo]
    group
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    have ha1 : a = 1 := by omega
    rw [ha1, pow_one] at hwo
    refine ⟨w, ?_, ?_, hwd⟩
    · intro h
      rw [h, orderOf_one] at hwo
      omega
    · rw [← hwo, pow_orderOf_eq_one]
  ·
    exfalso
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
    obtain ⟨u, hu⟩ : ∃ u, u = (w ^ 2) ^ (2 ^ c) := ⟨_, rfl⟩
    have hu' : u = w ^ (2 ^ (c + 1)) := by rw [hu, ← pow_mul, pow_succ']
    have hu2 : u ^ 2 = 1 := by
      rw [hu', ← pow_mul, show 2 ^ (c + 1) * 2 = 2 ^ (c + 2) by ring, ← hwo,
        pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := by
      intro h
      rw [hu'] at h
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [hwo] at hdvd
      have := Nat.le_of_dvd (by positivity) hdvd
      have h2 : 2 ^ (c + 1) < 2 ^ (c + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    apply hno u hu1 hu2
    intro d hd
    rw [hu]
    exact ((show Commute (w ^ 2) d from hw2 d hd).pow_left _).eq

end Involution

section Count

variable {X : Type*} [Group X] [Finite X]

theorem card_sup_le_mul {H K : Subgroup X} (hHK : H ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card (H ⊔ K : Subgroup X) ≤ Nat.card H * Nat.card K := by
  have hsurj : Function.Surjective (fun p : H × K =>
      (⟨(p.1 : X) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : (H ⊔ K : Subgroup X))) := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H K hHK] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod] at h

omit [Finite X] in
theorem card_zpowers_le_three {x : X} (hx : x ^ 3 = 1) : Nat.card (Subgroup.zpowers x) ≤ 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) hx

theorem card_mul_card_le {C N D : Subgroup X} (hCD : C ≤ D) (hND : N ≤ D) (hCN : C ⊓ N = ⊥) :
    Nat.card C * Nat.card N ≤ Nat.card D := by
  let f : C × N → D := fun p => ⟨(p.1 : X) * p.2, D.mul_mem (hCD p.1.2) (hND p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨c₁, hc₁⟩, ⟨n₁, hn₁⟩⟩ ⟨⟨c₂, hc₂⟩, ⟨n₂, hn₂⟩⟩ h
    have h' : c₁ * n₁ = c₂ * n₂ := congrArg Subtype.val h
    have hmem : c₂⁻¹ * c₁ ∈ C ⊓ N := by
      refine ⟨C.mul_mem (C.inv_mem hc₂) hc₁, ?_⟩
      have : c₂⁻¹ * c₁ = n₂ * n₁⁻¹ := by
        calc c₂⁻¹ * c₁ = c₂⁻¹ * (c₁ * n₁) * n₁⁻¹ := by group
          _ = c₂⁻¹ * (c₂ * n₂) * n₁⁻¹ := by rw [h']
          _ = n₂ * n₁⁻¹ := by group
      rw [this]
      exact N.mul_mem hn₂ (N.inv_mem hn₁)
    rw [hCN, Subgroup.mem_bot] at hmem
    have hc : c₁ = c₂ := by
      calc c₁ = c₂ * (c₂⁻¹ * c₁) := by group
        _ = c₂ := by rw [hmem, mul_one]
    subst hc
    have hn : n₁ = n₂ := mul_left_cancel h'
    subst hn
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h

theorem card_inf_centralizer_eq_nine {e : Fin 4 → X}
    (hDe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure (Set.range e)))
    (h81 : 81 ≤ Nat.card (Subgroup.closure (Set.range e))) {t : X}
    (h0 : t * e 0 * t⁻¹ = e 0) (h1 : t * e 1 * t⁻¹ = e 1) (h2 : t * e 2 * t⁻¹ = (e 2)⁻¹)
    (h3 : t * e 3 * t⁻¹ = (e 3)⁻¹) :
    Nat.card (Subgroup.closure (Set.range e) ⊓ Subgroup.centralizer {t} : Subgroup X) = 9 := by
  set D := Subgroup.closure (Set.range e) with hD
  set F := Subgroup.zpowers (e 0) ⊔ Subgroup.zpowers (e 1) with hF
  set N := Subgroup.zpowers (e 2) ⊔ Subgroup.zpowers (e 3) with hN
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have heD : ∀ i, e i ∈ D := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hcube : ∀ i, e i ^ 3 = 1 := fun i => hDe.2 _ (heD i)
  have hleD : ∀ i, Subgroup.zpowers (e i) ≤ D := fun i => Subgroup.zpowers_le.mpr (heD i)
  have hFD : F ≤ D := sup_le (hleD 0) (hleD 1)
  have hND : N ≤ D := sup_le (hleD 2) (hleD 3)
  have hnorm : ∀ H K : Subgroup X, H ≤ D → K ≤ D → H ≤ Subgroup.normalizer (K : Set X) := by
    intro H K hH hK h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hDcomm h (hH hh) k (hK hk), mul_inv_cancel_right]
      exact hk
    · intro hk
      have hkD : h * k * h⁻¹ ∈ D := hK hk
      have hkD' : k ∈ D := by
        have := D.mul_mem (D.mul_mem (D.inv_mem (hH hh)) hkD) (hH hh)
        simpa [mul_assoc] using this
      rw [hDcomm h (hH hh) k hkD', mul_inv_cancel_right] at hk
      exact hk
  have hFle : Nat.card F ≤ 9 :=
    (card_sup_le_mul (hnorm _ _ (hleD 0) (hleD 1))).trans
      (Nat.mul_le_mul (card_zpowers_le_three (hcube 0)) (card_zpowers_le_three (hcube 1)))
  have hNle : Nat.card N ≤ 9 :=
    (card_sup_le_mul (hnorm _ _ (hleD 2) (hleD 3))).trans
      (Nat.mul_le_mul (card_zpowers_le_three (hcube 2)) (card_zpowers_le_three (hcube 3)))
  have hDFN : D = F ⊔ N := by
    apply le_antisymm
    · rw [hD, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact sup_le hFD hND
  have hDle : Nat.card D ≤ Nat.card F * Nat.card N := by
    rw [hDFN]
    exact card_sup_le_mul (hnorm _ _ hFD hND)
  have hF9 : Nat.card F = 9 := by
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hN9 : Nat.card N = 9 := by
    have hpos : 0 < Nat.card F := Nat.card_pos
    nlinarith
  have hD81 : Nat.card D = 81 := by
    have := hDle
    rw [hF9, hN9] at this
    omega
  set C := D ⊓ Subgroup.centralizer ({t} : Set X) with hC
  have hFC : F ≤ C := by
    refine le_inf hFD (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      calc e 0 * t = t * e 0 * t⁻¹ * t := by rw [h0]
        _ = t * e 0 := by group
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      calc e 1 * t = t * e 1 * t⁻¹ * t := by rw [h1]
        _ = t * e 1 := by group
  have hinvN : ∀ n ∈ N, t * n * t⁻¹ = n⁻¹ := by
    intro n hn
    rw [hN, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hnorm _ _ (hleD 2) (hleD 3))] at hn
    obtain ⟨x, hx, y, hy, rfl⟩ := hn
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [show t * (e 2 ^ i * e 3 ^ j) * t⁻¹ = (t * e 2 ^ i * t⁻¹) * (t * e 3 ^ j * t⁻¹) by group,
      ← conj_zpow, ← conj_zpow, h2, h3, inv_zpow, inv_zpow, mul_inv_rev]
    exact hDcomm _ (D.inv_mem (D.zpow_mem (heD 2) i)) _ (D.inv_mem (D.zpow_mem (heD 3) j))
  have hCN : C ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro n ⟨⟨hnD, hnc⟩, hnN⟩
    rw [Subgroup.mem_bot]
    have h1' : t * n * t⁻¹ = n := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp hnc).symm, mul_inv_cancel_right]
    have h2' : n = n⁻¹ := h1'.symm.trans (hinvN n hnN)
    have hn2 : n ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h2']
      exact mul_inv_cancel n
    have hn3 : n ^ 3 = 1 := hDe.2 n hnD
    calc n = n ^ 3 * (n ^ 2)⁻¹ := by group
      _ = 1 := by rw [hn2, hn3, inv_one, one_mul]
  have hCNcard : Nat.card C * Nat.card N ≤ Nat.card D :=
    card_mul_card_le inf_le_left hND hCN
  have hCle : Nat.card C ≤ 9 := by
    rw [hN9, hD81] at hCNcard
    omega
  have hCge : 9 ≤ Nat.card C := hF9 ▸ Subgroup.card_le_of_le hFC
  omega

theorem mem_normalizer_closure_of_conj_mem {S : Set X} {s : X}
    (h : ∀ x ∈ S, s * x * s⁻¹ ∈ Subgroup.closure S) :
    s ∈ Subgroup.normalizer (Subgroup.closure S : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.closure S).map (MulAut.conj s).toMonoidHom ≤ Subgroup.closure S := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact h x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj s).injective).ge

omit [Finite X] in
theorem exists_pow_of_mem_zpowers {z w : X} (hz : z ^ 3 = 1) (hw : w ∈ Subgroup.zpowers z) :
    ∃ i < 3, w = z ^ i := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hz' : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod k hz', ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]

omit [Finite X] in
theorem zpowers_le_normalizer_of_comm {x y : X} (hxy : x * y = y * x) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set X) := by
  rw [Subgroup.zpowers_le]
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (Commute.zpow_left (show Commute y x from hxy.symm) k).eq

omit [Finite X] in
theorem exists_pow_of_mem_sup {x y n : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x)
    (hn : n ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ i < 3, ∃ j < 3, n = x ^ i * y ^ j := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (zpowers_le_normalizer_of_comm hxy)] at hn
  obtain ⟨u, hu, v, hv, rfl⟩ := hn
  obtain ⟨i, hi, rfl⟩ := exists_pow_of_mem_zpowers hx hu
  obtain ⟨j, hj, rfl⟩ := exists_pow_of_mem_zpowers hy hv
  exact ⟨i, hi, j, hj, rfl⟩

omit [Finite X] in
theorem exists_pow_of_mem_sup3 {x y z n : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hn : n ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers z) :
    ∃ i < 3, ∃ j < 3, ∃ k < 3, n = x ^ i * y ^ j * z ^ k := by
  have hN : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set X) :=
    sup_le (zpowers_le_normalizer_of_comm hxz) (zpowers_le_normalizer_of_comm hyz)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hn
  obtain ⟨u, hu, v, hv, rfl⟩ := hn
  obtain ⟨i, hi, j, hj, rfl⟩ := exists_pow_of_mem_sup hx hy hxy hu
  obtain ⟨k, hk, rfl⟩ := exists_pow_of_mem_zpowers hz hv
  exact ⟨i, hi, j, hj, k, hk, rfl⟩

theorem card_closure_four_le {a b c d : X}
    (hDe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({a, b, c, d} : Set X))) :
    Nat.card (Subgroup.closure ({a, b, c, d} : Set X)) ≤ 81 := by
  set D := Subgroup.closure ({a, b, c, d} : Set X) with hD
  have hmem : a ∈ D ∧ b ∈ D ∧ c ∈ D ∧ d ∈ D :=
    ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
      Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hnorm : ∀ H K : Subgroup X, H ≤ D → K ≤ D → H ≤ Subgroup.normalizer (K : Set X) := by
    intro H K hH hK h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hcomm h (hH hh) k (hK hk), mul_inv_cancel_right]
      exact hk
    · intro hk
      have hkD : h * k * h⁻¹ ∈ D := hK hk
      have hkD' : k ∈ D := by
        have := D.mul_mem (D.mul_mem (D.inv_mem (hH hh)) hkD) (hH hh)
        simpa [mul_assoc] using this
      rw [hcomm h (hH hh) k hkD', mul_inv_cancel_right] at hk
      exact hk
  have hz : ∀ x ∈ D, Subgroup.zpowers x ≤ D := fun x hx => Subgroup.zpowers_le.mpr hx
  have h3 : ∀ x ∈ D, Nat.card (Subgroup.zpowers x) ≤ 3 := fun x hx =>
    card_zpowers_le_three (hDe.2 x hx)
  have hab := hnorm _ _ (hz a hmem.1) (hz b hmem.2.1)
  have hcd := hnorm _ _ (hz c hmem.2.2.1) (hz d hmem.2.2.2)
  have hF : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) ≤ 9 :=
    (card_sup_le_mul hab).trans (Nat.mul_le_mul (h3 a hmem.1) (h3 b hmem.2.1))
  have hN : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup X) ≤ 9 :=
    (card_sup_le_mul hcd).trans (Nat.mul_le_mul (h3 c hmem.2.2.1) (h3 d hmem.2.2.2))
  have hFD : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ D := sup_le (hz a hmem.1) (hz b hmem.2.1)
  have hND : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ D :=
    sup_le (hz c hmem.2.2.1) (hz d hmem.2.2.2)
  have hDeq : D = (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔
      (Subgroup.zpowers c ⊔ Subgroup.zpowers d) := by
    apply le_antisymm
    · rw [hD, Subgroup.closure_le]
      rintro x (rfl | rfl | rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact sup_le hFD hND
  calc Nat.card D = Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔
        (Subgroup.zpowers c ⊔ Subgroup.zpowers d) : Subgroup X) := by rw [← hDeq]
    _ ≤ _ * _ := card_sup_le_mul (hnorm _ _ hFD hND)
    _ ≤ 9 * 9 := Nat.mul_le_mul hF hN
    _ = 81 := by norm_num

end Count

end CFSG.RankThree.PartTwo.Sec6.Res611Res4
