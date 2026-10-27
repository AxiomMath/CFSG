module

public import CFSG.Milestones.ASVolI.A3L3.StepsTheta
public import CFSG.Milestones.ASVolI.A3L3.StepsBase

public section

namespace CFSG.ASVolI

open CFSG.GorensteinWalter
open scoped Pointwise MatrixGroups

theorem burnsideA315y_sq_eq_one {X : Type} [Group X] {p : ℕ} {K : Subgroup X}
    (e : ↥K ≃* SL(2, ZMod p)) {z : X} (hzK : z ∈ K)
    (hzC : z ∈ Subgroup.centralizer (K : Set X)) : z ^ 2 = 1 := by
  have hc : e ⟨z, hzK⟩ ∈ Subgroup.center (SL(2, ZMod p)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC k k.2
  have h2 := burnsideA315y_sl2_center_sq hc
  have : (⟨z, hzK⟩ : ↥K) ^ 2 = 1 := e.injective (by rw [map_pow, h2, map_one])
  simpa using congrArg Subtype.val this

theorem burnsideA315y_pow_card_eq_one {X : Type} [Group X] [Finite X] {B : Subgroup X} {b : X}
    (hb : b ∈ B) : b ^ Nat.card ↥B = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb)

theorem burnsideA315y_eq_one_of_sq_of_odd {G : Type*} [Monoid G] {w : G} {n : ℕ} (hn : Odd n)
    (h2 : w ^ 2 = 1) (hn1 : w ^ n = 1) : w = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.2 hn)
    (orderOf_dvd_of_pow_eq_one hn1) (orderOf_dvd_of_pow_eq_one h2))

theorem burnsideA315y_conj_eq_inv {X : Type} [Group X] {p : ℕ} {K M : Subgroup X}
    (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M) (hMN : M ≤ Subgroup.normalizer (K : Set X))
    (θ : ↥M →* PGL2 (ZMod p))
    (hθker : ∀ m : ↥M, θ m = 1 ↔ (m : X) ∈ Subgroup.centralizer (K : Set X))
    (t : ↥M) {k : X} (hk : k ∈ K) {n : ℕ} (hn : Odd n) (hkn : k ^ n = 1)
    (hinv : θ t * θ ⟨k, hKM hk⟩ * (θ t)⁻¹ = (θ ⟨k, hKM hk⟩)⁻¹) :
    (t : X) * k * (t : X)⁻¹ = k⁻¹ := by
  have hw1 : θ (t * ⟨k, hKM hk⟩ * t⁻¹ * ⟨k, hKM hk⟩) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hinv, inv_mul_cancel]
  have hwC : (t : X) * k * (t : X)⁻¹ * k ∈ Subgroup.centralizer (K : Set X) := by
    have := (hθker _).1 hw1
    simpa using this
  have htK : (t : X) * k * (t : X)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hMN t.2) k).mp hk
  set w : X := (t : X) * k * (t : X)⁻¹ * k with hwdef
  have hwK : w ∈ K := K.mul_mem htK hk
  have hw2 : w ^ 2 = 1 := burnsideA315y_sq_eq_one e hwK hwC
  have heq : (t : X) * k * (t : X)⁻¹ = w * k⁻¹ := by rw [hwdef, mul_inv_cancel_right]
  have h1 : ((t : X) * k * (t : X)⁻¹) ^ n = 1 := by
    rw [conj_pow, hkn, mul_one, mul_inv_cancel]
  have hcomm : Commute w k⁻¹ := (Subgroup.mem_centralizer_iff.mp hwC k⁻¹ (K.inv_mem hk)).symm
  have h2 : w ^ n = 1 := by
    rw [heq, hcomm.mul_pow, inv_pow, hkn, inv_one, mul_one] at h1
    exact h1
  rw [heq, burnsideA315y_eq_one_of_sq_of_odd hn hw2 h2, one_mul]

theorem burnsideA315y_decomp_odd {X : Type} [Group X] [Finite X] {p : ℕ} {K M B : Subgroup X}
    (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M) (hBodd : Odd (Nat.card ↥B))
    (hBKC : ∀ b ∈ B, ∃ k ∈ K, ∃ c ∈ M ⊓ Subgroup.centralizer (K : Set X), b = k * c)
    {b : X} (hb : b ∈ B) :
    ∃ k ∈ K, ∃ c ∈ M ⊓ Subgroup.centralizer (K : Set X), b = k * c ∧
      k ^ Nat.card ↥B = 1 ∧ c ^ Nat.card ↥B = 1 := by
  obtain ⟨k, hk, c, hc, rfl⟩ := hBKC b hb
  set n := Nat.card ↥B with hndef
  have hbn : (k * c) ^ n = 1 := burnsideA315y_pow_card_eq_one hb
  have hkc : Commute k c := Subgroup.mem_centralizer_iff.mp hc.2 k hk
  have hprod : k ^ n * c ^ n = 1 := by rw [← hkc.mul_pow]; exact hbn
  set z := k ^ n with hzdef
  have hzK : z ∈ K := K.pow_mem hk n
  have hcn : c ^ n = z⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hzC : z ∈ Subgroup.centralizer (K : Set X) := by
    have : z = (c ^ n)⁻¹ := by rw [hcn, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc.2 n)
  have hz2 : z ^ 2 = 1 := burnsideA315y_sq_eq_one e hzK hzC
  obtain ⟨j, hj⟩ := hBodd
  have hzn : z ^ n = z := by rw [hj, pow_succ, pow_mul, hz2, one_pow, one_mul]
  refine ⟨k * z, K.mul_mem hk hzK, z * c,
    ⟨M.mul_mem (hKM hzK) hc.1, Subgroup.mul_mem _ hzC hc.2⟩, ?_, ?_, ?_⟩
  · calc k * c = k * (z * z) * c := by rw [← sq, hz2, mul_one]
      _ = k * z * (z * c) := by group
  · have hkz : Commute k z := Commute.self_pow k n
    rw [hkz.mul_pow, hzn, ← sq, hz2]
  · have hzc : Commute z c := Subgroup.mem_centralizer_iff.mp hc.2 z hzK
    rw [hzc.mul_pow, hzn, hcn, mul_inv_cancel]

theorem burnsideA315y_split {X : Type} [Group X] [Finite X] {p : ℕ} {K M B S : Subgroup X}
    (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M) (hMN : M ≤ Subgroup.normalizer (K : Set X))
    (hcent : ∀ c ∈ M ⊓ Subgroup.centralizer (K : Set X), ∀ m ∈ M, c * m = m * c)
    (hBM : B ≤ M) (hBodd : Odd (Nat.card ↥B))
    (hBKC : ∀ b ∈ B, ∃ k ∈ K, ∃ c ∈ M ⊓ Subgroup.centralizer (K : Set X), b = k * c)
    (hS : IsPGroup 2 ↥S) (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X))
    (θ : ↥M →* PGL2 (ZMod p))
    (hθker : ∀ m : ↥M, θ m = 1 ↔ (m : X) ∈ Subgroup.centralizer (K : Set X))
    (t : ↥M) (htS : (t : X) ∈ S)
    (hinv : ∀ (b : X) (hb : b ∈ B), θ t * θ ⟨b, hBM hb⟩ * (θ t)⁻¹ = (θ ⟨b, hBM hb⟩)⁻¹)
    {b : X} (hb : b ∈ B) :
    ∃ k ∈ B ⊓ K, ∃ c ∈ B ⊓ Subgroup.centralizer (K : Set X), b = k * c ∧
      (t : X) * k * (t : X)⁻¹ = k⁻¹ ∧ (t : X) * b * (t : X)⁻¹ ∈ B := by
  obtain ⟨k, hk, c, hc, rfl, hkn, hcn⟩ := burnsideA315y_decomp_odd e hKM hBodd hBKC hb
  have hθc : θ ⟨c, hc.1⟩ = 1 := (hθker _).2 hc.2
  have hθb : θ ⟨k * c, hBM hb⟩ = θ ⟨k, hKM hk⟩ := by
    have : (⟨k * c, hBM hb⟩ : ↥M) = ⟨k, hKM hk⟩ * ⟨c, hc.1⟩ := rfl
    rw [this, map_mul, hθc, mul_one]
  have hinvk : θ t * θ ⟨k, hKM hk⟩ * (θ t)⁻¹ = (θ ⟨k, hKM hk⟩)⁻¹ := by
    rw [← hθb]
    exact hinv _ hb
  have htk : (t : X) * k * (t : X)⁻¹ = k⁻¹ :=
    burnsideA315y_conj_eq_inv e hKM hMN θ hθker t hk hBodd hkn hinvk
  have htc : (t : X) * c * (t : X)⁻¹ = c := by
    have := hcent c hc t t.2
    rw [← this, mul_inv_cancel_right]
  have htb : (t : X) * (k * c) * (t : X)⁻¹ = k⁻¹ * c := by
    calc (t : X) * (k * c) * (t : X)⁻¹ =
        ((t : X) * k * (t : X)⁻¹) * ((t : X) * c * (t : X)⁻¹) := by group
      _ = k⁻¹ * c := by rw [htk, htc]
  have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc.2 k hk
  have hc2 : c ^ 2 = (t : X) * (k * c) * (t : X)⁻¹ * (k * c) := by
    rw [htb]
    calc c ^ 2 = k⁻¹ * (k * c) * c := by rw [sq]; group
      _ = k⁻¹ * (c * k) * c := by rw [hkc]
      _ = k⁻¹ * c * (k * c) := by group
  have hBS : B ≤ B ⊔ S := le_sup_left
  have hSBS : S ≤ B ⊔ S := le_sup_right
  have hc2mem : c ^ 2 ∈ B ⊔ S := by
    rw [hc2]
    exact (B ⊔ S).mul_mem ((B ⊔ S).mul_mem ((B ⊔ S).mul_mem (hSBS htS) (hBS hb))
      ((B ⊔ S).inv_mem (hSBS htS))) (hBS hb)
  have hcmem : c ∈ B ⊔ S := by
    obtain ⟨j, hj⟩ := hBodd
    have : c = (c ^ 2) ^ (j + 1) := by
      rw [← pow_mul]
      calc c = c ^ Nat.card ↥B * c := by rw [hcn, one_mul]
        _ = c ^ (Nat.card ↥B + 1) := (pow_succ c _).symm
        _ = c ^ (2 * (j + 1)) := by congr 1; omega
    rw [this]
    exact Subgroup.pow_mem _ hc2mem _
  have hZle : Subgroup.zpowers c ≤ B := by
    refine burnsideA315y_le_of_odd hBodd hS hperm ((Subgroup.zpowers_le).2 hcmem) ?_ ?_
    · rw [Subgroup.le_normalizer_iff]
      intro h hh x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hch : Commute c h := hcent c hc h (hBM hh)
      have : h * c ^ j * h⁻¹ = c ^ j := by
        rw [← ((hch.zpow_left j).eq), mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers c j
    · rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hBodd (orderOf_dvd_of_pow_eq_one hcn)
  have hcB : c ∈ B := hZle (Subgroup.mem_zpowers c)
  have hkB : k ∈ B := by
    have : k = (k * c) * c⁻¹ := by group
    rw [this]
    exact B.mul_mem hb (B.inv_mem hcB)
  refine ⟨k, ⟨hkB, hk⟩, c, ⟨hcB, hc.2⟩, rfl, htk, ?_⟩
  rw [htb]
  exact B.mul_mem (B.inv_mem hkB) hcB

theorem burnsideA315y_mem_normalizer {X : Type} [Group X] [Finite X] {B : Subgroup X} {t : X}
    (h : ∀ b ∈ B, t * b * t⁻¹ ∈ B) : t ∈ Subgroup.normalizer (B : Set X) := by
  have hle : B.map (MulAut.conj t).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have heq : B.map (MulAut.conj t).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  have : b = x := by simpa [MulAut.conj_apply] using hbx
  exact this ▸ hb

theorem burnsideA315y_card_image {X : Type} [Group X] [Finite X] {p : ℕ} {K M S : Subgroup X}
    (θ : ↥M →* PGL2 (ZMod p))
    (hθker : ∀ m : ↥M, θ m = 1 ↔ (m : X) ∈ Subgroup.centralizer (K : Set X)) (hSM : S ≤ M) :
    Nat.card ↥((S.subgroupOf M).map θ) * Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set X)) =
      Nat.card ↥S := by
  have h1 := Subgroup.relIndex_ker θ (K := S.subgroupOf M)
  have h2 := Subgroup.relIndex_mul_card θ.ker (S.subgroupOf M)
  have h3 : θ.ker ⊓ S.subgroupOf M = (S ⊓ Subgroup.centralizer (K : Set X)).subgroupOf M := by
    ext m
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, hθker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact and_comm
  have h4 : Nat.card ↥((S ⊓ Subgroup.centralizer (K : Set X)).subgroupOf M) =
      Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hSM)).toEquiv
  have h5 : Nat.card ↥(S.subgroupOf M) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  rw [h3, h4, h5, h1] at h2
  exact h2

theorem burnsideA315y_lift_sylow {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {K M S : Subgroup X} (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (θ : ↥M →* PGL2 (ZMod p))
    (hθK : ∀ (k : X) (hk : k ∈ K), θ ⟨k, hKM hk⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (e ⟨k, hk⟩)))
    (hSM : S ≤ M) (hS : IsPGroup 2 ↥S)
    (hSK : Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card ↥K).factorization 2)
    {d : PGL2 (ZMod p)} (hdD : d ∈ (S.subgroupOf M).map θ)
    (hdR : d ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range) :
    ∃ t : ↥M, (t : X) ∈ S ⊓ K ∧ θ t = d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set fK : ↥K →* PGL2 (ZMod p) := θ.comp (Subgroup.inclusion hKM) with hfKdef
  have hfK : ∀ k : ↥K, fK k =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (e k)) := fun k => hθK k k.2
  have hrange : fK.range =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range := by
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk (e k), (hfK k).symm⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨e.symm x, by rw [hfK, MulEquiv.apply_symm_apply]⟩
  have hPcard : Nat.card ↥((S ⊓ K).subgroupOf K) = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [← hSK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  let P : Sylow 2 ↥K := Sylow.ofCard _ hPcard
  let Q : Sylow 2 ↥fK.range := P.mapSurjective fK.rangeRestrict_surjective
  set D : Subgroup (PGL2 (ZMod p)) := (S.subgroupOf M).map θ with hDdef
  have hD : IsPGroup 2 ↥D := (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm).map θ
  have hQD : (Q : Subgroup ↥fK.range) ≤ D.subgroupOf fK.range := by
    intro y hy
    rw [Sylow.coe_mapSurjective] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : (x : X) ∈ S ⊓ K := by
      have : x ∈ (S ⊓ K).subgroupOf K := by
        rwa [Sylow.coe_ofCard] at hx
      exact this
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨(x : X), hKM x.2⟩, hx'.1, rfl⟩
  have hDeq : D.subgroupOf fK.range = (Q : Subgroup ↥fK.range) :=
    Q.is_maximal' hD.comap_subtype hQD
  have hdF : d ∈ fK.range := hrange ▸ hdR
  have hdQ : (⟨d, hdF⟩ : ↥fK.range) ∈ (Q : Subgroup ↥fK.range) := by
    rw [← hDeq, Subgroup.mem_subgroupOf]
    exact hdD
  rw [Sylow.coe_mapSurjective] at hdQ
  obtain ⟨x, hx, hxd⟩ := hdQ
  have hx' : (x : X) ∈ S ⊓ K := by
    have : x ∈ (S ⊓ K).subgroupOf K := by
      rwa [Sylow.coe_ofCard] at hx
    exact this
  refine ⟨⟨(x : X), hKM x.2⟩, hx', ?_⟩
  have := congrArg Subtype.val hxd
  exact this

theorem burnsideA315y_key {X : Type} [Group X] [Finite X] {p : ℕ} {K M B S : Subgroup X}
    (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M) (hMN : M ≤ Subgroup.normalizer (K : Set X))
    (hcent : ∀ c ∈ M ⊓ Subgroup.centralizer (K : Set X), ∀ m ∈ M, c * m = m * c)
    (hBM : B ≤ M) (hBodd : Odd (Nat.card ↥B))
    (hBKC : ∀ b ∈ B, ∃ k ∈ K, ∃ c ∈ M ⊓ Subgroup.centralizer (K : Set X), b = k * c)
    (hS : IsPGroup 2 ↥S) (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X))
    (θ : ↥M →* PGL2 (ZMod p))
    (hθker : ∀ m : ↥M, θ m = 1 ↔ (m : X) ∈ Subgroup.centralizer (K : Set X))
    (t : ↥M) (htS : (t : X) ∈ S)
    (hinv : ∀ x ∈ (B.subgroupOf M).map θ, θ t * x * (θ t)⁻¹ = x⁻¹) :
    B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) ∧
      Nonempty (↥(B ⊓ K) ≃* ↥((B.subgroupOf M).map θ)) ∧
      (t : X) ∈ Subgroup.normalizer (B : Set X) ∧
      ∀ x ∈ B ⊓ K, (t : X) * x * (t : X)⁻¹ = x⁻¹ := by
  have hinv' : ∀ (b : X) (hb : b ∈ B), θ t * θ ⟨b, hBM hb⟩ * (θ t)⁻¹ = (θ ⟨b, hBM hb⟩)⁻¹ :=
    fun b hb => hinv _ ⟨⟨b, hBM hb⟩, hb, rfl⟩
  have hsplit := fun {b : X} (hb : b ∈ B) =>
    burnsideA315y_split e hKM hMN hcent hBM hBodd hBKC hS hperm θ hθker t htS hinv' hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro b hb
      obtain ⟨k, hk, c, hc, rfl, -, -⟩ := hsplit hb
      exact Subgroup.mul_mem_sup hk hc
    · exact sup_le inf_le_left inf_le_left
  · have hle : B ⊓ K ≤ M := inf_le_right.trans hKM
    set f : ↥(B ⊓ K) →* PGL2 (ZMod p) := θ.comp (Subgroup.inclusion hle) with hfdef
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxC : (x : X) ∈ Subgroup.centralizer (K : Set X) := (hθker _).1 hx
      have h2 : (x : X) ^ 2 = 1 := burnsideA315y_sq_eq_one e x.2.2 hxC
      have hn : (x : X) ^ Nat.card ↥B = 1 := burnsideA315y_pow_card_eq_one x.2.1
      apply Subtype.ext
      exact burnsideA315y_eq_one_of_sq_of_odd hBodd h2 hn
    have hrange : f.range = (B.subgroupOf M).map θ := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact ⟨Subgroup.inclusion hle x, x.2.1, rfl⟩
      · rintro _ ⟨m, hm, rfl⟩
        obtain ⟨k, hk, c, hc, hmkc, -, -⟩ := hsplit (Subgroup.mem_subgroupOf.mp hm)
        refine ⟨⟨k, hk⟩, ?_⟩
        have hm' : m = ⟨k, hKM hk.2⟩ * ⟨c, hBM hc.1⟩ := Subtype.ext hmkc
        rw [hm', map_mul, (hθker ⟨c, hBM hc.1⟩).2 hc.2, mul_one]
        rfl
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩
  · refine burnsideA315y_mem_normalizer fun b hb => ?_
    obtain ⟨-, -, -, -, -, -, h⟩ := hsplit hb
    exact h
  · intro x hx
    have hn : x ^ Nat.card ↥B = 1 := burnsideA315y_pow_card_eq_one hx.1
    exact burnsideA315y_conj_eq_inv e hKM hMN θ hθker t hx.2 hBodd hn (hinv' x hx.1)

theorem burnsideA315y_steps (hPGL2 : burnsideA315y_PGL2Statement) :
    burnsideA315y_StepsStatement := by
  intro X _ _ p _ hp2 K M B S ⟨e⟩ hKM hMN hcent hBM hBab hBodd hBKC hSM hS hperm hSK hScard
  obtain ⟨θ, hθK, hθker⟩ := burnsideA315y_exists_theta hp2 e hKM hMN
  set Bθ : Subgroup (PGL2 (ZMod p)) := (B.subgroupOf M).map θ with hBθdef
  set D : Subgroup (PGL2 (ZMod p)) := (S.subgroupOf M).map θ with hDdef
  have hBθab : IsMulCommutative ↥Bθ := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    change (x : PGL2 (ZMod p)) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := congrArg Subtype.val (hBab.is_comm.comm (⟨(a : X), ha⟩ : ↥B) ⟨(b : X), hb⟩)
    simpa using this
  have hBθodd : Odd (Nat.card ↥Bθ) := by
    refine Odd.of_dvd_nat hBodd ?_
    have h := Subgroup.card_map_dvd (B.subgroupOf M) θ
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv] at h
  have hD2 : IsPGroup 2 ↥D := (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm).map θ
  have hDcard : Nat.card ↥D = 2 ^ (Nat.card (PGL2 (ZMod p))).factorization 2 := by
    have h := burnsideA315y_card_image θ hθker hSM (K := K)
    rw [hScard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hBDperm : (Bθ : Set (PGL2 (ZMod p))) * (D : Set (PGL2 (ZMod p))) =
      (D : Set (PGL2 (ZMod p))) * (Bθ : Set (PGL2 (ZMod p))) := by
    have h := burnsideA315x_subgroupOf_permute (K := S) hBM hperm
    rw [inf_of_le_left hSM] at h
    exact burnsideA315x_map_permute θ h
  obtain ⟨hcyc, hcase⟩ := hPGL2 p hp2 Bθ D hBθab hBθodd hD2 hDcard hBDperm
  rcases hcase with ⟨hε, d, hdD, hdR, hdinv⟩ | ⟨hp8, hB3, d, hdD, hdinv⟩
  · obtain ⟨t, htSK, rfl⟩ := burnsideA315y_lift_sylow e hKM θ hθK hSM hS hSK hdD hdR
    obtain ⟨h1, ⟨eBK⟩, -, h4⟩ :=
      burnsideA315y_key e hKM hMN hcent hBM hBodd hBKC hS hperm θ hθker t htSK.1 hdinv
    refine ⟨h1, isCyclic_of_surjective eBK.symm.toMonoidHom eBK.symm.surjective,
      Or.inl ⟨?_, (t : X), htSK, h4⟩⟩
    rw [Nat.card_congr eBK.toEquiv]
    exact hε
  · obtain ⟨s, hs, rfl⟩ := hdD
    obtain ⟨h1, ⟨eBK⟩, h3, h4⟩ :=
      burnsideA315y_key e hKM hMN hcent hBM hBodd hBKC hS hperm θ hθker s hs hdinv
    refine ⟨h1, isCyclic_of_surjective eBK.symm.toMonoidHom eBK.symm.surjective,
      Or.inr ⟨hp8, ?_, (s : X), ⟨hs, h3⟩, h4⟩⟩
    rw [Nat.card_congr eBK.toEquiv]
    exact hB3

end CFSG.ASVolI
