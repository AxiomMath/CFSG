module

public import CFSG.Milestones.ASVolI.A3L3.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Dickson
public import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.ASVolI

open CFSG.GorensteinWalter
open scoped Pointwise

theorem burnsideA315y_isSylowTwoOf_of_card {W : Type*} [Group W] [Finite W] {S : Subgroup W}
    (h : Nat.card ↥S = 2 ^ (Nat.card W).factorization 2) :
    CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 W := Sylow.ofCard S h
  refine ⟨le_top, P.isPGroup', ?_⟩
  have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [h1]
  exact P.not_dvd_index

theorem burnsideA315y_card_sup {X : Type*} [Group X] [Finite X] {S B : Subgroup X}
    (hodd : Odd (Nat.card ↥B)) (hS : IsPGroup 2 ↥S)
    (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) :
    Nat.card ↥(B ⊔ S) = Nat.card ↥B * Nat.card ↥S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdB : Nat.card ↥(B ⊓ S) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_left
  have hdS : Nat.card ↥(B ⊓ S) ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card ↥B) (2 ^ k) :=
    (Nat.coprime_two_left.2 hodd).symm.pow_right k
  have h1 : Nat.card ↥(B ⊓ S) ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdB hdS
  have hbot : B ⊓ S = ⊥ := Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
  exact burnsideA315x_card_sup hperm hbot

theorem burnsideA315y_comap_permute {G' G : Type*} [Group G'] [Group G] (f : G' →* G)
    {H K : Subgroup G} (hH : H ≤ f.range) (h : (H : Set G) * K = K * H) :
    ((H.comap f : Subgroup G') : Set G') * (K.comap f : Subgroup G') =
      (K.comap f : Subgroup G') * (H.comap f : Subgroup G') := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hab : f a * f b ∈ (K : Set G) * H := by
      rw [← h]
      exact Set.mul_mem_mul ha hb
    obtain ⟨k, hk, y, hy, hky⟩ := hab
    obtain ⟨y₀, rfl⟩ := hH hy
    refine ⟨a * b * y₀⁻¹, ?_, y₀, hy, by group⟩
    show f (a * b * y₀⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv, ← hky]
    simpa using hk
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hab : f a * f b ∈ (H : Set G) * K := by
      rw [h]
      exact Set.mul_mem_mul ha hb
    obtain ⟨y, hy, k, hk, hyk⟩ := hab
    obtain ⟨y₀, rfl⟩ := hH hy
    have hyk' : f y₀ * k = f a * f b := hyk
    refine ⟨y₀, hy, y₀⁻¹ * (a * b), ?_, by group⟩
    show f (y₀⁻¹ * (a * b)) ∈ K
    rw [map_mul, map_mul, map_inv, ← hyk']
    simpa using hk

theorem burnsideA315y_card_comap {G' G : Type} [Group G'] [Group G] {f : G' →* G}
    (hf : Function.Injective f) {H : Subgroup G} (hH : H ≤ f.range) :
    Nat.card ↥(H.comap f) = Nat.card ↥H := by
  rw [← Subgroup.card_map_of_injective (K := H.comap f) hf, Subgroup.map_comap_eq_self hH]

theorem burnsideA315y_cyclic_comap {G' G : Type} [Group G'] [Group G] {f : G' →* G}
    (hf : Function.Injective f) {H : Subgroup G} (hH : IsCyclic ↥H) : IsCyclic ↥(H.comap f) := by
  have h1 : IsCyclic ↥((H.comap f).map f) :=
    burnsideA315x_cyclic_of_le (Subgroup.map_comap_le f H) hH
  exact isCyclic_of_surjective ((H.comap f).equivMapOfInjective f hf).symm.toMonoidHom
    ((H.comap f).equivMapOfInjective f hf).symm.surjective

theorem burnsideA315y_inv_of_conj {Y : Type*} [Group Y] {B D : Subgroup Y}
    (hperm : (B : Set Y) * D = D * B) (hBab : IsMulCommutative ↥B) {β : Y} (hβ : β ∈ B)
    (hgen : ∀ x ∈ B, ∃ k : ℤ, β ^ k = x) {y : Y} (hy : y ∈ B ⊔ D)
    (hyβ : y * β * y⁻¹ = β⁻¹) :
    ∃ d ∈ D, ∀ x ∈ B, d * x * d⁻¹ = x⁻¹ := by
  have hy' : y ∈ (B : Set Y) * D := by
    rw [← burnsideA315x_coe_sup hperm]
    exact hy
  obtain ⟨b, hb, d, hd, rfl⟩ := hy'
  refine ⟨d, hd, fun x hx => ?_⟩
  have hc : b * β⁻¹ = β⁻¹ * b :=
    congrArg Subtype.val (hBab.is_comm.comm ⟨b, hb⟩ ⟨β⁻¹, B.inv_mem hβ⟩)
  have hdβ : d * β * d⁻¹ = β⁻¹ := by
    have h1 : d * β * d⁻¹ = b⁻¹ * (b * d * β * (b * d)⁻¹) * b := by group
    rw [h1, hyβ]
    calc b⁻¹ * β⁻¹ * b = b⁻¹ * (β⁻¹ * b) := by group
      _ = b⁻¹ * (b * β⁻¹) := by rw [hc]
      _ = β⁻¹ := by group
  obtain ⟨k, rfl⟩ := hgen x hx
  rw [← conj_zpow, hdβ, inv_zpow]

theorem burnsideA315y_perm4_conj_inv : ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 →
    ∃ τ : Equiv.Perm (Fin 4), τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

theorem burnsideA315y_perm4_not_normal : ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ τ : Equiv.Perm (Fin 4), τ * σ * τ⁻¹ ≠ σ ∧ τ * σ * τ⁻¹ ≠ σ⁻¹ := by
  decide +kernel

theorem burnsideA315y_conj_inv_of_perm4 {W : Type*} [Group W] (e : W ≃* Equiv.Perm (Fin 4))
    {x : W} (hx : x ^ 3 = 1) : ∃ w : W, w * x * w⁻¹ = x⁻¹ := by
  obtain ⟨τ, hτ⟩ := burnsideA315y_perm4_conj_inv (e x) (by rw [← map_pow, hx, map_one])
  refine ⟨e.symm τ, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply, hτ]

theorem burnsideA315y_not_normal_of_perm4 {W : Type*} [Group W] (e : W ≃* Equiv.Perm (Fin 4))
    {x : W} (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ w : W, w * x * w⁻¹ ≠ x ∧ w * x * w⁻¹ ≠ x⁻¹ := by
  obtain ⟨τ, hτ1, hτ2⟩ := burnsideA315y_perm4_not_normal (e x) (by rw [← map_pow, hx, map_one])
    (by rwa [ne_eq, map_eq_one_iff e e.injective])
  refine ⟨e.symm τ, fun h => hτ1 ?_, fun h => hτ2 ?_⟩
  · have h' := congrArg e h
    rwa [map_mul, map_mul, map_inv, e.apply_symm_apply] at h'
  · have h' := congrArg e h
    rwa [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply] at h'

theorem burnsideA315y_dihedral_rot {z : ℕ} {x : DihedralGroup z} (hx : Odd (orderOf x)) :
    ∃ i : ZMod z, x = DihedralGroup.r i := by
  rcases x with i | i
  · exact ⟨i, rfl⟩
  · exfalso
    rw [DihedralGroup.orderOf_sr] at hx
    exact absurd hx (by decide)

theorem burnsideA315y_dihedral_conj_rot {z : ℕ} (i : ZMod z) :
    DihedralGroup.sr 0 * DihedralGroup.r i * (DihedralGroup.sr 0)⁻¹ = (DihedralGroup.r i)⁻¹ ∧
    ∀ g : DihedralGroup z, g * DihedralGroup.r i * g⁻¹ = DihedralGroup.r i ∨
      g * DihedralGroup.r i * g⁻¹ = (DihedralGroup.r i)⁻¹ := by
  refine ⟨?_, fun g => ?_⟩
  · rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r]
    congr 1
    ring
  · rcases g with j | j
    · left
      rw [DihedralGroup.inv_r, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
      congr 1
      ring
    · right
      rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring

theorem burnsideA315y_conj_of_dihedral {W : Type*} [Group W] {z : ℕ} (e : W ≃* DihedralGroup z)
    {x : W} (hx : Odd (orderOf x)) :
    (∃ w : W, w * x * w⁻¹ = x⁻¹) ∧ ∀ w : W, w * x * w⁻¹ = x ∨ w * x * w⁻¹ = x⁻¹ := by
  have hx' : Odd (orderOf (e x)) := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨i, hi⟩ := burnsideA315y_dihedral_rot hx'
  obtain ⟨h1, h2⟩ := burnsideA315y_dihedral_conj_rot i
  refine ⟨⟨e.symm (DihedralGroup.sr 0), e.injective ?_⟩, fun w => ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply, hi, h1]
  · rcases h2 (e w) with h | h
    · left
      apply e.injective
      rw [map_mul, map_mul, map_inv, hi, h]
    · right
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, hi, h]

theorem burnsideA315y_isSquare_galois_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a : ZMod p) :
    IsSquare (algebraMap (ZMod p) (GaloisField p 2) a) := by
  by_cases ha : a = 0
  · subst ha
    rw [map_zero]
    exact ⟨0, by ring⟩
  · letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
    have hchar : ringChar (GaloisField p 2) ≠ 2 := by
      rw [ringChar.eq (GaloisField p 2) p]
      exact hp2
    have hne : algebraMap (ZMod p) (GaloisField p 2) a ≠ 0 := by
      intro h
      apply ha
      exact (algebraMap (ZMod p) (GaloisField p 2)).injective (by rw [h, map_zero])
    rw [FiniteField.isSquare_iff hchar hne]
    have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p 2 (by norm_num)
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    have h2 : p ^ 2 / 2 = (p - 1) * (k + 1) := by
      have h1 : p ^ 2 = 2 * ((p - 1) * (k + 1)) + 1 := by
        subst hk
        rw [Nat.add_sub_cancel]
        ring
      rw [h1]
      generalize (p - 1) * (k + 1) = X
      omega
    rw [hcard, h2, ← map_pow, pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow, map_one]

theorem burnsideA315y_pglMap_mem {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (g : PGL2 (ZMod p)) :
    CFSG.Glauberman.Dickson.h826_pglMap (algebraMap (ZMod p) (GaloisField p 2)) g ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p 2)).range := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [CFSG.Glauberman.Dickson.h826_pglMap_mk,
    CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have h : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap (ZMod p) (GaloisField p 2)) A) :
        (GaloisField p 2)ˣ) : GaloisField p 2) =
      algebraMap (ZMod p) (GaloisField p 2) ((Matrix.GeneralLinearGroup.det A : (ZMod p)ˣ) :
        ZMod p) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      RingHom.map_det]
    rfl
  rw [h]
  exact burnsideA315y_isSquare_galois_two hp2 _

theorem burnsideA315y_exists_embedding {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    ∃ ε : PGL2 (ZMod p) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2),
      Function.Injective ε := by
  set φ := CFSG.Glauberman.Dickson.h826_pglMap (algebraMap (ZMod p) (GaloisField p 2)) with hφ
  have hφi : Function.Injective φ :=
    CFSG.Glauberman.Dickson.h826_pglMap_injective _
      (algebraMap (ZMod p) (GaloisField p 2)).injective
  let e := MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := GaloisField p 2))
  refine ⟨e.symm.toMonoidHom.comp (φ.codRestrict _ (burnsideA315y_pglMap_mem hp2)), ?_⟩
  intro a b hab
  apply hφi
  have h := congrArg Subtype.val (e.symm.injective hab)
  simpa using h

theorem burnsideA315y_eq_three_of_dvd {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 3 * 2 ^ j) : p = 3 := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2

theorem burnsideA315y_dickson_sq {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    {W T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))}
    (hTW : T ≤ W) (hTnc : ¬ IsCyclic ↥T) {k : ℕ} (hTk : Nat.card ↥T = 2 ^ k)
    (hW : Nat.card ↥W = 3 * 2 ^ k) (hk : k = 3 ∨ k = 4) :
    (∃ z : ℕ, Nonempty (↥W ≃* DihedralGroup z)) ∨
      (k = 3 ∧ Nonempty (↥W ≃* Equiv.Perm (Fin 4))) := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds p 2 (by norm_num) W with
    ⟨-, m', -, hcard'⟩ | ⟨hcyc, -⟩ | ⟨z, -, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ |
      ⟨m', t, P, hP, -, hPc, hQc, -, -, -⟩ | ⟨m', hm', ⟨e'⟩⟩ | ⟨m', hm', ⟨e'⟩⟩
  · exfalso
    have h2 : 2 ∣ Nat.card ↥W := by
      rw [hW]
      exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) 3
    rw [hcard'] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  · exact (hTnc (burnsideA315x_cyclic_of_le hTW hcyc)).elim
  · exact Or.inl ⟨z, ⟨e'⟩⟩
  · exfalso
    have h := Nat.card_congr e'.toEquiv
    rw [hW, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h
    rcases hk with rfl | rfl <;> revert h <;> decide
  · have h := Nat.card_congr e'.toEquiv
    rw [hW, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
    rcases hk with rfl | rfl
    · exact Or.inr ⟨rfl, ⟨e'⟩⟩
    · exfalso
      revert h
      decide
  · exfalso
    have h := Nat.card_congr e'.toEquiv
    rw [hW, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h
    rcases hk with rfl | rfl <;> revert h <;> decide
  · exfalso
    haveI := hP
    exact burnsideA315x_case_ext hTW hp hp2 hTk hTnc P hPc hQc
  · exfalso
    have hm0 : m' ≠ 0 := by
      rintro rfl
      norm_num at hm'
    have hK : Nat.card (GaloisField p m') = p ^ m' := GaloisField.card p m' hm0
    have hodd : IsOddPrimePower (Nat.card (GaloisField p m')) :=
      ⟨p, m', hp, hpodd, Nat.pos_of_ne_zero hm0, hK⟩
    have hc := psl2_card_formula (GaloisField p m') hodd
    have h := Nat.card_congr e'.toEquiv
    rw [hW] at h
    change 3 * 2 ^ k = Nat.card (PSL2 (GaloisField p m')) at h
    rw [hc, hK] at h
    have heven : 2 ∣ p ^ m' * ((p ^ m') ^ 2 - 1) := by
      have h1 : Odd ((p ^ m') ^ 2) := (hpodd.pow).pow
      have h2 : Even ((p ^ m') ^ 2 - 1) := Nat.Odd.sub_odd h1 odd_one
      exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h2) _
    have h2 : p ^ m' * ((p ^ m') ^ 2 - 1) = 3 * 2 ^ (k + 1) := by
      rw [pow_succ 2 k, ← mul_assoc, h, Nat.div_mul_cancel heven]
    have hpd : p ∣ 3 * 2 ^ (k + 1) := h2 ▸ Dvd.dvd.mul_right (dvd_pow_self p hm0) _
    have hp3 := burnsideA315y_eq_three_of_dvd hp hp2 hpd
    subst hp3
    have hm2 : m' ≤ 2 := Nat.le_of_dvd (by norm_num) hm'
    interval_cases m' <;> rcases hk with rfl | rfl <;> revert h2 <;> decide
  · have hm1 : m' = 1 := by
      have h1 := Nat.le_of_dvd (by norm_num) hm'
      have h2 : m' ≠ 0 := by
        rintro rfl
        norm_num at hm'
      omega
    subst hm1
    have hK : Nat.card (GaloisField p 1) = p := by
      rw [GaloisField.card p 1 (by norm_num), pow_one]
    have hc := pgl2_card_formula (GaloisField p 1)
    have h := Nat.card_congr e'.toEquiv
    rw [hW] at h
    change 3 * 2 ^ k = Nat.card (PGL2 (GaloisField p 1)) at h
    rw [hc, hK] at h
    have hpd : p ∣ 3 * 2 ^ k := h ▸ Dvd.intro _ rfl
    have hp3 := burnsideA315y_eq_three_of_dvd hp hp2 hpd
    subst hp3
    rcases hk with rfl | rfl
    · obtain ⟨e3⟩ :=
        CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.nonempty_pgl2_galoisField_three
      exact Or.inr ⟨rfl, ⟨e'.trans e3⟩⟩
    · exfalso
      revert h
      decide

theorem burnsideA315y_case_dihedral {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hodd : Odd (Nat.card ↥B)) (hcard : Nat.card ↥(B ⊔ S) = Nat.card ↥B * Nat.card ↥S)
    {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (hSnc : ¬ IsCyclic ↥S) {z : ℕ} (e : ↥(B ⊔ S) ≃* DihedralGroup z) :
    IsCyclic ↥B ∧ Nat.card ↥B ∣ z ∧ 2 ∣ z ∧ ∃ s ∈ S, ∀ x ∈ B, s * x * s⁻¹ = x⁻¹ := by
  have hle : S ≤ B ⊔ S := le_sup_right
  have hHz : Nat.card ↥(B ⊔ S) = 2 * z := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hHz
    exact (Nat.card_pos (α := ↥(B ⊔ S))).ne' hHz
  haveI : NeZero z := ⟨hz0⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hz : z = Nat.card ↥B * 2 ^ (k' + 1) := by
    have h1 : 2 * z = 2 * (Nat.card ↥B * 2 ^ (k' + 1)) := by
      rw [← hHz, hcard, hSk]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hrot : ∀ y : ↥(B ⊔ S), Odd (orderOf y) → ∃ i : ZMod z, e y = DihedralGroup.r i := by
    intro y hy
    rcases hey : e y with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h2 : orderOf (e y) = orderOf y := MulEquiv.orderOf_eq e y
      rw [hey, DihedralGroup.orderOf_sr] at h2
      rw [← h2] at hy
      exact absurd hy (by decide)
  have hBrot : ∀ t : X, ∀ ht : t ∈ B, ∃ i : ZMod z,
      e ⟨t, (le_sup_left : B ≤ B ⊔ S) ht⟩ = DihedralGroup.r i := by
    intro t ht
    refine hrot _ ?_
    have h1 : orderOf (⟨t, ht⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    have h2 : orderOf (⟨t, (le_sup_left : B ≤ B ⊔ S) ht⟩ : ↥(B ⊔ S)) =
        orderOf (⟨t, ht⟩ : ↥B) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [h2]
    exact Odd.of_dvd_nat hodd h1
  refine ⟨burnsideA315x_rot_cyclic e B le_sup_left hBrot, ⟨2 ^ (k' + 1), hz⟩, ?_, ?_⟩
  · rw [hz]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  · have hrefl : ∃ s : X, ∃ hs : s ∈ S, ∃ j : ZMod z, e ⟨s, hle hs⟩ = DihedralGroup.sr j := by
      by_contra hno
      push Not at hno
      apply hSnc
      refine burnsideA315x_rot_cyclic e S hle ?_
      intro t ht
      rcases hey : e ⟨t, hle ht⟩ with i | i
      · exact ⟨i, rfl⟩
      · exact absurd hey (hno t ht i)
    obtain ⟨s, hs, j, hsj⟩ := hrefl
    refine ⟨s, hs, fun b hb => ?_⟩
    obtain ⟨i, hi⟩ := hBrot b hb
    have key : (⟨s, hle hs⟩ : ↥(B ⊔ S)) * ⟨b, (le_sup_left : B ≤ B ⊔ S) hb⟩ * ⟨s, hle hs⟩⁻¹ =
        ⟨b, (le_sup_left : B ≤ B ⊔ S) hb⟩⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, hsj, hi, DihedralGroup.inv_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
    have := congrArg Subtype.val key
    simpa using this

theorem burnsideA315y_eps_of_dihedral {q z N : ℕ} (hq : Odd q)
    (hz : z ∣ (q + 1) / Nat.gcd 2 (q - 1) ∨ z ∣ (q - 1) / Nat.gcd 2 (q - 1))
    (h2z : 2 ∣ z) (hNz : N ∣ z) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (q : ℤ) ∧ (N : ℤ) ∣ (q : ℤ) - ε := by
  obtain ⟨t, ht⟩ := hq
  have hg : Nat.gcd 2 (q - 1) = 2 := by
    rw [ht, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (Dvd.intro t rfl)
  rw [hg] at hz
  obtain ⟨z', hz'⟩ := h2z
  rcases hz with ⟨c, hc'⟩ | ⟨c, hc'⟩
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · have h4 : (q + 1) = 4 * (z' * c) := by
        have : (q + 1) = 2 * ((q + 1) / 2) := by omega
        rw [this, hc', hz']
        ring
      rw [Int.ModEq]
      omega
    · have hdvd : N ∣ q + 1 := by
        refine hNz.trans ⟨2 * c, ?_⟩
        have : (q + 1) = 2 * ((q + 1) / 2) := by omega
        rw [this, hc']
        ring
      have := Int.natCast_dvd_natCast.2 hdvd
      push_cast at this ⊢
      simpa using this
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · have h4 : (q - 1) = 4 * (z' * c) := by
        have : (q - 1) = 2 * ((q - 1) / 2) := by omega
        rw [this, hc', hz']
        ring
      rw [Int.ModEq]
      omega
    · have hdvd : N ∣ q - 1 := by
        refine hNz.trans ⟨2 * c, ?_⟩
        have : (q - 1) = 2 * ((q - 1) / 2) := by omega
        rw [this, hc']
        ring
      have h1 : 1 ≤ q := by omega
      have := Int.natCast_dvd_natCast.2 hdvd
      push_cast [Nat.cast_sub h1] at this ⊢
      exact this

theorem burnsideA315y_l2_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {S B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1))}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hB3 : IsPGroup 3 ↥B)
    (hperm : (B : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1))) *
      (S : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1))) =
      (S : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1))) * (B : Set _)) :
    (IsCyclic ↥B ∧ (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
        ((Nat.card ↥B : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧ ∃ s ∈ S, ∀ x ∈ B, s * x * s⁻¹ = x⁻¹) ∨
      (Nat.card ↥B = 3 ∧ Nat.card ↥S = 4) ∨
      (Nat.card ↥B = 3 ∧ Nat.card ↥S = 8 ∧ Nonempty (↥(B ⊔ S) ≃* Equiv.Perm (Fin 4))) := by
  have hp : p.Prime := Fact.out
  have hq : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 (by norm_num)
  obtain ⟨⟨m, hm, hSc⟩, hSnc⟩ :=
    burnsideA315x_sylow_facts (F := GaloisField p 1) hp hp2 le_rfl hq hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hB3.exists_card_eq
  have hodd : Odd (Nat.card ↥B) := by
    rw [hj]
    exact Odd.pow (by decide)
  have hcard0 := burnsideA315y_card_sup hodd hS.2.1 hperm
  have hcard : Nat.card ↥(B ⊔ S) = Nat.card ↥B * 2 ^ (m + 1) := by rw [hcard0, hSc]
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds p 1 le_rfl (B ⊔ S) with
    ⟨-, m', -, hcard'⟩ | ⟨hcyc, -⟩ | ⟨z, hz, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ |
      ⟨m', t, P, hP, -, hPc, hQc, -, -, -⟩ | ⟨m', hm', ⟨e'⟩⟩ | ⟨m', hm', ⟨e'⟩⟩
  · exfalso
    have hSH : 2 ∣ Nat.card ↥(B ⊔ S) := by
      rw [hcard]
      exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
    rw [hcard'] at hSH
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow hSH)).symm
  · exact (burnsideA315x_case_cyclic hSnc hcyc).elim
  · left
    obtain ⟨hBcyc, hBdvd, h2z, s, hs, hinv⟩ :=
      burnsideA315y_case_dihedral hodd hcard0 (k := m + 1) (by omega) hSc hSnc e'
    rw [pow_one] at hz
    exact ⟨hBcyc, burnsideA315y_eps_of_dihedral hpodd hz h2z hBdvd, s, hs, hinv⟩
  ·
    right
    left
    have h12 : Nat.card ↥(B ⊔ S) = 12 := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have hb : Nat.card ↥B * 2 ^ (m + 1) = 12 := by rw [← hcard, h12]
    have hm3 : m ≤ 2 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    interval_cases m
    · norm_num at hb hSc
      exact ⟨by omega, hSc⟩
    · norm_num at hb
      omega
  ·
    right
    right
    have h24 : Nat.card ↥(B ⊔ S) = 24 := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      decide
    have hb : Nat.card ↥B * 2 ^ (m + 1) = 24 := by rw [← hcard, h24]
    have hm3 : m ≤ 3 := by
      by_contra hcon
      have : 2 ^ 5 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    obtain ⟨u, hu⟩ := hodd
    interval_cases m
    · norm_num at hb
      omega
    · norm_num at hb hSc
      exact ⟨by omega, hSc, ⟨e'⟩⟩
    · norm_num at hb
      omega
  ·
    exfalso
    have h60 : Nat.card ↥(B ⊔ S) = 60 := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have hb : Nat.card ↥B * 2 ^ (m + 1) = 60 := by rw [← hcard, h60]
    have hm3 : m ≤ 4 := by
      by_contra hcon
      have : 2 ^ 6 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    have h15 : Nat.card ↥B = 15 := by
      obtain ⟨u, hu⟩ := hodd
      interval_cases m <;> omega
    have h5 : 5 ∣ 3 ^ j := by
      rw [← hj, h15]
      norm_num
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_three).1
      ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5)
    omega
  · exfalso
    haveI := hP
    exact burnsideA315x_case_ext le_sup_right hp hp2 hSc hSnc P hPc hQc
  ·
    right
    left
    have hm1 : m' = 1 := Nat.dvd_one.1 hm'
    subst hm1
    have hodd' : IsOddPrimePower (Nat.card (GaloisField p 1)) := ⟨p, 1, hp, hpodd, le_rfl, hq⟩
    have hc := psl2_card_formula (GaloisField p 1) hodd'
    have h := Nat.card_congr e'.toEquiv
    change Nat.card ↥(B ⊔ S) = Nat.card (PSL2 (GaloisField p 1)) at h
    rw [hc, hq, pow_one, hcard, hj] at h
    have heven : 2 ∣ p * (p ^ 2 - 1) := by
      have h1 : Odd (p ^ 2) := hpodd.pow
      have h2 : Even (p ^ 2 - 1) := Nat.Odd.sub_odd h1 odd_one
      exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h2) _
    have h2 : p * (p ^ 2 - 1) = 3 ^ j * 2 ^ (m + 2) := by
      rw [pow_succ 2 (m + 1), ← mul_assoc, h, Nat.div_mul_cancel heven]
    have hpd : p ∣ 3 ^ j * 2 ^ (m + 2) := h2 ▸ Dvd.intro _ rfl
    have hp3 : p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h' | h'
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h')
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
          hp2
    subst hp3
    have h24 : 3 ^ j * 2 ^ (m + 2) = 24 := by
      rw [← h2]
      norm_num
    have hm3 : m ≤ 1 := by
      by_contra hcon
      have h16 : 2 ^ 4 ∣ 24 := by
        rw [← h24]
        exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
      norm_num at h16
    have hm1 : m = 1 := by omega
    subst hm1
    norm_num at h24 hSc
    refine ⟨?_, hSc⟩
    rw [hj]
    omega
  · exfalso
    have := Nat.dvd_one.1 hm'
    omega

theorem burnsideA315y_inv_comap {L G : Type} [Group L] [Group G] {ψ : L →* G}
    {B D : Subgroup G} (hB : B ≤ ψ.range) {s : L} (hs : s ∈ D.comap ψ)
    (hinv : ∀ x ∈ B.comap ψ, s * x * s⁻¹ = x⁻¹) :
    ψ s ∈ D ∧ ∀ x ∈ B, ψ s * x * (ψ s)⁻¹ = x⁻¹ := by
  refine ⟨hs, fun x hx => ?_⟩
  obtain ⟨x₀, rfl⟩ := hB hx
  have hx₀ : x₀ ∈ B.comap ψ := hx
  rw [← map_inv, ← map_mul, ← map_mul, hinv x₀ hx₀, map_inv]

theorem burnsideA315y_cyclic_of_comap {L G : Type} [Group L] [Group G] {ψ : L →* G}
    (hψ : Function.Injective ψ) {B : Subgroup G} (hB : B ≤ ψ.range)
    (h : IsCyclic ↥(B.comap ψ)) : IsCyclic ↥B := by
  have h1 : IsCyclic ↥((B.comap ψ).map ψ) :=
    isCyclic_of_surjective ((B.comap ψ).equivMapOfInjective ψ hψ).toMonoidHom
      ((B.comap ψ).equivMapOfInjective ψ hψ).surjective
  rwa [Subgroup.map_comap_eq_self hB] at h1

theorem burnsideA315y_mod_eight {p : ℕ} (hp : Odd p) (h : ¬ 2 ^ 4 ∣ p * (p ^ 2 - 1)) :
    p % 8 = 3 ∨ p % 8 = 5 := by
  have h16 : p % 8 = 1 ∨ p % 8 = 7 → 16 ∣ p ^ 2 - 1 := by
    intro hp8
    have hsq : p ^ 2 % 16 = 1 := by
      have h' : p % 16 = 1 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 15 := by omega
      rw [Nat.pow_mod]
      rcases h' with h' | h' | h' | h' <;> rw [h']
    generalize p ^ 2 = X at hsq ⊢
    omega
  obtain ⟨t, ht⟩ := hp
  by_contra hcon
  have h17 : p % 8 = 1 ∨ p % 8 = 7 := by omega
  exact h (Dvd.dvd.mul_left (by norm_num; exact h16 h17) p)

theorem burnsideA315y_sq_conj {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B D : Subgroup (PGL2 (ZMod p))} (hB3 : Nat.card ↥B = 3) (hD2 : IsPGroup 2 ↥D)
    (hDnc : ¬ IsCyclic ↥D) {k : ℕ} (hDk : Nat.card ↥D = 2 ^ k) (hk : k = 3 ∨ k = 4)
    (hperm : (B : Set (PGL2 (ZMod p))) * (D : Set (PGL2 (ZMod p))) =
      (D : Set (PGL2 (ZMod p))) * (B : Set (PGL2 (ZMod p))))
    {β : PGL2 (ZMod p)} (hβ : β ∈ B) (hβ3 : orderOf β = 3) :
    (k = 3 → ∃ y ∈ B ⊔ D, y * β * y⁻¹ = β⁻¹) ∧
      (k = 4 → ∀ y ∈ B ⊔ D, y * β * y⁻¹ = β ∨ y * β * y⁻¹ = β⁻¹) := by
  obtain ⟨ε, hε⟩ := burnsideA315y_exists_embedding (p := p) hp2
  have hodd : Odd (Nat.card ↥B) := by
    rw [hB3]
    decide
  have hYc : Nat.card ↥(B ⊔ D) = 3 * 2 ^ k := by
    rw [burnsideA315y_card_sup hodd hD2 hperm, hB3, hDk]
  have hTW : D.map ε ≤ (B ⊔ D).map ε := Subgroup.map_mono le_sup_right
  have hTk : Nat.card ↥(D.map ε) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective hε, hDk]
  have hWc : Nat.card ↥((B ⊔ D).map ε) = 3 * 2 ^ k := by
    rw [Subgroup.card_map_of_injective hε, hYc]
  have hTnc : ¬ IsCyclic ↥(D.map ε) := by
    intro hc
    apply hDnc
    exact isCyclic_of_surjective (D.equivMapOfInjective ε hε).symm.toMonoidHom
      (D.equivMapOfInjective ε hε).symm.surjective
  have hxW : ε β ∈ (B ⊔ D).map ε := Subgroup.mem_map_of_mem ε (Subgroup.mem_sup_left hβ)
  set x : ↥((B ⊔ D).map ε) := ⟨ε β, hxW⟩ with hx
  have hxo : orderOf x = 3 := by
    rw [hx, Subgroup.orderOf_mk, orderOf_injective ε hε, hβ3]
  have hxodd : Odd (orderOf x) := by
    rw [hxo]
    decide
  have hx3 : x ^ 3 = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one x
  have pull : ∀ (w : ↥((B ⊔ D).map ε)) (y : PGL2 (ZMod p)), ε y = (w : _) →
      ∀ c : PGL2 (ZMod p), ((w * x * w⁻¹ : ↥((B ⊔ D).map ε)) : _) = ε c →
        y * β * y⁻¹ = c := by
    intro w y hyw c hc
    apply hε
    rw [map_mul, map_mul, map_inv, hyw, ← hc]
    simp [hx]
  rcases burnsideA315y_dickson_sq hp2 hTW hTnc hTk hWc hk with ⟨z, ⟨e⟩⟩ | ⟨hk3, ⟨e⟩⟩
  · obtain ⟨⟨w, hw⟩, hall⟩ := burnsideA315y_conj_of_dihedral e hxodd
    refine ⟨fun _ => ?_, fun _ y hy => ?_⟩
    · obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 w.2
      refine ⟨y, hy, pull w y hyw β⁻¹ ?_⟩
      rw [hw, map_inv]
      rfl
    · rcases hall ⟨ε y, Subgroup.mem_map_of_mem ε hy⟩ with h | h
      · left
        refine pull ⟨ε y, Subgroup.mem_map_of_mem ε hy⟩ y rfl β ?_
        rw [h]
      · right
        refine pull ⟨ε y, Subgroup.mem_map_of_mem ε hy⟩ y rfl β⁻¹ ?_
        rw [h, map_inv]
        rfl
  · subst hk3
    obtain ⟨w, hw⟩ := burnsideA315y_conj_inv_of_perm4 e hx3
    refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 w.2
    refine ⟨y, hy, pull w y hyw β⁻¹ ?_⟩
    rw [hw, map_inv]
    rfl

theorem burnsideA315y_pgl2 : burnsideA315y_PGL2Statement := by
  intro p _ hp2 B D hBab hBodd hD2 hDcard hperm
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  let θ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    psl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv
  let ψ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) →* PGL2 (ZMod p) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).comp θ.toMonoidHom
  have hψ : Function.Injective ψ :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).comp θ.injective
  have hψr : ψ.range =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨θ y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨θ.symm y, ?_⟩
      show Matrix.ProjectiveSpecialLinearGroup.toPGL (θ (θ.symm y)) = _
      rw [θ.apply_symm_apply]
  set N := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range
  haveI hNn : N.Normal :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglPSLRange_normal (ZMod p)
  have hBN : B ≤ N := by
    intro b hb
    apply pgl2_mem_psl2Range_of_odd_orderOf
    have h1 : orderOf (⟨b, hb⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hBodd h1
  have hBψ : B ≤ ψ.range := hψr ▸ hBN
  have hq1 : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 (by norm_num), pow_one]
  set M := Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1))
  have hL : M = p * (p ^ 2 - 1) / 2 := by
    have h := psl2_card_formula (GaloisField p 1) ⟨p, 1, hp, hpodd, le_rfl, by rw [hq1, pow_one]⟩
    rw [hq1] at h
    exact h
  have hG : Nat.card (PGL2 (ZMod p)) = p * (p ^ 2 - 1) := by
    rw [pgl2_card_formula, Nat.card_zmod]
  have heven : 2 ∣ p * (p ^ 2 - 1) := by
    have h1 : Odd (p ^ 2) := hpodd.pow
    have h2 : Even (p ^ 2 - 1) := Nat.Odd.sub_odd h1 odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h2) _
  have hGM : Nat.card (PGL2 (ZMod p)) = 2 * M := by
    rw [hG, hL]
    exact (Nat.mul_div_cancel' heven).symm
  have hM0 : M ≠ 0 := Nat.card_pos.ne'
  have hNc : Nat.card ↥N = M := by
    rw [← hψr]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have ha : (Nat.card (PGL2 (ZMod p))).factorization 2 = M.factorization 2 + 1 := by
    rw [hGM, Nat.factorization_mul (by norm_num) hM0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
    ring
  have hDc : Nat.card ↥D = 2 * 2 ^ M.factorization 2 := by
    rw [hDcard, ha, pow_succ, mul_comm]
  have hND : Nat.card ↥(N ⊓ D) = 2 ^ M.factorization 2 := by
    have h1 := Subgroup.relIndex_mul_card N D
    have h2 := Subgroup.relIndex_dvd_index_of_normal N D
    have hidx : N.index = 2 := by
      have h3 := Subgroup.card_mul_index N
      rw [hNc, hGM] at h3
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hM0) (h3.trans (mul_comm 2 M))
    rw [hidx] at h2
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exfalso
      rw [h, one_mul, hDcard] at h1
      have h3 : 2 ^ (Nat.card (PGL2 (ZMod p))).factorization 2 ∣ M := by
        rw [← h1, ← hNc]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hM0).1 h3
      omega
    · rw [h, hDc] at h1
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h1
  set S₀ := D.comap ψ with hS₀
  set B₀ := B.comap ψ
  have hS₀c : Nat.card ↥S₀ = 2 ^ M.factorization 2 := by
    rw [← Subgroup.card_map_of_injective (K := S₀) hψ, hS₀, Subgroup.map_comap_eq, hψr, hND]
  have hS₀syl : CFSG.QuasithinUnique.IsSylowTwoOf S₀ ⊤ :=
    burnsideA315y_isSylowTwoOf_of_card hS₀c
  have hB₀c : Nat.card ↥B₀ = Nat.card ↥B := burnsideA315y_card_comap hψ hBψ
  have hB₀odd : Odd (Nat.card ↥B₀) := by
    rw [hB₀c]
    exact hBodd
  have hB₀ab : IsMulCommutative ↥B₀ := by
    refine ⟨⟨fun a b => Subtype.ext (hψ ?_)⟩⟩
    have h := congrArg Subtype.val (hBab.is_comm.comm (⟨ψ a, a.2⟩ : ↥B) ⟨ψ b, b.2⟩)
    simpa using h
  have hperm₀ := burnsideA315y_comap_permute ψ hBψ hperm
  obtain ⟨⟨m, hm, hS₀m⟩, hS₀nc⟩ := burnsideA315x_sylow_facts (F := GaloisField p 1) hp hp2 le_rfl
    (GaloisField.card p 1 (by norm_num)) hS₀syl
  have hDnc : ¬ IsCyclic ↥D := fun hc => hS₀nc (burnsideA315y_cyclic_comap hψ hc)
  have hDm : Nat.card ↥D = 2 ^ (m + 2) := by
    rw [hDc, ← hS₀c, hS₀m, pow_succ 2 (m + 1), mul_comm]
  have concl_a : IsCyclic ↥B₀ → (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
      ((Nat.card ↥B₀ : ℕ) : ℤ) ∣ (p : ℤ) - ε) → (∃ s ∈ S₀, ∀ x ∈ B₀, s * x * s⁻¹ = x⁻¹) →
      IsCyclic ↥B ∧
      (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥B : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        ∃ d ∈ D, d ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ∧
          ∀ x ∈ B, d * x * d⁻¹ = x⁻¹) ∨
       ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥B = 3 ∧ ∃ d ∈ D, ∀ x ∈ B, d * x * d⁻¹ = x⁻¹)) := by
    rintro hcyc ⟨ε, hε1, hε2, hε3⟩ ⟨s, hs, hinv⟩
    obtain ⟨hsD, hsinv⟩ := burnsideA315y_inv_comap hBψ hs hinv
    refine ⟨burnsideA315y_cyclic_of_comap hψ hBψ hcyc,
      Or.inl ⟨⟨ε, hε1, hε2, ?_⟩, ψ s, hsD, ⟨θ s, rfl⟩, hsinv⟩⟩
    rw [← hB₀c]
    exact hε3
  by_cases h3 : IsPGroup 3 ↥B₀
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases burnsideA315y_l2_three hp2 hS₀syl h3 hperm₀ with
      ⟨hcyc, hε, hs⟩ | ⟨hB₀3, hS₀4⟩ | ⟨hB₀3, hS₀8, ⟨φ⟩⟩
    · exact concl_a hcyc hε hs
    ·
      have hB3 : Nat.card ↥B = 3 := hB₀c ▸ hB₀3
      have hm1 : m = 1 := by
        rw [hS₀m] at hS₀4
        have : 2 ^ (m + 1) = 2 ^ 2 := hS₀4
        have := Nat.pow_right_injective le_rfl this
        omega
      subst hm1
      haveI hBcyc : IsCyclic ↥B := isCyclic_of_prime_card hB3
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥B)
      have hgo : orderOf (g : PGL2 (ZMod p)) = 3 := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hB3]
      have hgen : ∀ x ∈ B, ∃ k : ℤ, (g : PGL2 (ZMod p)) ^ k = x := by
        intro x hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
        exact ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
      obtain ⟨h3', -⟩ := burnsideA315y_sq_conj hp2 hB3 hD2 hDnc hDm (Or.inl rfl) hperm g.2 hgo
      obtain ⟨y, hy, hyβ⟩ := h3' rfl
      obtain ⟨d, hd, hdinv⟩ := burnsideA315y_inv_of_conj hperm hBab g.2 hgen hy hyβ
      refine ⟨hBcyc, Or.inr ⟨?_, hB3, d, hd, hdinv⟩⟩
      apply burnsideA315y_mod_eight hpodd
      intro h16
      have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (by rw [← hG]; exact Nat.card_pos.ne')).1 h16
      rw [← hG] at h4
      have h5 : 2 ^ (Nat.card (PGL2 (ZMod p))).factorization 2 = 2 ^ 3 := by
        rw [← hDcard, hDm]
      have h6 := Nat.pow_right_injective le_rfl h5
      omega
    ·
      exfalso
      have hB3 : Nat.card ↥B = 3 := hB₀c ▸ hB₀3
      have hm2 : m = 2 := by
        rw [hS₀m] at hS₀8
        have : 2 ^ (m + 1) = 2 ^ 3 := hS₀8
        have := Nat.pow_right_injective le_rfl this
        omega
      subst hm2
      haveI hBcyc : IsCyclic ↥B := isCyclic_of_prime_card hB3
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥B)
      have hgo : orderOf (g : PGL2 (ZMod p)) = 3 := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hB3]
      obtain ⟨-, h4⟩ := burnsideA315y_sq_conj hp2 hB3 hD2 hDnc hDm (Or.inr rfl) hperm g.2 hgo
      have hall := h4 rfl
      obtain ⟨β₀, hβ₀⟩ := hBψ g.2
      have hβ₀B : β₀ ∈ B₀ := by
        show ψ β₀ ∈ B
        rw [hβ₀]
        exact g.2
      let x₀ : ↥(B₀ ⊔ S₀) := ⟨β₀, Subgroup.mem_sup_left hβ₀B⟩
      have hx₀3 : x₀ ^ 3 = 1 := by
        apply Subtype.ext
        apply hψ
        rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
        show ψ β₀ ^ 3 = 1
        rw [hβ₀, ← hgo]
        exact pow_orderOf_eq_one _
      have hx₀1 : x₀ ≠ 1 := by
        intro h
        have h' : ψ β₀ = 1 := by
          have := congrArg Subtype.val h
          rw [Subgroup.coe_one] at this
          show ψ β₀ = 1
          rw [show β₀ = (x₀ : _) from rfl, this, map_one]
        rw [hβ₀] at h'
        rw [h', orderOf_one] at hgo
        exact absurd hgo (by norm_num)
      obtain ⟨w, hw1, hw2⟩ := burnsideA315y_not_normal_of_perm4 φ hx₀3 hx₀1
      have hy : ψ (w : _) ∈ B ⊔ D := by
        have hle : (B₀ ⊔ S₀).map ψ ≤ B ⊔ D := by
          rw [Subgroup.map_sup]
          exact sup_le_sup (Subgroup.map_comap_le ψ B) (Subgroup.map_comap_le ψ D)
        exact hle (Subgroup.mem_map_of_mem ψ w.2)
      have hconj : ψ ((w * x₀ * w⁻¹ : ↥(B₀ ⊔ S₀)) : _) =
          ψ (w : _) * (g : PGL2 (ZMod p)) * (ψ (w : _))⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
        show ψ (w : _) * ψ β₀ * (ψ (w : _))⁻¹ = _
        rw [hβ₀]
      rcases hall _ hy with h | h
      · apply hw1
        apply Subtype.ext
        apply hψ
        rw [hconj, h]
        exact hβ₀.symm
      · apply hw2
        apply Subtype.ext
        apply hψ
        rw [hconj, h, Subgroup.coe_inv, map_inv]
        show _ = (ψ β₀)⁻¹
        rw [hβ₀]
  · have hc : burnsideA315x_Config _ S₀ B₀ := ⟨hS₀syl, hB₀odd, h3, Or.inl hB₀ab, hperm₀⟩
    obtain ⟨hcyc, ⟨ε, hε1, hε2, hε3⟩, hs⟩ := burnsideA315x_l2_core (p := p) (e := 1) hp2 le_rfl hc
    rw [pow_one] at hε2 hε3
    exact concl_a hcyc ⟨ε, hε1, hε2, hε3⟩ hs

end CFSG.ASVolI
