module

public import CFSG.Quasithin.H13.A5S1515a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

section General

variable {G : Type} [Group G]

abbrev Hstar (H : Subgroup G) : Type := ↥H ⧸ (pCoreOf 2 H).subgroupOf H

@[expose] noncomputable def piQ (H : Subgroup G) : ↥H →* Hstar H := QuotientGroup.mk' _

theorem piQ_surjective (H : Subgroup G) : Function.Surjective (piQ H) :=
  QuotientGroup.mk'_surjective _

theorem piQ_eq_one_iff {H : Subgroup G} (x : ↥H) : piQ H x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  unfold piQ
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem piQ_eq_iff {H : Subgroup G} (x y : ↥H) :
    piQ H x = piQ H y ↔ (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 H := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, piQ_eq_one_iff]
  rfl

@[expose] noncomputable def preQ (H : Subgroup G) (X : Subgroup (Hstar H)) : Subgroup G :=
  (X.comap (piQ H)).map H.subtype

theorem mem_preQ {H : Subgroup G} {X : Subgroup (Hstar H)} {x : G} :
    x ∈ preQ H X ↔ ∃ hx : x ∈ H, piQ H ⟨x, hx⟩ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hX⟩
    exact ⟨⟨x, hx⟩, hX, rfl⟩

theorem preQ_le (H : Subgroup G) (X : Subgroup (Hstar H)) : preQ H X ≤ H :=
  fun _ hx => (mem_preQ.1 hx).1

theorem le_normalizer_preQ (H : Subgroup G) (X : Subgroup (Hstar H)) [X.Normal] :
    H ≤ Subgroup.normalizer (preQ H X : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxH, hxX⟩ := mem_preQ.1 hx
    refine mem_preQ.2 ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
    have := Subgroup.Normal.conj_mem ‹_› _ hxX (piQ H ⟨h, hh⟩)
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact this
  · intro hx
    obtain ⟨hxH, hxX⟩ := mem_preQ.1 hx
    have hx' : x ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hxH) hh
      simpa [mul_assoc] using this
    refine mem_preQ.2 ⟨hx', ?_⟩
    have := Subgroup.Normal.conj_mem ‹_› _ hxX (piQ H ⟨h, hh⟩)⁻¹
    have e : piQ H ⟨x, hx'⟩ = (piQ H ⟨h, hh⟩)⁻¹ * piQ H ⟨h * x * h⁻¹, hxH⟩ *
        ((piQ H ⟨h, hh⟩)⁻¹)⁻¹ := by
      rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
    rw [e]
    exact this

theorem perm3_cube_of_odd : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 ∨ σ ^ 2 = 1 := by
  decide

end General

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pCore_two_Hstar (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    CFSG.Open.pCore 2 (Hstar H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hypF91 h1323 hH
  set P := CFSG.Open.pCore 2 (Hstar H)
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup 2
  set D := preQ H P
  have hDQ : D ≤ pCoreOf 2 H := by
    rw [hF.F92_3.1]
    refine hF.F92_1_reduced (preQ_le H P) (le_normalizer_preQ H P) fun d hd => ?_
    obtain ⟨hdH, hdP⟩ := mem_preQ.1 hd
    obtain ⟨k, hk⟩ := hPp ⟨_, hdP⟩
    refine ⟨k, ?_⟩
    rw [← hF.F92_3.1]
    have h1 : piQ H (⟨d, hdH⟩ ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact (piQ_eq_one_iff _).1 h1
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨x, rfl⟩ := piQ_surjective H a
  rw [Subgroup.mem_bot, piQ_eq_one_iff]
  exact hDQ (mem_preQ.2 ⟨x.2, ha⟩)

theorem I_S3 (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {h : G} (hh : h ∈ H)
    (hI : ¬ ∀ y ∈ V ⊔ conjSub h⁻¹ V, ∃ n : ℕ, y ^ 2 ^ n ∈ pCoreOf 2 H) :
    ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
      Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
        Equiv.Perm (Fin 3)) := by
  have hF := S.hypF91 h1323 hH
  have hV := S.not_V_le_QH h1323 hH hna
  have hcard : Nat.card V = 2 ^ 4 := S.card_V.trans (by norm_num)
  exact (hF956 G T V L S.V1 S.V3 H hF S.relIndex_V3 hV
    (fun g hg hlt => S.isPGroup_sup_of_lt h1323 h1326 h1336 hH hg hlt) (S.hyp_F956 h1323 H)
    hcard h hh hI).2

theorem cube_mem_of_odd (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {h : G} (hh : h ∈ H)
    (hI : ¬ ∀ y ∈ V ⊔ conjSub h⁻¹ V, ∃ n : ℕ, y ^ 2 ^ n ∈ pCoreOf 2 H)
    {y : G} (hy : y ∈ V ⊔ conjSub h⁻¹ V) {m : ℕ} (hm : Odd m) (hym : y ^ m ∈ pCoreOf 2 H) :
    y ^ 3 ∈ pCoreOf 2 H := by
  obtain ⟨hN, ⟨e⟩⟩ := S.I_S3 h1323 h1326 h1336 hF956 hH hna hh hI
  set I := V ⊔ conjSub h⁻¹ V
  set π := QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)
  have hπ1 : ∀ z : ↥I, π z = 1 ↔ (z : G) ∈ pCoreOf 2 H := fun z => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hm1 : e (π ⟨y, hy⟩) ^ m = 1 := by
    rw [← map_pow, ← map_pow, (hπ1 _).2 (by simpa using hym), map_one]
  rcases perm3_cube_of_odd (e (π ⟨y, hy⟩)) with h3 | h2
  · rw [← map_pow, ← map_pow] at h3
    have := (hπ1 _).1 (e.injective (h3.trans (map_one e).symm))
    simpa using this
  ·
    have hσ : e (π ⟨y, hy⟩) = 1 := by
      obtain ⟨k, hk⟩ := hm
      rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at hm1
      exact hm1
    have h1 : π ⟨y, hy⟩ = 1 := e.injective (hσ.trans (map_one e).symm)
    have := (hπ1 _).1 h1
    have hy3 : y ^ 3 = y * y ^ 2 := by group
    have hy1 : y ∈ pCoreOf 2 H := by simpa using this
    exact Subgroup.pow_mem _ hy1 3

end Setting

end CFSG.Quasithin.H13.A5
