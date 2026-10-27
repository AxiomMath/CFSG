module

public import CFSG.Quasithin.H13.A5S1521c
public import CFSG.Quasithin.H13.A5Facts1321b
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.H13.A5S1520b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.InternalSec
open scoped commutatorElement

section Conj

variable {Y : Type} [Group Y]

@[expose] noncomputable def conjNorm (K : Subgroup Y) :
    ↥(Subgroup.normalizer (K : Set Y)) →* MulAut ↥K where
  toFun y :=
    { toFun := fun k => ⟨(y : Y) * k * (y : Y)⁻¹, (Subgroup.mem_normalizer_iff.mp y.2 k).mp k.2⟩
      invFun := fun k => ⟨(y : Y)⁻¹ * k * y, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ y.2) k).mp k.2
        simpa using this⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k k' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext k; simp
  map_mul' y y' := by ext k; simp [mul_assoc]

theorem conjNorm_apply (K : Subgroup Y) (y : ↥(Subgroup.normalizer (K : Set Y))) (k : ↥K) :
    ((conjNorm K y k : ↥K) : Y) = y * k * (y : Y)⁻¹ := rfl

theorem conjNorm_of_mem (K : Subgroup Y) (k : ↥K) :
    conjNorm K ⟨k, Subgroup.le_normalizer k.2⟩ = MulAut.conj k := by
  ext k'
  rfl

theorem conjNorm_eq_one_iff (K : Subgroup Y) (y : ↥(Subgroup.normalizer (K : Set Y))) :
    conjNorm K y = 1 ↔ ∀ k ∈ K, (y : Y) * k = k * y := by
  constructor
  · intro h k hk
    have := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : Y)) h
    simp only [conjNorm_apply, MulAut.one_apply] at this
    calc (y : Y) * k = (y : Y) * k * (y : Y)⁻¹ * y := by group
      _ = k * y := by rw [this]
  · intro h
    ext k
    show (y : Y) * k * (y : Y)⁻¹ = k
    rw [h k k.2, mul_inv_cancel_right]

end Conj

theorem exists_two_of_card_nine {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hc : 9 ≤ Nat.card E) :
    ∃ x ∈ E, ∃ c ∈ E, x ^ 3 = 1 ∧ c ^ 3 = 1 ∧ x * c = c * x ∧ x ≠ 1 ∧
      c ∉ Subgroup.zpowers x := by
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by omega)
  have hcomm : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [this, Subgroup.card_bot] at hc
    omega
  have hx3 : x ^ 3 = 1 := hE.2 x hxE
  obtain ⟨c, hcE, hcx⟩ : ∃ c ∈ E, c ∉ Subgroup.zpowers x := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hle : E ≤ Subgroup.zpowers x := fun c hc => h c hc
    have heq : E = Subgroup.zpowers x := le_antisymm hle (Subgroup.zpowers_le.mpr hxE)
    rw [heq, Nat.card_zpowers] at hc
    have h2 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
    omega
  exact ⟨x, hxE, c, hcE, hx3, hE.2 c hcE, hcomm x hxE c hcE, hx1, hcx⟩

section L1

variable {Y : Type} [Group Y] {W : Type} [CommGroup W]

structure HypY (P : Hyp1321 Y W) where
  L : Subgroup Y
  normK : L ≤ Subgroup.normalizer (P.K : Set Y)
  comm : ∀ l ∈ L, l * P.b = P.b * l
  solv : Group.IsSolvable ↥L
  res : L ≤ oTwoRes L
  noncent : ∃ l ∈ L, ∃ k ∈ P.K, l * k ≠ k * l
  normC : ∀ k ∈ P.K, k * P.b = P.b * k → ∀ l ∈ L, k * l * k⁻¹ ∈ L

namespace HypY

variable {P : Hyp1321 Y W} (Q : HypY P)

@[expose] noncomputable def bhat : MulAut ↥P.K := conjNorm P.K ⟨P.b, P.bN⟩

@[expose] noncomputable def Lhat : Subgroup (MulAut ↥P.K) :=
  (Q.L.subgroupOf (Subgroup.normalizer (P.K : Set Y))).map (conjNorm P.K)

theorem mem_Lhat {α : MulAut ↥P.K} :
    α ∈ Q.Lhat ↔ ∃ l, ∃ hl : l ∈ Q.L, conjNorm P.K ⟨l, Q.normK hl⟩ = α := by
  constructor
  · rintro ⟨⟨l, hlN⟩, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Q.normK hl⟩, hl, rfl⟩

theorem bhat_ne_one : bhat (P := P) ≠ 1 := by
  intro h
  obtain ⟨k, hk, hkb⟩ := P.bc
  exact hkb ((conjNorm_eq_one_iff P.K _).mp h k hk).symm

theorem bhat_sq : bhat (P := P) * bhat = 1 := by
  rw [bhat, ← map_mul]
  have : (⟨P.b, P.bN⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) * ⟨P.b, P.bN⟩ = 1 :=
    Subtype.ext P.b2
  rw [this, map_one]

theorem Lhat_le_centralizer : Q.Lhat ≤ Subgroup.centralizer {bhat (P := P)} := by
  intro α hα
  obtain ⟨l, hl, rfl⟩ := Q.mem_Lhat.mp hα
  rw [Subgroup.mem_centralizer_singleton_iff, bhat, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Q.comm l hl)

theorem Lhat_solvable : Group.IsSolvable ↥Q.Lhat := by
  have := Q.solv
  let f : ↥Q.L →* ↥Q.Lhat :=
    { toFun := fun l => ⟨conjNorm P.K ⟨l, Q.normK l.2⟩, Q.mem_Lhat.mpr ⟨l, l.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one (conjNorm P.K))
      map_mul' := fun l l' => Subtype.ext (by
        show conjNorm P.K _ = conjNorm P.K _ * conjNorm P.K _
        rw [← map_mul]; rfl) }
  refine Group.isSolvable_of_surjective (f := f) ?_
  rintro ⟨α, hα⟩
  obtain ⟨l, hl, rfl⟩ := Q.mem_Lhat.mp hα
  exact ⟨⟨l, hl⟩, rfl⟩

theorem Lhat_res : Q.Lhat = oTwoRes Q.Lhat := by
  refine le_antisymm ?_ (oTwoRes_le _)
  intro α hα
  obtain ⟨l, hl, rfl⟩ := Q.mem_Lhat.mp hα
  have hl' := Q.res hl
  have key : ∀ x (hx : x ∈ oTwoRes Q.L), ∀ h : x ∈ Q.L,
      conjNorm P.K ⟨x, Q.normK h⟩ ∈ oTwoRes Q.Lhat := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxL, m, hm, hxm⟩ := hx
      intro h
      refine Subgroup.subset_closure ⟨Q.mem_Lhat.mpr ⟨x, h, rfl⟩, m, hm, ?_⟩
      rw [← map_pow]
      have : (⟨x, Q.normK h⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) ^ m = 1 := Subtype.ext hxm
      rw [this, map_one]
    | one => intro h; rw [show (⟨1, Q.normK h⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) = 1 from
        rfl, map_one]; exact Subgroup.one_mem _
    | mul a c ha hc iha ihc =>
      intro h
      have hrL := oTwoRes_le Q.L
      have e : (⟨a * c, Q.normK h⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) =
          ⟨a, Q.normK (hrL ha)⟩ * ⟨c, Q.normK (hrL hc)⟩ := rfl
      rw [e, map_mul]
      exact Subgroup.mul_mem _ (iha (hrL ha)) (ihc (hrL hc))
    | inv a ha iha =>
      intro h
      have hrL := oTwoRes_le Q.L
      have e : (⟨a⁻¹, Q.normK h⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) =
          (⟨a, Q.normK (hrL ha)⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ (iha (hrL ha))
  exact key l hl' hl

theorem Lhat_ne_bot : Q.Lhat ≠ ⊥ := by
  intro h
  obtain ⟨l, hl, k, hk, hlk⟩ := Q.noncent
  have h1 : conjNorm P.K ⟨l, Q.normK hl⟩ = 1 := by
    have := Q.mem_Lhat.mpr ⟨l, hl, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  exact hlk ((conjNorm_eq_one_iff P.K _).mp h1 k hk)

theorem Lhat_norm : ∀ k : ↥P.K, bhat (P := P) k = k →
    ∀ α ∈ Q.Lhat, MulAut.conj k * α * (MulAut.conj k)⁻¹ ∈ Q.Lhat := by
  intro k hk α hα
  obtain ⟨l, hl, rfl⟩ := Q.mem_Lhat.mp hα
  have hkb : (k : Y) * P.b = P.b * k := by
    have := congrArg Subtype.val hk
    rw [bhat, conjNorm_apply] at this
    calc (k : Y) * P.b = P.b * k * P.b⁻¹ * P.b := by rw [this]
      _ = P.b * k := by group
  have hkl := Q.normC k k.2 hkb l hl
  refine Q.mem_Lhat.mpr ⟨_, hkl, ?_⟩
  rw [← conjNorm_of_mem, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem pair_hat (g : ↥P.K) :
    (∃ k : ℕ, (bhat (P := P) * (MulAut.conj g * bhat * (MulAut.conj g)⁻¹)) ^ 2 ^ k = 1) ∨
      (bhat (P := P) * (MulAut.conj g * bhat * (MulAut.conj g)⁻¹)) ^ 3 = 1 := by
  have hm : P.b * (g * P.b * (g : Y)⁻¹) ∈ Subgroup.normalizer (P.K : Set Y) :=
    Subgroup.mul_mem _ P.bN (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.le_normalizer g.2) P.bN) (Subgroup.inv_mem _ (Subgroup.le_normalizer g.2)))
  have e : bhat (P := P) * (MulAut.conj g * bhat * (MulAut.conj g)⁻¹) =
      conjNorm P.K ⟨P.b * (g * P.b * (g : Y)⁻¹), hm⟩ := by
    rw [bhat, ← conjNorm_of_mem, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e]
  rcases P.pair g with ⟨k, hk⟩ | h3
  · left
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨P.b * (g * P.b * (g : Y)⁻¹), hm⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) ^ 2 ^ k
        = 1 := Subtype.ext hk
    rw [this, map_one]
  · right
    rw [← map_pow]
    have : (⟨P.b * (g * P.b * (g : Y)⁻¹), hm⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) ^ 3 = 1 :=
      Subtype.ext h3
    rw [this, map_one]

include Q in
theorem not_A7 [Finite Y] (hA7 : FactA7Grp1321)
    (hπ : ∃ π : ↥(alternatingGroup (Fin 7)) →* ↥P.K, Function.Surjective π) : False := by
  have : Nontrivial ↥P.K := CFSG.LocalCores.isQuasisimple_nontrivial P.quasi
  have := Q.Lhat_solvable
  exact Q.Lhat_ne_bot (hA7 ↥P.K inferInstance hπ bhat bhat_ne_one bhat_sq (pair_hat (P := P)) Q.Lhat
    Q.Lhat_le_centralizer Q.Lhat_norm inferInstance Q.Lhat_res)

include Q in
theorem not_L3 [Finite Y] (hL3 : FactL3Grp1321)
    (hπ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥P.K, Function.Surjective π) :
    False := by
  have : Nontrivial ↥P.K := CFSG.LocalCores.isQuasisimple_nontrivial P.quasi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSb⟩ := P.syl
  obtain ⟨S', hS'⟩ := RankOneRecog.isSylowTwoOf_iff_exists.mp hS
  refine Q.Lhat_ne_bot (hL3 ↥P.K inferInstance hπ bhat bhat_ne_one bhat_sq ⟨S', ?_⟩ Q.Lhat
    Q.Lhat_le_centralizer Q.Lhat_res)
  intro s hs
  have hsS : (s : Y) ∈ S := by rw [← hS']; exact ⟨s, hs, rfl⟩
  apply Subtype.ext
  rw [bhat, conjNorm_apply]
  show P.b * s * P.b⁻¹ = s
  rw [← hSb _ hsS, mul_inv_cancel_right]


end HypY

structure HypL1 (P : Hyp1321 Y W) where
  L : Subgroup Y
  normK : L ≤ Subgroup.normalizer (P.K : Set Y)
  comm : ∀ l ∈ L, l * P.b = P.b * l
  res : L ≤ oTwoRes L
  three : ∀ l ∈ L, ∀ m : ℕ, Odd m → l ^ m = 1 → l ^ 3 = 1
  Dinv : ∀ l ∈ L, ∀ d ∈ P.D, P.ρ l d ∈ P.D
  Dnt : ∃ l ∈ L, ∃ d ∈ P.D, P.ρ l d ≠ d

namespace HypL1

variable {P : Hyp1321 Y W} (Q : HypL1 P)


theorem eq_of_ne_one_of_card_two {M : Type*} [Group M] (h : Nat.card M = 2) {a c : M}
    (ha : a ≠ 1) (hc : c ≠ 1) : a = c := by
  have hidx : (⊥ : Subgroup M).index = 2 := by rw [Subgroup.index_bot, h]
  have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := c⁻¹)).mpr
    (iff_of_false (by rw [Subgroup.mem_bot]; exact ha)
      (by rw [Subgroup.mem_bot, inv_eq_one]; exact hc))
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem fix_D_of_two (hW : ∀ w : W, w ^ 2 = 1) {l : Y} (hl : l ∈ Q.L) {m : ℕ} (hm : Odd m)
    (hlm : l ^ m = 1) {J : Subgroup W}
    (hJL : ∀ l ∈ Q.L, ∀ d ∈ J, P.ρ l d ∈ J) (hJ2 : Nat.card J = 2)
    (hJi : (J.subgroupOf P.D).index = 2) : ∀ d ∈ P.D, P.ρ l d = d := by
  have hzm : P.ρ l ^ m = 1 := by rw [← map_pow, hlm, map_one]
  have hfixJ : ∀ j ∈ J, P.ρ l j = j := by
    intro j hj
    by_cases hj1 : j = 1
    · rw [hj1, map_one]
    · have h1 : (⟨P.ρ l j, hJL l hl j hj⟩ : ↥J) ≠ 1 := by
        intro h
        apply hj1
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_one] at this
        exact (map_eq_one_iff _ (P.ρ l).injective).mp this
      have h2 : (⟨j, hj⟩ : ↥J) ≠ 1 := fun h => hj1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (eq_of_ne_one_of_card_two hJ2 h1 h2)
  have hinvJ : ∀ d ∈ P.D, P.ρ l d ∈ J → d ∈ J := by
    intro d hd hld
    have hlinv : l ^ (m - 1) ∈ Q.L := Subgroup.pow_mem _ hl _
    have e : P.ρ (l ^ (m - 1)) (P.ρ l d) = d := by
      rw [← MulAut.mul_apply, ← map_mul, ← pow_succ, Nat.sub_add_cancel hm.pos, hlm, map_one,
        MulAut.one_apply]
    rw [← e]
    exact hJL _ hlinv _ hld
  intro d hd
  refine fix_of_odd_of_fix_comm hW hm hzm (hfixJ _ ?_)
  by_cases hdJ : d ∈ J
  · exact J.mul_mem (hJL l hl d hdJ) (J.inv_mem hdJ)
  · have hld : P.ρ l d ∈ P.D := Q.Dinv l hl d hd
    have hldJ : P.ρ l d ∉ J := fun h => hdJ (hinvJ d hd h)
    have := (Subgroup.mul_mem_iff_of_index_two hJi (a := ⟨P.ρ l d, hld⟩)
      (b := (⟨d, hd⟩ : ↥P.D)⁻¹)).mpr (iff_of_false hldJ (by
        rw [Subgroup.inv_mem_iff]; exact hdJ))
    exact this

theorem D_irr [Finite W] (J : Subgroup W) (hJD : J ≤ P.D) (hJL : ∀ l ∈ Q.L, ∀ d ∈ J, P.ρ l d ∈ J) :
    J = ⊥ ∨ J = P.D := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hJ1, hJD'⟩ := hne
  have hcJ : 1 < Nat.card J := (Subgroup.one_lt_card_iff_ne_bot J).mpr hJ1
  have hcard := Subgroup.card_mul_index (J.subgroupOf P.D)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJD).toEquiv] at hcard
  have hidx1 : (J.subgroupOf P.D).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one]
    intro h
    apply hJD'
    refine le_antisymm hJD fun d hd => ?_
    have : (⟨d, hd⟩ : ↥P.D) ∈ J.subgroupOf P.D := h ▸ Subgroup.mem_top _
    exact this
  have hidx0 : (J.subgroupOf P.D).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hD4 := P.hD4
  have hJ2 : Nat.card J = 2 ∧ (J.subgroupOf P.D).index = 2 := by
    set a := Nat.card J
    set c := (J.subgroupOf P.D).index
    have hc2 : 2 ≤ c := by omega
    have ha4 : a ≤ 4 := by nlinarith
    have hc4 : c ≤ 4 := by nlinarith
    interval_cases a <;> interval_cases c <;> omega
  have hfix : ∀ l ∈ oTwoRes Q.L, ∀ d ∈ P.D, P.ρ l d = d := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem l hl =>
      obtain ⟨hlL, m, hm, hlm⟩ := hl
      exact Q.fix_D_of_two P.sq hlL hm hlm hJL hJ2.1 hJ2.2
    | one => intro d _; rw [map_one, MulAut.one_apply]
    | mul a c _ _ ha hc =>
      intro d hd
      rw [map_mul, MulAut.mul_apply, hc d hd, ha d hd]
    | inv a _ ha =>
      intro d hd
      rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq, ha d hd]
  obtain ⟨l, hl, d, hd, hld⟩ := Q.Dnt
  exact hld (hfix l (Q.res hl) d hd)

include Q in
theorem card_D [Finite W] : Nat.card P.D = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥P.D := fun d => ⟨1, Subtype.ext (by simpa using P.sq d)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hD4 := P.hD4
  obtain ⟨l, hl, d, hd, hld⟩ := Q.Dnt
  have hd1 : (⟨d, hd⟩ : ↥P.D) ≠ 1 := by
    intro h
    apply hld
    have : d = 1 := congrArg Subtype.val h
    rw [this, map_one]
  have hlt : 1 < Nat.card P.D := Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hd1⟩⟩
  rw [hn] at hD4 hlt ⊢
  have hn2 : n ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · norm_num at hlt
  · exfalso
    apply hld
    have h2 : Nat.card ↥P.D = 2 := by rw [hn]; norm_num
    have hld1 : (⟨P.ρ l d, Q.Dinv l hl d hd⟩ : ↥P.D) ≠ 1 := by
      intro h
      apply hd1
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_one] at this
      exact Subtype.ext ((map_eq_one_iff _ (P.ρ l).injective).mp this)
    exact congrArg Subtype.val (eq_of_ne_one_of_card_two h2 hld1 hd1)
  · rfl


theorem le_K [Finite Y] (hZ : Subgroup.center ↥P.K = ⊥)
    (hrank : ∃ x ∈ P.K, ∃ c ∈ P.K, x ^ 3 = 1 ∧ c ^ 3 = 1 ∧ x * c = c * x ∧ x ≠ 1 ∧
      c ∉ Subgroup.zpowers x)
    (hout : ∀ α : MulAut ↥P.K, α ^ 3 = 1 → ∃ k : ↥P.K, α = MulAut.conj k) : Q.L ≤ P.K := by
  have hodd : ∀ x ∈ Q.L, (∃ m : ℕ, Odd m ∧ x ^ m = 1) → x ∈ P.K := by
    rintro x hxL ⟨m, hm, hxm⟩
    have hx3 := Q.three x hxL m hm hxm
    have hα3 : (conjNorm P.K ⟨x, Q.normK hxL⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, Q.normK hxL⟩ : ↥(Subgroup.normalizer (P.K : Set Y))) ^ 3 = 1 :=
        Subtype.ext hx3
      rw [this, map_one]
    obtain ⟨k, hk⟩ := hout _ hα3
    set z : Y := (k : Y)⁻¹ * x with hz
    have hzc : ∀ g ∈ P.K, z * g = g * z := by
      intro g hg
      have h1 := congrArg (fun α : MulAut ↥P.K => ((α ⟨g, hg⟩ : ↥P.K) : Y)) hk
      simp only [conjNorm_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc z * g = (k : Y)⁻¹ * (x * g * x⁻¹) * x := by rw [hz]; group
        _ = (k : Y)⁻¹ * ((k : Y) * g * (k : Y)⁻¹) * x := by rw [h1]
        _ = g * z := by rw [hz]; group
    have hxkz : x = k * z := by rw [hz]; group
    have hkz : Commute (k : Y) z := (hzc k k.2).symm
    have h13 : (k : Y) ^ 3 * z ^ 3 = 1 := by rw [← hkz.mul_pow, ← hxkz, hx3]
    have hzK : ∀ i : ℤ, z ^ i ∈ P.K → z ^ i = 1 := by
      intro i hi
      have hcen : (⟨z ^ i, hi⟩ : ↥P.K) ∈ Subgroup.center ↥P.K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (((show Commute z (g : Y) from hzc g g.2).zpow_left i).eq).symm
      rw [hZ, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    have hz3 : z ^ 3 = 1 := by
      have hz3K : z ^ ((3 : ℕ) : ℤ) ∈ P.K := by
        rw [zpow_natCast, eq_inv_of_mul_eq_one_right h13]
        exact P.K.inv_mem (P.K.pow_mem k.2 3)
      have := hzK _ hz3K
      rwa [zpow_natCast] at this
    by_cases hz1 : z = 1
    · rw [hxkz, hz1, mul_one]
      exact k.2
    · exfalso
      obtain ⟨x0, hx0K, c0, hc0K, hx03, hc03, hx0c0, hx01, hc0x0⟩ := hrank
      have hx0z : x0 ∉ Subgroup.zpowers z := by
        intro h
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
        apply hx01
        rw [← hi]
        exact hzK i (hi ▸ hx0K)
      have hc0 : c0 ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers x0 := by
        intro h
        have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers x0, a * b = b * a := by
          intro a ha b hb
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact ((show Commute z x0 from hzc x0 hx0K).zpow_zpow i j).eq
        obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hcomm h
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have hbK : b ∈ P.K := Subgroup.zpowers_le.mpr hx0K hb
        have hzi : z ^ i ∈ P.K := by
          have e : z ^ i = c0 * b⁻¹ := by rw [hab]; group
          rw [e]
          exact P.K.mul_mem hc0K (P.K.inv_mem hbK)
        rw [hzK i hzi, one_mul] at hab
        exact hc0x0 (hab ▸ hb)
      have h3 := three_le_pRank (K := Y) (hzc x0 hx0K).symm hx0c0 (hzc c0 hc0K) hx03 hz3 hc03
        hz1 hx0z hc0
      have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 := P.sqtk.sqt 3 Nat.prime_three (by norm_num)
      omega
  intro l hl
  have hres := Q.res hl
  have hle : oTwoRes Q.L ≤ P.K := by
    rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hxL, m, hm, hxm⟩
    exact hodd x hxL ⟨m, hm, hxm⟩
  exact hle hres

theorem rank_eq_two [Finite W] (hLK : Q.L ≤ P.K) {U1 U2 : Subgroup W}
    (h1 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U1, P.ρ y u ∈ U1)
    (h2 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U2, P.ρ y u ∈ U2)
    (hv : secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ ≠ 1) :
    P.D ≤ U1 ∧ P.D ⊓ U2 = ⊥ ∧
      rkIdx (fixV (Subgroup.zpowers
        (secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩))) = 2 := by
  classical
  have hbK' : P.b ∈ P.K ⊔ Subgroup.zpowers P.b := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  set v := secAct P.ρ _ h1 h2 ⟨P.b, hbK'⟩ with hv'
  have hL1 : ∀ l ∈ Q.L, ∀ u ∈ U1, P.ρ l u ∈ U1 := fun l hl => h1 l (Subgroup.mem_sup_left (hLK hl))
  have hL2 : ∀ l ∈ Q.L, ∀ u ∈ U2, P.ρ l u ∈ U2 := fun l hl => h2 l (Subgroup.mem_sup_left (hLK hl))
  have hlb : ∀ l ∈ Q.L, ∀ w : W, P.ρ l (P.ρ P.b w) = P.ρ P.b (P.ρ l w) := by
    intro l hl w
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, Q.comm l hl]
  obtain ⟨u, hu, hub⟩ : ∃ u ∈ U1, P.ρ P.b u * u⁻¹ ∉ U2 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hv ((secAct_eq_one_iff P.ρ _ h1 h2 _).mpr h)
  have hubD : P.ρ P.b u * u⁻¹ ∈ P.D := P.hD u
  have hubU1 : P.ρ P.b u * u⁻¹ ∈ U1 := U1.mul_mem (h1 _ hbK' u hu) (U1.inv_mem hu)
  have hDU1 : P.D ≤ U1 := by
    rcases Q.D_irr (P.D ⊓ U1) inf_le_left
        (fun l hl d hd => ⟨Q.Dinv l hl d hd.1, hL1 l hl d hd.2⟩) with h | h
    · exfalso
      have hm : P.ρ P.b u * u⁻¹ ∈ P.D ⊓ U1 := ⟨hubD, hubU1⟩
      rw [h, Subgroup.mem_bot] at hm
      rw [hm] at hub
      exact hub U2.one_mem
    · rw [← h]
      exact inf_le_right
  have hDU2 : P.D ⊓ U2 = ⊥ := by
    rcases Q.D_irr (P.D ⊓ U2) inf_le_left
        (fun l hl d hd => ⟨Q.Dinv l hl d hd.1, hL2 l hl d hd.2⟩) with h | h
    · exact h
    · exfalso
      apply hub
      have hm : P.ρ P.b u * u⁻¹ ∈ P.D ⊓ U2 := by rw [h]; exact hubD
      exact hm.2
  refine ⟨hDU1, hDU2, ?_⟩
  let δ1 : ↥U1 →* W :=
    { toFun := fun x => P.ρ P.b x * (x : W)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, map_mul]
        rw [mul_inv, mul_mul_mul_comm] }
  have hδ1 : δ1.range = P.D := by
    have hle : δ1.range ≤ P.D := by rintro _ ⟨x, rfl⟩; exact P.hD x
    rcases Q.D_irr δ1.range hle (by
        rintro l hl _ ⟨x, rfl⟩
        refine ⟨⟨P.ρ l x, hL1 l hl x x.2⟩, ?_⟩
        show P.ρ P.b (P.ρ l x) * (P.ρ l x)⁻¹ = P.ρ l (P.ρ P.b x * (x : W)⁻¹)
        rw [map_mul, map_inv, hlb l hl]) with h | h
    · exfalso
      have hm : δ1 ⟨u, hu⟩ ∈ δ1.range := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot] at hm
      have hm' : P.ρ P.b u * u⁻¹ = 1 := hm
      rw [hm'] at hub
      exact hub U2.one_mem
    · exact h
  let δ : ChiefSec U1 U2 →* ChiefSec U1 U2 :=
    { toFun := fun w => v w * w⁻¹
      map_one' := by simp
      map_mul' := fun a c => by
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hker : δ.ker = fixV (Subgroup.zpowers v) := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixV]
    constructor
    · intro h x hx
      have hw : v w = w := by
        have : v w * w⁻¹ = 1 := h
        rwa [mul_inv_eq_one] at this
      have hst : v ∈ MulAction.stabilizer (MulAut (ChiefSec U1 U2)) w := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hw
      have := (Subgroup.zpowers_le.mpr hst) hx
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    · intro h
      show v w * w⁻¹ = 1
      rw [h v (Subgroup.mem_zpowers v), mul_inv_cancel]
  have hδq : ∀ x : ↥U1, δ (chiefQ U1 U2 x) = chiefQ U1 U2 ⟨δ1 x, U1.mul_mem
      (h1 _ hbK' x x.2) (U1.inv_mem x.2)⟩ := by
    intro x
    show v (chiefQ U1 U2 x) * (chiefQ U1 U2 x)⁻¹ = _
    rw [hv', secAct_chiefQ, ← map_inv, ← map_mul]
    rfl
  let f : ↥P.D → ↥δ.range := fun d =>
    ⟨chiefQ U1 U2 ⟨d, hDU1 d.2⟩, by
      have hd : (d : W) ∈ δ1.range := by rw [hδ1]; exact d.2
      obtain ⟨x, hx⟩ := hd
      refine ⟨chiefQ U1 U2 x, ?_⟩
      rw [hδq]
      congr 1
      exact Subtype.ext hx⟩
  have hf : Function.Bijective f := by
    constructor
    · intro d d' h
      have h' := congrArg Subtype.val h
      simp only [f] at h'
      rw [← div_eq_one, ← map_div, chiefQ_eq_one_iff] at h'
      have hmem : (d : W) * (d' : W)⁻¹ ∈ P.D ⊓ U2 :=
        ⟨P.D.mul_mem d.2 (P.D.inv_mem d'.2), by simpa [div_eq_mul_inv] using h'⟩
      rw [hDU2, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact Subtype.ext hmem
    · rintro ⟨_, w, rfl⟩
      obtain ⟨x, rfl⟩ := chiefQ_surjective U1 U2 w
      refine ⟨⟨δ1 x, by rw [← hδ1]; exact ⟨x, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [f]
      rw [hδq]
  have hidx : (fixV (Subgroup.zpowers v)).index = 4 := by
    rw [← hker, Subgroup.index_ker, ← Q.card_D]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  unfold rkIdx
  rw [hidx, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

end HypL1

end L1


section Main

variable {Y : Type} [Group Y] [Finite Y] {W : Type} [CommGroup W] [Finite W]

omit [Finite Y] in
theorem injective_toL (P : Hyp1321 Y W) (hZ : Subgroup.center ↥P.K = ⊥) {U1 U2 : Subgroup W}
    (h1 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U1, P.ρ y u ∈ U1)
    (h2 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U2, P.ρ y u ∈ U2)
    (hB4 : B4Hyp (secAct P.ρ _ h1 h2).range
      ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2))) :
    Function.Injective ((secAct P.ρ _ h1 h2).comp (Subgroup.inclusion le_sup_left :
      ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b))) := by
  set f := (secAct P.ρ _ h1 h2).comp (Subgroup.inclusion le_sup_left :
      ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b)) with hf
  rw [injective_iff_map_eq_one]
  intro k hk
  rcases CFSG.LocalCores.quasisimple_normal_subgroups P.quasi f.normal_ker with h | h
  · exfalso
    have hLbot : (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hy0 : (y : Y) ∈ P.K := hy
      have hy' : (⟨y, hy0⟩ : ↥P.K) ∈ f.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hy'
      rw [Subgroup.mem_bot]
      exact hy'
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hB4.2.2.1
    rw [hLbot] at hnt
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩, hac⟩ := hnt
    rw [Subgroup.mem_bot] at ha hc
    exact hac (Subtype.ext (ha.trans hc.symm))
  · have := h hk
    rw [hZ, Subgroup.mem_bot] at this
    exact this


@[expose] def Rows1321Final {V : Type} [CommGroup V] [Finite V] (G L A : Subgroup (MulAut V)) :
    Prop :=
  B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1 ∨ B42Case10 G L A ∨ G2Natural (ffJ G) ⊤ ⊥ 1 ∨
    G2NaturalDerived L ⊤ ⊥ 1

theorem lemma_13_5_21_main
    (P : Hyp1321 Y W) (QY : HypY P) (QL : HypL1 P) (hF : Facts1321)
    (hR : FactRankRows1321) (hA7 : FactA7Grp1321) (hL3 : FactL3Grp1321)
    (hO : FactOutRows1321) :
    Subgroup.center ↥P.K = ⊥ ∧ QL.L ≤ P.K ∧
      ∃ (U1 U2 : Subgroup W) (h1 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U1, P.ρ y u ∈ U1)
        (h2 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U2, P.ρ y u ∈ U2),
        U2 < U1 ∧ (∀ k ∈ P.K, ∀ u ∈ U2, P.ρ k u = u) ∧ commSubOf U1 (P.K.map P.ρ) = U1 ∧
        (∀ J : Subgroup W, (∀ k ∈ P.K, ∀ u ∈ J, P.ρ k u ∈ J) → U2 ≤ J → J ≤ U1 →
          J = U2 ∨ J = U1) ∧
        B4Hyp (secAct P.ρ _ h1 h2).range
          ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2)) ∧
        Cond1321 (secAct P.ρ _ h1 h2).range
          ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2))
          (secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩) ∧
        Function.Injective ((secAct P.ρ _ h1 h2).comp (Subgroup.inclusion le_sup_left :
          ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b))) ∧
        P.D ≤ U1 ∧ P.D ⊓ U2 = ⊥ ∧
        rkIdx (fixV (Subgroup.zpowers
          (secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩))) = 2 ∧
        ∃ A, Rows1321Final (secAct P.ρ _ h1 h2).range
          ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2)) A := by
  classical
  have hZ := P.center_eq_bot hF hR
  have hU0 : ∀ x ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ (⊤ : Subgroup W), P.ρ x u ∈ ⊤ :=
    fun _ _ _ _ => Subgroup.mem_top _
  have hU0K : ∃ k ∈ P.K, ∃ u ∈ (⊤ : Subgroup W), P.ρ k u ≠ u := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have : Nontrivial ↥P.K := CFSG.LocalCores.isQuasisimple_nontrivial P.quasi
    obtain ⟨k, hk1⟩ := exists_ne (1 : ↥P.K)
    apply hk1
    apply Subtype.ext
    apply P.inj
    ext w
    rw [Subgroup.coe_one, map_one, MulAut.one_apply]
    exact h k k.2 w (Subgroup.mem_top w)
  obtain ⟨U1, U2, h1, h2, hU21, -, hfix, hcomm, hirr, hB4, hc⟩ := P.chief hU0 hU0K
  have hsq := P.chiefSec_sq U1 U2
  have hout := rows1321 hF hsq hB4 hc
  set ψ := secAct P.ρ _ h1 h2 with hψ
  set L' := (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ with hL'
  set f := ψ.comp (Subgroup.inclusion le_sup_left : ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b))
    with hf
  have hinj := injective_toL P hZ h1 h2 hB4
  let πK : ↥P.K →* ↥L' := f.codRestrict L' (fun k => ⟨_, k.2, rfl⟩)
  have hπK : Function.Bijective πK := by
    refine ⟨fun a c h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  let e : ↥P.K ≃* ↥L' := MulEquiv.ofBijective πK hπK
  rcases hout with ⟨π7, hπ7⟩ | ⟨F, _, _, hF2, πs, hπs⟩ | ⟨A, hA⟩
  · exact (QY.not_A7 hA7 ⟨e.symm.toMonoidHom.comp π7, e.symm.surjective.comp hπ7⟩).elim
  · exact (QY.not_L3 hL3 ⟨F, inferInstance, inferInstance, hF2, e.symm.toMonoidHom.comp πs,
      e.symm.surjective.comp hπs⟩).elim
  obtain ⟨-, hrank3⟩ := hR _ hsq _ _ A hB4 hA
  have hrank : ∃ x ∈ P.K, ∃ c ∈ P.K, x ^ 3 = 1 ∧ c ^ 3 = 1 ∧ x * c = c * x ∧ x ≠ 1 ∧
      c ∉ Subgroup.zpowers x := by
    obtain ⟨E, hEL, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L'
    obtain ⟨x', hx', c', hc', hx3, hc3, hxc, hx1, hcx⟩ :=
      exists_two_of_card_nine hE (by
        rw [hEc]
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ CFSG.Open.pRank 3 L' := Nat.pow_le_pow_right (by norm_num) hrank3)
    refine ⟨(e.symm ⟨x', hEL hx'⟩ : Y), (e.symm ⟨x', hEL hx'⟩).2, (e.symm ⟨c', hEL hc'⟩ : Y),
      (e.symm ⟨c', hEL hc'⟩).2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.coe_pow, ← map_pow]
      have : (⟨x', hEL hx'⟩ : ↥L') ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one, Subgroup.coe_one]
    · rw [← Subgroup.coe_pow, ← map_pow]
      have : (⟨c', hEL hc'⟩ : ↥L') ^ 3 = 1 := Subtype.ext hc3
      rw [this, map_one, Subgroup.coe_one]
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
      have : (⟨x', hEL hx'⟩ : ↥L') * ⟨c', hEL hc'⟩ = ⟨c', hEL hc'⟩ * ⟨x', hEL hx'⟩ :=
        Subtype.ext hxc
      rw [this]
    · intro h
      apply hx1
      have h' : e.symm ⟨x', hEL hx'⟩ = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff] at h'
      exact congrArg Subtype.val h'
    · intro h
      apply hcx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
      refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
      have h' : (e.symm ⟨x', hEL hx'⟩) ^ i = e.symm ⟨c', hEL hc'⟩ := Subtype.ext (by
        rw [Subgroup.coe_zpow]; exact hi)
      rw [← map_zpow, e.symm.injective.eq_iff] at h'
      exact congrArg Subtype.val h'
  have hout' : ∀ α : MulAut ↥P.K, α ^ 3 = 1 → ∃ k : ↥P.K, α = MulAut.conj k := by
    intro α hα
    let α' : MulAut ↥L' := (e.symm.trans α).trans e
    have hpow : ∀ n : ℕ, ∀ x : ↥L', (α' ^ n) x = e ((α ^ n) (e.symm x)) := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
        simp [α']
    have hα' : α' ^ 3 = 1 := by
      ext x
      rw [hpow, hα, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]
    obtain ⟨l, hl⟩ := hO _ hsq _ _ A hB4 hA α' hα'
    refine ⟨e.symm l, ?_⟩
    ext x
    have h1 := congrArg (fun φ : MulAut ↥L' => e.symm (φ (e x))) hl
    simp only [α', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      map_mul, map_inv] at h1
    rw [h1, MulAut.conj_apply]
  have hLK := QL.le_K hZ hrank hout'
  obtain ⟨hDU1, hDU2, hrk⟩ := QL.rank_eq_two hLK h1 h2 hc.ne_one
  refine ⟨hZ, hLK, U1, U2, h1, h2, hU21, hfix, hcomm, hirr, hB4, hc, hinj, hDU1, hDU2, hrk, A, ?_⟩
  rcases hA with h6 | hSp | h9 | h10 | hG2 | hG2'
  · exact Or.inl h6
  · exact Or.inr (Or.inl hSp)
  · exfalso
    have h1' := hF.lnat _ hsq _ _ _ hB4 hc h9
    have h12 : (1 : ℕ) = 2 := h1'.symm.trans hrk
    omega
  · exact Or.inr (Or.inr (Or.inl h10))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hG2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hG2')))

end Main

end CFSG.Quasithin.H13.A5
