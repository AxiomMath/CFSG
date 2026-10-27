module

public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.A3StructureListNative

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.InternalSec
open scoped commutatorElement


section General

variable {X : Type*} [Group X]

theorem centralizes_of_comm_central_perfect {K : Subgroup X} [Group.IsPerfect ↥K] {b : X}
    (hbK : b ∈ Subgroup.normalizer (K : Set X))
    (hc : ∀ k ∈ K, ∀ k' ∈ K, k' * (b * k * b⁻¹ * k⁻¹) = (b * k * b⁻¹ * k⁻¹) * k') :
    ∀ k ∈ K, k * b = b * k := by
  have hz : ∀ a : ↥K, (⟨b * a * b⁻¹ * (a : X)⁻¹, K.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hbK a).mp a.2) (K.inv_mem a.2)⟩ : ↥K) ∈
      Subgroup.center ↥K := by
    intro a
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc a a.2 g g.2)
  have hconj : ∀ a : ↥K, b * a * b⁻¹ ∈ K := fun a => (Subgroup.mem_normalizer_iff.mp hbK a).mp a.2
  set Cb : Subgroup ↥K := (Subgroup.centralizer {b}).subgroupOf K with hCb
  have hle : commutator ↥K ≤ Cb := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ c _
    rw [hCb, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have e1 : (⟨b * a * b⁻¹, hconj a⟩ : ↥K) =
        a * (⟨b * a * b⁻¹ * (a : X)⁻¹, K.mul_mem (hconj a) (K.inv_mem a.2)⟩ : ↥K) := by
      rw [(Subgroup.mem_center_iff.mp (hz a) a)]
      exact Subtype.ext (by simp)
    have e2 : (⟨b * c * b⁻¹, hconj c⟩ : ↥K) =
        c * (⟨b * c * b⁻¹ * (c : X)⁻¹, K.mul_mem (hconj c) (K.inv_mem c.2)⟩ : ↥K) := by
      rw [(Subgroup.mem_center_iff.mp (hz c) c)]
      exact Subtype.ext (by simp)
    have h1 : ⁅(⟨b * a * b⁻¹, hconj a⟩ : ↥K), ⟨b * c * b⁻¹, hconj c⟩⁆ = ⁅a, c⁆ := by
      rw [e1, e2, commutatorElement_mul_center_left _ (hz a),
        commutatorElement_mul_center_right _ (hz c)]
    have h2 := congrArg Subtype.val h1
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h3 : b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) * b⁻¹ =
        (a : X) * c * (a : X)⁻¹ * (c : X)⁻¹ := by
      calc b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) * b⁻¹ =
          b * a * b⁻¹ * (b * c * b⁻¹) * (b * a * b⁻¹)⁻¹ * (b * c * b⁻¹)⁻¹ := by group
        _ = _ := h2
    show (a : X) * c * (a : X)⁻¹ * (c : X)⁻¹ * b = b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹)
    calc (a : X) * c * (a : X)⁻¹ * (c : X)⁻¹ * b =
        b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) * b⁻¹ * b := by rw [h3]
      _ = b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) := by group
  rw [Group.IsPerfect.commutator_eq_top] at hle
  intro k hk
  have := hle (Subgroup.mem_top (⟨k, hk⟩ : ↥K))
  rw [hCb, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem mem_or_mul_mem_of_mem_sup {K : Subgroup X} {b : X}
    (hbK : b ∈ Subgroup.normalizer (K : Set X)) (hb2 : b * b = 1) {y : X}
    (hy : y ∈ K ⊔ Subgroup.zpowers b) : y ∈ K ∨ y * b ∈ K := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  have hconj : ∀ z ∈ K, b * z * b⁻¹ ∈ K := fun z hz => (Subgroup.mem_normalizer_iff.mp hbK z).mp hz
  let S : Subgroup X :=
    { carrier := {y | y ∈ K ∨ y * b ∈ K}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        rintro y z (hy | hy) (hz | hz)
        · exact Or.inl (K.mul_mem hy hz)
        · right
          rw [mul_assoc]
          exact K.mul_mem hy hz
        · right
          have e : y * z * b = (y * b) * (b⁻¹ * z * b) := by group
          have h1 : b⁻¹ * z * b ∈ K := by
            have := hconj z hz
            rw [hbinv] at this ⊢
            exact this
          rw [e]
          exact K.mul_mem hy h1
        · left
          have e : y * z = (y * b) * (b⁻¹ * (z * b) * b⁻¹) := by group
          have h1 : b⁻¹ * (z * b) * b⁻¹ ∈ K := by
            have := hconj _ hz
            rw [hbinv] at this ⊢
            exact this
          rw [e]
          exact K.mul_mem hy h1
      inv_mem' := by
        rintro y (hy | hy)
        · exact Or.inl (K.inv_mem hy)
        · right
          have e : y⁻¹ * b = (b⁻¹ * (y * b) * b⁻¹)⁻¹ := by group
          have h1 : b⁻¹ * (y * b) * b⁻¹ ∈ K := by
            have := hconj _ hy
            rw [hbinv] at this ⊢
            exact this
          rw [e]
          exact K.inv_mem h1 }
  have hle : K ⊔ Subgroup.zpowers b ≤ S :=
    sup_le (fun k hk => Or.inl hk)
      (Subgroup.zpowers_le.mpr (Or.inr (by show b * b ∈ K; rw [hb2]; exact K.one_mem)))
  exact hle hy

theorem isSylowTwoOf_map {Y : Type*} [Group Y] {S K : Subgroup X} (hS : IsSylowTwoOf S K)
    (f : X →* Y) : IsSylowTwoOf (S.map f) (K.map f) := by
  obtain ⟨hSK, hp, hidx⟩ := hS
  refine ⟨Subgroup.map_mono hSK, ?_, fun h => hidx ?_⟩
  · exact hp.map f
  · let f' : ↥K →* ↥(K.map f) := (f.comp K.subtype).codRestrict (K.map f)
      (fun k => ⟨k, k.2, rfl⟩)
    have hf' : Function.Surjective f' := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    have he : (S.subgroupOf K).map f' = (S.map f).subgroupOf (K.map f) := by
      ext ⟨y, hy⟩
      rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨k, hk, hky⟩
        rw [Subgroup.mem_subgroupOf] at hk
        refine ⟨k, hk, ?_⟩
        exact congrArg Subtype.val hky
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hSK hs⟩, hs, rfl⟩
    have := Subgroup.index_map_dvd (S.subgroupOf K) hf'
    rw [he] at this
    exact h.trans this

end General

section Ranks

theorem rkIdx_fixV_le_two {V : Type*} [CommGroup V] [Finite V] {v : MulAut V}
    {D : Subgroup V} (hD : ∀ w : V, v w * w⁻¹ ∈ D) (hD4 : Nat.card D ≤ 4) :
    rkIdx (fixV (Subgroup.zpowers v)) ≤ 2 := by
  let δ : V →* V :=
    { toFun := fun w => v w * w⁻¹
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [map_mul, mul_inv_rev]
        simp only [mul_comm, mul_left_comm, mul_assoc] }
  have hker : δ.ker = fixV (Subgroup.zpowers v) := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixV]
    constructor
    · intro h x hx
      have hw : v w = w := by
        have : v w * w⁻¹ = 1 := h
        rwa [mul_inv_eq_one] at this
      have hst : v ∈ MulAction.stabilizer (MulAut V) w := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hw
      have := (Subgroup.zpowers_le.mpr hst) hx
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    · intro h
      show v w * w⁻¹ = 1
      rw [h v (Subgroup.mem_zpowers v), mul_inv_cancel]
  have hidx : (fixV (Subgroup.zpowers v)).index ≤ 4 := by
    rw [← hker, Subgroup.index_ker]
    have : δ.range ≤ D := by rintro _ ⟨w, rfl⟩; exact hD w
    exact (Subgroup.card_le_of_le this).trans hD4
  unfold rkIdx
  have hpos : (fixV (Subgroup.zpowers v)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := pow_padicValNat_dvd (p := 2) (n := (fixV (Subgroup.zpowers v)).index)
  have h2 : 2 ^ padicValNat 2 (fixV (Subgroup.zpowers v)).index ≤ 4 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h1).trans hidx
  by_contra hlt
  have h3 : 2 ^ 3 ≤ 2 ^ padicValNat 2 (fixV (Subgroup.zpowers v)).index :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Ranks

section SQTK

theorem sqtkGroup_of_surjective_quasisimple
    {P Q : Type} [Group P] [Group Q] [Finite P]
    [Finite Q] (hS : SQTKGroup P) (f : P →* Q) (hf : Function.Surjective f)
    (hQ : CFSG.IsQuasisimple Q) : SQTKGroup Q := by
  let e : P ⧸ f.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hE : CFSG.layer (P ⧸ f.ker) = ⊤ :=
    B5.layer_eq_top_of_quasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ)
  have hsqt := CFSG.SectionRank.sqt_quotient_of_catalog CFSG.SectionRank.oddKernelCentralization
    CFSG.SectionRank.catalogStepHyp hS.isSQTKCat f.ker hE
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp
      (CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hsqt),
    (hS.2.quotient f.ker).of_mulEquiv e.symm⟩

theorem sqtkGroup_of_mulEquiv {P Q : Type} [Group P] [Group Q] [Finite P] [Finite Q]
    (hS : SQTKGroup P) (e : P ≃* Q) : SQTKGroup Q := by
  refine ⟨fun p hp hp2 => ?_, hS.2.of_mulEquiv e.symm⟩
  show CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ 2
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact hS.1 p hp hp2

end SQTK

section Chief

variable {W : Type} [CommGroup W]

theorem le_stabSub_of_maps {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) : X ≤ stabSub U := by
  intro x hx u
  refine ⟨fun hu => ?_, h x hx u⟩
  have := h x⁻¹ (X.inv_mem hx) _ hu
  simpa using this

theorem fix_of_fix_comm {K : Subgroup (MulAut W)} [Group.IsPerfect ↥K] {U : Subgroup W}
    (h : ∀ k ∈ K, ∀ k' ∈ K, ∀ u ∈ U, k' (k u * u⁻¹) = k u * u⁻¹) :
    ∀ k ∈ K, ∀ u ∈ U, k u = u := by
  let δ : ↥K →* (↥U → W) :=
    { toFun := fun k u => (k : MulAut W) u * (u : W)⁻¹
      map_one' := by ext u; simp
      map_mul' := fun k k' => by
        ext u
        have h1 := h k' k'.2 k k.2 u u.2
        have e : (k : MulAut W) ((k' : MulAut W) u) =
            (k' : MulAut W) u * (u : W)⁻¹ * (k : MulAut W) u := by
          calc (k : MulAut W) ((k' : MulAut W) u) =
              (k : MulAut W) ((k' : MulAut W) u * (u : W)⁻¹ * u) := by rw [inv_mul_cancel_right]
            _ = _ := by rw [map_mul, h1]
        show (k : MulAut W) ((k' : MulAut W) u) * (u : W)⁻¹ =
          (k : MulAut W) u * (u : W)⁻¹ * ((k' : MulAut W) u * (u : W)⁻¹)
        rw [e]
        simp only [mul_comm, mul_left_comm] }
  intro k hk u hu
  have hker : (⟨k, hk⟩ : ↥K) ∈ δ.ker :=
    Abelianization.commutator_subset_ker δ (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  have := congrFun (MonoidHom.mem_ker.mp hker) ⟨u, hu⟩
  simpa [δ, mul_inv_eq_one] using this

@[expose] def commSubOf (U : Subgroup W) (K : Subgroup (MulAut W)) : Subgroup W :=
  Subgroup.closure {w | ∃ k ∈ K, ∃ u ∈ U, k u * u⁻¹ = w}

theorem commSubOf_le {U : Subgroup W} {K : Subgroup (MulAut W)} (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) :
    commSubOf U K ≤ U := by
  rw [commSubOf, Subgroup.closure_le]
  rintro _ ⟨k, hk, u, hu, rfl⟩
  exact U.mul_mem (hKU k hk u hu) (U.inv_mem hu)

theorem mem_commSubOf {U : Subgroup W} {K : Subgroup (MulAut W)} {k : MulAut W} (hk : k ∈ K)
    {u : W} (hu : u ∈ U) : k u * u⁻¹ ∈ commSubOf U K :=
  Subgroup.subset_closure ⟨k, hk, u, hu, rfl⟩

theorem maps_commSubOf {U : Subgroup W} {K : Subgroup (MulAut W)} {x : MulAut W}
    (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hxU : ∀ u ∈ U, x u ∈ U) :
    ∀ w ∈ commSubOf U K, x w ∈ commSubOf U K := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨k, hk, u, hu, rfl⟩ := hw
    have e : x (k u * u⁻¹) = (x * k * x⁻¹) (x u) * (x u)⁻¹ := by
      simp [map_mul, map_inv]
    rw [e]
    exact mem_commSubOf (hxK k hk) (hxU u hu)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

variable [Finite W]

theorem exists_chief {X K : Subgroup (MulAut W)} [Group.IsPerfect ↥K] (hKX : K ≤ X)
    (hKn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) {U0 : Subgroup W}
    (hU0 : ∀ x ∈ X, ∀ u ∈ U0, x u ∈ U0) (hU0K : ¬ U0 ≤ fixV K) :
    ∃ U1 U2 : Subgroup W, U2 < U1 ∧ U1 ≤ U0 ∧ (∀ x ∈ X, ∀ u ∈ U1, x u ∈ U1) ∧
      (∀ x ∈ X, ∀ u ∈ U2, x u ∈ U2) ∧ commSubOf U1 K = U1 ∧ U2 ≤ fixV K ∧
      ∀ J : Subgroup W, (∀ x ∈ X, ∀ u ∈ J, x u ∈ J) → U2 ≤ J → J ≤ U1 → J = U2 ∨ J = U1 := by
  classical
  let P : Subgroup W → Prop := fun U => U ≤ U0 ∧ (∀ x ∈ X, ∀ u ∈ U, x u ∈ U) ∧ ¬ U ≤ fixV K
  have hP : ∃ n, ∃ U, P U ∧ Nat.card U = n := ⟨_, U0, ⟨le_rfl, hU0, hU0K⟩, rfl⟩
  obtain ⟨U1, hU1, hc1⟩ := Nat.find_spec hP
  have hmin : ∀ U, P U → Nat.card U1 ≤ Nat.card U := fun U hU => by
    rw [hc1]; exact Nat.find_min' hP ⟨U, hU, rfl⟩
  obtain ⟨hU1U0, hU1X, hU1K⟩ := hU1
  have hle : commSubOf U1 K ≤ U1 := commSubOf_le fun k hk u hu => hU1X k (hKX hk) u hu
  have hcomm : commSubOf U1 K = U1 := by
    by_contra hne
    have hlt : commSubOf U1 K < U1 := lt_of_le_of_ne hle hne
    have hfix : commSubOf U1 K ≤ fixV K := by
      by_contra hnf
      have := hmin _ ⟨hle.trans hU1U0, fun x hx => maps_commSubOf (hKn x hx) (hU1X x hx), hnf⟩
      exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr this)
    apply hU1K
    intro u hu k hk
    exact fix_of_fix_comm (fun k hk k' hk' u hu => hfix (mem_commSubOf hk hu) k' hk') k hk u hu
  have hU1bot : ⊥ < U1 := by
    refine bot_lt_iff_ne_bot.mpr fun h => hU1K ?_
    rw [h]
    exact bot_le
  let Q : ℕ → Prop := fun n => ∃ J : Subgroup W, J < U1 ∧ (∀ x ∈ X, ∀ u ∈ J, x u ∈ J) ∧
    Nat.card J = n
  have hQ1 : Q 1 := ⟨⊥, hU1bot, fun x _ u hu => by
    rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one], Subgroup.card_bot⟩
  have hb : 1 ≤ Nat.card W := Nat.card_pos
  obtain ⟨U2, hU21, hU2X, hc2⟩ := Nat.findGreatest_spec hb hQ1
  have hmax : ∀ J : Subgroup W, J < U1 → (∀ x ∈ X, ∀ u ∈ J, x u ∈ J) →
      Nat.card J ≤ Nat.card U2 := by
    intro J hJ hJX
    rw [hc2]
    by_contra hlt
    exact Nat.findGreatest_is_greatest (not_le.mp hlt) (Subgroup.card_le_card_group J)
      ⟨J, hJ, hJX, rfl⟩
  refine ⟨U1, U2, hU21, hU1U0, hU1X, hU2X, hcomm, ?_, ?_⟩
  ·
    by_contra hnf
    have := hmin U2 ⟨hU21.le.trans hU1U0, hU2X, hnf⟩
    exact absurd (Subgroup.card_lt_of_lt hU21) (not_lt.mpr this)
  · intro J hJX hU2J hJU1
    by_cases hJ : J = U1
    · exact Or.inr hJ
    · left
      have hJlt : J < U1 := lt_of_le_of_ne hJU1 hJ
      exact (Subgroup.eq_of_le_of_card_ge hU2J (hmax J hJlt hJX)).symm

omit [Finite W] in
theorem mem_stabSub_of_involution {b : MulAut W} (hb2 : b * b = 1) {S : Subgroup W}
    (h : ∀ u ∈ S, b u ∈ S) : b ∈ stabSub S := by
  intro u
  refine ⟨fun hu => ?_, h u⟩
  have e : b (b u) = u := by rw [← MulAut.mul_apply, hb2, MulAut.one_apply]
  rw [← e]
  exact h _ hu

theorem isSolvable_mulAut_of_card_le_four {M : Type*} [Group M] [Finite M]
    (h : Nat.card M ≤ 4) : Group.IsSolvable (MulAut M) := by
  have := Equiv.Perm.isSolvable h
  refine Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm M) fun a b hab => ?_
  ext x
  exact congrFun (congrArg (⇑) hab) x

theorem eq_one_of_perfect_of_solvable {K M : Type*} [Group K] [Group M] [Group.IsPerfect K]
    [Group.IsSolvable M] (f : K →* M) (k : K) : f k = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (⟨f k, k, rfl⟩ : f.range) 1)

theorem irr_of_chief {X K : Subgroup (MulAut W)} [Group.IsPerfect ↥K] (hKX : K ≤ X)
    (hKn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) {b : MulAut W} (hbX : b ∈ X) (hb2 : b * b = 1)
    (hX : X ≤ K ⊔ Subgroup.zpowers b) {D : Subgroup W} (hD : ∀ w : W, b w * w⁻¹ ∈ D)
    (hD4 : Nat.card D ≤ 4) {U1 U2 : Subgroup W} (hU21 : U2 < U1)
    (hU1X : ∀ x ∈ X, ∀ u ∈ U1, x u ∈ U1) (hU2X : ∀ x ∈ X, ∀ u ∈ U2, x u ∈ U2)
    (hcomm : commSubOf U1 K = U1)
    (hirrX : ∀ J : Subgroup W, (∀ x ∈ X, ∀ u ∈ J, x u ∈ J) → U2 ≤ J → J ≤ U1 → J = U2 ∨ J = U1)
    (J : Subgroup W) (hJK : ∀ k ∈ K, ∀ u ∈ J, k u ∈ J) (hU2J : U2 ≤ J) (hJU1 : J ≤ U1) :
    J = U2 ∨ J = U1 := by
  classical
  by_contra hne
  simp only [not_or] at hne
  have hbb : ∀ w : W, b (b w) = w := fun w => by
    rw [← MulAut.mul_apply, hb2, MulAut.one_apply]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  let P : ℕ → Prop := fun n => ∃ J1 : Subgroup W, (∀ k ∈ K, ∀ u ∈ J1, k u ∈ J1) ∧ U2 < J1 ∧
    J1 ≤ U1 ∧ Nat.card J1 = n
  have hP : ∃ n, P n := ⟨_, J, hJK, lt_of_le_of_ne hU2J (Ne.symm hne.1), hJU1, rfl⟩
  obtain ⟨J1, hJ1K, hU2J1, hJ1U1, hc⟩ := Nat.find_spec hP
  have hmin : ∀ J' : Subgroup W, (∀ k ∈ K, ∀ u ∈ J', k u ∈ J') → U2 < J' → J' ≤ U1 →
      Nat.card J1 ≤ Nat.card J' := fun J' h1 h2 h3 => by
    rw [hc]; exact Nat.find_min' hP ⟨J', h1, h2, h3, rfl⟩
  have hJ1lt : J1 < U1 := by
    refine lt_of_le_of_ne hJ1U1 fun h => ?_
    have h1 := hmin J hJK (lt_of_le_of_ne hU2J (Ne.symm hne.1)) hJU1
    rw [h] at h1
    exact absurd (Subgroup.card_lt_of_lt (lt_of_le_of_ne hJU1 hne.2)) (not_lt.mpr h1)
  set J1' : Subgroup W := J1.comap b.toMonoidHom with hJ1'
  have hmemJ1' : ∀ w, w ∈ J1' ↔ b w ∈ J1 := fun w => Iff.rfl
  have hJ1'K : ∀ k ∈ K, ∀ u ∈ J1', k u ∈ J1' := by
    intro k hk u hu
    rw [hmemJ1'] at hu ⊢
    have e : b (k u) = (b * k * b⁻¹) (b u) := by simp [MulAut.mul_apply]
    rw [e]
    exact hJ1K _ (hKn b hbX k hk) _ hu
  have hbJ1 : ∀ u ∈ J1, b u ∈ J1' := fun u hu => by rw [hmemJ1', hbb]; exact hu
  have hbJ1' : ∀ u ∈ J1', b u ∈ J1 := fun u hu => hu
  have hU2J1' : U2 ≤ J1' := fun u hu => hU2J1.le (hU2X b hbX u hu)
  have hJ1'U1 : J1' ≤ U1 := fun u hu => by
    rw [← hbb u]; exact hU1X b hbX _ (hJ1U1 hu)
  have hXinv : ∀ S : Subgroup W, (∀ k ∈ K, ∀ u ∈ S, k u ∈ S) → (∀ u ∈ S, b u ∈ S) →
      ∀ x ∈ X, ∀ u ∈ S, x u ∈ S := by
    intro S hSK hSb x hx u hu
    have hle : K ⊔ Subgroup.zpowers b ≤ stabSub S :=
      sup_le (le_stabSub_of_maps hSK)
        (Subgroup.zpowers_le.mpr (mem_stabSub_of_involution hb2 hSb))
    exact (hle (hX hx) u).mpr hu
  have hsup : J1 ⊔ J1' = U1 := by
    have hinv := hXinv (J1 ⊔ J1') (fun k hk u hu => by
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
        rw [map_mul]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hJ1K k hk y hy))
          (Subgroup.mem_sup_right (hJ1'K k hk z hz)))
      (fun u hu => by
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
        rw [map_mul]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hbJ1 y hy))
          (Subgroup.mem_sup_left (hbJ1' z hz)))
    rcases hirrX _ hinv (hU2J1.le.trans le_sup_left) (sup_le hJ1U1 hJ1'U1) with h | h
    · exact absurd (lt_of_lt_of_le hU2J1 (h ▸ (le_sup_left : J1 ≤ J1 ⊔ J1'))) (lt_irrefl _)
    · exact h
  have hinf : J1 ⊓ J1' = U2 := by
    have hinv := hXinv (J1 ⊓ J1') (fun k hk u hu => ⟨hJ1K k hk u hu.1, hJ1'K k hk u hu.2⟩)
      (fun u hu => ⟨hbJ1' u hu.2, hbJ1 u hu.1⟩)
    rcases hirrX _ hinv (le_inf hU2J1.le hU2J1') (inf_le_left.trans hJ1U1) with h | h
    · exact h
    · exact absurd (lt_of_lt_of_le hJ1lt (h ▸ (inf_le_left : J1 ⊓ J1' ≤ J1))) (lt_irrefl _)
  let δ : ↥J1 →* ↥D :=
    { toFun := fun j => ⟨b j * (j : W)⁻¹, hD j⟩
      map_one' := by ext; simp
      map_mul' := fun j j' => by
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        simp only [mul_comm, mul_left_comm, mul_assoc] }
  have hker : δ.ker ≤ U2.subgroupOf J1 := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hj' : b j = j := by
      have := congrArg Subtype.val hj
      simpa [δ, mul_inv_eq_one] using this
    rw [Subgroup.mem_subgroupOf, ← hinf]
    refine ⟨j.2, ?_⟩
    show (j : W) ∈ J1'
    rw [hmemJ1', hj']
    exact j.2
  have hcard : Nat.card (Sec J1 U2) ≤ 4 := by
    have h1 : Nat.card (Sec J1 U2) = (U2.subgroupOf J1).index := (Subgroup.index_eq_card _).symm
    rw [h1]
    refine (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)).trans ?_
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans hD4
  have hKJ1 : K ≤ stabSub J1 := le_stabSub_of_maps hJ1K
  have hKU2 : K ≤ stabSub U2 := le_stabSub_of_maps fun k hk => hU2X k (hKX hk)
  have := isSolvable_mulAut_of_card_le_four hcard
  have htriv : ∀ k ∈ K, ∀ w ∈ J1, k w * w⁻¹ ∈ U2 := by
    intro k hk w hw
    have h1 := eq_one_of_perfect_of_solvable (B5.secHom K hKJ1 hKU2) ⟨k, hk⟩
    have h2 := ((B5.mem_ker_secHom K hKJ1 hKU2 ⟨k, hk⟩).mp h1).2 w hw
    exact h2
  have htriv' : ∀ k ∈ K, ∀ w ∈ J1', k w * w⁻¹ ∈ U2 := by
    intro k hk w hw
    have hw' : b w ∈ J1 := hw
    have h1 := htriv _ (hKn b hbX k hk) _ hw'
    have e : (b * k * b⁻¹) (b w) * (b w)⁻¹ = b (k w * w⁻¹) := by
      simp [MulAut.mul_apply, hbinv, hbb]
    rw [e] at h1
    have := hU2X b hbX _ h1
    rwa [hbb] at this
  have hle : U1 ≤ U2 := by
    rw [← hcomm, commSubOf, Subgroup.closure_le]
    rintro _ ⟨k, hk, u, hu, rfl⟩
    rw [← hsup] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    have e : k (y * z) * (y * z)⁻¹ = (k y * y⁻¹) * (k z * z⁻¹) := by
      rw [map_mul]; simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    rw [e]
    exact U2.mul_mem (htriv k hk y hy) (htriv' k hk z hz)
  exact absurd (lt_of_lt_of_le hU21 hle) (lt_irrefl _)

theorem pCore_two_eq_bot_of_surjective {P Q : Type*} [Group P] [Group Q] [Finite P]
    (hP : CFSG.IsQuasisimple P) (hO : CFSG.Open.pCore 2 P = ⊥) (f : P →* Q)
    (hf : Function.Surjective f) : CFSG.Open.pCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective f hf
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hNn : ((CFSG.Open.pCore 2 Q).comap f).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal 2).comap f
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hP hNn with hN | hN
  ·
    have hQ2 : IsPGroup 2 Q := by
      intro q
      obtain ⟨x, rfl⟩ := hf q
      have hx : x ∈ (CFSG.Open.pCore 2 Q).comap f := hN ▸ Subgroup.mem_top x
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := Q) ⟨f x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Group.IsPerfect P := hP.1
    have : Group.IsPerfect Q := Group.IsPerfect.ofSurjective hf
    by_contra hy1
    have : Nontrivial Q := ⟨⟨y, 1, hy1⟩⟩
    exact Group.IsPerfect.not_isNilpotent Q hQ2.isNilpotent
  · obtain ⟨x, rfl⟩ := hf y
    have hxZ : x ∈ Subgroup.center P := hN hy
    obtain ⟨k, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hxm1 : x ^ m = 1 := by
      have hz : x ^ m ∈ Subgroup.center P := Subgroup.pow_mem _ hxZ m
      have hp : IsPGroup 2 (Subgroup.zpowers (x ^ m)) := by
        rintro ⟨g, hg⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        refine ⟨k, Subtype.ext ?_⟩
        show ((x ^ m) ^ i) ^ 2 ^ k = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
          mul_comm, ← hxm, pow_orderOf_eq_one, one_zpow]
      have hnorm : (Subgroup.zpowers (x ^ m)).Normal := ⟨fun n hn g => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
        have hc := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hz i) g
        rw [hc, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers _ i⟩
      have := CFSG.LieType.BorelTits.le_pCore 2 hnorm hp (Subgroup.mem_zpowers (x ^ m))
      rw [hO, Subgroup.mem_bot] at this
      exact this
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := Q) ⟨f x, hy⟩
    have h1 : f x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h2 : f x ^ m = 1 := by rw [← map_pow, hxm1, map_one]
    have h3 : orderOf (f x) ∣ Nat.gcd (2 ^ j) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    have h4 : Nat.gcd (2 ^ j) m = 1 :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3

@[expose] noncomputable def resTo (K : Subgroup (MulAut W)) (U : Subgroup W)
    (hK : K ≤ stabSub U) : ↥K →* ↥(autSub K U) :=
  ((resHom U).comp (Subgroup.inclusion hK)).codRestrict (autSub K U)
    (fun k => mem_autSub.mpr ⟨⟨k, hK k.2⟩, k.2, rfl⟩)

omit [Finite W] in
theorem resTo_apply {K : Subgroup (MulAut W)} {U : Subgroup W} (hK : K ≤ stabSub U) (k : ↥K)
    (u : ↥U) : (((resTo K U hK k : ↥(autSub K U)) : MulAut ↥U) u : W) = (k : MulAut W) u := rfl

omit [Finite W] in
theorem resTo_surjective {K : Subgroup (MulAut W)} {U : Subgroup W} (hK : K ≤ stabSub U) :
    Function.Surjective (resTo K U hK) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  exact ⟨⟨g, hg⟩, rfl⟩

theorem qsec_of_chief {X K : Subgroup (MulAut W)} (hKX : K ≤ X)
    (hKn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hK : CFSG.IsQuasisimple ↥K) (hO : CFSG.Open.pCore 2 ↥K = ⊥) (hW : ∀ w : W, w ^ 2 = 1)
    {U1 U2 : Subgroup W} (hU21 : U2 < U1)
    (hU1X : ∀ x ∈ X, ∀ u ∈ U1, x u ∈ U1) (hU2X : ∀ x ∈ X, ∀ u ∈ U2, x u ∈ U2)
    (hcomm : commSubOf U1 K = U1) (hfix : U2 ≤ fixV K)
    (hirr : ∀ J : Subgroup W, (∀ k ∈ K, ∀ u ∈ J, k u ∈ J) → U2 ≤ J → J ≤ U1 →
      J = U2 ∨ J = U1) :
    QSec (autSub X U1) (autSub K U1) (U2.subgroupOf U1) := by
  have hXU1 : X ≤ stabSub U1 := le_stabSub_of_maps hU1X
  have hKU1 : K ≤ stabSub U1 := hKX.trans hXU1
  have hU1ne : ∃ u ∈ U1, u ∉ U2 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact absurd (lt_of_lt_of_le hU21 (fun u hu => h u hu)) (lt_irrefl _)
  have hker : (resTo K U1 hKU1).ker ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK (resTo K U1 hKU1).normal_ker with
      h | h
    · exfalso
      obtain ⟨u, hu, hu2⟩ := hU1ne
      apply hu2
      have hU1bot : U1 ≤ ⊥ := by
        rw [← hcomm, commSubOf, Subgroup.closure_le]
        rintro _ ⟨k, hk, u', hu', rfl⟩
        have hk1 : (⟨k, hk⟩ : ↥K) ∈ (resTo K U1 hKU1).ker := h ▸ Subgroup.mem_top _
        have := congrArg (fun φ : ↥(autSub K U1) => (((φ : MulAut ↥U1) ⟨u', hu'⟩ : ↥U1) : W))
          (MonoidHom.mem_ker.mp hk1)
        simp only [resTo_apply] at this
        show k u' * u'⁻¹ ∈ (⊥ : Subgroup W)
        rw [Subgroup.mem_bot, this]
        simp
      rw [Subgroup.mem_bot.mp (hU1bot hu)]
      exact U2.one_mem
    · exact h
  have hq : CFSG.IsQuasisimple ↥(autSub K U1) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hK _ (resTo_surjective hKU1) hker
  have hO1 : CFSG.Open.pCore 2 ↥(autSub K U1) = ⊥ :=
    pCore_two_eq_bot_of_surjective hK hO _ (resTo_surjective hKU1)
  have hstab : autSub X U1 ≤ stabSub (U2.subgroupOf U1) :=
    autSub_le_stabSub_subgroupOf (le_stabSub_of_maps hU2X)
  have hfix1 : U2.subgroupOf U1 ≤ fixV (autSub K U1) := by
    intro c hc φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact Subtype.ext (hfix hc g hg)
  refine ⟨autSub_mono hKX U1, ?_, ?_, hstab, hfix1, ?_, ?_, ?_, ?_, hq⟩
  ·
    intro x hx k hk
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    obtain ⟨h, hh, rfl⟩ := mem_autSub.mp hk
    refine mem_autSub.mpr ⟨g * h * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    simpa using hKn _ hg _ hh
  ·
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    obtain ⟨e, he⟩ := h2 _ hg
    exact ⟨e, mem_autSub.mpr ⟨g ^ 2 ^ e, by simpa using he, by rw [map_pow]⟩⟩
  ·
    rw [eq_top_iff]
    rintro ⟨u, hu⟩ -
    have hu' : u ∈ commSubOf U1 K := hcomm.symm ▸ hu
    have key : ∀ (w : W) (hw : w ∈ commSubOf U1 K), ∀ h : w ∈ U1,
        (⟨w, h⟩ : ↥U1) ∈ commV (autSub K U1) := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨k, hk, u', hu', rfl⟩ := hw
        intro h
        refine Subgroup.subset_closure ⟨resTo K U1 hKU1 ⟨k, hk⟩, (resTo K U1 hKU1 ⟨k, hk⟩).2,
          ⟨u', hu'⟩, ?_⟩
        exact Subtype.ext (by simp [resTo_apply])
      | one => intro h; exact Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
        intro h
        have := Subgroup.mul_mem _ (iha (hcomm ▸ ha)) (ihb (hcomm ▸ hb))
        exact this
      | inv a ha iha =>
        intro h
        exact Subgroup.inv_mem _ (iha (hcomm ▸ ha))
    exact key u hu' hu
  ·
    rw [lt_top_iff_ne_top]
    intro h
    obtain ⟨u, hu, hu2⟩ := hU1ne
    have : (⟨u, hu⟩ : ↥U1) ∈ U2.subgroupOf U1 := h ▸ Subgroup.mem_top _
    exact hu2 this
  ·
    intro J hCJ hJinv
    set J' : Subgroup W := J.map U1.subtype with hJ'
    have hU2J' : U2 ≤ J' := by
      intro u hu
      have hu1 : u ∈ U1 := hU21.le hu
      exact ⟨⟨u, hu1⟩, hCJ (show (⟨u, hu1⟩ : ↥U1) ∈ U2.subgroupOf U1 from hu), rfl⟩
    have hJ'U1 : J' ≤ U1 := Subgroup.map_subtype_le J
    have hJ'K : ∀ k ∈ K, ∀ u ∈ J', k u ∈ J' := by
      rintro k hk _ ⟨j, hj, rfl⟩
      exact ⟨_, hJinv _ (resTo K U1 hKU1 ⟨k, hk⟩).2 j hj, rfl⟩
    rcases hirr J' hJ'K hU2J' hJ'U1 with h | h
    · left
      ext j
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hj
        have : (j : W) ∈ J' := ⟨j, hj, rfl⟩
        rwa [h] at this
      · intro hj
        have : (j : W) ∈ J' := by rw [h]; exact hj
        obtain ⟨j', hj', hjj⟩ := this
        rwa [Subtype.ext hjj] at hj'
    · right
      rw [eq_top_iff]
      intro j _
      have : (j : W) ∈ J' := by rw [h]; exact j.2
      obtain ⟨j', hj', hjj⟩ := this
      rwa [Subtype.ext hjj] at hj'
  ·
    have hV : ∀ v : ↥U1, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW v)
    refine inf_centSec_eq_bot_of_pCoreOf hV (fun φ hφ => hstab (autSub_mono hKX U1 hφ)) hfix1 ?_
    rw [pCoreOf, hO1, Subgroup.map_bot]

abbrev ChiefSec (U1 U2 : Subgroup W) : Type :=
  Sec (⊤ : Subgroup ↥U1) (U2.subgroupOf U1)

@[expose] noncomputable def chiefQ (U1 U2 : Subgroup W) : ↥U1 →* ChiefSec U1 U2 :=
  (QuotientGroup.mk' _).comp (Subgroup.topEquiv (G := ↥U1)).symm.toMonoidHom

omit [Finite W] in
theorem chiefQ_surjective (U1 U2 : Subgroup W) : Function.Surjective (chiefQ U1 U2) := by
  intro y
  obtain ⟨⟨u, -⟩, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨u, rfl⟩

omit [Finite W] in
theorem chiefQ_eq_one_iff {U1 U2 : Subgroup W} (u : ↥U1) :
    chiefQ U1 U2 u = 1 ↔ (u : W) ∈ U2 := by
  show (QuotientGroup.mk (⟨u, trivial⟩ : ↥(⊤ : Subgroup ↥U1)) : ChiefSec U1 U2) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]

@[expose] noncomputable def chiefHom {X : Subgroup (MulAut W)} {U1 U2 : Subgroup W}
    (hX1 : X ≤ stabSub U1) (hX2 : X ≤ stabSub U2) : ↥X →* MulAut (ChiefSec U1 U2) :=
  (B5.secHom (autSub X U1) (le_stabSub_top _) (autSub_le_stabSub_subgroupOf hX2)).comp
    (resTo X U1 hX1)

omit [Finite W] in
theorem chiefHom_chiefQ {X : Subgroup (MulAut W)} {U1 U2 : Subgroup W} (hX1 : X ≤ stabSub U1)
    (hX2 : X ≤ stabSub U2) (x : ↥X) (u : ↥U1) :
    chiefHom hX1 hX2 x (chiefQ U1 U2 u) =
      chiefQ U1 U2 ⟨(x : MulAut W) u, ((hX1 x.2) u).2 u.2⟩ := rfl

omit [Finite W] in
theorem chiefHom_eq_one_iff {X : Subgroup (MulAut W)} {U1 U2 : Subgroup W}
    (hX1 : X ≤ stabSub U1) (hX2 : X ≤ stabSub U2) (x : ↥X) :
    chiefHom hX1 hX2 x = 1 ↔ ∀ u ∈ U1, (x : MulAut W) u * u⁻¹ ∈ U2 := by
  constructor
  · intro h u hu
    have := congrArg (fun φ : MulAut (ChiefSec U1 U2) => φ (chiefQ U1 U2 ⟨u, hu⟩)) h
    simp only [chiefHom_chiefQ, MulAut.one_apply] at this
    rw [← div_eq_one, ← map_div, chiefQ_eq_one_iff] at this
    simpa [div_eq_mul_inv] using this
  · intro h
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, rfl⟩ := chiefQ_surjective U1 U2 y
    rw [chiefHom_chiefQ, MulAut.one_apply, ← div_eq_one, ← map_div, chiefQ_eq_one_iff]
    simpa [div_eq_mul_inv] using h u u.2

omit [Finite W] in
theorem range_chiefHom {X : Subgroup (MulAut W)} {U1 U2 : Subgroup W} (hX1 : X ≤ stabSub U1)
    (hX2 : X ≤ stabSub U2) :
    (chiefHom hX1 hX2).range = autSec (autSub X U1) ⊤ (U2.subgroupOf U1) := by
  rw [chiefHom, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (resTo_surjective hX1),
    ← MonoidHom.range_eq_map, B5.range_secHom]

omit [Finite W] in
theorem map_chiefHom {X K : Subgroup (MulAut W)} (hKX : K ≤ X) {U1 U2 : Subgroup W}
    (hX1 : X ≤ stabSub U1) (hX2 : X ≤ stabSub U2) :
    (K.subgroupOf X).map (chiefHom hX1 hX2) = autSec (autSub K U1) ⊤ (U2.subgroupOf U1) := by
  have h1 : (K.subgroupOf X).map (resTo X U1 hX1) = (autSub K U1).subgroupOf (autSub X U1) := by
    ext φ
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_autSub.mpr ⟨⟨x, hX1 x.2⟩, hx, rfl⟩
    · intro hφ
      obtain ⟨g, hg, hgφ⟩ := mem_autSub.mp hφ
      exact ⟨⟨g, hKX hg⟩, hg, Subtype.ext hgφ⟩
  rw [chiefHom, ← Subgroup.map_map, h1]
  exact B5.map_secHom_eq_autSec _ _ _ (autSub_mono hKX U1)

end Chief

section Main

variable {W : Type} [CommGroup W] [Finite W] {Y : Type} [Group Y] [Finite Y]

omit [Finite W] [Finite Y] in
theorem map_le_stabSub (ρ : Y →* MulAut W) {K' : Subgroup Y} {U : Subgroup W}
    (h : ∀ y ∈ K', ∀ u ∈ U, ρ y u ∈ U) : K'.map ρ ≤ stabSub U :=
  le_stabSub_of_maps (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

@[expose] noncomputable def secAct (ρ : Y →* MulAut W) (K' : Subgroup Y) {U1 U2 : Subgroup W}
    (h1 : ∀ y ∈ K', ∀ u ∈ U1, ρ y u ∈ U1) (h2 : ∀ y ∈ K', ∀ u ∈ U2, ρ y u ∈ U2) :
    ↥K' →* MulAut (ChiefSec U1 U2) :=
  (chiefHom (map_le_stabSub ρ h1) (map_le_stabSub ρ h2)).comp
    ((ρ.comp K'.subtype).codRestrict (K'.map ρ) (fun y => ⟨y, y.2, rfl⟩))

omit [Finite W] [Finite Y] in
theorem secAct_chiefQ (ρ : Y →* MulAut W) (K' : Subgroup Y) {U1 U2 : Subgroup W}
    (h1 : ∀ y ∈ K', ∀ u ∈ U1, ρ y u ∈ U1) (h2 : ∀ y ∈ K', ∀ u ∈ U2, ρ y u ∈ U2) (y : ↥K')
    (u : ↥U1) : secAct ρ K' h1 h2 y (chiefQ U1 U2 u) = chiefQ U1 U2 ⟨ρ y u, h1 y y.2 u u.2⟩ :=
  rfl

omit [Finite W] [Finite Y] in
theorem secAct_eq_one_iff (ρ : Y →* MulAut W) (K' : Subgroup Y) {U1 U2 : Subgroup W}
    (h1 : ∀ y ∈ K', ∀ u ∈ U1, ρ y u ∈ U1) (h2 : ∀ y ∈ K', ∀ u ∈ U2, ρ y u ∈ U2) (y : ↥K') :
    secAct ρ K' h1 h2 y = 1 ↔ ∀ u ∈ U1, ρ y u * u⁻¹ ∈ U2 :=
  chiefHom_eq_one_iff (map_le_stabSub ρ h1) (map_le_stabSub ρ h2) _

theorem exists_chief_b4
    (ρ : Y →* MulAut W) (hρ : Function.Injective ρ)
    (hW : ∀ w : W, w ^ 2 = 1) {K : Subgroup Y} (hK : CFSG.IsQuasisimple ↥K)
    (hO : CFSG.Open.pCore 2 ↥K = ⊥) (hSK : SQTKGroup ↥K) {b : Y} (hb2 : b * b = 1)
    (hbK : b ∈ Subgroup.normalizer (K : Set Y)) (hbc : ∃ k ∈ K, k * b ≠ b * k)
    {D : Subgroup W} (hD : ∀ w : W, ρ b w * w⁻¹ ∈ D) (hD4 : Nat.card D ≤ 4)
    (hsyl : ∃ S : Subgroup Y, IsSylowTwoOf S K ∧ ∀ s ∈ S, s * b = b * s)
    (hpair : ∀ x ∈ K ⊔ Subgroup.zpowers b,
      (∃ k : ℕ, (b * (x * b * x⁻¹)) ^ 2 ^ k = 1) ∨ (b * (x * b * x⁻¹)) ^ 3 = 1)
    {U0 : Subgroup W} (hU0 : ∀ x ∈ K ⊔ Subgroup.zpowers b, ∀ u ∈ U0, ρ x u ∈ U0)
    (hU0K : ∃ k ∈ K, ∃ u ∈ U0, ρ k u ≠ u) :
    ∃ (U1 U2 : Subgroup W) (h1 : ∀ y ∈ K ⊔ Subgroup.zpowers b, ∀ u ∈ U1, ρ y u ∈ U1)
      (h2 : ∀ y ∈ K ⊔ Subgroup.zpowers b, ∀ u ∈ U2, ρ y u ∈ U2),
      U2 < U1 ∧ U1 ≤ U0 ∧ (∀ k ∈ K, ∀ u ∈ U2, ρ k u = u) ∧ commSubOf U1 (K.map ρ) = U1 ∧
      (∀ J : Subgroup W, (∀ k ∈ K, ∀ u ∈ J, ρ k u ∈ J) → U2 ≤ J → J ≤ U1 → J = U2 ∨ J = U1) ∧
      B4Hyp (secAct ρ _ h1 h2).range
        ((K.subgroupOf (K ⊔ Subgroup.zpowers b)).map (secAct ρ _ h1 h2)) ∧
      Cond1321 (secAct ρ _ h1 h2).range
        ((K.subgroupOf (K ⊔ Subgroup.zpowers b)).map (secAct ρ _ h1 h2))
        (secAct ρ _ h1 h2 ⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩) := by
  classical
  set K' := K ⊔ Subgroup.zpowers b with hK'
  have hbK' : b ∈ K' := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hKK' : K ≤ K' := le_sup_left
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  have hK'N : K' ≤ Subgroup.normalizer (K : Set Y) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hbK)
  have hcases : ∀ y ∈ K', y ∈ K ∨ y * b ∈ K := fun y hy =>
    mem_or_mul_mem_of_mem_sup hbK hb2 hy
  set X := K'.map ρ with hX
  set KW := K.map ρ with hKW
  have hKWX : KW ≤ X := Subgroup.map_mono hKK'
  have hKWn : ∀ x ∈ X, ∀ k ∈ KW, x * k * x⁻¹ ∈ KW := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨y * k * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hK'N hy) k).mp hk, ?_⟩
    simp
  have hKW2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ KW := by
    rintro _ ⟨y, hy, rfl⟩
    rcases hcases y hy with h | h
    · exact ⟨0, by rw [pow_zero, pow_one]; exact ⟨y, h, rfl⟩⟩
    · refine ⟨1, ?_⟩
      have hyy : y ^ 2 = (y * b) * (b⁻¹ * (y * b) * b⁻¹) := by rw [pow_two]; group
      have hyy' : y ^ 2 ∈ K := by
        rw [hyy]
        refine K.mul_mem h ?_
        have := (Subgroup.mem_normalizer_iff.mp hbK (y * b)).mp h
        rw [hbinv] at this ⊢
        exact this
      rw [pow_one, ← map_pow]
      exact ⟨_, hyy', rfl⟩
  let eK : ↥K ≃* ↥KW := K.equivMapOfInjective ρ hρ
  have hKWq : CFSG.IsQuasisimple ↥KW := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK
  have : Group.IsPerfect ↥KW := hKWq.1
  have hOW : CFSG.Open.pCore 2 ↥KW = ⊥ := by
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eK, hO, Subgroup.map_bot]
  have hSKW : SQTKGroup ↥KW := sqtkGroup_of_mulEquiv hSK eK
  have hbX : ρ b ∈ X := ⟨b, hbK', rfl⟩
  have hbW2 : ρ b * ρ b = 1 := by rw [← map_mul, hb2, map_one]
  have hXle : X ≤ KW ⊔ Subgroup.zpowers (ρ b) := by
    rw [hX, hK', Subgroup.map_sup, MonoidHom.map_zpowers]
  have hU0X : ∀ x ∈ X, ∀ u ∈ U0, x u ∈ U0 := by
    rintro _ ⟨y, hy, rfl⟩ u hu
    exact hU0 y hy u hu
  have hU0KW : ¬ U0 ≤ fixV KW := by
    obtain ⟨k, hk, u, hu, hku⟩ := hU0K
    exact fun h => hku (h hu (ρ k) ⟨k, hk, rfl⟩)
  obtain ⟨U1, U2, hU21, hU1U0, hU1X, hU2X, hcomm, hfix, hirrX⟩ :=
    exists_chief hKWX hKWn hU0X hU0KW
  have hirr := irr_of_chief hKWX hKWn hbX hbW2 hXle hD hD4 hU21 hU1X hU2X hcomm hirrX
  have hq := qsec_of_chief hKWX hKWn hKW2 hKWq hOW hW hU21 hU1X hU2X hcomm hfix hirr
  have h1 : ∀ y ∈ K', ∀ u ∈ U1, ρ y u ∈ U1 := fun y hy u hu => hU1X _ ⟨y, hy, rfl⟩ u hu
  have h2 : ∀ y ∈ K', ∀ u ∈ U2, ρ y u ∈ U2 := fun y hy u hu => hU2X _ ⟨y, hy, rfl⟩ u hu
  refine ⟨U1, U2, h1, h2, hU21, hU1U0, fun k hk u hu => hfix hu (ρ k) ⟨k, hk, rfl⟩, hcomm,
    fun J hJ => hirr J (by rintro _ ⟨k, hk, rfl⟩ u hu; exact hJ k hk u hu), ?_⟩
  set ψ := secAct ρ K' h1 h2 with hψ
  have hX1 : X ≤ stabSub U1 := map_le_stabSub ρ h1
  have hX2 : X ≤ stabSub U2 := map_le_stabSub ρ h2
  set r : ↥K' →* ↥X := (ρ.comp K'.subtype).codRestrict X (fun y => ⟨y, y.2, rfl⟩) with hr
  have hr_surj : Function.Surjective r := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hψr : ψ = (chiefHom hX1 hX2).comp r := rfl
  have hG : ψ.range = autSec (autSub X U1) ⊤ (U2.subgroupOf U1) := by
    rw [hψr, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hr_surj,
      ← MonoidHom.range_eq_map, range_chiefHom]
  have hrK : (K.subgroupOf K').map r = KW.subgroupOf X := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [Subgroup.mem_subgroupOf] at hy
      have : x = ρ y := (congrArg Subtype.val hyx).symm
      show x ∈ KW
      rw [this]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hKK' hk⟩, hk, rfl⟩
  have hL : (K.subgroupOf K').map ψ = autSec (autSub KW U1) ⊤ (U2.subgroupOf U1) := by
    rw [hψr, ← Subgroup.map_map, hrK, map_chiefHom hKWX hX1 hX2]
  have hV1 : ∀ v : ↥U1, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW v)
  have hS1 : SQTKGroup ↥(autSub KW U1) :=
    sqtkGroup_of_surjective_quasisimple hSKW (resTo KW U1 (hKWX.trans hX1))
      (resTo_surjective _) hq.quasi
  have hB4 : B4Hyp ψ.range ((K.subgroupOf K').map ψ) := by
    rw [hG, hL]
    exact hq.b4Hyp hV1 hS1
  refine ⟨hB4, ?_⟩
  set v := ψ ⟨b, hbK'⟩ with hv
  set ψK : ↥K →* MulAut (ChiefSec U1 U2) := ψ.comp (Subgroup.inclusion hKK') with hψK
  have hker : ψK.ker ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK ψK.normal_ker with h | h
    · exfalso
      have hLbot : (K.subgroupOf K').map ψ = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨y, hy, rfl⟩
        have hy0 : (y : Y) ∈ K := hy
        have hy' : (⟨y, hy0⟩ : ↥K) ∈ ψK.ker := h ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at hy'
        rw [Subgroup.mem_bot]
        exact hy'
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hB4.2.2.1
      rw [hLbot] at hnt
      obtain ⟨⟨a, ha⟩, ⟨c, hc⟩, hac⟩ := hnt
      rw [Subgroup.mem_bot] at ha hc
      exact hac (Subtype.ext (ha.trans hc.symm))
    · exact h
  refine ⟨⟨⟨b, hbK'⟩, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hv1
    obtain ⟨k0, hk0, hk0b⟩ := hbc
    apply hk0b
    have hc : ∀ k ∈ K, ∀ k' ∈ K, k' * (b * k * b⁻¹ * k⁻¹) = (b * k * b⁻¹ * k⁻¹) * k' := by
      intro k hk k' hk'
      have hmem : b * k * b⁻¹ * k⁻¹ ∈ K :=
        K.mul_mem ((Subgroup.mem_normalizer_iff.mp hbK k).mp hk) (K.inv_mem hk)
      have hker' : (⟨_, hmem⟩ : ↥K) ∈ ψK.ker := by
        rw [MonoidHom.mem_ker]
        have e : (Subgroup.inclusion hKK' ⟨_, hmem⟩ : ↥K') =
            ⟨b, hbK'⟩ * ⟨k, hKK' hk⟩ * ⟨b, hbK'⟩⁻¹ * ⟨k, hKK' hk⟩⁻¹ := Subtype.ext rfl
        show ψ (Subgroup.inclusion hKK' ⟨_, hmem⟩) = 1
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hv, hv1]
        group
      have := Subgroup.mem_center_iff.mp (hker hker') ⟨k', hk'⟩
      exact congrArg Subtype.val this
    have : Group.IsPerfect ↥K := hK.1
    exact centralizes_of_comm_central_perfect hbK hc k0 hk0
  ·
    rw [hv, ← map_mul]
    have : (⟨b, hbK'⟩ : ↥K') * ⟨b, hbK'⟩ = 1 := Subtype.ext hb2
    rw [this, map_one]
  ·
    have htop : K.subgroupOf K' ⊔ Subgroup.zpowers (⟨b, hbK'⟩ : ↥K') = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨y, hy⟩ -
      rcases hcases y hy with h | h
      · exact Subgroup.mem_sup_left (show (⟨y, hy⟩ : ↥K') ∈ K.subgroupOf K' from h)
      · have e : (⟨y, hy⟩ : ↥K') = ⟨y * b, hKK' h⟩ * ⟨b, hbK'⟩ := by
          apply Subtype.ext
          show y = y * b * b
          rw [mul_assoc, hb2, mul_one]
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
          (show (⟨y * b, hKK' h⟩ : ↥K') ∈ K.subgroupOf K' from h))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, MonoidHom.map_zpowers]
  ·
    obtain ⟨S, hS, hSb⟩ := hsyl
    refine ⟨(S.subgroupOf K').map ψ, ?_, ?_⟩
    · have hS' : IsSylowTwoOf (S.subgroupOf K') (K.subgroupOf K') := by
        obtain ⟨hSK, hp, hidx⟩ := hS
        refine ⟨fun x (hx : (x : Y) ∈ S) => (hSK hx : (x : Y) ∈ K), ?_, ?_⟩
        · exact hp.of_equiv (Subgroup.subgroupOfEquivOfLe (hSK.trans hKK')).symm
        · rw [← Subgroup.relIndex] at hidx ⊢
          rw [Subgroup.relIndex_subgroupOf hKK']
          exact hidx
      exact isSylowTwoOf_map hS' ψ
    · rintro _ ⟨s, hs, rfl⟩
      have hs' : (s : Y) ∈ S := hs
      rw [Subgroup.mem_centralizer_singleton_iff, hv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hSb _ hs')
  ·
    set D' : Subgroup (ChiefSec U1 U2) := (D.subgroupOf U1).map (chiefQ U1 U2) with hD'
    refine rkIdx_fixV_le_two (D := D') ?_ ?_
    · intro w
      obtain ⟨u, rfl⟩ := chiefQ_surjective U1 U2 w
      rw [hv, hψ, secAct_chiefQ, ← map_inv, ← map_mul]
      refine ⟨_, ?_, rfl⟩
      show ρ b (u : W) * (u : W)⁻¹ ∈ D
      exact hD u
    · refine (Nat.card_le_card_of_surjective
        (fun d : ↥(D.subgroupOf U1) => (⟨chiefQ U1 U2 d, d, d.2, rfl⟩ : ↥D')) ?_).trans ?_
      · rintro ⟨_, d, hd, rfl⟩
        exact ⟨⟨d, hd⟩, rfl⟩
      · refine (Nat.card_le_card_of_injective
          (fun d : ↥(D.subgroupOf U1) => (⟨((d : ↥U1) : W), d.2⟩ : ↥D)) ?_).trans hD4
        intro d d' h
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h')
  ·
    rintro _ ⟨y, rfl⟩
    rw [hv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    rcases hpair y y.2 with ⟨k, hk⟩ | h3
    · left
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : ((⟨b, hbK'⟩ : ↥K') * (y * ⟨b, hbK'⟩ * y⁻¹)) ^ 2 ^ k = 1 := Subtype.ext hk
      rw [this, map_one]
    · right
      rw [← map_pow]
      have : ((⟨b, hbK'⟩ : ↥K') * (y * ⟨b, hbK'⟩ * y⁻¹)) ^ 3 = 1 := Subtype.ext h3
      rw [this, map_one]

end Main

end CFSG.Quasithin.H13.A5
