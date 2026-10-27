module

public import CFSG.Quasithin.Background.B19Block
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Quasithin.Background.B1Solvable

public section

namespace CFSG.Quasithin.B19

open CFSG.Quasithin
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem mem_map_conj {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext y
  rw [mem_map_conj]
  have := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) y
  rw [inv_inv] at this
  exact this.symm

theorem mem_normalizer_of_map_conj_le {X M : Subgroup G}
    (h : ∀ g ∈ X, M.map (MulAut.conj g).toMonoidHom ≤ M) :
    ∀ g ∈ X, g ∈ Subgroup.normalizer (M : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    exact h g hg ⟨m, hm, rfl⟩
  · intro hm
    have := h g⁻¹ (X.inv_mem hg) ⟨g * m * g⁻¹, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem commute_sup {A B C D : Subgroup G} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b) : ∀ g ∈ A ⊔ B, ∀ h ∈ C ⊔ D, g * h = h * g := by
  have hle : ∀ {E : Subgroup G}, (∀ e ∈ E, ∀ c ∈ C, e * c = c * e) →
      (∀ e ∈ E, ∀ d ∈ D, e * d = d * e) →
        E ≤ Subgroup.centralizer ((C ⊔ D : Subgroup G) : Set G) := by
    intro E hEC hED
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (fun c hc => Subgroup.mem_centralizer_iff.2 fun e he => hEC e he c hc)
      (fun d hd => Subgroup.mem_centralizer_iff.2 fun e he => hED e he d hd)
  intro g hg h hh
  have := sup_le (hle hAC hAD) (hle hBC hBD) hg
  exact (Subgroup.mem_centralizer_iff.1 this h hh).symm

@[expose] def commTo (Φ M : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (M : Set G) ∧ ∀ f ∈ Φ, ⁅f, g⁆ ∈ M}
  one_mem' := ⟨Subgroup.one_mem _, fun f _ => by rw [commutatorElement_one_right]; exact M.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun f hf => ?_⟩
    have e : ⁅f, a * b⁆ = ⁅f, a⁆ * (a * ⁅f, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem (ha' f hf) ((Subgroup.mem_normalizer_iff.1 ha _).1 (hb' f hf))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun f hf => ?_⟩
    have e : ⁅f, a⁻¹⁆ = a⁻¹ * ⁅f, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha) _).1 (M.inv_mem (ha' f hf))

theorem mem_commTo {Φ M : Subgroup G} {g : G} :
    g ∈ commTo Φ M ↔ g ∈ Subgroup.normalizer (M : Set G) ∧ ∀ f ∈ Φ, ⁅f, g⁆ ∈ M :=
  Iff.rfl

@[expose] def commWith (M : Subgroup G) (t : G) : Subgroup G where
  carrier := {k | k ∈ Subgroup.normalizer (M : Set G) ∧ ⁅k, t⁆ ∈ M}
  one_mem' := ⟨Subgroup.one_mem _, by rw [commutatorElement_one_left]; exact M.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have e : ⁅a * b, t⁆ = (a * ⁅b, t⁆ * a⁻¹) * ⁅a, t⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem ((Subgroup.mem_normalizer_iff.1 ha _).1 hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    have e : ⁅a⁻¹, t⁆ = a⁻¹ * ⁅a, t⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha) _).1 (M.inv_mem ha')

theorem mem_commWith {M : Subgroup G} {t k : G} :
    k ∈ commWith M t ↔ k ∈ Subgroup.normalizer (M : Set G) ∧ ⁅k, t⁆ ∈ M :=
  Iff.rfl

theorem exists_inv_mul_fix {N K : Subgroup G} (hN : Odd (Nat.card N)) {τ c : G}
    (hτ : τ * τ = 1) (hc : c ∈ N) (hcK : c ∈ K) (hτc : τ * c * τ⁻¹ ∈ N)
    (hτcK : τ * c * τ⁻¹ ∈ K) :
    ∃ i c', i ∈ N ∧ i ∈ K ∧ c' ∈ N ∧ c' ∈ K ∧ c = i * c' ∧ τ * i * τ⁻¹ = i⁻¹ ∧
      τ * c' * τ⁻¹ = c' := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  set d := c * (τ * c * τ⁻¹)⁻¹ with hd
  have hdN : d ∈ N := N.mul_mem hc (N.inv_mem hτc)
  have hdK : d ∈ K := K.mul_mem hcK (K.inv_mem hτcK)
  have hτd : τ * d * τ⁻¹ = d⁻¹ := by
    rw [hd]
    calc τ * (c * (τ * c * τ⁻¹)⁻¹) * τ⁻¹ = τ * c * τ⁻¹ * ((τ * τ) * c⁻¹ * (τ * τ)⁻¹) := by
          group
      _ = (c * (τ * c * τ⁻¹)⁻¹)⁻¹ := by rw [hτ]; group
  have hdn : d ^ Nat.card N = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' : (⟨d, hdN⟩ : ↥N) ^ Nat.card N = 1)
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  set i := d ^ ((Nat.card N + 1) / 2) with hi
  have hi2 : i ^ 2 = d := sq_pow_half hN hdn
  have hτi : τ * i * τ⁻¹ = i⁻¹ := by
    rw [hi, ← conj_pow, hτd, inv_pow]
  refine ⟨i, i⁻¹ * c, N.pow_mem hdN _, K.pow_mem hdK _, N.mul_mem (N.inv_mem (N.pow_mem hdN _)) hc,
    K.mul_mem (K.inv_mem (K.pow_mem hdK _)) hcK, by group, hτi, ?_⟩
  have h1 : τ * c * τ⁻¹ = i⁻¹ * i⁻¹ * c := by
    have : i * i = c * (τ * c * τ⁻¹)⁻¹ := by rw [← pow_two, hi2]
    calc τ * c * τ⁻¹ = (c * (τ * c * τ⁻¹)⁻¹)⁻¹ * c := by group
      _ = (i * i)⁻¹ * c := by rw [this]
      _ = i⁻¹ * i⁻¹ * c := by group
  calc τ * (i⁻¹ * c) * τ⁻¹ = (τ * i * τ⁻¹)⁻¹ * (τ * c * τ⁻¹) := by group
    _ = i⁻¹ * c := by rw [hτi, h1]; group

end Group

section Setting

variable {V : Type*} [CommGroup V]

structure Setting (X Φ : Subgroup (MulAut V)) : Prop where
  le : Φ ≤ X
  normal : ∀ g ∈ X, ∀ f ∈ Φ, g * f * g⁻¹ ∈ Φ
  odd : Odd (Nat.card Φ)
  solvable : Group.IsSolvable Φ

@[expose] def tvSet (X Φ : Subgroup (MulAut V)) : Set (MulAut V) :=
  {t | t ∈ X ∧ IsTransvection t ∧ ∃ f ∈ Φ, f * t ≠ t * f}

@[expose] def FOf (Φ : Subgroup (MulAut V)) (t : MulAut V) : Subgroup (MulAut V) :=
  ⁅Φ, Subgroup.zpowers t⁆

@[expose] def GOf (Φ : Subgroup (MulAut V)) (t : MulAut V) : Subgroup (MulAut V) :=
  FOf Φ t ⊔ Subgroup.zpowers t

theorem Setting.map_conj_eq {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) : Φ.map (MulAut.conj g).toMonoidHom = Φ := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact hS.normal g hg f hf
  · intro f hf
    rw [mem_map_conj]
    have := hS.normal g⁻¹ (X.inv_mem hg) f hf
    simpa using this

theorem Setting.FOf_conj {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) (t : MulAut V) :
    (FOf Φ t).map (MulAut.conj g).toMonoidHom = FOf Φ (g * t * g⁻¹) := by
  unfold FOf
  rw [Subgroup.map_commutator, hS.map_conj_eq hg, MonoidHom.map_zpowers]
  rfl

theorem Setting.GOf_conj {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) (t : MulAut V) :
    (GOf Φ t).map (MulAut.conj g).toMonoidHom = GOf Φ (g * t * g⁻¹) := by
  unfold GOf
  rw [Subgroup.map_sup, hS.FOf_conj hg, MonoidHom.map_zpowers]
  rfl

theorem Setting.conj_mem_tvSet {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g t : MulAut V}
    (hg : g ∈ X) (ht : t ∈ tvSet X Φ) : g * t * g⁻¹ ∈ tvSet X Φ := by
  obtain ⟨htX, htr, f, hf, hft⟩ := ht
  refine ⟨X.mul_mem (X.mul_mem hg htX) (X.inv_mem hg), B1.isTransvection_conj htr g,
    g * f * g⁻¹, hS.normal g hg f hf, fun h => hft ?_⟩
  have h1 : g * (f * t) * g⁻¹ = g * (t * f) * g⁻¹ := by
    calc g * (f * t) * g⁻¹ = g * f * g⁻¹ * (g * t * g⁻¹) := by group
      _ = g * t * g⁻¹ * (g * f * g⁻¹) := h
      _ = g * (t * f) * g⁻¹ := by group
  simpa using h1

theorem Setting.exists_tvBlock [Finite V] {X Φ : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hS : Setting X Φ) {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    ∃ x w, TvBlock Φ t x w := by
  obtain ⟨htX, ⟨ht1, w, htw⟩, hnt⟩ := ht
  have := hS.solvable
  obtain ⟨x, hx⟩ :=
    B19.exists_tvBlock hV hS.odd htw ht1 (fun f hf => hS.normal t htX f hf) hnt
  exact ⟨x, w, hx⟩

namespace TvBlock

variable {Φ : Subgroup (MulAut V)} {t x : MulAut V} {w : V}

theorem FOf_eq (h : TvBlock Φ t x w) : FOf Φ t = Subgroup.zpowers x := h.comm_eq

theorem GOf_eq (h : TvBlock Φ t x w) :
    GOf Φ t = Subgroup.zpowers x ⊔ Subgroup.zpowers t := by
  rw [GOf, h.FOf_eq]

theorem sq (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) : t * t = 1 := B1.tv_sq hV h.tw h.t1

theorem inv_zpowers (h : TvBlock Φ t x w) {y : MulAut V} (hy : y ∈ Subgroup.zpowers x) :
    t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h.inv, inv_zpow]

theorem le_normalizer (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup (MulAut V)) : Set (MulAut V)) := by
  have hsq := h.sq hV
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  refine sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h.inv_zpowers hy]
    exact Subgroup.inv_mem _ hy
  · intro hy
    have h1 := h.inv_zpowers hy
    have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
        _ = y := by rw [htinv, hsq]; group
    rw [← h2, h1]
    exact Subgroup.inv_mem _ hy

theorem card_zpowers (h : TvBlock Φ t x w) : Nat.card (Subgroup.zpowers x) = 3 :=
  card_zpowers_eq_three h.x3 h.x1

theorem card_commSub (h : TvBlock Φ t x w) :
    Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = 4 := by
  rw [← commV_eq_commSub]
  exact h.card_comm

theorem le_centSub_fixV (h : TvBlock Φ t x w) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers t ≤ centSub (fixV (Subgroup.zpowers x)) :=
  sup_le (Subgroup.zpowers_le.2 fun _ hc => hc x (Subgroup.mem_zpowers x))
    (Subgroup.zpowers_le.2 fun c hc => h.fix c hc)

theorem commV_zpowers_t_le (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    commV (Subgroup.zpowers t) ≤ commV (Subgroup.zpowers x) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨s, hs, v, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers (h.sq hV) hs with rfl | rfl
  · simp only [MulAut.one_apply, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rcases h.tw.2 v with h1 | h1
    · rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h1, mul_comm v w, mul_inv_cancel_right]
      exact h.w_mem

theorem commV_G (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    commV (Subgroup.zpowers x ⊔ Subgroup.zpowers t) = commV (Subgroup.zpowers x) := by
  rw [commV_sup]
  exact sup_eq_left.2 (h.commV_zpowers_t_le hV)

theorem oddCore_eq (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    (CFSG.oddCore ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t)).map
      (Subgroup.zpowers x ⊔ Subgroup.zpowers t).subtype = Subgroup.zpowers x := by
  set G := Subgroup.zpowers x ⊔ Subgroup.zpowers t with hG
  have hxG : Subgroup.zpowers x ≤ G := le_sup_left
  have hsq := h.sq hV
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  have hnorm : ((Subgroup.zpowers x).subgroupOf G).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hxG]
    intro a k ha hk
    exact (Subgroup.mem_normalizer_iff.1 (h.le_normalizer hV hk) a).1 ha
  have hodd : Odd (Nat.card ((Subgroup.zpowers x).subgroupOf G)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxG).toEquiv, h.card_zpowers]
    decide
  apply le_antisymm
  · have hle : CFSG.oddCore ↥G ≤ (Subgroup.zpowers x).subgroupOf G := by
      refine sSup_le fun N hN => ?_
      intro n hn
      rw [Subgroup.mem_subgroupOf]
      rcases mem_or_mul_mem_of_mem_sup hsq (fun f hf => by
          rw [h.inv_zpowers hf]; exact Subgroup.inv_mem _ hf) n.2 with h1 | h1
      · exact h1
      · have hn2 : n * n = 1 := by
          apply Subtype.ext
          show (n : MulAut V) * n = 1
          have e : (n : MulAut V) = ((n : MulAut V) * t) * t := by rw [mul_assoc, hsq, mul_one]
          calc (n : MulAut V) * n = ((n : MulAut V) * t) * t * (((n : MulAut V) * t) * t) := by
                rw [← e]
            _ = ((n : MulAut V) * t) * (t * ((n : MulAut V) * t) * t⁻¹) := by rw [htinv]; group
            _ = 1 := by rw [h.inv_zpowers h1, mul_inv_cancel]
        rw [eq_one_of_sq_of_odd hN.2 hn hn2]
        exact Subgroup.one_mem _
    calc (CFSG.oddCore ↥G).map G.subtype ≤ ((Subgroup.zpowers x).subgroupOf G).map G.subtype :=
          Subgroup.map_mono hle
      _ = Subgroup.zpowers x := Subgroup.map_subgroupOf_eq_of_le hxG
  · rw [← Subgroup.map_subgroupOf_eq_of_le hxG]
    exact Subgroup.map_mono (le_sSup ⟨hnorm, hodd⟩)

theorem isSylowTwoOf_zpowers (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Subgroup.zpowers t)
      (Subgroup.zpowers x ⊔ Subgroup.zpowers t) := by
  have hcardt : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.sq hV) h.t1
  refine ⟨le_sup_right, IsPGroup.of_card (n := 1) (by rw [hcardt]; simp), ?_⟩
  have h1 : (Subgroup.zpowers t).relIndex (Subgroup.zpowers x ⊔ Subgroup.zpowers t) *
      Nat.card ↥(Subgroup.zpowers t ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers t)) =
      Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.2 le_sup_right, hcardt, h.card_G] at h1
  have h3 : (Subgroup.zpowers t).relIndex (Subgroup.zpowers x ⊔ Subgroup.zpowers t) = 3 := by
    omega
  show ¬ 2 ∣ (Subgroup.zpowers t).relIndex (Subgroup.zpowers x ⊔ Subgroup.zpowers t)
  rw [h3]
  decide

section Finite

variable [Finite V]

theorem decomp (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    fixV (Subgroup.zpowers x) ⊔ commV (Subgroup.zpowers x) = ⊤ ∧
      fixV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers x) = ⊥ := by
  obtain ⟨hsup, hinf, -⟩ := zpowers_three_decomp hV h.x3
  rw [commV_eq_commSub]
  exact ⟨hsup, hinf⟩

theorem card_V (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) :
    Nat.card V = 4 * Nat.card (fixV (Subgroup.zpowers x)) := by
  obtain ⟨hsup, hinf⟩ := h.decomp hV
  have := card_sup_mul_card_inf (fixV (Subgroup.zpowers x)) (commV (Subgroup.zpowers x))
  rw [hsup, hinf, Subgroup.card_top, Subgroup.card_bot, mul_one, h.card_comm] at this
  rw [this, mul_comm]

theorem card_le_two_mul (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers x)) (hu1 : u ≠ 1) :
    Nat.card V ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers u) := by
  have hinf : fixV (Subgroup.zpowers x) ⊓ Subgroup.zpowers u = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← (h.decomp hV).2]
    exact inf_le_inf_left _ (Subgroup.zpowers_le.2 hu)
  have hcu : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV u) hu1
  have := card_sup_mul_card_inf (fixV (Subgroup.zpowers x)) (Subgroup.zpowers u)
  rw [hinf, Subgroup.card_bot, mul_one, hcu] at this
  rw [this, h.card_V hV]
  omega

theorem comm_of_sq (h : TvBlock Φ t x w) (hV : ∀ v : V, v ^ 2 = 1) {b : MulAut V}
    (hb : b * b = 1) (hbx : x * b = b * x) :
    b * t = t * b ∧ ∀ m ∈ commV (Subgroup.zpowers x), b m = m := by
  have hbM : ∀ m ∈ commV (Subgroup.zpowers x), b m = m := by
    rw [commV_eq_commSub]
    exact fix_of_comm_sq hV h.x3 h.x1 h.card_commSub hb hbx
  refine ⟨?_, hbM⟩
  have hbw : b w = w := hbM w h.w_mem
  have hs : IsTransvectionWith (b * t * b⁻¹) w := hbw ▸ B1.tv_conj h.tw b
  have hs1 : b * t * b⁻¹ ≠ 1 := B1.tv_conj_ne_one h.t1 b
  have hbinv : ∀ c ∈ fixV (Subgroup.zpowers x), b⁻¹ c ∈ fixV (Subgroup.zpowers x) := by
    intro c hc
    refine B1.fixV_smul_mem b⁻¹ (fun y hy => ?_) hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc' : Commute b (x ^ k) := ((show Commute x b from hbx).symm).zpow_right k
    rw [inv_inv, hc'.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hCs : ∀ c ∈ fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w, (b * t * b⁻¹) c = c := by
    have hle : fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w ≤
        fixV (Subgroup.zpowers (b * t * b⁻¹)) := by
      refine sup_le (fun c hc => B1.zpowers_fix ?_) (Subgroup.zpowers_le.2 ?_)
      · show b (t (b⁻¹ c)) = c
        rw [h.fix _ (hbinv c hc)]
        simp
      · exact B1.zpowers_fix (B1.tv_fix hs hs1)
    exact fun c hc => hle hc _ (Subgroup.mem_zpowers _)
  have hCt : ∀ c ∈ fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w, t c = c := by
    have hle : fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w ≤ fixV (Subgroup.zpowers t) :=
      sup_le (fun c hc => B1.zpowers_fix (h.fix c hc))
        (Subgroup.zpowers_le.2 (B1.zpowers_fix (B1.tv_fix h.tw h.t1)))
    exact fun c hc => hle hc _ (Subgroup.mem_zpowers _)
  have heq := tv_eq_of_fix hV hs hs1 h.tw h.t1 hCs hCt (h.card_le_two_mul hV h.w_mem h.tw.1)
  calc b * t = b * t * b⁻¹ * b := by group
    _ = t * b := by rw [heq]

theorem mem_G_of_eq (h : TvBlock Φ t x w) {t' x' : MulAut V} {w' : V} (h' : TvBlock Φ t' x' w')
    (hV : ∀ v : V, v ^ 2 = 1) (heq : Subgroup.zpowers x' = Subgroup.zpowers x) :
    t' ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers t := by
  have hw' : w' ∈ commV (Subgroup.zpowers x) := heq ▸ h'.w_mem
  obtain ⟨-, -, hMx, hfpf, hfpf2⟩ := zpowers_three_decomp hV h.x3
  have hw : w ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) := by
    rw [← commV_eq_commSub]
    exact h.w_mem
  have hw'' : w' ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) := by
    rw [← commV_eq_commSub]
    exact hw'
  have h4 := B1.four_elements hMx hfpf hfpf2 h.card_commSub.le hw h.tw.1 w' hw''
  obtain ⟨g, hgx, hgw⟩ : ∃ g ∈ Subgroup.zpowers x, g w = w' := by
    rcases h4 with h5 | h5 | h5 | h5
    · exact absurd h5 h'.tw.1
    · exact ⟨1, Subgroup.one_mem _, by rw [h5]; rfl⟩
    · exact ⟨x, Subgroup.mem_zpowers x, h5.symm⟩
    · exact ⟨x * x, Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x),
        h5.symm⟩
  have hs : IsTransvectionWith (g * t * g⁻¹) w' := hgw ▸ B1.tv_conj h.tw g
  have hs1 : g * t * g⁻¹ ≠ 1 := B1.tv_conj_ne_one h.t1 g
  have hfixg : ∀ c ∈ fixV (Subgroup.zpowers x), g⁻¹ c = c := fun c hc =>
    hc _ (Subgroup.inv_mem _ hgx)
  have hfixg' : ∀ c ∈ fixV (Subgroup.zpowers x), g c = c := fun c hc => hc _ hgx
  have hfixeq : fixV (Subgroup.zpowers x') = fixV (Subgroup.zpowers x) := by rw [heq]
  have hCs : ∀ c ∈ fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w', (g * t * g⁻¹) c = c := by
    have hle : fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w' ≤
        fixV (Subgroup.zpowers (g * t * g⁻¹)) := by
      refine sup_le (fun c hc => B1.zpowers_fix ?_) (Subgroup.zpowers_le.2 ?_)
      · show g (t (g⁻¹ c)) = c
        rw [hfixg c hc, h.fix c hc, hfixg' c hc]
      · exact B1.zpowers_fix (B1.tv_fix hs hs1)
    exact fun c hc => hle hc _ (Subgroup.mem_zpowers _)
  have hCt : ∀ c ∈ fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w', t' c = c := by
    have hle : fixV (Subgroup.zpowers x) ⊔ Subgroup.zpowers w' ≤ fixV (Subgroup.zpowers t') :=
      sup_le (fun c hc => B1.zpowers_fix (h'.fix c (hfixeq ▸ hc)))
        (Subgroup.zpowers_le.2 (B1.zpowers_fix (B1.tv_fix h'.tw h'.t1)))
    exact fun c hc => hle hc _ (Subgroup.mem_zpowers _)
  have hst := tv_eq_of_fix hV hs hs1 h'.tw h'.t1 hCs hCt (h.card_le_two_mul hV hw' h'.tw.1)
  rw [← hst]
  have hgG : g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers t :=
    le_sup_left (a := Subgroup.zpowers x) hgx
  have htG : t ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers t :=
    le_sup_right (a := Subgroup.zpowers x) (Subgroup.mem_zpowers t)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgG htG) (Subgroup.inv_mem _ hgG)

end Finite

end TvBlock

end Setting

section Facts

variable {V : Type*} [CommGroup V] {X Φ : Subgroup (MulAut V)}

theorem le_ffJP {P : Set (Subgroup (MulAut V))} {H A : Subgroup (MulAut V)} (hA : A ∈ P)
    (hAH : A ≤ H) : A ≤ ffJP P H :=
  le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ P) => ⨆ (_ : B ≤ H), B) A hA
    (le_iSup_of_le hAH le_rfl)

theorem le_ffJ {A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) : A ≤ ffJ X :=
  le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : IsFFStarOffender X B) => B) A hA le_rfl

theorem mem_GOf {t : MulAut V} : t ∈ GOf Φ t :=
  le_sup_right (a := FOf Φ t) (Subgroup.mem_zpowers t)

theorem FOf_le_GOf {t : MulAut V} : FOf Φ t ≤ GOf Φ t := le_sup_left

theorem isFFStarMin_zpowers_tv [Finite V] {t : MulAut V} (hV : ∀ v : V, v ^ 2 = 1)
    (ht : t ∈ tvSet X Φ) : IsFFStarMin X (Subgroup.zpowers t) :=
  isFFStarMin_zpowers hV ht.1 ht.2.1

namespace Setting

variable [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hS : Setting X Φ)
include hV hS

theorem FOf_le {t : MulAut V} (ht : t ∈ tvSet X Φ) : FOf Φ t ≤ Φ := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  exact Subgroup.zpowers_le.2 h.mem

theorem card_FOf {t : MulAut V} (ht : t ∈ tvSet X Φ) : Nat.card (FOf Φ t) = 3 := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  exact h.card_zpowers

theorem FOf_central {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    ∀ y ∈ FOf Φ t, ∀ g ∈ Φ, g * y = y * g := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  intro y hy g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((show Commute g x from h.central g hg).zpow_right k).eq

theorem card_commV_FOf {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    Nat.card (commV (FOf Φ t)) = 4 := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  exact h.card_comm

theorem commV_GOf {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    commV (GOf Φ t) = commV (FOf Φ t) := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq, h.FOf_eq]
  exact h.commV_G hV

theorem GOf_le {t : MulAut V} (ht : t ∈ tvSet X Φ) : GOf Φ t ≤ X :=
  sup_le ((hS.FOf_le hV ht).trans hS.le) (Subgroup.zpowers_le.2 ht.1)

theorem card_GOf {t : MulAut V} (ht : t ∈ tvSet X Φ) : Nat.card (GOf Φ t) = 6 := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq]
  exact h.card_G

theorem GOf_inf_centSub {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    GOf Φ t ⊓ centSub (commV (FOf Φ t)) = ⊥ := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq, h.FOf_eq]
  exact h.faithful

theorem autSub_GOf {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    autSub (GOf Φ t) (commV (FOf Φ t)) = ⊤ := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq, h.FOf_eq]
  exact h.full

theorem GOf_iso {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    Nonempty (↥(GOf Φ t) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq]
  exact h.iso

theorem GOf_le_centSub_fixV {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    GOf Φ t ≤ centSub (fixV (FOf Φ t)) := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq, h.FOf_eq]
  exact h.le_centSub_fixV

theorem decomp_FOf {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    fixV (FOf Φ t) ⊔ commV (FOf Φ t) = ⊤ ∧ fixV (FOf Φ t) ⊓ commV (FOf Φ t) = ⊥ := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  exact h.decomp hV

theorem FOf_inf_centSub {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    FOf Φ t ⊓ centSub (commV (FOf Φ t)) = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_right _ FOf_le_GOf).trans (hS.GOf_inf_centSub hV ht).le)

theorem inverted {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    ∀ y ∈ Φ, t * y * t⁻¹ = y⁻¹ → y ∈ FOf Φ t := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  exact h.inverted

theorem inv_FOf {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    ∀ y ∈ FOf Φ t, t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.FOf_eq]
  exact fun y hy => h.inv_zpowers hy

theorem sq_tv {t : MulAut V} (ht : t ∈ tvSet X Φ) : t * t = 1 := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  exact h.sq hV

theorem GOf_le_normalizer {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    GOf Φ t ≤ Subgroup.normalizer ((FOf Φ t : Subgroup (MulAut V)) : Set (MulAut V)) := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq, h.FOf_eq]
  exact h.le_normalizer hV

theorem oddCore_GOf {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    (CFSG.oddCore ↥(GOf Φ t)).map (GOf Φ t).subtype = FOf Φ t := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq, h.FOf_eq]
  exact h.oddCore_eq hV

theorem isSylowTwoOf_zpowers {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Subgroup.zpowers t) (GOf Φ t) := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  rw [h.GOf_eq]
  exact h.isSylowTwoOf_zpowers hV

theorem exists_tv_of_isSylowTwoOf {t : MulAut V} (ht : t ∈ tvSet X Φ)
    {A : Subgroup (MulAut V)} (hA : CFSG.QuasithinUnique.IsSylowTwoOf A (GOf Φ t)) :
    ∃ t' ∈ tvSet X Φ, A = Subgroup.zpowers t' ∧ FOf Φ t' = FOf Φ t := by
  obtain ⟨g, hg, hAg⟩ := B1.sylowTwo_conj (hS.isSylowTwoOf_zpowers hV ht) hA
  have hgX : g ∈ X := hS.GOf_le hV ht hg
  refine ⟨g * t * g⁻¹, hS.conj_mem_tvSet hgX ht, ?_, ?_⟩
  · rw [hAg, MonoidHom.map_zpowers]
    rfl
  · rw [← hS.FOf_conj hgX t]
    exact map_conj_eq_of_mem_normalizer (hS.GOf_le_normalizer hV ht hg)

theorem GOf_le_of_forall {t : MulAut V} (ht : t ∈ tvSet X Φ) {J : Subgroup (MulAut V)}
    (hJ : ∀ s ∈ tvSet X Φ, s ∈ J) : GOf Φ t ≤ J := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  have hsq := h.sq hV
  have hxX : x ∈ X := hS.le h.mem
  have htJ := hJ t ht
  have hsJ := hJ _ (hS.conj_mem_tvSet hxX ht)
  have hxJ : x ∈ J := by
    have e : x = t * (x * t * x⁻¹) := by
      have hx2 : x = x⁻¹ * x⁻¹ := by
        rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← pow_two, ← pow_succ', h.x3]
      calc x = x⁻¹ * x⁻¹ := hx2
        _ = (t * x * t⁻¹) * x⁻¹ := by rw [h.inv]
        _ = t * (x * t * x⁻¹) := by
          rw [inv_eq_of_mul_eq_one_right hsq]
          group
    rw [e]
    exact J.mul_mem htJ hsJ
  rw [h.GOf_eq]
  exact sup_le (Subgroup.zpowers_le.2 hxJ) (Subgroup.zpowers_le.2 htJ)

theorem commutator_zpowers_ne_bot {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    ⁅Φ, Subgroup.zpowers t⁆ ≠ ⊥ := by
  intro h
  have := hS.card_FOf hV ht
  rw [FOf, h, Subgroup.card_bot] at this
  omega

theorem exists_tv_of_isFFStarMin {A : Subgroup (MulAut V)} (hA : IsFFStarMin X A)
    (hnt : ⁅Φ, A⁆ ≠ ⊥) : ∃ t ∈ tvSet X Φ, A = Subgroup.zpowers t := by
  have hnt' : ∃ a ∈ A, ∃ f ∈ Φ, a * f ≠ f * a := by
    by_contra hno
    push Not at hno
    apply hnt
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hno a ha f hf
  have hA2 : IsElemAbelian2 A := hA.1.2.2.1
  have hFA : ∀ a ∈ A, ∀ f ∈ Φ, a * f * a⁻¹ ∈ Φ := fun a ha f hf => hS.normal a (hA.1.1 ha) f hf
  obtain ⟨Y, B, hYF, hBA, hBcard, hYinv, hBY, hAY⟩ :=
    B1.exists_hyperplane_trivial_sub hA2.1 hA2.2 hFA hS.odd hnt'
  have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hS.odd (Subgroup.card_dvd_of_le hYF)
  have hcard : Nat.card A = 2 := B1.key_mod hV hA hYodd hYinv hBA hBcard hBY hAY
  obtain ⟨⟨t, htA⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.1.2.1
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  have hord : orderOf t = 2 := by
    have h1 : orderOf (⟨t, htA⟩ : ↥A) ∣ Nat.card A := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ht1
    · exact h
  have hAt : A = Subgroup.zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 htA) ?_).symm
    rw [hcard, Nat.card_zpowers, hord]
  have htr : IsTransvection t := by
    refine ⟨ht1, ?_⟩
    have hge := B1.card_mul_card_fixV_of_isFFStarOffender_ge hA.1
    rw [hcard, hAt] at hge
    exact B1.tv_of_index_two ht1 hge
  refine ⟨t, ⟨hA.1.1 htA, htr, ?_⟩, hAt⟩
  obtain ⟨a, ha, f, hf, hne⟩ := hnt'
  refine ⟨f, hf, fun hft => hne ?_⟩
  rw [hAt] at ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact (((show Commute f t from hft).zpow_right k)).eq.symm

theorem commutator_ffJP_eq :
    ⁅Φ, ffJP {A | IsFFStarMin X A} X⁆ = ⨆ (t) (_ : t ∈ tvSet X Φ), FOf Φ t := by
  set M := ⨆ (t) (_ : t ∈ tvSet X Φ), FOf Φ t with hM
  apply le_antisymm
  · have hMn : ∀ g ∈ X, g ∈ Subgroup.normalizer (M : Set (MulAut V)) :=
      mem_normalizer_of_map_conj_le fun g hg => by
        rw [hM, Subgroup.map_iSup]
        refine iSup_le fun t => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun ht => ?_
        rw [hS.FOf_conj hg]
        exact le_iSup₂_of_le (f := fun (s : MulAut V) (_ : s ∈ tvSet X Φ) => FOf Φ s)
          (g * t * g⁻¹) (hS.conj_mem_tvSet hg ht) le_rfl
    have hJ : ffJP {A | IsFFStarMin X A} X ≤ commTo Φ M := by
      refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAX => ?_
      intro a ha
      refine ⟨hMn a (hAX ha), fun f hf => ?_⟩
      by_cases hnt : ⁅Φ, A⁆ = ⊥
      · have h1 : ⁅f, a⁆ ∈ ⁅Φ, A⁆ := Subgroup.commutator_mem_commutator hf ha
        rw [hnt, Subgroup.mem_bot] at h1
        rw [h1]
        exact M.one_mem
      · obtain ⟨t, ht, rfl⟩ := hS.exists_tv_of_isFFStarMin hV hA hnt
        exact (le_iSup₂_of_le (f := fun (s : MulAut V) (_ : s ∈ tvSet X Φ) => FOf Φ s) t ht
          le_rfl : FOf Φ t ≤ M) (Subgroup.commutator_mem_commutator hf ha)
    rw [Subgroup.commutator_le]
    intro f hf g hg
    exact (hJ hg).2 f hf
  · refine iSup₂_le fun t ht => Subgroup.commutator_mono le_rfl ?_
    exact le_ffJP (isFFStarMin_zpowers_tv hV ht) (Subgroup.zpowers_le.2 ht.1)

theorem pair_centSub {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (ht' : t' ∈ tvSet X Φ)
    (hne : FOf Φ t ≠ FOf Φ t') : GOf Φ t' ≤ centSub (commV (FOf Φ t)) := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  obtain ⟨x', w', h'⟩ := hS.exists_tvBlock hV ht'
  rw [h.FOf_eq, h'.FOf_eq] at hne
  rw [h'.GOf_eq, h.FOf_eq]
  have hxx' : x * x' = x' * x := (h.central x' h'.mem).symm
  have hnot : x' ∉ Subgroup.zpowers x := by
    intro hmem
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmem)
      (by rw [h.card_zpowers, h'.card_zpowers])).symm
  obtain ⟨h1, -⟩ := B1.commuting_fixes hV hxx' h.x3 h'.x3 h.x1 h'.x1 h.card_commSub
    h'.card_commSub hnot
  have hx'M : ∀ m ∈ commV (Subgroup.zpowers x), x' m = m := by
    rw [commV_eq_commSub]
    exact h1
  refine sup_le (Subgroup.zpowers_le.2 hx'M) (Subgroup.zpowers_le.2 fun m hm => ?_)
  exact h'.fix m (fun y hy => B1.zpowers_fix (hx'M m hm) y hy)

theorem pair_fixV {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (ht' : t' ∈ tvSet X Φ)
    (hne : FOf Φ t ≠ FOf Φ t') : commV (FOf Φ t') ≤ fixV (FOf Φ t) := by
  have h := hS.pair_centSub hV ht' ht (Ne.symm hne)
  intro m hm g hg
  exact h (FOf_le_GOf hg) m hm

theorem pair_tt {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (ht' : t' ∈ tvSet X Φ)
    (hne : FOf Φ t ≠ FOf Φ t') : t * t' = t' * t := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  obtain ⟨x', w', h'⟩ := hS.exists_tvBlock hV ht'
  have h1 := hS.pair_centSub hV ht ht' hne
  have h2 := hS.pair_centSub hV ht' ht (Ne.symm hne)
  have ht'w : t' w = w := h1 mem_GOf w (by rw [h.FOf_eq]; exact h.w_mem)
  have htw' : t w' = w' := h2 mem_GOf w' (by rw [h'.FOf_eq]; exact h'.w_mem)
  exact B1.tv_commute h.tw h'.tw htw' ht'w

theorem pair_tF {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (ht' : t' ∈ tvSet X Φ)
    (hne : FOf Φ t ≠ FOf Φ t') : ∀ y ∈ FOf Φ t, t' * y = y * t' := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  obtain ⟨x', w', h'⟩ := hS.exists_tvBlock hV ht'
  have htt' := hS.pair_tt hV ht ht' hne
  have hmap : (FOf Φ t).map (MulAut.conj t').toMonoidHom = FOf Φ t := by
    rw [hS.FOf_conj ht'.1]
    congr 1
    rw [← htt', mul_inv_cancel_right]
  have hx : t' * x * t'⁻¹ ∈ Subgroup.zpowers x := by
    rw [← h.FOf_eq, ← hmap]
    exact ⟨x, by rw [h.FOf_eq]; exact Subgroup.mem_zpowers x, rfl⟩
  have hcomm : t' * x = x * t' := by
    rcases eq_of_mem_zpowers_three h.x3 hx with h3 | h3 | h3
    · exfalso
      apply h.x1
      have := congrArg (fun z => t'⁻¹ * z * t') h3
      simpa [mul_assoc] using this
    · calc t' * x = t' * x * t'⁻¹ * t' := by group
        _ = x * t' := by rw [h3]
    · exfalso
      apply hne
      have hmem := h'.inverted x h.mem h3
      rw [h.FOf_eq, h'.FOf_eq]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmem)
        (by rw [h.card_zpowers, h'.card_zpowers])
  intro y hy
  rw [h.FOf_eq] at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((show Commute t' x from hcomm).zpow_right k).eq

theorem pair_comm {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (ht' : t' ∈ tvSet X Φ)
    (hne : FOf Φ t ≠ FOf Φ t') : ∀ a ∈ GOf Φ t, ∀ b ∈ GOf Φ t', a * b = b * a := by
  have htt' := hS.pair_tt hV ht ht' hne
  have ht'F := hS.pair_tF hV ht ht' hne
  have htF' := hS.pair_tF hV ht' ht (Ne.symm hne)
  refine commute_sup (fun a ha c hc => ?_) (fun a ha d hd => ?_) (fun b hb c hc => ?_)
    (fun b hb d hd => ?_)
  · exact (hS.FOf_central hV ht a ha c (hS.FOf_le hV ht' hc)).symm
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact ((show Commute t' a from ht'F a ha).zpow_left k).eq.symm
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((show Commute t c from htF' c hc).zpow_left k).eq
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact ((show Commute t t' from htt').zpow_zpow k m).eq

theorem GOf_eq_of_FOf_eq {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (ht' : t' ∈ tvSet X Φ)
    (heq : FOf Φ t = FOf Φ t') : GOf Φ t = GOf Φ t' := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  obtain ⟨x', w', h'⟩ := hS.exists_tvBlock hV ht'
  have hzz : Subgroup.zpowers x' = Subgroup.zpowers x := by rw [← h.FOf_eq, ← h'.FOf_eq, heq]
  have h1 : t' ∈ GOf Φ t := by
    rw [h.GOf_eq]
    exact h.mem_G_of_eq h' hV hzz
  have h2 : t ∈ GOf Φ t' := by
    rw [h'.GOf_eq]
    exact h'.mem_G_of_eq h hV hzz.symm
  apply le_antisymm
  · refine sup_le ?_ (Subgroup.zpowers_le.2 h2)
    rw [heq]
    exact FOf_le_GOf
  · refine sup_le ?_ (Subgroup.zpowers_le.2 h1)
    rw [← heq]
    exact FOf_le_GOf

theorem comm_of_sq {t b : MulAut V} (ht : t ∈ tvSet X Φ) (hb : b * b = 1)
    (hbF : ∀ y ∈ FOf Φ t, y * b = b * y) :
    (∀ g ∈ GOf Φ t, g * b = b * g) ∧ ∀ m ∈ commV (FOf Φ t), b m = m := by
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  have hbx : x * b = b * x := hbF x (by rw [h.FOf_eq]; exact Subgroup.mem_zpowers x)
  obtain ⟨hbt, hbM⟩ := h.comm_of_sq hV hb hbx
  refine ⟨fun g hg => ?_, by rw [h.FOf_eq]; exact hbM⟩
  have hle : GOf Φ t ≤ Subgroup.centralizer {b} := by
    rw [h.GOf_eq]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hbx
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hbt.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)


end Setting

end Facts

end CFSG.Quasithin.B19
