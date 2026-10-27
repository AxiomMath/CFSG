module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Quasithin.EmptyFaithful.S151S5A
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin.RonanD33

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isPGroup_iff_forall_mem {p : ℕ} {Y : Subgroup G} :
    IsPGroup p ↥Y ↔ ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k = 1 := by
  constructor
  · intro h y hy
    obtain ⟨k, hk⟩ := h ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro h ⟨y, hy⟩
    obtain ⟨k, hk⟩ := h y hy
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem pCoreOf_le (H : Subgroup G) : pCoreOf 2 H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_pCoreOf {H : Subgroup G} {x : G} :
    x ∈ pCoreOf 2 H ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pCoreOf_isPGroup (H : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 H) := by
  rw [isPGroup_iff_forall_mem]
  intro x hx
  obtain ⟨hxH, hxp⟩ := mem_pCoreOf.mp hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hxp⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hk
  simpa using this

theorem le_normalizer_pCoreOf (H : Subgroup G) : H ≤ normalizer (pCoreOf 2 H : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ pCoreOf 2 H, g * x * g⁻¹ ∈ pCoreOf 2 H := by
    intro g hg x hx
    obtain ⟨hxH, hxp⟩ := mem_pCoreOf.mp hx
    refine mem_pCoreOf.mpr ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), ?_⟩
    have h := (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem ⟨x, hxH⟩ hxp ⟨g, hg⟩
    exact h
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h := key g⁻¹ (H.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem isPGroup_subgroupOf {Y H : Subgroup G} (hY : IsPGroup 2 ↥Y) :
    IsPGroup 2 ↥(Y.subgroupOf H) := by
  rw [isPGroup_iff_forall_mem] at hY ⊢
  rintro ⟨y, hyH⟩ hy
  obtain ⟨k, hk⟩ := hY y hy
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem le_pCoreOf_of_le_normalizer {Y H : Subgroup G} (hYH : Y ≤ H)
    (hN : H ≤ normalizer (Y : Set G)) (hY : IsPGroup 2 ↥Y) : Y ≤ pCoreOf 2 H := by
  have hnorm : (Y.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hYH).mpr hN
  have hle : Y.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hnorm, isPGroup_subgroupOf hY⟩
  intro y hy
  exact mem_pCoreOf.mpr ⟨hYH hy, hle hy⟩

theorem conj_mem_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) {x : G} (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left (hA a ha)) (fun b hb => Subgroup.mem_sup_right (hB b hb))
  exact h hx

theorem conj_mem_of_mem_sup {A B N : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ N)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ N) {x : G} (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ N := by
  have h : A ⊔ B ≤ N.comap (MulAut.conj g).toMonoidHom := sup_le hA hB
  exact h hx

theorem le_normalizer_of_forall_conj_mem {S Y : Subgroup G} (h : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    S ≤ normalizer (Y : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h s hs y hy, fun hy => ?_⟩
  have h2 := h s⁻¹ (S.inv_mem hs) _ hy
  have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rwa [e] at h2

theorem mem_of_pow_mem_of_coprime {C : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ C) (hb : x ^ b ∈ C) : x ∈ C := by
  have hc : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  obtain ⟨u, v, huv⟩ := hc
  have h1 : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have e : (a : ℤ) * u + (b : ℤ) * v = 1 := by linarith
    rw [e, zpow_one]
  rw [h1]
  exact C.mul_mem (C.zpow_mem ha u) (C.zpow_mem hb v)


theorem frattini_sylow_normal (K : Type*) [Group K] [Finite K] (p : ℕ) [Fact p.Prime]
    (P : Sylow p (frattini K)) : (P.map (frattini K).subtype).Normal := by
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  have normalizer_P := frattini_nongenerating frattini_argument
  exact normalizer_eq_top_iff.mp normalizer_P

theorem odd_card_frattini_of_pCore_eq_bot {K : Type*} [Group K] [Finite K]
    (h : CFSG.pCore 2 K = ⊥) : Odd (Nat.card (frattini K)) := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow 2 (frattini K)) := inferInstance
  have hn : (P.map (frattini K).subtype).Normal := frattini_sylow_normal K 2 P
  have h2 : IsPGroup 2 (P.map (frattini K).subtype) := P.isPGroup'.map _
  have hle : P.map (frattini K).subtype ≤ CFSG.pCore 2 K := le_sSup ⟨hn, h2⟩
  rw [h] at hle
  have hP : (P : Subgroup (frattini K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : K) ∈ (⊥ : Subgroup K) := hle ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  have hcard : Nat.card P = 2 ^ (Nat.card (frattini K)).factorization 2 := P.card_eq_multiplicity
  rw [hP, Subgroup.card_bot] at hcard
  have hf : (Nat.card (frattini K)).factorization 2 = 0 := by
    rcases Nat.pow_eq_one.mp hcard.symm with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hndvd : ¬ 2 ∣ Nat.card (frattini K) := by
    intro hd
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hd
    omega
  exact Nat.odd_iff.mpr (by omega)

theorem odd_card_frattini_quotient_core (K : Type*) [Group K] [Finite K] :
    Odd (Nat.card (frattini (K ⧸ CFSG.pCore 2 K))) :=
  odd_card_frattini_of_pCore_eq_bot CFSG.Quasithin.S151S5.pCore_two_quotient_eq_bot

theorem center_le_frattini_of_perfect {K : Type*} [Group K] (h : Group.IsPerfect K) :
    Subgroup.center K ≤ frattini K := by
  unfold frattini Order.radical
  refine le_iInf₂ fun M hM => ?_
  have hM : IsCoatom M := hM
  by_contra hnle
  have hlt : M < M ⊔ center K :=
    lt_of_le_of_ne le_sup_left (fun h' => hnle (h' ▸ le_sup_right))
  have htop : M ⊔ center K = ⊤ := hM.2 _ hlt
  have key : ∀ (a b z z' : K), z ∈ center K → z' ∈ center K → ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
    intro a b z z' hz hz'
    rw [commutatorElement_def, commutatorElement_def]
    have h1 := mem_center_iff.mp hz
    have h2 := mem_center_iff.mp hz'
    calc a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹
        = a * (z * (b * z')) * z⁻¹ * a⁻¹ * (z'⁻¹ * b⁻¹) := by group
      _ = a * ((b * z') * z) * z⁻¹ * a⁻¹ * (z'⁻¹ * b⁻¹) := by rw [← h1 (b * z')]
      _ = a * b * z' * a⁻¹ * (z'⁻¹ * b⁻¹) := by group
      _ = a * b * (a⁻¹ * z') * (z'⁻¹ * b⁻¹) := by rw [h2 a⁻¹]; group
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have hcomm : commutator K ≤ M := by
    rw [_root_.commutator_def, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨g, -, g', -, rfl⟩
    have hg : g ∈ M ⊔ center K := htop ▸ mem_top g
    have hg' : g' ∈ M ⊔ center K := htop ▸ mem_top g'
    obtain ⟨m, hm, z, hz, rfl⟩ := mem_sup_of_normal_right.mp hg
    obtain ⟨m', hm', z', hz', rfl⟩ := mem_sup_of_normal_right.mp hg'
    rw [key m m' z z' hz hz', commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')
  rw [Group.isPerfect_def.mp h] at hcomm
  exact hM.1 (top_le_iff.mp hcomm)

theorem eq_of_trivial_mod_frattini {K : Type*} [Group K] [Finite K]
    (hodd : Odd (Nat.card (frattini K))) (σ : K ≃* K) {n : ℕ}
    (hσ : ∀ y : K, (σ : K → K)^[2 ^ n] y = y)
    (htriv : ∀ y : K, σ y * y⁻¹ ∈ frattini K) (y : K) : σ y = y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let F : Subgroup K := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id K)
  have hσN : ∀ z ∈ frattini K, σ z ∈ frattini K := by
    intro z hz
    have := Subgroup.characteristic_iff_map_eq.mp (inferInstance : (frattini K).Characteristic) σ
    rw [← this]
    exact Subgroup.mem_map_of_mem σ.toMonoidHom hz
  have hsup : F ⊔ frattini K = ⊤ := by
    rw [eq_top_iff]
    intro y _
    let S : Type _ := {z : K // y⁻¹ * z ∈ frattini K}
    have hSmem : ∀ z : S, y⁻¹ * σ z.1 ∈ frattini K := by
      intro z
      have h1 : y⁻¹ * σ z.1 = (y⁻¹ * (σ y * y⁻¹) * y) * σ (y⁻¹ * z.1) := by
        simp only [map_mul, map_inv]
        group
      rw [h1]
      refine (frattini K).mul_mem ?_ (hσN _ z.2)
      have := (inferInstance : (frattini K).Normal).conj_mem _ (htriv y) y⁻¹
      simpa using this
    let g : Function.End S := fun z => ⟨σ z.1, hSmem z⟩
    have hgit : ∀ (m : ℕ) (z : S), ((g ^ m) z).1 = (σ : K → K)^[m] z.1 := by
      intro m
      induction m with
      | zero => intro z; rfl
      | succ m ih =>
        intro z
        have h1 : (g ^ (m + 1)) z = (g ^ m) (g z) := rfl
        rw [h1, ih, Function.iterate_succ_apply]
    have hg : g ^ 2 ^ n = 1 := by
      funext z
      exact Subtype.ext (by rw [hgit]; exact hσ z.1)
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) hg
    let e : S ≃ frattini K :=
      { toFun := fun z => ⟨y⁻¹ * z.1, z.2⟩
        invFun := fun w => ⟨y * w.1, by simpa using w.2⟩
        left_inv := fun z => by ext; simp
        right_inv := fun w => by ext; simp }
    have hcard : Fintype.card S = Nat.card (frattini K) := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_congr e
    have hpos : 0 < Fintype.card (Function.fixedPoints g) := by
      have h1 : Fintype.card (Function.fixedPoints g) % 2 = 1 := by
        have h2 := hmod
        rw [hcard] at h2
        have h3 : Nat.card (frattini K) % 2 = 1 := Nat.odd_iff.mp hodd
        have h4 : Nat.card (frattini K) % 2 = Fintype.card (Function.fixedPoints g) % 2 := h2
        omega
      omega
    obtain ⟨⟨z, hz⟩⟩ := Fintype.card_pos_iff.mp hpos
    have hσz : σ z.1 = z.1 := by
      have := congrArg Subtype.val hz
      exact this
    have hzF : z.1 ∈ F := hσz
    have : y = z.1 * (y⁻¹ * z.1)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hzF ((frattini K).inv_mem z.2)
  have hF : F = ⊤ := frattini_nongenerating (K := F) (by rw [hsup])
  have hyF : y ∈ F := by rw [hF]; exact Subgroup.mem_top y
  exact hyF

@[expose] def phiPre (H : Subgroup G) : Subgroup G :=
  ((frattini (↥H ⧸ CFSG.pCore 2 ↥H)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

theorem mem_phiPre {H : Subgroup G} {x : G} :
    x ∈ phiPre H ↔ ∃ hx : x ∈ H,
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩ ∈ frattini (↥H ⧸ CFSG.pCore 2 ↥H) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem phiPre_le (H : Subgroup G) : phiPre H ≤ H := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem pCoreOf_conj_mem {X : Subgroup G} [X.Normal] {g x : G} (hx : x ∈ pCoreOf 2 X) :
    g * x * g⁻¹ ∈ pCoreOf 2 X := by
  obtain ⟨hxX, hxp⟩ := mem_pCoreOf.mp hx
  have hmap := Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (CFSG.pCore 2 ↥X).Characteristic) (MulAut.conjNormal g)
  have h1 : MulAut.conjNormal g ⟨x, hxX⟩ ∈ CFSG.pCore 2 ↥X := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hxp
  refine mem_pCoreOf.mpr ⟨Subgroup.Normal.conj_mem inferInstance x hxX g, ?_⟩
  have e : (⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hxX g⟩ : ↥X) =
      MulAut.conjNormal g ⟨x, hxX⟩ := Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [e]
  exact h1

@[expose] noncomputable def conjQuot (X : Subgroup G) [X.Normal] (g : G) :
    (↥X ⧸ CFSG.pCore 2 ↥X) ≃* (↥X ⧸ CFSG.pCore 2 ↥X) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥X) (MulAut.conjNormal g)
    (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore 2 ↥X).Characteristic) (MulAut.conjNormal g))

theorem conjQuot_mk {X : Subgroup G} [X.Normal] (g : G) (x : ↥X) :
    conjQuot X g (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) (MulAut.conjNormal g x) := rfl

theorem phiPre_conj_mem {X : Subgroup G} [X.Normal] {g x : G} (hx : x ∈ phiPre X) :
    g * x * g⁻¹ ∈ phiPre X := by
  obtain ⟨hxX, hxp⟩ := mem_phiPre.mp hx
  refine mem_phiPre.mpr ⟨Subgroup.Normal.conj_mem inferInstance x hxX g, ?_⟩
  have hmap := Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (frattini (↥X ⧸ CFSG.pCore 2 ↥X)).Characteristic) (conjQuot X g)
  have h1 : conjQuot X g (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hxX⟩) ∈
      frattini (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hxp
  rw [conjQuot_mk] at h1
  have e : (⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hxX g⟩ : ↥X) =
      MulAut.conjNormal g ⟨x, hxX⟩ := Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [e]
  exact h1


theorem pCoreOf_le_of_isSubnormal {H K : Subgroup G} (h : CFSG.Open.IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    have hHM : M ≤ normalizer (H : Set G) := (normal_subgroupOf_iff_le_normalizer hle).mp hN
    exact le_pCoreOf_of_le_normalizer ((pCoreOf_le H).trans hle)
      (hHM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup H)

theorem inf_pCoreOf_eq {L X : Subgroup G} (hLX : L ≤ X) (hsub : CFSG.Open.IsSubnormal L X) :
    L ⊓ pCoreOf 2 X = pCoreOf 2 L := by
  apply le_antisymm
  · have hQN : L ≤ normalizer (pCoreOf 2 X : Set G) := hLX.trans (le_normalizer_pCoreOf X)
    have hN : L ≤ normalizer ((L ⊓ pCoreOf 2 X : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hQN hx⟩
    exact le_pCoreOf_of_le_normalizer inf_le_left hN ((pCoreOf_isPGroup X).to_le inf_le_right)
  · exact le_inf (pCoreOf_le L) (pCoreOf_le_of_isSubnormal hsub)

theorem pow_mem_of_sup_pCoreOf_eq {X K : Subgroup G} (hKn : ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (h : K ⊔ pCoreOf 2 X = X) : ∀ x ∈ X, ∃ m : ℕ, x ^ 2 ^ m ∈ K := by
  intro x hx
  rw [← h] at hx
  have hNorm : pCoreOf 2 X ≤ normalizer (K : Set G) :=
    le_normalizer_of_forall_conj_mem fun s hs k hk => hKn s (pCoreOf_le X hs) k hk
  obtain ⟨k, hk, q, hq, rfl⟩ := CFSG.Quasithin.S151S5.mem_mul_of_le_normalizer hNorm hx
  obtain ⟨m, hm⟩ := isPGroup_iff_forall_mem.mp (pCoreOf_isPGroup X) q hq
  obtain ⟨q', hq', hqe⟩ :=
    CFSG.Quasithin.S151S5.mul_pow_mem_of_mem_normalizer (hNorm hq) hk (2 ^ m)
  exact ⟨m, by rw [hqe, hm, mul_one]; exact hq'⟩

theorem sup_pCoreOf_eq_of_sup_phiPre_eq [Finite G] {X K : Subgroup G} (hKX : K ≤ X)
    (h : K ⊔ phiPre X = X) : K ⊔ pCoreOf 2 X = X := by
  let Q : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* ↥X ⧸ Q := QuotientGroup.mk' Q
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hK' : K.subgroupOf X ⊔ (phiPre X).subgroupOf X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKX,
      Subgroup.map_subgroupOf_eq_of_le (phiPre_le X), h, Subgroup.map_top, Subgroup.range_subtype]
  have hphi : ((phiPre X).subgroupOf X).map π ≤ frattini (↥X ⧸ Q) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyX, hyf⟩ := mem_phiPre.mp hy
    exact hyf
  have h1 : (K.subgroupOf X).map π ⊔ frattini (↥X ⧸ Q) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup (↥X ⧸ Q)) = (⊤ : Subgroup ↥X).map π :=
          (Subgroup.map_top_of_surjective π hπ).symm
      _ = (K.subgroupOf X ⊔ (phiPre X).subgroupOf X).map π := by rw [hK']
      _ = (K.subgroupOf X).map π ⊔ ((phiPre X).subgroupOf X).map π := Subgroup.map_sup _ _ _
      _ ≤ _ := sup_le_sup_left hphi _
  have h2 : (K.subgroupOf X).map π = ⊤ := frattini_nongenerating h1
  have h3 : K.subgroupOf X ⊔ Q = ⊤ := by
    have := Subgroup.comap_map_eq π (K.subgroupOf X)
    rw [h2, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  apply le_antisymm (sup_le hKX (pCoreOf_le X))
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥X) ∈ K.subgroupOf X ⊔ Q := h3 ▸ Subgroup.mem_top _
  have h4 := Subgroup.mem_map_of_mem X.subtype hx'
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKX] at h4
  exact h4

theorem kl_of_caseII [Finite G] {X T K : Subgroup G} [X.Normal]
    (hres : ∀ N : Subgroup G, N ≤ X → (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      (∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = X)
    (hirr : ∀ N : Subgroup G, N ≤ X → phiPre X ≤ N → (∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N) →
      N = phiPre X ∨ N = X)
    (hKX : K ≤ X) (hKn : ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKT : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hK : K ≠ X) : K ≤ phiPre X := by
  have hN : ∀ t ∈ T, ∀ x ∈ K ⊔ phiPre X, t * x * t⁻¹ ∈ K ⊔ phiPre X :=
    fun t ht x hx => conj_mem_sup (fun a ha => hKT t ht a ha) (fun b hb => phiPre_conj_mem hb) hx
  rcases hirr (K ⊔ phiPre X) (sup_le hKX (phiPre_le X)) le_sup_right hN with h | h
  · exact le_sup_left.trans h.le
  · exfalso
    apply hK
    refine hres K hKX hKn ?_
    exact pow_mem_of_sup_pCoreOf_eq hKn (sup_pCoreOf_eq_of_sup_phiPre_eq hKX h)


theorem kl_of_caseI [Finite G] {X T L K : Subgroup G} [X.Normal]
    (hres : ∀ N : Subgroup G, N ≤ X → (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      (∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = X)
    (hLsub : CFSG.Open.IsSubnormal L ⊤) (hperfL : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hX : X = Subgroup.closure {x | ∃ h ∈ T, ∃ z ∈ L, h * z * h⁻¹ = x})
    (hKX : K ≤ X) (hKn : ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKT : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hK : K ≠ X) : K ≤ phiPre X := by
  let Q : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π : ↥X →* ↥X ⧸ Q := QuotientGroup.mk' Q
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hLX : L ≤ X := by
    rw [hX]
    intro z hz
    exact Subgroup.subset_closure ⟨1, T.one_mem, z, hz, by simp⟩
  have hgen : ∀ t ∈ T, ∀ z ∈ L, t * z * t⁻¹ ∈ X := by
    intro t ht z hz
    rw [hX]
    exact Subgroup.subset_closure ⟨t, ht, z, hz, rfl⟩
  have hLsubX : CFSG.Open.IsSubnormal L X := by
    have := hLsub.inf_of_le (le_top : X ≤ ⊤)
    rwa [inf_eq_left.mpr hLX] at this
  let ψ : ↥L →* ↥X ⧸ Q := π.comp (Subgroup.inclusion hLX)
  let J : Subgroup (↥X ⧸ Q) := ψ.range
  have hJmem : ∀ z (hz : z ∈ L), π ⟨z, hLX hz⟩ ∈ J := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have hJeq : J = (L.subgroupOf X).map π := by
    show ψ.range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkerψ : ψ.ker = CFSG.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    have h0 : ψ x = 1 ↔ Subgroup.inclusion hLX x ∈ Q :=
      QuotientGroup.eq_one_iff (N := Q) (Subgroup.inclusion hLX x)
    rw [h0]
    constructor
    · intro hx
      have h1 : (x : G) ∈ pCoreOf 2 X := mem_pCoreOf.mpr ⟨hLX x.2, hx⟩
      have h2 : (x : G) ∈ L ⊓ pCoreOf 2 X := ⟨x.2, h1⟩
      rw [inf_pCoreOf_eq hLX hLsubX] at h2
      obtain ⟨hxL, hxp⟩ := mem_pCoreOf.mp h2
      exact hxp
    · intro hx
      have h1 : (x : G) ∈ pCoreOf 2 L := mem_pCoreOf.mpr ⟨x.2, hx⟩
      have h2 := pCoreOf_le_of_isSubnormal hLsubX h1
      obtain ⟨hxX, hxp⟩ := mem_pCoreOf.mp h2
      exact hxp
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have hJq : CFSG.IsQuasisimple ↥J := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hJsub : J.IsSubnormal := by
    rw [hJeq]
    exact ((CFSG.Open.IsSubnormal.iff_subgroupOf hLX).mp hLsubX).map hπ
  have hJcomp : CFSG.IsComponent J := ⟨hJq, hJsub⟩
  have hKXn : (K.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hKn g.1 g.2 n.1 hn⟩
  have hKbn : ((K.subgroupOf X).map π).Normal := hKXn.map π hπ
  have hconj : ∀ (t z : G) (hz : z ∈ X) (w : G) (hw : w ∈ X), w = t * z * t⁻¹ →
      conjQuot X t (π ⟨z, hz⟩) = π ⟨w, hw⟩ := by
    intro t z hz w hw hwe
    rw [conjQuot_mk]
    exact congrArg π (Subtype.ext (by simp [MulAut.conjNormal_apply, hwe]))
  have hKinv : ∀ u ∈ T, ∀ y ∈ (K.subgroupOf X).map π, conjQuot X u y ∈ (K.subgroupOf X).map π := by
    rintro u hu _ ⟨⟨k, hkX⟩, hk, rfl⟩
    have hk' : k ∈ K := hk
    have huk : u * k * u⁻¹ ∈ X := Subgroup.Normal.conj_mem inferInstance k hkX u
    rw [hconj u k hkX _ huk rfl]
    exact ⟨⟨u * k * u⁻¹, huk⟩, hKT u hu k hk', rfl⟩
  have hdich : ∀ t ∈ T, J.map (conjQuot X t).toMonoidHom ≤ (K.subgroupOf X).map π ∨
      ⁅J.map (conjQuot X t).toMonoidHom, (K.subgroupOf X).map π⁆ = ⊥ := fun t _ =>
    CFSG.LocalCores.component_normal_subgroup
      (CFSG.LocalCores.isComponent_map_mulEquiv _ hJcomp) hKbn
  have hJt : ∀ t (ht : t ∈ T), ∀ z (hz : z ∈ L), π ⟨t * z * t⁻¹, hgen t ht z hz⟩ ∈
      J.map (conjQuot X t).toMonoidHom := by
    intro t ht z hz
    rw [← hconj t z (hLX hz) _ (hgen t ht z hz) rfl]
    exact Subgroup.mem_map_of_mem _ (hJmem z hz)
  by_cases hA : ∃ t ∈ T, J.map (conjQuot X t).toMonoidHom ≤ (K.subgroupOf X).map π
  ·
    exfalso
    obtain ⟨t₀, ht₀, hle⟩ := hA
    have hall : ∀ h (hh : h ∈ T), ∀ z (hz : z ∈ L),
        π ⟨h * z * h⁻¹, hgen h hh z hz⟩ ∈ (K.subgroupOf X).map π := by
      intro h hh z hz
      have h1 := hle (hJt t₀ ht₀ z hz)
      have h2 := hKinv (h * t₀⁻¹) (T.mul_mem hh (T.inv_mem ht₀)) _ h1
      have h3 := hconj (h * t₀⁻¹) (t₀ * z * t₀⁻¹) (hgen t₀ ht₀ z hz) (h * z * h⁻¹)
        (hgen h hh z hz) (by group)
      rw [h3] at h2
      exact h2
    have hXB : X ≤ (((K.subgroupOf X).map π).comap π).map X.subtype := by
      refine hX.le.trans ((Subgroup.closure_le _).mpr ?_)
      rintro _ ⟨h, hh, z, hz, rfl⟩
      exact ⟨⟨h * z * h⁻¹, hgen h hh z hz⟩, hall h hh z hz, rfl⟩
    have hsup : K ⊔ pCoreOf 2 X = X := by
      apply le_antisymm (sup_le hKX (pCoreOf_le X))
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hXB hx
      obtain ⟨k, hk, hky⟩ := hy
      have hy' : y = ⟨x, hx⟩ := Subtype.ext hyx
      have h1 : k⁻¹ * y ∈ Q := QuotientGroup.eq.mp hky
      have h2 : (k : G)⁻¹ * x ∈ pCoreOf 2 X := by
        subst hy'
        exact mem_pCoreOf.mpr ⟨X.mul_mem (X.inv_mem k.2) hx, h1⟩
      have h3 : x = (k : G) * ((k : G)⁻¹ * x) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk) h2
    exact hK (hres K hKX hKn (pow_mem_of_sup_pCoreOf_eq hKn hsup))
  · push_neg at hA
    have hcen : ∀ (k : G) (hk : k ∈ K), π ⟨k, hKX hk⟩ ∈ Subgroup.center (↥X ⧸ Q) := by
      intro k hk
      let c : ↥X ⧸ Q := π ⟨k, hKX hk⟩
      have hcK : c ∈ (K.subgroupOf X).map π := ⟨⟨k, hKX hk⟩, hk, rfl⟩
      have hgenc : ∀ t (ht : t ∈ T), ∀ z (hz : z ∈ L),
          π ⟨t * z * t⁻¹, hgen t ht z hz⟩ * c = c * π ⟨t * z * t⁻¹, hgen t ht z hz⟩ := by
        intro t ht z hz
        have hd := (hdich t ht).resolve_left (hA t ht)
        have h1 := Subgroup.commutator_mem_commutator (hJt t ht z hz) hcK
        rw [hd, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have hXZ : X ≤ ((Subgroup.centralizer ({c} : Set (↥X ⧸ Q))).comap π).map X.subtype := by
        refine hX.le.trans ((Subgroup.closure_le _).mpr ?_)
        rintro _ ⟨h, hh, z, hz, rfl⟩
        refine ⟨⟨h * z * h⁻¹, hgen h hh z hz⟩, ?_, rfl⟩
        show π ⟨h * z * h⁻¹, hgen h hh z hz⟩ ∈ Subgroup.centralizer ({c} : Set (↥X ⧸ Q))
        rw [Subgroup.mem_centralizer_iff]
        intro c' hc'
        rw [Set.mem_singleton_iff.mp hc']
        exact (hgenc h hh z hz).symm
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hπ g
      obtain ⟨y, hy, hyx⟩ := hXZ x.2
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      have hy2 : π y ∈ Subgroup.centralizer ({c} : Set (↥X ⧸ Q)) := hy
      rw [Subgroup.mem_centralizer_iff] at hy2
      exact (hy2 c (Set.mem_singleton c)).symm
    have hXX : ⁅X, X⁆ = X := by
      apply le_antisymm (Subgroup.commutator_le_right X X)
      refine hX.le.trans ((Subgroup.closure_le _).mpr ?_)
      rintro _ ⟨h, hh, z, hz, rfl⟩
      have hzXX : z ∈ ⁅X, X⁆ := by
        have : z ∈ ⁅L, L⁆ := by rw [hperfL]; exact hz
        exact Subgroup.commutator_mono hLX hLX this
      exact Subgroup.Normal.conj_mem inferInstance z hzXX h
    haveI : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXX
    have hperf : Group.IsPerfect (↥X ⧸ Q) := inferInstance
    intro k hk
    exact mem_phiPre.mpr ⟨hKX hk, center_le_frattini_of_perfect hperf (hcen k hk)⟩

theorem conjQuot_mul (X : Subgroup G) [X.Normal] (a b : G) (y : ↥X ⧸ CFSG.pCore 2 ↥X) :
    conjQuot X (a * b) y = conjQuot X a (conjQuot X b y) := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    change conjQuot X (a * b) (QuotientGroup.mk' _ x) =
      conjQuot X a (conjQuot X b (QuotientGroup.mk' _ x))
    rw [conjQuot_mk, conjQuot_mk, conjQuot_mk, map_mul]
    rfl

theorem conjQuot_one (X : Subgroup G) [X.Normal] (y : ↥X ⧸ CFSG.pCore 2 ↥X) :
    conjQuot X 1 y = y := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    change conjQuot X 1 (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
    rw [conjQuot_mk, map_one]
    rfl

theorem conjQuot_iterate (X : Subgroup G) [X.Normal] (t : G) (m : ℕ) (y : ↥X ⧸ CFSG.pCore 2 ↥X) :
    ((conjQuot X t : (↥X ⧸ CFSG.pCore 2 ↥X) → (↥X ⧸ CFSG.pCore 2 ↥X)))^[m] y =
      conjQuot X (t ^ m) y := by
  induction m generalizing y with
  | zero => rw [pow_zero, conjQuot_one]; rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', conjQuot_mul]

theorem o2_core_mem {Γ G' : Type*} [Group Γ] [Finite Γ] [Group G'] {X T : Subgroup Γ} [X.Normal]
    (hT : IsPGroup 2 ↥T)
    (hres : ∀ N : Subgroup Γ, N ≤ X → (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      (∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = X)
    (hKL : ∀ K : Subgroup Γ, K ≤ X → (∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) → K ≠ X → K ≤ phiPre X)
    (ρ : Γ →* G') (hQ : pCoreOf 2 X ≤ ρ.ker) (hnt : ¬ X ≤ ρ.ker) :
    ∀ t ∈ T, ρ t ∈ pCoreOf 2 ((X ⊔ T).map ρ) → t ∈ pCoreOf 2 (X ⊔ T) := by
  intro t₀ ht₀ hρt₀
  set H : Subgroup Γ := X ⊔ T with hH
  set D : Subgroup G' := pCoreOf 2 (H.map ρ) with hD
  have hXH : X ≤ H := le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hDn : ∀ h ∈ H, ∀ d ∈ D, ρ h * d * (ρ h)⁻¹ ∈ D := by
    intro h hh d hd
    have := le_normalizer_pCoreOf (H.map ρ) (Subgroup.mem_map_of_mem ρ hh)
    exact (mem_normalizer_iff.mp this d).mp hd
  have hD2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k = 1 := isPGroup_iff_forall_mem.mp (pCoreOf_isPGroup _)
  set C : Subgroup Γ := X ⊓ ρ.ker with hC
  have hCX : C ≤ X := inf_le_left
  have hCQ : pCoreOf 2 X ≤ C := le_inf (pCoreOf_le X) hQ
  have hCn : ∀ g ∈ X, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    refine ⟨X.mul_mem (X.mul_mem hg hc.1) (X.inv_mem hg), ?_⟩
    have h1 : ρ c = 1 := hc.2
    simp [MonoidHom.mem_ker, map_mul, h1]
  have hCne : C ≠ X := by
    intro h
    apply hnt
    intro x hx
    have : x ∈ C := by rw [h]; exact hx
    exact this.2
  set E : Subgroup Γ := X ⊓ D.comap ρ with hE
  have hEn : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E := by
    intro h hh e he
    refine ⟨Subgroup.Normal.conj_mem inferInstance e he.1 h, ?_⟩
    show ρ (h * e * h⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv]
    exact hDn h hh _ he.2
  have hEC : ∀ x ∈ E, ∃ k : ℕ, x ^ 2 ^ k ∈ C := by
    intro x hx
    obtain ⟨k, hk⟩ := hD2 (ρ x) hx.2
    refine ⟨k, X.pow_mem hx.1 _, ?_⟩
    show ρ (x ^ 2 ^ k) = 1
    rw [map_pow]
    exact hk
  have hEne : E ≠ X := by
    intro h
    apply hCne
    exact hres C hCX hCn (fun x hx => hEC x (by rw [h]; exact hx))
  have hEP : E ≤ phiPre X := hKL E inf_le_left (fun g hg k hk => hEn g (hXH hg) k hk)
    (fun t ht k hk => hEn t (hTH ht) k hk) hEne
  have hCE : C ≤ E := fun c hc => ⟨hc.1, by
    show ρ c ∈ D
    rw [show ρ c = 1 from hc.2]
    exact D.one_mem⟩
  have hodd := odd_card_frattini_quotient_core (↥X)
  have hEC' : E ≤ C := by
    intro x hx
    obtain ⟨k, hk⟩ := hEC x hx
    obtain ⟨hxX, hxf⟩ := mem_phiPre.mp (hEP hx)
    have hm : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hxX⟩) ^
        Nat.card (frattini (↥X ⧸ CFSG.pCore 2 ↥X)) = 1 := by
      have := pow_card_eq_one' (x := (⟨_, hxf⟩ : ↥(frattini (↥X ⧸ CFSG.pCore 2 ↥X))))
      exact congrArg Subtype.val this
    have hxm : x ^ Nat.card (frattini (↥X ⧸ CFSG.pCore 2 ↥X)) ∈ pCoreOf 2 X := by
      rw [← map_pow] at hm
      exact mem_pCoreOf.mpr ⟨X.pow_mem hxX _, (QuotientGroup.eq_one_iff _).mp hm⟩
    exact mem_of_pow_mem_of_coprime (a := 2 ^ k) (b := Nat.card (frattini (↥X ⧸ CFSG.pCore 2 ↥X)))
      (Nat.Coprime.pow_left k (Odd.coprime_two_left hodd)) hk (hCQ hxm)
  have hcomm : ∀ t ∈ T, ρ t ∈ D → ∀ x ∈ X, x * t * x⁻¹ * t⁻¹ ∈ C := by
    intro t ht hρt x hx
    have hxE : x * t * x⁻¹ * t⁻¹ ∈ E := by
      refine ⟨?_, ?_⟩
      · have h1 : t * x⁻¹ * t⁻¹ ∈ X := Subgroup.Normal.conj_mem inferInstance x⁻¹ (X.inv_mem hx) t
        have h2 := X.mul_mem hx h1
        have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
        rw [e]
        exact h2
      · show ρ (x * t * x⁻¹ * t⁻¹) ∈ D
        simp only [map_mul, map_inv]
        exact D.mul_mem (hDn x (hXH hx) _ hρt) (D.inv_mem hρt)
    exact hEC' hxE
  have hQc : ∀ t ∈ T, ρ t ∈ D → ∀ x ∈ X, x * t * x⁻¹ * t⁻¹ ∈ pCoreOf 2 X := by
    intro t ht hρt x hx
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    let Q : Subgroup ↥X := CFSG.pCore 2 ↥X
    let π : ↥X →* ↥X ⧸ Q := QuotientGroup.mk' Q
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
    have hσ : ∀ y : ↥X ⧸ Q, ((conjQuot X t : (↥X ⧸ Q) ≃* (↥X ⧸ Q)) : (↥X ⧸ Q) → (↥X ⧸ Q))^[2 ^ n] y
        = y := by
      intro y
      rw [conjQuot_iterate, htn, conjQuot_one]
    have htriv : ∀ y : ↥X ⧸ Q, conjQuot X t y * y⁻¹ ∈ frattini (↥X ⧸ Q) := by
      intro y
      obtain ⟨x', rfl⟩ := hπ y
      have hx'X : (x' : Γ) ∈ X := x'.2
      have hw : t * (x' : Γ) * t⁻¹ * (x' : Γ)⁻¹ ∈ phiPre X := by
        have h1 := (phiPre X).inv_mem (hEP (hCE (hcomm t ht hρt (x' : Γ) hx'X)))
        have e : (t * (x' : Γ) * t⁻¹ * (x' : Γ)⁻¹) = ((x' : Γ) * t * (x' : Γ)⁻¹ * t⁻¹)⁻¹ := by group
        rw [e]
        exact h1
      obtain ⟨hwX, hwf⟩ := mem_phiPre.mp hw
      have e2 : conjQuot X t (π x') * (π x')⁻¹ = π ⟨t * (x' : Γ) * t⁻¹ * (x' : Γ)⁻¹, hwX⟩ := by
        rw [conjQuot_mk, ← map_inv, ← map_mul]
        exact congrArg π (Subtype.ext (by simp [MulAut.conjNormal_apply]))
      rw [e2]
      exact hwf
    have hfix := eq_of_trivial_mod_frattini hodd (conjQuot X t) hσ htriv (π ⟨x⁻¹, X.inv_mem hx⟩)
    rw [conjQuot_mk] at hfix
    have h3 := QuotientGroup.eq.mp hfix.symm
    refine mem_pCoreOf.mpr ⟨?_, ?_⟩
    · have h1 : t * x⁻¹ * t⁻¹ ∈ X := Subgroup.Normal.conj_mem inferInstance x⁻¹ (X.inv_mem hx) t
      have h2 := X.mul_mem hx h1
      have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
      rw [e]
      exact h2
    · have e : (⟨x⁻¹, X.inv_mem hx⟩ : ↥X)⁻¹ * MulAut.conjNormal t ⟨x⁻¹, X.inv_mem hx⟩ =
          ⟨x * t * x⁻¹ * t⁻¹, by
            have h1 : t * x⁻¹ * t⁻¹ ∈ X := Subgroup.Normal.conj_mem inferInstance x⁻¹ (X.inv_mem hx) t
            have h2 := X.mul_mem hx h1
            have e' : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
            rw [e']
            exact h2⟩ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply, mul_assoc])
      rw [e] at h3
      exact h3
  set E₂ : Subgroup Γ := T ⊓ D.comap ρ with hE₂
  set Y : Subgroup Γ := pCoreOf 2 X ⊔ E₂ with hY
  have hE₂n : ∀ s ∈ T, ∀ e ∈ E₂, s * e * s⁻¹ ∈ E₂ := by
    intro s hs e he
    refine ⟨T.mul_mem (T.mul_mem hs he.1) (T.inv_mem hs), ?_⟩
    show ρ (s * e * s⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv]
    exact hDn s (hTH hs) _ he.2
  have hYT : IsPGroup 2 ↥Y := by
    refine IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup X) (hT.to_le inf_le_left) ?_
    exact le_normalizer_of_forall_conj_mem fun s hs q hq => by
      have := pCoreOf_conj_mem (X := X) (g := s) hq
      exact this
  have hYH : Y ≤ H := sup_le ((pCoreOf_le X).trans hXH) (inf_le_left.trans hTH)
  have hYn : H ≤ normalizer (Y : Set Γ) := by
    refine sup_le ?_ ?_
    · refine le_normalizer_of_forall_conj_mem fun x hx y hy => ?_
      refine conj_mem_of_mem_sup (fun a ha => Subgroup.mem_sup_left (pCoreOf_conj_mem ha))
        (fun e he => ?_) hy
      have h1 := hQc e he.1 he.2 x hx
      have h2 : x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
      rw [h2]
      exact Subgroup.mul_mem_sup h1 he
    · refine le_normalizer_of_forall_conj_mem fun s hs y hy => ?_
      exact conj_mem_of_mem_sup (fun a ha => Subgroup.mem_sup_left (pCoreOf_conj_mem ha))
        (fun e he => Subgroup.mem_sup_right (hE₂n s hs e he)) hy
  have hYo : Y ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer hYH hYn hYT
  exact hYo (Subgroup.mem_sup_right ⟨ht₀, hρt₀⟩)

theorem sylow_map {Γ G' : Type*} [Group Γ] [Group G'] (ρ : Γ →* G') {T H : Subgroup Γ}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 ↥T) (hidx : ¬ 2 ∣ T.index) :
    IsPGroup 2 ↥(T.map ρ) ∧ ¬ 2 ∣ ((T.map ρ).subgroupOf (H.map ρ)).index := by
  refine ⟨hT2.of_surjective (ρ.subgroupMap T) (ρ.subgroupMap_surjective T), ?_⟩
  intro h2
  have h1 : ((T.map ρ).subgroupOf (H.map ρ)).index = (T.map ρ).relIndex (H.map ρ) := rfl
  rw [h1, Subgroup.relIndex_map_map] at h2
  have h3 : (T ⊔ ρ.ker).relIndex (H ⊔ ρ.ker) ∣ T.index :=
    (Subgroup.relIndex_dvd_index_of_le (sup_le_sup_right hTH _)).trans
      (Subgroup.index_dvd_of_le le_sup_left)
  exact hidx (h2.trans h3)

theorem pCoreOf_le_of_sylow {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 ↥S)
    (hidx : ¬ 2 ∣ (S.subgroupOf H).index) : pCoreOf 2 H ≤ S := by
  have hS' : IsPGroup 2 ↥(S.subgroupOf H) := isPGroup_subgroupOf hS
  let P : Sylow 2 ↥H := hS'.toSylow hidx
  have h1 : CFSG.pCore 2 ↥H ≤ (P : Subgroup ↥H) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal P
  intro x hx
  obtain ⟨hxH, hxp⟩ := mem_pCoreOf.mp hx
  exact h1 hxp

theorem isQuasisimple_map_of_pCore_le_ker {G' : Type*} [Group G'] {L : Subgroup G} {ρ : G →* G'}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hker : pCoreOf 2 L ≤ ρ.ker) (hnt : ¬ L ≤ ρ.ker) : CFSG.IsQuasisimple ↥(L.map ρ) := by
  let ψ0 : ↥L →* G' := ρ.comp L.subtype
  have hψ : CFSG.pCore 2 ↥L ≤ ψ0.ker := by
    intro x hx
    have : (x : G) ∈ pCoreOf 2 L := mem_pCoreOf.mpr ⟨x.2, hx⟩
    exact hker this
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* G' := QuotientGroup.lift (CFSG.pCore 2 ↥L) ψ0 hψ
  have hψ_range : (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)).map ψ = L.map ρ := by
    ext g
    constructor
    · rintro ⟨y, -, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨QuotientGroup.mk ⟨l, hl⟩, Subgroup.mem_top _, rfl⟩
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  have hnt' : ¬ (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ ψ.ker := by
    intro h
    apply hnt
    intro l hl
    exact h (Subgroup.mem_top (QuotientGroup.mk ⟨l, hl⟩))
  have := CFSG.LocalCores.isQuasisimple_map hq' ψ hnt'
  rwa [hψ_range] at this

theorem map_closure_conj {G' : Type*} [Group G'] (ρ : G →* G') (T L : Subgroup G) :
    (Subgroup.closure {x | ∃ h ∈ T, ∃ z ∈ L, h * z * h⁻¹ = x}).map ρ =
      Subgroup.closure {x | ∃ h ∈ T.map ρ, ∃ z ∈ L.map ρ, h * z * h⁻¹ = x} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    exact ⟨ρ h, ⟨h, hh, rfl⟩, ρ z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨h, hh, z, hz, rfl⟩, by simp⟩

theorem mem_cComp_of_isQuasisimple_of_isSubnormal {K X : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hK : CFSG.Open.IsSubnormal K X) :
    K ∈ CFSG.Quasithin.cComp X := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, hK, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le hK
    have hsubK : CFSG.Open.IsSubnormal K' K :=
      CFSG.Quasithin.A3.subnormal_of_le_of_le hsub hlt.le hKX
    obtain ⟨P, hPK, hPn, hK'P⟩ := CFSG.Quasithin.A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

@[expose] noncomputable def quotMap {G' : Type*} [Group G'] (X : Subgroup G) (ρ : G →* G')
    (hker : pCoreOf 2 X ≤ ρ.ker) : (↥X ⧸ CFSG.pCore 2 ↥X) →* ↥(X.map ρ) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥X) (ρ.subgroupMap X) (by
    intro x hx
    have : (x : G) ∈ pCoreOf 2 X := mem_pCoreOf.mpr ⟨x.2, hx⟩
    exact Subtype.ext (hker this))

theorem quotMap_mk {G' : Type*} [Group G'] (X : Subgroup G) (ρ : G →* G')
    (hker : pCoreOf 2 X ≤ ρ.ker) (x : ↥X) :
    quotMap X ρ hker (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) = ρ.subgroupMap X x := rfl

theorem quotMap_surjective {G' : Type*} [Group G'] (X : Subgroup G) (ρ : G →* G')
    (hker : pCoreOf 2 X ≤ ρ.ker) : Function.Surjective (quotMap X ρ hker) := by
  intro y
  obtain ⟨x, hx⟩ := ρ.subgroupMap_surjective X y
  exact ⟨QuotientGroup.mk' _ x, by rw [quotMap_mk]; exact hx⟩

theorem isPGroup_map_of_pCore_le_ker {p : ℕ} {G' : Type*} [Group G'] {X : Subgroup G}
    {ρ : G →* G'} (hX : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X)) (hker : pCoreOf 2 X ≤ ρ.ker) :
    IsPGroup p ↥(X.map ρ) :=
  hX.of_surjective (quotMap X ρ hker) (quotMap_surjective X ρ hker)

theorem phiPre_map_le {G' : Type*} [Group G'] {X : Subgroup G} {ρ : G →* G'}
    (hker : pCoreOf 2 X ≤ ρ.ker) :
    (phiPre X).map ρ ≤ (frattini ↥(X.map ρ)).map (X.map ρ).subtype := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxX, hxf⟩ := mem_phiPre.mp hx
  have h1 := frattini_le_comap_frattini_of_surjective (quotMap_surjective X ρ hker) hxf
  exact ⟨⟨ρ x, Subgroup.mem_map_of_mem ρ hxX⟩, h1, rfl⟩

theorem frattini_map_lt {S : Subgroup G} [Finite ↥S] (hS : S ≠ ⊥) :
    (frattini ↥S).map S.subtype < S := by
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
  intro h
  apply hS
  have h1 : frattini ↥S = ⊤ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [h, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (⊥ : Subgroup ↥S) ⊔ frattini ↥S = ⊤ := by rw [h1]; exact sup_top_eq _
  have h3 : (⊥ : Subgroup ↥S) = ⊤ := frattini_nongenerating h2
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : ↥S) ∈ (⊥ : Subgroup ↥S) := by rw [h3]; exact Subgroup.mem_top _
  exact congrArg Subtype.val (Subgroup.mem_bot.mp this)

end CFSG.Quasithin.RonanD33
