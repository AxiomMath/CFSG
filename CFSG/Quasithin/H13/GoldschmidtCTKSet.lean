module

public import CFSG.Quasithin.H13.A6S1514Core
public import CFSG.Quasithin.H13.GoldschmidtCTKAbs
public import CFSG.Quasithin.H13.GoldschmidtCTKCoh

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.CTK
open scoped commutatorElement Pointwise

theorem eq_one_of_comm_c3 : ∀ σ : Perm (Fin 6),
    σ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * σ →
    σ * (swap 0 1 * swap 1 3) = (swap 0 1 * swap 1 3) * σ →
    σ * (swap 0 1 * swap 1 4) = (swap 0 1 * swap 1 4) * σ → σ = 1 := by
  decide +kernel

theorem exists_stab5_apply : ∀ i j : Fin 6, i ≠ 5 → j ≠ 5 →
    ∃ a : Perm (Fin 6), a 5 = 5 ∧ Perm.sign a = 1 ∧ a i = j := by
  decide +kernel

theorem exists_even_apply_five : ∀ j : Fin 6, ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g 5 = j := by
  decide +kernel

theorem mem_of_stab5 {P : Subgroup (Perm (Fin 6))}
    (h5 : ∀ σ : Perm (Fin 6), σ 5 = 5 → Perm.sign σ = 1 → σ ∈ P)
    {τ : Perm (Fin 6)} (hτ : τ ∈ P) (hτ5 : τ 5 ≠ 5) (hτs : Perm.sign τ = 1)
    {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) : σ ∈ P := by
  by_cases hσ5 : σ 5 = 5
  · exact h5 σ hσ5 hσ
  · obtain ⟨a, ha5, has, hai⟩ := exists_stab5_apply (τ 5) (σ 5) hτ5 hσ5
    have haP : a ∈ P := h5 a ha5 has
    have hx : σ⁻¹ * a * τ ∈ P := by
      apply h5
      · simp [Perm.mul_apply, hai]
      · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hσ, has, hτs]
        decide
    have e : σ = a * τ * (σ⁻¹ * a * τ)⁻¹ := by group
    rw [e]
    exact P.mul_mem (P.mul_mem haP hτ) (P.inv_mem hx)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem conj_mem_pCoreOf_sup {ℓ q : G} (hℓ : ℓ ∈ L) (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    ℓ * q * ℓ⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hℓ))
    q).mp hq

theorem Setting4.V_le_pCoreOf_LT (S : Setting4 G T L V) :
    V ≤ pCoreOf 2 (L ⊔ T) := by
  rw [← S.cT]
  exact fun v hv => ⟨S.V_le_T hv, S.V_le_centralizer_V hv⟩

@[expose] def Setting4.CD (S : Setting4 G T L V) : Subgroup G :=
  T ⊓ Subgroup.centralizer (S.L5 : Set G)

structure CTKHyp (S : Setting4 G T L V) : Prop where
  hat : ¬ IsHatA6 L
  short : IsShort2 S.L5
  alt : IsAltType S.L5 5
  O2 : pCoreOf 2 S.L5 = V
  cTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥

@[expose] def Setting4.YQ (S : Setting4 G T L V) : Subgroup G where
  carrier := {x | x ∈ L ∧ ∀ q ∈ pCoreOf 2 (L ⊔ T), ⁅q, x⁆ ∈ V}
  one_mem' := ⟨L.one_mem, fun q _ => by
    rw [show ⁅q, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
    exact V.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
    refine ⟨L.mul_mem hxL hyL, fun q hq => ?_⟩
    rw [comm_mul_right]
    exact V.mul_mem (hx q hq) ((Subgroup.mem_normalizer_iff.mp (S.frame.L_le hxL) _).mp (hy q hq))
  inv_mem' := by
    rintro x ⟨hxL, hx⟩
    refine ⟨L.inv_mem hxL, fun q hq => ?_⟩
    have e : ⁅q, x⁻¹⁆ = x⁻¹ * (⁅q, x⁆)⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 : (⁅q, x⁆)⁻¹ ∈ V := V.inv_mem (hx q hq)
    have := (Subgroup.mem_normalizer_iff.mp (S.frame.L_le (L.inv_mem hxL)) _).mp h1
    simpa using this

omit [Finite G] in
theorem comm_central_left {Q : Subgroup G} {x a b : G} (hx : ∀ q ∈ Q, x * q = q * x)
    (ha : a ∈ Q) (hb : b ∈ Q) : ⁅x * a, b⁆ = ⁅a, b⁆ := by
  have h1 := hx (a * b * a⁻¹) (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha))
  simp only [commutatorElement_def]
  calc x * a * b * (x * a)⁻¹ * b⁻¹ = x * (a * b * a⁻¹) * x⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * x * x⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem comm_central_right {Q : Subgroup G} {x a b : G} (hx : ∀ q ∈ Q, x * q = q * x)
    (ha : a ∈ Q) (hb : b ∈ Q) : ⁅a, x * b⁆ = ⁅a, b⁆ := by
  have h1 := hx (b * a⁻¹ * b⁻¹) (Q.mul_mem (Q.mul_mem hb (Q.inv_mem ha)) (Q.inv_mem hb))
  simp only [commutatorElement_def]
  calc a * (x * b) * a⁻¹ * (x * b)⁻¹ = a * (x * (b * a⁻¹ * b⁻¹)) * x⁻¹ := by group
    _ = a * ((b * a⁻¹ * b⁻¹) * x) * x⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem exists_central_comm {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hne : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    ∃ z ∈ ⁅Q, Q⁆, z ≠ 1 ∧ ∀ q ∈ Q, z * q = q * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  set N : Subgroup ↥Q := ⁅(⊤ : Subgroup ↥Q), ⊤⁆ with hN
  have hNbot : N ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, b, hb, hab⟩ := hne
    apply hab
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot (Subgroup.mem_top ⟨a, ha⟩)
    have h2 := Subgroup.mem_centralizer_iff.mp h1 ⟨b, hb⟩ (Subgroup.mem_top _)
    exact congrArg Subtype.val h2.symm
  have h3 := Group.IsNilpotent.inf_center_ne_bot_of_normal hNbot
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h3
  have hzN : (z : ↥Q) ∈ N := (Subgroup.mem_inf.1 z.2).1
  have hzC : (z : ↥Q) ∈ Subgroup.center ↥Q := (Subgroup.mem_inf.1 z.2).2
  refine ⟨(z : ↥Q), ?_, ?_, ?_⟩
  · have : N.map Q.subtype = ⁅Q, Q⁆ := by
      rw [hN, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← this]
    exact ⟨_, hzN, rfl⟩
  · intro h1
    apply hz1
    exact Subtype.ext (Subtype.ext h1)
  · intro q hq
    have := Subgroup.mem_center_iff.mp hzC ⟨q, hq⟩
    exact congrArg Subtype.val this.symm

theorem Setting4.comm_V_Q (S : Setting4 G T L V) {q v : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hv : v ∈ V) : v * q = q * v := by
  rw [← S.cT] at hq
  exact Subgroup.mem_centralizer_iff.mp hq.2 v hv

theorem Setting4.R_le_Q (S : Setting4 G T L V) (hhat : ¬ IsHatA6 L)
    {r : G} (hr : r ∈ L ⊓ Subgroup.centralizer (V : Set G)) : r ∈ pCoreOf 2 (L ⊔ T) :=
  pCoreOf_le_pCoreOf_sup S.T_le_NL (S.inf_centralizer_le_pCoreOf hhat hr)

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {y : G}
    (h : K.map (MulAut.conj y).toMonoidHom = K) : y ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have : y * z * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom := ⟨z, hz, by simp⟩
    rwa [h] at this
  · intro hz
    rw [← h] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := (MulAut.conj y).injective (by simpa using hwz)
    rwa [this] at hw

theorem InD6.apply_five : ∀ σ : Perm (Fin 6), InD6 σ → σ 5 ≠ 5 → σ 5 = 4 := by
  decide +kernel

omit [Finite G] in
theorem exists_odd_of_sylow {A T' : Subgroup G} (hT : IsSylowTwoOf T' A) (f : ↥A →* ℤˣ)
    {a : ↥A} (ha : f a = -1) : ∃ t : ↥A, (t : G) ∈ T' ∧ f t = -1 := by
  by_contra hcon
  push Not at hcon
  have hle : T'.subgroupOf A ≤ f.ker := by
    intro t ht
    rw [MonoidHom.mem_ker]
    rcases Int.units_eq_one_or (f t) with h1 | h1
    · exact h1
    · exact absurd h1 (hcon t ht)
  have h1 : f.ker.index ∣ (T'.subgroupOf A).index := Subgroup.index_dvd_of_le hle
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨a, ha⟩
  have h2 : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  exact hT.2.2 (h2 ▸ h1)

namespace CTKHyp

variable {S : Setting4 G T L V} (h : CTKHyp S)
include h

theorem CD_le_Q {d : G} (hd : d ∈ S.CD) : d ∈ pCoreOf 2 (L ⊔ T) := by
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hd.1
  have hcomm : ∀ τ : Perm (Fin 6), τ 5 = 5 → Perm.sign τ = 1 → τ ^ 3 = 1 →
      S.frame.ρ ⟨d, hdN⟩ * τ = τ * S.frame.ρ ⟨d, hdN⟩ := by
    intro τ h5 hs h3
    obtain ⟨x, hx, hρx⟩ := S.exists_L5_three h.hat h5 hs h3
    rw [← hρx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hd.2 x hx).symm
  have h1 : S.frame.ρ ⟨d, hdN⟩ = 1 :=
    eq_one_of_comm_c3 _ (hcomm _ (by decide) (by decide) (by decide))
      (hcomm _ (by decide) (by decide) (by decide)) (hcomm _ (by decide) (by decide) (by decide))
  rw [← S.cT]
  exact ⟨hd.1, (S.rho_eq_one_iff _).1 h1⟩

theorem Q_le_sup : pCoreOf 2 (L ⊔ T) ≤ V ⊔ S.CD := by
  have hsyl := S.isSylowTwoOf_T5 h.hat
  obtain ⟨hC, -⟩ := VolI.stmtC113c G S.L5 S.T5 hsyl S.T5_le_normalizer_L5 h.short h.alt
  rw [blockU_eq_of_alt5 h.short h.alt h.O2 S.card_V] at hC
  have hQ2 : IsPGroup 2 (pCoreOf 2 (L ⊔ T)) := pCoreOf_isPGroup 2 _
  have hQO : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (S.L5 ⊔ S.T5) := by
    refine le_pCoreOf_of_le_normalizer 2 (S.pCoreOf_LT_le_T5.trans le_sup_right) (sup_le ?_ ?_) hQ2
    · exact (S.L5_le_L.trans (le_sup_left : L ≤ L ⊔ T)).trans (le_normalizer_pCoreOf 2 _)
    · exact (S.T5_le_T.trans (le_sup_right : T ≤ L ⊔ T)).trans (le_normalizer_pCoreOf 2 _)
  refine hQO.trans (hC.le.trans ?_)
  exact sup_le_sup_left (inf_le_inf_right _ S.T5_le_T) V

theorem Q_eq : pCoreOf 2 (L ⊔ T) = V ⊔ S.CD :=
  le_antisymm h.Q_le_sup (sup_le S.V_le_pCoreOf_LT fun _ hd => h.CD_le_Q hd)

theorem CD_le_T5 : S.CD ≤ S.T5 := fun _ hd => S.pCoreOf_LT_le_T5 (h.CD_le_Q hd)

theorem V_inf_CD : V ⊓ S.CD = ⊥ := by
  have hsyl := S.isSylowTwoOf_T5 h.hat
  obtain ⟨-, hbot⟩ := VolI.stmtC113c G S.L5 S.T5 hsyl S.T5_le_normalizer_L5 h.short h.alt
  rw [blockU_eq_of_alt5 h.short h.alt h.O2 S.card_V] at hbot
  refine eq_bot_iff.2 (hbot ▸ inf_le_inf_left V ?_)
  exact le_inf (h.CD_le_T5) (fun d hd => hd.2)

theorem Q_mul : ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) = (V : Set G) * (S.CD : Set G) := by
  rw [h.Q_eq]
  exact Subgroup.coe_mul_of_right_le_normalizer_left V S.CD fun d hd => S.frame.T_le hd.1

theorem comm_Q_L5 {q k : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hk : k ∈ S.L5) : ⁅q, k⁆ ∈ V := by
  have hq' : q ∈ (V : Set G) * (S.CD : Set G) := by
    rw [← h.Q_mul]
    exact hq
  obtain ⟨v, hv, d, hd, rfl⟩ := hq'
  have hdk : d * k = k * d := (Subgroup.mem_centralizer_iff.mp hd.2 k hk).symm
  have e : ⁅v * d, k⁆ = ⁅v, k⁆ := by
    have e1 : d * k * d⁻¹ = k := by rw [hdk]; group
    simp only [commutatorElement_def]
    calc v * d * k * (v * d)⁻¹ * k⁻¹ = v * (d * k * d⁻¹) * v⁻¹ * k⁻¹ := by group
      _ = v * k * v⁻¹ * k⁻¹ := by rw [e1]
  rw [e]
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L5_le_L hk)
  have h1 : k * v⁻¹ * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hkN _).mp (V.inv_mem hv)
  have := V.mul_mem hv h1
  simpa [commutatorElement_def, mul_assoc] using this

theorem comm_Q_conj {q k ℓ : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hk : k ∈ S.L5) (hℓ : ℓ ∈ L) :
    ⁅q, ℓ⁻¹ * k * ℓ⁆ ∈ V := by
  have e : ⁅q, ℓ⁻¹ * k * ℓ⁆ = ℓ⁻¹ * ⁅ℓ * q * ℓ⁻¹, k⁆ * ℓ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have h1 := h.comm_Q_L5 (conj_mem_pCoreOf_sup hℓ hq) hk
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (S.frame.L_le hℓ)) _).mp h1
  simpa using this

theorem L5_le_YQ : S.L5 ≤ S.YQ := fun _ hk =>
  ⟨S.L5_le_L hk, fun _ hq => h.comm_Q_L5 hq hk⟩

theorem conj_L5_mem_YQ {k ℓ : G} (hk : k ∈ S.L5) (hℓ : ℓ ∈ L) : ℓ⁻¹ * k * ℓ ∈ S.YQ :=
  ⟨L.mul_mem (L.mul_mem (L.inv_mem hℓ) (S.L5_le_L hk)) hℓ, fun _ hq => h.comm_Q_conj hq hk hℓ⟩

theorem exists_YQ_lift {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) :
    ∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ S.YQ ∧ S.frame.ρ y = σ := by
  let P : Subgroup (Perm (Fin 6)) :=
    (S.YQ.comap (Subgroup.normalizer (V : Set G)).subtype).map S.frame.ρ
  have hmemP : ∀ τ : Perm (Fin 6),
      (∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ S.YQ ∧ S.frame.ρ y = τ) → τ ∈ P :=
    fun τ ⟨y, hy, hρ⟩ => ⟨y, hy, hρ⟩
  have h5 : ∀ τ : Perm (Fin 6), τ 5 = 5 → Perm.sign τ = 1 → τ ∈ P := by
    intro τ h5 hs
    obtain ⟨x, hx, hρ⟩ := S.exists_L5_rho h.hat h5 hs
    exact hmemP τ ⟨x, h.L5_le_YQ hx, hρ⟩
  have h4 : ∀ τ : Perm (Fin 6), τ 4 = 4 → Perm.sign τ = 1 → τ ∈ P := by
    intro τ h4 hs
    obtain ⟨g4, hg4s, hg45⟩ := exists_even_apply_five 4
    have hg4s' : g4⁻¹ ∈ alternatingGroup (Fin 6) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_inv, hg4s]
    obtain ⟨ℓ₀, hℓ₀L, hρℓ₀⟩ := (S.frame.image_L g4⁻¹).2 hg4s'
    have hinv : g4⁻¹ 4 = 5 := Perm.inv_eq_iff_eq.mpr hg45.symm
    have hσ'5 : (g4⁻¹ * τ * g4) 5 = 5 := by
      simp [Perm.mul_apply, hg45, h4, hinv]
    have hσ's : Perm.sign (g4⁻¹ * τ * g4) = 1 := by
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hg4s, hs]
      rfl
    obtain ⟨x, hx, hρx⟩ := S.exists_L5_rho h.hat hσ'5 hσ's
    refine hmemP τ ⟨ℓ₀⁻¹ * x * ℓ₀, h.conj_L5_mem_YQ hx hℓ₀L, ?_⟩
    rw [map_mul, map_mul, map_inv, hρℓ₀, hρx]
    group
  have hτ : (swap (0 : Fin 6) 1 * swap 1 5) ∈ P := h4 _ (by decide) (by decide)
  have hσP : σ ∈ P := mem_of_stab5 h5 hτ (by decide) (by decide) hσ
  obtain ⟨y, hy, hρ⟩ := hσP
  exact ⟨y, hy, hρ⟩

theorem L_eq_YR {ℓ : G} (hℓ : ℓ ∈ L) :
    ∃ y ∈ S.YQ, ∃ r ∈ L ⊓ Subgroup.centralizer (V : Set G), ℓ = y * r := by
  have hs : Perm.sign (S.frame.ρ ⟨ℓ, S.frame.L_le hℓ⟩) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨_, hℓ, rfl⟩)
  obtain ⟨y, hy, hρ⟩ := h.exists_YQ_lift hs
  refine ⟨y, hy, (y : G)⁻¹ * ℓ, ⟨L.mul_mem (L.inv_mem hy.1) hℓ, ?_⟩, by group⟩
  have e : (⟨(y : G)⁻¹ * ℓ, Subgroup.mul_mem _ (Subgroup.inv_mem _ y.2) (S.frame.L_le hℓ)⟩ :
      ↥(Subgroup.normalizer (V : Set G))) = y⁻¹ * ⟨ℓ, S.frame.L_le hℓ⟩ := rfl
  have h1 : S.frame.ρ (y⁻¹ * ⟨ℓ, S.frame.L_le hℓ⟩) = 1 := by
    rw [map_mul, map_inv, hρ, inv_mul_cancel]
  rw [← e] at h1
  exact (S.rho_eq_one_iff _).1 h1

theorem comm_Q_Q_mem_CD {a b : G} (ha : a ∈ pCoreOf 2 (L ⊔ T)) (hb : b ∈ pCoreOf 2 (L ⊔ T)) :
    ⁅a, b⁆ ∈ S.CD := by
  have ha' : a ∈ (V : Set G) * (S.CD : Set G) := by
    rw [← h.Q_mul]
    exact ha
  have hb' : b ∈ (V : Set G) * (S.CD : Set G) := by
    rw [← h.Q_mul]
    exact hb
  obtain ⟨v₁, hv₁, d₁, hd₁, rfl⟩ := ha'
  obtain ⟨v₂, hv₂, d₂, hd₂, rfl⟩ := hb'
  have hd₁Q : d₁ ∈ pCoreOf 2 (L ⊔ T) := h.CD_le_Q hd₁
  have hd₂Q : d₂ ∈ pCoreOf 2 (L ⊔ T) := h.CD_le_Q hd₂
  have hb2 : v₂ * d₂ ∈ pCoreOf 2 (L ⊔ T) :=
    (pCoreOf 2 (L ⊔ T)).mul_mem (S.V_le_pCoreOf_LT hv₂) hd₂Q
  rw [comm_central_left (fun q hq => S.comm_V_Q hq hv₁) hd₁Q hb2,
    comm_central_right (fun q hq => S.comm_V_Q hq hv₂) hd₁Q hd₂Q]
  exact S.CD.mul_mem (S.CD.mul_mem (S.CD.mul_mem hd₁ hd₂) (S.CD.inv_mem hd₁)) (S.CD.inv_mem hd₂)

theorem Q_abelian {a b : G} (ha : a ∈ pCoreOf 2 (L ⊔ T)) (hb : b ∈ pCoreOf 2 (L ⊔ T)) :
    a * b = b * a := by
  by_contra hab
  obtain ⟨z, hzN, hz1, hzc⟩ :=
    exists_central_comm (pCoreOf_isPGroup 2 (L ⊔ T)) ⟨a, ha, b, hb, hab⟩
  have hNCD : ⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆ ≤ S.CD := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact h.comm_Q_Q_mem_CD hx hy
  have hzCD : z ∈ S.CD := hNCD hzN
  have hzQ : z ∈ pCoreOf 2 (L ⊔ T) := h.CD_le_Q hzCD
  have hNconj : ∀ ℓ ∈ L, ∀ w ∈ ⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆,
      ℓ * w * ℓ⁻¹ ∈ ⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆ := by
    intro ℓ hℓ w hw
    have hmap : (⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆).map (MulAut.conj ℓ).toMonoidHom =
        ⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆ := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
        (le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hℓ))]
    rw [← hmap]
    exact ⟨w, hw, rfl⟩
  have hzL : ∀ ℓ ∈ L, ℓ * z = z * ℓ := by
    intro ℓ hℓ
    obtain ⟨y, hy, r, hr, rfl⟩ := h.L_eq_YR hℓ
    have hrQ : r ∈ pCoreOf 2 (L ⊔ T) := S.R_le_Q h.hat hr
    have hyz : y * z = z * y := by
      have h1 : ⁅z, y⁆ ∈ V := hy.2 z hzQ
      have h2 : ⁅z, y⁆ ∈ ⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆ := by
        have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ hzN (hNconj y hy.1 z⁻¹ (Subgroup.inv_mem _ hzN))
      have h3 : ⁅z, y⁆ ∈ V ⊓ S.CD := ⟨h1, hNCD h2⟩
      rw [h.V_inf_CD, Subgroup.mem_bot] at h3
      have h4 : z * y * z⁻¹ * y⁻¹ = 1 := h3
      calc y * z = (z * y * z⁻¹ * y⁻¹)⁻¹ * (z * y) := by group
        _ = z * y := by rw [h4]; group
    have hrz : r * z = z * r := (hzc r hrQ).symm
    calc y * r * z = y * (r * z) := by group
      _ = y * (z * r) := by rw [hrz]
      _ = (y * z) * r := by group
      _ = (z * y) * r := by rw [hyz]
      _ = z * (y * r) := by group
  have hzC : z ∈ T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hzCD.1, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => hzL ℓ hℓ⟩
  rw [h.cTL, Subgroup.mem_bot] at hzC
  exact hz1 hzC

theorem comm_Q_L {q ℓ : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hℓ : ℓ ∈ L) : ⁅q, ℓ⁆ ∈ V := by
  obtain ⟨y, hy, r, hr, rfl⟩ := h.L_eq_YR hℓ
  have hrQ : r ∈ pCoreOf 2 (L ⊔ T) := S.R_le_Q h.hat hr
  rw [comm_mul_right, show ⁅q, r⁆ = 1 by
    simp only [commutatorElement_def]
    rw [h.Q_abelian hq hrQ]
    group]
  have e : ⁅q, y⁆ * (y * (1 : G) * y⁻¹) = ⁅q, y⁆ := by group
  rw [e]
  exact hy.2 q hq

theorem CD_uniq {d₁ d₂ : G} (hd₁ : d₁ ∈ S.CD) (hd₂ : d₂ ∈ S.CD) (hn₁ : d₁ ≠ 1) (hn₂ : d₂ ≠ 1) :
    d₁ = d₂ := by
  refine eq_of_cocycle S.frame (D := S.CD) ?_ ?_ ?_ ?_ hd₁ hd₂ hn₁ hn₂
  · intro d hd v hv
    exact (S.comm_V_Q (h.CD_le_Q hd) hv).symm
  · intro d hd ℓ hℓ
    exact h.comm_Q_L (h.CD_le_Q hd) hℓ
  · intro d hd ℓ hℓ _ hρ
    exact h.Q_abelian (h.CD_le_Q hd) (S.R_le_Q h.hat ⟨hℓ, (S.rho_eq_one_iff _).1 hρ⟩)
  · intro u hu d hd hcomm
    have hx : u⁻¹ * d ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨T.mul_mem (T.inv_mem (S.V_le_T hu)) hd.1,
        Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => ?_⟩
      have h1 := hcomm ℓ hℓ
      simp only [commutatorElement_def] at h1
      have e1 : d * ℓ * d⁻¹ = u * ℓ * u⁻¹ := mul_right_cancel h1
      calc ℓ * (u⁻¹ * d) = u⁻¹ * (u * ℓ * u⁻¹) * d := by group
        _ = u⁻¹ * (d * ℓ * d⁻¹) * d := by rw [e1]
        _ = (u⁻¹ * d) * ℓ := by group
    rw [h.cTL, Subgroup.mem_bot] at hx
    have hud : u = d := inv_mul_eq_one.1 hx
    have h2 : d ∈ V ⊓ S.CD := ⟨hud ▸ hu, hd⟩
    rw [h.V_inf_CD, Subgroup.mem_bot] at h2
    exact h2

theorem card_CD (hD : S.CD ≠ ⊥) : Nat.card ↥S.CD = 2 := by
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ S.CD, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hD (eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (hcon x hx))
  rw [Nat.card_eq_two_iff' (1 : ↥S.CD)]
  refine ⟨⟨d, hdD⟩, fun hh => hd1 (congrArg Subtype.val hh), fun z hz => ?_⟩
  have hz1 : (z : G) ≠ 1 := fun hh => hz (Subtype.ext hh)
  exact Subtype.ext (h.CD_uniq z.2 hdD hz1 hd1)

theorem T5_le_centralizer_CD : S.T5 ≤ Subgroup.centralizer (S.CD : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  by_cases hd1 : d = 1
  · rw [hd1]
    simp
  · have htN := S.T5_le_normalizer_L5 ht
    have htT := S.T5_le_T ht
    have hmem : t * d * t⁻¹ ∈ S.CD := by
      refine ⟨T.mul_mem (T.mul_mem htT hd.1) (T.inv_mem htT),
        Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have hk' : t⁻¹ * k * t ∈ S.L5 := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) k).mp hk
        simpa using this
      have hcomm : (t⁻¹ * k * t) * d = d * (t⁻¹ * k * t) :=
        Subgroup.mem_centralizer_iff.mp hd.2 _ hk'
      calc k * (t * d * t⁻¹) = t * ((t⁻¹ * k * t) * d) * t⁻¹ := by group
        _ = t * (d * (t⁻¹ * k * t)) * t⁻¹ := by rw [hcomm]
        _ = (t * d * t⁻¹) * k := by group
    have hne : t * d * t⁻¹ ≠ 1 := by
      intro h1
      apply hd1
      have h2 := congrArg (fun x => t⁻¹ * x * t) h1
      have e : t⁻¹ * (t * d * t⁻¹) * t = d := by group
      simp only [e] at h2
      simpa using h2
    have e1 : t * d * t⁻¹ = d := h.CD_uniq hmem hd hne hd1
    have e2 : t * d = d * t := by
      calc t * d = (t * d * t⁻¹) * t := by group
        _ = d * t := by rw [e1]
    exact e2.symm

end CTKHyp

theorem Setting4.T5_relIndex_le_two (S : Setting4 G T L V) : S.T5.relIndex T ≤ 2 := by
  refine A6Block.relIndex_le_two_of fun x hx y hy hxn hyn => ?_
  have key : ∀ z ∈ T, z ∉ S.T5 → ∃ hz : z ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨z, hz⟩ 5 = 4 := by
    intro z hz hzn
    have hzN := S.frame.T_le hz
    refine ⟨hzN, InD6.apply_five _ (S.frame.T_D ⟨z, hzN⟩ hz) fun h5 => hzn ⟨hz, ?_⟩⟩
    exact S.mem_fix5V.2 ⟨hzN, h5⟩
  obtain ⟨hxN, hx4⟩ := key x hx hxn
  obtain ⟨hyN, hy4⟩ := key y hy hyn
  refine ⟨T.mul_mem (T.inv_mem hx) hy, S.mem_fix5V.2 ⟨Subgroup.mul_mem _
    (Subgroup.inv_mem _ hxN) hyN, ?_⟩⟩
  have e : (⟨x⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hyN⟩ :
      ↥(Subgroup.normalizer (V : Set G))) = ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩ := rfl
  rw [e, map_mul, map_inv, Perm.mul_apply, hy4]
  exact Perm.inv_eq_iff_eq.2 hx4.symm

theorem Setting4.normalizer_Q_le_NL (S : Setting4 G T L V) :
    Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hQne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := by
    intro hbot
    have := S.card_V
    have hV : V = ⊥ := le_bot_iff.1 (hbot ▸ S.V_le_pCoreOf_LT)
    rw [hV, Subgroup.card_bot] at this
    omega
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) :=
    ⟨_, hQne, pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hM := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
  exact hM ▸ hle

theorem Setting4.pCoreOf_normalizer_Q (S : Setting4 G T L V) :
    pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) = pCoreOf 2 (L ⊔ T) := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_right.trans hLT
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le_of_sylow S.h13.sylow hTN).trans le_sup_right)
      (hLT.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl (pCoreOf_isPGroup 2 _)

theorem Setting4.isSylowTwoOf_T_inf_L5 (S : Setting4 G T L V)
    (hhat : ¬ IsHatA6 L) : IsSylowTwoOf (T ⊓ S.L5) S.L5 := by
  have := S.isSylowTwoOf_T5_inf hhat
  have e : S.T5 ⊓ S.L5 = T ⊓ S.L5 := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxT, _⟩, hxL⟩
      exact ⟨hxT, hxL⟩
    · rintro ⟨hxT, hxL⟩
      exact ⟨⟨hxT, S.L5_le_fix5V hxL⟩, hxL⟩
  rwa [e] at this

namespace CTKHyp

variable {S : Setting4 G T L V} (h : CTKHyp S)
include h

theorem commutator_Q_L : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q hq ℓ hℓ
    exact h.comm_Q_L hq hℓ
  · have hU := blockU_eq_of_alt5 h.short h.alt h.O2 S.card_V
    calc V = blockU S.L5 := hU.symm
      _ = ⁅pCoreOf 2 S.L5, S.L5⁆ := rfl
      _ = ⁅V, S.L5⁆ := by rw [h.O2]
      _ ≤ ⁅pCoreOf 2 (L ⊔ T), L⁆ := Subgroup.commutator_mono (S.V_le_pCoreOf_LT) S.L5_le_L

theorem normalizer_Q_le_NV :
    Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  have hxL := S.normalizer_Q_le_NL hx
  rw [← h.commutator_Q_L]
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hx,
    map_conj_eq_of_mem_normalizer hxL]

end CTKHyp

namespace CTKHyp

variable {S : Setting4 G T L V} (h : CTKHyp S)
include h

theorem rho_five_of_cent (hD : S.CD ≠ ⊥) {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxC : x ∈ Subgroup.centralizer (S.CD : Set G)) :
    S.frame.ρ ⟨x, hxV⟩ 5 = 5 := by
  by_contra hne
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ d ∈ S.CD, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hD (eq_bot_iff.2 fun y hy => (Subgroup.mem_bot).2 (hcon y hy))
  set P : Subgroup (Perm (Fin 6)) :=
    ((L ⊓ Subgroup.centralizer (S.CD : Set G)).comap
      (Subgroup.normalizer (V : Set G)).subtype).map S.frame.ρ with hP
  have hL5C : S.L5 ≤ L ⊓ Subgroup.centralizer (S.CD : Set G) := fun k hk =>
    ⟨S.L5_le_L hk, Subgroup.mem_centralizer_iff.2 fun d hd =>
      (Subgroup.mem_centralizer_iff.mp hd.2 k hk).symm⟩
  have hP5 : ∀ τ : Perm (Fin 6), τ 5 = 5 → Perm.sign τ = 1 → τ ∈ P := by
    intro τ h5 hs
    obtain ⟨k, hk, hρ⟩ := S.exists_L5_rho h.hat h5 hs
    exact ⟨k, hL5C hk, hρ⟩
  set σx := S.frame.ρ ⟨x, hxV⟩ with hσx
  have hm : σx⁻¹ 5 ≠ 5 := by
    intro hm
    exact hne (Perm.inv_eq_iff_eq.1 hm).symm
  obtain ⟨σ', h5', hs', hσ'm⟩ : ∃ σ' : Perm (Fin 6), σ' 5 = 5 ∧ Perm.sign σ' = 1 ∧
      σ' (σx⁻¹ 5) ≠ σx⁻¹ 5 := by
    have key : ∀ m : Fin 6, m ≠ 5 →
        ∃ σ' : Perm (Fin 6), σ' 5 = 5 ∧ Perm.sign σ' = 1 ∧ σ' m ≠ m := by
      decide +kernel
    exact key _ hm
  obtain ⟨k, hk, hρk⟩ := S.exists_L5_rho h.hat h5' hs'
  have hxkN : x * (k : G) * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxV k.2) (Subgroup.inv_mem _ hxV)
  have hxkC : x * (k : G) * x⁻¹ ∈ L ⊓ Subgroup.centralizer (S.CD : Set G) := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp hxL _).mp (S.L5_le_L hk),
      Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
    have hdx : Commute d x := Subgroup.mem_centralizer_iff.mp hxC d hd
    have hdk : Commute d k := (Subgroup.mem_centralizer_iff.mp hd.2 k hk).symm
    exact ((hdx.mul_right hdk).mul_right hdx.inv_right).eq
  have hτP : σx * σ' * σx⁻¹ ∈ P := by
    refine ⟨⟨x * k * x⁻¹, hxkN⟩, hxkC, ?_⟩
    have e : (⟨x * (k : G) * x⁻¹, hxkN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, hxV⟩ * k * ⟨x, hxV⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρk]
  have hτ5 : (σx * σ' * σx⁻¹) 5 ≠ 5 := by
    intro h5
    simp only [Perm.mul_apply] at h5
    apply hσ'm
    apply σx.injective
    rw [h5]
    simp
  have hτs : Perm.sign (σx * σ' * σx⁻¹) = 1 := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs']
    simp
  have hA6 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → σ ∈ P := fun σ hσ =>
    mem_of_stab5 hP5 hτP hτ5 hτs hσ
  have hd₀L : d₀ ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨hd₀.1, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => ?_⟩
    have hs : Perm.sign (S.frame.ρ ⟨ℓ, S.frame.L_le hℓ⟩) = 1 :=
      Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨_, hℓ, rfl⟩)
    obtain ⟨c, hcC, hρc⟩ := hA6 _ hs
    have hrN : (c : G)⁻¹ * ℓ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ c.2) (S.frame.L_le hℓ)
    have hr1 : S.frame.ρ ⟨(c : G)⁻¹ * ℓ, hrN⟩ = 1 := by
      have e : (⟨(c : G)⁻¹ * ℓ, hrN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          c⁻¹ * ⟨ℓ, S.frame.L_le hℓ⟩ := rfl
      rw [e, map_mul, map_inv, hρc, inv_mul_cancel]
    have hrQ : (c : G)⁻¹ * ℓ ∈ pCoreOf 2 (L ⊔ T) :=
      S.R_le_Q h.hat ⟨L.mul_mem (L.inv_mem hcC.1) hℓ, (S.rho_eq_one_iff _).1 hr1⟩
    have hd₀Q : d₀ ∈ pCoreOf 2 (L ⊔ T) := h.CD_le_Q hd₀
    have h1 : (c : G) * d₀ = d₀ * c := (Subgroup.mem_centralizer_iff.mp hcC.2 d₀ hd₀).symm
    have h2 : d₀ * ((c : G)⁻¹ * ℓ) = ((c : G)⁻¹ * ℓ) * d₀ := h.Q_abelian hd₀Q hrQ
    calc ℓ * d₀ = (c : G) * (((c : G)⁻¹ * ℓ) * d₀) := by group
      _ = (c : G) * (d₀ * ((c : G)⁻¹ * ℓ)) := by rw [h2]
      _ = ((c : G) * d₀) * ((c : G)⁻¹ * ℓ) := by group
      _ = (d₀ * c) * ((c : G)⁻¹ * ℓ) := by rw [h1]
      _ = d₀ * ℓ := by group
  rw [h.cTL, Subgroup.mem_bot] at hd₀L
  exact hd₀1 hd₀L

theorem mem_Q_of_cent {c : G}
    (hcN : c ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G))
    (hcV : c ∈ Subgroup.centralizer (V : Set G)) (hcD : c ∈ Subgroup.centralizer (S.CD : Set G)) :
    c ∈ pCoreOf 2 (L ⊔ T) := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_right.trans hLT
  have hcQ : c ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ (V : Set G) * (S.CD : Set G) := by
      rw [← h.Q_mul]
      exact hq
    obtain ⟨v, hv, d, hd, rfl⟩ := hq'
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.mp hcV v hv
    have h2 : d * c = c * d := Subgroup.mem_centralizer_iff.mp hcD d hd
    calc v * d * c = v * (d * c) := by group
      _ = v * (c * d) := by rw [h2]
      _ = (v * c) * d := by group
      _ = (c * v) * d := by rw [h1]
      _ = c * (v * d) := by group
  have hne : pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) ≠ ⊥ := by
    rw [S.pCoreOf_normalizer_Q]
    intro hbot
    have := S.card_V
    have hV : V = ⊥ := le_bot_iff.1 (hbot ▸ S.V_le_pCoreOf_LT)
    rw [hV, Subgroup.card_bot] at this
    omega
  have hch : Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) ⊓
      Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) :=
    S.charTwo_of_inH ⟨hTN, hne⟩
  rw [S.pCoreOf_normalizer_Q] at hch
  exact hch ⟨hcN, hcQ⟩

theorem normalizer_inf_centralizer_le (hD : S.CD ≠ ⊥) :
    Subgroup.normalizer ((V ⊔ S.CD : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (S.CD : Set G) ≤ S.L5 ⊔ S.T5 := by
  rintro x ⟨hxN, hxC⟩
  rw [← h.Q_eq] at hxN
  have hxL := S.normalizer_Q_le_NL hxN
  have hxV := h.normalizer_Q_le_NV hxN
  set σx := S.frame.ρ ⟨x, hxV⟩ with hσx
  have h5 : σx 5 = 5 := h.rho_five_of_cent hD hxL hxV hxC
  have hQN : Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    h.normalizer_Q_le_NV
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hTA : T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := le_sup_right.trans hLT
  obtain ⟨t, htT5, htN, hts⟩ : ∃ t : G, t ∈ S.T5 ∧ ∃ htN : t ∈ Subgroup.normalizer (V : Set G),
      Perm.sign (S.frame.ρ ⟨t, htN⟩) = Perm.sign σx := by
    rcases Int.units_eq_one_or (Perm.sign σx) with hs | hs
    · refine ⟨1, S.T5.one_mem, Subgroup.one_mem _, ?_⟩
      rw [hs, show (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (V : Set G))) = 1 from rfl,
        map_one, Perm.sign_one]
    · let f : ↥(Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) →* ℤˣ :=
        Perm.sign.comp (S.frame.ρ.comp (Subgroup.inclusion hQN))
      have hfa : f ⟨x, hxN⟩ = -1 := hs
      obtain ⟨t₁, ht₁T, ht₁⟩ := exists_odd_of_sylow (A5.isSylowTwoOf_of_le S.h13.sylow hTA) f hfa
      have ht₁N : (t₁ : G) ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le ht₁T
      have ht₁s : Perm.sign (S.frame.ρ ⟨t₁, ht₁N⟩) = -1 := ht₁
      have hD6 : InD6 (S.frame.ρ ⟨t₁, ht₁N⟩) := S.frame.T_D ⟨t₁, ht₁N⟩ ht₁T
      have hσ₀D : (S.frame.ρ ⟨t₁, ht₁N⟩)⁻¹ * swap 0 1 ∈ D6sub :=
        D6sub.mul_mem (D6sub.inv_mem hD6) (by rw [mem_D6sub]; decide)
      have hσ₀s : (S.frame.ρ ⟨t₁, ht₁N⟩)⁻¹ * swap 0 1 ∈ alternatingGroup (Fin 6) := by
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, ht₁s,
          Perm.sign_swap (by decide)]
        decide
      obtain ⟨s, hsT, hρs⟩ := S.frame.DA_T _ hσ₀D hσ₀s
      have htN : (t₁ : G) * s ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ ht₁N s.2
      have hρt : S.frame.ρ ⟨(t₁ : G) * s, htN⟩ = swap 0 1 := by
        have e : (⟨(t₁ : G) * s, htN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨t₁, ht₁N⟩ * s := rfl
        rw [e, map_mul, hρs]
        group
      refine ⟨(t₁ : G) * s, ⟨T.mul_mem ht₁T hsT, S.mem_fix5V.2 ⟨htN, ?_⟩⟩, htN, ?_⟩
      · rw [hρt]
        decide
      · rw [hρt, hs, Perm.sign_swap (by decide)]
  obtain ⟨ht5⟩ : Nonempty (S.frame.ρ ⟨t, htN⟩ 5 = 5) :=
    ⟨(S.mem_fix5V.1 htT5.2).2⟩
  set σt := S.frame.ρ ⟨t, htN⟩ with hσt
  have hσ5 : (σx * σt⁻¹) 5 = 5 := by
    have : σt⁻¹ 5 = 5 := Perm.inv_eq_iff_eq.2 ht5.symm
    simp [Perm.mul_apply, this, h5]
  have hσs : Perm.sign (σx * σt⁻¹) = 1 := by
    rw [Perm.sign_mul, Perm.sign_inv, hts]
    simp
  obtain ⟨k, hk, hρk⟩ := S.exists_L5_rho h.hat hσ5 hσs
  have hcN : (k : G)⁻¹ * x * t⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) hxN)
      (Subgroup.inv_mem _ (hTA (S.T5_le_T htT5)))
    exact hLT (Subgroup.mem_sup_left (S.L5_le_L hk))
  have hcVN : (k : G)⁻¹ * x * t⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ k.2) hxV)
      (Subgroup.inv_mem _ htN)
  have hcV : (k : G)⁻¹ * x * t⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    refine (S.rho_eq_one_iff ⟨_, hcVN⟩).1 ?_
    have e : (⟨(k : G)⁻¹ * x * t⁻¹, hcVN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        k⁻¹ * ⟨x, hxV⟩ * ⟨t, htN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hρk]
    simp [hσx, hσt]
  have hcD : (k : G)⁻¹ * x * t⁻¹ ∈ Subgroup.centralizer (S.CD : Set G) := by
    have hkD : (k : G) ∈ Subgroup.centralizer (S.CD : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun d hd =>
        (Subgroup.mem_centralizer_iff.mp hd.2 k hk).symm
    have htD : t ∈ Subgroup.centralizer (S.CD : Set G) := h.T5_le_centralizer_CD htT5
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkD) hxC)
      (Subgroup.inv_mem _ htD)
  have hcQ := h.mem_Q_of_cent hcN hcV hcD
  have hxe : x = (k : G) * ((k : G)⁻¹ * x * t⁻¹) * t := by group
  rw [hxe]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right (S.pCoreOf_LT_le_T5 hcQ))) (Subgroup.mem_sup_right htT5)

end CTKHyp

theorem CTKHyp.CD_eq_bot {S : Setting4 G T L V} (h : CTKHyp S)
    (hLS : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h36 : Vol2Native.A36CoreForSQTKCat)
    (hl2 : L2MultiplierFact)
    (hlist : ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
      ∀ (H : Subgroup X) (N : Subgroup ↥H) [N.Normal] [IsSimpleGroup (↥H ⧸ N)],
        (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → CFSG.Milestones.SQTKSimpleList (↥H ⧸ N))
    (hExcl : ExclA5Block)
    (hy : ∃ y : G, y ^ 3 = 1 ∧ y ∉ Subgroup.normalizer (V : Set G) ∧
      ∀ d ∈ S.CD, y * d * y⁻¹ = d) : S.CD = ⊥ := by
  by_contra hD
  have hD2 := h.card_CD hD
  have hsyl : IsSylowTwoOf T ⊤ := A5.isSylowTwoOf_of_le S.h13.sylow le_top
  have hTQ : T ≤ Subgroup.normalizer ((V ⊔ S.CD : Subgroup G) : Set G) := by
    rw [← h.Q_eq]
    exact (le_sup_right : T ≤ L ⊔ T).trans (le_normalizer_pCoreOf 2 _)
  refine ctk_false_of_excl hLS h37 h38 h39 h36 hl2 hlist hExcl hsyl h.short h.alt h.O2
    S.card_V hD2 (fun d hd => hd.2) hTQ S.T5_le_T h.T5_le_centralizer_CD
    S.T5_le_normalizer_L5 ?_ h.CD_le_T5 S.T5_relIndex_le_two (S.isSylowTwoOf_T_inf_L5 h.hat) rfl
    (h.normalizer_inf_centralizer_le hD) ?_
  · intro x hx
    exact ⟨hx.1, S.L5_le_fix5V hx.2⟩
  · obtain ⟨y, hy3, hyN, hyD⟩ := hy
    have hy1 : y ≠ 1 := fun h1 => hyN (h1 ▸ Subgroup.one_mem _)
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine ⟨y, Subgroup.mem_centralizer_iff.2 fun d hd => ?_, orderOf_eq_prime hy3 hy1, hyN⟩
    have := hyD d hd
    calc d * y = (y * d * y⁻¹) * y := by rw [this]
      _ = y * d := by group

end CFSG.Quasithin.H13.A6

