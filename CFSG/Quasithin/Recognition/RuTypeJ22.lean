module

public import CFSG.Quasithin.Recognition.RuTypeNorm
public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

abbrev pullL (L : Subgroup G) (θ : L →* SL(3, ZMod 2)) (X : Subgroup SL(3, ZMod 2)) :
    Subgroup G :=
  (X.comap θ).map L.subtype

theorem mem_pullL {L : Subgroup G} {θ : L →* SL(3, ZMod 2)} {X : Subgroup SL(3, ZMod 2)}
    {g : G} : g ∈ pullL L θ X ↔ ∃ h : g ∈ L, θ ⟨g, h⟩ ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨g, h⟩, hx, rfl⟩

namespace RuDataN

variable (N : RuDataN G)

@[expose] noncomputable def zV : ruV N.L := N.ψV.symm (Multiplicative.ofAdd SL3.e0)

@[expose] noncomputable def z : G := (N.zV : G)

theorem z_mem_V : N.z ∈ ruV N.L := N.zV.2

theorem ψV_zV : Multiplicative.toAdd (N.ψV N.zV) = SL3.e0 := by
  simp [zV]

theorem θ_mem_P0 {t : G} (ht : t ∈ (N.T : Subgroup G)) (htL : t ∈ N.L) : N.θ ⟨t, htL⟩ ∈ SL3.P0 := by
  rw [← N.hP0]
  exact ⟨⟨t, htL⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩

variable [Finite G]

theorem z_mem_Z : N.z ∈ ruZ N.T := by
  rw [N.toRuData.Z_eq]
  refine ⟨N.z_mem_V, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  have htL := N.toRuData.T_le_L ht
  have h := (N.toRuData.conj_eq_iff ⟨t, htL⟩ N.zV).mpr (by
    rw [N.ψV_zV]
    exact ((SL3.fix_P0 SL3.e0).mpr ⟨rfl, rfl⟩) _ (N.θ_mem_P0 ht htL))
  calc t * N.z = t * N.z * t⁻¹ * t := by group
    _ = N.z * t := by rw [show t * N.z * t⁻¹ = N.z from h]

omit [Finite G] in
theorem z_ne_one : N.z ≠ 1 := by
  intro h
  have : N.zV = 1 := Subtype.ext h
  have e := N.ψV_zV
  rw [this, map_one] at e
  exact absurd (congrFun e 0) (by decide)

theorem mem_Z_iff {x : G} : x ∈ ruZ N.T ↔ x = 1 ∨ x = N.z := by
  constructor
  · intro hx
    have hcard := N.toRuData.card_Z
    by_contra hne
    simp only [not_or] at hne
    have h3 : 3 ≤ Nat.card (ruZ N.T) := by
      have hs : ({1, N.z, x} : Set G) ⊆ ruZ N.T := by
        intro y hy
        rcases hy with rfl | rfl | rfl
        · exact (ruZ N.T).one_mem
        · exact N.z_mem_Z
        · exact hx
      have := Set.ncard_le_ncard hs (Set.toFinite _)
      rw [Set.ncard_eq_three.mpr ⟨1, N.z, x, N.z_ne_one.symm, Ne.symm hne.1, Ne.symm hne.2, rfl⟩,
        ← Nat.card_coe_set_eq] at this
      exact this
    omega
  · rintro (rfl | rfl)
    · exact (ruZ N.T).one_mem
    · exact N.z_mem_Z

abbrev LT1 : Subgroup G := pullL N.L N.θ SL3.Stab0

abbrev R1 : Subgroup G := pullL N.L N.θ SL3.R0

omit [Finite G] in
theorem comm_z_iff (l : N.L) : (l : G) * N.z = N.z * l ↔ N.θ l ∈ SL3.Stab0 := by
  rw [SL3.mem_Stab0]
  have h := N.toRuData.conj_eq_iff l N.zV
  rw [N.ψV_zV] at h
  rw [← h]
  constructor
  · intro e
    show (l : G) * N.z * (l : G)⁻¹ = N.z
    rw [e, mul_inv_cancel_right]
  · intro e
    calc (l : G) * N.z = l * N.z * (l : G)⁻¹ * l := by group
      _ = N.z * l := by rw [show (l : G) * N.z * (l : G)⁻¹ = N.z from e]

theorem mem_H_iff_comm {h : G} : h ∈ ruH N.T ↔ N.z * h = h * N.z := by
  rw [N.toRuData.mem_H_iff]
  constructor
  · intro hh
    exact hh N.z N.z_mem_Z
  · intro hh x hx
    rcases N.mem_Z_iff.mp hx with rfl | rfl
    · simp
    · exact hh

theorem L_inf_H : N.L ⊓ ruH N.T = N.LT1 := by
  ext g
  rw [Subgroup.mem_inf, mem_pullL]
  constructor
  · rintro ⟨hgL, hgH⟩
    refine ⟨hgL, (N.comm_z_iff ⟨g, hgL⟩).mp ?_⟩
    exact (N.mem_H_iff_comm.mp hgH).symm
  · rintro ⟨hgL, hst⟩
    exact ⟨hgL, N.mem_H_iff_comm.mpr ((N.comm_z_iff ⟨g, hgL⟩).mpr hst).symm⟩

theorem LT1_le_H : N.LT1 ≤ ruH N.T := N.L_inf_H ▸ inf_le_right

omit [Finite G] in
theorem LT1_le_L : N.LT1 ≤ N.L := Subgroup.map_subtype_le _

omit [Finite G] in
theorem S_le_pullL (X : Subgroup SL(3, ZMod 2)) : ruS N.L ≤ pullL N.L N.θ X := by
  intro s hs
  refine mem_pullL.mpr ⟨N.toRuData.S_le_L hs, ?_⟩
  have : (⟨s, N.toRuData.S_le_L hs⟩ : N.L) ∈ N.θ.ker := by
    rw [N.θ_ker, Subgroup.mem_subgroupOf]
    exact hs
  rw [MonoidHom.mem_ker.mp this]
  exact X.one_mem

omit [Finite G] in
theorem card_pullL (X : Subgroup SL(3, ZMod 2)) :
    Nat.card (pullL N.L N.θ X) = 2 ^ 11 * Nat.card X := by
  rw [Subgroup.card_map_of_injective N.L.subtype_injective]
  have h1 := Subgroup.relIndex_ker (K := X.comap N.θ) N.θ
  have h2 := Subgroup.relIndex_mul_card N.θ.ker (X.comap N.θ)
  have hker : N.θ.ker ≤ X.comap N.θ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact X.one_mem
  rw [inf_eq_left.mpr hker, h1, Subgroup.map_comap_eq_self_of_surjective N.θ_surj, N.θ_ker,
    card_subgroupOf_of_le N.toRuData.S_le_L, N.toRuData.card_S] at h2
  rw [← h2, mul_comm]

omit [Finite G] in
theorem card_LT1 : Nat.card N.LT1 = 2 ^ 11 * 24 := by
  rw [card_pullL, SL3.card_Stab0]

omit [Finite G] in
theorem card_R1 : Nat.card N.R1 = 2 ^ 13 := by
  rw [card_pullL, SL3.card_R0]
  norm_num

theorem le_of_two_pow_dvd {a b c : ℕ} (h : 2 ^ b ∣ 2 ^ a * c) (hc : ¬ 2 ∣ c) : b ≤ a := by
  have hcop : Nat.Coprime (2 ^ b) c := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_two).mpr hc)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

omit [Finite G] in
theorem exists_card_eq_two_pow {A B : Subgroup G} {n : ℕ} (hAB : A ≤ B)
    (hB : Nat.card B = 2 ^ n) : ∃ k ≤ n, Nat.card A = 2 ^ k := by
  have h := Subgroup.card_dvd_of_le hAB
  rw [hB] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).mp h

theorem Q_le_LT1 : ruQ N.T ≤ N.LT1 := by
  let K : Subgroup (ruH N.T) := N.LT1.subgroupOf (ruH N.T)
  have h := Subgroup.card_ker_mul_card_range (N.σ5.comp K.subtype)
  have hK : Nat.card K = 2 ^ 11 * 24 := by
    rw [card_subgroupOf_of_le N.LT1_le_H, N.card_LT1]
  have hker : Nat.card (N.σ5.comp K.subtype).ker = Nat.card ↥(ruQ N.T ⊓ N.LT1) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨x.1.1, by
          have hx := x.2
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
          have : x.1.1 ∈ N.σ5.ker := hx
          rw [N.σ5_ker, Subgroup.mem_subgroupOf] at this
          exact this, x.1.2⟩
        invFun := fun y => ⟨⟨⟨y.1, N.LT1_le_H y.2.2⟩, y.2.2⟩, by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          have : (⟨y.1, N.LT1_le_H y.2.2⟩ : ruH N.T) ∈ N.σ5.ker := by
            rw [N.σ5_ker, Subgroup.mem_subgroupOf]
            exact y.2.1
          exact this⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  obtain ⟨a, ha11, ha⟩ := exists_card_eq_two_pow (inf_le_left : ruQ N.T ⊓ N.LT1 ≤ ruQ N.T)
    N.toRuData.card_Q
  have hr : Nat.card (N.σ5.comp K.subtype).range ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card (N.σ5.comp K.subtype).range
    rwa [Nat.card_perm, Nat.card_fin] at this
  rw [hK, hker, ha] at h
  obtain ⟨r, hr'⟩ := hr
  have h14 : 2 ^ 14 ∣ 2 ^ (a + 3) * 15 := by
    refine ⟨3 * r, ?_⟩
    have e : 2 ^ (a + 3) * 15 = 2 ^ a * 120 := by ring
    rw [e, hr', ← mul_assoc, h]
    ring
  have ha' : 11 ≤ a := by
    have := le_of_two_pow_dvd h14 (by norm_num)
    omega
  have heq : ruQ N.T ⊓ N.LT1 = ruQ N.T := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [ha, N.toRuData.card_Q]
    exact Nat.pow_le_pow_right (by norm_num) ha')
  rw [← heq]
  exact inf_le_right

theorem Q_le_L : ruQ N.T ≤ N.L := N.Q_le_LT1.trans N.LT1_le_L

theorem S_ne_Q : ruS N.L ≠ ruQ N.T := by
  intro hSQ
  have hnorm : ruH N.T ≤ Subgroup.normalizer (ruV N.L : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ ruH N.T, ∀ v ∈ ruV N.L, g * v * g⁻¹ ∈ ruV N.L := by
      intro g hg v hv
      rw [N.toRuData.mem_V_iff] at hv ⊢
      have hQ : ruH N.T ≤ Subgroup.normalizer (ruQ N.T : Set G) := le_normalizer_pCoreOf 2 _
      have hgQ := hQ hg
      rw [hSQ] at hv ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp hgQ v).mp hv.1, fun s hs => ?_⟩
      have hs' : g⁻¹ * s * g ∈ ruQ N.T := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgQ) s).mp hs
        simpa using this
      have := hv.2 _ hs'
      calc s * (g * v * g⁻¹) = g * ((g⁻¹ * s * g) * v) * g⁻¹ := by group
        _ = g * (v * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
        _ = g * v * g⁻¹ * s := by group
    intro x
    constructor
    · exact key h hh x
    · intro hx
      have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hx
      simpa [mul_assoc] using this
  have hU : ruU N.L N.T = ruV N.L := le_antisymm
    (conjClosure_le fun h hh v hv => (Subgroup.mem_normalizer_iff.mp (hnorm hh) v).mp hv)
    (le_conjClosure _ _)
  have := N.toRuData.card_U
  rw [hU, N.toRuData.card_V] at this
  omega

theorem θQ_eq : ((ruQ N.T).subgroupOf N.L).map N.θ = SL3.R0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := ((ruQ N.T).subgroupOf N.L).map N.θ with hX
  have hXp : IsPGroup 2 X := by
    have hQp : IsPGroup 2 ((ruQ N.T).subgroupOf N.L) :=
      (pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe N.Q_le_L).symm
    exact hQp.map N.θ
  have hXnorm : ∀ g ∈ SL3.Stab0, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    rintro g hg _ ⟨⟨q, hqL⟩, hq, rfl⟩
    obtain ⟨⟨l, hlL⟩, rfl⟩ := N.θ_surj g
    have hlH : l ∈ ruH N.T := N.LT1_le_H (mem_pullL.mpr ⟨hlL, hg⟩)
    have hq' : q ∈ ruQ N.T := Subgroup.mem_subgroupOf.mp hq
    have hmem : l * q * l⁻¹ ∈ ruQ N.T :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hlH) q).mp hq'
    refine ⟨⟨l * q * l⁻¹, N.Q_le_L hmem⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    rw [show (⟨l * q * l⁻¹, N.Q_le_L hmem⟩ : N.L) = ⟨l, hlL⟩ * ⟨q, hqL⟩ * ⟨l, hlL⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv]
  have hXle : X ≤ SL3.Stab0 := by
    rintro _ ⟨⟨q, hqL⟩, hq, rfl⟩
    exact (mem_pullL.mp (N.Q_le_LT1 (Subgroup.mem_subgroupOf.mp hq))).2
  have hXR : X ≤ SL3.R0 := by
    intro x hx
    by_contra hxR
    have hx4 : x ^ 4 = 1 := by
      apply SL3.pow_four_of_pow_eight
      obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
      have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        have := congrArg Subtype.val hk
        simpa using this)
      have hdvd' : orderOf x ∣ 168 := by
        rw [← SL3.card_SL3]
        exact orderOf_dvd_natCard x
      have : orderOf x ∣ 8 := by
        have h1 : orderOf x ∣ Nat.gcd (2 ^ k) 168 := Nat.dvd_gcd hdvd hdvd'
        have h2 : Nat.gcd (2 ^ k) 168 ∣ 8 := by
          have : Nat.gcd (2 ^ k) 168 ∣ 2 ^ k := Nat.gcd_dvd_left _ _
          obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
          rw [hj']
          have : 2 ^ j ∣ 168 := hj' ▸ Nat.gcd_dvd_right _ _
          have hj3 : j ≤ 3 :=
            le_of_two_pow_dvd (a := 3) (b := j) (c := 21)
              (by rw [show 2 ^ 3 * 21 = 168 by norm_num]; exact this) (by norm_num)
          exact Nat.pow_dvd_pow 2 hj3
        exact h1.trans h2
      exact orderOf_dvd_iff_pow_eq_one.mp this
    obtain ⟨g, hg, hne, h3⟩ := SL3.exists_comm_order_three x (hXle hx) hxR hx4
    have hmem : x * g * x⁻¹ * g⁻¹ ∈ X := by
      have := X.mul_mem hx (hXnorm g hg _ (X.inv_mem hx))
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := hXp ⟨_, hmem⟩
    have hk' : (x * g * x⁻¹ * g⁻¹) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    apply hne
    have h1 : orderOf (x * g * x⁻¹ * g⁻¹) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3)
    have h2 : Nat.gcd (2 ^ k) 3 = 1 :=
      Nat.Coprime.pow_left _ (by norm_num)
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply N.S_ne_Q
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · intro q hq
      have hqL := N.Q_le_L hq
      have : N.θ ⟨q, hqL⟩ ∈ X := ⟨⟨q, hqL⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      have hk : (⟨q, hqL⟩ : N.L) ∈ N.θ.ker := this
      rw [N.θ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    · rw [N.toRuData.card_S, N.toRuData.card_Q]
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXne
  refine le_antisymm hXR fun y hy => ?_
  by_cases hy1 : y = 1
  · rw [hy1]
    exact X.one_mem
  obtain ⟨g, hg, hgy⟩ := SL3.conj_R0_transitive x (hXR x.2) (fun e => hx1 (Subtype.ext e)) y hy
    hy1
  rw [← hgy]
  exact hXnorm g hg x x.2

theorem Q_sup_S : ruQ N.T ⊔ ruS N.L = N.R1 := by
  refine le_antisymm (sup_le ?_ (N.S_le_pullL _)) ?_
  · intro q hq
    refine mem_pullL.mpr ⟨N.Q_le_L hq, ?_⟩
    rw [← N.θQ_eq]
    exact ⟨⟨q, N.Q_le_L hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  · intro r hr
    obtain ⟨hrL, hrR⟩ := mem_pullL.mp hr
    rw [← N.θQ_eq] at hrR
    obtain ⟨⟨q, hqL⟩, hq, hqr⟩ := hrR
    have hk : (⟨q, hqL⟩ : N.L)⁻¹ * ⟨r, hrL⟩ ∈ N.θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqr, inv_mul_cancel]
    rw [N.θ_ker, Subgroup.mem_subgroupOf] at hk
    have : r = q * (q⁻¹ * r) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hq) hk

omit [Finite G] in
theorem V_le_U : ruV N.L ≤ ruU N.L N.T := le_conjClosure _ _

omit [Finite G] in
theorem U_le_H : ruU N.L N.T ≤ ruH N.T := N.two.U_le_Q.trans (pCoreOf_le 2 _)

omit [Finite G] in
theorem conj_mem_U {h u : G} (hh : h ∈ ruH N.T) (hu : u ∈ ruU N.L N.T) :
    h * u * h⁻¹ ∈ ruU N.L N.T :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hh) u).mp hu

omit [Finite G] in
theorem ψU_eq_one_iff (u : ruU N.L N.T) : N.ψU u = 1 ↔ (u : G) ∈ ruZ N.T := by
  have : u ∈ N.ψU.ker ↔ u ∈ (ruZ N.T).subgroupOf (ruU N.L N.T) := by rw [N.ψU_ker]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at this
  exact this

omit [Finite G] in
theorem Z_comm_H {w h : G} (hw : w ∈ ruZ N.T) (hh : h ∈ ruH N.T) : w * h = h * w :=
  N.toRuData.mem_H_iff.mp hh w hw

omit [Finite G] in
theorem ψU_conj (h : ruH N.T) (u : ruU N.L N.T) :
    Multiplicative.toAdd (N.ψU ⟨h * u * (h : G)⁻¹, N.conj_mem_U h.2 u.2⟩) =
      sigmaAct (N.φ h) (Multiplicative.toAdd (N.ψU u)) := by
  rw [N.ψU_equiv h u ⟨_, N.conj_mem_U h.2 u.2⟩ rfl, toAdd_ofAdd]

omit [Finite G] in
theorem exists_conj_mod_Z {u₁ u₂ : ruU N.L N.T} (h₁ : N.ψU u₁ ≠ 1) (h₂ : N.ψU u₂ ≠ 1) :
    ∃ h ∈ ruH N.T, ∃ w ∈ ruZ N.T, (u₂ : G) = h * u₁ * h⁻¹ * w := by
  have h₁' : Multiplicative.toAdd (N.ψU u₁) ≠ 0 := fun e => h₁ (by
    rw [← toAdd_one] at e
    exact Multiplicative.toAdd.injective e)
  have h₂' : Multiplicative.toAdd (N.ψU u₂) ≠ 0 := fun e => h₂ (by
    rw [← toAdd_one] at e
    exact Multiplicative.toAdd.injective e)
  obtain ⟨x, hx⟩ := Sigma.exists_sigmaAct_eq h₁' h₂'
  obtain ⟨h, rfl⟩ := N.φ_surj x
  let u₁' : ruU N.L N.T := ⟨h * u₁ * (h : G)⁻¹, N.conj_mem_U h.2 u₁.2⟩
  have e : N.ψU u₁' = N.ψU u₂ := Multiplicative.toAdd.injective (by rw [N.ψU_conj, hx])
  have hw : N.ψU (u₁'⁻¹ * u₂) = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
  refine ⟨h, h.2, u₁'⁻¹ * u₂, (N.ψU_eq_one_iff _).mp hw, ?_⟩
  simp [u₁']
  group

omit [Finite G] in
theorem z_sq : N.z ^ 2 = 1 := N.one.center_elem.2 _ N.z_mem_V

@[expose] noncomputable def v1V : ruV N.L := N.ψV.symm (Multiplicative.ofAdd ![0, 1, 0])

theorem v1_not_mem_Z : (N.v1V : G) ∉ ruZ N.T := by
  intro h
  rcases N.mem_Z_iff.mp h with h1 | h1
  · have : N.v1V = 1 := Subtype.ext h1
    have e : Multiplicative.toAdd (N.ψV N.v1V) = ![0, 1, 0] := by simp [v1V]
    rw [this, map_one] at e
    exact absurd (congrFun e 1) (by decide)
  · have : N.v1V = N.zV := Subtype.ext h1
    have e : Multiplicative.toAdd (N.ψV N.v1V) = ![0, 1, 0] := by simp [v1V]
    rw [this, N.ψV_zV] at e
    exact absurd (congrFun e 0) (by decide)

theorem U_sq {u : G} (hu : u ∈ ruU N.L N.T) : u ^ 2 = 1 := by
  by_cases hψ : N.ψU ⟨u, hu⟩ = 1
  · rcases N.mem_Z_iff.mp ((N.ψU_eq_one_iff _).mp hψ) with h | h
    · rw [show u = 1 from h, one_pow]
    · rw [show u = N.z from h, N.z_sq]
  · have hv : (N.v1V : G) ∈ ruU N.L N.T := N.V_le_U N.v1V.2
    have hv1 : N.ψU ⟨N.v1V, hv⟩ ≠ 1 := fun e => N.v1_not_mem_Z ((N.ψU_eq_one_iff _).mp e)
    obtain ⟨h, hh, w, hw, hu'⟩ := N.exists_conj_mod_Z hv1 hψ
    simp only at hu'
    have hvH : h * (N.v1V : G) * h⁻¹ ∈ ruH N.T :=
      N.U_le_H (N.conj_mem_U hh hv)
    have hcomm := N.Z_comm_H hw hvH
    have hw2 : w ^ 2 = 1 := by
      rcases N.mem_Z_iff.mp hw with h' | h'
      · rw [h', one_pow]
      · rw [h', N.z_sq]
    have hv2 : (N.v1V : G) ^ 2 = 1 := N.one.center_elem.2 _ N.v1V.2
    have key : ∀ a : G, w * a = a * w → (a * w) * (a * w) = a * a * (w * w) := by
      intro a ha
      rw [mul_assoc a w, ← mul_assoc w a, ha]
      group
    rw [hu', sq, key _ hcomm, ← sq, ← sq, hw2, mul_one]
    calc (h * ↑N.v1V * h⁻¹) ^ 2 = h * (N.v1V : G) ^ 2 * h⁻¹ := by
          rw [sq, sq]; group
      _ = 1 := by rw [hv2]; group

theorem U_elem : IsElemAbelian 2 (ruU N.L N.T) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => N.U_sq hx⟩
  have ha := N.U_sq a.2
  have hb := N.U_sq b.2
  have hab := N.U_sq (mul_mem a.2 b.2)
  simp only [Subgroup.coe_mul]
  have e1 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha])
  have e2 : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb])
  have e3 : ((a : G) * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq, hab])
  rw [mul_inv_rev, e1, e2] at e3
  exact e3.symm

end RuDataN

end CFSG.Quasithin.RuType
