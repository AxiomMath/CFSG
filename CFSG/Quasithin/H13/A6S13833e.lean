module

public import CFSG.Quasithin.H13.A6S13833d
public import CFSG.Quasithin.H13.A6G5

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

theorem stabW2_cList : ∀ σ ∈ cList, StabW2 σ := by decide +kernel

theorem fix_e0123_g5 : ∀ σ : Perm (Fin 6), ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4)) →
    act4f σ e0123 = e0123 := by
  decide +kernel

theorem mem_normalizer_of_conj_mem_fin {G : Type} [Group G] [Finite G] {X : Subgroup G} {x : G}
    (h : ∀ v ∈ X, x * v * x⁻¹ ∈ X) : x ∈ Subgroup.normalizer (X : Set G) := by
  have h1 : conjSub x X ≤ X := fun y hy => by
    have := h _ (mem_conjSub.mp hy)
    simpa [mul_assoc] using this
  have e : conjSub x X = X := Subgroup.eq_of_le_of_card_ge h1 (by rw [CosetGeom.card_conjSub])
  refine F7.mem_normalizer_of_conj_le e.le ?_
  rw [← e, conjSub_conjSub_inv, e]

private theorem mem_normalizer_inf_of {G : Type} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (hA y) (hB y)

theorem relIndex_sup_mul_card_inf {G : Type} [Group G] [Finite G] {A W : Subgroup G}
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) :
    W.relIndex (A ⊔ W) * Nat.card (A ⊓ W : Subgroup G) = Nat.card A := by
  have h1 := card_sup_mul_card_inf' hAW
  have h2 := Subgroup.relIndex_mul_card W (A ⊔ W)
  rw [inf_eq_left.2 le_sup_right] at h2
  have hW : 0 < Nat.card W := Nat.card_pos
  rw [← h2] at h1
  have : (W.relIndex (A ⊔ W) * Nat.card (A ⊓ W : Subgroup G)) * Nat.card W =
      Nat.card A * Nat.card W := by
    rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hW this

theorem exists_maximal_invariant {G : Type} [Group G] [Finite G] {V U Y : Subgroup G}
    (hVU : V < U) (hYV : Y ≤ Subgroup.normalizer (V : Set G)) :
    ∃ W : Subgroup G, V ≤ W ∧ W < U ∧ Y ≤ Subgroup.normalizer (W : Set G) ∧
      ∀ W' : Subgroup G, W ≤ W' → W' ≤ U → Y ≤ Subgroup.normalizer (W' : Set G) →
        W' = W ∨ W' = U := by
  obtain ⟨W, hW⟩ := (Set.toFinite {W : Subgroup G | V ≤ W ∧ W < U ∧
    Y ≤ Subgroup.normalizer (W : Set G)}).exists_maximal ⟨V, le_rfl, hVU, hYV⟩
  refine ⟨W, hW.1.1, hW.1.2.1, hW.1.2.2, fun W' hWW' hW'U hYW' => ?_⟩
  by_cases hU : W' = U
  · exact Or.inr hU
  · exact Or.inl (le_antisymm (hW.2 ⟨hW.1.1.trans hWW', lt_of_le_of_ne hW'U hU, hYW'⟩ hWW') hWW')

theorem comm_mem_of_maximal {G : Type} [Group G] [Finite G] {Q U W Y : Subgroup G}
    (hQ : IsPGroup 2 Q) (hUQ : U ≤ Q) (hWU : W < U) (hQY : Q ≤ Y)
    (hYQ : Y ≤ Subgroup.normalizer (Q : Set G)) (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ U → Y ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = U) :
    ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ W := by
  obtain ⟨z, hzU, hzW, hz⟩ := exists_fixed_mod hQ hUQ hWU (hQY.trans hYU) (hQY.trans hYW)
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) := hQY.trans hYW
  have hWC : W ≤ centralizerMod W U Q := fun w hw => by
    refine ⟨hWU.le hw, hQW (hUQ (hWU.le hw)), fun q hq => ?_⟩
    have h1 : q * w⁻¹ * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hQW hq) _).mp (W.inv_mem hw)
    have e : w * q * w⁻¹ * q⁻¹ = w * (q * w⁻¹ * q⁻¹) := by group
    rw [e]
    exact W.mul_mem hw h1
  have hzC : z ∈ centralizerMod W U Q := by
    refine ⟨hzU, hQW (hUQ hzU), fun q hq => ?_⟩
    have := W.inv_mem (hz q hq)
    have e : (q * z * q⁻¹ * z⁻¹)⁻¹ = z * q * z⁻¹ * q⁻¹ := by group
    rwa [e] at this
  rcases hmax _ hWC (centralizerMod_le_left _ _ _) (le_normalizer_centralizerMod hYW hYU hYQ)
    with h | h
  · rw [h] at hzC
    exact absurd hzC hzW
  · intro q hq u hu
    rw [← h] at hu
    have := W.inv_mem (hu.2.2 q hq)
    have e : (u * q * u⁻¹ * q⁻¹)⁻¹ = q * u * q⁻¹ * u⁻¹ := by group
    rwa [e] at this

theorem conj_mem_of_sq_conj_mem {G : Type} [Group G] {V : Subgroup G} {x a : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1)
    (h : a⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹) ∈ V) : a⁻¹ * (x * a * x⁻¹) ∈ V := by
  obtain ⟨r, rfl⟩ := hm
  have hx2 : x ^ 2 ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hxV 2
  have key : ∀ k : ℕ, a⁻¹ * (x ^ (2 * k) * a * (x ^ (2 * k))⁻¹) ∈ V := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : a⁻¹ * (x ^ (2 * (k + 1)) * a * (x ^ (2 * (k + 1)))⁻¹) =
          (a⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹)) *
            (x ^ 2 * (a⁻¹ * (x ^ (2 * k) * a * (x ^ (2 * k))⁻¹)) * (x ^ 2)⁻¹) := by
        rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add]
        group
      rw [e]
      exact V.mul_mem h ((Subgroup.mem_normalizer_iff.mp hx2 _).mp ih)
  have e : x ^ (2 * (r + 1)) = x := by
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, hxm, one_mul]
  have := key (r + 1)
  rwa [e] at this

theorem relIndex_centralizerMod_le {G : Type} [Group G] [Finite G] {U P A W : Subgroup G}
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hPU : P ≤ U) (hP : P.relIndex U ≤ 16)
    (hWU : W ≤ U) {x : G} (hA : Nat.card A = 2) (hAP : A ≤ P)
    (hcomm : ∀ u ∈ P, x * u * x⁻¹ * u⁻¹ ∈ A) :
    (centralizerMod W U (Subgroup.zpowers x)).relIndex U ≤ 32 := by
  have hxP : ∀ u ∈ P, x * u * x⁻¹ ∈ P := fun u hu => by
    have e : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact P.mul_mem (hAP (hcomm u hu)) hu
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => hUab a (hPU ha) b (hPU hb)
  set C := P ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have hC2 : C.relIndex P ≤ 2 := by
    by_cases hne : ∃ u₀ ∈ P, x * u₀ * x⁻¹ * u₀⁻¹ ≠ 1
    · obtain ⟨u₀, hu₀, hne⟩ := hne
      rw [relIndex_centralizer_eq_two hPab hxP hA hcomm hu₀ hne]
    · push Not at hne
      have hle : P ≤ C := fun u hu => by
        refine ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 := hne u hu
        calc u * x = (x * u * x⁻¹ * u⁻¹)⁻¹ * (x * u) := by group
          _ = x * u := by rw [h1, inv_one, one_mul]
      rw [Subgroup.relIndex_eq_one.2 hle]
      norm_num
  have hCle : C ≤ centralizerMod W U (Subgroup.zpowers x) := by
    intro a ha
    have haU : a ∈ U := hPU ha.1
    refine ⟨haU, Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w (hWU hw) a haU), fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have hcn : a * x ^ n = x ^ n * a := ((Commute.zpow_right hc n))
    rw [hcn, mul_inv_cancel_right, mul_inv_cancel]
    exact W.one_mem
  have hCU : C ≤ U := inf_le_left.trans hPU
  have hpos : C.relIndex U ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card C U
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  calc (centralizerMod W U (Subgroup.zpowers x)).relIndex U ≤ C.relIndex U :=
        Subgroup.relIndex_le_of_le_left hCle hpos
    _ = C.relIndex P * P.relIndex U := (Subgroup.relIndex_mul_relIndex C P U inf_le_left hPU).symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hC2 hP
    _ = 32 := by norm_num

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_G1_of_g5G1 {y : ↥(Subgroup.normalizer (V : Set G))} (hy : S.frame.ρ y ∈ g5G1) :
    (y : G) ∈ S.G1 := by
  have h : (y : G) * S.z * (y : G)⁻¹ = S.z := by
    refine (S.conj_eq_iff y ⟨S.z, S.z_mem_V⟩).2 ?_
    rw [S.psi_z]
    exact Subtype.ext (fix_e0123_g5 _ hy.2)
  show (y : G) ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (y : G) * S.z = (y : G) * S.z * (y : G)⁻¹ * y := by group
    _ = S.z * y := by rw [h]

theorem mem_NV2_of_cA6 {y : ↥(Subgroup.normalizer (V : Set G))} (hy : S.frame.ρ y ∈ cA6) :
    (y : G) ∈ Subgroup.normalizer (S.V2 : Set G) := by
  have hst := stabW2_cList _ (mem_cList _ hy.1)
  refine mem_normalizer_of_conj_mem_fin fun v hv => ?_
  obtain ⟨hvV, hvW⟩ := S.mem_pre.1 hv
  have hyv : (y : G) * v * (y : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp y.2 v).mp hvV
  refine S.mem_V2_of (v := ⟨_, hyv⟩) ?_
  have e : S.frame.ψ ⟨(y : G) * v * (y : G)⁻¹, hyv⟩ =
      act4 (S.frame.ρ y) (S.frame.ψ ⟨v, hvV⟩) := S.psi_conj y ⟨v, hvV⟩
  rw [e]
  exact hst _ hvW

theorem LT_le_NUL : L ⊔ T ≤ Subgroup.normalizer
    ((conjClosure (conjClosure S.V3 S.G1) L : Subgroup G) : Set G) := by
  have hTH : T ≤ S.G1 := fun t ht => by
    have := S.T_le_NV1 ht
    rwa [S.normalizer_V1] at this
  refine sup_le (le_normalizer_conjClosure _ L) fun t ht => ?_
  have hU : conjSub t (conjClosure S.V3 S.G1) = conjClosure S.V3 S.G1 :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 (hTH ht))
  have hL : conjSub t L = L := F7.conjSub_eq_of_mem_normalizer (S.T_le_NL ht)
  have e : conjSub t (conjClosure (conjClosure S.V3 S.G1) L) =
      conjClosure (conjClosure S.V3 S.G1) L := by rw [conjSub_conjClosure_eq, hU, hL]
  refine F7.mem_normalizer_of_conj_le e.le ?_
  rw [← e, conjSub_conjSub_inv, e]

theorem conj_mem_G1_of_UL (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    {a : G} (hA : conjSub a (fsuV1 T V) ≤ conjClosure (conjClosure S.V3 S.G1) L) {u : G}
    (hu : u ∈ conjClosure (conjClosure S.V3 S.G1) L) : a⁻¹ * u * a ∈ S.G1 := by
  have hz : a * S.z * a⁻¹ ∈ conjClosure (conjClosure S.V3 S.G1) L :=
    hA (mul_mem_conjSub (S.mem_V1_iff.2 (Or.inr rfl)))
  have hc := isElemAbelian_comm hUL hu hz
  show a⁻¹ * u * a ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc a⁻¹ * u * a * S.z = a⁻¹ * (u * (a * S.z * a⁻¹)) * a := by group
    _ = a⁻¹ * ((a * S.z * a⁻¹) * u) * a := by rw [hc]
    _ = S.z * (a⁻¹ * u * a) := by group

theorem relIndex_UL_inf_le {ρ : ↥S.G1 →* Perm (Fin 6)}
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L)) {a : G}
    (hA : conjSub a (fsuV1 T V) ≤ conjClosure (conjClosure S.V3 S.G1) L) :
    (conjClosure (conjClosure S.V3 S.G1) L ⊓ conjSub a (pCoreOf 2 S.G1)).relIndex
      (conjClosure (conjClosure S.V3 S.G1) L) ≤ 16 := by
  set UL := conjClosure (conjClosure S.V3 S.G1) L with hULdef
  have hUg : ∀ u : ↥UL, a⁻¹ * (u : G) * a ∈ S.G1 := fun u => S.conj_mem_G1_of_UL hUL hA u.2
  let φ : ↥UL →* Perm (Fin 6) :=
    { toFun := fun u => ρ ⟨a⁻¹ * (u : G) * a, hUg u⟩
      map_one' := by
        have e : (⟨a⁻¹ * ((1 : ↥UL) : G) * a, hUg 1⟩ : ↥S.G1) = 1 := Subtype.ext (by simp)
        simp only [e, map_one]
      map_mul' := fun u v => by
        have e : (⟨a⁻¹ * ((u * v : ↥UL) : G) * a, hUg (u * v)⟩ : ↥S.G1) =
            ⟨a⁻¹ * (u : G) * a, hUg u⟩ * ⟨a⁻¹ * (v : G) * a, hUg v⟩ :=
          Subtype.ext (by simp only [Subgroup.coe_mul]; group)
        simp only [e, map_mul] }
  have hker' : φ.ker = (UL ⊓ conjSub a (pCoreOf 2 S.G1)).subgroupOf UL := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_conjSub]
    constructor
    · intro h
      exact ⟨u.2, (hker _).1 h⟩
    · rintro ⟨-, h⟩
      exact (hker ⟨_, hUg u⟩).2 h
  have hidx : (UL ⊓ conjSub a (pCoreOf 2 S.G1)).relIndex UL = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker', Subgroup.index_ker]
  have h6 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have h720 : Nat.card φ.range ∣ 720 := h6 ▸ Subgroup.card_subgroup_dvd_card φ.range
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hUL)
  have hdvd : Nat.card φ.range ∣ 2 ^ k := by
    rw [← hidx, ← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hidx, hj']
  have hj4 : j ≤ 4 := by
    by_contra h
    push Not at h
    have h32 : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 h).trans (hj' ▸ h720)
    norm_num at h32
  calc 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj4
    _ = 16 := by norm_num

theorem comm_mem_A1 (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) {a x u : G}
    (hx : x ∈ conjSub a (conjClosure S.V3 S.G1)) (hu : u ∈ conjSub a (pCoreOf 2 S.G1)) :
    x * u * x⁻¹ * u⁻¹ ∈ conjSub a (fsuV1 T V) := by
  rw [mem_conjSub] at hx hu ⊢
  have := hF.toHypF91.commutator_conjClosure_le _ hx _ hu
  have e : a⁻¹ * (x * u * x⁻¹ * u⁻¹) * a =
      (a⁻¹ * x * a) * (a⁻¹ * u * a) * (a⁻¹ * x * a)⁻¹ * (a⁻¹ * u * a)⁻¹ := by group
  rw [e]
  exact this

theorem false_of_steinberg (hhat : ¬ IsHatA6 L)
    (hG52 : StmtG52) (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    {W W₁ W₂ : Subgroup G} (hWU : W < conjClosure (conjClosure S.V3 S.G1) L)
    (hWN : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure (conjClosure S.V3 S.G1) L →
      L ⊔ T ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨
        W' = conjClosure (conjClosure S.V3 S.G1) L)
    (hQW : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ u ∈ conjClosure (conjClosure S.V3 S.G1) L,
      q * u * q⁻¹ * u⁻¹ ∈ W)
    (hW₁ : W ≤ W₁ ∧ W₁ ≤ conjClosure (conjClosure S.V3 S.G1) L ∧ W.relIndex W₁ = 4 ∧
      ∀ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ L ⊔ T → S.frame.ρ y ∈ g5G1 →
        (y : G) ∈ Subgroup.normalizer (W₁ : Set G))
    (hW₂ : W ≤ W₂ ∧ W₂ ≤ conjClosure (conjClosure S.V3 S.G1) L ∧ W.relIndex W₂ = 4 ∧
      ∀ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ L ⊔ T → S.frame.ρ y ∈ cA6 →
        (y : G) ∈ Subgroup.normalizer (W₂ : Set G))
    {x : ↥(Subgroup.normalizer (V : Set G))} (hxT : (x : G) ∈ T) (hx : S.frame.ρ x = swap 4 5)
    (hcod : (centralizerMod W (conjClosure (conjClosure S.V3 S.G1) L)
      (Subgroup.zpowers (x : G))).relIndex (conjClosure (conjClosure S.V3 S.G1) L) < 2 ^ 8) :
    False := by
  set UL := conjClosure (conjClosure S.V3 S.G1) L with hULdef
  set Y := L ⊔ T with hY
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  set ρY : ↥Y →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hYN) with hρY
  have hρYe : ∀ y : ↥Y, ρY y = S.frame.ρ ⟨y, hYN y.2⟩ := fun _ => rfl
  have hTH : T ≤ S.G1 := fun t ht => by
    have := S.T_le_NV1 ht
    rwa [S.normalizer_V1] at this
  have hYUL : Y ≤ Subgroup.normalizer (UL : Set G) := by
    refine sup_le (le_normalizer_conjClosure _ L) fun t ht => ?_
    have hU : conjSub t (conjClosure S.V3 S.G1) = conjClosure S.V3 S.G1 :=
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 (hTH ht))
    have hL : conjSub t L = L := F7.conjSub_eq_of_mem_normalizer (S.T_le_NL ht)
    have e : conjSub t UL = UL := by rw [hULdef, conjSub_conjClosure_eq, hU, hL]
    refine F7.mem_normalizer_of_conj_le e.le ?_
    rw [← e, conjSub_conjSub_inv, e]
  have hUab : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hWle : W ≤ UL := hWU.le
  have hULN : UL ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w (hWle hw) a ha)
  have hsurj : Function.Surjective ρY := by
    intro σ
    by_cases hs : Perm.sign σ = 1
    · obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.mpr hs)
      exact ⟨⟨l, Subgroup.mem_sup_left hlL⟩, by rw [hρYe]; exact hl⟩
    · have hs' : Perm.sign (σ * swap 4 5) = 1 := by
        rw [map_mul, Perm.sign_swap (by decide)]
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h
        · exact absurd h hs
        · rw [h]; decide
      obtain ⟨l, hlL, hl⟩ := (S.frame.image_L _).2 (Perm.mem_alternatingGroup.mpr hs')
      refine ⟨⟨l * x, Y.mul_mem (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hxT)⟩, ?_⟩
      rw [hρYe]
      have e : (⟨(l : G) * x, hYN (Y.mul_mem (Subgroup.mem_sup_left hlL)
          (Subgroup.mem_sup_right hxT))⟩ : ↥(Subgroup.normalizer (V : Set G))) = l * x := rfl
      rw [e, map_mul, hl, hx, mul_assoc, swap_mul_self, mul_one]
  have hker : ∀ y : ↥Y, ρY y = 1 → ∀ a ∈ UL, (y : G) * a * (y : G)⁻¹ * a⁻¹ ∈ W := by
    intro y hy a ha
    rw [hρYe] at hy
    have hC : (y : G) ∈ Subgroup.centralizer (V : Set G) := (S.rho_eq_one_iff _).1 hy
    have hT : (y : G) ∈ T := S.cLT_le_T hhat ⟨y.2, hC⟩
    have hQ : (y : G) ∈ pCoreOf 2 (L ⊔ T) := by rw [← S.cT]; exact ⟨hT, hC⟩
    exact hQW _ hQ a ha
  obtain ⟨-, hswap, -⟩ := hG52 G UL W Y ρY hWle hULN
    (fun a ha => by rw [← sq, isElemAbelian_pow_eq_one hUL ha]; exact W.one_mem)
    (fun a ha a' ha' => by rw [hUab a ha a' ha']; group; exact W.one_mem)
    hYUL hWN hsurj hker hWU hmax
    ⟨W₁, hW₁.1, hW₁.2.1, hW₁.2.2.1, fun y hy => hW₁.2.2.2 ⟨y, hYN y.2⟩ y.2 hy⟩
    ⟨W₂, hW₂.1, hW₂.2.1, hW₂.2.2.1, fun y hy => hW₂.2.2.2 ⟨y, hYN y.2⟩ y.2 hy⟩
  have h8 := hswap ⟨x, Subgroup.mem_sup_right hxT⟩
    (by rw [hρYe]; exact ⟨4, 5, by decide, hx⟩)
  rw [h8] at hcod
  exact lt_irrefl _ hcod

section NatLines

variable {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {τ : Perm (Fin 6)}
  (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
include hρ' hN' hker' hβs hβk hβe

theorem UH_inf_W (hhat : ¬ IsHatA6 L) {W : Subgroup G} (hVW : V ≤ W)
    (hWU : W < conjClosure (conjClosure S.V3 S.G1) L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : conjClosure S.V3 S.G1 ⊓ W = S.V3 := by
  set U := conjClosure S.V3 S.G1 with hUdef
  set X := U ⊓ W with hXdef
  have hV3X : S.V3 ≤ X := le_inf (le_conjClosure _ _) (S.V3_le_V.trans hVW)
  have hU32 : Nat.card U = 32 := S.card_UH_nat hβs hβk
  set c := S.cL1 hhat with hcdef
  have hcL1 : (c : G) ∈ S.L1 := S.cL1_mem hhat
  have hcL : (c : G) ∈ L := S.L1_le_L hcL1
  have hcG1 : (c : G) ∈ S.G1 := by
    have := (S.L1_le hcL1).2
    rwa [S.normalizer_V1] at this
  have hcN3 : (c : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    S.L1T_le_NV3 (Subgroup.mem_sup_left hcL1)
  have hc3 : (c : G) ^ 3 = 1 := S.cL1_cube hhat
  have hc1 : (c : G) ≠ 1 := by
    intro h
    have h1 : c = 1 := Subtype.ext h
    have := S.cL1_rho hhat
    rw [← hcdef, h1, map_one] at this
    exact absurd this.symm (by decide)
  set k : ↥S.G1 := ⟨c, hcG1⟩ with hkdef
  have hk3 : k ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hk1 : k ≠ 1 := fun h => hc1 (by rw [show (c : G) = ((k : ↥S.G1) : G) from rfl, h]; rfl)
  have hcX : ∀ u ∈ X, (c : G) * u * (c : G)⁻¹ ∈ X := fun u hu =>
    ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hcG1) u).mp hu.1,
      (Subgroup.mem_normalizer_iff.mp (hLW hcL) u).mp hu.2⟩
  have hXd : Nat.card X ∣ 2 ^ 5 := by
    rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hU32]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hXj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hXd
  have h8 : 8 ∣ Nat.card X := by rw [← S.card_V3]; exact Subgroup.card_dvd_of_le hV3X
  rw [hXj] at h8
  interval_cases j
  · norm_num at h8
  · norm_num at h8
  · norm_num at h8
  · exact (Subgroup.eq_of_le_of_card_ge hV3X (by rw [hXj, S.card_V3]; norm_num)).symm
  ·
    exfalso
    have h2 : S.V3.relIndex X = 2 := by
      have h1 := Subgroup.relIndex_mul_card S.V3 X
      rw [inf_eq_left.2 hV3X, S.card_V3, hXj] at h1
      omega
    obtain ⟨u, huX, hu3⟩ : ∃ u ∈ X, u ∉ S.V3 := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le (show X ≤ S.V3 from h)
      rw [hXj, S.card_V3] at this
      norm_num at this
    have hcu3 : (c : G) * u * (c : G)⁻¹ ∉ S.V3 := fun h =>
      hu3 ((Subgroup.mem_normalizer_iff.mp hcN3 u).mpr h)
    have := inv_mul_mem_of_relIndex_two h2 huX (hcX u huX) hu3 hcu3
    exact hu3 (S.mem_V3_of_fpf_nat hρ' hN' hker' hβk hβe hk3 hk1 hcN3 huX.1 this)
  ·
    exfalso
    have hUW : U ≤ W := by
      have e : X = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hXj, hU32]; norm_num)
      rw [← e]; exact inf_le_right
    have : conjClosure U L ≤ W := conjClosure_le fun l hl u hu =>
      (Subgroup.mem_normalizer_iff.mp (hLW hl) u).mp (hUW hu)
    exact hWU.not_ge this

end NatLines

section NatSt

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L)
  (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  {K : Subgroup G} (hKT : K ⊔ T = S.G1)
  (hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6))
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hNS h13315 hhat h1356two hG1 h13314 hF hβs hβk hβe hρ' hN' hker' hKT hKA' honto'

theorem U2_inf_W (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    {W : Subgroup G} (hVW : V ≤ W) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hUW : conjClosure S.V3 S.G1 ⊓ W = S.V3) : S.U2 ⊓ W = V := by
  set X := S.U2 ⊓ W with hXdef
  have h64 := S.card_U2_nat h13315 hhat hNS h1356two hG1 h13314 hF hβs hβk hβe hρ' hN' hker' hKT
    hKA' honto'
  have h16 := S.card_U21_nat hβs hβk hβe hρ' hN' honto'
  have hVX : V ≤ X := le_inf S.V_le_U2 hVW
  have hU21W : S.U21 ⊓ W ≤ S.V3 := by
    rw [← hUW]; exact inf_le_inf_right W S.U21_le_UH
  have hXd : Nat.card X ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← h64]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hXj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hXd
  have h16d : 16 ∣ Nat.card X := by rw [← S.card_V]; exact Subgroup.card_dvd_of_le hVX
  rw [hXj] at h16d
  interval_cases j
  · norm_num at h16d
  · norm_num at h16d
  · norm_num at h16d
  · norm_num at h16d
  · exact (Subgroup.eq_of_le_of_card_ge hVX (by rw [hXj, S.card_V]; norm_num)).symm
  ·
    exfalso
    obtain ⟨x, hxL2, ⟨m, hm, hxm⟩, v, hv, hxv⟩ := S.exists_L2_not_NV3 h13315 hhat
    have hxL : x ∈ L := S.L2_le_L hxL2
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hxL
    have hxU2 : x ∈ Subgroup.normalizer (S.U2 : Set G) := S.normalizes_U2 (S.L2_le_NV2 hxL2) hxV
    have hxX : x ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_inf_of hxU2 (hLW hxL)
    have hXU2 : X.relIndex S.U2 = 2 := by
      have h1 := Subgroup.relIndex_mul_card X S.U2
      rw [inf_eq_left.2 (inf_le_left : X ≤ S.U2), hXj, h64] at h1
      omega
    have hVX2 : V.relIndex X = 2 := by
      have h1 := Subgroup.relIndex_mul_card V X
      rw [inf_eq_left.2 hVX, S.card_V, hXj] at h1
      omega
    have hfix : ∀ a ∈ S.U21, a⁻¹ * (x * a * x⁻¹) ∈ V := by
      intro a ha
      by_cases ha3 : a ∈ S.V3
      · exact V.mul_mem (V.inv_mem (S.V3_le_V ha3))
          ((Subgroup.mem_normalizer_iff.mp hxV a).mp (S.V3_le_V ha3))
      have haU2 : a ∈ S.U2 := S.U21_le_U2 ha
      have haX : a ∉ X := fun h => ha3 (hU21W ⟨ha, h.2⟩)
      have hconjX : ∀ b, b ∉ X → x * b * x⁻¹ ∉ X := fun b hb h =>
        hb ((Subgroup.mem_normalizer_iff.mp hxX b).mpr h)
      have hconjU : ∀ b ∈ S.U2, x * b * x⁻¹ ∈ S.U2 := fun b hb =>
        (Subgroup.mem_normalizer_iff.mp hxU2 b).mp hb
      have ha1U := hconjU a haU2
      have ha2U := hconjU _ ha1U
      have ha1X := hconjX a haX
      have ha2X := hconjX _ ha1X
      have hc := inv_mul_mem_of_relIndex_two hXU2 haU2 ha1U haX ha1X
      have hd := inv_mul_mem_of_relIndex_two hXU2 haU2 ha2U haX ha2X
      by_contra hcV
      by_cases hdV : a⁻¹ * (x * (x * a * x⁻¹) * x⁻¹) ∈ V
      · apply hcV
        refine conj_mem_of_sq_conj_mem hxV hm hxm ?_
        have e : x ^ 2 * a * (x ^ 2)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        rw [e]; exact hdV
      · have h1 := inv_mul_mem_of_relIndex_two hVX2 hc hd hcV hdV
        have e : (a⁻¹ * (x * a * x⁻¹))⁻¹ * (a⁻¹ * (x * (x * a * x⁻¹) * x⁻¹)) =
            x * (a⁻¹ * (x * a * x⁻¹)) * x⁻¹ := by group
        rw [e] at h1
        exact hcV ((Subgroup.mem_normalizer_iff.mp hxV _).mpr h1)
    have hle : S.U2 ≤ S.U21 ⊔ V := by
      refine (S.U2_le_sup hxL2 hv hxv).trans (sup_le le_sup_left fun y hy => ?_)
      rw [mem_conjSub] at hy
      have h1 := hfix _ hy
      have e : y = (x⁻¹ * y * x) * ((x⁻¹ * y * x)⁻¹ * (x * (x⁻¹ * y * x) * x⁻¹)) := by group
      rw [e]
      exact (S.U21 ⊔ V).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h1)
    have hinf : S.U21 ⊓ V = S.V3 := by
      refine le_antisymm (fun y hy => ?_) (le_inf S.V3_le_U21 S.V3_le_V)
      rw [← S.V_inf_UH hNS h13315 h1356two hG1 h13314]
      exact ⟨hy.2, S.U21_le_UH hy.1⟩
    have hU2L := S.U2_le_UL h13315 hhat
    have hN : S.U21 ≤ Subgroup.normalizer (V : Set G) := fun u hu =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
        isElemAbelian_comm hUL (hU2L (S.V_le_U2 hw)) (hU2L (S.U21_le_U2 hu)))
    have hcs := card_sup_mul_card_inf' hN
    rw [hinf, h16, S.card_V, S.card_V3] at hcs
    have := Subgroup.card_le_of_le hle
    rw [h64] at this
    omega
  ·
    exfalso
    have e : X = S.U2 := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hXj, h64]; norm_num)
    have hU2W : S.U2 ≤ W := by rw [← e]; exact inf_le_right
    have h1 : S.U21 ≤ S.V3 := fun u hu => hU21W ⟨hu, hU2W (S.U21_le_U2 hu)⟩
    have := Subgroup.card_le_of_le h1
    rw [h16, S.card_V3] at this
    norm_num at this

theorem false_nat (hG52 : StmtG52) (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
    (htr : IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V))
    (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1) : False := by
  set U := conjClosure S.V3 S.G1 with hUdef
  set UL := conjClosure U L with hULdef
  have hUab : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hYUL := S.LT_le_NUL
  have hYV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  obtain ⟨W, hVW, hWU, hWN, hmax⟩ :=
    exists_maximal_invariant (S.V_lt_UL hNS h13315 h1356two hG1 h13314) hYV
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hWN
  have hULN : UL ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w (hWU.le hw) a ha)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQW := comm_mem_of_maximal (pCoreOf_isPGroup 2 (L ⊔ T))
    (S.UL_le_Q hNS h13315 h1356two hG1 hF) hWU (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _)
    hYUL hWN hmax
  obtain ⟨x, hxU, hx⟩ := S.exists_Uγ_swap45 h13315 hF s hDH hDγ htr
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hQT := S.pCoreOf_G1_le_T
  rw [hg1] at hQT
  have hxT : (x : G) ∈ T := hQT (S.Uγ_le_QH_case1 hF s hDγ hxU)
  have hUW := S.UH_inf_W hρ' hN' hker' hβs hβk hβe hhat hVW hWU hLW
  have hUN : U ≤ Subgroup.normalizer (W : Set G) := (le_conjClosure U L).trans hULN
  have hW₁ := relIndex_sup_mul_card_inf hUN
  rw [hUW, S.card_UH_nat hβs hβk, S.card_V3] at hW₁
  have hU2W := S.U2_inf_W hNS h13315 hhat h1356two hG1 h13314 hF hβs hβk hβe hρ' hN' hker' hKT
    hKA' honto' hUL hVW hLW hUW
  have hU2L := S.U2_le_UL h13315 hhat
  have hW₂ := relIndex_sup_mul_card_inf (hU2L.trans hULN)
  rw [hU2W, S.card_U2_nat h13315 hhat hNS h1356two hG1 h13314 hF hβs hβk hβe hρ' hN' hker' hKT
    hKA' honto', S.card_V] at hW₂
  have hA : conjSub (g : G) (fsuV1 T V) ≤ UL := hA1.trans (le_conjClosure U L)
  have h16 := S.relIndex_UL_inf_le hker' hUL hA
  have hAP : conjSub (g : G) (fsuV1 T V) ≤ UL ⊓ conjSub (g : G) (pCoreOf 2 S.G1) :=
    le_inf hA (conjSub_mono _ hF.toHypF91.V₁_le_pCoreOf)
  have hcard : Nat.card (conjSub (g : G) (fsuV1 T V)) = 2 := by
    rw [CosetGeom.card_conjSub, S.card_V1]
  have h32 := relIndex_centralizerMod_le hUab inf_le_left h16 hWU.le hcard hAP
    (fun u hu => S.comm_mem_A1 hF hxU hu.2)
  refine S.false_of_steinberg hhat hG52 hUL hWU hWN hmax hQW
    ⟨le_sup_right, sup_le (le_conjClosure U L) hWU.le, by omega, fun y hyN hy => ?_⟩
    ⟨le_sup_right, sup_le hU2L hWU.le, by omega, fun y hyN hy => ?_⟩ hxT hx
    (lt_of_le_of_lt h32 (by norm_num))
  · exact Subgroup.inf_normalizer_le_normalizer_sup U W
      ⟨le_normalizer_conjClosure S.V3 S.G1 (S.mem_G1_of_g5G1 hy), hWN hyN⟩
  · exact Subgroup.inf_normalizer_le_normalizer_sup S.U2 W
      ⟨S.normalizes_U2 (S.mem_NV2_of_cA6 hy) y.2, hWN hyN⟩

end NatSt

end Setting4

@[expose] def Input13833AbCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L →
      ∀ K : Subgroup G, S.G1 ≤ Subgroup.normalizer (K : Set G) → K ⊔ T = S.G1 → S.L1 ≤ K →
        (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) →
      ∀ ρ : ↥S.G1 →* Perm (Fin 6), (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) →
        (∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6)) →
        (∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ) →
      ∀ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6), Function.Surjective β →
        (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) →
        (∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
          Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))) →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) →
        IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L) → False

theorem input13833Ab_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (hG52 : StmtG52)
    (hCov : Input13833AbCover) : Input13833Ab := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat γ γ' g s hDγ hUL
  obtain ⟨K, hKN, hKT, hL1K, hFs, hcase, h3⟩ := hst
  rcases hcase with ⟨-, ρ, hker, hKA, honto, hβ⟩ | ⟨hh, -⟩
  swap
  · exact absurd hh hhat
  obtain ⟨hDH, -, htr, -, hnQ⟩ := h3 γ γ' g s (Or.inl hDγ)
  rcases hβ with ⟨β, hβs, hβk, hβe⟩ | ⟨β, hβs, hβk, hβe⟩
  · have hn : ¬ F8.Uγ V S.G1 (g : G) ≤ ballStab 1 (F8.γ₁ T L S.G1) := fun h =>
      hnQ (h.trans (S.ballStab_γ₁_le_QH hF hKT hL1K ρ hker hKA honto
        (Or.inl ⟨β, hβs, hβk, hβe⟩)))
    obtain ⟨hA1, -⟩ := S.case1_symm hF s hn h3 hDH
    obtain ⟨τ, ρ', hρ', hN', hker', hKA', honto', -, -⟩ :=
      S.exists_coords hF hKT hL1K ρ hker hKA honto (Or.inl ⟨β, hβs, hβk, hβe⟩)
    exact S.false_nat hNS h13315 hhat h1356two hG1 h13314 hF hβs hβk hβe hρ' hN' hker' hKT hKA'
      honto' hG52 hUL s hDH hDγ htr hA1
  · exact hCov G T L V S hNS hNU hG1 hab hF
      ⟨K, hKN, hKT, hL1K, hFs, Or.inl ⟨hhat, ρ, hker, hKA, honto, Or.inr ⟨β, hβs, hβk, hβe⟩⟩, h3⟩
      hhat K hKN hKT hL1K hFs ρ hker hKA honto β hβs hβk hβe γ γ' g s hDγ hUL

end CFSG.Quasithin.H13.A6
