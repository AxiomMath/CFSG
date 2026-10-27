module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E55

variable {G : Type*} [Group G]

section PData

structure PDecomp (I P V N₁ N₂ P₁ P₂ : Subgroup G) : Prop where
  PI : I ≤ Subgroup.normalizer (P : Set G)
  P_le_I : P ≤ I
  VI : I ≤ Subgroup.normalizer (V : Set G)
  V_le_P : V ≤ P
  V_central : ∀ v ∈ V, ∀ p ∈ P, v * p = p * v
  N₁_le_I : N₁ ≤ I
  N₂_le_I : N₂ ≤ I
  N₁_norm : ∀ i ∈ I, ∀ n ∈ N₁, i * n * i⁻¹ ∈ N₁
  N₂_norm : ∀ i ∈ I, ∀ n ∈ N₂, i * n * i⁻¹ ∈ N₂
  sup : P₁ ⊔ P₂ = P
  inf : P₁ ⊓ P₂ = V
  cent₁ : P₁ = centralizerMod V P N₂
  cent₂ : P₂ = centralizerMod V P N₁

namespace PDecomp

variable {I P V N₁ N₂ P₁ P₂ : Subgroup G} (h : PDecomp I P V N₁ N₂ P₁ P₂)
include h

theorem symm : PDecomp I P V N₂ N₁ P₂ P₁ :=
  ⟨h.PI, h.P_le_I, h.VI, h.V_le_P, h.V_central, h.N₂_le_I, h.N₁_le_I, h.N₂_norm, h.N₁_norm,
    by rw [sup_comm]; exact h.sup, by rw [inf_comm]; exact h.inf, h.cent₂, h.cent₁⟩

theorem conj_V {i v : G} (hi : i ∈ I) (hv : v ∈ V) : i * v * i⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (h.VI hi) v).mp hv

theorem conj_P {i p : G} (hi : i ∈ I) (hp : p ∈ P) : i * p * i⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp (h.PI hi) p).mp hp

theorem V_le_P₂ : V ≤ P₂ := by
  intro v hv
  rw [h.cent₂]
  refine ⟨h.V_le_P hv, Subgroup.le_normalizer hv, fun u hu => ?_⟩
  have h1 : u * v⁻¹ * u⁻¹ ∈ V := h.conj_V (h.N₁_le_I hu) (V.inv_mem hv)
  have e : v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
  rw [e]
  exact V.mul_mem hv h1

theorem P₂_le_P : P₂ ≤ P := by
  rw [← h.sup]
  exact le_sup_right

theorem P₁_le_P : P₁ ≤ P := h.symm.P₂_le_P

theorem conj_P₂ {i x : G} (hi : i ∈ I) (hx : x ∈ P₂) : i * x * i⁻¹ ∈ P₂ := by
  rw [h.cent₂] at hx ⊢
  obtain ⟨hxP, hxN, hxc⟩ := hx
  refine ⟨h.conj_P hi hxP, ?_, fun u hu => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.VI hi) hxN) (Subgroup.inv_mem _ (h.VI hi))
  · have hu' : i⁻¹ * u * i ∈ N₁ := by
      have := h.N₁_norm i⁻¹ (I.inv_mem hi) u hu
      simpa using this
    have h1 := hxc _ hu'
    have h2 : i * (x * (i⁻¹ * u * i) * x⁻¹ * (i⁻¹ * u * i)⁻¹) * i⁻¹ ∈ V := h.conj_V hi h1
    have e : i * (x * (i⁻¹ * u * i) * x⁻¹ * (i⁻¹ * u * i)⁻¹) * i⁻¹ =
        i * x * i⁻¹ * u * (i * x * i⁻¹)⁻¹ * u⁻¹ := by group
    rw [e] at h2
    exact h2

theorem conj_P₁ {i x : G} (hi : i ∈ I) (hx : x ∈ P₁) : i * x * i⁻¹ ∈ P₁ :=
  h.symm.conj_P₂ hi hx

theorem I_le_normalizer_P₂ : I ≤ Subgroup.normalizer (P₂ : Set G) := by
  intro i hi
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h.conj_P₂ hi, fun hx => ?_⟩
  have := h.conj_P₂ (I.inv_mem hi) hx
  simpa [mul_assoc] using this

theorem exists_mul {a : G} (ha : a ∈ P) : ∃ p₁ ∈ P₁, ∃ p₂ ∈ P₂, p₁ * p₂ = a := by
  have h1 : P₁ ≤ Subgroup.normalizer (P₂ : Set G) :=
    (h.P₁_le_P.trans h.P_le_I).trans h.I_le_normalizer_P₂
  have e := Subgroup.coe_mul_of_left_le_normalizer_right P₁ P₂ h1
  rw [h.sup] at e
  have ha' : a ∈ ((P : Subgroup G) : Set G) := ha
  rw [e] at ha'
  exact ha'

theorem comm_mem_P₂ {a n : G} (ha : a ∈ P) (hn : n ∈ N₂) : a * n * a⁻¹ * n⁻¹ ∈ P₂ := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h.exists_mul ha
  have hnI : n ∈ I := h.N₂_le_I hn
  have hv : p₁ * n * p₁⁻¹ * n⁻¹ ∈ V := by
    have h0 := hp₁
    rw [h.cent₁] at h0
    exact h0.2.2 n hn
  have hq : n * p₂⁻¹ * n⁻¹ ∈ P₂ := h.conj_P₂ hnI (P₂.inv_mem hp₂)
  have e : p₁ * p₂ * n * (p₁ * p₂)⁻¹ * n⁻¹ =
      (p₁ * (p₂ * (n * p₂⁻¹ * n⁻¹)) * p₁⁻¹) * (p₁ * n * p₁⁻¹ * n⁻¹) := by group
  rw [e]
  refine P₂.mul_mem ?_ (h.V_le_P₂ hv)
  exact h.conj_P₂ (h.P_le_I (h.P₁_le_P hp₁)) (P₂.mul_mem hp₂ hq)

theorem sq_mem_V (h₁ : ∀ x ∈ P₁, x * x ∈ V) (h₂ : ∀ x ∈ P₂, x * x ∈ V) {a : G} (ha : a ∈ P) :
    a * a ∈ V := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h.exists_mul ha
  have hp₂P : p₂ ∈ P := h.P₂_le_P hp₂
  have hp₁P : p₁ ∈ P := h.P₁_le_P hp₁
  have hw₁ : p₂⁻¹ * p₁⁻¹ * p₂ * p₁ ∈ P₁ := by
    have h1 : p₂⁻¹ * p₁⁻¹ * p₂⁻¹⁻¹ ∈ P₁ := h.conj_P₁ (h.P_le_I (P.inv_mem hp₂P)) (P₁.inv_mem hp₁)
    simpa [mul_assoc] using P₁.mul_mem h1 hp₁
  have hw₂ : p₂⁻¹ * p₁⁻¹ * p₂ * p₁ ∈ P₂ := by
    have h1 : p₁⁻¹ * p₂ * p₁⁻¹⁻¹ ∈ P₂ := h.conj_P₂ (h.P_le_I (P.inv_mem hp₁P)) hp₂
    have h2 := P₂.mul_mem (P₂.inv_mem hp₂) h1
    simpa [mul_assoc] using h2
  have hw : p₂⁻¹ * p₁⁻¹ * p₂ * p₁ ∈ V := by
    rw [← h.inf]
    exact ⟨hw₁, hw₂⟩
  have e : p₁ * p₂ * (p₁ * p₂) = (p₁ * p₁) * (p₂⁻¹ * p₁⁻¹ * p₂ * p₁) * (p₂ * p₂) := by
    have hc : ∀ q ∈ P, (p₂⁻¹ * p₁⁻¹ * p₂ * p₁) * q = q * (p₂⁻¹ * p₁⁻¹ * p₂ * p₁) :=
      fun q hq => h.V_central _ hw q hq
    have h3 : (p₂⁻¹ * p₁⁻¹ * p₂ * p₁) * p₂ = p₂ * (p₂⁻¹ * p₁⁻¹ * p₂ * p₁) := hc p₂ hp₂P
    calc p₁ * p₂ * (p₁ * p₂) = p₁ * (p₂ * p₁) * p₂ := by group
      _ = p₁ * (p₁ * p₂ * (p₂⁻¹ * p₁⁻¹ * p₂ * p₁)) * p₂ := by
          congr 2
          group
      _ = (p₁ * p₁) * (p₂ * (p₂⁻¹ * p₁⁻¹ * p₂ * p₁)) * p₂ := by group
      _ = (p₁ * p₁) * ((p₂⁻¹ * p₁⁻¹ * p₂ * p₁) * p₂) * p₂ := by rw [h3]
      _ = (p₁ * p₁) * (p₂⁻¹ * p₁⁻¹ * p₂ * p₁) * (p₂ * p₂) := by group
  rw [e]
  exact V.mul_mem (V.mul_mem (h₁ p₁ hp₁) hw) (h₂ p₂ hp₂)

end PDecomp

end PData

section TwoGroup

theorem exists_pow_mul {Y U : Subgroup G} (hUY : U ≤ Subgroup.normalizer (Y : Set G)) {y u : G}
    (hy : y ∈ Y) (hu : u ∈ U) (n : ℕ) : ∃ yn ∈ Y, (y * u) ^ n = yn * u ^ n := by
  induction n with
  | zero => exact ⟨1, Y.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨yn, hyn, hn⟩ := ih
    have hun : u ^ n ∈ U := Subgroup.pow_mem _ hu n
    have h1 : u ^ n * y * (u ^ n)⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hUY hun) y).mp hy
    refine ⟨yn * (u ^ n * y * (u ^ n)⁻¹), Y.mul_mem hyn h1, ?_⟩
    rw [pow_succ, hn, pow_succ u n]
    group

theorem isPGroup_inf_centralizer {Y U V : Subgroup G} (hUY : U ≤ Subgroup.normalizer (Y : Set G))
    (hU : IsPGroup 2 U) (hYC : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (V : Set G))) :
    IsPGroup 2 ↥((Y ⊔ U) ⊓ Subgroup.centralizer (V : Set G)) := by
  rintro ⟨k, hkYU, hkC⟩
  have hk : k ∈ (Y : Set G) * (U : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y U hUY]
    exact hkYU
  obtain ⟨y, hy, u, hu, rfl⟩ := hk
  obtain ⟨m, hm⟩ := hU ⟨u, hu⟩
  have hum : u ^ (2 ^ m) = 1 := by
    simpa using congrArg Subtype.val hm
  obtain ⟨yn, hyn, hn⟩ := exists_pow_mul hUY hy hu (2 ^ m)
  rw [hum, mul_one] at hn
  have hmem : (y * u) ^ (2 ^ m) ∈ Y ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨?_, Subgroup.pow_mem _ hkC _⟩
    rw [hn]
    exact hyn
  obtain ⟨j, hj⟩ := hYC ⟨_, hmem⟩
  refine ⟨m + j, ?_⟩
  apply Subtype.ext
  have h1 : ((y * u) ^ (2 ^ m)) ^ (2 ^ j) = 1 := by
    simpa using congrArg Subtype.val hj
  show (y * u) ^ 2 ^ (m + j) = 1
  rw [pow_add, pow_mul]
  exact h1

theorem inf_centralizer_le_pCoreOf {Y U V : Subgroup G} (hUY : U ≤ Subgroup.normalizer (Y : Set G))
    (hU : IsPGroup 2 U) (hYC : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (V : Set G)))
    (hIV : Y ⊔ U ≤ Subgroup.normalizer (V : Set G)) :
    (Y ⊔ U) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (Y ⊔ U) := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (isPGroup_inf_centralizer hUY hU hYC)
  exact B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hIV)

end TwoGroup

section Closing

theorem Zu_le_centerP {U P Zu : Subgroup G} {g : G} (hZuU : Zu ≤ U)
    (hZuc : ∀ z ∈ Zu, ∀ u ∈ U, z * u = u * z)
    (hZuN : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (Zu : Set G))
    (hprod : ((P : Subgroup G) : Set G) =
      ((U ⊓ P : Subgroup G) : Set G) * (conjSubgroup (U ⊓ P) g : Set G))
    (hWg : conjSubgroup (U ⊓ P) g ≤ Subgroup.normalizer (U : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) (hZuP : Zu ≤ P)
    (hZu' : ∀ x ∈ conjSubgroup Zu g, x ∈ U → x = 1) :
    Zu ≤ P ⊓ Subgroup.centralizer (P : Set G) := by
  have hgP1 : ∀ p ∈ P, g * p * g⁻¹ ∈ P := fun p hp => (Subgroup.mem_normalizer_iff.mp hgP p).mp hp
  have hgP2 : ∀ p ∈ P, g⁻¹ * p * g ∈ P := by
    intro p hp
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (P : Set G)).inv_mem hgP) p).mp hp
    simpa using this
  have hmulP : ∀ p ∈ P, ∃ w ∈ U ⊓ P, ∃ w' ∈ conjSubgroup (U ⊓ P) g, w * w' = p := by
    intro p hp
    have : p ∈ ((U ⊓ P : Subgroup G) : Set G) * (conjSubgroup (U ⊓ P) g : Set G) := by
      rw [← hprod]
      exact hp
    exact this
  have hPN : P ≤ Subgroup.normalizer (U : Set G) := by
    intro p hp
    obtain ⟨w, hw, w', hw', rfl⟩ := hmulP p hp
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hw.1) (hWg hw')
  have hWZ : ∀ w ∈ U ⊓ P, ∀ x ∈ conjSubgroup Zu g, w * x * w⁻¹ ∈ conjSubgroup Zu g := by
    intro w hw x hx
    rw [mem_conjSubgroup_iff] at hx ⊢
    have hgw : g * w * g⁻¹ ∈ Subgroup.normalizer (Zu : Set G) := hZuN (hPN (hgP1 w hw.2))
    have e : g * (w * x * w⁻¹) * g⁻¹ = (g * w * g⁻¹) * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hgw _).mp hx
  have hZuW' : ∀ z' ∈ conjSubgroup Zu g, z' ∈ conjSubgroup (U ⊓ P) g := by
    intro z' hz'
    rw [mem_conjSubgroup_iff] at hz' ⊢
    exact ⟨hZuU hz', hZuP hz'⟩
  have hW'P : ∀ w' ∈ conjSubgroup (U ⊓ P) g, w' ∈ P := by
    intro w' hw'
    rw [mem_conjSubgroup_iff] at hw'
    have := hgP2 _ hw'.2
    simpa [mul_assoc] using this
  have hcW : ∀ z' ∈ conjSubgroup Zu g, ∀ w ∈ U ⊓ P, z' * w = w * z' := by
    intro z' hz' w hw
    have hz'N : z' ∈ Subgroup.normalizer (U : Set G) := hWg (hZuW' z' hz')
    have h1 : z' * w * z'⁻¹ * w⁻¹ ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp hz'N w).mp hw.1
      exact U.mul_mem this (U.inv_mem hw.1)
    have h2 : z' * w * z'⁻¹ * w⁻¹ ∈ conjSubgroup Zu g := by
      have := (conjSubgroup Zu g).mul_mem hz'
        (hWZ w hw z'⁻¹ ((conjSubgroup Zu g).inv_mem hz'))
      have e : z' * (w * z'⁻¹ * w⁻¹) = z' * w * z'⁻¹ * w⁻¹ := by group
      rwa [e] at this
    have h3 := hZu' _ h2 h1
    have : z' * w = w * z' := by
      have h4 : z' * w * z'⁻¹ * w⁻¹ = 1 := h3
      calc z' * w = (z' * w * z'⁻¹ * w⁻¹) * (w * z') := by group
        _ = w * z' := by rw [h4, one_mul]
    exact this
  have hcW' : ∀ z' ∈ conjSubgroup Zu g, ∀ w' ∈ conjSubgroup (U ⊓ P) g, z' * w' = w' * z' := by
    intro z' hz' w' hw'
    rw [mem_conjSubgroup_iff] at hz' hw'
    have := hZuc _ hz' _ hw'.1
    have e : g * (z' * w') * g⁻¹ = g * (w' * z') * g⁻¹ := by
      calc g * (z' * w') * g⁻¹ = (g * z' * g⁻¹) * (g * w' * g⁻¹) := by group
        _ = (g * w' * g⁻¹) * (g * z' * g⁻¹) := this
        _ = g * (w' * z') * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hZu'P : ∀ z' ∈ conjSubgroup Zu g, z' ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
    intro z' hz'
    refine ⟨hW'P z' (hZuW' z' hz'), Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    obtain ⟨w, hw, w', hw', rfl⟩ := hmulP p hp
    calc w * w' * z' = w * (w' * z') := by group
      _ = w * (z' * w') := by rw [hcW' z' hz' w' hw']
      _ = (w * z') * w' := by group
      _ = (z' * w) * w' := by rw [hcW z' hz' w hw]
      _ = z' * (w * w') := by group
  intro z hz
  have hz' : g⁻¹ * z * g ∈ conjSubgroup Zu g := by
    rw [mem_conjSubgroup_iff]
    have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [e]
    exact hz
  obtain ⟨hzP, hzC⟩ := hZu'P _ hz'
  have hzP' := hgP1 _ hzP
  have hzC' := (Subgroup.mem_normalizer_iff.mp (B2F.normalizer_le_normalizer_centralizer P hgP) _).mp hzC
  have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [e] at hzP' hzC'
  exact ⟨hzP', hzC'⟩

end Closing

end S153E55

end CFSG.Quasithin
