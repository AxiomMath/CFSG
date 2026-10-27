module

public import CFSG.Quasithin.H13.A6S13826e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem natural_of_le_sq
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {c : G} (hcK : c ∈ K)
    (hc3 : (α ⟨c, hcK⟩) ^ 3 = 1) (hc1 : α ⟨c, hcK⟩ ≠ 1)
    (hcc : ∀ t ∈ T, ∃ k : ↥K, ∀ hct : t⁻¹ * c * t ∈ K,
      α ⟨t⁻¹ * c * t, hct⟩ = α k * α ⟨c, hcK⟩ * (α k)⁻¹ ∨
        α ⟨t⁻¹ * c * t, hct⟩ = α k * (α ⟨c, hcK⟩)⁻¹ * (α k)⁻¹)
    {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H)
    (hle : (centralizerMod W X F).relIndex X ≤ ((F ⊓ pCoreOf 2 H).relIndex F) ^ 2) :
    W.relIndex X = 16 := by
  have hTH : T ≤ H := hs.hHK ▸ le_sup_right
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hαact : ∀ a b : ↥K, α a = α b →
      hs.act (Subgroup.inclusion hs.hKH a) = hs.act (Subgroup.inclusion hs.hKH b) := by
    intro a b hab
    have h1 : ((a⁻¹ * b : ↥K) : G) ∈ pCoreOf 2 H :=
      (hαk _).1 (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    have h2 := (hs.act_eq_one_iff (Subgroup.inclusion hs.hKH (a⁻¹ * b))).2 h1
    have e : Subgroup.inclusion hs.hKH (a⁻¹ * b) =
        (Subgroup.inclusion hs.hKH a)⁻¹ * Subgroup.inclusion hs.hKH b := by
      ext; simp
    rw [e, map_mul, map_inv] at h2
    exact inv_mul_eq_one.1 h2
  set c' := hs.act ⟨c, hs.hKH hcK⟩ with hc'
  have hc'L : c' ∈ autSec (autOn K X) ⊤ (W.subgroupOf X) :=
    (hs.mem_autSec_iff hs.hKH).2 ⟨_, hcK, rfl⟩
  have hc'3 : c' ^ 3 = 1 := by
    have h := hαact (⟨c, hcK⟩ ^ 3) 1 (by rw [map_pow, hc3, map_one])
    rw [map_pow, map_pow, map_one, map_one] at h
    exact h
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    rw [hαk]
    exact (hs.act_eq_one_iff ⟨c, hs.hKH hcK⟩).1 h
  set TX := autSec (autOn T X) ⊤ (W.subgroupOf X) with hTX
  have hTX2 : IsPGroup 2 TX := by
    rintro ⟨g, hg⟩
    obtain ⟨t, ht, rfl⟩ := (hs.mem_autSec_iff hTH).1 hg
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    refine ⟨n, Subtype.ext ?_⟩
    have htn : t ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, htn, map_one]
  have hGLT : autSec (autOn H X) ⊤ (W.subgroupOf X) ≤
      autSec (autOn K X) ⊤ (W.subgroupOf X) ⊔ TX := by
    intro g hg
    obtain ⟨h, -, rfl⟩ := (hs.mem_autSec_iff le_rfl).1 hg
    have hh : (h : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm, ← hs.hHK]
      exact h.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T K (hTH.trans hs.hKn)] at hh
    obtain ⟨t, ht, k, hk, htk⟩ := hh
    have e : h = ⟨t, hTH ht⟩ * ⟨k, hs.hKH hk⟩ := Subtype.ext htk.symm
    rw [e, map_mul]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right ((hs.mem_autSec_iff hTH).2 ⟨_, ht, rfl⟩))
      (Subgroup.mem_sup_left ((hs.mem_autSec_iff hs.hKH).2 ⟨_, hk, rfl⟩))
  have hcc' : ∀ t' ∈ TX, ∃ k' ∈ autSec (autOn K X) ⊤ (W.subgroupOf X),
      t'⁻¹ * c' * t' = k' * c' * k'⁻¹ ∨ t'⁻¹ * c' * t' = k' * c'⁻¹ * k'⁻¹ := by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := (hs.mem_autSec_iff hTH).1 ht'
    obtain ⟨k, hk⟩ := hcc t ht
    have hct : (t : G)⁻¹ * c * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hs.hKn (H.inv_mem t.2)) c).mp hcK
      simpa using this
    have htc : hs.act t⁻¹ * c' * hs.act t =
        hs.act (Subgroup.inclusion hs.hKH ⟨(t : G)⁻¹ * c * t, hct⟩) := by
      rw [hc', ← map_mul, ← map_mul]
      congr 1
    refine ⟨hs.act (Subgroup.inclusion hs.hKH k), (hs.mem_autSec_iff hs.hKH).2 ⟨_, k.2, rfl⟩, ?_⟩
    rw [← map_inv, htc]
    rcases hk hct with h | h
    · left
      have h1 := hαact ⟨(t : G)⁻¹ * c * t, hct⟩ (k * ⟨c, hcK⟩ * k⁻¹)
        (by rw [h, map_mul, map_mul, map_inv])
      have e : Subgroup.inclusion hs.hKH (k * ⟨c, hcK⟩ * k⁻¹) =
          Subgroup.inclusion hs.hKH k * ⟨c, hs.hKH hcK⟩ * (Subgroup.inclusion hs.hKH k)⁻¹ := by
        ext; simp
      rw [h1, e, map_mul, map_mul, map_inv]
    · right
      have h1 := hαact ⟨(t : G)⁻¹ * c * t, hct⟩ (k * (⟨c, hcK⟩ : ↥K)⁻¹ * k⁻¹)
        (by rw [h, map_mul, map_mul, map_inv, map_inv])
      have e : Subgroup.inclusion hs.hKH (k * (⟨c, hcK⟩ : ↥K)⁻¹ * k⁻¹) =
          Subgroup.inclusion hs.hKH k * (⟨c, hs.hKH hcK⟩ : ↥H)⁻¹ *
            (Subgroup.inclusion hs.hKH k)⁻¹ := by
        ext; simp
      rw [h1, e, map_mul, map_mul, map_inv, map_inv]
  have h1 := A6Md.natural_of_index_le_sq hs.sec_sq (hs.ctx hαs hαk) (hs.fixV_eq_bot hirr)
    (hs.irr_autSec hirr) hs.top_ne_bot hTX2 (hs.autSec_le hTH le_rfl) hGLT hc'L hc'3 hc'1 hcc'
    (hs.autSec_le hFH le_rfl) (hs.autSec_ne_bot hFH hF) (hs.isElemAbelian2_autSec hFH hFc hFs)
    ((hs.index_fixV_le hFH).trans (hle.trans (by rw [hs.card_autSec hFH])))
  rw [← card_sec (X := X) (W := W)]
  exact h1.1

theorem natural_of_hyp
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {u : G} (huH : u ∈ H)
    (huQ : u ∉ pCoreOf 2 H) (hu2 : u * u ∈ pCoreOf 2 H) {C : Subgroup G}
    (hidx : C.relIndex X ≤ 2) (hC : ∀ x ∈ C, u * x * u⁻¹ * x⁻¹ ∈ W) :
    W.relIndex X = 16 := by
  set u' := hs.act ⟨u, huH⟩ with hu'
  set B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) := Subgroup.zpowers u'
    with hB
  have hu'1 : u' ≠ 1 := fun h => huQ ((hs.act_eq_one_iff _).1 h)
  have hu'2 : u' ^ 2 = 1 := by
    rw [hu', ← map_pow, hs.act_eq_one_iff, pow_two]
    exact hu2
  have hBG : B ≤ autSec (autOn H X) ⊤ (W.subgroupOf X) := by
    rw [hB, Subgroup.zpowers_le]
    exact (hs.mem_autSec_iff le_rfl).2 ⟨_, huH, rfl⟩
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hu'1
    have : u' ∈ B := Subgroup.mem_zpowers u'
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hBab : IsElemAbelian2 B := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu'2, one_zpow]
  have hcardB : Nat.card B = 2 := by
    rw [hB, Nat.card_zpowers]
    exact orderOf_eq_prime hu'2 hu'1
  have hfix : (fixV B).index ≤ 2 := by
    have hle : (C.subgroupOf X).map (InternalSec.secMk (W.subgroupOf X)) ≤ fixV B := by
      rintro _ ⟨x, hx, rfl⟩ b hb
      have h1 : u' (InternalSec.secMk (W.subgroupOf X) x) =
          InternalSec.secMk (W.subgroupOf X) x := by
        rw [hu', act_secMk]
        have h2 : InternalSec.secMk (W.subgroupOf X) (Setup.rho X H hs.hHX ⟨u, huH⟩ x) *
            (InternalSec.secMk (W.subgroupOf X) x)⁻¹ = 1 := by
          rw [← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
          simp only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
          exact hC x (Subgroup.mem_subgroupOf.1 hx)
        exact mul_inv_eq_one.1 h2
      have hst : B ≤ MulAction.stabilizer (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))
          (InternalSec.secMk (W.subgroupOf X) x) := by
        rw [hB, Subgroup.zpowers_le]
        exact h1
      exact hst hb
    calc (fixV B).index
        ≤ ((C.subgroupOf X).map (InternalSec.secMk (W.subgroupOf X))).index :=
          Subgroup.index_antitone hle
      _ ≤ (C.subgroupOf X).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
            (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
      _ ≤ 2 := hidx
  have h1 := A6Md.natural_of_index_le hs.sec_sq (hs.ctx hαs hαk) (hs.fixV_eq_bot hirr)
    (hs.irr_autSec hirr) hs.top_ne_bot hBG hB1 hBab (by rw [hcardB]; exact hfix)
  rw [← card_sec (X := X) (W := W)]
  exact h1.1

theorem natural_of_transv
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {u : G} (huH : u ∈ H)
    (huQ : u ∉ pCoreOf 2 H) (hu2 : u * u ∈ pCoreOf 2 H) {z : G}
    (hz : ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ W ∨ u * x * u⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    W.relIndex X = 16 := by
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    have := mul_comm (⟨a, ha⟩ : ↥X) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hs.hHX huH) x).mp hx
  have hWn : ∀ w ∈ W, ∀ y ∈ X, y * w * y⁻¹ ∈ W := fun w hw y hy =>
    (Subgroup.mem_normalizer_iff.mp (hs.hHW (hs.hXH hy)) w).mp hw
  let C : Subgroup G :=
    { carrier := {x | x ∈ X ∧ u * x * u⁻¹ * x⁻¹ ∈ W}
      one_mem' := ⟨X.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨X.mul_mem ha hb, ?_⟩
        have e : u * (a * b) * u⁻¹ * (a * b)⁻¹ =
            (u * a * u⁻¹ * a⁻¹) * (a * (u * b * u⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact W.mul_mem ha' (hWn _ hb' a ha)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨X.inv_mem ha, ?_⟩
        have e : u * a⁻¹ * u⁻¹ * a⁻¹⁻¹ =
            (u * a⁻¹ * u⁻¹) * (u * a * u⁻¹ * a⁻¹)⁻¹ * (u * a⁻¹ * u⁻¹)⁻¹ := by
          group
        rw [e]
        exact hWn _ (W.inv_mem ha') _ (huX _ (X.inv_mem ha)) }
  have hidx : C.relIndex X ≤ 2 := by
    by_cases hall : ∀ x ∈ X, x ∈ C
    · have : C.relIndex X = 1 := Subgroup.relIndex_eq_one.2 hall
      omega
    · push Not at hall
      obtain ⟨a, haX, haC⟩ := hall
      have hdvd : C.relIndex X ∣ 2 := by
        rw [Subgroup.relIndex_dvd_two_iff]
        refine ⟨a, haX, fun b hbX => ?_⟩
        by_cases hbC : b ∈ C
        · right; exact hbC
        · left
          have ha' : u * a * u⁻¹ * a⁻¹ * z⁻¹ ∈ W :=
            (hz a haX).resolve_left fun h => haC ⟨haX, h⟩
          have hb' : u * b * u⁻¹ * b⁻¹ * z⁻¹ ∈ W :=
            (hz b hbX).resolve_left fun h => hbC ⟨hbX, h⟩
          refine ⟨X.mul_mem hbX haX, ?_⟩
          have hcomm1 : u * b * u⁻¹ * b⁻¹ ∈ X :=
            X.mul_mem (huX b hbX) (X.inv_mem hbX)
          have hcomm2 : u * a * u⁻¹ * a⁻¹ ∈ X :=
            X.mul_mem (huX a haX) (X.inv_mem haX)
          have hzX : z ∈ X := by
            have e : z = (u * a * u⁻¹ * a⁻¹ * z⁻¹)⁻¹ * (u * a * u⁻¹ * a⁻¹) := by group
            rw [e]
            exact X.mul_mem (X.inv_mem (hs.hWX ha')) hcomm2
          have hz2 : z * z ∈ W := hs.hsq z hzX
          have e : u * (b * a) * u⁻¹ * (b * a)⁻¹ =
              (u * b * u⁻¹ * b⁻¹) * (b * (u * a * u⁻¹ * a⁻¹) * b⁻¹) := by group
          have e2 : b * (u * a * u⁻¹ * a⁻¹) * b⁻¹ = u * a * u⁻¹ * a⁻¹ := by
            rw [hXc b hbX _ hcomm2]
            group
          rw [e, e2]
          have e3 : (u * b * u⁻¹ * b⁻¹) * (u * a * u⁻¹ * a⁻¹) =
              (u * b * u⁻¹ * b⁻¹ * z⁻¹) * (u * a * u⁻¹ * a⁻¹ * z⁻¹) * (z * z) := by
            have h1 := hXc _ hcomm2 z hzX
            have h2 := hXc _ (X.mul_mem hcomm2 (X.inv_mem hzX)) z hzX
            calc (u * b * u⁻¹ * b⁻¹) * (u * a * u⁻¹ * a⁻¹)
                = (u * b * u⁻¹ * b⁻¹ * z⁻¹) * (z * (u * a * u⁻¹ * a⁻¹)) := by group
              _ = (u * b * u⁻¹ * b⁻¹ * z⁻¹) * ((u * a * u⁻¹ * a⁻¹) * z) := by rw [h1]
              _ = (u * b * u⁻¹ * b⁻¹ * z⁻¹) * ((u * a * u⁻¹ * a⁻¹ * z⁻¹) * z * z) := by group
              _ = _ := by group
          rw [e3]
          exact W.mul_mem (W.mul_mem hb' ha') hz2
      exact Nat.le_of_dvd (by norm_num) hdvd
  exact hs.natural_of_hyp hirr hαs hαk huH huQ hu2 hidx fun x hx => hx.2

end SecHyp

theorem exists_chief_sec {H K W₀ X₀ : Subgroup G} (hKH : K ≤ H) (hperf : ⁅K, K⁆ = K)
    (hW₀X₀ : W₀ ≤ X₀)
    (hX₀c : ∀ a ∈ X₀, ∀ b ∈ X₀, a * b = b * a)
    (hHX₀ : H ≤ Subgroup.normalizer (X₀ : Set G)) (hHW₀ : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X₀, k * x * k⁻¹ * x⁻¹ ∉ W₀) :
    ∃ W₁ W₂ : Subgroup G, W₀ ≤ W₁ ∧ W₁ < W₂ ∧ W₂ ≤ X₀ ∧
      H ≤ Subgroup.normalizer (W₁ : Set G) ∧ H ≤ Subgroup.normalizer (W₂ : Set G) ∧
      (∀ W' : Subgroup G, W₁ ≤ W' → W' ≤ W₂ → H ≤ Subgroup.normalizer (W' : Set G) →
        W' = W₁ ∨ W' = W₂) ∧
      ∃ k ∈ K, ∃ x ∈ W₂, k * x * k⁻¹ * x⁻¹ ∉ W₁ := by
  classical
  obtain ⟨W₂, ⟨hW₀W₂, hW₂X₀, hHW₂, hKW₂⟩, hmin₂⟩ := WellFounded.has_min
    (wellFounded_lt (α := Subgroup G))
    {Y : Subgroup G | W₀ ≤ Y ∧ Y ≤ X₀ ∧ H ≤ Subgroup.normalizer (Y : Set G) ∧
      ∃ k ∈ K, ∃ x ∈ Y, k * x * k⁻¹ * x⁻¹ ∉ W₀} ⟨X₀, hW₀X₀, le_rfl, hHX₀, hKnt⟩
  have hW₀W₂' : W₀ < W₂ := by
    refine lt_of_le_of_ne hW₀W₂ fun h => ?_
    obtain ⟨k, hk, x, hx, hkx⟩ := hKW₂
    rw [← h] at hx
    apply hkx
    have h1 : k * x * k⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.mp (hHW₀ (hKH hk)) x).mp hx
    exact W₀.mul_mem h1 (W₀.inv_mem hx)
  obtain ⟨W₁, ⟨hW₀W₁, hW₁W₂, hHW₁⟩, hmax₁⟩ := WellFounded.has_min
    (wellFounded_gt (α := Subgroup G))
    {Y : Subgroup G | W₀ ≤ Y ∧ Y < W₂ ∧ H ≤ Subgroup.normalizer (Y : Set G)}
    ⟨W₀, le_rfl, hW₀W₂', hHW₀⟩
  refine ⟨W₁, W₂, hW₀W₁, hW₁W₂, hW₂X₀, hHW₁, hHW₂, fun W' hW₁W' hW'W₂ hHW' => ?_, ?_⟩
  · by_cases h : W' = W₂
    · exact Or.inr h
    · left
      by_contra hne
      exact hmax₁ W' ⟨hW₀W₁.trans hW₁W', lt_of_le_of_ne hW'W₂ h, hHW'⟩
        (lt_of_le_of_ne hW₁W' (Ne.symm hne))
  · by_contra hcon
    push Not at hcon
    have hK1 : ∀ k ∈ K, ∀ x ∈ W₁, k * x * k⁻¹ * x⁻¹ ∈ W₀ := by
      by_contra h
      push Not at h
      obtain ⟨k, hk, x, hx, hkx⟩ := h
      exact hmin₂ W₁ ⟨hW₀W₁, hW₁W₂.le.trans hW₂X₀, hHW₁, k, hk, x, hx, hkx⟩ hW₁W₂
    obtain ⟨k₀, hk₀, x₀, hx₀, hkx₀⟩ := hKW₂
    apply hkx₀
    have hX₁c : ∀ a ∈ W₁, ∀ b ∈ W₁, a * b = b * a := fun a ha b hb =>
      hX₀c a (hW₁W₂.le.trans hW₂X₀ ha) b (hW₁W₂.le.trans hW₂X₀ hb)
    let _ : CommGroup ↥W₁ := { (inferInstance : Group ↥W₁) with
      mul_comm := fun a b => Subtype.ext (hX₁c a a.2 b b.2) }
    have hW₁n : ∀ k ∈ K, ∀ y ∈ W₁, k * y * k⁻¹ ∈ W₁ := fun k hk y hy =>
      (Subgroup.mem_normalizer_iff.mp (hHW₁ (hKH hk)) y).mp hy
    have hmem : ∀ k : ↥K, (k : G) * x₀ * (k : G)⁻¹ * x₀⁻¹ ∈ W₁ := fun k => hcon k k.2 x₀ hx₀
    let δ : ↥K →* ↥W₁ ⧸ W₀.subgroupOf W₁ :=
      { toFun := fun k => QuotientGroup.mk ⟨_, hmem k⟩
        map_one' := by
          rw [← QuotientGroup.mk_one, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simp
        map_mul' := fun a b => by
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          set A : G := (a : G) * x₀ * (a : G)⁻¹ * x₀⁻¹ with hA
          set B : G := (b : G) * x₀ * (b : G)⁻¹ * x₀⁻¹ with hB
          have hAW : A ∈ W₁ := hmem a
          have hBW : B ∈ W₁ := hmem b
          have haB : (a : G) * B⁻¹ * (a : G)⁻¹ ∈ W₁ := hW₁n a a.2 _ (W₁.inv_mem hBW)
          have hcomm : A⁻¹ * ((a : G) * B⁻¹ * (a : G)⁻¹) = ((a : G) * B⁻¹ * (a : G)⁻¹) * A⁻¹ :=
            hX₁c _ (W₁.inv_mem hAW) _ haB
          have e : ((⟨((a * b : ↥K) : G) * x₀ * ((a * b : ↥K) : G)⁻¹ * x₀⁻¹, hmem (a * b)⟩ :
              ↥W₁)⁻¹ * (⟨A, hAW⟩ * ⟨B, hBW⟩) : ↥W₁) = ((a : G) * B⁻¹ * (a : G)⁻¹) * B⁻¹⁻¹ := by
            calc _ = A⁻¹ * ((a : G) * B⁻¹ * (a : G)⁻¹) * A * B := by
                  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hA, hB]
                  group
              _ = ((a : G) * B⁻¹ * (a : G)⁻¹) * A⁻¹ * A * B := by rw [hcomm]
              _ = _ := by group
          rw [e]
          exact hK1 a a.2 _ (W₁.inv_mem hBW) }
    have hperfK : commutator ↥K = ⊤ := (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
    have hδ : δ ⟨k₀, hk₀⟩ = 1 := by
      have hm : (⟨k₀, hk₀⟩ : ↥K) ∈ commutator ↥K := hperfK ▸ Subgroup.mem_top _
      exact Abelianization.commutator_subset_ker δ hm
    have h1 : (QuotientGroup.mk ⟨_, hmem ⟨k₀, hk₀⟩⟩ : ↥W₁ ⧸ W₀.subgroupOf W₁) = 1 := hδ
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1

end Setting4

end CFSG.Quasithin.H13.A6
