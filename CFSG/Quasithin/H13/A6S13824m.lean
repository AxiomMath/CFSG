module

public import CFSG.Quasithin.H13.A6S13824d

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem card_le_64_of_le
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hs.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hF : ¬ F ≤ pCoreOf 2 H) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H)
    (hle : (centralizerMod W X F).relIndex X ≤ (F ⊓ pCoreOf 2 H).relIndex F) :
    Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤ 2 ^ 6 := by
  obtain ⟨r, -, hrb, hcard⟩ := hs.card_le_index_pow7 hirr hαs hρk hρ1 hFH hF hFc hFs
  exact hcard.trans ((Nat.pow_le_pow_left ((hs.index_fixV_le hFH).trans hle) r).trans hrb)

theorem card_le_4096_of_le_sq
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hs.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hF : ¬ F ≤ pCoreOf 2 H) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H)
    (hle : (centralizerMod W X F).relIndex X ≤ (F ⊓ pCoreOf 2 H).relIndex F ^ 2) :
    Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤ 2 ^ 12 := by
  obtain ⟨r, -, hrb, hcard⟩ := hs.card_le_index_pow7 hirr hαs hρk hρ1 hFH hF hFc hFs
  refine hcard.trans ((Nat.pow_le_pow_left ((hs.index_fixV_le hFH).trans hle) r).trans ?_)
  rw [← pow_mul, mul_comm, pow_mul]
  calc ((F ⊓ pCoreOf 2 H).relIndex F ^ r) ^ 2 ≤ (2 ^ 6) ^ 2 := Nat.pow_le_pow_left hrb 2
    _ = 2 ^ 12 := by norm_num

omit [IsMulCommutative ↥X] in
theorem zpowers_comm_mem {u : G} (huH : u ∈ H) {x : G} (hux : u * x * u⁻¹ * x⁻¹ ∈ W) :
    ∀ f ∈ Subgroup.zpowers u, f * x * f⁻¹ * x⁻¹ ∈ W := by
  let St : Subgroup G :=
    { carrier := {f | f ∈ H ∧ f * x * f⁻¹ * x⁻¹ ∈ W}
      one_mem' := ⟨H.one_mem, by simp⟩
      mul_mem' := by
        rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
        refine ⟨H.mul_mem hf hg, ?_⟩
        have e : f * g * x * (f * g)⁻¹ * x⁻¹ =
            f * (g * x * g⁻¹ * x⁻¹) * f⁻¹ * (f * x * f⁻¹ * x⁻¹) := by group
        rw [e]
        exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hs.hHW hf) _).mp hg') hf'
      inv_mem' := by
        rintro f ⟨hf, hf'⟩
        refine ⟨H.inv_mem hf, ?_⟩
        have e : f⁻¹ * x * f⁻¹⁻¹ * x⁻¹ = f⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * f⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hs.hHW (H.inv_mem hf)) _).mp (W.inv_mem hf') }
  intro f hf
  exact ((Subgroup.zpowers_le (H := St)).2 ⟨huH, hux⟩ hf).2

theorem card_le_64_of_transv
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hs.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {u : G} (huH : u ∈ H)
    (huQ : u ∉ pCoreOf 2 H) (hu2 : u * u ∈ pCoreOf 2 H) {z : G}
    (hz : ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ W ∨ u * x * u⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤ 2 ^ 6 := by
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
  have hFH : Subgroup.zpowers u ≤ H := (Subgroup.zpowers_le).2 huH
  have hF : ¬ Subgroup.zpowers u ≤ pCoreOf 2 H := fun h => huQ (h (Subgroup.mem_zpowers u))
  refine hs.card_le_64_of_le hirr hαs hρk hρ1 hFH hF ?_ ?_ ?_
  · intro f hf f' hf'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf'
    have e : u ^ m * u ^ n * (u ^ m)⁻¹ * (u ^ n)⁻¹ = 1 := by group
    rw [e]
    exact (pCoreOf 2 H).one_mem
  · intro f hf
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    have e : u ^ m * u ^ m = (u * u) ^ m := by
      rw [← zpow_add, ← sq, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact (pCoreOf 2 H).zpow_mem hu2 m
  · have hrel : 2 ≤ (Subgroup.zpowers u ⊓ pCoreOf 2 H).relIndex (Subgroup.zpowers u) := by
      have h0 := relIndex_ne_zero' (Subgroup.zpowers u ⊓ pCoreOf 2 H) (Subgroup.zpowers u)
      have h1 : (Subgroup.zpowers u ⊓ pCoreOf 2 H).relIndex (Subgroup.zpowers u) ≠ 1 :=
        fun h => hF ((Subgroup.relIndex_eq_one.1 h).trans inf_le_right)
      omega
    refine le_trans ?_ (hidx.trans hrel)
    refine Subgroup.relIndex_le_of_le_left ?_ (relIndex_ne_zero' _ _)
    intro x hx
    refine ⟨hx.1, hs.hHW (hs.hXH hx.1), fun f hf => ?_⟩
    have h1 := W.inv_mem (hs.zpowers_comm_mem huH hx.2 f hf)
    have e : (f * x * f⁻¹ * x⁻¹)⁻¹ = x * f * x⁻¹ * f⁻¹ := by group
    rwa [e] at h1

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
