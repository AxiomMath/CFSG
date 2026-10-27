module

public import CFSG.Quasithin.Recognition.SzR1CaseTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace SzR1

namespace FamCtx

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

include C

section Gen

variable [Fintype Ω]

theorem conj_mem_V (hΩ : 4 ≤ Fintype.card Ω) {a : G} (haP : a ∈ L2 ⊔ S)
    (haZ : a ∉ Subgroup.normalizer (Zs : Set G)) {T : Subgroup G}
    (hTN : L2 ⊔ S ≤ Subgroup.normalizer (T : Set G))
    (hTW : T ≤ vBeta K1 L2 S Zs ⊓ conjSub a (vBeta K1 L2 S Zs)) {u : G} (huT : u ∈ T)
    (hus : ∀ s ∈ S, u * s = s * u) :
    ∀ p ∈ L2 ⊔ S, p * u * p⁻¹ * u⁻¹ ∈ conjClosure Zs L2 := by
  classical
  have hyp := C.amalgamHypV
  have hS := C.isNaturalS3
  have hSP : S ≤ L2 ⊔ S := le_sup_right
  have hQS : pCoreOf 2 (L2 ⊔ S) ≤ S := C.pCore_le_S
  have hQ2 : (pCoreOf 2 (L2 ⊔ S)).relIndex S = 2 := relIndex_pCoreOf_T hyp hS
  have hS3 : S.relIndex (L2 ⊔ S) = 3 := F112J2.relIndex_L2S C.hR C.h.s3
  have hQN : L2 ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 (L2 ⊔ S)
  have hVP : ∀ p ∈ L2 ⊔ S, conjSub p (conjClosure Zs L2) = conjClosure Zs L2 :=
    fun p hp => F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hp)
  have hVn : ∀ p ∈ L2 ⊔ S, ∀ v ∈ conjClosure Zs L2, p * v * p⁻¹ ∈ conjClosure Zs L2 :=
    fun p hp v hv => (Subgroup.mem_normalizer_iff.mp (hyp.normalizes hp) v).mp hv
  have hZV : Zs ≤ conjClosure Zs L2 := le_conjClosure Zs L2
  have hWP : vBeta K1 L2 S Zs ≤ L2 ⊔ S := C.vBeta_le_S.trans hSP
  let H : Subgroup G :=
    { carrier := {x | x ∈ L2 ⊔ S ∧ ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ conjClosure Zs L2}
      one_mem' := ⟨(L2 ⊔ S).one_mem, fun t _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
        refine ⟨(L2 ⊔ S).mul_mem hxP hyP, fun t ht => ?_⟩
        have e : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
            (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact (conjClosure Zs L2).mul_mem (hx t ht) (hVn x hxP _ (hy t ht))
      inv_mem' := by
        rintro x ⟨hxP, hx⟩
        refine ⟨(L2 ⊔ S).inv_mem hxP, fun t ht => ?_⟩
        have e : t * x⁻¹ * t⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * x := by group
        rw [e]
        have := hVn x⁻¹ ((L2 ⊔ S).inv_mem hxP) _ ((conjClosure Zs L2).inv_mem (hx t ht))
        rwa [inv_inv] at this }
  have hmemH : ∀ {x : G}, x ∈ H ↔ x ∈ L2 ⊔ S ∧
      ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ conjClosure Zs L2 := Iff.rfl
  have hWH : vBeta K1 L2 S Zs ≤ H := fun w hw =>
    hmemH.mpr ⟨hWP hw, fun t ht => hZV (C.U_comm_mem (hTW ht).1 hw)⟩
  have hWaH : conjSub a (vBeta K1 L2 S Zs) ≤ H := by
    intro w' hw'
    refine hmemH.mpr ⟨Vert.conjSub_le_of_mem hWP haP hw', fun t ht => ?_⟩
    have hta : a⁻¹ * t * a ∈ vBeta K1 L2 S Zs := mem_conjSub.mp (hTW ht).2
    have hwa : a⁻¹ * w' * a ∈ vBeta K1 L2 S Zs := mem_conjSub.mp hw'
    have h1 := C.U_comm_mem hta hwa
    have h2 : t * w' * t⁻¹ * w'⁻¹ ∈ conjSub a (conjClosure Zs L2) := by
      have h3 : t * w' * t⁻¹ * w'⁻¹ ∈ conjSub a Zs := by
        rw [mem_conjSub]
        have e : a⁻¹ * (t * w' * t⁻¹ * w'⁻¹) * a =
            (a⁻¹ * t * a) * (a⁻¹ * w' * a) * (a⁻¹ * t * a)⁻¹ * (a⁻¹ * w' * a)⁻¹ := by group
        rw [e]
        exact h1
      exact conjSub_mono a hZV h3
    rwa [hVP a haP] at h2
  have hHn : ∀ p ∈ L2 ⊔ S, ∀ x ∈ H, p * x * p⁻¹ ∈ H := by
    rintro p hp x hx
    obtain ⟨hxP, hx'⟩ := hmemH.mp hx
    refine hmemH.mpr ⟨(L2 ⊔ S).mul_mem ((L2 ⊔ S).mul_mem hp hxP) ((L2 ⊔ S).inv_mem hp),
      fun t ht => ?_⟩
    have hT' : p⁻¹ * t * p ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (hTN ((L2 ⊔ S).inv_mem hp)) t).mp ht
      rwa [inv_inv] at this
    have e : t * (p * x * p⁻¹) * t⁻¹ * (p * x * p⁻¹)⁻¹ =
        p * ((p⁻¹ * t * p) * x * (p⁻¹ * t * p)⁻¹ * x⁻¹) * p⁻¹ := by group
    rw [e]
    exact hVn p hp _ (hx' _ hT')
  have hSH : S ≤ Subgroup.normalizer (H : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hHn s (hSP hs) x hx, fun hx => ?_⟩
    have := hHn s⁻¹ ((L2 ⊔ S).inv_mem (hSP hs)) _ hx
    simpa [mul_assoc] using this
  have hSN : S ≤ Subgroup.normalizer (Zs : Set G) :=
    (F112J2.S_le_centralizer_Z C.h).trans (Subgroup.centralizer_le_normalizer _)
  have haS : a ∉ S := fun h => haZ (hSN h)
  have hnS : ¬ conjSub a S ≤ S := by
    intro hle
    have heq : conjSub a S = S := Subgroup.eq_of_le_of_card_ge hle (Vert.card_conjSub a S).ge
    have haN : a ∈ Subgroup.normalizer (S : Set G) := Vert.mem_normalizer_of_conjSub_eq heq
    have hPN : L2 ⊔ S ≤ Subgroup.normalizer (S : Set G) := by
      rcases Vert.eq_or_eq_of_relIndex_prime Nat.prime_three hS3
          (H := Subgroup.normalizer (S : Set G) ⊓ (L2 ⊔ S)) (le_inf Subgroup.le_normalizer hSP)
          inf_le_right with h | h
      · exact absurd (h.le (Subgroup.mem_inf.mpr ⟨haN, haP⟩)) haS
      · exact h.ge.trans inf_le_left
    have hVS : conjClosure Zs L2 ≤ Subgroup.centralizer (S : Set G) := by
      refine conjClosure_le fun c hc z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hcP : c ∈ L2 ⊔ S := Subgroup.mem_sup_left hc
      have hs' : c⁻¹ * s * c ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp (hPN ((L2 ⊔ S).inv_mem hcP)) s).mp hs
        rwa [inv_inv] at this
      have hzs := Subgroup.mem_centralizer_iff.mp (F112J2.S_le_centralizer_Z C.h hs') z hz
      calc s * (c * z * c⁻¹) = c * ((c⁻¹ * s * c) * z) * c⁻¹ := by group
        _ = c * (z * (c⁻¹ * s * c)) * c⁻¹ := by rw [← hzs]
        _ = (c * z * c⁻¹) * s := by group
    have hSQ : S ≤ pCoreOf 2 (L2 ⊔ S) := by
      rw [C.pCore_eq]
      refine le_inf le_rfl fun s hs => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hVS hv) s hs).symm
    have h1 : (pCoreOf 2 (L2 ⊔ S)).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSQ
    rw [h1] at hQ2
    exact absurd hQ2 (by norm_num)
  have hPS : L2 ⊔ S = S ⊔ conjSub a S := by
    rcases Vert.eq_or_eq_of_relIndex_prime Nat.prime_three hS3 (H := S ⊔ conjSub a S)
        le_sup_left (sup_le hSP (Vert.conjSub_le_of_mem hSP haP)) with h | h
    · exact absurd (le_sup_right.trans h.le) hnS
    · exact h.symm
  have hS_eq : S = pCoreOf 2 (L2 ⊔ S) ⊔ vBeta K1 L2 S Zs :=
    (Vert.sup_eq_of_relIndex_two hQS C.vBeta_le_S hQ2 (C.not_vBeta_le_pCore hΩ)).symm
  have hconj : conjSub a S = pCoreOf 2 (L2 ⊔ S) ⊔ conjSub a (vBeta K1 L2 S Zs) := by
    have := congrArg (conjSub a) hS_eq
    rwa [conjSub_sup, Vert.conjSub_eq_of_mem_normalizer (hQN haP)] at this
  have hPle : L2 ⊔ S ≤ H ⊔ S := by
    rw [hPS]
    refine sup_le le_sup_right ?_
    rw [hconj]
    exact sup_le (hQS.trans le_sup_right) (hWaH.trans le_sup_left)
  intro p hp
  have hp' : p ∈ H ⊔ S := hPle hp
  obtain ⟨h, hh, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSH).mp hp'
  obtain ⟨-, hh'⟩ := hmemH.mp hh
  have h1 : u * h * u⁻¹ * h⁻¹ ∈ conjClosure Zs L2 := hh' u huT
  have hsu : s * u * s⁻¹ = u := by
    rw [← hus s hs]
    group
  have e : h * s * u * (h * s)⁻¹ * u⁻¹ = (u * h * u⁻¹ * h⁻¹)⁻¹ := by
    calc h * s * u * (h * s)⁻¹ * u⁻¹ = h * (s * u * s⁻¹) * h⁻¹ * u⁻¹ := by group
      _ = h * u * h⁻¹ * u⁻¹ := by rw [hsu]
      _ = (u * h * u⁻¹ * h⁻¹)⁻¹ := by group
  rw [e]
  exact (conjClosure Zs L2).inv_mem h1

theorem false_of_noncentral_gen (hodd : Odd (Fintype.card Ω)) (hΩ : 4 ≤ Fintype.card Ω)
    {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    {a : G} (haP : a ∈ L2 ⊔ S) (haZ : a ∉ Subgroup.normalizer (Zs : Set G))
    {T : Subgroup G} (hTN : L2 ⊔ S ≤ Subgroup.normalizer (T : Set G))
    (hTW : T ≤ vBeta K1 L2 S Zs ⊓ conjSub a (vBeta K1 L2 S Zs))
    {u : G} (huT : u ∈ T) (hus : ∀ s ∈ S, u * s = s * u) (hu2 : u * u = 1) (huZ : u ∉ Zs)
    {a₁ a₂ : G} (ha₁ : a₁ ∈ L2 ⊔ S) (ha₂ : a₂ ∈ L2 ⊔ S)
    (hr : ∀ p ∈ L2 ⊔ S, p * (u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹)) * p⁻¹ =
      u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹)) : False := by
  classical
  have hyp := C.amalgamHypV
  have hVW : conjClosure Zs L2 ≤ vBeta K1 L2 S Zs := le_conjClosure (conjClosure Zs L2) (K1 ⊔ S)
  have hZV : Zs ≤ conjClosure Zs L2 := le_conjClosure Zs L2
  have huW : u ∈ vBeta K1 L2 S Zs := (hTW huT).1
  have hxc : ∀ t ∈ vBeta K1 L2 S Zs, u * t = t * u := fun t ht => hus t (C.vBeta_le_S ht)
  have hconj : ∀ a' ∈ L2 ⊔ S, a' * u * a'⁻¹ ∈ T := fun a' ha' =>
    (Subgroup.mem_normalizer_iff.mp (hTN ha') u).mp huT
  have hcm := C.conj_mem_V hΩ haP haZ hTN hTW huT hus
  have hnotV : ∀ a' ∈ L2 ⊔ S, u * (a' * u * a'⁻¹) ∈ conjClosure Zs L2 := by
    intro a' ha'
    have hw : a' * u * a'⁻¹ * u⁻¹ ∈ conjClosure Zs L2 := hcm a' ha'
    have hc : u * (a' * u * a'⁻¹ * u⁻¹) = (a' * u * a'⁻¹ * u⁻¹) * u := hxc _ (hVW hw)
    have e : u * (a' * u * a'⁻¹) = a' * u * a'⁻¹ * u⁻¹ := by
      calc u * (a' * u * a'⁻¹) = (u * (a' * u * a'⁻¹ * u⁻¹)) * u := by group
        _ = ((a' * u * a'⁻¹ * u⁻¹) * u) * u := by rw [hc]
        _ = (a' * u * a'⁻¹ * u⁻¹) * (u * u) := by simp only [mul_assoc]
        _ = a' * u * a'⁻¹ * u⁻¹ := by rw [hu2, mul_one]
    rw [e]
    exact hw
  have hu₁W : a₁ * u * a₁⁻¹ ∈ vBeta K1 L2 S Zs := (hTW (hconj a₁ ha₁)).1
  have hu₂W : a₂ * u * a₂⁻¹ ∈ vBeta K1 L2 S Zs := (hTW (hconj a₂ ha₂)).1
  have hv₁ := hnotV a₁ ha₁
  have hv₂ := hnotV a₂ ha₂
  set u₁ := a₁ * u * a₁⁻¹ with hu₁
  set u₂ := a₂ * u * a₂⁻¹ with hu₂
  set v := (u * u₁) * (u * u₂) with hv
  have hvV : v ∈ conjClosure Zs L2 := (conjClosure Zs L2).mul_mem hv₁ hv₂
  have hcomm1 : u₁ * u = u * u₁ := (hxc u₁ hu₁W).symm
  have hrv : u * u₁ * u₂ = u * v := by
    calc u * u₁ * u₂ = (u * u) * (u * u₁) * u₂ := by rw [hu2, one_mul]
      _ = (u * u) * (u₁ * u) * u₂ := by rw [hcomm1]
      _ = u * v := by simp only [hv, mul_assoc]
  have huv : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
  have hvS : v ∈ Zs := by
    rw [← C.V_inf_centralizer_S]
    refine ⟨hvV, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have h1 : s * (u * u₁ * u₂) * s⁻¹ = u * u₁ * u₂ := hr s (Subgroup.mem_sup_right hs)
    have h2 : s * (u * u₁ * u₂) = (u * u₁ * u₂) * s := by
      calc s * (u * u₁ * u₂) = (s * (u * u₁ * u₂) * s⁻¹) * s := by group
        _ = (u * u₁ * u₂) * s := by rw [h1]
    rw [hrv] at h2
    calc s * v = s * (u * (u * v)) := by rw [huv]
      _ = (s * u) * (u * v) := by rw [mul_assoc]
      _ = (u * s) * (u * v) := by rw [hus s hs]
      _ = u * (s * (u * v)) := by rw [mul_assoc]
      _ = u * ((u * v) * s) := by rw [h2]
      _ = (u * (u * v)) * s := (mul_assoc _ _ _).symm
      _ = v * s := by rw [huv]
  have hK : ∀ k ∈ K1, k * u = u * k := C.K1_centralizes_center hodd hij l₀ hl₀ hall huW hxc
  have hvK : ∀ k ∈ K1, k * v = v * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) v hvS).symm
  set r := u * u₁ * u₂ with hr_def
  have hrK : ∀ k ∈ K1, r * k = k * r := by
    intro k hk
    rw [hrv]
    calc u * v * k = u * (v * k) := by rw [mul_assoc]
      _ = u * (k * v) := by rw [hvK k hk]
      _ = (u * k) * v := by rw [← mul_assoc]
      _ = (k * u) * v := by rw [hK k hk]
      _ = k * (u * v) := by rw [mul_assoc]
  have hrP : ∀ p ∈ L2 ⊔ S, r * p = p * r := by
    intro p hp
    have h1 : p * r * p⁻¹ = r := hr p hp
    calc r * p = (p * r * p⁻¹) * p := by rw [h1]
      _ = p * r := by group
  have hrW : r ∈ vBeta K1 L2 S Zs := by
    rw [hrv]
    exact (vBeta K1 L2 S Zs).mul_mem huW (F112J2.Zs_le_vBeta K1 L2 S Zs hvS)
  have hr1 : r ≠ 1 := by
    intro h1
    rw [hrv] at h1
    apply huZ
    have : u = v⁻¹ := by
      calc u = (u * v) * v⁻¹ := by group
        _ = v⁻¹ := by rw [h1, one_mul]
    rw [this]
    exact Zs.inv_mem hvS
  have hrr : r * r = 1 := by
    have hvv : v * v = 1 := C.Zs_sq hvS
    have hcv : u * v = v * u := hxc v (F112J2.Zs_le_vBeta K1 L2 S Zs hvS)
    rw [hrv]
    calc u * v * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
      _ = u * (u * v) * v := by rw [← hcv]
      _ = (u * u) * (v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [hu2, hvv, one_mul]
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hrr) hr1
  have hp2 : IsPGroup 2 (Subgroup.zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hG₀ : K1 ⊔ L2 ⊔ S ≤ Subgroup.centralizer ({r} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hrK k hk).symm
    · exact fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr
        (hrP p (Subgroup.mem_sup_left hp)).symm
    · exact fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
        (hrP s (Subgroup.mem_sup_right hs)).symm
  have hrG₀ : r ∈ K1 ⊔ L2 ⊔ S :=
    (le_sup_right : S ≤ K1 ⊔ L2 ⊔ S) (C.vBeta_le_S hrW)
  have hle : Subgroup.zpowers r ≤ K1 ⊔ L2 ⊔ S := Subgroup.zpowers_le.mpr hrG₀
  have hnorm : K1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
    intro g hg
    have hgc : g ∈ Subgroup.centralizer ({r} : Set G) := hG₀ hg
    have hcr : r * g = g * r := (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
    have hgcen : g ∈ Subgroup.centralizer (Subgroup.zpowers r : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute r g from hcr) n).eq
    exact Subgroup.centralizer_le_normalizer _ hgcen
  have hcore := le_pCoreOf_of_le_normalizer 2 hle hnorm hp2
  rw [C.h.hyp.o2] at hcore
  exact hr1 (Subgroup.mem_bot.mp (hcore (Subgroup.mem_zpowers r)))

end Gen

end FamCtx

end SzR1

end CFSG.Quasithin
