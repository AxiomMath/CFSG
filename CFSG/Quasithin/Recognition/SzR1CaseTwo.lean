module

public import CFSG.Quasithin.Recognition.SzR1Prep
public import CFSG.Quasithin.Recognition.SzR1Enum
public import CFSG.Quasithin.Recognition.SzR1Vert

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

theorem V_inf_centralizer_S :
    conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) = Zs := by
  have hcard : Nat.card ↥(conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G)) = 2 :=
    F112W.card_inf_centralizer_T C.amalgamHypV C.isNaturalS3
  have hle : Zs ≤ conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) :=
    le_inf (le_conjClosure Zs L2) C.h.Z_cent_S
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, C.h.card_Z])).symm

section Five

variable [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
theorem sq_mem_Zs {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {x : G} (hx : x ∈ vBeta K1 L2 S Zs) :
    x * x ∈ Zs := by
  have hG := C.gramRel hij
  have hclos : (⟨x, hx⟩ : ↥(vBeta K1 L2 S Zs)) ∈
      Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    rw [C.closure_wU hij]
    exact Subgroup.mem_top _
  obtain ⟨c, hc⟩ := hG.sq_mem hclos
  have : x * x = (C.cm i₀ j₀) ^ c := by
    have h1 := congrArg Subtype.val hc
    rw [Subgroup.coe_mul, Subgroup.coe_pow] at h1
    exact h1
  rw [this]
  exact Zs.pow_mem (C.cm_mem i₀ j₀) c

omit [DecidableEq Ω] in
theorem mem_Zs_of_mem_V_central (hc5 : Fintype.card Ω = 5) {x : G}
    (hxV : x ∈ conjClosure Zs L2) (hxc : ∀ t ∈ vBeta K1 L2 S Zs, x * t = t * x) : x ∈ Zs := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) C.D.pt
  rw [← C.Vf_pt] at hxV
  rcases C.Vf_eq hxV with h1 | h1
  · exact h1
  · exfalso
    have hc' : ((C.zf C.D.pt)⁻¹ * x)⁻¹ ∈ Zs := Zs.inv_mem h1
    have hcen : ((C.zf C.D.pt)⁻¹ * x)⁻¹ * C.zf j = C.zf j * ((C.zf C.D.pt)⁻¹ * x)⁻¹ :=
      (C.Zs_central (C.zf_mem_U j) hc').symm
    have hxj := hxc (C.zf j) (C.zf_mem_U j)
    have e : C.zf C.D.pt = x * ((C.zf C.D.pt)⁻¹ * x)⁻¹ := by group
    have hcomm : C.zf C.D.pt * C.zf j = C.zf j * C.zf C.D.pt := by
      calc C.zf C.D.pt * C.zf j = (x * ((C.zf C.D.pt)⁻¹ * x)⁻¹) * C.zf j := by rw [← e]
        _ = x * (((C.zf C.D.pt)⁻¹ * x)⁻¹ * C.zf j) := by rw [mul_assoc]
        _ = x * (C.zf j * ((C.zf C.D.pt)⁻¹ * x)⁻¹) := by rw [hcen]
        _ = (x * C.zf j) * ((C.zf C.D.pt)⁻¹ * x)⁻¹ := by rw [← mul_assoc]
        _ = (C.zf j * x) * ((C.zf C.D.pt)⁻¹ * x)⁻¹ := by rw [hxj]
        _ = C.zf j * (x * ((C.zf C.D.pt)⁻¹ * x)⁻¹) := by rw [mul_assoc]
        _ = C.zf j * C.zf C.D.pt := by rw [← e]
    apply C.cm_ne_one (i := j) (j := C.D.pt) hj
    calc C.cm j C.D.pt = (C.zf j * C.zf C.D.pt) * (C.zf j)⁻¹ * (C.zf C.D.pt)⁻¹ := rfl
      _ = (C.zf C.D.pt * C.zf j) * (C.zf j)⁻¹ * (C.zf C.D.pt)⁻¹ := by rw [hcomm]
      _ = 1 := by group


theorem false_of_noncentral (hc5 : Fintype.card Ω = 5) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    {a : G} (haP : a ∈ L2 ⊔ S) (haZ : a ∉ Subgroup.normalizer (Zs : Set G))
    {T : Subgroup G} (hTN : L2 ⊔ S ≤ Subgroup.normalizer (T : Set G))
    (hTW : T ≤ vBeta K1 L2 S Zs ⊓ conjSub a (vBeta K1 L2 S Zs))
    {u : G} (huT : u ∈ T) (hus : ∀ s ∈ S, u * s = s * u) (hu2 : u * u = 1) (huZ : u ∉ Zs)
    {a₁ a₂ : G} (ha₁ : a₁ ∈ L2 ⊔ S) (ha₂ : a₂ ∈ L2 ⊔ S)
    (hr : ∀ p ∈ L2 ⊔ S, p * (u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹)) * p⁻¹ =
      u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹)) : False := by
  have hodd : Odd (Fintype.card Ω) := ⟨2, by omega⟩
  have hyp := C.amalgamHypV
  have hVP : ∀ p ∈ L2 ⊔ S, conjSub p (conjClosure Zs L2) = conjClosure Zs L2 :=
    fun p hp => F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hp)
  have hVW : conjClosure Zs L2 ≤ vBeta K1 L2 S Zs := le_conjClosure (conjClosure Zs L2) (K1 ⊔ S)
  have hZV : Zs ≤ conjClosure Zs L2 := le_conjClosure Zs L2
  have hzpV : C.zf C.D.pt ∈ conjClosure Zs L2 := by
    rw [← C.Vf_pt]
    exact C.zf_mem C.D.pt
  have hZZ : Zs ⊓ conjSub a Zs = ⊥ :=
    Vert.inf_eq_bot_of_card_two C.h.card_Z ((Vert.card_conjSub a Zs).trans C.h.card_Z)
      (fun h => haZ (Vert.mem_normalizer_of_conjSub_eq h))
  have huW : u ∈ vBeta K1 L2 S Zs := (hTW huT).1
  have hxc : ∀ t ∈ vBeta K1 L2 S Zs, u * t = t * u := fun t ht => hus t (C.vBeta_le_S ht)
  have hTsq : ∀ t ∈ T, t * t = 1 := by
    intro t ht
    obtain ⟨htW, htA⟩ := hTW ht
    have h1 : t * t ∈ Zs := C.sq_mem_Zs hij htW
    have h2 : t * t ∈ conjSub a Zs := by
      have hat : a⁻¹ * t * a ∈ vBeta K1 L2 S Zs := mem_conjSub.mp htA
      have := C.sq_mem_Zs hij hat
      rw [mem_conjSub]
      have e : a⁻¹ * (t * t) * a = (a⁻¹ * t * a) * (a⁻¹ * t * a) := by group
      rw [e]
      exact this
    have h3 : t * t ∈ Zs ⊓ conjSub a Zs := ⟨h1, h2⟩
    rw [hZZ, Subgroup.mem_bot] at h3
    exact h3
  have hTcomm : ∀ t ∈ T, t * C.zf C.D.pt = C.zf C.D.pt * t := by
    intro t ht
    obtain ⟨htW, htA⟩ := hTW ht
    have hat : a⁻¹ * t * a ∈ vBeta K1 L2 S Zs := mem_conjSub.mp htA
    have hv : a⁻¹ * C.zf C.D.pt * a ∈ vBeta K1 L2 S Zs := by
      have h := mul_mem_conjSub (g := a⁻¹) hzpV
      rw [hVP a⁻¹ ((L2 ⊔ S).inv_mem haP), inv_inv] at h
      exact hVW h
    have h1 : t * C.zf C.D.pt * t⁻¹ * (C.zf C.D.pt)⁻¹ ∈ Zs := C.U_comm_mem htW (hVW hzpV)
    have h2 : t * C.zf C.D.pt * t⁻¹ * (C.zf C.D.pt)⁻¹ ∈ conjSub a Zs := by
      rw [mem_conjSub]
      have := C.U_comm_mem hat hv
      have e : a⁻¹ * (t * C.zf C.D.pt * t⁻¹ * (C.zf C.D.pt)⁻¹) * a =
          (a⁻¹ * t * a) * (a⁻¹ * C.zf C.D.pt * a) * (a⁻¹ * t * a)⁻¹ *
            (a⁻¹ * C.zf C.D.pt * a)⁻¹ := by group
      rw [e]
      exact this
    have h3 : t * C.zf C.D.pt * t⁻¹ * (C.zf C.D.pt)⁻¹ ∈ Zs ⊓ conjSub a Zs := ⟨h1, h2⟩
    rw [hZZ, Subgroup.mem_bot] at h3
    calc t * C.zf C.D.pt = (t * C.zf C.D.pt * t⁻¹ * (C.zf C.D.pt)⁻¹) * (C.zf C.D.pt * t) := by
          group
      _ = C.zf C.D.pt * t := by rw [h3, one_mul]
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  set Y : G := ((SzR1.gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) with hY
  obtain ⟨c, hc⟩ : ∃ c : ℕ, u = (C.cm i₀ j₀) ^ c * Y := by
    rcases C.center_dichotomy hij l₀ hl₀ hall huW hxc with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact absurd (by rw [hb]; exact Zs.pow_mem (C.cm_mem i₀ j₀) b) huZ
    · exact ⟨b, hb⟩
  have hYY : Y * Y = 1 := by
    have h1 := hG.gprod_univ_sq l₀ hl₀ hall
    rw [show Nat.choose (Fintype.card Ω) 2 = 5 + 5 by rw [hc5]; decide,
      hG.z_pow_add_self] at h1
    exact congrArg Subtype.val h1
  have hYc : ∀ g ∈ vBeta K1 L2 S Zs, g * Y = Y * g := by
    intro g hg
    have hYe : Y = ((C.cm i₀ j₀) ^ c)⁻¹ * u := by
      rw [hc]
      group
    have h1 : g * ((C.cm i₀ j₀) ^ c)⁻¹ = ((C.cm i₀ j₀) ^ c)⁻¹ * g :=
      C.Zs_central hg (Zs.inv_mem (Zs.pow_mem (C.cm_mem i₀ j₀) c))
    rw [hYe]
    calc g * (((C.cm i₀ j₀) ^ c)⁻¹ * u) = (g * ((C.cm i₀ j₀) ^ c)⁻¹) * u := by rw [mul_assoc]
      _ = (((C.cm i₀ j₀) ^ c)⁻¹ * g) * u := by rw [h1]
      _ = ((C.cm i₀ j₀) ^ c)⁻¹ * (g * u) := by rw [mul_assoc]
      _ = ((C.cm i₀ j₀) ^ c)⁻¹ * (u * g) := by rw [← hxc g hg]
      _ = (((C.cm i₀ j₀) ^ c)⁻¹ * u) * g := by rw [mul_assoc]
  have hVtor : ∀ t ∈ T, t ∈ conjClosure Zs L2 ∨ u * t ∈ conjClosure Zs L2 := by
    intro t ht
    have htW := (hTW ht).1
    have hclos : (⟨t, htW⟩ : ↥(vBeta K1 L2 S Zs)) ∈
        Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
      rw [C.closure_wU hij]
      exact Subgroup.mem_top _
    obtain ⟨i, j, k, hijk⟩ := hG.sq_eq_one_comm_mem hz hc5 C.D.pt l₀ hl₀ hall hclos
      (Subtype.ext (hTsq t ht)) (Subtype.ext (hTcomm t ht))
    have ht' : t = (C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j * Y ^ k := by
      have h1 : ((⟨t, htW⟩ : ↥(vBeta K1 L2 S Zs)) : G) =
          ((C.zU i₀ j₀ ^ i * C.wU C.D.pt ^ j * SzR1.gprod C.wU l₀ ^ k :
            ↥(vBeta K1 L2 S Zs)) : G) := congrArg Subtype.val hijk
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
        Subgroup.coe_pow] at h1
      exact h1
    have hgV : (C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j ∈ conjClosure Zs L2 :=
      (conjClosure Zs L2).mul_mem (hZV (Zs.pow_mem (C.cm_mem i₀ j₀) i))
        ((conjClosure Zs L2).pow_mem hzpV j)
    rcases Nat.even_or_odd' k with ⟨m, hm | hm⟩
    · left
      have hYk : Y ^ k = 1 := by rw [hm, pow_mul, pow_two, hYY, one_pow]
      rw [ht', hYk, mul_one]
      exact hgV
    · right
      have hYk : Y ^ k = Y := by
        rw [hm, pow_succ, pow_mul, pow_two, hYY, one_pow, one_mul]
      have hgW : (C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j ∈ vBeta K1 L2 S Zs := hVW hgV
      have hcomm := hYc _ hgW
      have : u * t = (C.cm i₀ j₀) ^ c * ((C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j) := by
        rw [hc, ht', hYk]
        calc (C.cm i₀ j₀) ^ c * Y * ((C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j * Y)
            = (C.cm i₀ j₀) ^ c * (Y * ((C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j)) * Y := by
              simp only [mul_assoc]
          _ = (C.cm i₀ j₀) ^ c * (((C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j) * Y) * Y := by
              rw [← hcomm]
          _ = (C.cm i₀ j₀) ^ c * ((C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j) * (Y * Y) := by
              simp only [mul_assoc]
          _ = (C.cm i₀ j₀) ^ c * ((C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j) := by
              rw [hYY, mul_one]
      rw [this]
      exact (conjClosure Zs L2).mul_mem (hZV (Zs.pow_mem (C.cm_mem i₀ j₀) c)) hgV
  have hconj : ∀ a' ∈ L2 ⊔ S, a' * u * a'⁻¹ ∈ T := fun a' ha' =>
    (Subgroup.mem_normalizer_iff.mp (hTN ha') u).mp huT
  have hnotV : ∀ a' ∈ L2 ⊔ S, u * (a' * u * a'⁻¹) ∈ conjClosure Zs L2 := by
    intro a' ha'
    rcases hVtor _ (hconj a' ha') with h1 | h1
    · exfalso
      apply huZ
      refine C.mem_Zs_of_mem_V_central hc5 ?_ hxc
      have h2 := mul_mem_conjSub (g := a'⁻¹) h1
      rw [hVP a'⁻¹ ((L2 ⊔ S).inv_mem ha'), inv_inv] at h2
      have e : a'⁻¹ * (a' * u * a'⁻¹) * a' = u := by group
      rwa [e] at h2
    · exact h1
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

theorem gprod_mem_Zs_of_central (hodd : Odd (Fintype.card Ω)) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    {b : G} (hb : b ∈ L2 ⊔ S) (hbZ : b ∉ Subgroup.normalizer (Zs : Set G)) {u : G}
    (huZ : u ∈ Zs) (hu1 : u ≠ 1) (hbu : b * u * b⁻¹ ∈ ⁅vBeta K1 L2 S Zs, S⁆) :
    ((SzR1.gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∈ Zs := by
  have hyp := C.amalgamHypV
  have huV : u ∈ conjClosure Zs L2 := le_conjClosure Zs L2 huZ
  have hy'V : b * u * b⁻¹ ∈ conjClosure Zs L2 :=
    (Subgroup.mem_normalizer_iff.mp (hyp.normalizes hb) u).mp huV
  have hy'Z : b * u * b⁻¹ ∉ Zs := by
    intro hy'
    apply hbZ
    have hsub : conjSub b Zs ≤ Zs := by
      intro x hx
      have hx' : b⁻¹ * x * b ∈ Zs := mem_conjSub.mp hx
      rw [C.Zs_eq_zpowers huZ hu1] at hx'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx'
      have : x = (b * u * b⁻¹) ^ n := by
        calc x = b * (b⁻¹ * x * b) * b⁻¹ := by group
          _ = b * u ^ n * b⁻¹ := by rw [← hn]
          _ = (b * u * b⁻¹) ^ n := (conj_zpow).symm
      rw [this]
      exact Subgroup.zpow_mem _ hy' n
    exact mem_normalizer_of_conjSub_eq'
      (Subgroup.eq_of_le_of_card_ge hsub (CosetGeom.card_conjSub b Zs).ge)
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  have hcomm : ⁅vBeta K1 L2 S Zs, S⁆ ≤ hG.evenSub.map (vBeta K1 L2 S Zs).subtype := by
    rw [Subgroup.commutator_le]
    intro w hw s hs
    obtain ⟨y, hy, hye⟩ := C.comm_S_vBeta_mem_evenSub hij hs hw
    refine ⟨y⁻¹, hG.evenSub.inv_mem hy, ?_⟩
    show ((y⁻¹ : ↥(vBeta K1 L2 S Zs)) : G) = ⁅w, s⁆
    rw [commutatorElement_def, Subgroup.coe_inv, hye]
    group
  obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp (hcomm hbu)
  have hee' : (e : G) = b * u * b⁻¹ := hee
  have hwpt : C.wU C.D.pt ∈ hG.evenSub := by
    have hpt : b * u * b⁻¹ ∈ C.D.Vf (conjClosure Zs L2) C.D.pt := by
      rw [C.Vf_pt]
      exact hy'V
    rcases C.Vf_eq hpt with h1 | h1
    · exact absurd h1 hy'Z
    · obtain ⟨k, hk⟩ := C.exists_pow_zU hij (Zs.inv_mem h1)
      have : C.wU C.D.pt = e * (C.zU i₀ j₀) ^ k := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        show C.zf C.D.pt = (e : G) * (C.cm i₀ j₀) ^ k
        rw [hee', ← hk]
        group
      rw [this]
      exact hG.evenSub.mul_mem he (hG.evenSub.pow_mem hG.z_mem_evenSub k)
  have hodd' : Odd l₀.length := by
    have hlen : l₀.length = Fintype.card Ω := by
      have : l₀.toFinset = Finset.univ := by
        ext i
        simp [hall i]
      rw [← List.toFinset_card_of_nodup hl₀, this, Finset.card_univ]
    rw [hlen]
    exact hodd
  obtain ⟨b', hb'⟩ := hG.gprod_mem_zpowers_of_w_mem_evenSub hz l₀ hl₀ hall hodd' hwpt
  rw [hb', Subgroup.coe_pow]
  exact Zs.pow_mem (C.cm_mem i₀ j₀) b'


end Five

end FamCtx

end SzR1

end CFSG.Quasithin
