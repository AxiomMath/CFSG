module

public import CFSG.Quasithin.H13.A6S13813j
public import CFSG.Quasithin.H13.A6S13813k
public import CFSG.Quasithin.H13.A6S13813l
public import CFSG.Quasithin.H13.A6S13813h

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section PSec

variable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
  {hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G)}
  {hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G)} {p : ℕ}
  {P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))}
  (hP : A6P.PData S.L1 T L H (actH hV₁ hIH)
    (((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) p P)
include hS hH hP

theorem false_of_p5 (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9)
    (hsol : Group.IsSolvable ↥H) (hmin : ∀ K ∈ S.Hz, K ≤ H → K = H) (hp5 : p = 5)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hcard : Nat.card P = p ^ 2)
    {z : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hz : z ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hzinv : ∀ x ∈ P, z * x * z⁻¹ = x⁻¹) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    {h : G} (hhH : h ∈ H) (hβ : conjSub h (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T))
    {t : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (htU : t ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htrk : rk (commV (Subgroup.zpowers t)) = 2)
    (hP1 : Nat.card (⁅P, Subgroup.zpowers t⁆ :
      Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))) = 5)
    (hP1rk : rk (commV ⁅P, Subgroup.zpowers t⁆) = 4) : False := by
  subst hp5
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  set φ := actH hV₁ hIH with hφ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hV : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), v ^ 2 = 1 :=
    fun v => Subtype.ext (hF1.isElemAbelian_tilde.2 v v.2)
  have hPX : P ≤ φ.range := hP.le_pCore.trans (pCoreOf_le 5 _)
  have hPn : ∀ x ∈ φ.range, ∀ y ∈ P, x * y * x⁻¹ ∈ P := hP.normal
  have hcard25 : Nat.card P = 25 := by rw [hcard]; norm_num
  have hUγH : F8.Uγ S.V3 H (g : G) ≤ H := hF.Uγ_le_H s
  have hVγH : F8.Uγ V H (g : G) ≤ H := hF.Vγ_le_H s
  have hUseq : autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure S.V3 H)) = ((F8.Uγ S.V3 H (g : G)).subgroupOf H).map φ :=
    autOn_tilde_eq_map_actH hV₁ hIH hUγH
  set Us := autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (g : G)))
    (tildeOf (fsuV1 T V) (conjClosure S.V3 H)) with hUs
  set Vs := ((F8.Uγ V H (g : G)).subgroupOf H).map φ with hVs
  have hUY : Us ≤ Vs := by
    rw [hUseq]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, Subgroup.mem_subgroupOf.2 (hF.Uγ_le_Vγ (Subgroup.mem_subgroupOf.1 hw)), rfl⟩
  have hYX : Vs ≤ φ.range := Subgroup.map_le_range _ _
  have hVab := hF.isElemAbelian_Vγ (g := g)
  have hYc : ∀ a ∈ Vs, ∀ b ∈ Vs, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have e : (a : G) * b = b * a := congrArg Subtype.val (hVab.1.is_comm.comm
      (⟨a, Subgroup.mem_subgroupOf.1 ha⟩ : ↥(F8.Uγ V H (g : G))) ⟨b, Subgroup.mem_subgroupOf.1 hb⟩)
    exact Subtype.ext e
  have hY2 : ∀ a ∈ Vs, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      have := hVab.2 (a : G) (Subgroup.mem_subgroupOf.1 ha)
      simpa [pow_two] using this)
    rw [this, map_one]
  have hfaithR : ∀ r ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ,
      (∀ x ∈ P, r * x * r⁻¹ = x) → r = 1 := fun r hr hc =>
    S.eq_one_of_cent_P hS hH hP hr fun x hx => by
      calc r * x = r * x * r⁻¹ * r := by group
        _ = x * r := by rw [hc x hx]
  have hYf : ∀ r ∈ Vs, (∀ y ∈ P, r * y * r⁻¹ = y) → r = 1 := by
    intro r hr hc
    set c := φ ⟨h, hhH⟩ with hc'
    have hcX : c ∈ φ.range := ⟨_, rfl⟩
    have hcr : c * r * c⁻¹ ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ := by
      obtain ⟨w, hw, rfl⟩ := hr
      refine ⟨⟨h, hhH⟩ * w * ⟨h, hhH⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, by
        rw [map_mul, map_mul, map_inv]⟩
      exact hβ (mul_mem_conjSub (Subgroup.mem_subgroupOf.1 hw))
    have h1 := hfaithR _ hcr fun x hx => by
      have hx' : c⁻¹ * x * c ∈ P := by
        have := hPn c⁻¹ (φ.range.inv_mem hcX) x hx
        simpa using this
      calc c * r * c⁻¹ * x * (c * r * c⁻¹)⁻¹ = c * (r * (c⁻¹ * x * c) * r⁻¹) * c⁻¹ := by group
        _ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [hc _ hx']
        _ = x := by group
    have : r = c⁻¹ * (c * r * c⁻¹) * c := by group
    rw [this, h1]
    group
  have hDγQ := hF.Dγ_eq_inf_pCoreOf s
  obtain ⟨u₀, hu₀U, hu₀D⟩ := IsConcreteLE.exists_of_lt hDγ
  have hu₀Q : u₀ ∉ pCoreOf 2 H := fun hq => hu₀D (by rw [hDγQ]; exact ⟨hu₀U, hq⟩)
  have hYfour : ∃ a ∈ Vs, ∃ b ∈ Vs, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
    by_cases key : ∀ v ∈ F8.Uγ V H (g : G), v ∈ pCoreOf 2 H ∨ u₀⁻¹ * v ∈ pCoreOf 2 H
    · exact (S.false_of_key h13314 h13315 h1356two h139 hS hH hsol hmin s hDγ hDH hle hhH hβ
        hu₀U hu₀Q key).elim
    push Not at key
    obtain ⟨v, hv, hvQ, hu₀vQ⟩ := key
    have hu₀V := hF.Uγ_le_Vγ hu₀U
    refine ⟨φ ⟨u₀, hVγH hu₀V⟩, ⟨_, Subgroup.mem_subgroupOf.2 hu₀V, rfl⟩, φ ⟨v, hVγH hv⟩,
      ⟨_, Subgroup.mem_subgroupOf.2 hv, rfl⟩, fun h1 => hu₀Q ((hker _).1 h1),
      fun h1 => hvQ ((hker _).1 h1), fun h1 => hu₀vQ ?_⟩
    have : φ (⟨u₀, hVγH hu₀V⟩⁻¹ * ⟨v, hVγH hv⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (hker _).1 this
  have htX : t ∈ φ.range := hYX (hUY htU)
  have hP₁P : ⁅P, Subgroup.zpowers t⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro y hy s' hs'
    rw [commutatorElement_def, show y * s' * y⁻¹ * s'⁻¹ = y * (s' * y⁻¹ * s'⁻¹) by group]
    exact P.mul_mem hy (hPn s' ((Subgroup.zpowers_le.2 htX) hs') _ (P.inv_mem hy))
  obtain ⟨x, hxL, hx⟩ : ∃ x ∈ ((S.L1 ⊔ T).subgroupOf H).map φ,
      conjBy x ⁅P, Subgroup.zpowers t⁆ ≠ ⁅P, Subgroup.zpowers t⁆ := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ y ∈ ((S.L1 ⊔ T).subgroupOf H).map φ, ∀ x ∈ ⁅P, Subgroup.zpowers t⁆,
        y * x * y⁻¹ ∈ ⁅P, Subgroup.zpowers t⁆ := by
      intro y hy x hx
      rw [← hcon y hy]
      exact mem_conjBy_of_mem hx
    have hne : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hP1
      norm_num at hP1
    have := S.eq_P_of_inv hP hz hzinv hP₁P hinv hne
    rw [this, hcard25] at hP1
    norm_num at hP1
  have hxX : x ∈ φ.range := Subgroup.map_le_range _ _ hxL
  have hAc := S.card_subM_A₁ hS hH (g := g)
  have hDidx : ∀ k : ℕ, Nat.card Us ≤ 2 ^ k →
      Nat.card ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) ≤ 2 ^ k *
        Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G))) := by
    intro k hk
    have h1 := S.card_tilde_le_mul hS hH (g := g)
    have h2 := S.mIdx_Uγ_le hS hH s hk
    exact h1.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (hle.trans h2)))
  have hDU : ∀ u ∈ Us, ∀ d ∈ subM (fsuV1 T V) (conjClosure S.V3 H)
      (F8.DH S.V3 (fsuV1 T V) H (g : G)),
      u d * d⁻¹ ∈ subM (fsuV1 T V) (conjClosure S.V3 H) (F8.A₁ (fsuV1 T V) (g : G)) := by
    intro u hu d hd
    rw [hUseq] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact S.actH_mem_A₁ hS hH x.2 (Subgroup.mem_subgroupOf.1 hx) hd
  have hcent : ∀ w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)),
      (∀ u ∈ Us, u w = w) → ∀ b ∈ Vs,
        b w * w⁻¹ ∈ subM (fsuV1 T V) (conjClosure S.V3 H) (F8.A₁ (fsuV1 T V) (g : G)) := by
    intro w hw hfixU b hb
    obtain ⟨v, hv, rfl⟩ := hb
    refine S.actH_mem_A₁_of_fix hS hH s h13315 h1356two hw (fun x hxH hx => hfixU _ ?_) v.2
      (Subgroup.mem_subgroupOf.1 hv)
    rw [hUseq]
    exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  exact A6Four.false_of_p5_module hV hPX hPn hcomm hcard25 hP.exp htU ht1 ht2 htrk hP1 hP1rk
    hxX hx hUY hYX hYc hY2 hYf hYfour hAc hDidx hDU hcent

end PSec

theorem false_of_four (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hsol : Group.IsSolvable ↥H)
    (hmin : ∀ K ∈ S.Hz, K ≤ H → K = H) {a b : G} (ha : a ∈ pCoreOf 2 (S.L1 ⊔ T))
    (hb : b ∈ pCoreOf 2 (S.L1 ⊔ T)) (haH : a ∈ H) (hbH : b ∈ H) (haa : a * a ∈ pCoreOf 2 H)
    (hbb : b * b ∈ pCoreOf 2 H) (habc : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H)
    (haQ : a ∉ pCoreOf 2 H) (hbQ : b ∉ pCoreOf 2 H) (habQ : a⁻¹ * b ∉ pCoreOf 2 H) : False := by
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  set φ := actH hV₁ hIH with hφ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  set R := ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ with hR
  set a' := φ ⟨a, haH⟩ with ha'
  set b' := φ ⟨b, hbH⟩ with hb'
  have ha'R : a' ∈ R := ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  have hb'R : b' ∈ R := ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have ha'2 : a' * a' = 1 := by
    rw [ha', ← map_mul]; exact (hker _).2 haa
  have hb'2 : b' * b' = 1 := by
    rw [hb', ← map_mul]; exact (hker _).2 hbb
  have hab' : a' * b' = b' * a' := by
    have h1 : φ (⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹ * ⟨b, hbH⟩⁻¹) = 1 := (hker _).2 habc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc a' * b' = (a' * b' * a'⁻¹ * b'⁻¹) * (b' * a') := by group
      _ = b' * a' := by rw [h1, one_mul]
  have ha'1 : a' ≠ 1 := fun h => haQ ((hker _).1 h)
  have hb'1 : b' ≠ 1 := fun h => hbQ ((hker _).1 h)
  have hne' : a' ≠ b' := by
    intro h
    apply habQ
    have : φ (⟨a, haH⟩⁻¹ * ⟨b, hbH⟩) = 1 := by rw [map_mul, map_inv, ← ha', ← hb', h,
      inv_mul_cancel]
    exact (hker _).1 this
  have hA2 : IsPGroup 2 ↥R := fun x => by
    obtain ⟨k, hk⟩ := S.pow_two_pow_eq_one_of_mem_R1 x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hA1 : R ≠ ⊥ := fun h => ha'1 (by rw [h] at ha'R; exact (Subgroup.mem_bot).1 ha'R)
  obtain ⟨p, P, hP⟩ := S.exists_P h139 hS hH hsol hmin hV₁ hIH le_rfl hA2 hA1
  obtain ⟨hcomm, hcard, z, hzR, hzinv⟩ :=
    S.four_shape hS hH hP ha'R hb'R ha'2 hb'2 hab' ha'1 hb'1 hne'
  have hodd : Odd p := hP.prime.odd_of_ne_two hP.ne_two
  have : Fact p.Prime := ⟨hP.prime⟩
  have hfaithR : ∀ r ∈ R, (∀ x ∈ P, r * x * r⁻¹ = x) → r = 1 := fun r hr hc =>
    S.eq_one_of_cent_P hS hH hP hr fun x hx => by
      calc r * x = r * x * r⁻¹ * r := by group
        _ = x * r := by rw [hc x hx]
  have hinv_mul : ∀ r₁ r₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)),
      (∀ x ∈ P, r₁ * x * r₁⁻¹ = x⁻¹) → (∀ x ∈ P, r₂ * x * r₂⁻¹ = x⁻¹) →
        ∀ x ∈ P, r₁ * r₂ * x * (r₁ * r₂)⁻¹ = x := by
    intro r₁ r₂ h₁ h₂ x hx
    rw [show r₁ * r₂ * x * (r₁ * r₂)⁻¹ = r₁ * (r₂ * x * r₂⁻¹) * r₁⁻¹ by group, h₂ x hx,
      show r₁ * x⁻¹ * r₁⁻¹ = (r₁ * x * r₁⁻¹)⁻¹ by group, h₁ x hx, inv_inv]
  obtain ⟨r, hrR, hr2, hrn, hrni⟩ : ∃ r ∈ R, r * r = 1 ∧ (¬ ∀ x ∈ P, r * x * r⁻¹ = x) ∧
      ¬ ∀ x ∈ P, r * x * r⁻¹ = x⁻¹ := by
    have hna : ¬ ∀ x ∈ P, a' * x * a'⁻¹ = x := fun h => ha'1 (hfaithR a' ha'R h)
    have hnb : ¬ ∀ x ∈ P, b' * x * b'⁻¹ = x := fun h => hb'1 (hfaithR b' hb'R h)
    by_cases hai : ∀ x ∈ P, a' * x * a'⁻¹ = x⁻¹
    · refine ⟨b', hb'R, hb'2, hnb, fun hbi => hne' ?_⟩
      have h1 := hfaithR _ (R.mul_mem ha'R hb'R) (hinv_mul a' b' hai hbi)
      calc a' = a' * (b' * b') := by rw [hb'2, mul_one]
        _ = (a' * b') * b' := by group
        _ = b' := by rw [h1, one_mul]
    · exact ⟨a', ha'R, ha'2, hna, hai⟩
  have hnt := S.no_transv_of_solvable hS hH hsol
  obtain ⟨γ, γ', g, s, hDγ, hDH, hpos, hle, hQ⟩ := S.case2_of_no_transv hF hnt
  obtain ⟨h, hhH, hβ⟩ := A6P.exists_conj_Vγ_le hF s
  set Us := autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (g : G)))
    (tildeOf (fsuV1 T V) (conjClosure S.V3 H)) with hUs
  have hUγH : F8.Uγ S.V3 H (g : G) ≤ H := hF.Uγ_le_H s
  have hUseq : Us = ((F8.Uγ S.V3 H (g : G)).subgroupOf H).map φ :=
    autOn_tilde_eq_map_actH hV₁ hIH hUγH
  have hXrange : ∀ u ∈ Us, u ∈ φ.range := fun u hu => by
    rw [hUseq] at hu
    exact Subgroup.map_le_range _ _ hu
  have hconjR : ∀ u ∈ Us, φ ⟨h, hhH⟩ * u * (φ ⟨h, hhH⟩)⁻¹ ∈ R := by
    intro u hu
    rw [hUseq] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    refine ⟨⟨h, hhH⟩ * w * ⟨h, hhH⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    have hwV : (w : G) ∈ F8.Uγ V H (g : G) := hF.Uγ_le_Vγ (Subgroup.mem_subgroupOf.1 hw)
    exact hβ (mul_mem_conjSub hwV)
  have hfaithU : ∀ u ∈ Us, (∀ x ∈ P, u * x = x * u) → u = 1 := by
    intro u hu hc
    set c := φ ⟨h, hhH⟩ with hc'
    have hcX : c ∈ φ.range := ⟨_, rfl⟩
    have h1 := hfaithR _ (hconjR u hu) fun x hx => by
      have hx' : c⁻¹ * x * c ∈ P := by
        have := hP.normal c⁻¹ (φ.range.inv_mem hcX) x hx
        simpa using this
      calc c * u * c⁻¹ * x * (c * u * c⁻¹)⁻¹ = c * (u * (c⁻¹ * x * c) * u⁻¹) * c⁻¹ := by group
        _ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [hc _ hx', mul_inv_cancel_right]
        _ = x := by group
    have : u = c⁻¹ * (c * u * c⁻¹) * c := by group
    rw [this, h1]
    group
  have hVsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), v ^ 2 = 1 :=
    fun v => Subtype.ext (hF1.isElemAbelian_tilde.2 v v.2)
  have hPp : IsPGroup p ↥P := fun x => ⟨1, Subtype.ext (by simpa using hP.exp x x.2)⟩
  have hUP : ∀ u ∈ Us, ∀ x ∈ P, u * x * u⁻¹ ∈ P := fun u hu x hx =>
    hP.normal u (hXrange u hu) x hx
  obtain ⟨h35, h5⟩ := A6Four.prime_cases hVsq hQ hP.ne_two hPp hP.exp hUP hfaithU
  rcases h35 with hp3 | hp5
  · exact S.false_of_p3 hS hH hP hp3 hcomm hcard hzR hzinv hrR hr2 hrn hrni
  · obtain ⟨t, htU, ht1, ht2, htrk, hP1card, -, hP1rk⟩ := h5 hp5
    exact S.false_of_p5 hS hH hP h13314 h13315 h1356two h139 hsol hmin hp5 hcomm hcard hzR hzinv
      s hDγ hDH hle hhH hβ htU ht1 ht2 htrk hP1card hP1rk

end Setting4

theorem case13813Four_of (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9) : Case13813Four := by
  intro G _ _ T L V S hS H hH hsol hmin a ha b hb haH hbH haa hbb habc haQ hbQ habQ
  exact S.false_of_four h13314 h13315 h1356two h139 hS hH hsol hmin ha hb haH hbH haa hbb habc
    haQ hbQ habQ

theorem lem13813_holds (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9) : Lem13813 :=
  lem13813_of h13314 h13315 h1356two h139 (case13813Four_of h13314 h13315 h1356two h139)

end CFSG.Quasithin.H13.A6
