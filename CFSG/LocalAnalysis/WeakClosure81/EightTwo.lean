module

public import CFSG.LocalAnalysis.WeakClosure81.EightOne
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.CGT.Timmesfeld75.L2Real

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_conj_of_le_normalizer {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G}
    (h : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hab := CFSG.RankThree.GF2n.Tim77.tim77_2_3 hV hTI h
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hvsup : v ∈ V ⊔ conjSubgroup V g := Subgroup.mem_sup_left hv
    have hxsup : x ∈ V ⊔ conjSubgroup V g := Subgroup.mem_sup_right hx
    have hc : v * x = x * v :=
      congrArg Subtype.val (hab.1.is_comm.comm ⟨v, hvsup⟩ ⟨x, hxsup⟩)
    have hcalc : v * x * v⁻¹ = x := by
      calc v * x * v⁻¹ = x * v * v⁻¹ := by rw [hc]
        _ = x := by group
    rwa [hcalc]
  · intro hx
    have hvsup : v⁻¹ ∈ V ⊔ conjSubgroup V g := Subgroup.mem_sup_left (V.inv_mem hv)
    have hxsup : v * x * v⁻¹ ∈ V ⊔ conjSubgroup V g := Subgroup.mem_sup_right hx
    have hc : v⁻¹ * (v * x * v⁻¹) = (v * x * v⁻¹) * v⁻¹ :=
      congrArg Subtype.val (hab.1.is_comm.comm ⟨v⁻¹, hvsup⟩ ⟨v * x * v⁻¹, hxsup⟩)
    have hcalc : x = v * x * v⁻¹ := by
      calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
        _ = (v * x * v⁻¹) * v⁻¹ * v := by rw [hc]
        _ = v * x * v⁻¹ := by group
    rwa [hcalc]

theorem le_normalizer_conj_iff {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} :
    conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) ↔
      V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  constructor
  · exact le_normalizer_conj_of_le_normalizer hV hTI
  · intro h
    have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup' hV g
    have hTIg : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V g) := isTI_conj hTI g
    have h' : conjSubgroup (conjSubgroup V g) g⁻¹ ≤
        Subgroup.normalizer (conjSubgroup V g : Set G) := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      exact h
    have hres := le_normalizer_conj_of_le_normalizer hVg hTIg h'
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at hres

theorem commute_of_isPGroup_sup {V W W' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V)
    (hW : ∃ a : G, W = conjSubgroup V a) (hW' : ∃ b : G, W' = conjSubgroup V b)
    (hN : W ⊓ Subgroup.normalizer (W' : Set G) ≠ ⊥) (hP : IsPGroup 2 ↥(W ⊔ W')) :
    ∀ u ∈ W, ∀ v ∈ W', u * v = v * u := by
  obtain ⟨a, ha⟩ := hW
  obtain ⟨b, hb⟩ := hW'
  subst ha
  subst hb
  set g : G := a⁻¹ * b with hgdef
  have hW2 : IsElemAbelian 2 (conjSubgroup V a) := isElemAbelian_conjSubgroup' hV a
  have hTIW : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V a) := isTI_conj hTI a
  have hconj : conjSubgroup (conjSubgroup V a) g = conjSubgroup V b := by
    rw [hgdef, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hiff : conjSubgroup V b ≤ Subgroup.normalizer (conjSubgroup V a : Set G) ↔
      conjSubgroup V a ≤ Subgroup.normalizer (conjSubgroup V b : Set G) := by
    rw [← hconj]
    exact le_normalizer_conj_iff hW2 hTIW
  by_cases hWle : conjSubgroup V a ≤ Subgroup.normalizer (conjSubgroup V b : Set G)
  · have hW'le : conjSubgroup V b ≤ Subgroup.normalizer (conjSubgroup V a : Set G) :=
      hiff.mpr hWle
    intro u hu v hv
    have hcW' : u * v * u⁻¹ ∈ conjSubgroup V b :=
      (Subgroup.mem_normalizer_iff.mp (hWle hu) v).mp hv
    have hcW : u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V a := by
      have h1 : v * u⁻¹ * v⁻¹ ∈ conjSubgroup V a :=
        (Subgroup.mem_normalizer_iff.mp (hW'le hv) u⁻¹).mp ((conjSubgroup V a).inv_mem hu)
      have heq : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
      rw [heq]
      exact (conjSubgroup V a).mul_mem hu h1
    have hcW'2 : u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V b :=
      (conjSubgroup V b).mul_mem hcW' ((conjSubgroup V b).inv_mem hv)
    rcases inf_conjSubgroup_eq_bot_or_eq (V := conjSubgroup V a) hTIW 1 g with hb | he
    · rw [conjSubgroup_one] at hb
      have hmem : u * v * u⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hb, hconj]
        exact ⟨hcW, hcW'2⟩
      have h1 : u * v * u⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp hmem
      have h1' : (u * v) * (v * u)⁻¹ = 1 := by simpa [mul_inv_rev, mul_assoc] using h1
      exact mul_inv_eq_one.mp h1'
    · rw [conjSubgroup_one] at he
      exact CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hW2 hu (by rw [he, hconj]; exact hv)
  · have hW'le : ¬ conjSubgroup V b ≤ Subgroup.normalizer (conjSubgroup V a : Set G) :=
      fun h => hWle (hiff.mp h)
    have hLproper : conjSubgroup V a ⊓ Subgroup.normalizer (conjSubgroup V b : Set G) <
        conjSubgroup V a :=
      lt_of_le_of_ne inf_le_left fun h => hWle ((le_of_eq h.symm).trans inf_le_right)
    obtain ⟨v, hvA, hvL⟩ := SetLike.exists_of_lt hLproper
    have hLbproper : conjSubgroup V b ⊓ Subgroup.normalizer (conjSubgroup V a : Set G) <
        conjSubgroup V b :=
      lt_of_le_of_ne inf_le_left fun h => hW'le ((le_of_eq h.symm).trans inf_le_right)
    obtain ⟨x, hxB', hxLb⟩ := SetLike.exists_of_lt hLbproper
    have hg : conjSubgroup (conjSubgroup V a) g ≠ conjSubgroup V a := by
      intro heq
      apply hWle
      rw [← hconj, heq]
      exact Subgroup.le_normalizer
    have hU : nVSub (conjSubgroup V a) g ≠ ⊥ := by simpa [nVSub, hconj] using hN
    have hvU : v ∉ nVSub (conjSubgroup V a) g := by simpa [nVSub, hconj] using hvL
    have hxB : x ∉ bSub (conjSubgroup V a) g := by simpa [bSub, hconj] using hxLb
    exact absurd (hconj ▸ hP)
      (not_isPGroup_sup_of_odd hW2 hTIW hg hU hvA hvU (hconj ▸ hxB') hxB)

theorem conjSubgroup_le_conjClosure (Z H : Subgroup G) {h : G} (hh : h ∈ H) :
    conjSubgroup Z h ≤ conjClosure Z H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h := mem_conjClosure (H.inv_mem hh) hx
  simpa [mul_assoc] using h

theorem conjSubgroup_le_of_le {A H : Subgroup G} (hAH : A ≤ H) {h : G} (hh : h ∈ H) :
    conjSubgroup A h ≤ H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hx' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
  rw [hx']
  exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hAH hx)) hh

theorem eight_two {V H T U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hVne : V ≠ ⊥) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hUconj : ∃ g : G, U = conjSubgroup V g) (hUH : U ≤ H)
    (hCU : U ⊓ Subgroup.centralizer (eSub V H T : Set G) ≠ ⊥) :
    (∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ conjSubgroup V h, u * v = v * u) ∨
      (¬ IsCalH0 V H ∧ ∃ h ∈ H, U = conjSubgroup V h) := by
  have hCVne : V ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot hV hVne hH hT
  obtain ⟨u, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCU
  have huU : (u : G) ∈ U := u.2.1
  have huCE : (u : G) ∈ Subgroup.centralizer (eSub V H T : Set G) := u.2.2
  have hu1 : (u : G) ≠ 1 := fun hh => hu1' (Subtype.ext hh)
  have hstep : ∀ h ∈ H, U ⊓ Subgroup.normalizer (conjSubgroup V h : Set G) ≠ ⊥ := by
    intro h hh
    obtain ⟨c, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCVne
    have hcV : (c : G) ∈ V := c.2.1
    have hc1 : (c : G) ≠ 1 := fun hh => hc1' (Subtype.ext hh)
    have hzmem : h⁻¹ * (c : G) * h ∈
        conjSubgroup (V ⊓ Subgroup.centralizer (T : Set G)) h := by
      rw [mem_conjSubgroup_iff]
      have hce : h * (h⁻¹ * (c : G) * h) * h⁻¹ = (c : G) := by group
      rw [hce]
      exact c.2
    have hzE : h⁻¹ * (c : G) * h ∈ eSub V H T := by
      rw [eSub]
      exact conjSubgroup_le_conjClosure _ _ hh hzmem
    have hzV : h⁻¹ * (c : G) * h ∈ conjSubgroup V h := by
      rw [mem_conjSubgroup_iff]
      have hce : h * (h⁻¹ * (c : G) * h) * h⁻¹ = (c : G) := by group
      rw [hce]
      exact hcV
    have hz1 : h⁻¹ * (c : G) * h ≠ 1 := by
      intro hz
      apply hc1
      have := congrArg (fun t => h * t * h⁻¹) hz
      simpa [mul_assoc] using this
    have huz : h⁻¹ * (c : G) * h * (u : G) = (u : G) * (h⁻¹ * (c : G) * h) :=
      Subgroup.mem_centralizer_iff.mp huCE _ hzE
    have huN : (u : G) ∈ Subgroup.normalizer (conjSubgroup V h : Set G) :=
      centralizer_le_normalizer_conj hTI h hzV hz1
        (Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact huz)
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨(u : G), huU, huN⟩, fun hh => hu1 (congrArg Subtype.val hh)⟩
  by_cases hUH' : ∃ h ∈ H, U = conjSubgroup V h
  · by_cases hH0 : IsCalH0 V H
    · left
      intro h hh u hu v hv
      have hO2T : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
      have hVO2 : conjSubgroup V h ≤ pCoreOf 2 H := by
        have hhN : h ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hh
        calc conjSubgroup V h ≤ conjSubgroup (pCoreOf 2 H) h := Subgroup.map_mono hH0.2
          _ = pCoreOf 2 H := (conjSubgroup_eq_iff_mem_normalizer).mpr hhN
      have hUO2 : U ≤ pCoreOf 2 H := by
        obtain ⟨h0, hh0, rfl⟩ := hUH'
        have hh0N : h0 ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hh0
        calc conjSubgroup V h0 ≤ conjSubgroup (pCoreOf 2 H) h0 := Subgroup.map_mono hH0.2
          _ = pCoreOf 2 H := (conjSubgroup_eq_iff_mem_normalizer).mpr hh0N
      have hP : IsPGroup 2 ↥(U ⊔ conjSubgroup V h) :=
        hT.isPGroup.to_le (sup_le (hUO2.trans hO2T) (hVO2.trans hO2T))
      exact commute_of_isPGroup_sup hV hTI hUconj ⟨h, rfl⟩ (hstep h hh) hP u hu v hv
    · right
      exact ⟨hH0, hUH'⟩
  · left
    intro h hh u hu v hv
    have hyH : ∀ y ∈ U ⊔ conjSubgroup V h, y ∈ H := by
      refine fun y hy => (sup_le hUH (conjSubgroup_le_of_le hH.1 hh)) hy
    rcases two_conj_eq_or_comm hV hTI hUconj ⟨h, rfl⟩ (hstep h hh) with hcomm | ⟨y, hyX, hyeq⟩
    · exact hcomm u hu v hv
    · exact absurd ⟨h * y⁻¹, H.mul_mem hh (H.inv_mem (hyH y hyX)), by
        calc U = conjSubgroup (conjSubgroup U y) y⁻¹ := by
              rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
          _ = conjSubgroup (conjSubgroup V h) y⁻¹ := by rw [← hyeq]
          _ = conjSubgroup V (h * y⁻¹) := by rw [conjSubgroup_conjSubgroup]⟩ hUH'

theorem eq_one_of_odd_orderOf_of_mem_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G}
    (hx : x ∈ Q) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := CFSG.CGT.Timmesfeld75.exists_orderOf_eq_two_pow_of_mem hQ hx
  have hk' : orderOf x ∣ 2 ^ k := by rw [hk]
  have h1 : orderOf x = 1 := ((Nat.coprime_two_right.2 hodd).pow_right k).eq_one_of_dvd hk'
  exact orderOf_eq_one_iff.mp h1

theorem commute_of_le_normalizer_of_le_normalizer {V W W' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : CFSG.CGT.Timmesfeld75.IsTI V)
    (hW : ∃ a : G, W = conjSubgroup V a) (hW' : ∃ b : G, W' = conjSubgroup V b)
    (hle : W ≤ Subgroup.normalizer (W' : Set G))
    (hle' : W' ≤ Subgroup.normalizer (W : Set G)) :
    ∀ u ∈ W, ∀ v ∈ W', u * v = v * u := by
  obtain ⟨a, rfl⟩ := hW
  obtain ⟨b, rfl⟩ := hW'
  intro u hu v hv
  have hcW' : u * v * u⁻¹ ∈ conjSubgroup V b :=
    (Subgroup.mem_normalizer_iff.mp (hle hu) v).mp hv
  have hcW : u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V a := by
    have h1 : v * u⁻¹ * v⁻¹ ∈ conjSubgroup V a :=
      (Subgroup.mem_normalizer_iff.mp (hle' hv) u⁻¹).mp ((conjSubgroup V a).inv_mem hu)
    have heq : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
    rw [heq]
    exact (conjSubgroup V a).mul_mem hu h1
  have hcW'2 : u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V b :=
    (conjSubgroup V b).mul_mem hcW' ((conjSubgroup V b).inv_mem hv)
  rcases inf_conjSubgroup_eq_bot_or_eq (V := V) hTI a b with hb | he
  · have hmem : u * v * u⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hb]
      exact ⟨hcW, hcW'2⟩
    have h1 : u * v * u⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have h1' : (u * v) * (v * u)⁻¹ = 1 := by simpa [mul_inv_rev, mul_assoc] using h1
    exact mul_inv_eq_one.mp h1'
  · exact CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm (isElemAbelian_conjSubgroup' hV a) hu
      (he ▸ hv)

theorem conjSubgroup_le_pCoreOf_of_isCalH0 {V H : Subgroup G} (hH0 : IsCalH0 V H) {h : G}
    (hh : h ∈ H) : conjSubgroup V h ≤ pCoreOf 2 H := by
  have hhN : h ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hh
  calc conjSubgroup V h ≤ conjSubgroup (pCoreOf 2 H) h := Subgroup.map_mono hH0.2
    _ = pCoreOf 2 H := (conjSubgroup_eq_iff_mem_normalizer).mpr hhN

theorem mem_normalizer_conj_of_mem_centralizer {V H T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hVne : V ≠ ⊥) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) {u : G}
    (huCE : u ∈ Subgroup.centralizer (eSub V H T : Set G)) :
    ∀ h ∈ H, u ∈ Subgroup.normalizer (conjSubgroup V h : Set G) := by
  have hCVne : V ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot hV hVne hH hT
  intro h hh
  obtain ⟨c, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCVne
  have hcV : (c : G) ∈ V := c.2.1
  have hc1 : (c : G) ≠ 1 := fun hh' => hc1' (Subtype.ext hh')
  have hzmem : h⁻¹ * (c : G) * h ∈
      conjSubgroup (V ⊓ Subgroup.centralizer (T : Set G)) h := by
    rw [mem_conjSubgroup_iff]
    have hce : h * (h⁻¹ * (c : G) * h) * h⁻¹ = (c : G) := by group
    rw [hce]
    exact c.2
  have hzE : h⁻¹ * (c : G) * h ∈ eSub V H T := by
    rw [eSub]
    exact conjSubgroup_le_conjClosure _ _ hh hzmem
  have hzV : h⁻¹ * (c : G) * h ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    have hce : h * (h⁻¹ * (c : G) * h) * h⁻¹ = (c : G) := by group
    rw [hce]
    exact hcV
  have hz1 : h⁻¹ * (c : G) * h ≠ 1 := by
    intro hz
    apply hc1
    have h := congrArg (fun t => h * t * h⁻¹) hz
    simpa [mul_assoc] using h
  have huz : h⁻¹ * (c : G) * h * u = u * (h⁻¹ * (c : G) * h) :=
    Subgroup.mem_centralizer_iff.mp huCE _ hzE
  exact centralizer_le_normalizer_conj hTI h hzV hz1
    (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact huz)

theorem eight_four_one {V H T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hVne : V ≠ ⊥) (hH0 : IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (g : G) :
    (((conjSubgroup V g ⊓ H) ≤ Subgroup.centralizer (eSub V H T : Set G)) ∧
      ∀ h ∈ H, conjSubgroup (conjSubgroup V g ⊓ H) h ≤
        Subgroup.normalizer (V : Set G)) ∨
    (((conjSubgroup V g ⊓ H) ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥) ∧
      ∀ u ∈ conjSubgroup V g ⊓ H, u ≠ 1 →
        eSub V H T ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ H) : Set G) =
        eSub V H T ⊓ Subgroup.centralizer ({u} : Set G)) := by
  let W : Subgroup G := conjSubgroup V g
  let U : Subgroup G := W ⊓ H
  let Z : Subgroup G := V ⊓ Subgroup.centralizer (T : Set G)
  let E : Subgroup G := eSub V H T
  have hH : IsCalH V H := hH0.1
  have hUH : U ≤ H := inf_le_right
  have hUW : U ≤ W := inf_le_left
  have hEH : E ≤ H := (eSub_le_pCoreOf hV hH hT).trans (CFSG.openPCoreOf_le 2 H)
  by_cases hCU : U ⊓ Subgroup.centralizer (E : Set G) = ⊥
  · right
    refine ⟨hCU, ?_⟩
    intro u hu hu1
    have hEW : E ⊓ W = ⊥ := by
      have hEeq : E ⊓ W = E ⊓ U := by
        apply le_antisymm
        · intro x hx
          obtain ⟨hxE, hxW⟩ := Subgroup.mem_inf.mp hx
          exact Subgroup.mem_inf.mpr ⟨hxE, ⟨hxW, hEH hxE⟩⟩
        · intro x hx
          obtain ⟨hxE, hxU⟩ := Subgroup.mem_inf.mp hx
          exact Subgroup.mem_inf.mpr ⟨hxE, hUW hxU⟩
      rw [hEeq]
      have hEab : IsElemAbelian 2 E := eSub_isElemAbelian hV hH hT
      have hle : E ⊓ U ≤ U ⊓ Subgroup.centralizer (E : Set G) := by
        intro x hx
        obtain ⟨hxE, hxU⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hxE⟩ ⟨y, hy⟩)).symm⟩
      rw [hCU] at hle
      exact le_bot_iff.mp hle
    have hUn : U ≤ Subgroup.normalizer (E : Set G) :=
      hUH.trans (le_normalizer_conjClosure Z H)
    exact eight_one (V := W) (U := U) (E := E) (isTI_conj hTI g) hUW hUn hEW hu hu1
  · left
    obtain ⟨u, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCU
    have huU : (u : G) ∈ U := u.2.1
    have huCE : (u : G) ∈ Subgroup.centralizer (E : Set G) := u.2.2
    have hu1 : (u : G) ≠ 1 := fun hh' => hu1' (Subtype.ext hh')
    have huW : (u : G) ∈ W := hUW huU
    have huN : ∀ h ∈ H, (u : G) ∈ Subgroup.normalizer (conjSubgroup V h : Set G) :=
      mem_normalizer_conj_of_mem_centralizer hV hTI hVne hH hT huCE
    have hW2 : IsElemAbelian 2 W := isElemAbelian_conjSubgroup' hV g
    have hTIW : CFSG.CGT.Timmesfeld75.IsTI W := isTI_conj hTI g
    have hper : ∀ h ∈ H, U ≤ Subgroup.normalizer (conjSubgroup V h : Set G) ∧
        U ≤ Subgroup.centralizer (conjSubgroup Z h : Set G) := by
      intro h hh
      by_cases hWh : conjSubgroup V h = W
      · constructor
        · intro x hx
          rw [hWh]
          exact Subgroup.le_normalizer (hUW hx)
        · refine Subgroup.le_centralizer_iff.mpr ?_
          intro c hc
          refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
          have hcV : c ∈ conjSubgroup V h := by
            rw [mem_conjSubgroup_iff] at hc ⊢
            exact (Subgroup.mem_inf.mp
              (show h * c * h⁻¹ ∈ V ⊓ Subgroup.centralizer (T : Set G) from hc)).1
          exact (CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hW2
            (hWh ▸ hcV) (hUW hx)).symm
      · by_cases hcom : ∀ a ∈ W, ∀ b ∈ conjSubgroup V h, a * b = b * a
        · constructor
          · intro x hx
            exact Subgroup.centralizer_le_normalizer (conjSubgroup V h)
              (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcom x (hUW hx) b hb).symm)
          · refine Subgroup.le_centralizer_iff.mpr ?_
            intro c hc
            have hcV : c ∈ conjSubgroup V h := by
              rw [mem_conjSubgroup_iff] at hc ⊢
              exact (Subgroup.mem_inf.mp
                (show h * c * h⁻¹ ∈ V ⊓ Subgroup.centralizer (T : Set G) from hc)).1
            exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
              hcom x (hUW hx) c hcV
        · set g' : G := g⁻¹ * h with hg'def
          have hconj' : conjSubgroup W g' = conjSubgroup V h := by
            dsimp only [W, g']
            rw [conjSubgroup_conjSubgroup]
            congr 1
            group
          have hUnVne : nVSub W g' ≠ ⊥ := by
            refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(u : G), ?_⟩, ?_⟩
            · refine ⟨huW, ?_⟩
              rw [hconj']
              exact huN h hh
            · exact fun hh' => hu1 (congrArg Subtype.val hh')
          have hUnV : U ≤ nVSub W g' := by
            intro x hxU
            by_contra hxN
            have hxW : x ∈ W := hUW hxU
            have hxU' : x ∉ nVSub W g' := hxN
            have hnotle : ¬ conjSubgroup V h ≤ Subgroup.normalizer (W : Set G) := by
              intro hle
              apply hcom
              have hle'' : conjSubgroup W g' ≤ Subgroup.normalizer (W : Set G) := by
                rw [hconj']
                exact hle
              have hle' : W ≤ Subgroup.normalizer (conjSubgroup V h : Set G) := by
                have hh' : W ≤ Subgroup.normalizer (conjSubgroup W g' : Set G) :=
                  (le_normalizer_conj_iff hW2 hTIW).mp hle''
                rwa [hconj'] at hh'
              exact commute_of_le_normalizer_of_le_normalizer hV hTI ⟨g, rfl⟩ ⟨h, rfl⟩ hle' hle
            have hproper : conjSubgroup V h ⊓ Subgroup.normalizer (W : Set G) <
                conjSubgroup V h :=
              lt_of_le_of_ne inf_le_left fun hh' => hnotle ((le_of_eq hh'.symm).trans inf_le_right)
            obtain ⟨x', hx'1, hx'2⟩ := SetLike.exists_of_lt hproper
            have hx'B : x' ∉ bSub W g' := by simpa [bSub, hconj'] using hx'2
            have hodd : Odd (orderOf (x * x')) :=
              odd_orderOf_mul hW2 hTIW hUnVne hxW hxU' (hconj' ▸ hx'1) hx'B
            have hx'O2 : x' ∈ pCoreOf 2 H :=
              conjSubgroup_le_pCoreOf_of_isCalH0 hH0 hh hx'1
            have hmem : x * x' ∈ U ⊔ pCoreOf 2 H :=
              Subgroup.mul_mem _ (Subgroup.mem_sup_left hxU) (Subgroup.mem_sup_right hx'O2)
            have hU2 : IsPGroup 2 U := (CFSG.Open.IsElemAbelian.isPGroup hW2).to_le hUW
            have h2grp : IsPGroup 2 ↥(U ⊔ pCoreOf 2 H) :=
              hU2.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H)
                (hUH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H))
            have hxx' : x * x' = 1 :=
              eq_one_of_odd_orderOf_of_mem_isPGroup h2grp hmem hodd
            have hx2sq : x * x = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hW2 hxW
            have hxeq : x = x' := by
              have h : x' = x := by
                have h' := eq_inv_of_mul_eq_one_right hxx'
                rwa [inv_eq_of_mul_eq_one_right hx2sq] at h'
              exact h.symm
            have hbot : W ⊓ conjSubgroup V h = ⊥ := by
              rw [← hconj']
              exact inf_conjSubgroup_eq_bot_of_isTI hTIW (by rw [hconj']; exact hWh)
            have hxbot : x ∈ (⊥ : Subgroup G) := by
              rw [← hbot]
              exact ⟨hxW, hxeq ▸ hx'1⟩
            exact hxU' (by rw [Subgroup.mem_bot.mp hxbot]; exact (nVSub W g').one_mem)
          have hg' : conjSubgroup W g' ≠ W := by rw [hconj']; exact hWh
          constructor
          · intro x hx
            have hx' : x ∈ nVSub W g' := hUnV hx
            rw [← hconj']
            exact (Subgroup.mem_inf.mp
              (show x ∈ W ⊓ Subgroup.normalizer (conjSubgroup W g' : Set G) from hx')).2
          · refine Subgroup.le_centralizer_iff.mpr ?_
            intro c hc
            refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
            have hcE : c ∈ E := conjSubgroup_le_conjClosure Z H hh hc
            have hcVh : c ∈ conjSubgroup V h := by
              rw [mem_conjSubgroup_iff] at hc ⊢
              exact (Subgroup.mem_inf.mp
                (show h * c * h⁻¹ ∈ V ⊓ Subgroup.centralizer (T : Set G) from hc)).1
            have hcB : c ∈ bSub W g' := by
              refine ⟨by rwa [hconj'], ?_⟩
              have hcu : c * (u : G) = (u : G) * c :=
                Subgroup.mem_centralizer_iff.mp huCE c hcE
              exact centralizer_le_normalizer_of_isTI hTIW huW hu1
                (Subgroup.mem_centralizer_iff.mpr fun y hy => by
                  rw [Set.mem_singleton_iff] at hy
                  subst hy
                  exact hcu.symm)
            exact nVSub_comm_bSub hTIW hg' (hUnV hx) hcB
    refine ⟨?_, ?_⟩
    · refine Subgroup.le_centralizer_iff.mpr ?_
      show conjClosure Z H ≤ Subgroup.centralizer (U : Set G)
      refine conjClosure_le fun h hh c hc => ?_
      have hcZh : h * c * h⁻¹ ∈ conjSubgroup Z h⁻¹ := by
        rw [mem_conjSubgroup_iff]
        have hce : h⁻¹ * (h * c * h⁻¹) * (h⁻¹)⁻¹ = c := by group
        rw [hce]
        exact hc
      exact (Subgroup.le_centralizer_iff.mp (hper h⁻¹ (H.inv_mem hh)).2) hcZh
    · intro h hh
      have hconjN : conjSubgroup (conjSubgroup V h⁻¹) h = V := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      calc conjSubgroup U h ≤
            conjSubgroup (Subgroup.normalizer (conjSubgroup V h⁻¹ : Set G)) h :=
            Subgroup.map_mono (hper h⁻¹ (H.inv_mem hh)).1
        _ = Subgroup.normalizer (conjSubgroup (conjSubgroup V h⁻¹) h : Set G) :=
            conjSubgroup_normalizer _ _
        _ = Subgroup.normalizer (V : Set G) := by rw [hconjN]

end CFSG.LocalAnalysis.WeakClosure81

end
