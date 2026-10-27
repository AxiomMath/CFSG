module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mQuot_le_of_relIndex_le {A B C D : Subgroup G}
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (hrel : C.relIndex A ≤ D.relIndex B) :
    E3.mQuot A C ≤ E3.mQuot B D := by
  rw [E3.relIndex_eq_two_pow hA C, E3.relIndex_eq_two_pow hB D] at hrel
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hrel

@[expose] noncomputable def kSub15 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L Y Z : Subgroup G) : Subgroup G :=
  fSub15 M V₀ V hV L Z ⊓
    preTil (v1Sub M V₀ V hV L) V hV (fixV (barSub (v1Sub M V₀ V hV L) V hV Y))

theorem s15_Twelve_mem_kSub15 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {Y : Subgroup G} (hY : Y ≤ D.M) {Z : Subgroup G}
    (hZ : Z ∈ wConj D.M V₀ V hV L) {f : G} :
    f ∈ kSub15 D.M V₀ V hV L Y Z ↔ f ∈ fSub15 D.M V₀ V hV L Z ∧
      ∀ y ∈ Y, y * f * y⁻¹ * f⁻¹ ∈ v1Sub D.M V₀ V hV L := by
  set V1 := v1Sub D.M V₀ V hV L with hV1def
  have hV1V : V1 ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hFZV : fSub15 D.M V₀ V hV L Z ≤ V := by
    rw [fSub15]
    obtain ⟨m, hm, rfl⟩ := hZ
    exact sup_le (s15_Tools_conj_wSub_le D h.hyp125 hV hm) hV1V
  have hEs : Y ≤ stabTil V1 V :=
    hY.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 hV))
  rw [kSub15, Subgroup.mem_inf]
  constructor
  · rintro ⟨hfFZ, hfpre⟩
    exact ⟨hfFZ, (s15_Glue_mem_preTil_fixV_iff V1 V Y hV hEs (hFZV hfFZ)).1 hfpre⟩
  · rintro ⟨hfFZ, hall⟩
    exact ⟨hfFZ, (s15_Glue_mem_preTil_fixV_iff V1 V Y hV hEs (hFZV hfFZ)).2 hall⟩

theorem s15_Twelve_kernel (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {n : ℕ} {k : G} (hk : Cond1512 n D.M V k) {X Z : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) (hZ : Z ∈ wConj D.M V₀ V hV L)
    (hZk : ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k) :
    ∃ C : Subgroup G, C ≤ ySub15 D.M V₀ V hV L X k ∧
      (∀ y ∈ ySub15 D.M V₀ V hV L X k, y ∈ C ↔
        ∀ f ∈ fSub15 D.M V₀ V hV L Z, y * f * y⁻¹ * f⁻¹ ∈ v1Sub D.M V₀ V hV L) ∧
      mSub C ≤ mSub (v1Sub D.M V₀ V hV L) ∧
      gamma15 D.M V₀ V hV L ≤ E3.mQuot (ySub15 D.M V₀ V hV L X k) C + n := by
  classical
  set V1 := v1Sub D.M V₀ V hV L with hV1def
  set F := fSub15 D.M V₀ V hV L X with hFdef
  set FZ := fSub15 D.M V₀ V hV L Z with hFZdef
  set Y := ySub15 D.M V₀ V hV L X k with hYdef
  have h151 := h.hyp151
  have h125 := h.hyp151.hyp125
  have hV1V : V1 ≤ V := s15_Infra_v1Sub_le h125 hV
  have hMnorm : D.M ≤ normalizer (V1 : Set G) := s15_Infra_le_normalizer_v1Sub h125 hV
  obtain ⟨m', hm', hXeq⟩ := hX
  have hv1m : conjSubgroup V1 m' = V1 := s15_Infra_conjSubgroup_v1Sub h125 hV hm'
  have hFV : F ≤ V := by
    rw [hFdef, fSub15, hXeq]
    exact sup_le (s15_Tools_conj_wSub_le D h125 hV hm') hV1V
  have hFZV : FZ ≤ V := by
    rw [hFZdef, fSub15]
    obtain ⟨m, hm, rfl⟩ := hZ
    exact sup_le (s15_Tools_conj_wSub_le D h125 hV hm) hV1V
  have hsup : conjSubgroup (wSub V₀ V hV L) m' ⊔ conjSubgroup V1 m' =
      conjSubgroup (wSub V₀ V hV L ⊔ V1) m' := by
    unfold conjSubgroup
    rw [Subgroup.map_sup]
  have hFk : conjSubgroup F k = conjSubgroup (wSub V₀ V hV L ⊔ V1) (m' * k) := by
    rw [hFdef, fSub15, hXeq, ← hV1def, ← hv1m, hsup, conjSubgroup_conjSubgroup, hv1m]
  have hYFk : Y ≤ conjSubgroup F k := by
    rw [hYdef, ySub15]
    exact inf_le_left
  have hYM : Y ≤ D.M := by
    rw [hYdef, ySub15]
    exact inf_le_right
  have hFkVk : conjSubgroup F k ≤ conjSubgroup V k := E3.conjSubgroup_mono_left k hFV
  have hYVk : Y ≤ conjSubgroup V k := hYFk.trans hFkVk
  have hY2 : IsPGroup 2 Y := (E3.isElemAbelian_conjSubgroup hV k).isPGroup.to_le hYVk
  have hV12 : IsPGroup 2 V1 := hV.isPGroup.to_le hV1V
  have hFk2 : IsPGroup 2 (conjSubgroup F k) :=
    (E3.isElemAbelian_conjSubgroup hV k).isPGroup.to_le hFkVk
  have hVk2 : IsPGroup 2 (conjSubgroup V k) :=
    (E3.isElemAbelian_conjSubgroup hV k).isPGroup
  have hcent_le : ∀ y ∈ Y, y ≠ 1 → centralizer ({y} : Set G) ≤ conjSubgroup D.M k := by
    intro y hyY hy1
    have hyFk : y ∈ conjSubgroup (wSub V₀ V hV L ⊔ V1) (m' * k) := hFk ▸ (hYFk hyY)
    have hu := uniqueMax_conjSubgroup_of_mem (g := m' * k) h.unique₁ hyFk hy1
    have hK := UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) (m' * k)
    have hy2 : ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
      refine ⟨1, ?_⟩
      have hyy := (E3.isElemAbelian_conjSubgroup hV k).2 y (hYVk hyY)
      simpa using hyy
    have h1 := (centralizer_le_of_uniqueMax hK hy1 hy2 hu).1
    have hMeq : conjSubgroup D.M (m' * k) = conjSubgroup D.M k := by
      rw [← conjSubgroup_conjSubgroup, s15_Tools_conjSubgroup_M D hm']
    exact h1.trans (le_of_eq hMeq)
  obtain ⟨f₀, hf₀FZ, hf₀Mk⟩ := SetLike.not_le_iff_exists.1 hZk
  let C : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ f ∈ FZ, y * f * y⁻¹ * f⁻¹ ∈ V1}
      mul_mem' := by
        intro y y' hy hy'
        refine ⟨Y.mul_mem hy.1 hy'.1, fun f hf => ?_⟩
        have hyN : y ∈ normalizer (V1 : Set G) := hMnorm (hYM hy.1)
        have h1 : y * (y' * f * y'⁻¹ * f⁻¹) * y⁻¹ ∈ V1 :=
          (Subgroup.mem_normalizer_iff.1 hyN _).1 (hy'.2 f hf)
        have h2 : y * f * y⁻¹ * f⁻¹ ∈ V1 := hy.2 f hf
        have h3 : (y * y') * f * (y * y')⁻¹ * f⁻¹ =
            (y * (y' * f * y'⁻¹ * f⁻¹) * y⁻¹) * (y * f * y⁻¹ * f⁻¹) := by group
        rw [h3]
        exact V1.mul_mem h1 h2
      one_mem' := by
        refine ⟨Y.one_mem, fun f hf => ?_⟩
        simpa using V1.one_mem
      inv_mem' := by
        intro y hy
        refine ⟨Y.inv_mem hy.1, fun f hf => ?_⟩
        have hyN : y⁻¹ ∈ normalizer (V1 : Set G) :=
          (Subgroup.normalizer _).inv_mem (hMnorm (hYM hy.1))
        have h1 : y⁻¹ * (y * f * y⁻¹ * f⁻¹)⁻¹ * y ∈ V1 := by
          simpa using
            (Subgroup.mem_normalizer_iff.1 hyN _).1 (V1.inv_mem (hy.2 f hf))
        have h2 : y⁻¹ * f * (y⁻¹)⁻¹ * f⁻¹ =
            y⁻¹ * (y * f * y⁻¹ * f⁻¹)⁻¹ * y := by group
        rw [h2]
        exact h1 }
  have hCY : C ≤ Y := fun y hy => hy.1
  have hCFk : C ≤ conjSubgroup F k := hCY.trans hYFk
  have hCchar : ∀ y ∈ Y, y ∈ C ↔ ∀ f ∈ FZ, y * f * y⁻¹ * f⁻¹ ∈ V1 := by
    intro y hy
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hC2 : IsPGroup 2 C := hY2.to_le hCY
  have hCm : mSub C ≤ mSub V1 := by
    have hbot : C ⊓ centralizer ({f₀} : Set G) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hzbot
      have hz1 : z ≠ 1 := fun h => hzbot (Subgroup.mem_bot.2 h)
      have hzf : f₀ * z = z * f₀ :=
        (Subgroup.mem_centralizer_singleton_iff.1 hz.2).symm
      have hmem : f₀ ∈ centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 hzf
      exact hf₀Mk (hcent_le z hz.1.1 hz1 hmem)
    let φ : C → V1 := fun y =>
      ⟨y * f₀ * y⁻¹ * f₀⁻¹, (hCchar y y.2.1).1 y.2 f₀ hf₀FZ⟩
    have hinj : Function.Injective φ := by
      intro y y' hyy'
      have hval := congrArg Subtype.val hyy'
      have hcancel : (y : G) * f₀ * (y : G)⁻¹ = (y' : G) * f₀ * (y' : G)⁻¹ :=
        mul_right_cancel hval
      have hzC : ((y' : G)⁻¹ * y) ∈ C := C.mul_mem (C.inv_mem y'.2) y.2
      have hzcent : ((y' : G)⁻¹ * y) ∈ centralizer ({f₀} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have h2 : (y' : G)⁻¹ * y * f₀ * ((y' : G)⁻¹ * y)⁻¹ = f₀ := by
          calc (y' : G)⁻¹ * y * f₀ * ((y' : G)⁻¹ * y)⁻¹
              = (y' : G)⁻¹ * (y * f₀ * (y : G)⁻¹) * (y' : G) := by group
            _ = (y' : G)⁻¹ * (y' * f₀ * (y' : G)⁻¹) * (y' : G) := by rw [hcancel]
            _ = f₀ := by group
        calc (y' : G)⁻¹ * y * f₀
            = (y' : G)⁻¹ * y * f₀ * ((y' : G)⁻¹ * y)⁻¹ * ((y' : G)⁻¹ * y) := by group
          _ = f₀ * ((y' : G)⁻¹ * y) := by rw [h2]
      have hz : ((y' : G)⁻¹ * y) ∈ C ⊓ centralizer ({f₀} : Set G) := ⟨hzC, hzcent⟩
      rw [hbot] at hz
      have hz1 : (y' : G)⁻¹ * y = 1 := Subgroup.mem_bot.1 hz
      exact Subtype.ext (by
        calc (y : G) = y' * ((y' : G)⁻¹ * y) := by group
          _ = y' * 1 := by rw [hz1]
          _ = y' := by group)
    have hcard := Nat.card_le_card_of_injective φ hinj
    rw [card_eq_two_pow_mSub hC2, card_eq_two_pow_mSub hV12] at hcard
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hcard
  have hRank : mSub (conjSubgroup F k) = mSub V1 + gamma15 D.M V₀ V hV L := by
    have hA := s15_FiveTen_mQuot_conj_bot D h125 hV (L := L) (m' * k)
    rw [← hFk, s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk] at hA
    exact hA
  have hFY : E3.mQuot (conjSubgroup F k) Y ≤ n := by
    have hYeq : Y = conjSubgroup F k ⊓ (conjSubgroup V k ⊓ D.M) := by
      rw [hYdef, ySub15]
      rw [← inf_assoc, inf_eq_left.2 hFkVk]
    have hrel :
        (conjSubgroup F k ⊓ (conjSubgroup V k ⊓ D.M)).relIndex (conjSubgroup F k) ≤
          (conjSubgroup V k ⊓ D.M).relIndex (conjSubgroup V k) := by
      calc (conjSubgroup F k ⊓ (conjSubgroup V k ⊓ D.M)).relIndex (conjSubgroup F k)
          = (conjSubgroup V k ⊓ D.M).relIndex (conjSubgroup F k) :=
            Subgroup.inf_relIndex_left _ _
        _ ≤ (conjSubgroup V k ⊓ D.M).relIndex (conjSubgroup V k) :=
            Subgroup.relIndex_le_of_le_right hFkVk (E3.relIndex_ne_zero' _ _)
    calc E3.mQuot (conjSubgroup F k) Y
        = E3.mQuot (conjSubgroup F k) (conjSubgroup F k ⊓ (conjSubgroup V k ⊓ D.M)) := by
          rw [hYeq]
      _ ≤ E3.mQuot (conjSubgroup V k) (conjSubgroup V k ⊓ D.M) :=
            mQuot_le_of_relIndex_le hFk2 hVk2 hrel
      _ = E3.mQuot (conjSubgroup V k) D.M := by
            unfold E3.mQuot
            rw [inf_comm, Subgroup.inf_relIndex_right]
      _ ≤ n := hk.2.2.2
  have hA' : mSub (conjSubgroup F k) = mSub C + E3.mQuot (conjSubgroup F k) C := by
    have hh := E3.mQuot_add (V := conjSubgroup F k) (U := ⊥) (U' := C) bot_le hCFk
    rw [s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk] at hh
    exact hh
  have hB' : E3.mQuot (conjSubgroup F k) C = E3.mQuot Y C + E3.mQuot (conjSubgroup F k) Y :=
    E3.mQuot_add hCY hYFk
  have hEq : mSub V1 + gamma15 D.M V₀ V hV L =
      mSub C + (E3.mQuot Y C + E3.mQuot (conjSubgroup F k) Y) := by
    rw [← hRank, hA', hB']
  have hle : gamma15 D.M V₀ V hV L ≤ E3.mQuot Y C + n := by
    have hb : mSub V1 + gamma15 D.M V₀ V hV L ≤ mSub V1 + (E3.mQuot Y C + n) := by
      rw [hEq]
      exact add_le_add hCm (Nat.add_le_add_left hFY _)
    omega
  exact ⟨C, hCY, hCchar, hCm, hle⟩

theorem s15_Twelve_axis_pos (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {n : ℕ} {k : G} (hk : Cond1512 n D.M V k)
    (hn : n < gamma15 D.M V₀ V hV L) {X Z : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    (hZ : Z ∈ wConj D.M V₀ V hV L) (hZk : ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k) :
    1 ≤ E3.mQuot (fSub15 D.M V₀ V hV L Z)
      (kSub15 D.M V₀ V hV L (ySub15 D.M V₀ V hV L X k) Z) := by
  classical
  set V1 := v1Sub D.M V₀ V hV L with hV1def
  set FZ := fSub15 D.M V₀ V hV L Z with hFZdef
  set Y := ySub15 D.M V₀ V hV L X k with hYdef
  set K := kSub15 D.M V₀ V hV L Y Z with hKdef
  have h125 := h.hyp151.hyp125
  have hYM : Y ≤ D.M := by
    rw [hYdef, ySub15]
    exact inf_le_right
  have hKFZ : K ≤ FZ := by
    rw [hKdef, kSub15]
    exact inf_le_left
  have hFZV : FZ ≤ V := by
    rw [hFZdef, fSub15]
    obtain ⟨m, hm, rfl⟩ := hZ
    exact sup_le (s15_Tools_conj_wSub_le D h125 hV hm) (s15_Infra_v1Sub_le h125 hV)
  have hFZ2 : IsPGroup 2 FZ := hV.isPGroup.to_le hFZV
  by_contra hnot
  rw [Nat.not_le] at hnot
  have hmq0 : E3.mQuot FZ K = 0 := by omega
  have hKFZeq : K = FZ := (E3.mQuot_eq_zero_iff hFZ2 hKFZ).1 hmq0
  have hYmem : ∀ y ∈ Y, ∀ f ∈ FZ, y * f * y⁻¹ * f⁻¹ ∈ V1 := by
    intro y hy f hf
    have hfK : f ∈ K := hKFZeq.symm ▸ hf
    have hfK' : f ∈ kSub15 D.M V₀ V hV L Y Z := hKdef ▸ hfK
    exact (((s15_Twelve_mem_kSub15 D h.hyp151 hV hYM hZ).1 hfK').2) y hy
  obtain ⟨C, hCY, hCchar, hCm, hCbound⟩ := s15_Twelve_kernel D h hV hk hX hZ hZk
  have hYC : Y ≤ C := fun y hy => (hCchar y hy).2 (hYmem y hy)
  have hCY' : C = Y := le_antisymm hCY hYC
  have hle : gamma15 D.M V₀ V hV L ≤ n := by
    have hh := hCbound
    rw [hCY', ← hYdef, E3.mQuot_self, zero_add] at hh
    exact hh
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
