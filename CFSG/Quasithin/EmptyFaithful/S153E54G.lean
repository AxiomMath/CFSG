module

public import CFSG.Quasithin.EmptyFaithful.S153E54F

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Orth

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem orth_iff (cx : Ctx15350 T Mc M V₁ V₂ t) {a b : G} (ha : a ∈ VZ T M) (hb : b ∈ VZ T M) :
    Orth153 cx.c a b ↔ quadPolar (qW cx) (IntMod.mk cx.c.hyp.elemAbelian ⟨a, ha⟩)
      (IntMod.mk cx.c.hyp.elemAbelian ⟨b, hb⟩) = 0 :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨ha, hb, h⟩⟩

theorem quadPolar_comm' {W : Type*} [CommGroup W] (q : W → ZMod 2) (x y : W) :
    quadPolar q x y = quadPolar q y x := by
  unfold quadPolar
  rw [mul_comm x y]
  ring

theorem orth_comm (cx : Ctx15350 T Mc M V₁ V₂ t) {a b : G} (h : Orth153 cx.c a b) :
    Orth153 cx.c b a := by
  obtain ⟨ha, hb, -⟩ := id h
  rw [orth_iff cx ha hb] at h
  rw [orth_iff cx hb ha, quadPolar_comm']
  exact h

theorem orth_one_left (cx : Ctx15350 T Mc M V₁ V₂ t) {b : G} (hb : b ∈ VZ T M) :
    Orth153 cx.c 1 b := by
  rw [orth_iff cx (VZ T M).one_mem hb]
  exact quadPolar_one_left (qW_spec cx).1 _

theorem orth_one_right (cx : Ctx15350 T Mc M V₁ V₂ t) {a : G} (ha : a ∈ VZ T M) :
    Orth153 cx.c a 1 := by
  rw [orth_iff cx ha (VZ T M).one_mem]
  exact quadPolar_one_right (qW_spec cx).1 _

theorem orth_conj (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G} (hy : y ∈ M) {a b : G}
    (ha : a ∈ VZ T M) (hb : b ∈ VZ T M)
    (ha' : y * a * y⁻¹ ∈ VZ T M) (hb' : y * b * y⁻¹ ∈ VZ T M) :
    Orth153 cx.c (y * a * y⁻¹) (y * b * y⁻¹) ↔ Orth153 cx.c a b := by
  have hV := cx.c.hyp.elemAbelian
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := cx.c.hyp.le_normalizer hy
  have hiso : convI hV ⟨y, hyN⟩ ∈ orthogonalGroupOf (qW cx) := by
    rw [← (qW_spec cx).2.2.2]
    exact convI_mem_autI hV hy hyN
  rw [orth_iff cx ha' hb', orth_iff cx ha hb]
  have e1 : convI hV ⟨y, hyN⟩ (IntMod.mk hV ⟨a, ha⟩) = IntMod.mk hV ⟨y * a * y⁻¹, ha'⟩ :=
    IntMod.val_injective (by rw [convI_apply_val]; rfl)
  have e2 : convI hV ⟨y, hyN⟩ (IntMod.mk hV ⟨b, hb⟩) = IntMod.mk hV ⟨y * b * y⁻¹, hb'⟩ :=
    IntMod.val_injective (by rw [convI_apply_val]; rfl)
  rw [← e1, ← e2, quadPolar_apply_isometry hiso]

theorem not_orth_conj (cx : Ctx15350 T Mc M V₁ V₂ t) {g : G} (hg : g ∈ Y153 Mc M)
    (hgZ : NotOrth153 cx.c g) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hzgen : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) :
    ¬ Orth153 cx.c z (g⁻¹ * z * g) ∧ ¬ Orth153 cx.c z (g * z * g⁻¹) := by
  have hgM : g ∈ M := Y153_le Mc M hg
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hVn := cx.c.hyp.le_normalizer
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hz
  have hconjV : ∀ {y x : G}, y ∈ M → x ∈ VZ T M → y * x * y⁻¹ ∈ VZ T M := fun {y x} hy hx =>
    (Subgroup.mem_normalizer_iff.1 (hVn hy) x).1 hx
  have h2 : ¬ Orth153 cx.c z (g⁻¹ * z * g) := by
    intro h
    apply hgZ
    intro z₁ hz₁ z' hz'
    have hz'V : z' ∈ VZ T M := by
      have h1 : g * z' * g⁻¹ ∈ VZ T M := cx.c.hyp.Z_le_VZ (mem_conjSubgroup_iff.1 hz')
      have := hconjV hgM' h1
      simpa [mul_assoc] using this
    rcases hzgen z₁ hz₁ with rfl | rfl
    · exact orth_one_left cx hz'V
    · by_cases hz'1 : g * z' * g⁻¹ = 1
      · have : z' = 1 := by
          have := congrArg (fun x => g⁻¹ * x * g) hz'1
          simpa [mul_assoc] using this
        rw [this]
        exact orth_one_right cx (cx.c.hyp.Z_le_VZ hz₁)
      · have hz'z : g * z' * g⁻¹ = z₁ :=
          (hzgen _ (mem_conjSubgroup_iff.1 hz')).resolve_left hz'1
        have : z' = g⁻¹ * z₁ * g := by
          have := congrArg (fun x => g⁻¹ * x * g) hz'z
          simpa [mul_assoc] using this
        rw [this]
        exact h
  refine ⟨h2, fun h => h2 ?_⟩
  have hz'V : g⁻¹ * z * g ∈ VZ T M := by
    have := hconjV hgM' hzV
    simpa using this
  have hgzV : g * z * g⁻¹ ∈ VZ T M := hconjV hgM hzV
  have hA : g⁻¹ * z * g⁻¹⁻¹ ∈ VZ T M := by simpa using hz'V
  have hB : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ ∈ VZ T M := by simpa [mul_assoc] using hzV
  have key := (orth_conj cx hgM' hzV hgzV hA hB).2 h
  have e1 : g⁻¹ * z * g⁻¹⁻¹ = g⁻¹ * z * g := by simp
  have e2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rw [e1, e2] at key
  exact orth_comm cx key

theorem hgV_of_notOrth (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) {g : G}
    (hgZ : NotOrth153 cx.c g) :
    ¬ rconj (quasithinOmegaOneCenter T) g ≤ Zp54 T M V₁ Mc := by
  intro hle
  apply hgZ
  intro z hz z' hz'
  have hz'Zp : z' ∈ Zp54 T M V₁ Mc := hle hz'
  exact ((isPerp_Zp cx c z').1 hz'Zp).2 z hz

theorem centralizer_T_Y_trivial (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G}
    (hxT : x ∈ T) (hx : ∀ y ∈ Y153 Mc M, y * x = x * y) : x = 1 := by
  by_contra hx1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, -, hDY, hD3, hDi⟩ :=
    exists_sylow_ge (p := 3) (Q := (⊥ : Subgroup G)) (K := Y153 Mc M)
      (IsPGroup.of_card (p := 3) (n := 0) (by simp)) bot_le
  have hYD := Y_eq_sup_of_sylow cx hDY hD3 hDi
  have hCV := fixed_V_D_eq_one h113 cx hDY hD3 hYD
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (Y153 Mc M : Set G) with hQ
  have hxQ : x ∈ Q := ⟨hxT, Subgroup.mem_centralizer_iff.2 fun y hy => hx y hy⟩
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hxQ
    exact hx1 hxQ
  have hTNY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
    (T_le_M cx).trans (le_normalizer_Y153 Mc M)
  have hconjQ : ∀ t' ∈ T, ∀ q ∈ Q, t' * q * t'⁻¹ ∈ Q := by
    intro t' ht' q hq
    refine ⟨T.mul_mem (T.mul_mem ht' hq.1) (T.inv_mem ht'), Subgroup.mem_centralizer_iff.mpr
      fun y hy => ?_⟩
    have hy' : t'⁻¹ * y * t'⁻¹⁻¹ ∈ Y153 Mc M :=
      (Subgroup.mem_normalizer_iff.mp (hTNY (T.inv_mem ht')) y).mp hy
    have hc := Subgroup.mem_centralizer_iff.mp hq.2 _ hy'
    have e1 : y * (t' * q * t'⁻¹) = t' * ((t'⁻¹ * y * t'⁻¹⁻¹) * q) * t'⁻¹ := by group
    have e2 : (t' * q * t'⁻¹) * y = t' * (q * (t'⁻¹ * y * t'⁻¹⁻¹)) * t'⁻¹ := by group
    rw [e1, e2, hc]
  have hTNQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    intro t' ht'
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconjQ t' ht' q, fun hq => ?_⟩
    have := hconjQ t'⁻¹ (T.inv_mem ht') _ hq
    have e : t'⁻¹ * (t' * q * t'⁻¹) * t'⁻¹⁻¹ = q := by group
    rwa [e] at this
  have hT2 : IsPGroup 2 T := cx.hF.sylow_H.2.1
  have hQT : Q ≤ T := inf_le_left
  obtain ⟨z₀, hz₀Q, hz₀1, hz₀c⟩ := exists_ne_one_mem_center_of_normalized hT2 hQT hQne hTNQ
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨z₀, hQT hz₀Q⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hz₀1 hj
  set z₁ := z₀ ^ 2 ^ (j - 1) with hz₁
  have hord : orderOf z₁ = 2 := by
    have hd : 2 ^ (j - 1) ∣ orderOf z₀ := by
      rw [hj]
      exact pow_dvd_pow 2 (Nat.sub_le j 1)
    rw [hz₁, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hd, hj]
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    simp [pow_succ]
  have hz₁Q : z₁ ∈ Q := Subgroup.pow_mem _ hz₀Q _
  have hz₁sq : z₁ ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
  have hz₁T : z₁ ∈ T := hQT hz₁Q
  have hz₁c : ∀ y ∈ T, y * z₁ = z₁ * y := fun y hy =>
    (Commute.pow_right (hz₀c y hy : Commute y z₀) _).eq
  have hz₁Z : z₁ ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hz₁T, Subgroup.mem_centralizer_iff.mpr fun y hy => (hz₁c y hy)⟩,
      hz₁sq⟩
  have hz₁V : z₁ ∈ VZ T M := cx.c.hyp.Z_le_VZ hz₁Z
  have hz₁D : ∀ d ∈ D, d * z₁ * d⁻¹ = z₁ := by
    intro d hd
    have := Subgroup.mem_centralizer_iff.mp hz₁Q.2 d (hDY hd)
    calc d * z₁ * d⁻¹ = (z₁ * d) * d⁻¹ := by rw [this]
      _ = z₁ := by group
  have hz1 := hCV z₁ hz₁V hz₁D
  rw [hz1, orderOf_one] at hord
  omega

end Orth

section InfLeV

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem inf_le_V (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂)
    {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g ≤ VZ T M := by
  have hyp := hyp54 h113 cx c
  have hU : UH153 T M V₁ Mc = conjClosure (Zp54 T M V₁ Mc) Mc := (conjClosure_Zp_eq cx).symm
  have hgV := hgV_of_notOrth cx c hgZ
  have hVL := conjClosure_Z_Y h113 cx c
  obtain ⟨z, hz, hz1, hzgen⟩ := exists_Z_gen cx
  obtain ⟨hnZ1, hnZ2⟩ := not_orth_conj cx hg hgZ hz hzgen
  have hI' : UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g = Y153 Mc M ⊔ UH153 T M V₁ Mc := by
    have := hyp.G26_one hg hgV
    rwa [conjClosure_Zp_eq cx] at this
  obtain ⟨h31, h32, h33, h34, h35, h36⟩ := hyp.G26_three hU hg hgV rfl
  have h4 := hyp.G26_four hU hg hgV rfl
  rw [hVL] at h31 h32 h33 h34 h35 h4
  obtain ⟨hSeq, hSset⟩ := hyp.G26_two (U := UH153 T M V₁ Mc)
    (I := UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g)
    (S := pCoreOf 2 (UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g))
    (W := UH153 T M V₁ Mc ⊓ pCoreOf 2 (UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g))
    hU hg hgV rfl rfl rfl
  set U := UH153 T M V₁ Mc with hUdef
  set I := U ⊔ rconj U g with hIdef
  set S := pCoreOf 2 I with hSdef
  set X := U ⊓ rconj U g with hXdef
  have hYI : Y153 Mc M ≤ I := hI' ▸ le_sup_left
  have hgI : g ∈ I := hYI hg
  obtain ⟨-, -, hST, hINorm, hSU⟩ := sx_facts_gen hI' (U_le_T cx) (T_le_normalizer_U cx)
    cx.hF.normalizes_L cx.hF.sylow_LT
  have hgM : g ∈ M := Y153_le Mc M hg
  have hVn := cx.c.hyp.le_normalizer
  have hconjV : ∀ {y x : G}, y ∈ M → x ∈ VZ T M → y * x * y⁻¹ ∈ VZ T M := fun {y x} hy hx =>
    (Subgroup.mem_normalizer_iff.1 (hVn hy) x).1 hx
  have hperp := isPerp_Zp cx c
  have hSUg : ∀ y ∈ S, ∀ a ∈ rconj U g, y * a * y⁻¹ ∈ rconj U g := by
    intro y hy a ha
    rw [mem_rconj] at ha ⊢
    have h1 : g * y * g⁻¹ ∈ S := hINorm g hgI y hy
    have h2 := hSU _ h1 _ ha
    have e : g * (y * a * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  have hXW : ∀ x ∈ X, ∀ w ∈ U ⊓ S, x * w = w * x := by
    intro x hx w hw
    have hxU : x ∈ U := hx.1
    have hxg : x ∈ rconj U g := hx.2
    have hc₁Z : x * w * x⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T := commutator_U_mem cx hxU hw.1
    have hc₁g : x * w * x⁻¹ * w⁻¹ ∈ rconj U g := by
      have h1 : w * x⁻¹ * w⁻¹ ∈ rconj U g := hSUg w hw.2 x⁻¹ ((rconj U g).inv_mem hxg)
      have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
      rw [e]
      exact (rconj U g).mul_mem hxg h1
    have hc₁ : x * w * x⁻¹ * w⁻¹ = 1 := by
      by_contra hne
      have heq : x * w * x⁻¹ * w⁻¹ = z := (hzgen _ hc₁Z).resolve_left hne
      have hgz : g * z * g⁻¹ ∈ Zp54 T M V₁ Mc := by
        refine ⟨hconjV hgM (cx.c.hyp.Z_le_VZ hz), ?_⟩
        rw [← heq]
        exact mem_rconj.1 hc₁g
      exact hnZ2 (((hperp _).1 hgz).2 z hz)
    calc x * w = (x * w * x⁻¹ * w⁻¹) * (w * x) := by group
      _ = w * x := by rw [hc₁, one_mul]
  have hXW' : ∀ x ∈ X, ∀ w ∈ rconj (U ⊓ S) g, x * w = w * x := by
    intro x hx w hw
    have hxU : x ∈ U := hx.1
    have hxg : x ∈ rconj U g := hx.2
    have hwg : g * w * g⁻¹ ∈ U ⊓ S := mem_rconj.1 hw
    have hwS : w ∈ S := by
      have := hINorm g⁻¹ (I.inv_mem hgI) _ hwg.2
      simpa [mul_assoc] using this
    have hc₂U : x * w * x⁻¹ * w⁻¹ ∈ U := by
      have h1 : w * x⁻¹ * w⁻¹ ∈ U := hSU w hwS x⁻¹ (U.inv_mem hxU)
      have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
      rw [e]
      exact U.mul_mem hxU h1
    have hc₂Z : g * (x * w * x⁻¹ * w⁻¹) * g⁻¹ ∈ quasithinOmegaOneCenter T := by
      have e : g * (x * w * x⁻¹ * w⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * w * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ := by group
      rw [e]
      exact commutator_U_mem cx (mem_rconj.1 hxg) hwg.1
    have hc₂V : x * w * x⁻¹ * w⁻¹ ∈ VZ T M := by
      have := hconjV (M.inv_mem hgM) (cx.c.hyp.Z_le_VZ hc₂Z)
      simpa [mul_assoc] using this
    have hc₂ : x * w * x⁻¹ * w⁻¹ = 1 := by
      by_contra hne
      have hne' : g * (x * w * x⁻¹ * w⁻¹) * g⁻¹ ≠ 1 := fun h => hne (by
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this)
      have heq : g * (x * w * x⁻¹ * w⁻¹) * g⁻¹ = z := (hzgen _ hc₂Z).resolve_left hne'
      have hc : x * w * x⁻¹ * w⁻¹ = g⁻¹ * z * g := by
        have := congrArg (fun y => g⁻¹ * y * g) heq
        simpa [mul_assoc] using this
      have hmem : x * w * x⁻¹ * w⁻¹ ∈ Zp54 T M V₁ Mc := ⟨hc₂V, hc₂U⟩
      rw [hc] at hmem
      exact hnZ1 (((hperp _).1 hmem).2 z hz)
    calc x * w = (x * w * x⁻¹ * w⁻¹) * (w * x) := by group
      _ = w * x := by rw [hc₂, one_mul]
  have hXS : ∀ x ∈ X, ∀ s ∈ S, x * s = s * x := by
    intro x hx s hs
    have hs' : s ∈ ((S : Subgroup G) : Set G) := hs
    rw [hSset] at hs'
    obtain ⟨w, hw, w', hw', rfl⟩ := hs'
    calc x * (w * w') = (x * w) * w' := by group
      _ = (w * x) * w' := by rw [hXW x hx w hw]
      _ = w * (x * w') := by group
      _ = w * (w' * x) := by rw [hXW' x hx w' hw']
      _ = (w * w') * x := by group
  have hVC : VZ T M ≤ Subgroup.centralizer (S : Set G) := fun v hv => (h33 hv).2
  have hXC : X ≤ Subgroup.centralizer (S : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun s hs => (hXS x hx s hs).symm
  have hPC : VZ T M ⊔ X ≤ Subgroup.centralizer (S : Set G) := sup_le hVC hXC
  intro x hx
  by_contra hxV
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, -, hDY, hD3, hDi⟩ :=
    exists_sylow_ge (p := 3) (Q := (⊥ : Subgroup G)) (K := Y153 Mc M)
      (IsPGroup.of_card (p := 3) (n := 0) (by simp)) bot_le
  have hYD := Y_eq_sup_of_sylow cx hDY hD3 hDi
  have hxP : x ∈ VZ T M ⊔ X := Subgroup.mem_sup_right hx
  have hinv : ∀ d ∈ D, x⁻¹ * (d * x * d⁻¹) ∈ VZ T M := by
    intro d hd
    have hcomm := h4 (Subgroup.commutator_mem_commutator ((VZ T M ⊔ X).inv_mem hxP)
      (hYI (hDY hd)))
    have e : ⁅x⁻¹, d⁆ = x⁻¹ * (d * x * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rwa [e] at hcomm
  have hVD : ∀ d ∈ D, ∀ v ∈ VZ T M, d * v * d⁻¹ ∈ VZ T M := fun d hd v hv =>
    hconjV (Y153_le Mc M (hDY hd)) hv
  have hV16 : ¬ 3 ∣ Nat.card ↥(VZ T M) := by
    rw [cx.c.hyp.card_VZ]
    norm_num
  obtain ⟨x₁, hx₁V, hx₁D⟩ := exists_fixed_in_coset hD3 hV16 hinv hVD
  have hx₁P : x₁ ∈ VZ T M ⊔ X := by
    have e : x₁ = x * (x⁻¹ * x₁) := by group
    rw [e]
    exact (VZ T M ⊔ X).mul_mem hxP (Subgroup.mem_sup_left hx₁V)
  have hx₁V' : x₁ ∉ VZ T M := fun h => hxV (by
    have e : x = x₁ * (x⁻¹ * x₁)⁻¹ := by group
    rw [e]
    exact (VZ T M).mul_mem h ((VZ T M).inv_mem hx₁V))
  have hx₁S : x₁ ∈ S := h32 hx₁P
  have hx₁C : ∀ s ∈ S, s * x₁ = x₁ * s := fun s hs =>
    Subgroup.mem_centralizer_iff.1 (hPC hx₁P) s hs
  have hUY : U ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    (((U_le_T cx).trans (T_le_M cx)).trans (le_normalizer_Y153 Mc M)).trans
      (normalizer_le_normalizer_pCoreOf 2 _)
  have hOS : pCoreOf 2 (Y153 Mc M) ≤ S :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hYI)
      (by rw [hI']; exact sup_le (le_normalizer_pCoreOf 2 _) hUY) (pCoreOf_isPGroup 2 _)
  have hYC : ∀ y ∈ Y153 Mc M, y * x₁ = x₁ * y := by
    have hle : Y153 Mc M ≤ Subgroup.centralizer ({x₁} : Set G) := by
      rw [hYD]
      refine sup_le (fun a ha => ?_) (fun d hd => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hx₁C a (hOS ha)).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have := hx₁D d hd
        calc x₁ * d = (d * x₁ * d⁻¹) * d := by rw [this]
          _ = d * x₁ := by group
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) x₁ rfl).symm
  have hx₁1 := centralizer_T_Y_trivial h113 cx (hST hx₁S) hYC
  exact hx₁V' (by rw [hx₁1]; exact (VZ T M).one_mem)

end InfLeV

end S153E54

end CFSG.Quasithin
