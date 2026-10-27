module

public import CFSG.RankThree.GF2n.Tim79aSec23Cp
public import CFSG.RankThree.GF2n.Tim79aSec22Comm

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

theorem mem_of_conjSubgroup_le {a k : G} {K : Subgroup G} (h : conjSubgroup a K ≤ K) (hk : k ∈ K) :
    a * k * a⁻¹ ∈ K :=
  h ⟨k, hk, by simp [MulAut.conj_apply]⟩

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem cPbar_sq_eq_one {x : G} (hx : x ∈ cPbar V H P) : x * x = 1 := by
  have hxP : x ∈ P := (Subgroup.mem_inf.mp hx).1
  have hxc : ∀ y ∈ xOf V H, ⁅x, y⁆ ∈ wOf V H := ((Subgroup.mem_inf.mp hx).2).2
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hsqF : (⟨x, hxP⟩ : P) ^ 2 ∈ frattini ↥P :=
    CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) _
  have hxV : x * x ∈ V := hc.frattini_P_le ⟨_, hsqF, by simp [pow_two]⟩
  have hZ : x * x ∈ Subgroup.centralizer (xOf V H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hw : ⁅x, y⁆ ∈ wOf V H := hxc y hy
    have hxw : x * ⁅x, y⁆ = ⁅x, y⁆ * x := hc.cPbar_centralizes_wOf hx _ hw
    have hw2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hw
    have h1 : x * y = ⁅x, y⁆ * y * x := by simp only [commutatorElement_def]; group
    calc y * (x * x) = ⁅x, y⁆ * ⁅x, y⁆ * y * (x * x) := by rw [hw2, one_mul]
      _ = ⁅x, y⁆ * (⁅x, y⁆ * y * x) * x := by group
      _ = ⁅x, y⁆ * (x * y) * x := by rw [← h1]
      _ = (⁅x, y⁆ * x) * y * x := by group
      _ = (x * ⁅x, y⁆) * y * x := by rw [hxw]
      _ = x * (⁅x, y⁆ * y * x) := by group
      _ = x * (x * y) := by rw [← h1]
      _ = x * x * y := by group
  have : x * x ∈ V ⊓ Subgroup.centralizer (xOf V H : Set G) := ⟨hxV, hZ⟩
  rw [hc.inf_centralizer_xOf_eq_bot] at this
  exact this

theorem isElemAbelian_cPbar : Assembly.IsElemAbelian 2 (cPbar V H P) := by
  have h := CFSG.Open.IsElemAbelian.closure_of_commute (p := 2) (s := (cPbar V H P : Set G))
    (fun a ha b hb => by
      have : ⁅a, b⁆ ∈ ⁅cPbar V H P, cPbar V H P⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [hc.commutator_cPbar_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        at this
      exact this)
    (fun a ha => by rw [pow_two]; exact hc.cPbar_sq_eq_one ha)
  rwa [Subgroup.closure_eq] at h

theorem isElemAbelian_wOf_sup_cPbar : Assembly.IsElemAbelian 2 (wOf V H ⊔ cPbar V H P) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hc.wOf_isElemAbelian hc.isElemAbelian_cPbar
    (fun a ha b hb => (hc.cPbar_centralizes_wOf hb a ha).symm)

theorem wOf_conj_facts {g : G} (hgH : g ∈ H) :
    (∀ w ∈ wOf V H, ∀ p ∈ P, w * p * w⁻¹ ∈ P) ∧
    (∀ w ∈ wOf V H, ∀ b ∈ conjSubgroup g V, w * b * w⁻¹ ∈ conjSubgroup g V) ∧
    (∀ x ∈ H, ∀ w ∈ wOf V H, x * w * x⁻¹ ∈ wOf V H) :=
  ⟨fun w hw p hp => (Subgroup.mem_normalizer_iff.mp
      (hc.M_le_normalizer_P (hc.pCoreH_le_M (wOf_le_pCore V H hw))) p).mp hp,
   fun w hw b hb => (Subgroup.mem_normalizer_iff.mp
      (hc.pCoreH_le_normalizer_conj hgH (wOf_le_pCore V H hw)) b).mp hb,
   fun x hx w hw => (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hx) w).mp hw⟩

theorem sec25b_of_a {g : G} (hgX : g ∈ xOf V H)
    (hg : ∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H)
    (ha : (P ⊓ xOf V H) ⊔ conjSubgroup g V = xOf V H) :
    (P ⊓ wOf V H) ⊔ (conjSubgroup g V ⊓ wOf V H) = wOf V H ∧
      (P ⊓ wOf V H) ⊓ (conjSubgroup g V ⊓ wOf V H) = ⊥ := by
  have hXH : xOf V H ≤ H := xOf_le_H hc.V_le_H
  have hgH : g ∈ H := hXH hgX
  obtain ⟨hWP, hWB, hWW⟩ := hc.wOf_conj_facts hgH
  set B := conjSubgroup g V with hB
  set W := wOf V H with hW
  set A := P ⊓ xOf V H with hA
  set K := (P ⊓ W) ⊔ (B ⊓ W) with hK
  have hBX : B ≤ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hgH)
  have hWX : W ≤ xOf V H := wOf_le_xOf V H
  have hKW : K ≤ W := sup_le inf_le_right inf_le_right
  have hconjA : ∀ a ∈ A, conjSubgroup a K ≤ K := by
    intro a ha'
    have haP : a ∈ P := (Subgroup.mem_inf.mp ha').1
    have haH : a ∈ H := hXH (Subgroup.mem_inf.mp ha').2
    unfold conjSubgroup
    rw [hK, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      refine Subgroup.mem_sup_left (S := P ⊓ W) (T := B ⊓ W) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · have := P.mul_mem (P.mul_mem haP (Subgroup.mem_inf.mp hk).1) (P.inv_mem haP)
        simpa [MulAut.conj_apply] using this
      · simpa [MulAut.conj_apply] using hWW a haH k (Subgroup.mem_inf.mp hk).2
    · rintro _ ⟨k, hk, rfl⟩
      have hkW := (Subgroup.mem_inf.mp hk).2
      have hc1 : a * k * a⁻¹ * k⁻¹ ∈ P ⊓ W := by
        refine ⟨?_, ?_⟩
        · have := P.mul_mem haP (hWP k hkW a⁻¹ (P.inv_mem haP))
          simpa [mul_assoc] using this
        · exact W.mul_mem (hWW a haH k hkW) (W.inv_mem hkW)
      have hk' : k ∈ K := Subgroup.mem_sup_right hk
      have e : a * k * a⁻¹ = (a * k * a⁻¹ * k⁻¹) * k := by group
      have key : a * k * a⁻¹ ∈ K := by
        rw [e]; exact K.mul_mem (Subgroup.mem_sup_left hc1) hk'
      simpa [MulAut.conj_apply] using key
  have hconjB : ∀ b ∈ B, conjSubgroup b K ≤ K := by
    intro b hb
    have hbH : b ∈ H := hXH (hBX hb)
    unfold conjSubgroup
    rw [hK, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      have hkW := (Subgroup.mem_inf.mp hk).2
      have hc1 : b * k * b⁻¹ * k⁻¹ ∈ B ⊓ W := by
        refine ⟨?_, ?_⟩
        · have := B.mul_mem hb (hWB k hkW b⁻¹ (B.inv_mem hb))
          simpa [mul_assoc] using this
        · exact W.mul_mem (hWW b hbH k hkW) (W.inv_mem hkW)
      have hk' : k ∈ K := Subgroup.mem_sup_left hk
      have e : b * k * b⁻¹ = (b * k * b⁻¹ * k⁻¹) * k := by group
      have key : b * k * b⁻¹ ∈ K := by
        rw [e]; exact K.mul_mem (Subgroup.mem_sup_right hc1) hk'
      simpa [MulAut.conj_apply] using key
    · rintro _ ⟨k, hk, rfl⟩
      refine Subgroup.mem_sup_right (S := P ⊓ W) (T := B ⊓ W) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · have := B.mul_mem (B.mul_mem hb (Subgroup.mem_inf.mp hk).1) (B.inv_mem hb)
        simpa [MulAut.conj_apply] using this
      · simpa [MulAut.conj_apply] using hWW b hbH k (Subgroup.mem_inf.mp hk).2
  have hnorm : ∀ x : G, (∀ y ∈ K, x * y * x⁻¹ ∈ K) → (∀ y ∈ K, x⁻¹ * y * x⁻¹⁻¹ ∈ K) →
      x ∈ Subgroup.normalizer (K : Set G) := fun x h1 h2 => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => h1 y hy, fun hy => by simpa [mul_assoc] using h2 _ hy⟩
  let T : Subgroup G :=
    { carrier := {x | x ∈ xOf V H ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
        ∀ w ∈ W, ⁅w, x⁆ ∈ K}
      one_mem' := ⟨(xOf V H).one_mem, Subgroup.one_mem _, fun w _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxn, hxc⟩ ⟨hy, hyn, hyc⟩
        refine ⟨(xOf V H).mul_mem hx hy, Subgroup.mul_mem _ hxn hyn, fun w hw => ?_⟩
        have e : ⁅w, x * y⁆ = ⁅w, x⁆ * (x * ⁅w, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem (hxc w hw) ((Subgroup.mem_normalizer_iff.mp hxn _).mp (hyc w hw))
      inv_mem' := by
        rintro x ⟨hx, hxn, hxc⟩
        refine ⟨(xOf V H).inv_mem hx, Subgroup.inv_mem _ hxn, fun w hw => ?_⟩
        have e : ⁅w, x⁻¹⁆ = x⁻¹ * (⁅w, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxn) _).mp
          (K.inv_mem (hxc w hw))
        simpa [mul_assoc] using h1 }
  have hAT : A ≤ T := by
    intro a ha'
    have haP : a ∈ P := (Subgroup.mem_inf.mp ha').1
    have haH : a ∈ H := hXH (Subgroup.mem_inf.mp ha').2
    refine ⟨(Subgroup.mem_inf.mp ha').2,
      hnorm a (fun y hy => mem_of_conjSubgroup_le (hconjA a ha') hy)
        (fun y hy => mem_of_conjSubgroup_le (hconjA a⁻¹ (A.inv_mem ha')) hy), fun w hw => ?_⟩
    refine Subgroup.mem_sup_left (S := P ⊓ W) (T := B ⊓ W) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have := P.mul_mem (hWP w hw a haP) (P.inv_mem haP)
      simpa [commutatorElement_def] using this
    · have := W.mul_mem hw (hWW a haH w⁻¹ (W.inv_mem hw))
      simpa [commutatorElement_def, mul_assoc] using this
  have hBT : B ≤ T := by
    intro b hb
    have hbH : b ∈ H := hXH (hBX hb)
    refine ⟨hBX hb, hnorm b (fun y hy => mem_of_conjSubgroup_le (hconjB b hb) hy)
      (fun y hy => mem_of_conjSubgroup_le (hconjB b⁻¹ (B.inv_mem hb)) hy), fun w hw => ?_⟩
    refine Subgroup.mem_sup_right (S := P ⊓ W) (T := B ⊓ W) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have := B.mul_mem (hWB w hw b hb) (B.inv_mem hb)
      simpa [commutatorElement_def] using this
    · have := W.mul_mem hw (hWW b hbH w⁻¹ (W.inv_mem hw))
      simpa [commutatorElement_def, mul_assoc] using this
  have hXT : xOf V H ≤ T := by rw [← ha]; exact sup_le hAT hBT
  have hWK : W ≤ K := by
    have h : ⁅W, xOf V H⁆ = W := hc.commutator_wOf_xOf
    rw [← h, Subgroup.commutator_def]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, x, hx, rfl⟩
    exact (hXT hx).2.2 w hw
  refine ⟨le_antisymm hKW hWK, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxP : x ∈ P := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hxB : x ∈ B := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
  have hVN : V ≤ Subgroup.normalizer (B : Set G) := fun u hu =>
    Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g) hxB hx1
      (hc.commute_of_mem_P hxP hu)
  have hB2 : IsPGroup 2 ↥B := hc.isPGroup_V.of_equiv
    (V.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  have hVB : IsPGroup 2 ↥(V ⊔ B) := IsPGroup.to_sup_of_normal_right' hc.isPGroup_V hB2 hVN
  have hW2 : IsPGroup 2 ↥W := CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
    hc.wOf_isElemAbelian
  have hVBH : V ⊔ B ≤ H := sup_le hc.V_le_H (hBX.trans hXH)
  have hVBW : IsPGroup 2 ↥(V ⊔ B ⊔ W) := IsPGroup.to_sup_of_normal_right' hVB hW2
    (fun y hy => H_le_normalizer_wOf V H (hVBH hy))
  obtain ⟨u, hu, w, hw, hnc⟩ := hg
  exact hnc (by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (hc.commute_of_isPGroup_sup_wOf hgH hVBW u hu w hw)]
    exact W.one_mem)

theorem sec25a_of_bar {g : G} (hgX : g ∈ xOf V H)
    (hbar : ∀ x ∈ xOf V H, ∃ y ∈ (P ⊓ xOf V H) ⊔ conjSubgroup g V, ∃ w ∈ wOf V H, x = y * w) :
    (P ⊓ xOf V H) ⊔ conjSubgroup g V = xOf V H := by
  have hXH : xOf V H ≤ H := xOf_le_H hc.V_le_H
  have hgH : g ∈ H := hXH hgX
  obtain ⟨hWP, hWB, hWW⟩ := hc.wOf_conj_facts hgH
  have hBX : conjSubgroup g V ≤ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hgH)
  have hWX : wOf V H ≤ xOf V H := wOf_le_xOf V H
  set Y₀ := (P ⊓ xOf V H) ⊔ conjSubgroup g V with hY₀
  have hY₀X : Y₀ ≤ xOf V H := sup_le inf_le_right hBX
  let T : Subgroup G :=
    { carrier := {y | y ∈ Y₀ ∧ ∀ w ∈ wOf V H, ⁅w, y⁆ ∈ Y₀}
      one_mem' := ⟨Y₀.one_mem, fun w _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
        refine ⟨Y₀.mul_mem hx hy, fun w hw => ?_⟩
        have e : ⁅w, x * y⁆ = ⁅w, x⁆ * (x * ⁅w, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Y₀.mul_mem (hxc w hw) (Y₀.mul_mem (Y₀.mul_mem hx (hyc w hw)) (Y₀.inv_mem hx))
      inv_mem' := by
        rintro x ⟨hx, hxc⟩
        refine ⟨Y₀.inv_mem hx, fun w hw => ?_⟩
        have e : ⁅w, x⁻¹⁆ = x⁻¹ * (⁅w, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem hx) (Y₀.inv_mem (hxc w hw))) hx }
  have hAT : P ⊓ xOf V H ≤ T := by
    intro a ha
    have haP : a ∈ P := (Subgroup.mem_inf.mp ha).1
    have haX : a ∈ xOf V H := (Subgroup.mem_inf.mp ha).2
    refine ⟨Subgroup.mem_sup_left ha, fun w hw => Subgroup.mem_sup_left ?_⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := P.mul_mem (hWP w hw a haP) (P.inv_mem haP)
      simpa [commutatorElement_def] using this
    · have hwX : w ∈ xOf V H := hWX hw
      simpa [commutatorElement_def] using (xOf V H).mul_mem
        ((xOf V H).mul_mem ((xOf V H).mul_mem hwX haX) ((xOf V H).inv_mem hwX))
        ((xOf V H).inv_mem haX)
  have hBT : conjSubgroup g V ≤ T := by
    intro b hb
    refine ⟨Subgroup.mem_sup_right hb, fun w hw => Subgroup.mem_sup_right ?_⟩
    have := (conjSubgroup g V).mul_mem (hWB w hw b hb) ((conjSubgroup g V).inv_mem hb)
    simpa [commutatorElement_def] using this
  have hY₀T : Y₀ ≤ T := sup_le hAT hBT
  have hWY : wOf V H ≤ Y₀ := by
    have h : ⁅wOf V H, xOf V H⁆ = wOf V H := hc.commutator_wOf_xOf
    rw [← h, Subgroup.commutator_def]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, x, hx, rfl⟩
    obtain ⟨y, hy, w', hw', rfl⟩ := hbar x hx
    have e : ⁅w, y * w'⁆ = ⁅w, y⁆ * (y * ⁅w, w'⁆ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    have hww : ⁅w, w'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hc.wOf_isElemAbelian.comm hw hw')
    rw [e, hww]
    simpa using (hY₀T hy).2 w hw
  refine le_antisymm hY₀X (fun x hx => ?_)
  obtain ⟨y, hy, w, hw, rfl⟩ := hbar x hx
  exact Y₀.mul_mem hy (hWY hw)

end MinCex

end CFSG.RankThree.GF2n.Tim79a
