module

public import CFSG.RankThree.GF2n.Tim79aSec25
public import CFSG.RankThree.GF2n.Tim79aSec23MinGrp

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem exists_conj_ne : ∃ g ∈ H, conjSubgroup g V ≠ V := by
  by_contra hcon
  push Not at hcon
  have hnorm : H ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_iff_conjSubgroup_eq.mpr (hcon g hg)
  exact hc.notLe (Tim78.le_inSubgroup_pCore hc.V_le_H hnorm hc.isPGroup_V)

theorem not_isPGroup_barOf_sup_of_case_one
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup g V ≠ V) :
    ¬ IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup g V)) := by
  intro h2
  haveI := normal_oddCoreX V H
  have hle : barOf V H (conjSubgroup g V) ≤ barOf V H V := by
    intro y hy
    have hyX : y ∈ barOf V H (xOf V H) :=
      barOf_mono (le_xOf (conjSubgroup_mem_omegaOf hg)) hy
    rw [hX] at hyX
    obtain ⟨o, ho, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hyX
    have hoK : o ∈ barOf V H V ⊔ barOf V H (conjSubgroup g V) := by
      have : o = (o * u) * u⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hu))
    have hodd : Odd (orderOf o) := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : ↥(oddCoreX V H))
      rw [Subgroup.orderOf_mk] at this
      exact (odd_card_oddCoreX V H).of_dvd_nat this
    have ho1 : o = 1 := Tim78.eq_one_of_odd_of_isPGroup h2 hoK hodd
    rw [ho1, one_mul]
    exact hu
  have hconj : conjSubgroup (piBar V H ⟨g, hg⟩) (barOf V H V) =
      barOf V H (conjSubgroup g V) := conjSubgroup_piBar_barOf ⟨g, hg⟩ V
  have hne' : barOf V H V ⊓ conjSubgroup (piBar V H ⟨g, hg⟩) (barOf V H V) ≠ ⊥ := by
    rw [hconj, inf_eq_right.mpr hle, ← hconj]
    intro hbot
    have : (barOf V H V).map (MulAut.conj (piBar V H ⟨g, hg⟩)).toMonoidHom = ⊥ := hbot
    exact hc.barOf_V_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp this)
  exact hne (mem_normalizer_iff_conjSubgroup_eq.mp (hc.mem_normalizer_of_inf_ne_bot hg hne'))

theorem sup_eq_H_of_case_one
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup g V ≠ V) : P ⊔ conjSubgroup g V = H :=
  hc.sup_eq_H_of_not_isPGroup hg (hc.not_isPGroup_barOf_sup_of_case_one hX hg hne)

theorem isPGroup_barOf_sup_of_le_normalizer {g : G} (hg : g ∈ H)
    (hVN : V ≤ Subgroup.normalizer (conjSubgroup g V : Set G)) :
    IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup g V)) := by
  have hBX : conjSubgroup g V ≤ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hg)
  have hXH : xOf V H ≤ H := xOf_le_H hc.V_le_H
  have hB2 : IsPGroup 2 ↥(conjSubgroup g V) := hc.isPGroup_V.of_equiv
    (V.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  have hVB : IsPGroup 2 ↥(V ⊔ conjSubgroup g V) :=
    IsPGroup.to_sup_of_normal_right' hc.isPGroup_V hB2 hVN
  have hW2 : IsPGroup 2 ↥(wOf V H) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian
  have hVBH : V ⊔ conjSubgroup g V ≤ H := sup_le hc.V_le_H (hBX.trans hXH)
  have hVBW : IsPGroup 2 ↥(V ⊔ conjSubgroup g V ⊔ wOf V H) :=
    IsPGroup.to_sup_of_normal_right' hVB hW2 (fun y hy => H_le_normalizer_wOf V H (hVBH hy))
  exact (hc.isPGroup_barOf_sup_iff hg).2 hVBW

theorem wOf_eq_mul_of_case_one
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup g V ≠ V) :
    (∀ w ∈ wOf V H, ∃ e ∈ P ⊓ wOf V H, ∃ b ∈ conjSubgroup g V ⊓ wOf V H, w = e * b) ∧
      (P ⊓ wOf V H) ⊓ (conjSubgroup g V ⊓ wOf V H) = ⊥ := by
  have hsup : P ⊔ conjSubgroup g V = H := hc.sup_eq_H_of_case_one hX hg hne
  have hXH : xOf V H ≤ H := xOf_le_H hc.V_le_H
  obtain ⟨hWP, hWB, hWW⟩ := hc.wOf_conj_facts hg
  have hBH : conjSubgroup g V ≤ H := (le_xOf (conjSubgroup_mem_omegaOf hg)).trans hXH
  set B := conjSubgroup g V with hB
  set W := wOf V H with hW
  set K := (P ⊓ W) ⊔ (B ⊓ W) with hK
  have hKW : K ≤ W := sup_le inf_le_right inf_le_right
  have hconjA : ∀ a ∈ P, conjSubgroup a K ≤ K := by
    intro a haP
    have haH : a ∈ H := hc.PleH haP
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
    have hbH : b ∈ H := hBH hb
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
    { carrier := {x | x ∈ H ∧ x ∈ Subgroup.normalizer (K : Set G) ∧ ∀ w ∈ W, ⁅w, x⁆ ∈ K}
      one_mem' := ⟨H.one_mem, Subgroup.one_mem _, fun w _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxn, hxc⟩ ⟨hy, hyn, hyc⟩
        refine ⟨H.mul_mem hx hy, Subgroup.mul_mem _ hxn hyn, fun w hw => ?_⟩
        have e : ⁅w, x * y⁆ = ⁅w, x⁆ * (x * ⁅w, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem (hxc w hw) ((Subgroup.mem_normalizer_iff.mp hxn _).mp (hyc w hw))
      inv_mem' := by
        rintro x ⟨hx, hxn, hxc⟩
        refine ⟨H.inv_mem hx, Subgroup.inv_mem _ hxn, fun w hw => ?_⟩
        have e : ⁅w, x⁻¹⁆ = x⁻¹ * (⁅w, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxn) _).mp
          (K.inv_mem (hxc w hw))
        simpa [mul_assoc] using h1 }
  have hPT : P ≤ T := by
    intro a haP
    have haH : a ∈ H := hc.PleH haP
    refine ⟨haH, hnorm a (fun y hy => mem_of_conjSubgroup_le (hconjA a haP) hy)
        (fun y hy => mem_of_conjSubgroup_le (hconjA a⁻¹ (P.inv_mem haP)) hy), fun w hw => ?_⟩
    refine Subgroup.mem_sup_left (S := P ⊓ W) (T := B ⊓ W) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have := P.mul_mem (hWP w hw a haP) (P.inv_mem haP)
      simpa [commutatorElement_def] using this
    · have := W.mul_mem hw (hWW a haH w⁻¹ (W.inv_mem hw))
      simpa [commutatorElement_def, mul_assoc] using this
  have hBT : B ≤ T := by
    intro b hb
    have hbH : b ∈ H := hBH hb
    refine ⟨hbH, hnorm b (fun y hy => mem_of_conjSubgroup_le (hconjB b hb) hy)
      (fun y hy => mem_of_conjSubgroup_le (hconjB b⁻¹ (B.inv_mem hb)) hy), fun w hw => ?_⟩
    refine Subgroup.mem_sup_right (S := P ⊓ W) (T := B ⊓ W) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have := B.mul_mem (hWB w hw b hb) (B.inv_mem hb)
      simpa [commutatorElement_def] using this
    · have := W.mul_mem hw (hWW b hbH w⁻¹ (W.inv_mem hw))
      simpa [commutatorElement_def, mul_assoc] using this
  have hHT : H ≤ T := by rw [← hsup]; exact sup_le hPT hBT
  have hWK : W ≤ K := by
    have h : ⁅W, xOf V H⁆ = W := hc.commutator_wOf_xOf
    rw [← h, Subgroup.commutator_def]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, x, hx, rfl⟩
    exact (hHT (hXH hx)).2.2 w hw
  have hBN : B ⊓ W ≤ Subgroup.normalizer ((P ⊓ W : Subgroup G) : Set G) :=
    le_normalizer_of_comm fun x hx y hy => hc.wOf_isElemAbelian.comm hx.2 hy.2
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨e, he, b, hb, hwe⟩ := exists_mul_of_mem_sup hBN (hWK hw)
    exact ⟨e, he, b, hb, hwe⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxP : x ∈ P := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
    have hxB : x ∈ B := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
    exact hc.not_isPGroup_barOf_sup_of_case_one hX hg hne
      (hc.isPGroup_barOf_sup_of_le_normalizer hg fun u hu =>
        Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g) hxB hx1
          (hc.commute_of_mem_P hxP hu))

theorem not_commute_of_case_one (hq : Nat.card (barOf V H V) = 2)
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup g V ≠ V) {v : G} (hv : v ∈ V) (hvW : v ∉ wOf V H) {b : G}
    (hb : b ∈ conjSubgroup g V) (hb1 : b ≠ 1) : v * b ≠ b * v := by
  intro hcomm
  have hvN : v ∈ Subgroup.normalizer (conjSubgroup g V : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g) hb hb1 hcomm
  have hWN : wOf V H ≤ Subgroup.normalizer (conjSubgroup g V : Set G) := fun w hw =>
    hc.pCoreH_le_normalizer_conj hg (wOf_le_pCore V H hw)
  have hVN : V ≤ Subgroup.normalizer (conjSubgroup g V : Set G) := by
    intro u hu
    by_cases huW : u ∈ wOf V H
    · exact hWN huW
    · have hvH : v ∈ H := hc.V_le_H hv
      have huH : u ∈ H := hc.V_le_H hu
      have hv1 : piBar V H ⟨v, hvH⟩ ≠ 1 := fun h => hvW ((piBar_eq_one_iff _).1 h)
      have hu1 : piBar V H ⟨u, huH⟩ ≠ 1 := fun h => huW ((piBar_eq_one_iff _).1 h)
      have hvm : piBar V H ⟨v, hvH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hv, rfl⟩
      have hum : piBar V H ⟨u, huH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hu, rfl⟩
      obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(barOf V H V))).mp hq
      have heq : piBar V H ⟨u, huH⟩ = piBar V H ⟨v, hvH⟩ := by
        have h1 := hyuniq ⟨_, hum⟩ (fun h => hu1 (congrArg Subtype.val h))
        have h2 := hyuniq ⟨_, hvm⟩ (fun h => hv1 (congrArg Subtype.val h))
        exact congrArg Subtype.val (h1.trans h2.symm)
      have hvuW : v⁻¹ * u ∈ wOf V H := by
        have : piBar V H ((⟨v, hvH⟩ : ↥H)⁻¹ * ⟨u, huH⟩) = 1 := by
          rw [map_mul, map_inv, heq]; simp
        simpa using (piBar_eq_one_iff _).1 this
      have hu' : u = v * (v⁻¹ * u) := by group
      rw [hu']
      exact Subgroup.mul_mem _ hvN (hWN hvuW)
  exact hc.not_isPGroup_barOf_sup_of_case_one hX hg hne
    (hc.isPGroup_barOf_sup_of_le_normalizer hg hVN)

theorem mem_P_of_commute_of_case_one (hq : Nat.card (barOf V H V) = 2)
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) :
    ∀ v ∈ V, v ∉ wOf V H → ∀ w ∈ wOf V H, v * w = w * v → w ∈ P := by
  intro v hv hvW w hw hvw
  obtain ⟨g, hg, hne⟩ := hc.exists_conj_ne
  obtain ⟨e, he, b, hb, rfl⟩ := (hc.wOf_eq_mul_of_case_one hX hg hne).1 w hw
  have heP : e ∈ P := (Subgroup.mem_inf.mp he).1
  have hve : v * e = e * v := hc.commute_of_mem_P heP hv
  have hvb : v * b = b * v := by
    apply mul_left_cancel (a := e)
    calc e * (v * b) = (e * v) * b := by rw [mul_assoc]
      _ = (v * e) * b := by rw [hve]
      _ = v * (e * b) := by rw [mul_assoc]
      _ = (e * b) * v := hvw
      _ = e * (b * v) := by rw [mul_assoc]
  have hb1 : b = 1 := by
    by_contra hb1
    exact hc.not_commute_of_case_one hq hX hg hne hv hvW (Subgroup.mem_inf.mp hb).1 hb1 hvb
  rw [hb1, mul_one]
  exact heP

theorem mem_wOf_of_centralizes (hq : Nat.card (barOf V H V) = 2) {v : G} (hv : v ∈ V)
    (hvc : ∀ w ∈ wOf V H, v * w = w * v) : v ∈ wOf V H := by
  by_contra hvW
  have hVc : ∀ u ∈ V, ∀ w ∈ wOf V H, u * w = w * u := by
    intro u hu w hw
    by_cases huW : u ∈ wOf V H
    · exact hc.wOf_isElemAbelian.comm huW hw
    · have huH : u ∈ H := hc.V_le_H hu
      have hvH : v ∈ H := hc.V_le_H hv
      have hu1 : piBar V H ⟨u, huH⟩ ≠ 1 := fun h => huW ((piBar_eq_one_iff _).1 h)
      have hv1 : piBar V H ⟨v, hvH⟩ ≠ 1 := fun h => hvW ((piBar_eq_one_iff _).1 h)
      have hum : piBar V H ⟨u, huH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hu, rfl⟩
      have hvm : piBar V H ⟨v, hvH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hv, rfl⟩
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(barOf V H V))).1 hq
      have h1 : (⟨piBar V H ⟨u, huH⟩, hum⟩ : ↥(barOf V H V)) = y :=
        hy _ (fun h => hu1 (congrArg Subtype.val h))
      have h2 : (⟨piBar V H ⟨v, hvH⟩, hvm⟩ : ↥(barOf V H V)) = y :=
        hy _ (fun h => hv1 (congrArg Subtype.val h))
      have h3 : piBar V H ⟨u, huH⟩ = piBar V H ⟨v, hvH⟩ :=
        congrArg Subtype.val (h1.trans h2.symm)
      have h4 : v⁻¹ * u ∈ wOf V H := by
        have : piBar V H ((⟨v, hvH⟩ : ↥H)⁻¹ * ⟨u, huH⟩) = 1 := by
          rw [map_mul, map_inv, h3]; simp
        exact (piBar_eq_one_iff _).1 this
      have hcomm : (v⁻¹ * u) * w = w * (v⁻¹ * u) := hc.wOf_isElemAbelian.comm h4 hw
      calc u * w = v * ((v⁻¹ * u) * w) := by group
        _ = v * (w * (v⁻¹ * u)) := by rw [hcomm]
        _ = (v * w) * (v⁻¹ * u) := by group
        _ = (w * v) * (v⁻¹ * u) := by rw [hvc w hw]
        _ = w * u := by group
  have hXc : xOf V H ≤ Subgroup.centralizer (wOf V H : Set G) := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    intro u' hu'
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hu₀ : h⁻¹ * u' * h ∈ V := mem_conjSubgroup.mp hu'
    have hw₀ : h⁻¹ * w * h ∈ wOf V H := by
      simpa using (hc.wOf_conj_facts hh).2.2 h⁻¹ (H.inv_mem hh) w hw
    calc w * u' = h * ((h⁻¹ * w * h) * (h⁻¹ * u' * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * u' * h) * (h⁻¹ * w * h)) * h⁻¹ := by rw [← hVc _ hu₀ _ hw₀]
      _ = u' * w := by group
  have hWle : wOf V H ≤ wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) := by
    refine le_inf le_rfl fun w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hXc hy) w hw).symm
  rw [hc.wOf_inf_centralizer_xOf_eq_bot, le_bot_iff] at hWle
  apply hc.V_inf_wOf_ne_bot
  rw [hWle, inf_bot_eq]

theorem commutator_mem_wOf_of_centralizes (hq : Nat.card (barOf V H V) = 2) {c : G}
    (hcH : c ∈ H) (hcW : ∀ w ∈ wOf V H, c * w = w * c) :
    ∀ y ∈ xOf V H, ⁅c, y⁆ ∈ wOf V H := by
  have hcZ : c ∈ Subgroup.centralizer (wOf V H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun w hw => (hcW w hw).symm
  have hVC : ∀ h ∈ H, ∀ y ∈ conjSubgroup h V, ⁅c, y⁆ ∈ wOf V H := by
    intro h hh y hy
    have hyH : y ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hh hy
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.conj_inf_wOf_ne_bot hh)
    obtain ⟨hbB, hbW⟩ := Subgroup.mem_inf.mp hb
    have hcN : c ∈ Subgroup.normalizer (conjSubgroup h V : Set G) :=
      Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti h) hbB
        (fun h' => hb1 (Subtype.ext h')) (hcW b hbW)
    have hzB : ⁅c, y⁆ ∈ conjSubgroup h V :=
      (conjSubgroup h V).mul_mem ((Subgroup.mem_normalizer_iff.mp hcN y).mp hy)
        ((conjSubgroup h V).inv_mem hy)
    have hzZ : ⁅c, y⁆ ∈ Subgroup.centralizer (wOf V H : Set G) := by
      have hyN : y ∈ Subgroup.normalizer
          (Subgroup.centralizer (wOf V H : Set G) : Set G) :=
        mem_normalizer_centralizer (H_le_normalizer_wOf V H hyH)
      have h2 : y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (wOf V H : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hyN _).mp (Subgroup.inv_mem _ hcZ)
      have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hcZ h2
    generalize ⁅c, y⁆ = z at hzB hzZ ⊢
    have hu : h⁻¹ * z * h ∈ V := mem_conjSubgroup.mp hzB
    have hu' : h⁻¹ * z * h ∈ wOf V H := by
      refine hc.mem_wOf_of_centralizes hq hu fun w hw => ?_
      have hw₀ : h * w * h⁻¹ ∈ wOf V H := (hc.wOf_conj_facts hh).2.2 h hh w hw
      have hcomm := Subgroup.mem_centralizer_iff.mp hzZ _ hw₀
      calc h⁻¹ * z * h * w = h⁻¹ * (z * (h * w * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * w * h⁻¹) * z) * h := by rw [hcomm]
        _ = w * (h⁻¹ * z * h) := by group
    have := (hc.wOf_conj_facts hh).2.2 h hh _ hu'
    have e : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
    rwa [e] at this
  let C : Subgroup ↥H :=
    (Subgroup.centralizer ({piBar V H ⟨c, hcH⟩} : Set (Hbar V H))).comap (piBar V H)
  have hCmem : ∀ y : ↥H, y ∈ C ↔ ⁅c, (y : G)⁆ ∈ wOf V H := by
    intro y
    have h1 : piBar V H ⁅(⟨c, hcH⟩ : ↥H), y⁆ = ⁅piBar V H ⟨c, hcH⟩, piBar V H y⁆ :=
      map_commutatorElement _ _ _
    have h2 : ((⁅(⟨c, hcH⟩ : ↥H), y⁆ : ↥H) : G) = ⁅c, (y : G)⁆ := rfl
    rw [← h2, ← piBar_eq_one_iff, h1, commutatorElement_eq_one_iff_mul_comm,
      Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hXC : xOf V H ≤ C.map H.subtype := iSup₂_le fun U hU => by
    obtain ⟨h, hh, rfl⟩ := hU
    intro y hy
    have hyH : y ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hh hy
    exact ⟨⟨y, hyH⟩, (hCmem _).2 (hVC h hh y hy), rfl⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hXC hy
  exact (hCmem y').1 hy'

theorem centralizes_of_act_eq
    (hA3 : ∀ g ∈ H, conjSubgroup g V ≠ V →
      ((∀ w ∈ wOf V H, ∃ e ∈ P ⊓ wOf V H, ∃ b ∈ conjSubgroup g V ⊓ wOf V H, w = e * b) ∧
        (P ⊓ wOf V H) ⊓ (conjSubgroup g V ⊓ wOf V H) = ⊥))
    {g x y : G} (hg : g ∈ H) (hne : conjSubgroup g V ≠ V) (hx : x ∈ P)
    (hy : y ∈ conjSubgroup g P) (hxy : ∀ w ∈ wOf V H, x * w * x⁻¹ = y * w * y⁻¹) :
    ∀ w ∈ wOf V H, x * w = w * x := by
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hcomm_le : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ V := by
    intro a ha b hb
    have h := CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2)
    have hmem : (⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ : ↥P) ∈ frattini ↥P :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact hc.frattini_P_le ⟨_, hmem, by simp [commutatorElement_def]⟩
  have hα := (hA3 g hg hne).1
  have hne' : conjSubgroup g⁻¹ V ≠ V := by
    intro h
    apply hne
    calc conjSubgroup g V = conjSubgroup g (conjSubgroup g⁻¹ V) := by rw [h]
      _ = V := by rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hβ := (hA3 g⁻¹ (H.inv_mem hg) hne').1
  have hW3 := (hc.wOf_conj_facts hg).2.2
  have hβ' : ∀ w ∈ wOf V H,
      ∃ e ∈ conjSubgroup g P ⊓ wOf V H, ∃ a ∈ V ⊓ wOf V H, w = e * a := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ wOf V H := by
      simpa using hW3 g⁻¹ (H.inv_mem hg) w hw
    obtain ⟨e, he, b, hb, hwe⟩ := hβ _ hw'
    refine ⟨g * e * g⁻¹, Subgroup.mem_inf.mpr ⟨?_, hW3 g hg e (Subgroup.mem_inf.mp he).2⟩,
      g * b * g⁻¹, Subgroup.mem_inf.mpr ⟨?_, hW3 g hg b (Subgroup.mem_inf.mp hb).2⟩, ?_⟩
    · rw [mem_conjSubgroup]
      have e1 : g⁻¹ * (g * e * g⁻¹) * g = e := by group
      rw [e1]
      exact (Subgroup.mem_inf.mp he).1
    · simpa using mem_conjSubgroup.mp (Subgroup.mem_inf.mp hb).1
    · calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = g * (e * b) * g⁻¹ := by rw [hwe]
        _ = (g * e * g⁻¹) * (g * b * g⁻¹) := by group
  intro w hw
  obtain ⟨e, he, b, hb, rfl⟩ := hα w hw
  obtain ⟨e', he', a, ha, hea⟩ := hβ' e (Subgroup.mem_inf.mp he).2
  have haV : a ∈ V := (Subgroup.mem_inf.mp ha).1
  have he'P : e' ∈ P := by
    have h1 : e' = e * a⁻¹ := by rw [hea]; group
    rw [h1]
    exact P.mul_mem (Subgroup.mem_inf.mp he).1 (P.inv_mem (hc.V_le_P haV))
  have hxa : x * a = a * x := (hc.commute_of_mem_P hx haV).symm
  have hxb : x * b = b * x := by
    have hbB : b ∈ conjSubgroup g V := (Subgroup.mem_inf.mp hb).1
    have hyb : y * b = b * y := by
      have := hc.commute_of_mem_P (mem_conjSubgroup.mp hy) (mem_conjSubgroup.mp hbB)
      calc y * b = g * ((g⁻¹ * y * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = b * y := by group
    have h1 := hxy b (Subgroup.mem_inf.mp hb).2
    have h2 : y * b * y⁻¹ = b := by rw [hyb]; group
    rw [h2] at h1
    calc x * b = x * b * x⁻¹ * x := by group
      _ = b * x := by rw [h1]
  have hxe : x * e' = e' * x := by
    have he'W : e' ∈ wOf V H := (Subgroup.mem_inf.mp he').2
    have he'g : e' ∈ conjSubgroup g P := (Subgroup.mem_inf.mp he').1
    have hV1 : ⁅x, e'⁆ ∈ V := hcomm_le x hx e' he'P
    have hV2 : ⁅x, e'⁆ ∈ conjSubgroup g V := by
      have e1 : ⁅x, e'⁆ = ⁅y, e'⁆ := by
        simp only [commutatorElement_def]; rw [hxy e' he'W]
      rw [e1, mem_conjSubgroup]
      have e2 : g⁻¹ * ⁅y, e'⁆ * g = ⁅g⁻¹ * y * g, g⁻¹ * e' * g⁆ := by
        simp only [commutatorElement_def]; group
      rw [e2]
      exact hcomm_le _ (mem_conjSubgroup.mp hy) _ (mem_conjSubgroup.mp he'g)
    have hmem : ⁅x, e'⁆ ∈ V ⊓ conjSubgroup g V := ⟨hV1, hV2⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI hc.ti hne, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  subst hea
  exact (Commute.mul_right (Commute.mul_right hxe hxa) hxb).eq

end MinCex

end CFSG.RankThree.GF2n.Tim79a
