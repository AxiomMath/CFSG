module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VOmega6
import CFSG.RankThree.PartTwo.Sec14.Ronan148VJ2Syl
import CFSG.RankThree.PartTwo.Sec14.Ronan148VA5Inner
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148

variable {G : Type} [Group G] [Finite G]

section Count


theorem exists_normalizer_conj_of_j2_factor {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) [(ker148 A Y).Normal]
    {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hP : Nonempty (↥P ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAP : img148 A Y A ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {z t : G} (hzA : z ∈ A) (htA : t ∈ A) (hzP : alpha148 A Y z hzA ∈ P) (hz1 : z ≠ 1)
    (h27 : 27 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {alpha148 A Y z hzA}))
    (htP : alpha148 A Y t htA ∈ P) (htz : t ∉ Subgroup.zpowers z) :
    ∃ w : G, w ∈ Subgroup.normalizer (A : Set G) ∧ w * z * w⁻¹ = z ∧
      (w * t * w⁻¹ = z * t ∨ w * t * w⁻¹ = z ^ 2 * t) := by
  classical
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAq3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hAY hw hw3
  obtain ⟨φ⟩ := hP
  have hPc : Subgroup.center ↥P = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φ⟩
  have hPP : P ⊓ Subgroup.centralizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥P) ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hPc, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hCD := Ronan148J.sup_eq_of_forall_inner hAab hAq3 hF3 hPP hAP
    (fun a ha => Ronan148J.exists_inner_of_j2 φ (hAP ha) (hAq3 a ha))
  set zα := alpha148 A Y z hzA with hzαdef
  set tα := alpha148 A Y t htA with htαdef
  have hzαA : zα ∈ img148 A Y A := alpha148_mem_img148 hzA
  have htαA : tα ∈ img148 A Y A := alpha148_mem_img148 htA
  have hzα3 : zα ^ 3 = 1 := hAq3 _ hzαA
  have htα3 : tα ^ 3 = 1 := hAq3 _ htαA
  have hzα1 : zα ≠ 1 := fun h =>
    hz1 (alpha148_injective hA3 hzA A.one_mem (h.trans alpha148_one'.symm))
  have htzα : tα ∉ Subgroup.zpowers zα := by
    intro h
    apply htz
    rcases inner_a5_mem_zpowers hzα3 h with h1 | h1 | h1
    · rw [alpha148_injective hA3 htA A.one_mem (h1.trans alpha148_one'.symm)]
      exact one_mem _
    · rw [alpha148_injective hA3 htA hzA h1]
      exact Subgroup.mem_zpowers z
    · rw [alpha148_injective hA3 htA (A.inv_mem hzA) (h1.trans (alpha148_inv hzA).symm)]
      exact inv_mem (Subgroup.mem_zpowers z)
  have hzt : zα * tα = tα * zα := hAab _ hzαA _ htαA
  have h9 : Nat.card ↥(Subgroup.zpowers zα ⊔ Subgroup.zpowers tα) = 9 :=
    Ronan148J.card_zpowers_sup_zpowers_eq_nine hzt hzα3 hzα1 htα3 htzα
  have hle9 : Nat.card ↥(img148 A Y A ⊓ P) ≤ 9 := by
    set F : Subgroup ↥P := (img148 A Y A ⊓ P).subgroupOf P with hF
    have hFc : Nat.card F = Nat.card ↥(img148 A Y A ⊓ P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hFE : CFSG.Assembly.IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
      · have hx := Subgroup.mem_subgroupOf.mp x.2
        have hy := Subgroup.mem_subgroupOf.mp y.2
        exact hAab _ hx.1 _ hy.1
      · have hx' := Subgroup.mem_subgroupOf.mp hx
        exact Subtype.ext (by simpa using hAq3 _ hx'.1)
    rw [← hFc]
    exact Sec15.Proof15Res8Diag.card_le_nine_of_j2 φ hFE
  have hsub : Subgroup.zpowers zα ⊔ Subgroup.zpowers tα ≤ img148 A Y A ⊓ P :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hzαA, hzP⟩) (Subgroup.zpowers_le.mpr ⟨htαA, htP⟩)
  have hAPeq : img148 A Y A ⊓ P = Subgroup.zpowers zα ⊔ Subgroup.zpowers tα :=
    (Subgroup.eq_of_le_of_card_ge hsub (by rw [h9]; exact hle9)).symm
  have h27' : 27 ∣ Nat.card (Subgroup.centralizer ({⟨zα, hzP⟩} : Set ↥P)) := by
    rw [card_centralizer_subtype_eq]
    exact h27
  have hcnd : (⟨tα, htP⟩ : ↥P) ∉ Subgroup.zpowers (⟨zα, hzP⟩ : ↥P) := by
    intro h
    apply htzα
    have h' := Subgroup.mem_map_of_mem P.subtype h
    rwa [MonoidHom.map_zpowers] at h'
  obtain ⟨y, hyz, hyt⟩ := exists_conj_eq_mul_of_j2 ⟨φ⟩ (d := ⟨zα, hzP⟩) (c := ⟨tα, htP⟩)
    (fun h => hzα1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hzα3)) h27'
    (Subtype.ext (by simpa using htα3)) (Subtype.ext hzt.symm) hcnd
  have hyz' : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * zα = zα * y := by
    simpa using congrArg Subtype.val hyz
  have hyt' : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * tα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = zα * tα ∨
      (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * tα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = zα ^ 2 * tα := by
    rcases hyt with h | h
    · left
      simpa using congrArg Subtype.val h
    · right
      simpa using congrArg Subtype.val h
  have hyzc : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * zα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = zα := by
    rw [hyz', mul_inv_cancel_right]
  have hyA : ∀ a ∈ img148 A Y A,
      (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * a * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ ∈ img148 A Y A := by
    have h2 : Subgroup.zpowers zα ⊔ Subgroup.zpowers tα ≤ (img148 A Y A).comap
        (MulAut.conj (y : ↥(Y ⊔ A) ⧸ ker148 A Y)).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        simpa [MulAut.conj_apply, hyzc] using hzαA
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        have hm : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * tα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ ∈
            img148 A Y A := by
          rcases hyt' with h | h
          · rw [h]
            exact mul_mem hzαA htαA
          · rw [h]
            exact mul_mem (pow_mem hzαA 2) htαA
        simpa [MulAut.conj_apply] using hm
    rw [← hAPeq] at h2
    have hle : img148 A Y A ⊓ Subgroup.centralizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
        img148 A Y A ⊓ P ≤ (img148 A Y A).comap
          (MulAut.conj (y : ↥(Y ⊔ A) ⧸ ker148 A Y)).toMonoidHom := by
      refine sup_le (fun a ha => ?_) h2
      rw [Subgroup.mem_comap]
      have hya : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * a = a * y :=
        Subgroup.mem_centralizer_iff.mp ha.2 _ y.2
      have : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * a * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = a := by
        rw [hya, mul_inv_cancel_right]
      simpa [MulAut.conj_apply, this] using ha.1
    rw [hCD] at hle
    intro a ha
    simpa [MulAut.conj_apply] using hle ha
  have hyN : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈
      Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    Item148HJ.mem_normalizer_of_conj_mem hyA
  obtain ⟨w, hwN, hwy⟩ := exists_normalizer_lift148 hAp hyN
  have hwA : ∀ a ∈ A, (w : G) * a * (w : G)⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hwN a).mp ha
  have hz2A : z ^ 2 ∈ A := pow_mem hzA 2
  refine ⟨w, hwN, ?_, ?_⟩
  · refine alpha148_injective (Y := Y) hA3 (hwA z hzA) hzA ?_
    rw [alpha148_conj w hzA, hwy]
    exact hyzc
  · rcases hyt' with h | h
    · left
      refine alpha148_injective (Y := Y) hA3 (hwA t htA) (A.mul_mem hzA htA) ?_
      rw [alpha148_conj w htA, hwy, alpha148_mul hzA htA]
      exact h
    · right
      refine alpha148_injective (Y := Y) hA3 (hwA t htA) (A.mul_mem hz2A htA) ?_
      rw [alpha148_conj w htA, hwy, alpha148_mul hz2A htA, alpha148_pow hzA]
      exact h

theorem dvd_card_centralizer_of_normalizer_le {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    [(ker148 A Y).Normal] {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hP : Nonempty (↥P ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAP : img148 A Y A ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {δ u : G} (hδA : δ ∈ A) (huA : u ∈ A) (hδP : alpha148 A Y δ hδA ∈ P) (hδ1 : δ ≠ 1)
    (huP : alpha148 A Y u huA ∈ P) (huδ : u ∉ Subgroup.zpowers δ)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers δ : Set G)) :
    27 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {alpha148 A Y δ hδA}) := by
  classical
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAq3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  obtain ⟨φ⟩ := hP
  set δα := alpha148 A Y δ hδA with hδαdef
  set uα := alpha148 A Y u huA with huαdef
  have hδαA : δα ∈ img148 A Y A := alpha148_mem_img148 hδA
  have huαA : uα ∈ img148 A Y A := alpha148_mem_img148 huA
  have hδα3 : δα ^ 3 = 1 := hAq3 _ hδαA
  have huα3 : uα ^ 3 = 1 := hAq3 _ huαA
  have hδα1 : δα ≠ 1 := fun h =>
    hδ1 (alpha148_injective hA3 hδA A.one_mem (h.trans alpha148_one'.symm))
  have huδα : uα ∉ Subgroup.zpowers δα := by
    intro h
    apply huδ
    rcases inner_a5_mem_zpowers hδα3 h with h1 | h1 | h1
    · rw [alpha148_injective hA3 huA A.one_mem (h1.trans alpha148_one'.symm)]
      exact one_mem _
    · rw [alpha148_injective hA3 huA hδA h1]
      exact Subgroup.mem_zpowers δ
    · rw [alpha148_injective hA3 huA (A.inv_mem hδA) (h1.trans (alpha148_inv hδA).symm)]
      exact inv_mem (Subgroup.mem_zpowers δ)
  have hδu : δα * uα = uα * δα := hAab _ hδαA _ huαA
  set δ' : ↥P := ⟨δα, hδP⟩ with hδ'
  set u' : ↥P := ⟨uα, huP⟩ with hu'
  have hδ'1 : δ' ≠ 1 := fun h => hδα1 (congrArg Subtype.val h)
  have hδ'3 : δ' ^ 3 = 1 := Subtype.ext (by simpa using hδα3)
  have hu'3 : u' ^ 3 = 1 := Subtype.ext (by simpa using huα3)
  have hδu' : u' * δ' = δ' * u' := Subtype.ext hδu.symm
  have hu'δ' : u' ∉ Subgroup.zpowers δ' := by
    intro h
    apply huδα
    have h' := Subgroup.mem_map_of_mem P.subtype h
    rwa [MonoidHom.map_zpowers] at h'
  have hB9 : Nat.card ↥(Subgroup.zpowers δ' ⊔ Subgroup.zpowers u') = 9 :=
    Ronan148J.card_zpowers_sup_zpowers_eq_nine hδu'.symm hδ'3 hδ'1 hu'3 hu'δ'
  obtain ⟨S, hBS⟩ := j2Syl_exists_sylow hB9
  obtain ⟨⟨hH, -⟩, -⟩ := h415 ↥P ⟨φ⟩ S _ rfl _ rfl
  obtain ⟨hExt, hS27, -⟩ := hH
  obtain ⟨-, -, -, hZ3⟩ := hExt
  have hZne : Subgroup.center ↥(S : Subgroup ↥P) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  set z : ↥P := ((z₀ : ↥(S : Subgroup ↥P)) : ↥P) with hz
  have hzS : z ∈ (S : Subgroup ↥P) := (z₀ : ↥(S : Subgroup ↥P)).2
  have hz1 : z ≠ 1 := fun h => hz₀1 (Subtype.ext (Subtype.ext h))
  have hzZ : z ∈ (S : Subgroup ↥P) ⊓ Subgroup.centralizer ((S : Subgroup ↥P) : Set ↥P) := by
    refine ⟨hzS, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hc := Subgroup.mem_center_iff.mp z₀.2 ⟨h, hh⟩
    exact congrArg Subtype.val hc
  have hzC : (S : Subgroup ↥P) ≤ Subgroup.centralizer ({z} : Set ↥P) := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzZ.2 h hh
  have h27z : 27 ∣ Nat.card (Subgroup.centralizer ({z} : Set ↥P)) := by
    rw [← hS27]
    exact Subgroup.card_dvd_of_le hzC
  have hz3 : z ^ 3 = 1 := by
    have h := orderOf_dvd_natCard z₀
    rw [hZ3] at h
    have h0 : z₀ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    calc z ^ 3 = (((z₀ ^ 3 : ↥(Subgroup.center ↥(S : Subgroup ↥P))) :
          ↥(S : Subgroup ↥P)) : ↥P) := by simp [hz]
      _ = 1 := by rw [h0]; rfl
  have hBS' : Subgroup.zpowers δ' ⊔ Subgroup.zpowers u' ≤ (S : Subgroup ↥P) := hBS
  have hδ'S : δ' ∈ (S : Subgroup ↥P) := hBS' (Subgroup.mem_sup_left (Subgroup.mem_zpowers δ'))
  have hu'S : u' ∈ (S : Subgroup ↥P) := hBS' (Subgroup.mem_sup_right (Subgroup.mem_zpowers u'))
  have hzB : z ∈ Subgroup.zpowers δ' ⊔ Subgroup.zpowers u' := by
    by_contra hzB
    have hzδ' : δ' * z = z * δ' := (Subgroup.mem_centralizer_iff.mp hzZ.2 δ' hδ'S)
    have hδ'z : δ' ∉ Subgroup.zpowers z := by
      intro h
      apply hzB
      have hle : Subgroup.zpowers δ' ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr h
      have hzz : Subgroup.zpowers δ' = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hz3 hz1,
            orderOf_eq_prime hδ'3 hδ'1])
      have hzδ'' : z ∈ Subgroup.zpowers δ' := by
        rw [hzz]
        exact Subgroup.mem_zpowers z
      exact Subgroup.mem_sup_left hzδ''
    have hB9z : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers δ') = 9 :=
      Ronan148J.card_zpowers_sup_zpowers_eq_nine hzδ'.symm hz3 hz1 hδ'3 hδ'z
    have hBSz : Subgroup.zpowers z ⊔ Subgroup.zpowers δ' ≤ (S : Subgroup ↥P) :=
      sup_le (Subgroup.zpowers_le.mpr hzS) (Subgroup.zpowers_le.mpr hδ'S)
    have hu'B : u' ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers δ' := by
      intro hu
      apply hzB
      have hle : Subgroup.zpowers δ' ⊔ Subgroup.zpowers u' ≤
          Subgroup.zpowers z ⊔ Subgroup.zpowers δ' :=
        sup_le le_sup_right (Subgroup.zpowers_le.mpr hu)
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, hB9z])
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    exact j2Syl_not_comm h415 ⟨φ⟩ S hz1 hzδ' hδ'z hBSz hS27 hB9z hzZ hδ'S hu'S hu'B hδu'
  set zq : ↥(Y ⊔ A) ⧸ ker148 A Y := (z : ↥(Y ⊔ A) ⧸ ker148 A Y) with hzq
  have hzqP : zq ∈ P := z.2
  have hzqB : zq ∈ Subgroup.zpowers δα ⊔ Subgroup.zpowers uα := by
    have h := Subgroup.mem_map_of_mem P.subtype hzB
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
  have hzqA : zq ∈ img148 A Y A :=
    sup_le (Subgroup.zpowers_le.mpr hδαA) (Subgroup.zpowers_le.mpr huαA) hzqB
  obtain ⟨z', hz'M, hz'A, hz'eq⟩ := mem_img148_iff.mp hzqA
  have hz'α : alpha148 A Y z' hz'A = zq := (alpha148_eq_mk' hz'A).trans hz'eq
  have hzq1 : zq ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h27q : 27 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {zq}) := by
    rw [← card_centralizer_subtype_eq z]
    exact h27z
  by_cases hzd : δα ∈ Subgroup.zpowers zq
  ·
    refine h27q.trans (Subgroup.card_dvd_of_le fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzd
    have hx2 : x * zq = zq * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (Commute.zpow_right hx2 k).eq
  · exfalso
    have hz'1 : z' ≠ 1 := by
      rintro rfl
      exact hzq1 (hz'α.symm.trans alpha148_one')
    have hδz' : δ ∉ Subgroup.zpowers z' := fun h =>
      hzd (alpha148_mem_of_mem_zpowers (P := Subgroup.zpowers zq) hA3 hz'A hδA h
        (by rw [hz'α]; exact Subgroup.mem_zpowers zq))
    obtain ⟨w, hwN, -, hwδ⟩ := exists_normalizer_conj_of_j2_factor hS hAY ⟨φ⟩ hAP hz'A hδA
      (by rw [hz'α]; exact hzqP) hz'1 (by rw [hz'α]; exact h27q) hδP hδz'
    have hwδ' : w * δ * w⁻¹ ∈ Subgroup.zpowers δ :=
      (Subgroup.mem_normalizer_iff.mp (hW hwN) δ).mp (Subgroup.mem_zpowers δ)
    have hz'δ : z' ∈ Subgroup.zpowers δ := by
      have hz'3 : z' ^ 3 = 1 := hA3 z' hz'A
      rcases hwδ with h | h
      · rw [h] at hwδ'
        have := mul_mem hwδ' (inv_mem (Subgroup.mem_zpowers δ))
        rwa [mul_inv_cancel_right] at this
      · rw [h] at hwδ'
        have h2 : z' ^ 2 ∈ Subgroup.zpowers δ := by
          have := mul_mem hwδ' (inv_mem (Subgroup.mem_zpowers δ))
          rwa [mul_inv_cancel_right] at this
        have h4 : z' = (z' ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hz'3, one_mul]
        rw [h4]
        exact pow_mem h2 2
    have hzqδ : zq ∈ Subgroup.zpowers δα := by
      rw [← hz'α]
      exact alpha148_mem_of_mem_zpowers (P := Subgroup.zpowers δα) hA3 hδA hz'A hz'δ
        (Subgroup.mem_zpowers δα)
    apply hzd
    have hle : Subgroup.zpowers zq ≤ Subgroup.zpowers δα := Subgroup.zpowers_le.mpr hzqδ
    have hzq3 : zq ^ 3 = 1 := hAq3 zq hzqA
    have heq : Subgroup.zpowers zq = Subgroup.zpowers δα :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzq3 hzq1,
          orderOf_eq_prime hδα3 hδα1])
    rw [heq]
    exact Subgroup.mem_zpowers δα

theorem ncard_omegaA_eq_six_or_twelve_of_j2_factor' (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) [(ker148 A Y).Normal]
    {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hP : Nonempty (↥P ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAP : img148 A Y A ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {δ u v : G} (hδA : δ ∈ A) (huA : u ∈ A) (hvA : v ∈ A) (hδP : alpha148 A Y δ hδA ∈ P)
    (hδ1 : δ ≠ 1)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers δ : Set G))
    (hu : Subgroup.zpowers u ∈ omegaA A) (huP : alpha148 A Y u huA ∈ P)
    (huδ : u ∉ Subgroup.zpowers δ) (hv : Subgroup.zpowers v ∈ omegaA A)
    (hvP : alpha148 A Y v hvA ∉ P) :
    (omegaA A).ncard = 6 ∨ (omegaA A).ncard = 12 :=
  ncard_omegaA_eq_six_or_twelve_of_j2_factor h134 h48 hS hB hc hAY hP hAP hδA huA hvA hδP hδ1
    (dvd_card_centralizer_of_normalizer_le hS hAY hP hAP hδA huA hδP hδ1 huP huδ hW) hu huP huδ
    hv hvP

end Count

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
