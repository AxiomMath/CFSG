module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Ronan148VJ2Syl
import CFSG.RankThree.PartTwo.Sec14.Ronan148VA5Inner
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Descent2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

variable {G : Type} [Group G] [Finite G]

theorem eq_of_zpowers_mul_eq {X : Type} [Group X] {a b u δ : X}
    (ha : a ∈ Subgroup.zpowers δ) (hb : b ∈ Subgroup.zpowers δ) (hbu : b * u = u * b)
    (hu3 : u ^ 3 = 1) (hau3 : (a * u) ^ 3 = 1) (huδ : u ∉ Subgroup.zpowers δ)
    (h : Subgroup.zpowers (a * u) = Subgroup.zpowers (b * u)) : a = b := by
  have hbu' : b * u ∈ Subgroup.zpowers (a * u) := h ▸ Subgroup.mem_zpowers _
  rcases inner_a5_mem_zpowers hau3 hbu' with h1 | h1 | h1
  · exfalso
    apply huδ
    have hu : u = b⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hu]
    exact inv_mem hb
  · exact (mul_right_cancel h1).symm
  · exfalso
    apply huδ
    have e1 : a * u * (b * u) = 1 := by rw [h1, mul_inv_cancel]
    have e2 : a * b * (u * u) = 1 :=
      calc a * b * (u * u) = a * (b * u) * u := by simp only [mul_assoc]
        _ = a * (u * b) * u := by rw [hbu]
        _ = a * u * (b * u) := by simp only [mul_assoc]
        _ = 1 := e1
    have e3 : u * u = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right e2
    have e4 : u = (u * u)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three]; exact hu3)
    rw [e4, e3, inv_inv]
    exact mul_mem ha hb

theorem card_centralizer_subtype_eq {X : Type*} [Group X] {P : Subgroup X} (x : ↥P) :
    Nat.card (Subgroup.centralizer ({x} : Set ↥P)) =
      Nat.card ↥(P ⊓ Subgroup.centralizer {(x : X)}) := by
  have heq : (Subgroup.centralizer ({x} : Set ↥P)).map P.subtype =
      P ⊓ Subgroup.centralizer {(x : X)} := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, by simpa using congrArg Subtype.val hp⟩
    · rintro ⟨hg, hgx⟩
      exact ⟨⟨g, hg⟩, Subtype.ext (by simpa using hgx), rfl⟩
  rw [← heq, Subgroup.card_map_of_injective P.subtype_injective]

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem exists_normalizer_lift148 (hA3 : IsPGroup 3 A) {g : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hg : g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ∃ w : ↥(Y ⊔ A), (w : G) ∈ Subgroup.normalizer (A : Set G) ∧
      QuotientGroup.mk' (ker148 A Y) w = g := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) g
  set R : Subgroup ↥(Y ⊔ A) := A.subgroupOf (Y ⊔ A) with hR
  set C := ker148 A Y with hC
  have hR3 : IsPGroup 3 R := hA3.comap_of_injective (Y ⊔ A).subtype (Y ⊔ A).subtype_injective
  have hC3 : ¬ 3 ∣ Nat.card C := not_three_dvd_card_ker148
  have hpre : ∀ y : ↥(Y ⊔ A), y ∈ C ⊔ R ↔ QuotientGroup.mk' C y ∈ img148 A Y A := by
    intro y
    have h1 : (img148 A Y A).comap (QuotientGroup.mk' C) = R ⊔ C := by
      rw [img148, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← Subgroup.mem_comap, h1]
    exact ⟨fun h => (sup_comm C R).le h, fun h => (sup_comm R C).le h⟩
  have hxn : x ∈ Subgroup.normalizer ((C ⊔ R : Subgroup ↥(Y ⊔ A)) : Set ↥(Y ⊔ A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hpre, hpre, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hg _
  obtain ⟨o, ho, hon⟩ := StrongThree.exists_mul_mem_normalizer_of_sup hR3 hC3 hxn
  refine ⟨o * x, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzM : z ∈ Y ⊔ A := Subgroup.mem_sup_right hz
      exact (Subgroup.mem_normalizer_iff.mp hon ⟨z, hzM⟩).mp hz
    · intro hz
      set w : ↥(Y ⊔ A) := o * x with hw
      have hzM : z ∈ Y ⊔ A := by
        have h1 : (w : G) * z * (w : G)⁻¹ ∈ Y ⊔ A := Subgroup.mem_sup_right hz
        have h2 := (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem w.2) h1) w.2
        simpa [mul_assoc] using h2
      exact (Subgroup.mem_normalizer_iff.mp hon ⟨z, hzM⟩).mpr hz
  · have hoα : QuotientGroup.mk' C o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, hoα, one_mul]

theorem alpha148_conj (w : ↥(Y ⊔ A)) {a : G} (ha : a ∈ A) (hwa : (w : G) * a * (w : G)⁻¹ ∈ A) :
    alpha148 A Y ((w : G) * a * (w : G)⁻¹) hwa =
      QuotientGroup.mk' (ker148 A Y) w * alpha148 A Y a ha *
        (QuotientGroup.mk' (ker148 A Y) w)⁻¹ := by
  rw [alpha148_eq_mk', alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem alpha148_one' : alpha148 A Y 1 A.one_mem = 1 :=
  (alpha148_eq_mk' A.one_mem).trans (mk'_ker148_eq_one_iff.mpr (Subgroup.one_mem _))

theorem alpha148_mem_of_mem_zpowers (hA3 : ∀ a ∈ A, a ^ 3 = 1) {x v : G} (hx : x ∈ A)
    (hv : v ∈ A) (hvx : v ∈ Subgroup.zpowers x) {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hxP : alpha148 A Y x hx ∈ P) : alpha148 A Y v hv ∈ P := by
  rcases inner_a5_mem_zpowers (hA3 x hx) hvx with rfl | rfl | rfl
  · rw [alpha148_one']
    exact one_mem _
  · exact hxP
  · rw [alpha148_inv hx]
    exact inv_mem hxP

end Quot

section Count


theorem ncard_omegaA_cases_of_isLBConfig (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    (omegaA A).ncard = 1 ∨ (omegaA A).ncard = 3 ∨ (omegaA A).ncard = 6 ∨
      (omegaA A).ncard = 12 := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, -, -, -, -, ⟨-, h3⟩ | ⟨-, -, -, -, -, -, -, -, h6, -⟩⟩ | ⟨-, -, -, h12⟩
  · left
    rw [h1, Set.ncard_singleton]
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h6))
  · exact Or.inr (Or.inr (Or.inr h12))

theorem four_le_ncard_omegaA_of_j2_factor {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) [(ker148 A Y).Normal]
    {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hP : Nonempty (↥P ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAP : img148 A Y A ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {δ u v : G} (hδA : δ ∈ A) (huA : u ∈ A) (hvA : v ∈ A) (hδP : alpha148 A Y δ hδA ∈ P)
    (hδ1 : δ ≠ 1)
    (h27 : 27 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {alpha148 A Y δ hδA}))
    (hu : Subgroup.zpowers u ∈ omegaA A) (huP : alpha148 A Y u huA ∈ P)
    (huδ : u ∉ Subgroup.zpowers δ) (hv : Subgroup.zpowers v ∈ omegaA A)
    (hvP : alpha148 A Y v hvA ∉ P) :
    4 ≤ (omegaA A).ncard := by
  classical
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
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
  have h9 : Nat.card ↥(Subgroup.zpowers δα ⊔ Subgroup.zpowers uα) = 9 :=
    Ronan148J.card_zpowers_sup_zpowers_eq_nine hδu hδα3 hδα1 huα3 huδα
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
  have hsub : Subgroup.zpowers δα ⊔ Subgroup.zpowers uα ≤ img148 A Y A ⊓ P :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hδαA, hδP⟩) (Subgroup.zpowers_le.mpr ⟨huαA, huP⟩)
  have hAPeq : img148 A Y A ⊓ P = Subgroup.zpowers δα ⊔ Subgroup.zpowers uα :=
    (Subgroup.eq_of_le_of_card_ge hsub (by rw [h9]; exact hle9)).symm
  have h27' : 27 ∣ Nat.card (Subgroup.centralizer ({⟨δα, hδP⟩} : Set ↥P)) := by
    rw [card_centralizer_subtype_eq]
    exact h27
  have hcnd : (⟨uα, huP⟩ : ↥P) ∉ Subgroup.zpowers (⟨δα, hδP⟩ : ↥P) := by
    intro h
    apply huδα
    have h' := Subgroup.mem_map_of_mem P.subtype h
    rwa [MonoidHom.map_zpowers] at h'
  obtain ⟨y, hyd, hyu⟩ := exists_conj_eq_mul_of_j2 ⟨φ⟩ (d := ⟨δα, hδP⟩) (c := ⟨uα, huP⟩)
    (fun h => hδα1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hδα3)) h27'
    (Subtype.ext (by simpa using huα3)) (Subtype.ext hδu.symm) hcnd
  have hyd' : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * δα = δα * y := by
    simpa using congrArg Subtype.val hyd
  have hyu' : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * uα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = δα * uα ∨
      (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * uα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = δα ^ 2 * uα := by
    rcases hyu with h | h
    · left
      simpa using congrArg Subtype.val h
    · right
      simpa using congrArg Subtype.val h
  have hyδ : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * δα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ = δα := by
    rw [hyd', mul_inv_cancel_right]
  have hyA : ∀ a ∈ img148 A Y A,
      (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * a * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ ∈ img148 A Y A := by
    have h2 : Subgroup.zpowers δα ⊔ Subgroup.zpowers uα ≤ (img148 A Y A).comap
        (MulAut.conj (y : ↥(Y ⊔ A) ⧸ ker148 A Y)).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        simpa [MulAut.conj_apply, hyδ] using hδαA
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        have hm : (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * uα * (y : ↥(Y ⊔ A) ⧸ ker148 A Y)⁻¹ ∈
            img148 A Y A := by
          rcases hyu' with h | h
          · rw [h]
            exact mul_mem hδαA huαA
          · rw [h]
            exact mul_mem (pow_mem hδαA 2) huαA
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
  have hwδ : (w : G) * δ * (w : G)⁻¹ = δ := by
    refine alpha148_injective (Y := Y) hA3 (hwA δ hδA) hδA ?_
    rw [alpha148_conj w hδA, hwy]
    exact hyδ
  have hδ2A : δ ^ 2 ∈ A := pow_mem hδA 2
  have hwu : (w : G) * u * (w : G)⁻¹ = δ * u ∨ (w : G) * u * (w : G)⁻¹ = δ ^ 2 * u := by
    rcases hyu' with h | h
    · left
      refine alpha148_injective (Y := Y) hA3 (hwA u huA) (A.mul_mem hδA huA) ?_
      rw [alpha148_conj w huA, hwy, alpha148_mul hδA huA]
      exact h
    · right
      refine alpha148_injective (Y := Y) hA3 (hwA u huA) (A.mul_mem hδ2A huA) ?_
      rw [alpha148_conj w huA, hwy, alpha148_mul hδ2A huA, alpha148_pow hδA]
      exact h
  have hΩw : ∀ x : G, Subgroup.zpowers x ∈ omegaA A →
      Subgroup.zpowers ((w : G) * x * (w : G)⁻¹) ∈ omegaA A := by
    intro x hx
    have h := (map_conj_mem_omegaA_iff (F := Subgroup.zpowers x) hwN).mpr hx
    rwa [MonoidHom.map_zpowers] at h
  have hconj : ∀ k : ℕ, (w : G) * (δ ^ k * u) * (w : G)⁻¹ =
      δ ^ k * ((w : G) * u * (w : G)⁻¹) := by
    intro k
    have hk : (w : G) * δ ^ k * (w : G)⁻¹ = δ ^ k := by
      rw [← conj_pow, hwδ]
    calc (w : G) * (δ ^ k * u) * (w : G)⁻¹ =
        ((w : G) * δ ^ k * (w : G)⁻¹) * ((w : G) * u * (w : G)⁻¹) := by group
      _ = δ ^ k * ((w : G) * u * (w : G)⁻¹) := by rw [hk]
  have hδ3 : δ ^ 3 = 1 := hA3 δ hδA
  have hU1 : Subgroup.zpowers (δ * u) ∈ omegaA A ∧ Subgroup.zpowers (δ ^ 2 * u) ∈ omegaA A := by
    rcases hwu with h | h
    · have h1 : Subgroup.zpowers (δ * u) ∈ omegaA A := h ▸ hΩw u hu
      refine ⟨h1, ?_⟩
      have h2 := hΩw _ h1
      rwa [show (w : G) * (δ * u) * (w : G)⁻¹ = δ ^ 2 * u by
        rw [← pow_one δ, hconj 1, h, pow_one, ← mul_assoc, ← pow_two]] at h2
    · have h1 : Subgroup.zpowers (δ ^ 2 * u) ∈ omegaA A := h ▸ hΩw u hu
      refine ⟨?_, h1⟩
      have h2 := hΩw _ h1
      rwa [show (w : G) * (δ ^ 2 * u) * (w : G)⁻¹ = δ * u by
        rw [hconj 2, h, ← mul_assoc, ← pow_add,
          show δ ^ (2 + 2) = δ by rw [show 2 + 2 = 3 + 1 by norm_num, pow_add, hδ3, one_mul,
            pow_one]]] at h2
  have hδz : δ ∈ Subgroup.zpowers δ := Subgroup.mem_zpowers δ
  have hδ2z : δ ^ 2 ∈ Subgroup.zpowers δ := pow_mem hδz 2
  have h1z : (1 : G) ∈ Subgroup.zpowers δ := one_mem _
  have hu3 : u ^ 3 = 1 := hA3 u huA
  have hcu : ∀ {a : G}, a ∈ A → a * u = u * a := fun ha => hAc _ ha _ huA
  have hne : ∀ {a b : G}, a ∈ Subgroup.zpowers δ → b ∈ Subgroup.zpowers δ → a ∈ A → b ∈ A →
      a ≠ b → Subgroup.zpowers (a * u) ≠ Subgroup.zpowers (b * u) := by
    intro a b ha hb haA hbA hab heq
    exact hab (eq_of_zpowers_mul_eq ha hb (hcu hbA) hu3 (hA3 _ (A.mul_mem haA huA)) huδ heq)
  have hδne1 : δ ≠ 1 := hδ1
  have hδ2ne1 : δ ^ 2 ≠ 1 := by
    intro h
    apply hδ1
    calc δ = δ ^ 3 * (δ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hδ3, h]; group
  have hδneδ2 : δ ≠ δ ^ 2 := by
    intro h
    apply hδ1
    calc δ = δ ^ 2 * δ⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel]
  have h01 : Subgroup.zpowers u ≠ Subgroup.zpowers (δ * u) := by
    have := hne h1z hδz A.one_mem hδA hδne1.symm
    rwa [one_mul] at this
  have h02 : Subgroup.zpowers u ≠ Subgroup.zpowers (δ ^ 2 * u) := by
    have := hne h1z hδ2z A.one_mem hδ2A hδ2ne1.symm
    rwa [one_mul] at this
  have h12 : Subgroup.zpowers (δ * u) ≠ Subgroup.zpowers (δ ^ 2 * u) :=
    hne hδz hδ2z hδA hδ2A hδneδ2
  have hvne : ∀ {x : G} (hx : x ∈ A), alpha148 A Y x hx ∈ P →
      Subgroup.zpowers v ≠ Subgroup.zpowers x := by
    intro x hx hxP heq
    apply hvP
    have hvx : v ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers v
    exact alpha148_mem_of_mem_zpowers hA3 hx hvA hvx hxP
  have hδuP : alpha148 A Y (δ * u) (A.mul_mem hδA huA) ∈ P := by
    rw [alpha148_mul hδA huA]
    exact mul_mem hδP huP
  have hδ2uP : alpha148 A Y (δ ^ 2 * u) (A.mul_mem hδ2A huA) ∈ P := by
    rw [alpha148_mul hδ2A huA, alpha148_pow hδA]
    exact mul_mem (pow_mem hδP 2) huP
  have hv0 := hvne huA huP
  have hv1 := hvne (A.mul_mem hδA huA) hδuP
  have hv2 := hvne (A.mul_mem hδ2A huA) hδ2uP
  have hsubΩ : ({Subgroup.zpowers u, Subgroup.zpowers (δ * u), Subgroup.zpowers (δ ^ 2 * u),
      Subgroup.zpowers v} : Set (Subgroup G)) ⊆ omegaA A := by
    intro F hF
    rcases hF with rfl | rfl | rfl | rfl
    · exact hu
    · exact hU1.1
    · exact hU1.2
    · exact hv
  have hcard : ({Subgroup.zpowers u, Subgroup.zpowers (δ * u), Subgroup.zpowers (δ ^ 2 * u),
      Subgroup.zpowers v} : Set (Subgroup G)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hv2.symm]
    · rintro (h | h)
      · exact h12 h
      · exact hv1 h.symm
    · rintro (h | h | h)
      · exact h01 h
      · exact h02 h
      · exact hv0 h.symm
  calc 4 = _ := hcard.symm
    _ ≤ (omegaA A).ncard := Set.ncard_le_ncard hsubΩ (Set.toFinite _)

theorem ncard_omegaA_eq_six_or_twelve_of_j2_factor (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) [(ker148 A Y).Normal]
    {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hP : Nonempty (↥P ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAP : img148 A Y A ≤ Subgroup.normalizer (P : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {δ u v : G} (hδA : δ ∈ A) (huA : u ∈ A) (hvA : v ∈ A) (hδP : alpha148 A Y δ hδA ∈ P)
    (hδ1 : δ ≠ 1)
    (h27 : 27 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {alpha148 A Y δ hδA}))
    (hu : Subgroup.zpowers u ∈ omegaA A) (huP : alpha148 A Y u huA ∈ P)
    (huδ : u ∉ Subgroup.zpowers δ) (hv : Subgroup.zpowers v ∈ omegaA A)
    (hvP : alpha148 A Y v hvA ∉ P) :
    (omegaA A).ncard = 6 ∨ (omegaA A).ncard = 12 := by
  have h4 := four_le_ncard_omegaA_of_j2_factor hS hAY hP hAP hδA huA hvA hδP hδ1 h27 hu huP huδ
    hv hvP
  rcases ncard_omegaA_cases_of_isLBConfig h134 h48 hS hB hc with h | h | h | h <;> omega

end Count

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
