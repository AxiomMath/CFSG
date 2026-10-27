module

public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFix
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpComp
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpPull
import CFSG.GroupTheory.ElemAbelianClosure

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace A6InsideSp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.ChoiceTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L]
  [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)

theorem exists_shape (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hL : Module.finrank K L = 2) {c : Fin F.s → ZMod 3} {i₀ : Fin F.s}
    (hc : ∀ i, c i ≠ 0 ↔ i = i₀) {B D J : Subgroup (StatedSp n K)} (hBE : B ≤ E)
    (hB : 3 ^ 4 ≤ Nat.card B)
    (hpre : LargeEvenStdSubPre 3 B (F.tor c) (spFixedFactor (F.tor c)) D J)
    (hJ : Nat.card J = 360) :
    ∃ (a b : Fin F.s) (d : Fin F.s → ZMod 3), a ≠ i₀ ∧ b ≠ i₀ ∧ a ≠ b ∧
      (∀ i, d i = 0 ↔ (i = i₀ ∨ i = a ∨ i = b)) ∧ F.tor d ∈ B ∧ F.s ≤ 6 ∧
      (∀ f, F.tor f ∈ B → f a = 0 → f b = 0 → ∃ α β : ZMod 3, f = α • c + β • d) ∧
      ∀ u v : ZMod 3, ∃ f, F.tor f ∈ B ∧ f a = u ∧ f b = v := by
  classical
  haveI hfin : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have hspos : 0 < F.s := Fin.pos_iff_nonempty.mpr ⟨i₀⟩
  haveI hnez : NeZero n := ⟨by
    have hs : F.s = n := s_eq F hL
    omega⟩
  change D ≤ B ∧ CFSG.Open.IsElemAbelian 3 D ∧ Nat.card D = 3 ^ 2 ∧ F.tor c ∈ D ∧
    J = LargeEvenLayer (spFixedFactor (F.tor c) ⊓
      Subgroup.centralizer (D : Set (StatedSp n K))) ∧
    IsComponentOf J (spFixedFactor (F.tor c) ⊓
      Subgroup.centralizer (D : Set (StatedSp n K))) ∧
    D = B ⊓ Subgroup.centralizer (J : Set (StatedSp n K)) at hpre
  obtain ⟨hDB, hDea, hDcard, hxD, hJeq, hJcomp, hDeq⟩ := hpre
  have hD9 : Nat.card D = 9 := by rw [hDcard]; norm_num
  have hc0 : c i₀ ≠ 0 := (hc i₀).mpr rfl
  have hc_eq : ∀ i, i ≠ i₀ → c i = 0 := by
    intro i hi
    by_contra hne
    exact hi ((hc i).mp hne)
  obtain ⟨d, hdD, hdi, hind, hDgen⟩ :=
    exists_eq_closure_pair F hζo (hDB.trans hBE) hD9 hxD hc0
  have hZmem : ∀ i, i ∈ F.zeroSet (c + d) ↔ i ≠ i₀ ∧ d i = 0 := by
    intro i
    rw [F.mem_zeroSet]
    constructor
    · intro h
      simp only [Pi.add_apply] at h
      have hci : c i = 0 := by
        by_contra hci
        have hi0 : i = i₀ := (hc i).mp hci
        rw [hi0, hdi] at h
        exact hc0 (by simpa using h)
      have hdi' : d i = 0 := by simpa [hci] using h
      exact ⟨fun hi0 => hc0 (by rwa [hi0] at hci), hdi'⟩
    · rintro ⟨hi, hdi'⟩
      have hci : c i = 0 := hc_eq i hi
      rw [Pi.add_apply, hci, hdi', add_zero]
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy => hDea.comm hx hy
  have hDw : D ≤ Subgroup.centralizer {F.tor d} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hDcomm x hx (F.tor d) hdD
  have hCw : Subgroup.centralizer (D : Set (StatedSp n K)) ≤
      Subgroup.centralizer {F.tor d} :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hdD)
  have hSD : spSupported (F.tor d) {phi3 K} ≤
      Subgroup.centralizer (D : Set (StatedSp n K)) := by
    rw [hDgen, Subgroup.centralizer_closure]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with hy | hy
    · subst hy
      refine (Subgroup.mem_centralizer_singleton_iff.mp
        (spSupported_le_centralizer_tor F hK hζo (κ := 0) (fun i hi => ?_) hg)).symm
      rw [zero_mul]
      exact hc_eq i (fun h => hi (by rw [h]; exact hdi))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        (SevSpNs.spSupported_le_centralizer (F.tor d) {phi3 K} hg)).symm
  have hJcD : IsComponentOf J (Subgroup.centralizer (D : Set (StatedSp n K))) :=
    isComponentOf_centralizer_of_inf (x := F.tor c) (D := D)
      (L₀ := spFixedFactor (F.tor c)) hxD (spFixedFactor_le_centralizer (F.tor c))
      (spFixedFactor_normalized (F.tor c)) hJcomp
  have h27 : ¬ 27 ∣ Nat.card J := by rw [hJ]; norm_num
  have hJFd : J ≤ spFixedFactor (F.tor d) :=
    le_spFixedFactor_of_isComponentOf F hK hζo hL hDw hCw hSD hJcD h27
  have hJFcd : J ≤ spFixedFactor (F.tor (c + d)) := by
    intro g hg
    exact mem_spFixedFactor_add F hK hζo (hJcomp.1.trans inf_le_left hg) (hJFd hg)
  have hSA : spFixedFactor (F.tor (c + d)) ≤
      Subgroup.centralizer (D : Set (StatedSp n K)) := by
    rw [hDgen, Subgroup.centralizer_closure]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with hy | hy
    · subst hy
      refine (Subgroup.mem_centralizer_singleton_iff.mp
        (spFixedFactor_le_centralizer_tor F hK hζo (f := c + d) (h := c) (fun i hi => ?_)
          hg)).symm
      exact hc_eq i ((hZmem i).mp (F.mem_zeroSet.mpr hi)).1
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine (Subgroup.mem_centralizer_singleton_iff.mp
        (spFixedFactor_le_centralizer_tor F hK hζo (f := c + d) (h := d) (fun i hi => ?_)
          hg)).symm
      exact ((hZmem i).mp (F.mem_zeroSet.mpr hi)).2
  have hJcd : IsComponentOf J (Subgroup.centralizer {F.tor (c + d)}) :=
    isComponentOf_of_le_normalized hJcD hJFcd hSA
      (spFixedFactor_le_centralizer (F.tor (c + d)))
      (spFixedFactor_normalized (F.tor (c + d)))
  have hf0 : c + d ≠ 0 := by
    intro h
    have h1 := congrFun h i₀
    simp only [Pi.add_apply, Pi.zero_apply] at h1
    rw [hdi, add_zero] at h1
    exact hc0 h1
  have hZge2 : 2 ≤ (F.zeroSet (c + d)).card := by
    by_contra hlt
    have hle1 : (F.zeroSet (c + d)).card ≤ 1 := by omega
    have hcases : (F.zeroSet (c + d)).card = 0 ∨ (F.zeroSet (c + d)).card = 1 := by omega
    rcases hcases with hZcard | hZcard
    ·
      have hZ0 : F.zeroSet (c + d) = ∅ := Finset.card_eq_zero.mp hZcard
      have hsupp_univ : F.suppSet (c + d) = Finset.univ := by
        rw [Finset.eq_univ_iff_forall]
        intro i
        rw [F.mem_suppSet]
        intro hi
        have hmem : i ∈ F.zeroSet (c + d) := F.mem_zeroSet.mpr hi
        rw [hZ0] at hmem
        exact Finset.notMem_empty i hmem
      have htop : primaryComponent (spEnd (F.tor (c + d))) (phi3 K) = ⊤ := by
        rw [F.phi3_eq_map hζo, hsupp_univ]
        have hsuppSub : suppSub (L := L) K (Finset.univ : Finset (Fin F.s)) = ⊤ := by
          rw [Submodule.eq_top_iff']
          intro x
          rw [mem_suppSub]
          simp
        rw [hsuppSub, Submodule.map_top, LinearEquiv.range]
      have hphi3mem : phi3 K ∈ primaryFactors (spEnd (F.tor (c + d))) := by
        by_contra hnm
        have hbot := primaryComponent_eq_bot_of_not_mem (phi3_irreducible hK) monic_phi3 hnm
        have hdim := F.finrank_phi3_tor hζo hL (c + d)
        rw [hbot, finrank_bot, hsupp_univ, Finset.card_univ, Fintype.card_fin] at hdim
        omega
      have hbot : spFixedFactor (F.tor (c + d)) = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        rw [Subgroup.mem_bot]
        refine eq_of_spEnd_eq' fun v => ?_
        rw [spEnd_one_apply]
        exact (mem_spSupported.mp hg).2 (phi3 K) hphi3mem
          (fun h => phi3_ne_X_sub_one h) v (htop ▸ Submodule.mem_top)
      have hle := Subgroup.card_le_of_le hJFcd
      rw [hbot, Subgroup.card_bot, hJ] at hle
      omega
    ·
      obtain ⟨z, hZ1⟩ := Finset.card_eq_one.mp hZcard
      have hz : (F.zeroSet (c + d)).Nonempty :=
        ⟨z, by rw [hZ1]; exact Finset.mem_singleton_self z⟩
      obtain ⟨e⟩ := nonempty_spFixedFactor_equiv F hK hζo hL hf0 hz
      have hcard : Nat.card (spFixedFactor (F.tor (c + d))) = 6 := by
        rw [Nat.card_congr e.toEquiv, hZcard]
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
        norm_num [hK]
      have hle := Subgroup.card_le_of_le hJFcd
      rw [hcard, hJ] at hle
      omega
  have hZle2 : (F.zeroSet (c + d)).card ≤ 2 := by
    by_contra hlt
    have hZ3 : 3 ≤ (F.zeroSet (c + d)).card := by omega
    have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd (F.tor (c + d))) := by
      refine X_sub_one_mem_primaryFactors (F.tor (c + d)) ?_
      rw [F.spFixedDim_tor hζo hL]
      omega
    obtain ⟨-, hfix⟩ := SevSpNs.fixed_case (K := K) (r := n) (f := 1) (p := 3)
      (by simpa using hK) le_rfl Nat.prime_three (by norm_num)
      (F.tor_pow_three hζo.pow_eq_one (c + d)) (F.blocks_tor hK hζo hf0) hmem hJcd hJFcd
    have htorSub_le : torSub F hζo.pow_eq_one (coordSub (F.zeroSet (c + d))) ≤ J := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := (mem_torSub F hζo.pow_eq_one).mp hg
      refine hfix (F.tor f) (F.tor_mem_spFixedFactor hK hζo (c + d) f (fun i hi => ?_))
        (F.tor_pow_three hζo.pow_eq_one f)
      exact (mem_coordSub.mp hf) i (fun hiZ => hi (F.mem_zeroSet.mp hiZ))
    have hdvd : 3 ^ (F.zeroSet (c + d)).card ∣ Nat.card J := by
      have h2 : Nat.card (torSub F hζo.pow_eq_one (coordSub (F.zeroSet (c + d)))) ∣
          Nat.card J := Subgroup.card_dvd_of_le htorSub_le
      rwa [card_torSub F hζo, card_coordSub] at h2
    have h3 : 3 ^ 3 ∣ 3 ^ (F.zeroSet (c + d)).card := Nat.pow_dvd_pow 3 hZ3
    have h27 : 27 ∣ 360 := by
      have hdvd' : 3 ^ (F.zeroSet (c + d)).card ∣ 360 := by rwa [hJ] at hdvd
      have h : 3 ^ 3 ∣ 360 := h3.trans hdvd'
      simpa only [show (3 : ℕ) ^ 3 = 27 by norm_num] using h
    norm_num at h27
  have hZcard : (F.zeroSet (c + d)).card = 2 := le_antisymm hZle2 hZge2
  obtain ⟨a, b, hab, hZab⟩ := Finset.card_eq_two.mp hZcard
  have haZ : a ∈ F.zeroSet (c + d) := by
    rw [hZab]; exact Finset.mem_insert_self a {b}
  have hbZ : b ∈ F.zeroSet (c + d) := by
    rw [hZab]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hai : a ≠ i₀ := ((hZmem a).mp haZ).1
  have hbi : b ≠ i₀ := ((hZmem b).mp hbZ).1
  have hda : d a = 0 := ((hZmem a).mp haZ).2
  have hdb : d b = 0 := ((hZmem b).mp hbZ).2
  have hdzero : ∀ i, d i = 0 ↔ i = i₀ ∨ i = a ∨ i = b := by
    intro i
    constructor
    · intro hdi'
      by_cases hi : i = i₀
      · exact Or.inl hi
      · have hiZ : i ∈ F.zeroSet (c + d) := (hZmem i).mpr ⟨hi, hdi'⟩
        rw [hZab] at hiZ
        rcases Finset.mem_insert.mp hiZ with rfl | hiZ
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp hiZ))
    · rintro (rfl | rfl | rfl)
      · exact hdi
      · exact hda
      · exact hdb
  have hsupp_le : (F.suppSet d).card ≤ 3 := by
    by_contra hle
    have hbig : 4 ≤ (F.suppSet d).card := by omega
    have hPq : CFSG.IsQuasisimple ↥(spPull (F.tor d) (phi3 K)) :=
      isQuasisimple_spPull_phi3 F hK hζo hL hbig
    have hPleL : spPull (F.tor d) (phi3 K) ≤ spFixedFactor (F.tor c) := by
      intro g hg
      refine mem_spFixedFactor_of_disjoint F hK hζo (f₁ := c) (f₂ := d) ?_ ?_ ?_
      · intro i hi
        rw [(hc i).mp hi]
        exact hdi
      · exact spPull_phi3_le_spSupported F d hg
      · exact (Subgroup.mem_centralizer_iff.mp
          (hSD (spPull_phi3_le_spSupported F d hg)) (F.tor c) hxD).symm
    have hPleC : spPull (F.tor d) (phi3 K) ≤
        Subgroup.centralizer (D : Set (StatedSp n K)) :=
      (spPull_phi3_le_spSupported F d).trans hSD
    have hPcomp : IsComponentOf (spPull (F.tor d) (phi3 K))
        (spFixedFactor (F.tor c) ⊓ Subgroup.centralizer (D : Set (StatedSp n K))) := by
      refine SpNonsplitComp.isComponentOf_of_normalizes (le_inf hPleL hPleC) ?_ hPq
      intro m hm g hg
      exact spPull_normalized (F.tor d) (phi3 K) m (hCw hm.2) g hg
    have hPleJ : spPull (F.tor d) (phi3 K) ≤ J := by
      rw [hJeq]
      change spPull (F.tor d) (phi3 K) ≤
        sSup {K' : Subgroup (StatedSp n K) | IsComponentOf K'
          (spFixedFactor (F.tor c) ⊓
            Subgroup.centralizer (D : Set (StatedSp n K)))}
      exact le_sSup hPcomp
    have hPbot : spPull (F.tor d) (phi3 K) ≤ ⊥ := by
      rw [← spFixedFactor_inf_spSupported_phi3 hK (F.tor_pow_three hζo.pow_eq_one d)]
      exact le_inf (hPleJ.trans hJFd) (spPull_phi3_le_spSupported F d)
    have hPbot' : spPull (F.tor d) (phi3 K) = ⊥ := le_antisymm hPbot bot_le
    have hnt : Nontrivial ↥(spPull (F.tor d) (phi3 K)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hPq
    rw [hPbot'] at hnt
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
  have hzeroSet_d : F.zeroSet d = {i₀, a, b} := by
    ext i
    rw [F.mem_zeroSet, hdzero i]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hd_card : (F.zeroSet d).card = 3 := by
    have h1 : i₀ ∉ ({a, b} : Finset (Fin F.s)) := by simp [hai.symm, hbi.symm]
    have h2 : a ∉ ({b} : Finset (Fin F.s)) := by simp [hab]
    rw [hzeroSet_d, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  have hsum : (F.zeroSet d).card + (F.suppSet d).card = F.s := by
    have hzero : F.zeroSet d = Finset.univ.filter (fun i => d i = 0) := rfl
    have hsupp : F.suppSet d = Finset.univ.filter (fun i => d i ≠ 0) := rfl
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin F.s))) (p := fun i => d i = 0)
    have h' : (Finset.univ.filter (fun i => d i = 0)).card +
        (Finset.univ.filter (fun i => d i ≠ 0)).card = F.s := by
      simpa [Finset.card_univ] using h
    rw [hzero, hsupp]
    exact h'
  have hFle6 : F.s ≤ 6 := by omega
  have hkernel : ∀ f : Fin F.s → ZMod 3, F.tor f ∈ B → f a = 0 → f b = 0 →
      ∃ α β : ZMod 3, f = α • c + β • d := by
    intro f hfB hfa hfb
    have hF1C : spFixedFactor (F.tor (c + d)) ≤ Subgroup.centralizer {F.tor f} := by
      refine spFixedFactor_le_centralizer_tor F hK hζo (f := c + d) (h := f) (fun i hi => ?_)
      have hiZ : i ∈ F.zeroSet (c + d) := F.mem_zeroSet.mpr hi
      rw [hZab] at hiZ
      rcases Finset.mem_insert.mp hiZ with rfl | hiZ
      · exact hfa
      · rw [Finset.mem_singleton.mp hiZ]
        exact hfb
    have hfCJ : F.tor f ∈ Subgroup.centralizer (J : Set (StatedSp n K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.mp (hF1C (hJFcd hj))
    have hfD : F.tor f ∈ D := by
      rw [hDeq]
      exact ⟨hfB, hfCJ⟩
    have hfD' : F.tor f ∈ Subgroup.closure {F.tor c, F.tor d} := by
      rw [← hDgen]; exact hfD
    obtain ⟨α, β, hαβ⟩ := (mem_closure_pair_iff F hζo.pow_eq_one).mp hfD'
    exact ⟨α, β, F.tor_injective hζo hαβ⟩
  let P : AddSubgroup (Fin F.s → ZMod 3) :=
    { carrier := {f | F.tor f ∈ B}
      add_mem' := by
        intro f g hf hg
        change F.tor (f + g) ∈ B
        rw [F.tor_add hζo.pow_eq_one]
        exact Subgroup.mul_mem B hf hg
      zero_mem' := by
        change F.tor 0 ∈ B
        rw [F.tor_zero]
        exact Subgroup.one_mem B
      neg_mem' := by
        intro f hf
        change F.tor (-f) ∈ B
        have hneg : F.tor (-f) = (F.tor f)⁻¹ := by
          refine eq_inv_of_mul_eq_one_right ?_
          rw [← F.tor_add hζo.pow_eq_one]
          simp [F.tor_zero]
        rw [hneg]
        exact Subgroup.inv_mem B hf }
  have hPcard : 3 ^ 4 ≤ Nat.card P := by
    have h := card_eq_card_exps F hζo hBE
    have hP : Nat.card P = Nat.card B := by
      rw [h]
      rfl
    rw [hP]; exact hB
  let φ : P →+ ZMod 3 × ZMod 3 :=
    { toFun := fun f => ((f : Fin F.s → ZMod 3) a, (f : Fin F.s → ZMod 3) b)
      map_zero' := rfl
      map_add' := fun f g => rfl }
  let S : Set (Fin F.s → ZMod 3) := {f | ∃ α β : ZMod 3, f = α • c + β • d}
  have hS_card : Nat.card S = 9 := by
    have hbij : Function.Bijective (fun p : ZMod 3 × ZMod 3 =>
        (⟨p.1 • c + p.2 • d, ⟨p.1, p.2, rfl⟩⟩ : S)) := by
      constructor
      · rintro ⟨α, β⟩ ⟨α', β'⟩ h
        have h' : α • c + β • d = α' • c + β' • d := congrArg Subtype.val h
        have hzero : (α - α') • c + (β - β') • d = 0 := by
          have h1 : (α - α') • c + (β - β') • d =
              (α • c + β • d) - (α' • c + β' • d) := by module
          rw [h1, sub_eq_zero.mpr h']
        obtain ⟨h1, h2⟩ := hind (α - α') (β - β') hzero
        exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
      · rintro ⟨f, α, β, rfl⟩
        exact ⟨(α, β), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_zmod]
  have hker_sub : ∀ f : ↥φ.ker, f.1.1 ∈ S := by
    intro f
    have hf0 := AddMonoidHom.mem_ker.mp f.2
    have hfa : f.1.1 a = 0 := congrArg Prod.fst hf0
    have hfb : f.1.1 b = 0 := congrArg Prod.snd hf0
    obtain ⟨α, β, hαβ⟩ := hkernel f.1.1 f.1.2 hfa hfb
    exact ⟨α, β, hαβ⟩
  have hker_le : Nat.card ↥φ.ker ≤ 9 := by
    have hinj : Function.Injective (fun f : ↥φ.ker => (⟨f.1.1, hker_sub f⟩ : S)) := by
      intro f g h
      have hfun : (f.1 : Fin F.s → ZMod 3) = (g.1 : Fin F.s → ZMod 3) :=
        congrArg (fun x : S => (x : Fin F.s → ZMod 3)) h
      exact Subtype.ext (Subtype.ext hfun)
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [hS_card] at h
  have hP_eq : Nat.card P = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [← AddSubgroup.card_ker_mul_card_range φ, Nat.mul_comm]
  have hrange_ge : 9 ≤ Nat.card ↥φ.range := by
    have h81 : 81 ≤ Nat.card ↥φ.ker * Nat.card ↥φ.range := by
      have h := hPcard
      rw [hP_eq, Nat.mul_comm] at h
      exact h
    have hmono : Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ 9 * Nat.card ↥φ.range :=
      Nat.mul_le_mul_right _ hker_le
    have h9 : 9 * 9 ≤ 9 * Nat.card ↥φ.range := by
      calc 9 * 9 = 81 := by norm_num
        _ ≤ Nat.card ↥φ.ker * Nat.card ↥φ.range := h81
        _ ≤ 9 * Nat.card ↥φ.range := hmono
    exact Nat.le_of_mul_le_mul_left h9 (by norm_num)
  have hrange_le : Nat.card ↥φ.range ≤ 9 := by
    have h := Nat.card_le_card_of_injective
      (fun x : ↥φ.range => (x : ZMod 3 × ZMod 3)) Subtype.val_injective
    rwa [Nat.card_prod, Nat.card_zmod] at h
  have hrange_top : φ.range = ⊤ := by
    refine AddSubgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_prod, Nat.card_zmod]
    omega
  refine ⟨a, b, d, hai, hbi, hab, hdzero, hDB hdD, hFle6, hkernel, ?_⟩
  intro u v
  have hmem : (u, v) ∈ φ.range := by rw [hrange_top]; exact AddSubgroup.mem_top _
  obtain ⟨f, hf⟩ := (AddMonoidHom.mem_range).mp hmem
  exact ⟨f.1, f.2, congrArg Prod.fst hf, congrArg Prod.snd hf⟩

end A6InsideSp

end CFSG.StandardType
