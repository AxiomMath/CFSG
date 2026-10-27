module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporAll
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Nine

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open Subgroup

@[expose] def K423J4ThetaCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J4) →
    ∀ b : X, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) ≤
        Subgroup.center (Subgroup.centralizer ({b} : Set X))

namespace Res423Three

open Res423Two Item434SporGen

section Criterion

variable {X : Type} [Group X] [Finite X]

theorem forall_comm_of_mem_theta (hZ : Subgroup.center X = ⊥) {Y : Subgroup (MulAut X)}
    (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) {b₀ : X}
    (hθ : aschbacherSolvableCore 3 (Subgroup.centralizer ({b₀} : Set X)) ≤
      Subgroup.center (Subgroup.centralizer ({b₀} : Set X)))
    {b : Y} (hb : (b : MulAut X) = MulAut.conj b₀) {q : Y}
    (hq : q ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)))
    {w : X} (hw : (q : MulAut X) = MulAut.conj w) :
    ∀ c ∈ Subgroup.centralizer ({b₀} : Set X), w * c = c * w := by
  have hinj := conj_injective_of_center hZ
  set C := Subgroup.centralizer ({b} : Set Y) with hC
  set Q := inSubgroup (aschbacherSolvableCore 3) C with hQ
  set C₀ := Subgroup.centralizer ({b₀} : Set X) with hC₀
  have hγ : ∀ x ∈ C₀, (⟨MulAut.conj x, hY ⟨x, rfl⟩⟩ : Y) ∈ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change MulAut.conj x * (b : MulAut X) = (b : MulAut X) * MulAut.conj x
    rw [hb, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]
  set W : Subgroup X := ((Q.map Y.subtype).comap (MulAut.conj : X →* MulAut X)) ⊓ C₀ with hW
  have hWC : W ≤ C₀ := inf_le_right
  set N := W.subgroupOf C₀ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hn1, hn2⟩ := hn
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk, hkn⟩ := hn1
      have hgC := hγ g g.2
      refine ⟨⟨MulAut.conj (g : X), hY ⟨_, rfl⟩⟩ * k * (⟨MulAut.conj (g : X), hY ⟨_, rfl⟩⟩ : Y)⁻¹,
        conj_mem_inSubgroup_theta' hgC hk, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
        rw [show ((k : MulAut X)) = MulAut.conj ((n : C₀) : X) from hkn]
        simp only [map_mul, map_inv]
    · exact (g * n * g⁻¹).2
  let f : N →* (Q.map Y.subtype) :=
    { toFun := fun n => ⟨MulAut.conj ((n : C₀) : X), (Subgroup.mem_subgroupOf.mp n.2).1⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : MulAut.conj ((x : C₀) : X) = MulAut.conj ((y : C₀) : X) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext (hinj h1))
  have hNs : Group.IsSolvable N := by
    have hQs : Group.IsSolvable (Q.map Y.subtype) := by
      have := isSolvable_inSubgroup_theta C
      exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective Y.subtype Q)
    exact Group.isSolvable_of_isSolvable_injective hf
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    apply not_three_dvd_card_inSubgroup_theta C
    have hcard : Nat.card N ∣ Nat.card (Q.map Y.subtype) := Subgroup.card_dvd_of_injective f hf
    rw [Subgroup.card_map_of_injective Y.subtype_injective] at hcard
    exact h3.trans hcard
  have hle := (solvable_prime_complement_core_characterization (H := C₀)
    Nat.prime_three).2.2.2.1 N hNn hNs hN3
  have hwC₀ : w ∈ C₀ := by
    have hqC : q ∈ C := inSubgroup_theta_le C hq
    have h1 : (q : MulAut X) * (b : MulAut X) = (b : MulAut X) * (q : MulAut X) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hqC)
    rw [hw, hb, ← map_mul, ← map_mul] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hinj h1)
  have hwW : w ∈ W := ⟨⟨q, hq, hw⟩, hwC₀⟩
  have hwN : (⟨w, hwC₀⟩ : C₀) ∈ N := Subgroup.mem_subgroupOf.mpr hwW
  have hwZ := hθ (hle hwN)
  intro c hc
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨c, hc⟩).symm

theorem alphaVanishes_of_central_fixGen (hZ : Subgroup.center X = ⊥)
    (hinn : ∀ φ : MulAut X, φ ∈ (MulAut.conj : X →* MulAut X).range)
    {D : Subgroup X} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hθ : ∀ b ∈ D, b ≠ 1 → aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) ≤
      Subgroup.center (Subgroup.centralizer ({b} : Set X)))
    (hgen : FixGen D) : AlphaVanishes X D := by
  intro Y hY
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  have hkey : ∀ b ∈ B, b ≠ 1 → ∃ b₀ ∈ D, b₀ ≠ 1 ∧ (b : MulAut X) = MulAut.conj b₀ ∧
      ∀ q ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)),
        ∃ w : X, (q : MulAut X) = MulAut.conj w ∧
          ∀ c ∈ Subgroup.centralizer ({b₀} : Set X), w * c = c * w := by
    intro b hb hb1
    obtain ⟨b₀, hb₀, hbb₀⟩ := Subgroup.mem_subgroupOf.mp hb
    have hb₀1 : b₀ ≠ 1 := by
      rintro rfl
      apply hb1
      apply Subtype.ext
      rw [← hbb₀]
      simp
    refine ⟨b₀, hb₀, hb₀1, hbb₀.symm, fun q hq => ?_⟩
    obtain ⟨w, hw⟩ := hinn (q : MulAut X)
    exact ⟨w, hw.symm, forall_comm_of_mem_theta hZ hY (hθ b₀ hb₀ hb₀1) hbb₀.symm hq hw.symm⟩
  have hJ : thetaJ 3 B = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    obtain ⟨b₀, hb₀, -, -, hq⟩ := hkey b hb hb1
    rw [Subgroup.commutator_le]
    intro q hq' d hd
    obtain ⟨w, hqw, hwc⟩ := hq q hq'
    obtain ⟨d₀, hd₀, hdd₀⟩ := Subgroup.mem_subgroupOf.mp hd
    have hd₀C : d₀ ∈ Subgroup.centralizer ({b₀} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hDc d₀ hd₀ b₀ hb₀)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hdd₀, hqw, ← map_mul, ← map_mul, hwc d₀ hd₀C]
  have hT : thetaT 3 B = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    obtain ⟨w, hw⟩ := hinn (t : MulAut X)
    have hwc : ∀ x : X, (∃ p ∈ D, p ≠ 1 ∧ p * x = x * p) → w * x = x * w := by
      rintro x ⟨p, hp, hp1, hpx⟩
      have hpY : MulAut.conj p ∈ Y := hY ⟨p, rfl⟩
      set bp : Y := ⟨MulAut.conj p, hpY⟩
      have hbB : bp ∈ B := Subgroup.mem_subgroupOf.mpr ⟨p, hp, rfl⟩
      have hb1 : bp ≠ 1 := by
        intro h1
        apply hp1
        apply hinj
        rw [map_one]
        exact congrArg Subtype.val h1
      have htb : t ∈
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({bp} : Set Y)) := by
        have h1 := Subgroup.mem_iInf.mp ht bp
        have h2 := Subgroup.mem_iInf.mp h1 hbB
        exact Subgroup.mem_iInf.mp h2 hb1
      exact forall_comm_of_mem_theta hZ hY (hθ p hp hp1) rfl htb hw.symm x
        (Subgroup.mem_centralizer_singleton_iff.mpr hpx.symm)
    obtain ⟨S, hS, hSgen⟩ := hgen
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({w} : Set X) := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨-, p, hp, hp1, hpx⟩ := hSgen x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hwc x ⟨p, hp, hp1, hpx⟩).symm
    have hwZ : w ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hS (Subgroup.mem_top x)))
    rw [hZ, Subgroup.mem_bot] at hwZ
    apply Subtype.ext
    rw [← hw, hwZ, map_one]
    rfl
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

end Criterion

theorem fixGen_map_mulEquiv {M X : Type*} [Group M] [Group X] (e : M ≃* X) {P : Subgroup M}
    (h : FixGen P) : FixGen (P.map e.toMonoidHom) := by
  obtain ⟨S, hS, hgen⟩ := h
  refine ⟨e '' S, ?_, ?_⟩
  · intro x _
    have hx : e.symm x ∈ Subgroup.closure S := hS (Subgroup.mem_top _)
    have h1 : e (e.symm x) ∈ (Subgroup.closure S).map e.toMonoidHom := ⟨_, hx, rfl⟩
    rw [MonoidHom.map_closure] at h1
    simpa using h1
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨hσ3, p, hp, hp1, hpσ⟩ := hgen σ hσ
    refine ⟨by rw [MulEquiv.orderOf_eq]; exact hσ3, e p, ⟨p, hp, rfl⟩, ?_, ?_⟩
    · intro h1
      apply hp1
      apply e.injective
      rw [h1, map_one]
    · rw [← map_mul, ← map_mul, hpσ]

end Res423Three

open Res423Three

theorem k423SporJ4_of
    (h : K423J4ThetaCentral) : K423SporJ4 := by
  rintro X _ _ ⟨φ⟩
  have hcardJ : Nat.card NativeSporadic.J4 = 86775571046077562880 := CFSG.Sporadic.J4.card_J4
  have : Finite NativeSporadic.J4 := Nat.finite_of_card_ne_zero (by rw [hcardJ]; norm_num)
  have hL : (Nat.card NativeSporadic.J4).factorization 3 = 3 := by
    rw [hcardJ, show (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  have hcardC : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  have hcardX : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr φ.toEquiv, hcardC]
  have := CFSG.Sporadic.J4.isSimpleGroup_J4
  have hsimple : IsSimpleGroup X := MulEquiv.isSimpleGroup (H := NativeSporadic.J4) φ
  have hinn : ∀ ψ : MulAut X, ψ ∈ (MulAut.conj : X →* MulAut X).range := by
    have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≤ 1 :=
      CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.AGLEmbedding.card_outer_J4.le φ
    have : Finite (MulAut X) := MulEquiv.finite_left
    have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
      Nat.card_pos
    have hidx : (CFSG.ComponentClassification.OuterAutomorphisms.inner X).index = 1 := by
      change Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 1
      omega
    intro ψ
    change ψ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X
    rw [Subgroup.index_eq_one.mp hidx]
    exact Subgroup.mem_top ψ
  refine Res423Two.census423_of_alphaVanishes fun D hD hD9 => ?_
  have hD1 : D ≠ ⊥ := Res423Two.ne_bot_of_card_nine hD9
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
    · exact hc
    · exfalso
      have hDn : D.Normal := ⟨fun n hn g => by
        have hg : g ∈ Subgroup.center X := hc ▸ Subgroup.mem_top g
        rw [← Subgroup.mem_center_iff.mp hg n, mul_inv_cancel_right]
        exact hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with hDb | hDt
      · exact hD1 hDb
      · rw [hDt, Subgroup.card_top, hcardX] at hD9
        norm_num at hD9
  have hgen : Item434SporGen.FixGen D := by
    have h9 : Nat.card (D.map φ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective φ.injective, hD9]
    have h1 := fixGen_map_mulEquiv φ.symm (ONanJ4Nine.fixGen_j4 hL _ h9)
    have h2 : (D.map φ.toMonoidHom).map φ.symm.toMonoidHom = D := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id D
      ext x
      simp
    rwa [h2] at h1
  exact alphaVanishes_of_central_fixGen hZ hinn (Res423Two.comm_of_isElemAbelian hD.prop)
    (fun b hb hb1 => h X ⟨φ⟩ b (hD.prop.2 b hb) hb1) hgen

end CFSG.RankThree.PartTwo.Sec4
