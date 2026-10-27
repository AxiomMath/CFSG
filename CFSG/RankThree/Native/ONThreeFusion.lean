module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.ON
public import Certificates.Certificate9590

public section

namespace CFSG.RankThree.Native

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaON CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint Subgroup
open scoped Pointwise

@[expose] def onThreeOrb : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4), (0, 5), (1, 5),
    (0, 6), (1, 6), (0, 7), (1, 7), (0, 8), (1, 8), (0, 9), (1, 9), (0, 10), (1, 10), (0, 11),
    (1, 11), (0, 12), (1, 12), (0, 13), (0, 14), (1, 14), (0, 15), (1, 15), (0, 17), (1, 17),
    (0, 18), (1, 18), (0, 19), (0, 20), (0, 21), (1, 21), (0, 22), (1, 22), (0, 24), (0, 25),
    (0, 27), (1, 27), (0, 28), (0, 29), (0, 30), (1, 30), (1, 31), (0, 32), (1, 32), (0, 33),
    (1, 33), (0, 34), (0, 35), (1, 36), (0, 37), (1, 37), (1, 38), (0, 39), (0, 40), (1, 40),
    (0, 42), (1, 44), (0, 45), (1, 46), (1, 47), (0, 48), (1, 48), (0, 52), (0, 55), (1, 55),
    (0, 61), (0, 65), (1, 65), (0, 67), (1, 70), (0, 73)]

@[expose] def onThreeTarget : List (List ℕ) :=
  (allVecs 3 4).filter fun c => !c.all (· == 0)

theorem onThree_orbChk : onMod.orbChk 3 onThreeTarget [[1, 0, 0, 0]] onThreeOrb = true := by
  decide +kernel

section Conj

variable {X : Type} [Group X] {p : ℕ} [NeZero p]

theorem orbChk_conj (m : NMod) (a : Fin m.basis.length → X) (gOf : NAct → X)
    (hcomm : ∀ i j, a i * a j = a j * a i) (hpow : ∀ i, a i ^ p = 1)
    (hg : ∀ g ∈ m.acts, ∀ i, gOf g * a i * (gOf g)⁻¹ =
      preElt a (fun k => actMatN p m.basis.length g k i)) (target : List (List ℕ)) (a₀ : X) :
    ∀ (orb : List (ℕ × ℕ)) (known : List (List ℕ)),
      (∀ c ∈ known, ∃ h : X, h * a₀ * h⁻¹ = preElt a (vecOf p m.basis.length c)) →
      m.orbChk p target known orb = true →
      ∀ c ∈ target, ∃ h : X, h * a₀ * h⁻¹ = preElt a (vecOf p m.basis.length c)
  | [], known, hk, h => by
    intro c hc
    simp only [NMod.orbChk, List.all_eq_true] at h
    exact hk c (List.mem_of_elem_eq_true (h c hc))
  | (j, par) :: rest, known, hk, h => by
    simp only [NMod.orbChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, hpar⟩, hrest⟩ := h
    refine orbChk_conj m a gOf hcomm hpow hg target a₀ rest _ ?_ hrest
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hk c hc
    · rw [List.mem_singleton] at hc
      subst hc
      have hgmem : m.acts.getD j default ∈ m.acts := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_mem hj
      have hmem : known.getD par [] ∈ known := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpar, Option.getD_some]
        exact List.getElem_mem hpar
      obtain ⟨h₀, hh₀⟩ := hk _ hmem
      refine ⟨gOf (m.acts.getD j default) * h₀, ?_⟩
      rw [vecOf_matVecL, ← actMatN_eq_toMatL, ← pre_conj_elt hcomm hpow (hg _ hgmem), ← hh₀]
      group

end Conj

theorem factorization_card_ON :
    (Nat.card NativeSporadic.ON).factorization 3 = 4 := by
  rw [CFSG.Sporadic.ON.card_ON, show (460815505920 : ℕ) = 3 ^ 4 * 5689080320 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Fusion


theorem onThree_fusion {x y : NativeSporadic.ON} (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ k : NativeSporadic.ON, k * x * k⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite NativeSporadic.ON :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  have h := Certificates.certificate9590
  unfold absCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hC, hw⟩, hn4⟩, ha⟩, hb⟩, hfun⟩, halt⟩ := h
  have hf : ∀ f ∈ onMod.facts 3, f ∈ (⟨onNregs, onProg, onMod.facts 3⟩ : MCert).facts :=
    fun f hf => hf
  let D := NMod.spec (spec3 154) hC onMod hf hw
  have hg : ∀ g ∈ onMod.acts, ∀ i : Fin onMod.basis.length,
      regUnit (spec3 154) hC g.reg * D.a i * (regUnit (spec3 154) hC g.reg)⁻¹ =
        preElt D.a (fun k => actMatN 3 onMod.basis.length g k i) :=
    fun g hgm i => act_N (spec3 154) hC hf hgm i
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : NativeSporadic.ON,
      a₀ = preElt D.a (vecOf 3 onMod.basis.length [1, 0, 0, 0]) := ⟨_, rfl⟩
  have hconj := orbChk_conj onMod D.a (fun g => regUnit (spec3 154) hC g.reg) D.comm D.pow hg
    onThreeTarget a₀ onThreeOrb [[1, 0, 0, 0]] (by
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨1, by rw [one_mul, inv_one, mul_one, ha₀]; rfl⟩) onThree_orbChk
  let S : Sylow 3 NativeSporadic.ON := Sylow.ofCard D.span (by
    rw [D.card_span Nat.prime_three, factorization_card_ON]
    rfl)
  have key : ∀ z : NativeSporadic.ON, orderOf z = 3 →
      ∃ k : NativeSporadic.ON, k * z * k⁻¹ = a₀ := by
    intro z hz
    have hp : IsPGroup 3 (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq NativeSporadic.ON Q S
    have hzmem : u * z * u⁻¹ ∈ D.span := by
      have h1 : MulAut.conj u • z ∈ MulAut.conj u • (Q : Subgroup NativeSporadic.ON) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (mem_zpowers z))
      rwa [← Sylow.coe_subgroup_smul, hu, MulAut.smul_def, MulAut.conj_apply] at h1
    obtain ⟨c, hc⟩ := D.exists_elt hzmem
    have hcne : c ≠ 0 := by
      rintro rfl
      rw [D.elt_zero] at hc
      have hz1 : z = 1 := by
        have := congrArg (fun y => u⁻¹ * y * u) hc
        simpa [mul_assoc] using this.symm
      rw [hz1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    set l : List ℕ := List.ofFn fun k => (c k).val with hl
    have hlen : l.length = onMod.basis.length := by rw [hl, List.length_ofFn]; rfl
    have hlt : ∀ x ∈ l, x < 3 := by
      intro x hx
      simp only [hl, List.mem_ofFn'] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ZMod.val_lt _
    have hmem : l ∈ allVecs 3 onMod.basis.length := (mem_allVecs 3 _ l).2 ⟨hlen, hlt⟩
    have hnz : ¬ (l.all (· == 0)) = true := by
      intro hall
      obtain ⟨k0, hk0⟩ := Function.ne_iff.1 hcne
      have := List.all_eq_true.1 hall (c k0).val (by simp [hl])
      have h0 : (c k0).val = 0 := by simpa using this
      exact hk0 ((ZMod.val_eq_zero _).1 h0)
    have htarget : l ∈ onThreeTarget := by
      rw [onThreeTarget, List.mem_filter]
      exact ⟨hmem, by simpa using hnz⟩
    have hvec : vecOf 3 onMod.basis.length l = c := by
      funext k
      have hk : (k : ℕ) < D.n := k.2
      simp only [vecOf, hl, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, dite_eq_left,
        Option.getD_some, ZMod.natCast_zmod_val]
      rfl
    obtain ⟨h, hh⟩ := hconj l htarget
    rw [hvec] at hh
    have hh2 : h * a₀ * h⁻¹ = u * z * u⁻¹ := hh.trans hc
    refine ⟨h⁻¹ * u, ?_⟩
    calc h⁻¹ * u * z * (h⁻¹ * u)⁻¹ = h⁻¹ * (u * z * u⁻¹) * h := by group
      _ = h⁻¹ * (h * a₀ * h⁻¹) * h := by rw [hh2]
      _ = a₀ := by group
  obtain ⟨kx, hkx⟩ := key x hx
  obtain ⟨ky, hky⟩ := key y hy
  refine ⟨ky⁻¹ * kx, ?_⟩
  calc ky⁻¹ * kx * x * (ky⁻¹ * kx)⁻¹ = ky⁻¹ * (kx * x * kx⁻¹) * ky := by group
    _ = ky⁻¹ * (ky * y * ky⁻¹) * ky := by rw [hkx, hky]
    _ = y := by group

end Fusion

end CFSG.RankThree.Native
