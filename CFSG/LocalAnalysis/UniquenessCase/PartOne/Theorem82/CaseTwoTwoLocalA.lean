module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.RankThree.PartOne.CTP.StrongPTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem normalizer_le_of_le_AA {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {Q : Subgroup G} (hQA : Q ≤ t.d.AA)
    (hQ1 : Q ≠ ⊥) : Subgroup.normalizer (Q : Set G) ≤ c.S.M := by
  classical
  have hP01AA : (t.d.A 0 ⊔ t.d.A 1) ≤ t.d.AA := by
    rw [t.d.AA_def]
    exact le_sup_left
  by_cases hpair : ∃ i j : Fin 3, i ≠ j ∧ Q ≤ t.d.A i ⊔ t.d.A j
  · obtain ⟨i, j, hij, hQp⟩ := hpair
    exact hN.normalizer_le hij hQp hQ1
  push Not at hpair
  by_cases hbot : Q ⊓ (t.d.A 0 ⊔ t.d.A 1) = ⊥
  ·
    have hcomm : ∀ x ∈ Q, ∀ y ∈ (t.d.A 0 ⊔ t.d.A 1), x * y = y * x :=
      fun x hx y hy => t.d.isElemAbelian_AA.comm (hQA hx) (hP01AA hy)
    obtain ⟨hcardmul, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q (t.d.A 0 ⊔ t.d.A 1) hcomm
    have hcardP01 : Nat.card ↥(t.d.A 0 ⊔ t.d.A 1) = 9 := by
      rw [t.d.card_A_sup_A (by decide)]
      norm_num
    have hsup_card : Nat.card ↥(Q ⊔ (t.d.A 0 ⊔ t.d.A 1)) ≤ 27 := by
      rw [← t.d.card_AA]
      exact Subgroup.card_le_of_le (sup_le hQA hP01AA)
    have hQcard_le : Nat.card Q ≤ 3 := by
      rw [hbot, Subgroup.card_bot, hcardP01, mul_one] at hcardmul
      have h1 : Nat.card Q * 9 ≤ 27 := by
        rw [← hcardmul]
        exact hsup_card
      omega
    have hQcard_dvd : Nat.card Q ∣ 27 := by
      rw [← t.d.card_AA]
      exact Subgroup.card_dvd_of_le hQA
    have hQ3 : Nat.card Q = 3 := by
      have hQgt : 1 < Nat.card Q := by
        have hpos := Nat.card_pos (α := ↥Q)
        have hne1 : Nat.card Q ≠ 1 := fun h => hQ1 ((Subgroup.card_eq_one).mp h)
        omega
      have h23 : Nat.card Q = 2 ∨ Nat.card Q = 3 := by omega
      rcases h23 with h2 | h3
      · exfalso
        have hd : (2 : ℕ) ∣ 27 := h2 ▸ hQcard_dvd
        norm_num at hd
      · exact h3
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
    have hx1G : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxAA : (x : G) ∈ t.d.AA := hQA x.2
    have hxpow : (x : G) ^ 3 = 1 := t.d.isElemAbelian_AA.2 (x : G) hxAA
    have hxord : orderOf (x : G) = 3 := orderOf_eq_prime hxpow hx1G
    have hQeq : Q = Subgroup.zpowers (x : G) := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_).symm
      rw [Nat.card_zpowers, hxord, hQ3]
    have hxnotpair : ∀ i j : Fin 3, i ≠ j → (x : G) ∉ t.d.A i ⊔ t.d.A j := by
      intro i j hij hmem
      apply hpair i j hij
      rw [hQeq]
      exact Subgroup.zpowers_le.mpr hmem
    have hxij : ∀ i j : Fin 3, (x : G) ∉ t.d.A i ⊔ t.d.A j := by
      intro i j hmem
      by_cases hij : i = j
      · subst hij
        obtain ⟨j', hj'⟩ : ∃ j' : Fin 3, j' ≠ i := by
          fin_cases i
          · exact ⟨1, by decide⟩
          · exact ⟨0, by decide⟩
          · exact ⟨0, by decide⟩
        exact hxnotpair i j' (Ne.symm hj') (Subgroup.mem_sup_left (by simpa using hmem))
      · exact hxnotpair i j hij hmem
    obtain ⟨l, hlL, hlZ⟩ := t.exists_conj_mem_Z hxAA hxij
    have hzord : orderOf (l * (x : G) * l⁻¹) = 3 := by
      simpa [MulAut.conj_apply, hxord] using (MulAut.conj l).orderOf_eq (x : G)
    have hZgen : t.Z = Subgroup.zpowers (l * (x : G) * l⁻¹) := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hlZ) ?_).symm
      rw [Nat.card_zpowers, hzord, t.card_Z]
    have hQZ : Q.map (MulAut.conj l).toMonoidHom = t.Z := by
      rw [hQeq, MonoidHom.map_zpowers]
      simpa [MulAut.conj_apply] using hZgen.symm
    have hlM : l ∈ c.S.M := c.hyp81.1 (t.hdL ▸ hlL)
    intro g hg
    have hgmap : Q.map (MulAut.conj g).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hcomp : (MulAut.conj (l * g * l⁻¹)).toMonoidHom.comp
        (MulAut.conj l).toMonoidHom =
        (MulAut.conj l).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hnorm : l * g * l⁻¹ ∈ Subgroup.normalizer (t.Z : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc t.Z.map (MulAut.conj (l * g * l⁻¹)).toMonoidHom
          = (Q.map (MulAut.conj l).toMonoidHom).map
              (MulAut.conj (l * g * l⁻¹)).toMonoidHom := by rw [hQZ]
        _ = Q.map ((MulAut.conj (l * g * l⁻¹)).toMonoidHom.comp
              (MulAut.conj l).toMonoidHom) := by rw [Subgroup.map_map]
        _ = Q.map ((MulAut.conj l).toMonoidHom.comp
              (MulAut.conj g).toMonoidHom) := by rw [hcomp]
        _ = (Q.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj l).toMonoidHom := by rw [← Subgroup.map_map]
        _ = Q.map (MulAut.conj l).toMonoidHom := by rw [hgmap]
        _ = t.Z := hQZ
    have hlgM : l * g * l⁻¹ ∈ c.S.M := t.normalizer_Z_le hp hN hZ hnorm
    have hg_eq : g = l⁻¹ * (l * g * l⁻¹) * l := by group
    rw [hg_eq]
    exact c.S.M.mul_mem (c.S.M.mul_mem (c.S.M.inv_mem hlM) hlgM) hlM
  ·
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hw1G : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
    obtain ⟨hwQ, hwP⟩ := Subgroup.mem_inf.mp w.2
    have hle : c.S.M ⊓ Subgroup.centralizer ((t.d.A 0 ⊔ t.d.A 1 : Subgroup G) : Set G)
        ≤ c.S.M ⊓ Subgroup.centralizer
          ((Subgroup.zpowers (w : G) : Subgroup G) : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hwP))
    have hdvd : p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer
        ((Subgroup.zpowers (w : G) : Subgroup G) : Set G) : Subgroup G) :=
      (hN.dvd_card (i := 0) (j := 1) (by decide)).trans (Subgroup.card_dvd_of_le hle)
    intro g hg
    have hgmap : Q.map (MulAut.conj g).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hxQ : g * (w : G) * g⁻¹ ∈ Q := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hwQ
      rw [hgmap] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hx1 : g * (w : G) * g⁻¹ ≠ 1 := by
      intro h
      apply hw1G
      calc (w : G) = g⁻¹ * (g * (w : G) * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hCx : Subgroup.centralizer ({g * (w : G) * g⁻¹} : Set G) ≤ c.S.M :=
      t.centralizer_le_of_mem_AA hN hZ (hQA hxQ) hx1
    have hX : Subgroup.centralizer
        ((Subgroup.zpowers (g * (w : G) * g⁻¹) : Subgroup G) : Set G) ≤ c.S.M := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hCx
    have hmapX : (Subgroup.zpowers (g * (w : G) * g⁻¹)).map
        (MulAut.conj g⁻¹).toMonoidHom = Subgroup.zpowers (w : G) := by
      rw [MonoidHom.map_zpowers]
      congr 1
      show g⁻¹ * (g * (w : G) * g⁻¹) * (g⁻¹)⁻¹ = (w : G)
      group
    have hdvd' : p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer
        (((Subgroup.zpowers (g * (w : G) * g⁻¹)).map
          (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) : Subgroup G) := by
      rw [hmapX]
      exact hdvd
    have hginv : g⁻¹ ∈ c.S.M :=
      (c.isStronglyPEmbedded_of_mem_sigma hp).mem_of_centralizer_le hX hdvd'
    simpa using c.S.M.inv_mem hginv

theorem le_M_of_isTwoLocal_of_le_AA {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {B H : Subgroup G} (hBA : B ≤ t.d.AA)
    (hB : 2 ≤ CFSG.Open.pRank 3 B) (hH : CFSG.Open.IsTwoLocal H) (hBH : B ≤ H) :
    H ≤ c.S.M := by
  have hAAM : t.d.AA ≤ c.S.M := by
    have h := c.hyp81.1
    rw [← t.hdL] at h
    exact t.d.AA_le_L.trans h
  have hB3 : IsPGroup 3 ↥B := IsPGroup.to_le t.d.hS.isPGroup (hBA.trans t.d.AA_le_S)
  have hBM : B ≤ c.S.M := hBA.trans hAAM
  have hΓ : CFSG.Open.rankThreeGamma 1 3 B ≤ c.S.M :=
    sSup_le fun N hNmem => by
      obtain ⟨Q, hQ, hk, rfl⟩ := hNmem
      refine t.normalizer_le_of_le_AA hp hN hZ (hQ.trans hBA) ?_
      intro hbot
      have h3 : 3 ∣ Nat.card Q :=
        CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hk
      rw [hbot, Subgroup.card_bot] at h3
      omega
  exact c.theoremC 3 Nat.prime_three (by norm_num) B hBM hB3 hB hΓ H hH hBH

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
