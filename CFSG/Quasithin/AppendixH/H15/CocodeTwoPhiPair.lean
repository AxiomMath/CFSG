module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhi
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoNorm
public import CFSG.Quasithin.AppendixH.Common.OctadYAct

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

namespace PhiData

variable (P : PhiData O β)

private theorem mul_inv_mem_ker_of_isVecOf {e f : PM24} {v : V}
    (hv : IsVecOf (mathModel false d a b Γ) β e v)
    (hw : IsVecOf (mathModel false d a b Γ) β f v) :
    e * f⁻¹ ∈ (mathModel false d a b Γ).ker := by
  obtain ⟨he, hve⟩ := hv
  obtain ⟨hf, hwf⟩ := hw
  have hq : (QuotientGroup.mk (⟨e, he⟩ : ↥(mathModel false d a b Γ).sec) :
      ↥(mathModel false d a b Γ).sec ⧸
        (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) =
      QuotientGroup.mk (⟨f, hf⟩ : ↥(mathModel false d a b Γ).sec) := by
    rw [← hve, hwf]
  have hmem : (⟨e, he⟩ : ↥(mathModel false d a b Γ).sec)⁻¹ * ⟨f, hf⟩ ∈
      (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec :=
    QuotientGroup.eq.mp hq
  rw [Subgroup.mem_subgroupOf] at hmem
  have hmem' : e⁻¹ * f ∈ (mathModel false d a b Γ).ker := by
    change e⁻¹ * f ∈ (mathModel false d a b Γ).ker at hmem
    exact hmem
  have heq : e⁻¹ * f = e * f⁻¹ := by simp [inv24_eq]
  rwa [heq] at hmem'

private theorem eY_mul_eq_pair (X Y : Finset (Fin 24)) : eY X * eY Y = eY (symmDiff X Y) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_symmDiff]
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [hx, hy] <;> decide

private theorem ker_eq_of_ne22 (hd : d ≠ 22) :
    (mathModel false d a b Γ).ker = golayC := by
  unfold mathModel FFModel.golaySec
  exact if_neg hd

private theorem ker_eq_of_eq22 (hd : d = 22) :
    (mathModel false d a b Γ).ker = golayC ⊔ Subgroup.zpowers (pairVec a b) := by
  unfold mathModel FFModel.golaySec
  exact if_pos hd

private theorem fin8_eq_zero_or_one_of_not_two_le {p : Fin 8} (hp : ¬ 2 ≤ p.val) :
    p = 0 ∨ p = 1 := by
  have h : p.val = 0 ∨ p.val = 1 := by omega
  rcases h with h | h
  · left; exact Fin.ext (by simpa using h)
  · right; exact Fin.ext (by simpa using h)

theorem pair_stab (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {g : ↥Γ} {p q : Fin 8} (hpq : p ≠ q)
    (h22 : d = 22 → P.o p ≠ a ∧ P.o p ≠ b ∧ P.o q ≠ a ∧ P.o q ≠ b)
    (hfix : ρ g (P.φ (Multiplicative.ofAdd (evPair p q))) =
      P.φ (Multiplicative.ofAdd (evPair p q))) :
    ({(g : S24) (P.o p), (g : S24) (P.o q)} : Finset (Fin 24)) = {P.o p, P.o q} := by
  have hv : IsVecOf (mathModel false d a b Γ) β (pairVec (P.o p) (P.o q))
      (P.φ (Multiplicative.ofAdd (evPair p q))) := P.isVecOf_pair hM hpq
  have hv_act : IsVecOf (mathModel false d a b Γ) β
      (G6.permAct 24 (g : S24) (pairVec (P.o p) (P.o q)))
      (ρ g (P.φ (Multiplicative.ofAdd (evPair p q)))) := isVecOf_act hM hv g
  rw [permAct_pairVec, hfix] at hv_act
  have hmem := mul_inv_mem_ker_of_isVecOf hv_act hv
  have hne_g : (g : S24) (P.o p) ≠ (g : S24) (P.o q) :=
    fun h => hpq (P.o_inj ((g : S24).injective h))
  have hne_ij : P.o p ≠ P.o q := fun h => hpq (P.o_inj h)
  have hker : eY ({(g : S24) (P.o p), (g : S24) (P.o q)} : Finset (Fin 24)) *
      eY ({P.o p, P.o q} : Finset (Fin 24)) ∈ (mathModel false d a b Γ).ker := by
    rwa [pairVec_eq_eY_pair _ _ hne_g, pairVec_eq_eY_pair _ _ hne_ij, inv24_eq] at hmem
  have hc1 : ({(g : S24) (P.o p), (g : S24) (P.o q)} : Finset (Fin 24)).card = 2 :=
    Finset.card_pair hne_g
  have hc2 : ({P.o p, P.o q} : Finset (Fin 24)).card = 2 := Finset.card_pair hne_ij
  have hcard : ({(g : S24) (P.o p), (g : S24) (P.o q)} : Finset (Fin 24)).card +
      ({P.o p, P.o q} : Finset (Fin 24)).card < 8 := by rw [hc1, hc2]; norm_num
  by_cases hd : d = 22
  · have hker_eq := ker_eq_of_eq22 (d := d) (a := a) (b := b) (Γ := Γ) hd
    have hsup : eY ({(g : S24) (P.o p), (g : S24) (P.o q)} : Finset (Fin 24)) *
        eY ({P.o p, P.o q} : Finset (Fin 24)) ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) := by
      rwa [hker_eq] at hker
    rcases (mem_sup_zpowers_iff' (pairVec_sq a b) _).mp hsup with hgolay | hprod
    · exact (eY_mul_eY_mem_golayC_iff _ _ hcard).mp hgolay
    · exfalso
      let U : Finset (Fin 24) := {(g : S24) (P.o p), (g : S24) (P.o q)}
      let W : Finset (Fin 24) := {P.o p, P.o q}
      let Tset : Finset (Fin 24) := symmDiff (symmDiff U W) ({a, b} : Finset (Fin 24))
      have hprod' : (eY U * eY W) * pairVec a b ∈ golayC := hprod
      have hcases : eY Tset ∈ golayC := by
        dsimp only [Tset]
        rwa [eY_mul_eq_pair U W, pairVec_eq_eY_pair a b hM.cfg.ne,
          eY_mul_eq_pair (symmDiff U W) ({a, b} : Finset (Fin 24))] at hprod'
      have hsub : Tset ⊆ U ∪ W ∪ ({a, b} : Finset (Fin 24)) := by
        intro x hx
        dsimp only [Tset] at hx
        rw [Finset.mem_symmDiff] at hx
        rcases hx with ⟨hx1, -⟩ | ⟨hx2, -⟩
        · rw [Finset.mem_symmDiff] at hx1
          rcases hx1 with ⟨hxU, -⟩ | ⟨hxW, -⟩
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxU)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxW)
        · exact Finset.mem_union_right _ hx2
      have hle : Tset.card ≤ 6 := by
        calc Tset.card ≤ (U ∪ W ∪ ({a, b} : Finset (Fin 24))).card := Finset.card_le_card hsub
          _ ≤ (U ∪ W).card + ({a, b} : Finset (Fin 24)).card := Finset.card_union_le _ _
          _ ≤ (U.card + W.card) + ({a, b} : Finset (Fin 24)).card :=
              Nat.add_le_add_right (Finset.card_union_le U W) _
          _ = 6 := by
              rw [show U.card = 2 from hc1, show W.card = 2 from hc2,
                Finset.card_pair hM.cfg.ne]
      have hTempty : Tset = ∅ := (eY_mem_golayC_iff Tset (by omega)).mp hcases
      have hsdeq : symmDiff U W = ({a, b} : Finset (Fin 24)) :=
        Finset.symmDiff_eq_empty.mp hTempty
      have haU : a ∈ U := by
        have ha : a ∈ symmDiff U W := by
          rw [hsdeq]
          exact Finset.mem_insert_self a {b}
        rw [Finset.mem_symmDiff] at ha
        rcases ha with ⟨haU, -⟩ | ⟨haW, -⟩
        · exact haU
        · exfalso
          rw [Finset.mem_insert, Finset.mem_singleton] at haW
          rcases haW with h | h
          · exact (h22 hd).1 h.symm
          · exact (h22 hd).2.2.1 h.symm
      have hΓle : Γ ≤ M2ab a b := by
        rcases mctx_cases hM with ⟨h24, -⟩ | ⟨h23, -⟩ | ⟨-, -, hle'⟩
        · exact absurd (h24.symm.trans hd) (by norm_num)
        · exact absurd (h23.symm.trans hd) (by norm_num)
        · exact hle'
      have hswap := ((mem_M2ab_iff a b hM.cfg.ne (g : S24)).1 (hΓle g.2)).2
      rw [Finset.mem_insert, Finset.mem_singleton] at haU
      rcases haU with hgi | hgj
      · have hi : P.o p = (g : S24).symm a := by
          calc P.o p = (g : S24).symm ((g : S24) (P.o p)) :=
                (Equiv.symm_apply_apply (g : S24) (P.o p)).symm
            _ = (g : S24).symm a := congrArg (g : S24).symm hgi.symm
        rcases hswap with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
        · have hsa : (g : S24).symm a = a := by
            have := (congrArg (g : S24).symm hga).symm
            simpa using this
          exact (h22 hd).1 (hi.trans hsa)
        · have hsb : (g : S24).symm a = b := by
            have := (congrArg (g : S24).symm hgb).symm
            simpa using this
          exact (h22 hd).2.1 (hi.trans hsb)
      · have hj : P.o q = (g : S24).symm a := by
          calc P.o q = (g : S24).symm ((g : S24) (P.o q)) :=
                (Equiv.symm_apply_apply (g : S24) (P.o q)).symm
            _ = (g : S24).symm a := congrArg (g : S24).symm hgj.symm
        rcases hswap with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
        · have hsa : (g : S24).symm a = a := by
            have := (congrArg (g : S24).symm hga).symm
            simpa using this
          exact (h22 hd).2.2.1 (hj.trans hsa)
        · have hsb : (g : S24).symm a = b := by
            have := (congrArg (g : S24).symm hgb).symm
            simpa using this
          exact (h22 hd).2.2.2 (hj.trans hsb)
  · have hker_eq := ker_eq_of_ne22 (d := d) (a := a) (b := b) (Γ := Γ) hd
    have hgolay : eY ({(g : S24) (P.o p), (g : S24) (P.o q)} : Finset (Fin 24)) *
        eY ({P.o p, P.o q} : Finset (Fin 24)) ∈ golayC := by
      rwa [hker_eq] at hker
    exact (eY_mul_eY_mem_golayC_iff _ _ hcard).mp hgolay

theorem mem_octFix_of_fix_pairs
    (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {g : ↥Γ}
    (hfix : ∀ p q : Fin 8, p ≠ q → (d = 22 → 2 ≤ p.val ∧ 2 ≤ q.val) →
      ρ g (P.φ (Multiplicative.ofAdd (evPair p q))) = P.φ (Multiplicative.ofAdd (evPair p q))) :
    (g : S24) ∈ octFix O := by
  have hthree : ∀ p : Fin 8, ∃ q r : Fin 8, q ≠ p ∧ r ≠ p ∧ q ≠ r := by decide
  have hthree22 : ∀ p : Fin 8, 2 ≤ p.val → ∃ q r : Fin 8,
      2 ≤ q.val ∧ 2 ≤ r.val ∧ q ≠ p ∧ r ≠ p ∧ q ≠ r := by decide
  rw [mem_octFix_iff]
  refine ⟨mctx_le_M24 hM g.2, ?_⟩
  intro x hx
  obtain ⟨p, hp⟩ := (P.o_mem x).1 hx
  subst hp
  by_cases hd : d = 22
  · have hΓle : Γ ≤ M2ab a b := by
      rcases mctx_cases hM with ⟨h24, -⟩ | ⟨h23, -⟩ | ⟨-, -, hle⟩
      · exact absurd (h24.symm.trans hd) (by norm_num)
      · exact absurd (h23.symm.trans hd) (by norm_num)
      · exact hle
    have hgswap := ((mem_M2ab_iff a b hM.cfg.ne (g : S24)).1 (hΓle g.2)).2
    have hnot_ab : ∀ p : Fin 8, 2 ≤ p.val → P.o p ≠ a ∧ P.o p ≠ b := by
      intro p hp2
      constructor
      · intro h
        have : p = 0 := P.o_inj (h.trans P.o_zero.symm)
        rw [this] at hp2; norm_num at hp2
      · intro h
        have : p = 1 := P.o_inj (h.trans P.o_one.symm)
        rw [this] at hp2; norm_num at hp2
    have hfix_ge2 : ∀ p : Fin 8, 2 ≤ p.val → (g : S24) (P.o p) = P.o p := by
      intro p hp2
      obtain ⟨q, r, hq2, hr2, hqp, hrp, hqr⟩ := hthree22 p hp2
      have hpq : p ≠ q := Ne.symm hqp
      have hpr : p ≠ r := Ne.symm hrp
      have hpab := hnot_ab p hp2
      have hqab := hnot_ab q hq2
      have hrab := hnot_ab r hr2
      have h22pq : d = 22 → P.o p ≠ a ∧ P.o p ≠ b ∧ P.o q ≠ a ∧ P.o q ≠ b :=
        fun _ => ⟨hpab.1, hpab.2, hqab.1, hqab.2⟩
      have h22pr : d = 22 → P.o p ≠ a ∧ P.o p ≠ b ∧ P.o r ≠ a ∧ P.o r ≠ b :=
        fun _ => ⟨hpab.1, hpab.2, hrab.1, hrab.2⟩
      have h1 := P.pair_stab hM hpq h22pq (hfix p q hpq (fun _ => ⟨hp2, hq2⟩))
      have h2 := P.pair_stab hM hpr h22pr (hfix p r hpr (fun _ => ⟨hp2, hr2⟩))
      have hdisj1 : (g : S24) (P.o p) = P.o p ∨ (g : S24) (P.o p) = P.o q := by
        have hm : (g : S24) (P.o p) ∈ ({P.o p, P.o q} : Finset (Fin 24)) := by
          rw [← h1]; simp
        simpa using hm
      have hdisj2 : (g : S24) (P.o p) = P.o p ∨ (g : S24) (P.o p) = P.o r := by
        have hm : (g : S24) (P.o p) ∈ ({P.o p, P.o r} : Finset (Fin 24)) := by
          rw [← h2]; simp
        simpa using hm
      rcases hdisj1 with h | h
      · exact h
      · rcases hdisj2 with h' | h'
        · exact h'
        · exact absurd (P.o_inj (h.symm.trans h')) hqr
    have hcontra : (g : S24) a = b → (g : S24) b = a → False := by
      intro ha hb
      have hgO : (g : S24) ∈ octStab O := by
        rw [mem_octStab_iff]
        refine ⟨mctx_le_M24 hM g.2, ?_⟩
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          rw [smul_finset_eq_map, Finset.mem_map_equiv] at hy
          obtain ⟨s, hs⟩ := (P.o_mem ((g : S24).symm y)).1 hy
          have hy_eq : y = (g : S24) (P.o s) := by
            calc y = (g : S24) ((g : S24).symm y) :=
                  (Equiv.apply_symm_apply (g : S24) y).symm
              _ = (g : S24) (P.o s) := congrArg (g : S24) hs.symm
          rw [hy_eq]
          by_cases hs2 : 2 ≤ s.val
          · rw [hfix_ge2 s hs2]
            exact (P.o_mem (P.o s)).2 ⟨s, rfl⟩
          · have hs01 : s = 0 ∨ s = 1 := fin8_eq_zero_or_one_of_not_two_le hs2
            rcases hs01 with rfl | rfl
            · rw [P.o_zero, ha]
              exact (P.o_mem b).2 ⟨1, P.o_one⟩
            · rw [P.o_one, hb]
              exact (P.o_mem a).2 ⟨0, P.o_zero⟩
        · simp
      obtain ⟨σ, hσalt, hσfix⟩ := exists_perm_of_octStab P.o_octad P.o_inj P.o_mem hgO
      have hσeq : σ = Equiv.swap (0 : Fin 8) 1 := by
        apply Equiv.ext
        intro s
        by_cases hs0 : s = 0
        · subst hs0
          have h0 : σ 0 = 1 := P.o_inj (by rw [← hσfix 0, P.o_zero, ha, P.o_one])
          rw [h0]; simp
        · by_cases hs1 : s = 1
          · subst hs1
            have h1 : σ 1 = 0 := P.o_inj (by rw [← hσfix 1, P.o_one, hb, P.o_zero])
            rw [h1]; simp
          · have hs2 : 2 ≤ s.val := by
              have hs0v : s.val ≠ 0 := fun h => hs0 (Fin.ext (by simpa using h))
              have hs1v : s.val ≠ 1 := fun h => hs1 (Fin.ext (by simpa using h))
              have := s.isLt
              omega
            have hss : σ s = s := P.o_inj (by rw [← hσfix s, hfix_ge2 s hs2])
            rw [hss]
            exact (Equiv.swap_apply_of_ne_of_ne hs0 hs1).symm
      have hsign : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp hσalt
      rw [hσeq, Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1)] at hsign
      exact (by decide : (-1 : ℤˣ) ≠ 1) hsign
    by_cases hp2 : 2 ≤ p.val
    · exact hfix_ge2 p hp2
    · have hp01 : p = 0 ∨ p = 1 := fin8_eq_zero_or_one_of_not_two_le hp2
      rcases hp01 with rfl | rfl
      · rcases hgswap with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [P.o_zero]; exact ha
        · exfalso; exact hcontra ha hb
      · rcases hgswap with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [P.o_one]; exact hb
        · exfalso; exact hcontra ha hb
  · obtain ⟨q, r, hqp, hrp, hqr⟩ := hthree p
    have hpq : p ≠ q := Ne.symm hqp
    have hpr : p ≠ r := Ne.symm hrp
    have h1 := P.pair_stab hM hpq (fun h => absurd h hd) (hfix p q hpq (fun h => absurd h hd))
    have h2 := P.pair_stab hM hpr (fun h => absurd h hd) (hfix p r hpr (fun h => absurd h hd))
    have hdisj1 : (g : S24) (P.o p) = P.o p ∨ (g : S24) (P.o p) = P.o q := by
      have hm : (g : S24) (P.o p) ∈ ({P.o p, P.o q} : Finset (Fin 24)) := by
        rw [← h1]; simp
      simpa using hm
    have hdisj2 : (g : S24) (P.o p) = P.o p ∨ (g : S24) (P.o p) = P.o r := by
      have hm : (g : S24) (P.o p) ∈ ({P.o p, P.o r} : Finset (Fin 24)) := by
        rw [← h2]; simp
      simpa using hm
    rcases hdisj1 with h | h
    · exact h
    · rcases hdisj2 with h' | h'
      · exact h'
      · exact absurd (P.o_inj (h.symm.trans h')) hqr

end PhiData

end CFSG.ASVolI.AppH

