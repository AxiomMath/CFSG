module

public import CFSG.Quasithin.MS93.S5A56W2
public import CFSG.Quasithin.MS93.S5A54Sp

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F] [CharP F 2]

theorem transport_lines' {l : Submodule F (V4 F)} {φ : Sp4 F}
    (hφl : (ln₀ F).map (mulVecLin (mat φ)) = l) {x₀ : Sp4 F}
    (hx₀l : (ln₀' F).map (mulVecLin (mat x₀⁻¹)) ⊓ ln₀' F = ⊥) :
    l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹))).map (mulVecLin (mat (φ * x₀ * φ⁻¹)⁻¹)) ⊓
        l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) = ⊥ := by
  have hg : (φ * sig F * φ⁻¹)⁻¹ = φ * sig F * φ⁻¹ := by
    rw [show (φ * sig F * φ⁻¹)⁻¹ = φ * (sig F)⁻¹ * φ⁻¹ by group, sig_inv]
  have hl₁ : l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) = (ln₀' F).map (mulVecLin (mat φ)) := by
    rw [hg, ← hφl, map_mat_mul, map_mat_mul, map_map_mat_inv', sig_map_ln₀]
  refine ⟨?_, ?_⟩
  · rw [hl₁, ← hφl, ← map_inf_map, inf_comm, ln₀_inf_ln₀', Submodule.map_bot]
  · rw [hl₁, show (φ * x₀ * φ⁻¹)⁻¹ = φ * x₀⁻¹ * φ⁻¹ by group, map_mat_mul, map_mat_mul,
      map_map_mat_inv', ← map_inf_map, hx₀l, Submodule.map_bot]

omit [CharP F 2] in
theorem commutator_le_of_map_conj {K : Subgroup (Sp4 F)} (c : Sp4 F)
    (h : commutator (Sp4 F) ≤ K.map (MulAut.conj c).toMonoidHom) : commutator (Sp4 F) ≤ K := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := h ((inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hx c)
  have : y = x := by
    have := congrArg (fun z => c⁻¹ * z * c) hyx
    simpa [mul_assoc] using this
  rwa [← this]

theorem xAltNu_opp (a : F) :
    (ln₀' F).map (mulVecLin (mat (xAlt F * nuE a)⁻¹)) ⊓ ln₀' F = ⊥ := by
  refine map_inv_inf_eq_bot fun v hv hv' => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀'.1 hv
  obtain ⟨h2, h3⟩ := mem_ln₀'.1 hv'
  rw [mat_mul_mulVec, nuE_mulVec, xAlt_mulVec] at h2 h3
  simp [h0, h1] at h2 h3
  have h4 : v (.inr 1) = 0 := by rw [h3, mul_zero, add_zero] at h2; exact h2
  exact ext4 (by simp [h0]) (by simp [h1]) (by simp [h3]) (by simp [h4])

omit [CharP F 2] in
theorem xAlt_mem_Q₁ : xAlt F ∈ Q₁ F :=
  mul_mem (mul_mem (transv_e₁_mem_Q₁ 1) (transv_e₂_mem_Q₁ 1)) (transv_e₁_add_e₂_mem_Q₁ 1)

variable [Finite F]

theorem xAlt_mul_mem_commutator {d : Sp4 F} (hd : d = wAl F ∨ d = nuE 1 ∨ 4 ≤ Nat.card F) :
    xAlt F * d ∈ commutator (Sp4 F) := by
  rcases hd with rfl | rfl | h4
  · exact xZero_mem_commutator
  · exact xOne_mem_commutator
  · have := isPerfect_sp4_of_card h4
    exact Group.IsPerfect.mem_commutator

theorem exists_caseLb {l : Submodule F (V4 F)} (hl : IsLine l) {J : Subgroup (Sp4 F)}
    (hJl : J ≤ qLine l) (hJc : Nat.card J = Nat.card F ^ 2) :
    ∃ g x : Sp4 F, x ∈ commutator (Sp4 F) ∧ l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
        l.map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      commutator (Sp4 F) ≤ J.map (MulAut.conj g⁻¹).toMonoidHom ⊔ J ⊔
        J.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨φ, hφl⟩ := exists_map_ln₀_eq hl
  set J₀ := J.map (MulAut.conj φ⁻¹).toMonoidHom with hJ₀
  have hJ₀Q : J₀ ≤ Q₁ F := (Subgroup.map_mono hJl).trans (qLine_map_conj_inv φ hφl).le
  have hJ₀c : Nat.card J₀ = Nat.card F ^ 2 :=
    (Subgroup.card_map_of_injective (MulAut.conj φ⁻¹).injective).trans hJc
  have hS : ∀ x₀ : Sp4 F,
      (J.map (MulAut.conj (φ * sig F * φ⁻¹)⁻¹).toMonoidHom ⊔ J ⊔
        J.map (MulAut.conj (φ * x₀ * φ⁻¹)).toMonoidHom).map
          (MulAut.conj (sig F * φ⁻¹)).toMonoidHom =
        J₀ ⊔ J₀.map (MulAut.conj (sig F)).toMonoidHom ⊔
          (J₀.map (MulAut.conj x₀).toMonoidHom).map (MulAut.conj (sig F)).toMonoidHom := by
    intro x₀
    obtain ⟨h1, h2, h3⟩ := transport_conj J φ x₀
    rw [Subgroup.map_sup, Subgroup.map_sup, h1, h2, h3]
  by_cases hinv : (∀ a : F, ∀ g ∈ J₀, nuE a * g * (nuE a)⁻¹ ∈ J₀) ∧
      ∀ g ∈ J₀, wAl F * g * (wAl F)⁻¹ ∈ J₀
  ·
    obtain ⟨hq, h₁, h₂⟩ := levi_invariant hJ₀Q hJ₀c hinv.1 hinv.2
    obtain ⟨hopp, hopp'⟩ := transport_lines' hφl (xW_opp (F := F))
    refine ⟨φ * sig F * φ⁻¹, φ * xW F * φ⁻¹,
      (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ xW_mem_commutator φ, hopp, hopp',
      commutator_le_of_map_conj (sig F * φ⁻¹) ?_⟩
    rw [hS]
    have hw2 := commutator_le_sup_w2 hq h₁ h₂
    have hσ := Subgroup.map_mono (f := (MulAut.conj (sig F)).toMonoidHom) hw2
    rw [Subgroup.map_sup, Subgroup.map_sup, map_conj_map_conj', sig_mul_self, map_conj_one]
      at hσ
    refine le_trans ?_ (hσ.trans (le_of_eq ?_))
    · intro x hx
      exact ⟨sig F * x * (sig F)⁻¹,
        (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hx _, by
          change sig F * (sig F * x * (sig F)⁻¹) * (sig F)⁻¹ = x
          rw [show sig F * (sig F * x * (sig F)⁻¹) * (sig F)⁻¹ =
            (sig F * sig F) * x * (sig F * sig F)⁻¹ by group, sig_mul_self]
          group⟩
    · rw [sup_comm J₀]
  ·
    obtain ⟨x₀, hx₀c, hx₀s, hx₀l, g, hg, hmv⟩ : ∃ x₀ : Sp4 F, x₀ ∈ commutator (Sp4 F) ∧
        x₀ ∈ stab (ln₀ F) ∧ (ln₀' F).map (mulVecLin (mat x₀⁻¹)) ⊓ ln₀' F = ⊥ ∧
        ∃ g ∈ J₀, x₀ * g * x₀⁻¹ ∉ J₀ := by
      have hcomm : ∀ {d : Sp4 F}, d ∈ stab (ln₀ F) → ∀ g ∈ J₀,
          xAlt F * d * g * (xAlt F * d)⁻¹ = d * g * d⁻¹ := fun {d} hd g hg => by
        have hc := Q₁_comm xAlt_mem_Q₁ (conj_mem_Q₁ hd (hJ₀Q hg))
        calc xAlt F * d * g * (xAlt F * d)⁻¹ = xAlt F * (d * g * d⁻¹) * (xAlt F)⁻¹ := by group
          _ = d * g * d⁻¹ * xAlt F * (xAlt F)⁻¹ := by rw [hc]
          _ = d * g * d⁻¹ := by group
      rw [not_and_or] at hinv
      rcases hinv with hν | hw
      · push Not at hν
        obtain ⟨a, g, hg, hmv⟩ := hν
        have hds := nuE_mem_stab a
        refine ⟨xAlt F * nuE a, ?_, mul_mem (fixer_le_stab _ xAlt_mem_Q₁) hds, xAltNu_opp a, g,
          hg, by rwa [hcomm hds g hg]⟩
        rcases card_eq_two_or_four_le (F := F) with h2 | h4
        · rcases eq_zero_or_eq_one_of_card_two h2 a with rfl | rfl
          · exfalso
            refine hmv ?_
            have h0 : nuE (0 : F) = 1 := by
              refine ext_mulVec fun v => ?_
              rw [nuE_mulVec, mat_one, one_mulVec]
              simp
            rw [h0, one_mul, inv_one, mul_one]
            exact hg
          · exact xAlt_mul_mem_commutator (Or.inr (Or.inl rfl))
        · exact xAlt_mul_mem_commutator (Or.inr (Or.inr h4))
      · push Not at hw
        obtain ⟨g, hg, hmv⟩ := hw
        exact ⟨xZero F, xZero_mem_commutator, xZero_mem_stab, xZero_opp, g, hg,
          by rwa [xZero, hcomm wAl_mem_stab g hg]⟩
    obtain ⟨hxs, hopp, hopp'⟩ := transport_lines hφl hx₀s hx₀l
    refine ⟨φ * sig F * φ⁻¹, φ * x₀ * φ⁻¹,
      (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hx₀c φ, hopp, hopp', ?_⟩
    suffices hsup : (J.map (MulAut.conj (φ * sig F * φ⁻¹)⁻¹).toMonoidHom ⊔ J ⊔
        J.map (MulAut.conj (φ * x₀ * φ⁻¹)).toMonoidHom).map
          (MulAut.conj (sig F * φ⁻¹)).toMonoidHom = ⊤ by
      rw [eq_top_of_map_conj _ hsup]
      exact le_top
    rw [hS]
    set E := J₀ ⊔ J₀.map (MulAut.conj x₀).toMonoidHom with hE
    have hEQ : E ≤ Q₁ F := sup_le hJ₀Q ((Subgroup.map_mono hJ₀Q).trans
      (mem_normalizer_iff_map_conj.1 (stab_le_normalizer_fixer _ hx₀s)).le)
    have hlt : J₀ < E := lt_of_le_of_ne le_sup_left fun h => hmv (h ▸
      Subgroup.mem_sup_right ⟨g, hg, rfl⟩)
    have hEc : Nat.card F ^ 2 < Nat.card E := hJ₀c ▸ Subgroup.card_lt_of_lt hlt
    have hEσ : E.map (MulAut.conj (sig F)).toMonoidHom ≤ qLine (ln₀' F) := by
      rw [← sig_map_ln₀, qLine_map]
      exact Subgroup.map_mono hEQ
    have hEσc : Nat.card F ^ 2 < Nat.card ↥(E.map (MulAut.conj (sig F)).toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj (sig F)).injective]
    have hq2 : Nat.card F < Nat.card J₀ := by
      rw [hJ₀c]
      have hq : 1 < Nat.card F := Finite.one_lt_card
      calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
        _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
    have htop := sup_eq_top_of_le_qLine' isLine_ln₀ isLine_ln₀' ln₀_inf_ln₀' hJ₀Q hEσ hq2 hEσc
    refine eq_top_iff.2 (htop.symm.le.trans (sup_le (le_sup_left.trans le_sup_left) ?_))
    rw [hE, Subgroup.map_sup, sup_assoc]
    exact le_sup_right

theorem exists_caseL {l : Submodule F (V4 F)} (hl : IsLine l) {R J Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hRl : R ≤ stab l) (hJ : candMax R = {J}) (hJl : J ≤ qLine l)
    (hJc : Nat.card F ^ 2 ≤ Nat.card J) (hZR : Z ≤ R) (hZc : Nat.card F ^ 2 ≤ Nat.card Z)
    (hZq : commSp Z ≤ fixSp Z) (hZf : Module.finrank F (fixSp Z) ≤ 2) :
    ∃ g x : Sp4 F, x ∈ commutator (Sp4 F) ∧ l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
        l.map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      commutator (Sp4 F) ≤ J.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z ⊔
        Z.map (MulAut.conj x).toMonoidHom := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqq : Nat.card F < Nat.card F ^ 2 := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
  have hJmax : J ∈ candMax R := hJ ▸ Set.mem_singleton J
  have hZ2 : IsPGroup 2 Z := hR.to_le hZR
  have hf2 : Module.finrank F (fixSp Z) = 2 := le_antisymm hZf (two_le_finrank_fixSp hZq)
  obtain ⟨hm, hZm⟩ := isLine_fixSp_of_finrank_two hZ2 hf2
  set m := fixSp Z with hmdef
  have hZcand : IsCandSp R Z := by
    have hfix : Nat.card (fixSp Z) = Nat.card F ^ 2 := by rw [card_fixSp, hf2]
    refine ⟨hZR, ?_, ?_⟩
    · rw [card_V4, hfix, show 4 = 2 + 2 from rfl, pow_add]
      exact Nat.mul_le_mul_left _ hZc
    · rw [card_V4, hfix, show 4 = 2 + 2 from rfl, pow_add]
  have hZJ : Nat.card Z ≤ Nat.card J := hJmax.2 Z hZcand
  by_cases hml : m = l
  · rw [hml] at hZm
    rcases hJc.lt_or_eq with hlt | heq
    ·
      obtain ⟨φ, hφl⟩ := exists_map_ln₀_eq hl
      obtain ⟨-, hopp, hopp'⟩ := transport_lines hφl xZero_mem_stab xZero_opp
      refine ⟨φ * sig F * φ⁻¹, φ * xZero F * φ⁻¹,
        (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ xZero_mem_commutator φ, hopp,
        hopp', ?_⟩
      suffices hsup : (J.map (MulAut.conj (φ * sig F * φ⁻¹)⁻¹).toMonoidHom ⊔ Z ⊔
          Z.map (MulAut.conj (φ * xZero F * φ⁻¹)).toMonoidHom).map
            (MulAut.conj (sig F * φ⁻¹)).toMonoidHom = ⊤ by
        rw [eq_top_of_map_conj _ hsup]
        exact le_top
      obtain ⟨h1, -, h3⟩ := transport_conj Z φ (xZero F)
      rw [Subgroup.map_sup, Subgroup.map_sup, (transport_conj J φ (xZero F)).1, h3]
      have hJ₀Q : J.map (MulAut.conj φ⁻¹).toMonoidHom ≤ Q₁ F :=
        (Subgroup.map_mono hJl).trans (qLine_map_conj_inv φ hφl).le
      have hZσ : (Z.map (MulAut.conj φ⁻¹).toMonoidHom).map (MulAut.conj (sig F)).toMonoidHom ≤
          qLine (ln₀' F) := by
        rw [← sig_map_ln₀, qLine_map]
        exact Subgroup.map_mono ((Subgroup.map_mono hZm).trans (qLine_map_conj_inv φ hφl).le)
      have hcJ : Nat.card F ^ 2 < Nat.card ↥(J.map (MulAut.conj φ⁻¹).toMonoidHom) := by
        rwa [Subgroup.card_map_of_injective (MulAut.conj _).injective]
      have hcZ : Nat.card F <
          Nat.card ↥((Z.map (MulAut.conj φ⁻¹).toMonoidHom).map
            (MulAut.conj (sig F)).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj _).injective,
          Subgroup.card_map_of_injective (MulAut.conj _).injective]
        exact hqq.trans_le hZc
      have htop := sup_eq_top_of_le_qLine' isLine_ln₀' isLine_ln₀
        (by rw [inf_comm]; exact ln₀_inf_ln₀') hZσ hJ₀Q hcZ hcJ
      refine eq_top_iff.2 (htop.symm.le.trans (sup_le ?_ (le_sup_left.trans le_sup_left)))
      exact le_sup_right.trans le_sup_left
    ·
      have hZeq : Z = J := by
        have hZm' : Z ∈ candMax R := ⟨hZcand, fun B hB => (hJmax.2 B hB).trans
          (by rw [← heq]; exact hZc)⟩
        rw [hJ] at hZm'
        exact hZm'
      subst hZeq
      exact exists_caseLb hl hJl heq.symm
  ·
    by_cases h0 : m ⊓ l = ⊥
    · exfalso
      have hbot : Z = ⊥ := le_bot_iff.1 ((le_inf hZm (hZR.trans hRl)).trans
        (qLine_inf_stab_eq_bot hm hl h0).le)
      rw [hbot, Subgroup.card_bot] at hZc
      have : 1 < Nat.card F ^ 2 := lt_of_lt_of_le hq (Nat.le_self_pow two_ne_zero _)
      omega
    · have hp := isPoint_inf hm hl hml h0
      have hZp : Z ≤ qLine m ⊓ qPoint (m ⊓ l) :=
        le_inf hZm ((le_inf hZm (hZR.trans hRl)).trans (qLine_inf_stab_le_qPoint hm hl hp rfl))
      have hZeq : Z = qLine m ⊓ qPoint (m ⊓ l) := Subgroup.eq_of_le_of_card_ge hZp
        (by rw [card_qLine_inf_qPoint hp hm inf_le_left]; exact hZc)
      have hXZ : xPoint (m ⊓ l) ≤ Z := hZeq ▸ le_inf (xPoint_le_qLine hm inf_le_left)
        (xPoint_le_qPoint hp)
      have hJlt : Nat.card F ^ 2 < Nat.card J := by
        refine lt_of_le_of_ne hJc fun heq => ?_
        have hK : Nat.card F ^ 2 ≤ Nat.card ↥(qLine m ⊓ R) :=
          hZc.trans (Subgroup.card_le_of_le (le_inf hZm hZR))
        have hKc := isCandSp_qLine_inf hm hK
        have hKm : qLine m ⊓ R ∈ candMax R :=
          ⟨hKc, fun B hB => (hJmax.2 B hB).trans (heq ▸ hK)⟩
        rw [hJ, Set.mem_singleton_iff] at hKm
        have hJx : J ≤ xPoint (m ⊓ l) := by
          rw [← qLine_inf_qLine hm hl hp rfl, ← hKm]
          exact le_inf inf_le_left (hKm ▸ hJl)
        have := Subgroup.card_le_of_le hJx
        rw [card_xPoint hp, ← heq] at this
        omega
      obtain ⟨g, x, hx, -, hopp, hopp', htop⟩ := exists_caseP hl hp inf_le_right hJl hJc
        (fun h => absurd h hJlt.ne')
      refine ⟨g, x, hx, hopp, hopp', ?_⟩
      rw [← xPoint_map_conj] at htop
      refine eq_top_iff.2 (htop.symm.le.trans (sup_le_sup (sup_le_sup_left hXZ _)
        (Subgroup.map_mono hXZ))) ▸ le_top

end CFSG.Quasithin.MS93.S5
