module

public import CFSG.Quasithin.MS93.S5A56Hat
public import CFSG.Quasithin.MS93.S5A56FStmt
public import CFSG.Quasithin.MS93.S5A56FW
public import CFSG.Quasithin.MS93.S33SpS5
public import CFSG.Quasithin.MS93.S5A56L

public section

namespace CFSG.Quasithin.MS93.S5

section Sp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem map_inf_eq_bot_of_mem_stab {l : Submodule F (V4 F)} {g x : Sp4 F}
    (hopp : l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥) (hx : x ∈ MSP.stab l) :
    (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓ l = ⊥ := by
  have hxl : l.map (mulVecLin (mat x⁻¹)) = l := by
    have := congrArg (Submodule.map (mulVecLin (mat x⁻¹))) (mem_stab_iff.1 hx)
    rw [map_map_mat_inv'] at this
    exact this.symm
  calc (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓ l =
        (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
          l.map (mulVecLin (mat x⁻¹)) := by rw [hxl]
    _ = (l.map (mulVecLin (mat g⁻¹)) ⊓ l).map (mulVecLin (mat x⁻¹)) := (map_inf_map _ _ _).symm
    _ = ⊥ := by rw [hopp, Submodule.map_bot]

omit [Finite F] in
theorem transport_lines_ln₀ {l : Submodule F (V4 F)} {φ : Sp4 F}
    (hφl : (ln₀ F).map (mulVecLin (mat φ)) = l) {x₀ : Sp4 F}
    (hx₀l : (ln₀' F).map (mulVecLin (mat x₀⁻¹)) ⊓ ln₀ F = ⊥) :
    (l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹))).map (mulVecLin (mat (φ * x₀ * φ⁻¹)⁻¹)) ⊓
      l = ⊥ := by
  have hg : (φ * sig F * φ⁻¹)⁻¹ = φ * sig F * φ⁻¹ := by
    rw [show (φ * sig F * φ⁻¹)⁻¹ = φ * (sig F)⁻¹ * φ⁻¹ by group, sig_inv]
  have hl₁ : l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) = (ln₀' F).map (mulVecLin (mat φ)) := by
    rw [hg, ← hφl, map_mat_mul, map_mat_mul, map_map_mat_inv', sig_map_ln₀]
  rw [hl₁, show (φ * x₀ * φ⁻¹)⁻¹ = φ * x₀⁻¹ * φ⁻¹ by group, map_mat_mul, map_mat_mul,
    map_map_mat_inv', ← hφl, ← map_inf_map, hx₀l, Submodule.map_bot]

theorem exists_caseLbf {l : Submodule F (V4 F)} (hl : IsLine l) {J : Subgroup (Sp4 F)}
    (hJl : J ≤ qLine l) (hJc : Nat.card J = Nat.card F ^ 2) :
    ∃ g x : Sp4 F, x ∈ commutator (Sp4 F) ∧ (x ∈ MSP.stab l ∨ Nat.card F = 2) ∧
      l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
        l.map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓ l = ⊥ ∧
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
    obtain ⟨hopp, hopp'⟩ := transport_lines' hφl (xWo_opp (F := F))
    refine ⟨φ * sig F * φ⁻¹, φ * xWo F * φ⁻¹,
      (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ xWo_mem_commutator φ, Or.inr hq,
      hopp, hopp', transport_lines_ln₀ hφl xWo_opp_ln₀,
      commutator_le_of_map_conj (sig F * φ⁻¹) ?_⟩
    rw [hS]
    have hw2 := commutator_le_sup_w2o hq h₁ h₂
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
        x₀ ∈ MSP.stab (ln₀ F) ∧ (ln₀' F).map (mulVecLin (mat x₀⁻¹)) ⊓ ln₀' F = ⊥ ∧
        ∃ g ∈ J₀, x₀ * g * x₀⁻¹ ∉ J₀ := by
      have hcomm : ∀ {d : Sp4 F}, d ∈ MSP.stab (ln₀ F) → ∀ g ∈ J₀,
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
      (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hx₀c φ, Or.inl hxs, hopp, hopp',
      map_inf_eq_bot_of_mem_stab hopp hxs, ?_⟩
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

theorem exists_caseLf {l : Submodule F (V4 F)} (hl : IsLine l) {R J Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hRl : R ≤ MSP.stab l) (hJ : candMax R = {J}) (hJl : J ≤ qLine l)
    (hJc : Nat.card F ^ 2 ≤ Nat.card J) (hZR : Z ≤ R) (hZc : Nat.card F ^ 2 ≤ Nat.card Z)
    (hZq : commSp Z ≤ fixSp Z) (hZf : Module.finrank F (fixSp Z) ≤ 2) :
    ∃ g x : Sp4 F, x ∈ commutator (Sp4 F) ∧
      (x ∈ MSP.stab l ∨ Nat.card F = 2 ∧ Nat.card J = Nat.card F ^ 2) ∧
      l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
        l.map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓ l = ⊥ ∧
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
      obtain ⟨hxs, hopp, hopp'⟩ := transport_lines hφl xZero_mem_stab xZero_opp
      refine ⟨φ * sig F * φ⁻¹, φ * xZero F * φ⁻¹,
        (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ xZero_mem_commutator φ,
        Or.inl hxs, hopp, hopp', map_inf_eq_bot_of_mem_stab hopp hxs, ?_⟩
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
      obtain ⟨g, x, hx, hxs, hopp, hopp', hopp'', htop⟩ := exists_caseLbf hl hJl heq.symm
      exact ⟨g, x, hx, hxs.imp_right fun h => ⟨h, heq.symm⟩, hopp, hopp', hopp'', htop⟩
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
      obtain ⟨g, x, hx, hxs, hopp, hopp', htop⟩ := exists_caseP hl hp inf_le_right hJl hJc
        (fun h => absurd h hJlt.ne')
      refine ⟨g, x, hx, Or.inl hxs, hopp, hopp', map_inf_eq_bot_of_mem_stab hopp hxs, ?_⟩
      rw [← xPoint_map_conj] at htop
      refine eq_top_iff.2 (htop.symm.le.trans (sup_le_sup (sup_le_sup_left hXZ _)
        (Subgroup.map_mono hXZ))) ▸ le_top

end Sp

section Concl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem concl56f_of (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hZ : zHat _ (baseA (puAmalgam h.le)) α' ≤ stab (puAmalgam h.le) (baseA _))
    (hJ : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ stab (puAmalgam h.le) (baseA _))
    (hQJ : Qv (puAmalgam h.le) (baseA _) ≤ jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _))
    {g₀ x₀ : ↥(StatedSp 2 F)} (hx₀ : x₀ ∈ commutator (StatedSp 2 F))
    (hopp : l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹)) ⊓ l = ⊥)
    (hopp' : (l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹))).map (Matrix.mulVecLin (MSP.mat x₀⁻¹)) ⊓
      l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹)) = ⊥)
    (hc : commutator (StatedSp 2 F) ≤
      (vIm h.le a (jOff h.le L (2 ^ k) (baseA _) (baseB _))).map (MulAut.conj g₀⁻¹).toMonoidHom ⊔
        vIm h.le a (zHat _ (baseA _) α') ⊔
        (vIm h.le a (zHat _ (baseA _) α')).map (MulAut.conj x₀).toMonoidHom)
    (hdq : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k → x₀ ∈ MSP.stab l)
    (hes : ¬ (2 ^ k = 2 ∧ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (jOff h.le L (2 ^ k) (baseA _) (baseB _)) = (2 ^ k) ^ 2) → x₀ ∈ MSP.stab l)
    (hopp'' : (l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹))).map (Matrix.mulVecLin (MSP.mat x₀⁻¹)) ⊓
      l = ⊥) :
    ∃ g ∈ stab _ (baseA (puAmalgam h.le)), ∃ x ∈ puTrans h.le L (baseA _),
      Concl56f h (2 ^ k) a α' l g x := by
  have := hd.charP
  obtain ⟨m₀, rfl⟩ := hd.surj g₀
  obtain ⟨y, hyL, rfl⟩ := commutator_le_imSp_L h hd hx₀
  have hst : stab (puAmalgam h.le) (baseA _) = (puAmalgam h.le).ofA.range :=
    (ofA_range_eq h.le).symm
  have hgst : (puAmalgam h.le).ofA m₀ ∈ stab (puAmalgam h.le) (baseA _) := hst ▸ ⟨m₀, rfl⟩
  have hxL : (puAmalgam h.le).ofA y ∈ puTrans h.le L (baseA _) := by
    rw [puTrans_L_baseA h]
    exact ⟨y, hyL, rfl⟩
  have hconj : ∀ (m : ↥M) (K : Subgroup (puAmalgam h.le).Universal),
      vIm h.le a (rconj ((puAmalgam h.le).ofA m) K) =
        (vIm h.le a K).map (MulAut.conj (a m)⁻¹).toMonoidHom := fun m K => by
    rw [rconj, ← map_inv, vIm_map_conj h.le m⁻¹ K, map_inv]
  have hQ₁ := vPre_le_stab (a := a) h (MSP.qLine l)
  have hl₁ : MSP.IsLine (l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))) := MSP.isLine_map hl _
  have hl₂ : MSP.IsLine ((l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))).map
      (Matrix.mulVecLin (MSP.mat (a y)⁻¹))) := MSP.isLine_map hl₁ _
  have hvQ₁ : vIm h.le a (rconj ((puAmalgam h.le).ofA m₀) (vPre h.le a (MSP.qLine l))) =
      MSP.qLine (l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))) := by
    rw [hconj, vIm_vPre h hd, MSP.qLine_map]
  have hxst : (puAmalgam h.le).ofA y ∈ stab (puAmalgam h.le) (baseA _) := hst ▸ ⟨y, rfl⟩
  have hK₂ : rconj ((puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y)
      (vPre h.le a (MSP.qLine l)) ≤ stab (puAmalgam h.le) (baseA _) :=
    rconj_le_stab h hQ₁ (mul_mem hgst hxst)
  have hvK₂ : vIm h.le a (rconj ((puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y)
      (vPre h.le a (MSP.qLine l))) =
      MSP.qLine ((l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))).map
        (Matrix.mulVecLin (MSP.mat (a y)⁻¹))) := by
    rw [show (puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y = (puAmalgam h.le).ofA (m₀ * y)
      from (map_mul _ _ _).symm, hconj, vIm_vPre h hd, MSP.qLine_map, MSP.qLine_map,
      MSP.map_conj_map_conj, map_mul, _root_.mul_inv_rev]
  refine ⟨(puAmalgam h.le).ofA m₀, hgst, (puAmalgam h.le).ofA y, hxL,
    ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  ·
    intro E₁ E₂ hE₁2 hE₂2 hE₁ hE₂ hE₁c hE₂c
    have hE₁st : E₁ ≤ stab (puAmalgam h.le) (baseA _) := hE₁.trans (rconj_le_stab h hQ₁ hgst)
    have hE₂st : E₂ ≤ stab (puAmalgam h.le) (baseA _) := hE₂.trans hQ₁
    have hv₁ : vIm h.le a E₁ ≤ MSP.qLine (l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))) :=
      hvQ₁ ▸ vIm_mono' h hE₁
    have hv₂ : vIm h.le a E₂ ≤ MSP.qLine l := (vIm_vPre h hd (MSP.qLine l)) ▸ vIm_mono' h hE₂
    have htop := MSP.sup_eq_top_of_le_qLine hl₁ hl hopp hv₁ hv₂
      (by rw [card_vIm h hd hE₁st hE₁2, hd.nat_card_eq]; exact hE₁c)
      (by rw [card_vIm h hd hE₂st hE₂2, hd.nat_card_eq]; exact hE₂c)
    have hK : E₁ ⊔ E₂ ⊔ Qv (puAmalgam h.le) (baseA _) ≤ stab (puAmalgam h.le) (baseA _) :=
      sup_le (sup_le hE₁st hE₂st) (qv_le_stab _ _)
    refine (lift56 h hd hK le_sup_right).2 (eq_top_iff.2 ?_)
    rw [← htop]
    exact sup_le (vIm_mono' h (le_sup_left.trans le_sup_left))
      (vIm_mono' h (le_sup_right.trans le_sup_left))
  ·
    have hK₁ : rconj ((puAmalgam h.le).ofA m₀) (vPre h.le a (MSP.qLine l)) ≤
        stab (puAmalgam h.le) (baseA _) := rconj_le_stab h hQ₁ hgst
    have htop := MSP.qLine_sup_qLine_eq_top hl₂ hl₁ hopp'
    have hK : rconj ((puAmalgam h.le).ofA m₀) (vPre h.le a (MSP.qLine l)) ⊔
        rconj ((puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y) (vPre h.le a (MSP.qLine l)) =
        stab (puAmalgam h.le) (baseA _) := by
      refine (lift56 h hd (sup_le hK₁ hK₂) (le_sup_left.trans' (qv_le_rconj h
        (qv_le_vPre h hd _) hgst))).2 (eq_top_iff.2 ?_)
      rw [← htop]
      exact sup_le (hvK₂ ▸ vIm_mono' h le_sup_right) (hvQ₁ ▸ vIm_mono' h le_sup_left)
    rintro z ⟨⟨hzZ, hz₁⟩, hz₂⟩
    have hzst : z ∈ stab (puAmalgam h.le) (baseA _) :=
      (zm_le_qv_self _ (isMVtx_baseA _) h.critDist_pos |>.trans (qv_le_stab _ _)) hzZ
    have hle : stab (puAmalgam h.le) (baseA _) ≤ Subgroup.centralizer {z} := by
      rw [← hK]
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hz₁ w hw)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hz₂ w hw)
    refine ⟨⟨z, hzst⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle w.2)
  ·
    have hxinv : ((puAmalgam h.le).ofA y)⁻¹ ∈ stab (puAmalgam h.le) (baseA _) :=
      inv_mem (hst ▸ ⟨y, rfl⟩)
    have hH : rconj ((puAmalgam h.le).ofA m₀) (jOff h.le L (2 ^ k) (baseA _) (baseB _)) ⊔
        zHat _ (baseA _) α' ⊔ rconj ((puAmalgam h.le).ofA y)⁻¹ (zHat _ (baseA _) α') ≤
        stab (puAmalgam h.le) (baseA _) :=
      sup_le (sup_le (rconj_le_stab h hJ hgst) hZ) (rconj_le_stab h hZ hxinv)
    have hQH : Qv (puAmalgam h.le) (baseA _) ≤
        rconj ((puAmalgam h.le).ofA m₀) (jOff h.le L (2 ^ k) (baseA _) (baseB _)) ⊔
        zHat _ (baseA _) α' ⊔ rconj ((puAmalgam h.le).ofA y)⁻¹ (zHat _ (baseA _) α') :=
      (qv_le_rconj h hQJ hgst).trans (le_sup_left.trans le_sup_left)
    refine (lift56 h hd hH hQH).1 ((imSp_L_le_commutator h).trans (hc.trans ?_))
    refine sup_le (sup_le ?_ (vIm_mono' h (le_sup_right.trans le_sup_left))) ?_
    · rw [← hconj]
      exact vIm_mono' h (le_sup_left.trans le_sup_left)
    · have e : rconj ((puAmalgam h.le).ofA y)⁻¹ (zHat _ (baseA _) α') =
          (zHat _ (baseA _) α').map (MulAut.conj ((puAmalgam h.le).ofA y)).toMonoidHom := by
        rw [rconj, inv_inv]
      rw [← vIm_map_conj h.le y, ← e]
      exact vIm_mono' h le_sup_right
  ·
    intro hrel
    exact ⟨y, hdq hrel, rfl⟩
  ·
    intro hn
    exact ⟨y, hes hn, rfl⟩
  ·
    intro E₁ E₂ hE₁2 hE₂2 hE₁ hE₂ hE₁c hE₂c
    have hE₁st : E₁ ≤ stab (puAmalgam h.le) (baseA _) := hE₁.trans hK₂
    have hE₂st : E₂ ≤ stab (puAmalgam h.le) (baseA _) := hE₂.trans hQ₁
    have hv₁ : vIm h.le a E₁ ≤ MSP.qLine ((l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))).map
        (Matrix.mulVecLin (MSP.mat (a y)⁻¹))) := hvK₂ ▸ vIm_mono' h hE₁
    have hv₂ : vIm h.le a E₂ ≤ MSP.qLine l := (vIm_vPre h hd (MSP.qLine l)) ▸ vIm_mono' h hE₂
    have htop := MSP.sup_eq_top_of_le_qLine hl₂ hl hopp'' hv₁ hv₂
      (by rw [card_vIm h hd hE₁st hE₁2, hd.nat_card_eq]; exact hE₁c)
      (by rw [card_vIm h hd hE₂st hE₂2, hd.nat_card_eq]; exact hE₂c)
    have hK : E₁ ⊔ E₂ ⊔ Qv (puAmalgam h.le) (baseA _) ≤ stab (puAmalgam h.le) (baseA _) :=
      sup_le (sup_le hE₁st hE₂st) (qv_le_stab _ _)
    refine (lift56 h hd hK le_sup_right).2 (eq_top_iff.2 ?_)
    rw [← htop]
    exact sup_le (vIm_mono' h (le_sup_left.trans le_sup_left))
      (vIm_mono' h (le_sup_right.trans le_sup_left))

end Concl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

theorem s56f_of (h51 : S51) : S56f := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hβ l hl hTl hJl
  have := hd.charP
  have hb0 := h.critDist_pos
  have hTst : imSp a T ≤ MSP.stab l := by
    have := vIm_le_of_le_vPre' h.le hTl
    rwa [puAmalgam.qv_baseB, vIm_imM h] at this
  have hJst := vIm_le_of_le_vPre' h.le hJl
  rw [jOff_baseA h, vIm_imM h] at hJst
  have hJM : jOffM M T L (2 ^ k) ≤ M := iSup₂_le fun E hE => (offSetM_le _ hE).trans h.le
  have hJq : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤
      stab (puAmalgam h.le) (baseA _) := by
    rw [jOff_baseA h, puAmalgam.stab_baseA]
    exact imM_mono h.le hJM
  have hZst : ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) (baseA _) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZhst : zHat _ (baseA (puAmalgam h.le)) α' ≤ stab (puAmalgam h.le) (baseA _) :=
    inf_le_left.trans hZst
  have hZT : vIm h.le a (ZM _ α') ≤ imSp a T := by
    have := vIm_mono' (a := a) h (zm_le_qv_baseB h hc hβ)
    rwa [puAmalgam.qv_baseB, vIm_imM h] at this
  rcases sp4_54M h51 hd h hmin hb with ⟨A₀, -, hA, -, -, -, hA₀c, hJ⟩ | ⟨p, hp, hTp, hJT⟩
  swap
  · exfalso
    rw [hJT, hTp] at hJst
    have := MSP.fixSp_antitone hJst
    rw [MSP.fixSp_qLine hl, MSP.fixSp_qPoint hp] at this
    have h2 := Submodule.finrank_mono this
    rw [hl.1, hp] at h2
    omega
  have hA₀T : A₀ ≤ imSp a T := (hA ▸ Set.mem_singleton A₀ : A₀ ∈ candMax (imSp a T)).1.1
  rw [hJ, imSp_liftT hA₀T] at hJst
  have hvJ : vIm h.le a (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) = A₀ := by
    rw [jOff_baseA h, vIm_imM h, hJ, imSp_liftT hA₀T]
  have hA₀max : A₀ ∈ candMax (imSp a T) := hA ▸ Set.mem_singleton A₀
  have hQJ : Qv (puAmalgam h.le) (baseA _) ≤
      jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) := by
    rw [qv_baseA_eq h, jOff_baseA h, hJ]
    exact imM_mono h.le (hd.pCoreOf_le_liftT h A₀)
  have hq2 : Nat.card F ^ 2 ≤ Nat.card A₀ := hA₀c
  rcases S33.shape_of_sp4Data h hd hc with ⟨hrel, hzh, p, hp, hZp⟩ |
    ⟨hrel1, hrel2, hfin⟩
  ·
    have hpl : p ≤ l := MSP.le_of_xPoint_le_stab hp hl (hZp ▸ hZT.trans hTst)
    have hJ2 : Nat.card A₀ = Nat.card F ^ 2 → MSP.xPoint p ≤ A₀ ∧
        ∀ p', MSP.IsPoint p' → p' ≤ l → p' ≠ p → ¬ MSP.xPoint p ⊔ MSP.xPoint p' ≤ A₀ := by
      intro heq
      have hK : Nat.card F ^ 2 ≤ Nat.card ↥(MSP.qLine l ⊓ imSp a T) :=
        hq2.trans (Subgroup.card_le_of_le (le_inf hJst hA₀T))
      have hKeq : MSP.qLine l ⊓ imSp a T = A₀ := (Subgroup.eq_of_le_of_card_ge
        (le_inf hJst hA₀T) ((hA₀max.2 _ (isCandSp_qLine_inf hl hK)))).symm
      refine ⟨hKeq ▸ le_inf (MSP.xPoint_le_qLine hl hpl) (hZp ▸ hZT), fun p' hp' hp'l hne hle => ?_⟩
      have hcard := card_xPoint_sup hp hp' hne.symm (hp'l.trans (le_perp_of_le hl hpl))
      have hE : MSP.xPoint p ⊔ MSP.xPoint p' = A₀ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [heq]; exact hcard)
      exact jOffM_ne_xPoint_sup h51 hd h hmin hb hp hp' (by rw [hJ, imSp_liftT hA₀T, hE])
    obtain ⟨g₀, x₀, hx₀c, hx₀s, hopp, hopp', htop⟩ := exists_caseP hl hp hpl hJst hq2 hJ2
    refine concl56f_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_ (fun _ => hx₀s) (fun _ => hx₀s)
      (map_inf_eq_bot_of_mem_stab hopp hx₀s)
    rw [hvJ, hzh, hZp, MSP.xPoint_map_conj, htop]
    exact le_top
  ·
    have hZ2 : IsPGroup 2 (ZM (puAmalgam h.le) α') :=
      (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (zm_le_qv_baseB h hc hβ)
    by_cases hhat : ∃ t₁ t₂ t₃, IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ ∧
        t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α'
    · obtain ⟨t₁, t₂, t₃, ht, hn⟩ := hhat
      obtain ⟨hk1, -, -, -⟩ := S33.of_isHatTriple h hd hc ht
      have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, hk1]; rfl
      have hZh := zHat_eq_of_isHatTriple h hd hq hc ht hn
      have hZ4 : 4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
        rw [hk1] at hrel2
        exact hrel2
      obtain ⟨v₁, v₂, h₁, h₂, h₁₂, hf, hZv₁, hZv₂, hs⟩ := hat_shape h hd hq hc ht hZh hZ4
      have hp₁ := MSP.isPoint_span h₁
      have hp₂ := MSP.isPoint_span h₂
      have hX₁ : MSP.xPoint (F ∙ v₁) ≤ imSp a T := (xPoint_span_le_of_card_two hq h₁ hZv₁).trans hZT
      have hX₂ : MSP.xPoint (F ∙ v₂) ≤ imSp a T := (xPoint_span_le_of_card_two hq h₂ hZv₂).trans hZT
      have hv₁l : (F ∙ v₁) ≤ l := MSP.le_of_xPoint_le_stab hp₁ hl (hX₁.trans hTst)
      have hv₂l : (F ∙ v₂) ≤ l := MSP.le_of_xPoint_le_stab hp₂ hl (hX₂.trans hTst)
      have hne : (F ∙ v₁) ≠ (F ∙ v₂) := by
        intro e
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (e ▸ Submodule.mem_span_singleton_self v₂ :
          v₂ ∈ F ∙ v₁)
        rcases eq_zero_or_eq_one_of_card_two hq c with rfl | rfl
        · exact h₂ (by rw [← hc, zero_smul])
        · exact h₁₂ (by rw [← hc, one_smul])
      have hperp : (F ∙ v₂) ≤ MSP.perp (F ∙ v₁) :=
        (Submodule.span_singleton_le_iff_mem _ _).2 (MSP.mem_perp_span.2 hf)
      have hcard4 := card_xPoint_sup hp₁ hp₂ hne hperp
      have hJgt : Nat.card F ^ 2 < Nat.card A₀ := by
        refine lt_of_le_of_ne hq2 fun heq => ?_
        have hsub : MSP.xPoint (F ∙ v₁) ⊔ MSP.xPoint (F ∙ v₂) ≤ MSP.qLine l ⊓ imSp a T :=
          le_inf (sup_le (MSP.xPoint_le_qLine hl hv₁l) (MSP.xPoint_le_qLine hl hv₂l))
            (sup_le hX₁ hX₂)
        have hK : Nat.card F ^ 2 ≤ Nat.card ↥(MSP.qLine l ⊓ imSp a T) :=
          hcard4.trans (Subgroup.card_le_of_le hsub)
        have hKeq : MSP.qLine l ⊓ imSp a T = A₀ := (Subgroup.eq_of_le_of_card_ge
          (le_inf hJst hA₀T) ((hA₀max.2 _ (isCandSp_qLine_inf hl hK)))).symm
        have hE : MSP.xPoint (F ∙ v₁) ⊔ MSP.xPoint (F ∙ v₂) = A₀ :=
          Subgroup.eq_of_le_of_card_ge (hKeq ▸ hsub) (by rw [← heq]; exact hcard4)
        exact jOffM_ne_xPoint_sup h51 hd h hmin hb hp₁ hp₂ (by rw [hJ, imSp_liftT hA₀T, hE])
      have hdq : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k → False := by
        intro hq'
        rw [hq'] at hrel1
        have : 2 ^ k < (2 ^ k) ^ 2 := by
          have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
          nlinarith
        omega
      have hcaseP : ∀ {v : MSP.V4 F}, v ≠ 0 → (F ∙ v) ≤ l →
          MSP.transv v 1 ∈ vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') →
          ∃ g ∈ stab _ (baseA (puAmalgam h.le)), ∃ x ∈ puTrans h.le L (baseA _),
            Concl56f h (2 ^ k) a α' l g x := by
        intro v hv hvl hvZ
        have hXZ := xPoint_span_le_of_card_two hq hv hvZ
        obtain ⟨g₀, x₀, hx₀c, hx₀s, hopp, hopp', htop⟩ :=
          exists_caseP hl (MSP.isPoint_span hv) hvl hJst hq2 (fun h' => absurd h' hJgt.ne')
        refine concl56f_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_
          (fun hq' => (hdq hq').elim) (fun _ => hx₀s) (map_inf_eq_bot_of_mem_stab hopp hx₀s)
        rw [hvJ]
        have hle : commutator (StatedSp 2 F) ≤ ⊤ := le_top
        rw [← htop, ← MSP.xPoint_map_conj] at hle
        exact hle.trans (sup_le_sup (sup_le_sup_left hXZ _) (Subgroup.map_mono hXZ))
      rcases hs with hs | hs | hs
      · exact hcaseP h₁ hv₁l hs
      · exact hcaseP h₂ hv₂l hs
      · obtain ⟨g₀, x₀, hx₀c, hx₀s, hopp, hopp', htop⟩ := exists_caseHat hq hl h₁ h₂ h₁₂
          ((Submodule.span_singleton_le_iff_mem _ _).1 hv₁l)
          ((Submodule.span_singleton_le_iff_mem _ _).1 hv₂l) hJst hJgt hs
        refine concl56f_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_
          (fun hq' => (hdq hq').elim) (fun _ => hx₀s) (map_inf_eq_bot_of_mem_stab hopp hx₀s)
        rw [hvJ, htop]
        exact le_top
    · have hzh := zHat_eq_of_not hhat
      have hZc : Nat.card F ^ 2 ≤ Nat.card ↥(vIm h.le a (ZM _ α')) := by
        rw [card_vIm h hd hZst hZ2, hd.nat_card_eq]
        exact hrel2
      have hJ2 : IsPGroup 2 (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) :=
        (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (iSup₂_le fun _ hE => hE.1.1)
      obtain ⟨g₀, x₀, hx₀c, hx₀s, hopp, hopp', hopp'', hcc⟩ := exists_caseLf hl
        (IsSp4Data.isPGroup_imSp (a := a) h) hTst hA
        hJst hq2 hZT hZc (commSp_le_fixSp_zm h hd hc) hfin
      refine concl56f_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_ (fun hq => ?_) (fun hn => ?_)
        hopp''
      · rwa [hvJ, hzh]
      · exfalso
        rw [hq] at hrel1
        have : 2 ^ k < (2 ^ k) ^ 2 := by
          have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
          nlinarith
        omega
      · rcases hx₀s with hx₀s | ⟨hF2, hA₀2⟩
        · exact hx₀s
        · refine absurd ⟨?_, ?_⟩ hn
          · rw [← hd.nat_card_eq, hF2]
          · rw [← card_vIm h hd hJq hJ2, hvJ, hA₀2, hd.nat_card_eq]

end CFSG.Quasithin.MS93.S5
