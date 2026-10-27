module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenComb
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenSupp
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenConj
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenPhan
import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

open CFSG.StandardType (ggCoxeterMatrixD)

@[expose] noncomputable def TBJOmData.simpleSub {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) (i : Fin r) :
    Subgroup (V ≃ₗ[K] V) :=
  if i.val + 1 < r then Δ.rankOne (simpleLo i) (simpleHi i)
  else Δ.rankOnePos (simpleLo i) (simpleHi i)

theorem TBJOmData.simpleSub_le {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) (i : Fin r) :
    Δ.simpleSub i ≤ orthDerived Q := by
  intro x hx
  by_cases hi : i.val + 1 < r
  · rw [TBJOmData.simpleSub, if_pos hi] at hx
    exact ((ggOTwoPrime_le _).trans inf_le_right) hx
  · rw [TBJOmData.simpleSub, if_neg hi] at hx
    exact ((ggOTwoPrime_le _).trans inf_le_right) hx

theorem TBJOmData.simpleSub_le_sup {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
    {r : ℕ} (Δ : TBJOmData Q p A r) (hr : 2 ≤ r) (i : Fin r) :
    Δ.simpleSub i ≤ ⨆ (a : Fin r) (b : Fin r) (_ : a ≠ b), (Δ.rankOne a b ⊔ Δ.rankOnePos a b) := by
  intro x hx
  have hne : simpleLo i ≠ simpleHi i := simpleLo_ne_simpleHi hr i
  by_cases hi : i.val + 1 < r
  · rw [TBJOmData.simpleSub, if_pos hi] at hx
    exact Subgroup.mem_iSup_of_mem (S := fun a => ⨆ (b : Fin r) (_ : a ≠ b),
      (Δ.rankOne a b ⊔ Δ.rankOnePos a b)) (simpleLo i)
      (Subgroup.mem_iSup_of_mem (S := fun b => ⨆ (_ : simpleLo i ≠ b),
        (Δ.rankOne (simpleLo i) b ⊔ Δ.rankOnePos (simpleLo i) b)) (simpleHi i)
        (Subgroup.mem_iSup_of_mem (S := fun (_ : simpleLo i ≠ simpleHi i) =>
          (Δ.rankOne (simpleLo i) (simpleHi i) ⊔
            Δ.rankOnePos (simpleLo i) (simpleHi i))) hne
          (Subgroup.mem_sup_left hx)))
  · rw [TBJOmData.simpleSub, if_neg hi] at hx
    exact Subgroup.mem_iSup_of_mem (S := fun a => ⨆ (b : Fin r) (_ : a ≠ b),
      (Δ.rankOne a b ⊔ Δ.rankOnePos a b)) (simpleLo i)
      (Subgroup.mem_iSup_of_mem (S := fun b => ⨆ (_ : simpleLo i ≠ b),
        (Δ.rankOne (simpleLo i) b ⊔ Δ.rankOnePos (simpleLo i) b)) (simpleHi i)
        (Subgroup.mem_iSup_of_mem (S := fun (_ : simpleLo i ≠ simpleHi i) =>
          (Δ.rankOne (simpleLo i) (simpleHi i) ⊔
            Δ.rankOnePos (simpleLo i) (simpleHi i))) hne
          (Subgroup.mem_sup_right hx)))


private theorem q2cO5g_conj_eq_self_of_commute {G : Type*} [Group G] {w x : G}
    (h : x * w = w * x) : MulAut.conj w x = x := by
  rw [MulAut.conj_apply, ← h, mul_assoc, mul_inv_cancel, mul_one]

private theorem q2cO5g_simpleSub_fixes_outside {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (hr : 3 ≤ r) (h2 : Δ.RankOneModel)
    (i : Fin r) {x : V ≃ₗ[K] V} (hx : x ∈ Δ.simpleSub i) :
    ∀ l : Fin r, l ∉ ({simpleLo i, simpleHi i} : Finset (Fin r)) →
      ∀ u ∈ Δ.F.U l, x u = u := by
  have hab : simpleLo i ≠ simpleHi i := simpleLo_ne_simpleHi (by omega) i
  intro l hl u hu
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  by_cases hi : i.val + 1 < r
  · rw [TBJOmData.simpleSub, if_pos hi] at hx
    exact Δ.fixes_outside_rankOne (i := simpleLo i) (j := simpleHi i) h2 hab x hx
      l hl.1 hl.2 u hu
  · rw [TBJOmData.simpleSub, if_neg hi] at hx
    exact Δ.fixes_outside_rankOnePos (i := simpleLo i) (j := simpleHi i) hfix hr h2 hab
      x hx l hl.1 hl.2 u hu

theorem TBJOmData.simpleSub_iso {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (hr : 3 ≤ r)
    (h2 : Δ.RankOneModel) {f : ℕ} (hf : Nat.card K = 2 ^ f) (K' : Type) [Field K'] [Finite K']
    [CharP K' 2] (hK' : Nat.card K' = (2 ^ f) ^ 2) (i : Fin r) :
    Nonempty (Su K' 2 f 2 ≃* Δ.simpleSub i) := by
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.CTP.exists_suid_two_equiv_sl hK' hf
  have hne : simpleLo i ≠ simpleHi i := simpleLo_ne_simpleHi (by omega) i
  by_cases hi : i.val + 1 < r
  · rw [TBJOmData.simpleSub, if_pos hi]
    obtain ⟨⟨θ, hinj, hrange, -⟩, -⟩ := h2 (simpleLo i) (simpleHi i) hne
    exact ⟨φ.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩
  · have hi' : i.val + 1 = r := by omega
    have ha : (simpleLo i).val = r - 2 := simpleLo_of_last hi'
    have hb : (simpleHi i).val = r - 1 := simpleHi_of_last hi'
    let k : Fin r := ⟨0, by omega⟩
    have hak : simpleLo i ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      simp only [k, Fin.val_mk] at hv
      omega
    have hbk : simpleHi i ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      simp only [k, Fin.val_mk] at hv
      omega
    obtain ⟨w, -, hwfix, -, hwconj⟩ :=
      Δ.exists_dinv_conj hfix (i := simpleLo i) (j := simpleHi i) (k := k) hne hbk hak
    obtain ⟨⟨θ, hinj, hrange, -⟩, -⟩ := h2 (simpleLo i) (simpleHi i) hne
    rw [TBJOmData.simpleSub, if_neg hi]
    refine ⟨(φ.trans ((MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr hrange))).trans
      ((Subgroup.equivMapOfInjective (Δ.rankOne (simpleLo i) (simpleHi i))
        (MulAut.conj w).toMonoidHom (MulAut.conj w).injective).trans
        (MulEquiv.subgroupCongr hwconj.symm))⟩

theorem TBJOmData.simpleSub_comm {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) (hr : 4 ≤ r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (h2 : Δ.RankOneModel) (i j : Fin r)
    (hM : ggCoxeterMatrixD r i j = 2) :
    ∀ x ∈ Δ.simpleSub i, ∀ y ∈ Δ.simpleSub j, x * y = y * x := by
  intro x hx y hy
  have hxΩ : x ∈ orthDerived Q := Δ.simpleSub_le i hx
  have hyΩ : y ∈ orthDerived Q := Δ.simpleSub_le j hy
  have hxfix := q2cO5g_simpleSub_fixes_outside Δ hfix (by omega) h2 i hx
  have hyfix := q2cO5g_simpleSub_fixes_outside Δ hfix (by omega) h2 j hy
  have hne' : simpleLo j ≠ simpleHi j := simpleLo_ne_simpleHi (by omega) j
  have hij : i ≠ j := by
    rintro rfl
    have h1 : ggCoxeterMatrixD r i i = 1 := (ggCoxeterMatrixD r).diagonal i
    omega
  rcases ggCoxeterMatrixD_eq_two_cases hr hij hM with hdisj | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact Δ.commute_of_fixes_outside hfix (S := {simpleLo i, simpleHi i})
      (S' := {simpleLo j, simpleHi j}) hdisj hxΩ hyΩ hxfix hyfix
  · have hi' : i.val + 1 < r := by omega
    have hlast : j.val + 1 = r := hj
    have hli : (simpleLo i).val = r - 2 := by
      rw [simpleLo_of_lt hi']; omega
    have hhi : (simpleHi i).val = r - 1 := by
      rw [simpleHi_of_lt hi']; omega
    have hlj : (simpleLo j).val = r - 2 := simpleLo_of_last hlast
    have hhj : (simpleHi j).val = r - 1 := simpleHi_of_last hlast
    have hL : simpleLo i = simpleLo j := Fin.ext (by rw [hli, hlj])
    have hH : simpleHi i = simpleHi j := Fin.ext (by rw [hhi, hhj])
    rw [TBJOmData.simpleSub, if_pos hi'] at hx
    rw [TBJOmData.simpleSub, if_neg (by omega : ¬ j.val + 1 < r)] at hy
    rw [hL, hH] at hx
    exact (h2 _ _ hne').2 x hx y hy
  · have hj' : j.val + 1 < r := by omega
    have hlast : i.val + 1 = r := hi
    have hli : (simpleLo i).val = r - 2 := simpleLo_of_last hlast
    have hhi : (simpleHi i).val = r - 1 := simpleHi_of_last hlast
    have hlj : (simpleLo j).val = r - 2 := by
      rw [simpleLo_of_lt hj']; omega
    have hhj : (simpleHi j).val = r - 1 := by
      rw [simpleHi_of_lt hj']; omega
    have hL : simpleLo i = simpleLo j := Fin.ext (by rw [hli, hlj])
    have hH : simpleHi i = simpleHi j := Fin.ext (by rw [hhi, hhj])
    rw [TBJOmData.simpleSub, if_neg (by omega : ¬ i.val + 1 < r)] at hx
    rw [TBJOmData.simpleSub, if_pos hj'] at hy
    rw [hL, hH] at hx
    exact ((h2 _ _ hne').2 y hy x hx).symm

private theorem q2cO5g_pair_map_conj {f : ℕ} {K' : Type} [Field K'] [Finite K']
    [CharP K' 2] {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K' 2 f W U V) (w : X) :
    UnitaryBlockStandardPair K' 2 f (W.map (MulAut.conj w).toMonoidHom)
      (U.map (MulAut.conj w).toMonoidHom) (V.map (MulAut.conj w).toMonoidHom) := by
  obtain ⟨θ, c, hrange, hker, hUV⟩ := h
  refine ⟨(MulAut.conj w).toMonoidHom.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj w).injective]
    exact hker
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by rw [← Subgroup.map_map, h1],
        by rw [← Subgroup.map_map, h2]⟩
    · right
      exact ⟨by rw [← Subgroup.map_map, h1],
        by rw [← Subgroup.map_map, h2]⟩

private theorem q2cO5g_pair_swap {f : ℕ} {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K' 2 f W U V) :
    UnitaryBlockStandardPair K' 2 f W V U := by
  obtain ⟨θ, c, hrange, hker, hUV⟩ := h
  refine ⟨θ, c, hrange, hker, ?_⟩
  rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

theorem TBJOmData.pair_rankOne_rankOnePos {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {f : ℕ} {K' : Type}
    [Field K'] [Finite K'] [CharP K' 2] (h4 : Δ.PairModel f K')
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ W : Subgroup (V ≃ₗ[K] V),
      UnitaryBlockStandardPair K' 2 f W (Δ.rankOne a b) (Δ.rankOnePos b c) := by
  obtain ⟨W, hW⟩ := h4 a b c hab hbc hac
  obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.dinvMove a b hab
  have hU := Δ.rankOne_map_dinv_self hab w hwΩ hwconj
  have hwconj' : ∀ g, w * Δ.τ g * w⁻¹ = Δ.τ (NbrOrth.dinv b a g) := by
    intro g
    rw [hwconj]
    congr 1
    funext l
    simp only [OrthNs.dinv_apply_eq, if_neg hab, if_neg hab.symm, or_comm]
  have hV := Δ.rankOne_map_dinv (i := c) (j := b) (k := a) hbc.symm hab.symm hac.symm
    w hwΩ hwconj'
  rw [Δ.rankOne_comm_index c b, Δ.rankOnePos_comm_index c b] at hV
  have hpair := q2cO5g_pair_map_conj hW w
  rw [hU, hV] at hpair
  exact ⟨W.map (MulAut.conj w).toMonoidHom, hpair⟩

theorem TBJOmData.pair_rankOnePos_rankOnePos {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {f : ℕ} {K' : Type}
    [Field K'] [Finite K'] [CharP K' 2] (h4 : Δ.PairModel f K')
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ W : Subgroup (V ≃ₗ[K] V),
      UnitaryBlockStandardPair K' 2 f W (Δ.rankOnePos a b) (Δ.rankOnePos b c) := by
  obtain ⟨W, hW⟩ := h4 a b c hab hbc hac
  obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.dinvMove a c hac
  have hU := Δ.rankOne_map_dinv (i := b) (j := a) (k := c) hab.symm hac hbc w hwΩ hwconj
  rw [Δ.rankOne_comm_index b a, Δ.rankOnePos_comm_index b a] at hU
  have hwconj' : ∀ g, w * Δ.τ g * w⁻¹ = Δ.τ (NbrOrth.dinv c a g) := by
    intro g
    rw [hwconj]
    congr 1
    funext l
    simp only [OrthNs.dinv_apply_eq, if_neg hac, if_neg hac.symm, or_comm]
  have hV := Δ.rankOne_map_dinv (i := b) (j := c) (k := a) hbc hac.symm hab.symm w hwΩ hwconj'
  have hpair := q2cO5g_pair_map_conj hW w
  rw [hU, hV] at hpair
  exact ⟨W.map (MulAut.conj w).toMonoidHom, hpair⟩

theorem TBJOmData.pair_signed {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) {f : ℕ} {K' : Type}
    [Field K'] [Finite K'] [CharP K' 2] (h4 : Δ.PairModel f K')
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (s t : Bool) :
    ∃ W : Subgroup (V ≃ₗ[K] V), UnitaryBlockStandardPair K' 2 f W
      (if s then Δ.rankOnePos a b else Δ.rankOne a b)
      (if t then Δ.rankOnePos b c else Δ.rankOne b c) := by
  cases s <;> cases t
  · exact h4 a b c hab hbc hac
  · exact Δ.pair_rankOne_rankOnePos h4 hab hbc hac
  · obtain ⟨W, hW⟩ := Δ.pair_rankOne_rankOnePos h4 hbc.symm hab.symm hac.symm
    rw [Δ.rankOne_comm_index c b, Δ.rankOnePos_comm_index b a] at hW
    exact ⟨W, q2cO5g_pair_swap hW⟩
  · exact Δ.pair_rankOnePos_rankOnePos h4 hab hbc hac

theorem TBJOmData.simpleSub_pair {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r)
    (hr : 4 ≤ r) {f : ℕ} {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (h4 : Δ.PairModel f K') (i j : Fin r) (hM : ggCoxeterMatrixD r i j = 3) :
    ∃ W : Subgroup (V ≃ₗ[K] V), UnitaryBlockStandardPair K' 2 f W (Δ.simpleSub i)
      (Δ.simpleSub j) := by
  rcases (ggCoxeterMatrixD_eq_three_iff (by omega) i j).mp hM with
    ⟨hji, hjr⟩ | ⟨hij, hir⟩ | ⟨hir, hjr⟩ | ⟨hjr, hir⟩
  · have hi : i.val + 1 < r := by omega
    have hj : j.val + 1 < r := hjr
    have hv1 : (simpleLo i).val = i.val := simpleLo_of_lt hi
    have hv2 : (simpleHi i).val = i.val + 1 := simpleHi_of_lt hi
    have hv3 : (simpleLo j).val = j.val := simpleLo_of_lt hj
    have hv4 : (simpleHi j).val = j.val + 1 := simpleHi_of_lt hj
    have hsl : simpleLo j = simpleHi i := Fin.ext (by rw [hv3, hv2]; omega)
    have hab : simpleLo i ≠ simpleHi i := Fin.ne_of_val_ne (by rw [hv1, hv2]; omega)
    have hbc : simpleHi i ≠ simpleHi j := Fin.ne_of_val_ne (by rw [hv2, hv4]; omega)
    have hac : simpleLo i ≠ simpleHi j := Fin.ne_of_val_ne (by rw [hv1, hv4]; omega)
    simp only [TBJOmData.simpleSub, if_pos hi, if_pos hj]
    rw [hsl]
    exact h4 (simpleLo i) (simpleHi i) (simpleHi j) hab hbc hac
  · have hi : i.val + 1 < r := hir
    have hj : j.val + 1 < r := by omega
    have hv1 : (simpleLo j).val = j.val := simpleLo_of_lt hj
    have hv2 : (simpleHi j).val = j.val + 1 := simpleHi_of_lt hj
    have hv3 : (simpleLo i).val = i.val := simpleLo_of_lt hi
    have hv4 : (simpleHi i).val = i.val + 1 := simpleHi_of_lt hi
    have hsl : simpleLo i = simpleHi j := Fin.ext (by rw [hv3, hv2]; omega)
    have hab : simpleLo j ≠ simpleHi j := Fin.ne_of_val_ne (by rw [hv1, hv2]; omega)
    have hbc : simpleHi j ≠ simpleHi i := Fin.ne_of_val_ne (by rw [hv2, hv4]; omega)
    have hac : simpleLo j ≠ simpleHi i := Fin.ne_of_val_ne (by rw [hv1, hv4]; omega)
    simp only [TBJOmData.simpleSub, if_pos hi, if_pos hj]
    rw [hsl]
    obtain ⟨W, hW⟩ := h4 (simpleLo j) (simpleHi j) (simpleHi i) hab hbc hac
    exact ⟨W, q2cO5g_pair_swap hW⟩
  · have hi : i.val + 1 < r := by omega
    have hlast : j.val + 1 = r := hjr
    have hv1 : (simpleLo i).val = r - 3 := by rw [simpleLo_of_lt hi]; omega
    have hv2 : (simpleHi i).val = r - 2 := by rw [simpleHi_of_lt hi]; omega
    have hv3 : (simpleLo j).val = r - 2 := simpleLo_of_last hlast
    have hv4 : (simpleHi j).val = r - 1 := simpleHi_of_last hlast
    have hab : simpleLo i ≠ simpleHi i := Fin.ne_of_val_ne (by rw [hv1, hv2]; omega)
    have hbc : simpleHi i ≠ simpleHi j := Fin.ne_of_val_ne (by rw [hv2, hv4]; omega)
    have hac : simpleLo i ≠ simpleHi j := Fin.ne_of_val_ne (by rw [hv1, hv4]; omega)
    have hsl : simpleLo j = simpleHi i := Fin.ext (by rw [hv3, hv2])
    simp only [TBJOmData.simpleSub, if_pos hi, if_neg (by omega : ¬ j.val + 1 < r)]
    rw [hsl]
    exact Δ.pair_rankOne_rankOnePos h4 (a := simpleLo i) (b := simpleHi i)
      (c := simpleHi j) hab hbc hac
  · have hj : j.val + 1 < r := by omega
    have hlast : i.val + 1 = r := hir
    have hv1 : (simpleLo j).val = r - 3 := by rw [simpleLo_of_lt hj]; omega
    have hv2 : (simpleHi j).val = r - 2 := by rw [simpleHi_of_lt hj]; omega
    have hv3 : (simpleLo i).val = r - 2 := simpleLo_of_last hlast
    have hv4 : (simpleHi i).val = r - 1 := simpleHi_of_last hlast
    have hab : simpleLo j ≠ simpleHi j := Fin.ne_of_val_ne (by rw [hv1, hv2]; omega)
    have hbc : simpleHi j ≠ simpleHi i := Fin.ne_of_val_ne (by rw [hv2, hv4]; omega)
    have hac : simpleLo j ≠ simpleHi i := Fin.ne_of_val_ne (by rw [hv1, hv4]; omega)
    have hsl : simpleLo i = simpleHi j := Fin.ext (by rw [hv3, hv2])
    simp only [TBJOmData.simpleSub, if_neg (by omega : ¬ i.val + 1 < r), if_pos hj]
    rw [hsl]
    obtain ⟨W, hW⟩ := Δ.pair_rankOne_rankOnePos h4 (a := simpleLo j)
      (b := simpleHi j) (c := simpleHi i) hab hbc hac
    exact ⟨W, q2cO5g_pair_swap hW⟩


theorem tbjOm_generation_model (hD : PhanDInput2) {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r) (hr : 4 ≤ r)
    (hq : 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (h2 : Δ.RankOneModel) (h4 : Δ.PairModel f K')
    (hUPlus : Even r → Nonempty ((lieUniversal .POmegaPlus r 2 f Nat.prime_two).K ≃* ↥(orthDerived Q)))
    (hUMinus : Odd r → Nonempty ((lieUniversal .POmegaMinus r 2 f Nat.prime_two).K ≃* ↥(orthDerived Q))) :
    (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j), (Δ.rankOne i j ⊔ Δ.rankOnePos i j)) = orthDerived Q := by
  classical
  have hq4 : 4 ≤ 2 ^ f := by rw [← hf]; exact hq
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  haveI : Finite ↥(orthDerived Q) := inferInstance
  have hY : ⨆ i, Δ.simpleSub i = orthDerived Q :=
    iSup_eq_of_phanD hD (Ω := orthDerived Q) hr hq4 K' hK' Δ.simpleSub
      Δ.simpleSub_le
      (fun i => Δ.simpleSub_iso hfix (by omega) h2 hf K' hK' i)
      (fun i j hM => Δ.simpleSub_comm hr hfix h2 i j hM)
      (fun i j hM => Δ.simpleSub_pair hr h4 i j hM)
      hUPlus hUMinus
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun h => ?_
    exact sup_le (Δ.rankOne_le i j) (Δ.rankOnePos_le i j)
  · rw [← hY]
    exact iSup_le fun i => Δ.simpleSub_le_sup (by omega) i

end OrthTorus

end CFSG.StandardType

end
