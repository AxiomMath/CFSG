module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameReal

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private lemma l02qfri_single_eq_of_ne {N : ℕ} (i j : Fin N) (h : i ≠ j) (x : UnitRaw.F) :
    (Pi.single i x : UnitRaw.W N) j = 0 := by
  simp [Pi.single_apply, Ne.symm h]

private lemma l02qfri_single_eq_same {N : ℕ} (i : Fin N) (x : PlaneRaw.F) :
    (Pi.single i x : PlaneRaw.V N) i = x := by
  simp [Pi.single_apply]

private lemma l02qfri_negEquiv_moves {t : ℕ} (i : Fin t) :
    PlaneRaw.negEquiv t i (Pi.single i (1 : PlaneRaw.F)) ≠ Pi.single i (1 : PlaneRaw.F) := by
  intro h
  have h' := congrArg (fun v => v i) h
  simp [PlaneRaw.negEquiv, LinearEquiv.piCongrRight_apply, l02qfri_single_eq_same] at h'
  exact (by decide : (-1 : PlaneRaw.F) ≠ 1) h'

private lemma l02qfri_swapEquiv_moves {t : ℕ} {i j : Fin t} (hij : i ≠ j) :
    PlaneRaw.swapEquiv t i j (Pi.single i (1 : PlaneRaw.F)) ≠ Pi.single i (1 : PlaneRaw.F) := by
  intro h
  have h' := congrArg (fun v => v j) h
  simp [PlaneRaw.swapEquiv, LinearEquiv.funCongrLeft_apply, hij, l02qfri_single_eq_same] at h'

private lemma l02qfri_rotEquiv_moves {t : ℕ} {i j : Fin t} (hij : i ≠ j) :
    PlaneRaw.rotEquiv t i j (Pi.single i (1 : PlaneRaw.F)) ≠ Pi.single i (1 : PlaneRaw.F) := by
  intro h
  have h' := congrArg (fun v => v j) h
  simp [PlaneRaw.rotEquiv, PlaneRaw.swapEquiv, PlaneRaw.negEquiv, LinearEquiv.funCongrLeft_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.mul_apply, hij, l02qfri_single_eq_same] at h'

private lemma l02qfri_orientEquiv_mul_self (t : ℕ) (e : PlaneRaw.V t) :
    PlaneRaw.orientEquiv t e * PlaneRaw.orientEquiv t e = 1 := by
  ext w k
  simp only [LinearEquiv.mul_apply, PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private lemma l02qfri_orientEquiv_symm (t : ℕ) (e : PlaneRaw.V t) :
    (PlaneRaw.orientEquiv t e)⁻¹ = PlaneRaw.orientEquiv t e :=
  inv_eq_of_mul_eq_one_right (l02qfri_orientEquiv_mul_self t e)

private lemma l02qfri_swapTwist_moves {t : ℕ} {e : PlaneRaw.V t} {i j : Fin t}
    (hei : e i ≠ 0) (hej : e j ≠ 0) (hij : i ≠ j) :
    PlaneRaw.swapTwist t e i j (Pi.single i (e i) + Pi.single j (-(e j))) ≠
      (Pi.single i (e i) + Pi.single j (-(e j))) := by
  intro h
  have h' := congrArg (fun w => w i) h
  have h3 : ∀ x : PlaneRaw.F, x = 0 ∨ x = 1 ∨ x = -1 := by decide
  have hx := h3 (e i)
  have hy := h3 (e j)
  rcases hx with hxi | hxi | hxi
  · exact absurd hxi hei
  · rcases hy with hyj | hyj | hyj
    · exact absurd hyj hej
    · simp [PlaneRaw.swapTwist, PlaneRaw.orientEquiv, PlaneRaw.swapEquiv, PlaneRaw.negEquiv,
        l02qfri_orientEquiv_symm, LinearEquiv.piCongrRight_apply, LinearEquiv.funCongrLeft_apply,
        LinearEquiv.mul_apply, hij, l02qfri_single_eq_same, hxi, hyj] at h'
      norm_num at h'
      first
        | exact (by decide : (-1 : PlaneRaw.F) ≠ 1) h'
        | exact (by decide : (1 : PlaneRaw.F) ≠ -1) h'
    · simp [PlaneRaw.swapTwist, PlaneRaw.orientEquiv, PlaneRaw.swapEquiv, PlaneRaw.negEquiv,
        l02qfri_orientEquiv_symm, LinearEquiv.piCongrRight_apply, LinearEquiv.funCongrLeft_apply,
        LinearEquiv.mul_apply, hij, l02qfri_single_eq_same, hxi, hyj] at h'
      norm_num at h'
      first
        | exact (by decide : (-1 : PlaneRaw.F) ≠ 1) h'
        | exact (by decide : (1 : PlaneRaw.F) ≠ -1) h'
  · rcases hy with hyj | hyj | hyj
    · exact absurd hyj hej
    · simp [PlaneRaw.swapTwist, PlaneRaw.orientEquiv, PlaneRaw.swapEquiv, PlaneRaw.negEquiv,
        l02qfri_orientEquiv_symm, LinearEquiv.piCongrRight_apply, LinearEquiv.funCongrLeft_apply,
        LinearEquiv.mul_apply, hij, l02qfri_single_eq_same, hxi, hyj] at h'
      norm_num at h'
      first
        | exact (by decide : (-1 : PlaneRaw.F) ≠ 1) h'
        | exact (by decide : (1 : PlaneRaw.F) ≠ -1) h'
    · simp [PlaneRaw.swapTwist, PlaneRaw.orientEquiv, PlaneRaw.swapEquiv, PlaneRaw.negEquiv,
        l02qfri_orientEquiv_symm, LinearEquiv.piCongrRight_apply, LinearEquiv.funCongrLeft_apply,
        LinearEquiv.mul_apply, hij, l02qfri_single_eq_same, hxi, hyj] at h'
      norm_num at h'
      first
        | exact (by decide : (-1 : PlaneRaw.F) ≠ 1) h'
        | exact (by decide : (1 : PlaneRaw.F) ≠ -1) h'

theorem planeEntry_rawInsideMoved (k : PlaneRaw.PlaneKind) (t : ℕ) :
    RawInsideMoved (planeEntry k t) := by
  intro c hc
  change ∃ g ∈ PlaneRaw.normalizerOf k t c, ∃ v ∈ PlaneRaw.inside k c, g v ≠ v
  have hadm : PlaneRaw.admissible k c := hc.2
  rcases c with S | e
  · rcases k with ε | _ | δ
    ·
      have hS : S.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        subst h
        change 3 ≤ 2 * (∅ : Finset (Fin t)).card + ε.val at hadm
        simp only [Finset.card_empty, Nat.mul_zero, Nat.zero_add] at hadm
        have hε : ε.val < 2 := ε.isLt
        omega
      obtain ⟨i, hi⟩ := hS
      refine ⟨PlaneRaw.negEquiv t i, ?_, Pi.single i (1 : PlaneRaw.F), ?_, ?_⟩
      · apply Subgroup.subset_closure
        exact Or.inr ⟨i, hi, rfl⟩
      · rw [PlaneRaw.mem_inside_zero]
        intro j hj
        rw [PlaneRaw.mem_vSupport] at hj
        have hji : j = i := by
          by_contra hne
          exact hj (l02qfri_single_eq_of_ne i j (Ne.symm hne) 1)
        rw [hji]
        exact hi
      · exact l02qfri_negEquiv_moves i
    ·
      by_cases hS2 : S.card = 2
      ·
        have h1 : 1 < S.card := by omega
        have hex : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j := by
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
          exact ⟨a, b, ha, hb, hab⟩
        refine ⟨PlaneRaw.rotEquiv t hex.choose hex.choose_spec.choose, ?_,
          Pi.single hex.choose (1 : PlaneRaw.F), ?_, ?_⟩
        · change PlaneRaw.rotEquiv t hex.choose hex.choose_spec.choose ∈
            (if S.card = 2 then
              Subgroup.zpowers (if h : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j then
                PlaneRaw.rotEquiv t h.choose h.choose_spec.choose else 1)
            else PlaneRaw.signedPermGroupOn t S)
          rw [if_pos hS2]
          rw [dif_pos hex]
          exact Subgroup.mem_zpowers _
        · rw [PlaneRaw.mem_inside_zero]
          intro k hk
          rw [PlaneRaw.mem_vSupport] at hk
          have hki : k = hex.choose := by
            by_contra hne
            exact hk (l02qfri_single_eq_of_ne hex.choose k (Ne.symm hne) 1)
          rw [hki]
          exact hex.choose_spec.choose_spec.1
        · exact l02qfri_rotEquiv_moves hex.choose_spec.choose_spec.2.2
      ·
        have hS : S.Nonempty := by
          change 2 ≤ S.card at hadm
          have : 0 < S.card := by omega
          exact Finset.card_pos.mp this
        obtain ⟨i, hi⟩ := hS
        refine ⟨PlaneRaw.negEquiv t i, ?_, Pi.single i (1 : PlaneRaw.F), ?_, ?_⟩
        · change PlaneRaw.negEquiv t i ∈
            (if S.card = 2 then
              Subgroup.zpowers (if h : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j then
                PlaneRaw.rotEquiv t h.choose h.choose_spec.choose else 1)
            else PlaneRaw.signedPermGroupOn t S)
          rw [if_neg hS2]
          apply Subgroup.subset_closure
          exact Or.inr ⟨i, hi, rfl⟩
        · rw [PlaneRaw.mem_inside_zero]
          intro j hj
          rw [PlaneRaw.mem_vSupport] at hj
          have hji : j = i := by
            by_contra hne
            exact hj (l02qfri_single_eq_of_ne i j (Ne.symm hne) 1)
          rw [hji]
          exact hi
        · exact l02qfri_negEquiv_moves i
    ·
      by_cases hδ : δ.val = 0
      ·
        change (Even S.card ∧ 3 ≤ S.card + δ.val) ∨ (Odd S.card ∧ 2 ≤ S.card + δ.val) at hadm
        have hS2 : 2 ≤ S.card := by
          rcases hadm with ⟨heven, hge⟩ | ⟨hodd, hge⟩ <;> omega
        have h1 : 1 < S.card := by omega
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1
        refine ⟨PlaneRaw.swapEquiv t i j, ?_, Pi.single i (1 : PlaneRaw.F), ?_, ?_⟩
        · change PlaneRaw.swapEquiv t i j ∈
            (if δ.val = 0 then PlaneRaw.evenSignedPermGroupOn t S else PlaneRaw.signedPermGroupOn t S)
          rw [if_pos hδ]
          apply Subgroup.subset_closure
          exact Or.inl ⟨i, hi, j, hj, rfl⟩
        · rw [PlaneRaw.mem_inside_zero]
          intro k hk
          rw [PlaneRaw.mem_vSupport] at hk
          have hki : k = i := by
            by_contra hne
            exact hk (l02qfri_single_eq_of_ne i k (Ne.symm hne) 1)
          rw [hki]
          exact hi
        · exact l02qfri_swapEquiv_moves hij
      ·
        change (Even S.card ∧ 3 ≤ S.card + δ.val) ∨ (Odd S.card ∧ 2 ≤ S.card + δ.val) at hadm
        have hS : S.Nonempty := by
          rcases hadm with ⟨heven, hge⟩ | ⟨hodd, hge⟩
          · have : 0 < S.card := by omega
            exact Finset.card_pos.mp this
          · have : 0 < S.card := by omega
            exact Finset.card_pos.mp this
        obtain ⟨i, hi⟩ := hS
        refine ⟨PlaneRaw.negEquiv t i, ?_, Pi.single i (1 : PlaneRaw.F), ?_, ?_⟩
        · change PlaneRaw.negEquiv t i ∈
            (if δ.val = 0 then PlaneRaw.evenSignedPermGroupOn t S else PlaneRaw.signedPermGroupOn t S)
          rw [if_neg hδ]
          apply Subgroup.subset_closure
          exact Or.inr ⟨i, hi, rfl⟩
        · rw [PlaneRaw.mem_inside_zero]
          intro k hk
          rw [PlaneRaw.mem_vSupport] at hk
          have hki : k = i := by
            by_contra hne
            exact hk (l02qfri_single_eq_of_ne i k (Ne.symm hne) 1)
          rw [hki]
          exact hi
        · exact l02qfri_negEquiv_moves i
  ·
    rcases hadm with ⟨he, hcard⟩
    have h2 : 2 ≤ (PlaneRaw.Code.extSupport e).card := by
      rcases k with ε | _ | δ
      · exact hcard
      · omega
      · omega
    have h1 : 1 < (PlaneRaw.Code.extSupport e).card := by omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1
    have hei : e i ≠ 0 := (PlaneRaw.mem_extSupport e i).mp hi
    have hej : e j ≠ 0 := (PlaneRaw.mem_extSupport e j).mp hj
    let v : PlaneRaw.V t := Pi.single i (e i) + Pi.single j (-(e j))
    refine ⟨PlaneRaw.swapTwist t e i j, ?_, v, ?_, ?_⟩
    · apply Subgroup.subset_closure
      exact ⟨i, j, hei, hej, rfl⟩
    · change v ∈ PlaneRaw.insideExt e
      rw [PlaneRaw.mem_insideExt]
      refine ⟨?_, ?_⟩
      · intro k hk
        have hki : k ≠ i := by intro h; subst h; exact hei hk
        have hkj : k ≠ j := by intro h; subst h; exact hej hk
        dsimp [v]
        rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) (e i),
          l02qfri_single_eq_of_ne j k (Ne.symm hkj) (-(e j))]
        simp
      · have hv_support : ∀ k, k ≠ i → k ≠ j → v k = 0 := by
          intro k hki hkj
          dsimp [v]
          rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) (e i),
            l02qfri_single_eq_of_ne j k (Ne.symm hkj) (-(e j))]
          simp
        have hsub : ∑ k ∈ ({i, j} : Finset (Fin t)), e k * v k = ∑ k, e k * v k := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro k _ hk
          have hki : k ≠ i := by
            intro h; subst h; exact hk (by simp)
          have hkj : k ≠ j := by
            intro h; subst h; exact hk (by simp)
          rw [hv_support k hki hkj, mul_zero]
        rw [← hsub]
        rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
        have hvi : v i = e i := by
          dsimp [v]
          rw [l02qfri_single_eq_same i (e i),
            l02qfri_single_eq_of_ne j i (Ne.symm hij) (-(e j))]
          simp
        have hvj : v j = -(e j) := by
          dsimp [v]
          rw [l02qfri_single_eq_of_ne i j hij (e i),
            l02qfri_single_eq_same j (-(e j))]
          simp
        rw [hvi, hvj]
        have h3 : ∀ x : PlaneRaw.F, x = 0 ∨ x = 1 ∨ x = -1 := by decide
        have hsq_i : e i * e i = 1 := by
          rcases h3 (e i) with h | h | h
          · exact absurd h hei
          · rw [h]; decide
          · rw [h]; decide
        have hsq_j : e j * e j = 1 := by
          rcases h3 (e j) with h | h | h
          · exact absurd h hej
          · rw [h]; decide
          · rw [h]; decide
        rw [hsq_i, mul_neg, hsq_j]
        simp
    · exact l02qfri_swapTwist_moves hei hej hij

theorem unitFullEntry_rawInsideMoved (N : ℕ) : RawInsideMoved (unitFullEntry N) := by
  intro S hS
  change ∃ g ∈ UnitRaw.normalizerOf S, ∃ v ∈ UnitRaw.inside S, g v ≠ v
  have hcard : 4 ≤ S.card := hS.2
  have h1 : 1 < S.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1
  let w : UnitRaw.W N := Pi.single i (1 : UnitRaw.F) - Pi.single j (1 : UnitRaw.F)
  have hw_not_mem : w ∉ UnitRaw.oneLine N := by
    intro hmem
    obtain ⟨c, hc⟩ := (UnitRaw.mem_oneLine w).mp hmem
    have hwi : w i = 1 := by
      dsimp [w]
      rw [Pi.single_eq_same]
      rw [l02qfri_single_eq_of_ne j i (Ne.symm hij) 1]
      simp
    have hwj : w j = -1 := by
      dsimp [w]
      rw [l02qfri_single_eq_of_ne i j hij 1]
      rw [Pi.single_eq_same]
      simp
    have hci : c = 1 := by rw [← hwi, hc]
    have hcj : c = -1 := by rw [← hwj, hc]
    have h_eq : (1 : UnitRaw.F) = -1 := by
      calc (1 : UnitRaw.F) = c := hci.symm
        _ = -1 := hcj
    exact (by decide : (1 : UnitRaw.F) ≠ -1) h_eq
  have hv_ne_zero : (UnitRaw.oneLine N).mkQ w ≠ 0 := by
    intro h
    have : w ∈ UnitRaw.oneLine N := by
      rw [← Submodule.ker_mkQ (UnitRaw.oneLine N), LinearMap.mem_ker]
      exact h
    exact hw_not_mem this
  refine ⟨UnitRaw.permEquivQ N (Equiv.swap i j), ?_, (UnitRaw.oneLine N).mkQ w, ?_, ?_⟩
  · apply Subgroup.subset_closure
    exact ⟨i, hi, j, hj, rfl⟩
  · apply (UnitRaw.mem_inside_iff S ((UnitRaw.oneLine N).mkQ w)).mpr
    refine ⟨w, rfl, ?_, ?_⟩
    · intro k hk
      have hki : k ≠ i := by intro h; subst h; exact hk hi
      have hkj : k ≠ j := by intro h; subst h; exact hk hj
      dsimp [w]
      rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) 1]
      rw [l02qfri_single_eq_of_ne j k (Ne.symm hkj) 1]
      simp
    · have hsum_i : ∑ k : Fin N, Pi.single i (1 : UnitRaw.F) k = 1 := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          exact l02qfri_single_eq_of_ne i b (Ne.symm hb) 1
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
      have hsum_j : ∑ k : Fin N, Pi.single j (1 : UnitRaw.F) k = 1 := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          exact l02qfri_single_eq_of_ne j b (Ne.symm hb) 1
        · intro hj'
          exact absurd (Finset.mem_univ j) hj'
      simp only [w, Pi.sub_apply, Finset.sum_sub_distrib]
      rw [hsum_i, hsum_j]
      simp
  · have hgv : UnitRaw.permEquivQ N (Equiv.swap i j) ((UnitRaw.oneLine N).mkQ w) = -((UnitRaw.oneLine N).mkQ w) := by
      rw [UnitRaw.permEquivQ_mk]
      have hfun : (fun k : Fin N => w (Equiv.swap i j k)) = -w := by
        funext k
        by_cases hki : k = i
        · subst hki
          dsimp [w]
          rw [Equiv.swap_apply_left]
          rw [l02qfri_single_eq_of_ne k j hij 1]
          rw [Pi.single_eq_same]
          rw [Pi.single_eq_same]
          rw [l02qfri_single_eq_of_ne j k (Ne.symm hij) 1]
          simp
        · by_cases hkj : k = j
          · subst hkj
            dsimp [w]
            rw [Equiv.swap_apply_right]
            rw [Pi.single_eq_same]
            rw [l02qfri_single_eq_of_ne k i hki 1]
            rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) 1]
            rw [Pi.single_eq_same]
            simp
          · have hswap : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
            dsimp [w]
            rw [hswap]
            rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) 1]
            rw [l02qfri_single_eq_of_ne j k (Ne.symm hkj) 1]
            simp
      have hs : Equiv.symm (Equiv.swap i j) = Equiv.swap i j := rfl
      rw [hs]
      rw [hfun]
      simp
    rw [hgv]
    intro h
    have h2v : (2 : UnitRaw.F) • ((UnitRaw.oneLine N).mkQ w) = 0 := by
      rw [show (2 : UnitRaw.F) = 1 + 1 by norm_num]
      rw [add_smul, one_smul]
      exact neg_eq_iff_add_eq_zero.mp h
    have h2ne : (2 : UnitRaw.F) ≠ 0 := by decide
    have hv_zero : (UnitRaw.oneLine N).mkQ w = 0 := (smul_eq_zero.mp h2v).resolve_left h2ne
    exact hv_ne_zero hv_zero

theorem unitHeartEntry_rawInsideMoved (N : ℕ) : RawInsideMoved (unitHeartEntry N) := by
  intro S hS
  change ∃ g ∈ UnitRaw.normalizerOfH S, ∃ v ∈ UnitRaw.insideH S, g v ≠ v
  have hcard : 4 ≤ S.card := hS.2.2
  have h1 : 1 < S.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1
  let w : UnitRaw.W N := Pi.single i (1 : UnitRaw.F) - Pi.single j (1 : UnitRaw.F)
  have hw_sum : ∑ k : Fin N, w k = 0 := by
    have hsum_i : ∑ k : Fin N, Pi.single i (1 : UnitRaw.F) k = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        exact l02qfri_single_eq_of_ne i b (Ne.symm hb) 1
      · intro hi'
        exact absurd (Finset.mem_univ i) hi'
    have hsum_j : ∑ k : Fin N, Pi.single j (1 : UnitRaw.F) k = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        exact l02qfri_single_eq_of_ne j b (Ne.symm hb) 1
      · intro hj'
        exact absurd (Finset.mem_univ j) hj'
    simp only [w, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hsum_i, hsum_j]
    simp
  have hw_ker : w ∈ LinearMap.ker (UnitRaw.sumFun N) := by
    rw [LinearMap.mem_ker, UnitRaw.sumFun_apply]
    exact hw_sum
  let v : ↥(UnitRaw.heart N) := ⟨(UnitRaw.oneLine N).mkQ w, Submodule.mem_map.mpr ⟨w, hw_ker, rfl⟩⟩
  have hv_inside : v ∈ UnitRaw.insideH S := by
    change (v : UnitRaw.Vfull N) ∈ UnitRaw.inside (S : Finset (Fin N))
    apply (UnitRaw.mem_inside_iff (S : Finset (Fin N)) ((UnitRaw.oneLine N).mkQ w)).mpr
    refine ⟨w, rfl, ?_, hw_sum⟩
    intro k hk
    have hki : k ≠ i := by intro h; subst h; exact hk hi
    have hkj : k ≠ j := by intro h; subst h; exact hk hj
    dsimp [w]
    rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) 1]
    rw [l02qfri_single_eq_of_ne j k (Ne.symm hkj) 1]
    simp
  have hv_ne_zero : v ≠ 0 := by
    intro hzero
    have hw_mem : w ∈ UnitRaw.oneLine N := by
      have hval : (v : UnitRaw.Vfull N) = 0 := by simp [hzero]
      have hmk : (UnitRaw.oneLine N).mkQ w = 0 := by simpa [v] using hval
      rw [← Submodule.ker_mkQ (UnitRaw.oneLine N), LinearMap.mem_ker]
      exact hmk
    have hwi : w i = 1 := by
      dsimp [w]
      rw [Pi.single_eq_same]
      rw [l02qfri_single_eq_of_ne j i (Ne.symm hij) 1]
      simp
    have hwj : w j = -1 := by
      dsimp [w]
      rw [l02qfri_single_eq_of_ne i j hij 1]
      rw [Pi.single_eq_same]
      simp
    obtain ⟨c, hc⟩ := (UnitRaw.mem_oneLine w).mp hw_mem
    have hci : c = 1 := by rw [← hwi, hc]
    have hcj : c = -1 := by rw [← hwj, hc]
    have h_eq : (1 : UnitRaw.F) = -1 := by
      calc (1 : UnitRaw.F) = c := hci.symm
        _ = -1 := hcj
    exact (by decide : (1 : UnitRaw.F) ≠ -1) h_eq
  refine ⟨UnitRaw.permEquivH N (Equiv.swap i j), ?_, v, hv_inside, ?_⟩
  · apply Subgroup.subset_closure
    exact ⟨i, hi, j, hj, rfl⟩
  · have hgv : UnitRaw.permEquivH N (Equiv.swap i j) v = -v := by
      ext
      change UnitRaw.permEquivQ N (Equiv.swap i j) (v : UnitRaw.Vfull N) = -(v : UnitRaw.Vfull N)
      have hv_eq : (v : UnitRaw.Vfull N) = (UnitRaw.oneLine N).mkQ w := rfl
      rw [hv_eq]
      rw [UnitRaw.permEquivQ_mk]
      have hfun : (fun k : Fin N => w (Equiv.swap i j k)) = -w := by
        funext k
        by_cases hki : k = i
        · subst hki
          dsimp [w]
          rw [Equiv.swap_apply_left]
          rw [l02qfri_single_eq_of_ne k j hij 1]
          rw [Pi.single_eq_same]
          rw [Pi.single_eq_same]
          rw [l02qfri_single_eq_of_ne j k (Ne.symm hij) 1]
          simp
        · by_cases hkj : k = j
          · subst hkj
            dsimp [w]
            rw [Equiv.swap_apply_right]
            rw [Pi.single_eq_same]
            rw [l02qfri_single_eq_of_ne k i hki 1]
            rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) 1]
            rw [Pi.single_eq_same]
            simp
          · have hswap : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
            dsimp [w]
            rw [hswap]
            rw [l02qfri_single_eq_of_ne i k (Ne.symm hki) 1]
            rw [l02qfri_single_eq_of_ne j k (Ne.symm hkj) 1]
            simp
      have hs : Equiv.symm (Equiv.swap i j) = Equiv.swap i j := rfl
      rw [hs]
      rw [hfun]
      simp
    rw [hgv]
    intro h
    have h2v : (2 : UnitRaw.F) • v = 0 := by
      rw [show (2 : UnitRaw.F) = 1 + 1 by norm_num]
      rw [add_smul, one_smul]
      exact neg_eq_iff_add_eq_zero.mp h
    have h2ne : (2 : UnitRaw.F) ≠ 0 := by decide
    have hv_zero : v = 0 := (smul_eq_zero.mp h2v).resolve_left h2ne
    exact hv_ne_zero hv_zero

theorem classicalCatalogue_rawInsideMoved (k : FrameKind) (hk : IsClassical k) :
    RawInsideMoved (classicalCatalogue k) := by
  cases k with
  | lin t ε => exact planeEntry_rawInsideMoved (.linear ε) t
  | symp t => exact planeEntry_rawInsideMoved .symplectic t
  | orth t δ => exact planeEntry_rawInsideMoved (.orthogonal δ) t
  | unitFull N => exact unitFullEntry_rawInsideMoved N
  | unitHeart N => exact unitHeartEntry_rawInsideMoved N
  | exceptional m => exact absurd hk (by simp [IsClassical])

end

end CFSG.StandardType.GGQ2Frame
