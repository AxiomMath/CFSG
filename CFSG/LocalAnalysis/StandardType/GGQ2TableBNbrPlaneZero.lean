module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainData
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private def tbnpz_restr {t : ℕ} (S : Finset (Fin t)) :
    PlaneRaw.V t →ₗ[ZMod 3] (S → ZMod 3) where
  toFun v i := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tbnpz_ker_restr {t : ℕ} (S : Finset (Fin t)) :
    LinearMap.ker (tbnpz_restr S) = PlaneRaw.centZero S := by
  ext v
  rw [LinearMap.mem_ker, PlaneRaw.mem_centZero]
  constructor
  · intro h i hi
    have h' := congrFun h ⟨i, hi⟩
    simpa [tbnpz_restr] using h'
  · intro h
    funext i
    simpa [tbnpz_restr] using h i.1 i.2

private theorem tbnpz_surjective_restr {t : ℕ} (S : Finset (Fin t)) :
    Function.Surjective (tbnpz_restr S) := by
  intro g
  refine ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 0, ?_⟩
  funext i
  simp [tbnpz_restr, i.2]

private theorem tbnpz_finrank_centZero {t : ℕ} (S : Finset (Fin t)) :
    Module.finrank (ZMod 3) (PlaneRaw.centZero S) = t - S.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (tbnpz_restr S)
  rw [tbnpz_ker_restr,
    LinearMap.range_eq_top.mpr (tbnpz_surjective_restr S)] at h
  rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  have hV : Module.finrank (ZMod 3) (PlaneRaw.V t) = t := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hV] at h
  omega

private theorem tbnpz_three_le_card {t : ℕ} (S : Finset (Fin t))
    (hcod : 3 + Module.finrank (ZMod 3) (PlaneRaw.centZero S) ≤
      Module.finrank (ZMod 3) (PlaneRaw.V t)) : 3 ≤ S.card := by
  have hV : Module.finrank (ZMod 3) (PlaneRaw.V t) = t := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hV, tbnpz_finrank_centZero] at hcod
  omega

private theorem tbnpz_image_orderEmbOfFin {t n : ℕ} (S : Finset (Fin t))
    (hn : S.card = n) : Finset.univ.image (S.orderEmbOfFin hn) = S := by
  classical
  ext i
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, -, rfl⟩
    exact Finset.orderEmbOfFin_mem S hn a
  · intro hi
    have hmem : i ∈ Set.range (S.orderEmbOfFin hn) := by
      rw [Finset.range_orderEmbOfFin S hn]
      exact hi
    obtain ⟨a, rfl⟩ := hmem
    exact ⟨a, Finset.mem_univ _, rfl⟩

private theorem tbnpz_image_comp_cast {t N M : ℕ} (S : Finset (Fin t)) (s : Fin N → Fin t)
    (hs : Finset.univ.image s = S) (h : M = N) :
    Finset.univ.image (fun i : Fin M => s (Fin.cast h i)) = S := by
  have hcast : Finset.univ.image (fun i : Fin M => Fin.cast h i) = Finset.univ :=
    Finset.image_univ_of_surjective fun b => ⟨Fin.cast h.symm b, by simp⟩
  calc Finset.univ.image (fun i : Fin M => s (Fin.cast h i))
      = Finset.univ.image (s ∘ fun i : Fin M => Fin.cast h i) := rfl
    _ = Finset.image s (Finset.univ.image (fun i : Fin M => Fin.cast h i)) := Finset.image_comp
    _ = S := by rw [hcast, hs]

private theorem tbnpz_chainRootB_castSucc {t m : ℕ} (c : Fin (m + 1) → Fin t)
    (κ : Fin m) (v : PlaneRaw.V t) :
    PlaneRaw.chainRootB t (1 : PlaneRaw.V t) c κ.castSucc v =
      v (c κ.castSucc) - v (c κ.succ) := by
  simp [PlaneRaw.chainRootB, PlaneRaw.chainRootA, PlaneRaw.coordRoot_apply]

private theorem tbnpz_chainRootB_last {t m : ℕ} (c : Fin (m + 1) → Fin t)
    (v : PlaneRaw.V t) :
    PlaneRaw.chainRootB t (1 : PlaneRaw.V t) c (Fin.last m) v = v (c (Fin.last m)) := by
  simp [PlaneRaw.chainRootB, PlaneRaw.coordRoot_apply]

private theorem tbnpz_chainRootD_castSucc {t m : ℕ} (c : Fin (m + 2) → Fin t)
    (κ : Fin (m + 1)) (v : PlaneRaw.V t) :
    PlaneRaw.chainRootD t (1 : PlaneRaw.V t) c κ.castSucc v =
      v (c κ.castSucc) - v (c κ.succ) := by
  simp [PlaneRaw.chainRootD, PlaneRaw.chainRootA, PlaneRaw.coordRoot_apply]

private theorem tbnpz_chainRootD_last {t m : ℕ} (c : Fin (m + 2) → Fin t)
    (v : PlaneRaw.V t) :
    PlaneRaw.chainRootD t (1 : PlaneRaw.V t) c (Fin.last (m + 1)) v =
      v (c ((Fin.last m).castSucc)) + v (c (Fin.last (m + 1))) := by
  simp [PlaneRaw.chainRootD, PlaneRaw.coordRoot_apply]

private theorem tbnpz_range_chainReflB {t m : ℕ} (c : Fin (m + 1) → Fin t) :
    Set.range (PlaneRaw.chainReflB t (1 : PlaneRaw.V t) c) =
      Set.range (fun κ : Fin m =>
        PlaneRaw.swapTwist t (1 : PlaneRaw.V t) (c κ.castSucc) (c κ.succ)) ∪
        {PlaneRaw.negEquiv t (c (Fin.last m))} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨κ, rfl⟩ | rfl
    · exact Or.inl ⟨κ, by simp [PlaneRaw.chainReflB]⟩
    · exact Or.inr (by simp [PlaneRaw.chainReflB])
  · rintro (⟨κ, rfl⟩ | hx)
    · exact ⟨κ.castSucc, by simp [PlaneRaw.chainReflB]⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨Fin.last m, by simp [PlaneRaw.chainReflB, hx]⟩

private theorem tbnpz_range_chainReflD {t m : ℕ} (c : Fin (m + 2) → Fin t) :
    Set.range (PlaneRaw.chainReflD t (1 : PlaneRaw.V t) c) =
      Set.range (fun κ : Fin (m + 1) =>
        PlaneRaw.swapTwist t (1 : PlaneRaw.V t) (c κ.castSucc) (c κ.succ)) ∪
        {PlaneRaw.forkTwist t (1 : PlaneRaw.V t) (c (Fin.last m).castSucc)
          (c (Fin.last (m + 1)))} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨κ, rfl⟩ | rfl
    · exact Or.inl ⟨κ, by simp [PlaneRaw.chainReflD]⟩
    · exact Or.inr (by simp [PlaneRaw.chainReflD])
  · rintro (⟨κ, rfl⟩ | hx)
    · exact ⟨κ.castSucc, by simp [PlaneRaw.chainReflD]⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨Fin.last (m + 1), by simp [PlaneRaw.chainReflD, hx]⟩

private theorem tbnpz_chainRootD_zero_iff {t m : ℕ} (c : Fin (m + 2) → Fin t)
    (v : PlaneRaw.V t) :
    (∀ i : Fin (m + 2), PlaneRaw.chainRootD t (1 : PlaneRaw.V t) c i v = 0) ↔
      ∀ κ, v (c κ) = 0 := by
  have hone : ∀ κ : Fin (m + 2), (1 : PlaneRaw.V t) (c κ) ≠ 0 := fun _ => one_ne_zero
  constructor
  · intro h κ
    have hconj :
        ((∀ κ : Fin (m + 1), (1 : PlaneRaw.V t) (c κ.castSucc) * v (c κ.castSucc) =
          (1 : PlaneRaw.V t) (c κ.succ) * v (c κ.succ)) ∧
          (1 : PlaneRaw.V t) (c (Fin.last m).castSucc) * v (c (Fin.last m).castSucc) +
            (1 : PlaneRaw.V t) (c (Fin.last (m + 1))) * v (c (Fin.last (m + 1))) = 0) := by
      refine ⟨fun κ => ?_, ?_⟩
      · have hk := h κ.castSucc
        rw [tbnpz_chainRootD_castSucc c κ v] at hk
        simpa using sub_eq_zero.mp hk
      · have hk := h (Fin.last (m + 1))
        rw [tbnpz_chainRootD_last c v] at hk
        simpa using hk
    exact (PlaneRaw.chain_kernel_fork c hone v).mp hconj κ
  · intro h i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨κ, rfl⟩ | rfl
    · rw [tbnpz_chainRootD_castSucc c κ v, h κ.castSucc, h κ.succ, sub_zero]
    · rw [tbnpz_chainRootD_last c v, h (Fin.last m).castSucc, h (Fin.last (m + 1)), add_zero]

private theorem tbnpz_datum_B (k : PlaneRaw.PlaneKind) (t n : ℕ) (S : Finset (Fin t))
    (hn : S.card = n) (h3 : 3 ≤ n)
    (hnorm : (planeEntry k t).normalizerGroup (PlaneRaw.Code.zero S) =
      PlaneRaw.signedPermGroupOn t S) :
    Nonempty (CodeWeylDatum (planeEntry k t) (PlaneRaw.Code.zero S)) := by
  classical
  unfold planeEntry at hnorm ⊢
  change PlaneRaw.normalizerOf k t (PlaneRaw.Code.zero S) =
    PlaneRaw.signedPermGroupOn t S at hnorm
  let m := n - 1
  have hm : m + 1 = n := by omega
  have hcS : m + 1 = S.card := hm.trans hn.symm
  let c : Fin (m + 1) → Fin t := fun i => S.orderEmbOfFin rfl (Fin.cast hcS i)
  have hc : Function.Injective c := by
    intro a b hab
    exact Fin.cast_injective hcS ((S.orderEmbOfFin rfl).injective hab)
  have himage : Finset.univ.image c = S :=
    tbnpz_image_comp_cast S (S.orderEmbOfFin rfl) (tbnpz_image_orderEmbOfFin S rfl) hcS
  have hone : ∀ κ : Fin (m + 1), (1 : PlaneRaw.V t) (c κ) ≠ 0 := fun _ => one_ne_zero
  refine ⟨{ ι := Fin (m + 1)
            coxeter := CoxeterMatrix.B (m + 1)
            cartan := CartanMatrix.B (m + 1)
            coroot := PlaneRaw.chainCorootB t (1 : PlaneRaw.V t) c
            root := PlaneRaw.chainRootB t (1 : PlaneRaw.V t) c
            isWeyl := CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B (m + 1) (by omega)
            isCartan := ggIntCartan_B (m + 1)
            pairing := fun i j => PlaneRaw.chainB_pairing hc hone i j
            refl := PlaneRaw.chainReflB t (1 : PlaneRaw.V t) c
            refl_apply := fun i v => by
              have hpair : PlaneRaw.chainRootB t (1 : PlaneRaw.V t) c i
                  (PlaneRaw.chainCorootB t (1 : PlaneRaw.V t) c i) = 2 := by
                rw [PlaneRaw.chainB_pairing hc hone i i, CartanMatrix.B_diag]
                norm_num
              rw [← PlaneRaw.reflection_chainB (e := (1 : PlaneRaw.V t)) (c := c) hone i hpair]
              exact Module.reflection_apply v hpair
            closure_refl := by
              change Subgroup.closure (Set.range (PlaneRaw.chainReflB t (1 : PlaneRaw.V t) c)) =
                PlaneRaw.normalizerOf k t (PlaneRaw.Code.zero S)
              rw [tbnpz_range_chainReflB c, hnorm, ← himage]
              exact PlaneRaw.closure_chainTwist_neg c hc hone
            ker_iff := fun v => by
              change (∀ i : Fin (m + 1), PlaneRaw.chainRootB t (1 : PlaneRaw.V t) c i v = 0) ↔
                v ∈ PlaneRaw.centZero S
              rw [PlaneRaw.mem_centZero]
              constructor
              · intro h i hi
                have hi' : i ∈ Finset.univ.image c := by rw [himage]; exact hi
                obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi'
                have hchain :
                    ((∀ κ : Fin m, (1 : PlaneRaw.V t) (c κ.castSucc) * v (c κ.castSucc) =
                      (1 : PlaneRaw.V t) (c κ.succ) * v (c κ.succ)) ∧
                      (1 : PlaneRaw.V t) (c (Fin.last m)) * v (c (Fin.last m)) = 0) := by
                  refine ⟨fun κ => ?_, ?_⟩
                  · have hk := h κ.castSucc
                    rw [tbnpz_chainRootB_castSucc c κ v] at hk
                    simpa using sub_eq_zero.mp hk
                  · have hk := h (Fin.last m)
                    rw [tbnpz_chainRootB_last c v] at hk
                    simpa using hk
                exact (PlaneRaw.chain_kernel_neg c hone v).mp hchain κ
              · intro h i
                have hall : ∀ κ, v (c κ) = 0 := fun κ =>
                  h (c κ) (by
                    rw [← himage]
                    exact Finset.mem_image.mpr ⟨κ, Finset.mem_univ _, rfl⟩)
                rcases Fin.eq_castSucc_or_eq_last i with ⟨κ, rfl⟩ | rfl
                · rw [tbnpz_chainRootB_castSucc c κ v, hall κ.castSucc, hall κ.succ, sub_zero]
                · rw [tbnpz_chainRootB_last c v, hall (Fin.last m)] }⟩

private theorem tbnpz_datum_D (k : PlaneRaw.PlaneKind) (t n : ℕ) (S : Finset (Fin t))
    (hn : S.card = n) (h4 : 4 ≤ n)
    (hnorm : (planeEntry k t).normalizerGroup (PlaneRaw.Code.zero S) =
      PlaneRaw.evenSignedPermGroupOn t S) :
    Nonempty (CodeWeylDatum (planeEntry k t) (PlaneRaw.Code.zero S)) := by
  classical
  unfold planeEntry at hnorm ⊢
  change PlaneRaw.normalizerOf k t (PlaneRaw.Code.zero S) =
    PlaneRaw.evenSignedPermGroupOn t S at hnorm
  let m := n - 2
  have hm : m + 2 = n := by omega
  have hcS : m + 2 = S.card := hm.trans hn.symm
  let c : Fin (m + 2) → Fin t := fun i => S.orderEmbOfFin rfl (Fin.cast hcS i)
  have hc : Function.Injective c := by
    intro a b hab
    exact Fin.cast_injective hcS ((S.orderEmbOfFin rfl).injective hab)
  have himage : Finset.univ.image c = S :=
    tbnpz_image_comp_cast S (S.orderEmbOfFin rfl) (tbnpz_image_orderEmbOfFin S rfl) hcS
  have hone : ∀ κ : Fin (m + 2), (1 : PlaneRaw.V t) (c κ) ≠ 0 := fun _ => one_ne_zero
  refine ⟨{ ι := Fin (m + 2)
            coxeter := ggCoxeterMatrixD (m + 2)
            cartan := CartanMatrix.D (m + 2)
            coroot := PlaneRaw.chainCorootD t (1 : PlaneRaw.V t) c
            root := PlaneRaw.chainRootD t (1 : PlaneRaw.V t) c
            isWeyl := CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_D (m + 2) (by omega)
            isCartan := ggIntCartan_D (m + 2)
            pairing := fun i j => PlaneRaw.chainD_pairing hc hone i j
            refl := PlaneRaw.chainReflD t (1 : PlaneRaw.V t) c
            refl_apply := fun i v => by
              have hpair : PlaneRaw.chainRootD t (1 : PlaneRaw.V t) c i
                  (PlaneRaw.chainCorootD t (1 : PlaneRaw.V t) c i) = 2 := by
                rw [PlaneRaw.chainD_pairing hc hone i i, CartanMatrix.D_diag]
                norm_num
              rw [← PlaneRaw.reflection_chainD (e := (1 : PlaneRaw.V t)) (c := c) hone i hpair]
              exact Module.reflection_apply v hpair
            closure_refl := by
              change Subgroup.closure (Set.range (PlaneRaw.chainReflD t (1 : PlaneRaw.V t) c)) =
                PlaneRaw.normalizerOf k t (PlaneRaw.Code.zero S)
              rw [tbnpz_range_chainReflD c, hnorm, ← himage]
              exact PlaneRaw.closure_chainTwist_fork c hc hone
            ker_iff := fun v => by
              change (∀ i : Fin (m + 2), PlaneRaw.chainRootD t (1 : PlaneRaw.V t) c i v = 0) ↔
                v ∈ PlaneRaw.centZero S
              rw [tbnpz_chainRootD_zero_iff c v, PlaneRaw.mem_centZero]
              constructor
              · intro h i hi
                have hi' : i ∈ Finset.univ.image c := by rw [himage]; exact hi
                obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi'
                exact h κ
              · intro h κ
                exact h (c κ) (by
                  rw [← himage]
                  exact Finset.mem_image.mpr ⟨κ, Finset.mem_univ _, rfl⟩) }⟩

private theorem tbnpz_cartanD3_swap (i j : Fin 3) :
    CartanMatrix.D 3 (Equiv.swap (0 : Fin 3) 1 i) (Equiv.swap (0 : Fin 3) 1 j) =
      CartanMatrix.A 3 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem tbnpz_cartanA3_diag (i : Fin 3) : CartanMatrix.A 3 i i = 2 := by
  fin_cases i <;> decide

private theorem tbnpz_range_comp_swapD {t : ℕ} (s : Fin 3 → Fin t) :
    Set.range (fun i : Fin 3 =>
      PlaneRaw.chainReflD t (1 : PlaneRaw.V t) s (Equiv.swap (0 : Fin 3) 1 i)) =
      Set.range (PlaneRaw.chainReflD t (1 : PlaneRaw.V t) s) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Equiv.swap (0 : Fin 3) 1 i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Equiv.swap (0 : Fin 3) 1 i, by simp⟩

private theorem tbnpz_datum_A3 (k : PlaneRaw.PlaneKind) (t : ℕ) (S : Finset (Fin t))
    (h3 : S.card = 3)
    (hnorm : (planeEntry k t).normalizerGroup (PlaneRaw.Code.zero S) =
      PlaneRaw.evenSignedPermGroupOn t S) :
    Nonempty (CodeWeylDatum (planeEntry k t) (PlaneRaw.Code.zero S)) := by
  classical
  unfold planeEntry at hnorm ⊢
  change PlaneRaw.normalizerOf k t (PlaneRaw.Code.zero S) =
    PlaneRaw.evenSignedPermGroupOn t S at hnorm
  let s : Fin 3 → Fin t := S.orderEmbOfFin h3
  have hs : Function.Injective s := (S.orderEmbOfFin h3).injective
  have himage : Finset.univ.image s = S := tbnpz_image_orderEmbOfFin S h3
  have hone : ∀ κ : Fin 3, (1 : PlaneRaw.V t) (s κ) ≠ 0 := fun _ => one_ne_zero
  refine ⟨{ ι := Fin 3
            coxeter := CoxeterMatrix.A 3
            cartan := CartanMatrix.A 3
            coroot := fun i => PlaneRaw.chainCorootD t (1 : PlaneRaw.V t) s
              (Equiv.swap (0 : Fin 3) 1 i)
            root := fun i => PlaneRaw.chainRootD t (1 : PlaneRaw.V t) s
              (Equiv.swap (0 : Fin 3) 1 i)
            isWeyl := Or.inl ⟨3, Equiv.refl _, by norm_num,
              Or.inl (CoxeterMatrix.ext (Matrix.ext fun i j => by
                simp [CoxeterMatrix.reindex_apply]))⟩
            isCartan := ggIntCartan_A 3
            pairing := fun i j => by
              rw [PlaneRaw.chainD_pairing hs hone (Equiv.swap (0 : Fin 3) 1 i)
                (Equiv.swap (0 : Fin 3) 1 j), tbnpz_cartanD3_swap i j]
            refl := fun i => PlaneRaw.chainReflD t (1 : PlaneRaw.V t) s
              (Equiv.swap (0 : Fin 3) 1 i)
            refl_apply := fun i v => by
              have hpair : PlaneRaw.chainRootD t (1 : PlaneRaw.V t) s
                  (Equiv.swap (0 : Fin 3) 1 i)
                  (PlaneRaw.chainCorootD t (1 : PlaneRaw.V t) s
                    (Equiv.swap (0 : Fin 3) 1 i)) = 2 := by
                rw [PlaneRaw.chainD_pairing hs hone (Equiv.swap (0 : Fin 3) 1 i)
                  (Equiv.swap (0 : Fin 3) 1 i), tbnpz_cartanD3_swap i i]
                norm_num [tbnpz_cartanA3_diag i]
              rw [← PlaneRaw.reflection_chainD (e := (1 : PlaneRaw.V t)) (c := s) hone
                (Equiv.swap (0 : Fin 3) 1 i) hpair]
              exact Module.reflection_apply v hpair
            closure_refl := by
              change Subgroup.closure (Set.range (fun i : Fin 3 =>
                PlaneRaw.chainReflD t (1 : PlaneRaw.V t) s
                  (Equiv.swap (0 : Fin 3) 1 i))) =
                PlaneRaw.normalizerOf k t (PlaneRaw.Code.zero S)
              rw [tbnpz_range_comp_swapD s, tbnpz_range_chainReflD s, hnorm, ← himage]
              exact PlaneRaw.closure_chainTwist_fork s hs hone
            ker_iff := fun v => by
              change (∀ i : Fin 3, PlaneRaw.chainRootD t (1 : PlaneRaw.V t) s
                (Equiv.swap (0 : Fin 3) 1 i) v = 0) ↔ v ∈ PlaneRaw.centZero S
              have hiff : (∀ i : Fin 3, PlaneRaw.chainRootD t (1 : PlaneRaw.V t) s
                    (Equiv.swap (0 : Fin 3) 1 i) v = 0) ↔
                  (∀ j : Fin 3, PlaneRaw.chainRootD t (1 : PlaneRaw.V t) s j v = 0) := by
                constructor
                · intro h j
                  simpa using h (Equiv.swap (0 : Fin 3) 1 j)
                · intro h i
                  exact h (Equiv.swap (0 : Fin 3) 1 i)
              rw [hiff, tbnpz_chainRootD_zero_iff (m := 1) s v, PlaneRaw.mem_centZero]
              constructor
              · intro h i hi
                have hi' : i ∈ Finset.univ.image s := by rw [himage]; exact hi
                obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi'
                exact h κ
              · intro h κ
                exact h (s κ) (by
                  rw [← himage]
                  exact Finset.mem_image.mpr ⟨κ, Finset.mem_univ _, rfl⟩) }⟩

theorem planeZero_codeWeylDatum (k : PlaneRaw.PlaneKind) (t : ℕ) (S : Finset (Fin t))
    (hadm : (planeEntry k t).admissible (PlaneRaw.Code.zero S))
    (hcod : 3 + finrank (ZMod 3) ((planeEntry k t).cent (PlaneRaw.Code.zero S)) ≤
      finrank (ZMod 3) (planeEntry k t).V) :
    Nonempty (CodeWeylDatum (planeEntry k t) (PlaneRaw.Code.zero S)) := by
  classical
  have _ := hadm
  unfold planeEntry at hcod
  change 3 + Module.finrank (ZMod 3) (PlaneRaw.centZero S) ≤
    Module.finrank (ZMod 3) (PlaneRaw.V t) at hcod
  have h3 : 3 ≤ S.card := tbnpz_three_le_card S hcod
  cases k with
  | linear ε =>
      exact tbnpz_datum_B (.linear ε) t S.card S rfl h3 (by
        unfold planeEntry
        rfl)
  | symplectic =>
      have h2 : S.card ≠ 2 := by omega
      exact tbnpz_datum_B .symplectic t S.card S rfl h3 (by
        unfold planeEntry
        simp [PlaneRaw.normalizerOf, h2])
  | orthogonal δ =>
      by_cases hδ : δ.val = 0
      · by_cases hS3 : S.card = 3
        · exact tbnpz_datum_A3 (.orthogonal δ) t S hS3 (by
            unfold planeEntry
            simp [PlaneRaw.normalizerOf, hδ])
        · have h4 : 4 ≤ S.card := by omega
          exact tbnpz_datum_D (.orthogonal δ) t S.card S rfl h4 (by
            unfold planeEntry
            simp [PlaneRaw.normalizerOf, hδ])
      · exact tbnpz_datum_B (.orthogonal δ) t S.card S rfl h3 (by
          unfold planeEntry
          simp [PlaneRaw.normalizerOf, hδ])

end

end CFSG.StandardType.GGQ2Frame

end
