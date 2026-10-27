module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Defs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Node
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Seed

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBF4TwoInputs

@[expose] def torusMove (m : Fin 4) (f : Fin 3 → Multiplicative (ZMod 3)) :
    Fin 3 → Multiplicative (ZMod 3) :=
  if h : (m : ℕ) < 3 then TableBF4Two.reflHom ⟨m, h⟩ f else TableBF4TwoInputs.shift f

@[expose] def torusWord (w : List (Fin 4)) (f : Fin 3 → Multiplicative (ZMod 3)) :
    Fin 3 → Multiplicative (ZMod 3) :=
  w.foldr torusMove f

@[expose] def vecE0 : Fin 3 → Multiplicative (ZMod 3) :=
  Pi.mulSingle 0 (Multiplicative.ofAdd 1)

@[expose] def vecE01 : Fin 3 → Multiplicative (ZMod 3) :=
  (Pi.mulSingle 0 (Multiplicative.ofAdd 1) : Fin 3 → Multiplicative (ZMod 3)) *
    (Pi.mulSingle 1 (Multiplicative.ofAdd 1) : Fin 3 → Multiplicative (ZMod 3))

@[expose] def vecDelta : Fin 3 → Multiplicative (ZMod 3) :=
  fun _ => Multiplicative.ofAdd (1 : ZMod 3)

@[expose] def nodeWords : List (List (Fin 4)) :=
  [[], [0], [1], [1, 0], [3], [3, 0], [3, 1], [3, 1, 0], [3, 3], [3, 3, 0], [3, 3, 1],
    [3, 3, 1, 0]]

@[expose] def threeWords : List (List (Fin 4)) :=
  [[], [0], [1], [2], [1, 0], [2, 0], [2, 1], [2, 1, 0]]

theorem exists_nodeWords : ∀ a b c : Multiplicative (ZMod 3), (a = 1 ∨ b = 1 ∨ c = 1) →
    (a ≠ 1 ∨ b ≠ 1 ∨ c ≠ 1) →
      ∃ w ∈ nodeWords, torusWord w vecE0 = ![a, b, c] ∨ torusWord w vecE01 = ![a, b, c] := by
  decide +kernel

theorem exists_threeWords : ∀ a b c : Multiplicative (ZMod 3), a ≠ 1 → b ≠ 1 → c ≠ 1 →
    ∃ w ∈ threeWords, torusWord w vecDelta = ![a, b, c] := by
  decide +kernel

theorem not_isSolvable_of_isQuasisimple {Q : Type} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  intro h
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)

section Orbits

variable
  {K : Type} [Field K] [CharP K 2]

theorem exists_mulEquiv_torusMove {y : adjointGroup .F4 K} {g : Fin 3 → Multiplicative (ZMod 3)}
    (h : ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K, α y = TableBF4Two.torus3 K g)
    (m : Fin 4) :
    ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      α y = TableBF4Two.torus3 K (torusMove m g) := by
  obtain ⟨α, hα⟩ := h
  rw [torusMove]
  split_ifs with hm
  · refine ⟨α.trans (MulAut.conj (TableBF4Two.reflGen K ⟨m, hm⟩)), ?_⟩
    rw [MulEquiv.trans_apply, hα, MulAut.conj_apply, TableBF4Two.reflGen_conj_torus3]
  · refine ⟨α.trans (MulAut.conj (cElt K)), ?_⟩
    rw [MulEquiv.trans_apply, hα, MulAut.conj_apply, cElt_conj_torus3]

theorem exists_mulEquiv_torusWord {y : adjointGroup .F4 K} {g : Fin 3 → Multiplicative (ZMod 3)}
    (h : ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K, α y = TableBF4Two.torus3 K g) :
    ∀ w : List (Fin 4), ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      α y = TableBF4Two.torus3 K (torusWord w g)
  | [] => h
  | m :: w => exists_mulEquiv_torusMove (exists_mulEquiv_torusWord h w) m

theorem not_eltHyp_vecDelta (h3C : GGF4TwoThreeCSolv K) (D : Subgroup (adjointGroup .F4 K)) :
    ¬ EltHyp (TableBF4Two.torus3 K vecDelta) D := by
  rintro ⟨hDC, -, hDq⟩
  have : Group.IsSolvable (Subgroup.centralizer
      ({TableBF4Two.torus3 K vecDelta} : Set (adjointGroup .F4 K))) := h3C
  exact not_isSolvable_of_isQuasisimple hDq
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDC))

variable [Finite K]

theorem exists_mulEquiv_nodeElt_eq_vecE0 :
    ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      α (nodeElt K) = TableBF4Two.torus3 K vecE0 := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_nodeElt_eq_torusGen_zero (K := K)
  exact ⟨α, hα.trans (torusGen_eq_torus3 0)⟩

theorem exists_mulEquiv_nodeElt_eq_vecE01 :
    ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      α (nodeElt K) = TableBF4Two.torus3 K vecE01 := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_nodeElt_eq_s0s1 (K := K)
  refine ⟨α, hα.trans ?_⟩
  rw [torusGen_eq_torus3, torusGen_eq_torus3, ← map_mul]
  rfl

theorem eltConcl_range_torus3 (hK : Nat.card K = 2) (h3C : GGF4TwoThreeCSolv K)
    {x : adjointGroup .F4 K} (hx : x ∈ (TableBF4Two.torus3 K).range) (hx1 : x ≠ 1)
    {D : Subgroup (adjointGroup .F4 K)} (hD : EltHyp x D) :
    EltConcl 3 (TableBF4Two.torus3 K).range D := by
  obtain ⟨f, rfl⟩ := hx
  have hf : f = ![f 0, f 1, f 2] := by
    funext k
    fin_cases k <;> rfl
  by_cases hk : f 0 = 1 ∨ f 1 = 1 ∨ f 2 = 1
  · have hf1 : f 0 ≠ 1 ∨ f 1 ≠ 1 ∨ f 2 ≠ 1 := by
      by_contra hc
      push Not at hc
      obtain ⟨h0, h1, h2⟩ := hc
      refine hx1 ?_
      have h3 : f = 1 := by
        funext k
        fin_cases k
        exacts [h0, h1, h2]
      rw [h3, map_one]
    obtain ⟨w, -, hw⟩ := exists_nodeWords (f 0) (f 1) (f 2) hk hf1
    rw [← hf] at hw
    obtain ⟨α, hα⟩ : ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
        α (nodeElt K) = TableBF4Two.torus3 K f := by
      rcases hw with hw | hw
      · rw [← hw]
        exact exists_mulEquiv_torusWord exists_mulEquiv_nodeElt_eq_vecE0 w
      · rw [← hw]
        exact exists_mulEquiv_torusWord exists_mulEquiv_nodeElt_eq_vecE01 w
    obtain ⟨k, hk⟩ : ∃ k, f k = 1 := by
      rcases hk with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
    exact eltConcl_of_node hK α hα hk hD
  · rw [not_or, not_or] at hk
    obtain ⟨h0, h1, h2⟩ := hk
    obtain ⟨w, -, hw⟩ := exists_threeWords (f 0) (f 1) (f 2) h0 h1 h2
    rw [← hf] at hw
    obtain ⟨β, hβ⟩ := exists_mulEquiv_torusWord (y := TableBF4Two.torus3 K vecDelta)
      (g := vecDelta) ⟨MulEquiv.refl _, rfl⟩ w
    rw [hw] at hβ
    rw [← hβ] at hD
    have h := eltHyp_map β.symm hD
    rw [MulEquiv.symm_apply_apply] at h
    exact (not_eltHyp_vecDelta h3C _ h).elim

end Orbits

end CFSG.StandardType.SmallExc.F4Two

end
