module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.Permutation.Embedding
import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Permutation.ProperSupportMaps
open CFSG.Permutation.SymmetricCoxeter
open Equiv Equiv.Perm
open CFSG.ClassicalGroups.Orthogonal
open CFSG.Timmesfeld.ClassicalOrders
open Module QuadraticMap

section SparseSplitCharts

section PurePermutationGluing

private theorem exists_viaEmbeddingHom_of_fixing {m : ℕ}
    (i : Fin (m + 3) ↪ Fin (m + 4)) (d : Fin (m + 4))
    (hrange : ∀ x, x ∈ Set.range i ↔ x ≠ d)
    (σ : Perm (Fin (m + 4))) (hσd : σ d = d) :
    ∃ τ : Perm (Fin (m + 3)), viaEmbeddingHom i τ = σ := by
    let e : Fin (m + 3) ≃ {x : Fin (m + 4) // x ∈ Set.range i} :=
      Equiv.ofInjective (fun k => i k) i.injective
    have hiff : ∀ x, (σ x ∈ Set.range i) ↔ (x ∈ Set.range i) := by
      intro x
      rw [hrange (σ x), hrange x]
      constructor
      · intro h hx
        exact h (by rw [hx, hσd])
      · intro h hx
        exact h (σ.injective (hx.trans hσd.symm))
    let S : Perm {x : Fin (m + 4) // x ∈ Set.range i} := σ.subtypePerm hiff
    let τ : Perm (Fin (m + 3)) := e.trans (S.trans e.symm)
    refine ⟨τ, ?_⟩
    ext x
    by_cases hx : x ∈ Set.range i
    · let z : {x : Fin (m + 4) // x ∈ Set.range i} := ⟨x, hx⟩
      let k : Fin (m + 3) := e.symm z
      have hik : i k = x := by
        have h := Equiv.apply_ofInjective_symm (f := fun k => i k) i.injective z
        exact h
      have hτk : τ k = e.symm (S z) := by
        dsimp [τ, k]
        change e.symm (S (e (e.symm z))) = e.symm (S z)
        rw [e.apply_symm_apply]
      have hSz : ((S z : {x : Fin (m + 4) // x ∈ Set.range i}) : Fin (m + 4)) = σ x := by
        dsimp [S, z]
      rw [← hik, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply,
        hτk]
      have happly : i (e.symm (S z)) = (S z : Fin (m + 4)) := by
        have h := Equiv.apply_ofInjective_symm (f := fun k => i k) i.injective (S z)
        exact h
      rw [happly, hSz, hik]
    · have hx0 : x = d := by
        by_contra hne
        exact hx ((hrange x).mpr hne)
      rw [hx0]
      rw [Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem τ i d (by
          rw [hrange d]
          exact fun h => h rfl)]
      first
      | exact congrArg Fin.val hσd.symm
      | exact Fin.ext (congrArg Fin.val hσd.symm)

private theorem exists_permHom_of_point_stabilizers_with_enumeration
    {m : ℕ} {G : Type*} [Group G]
    {u v cc : Fin (m + 4)}
    (q : Perm (Fin (m + 4)))
    (hq0 : q 0 = u)
    (hq1 : q 1 = v)
    (hq2 : q ⟨m + 2, by omega⟩ = cc)
    (hqlast : q (Fin.last (m + 3)) = 0)
    (aP : MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)) →* G)
    (kP : MulAction.stabilizer (Perm (Fin (m + 4))) u →* G)
    (hOverlap : ∀ (sigma : Perm (Fin (m + 4)))
        (h0 : sigma ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)))
        (hu : sigma ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u),
      aP ⟨sigma, h0⟩ = kP ⟨sigma, hu⟩)
    (hUV : Equiv.swap u v ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)))
    (hC0 : Equiv.swap cc 0 ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u)
    (hCross : Commute (aP ⟨Equiv.swap u v, hUV⟩)
      (kP ⟨Equiv.swap cc 0, hC0⟩)) :
    ∃ t : Perm (Fin (m + 4)) →* G,
      t.comp (MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4))).subtype = aP ∧
      t.comp (MulAction.stabilizer (Perm (Fin (m + 4))) u).subtype = kP ∧
      t.range = aP.range ⊔ kP.range := by
  classical
  let iL : Fin (m + 3) ↪ Fin (m + 4) :=
    (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)).trans q.toEmbedding
  let iK : Fin (m + 3) ↪ Fin (m + 4) :=
    (Fin.succEmb (m + 3)).trans q.toEmbedding
  have hq3 : q ⟨m + 3, by omega⟩ = 0 := by
    rw [show (⟨m + 3, by omega⟩ : Fin (m + 4)) = Fin.last (m + 3) from Fin.ext rfl]
    exact hqlast
  have hrangeL : ∀ x : Fin (m + 4), x ∈ Set.range iL ↔ x ≠ 0 := by
    intro x
    constructor
    · rintro ⟨k, rfl⟩ h
      change q (Fin.castSucc k) = 0 at h
      have hk : Fin.castSucc k = Fin.last (m + 3) := by
        apply q.injective
        rw [h, hqlast]
      exact (Fin.castSucc_ne_last k) hk
    · intro hx
      have hxlast : q.symm x ≠ Fin.last (m + 3) := by
        intro h
        apply hx
        have h' := congrArg q h
        rwa [q.apply_symm_apply, hqlast] at h'
      obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hxlast
      refine ⟨k, ?_⟩
      change q (Fin.castSucc k) = x
      rw [hk, q.apply_symm_apply]
  have hrangeK : ∀ x : Fin (m + 4), x ∈ Set.range iK ↔ x ≠ u := by
    intro x
    constructor
    · rintro ⟨k, rfl⟩ h
      change q (Fin.succ k) = u at h
      have hk : Fin.succ k = 0 := by
        apply q.injective
        rw [h, hq0]
      exact (Fin.succ_ne_zero k) hk
    · intro hx
      have hx0 : q.symm x ≠ (0 : Fin (m + 4)) := by
        intro h
        apply hx
        have h' := congrArg q h
        rwa [q.apply_symm_apply, hq0] at h'
      obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hx0
      refine ⟨k, ?_⟩
      change q (Fin.succ k) = x
      rw [hk, q.apply_symm_apply]
  have hnot0 : (0 : Fin (m + 4)) ∉ Set.range iL := by
    rw [hrangeL]
    exact fun h => h rfl
  have hnotU : u ∉ Set.range iK := by
    rw [hrangeK]
    exact fun h => h rfl
  have hmemL : ∀ τ : Perm (Fin (m + 3)), viaEmbeddingHom iL τ ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)) := by
    intro τ
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
      Equiv.Perm.viaEmbeddingHom_apply]
    exact Equiv.Perm.viaEmbedding_apply_of_notMem τ iL 0 hnot0
  have hmemK : ∀ τ : Perm (Fin (m + 3)), viaEmbeddingHom iK τ ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u := by
    intro τ
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
      Equiv.Perm.viaEmbeddingHom_apply]
    exact Equiv.Perm.viaEmbedding_apply_of_notMem τ iK u hnotU
  let eL : Perm (Fin (m + 3)) →* MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)) :=
    { toFun := fun τ => ⟨viaEmbeddingHom iL τ, hmemL τ⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  let eK : Perm (Fin (m + 3)) →* MulAction.stabilizer (Perm (Fin (m + 4))) u :=
    { toFun := fun τ => ⟨viaEmbeddingHom iK τ, hmemK τ⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  let f : Perm (Fin (m + 3)) →* G := aP.comp eL
  let g : Perm (Fin (m + 3)) →* G := kP.comp eK
  have hOverlap' : f.comp (viaEmbeddingHom (Fin.succEmb (m + 2))) =
      g.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 2) ↪ Fin (m + 3))) := by
    refine MonoidHom.eq_of_eqOn_dense (s := adjSwap (m + 1) '' Set.Iio (m + 1))
      (closure_adjSwap (m + 1)) ?_
    rintro _ ⟨i, hi, rfl⟩
    simp only [MonoidHom.comp_apply]
    let τL : Perm (Fin (m + 3)) :=
      viaEmbeddingHom (Fin.succEmb (m + 2)) (adjSwap (m + 1) i)
    let τK : Perm (Fin (m + 3)) :=
      viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 2) ↪ Fin (m + 3)) (adjSwap (m + 1) i)
    change aP (eL τL) = kP (eK τK)
    have hi' : i < m + 1 := hi
    have hτL : viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τL =
        adjSwap (m + 3) (i + 1) := by
      dsimp [τL]
      rw [CFSG.Permutation.SymmetricCoxeter.viaEmbeddingHom_succEmb_adjSwap (m + 1) i hi']
      rw [CFSG.Permutation.SymmetricCoxeter.viaEmbeddingHom_castSuccEmb_adjSwap (m + 2)
        (i + 1) (by omega)]
    have hτK : viaEmbeddingHom (Fin.succEmb (m + 3)) τK =
        adjSwap (m + 3) (i + 1) := by
      dsimp [τK]
      rw [CFSG.Permutation.SymmetricCoxeter.viaEmbeddingHom_castSuccEmb_adjSwap (m + 1) i hi']
      rw [CFSG.Permutation.SymmetricCoxeter.viaEmbeddingHom_succEmb_adjSwap (m + 2) i
        (by omega)]
    have hPL : viaEmbeddingHom iL τL = q * adjSwap (m + 3) (i + 1) * q⁻¹ := by
      dsimp only [iL]
      rw [CFSG.Permutation.viaEmbeddingHom_trans_conj q (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τL,
        hτL]
    have hPK : viaEmbeddingHom iK τK = q * adjSwap (m + 3) (i + 1) * q⁻¹ := by
      dsimp only [iK]
      rw [CFSG.Permutation.viaEmbeddingHom_trans_conj q (Fin.succEmb (m + 3)) τK, hτK]
    let Pconj : Perm (Fin (m + 4)) := q * adjSwap (m + 3) (i + 1) * q⁻¹
    have h0 : Pconj ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)) := by
      rw [show Pconj = viaEmbeddingHom iL τL from hPL.symm]
      exact hmemL τL
    have hu : Pconj ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u := by
      rw [show Pconj = viaEmbeddingHom iK τK from hPK.symm]
      exact hmemK τK
    have h := hOverlap Pconj h0 hu
    have hsubL : (⟨Pconj, h0⟩ : MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4))) = eL τL := Subtype.ext hPL.symm
    have hsubK : (⟨Pconj, hu⟩ : MulAction.stabilizer (Perm (Fin (m + 4))) u) = eK τK := Subtype.ext hPK.symm
    rw [hsubL, hsubK] at h
    exact h
  have heLswap : eL (adjSwap (m + 2) 0) = ⟨Equiv.swap u v, hUV⟩ := by
    apply Subtype.ext
    change viaEmbeddingHom iL (adjSwap (m + 2) 0) = Equiv.swap u v
    rw [adjSwap_of_lt (show 0 < m + 2 by omega)]
    rw [CFSG.Permutation.viaEmbeddingHom_swap]
    simp [iL, Fin.castSucc_mk, hq0, hq1]
  have heKswap : eK (adjSwap (m + 2) (m + 1)) = ⟨Equiv.swap cc 0, hC0⟩ := by
    apply Subtype.ext
    change viaEmbeddingHom iK (adjSwap (m + 2) (m + 1)) = Equiv.swap cc 0
    rw [adjSwap_of_lt (show m + 1 < m + 2 by omega)]
    rw [CFSG.Permutation.viaEmbeddingHom_swap]
    simp [iK, Fin.succ_mk, hq2, hq3]
  have hCross' : Commute (f (adjSwap (m + 2) 0)) (g (adjSwap (m + 2) (m + 1))) := by
    change Commute (aP (eL (adjSwap (m + 2) 0)))
      (kP (eK (adjSwap (m + 2) (m + 1))))
    rw [heLswap, heKswap]
    exact hCross
  obtain ⟨F0, hF0L, hF0K⟩ :=
    CFSG.Permutation.SymmetricCoxeter.exists_hom_perm_of_overlap m f g hOverlap' hCross'
  let t : Perm (Fin (m + 4)) →* G := F0.comp (MulAut.conj q⁻¹).toMonoidHom
  have hEmbdL : ∀ τ : Perm (Fin (m + 3)),
      t (viaEmbeddingHom iL τ) = aP (eL τ) := by
    intro τ
    have ht : t (viaEmbeddingHom iL τ) =
        F0 (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τ) := by
      change F0 ((MulAut.conj q⁻¹) (viaEmbeddingHom iL τ)) =
        F0 (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τ)
      dsimp only [iL]
      rw [CFSG.Permutation.viaEmbeddingHom_trans_conj q (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τ]
      congr 1
      simp only [MulAut.conj_apply]
      group
    have hf : F0 (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τ) =
        f τ := by
      have h := congrArg (fun φ : Perm (Fin (m + 3)) →* G => φ τ) hF0L
      simpa using h
    calc
      t (viaEmbeddingHom iL τ) =
          F0 (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) τ) := ht
      _ = f τ := hf
      _ = aP (eL τ) := rfl
  have hEmbdK : ∀ τ : Perm (Fin (m + 3)),
      t (viaEmbeddingHom iK τ) = kP (eK τ) := by
    intro τ
    have ht : t (viaEmbeddingHom iK τ) =
        F0 (viaEmbeddingHom (Fin.succEmb (m + 3)) τ) := by
      change F0 ((MulAut.conj q⁻¹) (viaEmbeddingHom iK τ)) =
        F0 (viaEmbeddingHom (Fin.succEmb (m + 3)) τ)
      dsimp only [iK]
      rw [CFSG.Permutation.viaEmbeddingHom_trans_conj q (Fin.succEmb (m + 3)) τ]
      congr 1
      simp only [MulAut.conj_apply]
      group
    have hg : F0 (viaEmbeddingHom (Fin.succEmb (m + 3)) τ) = g τ := by
      have h := congrArg (fun φ : Perm (Fin (m + 3)) →* G => φ τ) hF0K
      simpa using h
    calc
      t (viaEmbeddingHom iK τ) = F0 (viaEmbeddingHom (Fin.succEmb (m + 3)) τ) := ht
      _ = g τ := hg
      _ = kP (eK τ) := rfl
  have hRestrL : t.comp (MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4))).subtype = aP := by
    ext sigma
    have hsigma : (sigma : Perm (Fin (m + 4))) 0 = 0 := by
      have h := sigma.2
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
      exact h
    obtain ⟨τ, hτ⟩ := exists_viaEmbeddingHom_of_fixing iL 0 hrangeL
      (sigma : Perm (Fin (m + 4))) hsigma
    have hsigmaCoe : (sigma : Perm (Fin (m + 4))) = viaEmbeddingHom iL τ := hτ.symm
    have hsigmaEq : sigma = eL τ := Subtype.ext hτ.symm
    change t (sigma : Perm (Fin (m + 4))) = aP sigma
    rw [hsigmaCoe, hsigmaEq]
    exact hEmbdL τ
  have hRestrK : t.comp (MulAction.stabilizer (Perm (Fin (m + 4))) u).subtype = kP := by
    ext sigma
    have hsigma : (sigma : Perm (Fin (m + 4))) u = u := by
      have h := sigma.2
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
      exact h
    obtain ⟨τ, hτ⟩ := exists_viaEmbeddingHom_of_fixing iK u hrangeK
      (sigma : Perm (Fin (m + 4))) hsigma
    have hsigmaCoe : (sigma : Perm (Fin (m + 4))) = viaEmbeddingHom iK τ := hτ.symm
    have hsigmaEq : sigma = eK τ := Subtype.ext hτ.symm
    change t (sigma : Perm (Fin (m + 4))) = kP sigma
    rw [hsigmaCoe, hsigmaEq]
    exact hEmbdK τ
  have ht_range : t.range = F0.range := by
    dsimp [t]
    rw [MonoidHom.range_comp,
      show (↑(MulAut.conj q⁻¹) : Perm (Fin (m + 4)) →* Perm (Fin (m + 4))).range = ⊤ from
        MonoidHom.range_eq_top.mpr (MulAut.conj q⁻¹).surjective]
    exact (MonoidHom.range_eq_map F0).symm
  have hfrange : f.range ≤ aP.range := by
    rintro y ⟨τ, rfl⟩
    exact ⟨eL τ, rfl⟩
  have hgrange : g.range ≤ kP.range := by
    rintro y ⟨τ, rfl⟩
    exact ⟨eK τ, rfl⟩
  have ht_le : t.range ≤ aP.range ⊔ kP.range := by
    calc
      t.range = F0.range := ht_range
      _ = f.range ⊔ g.range :=
        CFSG.Permutation.SymmetricCoxeter.range_eq_sup hF0L hF0K
      _ ≤ aP.range ⊔ kP.range := sup_le_sup hfrange hgrange
  have hle_rev : aP.range ⊔ kP.range ≤ t.range := by
    apply sup_le
    · rintro y ⟨x, rfl⟩
      exact ⟨(x : Perm (Fin (m + 4))), DFunLike.congr_fun hRestrL x⟩
    · rintro y ⟨x, rfl⟩
      exact ⟨(x : Perm (Fin (m + 4))), DFunLike.congr_fun hRestrK x⟩
  exact ⟨t, hRestrL, hRestrK, le_antisymm ht_le hle_rev⟩

theorem exists_permHom_of_point_stabilizers
    {m : ℕ} {G : Type*} [Group G]
    {u v cc : Fin (m + 4)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (m + 4)) ≠ u)
    (h0v : (0 : Fin (m + 4)) ≠ v) (hcc0 : cc ≠ 0)
    (aP : MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)) →* G)
    (kP : MulAction.stabilizer (Perm (Fin (m + 4))) u →* G)
    (hOverlap : ∀ (sigma : Perm (Fin (m + 4)))
        (h0 : sigma ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)))
        (hu : sigma ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u),
      aP ⟨sigma, h0⟩ = kP ⟨sigma, hu⟩)
    (hCross : ∀ (hUV : Equiv.swap u v ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)))
        (hC0 : Equiv.swap cc 0 ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u),
      Commute (aP ⟨Equiv.swap u v, hUV⟩)
        (kP ⟨Equiv.swap cc 0, hC0⟩)) :
    ∃ t : Perm (Fin (m + 4)) →* G,
      t.comp (MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4))).subtype = aP ∧
      t.comp (MulAction.stabilizer (Perm (Fin (m + 4))) u).subtype = kP ∧
      t.range = aP.range ⊔ kP.range := by
  classical
  let std : Fin 4 → Fin (m + 4) :=
    ![0, 1, ⟨m + 2, by omega⟩, ⟨m + 3, by omega⟩]
  let lab : Fin 4 → Fin (m + 4) := ![u, v, cc, 0]
  have hstd : Function.Injective std := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [std] at h ⊢ <;>
      omega
  have hlab : Function.Injective lab := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [lab, huv, hcu, hcv, h0u, h0v, hcc0,
        huv.symm, hcu.symm, hcv.symm, h0u.symm, h0v.symm, hcc0.symm] at h ⊢
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair std lab hstd hlab
  have hq0 : q 0 = u := by simpa [std, lab] using hq 0
  have hq1 : q 1 = v := by simpa [std, lab] using hq 1
  have hq2 : q ⟨m + 2, by omega⟩ = cc := by simpa [std, lab] using hq 2
  have hq3 : q ⟨m + 3, by omega⟩ = 0 := by simpa [std, lab] using hq 3
  have hqlast : q (Fin.last (m + 3)) = 0 := by
    rw [show Fin.last (m + 3) = (⟨m + 3, by omega⟩ : Fin (m + 4)) from Fin.ext rfl]
    exact hq3
  have hUV : Equiv.swap u v ∈ MulAction.stabilizer (Perm (Fin (m + 4))) (0 : Fin (m + 4)) := by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact Equiv.swap_apply_of_ne_of_ne h0u h0v
  have hC0 : Equiv.swap cc 0 ∈ MulAction.stabilizer (Perm (Fin (m + 4))) u := by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact Equiv.swap_apply_of_ne_of_ne hcu.symm h0u.symm
  exact exists_permHom_of_point_stabilizers_with_enumeration q hq0 hq1 hq2 hqlast
    aP kP hOverlap hUV hC0 (hCross hUV hC0)

end PurePermutationGluing

variable {G F : Type} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2]
  {r p : ℕ} {b c : F}

local notation "I" => Fin (r + 1)
local notation "C" =>
  (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c))
local notation "D0" => (deletionPlanes r)

private theorem sparse_native_supported_commute
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {cc d u v : I}
    (hcd : cc ≠ d) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (hdu : d ≠ u) (hdv : d ≠ v) (huv : u ≠ v)
    {g h : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F}
    (hg : g ∈ supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) ({cc, d} : Finset I)))
    (hh : h ∈ supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) ({u, v} : Finset I)))
    (hg2 : g ^ 2 = 1)
    (hcomm : ∀ s ∈ supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)), Commute g s) :
    Commute g h := by
  classical
  let Q : QuadraticForm F (Vm (r + 2) F) := quadMinus (r + 2) F b c
  let ψ : Vm (r + 2) F ≃ₗ[F] (Fin 2 → F) × (I → F × F) :=
    minusPlaneCoordinates (n := r + 2) (F := F)
  let W : Submodule F (Vm (r + 2) F) := coordAnchor ψ
  let U : I → Submodule F (Vm (r + 2) F) := fun i => coordPlane ψ i
  let A : Submodule F (Vm (r + 2) F) := ({cc, d} : Finset I).sup U
  let B : Submodule F (Vm (r + 2) F) := ({u, v} : Finset I).sup U
  have hψ : ∀ v : Vm (r + 2) F,
      Q v = binaryForm F b c (ψ v).1 + ∑ i, hypPlane F ((ψ v).2 i) := by
    intro v
    exact quadMinus_eq_binaryForm_add_minusPlaneCoordinates r v
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (r + 2) F hirr
  have hQE : (polarBilin (hypPlane F)).Nondegenerate := hypPlane_polarBilin_nondegenerate
  have hWreg : (polarBilin (Q.comp W.subtype)).Nondegenerate :=
    coordAnchor_nondegenerate ψ hψ hQ hQE
  have hWdim : finrank F W = 2 := by
    have hinj : Function.Injective
        (ψ.symm.toLinearMap.comp (LinearMap.inl F (Fin 2 → F) (I → F × F))) :=
      ψ.symm.injective.comp LinearMap.inl_injective
    have hdim : finrank F W = finrank F (Fin 2 → F) := by
      dsimp [W, coordAnchor]
      exact LinearMap.finrank_range_of_inj hinj
    rw [hdim, Module.finrank_fintype_fun_eq_card]
    simp
  have hWaniso : ∀ w ∈ W, Q w = 0 → w = 0 := by
    intro w hw hQw
    obtain ⟨ρ, rfl⟩ := mem_coordAnchor.mp hw
    have hQeq : Q (ψ.symm (ρ, 0)) = binaryForm F b c ρ := by
      have h := quadMinus_eq_binaryForm_add_minusPlaneCoordinates (r := r) (F := F) (b := b)
        (c := c) (ψ.symm (ρ, 0))
      simpa [ψ, hypPlane_apply] using h
    have hzero : binaryForm F b c ρ = 0 := by
      rw [← hQeq]
      exact hQw
    have hparts : ρ 0 = 0 ∧ ρ 1 = 0 :=
      binary_eq_zero_of_irreducible (b := b) (c := c) (u := ρ 0) (v := ρ 1) hirr
        (by simpa [binaryForm_apply] using hzero)
    have hρ : ρ = 0 := by
      funext t
      fin_cases t <;> simp [hparts.1, hparts.2]
    rw [hρ]
    simp
  have hUreg : ∀ i : I, PolarNondegOn Q (U i) := fun i =>
    coordPlane_polarNondegOn ψ hψ hQE i
  have hUorth : ∀ i j : I, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, polar Q x y = 0 :=
    fun i j hij x hx y hy => polar_coordPlane_plane ψ hψ hij hx hy
  have hAreg : (polarBilin (Q.comp A.subtype)).Nondegenerate :=
    nondegenerate_finset_sup U hUreg hUorth ({cc, d} : Finset I)
  have hBreg : (polarBilin (Q.comp B.subtype)).Nondegenerate :=
    nondegenerate_finset_sup U hUreg hUorth ({u, v} : Finset I)
  have hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0 := by
    intro w hw a ha
    exact polar_coordAnchor_active ψ hψ hw
      (Finset.sup_le (fun i _ => le_iSup (fun i => U i) i) ha)
  have hWB : ∀ w ∈ W, ∀ b ∈ B, polar Q w b = 0 := by
    intro w hw b hb
    exact polar_coordAnchor_active ψ hψ hw
      (Finset.sup_le (fun i _ => le_iSup (fun i => U i) i) hb)
  have hdisjUV : Disjoint ({cc, d} : Finset I) ({u, v} : Finset I) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hcu rfl
    · exact hcv rfl
    · exact hdu rfl
    · exact hdv rfl
  have hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0 := by
    intro a ha b hb
    exact polar_eq_zero_of_mem_finset_sup_disjoint U hUorth hdisjUV ha hb
  have hWAsupp : anchoredSupport F (r + 2) ({cc, d} : Finset I) = W ⊔ A := by
    rw [← coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := r + 2) (F := F)
      ({cc, d} : Finset I)]
    rfl
  have hWBsupp : anchoredSupport F (r + 2) ({u, v} : Finset I) = W ⊔ B := by
    rw [← coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := r + 2) (F := F)
      ({u, v} : Finset I)]
    rfl
  have hWempty : W = anchoredSupport F (r + 2) (∅ : Finset I) := by
    dsimp [W, ψ]
    exact coordAnchor_minusPlaneCoordinates
  have hcommW : ∀ s ∈ supportedDerived Q W, Commute g s := by
    intro s hs
    exact hcomm s (by rwa [hWempty] at hs)
  have hgsupp : g ∈ supportedDerived Q (W ⊔ A) := by
    rw [← hWAsupp]
    exact hg
  have hhsupp : h ∈ supportedDerived Q (W ⊔ B) := by
    rw [← hWBsupp]
    exact hh
  exact supportedDerived_commute_of_anisotropic_anchor_involution
    (Q := Q) (W := W) (A := A) (B := B)
    hWreg hWdim hWaniso hAreg hBreg hWA hWB hAB hgsupp hhsupp hg2 hcommW

private theorem sparse_swap_images
    {cc d u v : I}
    (hdc : d ≠ cc) (hdu : d ≠ u) (hdv : d ≠ v)
    (hcc0 : cc ≠ 0) (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) :
    (Equiv.swap (0 : I) d) '' ((({cc, 0} : Finset I) : Set I)) =
      (({cc, d} : Finset I) : Set I) ∧
    (Equiv.swap (0 : I) d) '' ((({u, v} : Finset I) : Set I)) =
      (({u, v} : Finset I) : Set I) ∧
    (Equiv.swap (0 : I) d) '' ((({v} : Finset I) : Set I)) =
      (({v} : Finset I) : Set I) ∧
    (Equiv.swap (0 : I) d) '' ((({cc} : Finset I) : Set I)) =
      (({cc} : Finset I) : Set I) := by
  classical
  let S0 : Finset I := {cc, 0}
  let Sv : Finset I := {v}
  let Scc : Finset I := {cc}
  let Suv : Finset I := {u, v}
  let Scd : Finset I := {cc, d}
  have hS0set : ((S0 : Finset I) : Set I) = ({cc, 0} : Set I) := by
    ext x
    simp [S0]
  have hScdset : ((Scd : Finset I) : Set I) = ({cc, d} : Set I) := by
    ext x
    simp [Scd]
  have hSuvset : ((Suv : Finset I) : Set I) = ({u, v} : Set I) := by
    ext x
    simp [Suv]
  have hSvset : ((Sv : Finset I) : Set I) = ({v} : Set I) := by
    ext x
    simp [Sv]
  have hSccset : ((Scc : Finset I) : Set I) = ({cc} : Set I) := by
    ext x
    simp [Scc]
  have hswap0 : (Equiv.swap (0 : I) d) '' (((S0 : Finset I) : Set I)) =
      ((Scd : Finset I) : Set I) := by
    rw [hS0set, hScdset]
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, (rfl | rfl), rfl⟩
      · left
        exact Equiv.swap_apply_of_ne_of_ne hcc0 hdc.symm
      · right
        exact Equiv.swap_apply_left (0 : I) d
    · intro hx
      rcases hx with hx | hx
      · refine ⟨cc, Or.inl rfl, ?_⟩
        rw [hx]
        exact Equiv.swap_apply_of_ne_of_ne hcc0 hdc.symm
      · refine ⟨0, Or.inr rfl, ?_⟩
        rw [hx]
        exact Equiv.swap_apply_left (0 : I) d
  have hswapUV : (Equiv.swap (0 : I) d) '' (((Suv : Finset I) : Set I)) =
      ((Suv : Finset I) : Set I) := by
    rw [hSuvset]
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, (rfl | rfl), rfl⟩
      · left
        exact Equiv.swap_apply_of_ne_of_ne h0u.symm hdu.symm
      · right
        exact Equiv.swap_apply_of_ne_of_ne h0v.symm hdv.symm
    · intro hx
      rcases hx with hx | hx
      · refine ⟨u, Or.inl rfl, ?_⟩
        rw [hx]
        exact Equiv.swap_apply_of_ne_of_ne h0u.symm hdu.symm
      · refine ⟨v, Or.inr rfl, ?_⟩
        rw [hx]
        exact Equiv.swap_apply_of_ne_of_ne h0v.symm hdv.symm
  have hswapV : (Equiv.swap (0 : I) d) '' (((Sv : Finset I) : Set I)) =
      ((Sv : Finset I) : Set I) := by
    rw [hSvset]
    ext x
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl, rfl⟩
      exact Equiv.swap_apply_of_ne_of_ne h0v.symm hdv.symm
    · intro hx
      rw [hx]
      exact ⟨v, rfl, Equiv.swap_apply_of_ne_of_ne h0v.symm hdv.symm⟩
  have hswapCC : (Equiv.swap (0 : I) d) '' (((Scc : Finset I) : Set I)) =
      ((Scc : Finset I) : Set I) := by
    rw [hSccset]
    ext x
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl, rfl⟩
      exact Equiv.swap_apply_of_ne_of_ne hcc0 hdc.symm
    · intro hx
      rw [hx]
      exact ⟨cc, rfl, Equiv.swap_apply_of_ne_of_ne hcc0 hdc.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [S0, Scd] using hswap0
  · simpa [Suv] using hswapUV
  · simpa [Sv] using hswapV
  · simpa [Scc] using hswapCC

private theorem sparse_block0
    (Bs : Subgroup G) (eta : Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) {cc d u v : I}
    (hdc : d ≠ cc) (hdu : d ≠ u) (hdv : d ≠ v)
    (hcc0 : cc ≠ 0) (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v)
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgτ : MulAut.congr eta (ggConjAut Bs hgN) =
      SpCoord.permAut (ell * Equiv.swap (0 : I) d * ell⁻¹)) :
    (ggBlockComm Bs eta (ell '' (({cc, 0} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({cc, d} : Finset I) : Set I)) := by
  obtain ⟨hswap, -, -, -⟩ :=
    sparse_swap_images (d := d) hdc hdu hdv hcc0 h0u h0v
  have h := ggBlockComm_image_map_conj (Bs := Bs) (eta := eta) (p := p) (n := r + 1)
    (π := ell) (g := g) hgN (ρ := Equiv.swap (0 : I) d) hgτ
    ((({cc, 0} : Finset I) : Set I))
  rw [hswap] at h
  exact h

private theorem sparse_blockUV
    (Bs : Subgroup G) (eta : Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) {cc d u v : I}
    (hdc : d ≠ cc) (hdu : d ≠ u) (hdv : d ≠ v)
    (hcc0 : cc ≠ 0) (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v)
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgτ : MulAut.congr eta (ggConjAut Bs hgN) =
      SpCoord.permAut (ell * Equiv.swap (0 : I) d * ell⁻¹)) :
    (ggBlockComm Bs eta (ell '' (({u, v} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({u, v} : Finset I) : Set I)) := by
  obtain ⟨-, hswap, -, -⟩ :=
    sparse_swap_images (d := d) hdc hdu hdv hcc0 h0u h0v
  have h := ggBlockComm_image_map_conj (Bs := Bs) (eta := eta) (p := p) (n := r + 1)
    (π := ell) (g := g) hgN (ρ := Equiv.swap (0 : I) d) hgτ
    ((({u, v} : Finset I) : Set I))
  rw [hswap] at h
  exact h

private theorem sparse_blockV
    (Bs : Subgroup G) (eta : Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) {cc d u v : I}
    (hdc : d ≠ cc) (hdu : d ≠ u) (hdv : d ≠ v)
    (hcc0 : cc ≠ 0) (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v)
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgτ : MulAut.congr eta (ggConjAut Bs hgN) =
      SpCoord.permAut (ell * Equiv.swap (0 : I) d * ell⁻¹)) :
    (ggBlockComm Bs eta (ell '' (({v} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({v} : Finset I) : Set I)) := by
  obtain ⟨-, -, hswap, -⟩ :=
    sparse_swap_images (d := d) hdc hdu hdv hcc0 h0u h0v
  have h := ggBlockComm_image_map_conj (Bs := Bs) (eta := eta) (p := p) (n := r + 1)
    (π := ell) (g := g) hgN (ρ := Equiv.swap (0 : I) d) hgτ
    ((({v} : Finset I) : Set I))
  rw [hswap] at h
  exact h

private theorem sparse_blockCC
    (Bs : Subgroup G) (eta : Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) {cc d u v : I}
    (hdc : d ≠ cc) (hdu : d ≠ u) (hdv : d ≠ v)
    (hcc0 : cc ≠ 0) (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v)
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgτ : MulAut.congr eta (ggConjAut Bs hgN) =
      SpCoord.permAut (ell * Equiv.swap (0 : I) d * ell⁻¹)) :
    (ggBlockComm Bs eta (ell '' (({cc} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({cc} : Finset I) : Set I)) := by
  obtain ⟨-, -, -, hswap⟩ :=
    sparse_swap_images (d := d) hdc hdu hdv hcc0 h0u h0v
  have h := ggBlockComm_image_map_conj (Bs := Bs) (eta := eta) (p := p) (n := r + 1)
    (π := ell) (g := g) hgN (ρ := Equiv.swap (0 : I) d) hgτ
    ((({cc} : Finset I) : Set I))
  rw [hswap] at h
  exact h

private theorem sparse_blockA0
    (Bs : Subgroup G) (eta : Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) {cc v : I} {g : G}
    (hMv : (ggBlockComm Bs eta (ell '' (({v} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({v} : Finset I) : Set I)))
    (hMcc : (ggBlockComm Bs eta (ell '' (({cc} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({cc} : Finset I) : Set I))) :
    ((ggBlockComm Bs eta (ell '' (({v} : Finset I) : Set I))) ⊓
      ggBlockComm Bs eta (ell '' (({cc} : Finset I) : Set I))).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (ell '' (({v} : Finset I) : Set I)) ⊓
        ggBlockComm Bs eta (ell '' (({cc} : Finset I) : Set I)) := by
  rw [Subgroup.map_inf_eq _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    hMv, hMcc]

private theorem sparse_anchored_regular
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : Finset I) :
    (polarBilin ((quadMinus (r + 2) F b c).comp
      (anchoredSupport F (r + 2) S).subtype)).Nondegenerate := by
  have hW : PolarNondegOn (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) S) :=
    polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr S
  exact CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
    (Q := quadMinus (r + 2) F b c) (U := anchoredSupport F (r + 2) S)
    (fun x hx h => hW x hx h)

private theorem sparse_anchor_le_orth
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)) ≤
      orthDerived (quadMinus (r + 2) F b c) :=
  supportedDerived_le_orthDerived_of_regular
    (sparse_anchored_regular (r := r) (F := F) (b := b) (c := c) hirr ∅)

private theorem sparse_anchor_le
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {S : Finset I}
    (hS : anchoredSupport F (r + 2) (∅ : Finset I) ≤ anchoredSupport F (r + 2) S) :
    supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)) ≤
      supportedDerived (quadMinus (r + 2) F b c) (anchoredSupport F (r + 2) S) :=
  supportedDerived_le_supportedDerived_of_le hS
    (sparse_anchored_regular (r := r) (F := F) (b := b) (c := c) hirr ∅)
    (sparse_anchored_regular (r := r) (F := F) (b := b) (c := c) hirr S)

private theorem sparse_anchor_phi
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ φ : supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (∅ : Finset I)) → C D0,
      ∀ s : supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (∅ : Finset I)), (φ s).1.1 = s.1 := by
  classical
  let Q : QuadraticForm F (Vm (r + 2) F) := quadMinus (r + 2) F b c
  let X : Subgroup (Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) := orthDerived Q
  have hWorth : supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)) ≤ X :=
    sparse_anchor_le_orth (r := r) (F := F) (b := b) (c := c) hirr
  have hAnchorD0 : supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)) ≤
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) D0) :=
    sparse_anchor_le (r := r) (F := F) (b := b) (c := c) hirr
      (anchoredSupport_mono (Finset.empty_subset D0))
  refine ⟨fun s => (⟨(⟨s.1, hWorth s.2⟩ : X), hAnchorD0 s.2⟩ : C D0), ?_⟩
  intro s
  rfl

private theorem sparse_anchor_phiA
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {v cc : I} (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (a : C D0 →* G)
    (M : Finset I → Subgroup G)
    (hmarkM : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a = M S)
    {A0 : Subgroup G}
    (hA0def : A0 = M ({v} : Finset I) ⊓ M ({cc} : Finset I))
    {φ : supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (∅ : Finset I)) → C D0}
    (hφ : ∀ s : supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (∅ : Finset I)), (φ s).1.1 = s.1) :
    ∀ s, a (φ s) ∈ A0 := by
  classical
  let Q : QuadraticForm F (Vm (r + 2) F) := quadMinus (r + 2) F b c
  let X : Subgroup (Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) := orthDerived Q
  let Sv : Finset I := {v}
  let Scc : Finset I := {cc}
  have hSvne : Sv.Nonempty := ⟨v, by simp [Sv]⟩
  have hSvcard : Sv.card ≤ 2 := by simp [Sv]
  have hSvD : Sv ⊆ D0 := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    simp [deletionPlanes, h0v.symm]
  have hSccne : Scc.Nonempty := ⟨cc, by simp [Scc]⟩
  have hScccard : Scc.card ≤ 2 := by simp [Scc]
  have hSccD : Scc ⊆ D0 := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    simp [deletionPlanes, hcc0]
  have hmemM : ∀ (S : Finset I), S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ∀ {x : C D0}, x ∈ (C S).subgroupOf (C D0) → a x ∈ M S := by
    intro S hSne hScard hSD x hx
    have hmap := hmarkM S hSne hScard hSD
    rw [← hmap]
    exact Subgroup.mem_map_of_mem a hx
  have hAnchorSv : supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)) ≤
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) Sv) :=
    sparse_anchor_le (r := r) (F := F) (b := b) (c := c) hirr
      (anchoredSupport_mono (Finset.empty_subset Sv))
  have hAnchorScc : supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)) ≤
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) Scc) :=
    sparse_anchor_le (r := r) (F := F) (b := b) (c := c) hirr
      (anchoredSupport_mono (Finset.empty_subset Scc))
  intro s
  have hsSv : φ s ∈ (C Sv).subgroupOf (C D0) := by
    change (φ s).1.1 ∈ supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) Sv)
    rw [hφ s]
    exact hAnchorSv s.2
  have hsScc : φ s ∈ (C Scc).subgroupOf (C D0) := by
    change (φ s).1.1 ∈ supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) Scc)
    rw [hφ s]
    exact hAnchorScc s.2
  rw [hA0def]
  exact ⟨hmemM Sv hSvne hSvcard hSvD hsSv,
    hmemM Scc hSccne hScccard hSccD hsScc⟩

private theorem sparse_anchor_centralizer
    (a : C D0 →* G) (ha : Function.Injective a)
    {xdom : C D0} {z' : G} {A0 : Subgroup G}
    (hxdom : a xdom = z')
    (hz'A : ∀ y ∈ A0, Commute z' y)
    {φ : supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (∅ : Finset I)) → C D0}
    (hφ : ∀ s : supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (∅ : Finset I)), (φ s).1.1 = s.1)
    (hφA : ∀ s, a (φ s) ∈ A0) :
    ∀ s ∈ supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (∅ : Finset I)),
      Commute ((xdom : orthDerived (quadMinus (r + 2) F b c)) :
        Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) s := by
  classical
  let Q : QuadraticForm F (Vm (r + 2) F) := quadMinus (r + 2) F b c
  let X : Subgroup (Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) := orthDerived Q
  intro s hs
  let sdom : C D0 := φ ⟨s, hs⟩
  have hsA0 : a sdom ∈ A0 := hφA ⟨s, hs⟩
  have hcommIm : Commute z' (a sdom) := hz'A (a sdom) hsA0
  have hxcomm : Commute xdom sdom := by
    apply ha
    rw [map_mul, map_mul, hxdom]
    exact hcommIm
  have h := congrArg (fun t : C D0 =>
    ((t : X) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)) hxcomm
  have hsdom : (sdom : C D0).1.1 = s := by
    simpa using hφ ⟨s, hs⟩
  rw [commute_iff_eq]
  simpa [hsdom] using h

private theorem sparse_marked_transport
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {u v cc d : I}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (hd0 : d ≠ 0) (hdu : d ≠ u) (hdv : d ≠ v) (hdc : d ≠ cc)
    (a : C D0 →* G) (ha : Function.Injective a)
    (M : Finset I → Subgroup G)
    (hmarkM : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a = M S)
    {g z z' : G} {A0 : Subgroup G}
    (hM0 : (M ({cc, 0} : Finset I)).map (MulAut.conj g).toMonoidHom =
      M ({cc, d} : Finset I))
    (hMuv : (M ({u, v} : Finset I)).map (MulAut.conj g).toMonoidHom =
      M ({u, v} : Finset I))
    (hz' : z' = MulAut.conj g z)
    (hz'M : z' ∈ M ({cc, d} : Finset I))
    (hz'2 : z' ^ 2 = 1)
    (hz'A : ∀ y ∈ A0, Commute z' y)
    (hA0def : A0 = M ({v} : Finset I) ⊓ M ({cc} : Finset I)) :
    ∀ y ∈ M ({u, v} : Finset I), Commute z y := by
  classical
  let S0 : Finset I := {cc, 0}
  let Sv : Finset I := {v}
  let Scc : Finset I := {cc}
  let Suv : Finset I := {u, v}
  let Scd : Finset I := {cc, d}
  let Q : QuadraticForm F (Vm (r + 2) F) := quadMinus (r + 2) F b c
  let X : Subgroup (Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) := orthDerived Q
  have hSvne : Sv.Nonempty := ⟨v, by simp [Sv]⟩
  have hSvcard : Sv.card ≤ 2 := by simp [Sv]
  have hSvD : Sv ⊆ D0 := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    simp [deletionPlanes, h0v.symm]
  have hSccne : Scc.Nonempty := ⟨cc, by simp [Scc]⟩
  have hScccard : Scc.card ≤ 2 := by simp [Scc]
  have hSccD : Scc ⊆ D0 := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    simp [deletionPlanes, hcc0]
  have hSuvne : Suv.Nonempty := ⟨u, by simp [Suv]⟩
  have hSuvcard : Suv.card ≤ 2 := by
    have h : Suv.card = 2 := by simpa [Suv] using Finset.card_pair huv
    omega
  have hSuvD : Suv ⊆ D0 := by
    intro x hx
    simp only [Suv, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [deletionPlanes, h0u.symm]
    · simp [deletionPlanes, h0v.symm]
  have hScdne : Scd.Nonempty := ⟨cc, by simp [Scd]⟩
  have hScdcard : Scd.card ≤ 2 := by
    have h : Scd.card = 2 := by simpa [Scd] using Finset.card_pair hdc.symm
    omega
  have hScdD : Scd ⊆ D0 := by
    intro x hx
    simp only [Scd, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [deletionPlanes, hcc0]
    · simp [deletionPlanes, hd0]
  have hpre : ∀ (S : Finset I), S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ∀ {y : G}, y ∈ M S →
        ∃ x : C D0, x ∈ (C S).subgroupOf (C D0) ∧ a x = y := by
    intro S hSne hScard hSD y hy
    have hmap := hmarkM S hSne hScard hSD
    rw [← hmap] at hy
    exact Subgroup.mem_map.mp hy
  have hmemM : ∀ (S : Finset I), S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ∀ {x : C D0}, x ∈ (C S).subgroupOf (C D0) → a x ∈ M S := by
    intro S hSne hScard hSD x hx
    have hmap := hmarkM S hSne hScard hSD
    rw [← hmap]
    exact Subgroup.mem_map_of_mem a hx
  obtain ⟨xdom, hxdomS, hxdom⟩ := hpre Scd hScdne hScdcard hScdD hz'M
  let gN : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F := ((xdom : X) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)
  have hgNsupp : gN ∈ supportedDerived Q (anchoredSupport F (r + 2) Scd) := by
    have hxS : (xdom : X) ∈ C Scd := Subgroup.mem_subgroupOf.mp hxdomS
    exact Subgroup.mem_subgroupOf.mp hxS
  have hgN2 : gN ^ 2 = 1 := by
    have hx2 : xdom ^ 2 = 1 := by
      apply ha
      rw [map_pow, hxdom, hz'2, map_one]
    have h := congrArg (fun t : C D0 =>
      ((t : X) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)) hx2
    simpa [gN] using h
  obtain ⟨φ, hφ⟩ := sparse_anchor_phi (r := r) (F := F) (b := b) (c := c) hirr
  have hφA : ∀ s, a (φ s) ∈ A0 :=
    sparse_anchor_phiA (r := r) (F := F) (b := b) (c := c)
      hirr h0v hcc0 a M hmarkM hA0def hφ
  have hcommW : ∀ s ∈ supportedDerived Q (anchoredSupport F (r + 2) (∅ : Finset I)),
      Commute gN s := by
    intro s hs
    exact sparse_anchor_centralizer (r := r) (F := F) (b := b) (c := c)
      (a := a) (ha := ha) (xdom := xdom) (z' := z') (A0 := A0) (φ := φ)
      hxdom hz'A hφ hφA s hs
  have hcross : ∀ h : G, h ∈ M Suv → Commute z' h := by
    intro h hM
    obtain ⟨ydom, hydomS, hydom⟩ := hpre Suv hSuvne hSuvcard hSuvD hM
    let yNat : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F :=
      ((ydom : X) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)
    have hyS : (ydom : X) ∈ C Suv := Subgroup.mem_subgroupOf.mp hydomS
    have hyraw : yNat ∈ supportedDerived Q (anchoredSupport F (r + 2) Suv) :=
      Subgroup.mem_subgroupOf.mp hyS
    have hnative : Commute gN yNat :=
      sparse_native_supported_commute (r := r) (F := F) (b := b) (c := c)
        hirr hdc.symm hcu hcv hdu hdv huv
        (by simpa [gN, Scd] using hgNsupp) (by simpa [yNat, Suv] using hyraw)
        hgN2 hcommW
    have hxydom : xdom * ydom = ydom * xdom := by
      apply Subtype.ext
      apply Subtype.ext
      exact hnative
    have hcomm := congrArg a hxydom
    rw [commute_iff_eq]
    simpa only [map_mul, hxdom, hydom] using hcomm
  have hfinal : ∀ y ∈ M Suv, Commute z y := by
    intro y hy
    have hy' : MulAut.conj g y ∈ M Suv := by
      rw [← show (M Suv).map (MulAut.conj g).toMonoidHom = M Suv from by
        simpa [Suv] using hMuv]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
    have hcomm := (hcross (MulAut.conj g y) hy').map (MulAut.conj g⁻¹)
    have hz_inv : (MulAut.conj g⁻¹) z' = z := by
      rw [hz']
      simp only [MulAut.conj_apply]
      group
    have hy_inv : (MulAut.conj g⁻¹) (MulAut.conj g y) = y := by
      simp only [MulAut.conj_apply]
      group
    simpa only [hz_inv, hy_inv] using hcomm
  simpa [Suv] using hfinal

theorem ggBlockComm_commute_of_marked_split_involution
    (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Bs L : Subgroup G) (𝒦 : Finset (Subgroup G))
    (eta : Bs ≃* (I → Multiplicative (ZMod p))) (ell : Equiv.Perm I)
    (hSigma : (ggAutomizerJoin L Bs 𝒦).map
      (MulAut.congr eta).toMonoidHom = bSignedFull (r + 1) p)
    {u v cc : I}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (a : C D0 →* G) (ha : Function.Injective a)
    (hmarkL : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a =
        ggBlockComm Bs eta (ell '' (S : Set I)))
    {z : G}
    (hz : z ∈ ggBlockComm Bs eta (ell '' ({cc, 0} : Set I)))
    (hz2 : z ^ 2 = 1)
    (hzA : ∀ y ∈
      ggBlockComm Bs eta (ell '' ({v} : Set I)) ⊓
        ggBlockComm Bs eta (ell '' ({cc} : Set I)), Commute z y) :
    ∀ y ∈ ggBlockComm Bs eta (ell '' ({u, v} : Set I)), Commute z y := by
  classical
  let T : Finset I := {0, u, v, cc}
  have hTcard : T.card ≤ 4 := by
    have h1 : T.card ≤ ({u, v, cc} : Finset I).card + 1 := by
      simpa [T] using Finset.card_insert_le (0 : I) ({u, v, cc} : Finset I)
    have h2 : ({u, v, cc} : Finset I).card ≤ ({v, cc} : Finset I).card + 1 :=
      Finset.card_insert_le u ({v, cc} : Finset I)
    have h3 : ({v, cc} : Finset I).card ≤ ({cc} : Finset I).card + 1 :=
      Finset.card_insert_le v ({cc} : Finset I)
    have h4 : ({cc} : Finset I).card = 1 := by simp
    omega
  have hlt : T.card < (Finset.univ : Finset I).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, -, hdT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hd0 : d ≠ 0 := by
    intro h
    exact hdT (by rw [h]; simp [T])
  have hdu : d ≠ u := by
    intro h
    exact hdT (by rw [h]; simp [T])
  have hdv : d ≠ v := by
    intro h
    exact hdT (by rw [h]; simp [T])
  have hdc : d ≠ cc := by
    intro h
    exact hdT (by rw [h]; simp [T])
  let S0 : Finset I := {cc, 0}
  let Sv : Finset I := {v}
  let Scc : Finset I := {cc}
  let Suv : Finset I := {u, v}
  let Scd : Finset I := {cc, d}
  let M : Finset I → Subgroup G := fun S => ggBlockComm Bs eta (ell '' (S : Set I))
  let A0 : Subgroup G := M Sv ⊓ M Scc
  let tau : Equiv.Perm I := ell * Equiv.swap (0 : I) d * ell⁻¹
  have hmemAuto : SpCoord.permAut (p := p) tau ∈
      (ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs).map (MulAut.congr eta).toMonoidHom := by
    have hmemSigned : SpCoord.permAut (p := p) tau ∈ bSignedFull (r + 1) p :=
      aPermutationFull_le_bSignedFull (n := r + 1) (p := p)
        (permAut_mem_aPermutationFull (n := r + 1) (p := p) tau)
    have hmemJoin : SpCoord.permAut (p := p) tau ∈
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
      rw [hSigma]
      exact hmemSigned
    exact Subgroup.map_mono (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦) hmemJoin
  obtain ⟨g, hgN, -, hgτ⟩ := exists_mem_of_mem_map_congr eta hmemAuto
  have hM0e := sparse_block0 (Bs := Bs) (eta := eta) (ell := ell) (d := d)
    hdc hdu hdv hcc0 h0u h0v hgN hgτ
  have hMuve := sparse_blockUV (Bs := Bs) (eta := eta) (ell := ell) (d := d)
    hdc hdu hdv hcc0 h0u h0v hgN hgτ
  have hMve := sparse_blockV (Bs := Bs) (eta := eta) (ell := ell) (d := d)
    hdc hdu hdv hcc0 h0u h0v hgN hgτ
  have hMccE := sparse_blockCC (Bs := Bs) (eta := eta) (ell := ell) (d := d)
    hdc hdu hdv hcc0 h0u h0v hgN hgτ
  have hA0e := sparse_blockA0 (Bs := Bs) (eta := eta) (ell := ell) hMve hMccE
  have hM0 : (M S0).map (MulAut.conj g).toMonoidHom = M Scd := by
    simpa [M, S0, Scd] using hM0e
  have hMuv : (M Suv).map (MulAut.conj g).toMonoidHom = M Suv := by
    simpa [M, Suv] using hMuve
  have hMv : (M Sv).map (MulAut.conj g).toMonoidHom = M Sv := by
    simpa [M, Sv] using hMve
  have hMcc : (M Scc).map (MulAut.conj g).toMonoidHom = M Scc := by
    simpa [M, Scc] using hMccE
  have hA0 : (A0).map (MulAut.conj g).toMonoidHom = A0 := by
    simpa [A0, M, Sv, Scc] using hA0e
  let z' : G := MulAut.conj g z
  have hzM : z ∈ M S0 := by
    simpa [M, S0] using hz
  have hz'M : z' ∈ M Scd := by
    have hmem : z' ∈ (M S0).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzM
    rwa [hM0] at hmem
  have hz'2 : z' ^ 2 = 1 := by
    have h := congrArg (MulAut.conj g) hz2
    simpa [z'] using h
  have hzA0 : ∀ y ∈ A0, Commute z y := by
    intro y hy
    exact hzA y (by simpa [A0, M, Sv, Scc] using hy)
  have hz'A : ∀ y ∈ A0, Commute z' y := by
    intro y hy
    have hy' : y ∈ (A0).map (MulAut.conj g).toMonoidHom := by
      rw [hA0]
      exact hy
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy'
    have h := (hzA0 y0 hy0).map (MulAut.conj g)
    simpa [z'] using h
  have htransport : ∀ y ∈ M ({u, v} : Finset I), Commute z y :=
    sparse_marked_transport (r := r) (F := F) (b := b) (c := c)
      hirr huv hcu hcv h0u h0v hcc0 hd0 hdu hdv hdc a ha M
      (fun S hSne hScard hSD => by simpa [M] using hmarkL S hSne hScard hSD)
      (g := g) (z := z) (z' := z') (A0 := A0)
      (by simpa [S0, Scd] using hM0) (by simpa [Suv] using hMuv)
      rfl (by simpa [Scd] using hz'M) hz'2 hz'A rfl
  simpa [M, Suv] using htransport

omit [Finite G] in
theorem ggBlockComm_commute_splitMinusRho_of_marked_singletons
    (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Bs : Subgroup G)
    (eta : Bs ≃* (I → Multiplicative (ZMod p))) (ell : Equiv.Perm I)
    (S : Finset I) (k : C S →* G) (hk : Function.Injective k)
    (hmark : ∀ i ∈ S,
      ((C ({i} : Finset I)).subgroupOf (C S)).map k =
        ggBlockComm Bs eta (ell '' ({i} : Set I)))
    {i j : I} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (sigma : Equiv.Perm I)
    (hsigma : splitMinusRho (r := r) (F := F) (b := b) (c := c)
      hirr hr sigma ∈ C S) :
    ∀ y ∈
      ggBlockComm Bs eta (ell '' ({i} : Set I)) ⊓
        ggBlockComm Bs eta (ell '' ({j} : Set I)),
      Commute
        (k ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr sigma, hsigma⟩)
        y := by
  classical
  intro y hy
  obtain ⟨hyi, hyj⟩ := Subgroup.mem_inf.mp hy
  have hpre_i : y ∈ ((C ({i} : Finset I)).subgroupOf (C S)).map k := by
    rw [hmark i hi]
    exact hyi
  have hpre_j : y ∈ ((C ({j} : Finset I)).subgroupOf (C S)).map k := by
    rw [hmark j hj]
    exact hyj
  obtain ⟨xi, hxi, hxiy⟩ := Subgroup.mem_map.mp hpre_i
  obtain ⟨xj, hxj, hxjy⟩ := Subgroup.mem_map.mp hpre_j
  have hxij : xi = xj := hk (by rw [hxiy, hxjy])
  let e : C S := xi
  have hei : e ∈ (C ({i} : Finset I)).subgroupOf (C S) := by
    simpa [e] using hxi
  have hej : e ∈ (C ({j} : Finset I)).subgroupOf (C S) := by
    simpa [e, hxij] using hxj
  have hey : k e = y := by
    simpa [e] using hxiy
  let Q : QuadraticForm F (Vm (r + 2) F) := quadMinus (r + 2) F b c
  let X : Subgroup (Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) := orthDerived Q
  let ψ : Vm (r + 2) F ≃ₗ[F] (Fin 2 → F) × (I → F × F) :=
    minusPlaneCoordinates (n := r + 2) (F := F)
  let W : Submodule F (Vm (r + 2) F) := coordAnchor ψ
  let U : I → Submodule F (Vm (r + 2) F) := fun l => coordPlane ψ l
  let eNat : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F := ((e : C S) : X)
  have heiRaw : eNat ∈ supportedDerived Q
      (anchoredSupport F (r + 2) ({i} : Finset I)) := by
    have h := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hei)
    simpa [eNat, Q, chartSubgroup, X] using h
  have hejRaw : eNat ∈ supportedDerived Q
      (anchoredSupport F (r + 2) ({j} : Finset I)) := by
    have h := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hej)
    simpa [eNat, Q, chartSubgroup, X] using h
  have hψ : ∀ v : Vm (r + 2) F,
      Q v = binaryForm F b c (ψ v).1 + ∑ l, hypPlane F ((ψ v).2 l) := by
    intro v
    exact quadMinus_eq_binaryForm_add_minusPlaneCoordinates r v
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (r + 2) F hirr
  have hQE : (polarBilin (hypPlane F)).Nondegenerate := hypPlane_polarBilin_nondegenerate
  have hsuppi : anchoredSupport F (r + 2) ({i} : Finset I) = W ⊔ U i := by
    rw [← coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := r + 2) (F := F)
      ({i} : Finset I)]
    simp [coordSupport, ψ, W, U]
  have hsuppj : anchoredSupport F (r + 2) ({j} : Finset I) = W ⊔ U j := by
    rw [← coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := r + 2) (F := F)
      ({j} : Finset I)]
    simp [coordSupport, ψ, W, U]
  have heiSup : eNat ∈ supportedDerived Q (W ⊔ U i) := by
    rwa [hsuppi] at heiRaw
  have hejSup : eNat ∈ supportedDerived Q (W ⊔ U j) := by
    rwa [hsuppj] at hejRaw
  have hUi : (polarBilin (Q.comp (U i).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (Q := Q) (U := U i)
      (fun x hx h => coordPlane_polarNondegOn ψ hψ hQE i x hx h)
  have hWA : ∀ w ∈ W, ∀ a ∈ U i, polar Q w a = 0 :=
    fun w hw a ha => polar_coordAnchor_plane ψ hψ hw ha
  have hAB : ∀ a ∈ U i, ∀ b ∈ U j, polar Q a b = 0 :=
    fun a ha b hb => polar_coordPlane_plane ψ hψ hij ha hb
  have heW : ∀ w ∈ W, eNat w ∈ W := fun w hw =>
    supportedDerived_apply_mem_of_mem_two_supports (Q := Q) (W := W) (A := U i) (B := U j)
      hUi hWA hAB heiSup hejSup hw
  have hePerp : ∀ x ∈ suppPerp Q W, eNat x = x := fun x hx =>
    supportedDerived_apply_perp_of_mem_two_supports (Q := Q) (W := W) (A := U i) (B := U j)
      hUi hWA hAB heiSup hejSup hx
  let rhoElem : C S :=
    ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr sigma, hsigma⟩
  let gNat : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F := ((rhoElem : C S) : X)
  have hgNatEq : gNat = coordPermHom ψ sigma := by
    simpa [gNat, rhoElem, ψ] using
      coe_splitMinusRho_apply (r := r) (F := F) (b := b) (c := c) hirr hr sigma
  have hgW : ∀ x ∈ W, gNat x = x := by
    intro x hx
    obtain ⟨r0, rfl⟩ := mem_coordAnchor.mp hx
    rw [hgNatEq]
    exact coordPermHom_anchor ψ sigma r0
  have hgX : (((rhoElem : C S) : X) :
      Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) ∈ orthDerived Q := by
    change (((rhoElem : C S) : X) :
      Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) ∈ X
    exact ((rhoElem : C S) : X).2
  have hgO : gNat ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup_of_commutator (R := Q) hgX
  have hWreg : (polarBilin (Q.comp W.subtype)).Nondegenerate :=
    coordAnchor_nondegenerate ψ hψ hQ hQE
  have hcommNat : gNat * eNat = eNat * gNat :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq (Q := Q) (U := W)
      hWreg hgO hgW heW hePerp
  have hcommCS : Commute rhoElem e := by
    rw [commute_iff_eq]
    apply Subtype.ext
    apply Subtype.ext
    simpa [gNat, eNat] using hcommNat
  have hmap := hcommCS.map k
  simpa [rhoElem, hey] using hmap

private theorem splitMinusRho_mem_chartSubgroup_of_fixing_compl
    (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    (S : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀ i : I, i ∉ S → σ i = i) :
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ ∈ C S := by
  change (((splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ :
      orthDerived (quadMinus (r + 2) F b c)) :
      Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)) ∈
    supportedDerived (quadMinus (r + 2) F b c) (anchoredSupport F (r + 2) S)
  rw [coe_splitMinusRhoOfTwoLe_apply]
  exact coordPermHom_mem_supportedDerived_of_fixing_compl
    (n := r + 2) (F := F) hirr hcard S σ hσ

private theorem splitMinusRho_mem_chartSubgroup_erase
    (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (d : I) (σ : Equiv.Perm I) (hσ : σ d = d) :
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ ∈
      C (Finset.univ.erase d) := by
  apply splitMinusRho_mem_chartSubgroup_of_fixing_compl hr hirr hcard
  intro i hi
  have hid : i = d := by
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] using hi
  subst i
  exact hσ

private noncomputable def splitMinusRhoStabilizerHom
    (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (d : I) :
    MulAction.stabilizer (Equiv.Perm I) d →* C (Finset.univ.erase d) where
  toFun sigma :=
    ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr
        (sigma : Equiv.Perm I),
      splitMinusRho_mem_chartSubgroup_erase (r := r) hr hirr hcard d
        (sigma : Equiv.Perm I)
        (by
          simpa only [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] using
            sigma.property)⟩
  map_one' := by ext; simp
  map_mul' := by intro x y; ext; simp

private theorem splitMinusRho_eq_splitMinusRhoOfTwoLe
    (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (σ : Equiv.Perm I) :
    splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr σ =
      splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ := by
  apply Subtype.ext
  rw [coe_splitMinusRho_apply, coe_splitMinusRhoOfTwoLe_apply]

private theorem native_marked_deletion_crossing
    (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    (Bs L : Subgroup G) (𝒦 : Finset (Subgroup G))
    (eta : Bs ≃* (I → Multiplicative (ZMod p))) (ell : Equiv.Perm I)
    (hSigma : (ggAutomizerJoin L Bs 𝒦).map
      (MulAut.congr eta).toMonoidHom = bSignedFull (r + 1) p)
    {u v cc : I}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (a : C D0 →* G) (k : C (Finset.univ.erase u) →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (hmarkL : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a =
        ggBlockComm Bs eta (ell '' (S : Set I)))
    (hmarkK : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 →
      S ⊆ Finset.univ.erase u →
      ((C S).subgroupOf (C (Finset.univ.erase u))).map k =
        ggBlockComm Bs eta (ell '' (S : Set I)))
    (hmem : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
      (Equiv.swap cc 0) ∈ C (Finset.univ.erase u)) :
    ∀ x : C ({u, v} : Finset I),
      Commute (k ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
          (Equiv.swap cc 0), hmem⟩)
        (a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x)) := by
  classical
  let z : G := k ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
    (Equiv.swap cc 0), hmem⟩
  have hmemCC0 : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
      (Equiv.swap cc 0) ∈ C ({cc, 0} : Finset I) := by
    simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using
      splitMinusRho_mem_chartSubgroup_of_fixing_compl (r := r) (by omega) hirr hcard
        ({cc, 0} : Finset I) (Equiv.swap cc 0) (by
          intro k hk
          have hkcc : k ≠ cc := by
            intro h
            exact hk (by simp [h])
          have hk0 : k ≠ 0 := by
            intro h
            exact hk (by simp [h])
          exact Equiv.swap_apply_of_ne_of_ne hkcc hk0)
  have hmarkKpair : ((C ({cc, 0} : Finset I)).subgroupOf
      (C (Finset.univ.erase u))).map k =
      ggBlockComm Bs eta (ell '' (({cc, 0} : Finset I) : Set I)) := by
    refine hmarkK ({cc, 0} : Finset I) ?_ ?_ ?_
    · exact ⟨cc, by simp⟩
    · rw [Finset.card_pair hcc0]
      try omega
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [hcu]
      · simp [h0u]
  have hzM0 : z ∈ ggBlockComm Bs eta (ell '' (({cc, 0} : Finset I) : Set I)) := by
    rw [← hmarkKpair]
    exact Subgroup.mem_map_of_mem k
      (show (⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
        (Equiv.swap cc 0), hmem⟩ : C (Finset.univ.erase u)) ∈
          (C ({cc, 0} : Finset I)).subgroupOf (C (Finset.univ.erase u)) from hmemCC0)
  have hmarkKsing : ∀ i ∈ Finset.univ.erase u,
      ((C ({i} : Finset I)).subgroupOf (C (Finset.univ.erase u))).map k =
        ggBlockComm Bs eta (ell '' ({i} : Set I)) := by
    intro i hi
    have h := hmarkK ({i} : Finset I) ⟨i, by simp⟩ (by simp) (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      rwa [hx])
    simpa only [Finset.coe_singleton] using h
  have hvDu : v ∈ Finset.univ.erase u := by simp [huv.symm]
  have hccDu : cc ∈ Finset.univ.erase u := by simp [hcu]
  have hzA := ggBlockComm_commute_splitMinusRho_of_marked_singletons
    (r := r) (F := F) (b := b) (c := c) hr hirr Bs eta ell
    (Finset.univ.erase u) k hk hmarkKsing hvDu hccDu hcv.symm
    (Equiv.swap cc 0) hmem
  have hsqPerm : (Equiv.swap cc (0 : I) : Equiv.Perm I) ^ 2 = 1 := by
    rw [pow_two, Equiv.swap_mul_self]
  have hsq : (⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
      (Equiv.swap cc 0), hmem⟩ : C (Finset.univ.erase u)) ^ 2 = 1 := by
    apply Subtype.ext
    change (splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
      (Equiv.swap cc 0)) ^ 2 = 1
    rw [← map_pow, hsqPerm, map_one]
  have hz2 : z ^ 2 = 1 := by
    dsimp [z]
    rw [← map_pow, hsq, map_one]
  have hzCross : ∀ y ∈ ggBlockComm Bs eta
      (ell '' ({u, v} : Set I)), Commute z y :=
    ggBlockComm_commute_of_marked_split_involution
      (r := r) hr hirr Bs L 𝒦 eta ell hSigma huv hcu hcv h0u h0v hcc0
      a ha hmarkL (by simpa only [Finset.coe_insert, Finset.coe_singleton] using hzM0)
      hz2 hzA
  intro x
  have hxM : a (Subgroup.inclusion
      (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
        (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) ∈
      ggBlockComm Bs eta (ell '' (({u, v} : Finset I) : Set I)) := by
    rw [← hmarkL ({u, v} : Finset I) ?_ ?_ ?_]
    · exact Subgroup.mem_map_of_mem a (Subgroup.mem_subgroupOf.mpr x.2)
    · exact ⟨u, by simp⟩
    · rw [Finset.card_pair huv]
      try omega
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · simp [h0u.symm]
      · simp [h0v.symm]
  exact hzCross _ (by simpa only [Finset.coe_insert, Finset.coe_singleton] using hxM)

private theorem range_deletion_chart_le_sup_perm_range
    (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {u : I} (h0u : (0 : I) ≠ u)
    (a : C D0 →* G) (k : C (Finset.univ.erase u) →* G) (t : Equiv.Perm I →* G)
    (hcoh : ∀ x : C (D0 ∩ Finset.univ.erase u),
      a (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_left) x) =
      k (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_right) x))
    (hRestrK : ∀ sigma : Equiv.Perm I, sigma u = u →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
          (by omega) sigma ∈ C (Finset.univ.erase u),
        k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
          (by omega) sigma, h⟩ = t sigma) :
    k.range ≤ a.range ⊔ t.range := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ r by omega)
  let Ch : Finset (Fin (m + 4)) → Subgroup (orthDerived (quadMinus ((m + 3) + 2) F b c)) :=
    fun S => chartSubgroup (n := (m + 3) + 2) (F := F) (b := b) (c := c) S
  let D : Finset (Fin (m + 4)) := deletionPlanes (m + 3)
  let Du : Finset (Fin (m + 4)) := Finset.univ.erase u
  let O : Finset (Fin (m + 4)) := D ∩ Du
  have hDuCard : 2 ≤ Du.card := by
    dsimp [Du]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u)]
    simp
  have hgenDu : Ch Du = ⨆ P : PairBelow Du,
      Ch (P : Finset (Fin (m + 4))) :=
    chartSubgroup_eq_iSup_pair (r := m + 3) (F := F) (b := b) (c := c) hirr Du hDuCard
  have hOcard : O.card = m + 2 := by
    have hOeq : O = D.erase u := by
      dsimp [O, Du]
      rw [Finset.inter_erase]
      simp
    rw [hOeq, Finset.card_erase_of_mem (by
      dsimp [D, deletionPlanes]
      exact Finset.mem_erase.mpr ⟨h0u.symm, Finset.mem_univ u⟩)]
    have hDcard : D.card = m + 3 := by
      dsimp [D, deletionPlanes]
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (m + 4)))]
      simp
    rw [hDcard]
    omega
  have htop : (⊤ : Subgroup (Ch Du)) =
      ⨆ P : PairBelow Du, (Ch (P : Finset (Fin (m + 4)))).subgroupOf (Ch Du) := by
    apply Subgroup.map_injective (f := (Ch Du).subtype) (Ch Du).subtype_injective
    calc
      (⊤ : Subgroup (Ch Du)).map (Ch Du).subtype = Ch Du := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = ⨆ P : PairBelow Du, Ch (P : Finset (Fin (m + 4))) := hgenDu
      _ = (⨆ P : PairBelow Du, (Ch (P : Finset (Fin (m + 4)))).subgroupOf (Ch Du)).map
          (Ch Du).subtype := by
        rw [Subgroup.map_iSup]
        refine iSup_congr fun P => ?_
        exact (Subgroup.map_subgroupOf_eq_of_le
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr P.2.1)).symm
  have hpairle : ∀ P : PairBelow Du,
      ((Ch (P : Finset (Fin (m + 4)))).subgroupOf (Ch Du)).map k ≤
        a.range ⊔ t.range := by
    intro P
    rintro y ⟨x, hx, rfl⟩
    have hxP : (x : orthDerived (quadMinus ((m + 3) + 2) F b c)) ∈
        Ch (P : Finset (Fin (m + 4))) := Subgroup.mem_subgroupOf.mp hx
    by_cases h0P : (0 : Fin (m + 4)) ∈ (P : Finset (Fin (m + 4)))
    ·
      have herase : ((P : Finset (Fin (m + 4))).erase (0 : Fin (m + 4))).card = 1 := by
        rw [Finset.card_erase_of_mem h0P, P.2.2]
        try omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp herase
      have hPpair : (P : Finset (Fin (m + 4))) = {0, i} := by
        rw [← Finset.insert_erase h0P, hi]
        try simp
      have hi0 : i ≠ 0 := by
        have hi' : i ∈ (P : Finset (Fin (m + 4))).erase (0 : Fin (m + 4)) := by
          rw [hi]
          simp
        exact (Finset.mem_erase.mp hi').1
      have hiP : i ∈ (P : Finset (Fin (m + 4))) := by
        rw [hPpair]
        simp
      have hiDu : i ∈ Du := P.2.1 hiP
      have hiO : i ∈ O := by
        refine Finset.mem_inter.mpr ⟨?_, hiDu⟩
        dsimp [D, deletionPlanes]
        exact Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩
      obtain ⟨j, hjO, hji⟩ := Finset.exists_mem_ne (s := O) (a := i) (by
        rw [hOcard]
        omega)
      have hj0 : j ≠ 0 := by
        have hjD : j ∈ D := (Finset.mem_inter.mp hjO).1
        dsimp [D, deletionPlanes] at hjD
        exact (Finset.mem_erase.mp hjD).1
      have hju : j ≠ u := by
        have hjDu : j ∈ Du := (Finset.mem_inter.mp hjO).2
        dsimp [Du] at hjDu
        exact (Finset.mem_erase.mp hjDu).1
      let tau : Perm (Fin (m + 4)) := Equiv.swap 0 j
      have htauu : tau u = u := by
        dsimp [tau]
        exact Equiv.swap_apply_of_ne_of_ne h0u.symm hju.symm
      obtain ⟨hτDu, hkτ⟩ := hRestrK tau htauu
      have hQimage : (({j, i} : Finset (Fin (m + 4))).image tau) =
          (P : Finset (Fin (m + 4))) := by
        rw [hPpair]
        ext z
        simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨w, hw, hwz⟩
          rcases hw with hwj | hwi
          · subst w
            rw [← hwz]
            left
            exact Equiv.swap_apply_right (0 : Fin (m + 4)) j
          · subst w
            rw [← hwz]
            right
            exact Equiv.swap_apply_of_ne_of_ne hi0 hji.symm
        · intro hz
          rcases hz with hz0 | hzi
          · subst z
            refine ⟨j, Or.inl rfl, ?_⟩
            exact Equiv.swap_apply_right (0 : Fin (m + 4)) j
          · subst z
            refine ⟨i, Or.inr rfl, ?_⟩
            exact Equiv.swap_apply_of_ne_of_ne hi0 hji.symm
      have hmap := chartSubgroup_map_conj_splitMinusRhoOfTwoLe (r := m + 3) (F := F)
        (b := b) (c := c) hirr (by omega) tau ({j, i} : Finset (Fin (m + 4)))
      rw [hQimage] at hmap
      have hxmap : (x : orthDerived (quadMinus ((m + 3) + 2) F b c)) ∈
          (Ch ({j, i} : Finset (Fin (m + 4)))).map
            (MulAut.conj (splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c)
              hirr (by omega) tau)).toMonoidHom := by
        rw [hmap]
        exact hxP
      obtain ⟨y0, hy0, hy0x⟩ := Subgroup.mem_map.mp hxmap
      have hsubJIO : ({j, i} : Finset (Fin (m + 4))) ⊆ O := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hjO
        · exact hiO
      have hsubJIDu : ({j, i} : Finset (Fin (m + 4))) ⊆ Du := by
        intro z hz
        exact (Finset.mem_inter.mp (hsubJIO hz)).2
      have hy0Du : y0 ∈ Ch Du :=
        chartSubgroup_mono (F := F) (b := b) (c := c) hirr hsubJIDu hy0
      let ρD : Ch Du :=
        ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr
          (by omega) tau, hτDu⟩
      let yD : Ch Du := ⟨y0, hy0Du⟩
      let yO : Ch O := ⟨y0, chartSubgroup_mono (F := F) (b := b) (c := c) hirr
        hsubJIO hy0⟩
      have hyOeq : Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_right : O ⊆ Du)) yO = yD := by
        apply Subtype.ext
        rfl
      have hxD : x = ρD * yD * ρD⁻¹ := by
        apply Subtype.ext
        change (x : orthDerived (quadMinus ((m + 3) + 2) F b c)) =
          splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr
            (by omega) tau *
            y0 *
            (splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr
              (by omega) tau)⁻¹
        rw [← hy0x]
        change (MulAut.conj (splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c)
          hirr (by omega) tau)) y0 = _
        rw [MulAut.conj_apply]
      have hkx : k x = k ρD * k yD * (k ρD)⁻¹ := by
        rw [hxD, map_mul, map_mul, map_inv]
      have hkrho : k ρD = t tau := by
        exact hkτ
      have hki : k yD = a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_left : O ⊆ D)) yO) := by
        rw [← hyOeq]
        exact (hcoh yO).symm
      have hkiL : k yD ∈ a.range := by
        rw [hki]
        exact ⟨_, rfl⟩
      have hkrhoT : k ρD ∈ t.range := ⟨tau, hkrho.symm⟩
      have hmem : k x ∈ a.range ⊔ t.range := by
        rw [hkx]
        exact Subgroup.mul_mem (a.range ⊔ t.range)
          (Subgroup.mul_mem (a.range ⊔ t.range) (Subgroup.mem_sup_right hkrhoT)
            (Subgroup.mem_sup_left hkiL))
          (Subgroup.inv_mem (a.range ⊔ t.range) (Subgroup.mem_sup_right hkrhoT))
      exact hmem
    ·
      have hPsubO : (P : Finset (Fin (m + 4))) ⊆ O := by
        intro z hz
        have hzDu : z ∈ Du := P.2.1 hz
        have hz0 : z ≠ 0 := by
          intro h
          exact h0P (h ▸ hz)
        refine Finset.mem_inter.mpr ⟨?_, hzDu⟩
        dsimp [D, deletionPlanes]
        exact Finset.mem_erase.mpr ⟨hz0, Finset.mem_univ z⟩
      let xO : Ch O := ⟨(x : orthDerived (quadMinus ((m + 3) + 2) F b c)),
        chartSubgroup_mono (F := F) (b := b) (c := c) hirr hPsubO hxP⟩
      have hxOeq : Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_right : O ⊆ Du)) xO = x := by
        apply Subtype.ext
        rfl
      have hkx : k x = a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_left : O ⊆ D)) xO) := by
        rw [← hxOeq]
        exact (hcoh xO).symm
      rw [hkx]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
  rw [MonoidHom.range_eq_map, htop, Subgroup.map_iSup]
  apply iSup_le
  intro P
  exact hpairle P

private theorem coherent_sparse_gluing_stage2
    (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    {u v cc : I}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (a : C D0 →* G) (k : C (Finset.univ.erase u) →* G)
    (hcoh : ∀ x : C (D0 ∩ Finset.univ.erase u),
      a (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_left) x) =
      k (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_right) x))
    (hnative : ∀ hmem : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
        (by omega) (Equiv.swap cc 0) ∈ C (Finset.univ.erase u),
      ∀ x : C ({u, v} : Finset I),
        Commute (k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) (Equiv.swap cc 0), hmem⟩)
          (a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x))) :
    ∃ t : Equiv.Perm I →* G,
      (∀ sigma : Equiv.Perm I, sigma 0 = 0 →
        ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma ∈ C D0,
          a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma, h⟩ = t sigma) ∧
      (∀ sigma : Equiv.Perm I, sigma u = u →
        ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma ∈ C (Finset.univ.erase u),
          k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma, h⟩ = t sigma) ∧
      (∀ x : C ({u, v} : Finset I),
        t (Equiv.swap cc (0 : I)) *
            a (Subgroup.inclusion
              (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
                (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) =
          a (Subgroup.inclusion
              (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
                (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) *
            t (Equiv.swap cc (0 : I))) ∧
      t.range ≤ a.range ⊔ k.range := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ r by omega)
  let Ch : Finset (Fin (m + 4)) → Subgroup (orthDerived (quadMinus ((m + 3) + 2) F b c)) :=
    fun S => chartSubgroup (n := (m + 3) + 2) (F := F) (b := b) (c := c) S
  let D : Finset (Fin (m + 4)) := deletionPlanes (m + 3)
  let Du : Finset (Fin (m + 4)) := Finset.univ.erase u
  let O : Finset (Fin (m + 4)) := D ∩ Du
  let lift := splitMinusRhoStabilizerHom (r := m + 3) (F := F) (b := b) (c := c)
    (by omega) hirr hcard
  let aP : MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) (0 : Fin (m + 4)) →* G :=
    a.comp (lift 0)
  let kP : MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) u →* G := k.comp (lift u)
  have hOverlapP : ∀ (sigma : Equiv.Perm (Fin (m + 4)))
      (h0 : sigma ∈ MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) (0 : Fin (m + 4)))
      (hu : sigma ∈ MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) u),
      aP ⟨sigma, h0⟩ = kP ⟨sigma, hu⟩ := by
    intro sigma h0 hu
    have hsig0 : sigma (0 : Fin (m + 4)) = 0 := by
      have h := h0
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
      exact h
    have hsigU : sigma u = u := by
      have h := hu
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
      exact h
    have hcompl : ∀ k : Fin (m + 4), k ∉ O → k = 0 ∨ k = u := by
      intro k hk
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · right
        by_contra hku
        apply hk
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_erase.mpr ⟨hk0, Finset.mem_univ k⟩
        · exact Finset.mem_erase.mpr ⟨hku, Finset.mem_univ k⟩
    have hfixO : ∀ k : Fin (m + 4), k ∉ O → sigma k = k := by
      intro k hk
      rcases hcompl k hk with hk0 | hku
      · subst k
        exact hsig0
      · subst k
        exact hsigU
    have hmemO : splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega) sigma ∈
        Ch O :=
      splitMinusRho_mem_chartSubgroup_of_fixing_compl (r := m + 3) (by omega) hirr hcard O sigma
        hfixO
    let xO : Ch O :=
      ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega) sigma, hmemO⟩
    have haeq : aP ⟨sigma, h0⟩ =
        a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_left : O ⊆ D)) xO) := by
      change a (lift 0 ⟨sigma, h0⟩) =
        a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_left : O ⊆ D)) xO)
      apply congrArg a
      apply Subtype.ext
      rfl
    have hkeq : kP ⟨sigma, hu⟩ =
        k (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_right : O ⊆ Du)) xO) := by
      change k (lift u ⟨sigma, hu⟩) =
        k (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (Finset.inter_subset_right : O ⊆ Du)) xO)
      apply congrArg k
      apply Subtype.ext
      rfl
    rw [haeq, hkeq]
    exact hcoh xO
  have hCrossP : ∀ (hUV : Equiv.swap u v ∈
        MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) (0 : Fin (m + 4)))
      (hC0 : Equiv.swap cc 0 ∈ MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) u),
      Commute (aP ⟨Equiv.swap u v, hUV⟩) (kP ⟨Equiv.swap cc 0, hC0⟩) := by
    intro hUV hC0
    have hmemUV : splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega)
        (Equiv.swap u v) ∈ Ch ({u, v} : Finset (Fin (m + 4))) := by
      apply splitMinusRho_mem_chartSubgroup_of_fixing_compl (r := m + 3) (by omega) hirr hcard
      intro k hk
      have hku : k ≠ u := by
        intro h
        exact hk (by simp [h])
      have hkv : k ≠ v := by
        intro h
        exact hk (by simp [h])
      exact Equiv.swap_apply_of_ne_of_ne hku hkv
    have hmemDu : splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega)
        (Equiv.swap cc 0) ∈ Ch Du := by
      apply splitMinusRho_mem_chartSubgroup_erase (r := m + 3) (by omega) hirr hcard u
      exact Equiv.swap_apply_of_ne_of_ne hcu.symm h0u.symm
    have haeq : aP ⟨Equiv.swap u v, hUV⟩ =
        a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (pair_subset_deletionSet (d := (0 : Fin (m + 4))) h0u.symm h0v.symm))
          (⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega)
            (Equiv.swap u v), hmemUV⟩ : Ch ({u, v} : Finset (Fin (m + 4))))) := by
      change a (lift 0 ⟨Equiv.swap u v, hUV⟩) =
        a (Subgroup.inclusion
          (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
            (pair_subset_deletionSet (d := (0 : Fin (m + 4))) h0u.symm h0v.symm))
          (⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega)
            (Equiv.swap u v), hmemUV⟩ : Ch ({u, v} : Finset (Fin (m + 4)))))
      apply congrArg a
      apply Subtype.ext
      rfl
    have hkeq : kP ⟨Equiv.swap cc 0, hC0⟩ =
        k ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega)
          (Equiv.swap cc 0), hmemDu⟩ := by
      change k (lift u ⟨Equiv.swap cc 0, hC0⟩) =
        k ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega)
          (Equiv.swap cc 0), hmemDu⟩
      apply congrArg k
      apply Subtype.ext
      rfl
    rw [haeq, hkeq]
    exact (hnative hmemDu ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c)
      hirr (by omega) (Equiv.swap u v), hmemUV⟩).symm
  obtain ⟨t, hRestrLhom, hRestrKhom, hRange⟩ :=
    exists_permHom_of_point_stabilizers huv hcu hcv h0u h0v hcc0 aP kP hOverlapP hCrossP
  have hRestrL : ∀ sigma : Equiv.Perm (Fin (m + 4)), sigma 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega) sigma ∈ Ch D,
        a ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega) sigma, h⟩ =
          t sigma := by
    intro sigma hsigma
    have hmem : sigma ∈ MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) (0 : Fin (m + 4)) := by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hsigma
    refine ⟨(lift 0 ⟨sigma, hmem⟩).2, ?_⟩
    have hx := DFunLike.congr_fun hRestrLhom ⟨sigma, hmem⟩
    exact hx.symm
  have hRestrK : ∀ sigma : Equiv.Perm (Fin (m + 4)), sigma u = u →
      ∃ h : splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega) sigma ∈ Ch Du,
        k ⟨splitMinusRhoOfTwoLe (r := m + 3) (F := F) (b := b) (c := c) hirr (by omega) sigma, h⟩ =
          t sigma := by
    intro sigma hsigma
    have hmem : sigma ∈ MulAction.stabilizer (Equiv.Perm (Fin (m + 4))) u := by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hsigma
    refine ⟨(lift u ⟨sigma, hmem⟩).2, ?_⟩
    have hx := DFunLike.congr_fun hRestrKhom ⟨sigma, hmem⟩
    exact hx.symm
  have hcross : ∀ x : Ch ({u, v} : Finset (Fin (m + 4))),
      t (Equiv.swap cc (0 : Fin (m + 4))) *
          a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (m + 4))) h0u.symm h0v.symm)) x) =
        a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (m + 4))) h0u.symm h0v.symm)) x) *
          t (Equiv.swap cc (0 : Fin (m + 4))) := by
    intro x
    obtain ⟨h, hh⟩ := hRestrK (Equiv.swap cc 0)
      (Equiv.swap_apply_of_ne_of_ne hcu.symm h0u.symm)
    rw [← hh]
    exact (hnative h x).eq
  have haP_le : aP.range ≤ a.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨lift 0 x, rfl⟩
  have hkP_le : kP.range ≤ k.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨lift u x, rfl⟩
  have ht_le : t.range ≤ a.range ⊔ k.range := by
    rw [hRange]
    exact sup_le_sup haP_le hkP_le
  exact ⟨t, hRestrL, hRestrK, hcross, ht_le⟩

theorem exists_permHom_of_coherent_sparse_split_charts_of_three_le
    (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    {u v cc : I}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (a : C D0 →* G) (k : C (Finset.univ.erase u) →* G)
    (hcoh : ∀ x : C (D0 ∩ Finset.univ.erase u),
      a (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_left) x) =
      k (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_right) x))
    (hnative : ∀ hmem : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
        (by omega) (Equiv.swap cc 0) ∈ C (Finset.univ.erase u),
      ∀ x : C ({u, v} : Finset I),
        Commute (k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) (Equiv.swap cc 0), hmem⟩)
          (a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x))) :
    ∃ t : Equiv.Perm I →* G,
      (∀ sigma : Equiv.Perm I, sigma 0 = 0 →
        ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma ∈ C D0,
          a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma, h⟩ = t sigma) ∧
      (∀ sigma : Equiv.Perm I, sigma u = u →
        ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma ∈ C (Finset.univ.erase u),
          k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) sigma, h⟩ = t sigma) ∧
      (∀ x : C ({u, v} : Finset I),
        t (Equiv.swap cc (0 : I)) *
            a (Subgroup.inclusion
              (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
                (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) =
          a (Subgroup.inclusion
              (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
                (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) *
            t (Equiv.swap cc (0 : I))) ∧
      a.range ⊔ t.range = a.range ⊔ k.range := by
  classical
  obtain ⟨t, hRestrL, hRestrK, hcross, ht_le⟩ :=
    coherent_sparse_gluing_stage2 hr hirr hcard huv hcu hcv h0u h0v hcc0 a k hcoh hnative
  have hK_le : k.range ≤ a.range ⊔ t.range :=
    range_deletion_chart_le_sup_perm_range hr hirr h0u a k t hcoh hRestrK
  have hrange : a.range ⊔ t.range = a.range ⊔ k.range :=
    le_antisymm (sup_le le_sup_left ht_le) (sup_le le_sup_left hK_le)
  exact ⟨t, hRestrL, hRestrK, hcross, hrange⟩

theorem exists_permHom_of_coherent_marked_sparse_split_charts
    (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F)
    (Bs L K : Subgroup G) (𝒦 : Finset (Subgroup G))
    (eta : Bs ≃* (I → Multiplicative (ZMod p))) (ell : Equiv.Perm I)
    (hSigma : (ggAutomizerJoin L Bs 𝒦).map
      (MulAut.congr eta).toMonoidHom = bSignedFull (r + 1) p)
    {u v cc : I}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : I) ≠ u) (h0v : (0 : I) ≠ v) (hcc0 : cc ≠ 0)
    (a : C D0 →* G) (k : C (Finset.univ.erase u) →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (haL : a.range = L) (hkK : k.range = K)
    (hmarkL : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a =
        ggBlockComm Bs eta (ell '' (S : Set I)))
    (hmarkK : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 →
      S ⊆ Finset.univ.erase u →
      ((C S).subgroupOf (C (Finset.univ.erase u))).map k =
        ggBlockComm Bs eta (ell '' (S : Set I)))
    (hcoh : ∀ x : C (D0 ∩ Finset.univ.erase u),
      a (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_left) x) =
      k (Subgroup.inclusion
        (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_right) x)) :
    ∃ t : Equiv.Perm I →* G,
      (∀ sigma : Equiv.Perm I, sigma 0 = 0 →
        ∃ h : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr sigma ∈ C D0,
          a ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr sigma, h⟩ =
            t sigma) ∧
      (∀ sigma : Equiv.Perm I, sigma u = u →
        ∃ h : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr sigma ∈
            C (Finset.univ.erase u),
          k ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr sigma, h⟩ =
            t sigma) ∧
      (∀ x : C ({u, v} : Finset I),
        t (Equiv.swap cc (0 : I)) *
            a (Subgroup.inclusion
              (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
                (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) =
          a (Subgroup.inclusion
              (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
                (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x) *
            t (Equiv.swap cc (0 : I))) ∧
      a.range ⊔ t.range = L ⊔ K := by
  classical
  have hnative : ∀ hmem : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
      (Equiv.swap cc 0) ∈ C (Finset.univ.erase u),
      ∀ x : C ({u, v} : Finset I),
        Commute (k ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
            (Equiv.swap cc 0), hmem⟩)
          (a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x)) :=
    native_marked_deletion_crossing hr hirr hcard Bs L 𝒦 eta ell hSigma
      huv hcu hcv h0u h0v hcc0 a k ha hk hmarkL hmarkK
  have hnative' : ∀ hmem : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
      (by omega) (Equiv.swap cc 0) ∈ C (Finset.univ.erase u),
      ∀ x : C ({u, v} : Finset I),
        Commute (k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) (Equiv.swap cc 0), hmem⟩)
          (a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : I)) h0u.symm h0v.symm)) x)) := by
    intro hmem x
    simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using
      hnative (by simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using hmem) x
  obtain ⟨t, hRestrL, hRestrK, hcross, hrange⟩ :=
    exists_permHom_of_coherent_sparse_split_charts_of_three_le
      (show 3 ≤ r by omega) hirr hcard huv hcu hcv h0u h0v hcc0 a k hcoh hnative'
  refine ⟨t, ?_, ?_, hcross, ?_⟩
  · intro sigma hsigma
    obtain ⟨h, hh⟩ := hRestrL sigma hsigma
    exact ⟨by simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using h,
      by simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using hh⟩
  · intro sigma hsigma
    obtain ⟨h, hh⟩ := hRestrK sigma hsigma
    exact ⟨by simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using h,
      by simpa only [splitMinusRho_eq_splitMinusRhoOfTwoLe] using hh⟩
  · rw [haL, hkK] at hrange
    rw [haL]
    exact hrange

end SparseSplitCharts

end CFSG.StandardType

end
