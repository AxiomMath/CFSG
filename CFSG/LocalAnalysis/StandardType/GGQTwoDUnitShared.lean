module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoord
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]


private lemma qtwoDB11_dSign_mul_self (m : ℕ) (a b : Fin m) :
    dSign m a b * dSign m a b = 1 := by
  refine (dBasis m).ext' fun i => ?_
  rw [LinearEquiv.mul_apply, dSign_apply, map_smul, dSign_apply, smul_smul]
  by_cases h : i = a ∨ i = b <;> simp [h]

private lemma qtwoDB11_dSign_invol (m : ℕ) (a b : Fin m) (v : DVec m) :
    dSign m a b (dSign m a b v) = v := by
  have h := congrArg (fun f : DVec m ≃ₗ[ZMod 3] DVec m => f v)
    (qtwoDB11_dSign_mul_self m a b)
  simpa using h

private lemma qtwoDB11_dSign_dPerm_swap (m : ℕ) {a b i j : Fin m}
    (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) :
    dSign m a b * dPerm m (Equiv.swap i j) =
      dPerm m (Equiv.swap i j) * dSign m a b := by
  refine (dBasis m).ext' fun k => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dPerm_apply, dSign_apply, dSign_apply,
    map_smul, dPerm_apply]
  congr 1
  have hfixa : Equiv.swap i j a = a := Equiv.swap_apply_of_ne_of_ne hai haj
  have hfixb : Equiv.swap i j b = b := Equiv.swap_apply_of_ne_of_ne hbi hbj
  by_cases hk : k = a ∨ k = b
  · have hk' : Equiv.swap i j k = a ∨ Equiv.swap i j k = b := by
      rcases hk with h | h
      · exact Or.inl (by rw [h, hfixa])
      · exact Or.inr (by rw [h, hfixb])
    rw [if_pos hk, if_pos hk']
  · have hk' : ¬ (Equiv.swap i j k = a ∨ Equiv.swap i j k = b) := by
      rintro (h | h)
      · exact hk (Or.inl (by
          have := congrArg (Equiv.swap i j) h
          rwa [Equiv.swap_apply_self, hfixa] at this))
      · exact hk (Or.inr (by
          have := congrArg (Equiv.swap i j) h
          rwa [Equiv.swap_apply_self, hfixb] at this))
    rw [if_neg hk, if_neg hk']

private lemma qtwoDB11_dSign_dPerm_swap_apply (m : ℕ) {a b i j : Fin m}
    (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) (v : DVec m) :
    dSign m a b (dPerm m (Equiv.swap i j) v) =
      dPerm m (Equiv.swap i j) (dSign m a b v) :=
  congrArg (fun f : DVec m ≃ₗ[ZMod 3] DVec m => f v)
    (qtwoDB11_dSign_dPerm_swap m hai haj hbi hbj)

private lemma qtwoDB11_iSup_coordBlockSU_three_eq_top {K : Type} [Field K] [Finite K]
    [CharP K 2] {k : ℕ} (hK : Nat.card K = 4) (hk : 3 ≤ k) :
    (⨆ (A : Finset (Fin k)) (_ : A.card = 3), coordBlockSU K 2 1 A) = ⊤ := by
  rcases eq_or_lt_of_le hk with rfl | hk4
  · rw [eq_top_iff]
    intro x _
    refine Subgroup.mem_iSup_of_mem (Finset.univ : Finset (Fin 3)) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    rw [SixPoint.qTwoSixWin_coordBlockSU_univ]
    exact Subgroup.mem_top x
  · rw [eq_top_iff, ← fourBlockSup_eq_top (K := K) hK (by omega : 4 ≤ k)]
    unfold fourBlockSup
    refine iSup₂_le fun I hI => ?_
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hI
    have hA : ({a, b, c} : Finset (Fin k)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    have hB : ({b, c, d} : Finset (Fin k)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
    have hAB : (({a, b, c} : Finset (Fin k)) ∪ {b, c, d}).card = 4 := by
      rw [show ({a, b, c} : Finset (Fin k)) ∪ {b, c, d} = {a, b, c, d} by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto]
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
    rw [show ({a, b, c, d} : Finset (Fin k)) = ({a, b, c} : Finset (Fin k)) ∪ {b, c, d} by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    rw [← coordBlockSU_sup_three (K := K) hK hA hB hAB]
    exact sup_le (le_iSup₂_of_le {a, b, c} hA le_rfl)
      (le_iSup₂_of_le {b, c, d} hB le_rfl)

private lemma qtwoDB11_coordBlockSU_le_iSup_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {N : ℕ} (hK : Nat.card K = 4) {T : Finset (Fin N)} (hT : 3 ≤ T.card) :
    coordBlockSU K 2 1 T ≤
      ⨆ (A : Finset (Fin N)) (_ : A ⊆ T) (_ : A.card = 3), coordBlockSU K 2 1 A := by
  set k : ℕ := T.card with hk
  have hk3 : 3 ≤ k := hT
  have h0k : 0 + k ≤ N := by
    have h := T.card_le_univ
    rw [Fintype.card_fin] at h
    omega
  set W : Finset (Fin N) := Finset.univ.map (SixPoint.qTwoSixWinEmb h0k) with hW
  have hWcard : W.card = k := by
    rw [hW, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq W T (by rw [hWcard, hk])
  have hTW : coordBlockSU K 2 1 T =
      (coordBlockSU K 2 1 W).map
        (MulAut.conj (ggPhanNSAPairAux_permElt (f := 1) τ)).toMonoidHom :=
    ((ggQTwoDUnit_coordBlockSU_conj (K := K) (f := 1) τ W).trans (by rw [hτ])).symm
  have hWgen : coordBlockSU K 2 1 W =
      ⨆ (A : Finset (Fin k)) (_ : A.card = 3),
        coordBlockSU K 2 1 (A.map (SixPoint.qTwoSixWinEmb h0k)) := by
    rw [hW, ← SixPoint.qTwoSixWin_range (K := K) (m := N) (k := k) (i := 0) h0k]
    calc (blockEmb K 2 1 N k 0 h0k).range
        = (⊤ : Subgroup (Su K 2 1 k)).map (blockEmb K 2 1 N k 0 h0k) := by
            rw [Subgroup.map_top]
      _ = (⨆ (A : Finset (Fin k)) (_ : A.card = 3), coordBlockSU K 2 1 A).map
            (blockEmb K 2 1 N k 0 h0k) := by
            rw [qtwoDB11_iSup_coordBlockSU_three_eq_top (K := K) hK hk3]
      _ = ⨆ (A : Finset (Fin k)) (_ : A.card = 3),
            (coordBlockSU K 2 1 A).map (blockEmb K 2 1 N k 0 h0k) := by
            simp only [Subgroup.map_iSup]
      _ = ⨆ (A : Finset (Fin k)) (_ : A.card = 3),
            coordBlockSU K 2 1 (A.map (SixPoint.qTwoSixWinEmb h0k)) := by
            refine iSup_congr fun A => iSup_congr fun _ => ?_
            rw [SixPoint.qTwoSixWin_map_coordBlockSU]
  rw [hTW, hWgen]
  simp only [Subgroup.map_iSup]
  refine iSup_le fun A => iSup_le fun hA => ?_
  rw [ggQTwoDUnit_coordBlockSU_conj (K := K) (f := 1) τ
    (A.map (SixPoint.qTwoSixWinEmb h0k))]
  refine le_iSup_of_le ((A.map (SixPoint.qTwoSixWinEmb h0k)).map τ.toEmbedding)
    (le_iSup_of_le ?_ (le_iSup_of_le ?_ le_rfl))
  · rw [← hτ]
    exact (Finset.map_subset_map).mpr ((Finset.map_subset_map).mpr (Finset.subset_univ A))
  · rw [Finset.card_map, Finset.card_map, hA]

private lemma qtwoDB11_coordBlockSU_eq_iSup_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {N : ℕ} (hK : Nat.card K = 4) {T : Finset (Fin N)} (hT : 3 ≤ T.card) :
    coordBlockSU K 2 1 T =
      ⨆ (A : Finset (Fin N)) (_ : A ⊆ T) (_ : A.card = 3), coordBlockSU K 2 1 A :=
  le_antisymm (qtwoDB11_coordBlockSU_le_iSup_three hK hT)
    (iSup_le fun A => iSup_le fun hA => iSup_le fun _ => qTwoS34_coordBlockSU_mono hA)

theorem ggQTwoDUnit_shared_three (hEA : GGQTwoEdgeAmbientInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} (hbase : QTwoUnitBase p B Bs x L ψ ε)
    {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ} (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    {a b : Fin m} (hab : a ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {T : Finset (Fin m)}
    (hT : T.card = 3) (haT : a ∉ T) (hbT : b ∉ T) :
    ((coordBlockSU F0 2 1 T).map ψ).map (MulAut.conj g).toMonoidHom =
      (coordBlockSU F0 2 1 T).map ψ := by
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hT
  have hai : a ≠ i := fun h => haT (by rw [h]; simp)
  have haj : a ≠ j := fun h => haT (by rw [h]; simp)
  have hak : a ≠ k := fun h => haT (by rw [h]; simp)
  have hbi : b ≠ i := fun h => hbT (by rw [h]; simp)
  have hbj : b ≠ j := fun h => hbT (by rw [h]; simp)
  have hbk : b ≠ k := fun h => hbT (by rw [h]; simp)
  set r : MulAut ↥Bs := ((ε (Equiv.swap i j) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with hr
  set r' : MulAut ↥Bs := ((ε (Equiv.swap j k) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with hr'
  have hrA : r ∈ ggAutomizer L Bs := by rw [hr]; exact (ε (Equiv.swap i j)).2
  have hrA' : r' ∈ ggAutomizer L Bs := by rw [hr']; exact (ε (Equiv.swap j k)).2
  have hrJ : r ∈ ggAutomizerJoin L Bs 𝒦 := by
    rw [ggAutomizerJoin]
    exact Subgroup.mem_sup_left hrA
  have hrJ' : r' ∈ ggAutomizerJoin L Bs 𝒦 := by
    rw [ggAutomizerJoin]
    exact Subgroup.mem_sup_left hrA'
  have hact_r : ∀ s : ↥Bs, βL (Additive.ofMul (r s)) =
      dPerm m (Equiv.swap i j) (βL (Additive.ofMul s)) := by
    intro s; rw [hr]; exact hcoords.perm (Equiv.swap i j) s
  have hact_r' : ∀ s : ↥Bs, βL (Additive.ofMul (r' s)) =
      dPerm m (Equiv.swap j k) (βL (Additive.ofMul s)) := by
    intro s; rw [hr']; exact hcoords.perm (Equiv.swap j k) s
  have hrC : r ∈ ggCoxRefl M e := by
    refine hcoords.cox false i j hij r hrJ ?_
    intro s
    rw [hact_r s]
    simp [dTau]
  have hrC' : r' ∈ ggCoxRefl M e := by
    refine hcoords.cox false j k hjk r' hrJ' ?_
    intro s
    rw [hact_r' s]
    simp [dTau]
  have hne : r * r' ≠ r' * r := by
    intro heq
    obtain ⟨s, hs⟩ : ∃ s : ↥Bs, βL (Additive.ofMul s) = dBasis m i := by
      obtain ⟨x, hx⟩ := βL.surjective (dBasis m i)
      exact ⟨Additive.toMul x, by simpa using hx⟩
    have h1 : βL (Additive.ofMul ((r * r') s)) = dBasis m j := by
      change βL (Additive.ofMul (r (r' s))) = dBasis m j
      rw [hact_r (r' s), hact_r' s, hs]
      rw [dPerm_apply, dPerm_apply, Equiv.swap_apply_of_ne_of_ne hij hik,
        Equiv.swap_apply_left]
    have h2 : βL (Additive.ofMul ((r' * r) s)) = dBasis m k := by
      change βL (Additive.ofMul (r' (r s))) = dBasis m k
      rw [hact_r' (r s), hact_r s, hs]
      rw [dPerm_apply, dPerm_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
    have hsame : (r * r') s = (r' * r) s := by rw [heq]
    rw [hsame, h2] at h1
    exact (dBasis m).injective.ne hjk h1.symm
  have hαinv : ∀ s : ↥Bs, βL (Additive.ofMul (α⁻¹ s)) =
      dSign m a b (βL (Additive.ofMul s)) := by
    intro s
    have h1 : βL (Additive.ofMul s) =
        dSign m a b (βL (Additive.ofMul (α⁻¹ s))) := by
      have := hα (α⁻¹ s)
      simpa using this
    have h2 := congrArg (dSign m a b) h1
    rw [qtwoDB11_dSign_invol] at h2
    exact h2.symm
  have hinj : Function.Injective (fun s : ↥Bs => βL (Additive.ofMul s)) :=
    βL.injective.comp (fun _ _ h => h)
  have hconj_r : α * r * α⁻¹ = r := by
    refine MulEquiv.ext fun s => ?_
    apply hinj
    calc βL (Additive.ofMul ((α * r * α⁻¹) s))
        = βL (Additive.ofMul (α (r (α⁻¹ s)))) := by rfl
      _ = dSign m a b (βL (Additive.ofMul (r (α⁻¹ s)))) := hα _
      _ = dSign m a b (dPerm m (Equiv.swap i j)
            (βL (Additive.ofMul (α⁻¹ s)))) := by rw [hact_r (α⁻¹ s)]
      _ = dSign m a b (dPerm m (Equiv.swap i j)
            (dSign m a b (βL (Additive.ofMul s)))) := by rw [hαinv s]
      _ = dSign m a b (dSign m a b (dPerm m (Equiv.swap i j)
            (βL (Additive.ofMul s)))) := by
            rw [← qtwoDB11_dSign_dPerm_swap_apply m hai haj hbi hbj]
      _ = dPerm m (Equiv.swap i j) (βL (Additive.ofMul s)) := by
            rw [qtwoDB11_dSign_invol]
      _ = βL (Additive.ofMul (r s)) := (hact_r s).symm
  have hconj_r' : α * r' * α⁻¹ = r' := by
    refine MulEquiv.ext fun s => ?_
    apply hinj
    calc βL (Additive.ofMul ((α * r' * α⁻¹) s))
        = βL (Additive.ofMul (α (r' (α⁻¹ s)))) := by rfl
      _ = dSign m a b (βL (Additive.ofMul (r' (α⁻¹ s)))) := hα _
      _ = dSign m a b (dPerm m (Equiv.swap j k)
            (βL (Additive.ofMul (α⁻¹ s)))) := by rw [hact_r' (α⁻¹ s)]
      _ = dSign m a b (dPerm m (Equiv.swap j k)
            (dSign m a b (βL (Additive.ofMul s)))) := by rw [hαinv s]
      _ = dSign m a b (dSign m a b (dPerm m (Equiv.swap j k)
            (βL (Additive.ofMul s)))) := by
            rw [← qtwoDB11_dSign_dPerm_swap_apply m haj hak hbj hbk]
      _ = dPerm m (Equiv.swap j k) (βL (Additive.ofMul s)) := by
            rw [qtwoDB11_dSign_invol]
      _ = βL (Additive.ofMul (r' s)) := (hact_r' s).symm
  have hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap i j)) * (s : G) * (ψ (ggPermSU (Equiv.swap i j)))⁻¹ := by
    intro s
    rw [hr, hbase.perm (Equiv.swap i j) s, Equiv.swap_inv]
  have hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap j k)) * (s : G) * (ψ (ggPermSU (Equiv.swap j k)))⁻¹ := by
    intro s
    rw [hr', hbase.perm (Equiv.swap j k) s, Equiv.swap_inv]
  have hedge : ggRankTwo Bs r r' = ggRankTwoIn L Bs r r' :=
    hEA G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) r hrA hrC r' hrA' hrC' hne
  have hrank := ggQTwoDUnit_rankTwoIn_eq (K := F0) (n := m) (ψ := ψ)
    hbase.hyp hbase.card_field hbase.diag hij hjk hik hr hr'
  have hrank' : ggRankTwoIn L Bs r r' =
      (coordBlockSU F0 2 1 ({i, j, k} : Finset (Fin m))).map ψ := by
    rw [← hrank, hbase.range]
  have hconj : (ggRankTwo Bs r r').map (MulAut.conj g).toMonoidHom = ggRankTwo Bs r r' := by
    rw [ggRankTwo_map_conj hg r r', hconj_r, hconj_r']
  rw [← hrank', ← hedge]
  exact hconj

theorem ggQTwoDUnit_shared (hEA : GGQTwoEdgeAmbientInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} (hbase : QTwoUnitBase p B Bs x L ψ ε)
    {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ} (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    {a b : Fin m} (hab : a ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {T : Finset (Fin m)}
    (hT : 3 ≤ T.card) (haT : a ∉ T) (hbT : b ∉ T) :
    ((coordBlockSU F0 2 1 T).map ψ).map (MulAut.conj g).toMonoidHom =
      (coordBlockSU F0 2 1 T).map ψ := by
  rw [qtwoDB11_coordBlockSU_eq_iSup_three (K := F0) hbase.card_field hT]
  simp only [Subgroup.map_iSup]
  refine iSup_congr fun A => iSup_congr fun hA => iSup_congr fun hc => ?_
  exact ggQTwoDUnit_shared_three hEA hcfg e' hm hM hbase hcoords hab hα hgN hg hc
    (fun h => haT (hA h)) (fun h => hbT (hA h))

end CFSG.StandardType.QTwo

end
