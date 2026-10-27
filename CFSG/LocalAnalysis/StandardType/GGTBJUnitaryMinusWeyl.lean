module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGRealKGUSplitRoot
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusWAux
import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.StandardType.SuSplitRootGen

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.CALinearPlane Multiplicative

theorem uniMinus_signed_of_frame
    {G : Type} [Group G] {F : Type} [Field F] {f m ε p : ℕ} [Fact p.Prime]
    {h : UnitaryFieldData 2 f F} {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {φ : hypSU h m ε →* G} (hker : φ.ker ≤ Subgroup.center (hypSU h m ε))
    (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) :
    (∀ x ∈ φ.range, (∀ v, ∃ v', x * hypFrame φ τ v * x⁻¹ = hypFrame φ τ v') →
      ∃ σ ∈ SpJoin.spSignedGroup m p, ∀ v, x * hypFrame φ τ v * x⁻¹ = hypFrame φ τ (σ v)) ∧
    ∀ i : Fin m, ∃ w ∈ φ.range, ∀ v,
      w * hypFrame φ τ v * w⁻¹ = hypFrame φ τ (SpJoin.spReflPerm m p i v) := by
  classical
  have hp : p.Prime := Fact.out
  have hframe : ∀ v : Fin m → Multiplicative (ZMod p),
      hypFrame φ τ v = φ (τ (ofAdd (fun i => toAdd (v i)))) := fun v => hypFrame_eq_ofAdd φ τ v
  have hcoord : ∀ (σ : Equiv.Perm (Fin m)) (v : Fin m → Multiplicative (ZMod p)),
      SpCoord.permAut σ v = SpJoin.coordPerm m p σ v := by
    intro σ v
    funext k
    rfl
  constructor
  · rintro x ⟨s, rfl⟩ hx
    have hn : ∀ t : Fin m → ZMod p, ∃ t', s * τ (ofAdd t) * s⁻¹ = τ (ofAdd t') := by
      intro t
      obtain ⟨v', hv'⟩ := hx (MulEquiv.piMultiplicative (fun _ : Fin m => ZMod p) (ofAdd t))
      have hφ : φ (s * τ (ofAdd t) * s⁻¹) = φ (τ (ofAdd (fun i => toAdd (v' i)))) := by
        rw [map_mul, map_mul, map_inv, ← hypFrame_ofAdd φ τ t, ← hypFrame_eq_ofAdd φ τ v']
        exact hv'
      refine ⟨fun i => toAdd (v' i), ?_⟩
      set t' : Fin m → ZMod p := fun i => toAdd (v' i) with ht'
      set z : hypSU h m ε := s * τ (ofAdd t) * s⁻¹ * (τ (ofAdd t'))⁻¹ with hz
      have hzker : z ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hz]
        rw [map_mul, map_inv, hφ]
        group
      have hzcent : z ∈ Subgroup.center (hypSU h m ε) := hker hzker
      have hcomm : Commute z (τ (ofAdd t')) :=
        (Subgroup.mem_center_iff.mp hzcent (τ (ofAdd t'))).symm
      have hconj : s * τ (ofAdd t) * s⁻¹ = z * τ (ofAdd t') := by rw [hz]; group
      have hconjpow : (s * τ (ofAdd t) * s⁻¹) ^ p = 1 := by
        rw [show s * τ (ofAdd t) * s⁻¹ = MulAut.conj s (τ (ofAdd t)) from
          (MulAut.conj_apply s (τ (ofAdd t))).symm]
        rw [← map_pow, map_pow_prime_eq_one τ t, map_one]
      have h1 : (z * τ (ofAdd t')) ^ p = 1 := by rw [← hconj]; exact hconjpow
      have hzp : z ^ p = 1 := by
        have h3 : z ^ p * (τ (ofAdd t')) ^ p = 1 := by
          rw [← hcomm.mul_pow, h1]
        rwa [map_pow_prime_eq_one τ t', mul_one] at h3
      have hz1 : z = 1 := hkp z hzker hzp
      rw [hz1, one_mul] at hconj
      exact hconj
    obtain ⟨π, σ, hσ, hrel⟩ :=
      CFSG.StandardType.RealKGUSplit.exists_signedPerm_of_normalizer h hp hζ hτ s hn
    set T : Finset (Fin m) := Finset.univ.filter (fun i => σ i = -1) with hT
    have hTmem : ∀ i, (i ∈ T ↔ σ i = -1) := by
      intro i; rw [hT, Finset.mem_filter]; simp
    obtain ⟨w, hwmem, hwval⟩ := SpJoin.exists_mem_spSignedGroup_coord (p := p) π T
    refine ⟨w, hwmem, fun v => ?_⟩
    obtain ⟨t₀', ht₀'⟩ := hn (fun i => toAdd (v i))
    have hval₁ : ∀ i, t₀' (π i) = σ i * toAdd (v i) := hrel _ _ ht₀'
    have hval₂ : ∀ i, toAdd ((w v) (π i)) = σ i * toAdd (v i) := by
      intro i
      rw [hwval v i]
      by_cases hi : i ∈ T
      · rw [if_pos hi]
        have hσi : σ i = -1 := (hTmem i).mp hi
        rw [hσi, toAdd_inv]
        ring
      · rw [if_neg hi]
        have hσi : σ i = 1 := by
          rcases hσ i with h | h
          · exact h
          · exact absurd ((hTmem i).mpr h) hi
        rw [hσi, one_mul]
    have hfun : t₀' = fun i => toAdd ((w v) i) := by
      funext j
      obtain ⟨i, rfl⟩ := π.surjective j
      rw [hval₁ i, hval₂ i]
    calc (φ s) * hypFrame φ τ v * (φ s)⁻¹
        = φ (s * τ (ofAdd (fun i => toAdd (v i))) * s⁻¹) := by
          rw [hframe v, map_mul, map_mul, map_inv]
      _ = φ (τ (ofAdd t₀')) := by rw [ht₀']
      _ = φ (τ (ofAdd (fun i => toAdd ((w v) i)))) := by rw [hfun]
      _ = hypFrame φ τ (w v) := by rw [hframe (w v)]
  · intro i
    by_cases hlt : i.val + 1 < m
    ·
      let j : Fin m := ⟨i.val + 1, hlt⟩
      refine ⟨φ (pairWeyl h ε i j), ⟨pairWeyl h ε i j, rfl⟩, fun v => ?_⟩
      calc (φ (pairWeyl h ε i j)) * hypFrame φ τ v * (φ (pairWeyl h ε i j))⁻¹
          = φ (pairWeyl h ε i j * τ (ofAdd (fun k => toAdd (v k))) *
              (pairWeyl h ε i j)⁻¹) := by
            rw [hframe v, map_mul, map_mul, map_inv]
        _ = φ (τ (ofAdd (SlNsRootGen.swapMap i j (fun k => toAdd (v k))))) := by
            rw [pairWeyl_conj h hτ i j]
        _ = φ (τ (ofAdd (fun k => toAdd (SpCoord.permAut (Equiv.swap i j) v k)))) := by
            rw [CFSG.StandardType.RealKGCover.coord_swap]
        _ = hypFrame φ τ (SpCoord.permAut (Equiv.swap i j) v) := by
            rw [hframe (SpCoord.permAut (Equiv.swap i j) v)]
        _ = hypFrame φ τ (SpJoin.spReflPerm m p i v) := by
            rw [SpJoin.spReflPerm_of_lt m p i hlt]
            rw [hcoord]
    ·
      refine ⟨φ (lineWeyl h ε i), ⟨lineWeyl h ε i, rfl⟩, fun v => ?_⟩
      calc (φ (lineWeyl h ε i)) * hypFrame φ τ v * (φ (lineWeyl h ε i))⁻¹
          = φ (lineWeyl h ε i * τ (ofAdd (fun k => toAdd (v k))) *
              (lineWeyl h ε i)⁻¹) := by
            rw [hframe v, map_mul, map_mul, map_inv]
        _ = φ (τ (ofAdd (SlNsRootGen.negMap i (fun k => toAdd (v k))))) := by
            rw [lineWeyl_conj h hp hζ.pow_eq_one hτ i]
        _ = φ (τ (ofAdd (fun k => toAdd (SpCoord.sgnAut i v k)))) := by
            rw [CFSG.StandardType.RealKGCover.coord_neg]
        _ = hypFrame φ τ (SpCoord.sgnAut i v) := by
            rw [hframe (SpCoord.sgnAut i v)]
        _ = hypFrame φ τ (SpJoin.spReflPerm m p i v) := by
            rw [SpJoin.spReflPerm_of_not_lt m p i hlt]
            congr 1

theorem uniMinus_leviBlock_automizer
    {G : Type} [Group G] {F : Type} [Field F] {f m ε p : ℕ} [Fact p.Prime]
    {h : UnitaryFieldData 2 f F} {ζ : F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    (φ : hypSU h m ε →* G) (S : Finset (Fin m)) :
    (∀ x ∈ (coordBlockSL F S).map (φ.comp (leviSU h ε)), ∀ v : Fin m → Multiplicative (ZMod p),
        (∀ i ∈ S, ∀ j ∈ S, v i = v j) → x * hypFrame φ τ v = hypFrame φ τ v * x) ∧
    ∀ i ∈ S, ∀ j ∈ S, ∃ w ∈ (coordBlockSL F S).map (φ.comp (leviSU h ε)), ∀ v,
      w * hypFrame φ τ v * w⁻¹ = hypFrame φ τ (SpCoord.permAut (p := p) (Equiv.swap i j) v) := by
  constructor
  · intro x hx v hv
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
    have hcomm := SuSplitRootGen.leviSU_commute_splitTorus h hτ hA
      (t := fun i => toAdd (v i)) (fun i hi j hj => by rw [hv i hi j hj])
    rw [hypFrame_eq_ofAdd φ τ v]
    change φ ((leviSU h ε) A) * φ (τ (ofAdd (fun i => toAdd (v i)))) =
      φ (τ (ofAdd (fun i => toAdd (v i)))) * φ ((leviSU h ε) A)
    rw [← map_mul, ← map_mul, hcomm]
  · intro i hi j hj
    obtain ⟨A, hA, hAeq⟩ :=
      Subgroup.mem_map.mp (SuSplitRootGen.pairWeyl_mem_pairBlock h i j)
    have hsub : ({i, j} : Finset (Fin m)) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hAS : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL F S :=
      CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mpr fun a b hab =>
        CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA a b (by
          rcases hab with ha | hb
          · exact Or.inl fun hJ => ha (hsub hJ)
          · exact Or.inr fun hJ => hb (hsub hJ))
    refine ⟨(φ.comp (leviSU h ε)) A, Subgroup.mem_map.mpr ⟨A, hAS, rfl⟩, fun v => ?_⟩
    have hw : (φ.comp (leviSU h ε)) A = φ (SuSplitRootGen.pairWeyl h ε i j) := by
      rw [MonoidHom.comp_apply, hAeq]
    rw [hw]
    calc (φ (SuSplitRootGen.pairWeyl h ε i j)) * hypFrame φ τ v *
          (φ (SuSplitRootGen.pairWeyl h ε i j))⁻¹
        = φ (SuSplitRootGen.pairWeyl h ε i j * τ (ofAdd (fun k => toAdd (v k))) *
            (SuSplitRootGen.pairWeyl h ε i j)⁻¹) := by
          rw [hypFrame_eq_ofAdd φ τ v, map_mul, map_mul, map_inv]
      _ = φ (τ (ofAdd (CFSG.StandardType.SlNsRootGen.swapMap i j
            (fun k => toAdd (v k))))) := by
          rw [SuSplitRootGen.pairWeyl_conj h hτ i j]
      _ = φ (τ (ofAdd (fun k => toAdd (SpCoord.permAut (Equiv.swap i j) v k)))) := by
          rw [CFSG.StandardType.RealKGCover.coord_swap]
      _ = hypFrame φ τ (SpCoord.permAut (Equiv.swap i j) v) := by
          rw [hypFrame_eq_ofAdd φ τ (SpCoord.permAut (Equiv.swap i j) v)]

theorem uniMinus_zeroBlock_automizer
    {G : Type} [Group G] {F : Type} [Field F] {f m ε p : ℕ} [Fact p.Prime]
    {h : UnitaryFieldData 2 f F} {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    (φ : hypSU h m ε →* G) (S : Finset (Fin m)) :
    (∀ x ∈ (hypBlock h (zeroCoords S)).map φ, ∀ v : Fin m → Multiplicative (ZMod p),
        (∀ i ∈ S, v i = 1) → x * hypFrame φ τ v = hypFrame φ τ v * x) ∧
    (∀ i ∈ S, ∀ j ∈ S, ∃ w ∈ (hypBlock h (zeroCoords S)).map φ, ∀ v,
      w * hypFrame φ τ v * w⁻¹ = hypFrame φ τ (SpCoord.permAut (p := p) (Equiv.swap i j) v)) ∧
    ∀ i ∈ S, ∃ w ∈ (hypBlock h (zeroCoords S)).map φ, ∀ v,
      w * hypFrame φ τ v * w⁻¹ = hypFrame φ τ (SpCoord.sgnAut (p := p) i v) := by
  have hp : p.Prime := Fact.out
  have hdiag : ∀ v : Fin m → Multiplicative (ZMod p), (∀ i ∈ S, v i = 1) →
      ∀ a ∈ zeroCoords (ε := ε) S, splitEntries ζ (fun k => toAdd (v k)) a = 1 := by
    intro v hv a ha
    have ht : ∀ i ∈ S, toAdd (v i) = 0 := by
      intro i hi; rw [hv i hi]; rfl
    rcases a with i | k | i
    · rw [SuSplitRootGen.mem_zeroCoords_inl] at ha
      rw [splitEntries, ht i ha]; simp
    · rw [splitEntries]
    · rw [SuSplitRootGen.mem_zeroCoords_inr_inr] at ha
      rw [splitEntries, ht i ha]; simp
  constructor
  · intro x hx v hv
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    have hd : ∀ a ∈ zeroCoords (ε := ε) S, ∀ b ∈ zeroCoords (ε := ε) S,
        splitEntries ζ (fun k => toAdd (v k)) a = splitEntries ζ (fun k => toAdd (v k)) b :=
      fun a ha b hb => by rw [hdiag v hv a ha, hdiag v hv b hb]
    have hcomm := SuSplitRootGen.hypBlock_commute_diagonal h hg hd
    rw [hypFrame_eq_ofAdd φ τ v, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hτ _]
    exact hcomm
  constructor
  · intro i hi j hj
    obtain ⟨A, hA, hAeq⟩ :=
      Subgroup.mem_map.mp (SuSplitRootGen.pairWeyl_mem_pairBlock h i j)
    have hsub : ({i, j} : Finset (Fin m)) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hAS : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL F S :=
      CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mpr fun a b hab =>
        CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA a b (by
          rcases hab with ha | hb
          · exact Or.inl fun hJ => ha (hsub hJ)
          · exact Or.inr fun hJ => hb (hsub hJ))
    have hpair : SuSplitRootGen.pairWeyl h ε i j ∈ hypBlock h (zeroCoords (ε := ε) S) := by
      rw [← hAeq]
      exact SuSplitRootGen.leviSU_mem_hypBlock h hAS
    refine ⟨φ (SuSplitRootGen.pairWeyl h ε i j),
      Subgroup.mem_map.mpr ⟨SuSplitRootGen.pairWeyl h ε i j, hpair, rfl⟩, fun v => ?_⟩
    calc (φ (SuSplitRootGen.pairWeyl h ε i j)) * hypFrame φ τ v *
          (φ (SuSplitRootGen.pairWeyl h ε i j))⁻¹
        = φ (SuSplitRootGen.pairWeyl h ε i j * τ (ofAdd (fun k => toAdd (v k))) *
            (SuSplitRootGen.pairWeyl h ε i j)⁻¹) := by
          rw [hypFrame_eq_ofAdd φ τ v, map_mul, map_mul, map_inv]
      _ = φ (τ (ofAdd (CFSG.StandardType.SlNsRootGen.swapMap i j
            (fun k => toAdd (v k))))) := by
          rw [SuSplitRootGen.pairWeyl_conj h hτ i j]
      _ = φ (τ (ofAdd (fun k => toAdd (SpCoord.permAut (Equiv.swap i j) v k)))) := by
          rw [CFSG.StandardType.RealKGCover.coord_swap]
      _ = hypFrame φ τ (SpCoord.permAut (Equiv.swap i j) v) := by
          rw [hypFrame_eq_ofAdd φ τ (SpCoord.permAut (Equiv.swap i j) v)]
  · intro i hi
    have hmem : SuSplitRootGen.lineWeyl h ε i ∈ hypBlock h (zeroCoords (ε := ε) S) :=
      SuSplitRootGen.hypBlock_mono (SuSplitRootGen.lineCoords_subset_zeroCoords hi)
        (SuSplitRootGen.lineWeyl_mem_lineBlock h i)
    refine ⟨φ (SuSplitRootGen.lineWeyl h ε i),
      Subgroup.mem_map.mpr ⟨SuSplitRootGen.lineWeyl h ε i, hmem, rfl⟩, fun v => ?_⟩
    calc (φ (SuSplitRootGen.lineWeyl h ε i)) * hypFrame φ τ v *
          (φ (SuSplitRootGen.lineWeyl h ε i))⁻¹
        = φ (SuSplitRootGen.lineWeyl h ε i * τ (ofAdd (fun k => toAdd (v k))) *
            (SuSplitRootGen.lineWeyl h ε i)⁻¹) := by
          rw [hypFrame_eq_ofAdd φ τ v, map_mul, map_mul, map_inv]
      _ = φ (τ (ofAdd (CFSG.StandardType.SlNsRootGen.negMap i
            (fun k => toAdd (v k))))) := by
          rw [SuSplitRootGen.lineWeyl_conj h hp hζ.pow_eq_one hτ i]
      _ = φ (τ (ofAdd (fun k => toAdd (SpCoord.sgnAut i v k)))) := by
          rw [CFSG.StandardType.RealKGCover.coord_neg]
      _ = hypFrame φ τ (SpCoord.sgnAut i v) := by
          rw [hypFrame_eq_ofAdd φ τ (SpCoord.sgnAut i v)]

end CFSG.StandardType.SuSplitRootGen

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem le_card_add_one_of_levi_fix
    {G : Type} [Group G] [Finite G] {m p : ℕ} [Fact p.Prime] {Bs X J : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (Θ : (Fin m → Multiplicative (ZMod p)) →* G) (hΘ : Function.Injective Θ)
    (hΘB : ∀ v, Θ v ∈ Bs) (hΘX : ∀ v, Θ v ∈ Subgroup.centralizer (X : Set G) → v = 1)
    {z : G} (hzB : z ∈ Bs) (hzX : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1)
    (hJX : J ≤ X) (hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    {S : Finset (Fin m)} (hS : S.Nonempty)
    (hfix : ∀ v, (∀ i ∈ S, ∀ j ∈ S, v i = v j) → Θ v ∈ Subgroup.centralizer (J : Set G)) :
    m ≤ S.card + 1 := by
  classical
  set W : Subgroup (Fin m → Multiplicative (ZMod p)) := SuSplitRootGen.constSubgroup p S with hW
  set A : Subgroup G := W.map Θ with hA
  have hABs : A ≤ Bs := by
    rintro _ ⟨v, -, rfl⟩
    exact hΘB v
  have hAcard : Nat.card A = p ^ (m - S.card + 1) := by
    rw [hA, Subgroup.card_map_of_injective (f := Θ) hΘ, SuSplitRootGen.card_constSubgroup hS]
  have hzA : z ∉ A := by
    intro hz
    obtain ⟨v, hv, hvz⟩ := Subgroup.mem_map.mp hz
    have hv1 : v = 1 := hΘX v (hvz ▸ hzX)
    rw [hv1, map_one] at hvz
    exact hz1 hvz.symm
  have hcomm : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    have hcommB : IsMulCommutative ↥Bs := hBs.1
    exact congrArg Subtype.val (hcommB.is_comm.comm ⟨a, hABs ha⟩ ⟨z, hzB⟩)
  have hsupcard : Nat.card ↥(A ⊔ Subgroup.zpowers z) = Nat.card A * p :=
    CFSG.RankThree.PartOne.Planes.card_sup_zpowers (Fact.out : p.Prime) A (hBs.2 z hzB) hzA hcomm
  have hle : A ⊔ Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (J : Set G) := by
    refine le_inf ?_ ?_
    · exact sup_le hABs (Subgroup.zpowers_le.mpr hzB)
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact hfix v (SuSplitRootGen.mem_constSubgroup.mp (by rwa [hW] at hv))
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro j hj
        exact Subgroup.mem_centralizer_iff.mp hzX j (hJX hj)
  have hcardle : Nat.card ↥(A ⊔ Subgroup.zpowers z) ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have h1 : p ^ (m - S.card + 1) * p ≤ p ^ 3 := by
    calc p ^ (m - S.card + 1) * p = Nat.card A * p := by rw [hAcard]
      _ = Nat.card ↥(A ⊔ Subgroup.zpowers z) := hsupcard.symm
      _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hcardle
      _ ≤ p ^ 3 := hcard
  have h2 : p ^ (m - S.card + 1) * p = p ^ (m - S.card + 1 + 1) := by
    rw [mul_comm, ← pow_succ']
  rw [h2] at h1
  have h3 : m - S.card + 1 + 1 ≤ 3 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h1
  have hSm : S.card ≤ m := by simpa using S.card_le_univ
  omega

theorem le_card_add_two_of_zero_fix
    {G : Type} [Group G] [Finite G] {m p : ℕ} [Fact p.Prime] {Bs X J : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (Θ : (Fin m → Multiplicative (ZMod p)) →* G) (hΘ : Function.Injective Θ)
    (hΘB : ∀ v, Θ v ∈ Bs) (hΘX : ∀ v, Θ v ∈ Subgroup.centralizer (X : Set G) → v = 1)
    {z : G} (hzB : z ∈ Bs) (hzX : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1)
    (hJX : J ≤ X) (hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    (S : Finset (Fin m))
    (hfix : ∀ v, (∀ i ∈ S, v i = 1) → Θ v ∈ Subgroup.centralizer (J : Set G)) :
    m ≤ S.card + 2 := by
  classical
  set W : Subgroup (Fin m → Multiplicative (ZMod p)) := SuSplitRootGen.trivSubgroup p S with hW
  set A : Subgroup G := W.map Θ with hA
  have hABs : A ≤ Bs := by
    rintro _ ⟨v, -, rfl⟩
    exact hΘB v
  have hAcard : Nat.card A = p ^ (m - S.card) := by
    rw [hA, Subgroup.card_map_of_injective (f := Θ) hΘ, SuSplitRootGen.card_trivSubgroup]
  have hzA : z ∉ A := by
    intro hz
    obtain ⟨v, hv, hvz⟩ := Subgroup.mem_map.mp hz
    have hv1 : v = 1 := hΘX v (hvz ▸ hzX)
    rw [hv1, map_one] at hvz
    exact hz1 hvz.symm
  have hcomm : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    have hcommB : IsMulCommutative ↥Bs := hBs.1
    exact congrArg Subtype.val (hcommB.is_comm.comm ⟨a, hABs ha⟩ ⟨z, hzB⟩)
  have hsupcard : Nat.card ↥(A ⊔ Subgroup.zpowers z) = Nat.card A * p :=
    CFSG.RankThree.PartOne.Planes.card_sup_zpowers (Fact.out : p.Prime) A (hBs.2 z hzB) hzA hcomm
  have hle : A ⊔ Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (J : Set G) := by
    refine le_inf ?_ ?_
    · exact sup_le hABs (Subgroup.zpowers_le.mpr hzB)
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact hfix v (SuSplitRootGen.mem_trivSubgroup.mp (by rwa [hW] at hv))
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro j hj
        exact Subgroup.mem_centralizer_iff.mp hzX j (hJX hj)
  have hcardle : Nat.card ↥(A ⊔ Subgroup.zpowers z) ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have h1 : p ^ (m - S.card) * p ≤ p ^ 3 := by
    calc p ^ (m - S.card) * p = Nat.card A * p := by rw [hAcard]
      _ = Nat.card ↥(A ⊔ Subgroup.zpowers z) := hsupcard.symm
      _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hcardle
      _ ≤ p ^ 3 := hcard
  have h2 : p ^ (m - S.card) * p = p ^ (m - S.card + 1) := by
    rw [mul_comm, ← pow_succ']
  rw [h2] at h1
  have h3 : m - S.card + 1 ≤ 3 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h1
  have hSm : S.card ≤ m := by simpa using S.card_le_univ
  omega

end CFSG.StandardType

end
