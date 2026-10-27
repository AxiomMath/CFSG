module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PermBlocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.SUGeneration
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.SeitzReduction.UnitaryPilot (permSUHom)

@[expose] def GGUniFourCompletion : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] (f : ℕ)
    (E : QuadExt F K (unitaryInvolution K 2 f)), 4 ≤ Nat.card F → Nat.card K = (2 ^ f) ^ 2 →
  ∀ (G : Type) [Group G] (a : Fin 4 → (normOmega E 3 →* G)),
    (∀ i, Function.Injective (a i)) → ∀ R : Finset (Fin 4) → Subgroup G,
    (∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove)) →
    ∃ Ψ : normOmega E 4 →* G, Function.Injective Ψ ∧
      Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a 3 ∧
      Ψ.range = ⨆ i, (a i).range

@[expose] def uniFourTau : Fin 4 → Equiv.Perm (Fin 4)
  | 0 => finRotate 4
  | 1 => Equiv.swap 1 3 * Equiv.swap 1 2
  | 2 => Equiv.swap 2 3
  | 3 => 1

theorem uniFourTau_castSucc (i : Fin 4) (s : Fin 3) :
    uniFourTau i s.castSucc = i.succAbove s := by
  fin_cases i <;> fin_cases s <;> decide

theorem uniFourTau_last (i : Fin 4) : uniFourTau i (Fin.last 3) = i := by
  fin_cases i <;> decide

section Normalizer

variable {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  {Bs X : Subgroup G}

theorem ggConjAut_mul {g h : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hh : h ∈ Subgroup.normalizer (Bs : Set G)) :
    ggConjAut Bs (Subgroup.mul_mem _ hg hh) = ggConjAut Bs hg * ggConjAut Bs hh := by
  ext b
  simp only [ggConjAut_apply, MulAut.mul_apply, Subgroup.coe_mul, mul_assoc, mul_inv_rev]

theorem ggConjAut_one : ggConjAut Bs (Subgroup.one_mem (Subgroup.normalizer (Bs : Set G))) = 1 := by
  ext b
  simp [ggConjAut_apply]

theorem SpCoord.permAut_mul' (σ τ : Equiv.Perm (Fin n)) :
    (SpCoord.permAut (p := p) (σ * τ)) = SpCoord.permAut σ * SpCoord.permAut τ := by
  ext a j
  simp [SpCoord.permAut_apply, MulAut.mul_apply, mul_inv_rev]

theorem SpCoord.permAut_one' : (SpCoord.permAut (p := p) (1 : Equiv.Perm (Fin n))) = 1 := by
  ext a j
  simp [SpCoord.permAut_apply]

theorem GGSecFiveBPermUniLFrame.permSUHom_mem_normalizer [Finite G] {π : Equiv.Perm (Fin n)}
    {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hp : p.Prime)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hn : 3 ≤ n) (ρ : Equiv.Perm (Fin n)) :
    ∃ hu : σ (permSUHom hK ρ) ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hu) = SpCoord.permAut (π * ρ * π⁻¹) := by
  induction ρ using Equiv.Perm.swap_induction_on with
  | one =>
    have h1 : σ (permSUHom hK 1) = 1 := by rw [map_one, map_one]
    refine ⟨h1 ▸ Subgroup.one_mem _, ?_⟩
    have hc : ggConjAut Bs (h1 ▸ Subgroup.one_mem _ :
        σ (permSUHom hK 1) ∈ Subgroup.normalizer (Bs : Set G)) = 1 := by
      ext b
      simp [ggConjAut_apply, h1]
    rw [hc, map_one, mul_one, mul_inv_cancel, SpCoord.permAut_one']
  | swap_mul ρ a b hab ih =>
    obtain ⟨hu, hη⟩ := ih
    obtain ⟨hv, hvη⟩ := hF.permSUHom_swap_mem_normalizer hK hp hBsC hA hn a b
    have hmul : σ (permSUHom hK (Equiv.swap a b * ρ)) =
        σ (permSUHom hK (Equiv.swap a b)) * σ (permSUHom hK ρ) := by
      rw [map_mul, map_mul]
    refine ⟨hmul ▸ Subgroup.mul_mem _ hv hu, ?_⟩
    have hc : ggConjAut Bs (hmul ▸ Subgroup.mul_mem _ hv hu :
        σ (permSUHom hK (Equiv.swap a b * ρ)) ∈ Subgroup.normalizer (Bs : Set G)) =
        ggConjAut Bs hv * ggConjAut Bs hu := by
      ext c
      simp [ggConjAut_apply, hmul, mul_assoc]
    rw [hc, map_mul, hvη, hη, ← SpCoord.permAut_mul', Equiv.swap_apply_apply]
    congr 1
    group

end Normalizer

section Charts

variable {G : Type} [Group G] {p f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
  [Finite K] [CharP K 2] {E : QuadExt F K (unitaryInvolution K 2 f)}

@[expose] noncomputable def uniFourChart (hK : UnitaryFieldData 2 f K)
    (σ : ↥(unitarySU 2 f K 4) →* G) (κ : normOmega E 3 →* G) (i : Fin 4) :
    normOmega E 3 →* G :=
  (MulAut.conj (σ (permSUHom hK (uniFourTau i)))).toMonoidHom.comp κ

theorem uniFourChart_apply (hK : UnitaryFieldData 2 f K) (σ : ↥(unitarySU 2 f K 4) →* G)
    (κ : normOmega E 3 →* G) (i : Fin 4) (a : normOmega E 3) :
    uniFourChart hK σ κ i a =
      σ (permSUHom hK (uniFourTau i)) * κ a * (σ (permSUHom hK (uniFourTau i)))⁻¹ :=
  rfl

theorem uniFourChart_three (hK : UnitaryFieldData 2 f K) (σ : ↥(unitarySU 2 f K 4) →* G)
    (κ : normOmega E 3 →* G) : uniFourChart hK σ κ 3 = κ := by
  ext a
  simp [uniFourChart_apply, uniFourTau]

theorem uniFourChart_frame [Finite G] {Bs L KU : Subgroup G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {χ' : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs KU eta π σ χ') (hp : p.Prime)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer KU Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (i : Fin 4) :
    ∃ hu : σ (permSUHom hK (uniFourTau i)) ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hu) = SpCoord.permAut (π * uniFourTau i * π⁻¹) ∧
      GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj (σ (permSUHom hK (uniFourTau i)))).toMonoidHom)
        eta ((uniFourTau i).trans π) (uniFourChart hK σ κ i) χ := by
  obtain ⟨hu, hη⟩ := hσ.permSUHom_mem_normalizer hK hp hBsC hA (by norm_num) (uniFourTau i)
  refine ⟨hu, hη, ?_⟩
  have h := hκ.conj_transporter hu hη
  have hπ : π.trans (π * uniFourTau i * π⁻¹) = (uniFourTau i).trans π := by
    ext a
    simp [Equiv.Perm.mul_apply]
  rw [hπ] at h
  exact h

theorem uniFourChart_range (hK : UnitaryFieldData 2 f K) (σ : ↥(unitarySU 2 f K 4) →* G)
    {κ : normOmega E 3 →* G} {L : Subgroup G} (hκr : κ.range = L) (i : Fin 4) :
    (uniFourChart hK σ κ i).range =
      L.map (MulAut.conj (σ (permSUHom hK (uniFourTau i)))).toMonoidHom := by
  rw [uniFourChart, MonoidHom.range_comp, hκr]

theorem uniFourChart_map_normBlock_pair [Finite G] [Fact p.Prime] {Bs L KU : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {χ' : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs KU eta π σ χ')
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer KU Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hX : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxB : x ∈ Bs)
    (i : Fin 4) {s s' : Fin 3} (hss' : s ≠ s') :
    (normBlock E 3 {s, s'}).map (uniFourChart hK σ κ i) =
      ggBlockComm Bs eta ({π (i.succAbove s), π (i.succAbove s')} : Set (Fin 4)) := by
  obtain ⟨hu, -, hfr⟩ := uniFourChart_frame hκ hK hσ (Fact.out : p.Prime) hBsC hA i
  set w := σ (permSUHom hK (uniFourTau i)) with hw
  have hX' : CFSG.Open.IsComponentOf (L.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({w * x * w⁻¹} : Set G)) :=
    isComponentOf_iff_open.mp (isComponentOf_centralizer_map_conj (isComponentOf_iff_open.mpr hX) w)
  have hyB : w * x * w⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hu x).mp hxB
  have hcard : ({s, s'} : Finset (Fin 3)).card = 2 := Finset.card_pair hss'
  have h := hfr.blockComm_eq_map_normBlock hBsC hyB hX' (S := {s, s'}) (by omega) (by omega)
  rw [← h]
  congr 1
  rw [Finset.coe_pair, Set.image_pair]
  exact congrArg₂ (fun a b => ({a, b} : Set (Fin 4))) (congrArg π (uniFourTau_castSucc i s))
    (congrArg π (uniFourTau_castSucc i s'))

private theorem uniFour_blockSU_mono {d : ℕ} {S T : Finset (Fin d)} (hST : S ⊆ T) :
    TableBUE.blockSU (K := K) (n := f) S ≤ TableBUE.blockSU (K := K) (n := f) T := by
  intro y hy
  rw [TableBUE.mem_blockSU] at hy ⊢
  intro a b hab
  exact hy a b (hab.imp (fun h ha => h (hST ha)) (fun h hb => h (hST hb)))

private theorem uniFour_blockSU_le_range_uniCast (hK : UnitaryFieldData 2 f K)
    {S : Finset (Fin 4)} (hS : ∀ a ∈ S, a ≠ Fin.last 3) :
    TableBUE.blockSU (K := K) (n := f) S ≤ (uniCast hK 3).range := by
  have hsub : S ⊆ Finset.univ.map Fin.castSuccEmb := by
    intro a ha
    rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
    · exact Finset.mem_map_of_mem _ (Finset.mem_univ b)
    · exact absurd rfl (hS _ ha)
  refine (uniFour_blockSU_mono hsub).trans ?_
  have hblock : TableBUE.blockSU (K := K) (n := f) (Finset.univ.map Fin.castSuccEmb) =
      CFSG.SeitzReduction.UnitaryPilot.unitaryBlock hK
        (Finset.univ.map (Fin.castSuccEmb : Fin 3 ↪ Fin 4)) := by
    ext z
    rw [CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock, TableBUE.mem_blockSU]
    exact Iff.rfl
  rw [hblock]
  exact unitaryBlock_castSucc_le_range_uniCast hK 3

theorem uniFour_exists_ne_ne (a b : Fin 4) : ∃ k : Fin 4, k ≠ a ∧ k ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

theorem map_blockSU_pair_le_range_uniFourChart (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {κ : normOmega E 3 →* G} {L : Subgroup G}
    (hκr : κ.range = L) (hU1 : ∀ g, κ (uniEmb E hK 3 g) = σ (uniCast hK 3 g))
    {a b k : Fin 4} (hka : k ≠ a) (hkb : k ≠ b) :
    (TableBUE.blockSU (K := K) (n := f) ({a, b} : Finset (Fin 4))).map σ ≤
      (uniFourChart hK σ κ k).range := by
  rw [uniFourChart_range hK σ hκr k]
  set τ := uniFourTau k with hτ
  set S : Finset (Fin 4) := ({τ⁻¹ a, τ⁻¹ b} : Finset (Fin 4)) with hS
  have hSmap : S.map τ.toEmbedding = ({a, b} : Finset (Fin 4)) := by
    rw [hS, Finset.map_insert, Finset.map_singleton]
    simp
  have hSlast : ∀ c ∈ S, c ≠ Fin.last 3 := by
    intro c hc h
    rw [hS, Finset.mem_insert, Finset.mem_singleton] at hc
    have hτl : τ (Fin.last 3) = k := uniFourTau_last k
    rcases hc with rfl | rfl
    · exact hka (by rw [← hτl, ← h]; simp)
    · exact hkb (by rw [← hτl, ← h]; simp)
  have hconj := map_conj_permSUHom_blockSU (K := K) hK τ S
  rw [hSmap] at hconj
  rw [← hconj, Subgroup.map_map]
  have hcomm : σ.comp (MulAut.conj (permSUHom hK τ)).toMonoidHom =
      (MulAut.conj (σ (permSUHom hK τ))).toMonoidHom.comp σ := by
    ext y
    simp
  rw [hcomm, ← Subgroup.map_map]
  refine Subgroup.map_mono ?_
  have hle := Subgroup.map_mono (f := σ) (uniFour_blockSU_le_range_uniCast hK hSlast)
  refine hle.trans ?_
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  rw [← hκr, ← hU1 g]
  exact ⟨_, rfl⟩

theorem iSup_range_uniFourChart (hK : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f)
    {σ : ↥(unitarySU 2 f K 4) →* G} {κ : normOmega E 3 →* G} {L KU : Subgroup G}
    (hκr : κ.range = L) (hσr : σ.range = KU)
    (hU1 : ∀ g, κ (uniEmb E hK 3 g) = σ (uniCast hK 3 g)) :
    (⨆ i, (uniFourChart hK σ κ i).range) = L ⊔ KU := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [uniFourChart_range hK σ hκr i]
    rintro _ ⟨l, hl, rfl⟩
    have hw : σ (permSUHom hK (uniFourTau i)) ∈ L ⊔ KU :=
      le_sup_right (a := L) (hσr ▸ ⟨_, rfl⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (le_sup_left (b := KU) hl))
      (Subgroup.inv_mem _ hw)
  · refine sup_le ?_ ?_
    · calc L = (uniFourChart hK σ κ 3).range := by rw [uniFourChart_three, hκr]
        _ ≤ _ := le_iSup (fun i => (uniFourChart hK σ κ i).range) 3
    · rw [← hσr, MonoidHom.range_eq_map, ← SuNsRootGen.iSup_blockSU_pairs hK hq (by norm_num) 0 1]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
      obtain ⟨k, hka, hkb⟩ := uniFour_exists_ne_ne a b
      exact (map_blockSU_pair_le_range_uniFourChart hK hκr hU1 hka hkb).trans
        (le_iSup (fun i => (uniFourChart hK σ κ i).range) k)

@[expose] noncomputable def ggSingletonFrom {n : ℕ} (Bs : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (c d : Fin n) : Subgroup G :=
  ⁅ggBlockComm Bs eta ({c, d} : Set (Fin n)) ⊓
      Subgroup.centralizer {((eta.symm (Pi.mulSingle d (Multiplicative.ofAdd 1)) : ↥Bs) : G)},
    ggBlockComm Bs eta ({c, d} : Set (Fin n)) ⊓
      Subgroup.centralizer {((eta.symm (Pi.mulSingle d (Multiplicative.ofAdd 1)) : ↥Bs) : G)}⁆

theorem GGSecFiveBPermOmKFrame.map_normBlock_singleton [Fact p.Prime] {m n : ℕ}
    {Bs X : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (m + 1) ≃ Fin n} {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hm : 3 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {s t : Fin m} (hst : s ≠ t) (b : ↥Bs)
    (hb : eta b = Pi.mulSingle (π t.castSucc) (Multiplicative.ofAdd 1)) :
    (normBlock E m {s}).map κ =
      ⁅(normBlock E m {s, t}).map κ ⊓ Subgroup.centralizer {(b : G)},
        (normBlock E m {s, t}).map κ ⊓ Subgroup.centralizer {(b : G)}⁆ := by
  classical
  obtain ⟨hinj, -, hχ, hact⟩ := hκ
  obtain ⟨T, hT, hbT⟩ := hact b
  have hfun : (fun i : Fin m => eta b (π i.castSucc)) = Pi.mulSingle t (Multiplicative.ofAdd 1) := by
    funext i
    rw [hb]
    by_cases hi : i = t
    · subst hi
      simp
    · rw [Pi.mulSingle_eq_of_ne (fun h => hi (Fin.castSucc_injective _ (π.injective h))),
        Pi.mulSingle_eq_of_ne hi]
  have hTeq : T = normPlaneTorus E (by omega) hpq χ (Pi.mulSingle t (Multiplicative.ofAdd 1)) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hT v, normPlaneTorus_apply, ← hfun]
  have hmap : (normBlock E m {s, t} ⊓ Subgroup.centralizer {T}).map κ =
      (normBlock E m {s, t}).map κ ⊓ Subgroup.centralizer {(b : G)} := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, ⟨hz, hzT⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      have h1 : T * z * T⁻¹ = z := by rw [← hzT, mul_inv_cancel_right]
      have h := hbT z
      rw [h1] at h
      calc κ z * (b : G) = ((b : G) * κ z * (b : G)⁻¹) * b := by rw [h]
        _ = b * κ z := by group
    · rintro ⟨⟨z, hz, rfl⟩, hzb⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      have h2 : (b : G) * κ z * (b : G)⁻¹ = κ z := by rw [← hzb, mul_inv_cancel_right]
      have h3 : T * z * T⁻¹ = z := hinj (by rw [← hbT z, h2])
      calc z * T = (T * z * T⁻¹) * T := by rw [h3]
        _ = T * z := by group
  rw [← commutator_normBlock_pair_inf_centralizer_planeTorus_eq E hm hpq χ hχ hst, ← hTeq,
    Subgroup.map_commutator, hmap]

theorem uniFourChart_map_normBlock_singleton [Finite G] [Fact p.Prime] {Bs L KU : Subgroup G}
    {x : G} {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {χ' : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs KU eta π σ χ')
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer KU Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hX : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxB : x ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) (i : Fin 4) {s t : Fin 3} (hst : s ≠ t) :
    (normBlock E 3 {s}).map (uniFourChart hK σ κ i) =
      ggSingletonFrom Bs eta (π (i.succAbove s)) (π (i.succAbove t)) := by
  obtain ⟨-, -, hfr⟩ := uniFourChart_frame hκ hK hσ (Fact.out : p.Prime) hBsC hA i
  have hb : eta (eta.symm (Pi.mulSingle (π (i.succAbove t)) (Multiplicative.ofAdd 1))) =
      Pi.mulSingle (((uniFourTau i).trans π) t.castSucc) (Multiplicative.ofAdd 1) := by
    rw [MulEquiv.apply_symm_apply, Equiv.trans_apply, uniFourTau_castSucc]
  rw [hfr.map_normBlock_singleton (by norm_num) hpq hst _ hb,
    uniFourChart_map_normBlock_pair hκ hK hσ hBsC hA hX hxB i hst, ggSingletonFrom]

private theorem uniFour_exists_ne_ne_ne (a b c : Fin 4) : ∃ k : Fin 4, k ≠ a ∧ k ≠ b ∧ k ≠ c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem ggSingletonFrom_eq_of_four_charts {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    (a : Fin 4 → (normOmega E 3 →* G))
    (hsing : ∀ (i : Fin 4) (s t : Fin 3), s ≠ t →
      (normBlock E 3 {s}).map (a i) =
        ggSingletonFrom Bs eta (π (i.succAbove s)) (π (i.succAbove t)))
    {c d d' : Fin 4} (hd : d ≠ c) (hd' : d' ≠ c) :
    ggSingletonFrom Bs eta (π c) (π d) = ggSingletonFrom Bs eta (π c) (π d') := by
  obtain ⟨i, hic, hid, hid'⟩ := uniFour_exists_ne_ne_ne c d d'
  obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hic.symm
  obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hid.symm
  obtain ⟨t', rfl⟩ := Fin.exists_succAbove_eq hid'.symm
  rw [← hsing i s t (fun h => hd (by rw [h])),
    ← hsing i s t' (fun h => hd' (by rw [h]))]

theorem ggSingletonFrom_uniFour_eq [Finite G] [Fact p.Prime] {Bs L KU : Subgroup G}
    {x : G} {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {χ' : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs KU eta π σ χ')
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer KU Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hX : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxB : x ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) {c d d' : Fin 4} (hd : d ≠ c) (hd' : d' ≠ c) :
    ggSingletonFrom Bs eta (π c) (π d) = ggSingletonFrom Bs eta (π c) (π d') := by
  exact ggSingletonFrom_eq_of_four_charts (uniFourChart hK σ κ)
    (fun i s t hst => uniFourChart_map_normBlock_singleton hκ hK hσ hBsC hA hX hxB hpq i hst)
    hd hd'

private theorem uniFour_add_one_ne (c : Fin 4) : c + 1 ≠ c := by
  fin_cases c <;> decide

@[expose] noncomputable def uniFourBlocks (Bs : Subgroup G)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (π : Equiv.Perm (Fin 4))
    (T : Finset (Fin 4)) : Subgroup G :=
  if T.card = 1 then ⨆ c ∈ T, ggSingletonFrom Bs eta (π c) (π (c + 1))
  else ggBlockComm Bs eta (π '' (T : Set (Fin 4)))

theorem fourCharts_map_normBlock_eq_uniFourBlocks {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    (a : Fin 4 → (normOmega E 3 →* G))
    (hsing : ∀ (i : Fin 4) (s t : Fin 3), s ≠ t →
      (normBlock E 3 {s}).map (a i) =
        ggSingletonFrom Bs eta (π (i.succAbove s)) (π (i.succAbove t)))
    (hpair : ∀ (i : Fin 4) (s t : Fin 3), s ≠ t →
      (normBlock E 3 {s, t}).map (a i) =
        ggBlockComm Bs eta ({π (i.succAbove s), π (i.succAbove t)} : Set (Fin 4)))
    (i : Fin 4) (S : Finset (Fin 3)) (hS : S.Nonempty) (hS2 : S.card ≤ 2) :
    (normBlock E 3 S).map (a i) = uniFourBlocks Bs eta π (S.image i.succAbove) := by
  classical
  have hcard : (S.image i.succAbove).card = S.card :=
    Finset.card_image_of_injective _ Fin.succAbove_right_injective
  rcases (show S.card = 1 ∨ S.card = 2 by have := hS.card_pos; omega) with h1 | h2
  · obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨t, hts⟩ : ∃ t : Fin 3, t ≠ s := ⟨s + 1, by fin_cases s <;> decide⟩
    rw [uniFourBlocks, if_pos (hcard.trans h1), Finset.image_singleton]
    simp only [Finset.mem_singleton, iSup_iSup_eq_left]
    rw [hsing i s t hts.symm]
    exact ggSingletonFrom_eq_of_four_charts a hsing
      (fun h => hts (Fin.succAbove_right_injective h)) (uniFour_add_one_ne _)
  · obtain ⟨s, s', hss', rfl⟩ := Finset.card_eq_two.mp h2
    rw [uniFourBlocks, if_neg (by rw [hcard, h2]; decide), Finset.image_insert,
      Finset.image_singleton, Finset.coe_pair, Set.image_pair, hpair i s s' hss']

theorem uniFourChart_map_normBlock_eq_uniFourBlocks [Finite G] [Fact p.Prime]
    {Bs L KU : Subgroup G} {x : G} {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin 4)} {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {χ' : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs KU eta π σ χ')
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer KU Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hX : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxB : x ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) (i : Fin 4) (S : Finset (Fin 3)) (hS : S.Nonempty)
    (hS2 : S.card ≤ 2) :
    (normBlock E 3 S).map (uniFourChart hK σ κ i) =
      uniFourBlocks Bs eta π (S.image i.succAbove) := by
  exact fourCharts_map_normBlock_eq_uniFourBlocks (uniFourChart hK σ κ)
    (fun i s t hst => uniFourChart_map_normBlock_singleton hκ hK hσ hBsC hA hX hxB hpq i hst)
    (fun i s t hst => uniFourChart_map_normBlock_pair hκ hK hσ hBsC hA hX hxB i hst)
    i S hS hS2

end Charts

end CFSG.StandardType

end
