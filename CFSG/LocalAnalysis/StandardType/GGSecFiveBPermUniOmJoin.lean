module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenComp
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.ScalarCentralizer
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Simple

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.Generic.S1.SymBlocksUni (blkMat blkMat_apply_ι blkMat_apply_of_not_mem_left
  blkMat_apply_of_not_mem_right blkMat_one blkMat_injective)

variable {G : Type} [Group G] {p n m f : ℕ}

section Blocks

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]

private theorem uj_isSimpleGroup_normOmega_two (E : QuadExt F K (unitaryInvolution K 2 f)) :
    IsSimpleGroup ↥(normOmega E 2) :=
  haveI : Finite F := Finite.of_injective _ (algebraMap F K).injective
  isSimpleGroup_normOmega E (by norm_num)

theorem GGSecFiveBPermOmKFrame.ggBlockComm_le [Finite G] [Fact p.Prime]
    {E : QuadExt F K (unitaryInvolution K 2 f)} {Bs X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hm : 3 ≤ m)
    {c d : Fin n} (hcd : c ≠ d) (hc : c ≠ π (Fin.last m)) (hd : d ≠ π (Fin.last m)) :
    ggBlockComm Bs eta {c, d} ≤ X := by
  classical
  have h := ggSecFiveBPermOmK_ggBlockComm_le_of_card hBs hyB hX hκ (k := 2) le_rfl (by omega)
    (uj_isSimpleGroup_normOmega_two E) (T := {π.symm c, π.symm d})
    (Finset.card_pair (π.symm.injective.ne hcd)) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hc (by rw [h, Equiv.apply_symm_apply]),
        fun h => hd (by rw [h, Equiv.apply_symm_apply])⟩)
  rwa [Finset.coe_pair, Set.image_pair, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

theorem GGSecFiveBPermOmKFrame.map_anchorBlock_conj [Finite G] [Fact p.Prime]
    {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hm : 3 ≤ m) {u : G}
    (hu : u ∈ Subgroup.normalizer (Bs : Set G)) {a b : Fin n}
    (huη : MulAut.congr eta (ggConjAut Bs hu) = SpCoord.permAut (Equiv.swap a b))
    (ha0 : a ≠ π ⟨0, by omega⟩) (ha1 : a ≠ π ⟨1, by omega⟩) (hb0 : b ≠ π ⟨0, by omega⟩)
    (hb1 : b ≠ π ⟨1, by omega⟩) :
    ((anchorBlock E (by omega : 2 ≤ m)).map κ).map (MulAut.conj u).toMonoidHom =
      (anchorBlock E (by omega : 2 ≤ m)).map κ := by
  have h2 := ggSecFiveBPermOmK_ggBlockComm_eq hBs hyB hX hκ (k := 2) (by norm_num)
    (by omega) (uj_isSimpleGroup_normOmega_two E)
  have hset : (Set.range fun i : Fin 2 => π (Fin.castLE (by omega) i)) =
      ({π ⟨0, by omega⟩, π ⟨1, by omega⟩} : Set (Fin n)) := by
    ext z
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    have e0 : π (Fin.castLE (by omega) (0 : Fin 2)) = π ⟨0, by omega⟩ := rfl
    have e1 : π (Fin.castLE (by omega) (1 : Fin 2)) = π ⟨1, by omega⟩ := rfl
    rw [e0, e1]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  rw [hset] at h2
  have hA : (anchorBlock E (by omega : 2 ≤ m)).map κ = ggBlockComm Bs eta
      ({π ⟨0, by omega⟩, π ⟨1, by omega⟩} : Set (Fin n)) := h2.symm
  rw [hA, ggBlockComm_map_conj hu huη, Set.image_pair,
    Equiv.swap_apply_of_ne_of_ne ha0.symm hb0.symm, Equiv.swap_apply_of_ne_of_ne ha1.symm hb1.symm]

end Blocks

section Shared

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]

private theorem uj_coe_uniCast (hK : UnitaryFieldData 2 f K) (m : ℕ) (g : ↥(unitarySU 2 f K m)) :
    (((uniCast hK m g : ↥(unitarySU 2 f K (m + 1))) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      blkMat Fin.castSucc ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
  rfl

private theorem uj_map_uniCast_blockSU_le (hK : UnitaryFieldData 2 f K) (m : ℕ) (k l : Fin m) :
    (TableBUE.blockSU (K := K) (n := f) ({k, l} : Finset (Fin m))).map (uniCast hK m) ≤
      TableBUE.blockSU (K := K) (n := f) ({k.castSucc, l.castSucc} : Finset (Fin (m + 1))) := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : TableBUE.IsBlockOn ({k, l} : Finset (Fin m))
      ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := hg
  change TableBUE.IsBlockOn _ _
  rw [uj_coe_uniCast]
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [blkMat_apply_ι (Fin.castSucc_injective m)]
      have hij' : i' ∉ ({k, l} : Finset (Fin m)) ∨ j' ∉ ({k, l} : Finset (Fin m)) := by
        simpa [Fin.castSucc_inj] using hij
      rw [hg' i' j' hij']
      simp [Matrix.one_apply, Fin.castSucc_inj]
    · exact blkMat_apply_of_not_mem_right _ _ (fun y => (Fin.castSucc_lt_last y).ne')
  · exact blkMat_apply_of_not_mem_left _ (fun y => (Fin.castSucc_lt_last y).ne') j

theorem GGSecFiveBPermUniLFrame.range_comp_uniCast_le {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin (m + 1))}
    {σ : ↥(unitarySU 2 f K (m + 1)) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hm : 3 ≤ m) {M : Subgroup G}
    (hM : ∀ c d : Fin (m + 1), c ≠ d → c ≠ π (Fin.last m) → d ≠ π (Fin.last m) →
      ggBlockComm Bs eta {c, d} ≤ M) :
    (σ.comp (uniCast hK m)).range ≤ M := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [MonoidHom.range_eq_map,
    ← SuNsRootGen.iSup_blockSU_pairs hK hq hm ⟨0, by omega⟩ ⟨1, by omega⟩]
  simp only [Subgroup.map_iSup]
  refine iSup_le fun k => iSup_le fun l => iSup_le fun hkl => ?_
  rw [← Subgroup.map_map]
  refine (Subgroup.map_mono (uj_map_uniCast_blockSU_le hK m k l)).trans ?_
  refine (hF.map_blockSU_le_ggBlockComm hK hf hp (by omega)
    ((Fin.castSucc_injective m).ne hkl.1)).trans ?_
  exact hM _ _ (π.injective.ne ((Fin.castSucc_injective m).ne hkl.1))
    (π.injective.ne (Fin.castSucc_lt_last k).ne) (π.injective.ne (Fin.castSucc_lt_last l).ne)

theorem GGSecFiveBPermUniLFrame.range_comp_uniCast_eq [Finite G] [Fact p.Prime] (hp2 : p ≠ 2)
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    (hpq : p ∣ 2 ^ f + 1) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ f = 2)) {Bs XU XO : Subgroup G}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin (m + 1))}
    {σ : ↥(unitarySU 2 f K (m + 1)) →* G} {χL : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK)
    (hJK : (σ.comp (uniCast hK m)).range ≤ XO) :
    (σ.comp (uniCast hK m)).range = (κ.comp (uniEmb E hK m)).range := by
  classical
  set c0 : Multiplicative (ZMod p) := Multiplicative.ofAdd 1 with hc0
  have hc01 : c0 ≠ 1 := by
    intro h
    have h' : Multiplicative.toAdd c0 = Multiplicative.toAdd (1 : Multiplicative (ZMod p)) := by
      rw [h]
    rw [hc0, toAdd_ofAdd, toAdd_one] at h'
    exact one_ne_zero h'
  have hc0p : c0 ^ p = 1 := by
    rw [hc0, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]
  let x : ↥Bs := eta.symm (fun i => if i = π (Fin.last m) then 1 else c0)
  have hx : ∀ i, eta x i = if i = π (Fin.last m) then 1 else c0 := fun i => by
    simp only [x, MulEquiv.apply_symm_apply]
  have hxK : ∀ i : Fin m, eta x (π i.castSucc) = c0 := fun i => by
    rw [hx, if_neg (π.injective.ne (Fin.castSucc_lt_last i).ne)]
  have hcomm : ∀ g : ↥(unitarySU 2 f K m),
      (x : G) * σ (uniCast hK m g) * (x : G)⁻¹ = σ (uniCast hK m g) := by
    intro g
    obtain ⟨D, hD, hDd, hDσ⟩ := hσ.2.2.2 x
    rw [hDσ]
    congr 1
    apply Subtype.ext
    rw [LineU.coe_conjN]
    have hDs : D * (uniCast hK m g : GL (Fin (m + 1)) K) =
        (uniCast hK m g : GL (Fin (m + 1)) K) * D := by
      ext i j
      rw [Units.val_mul, Units.val_mul, hDd, uj_coe_uniCast, Matrix.diagonal_mul,
        Matrix.mul_diagonal]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · rw [hxK i', hxK j', mul_comm]
        · rw [blkMat_apply_of_not_mem_right _ _ (fun y => (Fin.castSucc_lt_last y).ne'),
            Matrix.one_apply_ne (Fin.castSucc_lt_last i').ne]
          simp
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · rw [blkMat_apply_of_not_mem_left _ (fun y => (Fin.castSucc_lt_last y).ne'),
            Matrix.one_apply_ne (Fin.castSucc_lt_last j').ne']
          simp
        · exact mul_comm _ _
    rw [hDs, mul_inv_cancel_right]
  obtain ⟨T, hT, hTκ⟩ := hκ.2.2.2 x
  have hT' : ∀ v : (F × F) × (Fin m → K),
      (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
        (v.1, fun i => ((χK c0 : Kˣ) : K) * v.2 i) := by
    intro v
    rw [hT]
    simp only [hxK]
  have hωF : ((χK c0 : Kˣ) : K) ∉ Set.range (algebraMap F K) := by
    rintro ⟨t, ht⟩
    have hfix : unitaryInvolution K 2 f ((χK c0 : Kˣ) : K) = ((χK c0 : Kˣ) : K) := by
      rw [← ht]
      exact E.fix t
    rw [unitaryInvolution_apply] at hfix
    have hu1 : χK c0 ≠ 1 := fun h => hc01 (hκ.2.2.1 (h.trans (map_one χK).symm))
    have hup : χK c0 ^ p = 1 := by rw [← map_pow, hc0p, map_one]
    have huq : χK c0 ^ (2 ^ f - 1) = 1 := by
      have h1 : χK c0 ^ (2 ^ f) = χK c0 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hfix)
      have h2 : 2 ^ f = (2 ^ f - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
      rw [h2, pow_succ] at h1
      exact mul_right_cancel (h1.trans (one_mul _).symm)
    have hord : orderOf (χK c0) = p := orderOf_eq_prime hup hu1
    have hdvd : p ∣ 2 ^ f - 1 := hord ▸ orderOf_dvd_of_pow_eq_one huq
    have h2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hdvd
      have he : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by
        have := Nat.one_le_two_pow (n := f)
        omega
      rwa [he] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2)
  set J0 := (σ.comp (uniCast hK m)).range with hJ0
  have hJ0K : J0 ≤ κ.range := hκ.2.1 ▸ hJK
  set P : Subgroup (normOmega E m) := J0.comap κ with hPdef
  have hPmap : P.map κ = J0 := Subgroup.map_comap_eq_self hJ0K
  have hperf : Group.IsPerfect ↥(unitarySU 2 f K m) := by
    refine CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f)
      (by rw [hK.card, ← pow_mul, mul_comm]) (by omega) ?_
    intro h
    exact hq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  have hJ0perf : ⁅J0, J0⁆ = J0 := by
    have hc : ⁅(⊤ : Subgroup ↥(unitarySU 2 f K m)), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    rw [hJ0, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hc]
  have hP : P ≤ ⁅P, P⁆ := by
    have h : (⁅P, P⁆).map κ = P.map κ := by rw [Subgroup.map_commutator, hPmap, hJ0perf]
    exact (Subgroup.map_injective hκ.1 h).ge
  have hPT : P ≤ Subgroup.centralizer ({T} : Set (normOmega E m)) := by
    intro s hs
    obtain ⟨g, hg⟩ : κ s ∈ J0 := hs
    have h1 := hTκ s
    have h3 : σ (uniCast hK m g) = κ s := hg
    rw [← hg, MonoidHom.comp_apply, hcomm g, h3] at h1
    have h2 : T * s * T⁻¹ = s := hκ.1 h1.symm
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hPU : P ≤ (uniEmb E hK m).range :=
    le_range_uniEmb_of_commute_scalar E hK hωF hT' hP hPT
  have hle : J0 ≤ (κ.comp (uniEmb E hK m)).range := by
    rw [← hPmap, MonoidHom.range_comp]
    exact Subgroup.map_mono hPU
  have hinj1 : Function.Injective (σ.comp (uniCast hK m)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, hc⟩ := hσ.2.1 (uniCast hK m g) hg
    have hlast := congrFun (congrFun hc (Fin.last m)) (Fin.last m)
    rw [uj_coe_uniCast, blkMat_apply_of_not_mem_left _ (fun y => (Fin.castSucc_lt_last y).ne'),
      Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at hlast
    rw [← hlast, Matrix.diagonal_one, uj_coe_uniCast, ← blkMat_one (ι := Fin.castSucc)] at hc
    have h2 := blkMat_injective (Fin.castSucc_injective m) hc
    exact Subtype.ext (Units.ext h2)
  have hinj2 : Function.Injective (κ.comp (uniEmb E hK m)) :=
    hκ.1.comp (uniEmb_injective E hK m)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hJ0, ← Nat.card_congr (MonoidHom.ofInjective hinj1).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective hinj2).toEquiv]

end Shared

end CFSG.StandardType

end
