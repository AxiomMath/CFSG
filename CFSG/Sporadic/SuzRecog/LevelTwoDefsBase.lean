
module

public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
public import CFSG.Sporadic.SuzRecog.Q3AGraph
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.Sporadic.SuzRecog.LevelTwo

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData

theorem getElem!_map_nat {L : Array (Array ℕ)} (f : Array ℕ → Array ℕ) {i : ℕ} (hi : i < L.size) :
    (L.map f)[i]! = f L[i]! := by
  rw [getElem!_pos (L.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos L i hi]

theorem Rep.of_eqA {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (hu : Rep n u g)
    (h : eqA n t u = true) : Rep n t g := fun x => by
  rw [← hu x]
  have := allLt_spec h x.2
  simpa [beq_iff_eq] using this

theorem eq_of_conjEq {g gi a b : Array ℕ} {G A B : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (hgi : Rep 1782 gi G⁻¹) (ha : Rep 1782 a A) (hb : Rep 1782 b B)
    (h : conjEq g gi a b = true) : B = G * A * G⁻¹ := by
  rw [conjEq] at h
  have := eq_of_eqA hb (rep_compA hg (rep_compA ha hgi)) h
  rw [this, mul_assoc]

theorem rep_of_conjEq {g gi a b : Array ℕ} {G A : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (hgi : Rep 1782 gi G⁻¹) (ha : Rep 1782 a A) (h : conjEq g gi a b = true) :
    Rep 1782 b (G * A * G⁻¹) := by
  rw [conjEq] at h
  have := Rep.of_eqA (rep_compA hg (rep_compA ha hgi)) h
  rwa [← mul_assoc] at this

@[expose] noncomputable def x1 : Equiv.Perm (Fin 1782) := permC 1782 gens[0]!

@[expose] noncomputable def x2 : Equiv.Perm (Fin 1782) := permC 1782 gens[1]!

@[expose] noncomputable def xGroup : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure {x1, x2}

theorem gens_size : gens.size = 2 := rfl

theorem xStrongArrs_size : xStrongArrs.size = 9 := by simp [xStrongArrs]

theorem gensInv_get {s : ℕ} (hs : s < 2) : gensInv[s]! = invCand 1782 gens[s]! :=
  getElem!_map_nat _ (by rw [gens_size]; exact hs)

@[expose] def xBaseFin : List (Fin 1782) := xBase.map (pt 1782)

theorem xBaseFin_eq : xBaseFin = [1, 15, 33, 20, 0] := by decide

theorem xBaseFin_nodup : xBaseFin.Nodup := by rw [xBaseFin_eq]; decide

theorem xBaseFin_vals : (xBaseFin.map Fin.val).toArray = xBase.toArray := by
  rw [xBaseFin_eq]
  rfl

theorem gens_le_strong : gens.size ≤ xStrongArrs.size := by
  rw [gens_size, xStrongArrs_size]; norm_num

@[expose] noncomputable def xChain : RawSchreierDatum 1782 :=
  rawOfArrays 1782 (by norm_num) gens xStrongArrs gens_le_strong xBaseFin xBaseFin_nodup xWords

theorem xChain_originalCount : xChain.originalCount = 2 := rfl

theorem xChain_original_get (i : Fin xChain.originalCount) :
    xChain.original.get i = permC 1782 gens[(i : ℕ)]! :=
  rawOfArrays_original_get i

theorem mem_xChain_original {g : Equiv.Perm (Fin 1782)} :
    g ∈ xChain.original.toList ↔ g = x1 ∨ g = x2 := by
  rw [schreier_vector_mem_toList_iff_get]
  constructor
  · rintro ⟨i, rfl⟩
    rw [xChain_original_get]
    have hi : (i : ℕ) < 2 := i.2
    interval_cases h : (i : ℕ)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by rw [xChain_originalCount]; norm_num⟩, by rw [xChain_original_get]; rfl⟩
    · exact ⟨⟨1, by rw [xChain_originalCount]; norm_num⟩, by rw [xChain_original_get]; rfl⟩

theorem xChain_originalSubgroup : xChain.originalSubgroup = xGroup := by
  rw [RawSchreierDatum.originalSubgroup, xGroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_xChain_original

theorem fp_eq_of_rep {a b : Array ℕ} {G : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a G)
    (hb : Rep 1782 b G) : fp a = fp b := by
  simp only [fp]
  rw [ha.apply (by norm_num), hb.apply (by norm_num), ha.apply (by norm_num : 333 < 1782),
    hb.apply (by norm_num : 333 < 1782), ha.apply (by norm_num : 901 < 1782),
    hb.apply (by norm_num : 901 < 1782), ha.apply (by norm_num : 1500 < 1782),
    hb.apply (by norm_num : 1500 < 1782), ha.apply (by norm_num : 1234 < 1782),
    hb.apply (by norm_num : 1234 < 1782), ha.apply (by norm_num : 77 < 1782),
    hb.apply (by norm_num : 77 < 1782)]

theorem card_Nrho1_le :
    Nat.card ↥(Subgroup.normalizer (Q3A.base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) ≤
      19595520 := by
  have hmul := Q3A.card_vtx_mul
  have hpos : Nat.card Q3A.Vtx ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact absurd hmul (by norm_num)
  have : Finite Q3A.Vtx := Nat.finite_of_card_ne_zero hpos
  have hinj : Function.Injective fun i : Fin 22880 => Q3A.vtx i.1 :=
    fun i j h => Fin.ext (Q3A.vtx_injective i.2 j.2 h)
  have hle : 22880 ≤ Nat.card Q3A.Vtx := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  by_contra hlt
  have : 22880 * 19595521 ≤ Nat.card Q3A.Vtx *
      Nat.card ↥(Subgroup.normalizer (Q3A.base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) :=
    Nat.mul_le_mul hle (by omega)
  omega

end CFSG.Sporadic.SuzRecog.LevelTwo
