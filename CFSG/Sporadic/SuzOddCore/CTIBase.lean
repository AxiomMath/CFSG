module

public import CFSG.Sporadic.SuzOddCore.CTICheckInputs
public import CFSG.Sporadic.SuzOddCore.OddCore
public import CFSG.Sporadic.SuzOddCore.Restrict

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four

theorem mem_fixList {i : ℕ} (hi : i < 4) (x : Fin 1782) :
    (x : ℕ) ∈ fixList i ↔ suzInv i x = x := by
  rw [fixList, fixedList, List.mem_filter, List.mem_range, beq_iff_eq, rep_suzInv hi x]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨x.2, by rw [h]⟩⟩

theorem fixList_points {i m : ℕ} (hm : (fixList i).length = m) : PointsList 1782 m (fixList i) where
  len := hm
  lt x hx := by
    rw [fixList, fixedList, List.mem_filter, List.mem_range] at hx
    exact hx.1
  nodup := List.nodup_range.filter _

theorem invE_preserves
    {i : ℕ} (hi : i < 4) :
    ∀ g ∈ invE i, ∀ x : Fin 1782, (x : ℕ) ∈ fixList i → (g x : ℕ) ∈ fixList i := by
  intro g hg x hx
  rw [mem_fixList hi] at hx ⊢
  rw [invE_eq_centM hi] at hg
  have hc := Subgroup.mem_centralizer_singleton_iff.1 hg.1
  have := congrArg (fun σ : Equiv.Perm (Fin 1782) => σ x) hc
  simp only [Equiv.Perm.mul_apply, hx] at this
  exact this.symm

@[expose] def cRho
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m) :
    invE i →* Equiv.Perm (Fin m) :=
  (fixList_points hm).restrHom (invE i) (invE_preserves hi)

@[expose] def innerGenE {i : ℕ} (hi : i < 4) (k : ℕ) : invE i :=
  if hk : k < (invInnerGenArrs i).size then ⟨invInnerGen i k, invInnerGen_mem hi hk⟩ else 1

theorem tabRep_kGens
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m) {k : ℕ}
    (hk : k < (invInnerGenArrs i).size) :
    TabRep (kGens i)[k]! (cRho hi hm (innerGenE hi k)) := by
  have h1 : (kGens i)[k]! = restrictArr (fixList i) (invInnerGenArrs i)[k]! := by
    rw [kGens, getElem!_pos _ k (by simpa using hk), Array.getElem_map,
      ← getElem!_pos _ k hk]
  rw [h1]
  refine (fixList_points hm).tabRep_restrHom _ _ _ ?_
  simp only [innerGenE, hk, ↓reduceDIte]
  exact rep_invInnerGen hi hk

@[expose] def kGenSet
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m) :
    Set (Equiv.Perm (Fin m)) :=
  {g | ∃ k < (invInnerGenArrs i).size, cRho hi hm (innerGenE hi k) = g}

theorem invE_eq_closure {i : ℕ} (hi : i < 4) :
    invE i = Subgroup.closure {g | ∃ k < (invInnerGenArrs i).size, invInnerGen i k = g} := by
  rw [invE, RawSchreierDatum.originalSubgroup]
  apply congrArg Subgroup.closure
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hg
    obtain ⟨⟨k, hk⟩, rfl⟩ := (schreier_vector_mem_toList_iff_get _ g).1 hg
    have hk' : k < (invInnerGenArrs i).size := hk
    refine ⟨k, hk', ?_⟩
    exact (rep_invInnerGen hi hk').unique ((invInnerChain_arrays hi).orig ⟨k, hk⟩)
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < (invInnerChain i).originalCount := hk
    rw [(rep_invInnerGen hi hk).unique ((invInnerChain_arrays hi).orig ⟨k, hk'⟩)]
    exact schreier_vector_get_mem_toList _ _

theorem range_cRho
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m) :
    (cRho hi hm).range = Subgroup.closure (kGenSet hi hm) := by
  have htop : (⊤ : Subgroup (invE i)) = Subgroup.closure
      (((↑) : invE i → Equiv.Perm (Fin 1782)) ⁻¹'
        {g | ∃ k < (invInnerGenArrs i).size, invInnerGen i k = g}) := by
    have := Subgroup.closure_closure_coe_preimage
      (k := {g | ∃ k < (invInnerGenArrs i).size, invInnerGen i k = g})
    rw [← invE_eq_closure hi] at this
    exact this.symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext σ
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq, kGenSet]
  constructor
  · rintro ⟨g, ⟨k, hk, hkg⟩, rfl⟩
    refine ⟨k, hk, ?_⟩
    apply congrArg (cRho hi hm)
    apply Subtype.ext
    simp only [innerGenE, hk, ↓reduceDIte]
    exact hkg
  · rintro ⟨k, hk, rfl⟩
    exact ⟨innerGenE hi k, ⟨k, hk, by simp [innerGenE, hk]⟩, rfl⟩

theorem cRho_enumerates
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m) {E : Enum}
    (hE : enumOK m (kGens i) E = true) : Enumerates (cRho hi hm).range E.tabs.toList := by
  rw [range_cRho]
  refine enumerates_closure ?_ ?_ hE
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [kGens] using hk, tabRep_kGens hi hm hk⟩
  · intro k hk
    have hk' : k < (invInnerGenArrs i).size := by simpa [kGens] using hk
    exact ⟨_, ⟨k, hk', rfl⟩, tabRep_kGens hi hm hk'⟩

theorem card_ker_cRho
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m) :
    Nat.card (cRho hi hm).ker * Nat.card (cRho hi hm).range = invInnerOrders.getD i 0 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (cRho hi hm).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (cRho hi hm)).toEquiv,
    card_invE hi] at h
  rw [h, mul_comm]

theorem suzInv_mem_ker
    {i m : ℕ} (hi : i < 4) (hm : (fixList i).length = m)
    (ht : suzInv i ∈ invE i) : (⟨suzInv i, ht⟩ : invE i) ∈ (cRho hi hm).ker := by
  rw [MonoidHom.mem_ker, cRho, PointsList.restrHom_eq_one_iff]
  intro x hx
  exact (mem_fixList hi x).1 hx

theorem suzInv_mem_invE
    {i : ℕ} (hi : i < 4) (hM : suzInv i ∈ suzM) : suzInv i ∈ invE i := by
  rw [invE_eq_centM hi]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hM⟩

end CFSG.Sporadic.SuzOddCore
