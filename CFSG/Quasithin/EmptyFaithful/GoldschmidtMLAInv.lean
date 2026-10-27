module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLACarrier

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem conjByElt_mul' (x y : G) (K : Subgroup G) :
    conjByElt (x * y) K = conjByElt x (conjByElt y K) := by
  ext z
  simp only [mem_conjByElt, mul_inv_rev, mul_assoc]

theorem conjByElt_one' (K : Subgroup G) : conjByElt 1 K = K := by
  ext z
  simp [mem_conjByElt]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem mem_normalizer_of_conjByElt_eq {g : G} {K : Subgroup G} (h : conjByElt g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have h2 : conjByElt g⁻¹ K = K := by
    conv_lhs => rw [← h]
    rw [← conjByElt_mul', inv_mul_cancel, conjByElt_one']
  exact mem_normalizer_of_map_le (le_of_eq h) (le_of_eq h2)

theorem conjByElt_eq_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : conjByElt g K = K := by
  ext z
  rw [mem_conjByElt]
  have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z
  simpa using this.symm

theorem inf_le_normalizer {S MZ L P : Subgroup G} (hSM : S ≤ MZ) (hPL : IsSylowTwoOf P L)
    (hPS : P ≤ S)
    (hOG : ∀ H : Subgroup G, P ≤ H → H ≤ L → H ≠ L → H ≤ Subgroup.normalizer (P : Set G))
    (hLM : ¬ L ≤ MZ) : MZ ⊓ L ≤ Subgroup.normalizer (P : Set G) := by
  refine hOG (MZ ⊓ L) (le_inf (hPS.trans hSM) hPL.1) inf_le_right ?_
  intro h
  apply hLM
  rw [← h]
  exact inf_le_left

theorem pCoreOf_inf_eq [Finite G] {S MZ L P : Subgroup G} (hSM : S ≤ MZ) (hPL : IsSylowTwoOf P L)
    (hPS : P ≤ S) (hN : MZ ⊓ L ≤ Subgroup.normalizer (P : Set G)) : pCoreOf 2 (MZ ⊓ L) = P := by
  have hPM : P ≤ MZ ⊓ L := le_inf (hPS.trans hSM) hPL.1
  have hSyl : IsSylowTwoOf P (MZ ⊓ L) := A4.isSylowTwoOf_mono hPL hPM inf_le_right
  exact le_antisymm hSyl.pCoreOf_le (le_pCoreOf_of_le_normalizer 2 hPM hN hPL.2.1)

theorem normalizer_stable [Finite G] {MZ L P : Subgroup G} (hpc : pCoreOf 2 (MZ ⊓ L) = P) {n : G}
    (hnM : n ∈ MZ) (hnL : n ∈ Subgroup.normalizer (L : Set G)) :
    n ∈ Subgroup.normalizer (P : Set G) ∧
      n ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) := by
  have h1 : n ∈ Subgroup.normalizer ((MZ ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hnM) hnL
  have h2 : n ∈ Subgroup.normalizer (P : Set G) := by
    have := normalizer_le_normalizer_pCoreOf 2 (MZ ⊓ L) h1
    rwa [hpc] at this
  exact ⟨h2, mem_normalizer_inf hnL (Subgroup.le_normalizer h2)⟩

theorem normalizes_conjClosure {S MZ L B : Subgroup G} (hSM : S ≤ MZ)
    (hstar : ∀ m ∈ MZ, ∃ s ∈ S, conjByElt m L = conjByElt s L)
    (hB : ∀ n ∈ MZ, n ∈ Subgroup.normalizer (L : Set G) →
      n ∈ Subgroup.normalizer (B : Set G)) :
    MZ ≤ Subgroup.normalizer ((conjClosure B S : Subgroup G) : Set G) := by
  have key : ∀ m ∈ MZ, ∀ s ∈ S, ∀ b ∈ B, m * (s * b * s⁻¹) * m⁻¹ ∈ conjClosure B S := by
    intro m hm s hs b hb
    obtain ⟨s', hs', hms⟩ := hstar (m * s) (MZ.mul_mem hm (hSM hs))
    have hnL : s'⁻¹ * (m * s) ∈ Subgroup.normalizer (L : Set G) := by
      refine mem_normalizer_of_conjByElt_eq ?_
      rw [conjByElt_mul', hms, ← conjByElt_mul', inv_mul_cancel, conjByElt_one']
    have hnM : s'⁻¹ * (m * s) ∈ MZ :=
      MZ.mul_mem (MZ.inv_mem (hSM hs')) (MZ.mul_mem hm (hSM hs))
    have hb' := (Subgroup.mem_normalizer_iff.mp (hB _ hnM hnL) b).mp hb
    have e : m * (s * b * s⁻¹) * m⁻¹ =
        s' * ((s'⁻¹ * (m * s)) * b * (s'⁻¹ * (m * s))⁻¹) * s'⁻¹ := by group
    rw [e]
    exact mem_conjClosure hs' hb'
  have hmap : ∀ m ∈ MZ, (conjClosure B S).map (MulAut.conj m).toMonoidHom ≤ conjClosure B S := by
    intro m hm
    rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun s hs b hb => ?_
    exact key m hm s hs b hb
  intro m hm
  exact mem_normalizer_of_map_le (hmap m hm) (hmap m⁻¹ (MZ.inv_mem hm))

theorem inf_pCoreOf_le [Finite G] {X L P : Subgroup G} (hLX : L ≤ X) (hP : IsSylowTwoOf P L) :
    pCoreOf 2 X ⊓ L ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : L ≤ Subgroup.normalizer ((pCoreOf 2 X ⊓ L : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (le_normalizer_pCoreOf 2 X (hLX hx)) (Subgroup.le_normalizer hx)
  have hp : IsPGroup 2 ↥(pCoreOf 2 X ⊓ L) := (pCoreOf_isPGroup 2 X).to_le inf_le_left
  exact (le_pCoreOf_of_le_normalizer 2 inf_le_right hn hp).trans hP.pCoreOf_le

end CFSG.Quasithin.GoldMLA
