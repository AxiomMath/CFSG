module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSL25
public import CFSG.Milestones.ASVolI.C61.PAppCCls2

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Mate
open CFSG.QuasithinUnique.AppC.Mate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : Cfg T M H S L) (m : Mate S T M₀ x)
include C m

theorem exists_involution_over_z :
    ∃ ℓ : ↥L, ℓ * ℓ = 1 ∧ ((C.P.α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = zA := by
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (Mate.V_le_S (m := m) C).trans C.hSN
  have hzE : zA ∈ Eset := (mem_Eset_iff _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hzV : zA ∈ C.P.im (conjR (blockU L) x) := by
    rw [Mate.im_V (m := m) C]; exact (mem_Estd _).2 hzE
  obtain ⟨t, htV, htz⟩ := (C.P.mem_im_pf hVN).1 hzV
  have htS : t ∈ S := Mate.V_le_S (m := m) C htV
  have ht2 : t * t = 1 := by
    have := V_sq (x := x) C htV
    rwa [pow_two] at this
  obtain ⟨ℓ₀, hℓ₀⟩ := C.P.hα ⟨zA, Equiv.Perm.mem_alternatingGroup.2 zA_sign⟩
  have hℓ₀N : (ℓ₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ℓ₀.2
  have hpℓ₀ : C.P.pf (ℓ₀ : G) = zA := by
    rw [C.P.pf_eq hℓ₀N, C.P.hπα (ℓ₀ : G) ℓ₀.2, hℓ₀]
  have hyH : (ℓ₀ : G)⁻¹ * t ∈ H := mul_mem (inv_mem (C56.le_H C.hcs ℓ₀.2)) (C.hSH htS)
  have hyN : (ℓ₀ : G)⁻¹ * t ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem hℓ₀N) (C.hSN htS)
  have hypf : C.P.pf ((ℓ₀ : G)⁻¹ * t) = 1 := by
    rw [C.P.pf_mul (inv_mem hℓ₀N) (C.hSN htS), C.P.pf_inv hℓ₀N, hpℓ₀, htz, inv_mul_cancel]
  have hyQ : (ℓ₀ : G)⁻¹ * t ∈ pCoreOf 2 H := by
    rw [C.P.pf_eq hyN] at hypf
    have h2 := (C.P.hker ⟨_, hyN⟩).1 hypf
    rw [← C.hQ]
    refine ⟨hyH, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have := h2 u hu
    calc u * ((ℓ₀ : G)⁻¹ * t)
        = ((((ℓ₀ : G)⁻¹ * t) * u * ((ℓ₀ : G)⁻¹ * t)⁻¹)) * ((ℓ₀ : G)⁻¹ * t) := by rw [this]
      _ = ((ℓ₀ : G)⁻¹ * t) * u := by group
  obtain ⟨u, hu, d, hd, hyud⟩ := C.exists_UD hyQ
  have huL : u ∈ L := C1.blockQ_le L (C1.blockU_le_blockQ C.hL hu)
  refine ⟨ℓ₀ * ⟨u, huL⟩, ?_, ?_⟩
  · apply Subtype.ext
    show ((ℓ₀ : G) * u) * ((ℓ₀ : G) * u) = 1
    set ℓ : G := (ℓ₀ : G) * u with hℓdef
    have htd : t = ℓ * d := by
      calc t = (ℓ₀ : G) * ((ℓ₀ : G)⁻¹ * t) := by group
        _ = (ℓ₀ : G) * (u * d) := by rw [hyud]
        _ = ℓ * d := by rw [hℓdef]; group
    have hdc : d * ℓ = ℓ * d := blockD_comm C.hj hd (mul_mem ℓ₀.2 huL)
    have hd2 : d * d = 1 := by
      have := (Mate.D_elem (m := m) C).2 d hd
      rwa [pow_two] at this
    calc ℓ * ℓ = ℓ * ℓ * (d * d) := by rw [hd2, mul_one]
      _ = ℓ * (ℓ * d) * d := by group
      _ = ℓ * (d * ℓ) * d := by rw [hdc]
      _ = (ℓ * d) * (ℓ * d) := by group
      _ = t * t := by rw [← htd]
      _ = 1 := ht2
  · have hu' : (⟨u, huL⟩ : ↥L) ∈ C.P.α.ker := by
      rw [C.P.hαk]
      exact (mem_pCore_iff_mem_blockQ _).2 (C1.blockU_le_blockQ C.hL hu)
    rw [map_mul, MonoidHom.mem_ker.1 hu', mul_one, hℓ₀]

theorem blockQ_eq_blockU : blockQ L = blockU L := by
  refine le_antisymm ?_ (C1.blockU_le_blockQ C.hL)
  obtain ⟨ℓ, hℓ, hαℓ⟩ := Mate.exists_involution_over_z (m := m) C
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ C.hL).trans (C1.blockQ_le L)
  have hN : ((blockU L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr (C1.le_normalizer_blockU L)
  have hmem : ∀ q ∈ C.P.α.ker, (q : G) ∈ blockQ L := fun q hq => by
    rw [C.P.hαk] at hq
    exact (mem_pCore_iff_mem_blockQ q).1 hq
  have key := central_cover_trivial (Λ := ↥L) C.hL.1 C.P.α C.P.hα ((blockU L).subgroupOf L)
    (fun u hu => by
      rw [MonoidHom.mem_ker]
      have hu' : u ∈ C.P.α.ker := by
        rw [C.P.hαk]
        exact (mem_pCore_iff_mem_blockQ u).2
          (C1.blockU_le_blockQ C.hL (Subgroup.mem_subgroupOf.1 hu))
      exact hu')
    (fun q hq => by
      have hqQ : (q : G) ∈ pCoreOf 2 H := C56.blockQ_le_pCoreOf C.hcs C.hj (hmem q hq)
      apply Subtype.ext
      have := (Mate.Q_elem (m := m) C).2 (q : G) hqQ
      simpa [pow_two] using this)
    (fun q hq g => Subgroup.mem_subgroupOf.2 (C1.commutator_mem_blockU (hmem q hq) g.2))
    ℓ hℓ hαℓ
  intro q hq
  have hqL : q ∈ L := C1.blockQ_le L hq
  have hk : (⟨q, hqL⟩ : ↥L) ∈ C.P.α.ker := by
    rw [C.P.hαk]
    exact (mem_pCore_iff_mem_blockQ _).2 hq
  exact Subgroup.mem_subgroupOf.1 (key hk)

end Mate

end CFSG.QuasithinUnique.burnsideC56_P.AppC
