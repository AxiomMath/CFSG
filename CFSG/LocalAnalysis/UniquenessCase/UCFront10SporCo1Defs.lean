module

public import CFSG.Sporadic.Co1.Cover.Iota
public import Certificates.Data.CFSGNative.Co1K105.Check
public import CFSG.Sporadic.Co1.Cover.FoxProof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1.Cover CFSG.Blueprint CFSG.KD.Co1K105

@[expose] noncomputable def t24Gen (i : Fin 4) : PM24 :=
  eltPos (CFSG.Monster.Schur.M24.gen 0) (CFSG.Monster.Schur.M24.gen 1)
    (wordOf (t24Codes.getD i.val (0, 0)).1 (t24Codes.getD i.val (0, 0)).2)

@[expose] noncomputable def t24 : Subgroup PM24 :=
  Subgroup.closure (Set.range t24Gen)

@[expose] noncomputable def co1Sylow :
    Subgroup NativeSporadic.Co1 :=
  (t24.comap (SemidirectProduct.rightHom : SM24 →* PM24)).map theta

theorem epsHom_range_le_co1Sylow :
    epsHom.range ≤ co1Sylow := by
  rintro _ ⟨x, rfl⟩
  refine ⟨SemidirectProduct.inl x, ?_, theta_inl x⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, SemidirectProduct.rightHom_inl]
  exact Subgroup.one_mem _

theorem theta_mem_co1Sylow_iff
    (s : SM24) :
    theta s ∈ co1Sylow ↔ s.right ∈ t24 := by
  constructor
  · rintro ⟨s', hs', he⟩
    rw [theta_injective he] at hs'
    exact hs'
  · intro h
    exact ⟨s, h, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
