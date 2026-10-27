module

public import CFSG.Quasithin.Vol2.Ch1Sec3L42L5
public import CFSG.Quasithin.Vol2.Ch1Sec3L42Gen

public section

namespace CFSG.Quasithin.L139L42

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique.Vol2Native.A312L (slEquivStatedProj)

theorem exists_inner_l5_of_isPSL {X : Type} [Group X] [Finite X] (hX : IsPSL 5 2 1 X)
    {P : Subgroup X} (hP : IsParabolic2 (⊤ : Subgroup X) P)
    (h4 : IsPSL 4 2 1 (ModO2 (perfectCore P))) (β : MulAut X)
    (hβ : ∀ x ∈ perfectCore P, β x ∈ perfectCore P) :
    ∃ b ∈ perfectCore P, ∀ x ∈ perfectCore P,
      (β x)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 (perfectCore P) := by
  classical
  obtain ⟨-, F, _, _, hF1, ⟨e₀⟩⟩ := hX
  have hF : Nat.card F = 2 := by simpa using hF1
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hF1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e₁ : X ≃* SpecialLinearGroup (Fin 5) F := e₀.trans (slEquivStatedProj hF 5).symm
  obtain ⟨-, S, hS, hNS⟩ := hP
  have hS' := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hS
  let T : Sylow 2 X := hS'.1.toSylow hS'.2
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 5) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 5) F)
    (T.mapSurjective (f := e₁.toMonoidHom) e₁.surjective) U₀
  let e : X ≃* SpecialLinearGroup (Fin 5) F := e₁.trans (MulAut.conj g)
  have hSe : S.map e.toMonoidHom = unitriangular 5 F := by
    have h1 := congrArg (fun R : Sylow 2 (SpecialLinearGroup (Fin 5) F) =>
      (R : Subgroup (SpecialLinearGroup (Fin 5) F))) hg
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    have h2 : (S.map e₁.toMonoidHom).map (MulAut.conj g).toMonoidHom = unitriangular 5 F := by
      rw [← hU₀]
      exact Eq.trans rfl h1
    rw [← h2, Subgroup.map_map]
    rfl
  have hUP : upperTriangular 5 F ≤ P.map e.toMonoidHom := by
    rw [← normalizer_unitriangular, ← hSe, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono fun x hx => hNS ⟨Subgroup.mem_top x, hx⟩
  have hPC : perfectCore (P.map e.toMonoidHom) = (perfectCore P).map e.toMonoidHom :=
    (map_perfectCore _ _).symm
  have h4' : IsPSL 4 2 1 (ModO2 (perfectCore (P.map e.toMonoidHom))) := by
    rw [hPC]
    exact IsPSL.of_mulEquiv (modO2MapEquiv e _).symm h4
  set β' : MulAut (SpecialLinearGroup (Fin 5) F) := e.symm.trans (β.trans e) with hβ'
  have hβ'B : ∀ y ∈ perfectCore (P.map e.toMonoidHom),
      β' y ∈ perfectCore (P.map e.toMonoidHom) := by
    rw [hPC]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨β x, hβ x hx, ?_⟩
    simp [hβ']
  have h := exists_inner_l5 hF hUP h4' β' hβ'B
  rw [hPC] at h
  exact exists_inner_of_map e h

theorem exists_inner_l5_sub {Q : Type} [Group Q] [Finite Q] {K P B : Subgroup Q}
    (hK : IsPSL 5 2 1 ↥K) (hP : IsParabolic2 K P) (hB : B = perfectCore P)
    (h4 : IsPSL 4 2 1 (ModO2 B)) {g : Q} (hgK : g ∈ Subgroup.normalizer (K : Set Q))
    (hgB : g ∈ Subgroup.normalizer (B : Set Q)) :
    ∃ b ∈ B, ∀ x ∈ B, (g * x * g⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B := by
  have hPK : P ≤ K := hP.1
  have hBK : B ≤ K := hB ▸ (perfectCore_le P).trans hPK
  refine exists_inner_of_sub hBK hgK ?_
  have hBc : B.subgroupOf K = perfectCore (P.subgroupOf K) := by
    rw [perfectCore_subgroupOf hPK, hB]
  have h4' : IsPSL 4 2 1 (ModO2 (perfectCore (P.subgroupOf K))) := by
    rw [← hBc]
    exact IsPSL.of_mulEquiv (modO2SubgroupOfEquiv hBK).symm h4
  have hβ : ∀ x ∈ perfectCore (P.subgroupOf K),
      L139A5.conjSub hgK x ∈ perfectCore (P.subgroupOf K) := by
    rw [← hBc]
    exact conjSub_mem_subgroupOf hgK hgB
  have h := exists_inner_l5_of_isPSL hK (isParabolic2_subgroupOf hP) h4' (L139A5.conjSub hgK) hβ
  rwa [← hBc] at h

end CFSG.Quasithin.L139L42
