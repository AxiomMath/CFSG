module

public import CFSG.Quasithin.Recognition.CertTwoF4Table
public import CFSG.Quasithin.Recognition.CertTwoF4Outer
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal

public noncomputable section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits

theorem TwoLocalLattice.isSylowTwoOf_top {N : Type*} [Group N] (L : TwoLocalLattice N) :
    IsSylowTwoOf L.S ⊤ := by
  refine ⟨le_top, L.sylow.1, ?_⟩
  have e1 : (L.S.subgroupOf ⊤).index = L.S.index := Subgroup.relIndex_top_right L.S
  rw [e1]
  exact L.sylow.2

theorem twoF4H_le_twoF4M
    : twoF4H ≤ twoF4M := extSub_mono titsH_le_titsD

theorem twoF4Lattice_P₁
    : twoF4Lattice.P₁ = twoF4H.subgroupOf twoF4M := by
  ext x
  exact Iff.rfl

theorem twoF4Lattice_P₂
    : twoF4Lattice.P₂ = twoF4N.subgroupOf twoF4M := by
  ext x
  exact Iff.rfl

theorem twoF4AmalgamLocal_of_outBound
    (hOut : TitsOutBound) : TwoF4AmalgamLocal := by
  intro G _ _ H L2 hCase
  obtain ⟨⟨Y, _, hTw, T, M₁, M₂, hpair, ⟨iso⟩⟩, -, -, -, hP2⟩ := hCase
  obtain ⟨e⟩ : Nonempty (Y ≃* MulAut CFSG.Open.quasithinTits) := by
    rcases hTw with ⟨-, h⟩ | ⟨h, -, -⟩
    · exact h
    · omega
  let φ : Y ≃* twoF4M := e.trans (twoF4AutEquiv hOut)
  have hpair' := IsYAmalgamPair.map φ hpair
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow twoF4Lattice.isSylowTwoOf_top hpair'.1
  let f : Y ≃* twoF4M := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) →
      (M.map f.toMonoidHom = twoF4Lattice.P₁ ∨ M.map f.toMonoidHom = twoF4Lattice.P₂) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact twoF4Lattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : M₁.map f.toMonoidHom ≠ M₂.map f.toMonoidHom := fun h =>
    hpair.2.1 (Subgroup.map_injective f.injective h)
  rcases hlocal M₁ (Or.inl rfl) with h1 | h1 <;> rcases hlocal M₂ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  ·
    let ψ : ↥H ≃* ↥twoF4H := ((amalgamIsoφ1 iso).trans (f.subgroupMap M₁)).trans
      ((MulEquiv.subgroupCongr h1).trans ((MulEquiv.subgroupCongr twoF4Lattice_P₁).trans
        (Subgroup.subgroupOfEquivOfLe twoF4H_le_twoF4M)))
    refine TitsLikeVertexFacts.of_vertexEquiv' ψ (fun x => ?_) twoF4VertexFacts
    have h3 := amalgamIso_mem_iff iso x
    have h4 : ∀ y : Y, y ∈ M₂ ↔ ((f y : twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4N := fun y => by
      have h5 : y ∈ M₂ ↔ f y ∈ twoF4Lattice.P₂ := by
        rw [← h2, Subgroup.mem_map_equiv]
        simp
      rw [h5, twoF4Lattice_P₂]
      exact Iff.rfl
    rw [h3, h4]
    exact Iff.rfl
  ·
    exfalso
    let ψ : ↥L2 ≃* ↥twoF4H := (iso.φ2.trans (f.subgroupMap M₂)).trans
      ((MulEquiv.subgroupCongr h2).trans ((MulEquiv.subgroupCongr twoF4Lattice_P₁).trans
        (Subgroup.subgroupOfEquivOfLe twoF4H_le_twoF4M)))
    have := card_pCoreOf_eq_of_mulEquiv ψ
    rw [hP2, card_pCoreOf_twoF4H] at this
    norm_num at this
  · exact absurd (h1.trans h2.symm) hne

end CFSG.Quasithin
