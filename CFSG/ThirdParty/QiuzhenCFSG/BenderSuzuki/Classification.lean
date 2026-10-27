module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.Converse.StronglyEmbedded

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki

open PFAppendixIII MatrixGroups

universe u v

/-! ### Transport along an isomorphism

Strong embedding is invariant under isomorphism, so the property may be checked in any
concrete model of the group.  Phrased by involutions it transports with no cardinality
argument: an isomorphism matches involutions with involutions. -/

private theorem isInvolution_map_iff {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (x : G) : _root_.CFSG.IsInvolution (e x) ↔ _root_.CFSG.IsInvolution x := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h1 (by rw [hx, map_one]), e.injective ?_⟩
    rw [map_pow, h2, map_one]
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h1 (e.injective (by rw [hx, map_one])), ?_⟩
    rw [← map_pow, h2, map_one]

private theorem conj_comp {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) (g : G) :
    (MulAut.conj (e g)).toMonoidHom.comp (e : G →* H)
      = (e : G →* H).comp (MulAut.conj g).toMonoidHom := by
  ext x; simp

private theorem map_conj_comm {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H)
    (M : Subgroup G) (g : G) :
    (M.map (MulAut.conj g).toMonoidHom).map (e : G →* H)
      = (M.map (e : G →* H)).map (MulAut.conj (e g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, conj_comp]

private theorem isStronglyEmbedded_map {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) {M : Subgroup G} (hM : _root_.IsStronglyEmbedded M) :
    _root_.IsStronglyEmbedded (M.map (e : G →* H)) := by
  obtain ⟨hne, ⟨x, hxM, hx⟩, hno⟩ := hM
  refine ⟨?_, ⟨e x, ⟨x, hxM, rfl⟩, (isInvolution_map_iff e x).2 hx⟩, ?_⟩
  · intro htop
    refine hne ?_
    have h := Subgroup.comap_map_eq_self_of_injective (f := (e : G →* H)) e.injective M
    rw [htop, Subgroup.comap_top] at h
    exact h.symm
  · intro h hh y hy
    obtain ⟨g₀, rfl⟩ : ∃ g₀ : G, e g₀ = h := ⟨e.symm h, by simp⟩
    have hg : g₀ ∉ M := fun hc => hh ⟨g₀, hc, rfl⟩
    rw [← map_conj_comm e M g₀, ← Subgroup.map_inf _ _ (e : G →* H) e.injective] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact fun hinv => hno g₀ hg z hz ((isInvolution_map_iff e z).1 hinv)

/-! ### Each group in the conclusion has a strongly embedded subgroup -/

/-- `PSL(2, 2ⁿ)` has a strongly embedded subgroup: the Borel subgroup. -/
private theorem exists_stronglyEmbedded_psl2Model (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Subgroup (PSL2Model n), _root_.IsStronglyEmbedded M :=
  ⟨Converse.PBorel (BinaryGaloisField n), Converse.stronglyEmbedded_PSL2_binary n hn⟩

/-- `Sz(2^(2n+1))` has a strongly embedded subgroup: the stabilizer of a point of the
ovoid, carried across `szModel_eq_suzukiMatrixGroup`. -/
private theorem exists_stronglyEmbedded_szModel (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : Subgroup (SzModel n), _root_.IsStronglyEmbedded M := by
  haveI : NeZero n := ⟨by omega⟩
  have e : (SzModel n) ≃* (SuzukiMatrixGroup n) :=
    MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup n)
  exact ⟨(Converse.szHstab n).map (e.symm : _ →* _),
    isStronglyEmbedded_map e.symm (Converse.stronglyEmbedded_Sz n)⟩

/-- `PSU₃(2ⁿ)` has a strongly embedded subgroup: the stabilizer of an isotropic point,
carried across `projectiveSpecialUnitary_equiv_psu3Model`. -/
private theorem exists_stronglyEmbedded_psu3Model (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Subgroup (PSU3Model n), _root_.IsStronglyEmbedded M := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_psu3Model (Converse.uform n) n hn rfl
    (Converse.card_UField n (by omega)) (Converse.card_fixed_UField n (by omega))
  obtain ⟨M, hM⟩ := Converse.stronglyEmbedded_PSU3 n hn
  exact ⟨M.map (e : _ →* _), isStronglyEmbedded_map e hM⟩

/-- **The converse of the Bender--Suzuki theorem.**  Every group the classification
allows really does have a strongly embedded subgroup, so the classification omits
nothing. -/
public theorem exists_stronglyEmbedded_of_isSimpleBenderGroup {X : Type u} [Group X]
    [Finite X] (h : _root_.CFSG.IsSimpleBenderGroup X) :
    ∃ M : Subgroup X, _root_.IsStronglyEmbedded M := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · obtain ⟨M, hM⟩ := exists_stronglyEmbedded_psl2Model n hn
    exact ⟨M.map (e.symm : _ →* _), isStronglyEmbedded_map e.symm hM⟩
  · obtain ⟨M, hM⟩ := exists_stronglyEmbedded_szModel n hn
    exact ⟨M.map (e.symm : _ →* _), isStronglyEmbedded_map e.symm hM⟩
  · obtain ⟨M, hM⟩ := exists_stronglyEmbedded_psu3Model n hn
    exact ⟨M.map (e.symm : _ →* _), isStronglyEmbedded_map e.symm hM⟩

/-- **The Bender--Suzuki theorem, as an equivalence.**  A finite simple group has a
strongly embedded subgroup exactly when it is `PSL(2, 2ⁿ)` with `n ≥ 2`, `Sz(2^(2n+1))`
with `n ≥ 1`, or `PSU₃(2ⁿ)` with `n ≥ 2`.

Left to right is `bender_suzuki`; right to left is
`exists_stronglyEmbedded_of_isSimpleBenderGroup`. -/
public theorem isSimpleBenderGroup_iff_exists_stronglyEmbedded {X : Type u} [Group X]
    [Finite X] [IsSimpleGroup X] :
    (∃ M : Subgroup X, _root_.IsStronglyEmbedded M) ↔ _root_.CFSG.IsSimpleBenderGroup X := by
  constructor
  · rintro ⟨M, hM⟩
    exact bender_suzuki M hM
  · exact exists_stronglyEmbedded_of_isSimpleBenderGroup

end CFSG.BenderSuzuki
