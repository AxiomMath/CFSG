module

public import CFSG.Milestones.ASVolI.A3Aut.Model

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique.Setup.X6 CFSG.ABGLocalTools

theorem burnsideAut_solvBorel_of_isSylow {X M : Type} [Group X] [Group M] [Finite X] [Finite M]
    (e : X ≃* M) {U₀ : Subgroup M} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (h : burnsideAut_SolvBorel M U₀) {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) : burnsideAut_SolvBorel X S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsSylowOf 2 (S.map e.toMonoidHom) ⊤ := by
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hS)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj hS'
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = S.map e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  set φ : X ≃* M := e.trans (MulAut.conj k).symm with hφ
  have hφU : S.map φ.toMonoidHom = U₀ := by
    have : S.map φ.toMonoidHom = (S.map e.toMonoidHom).map (MulAut.conj k).symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [this, ← hconj]
    exact map_symm_map (MulAut.conj k) U₀
  exact burnsideAut_solvBorel_of_mulEquiv φ (hφU ▸ h)

theorem burnsideAut_not_isSolvable_of_perfect_hom {P G : Type*} [Group P] [Group G]
    [Group.IsPerfect P] (φ : P →* G) {g : P} (hg : φ g ≠ 1) {M : Subgroup G}
    (hM : φ.range ≤ M) : ¬ Group.IsSolvable ↥M := by
  intro hs
  have h1 : Group.IsSolvable ↥φ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM)
  have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  have : Nontrivial ↥φ.range :=
    ⟨⟨⟨φ g, g, rfl⟩, 1, fun h => hg (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥φ.range h1

theorem burnsideAut_not_isSolvable_of_perfect_le {G : Type*} [Group G] {L M : Subgroup G}
    (hL : commutator ↥L = ⊤) {g : G} (hgL : g ∈ L) (hg : g ≠ 1) (hLM : L ≤ M) :
    ¬ Group.IsSolvable ↥M := by
  have : Group.IsPerfect ↥L := ⟨hL⟩
  refine burnsideAut_not_isSolvable_of_perfect_hom L.subtype (g := ⟨g, hgL⟩) hg ?_
  rwa [Subgroup.range_subtype]

theorem burnsideAut_solvBorel_of_comap {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (hker : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a)
    {V B : Subgroup G} (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ Y : Subgroup G, V ≤ Y → Group.IsSolvable ↥Y → Y ≤ B) :
    burnsideAut_SolvBorel Q (V.map π) := by
  intro Y hVY hY
  set Y' : Subgroup G := Y.comap π with hY'
  have hVY' : V ≤ Y' := fun v hv => hVY ⟨v, hv, rfl⟩
  have hY's : Group.IsSolvable ↥Y' := by
    have hkerY : π.ker ≤ Y' := fun k hk => by
      change π k ∈ Y
      rw [hk]
      exact Y.one_mem
    set f : ↥Y' →* ↥Y := (π.comp Y'.subtype).codRestrict Y (fun y => y.2) with hf
    set k : ↥(π.ker.subgroupOf Y') →* ↥Y' := (π.ker.subgroupOf Y').subtype with hk
    have hks : Group.IsSolvable ↥(π.ker.subgroupOf Y') := by
      haveI : IsMulCommutative ↥(π.ker.subgroupOf Y') :=
        ⟨⟨fun a b => Subtype.ext (Subtype.ext (hker _ a.2 _ b.2))⟩⟩
      infer_instance
    refine Group.isSolvable_of_ker_le_range k f ?_
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have : π x = 1 := congrArg Subtype.val hx
    exact this
  have hle := h Y' hVY' hY's
  intro q hq
  obtain ⟨g, rfl⟩ := hπ q
  exact Subgroup.le_normalizer_map π ⟨g, hBV (hle hq), rfl⟩

end CFSG.ASVolI
