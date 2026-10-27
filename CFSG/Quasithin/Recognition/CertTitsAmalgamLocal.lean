module

public import CFSG.Quasithin.Recognition.CertTitsVertex
public import CFSG.Quasithin.Recognition.CertVertexTransport
public import CFSG.Quasithin.Recognition.CertTitsBridge

public noncomputable section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits

theorem exists_mulEquiv_map_sylow {N : Type*} [Group N] [Finite N] {S T : Subgroup N}
    (hS : IsSylowTwoOf S ⊤) (hT : IsSylowTwoOf T ⊤) :
    ∃ ρ : N ≃* N, T.map ρ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hpS, hidxS'⟩ := hS
  obtain ⟨-, hpT, hidxT'⟩ := hT
  have e1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have e2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  have hidxS : ¬ 2 ∣ S.index := by rwa [e1] at hidxS'
  have hidxT : ¬ 2 ∣ T.index := by rwa [e2] at hidxT'
  let S₀ : Sylow 2 N := hpS.toSylow hidxS
  let T₀ : Sylow 2 N := hpT.toSylow hidxT
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq N T₀ S₀
  refine ⟨MulAut.conj k, ?_⟩
  have h1 := congrArg (fun P : Sylow 2 N => (P : Subgroup N)) hk
  simp only [Sylow.coe_subgroup_smul] at h1
  rw [← show (S₀ : Subgroup N) = S from IsPGroup.toSylow_coe _ _, ← h1]
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem card_pCoreOf_eq_card_pCore {X : Type*} [Group X] (L : Subgroup X) :
    Nat.card (pCoreOf 2 L) = Nat.card (Open.pCore 2 ↥L) :=
  Subgroup.card_map_of_injective L.subtype_injective

theorem card_pCoreOf_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    {K : Subgroup G'} (e : ↥H ≃* ↥K) : Nat.card (pCoreOf 2 H) = Nat.card (pCoreOf 2 K) := by
  rw [card_pCoreOf_eq_card_pCore, card_pCoreOf_eq_card_pCore,
    ← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e, Subgroup.card_map_of_injective e.injective]

theorem card_pCoreOf_titsH
    : Nat.card (pCoreOf 2 titsH) = 512 := by
  rw [pCoreOf_titsH, titsQJ_facts.2.2.2]

theorem titsHD_inf_titsND
    : titsHD ⊓ titsND = titsSD := by
  ext x
  rw [Subgroup.mem_inf]
  change (↑x ∈ titsH ∧ ↑x ∈ titsN) ↔ ↑x ∈ titsS
  rw [← Subgroup.mem_inf, titsH_inf_titsN]

@[expose] def amalgamIsoφ1 {G Y : Type u} [Group G] [Group Y] {H L2 : Subgroup G}
    {M₁ M₂ : Subgroup Y}
    (iso : (RankTwoAmalgam.ofSubgroups H L2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    ↥H ≃* ↥M₁ := iso.φ1

@[expose] def amalgamIsoφ12 {G Y : Type u} [Group G] [Group Y] {H L2 : Subgroup G}
    {M₁ M₂ : Subgroup Y}
    (iso : (RankTwoAmalgam.ofSubgroups H L2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    ↥(H ⊓ L2) ≃* ↥(M₁ ⊓ M₂) := iso.φ12

theorem amalgamIso_comm {G Y : Type u} [Group G] [Group Y] {H L2 : Subgroup G}
    {M₁ M₂ : Subgroup Y}
    (iso : (RankTwoAmalgam.ofSubgroups H L2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (g : ↥(H ⊓ L2)) :
    (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) (amalgamIsoφ12 iso g) : ↥M₁) =
      amalgamIsoφ1 iso (Subgroup.inclusion (inf_le_left : H ⊓ L2 ≤ H) g) :=
  iso.comm1 g

theorem amalgamIso_mem_iff {G Y : Type u} [Group G] [Group Y] {H L2 : Subgroup G}
    {M₁ M₂ : Subgroup Y}
    (iso : (RankTwoAmalgam.ofSubgroups H L2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (x : ↥H) : (x : G) ∈ L2 ↔ ((amalgamIsoφ1 iso x : ↥M₁) : Y) ∈ M₂ := by
  constructor
  · intro hx
    let g : ↥(H ⊓ L2) := ⟨x, x.2, hx⟩
    have h := amalgamIso_comm iso g
    have e : (Subgroup.inclusion (inf_le_left : H ⊓ L2 ≤ H) g : ↥H) = x := rfl
    rw [e] at h
    have h2 : ((amalgamIsoφ12 iso g : ↥(M₁ ⊓ M₂)) : Y) = ((amalgamIsoφ1 iso x : ↥M₁) : Y) :=
      congrArg Subtype.val h
    rw [← h2]
    exact (amalgamIsoφ12 iso g).2.2
  · intro hx
    let g' : ↥(M₁ ⊓ M₂) := ⟨((amalgamIsoφ1 iso x : ↥M₁) : Y), (amalgamIsoφ1 iso x).2, hx⟩
    let g : ↥(H ⊓ L2) := (amalgamIsoφ12 iso).symm g'
    have h := amalgamIso_comm iso g
    have e2 : amalgamIsoφ12 iso g = g' := (amalgamIsoφ12 iso).apply_symm_apply g'
    rw [e2] at h
    have h3 : amalgamIsoφ1 iso x =
        amalgamIsoφ1 iso (Subgroup.inclusion (inf_le_left : H ⊓ L2 ≤ H) g) := h
    have h4 := (amalgamIsoφ1 iso).injective h3
    have h5 : (x : G) = (g : G) := congrArg Subtype.val h4
    rw [h5]
    exact g.2.2

theorem titsAmalgamLocal
    : TitsAmalgamLocal := by
  intro G _ _ H L2 hCase
  obtain ⟨⟨Y, _, ⟨e⟩, T, M₁, M₂, hpair, ⟨iso⟩⟩, -, -, -, hP2⟩ := hCase
  let φ : Y ≃* titsD := e.trans quasithinTitsEquivD
  have hpair' := IsYAmalgamPair.map φ hpair
  have hSylS : IsSylowTwoOf titsSD ⊤ := by
    have := isSylowTwoOf_top_of_sylow titsSylow
    rwa [coe_titsSylow] at this
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow hSylS hpair'.1
  let f : Y ≃* titsD := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) →
      (M.map f.toMonoidHom = titsHD ∨ M.map f.toMonoidHom = titsND) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact titsTwoLocalLattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : M₁.map f.toMonoidHom ≠ M₂.map f.toMonoidHom := fun h =>
    hpair.2.1 (Subgroup.map_injective f.injective h)
  rcases hlocal M₁ (Or.inl rfl) with h1 | h1 <;> rcases hlocal M₂ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  ·
    let ψ : ↥H ≃* ↥titsH := ((amalgamIsoφ1 iso).trans (f.subgroupMap M₁)).trans
      ((MulEquiv.subgroupCongr h1).trans (Subgroup.subgroupOfEquivOfLe titsH_le_titsD))
    refine TitsLikeVertexFacts.of_vertexEquiv' ψ (fun x => ?_) titsVertexFacts
    have h3 := amalgamIso_mem_iff iso x
    have h4 : ∀ y : Y, y ∈ M₂ ↔ f y ∈ titsND := fun y => by
      rw [← h2, Subgroup.mem_map_equiv]
      simp
    rw [h3, h4]
    exact Iff.rfl
  ·
    exfalso
    let ψ : ↥L2 ≃* ↥titsH := (iso.φ2.trans (f.subgroupMap M₂)).trans
      ((MulEquiv.subgroupCongr h2).trans (Subgroup.subgroupOfEquivOfLe titsH_le_titsD))
    have := card_pCoreOf_eq_of_mulEquiv ψ
    rw [hP2, card_pCoreOf_titsH] at this
    norm_num at this
  · exact absurd (h1.trans h2.symm) hne

end CFSG.Quasithin
