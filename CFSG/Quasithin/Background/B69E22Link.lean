module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace B69

variable {H₀ Y : Type} [Group H₀] [Group Y]

theorem ker_star_hom (φ : H₀ →* Y) {H M' : Subgroup H₀} {M : Subgroup Y}
    (hMH : M' ≤ H) (hH : H.map φ = ⊤) (hM : M'.map φ = M) (hker : φ.ker ⊓ H ≤ M') :
    ((QuotientGroup.mk' (kerIn M ⊤)).comp (φ.comp H.subtype)).ker =
      (kerIn M' H).subgroupOf H := by
  have key : ∀ x ∈ H, φ x ∈ M → x ∈ M' := by
    intro x hx hxM
    rw [← hM] at hxM
    obtain ⟨m, hm, hmx⟩ := hxM
    have h1 : m⁻¹ * x ∈ φ.ker ⊓ H := ⟨by simp [map_mul, map_inv, hmx],
      H.mul_mem (H.inv_mem (hMH hm)) hx⟩
    have := hker h1
    have h2 : m * (m⁻¹ * x) ∈ M' := M'.mul_mem hm this
    simpa using h2
  ext h
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.coe_subtype, Subgroup.mem_subgroupOf, mem_kerIn,
    Subgroup.mem_top, forall_const]
  constructor
  · intro hh b hb
    apply key _ (H.mul_mem (H.mul_mem hb h.2) (H.inv_mem hb))
    have := hh (φ b)
    simpa [map_mul, map_inv] using this
  · intro hh y
    have hy : y ∈ H.map φ := by rw [hH]; trivial
    obtain ⟨b, hb, rfl⟩ := hy
    have := hh b hb
    rw [← hM]
    exact ⟨_, this, by simp [map_mul, map_inv]⟩

theorem exists_conj_eq_of_component {Z : Type} [Group Z] [Finite Z] {K L T : Subgroup Z}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hK : K.IsSubnormal) (hKs : IsSimpleGroup ↥K)
    (hT : IsPGroup 2 ↥T) (hZ : K ⊔ T = ⊤) : ∃ z : Z, L = conjSub z K := by
  have hL' : CFSG.GorensteinWalter.IsComponentOf L ⊤ := (CFSG.Adapters.isComponentOf_top_iff L).1 hL
  have hLsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).1 hL.2.1
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
  have hLcomm : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLperf
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  let N : Subgroup Z := Subgroup.normalClosure (K : Set Z)
  have hKN : K ≤ N := Subgroup.subset_normalClosure
  have hLN : L ≤ N := by
    let q : Z →* Z ⧸ N := QuotientGroup.mk' N
    have h1 : K.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      simpa [q] using hKN
    have h2 : (⊤ : Subgroup Z).map q = T.map q := by
      rw [← hZ, Subgroup.map_sup, h1, bot_sup_eq]
    have h3 : L.map q ≤ T.map q := (Subgroup.map_mono le_top).trans h2.le
    have hT2 : IsPGroup 2 ↥(T.map q) := hT.map _
    have hLq2 : IsPGroup 2 ↥(L.map q) := hT2.to_le h3
    have hperf : ⁅L.map q, L.map q⁆ = L.map q := by
      rw [← Subgroup.map_commutator, hLcomm]
    by_contra hnot
    have hne : L.map q ≠ ⊥ := by
      intro hbot
      apply hnot
      rw [Subgroup.map_eq_bot_iff] at hbot
      simpa [q] using hbot
    have : Nontrivial ↥(L.map q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥(L.map q) := Subgroup.isPerfect_iff.mpr hperf
    exact Group.IsPerfect.not_isNilpotent ↥(L.map q) hLq2.isNilpotent
  have hex : ∃ z : Z, ⁅L, conjSub z K⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have hcent : N ≤ Subgroup.centralizer (L : Set Z) := by
      show Subgroup.closure (Group.conjugatesOfSet (K : Set Z)) ≤ _
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have hgmem : g ∈ conjSub c K := by
        rw [mem_conjSub, ← hc]
        simpa [mul_assoc] using hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : ⁅l, g⁆ ∈ ⁅L, conjSub c K⁆ := Subgroup.commutator_mem_commutator hl hgmem
      rw [hall c, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hLabel : ⁅L, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hLN.trans hcent)
    rw [hLcomm] at hLabel
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt hLabel
  obtain ⟨z, hz⟩ := hex
  have hsn : (conjSub z K).IsSubnormal :=
    Subgroup.IsSubnormal.map (f := (MulAut.conj z).toMonoidHom) (MulAut.conj z).surjective hK
  have hLle : L ≤ conjSub z K := by
    rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot hL' hsn with h | h
    · exact h
    · exact absurd h hz
  refine ⟨z, le_antisymm hLle ?_⟩
  have hWs : IsSimpleGroup ↥(conjSub z K) :=
    (MulEquiv.isSimpleGroup_congr (K.equivMapOfInjective (MulAut.conj z).toMonoidHom
      (MulAut.conj z).injective)).mp hKs
  have hU : (L.subgroupOf (conjSub z K)).IsSubnormal := hLsn.subgroupOf
  rcases hU.eq_bot_or_top_of_isSimpleGroup hWs with hbot | htop
  · exfalso
    have : L = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact hbot.eq_bot_of_le hLle
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt this
  · intro x hx
    have : (⟨x, hx⟩ : ↥(conjSub z K)) ∈ L.subgroupOf (conjSub z K) := by rw [htop]; trivial
    exact this

theorem isComponentOf_map_top {Z : Type} [Group Z] (f : Y →* Z) (hf : Function.Surjective f)
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) (hLf : ¬ L ≤ f.ker) :
    CFSG.Open.IsComponentOf (L.map f) ⊤ := by
  have hLsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).1 hL.2.1
  refine ⟨le_top, (CFSG.Adapters.isSubnormal_top_iff _).2 (hLsn.map hf), ?_⟩
  let g : ↥L →* Z := f.comp L.subtype
  have hker : g.ker ≠ ⊤ := by
    intro htop
    apply hLf
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ g.ker := by rw [htop]; trivial
    exact this
  have hq := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hL.2.2 g hker
  have hrange : g.range = L.map f := by
    show (f.comp L.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (MulEquiv.subgroupCongr hrange).symm hq

theorem isSubnormal_subgroupOf_of_chain {X : Type*} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

end B69

end CFSG.Quasithin
