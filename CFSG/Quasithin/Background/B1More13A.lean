module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1MoreTenC
public import CFSG.Quasithin.Background.B1MoreTwelveD

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B113

section Subnormal

variable {Ω : Type*} [Group Ω]

theorem le_of_isSubnormal {L K : Subgroup Ω} (h : IsSubnormal L K) : L ≤ K :=
  h.le

theorem isSubnormal_inf_of_le {L K H : Subgroup Ω} (h : IsSubnormal L K) (hHK : H ≤ K) :
    IsSubnormal (H ⊓ L) H :=
  by rw [inf_comm]; exact h.inf_of_le hHK

theorem subgroupOf_isSubnormal {X H : Subgroup Ω} (h : IsSubnormal X H) :
    (X.subgroupOf H).IsSubnormal :=
  CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
    ((isSubnormal_subgroupOf_top_iff (le_of_isSubnormal h)).2 h) Subgroup.IsSubnormal.top

theorem mem_map_conj {L : Subgroup Ω} {g x : Ω} :
    x ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ L := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end Subnormal

section Components

variable {Ω : Type*} [Group Ω]

theorem isComponentOf_conj {L G : Subgroup Ω} (hL : IsComponentOf L G) {g : Ω} (hg : g ∈ G) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) G := by
  have hGg : G.map (MulAut.conj g).toMonoidHom = G := B1Red.map_conj_eq_self_of_mem_normalizer
    (Subgroup.le_normalizer hg)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hGg]
    exact Subgroup.map_mono hL.1
  · have := CFSG.ComponentClassification.Components.chain_map (MulAut.conj g).toMonoidHom hL.2.1
    rwa [hGg] at this
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm hL.2.2

theorem conj_mem_normalizer_of_comps {G J : Subgroup Ω}
    (hJ : ∀ L : Subgroup Ω, IsComponentOf L G → J ≤ Subgroup.normalizer (L : Set Ω))
    {L : Subgroup Ω} (hL : IsComponentOf L G) {g j : Ω} (hg : g ∈ G) (hj : j ∈ J) :
    g * j * g⁻¹ ∈ Subgroup.normalizer (L : Set Ω) := by
  have hL' : IsComponentOf (L.map (MulAut.conj g⁻¹).toMonoidHom) G :=
    isComponentOf_conj hL (G.inv_mem hg)
  have hj' := hJ _ hL' hj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e1 : x ∈ L ↔ g⁻¹ * x * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [mem_map_conj]
    simp [mul_assoc]
  have e2 := Subgroup.mem_normalizer_iff.mp hj' (g⁻¹ * x * g)
  have e3 : j * (g⁻¹ * x * g) * j⁻¹ ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ↔
      (g * j * g⁻¹) * x * (g * j * g⁻¹)⁻¹ ∈ L := by
    rw [mem_map_conj]
    simp [mul_assoc]
  rw [e1, e2, e3]

theorem le_normalizer_of_commutator_of_comps {G K J : Subgroup Ω} (hKG : K ≤ G)
    (hJ : ∀ L : Subgroup Ω, IsComponentOf L G → J ≤ Subgroup.normalizer (L : Set Ω))
    (hKJ : ⁅K, J⁆ = K) {L : Subgroup Ω} (hL : IsComponentOf L G) :
    K ≤ Subgroup.normalizer (L : Set Ω) := by
  calc K = ⁅K, J⁆ := hKJ.symm
    _ ≤ Subgroup.normalizer (L : Set Ω) := by
      rw [Subgroup.commutator_le]
      intro k hk j hj
      have h1 := conj_mem_normalizer_of_comps hJ hL (hKG hk) hj
      have h2 : j⁻¹ ∈ Subgroup.normalizer (L : Set Ω) :=
        (Subgroup.normalizer (L : Set Ω)).inv_mem (hJ L hL hj)
      have h3 : ⁅k, j⁆ = (k * j * k⁻¹) * j⁻¹ := rfl
      rw [h3]
      exact Subgroup.mul_mem _ h1 h2

theorem component_le_or_commutator_eq_bot [Finite Ω] {K X H : Subgroup Ω}
    (hK : IsComponentOf K H) (hX : IsSubnormal X H) : K ≤ X ∨ ⁅K, X⁆ = ⊥ := by
  have hXH : X ≤ H := le_of_isSubnormal hX
  have hq : CFSG.GorensteinWalter.IsQuasisimple ↥K := by
    obtain ⟨h1, h2⟩ := hK.2.2
    refine ⟨?_, h1, h2⟩
    obtain ⟨a, b, hab⟩ := h2.exists_pair_ne
    refine ⟨?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  have hE : CFSG.GorensteinWalter.IsComponentOf K H := ⟨hK.1, subgroupOf_isSubnormal hK.2.1, hq⟩
  exact CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf hXH
    (subgroupOf_isSubnormal hX) hE

theorem conj_mem_centralizer_of_normalizes {L : Subgroup Ω} {k j : Ω}
    (hk : k ∈ Subgroup.normalizer (L : Set Ω)) (hj : j ∈ Subgroup.centralizer (L : Set Ω)) :
    k * j * k⁻¹ ∈ Subgroup.centralizer (L : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : k⁻¹ * x * k ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 hk (k⁻¹ * x * k)).2 (by simpa [mul_assoc] using hx)
    exact this
  have h1 := Subgroup.mem_centralizer_iff.1 hj (k⁻¹ * x * k) hx'
  calc x * (k * j * k⁻¹) = k * ((k⁻¹ * x * k) * j) * k⁻¹ := by group
    _ = k * (j * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
    _ = (k * j * k⁻¹) * x := by group

theorem isSylowTwoOf_inf_of_isSubnormal [Finite Ω] {G T L : Subgroup Ω}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) (hL : IsSubnormal L G) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
  CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hT (le_of_isSubnormal hL)
    (subgroupOf_isSubnormal hL)

theorem le_centralizer_of_odd [Finite Ω] {K L : Subgroup Ω}
    (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3)
    (h : ∀ x ∈ K, Odd (orderOf x) → x ∈ Subgroup.centralizer (L : Set Ω)) :
    K ≤ Subgroup.centralizer (L : Set Ω) := by
  rcases hK with hq | h3
  · have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
    rw [← B1Red.oTwoUpper_eq_of_perfect hperf]
    exact (Subgroup.closure_le _).2 fun x hx => h x hx.1 hx.2
  · intro x hx
    exact h x hx (B1Red.odd_orderOf_of_card_three h3 hx)

end Components

end B113

end CFSG.Quasithin
