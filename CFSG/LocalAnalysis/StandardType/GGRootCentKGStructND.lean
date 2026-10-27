module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

namespace KGND

open scoped Pointwise commutatorElement

@[expose] def KGPiecesD {U : Type} [Group U] (𝒟 : Subgroup (MulAut U)) (z : U) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ψ : U →* G), Function.Injective ψ →
    ∀ E : Subgroup G, E ≤ Subgroup.centralizer {ψ z} →
      (∀ ε ∈ E, ∃ δ ∈ 𝒟, ∀ u : U, ε⁻¹ * ψ u * ε = ψ (δ u)) →
      ∃ 𝒥 : Set (Subgroup G),
        (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {ψ z} → ⁅P, P⁆ = P →
          P ≤ sSup 𝒥) ∧
        ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {ψ z}) E J

theorem KGPiecesD.map {U : Type} [Group U] {𝒟 : Subgroup (MulAut U)} {z : U}
    (h : KGPiecesD 𝒟 z) (β : MulAut U) (hβ : ∀ δ ∈ 𝒟, β⁻¹ * δ * β ∈ 𝒟) :
    KGPiecesD 𝒟 (β z) := by
  intro G _ _ ψ hψ E hE hact
  have hr : (ψ.comp β.toMonoidHom).range = ψ.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨β y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨β.symm y, by simp⟩
  have hz : (ψ.comp β.toMonoidHom) z = ψ (β z) := rfl
  have hact' : ∀ ε ∈ E, ∃ δ ∈ 𝒟, ∀ u : U,
      ε⁻¹ * (ψ.comp β.toMonoidHom) u * ε = (ψ.comp β.toMonoidHom) (δ u) := by
    intro ε hε
    obtain ⟨δ, hδ, hδact⟩ := hact ε hε
    refine ⟨β⁻¹ * δ * β, hβ δ hδ, fun u => ?_⟩
    have h1 : (β⁻¹ * δ * β) u = β⁻¹ (δ (β u)) := by
      rw [MulAut.mul_apply, MulAut.mul_apply]
    rw [h1]
    simpa using hδact (β u)
  obtain ⟨𝒥, hcover, hpiece⟩ := h G (ψ.comp β.toMonoidHom) (hψ.comp β.injective) E
    (by rw [hz]; exact hE) hact'
  rw [hr, hz] at hcover hpiece
  exact ⟨𝒥, hcover, hpiece⟩

theorem KGPiecesD.map_of_mem {U : Type} [Group U] {𝒟 : Subgroup (MulAut U)} {z : U}
    (h : KGPiecesD 𝒟 z) {β : MulAut U} (hβ : β ∈ 𝒟) : KGPiecesD 𝒟 (β z) :=
  h.map β fun δ hδ => 𝒟.mul_mem (𝒟.mul_mem (𝒟.inv_mem hβ) hδ) hβ

private theorem sup_proj_mem {G : Type} [Group G] {Q L : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (π : ↥(Q ⊔ L) →* ↥L)
    (hπ : ∀ (x : ↥(Q ⊔ L)) (l : ↥L), (x : G) * (l : G)⁻¹ ∈ Q → π x = l) :
    ∀ x : ↥(Q ⊔ L), (x : G) * ((π x : ↥L) : G)⁻¹ ∈ Q := by
  intro x
  have hx : (x : G) ∈ (Q : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ]
    exact x.2
  obtain ⟨q, hq, l, hl, hEq⟩ := hx
  have hπx : π x = ⟨l, hl⟩ := hπ x ⟨l, hl⟩ (by rw [← hEq]; simpa using hq)
  rw [hπx]
  have hql : (x : G) * l⁻¹ = q := by rw [← hEq]; group
  rw [hql]
  exact hq

private theorem exists_delta_alpha {U G : Type} [Group U] [Group G]
    {𝒟 : Subgroup (MulAut U)} {z : U} {Q L : Subgroup U} {ψ : U →* G} {E : Subgroup G}
    (hψ : Function.Injective ψ) (hE : E ≤ Subgroup.centralizer ({ψ z} : Set G))
    (hact : ∀ ε ∈ E, ∃ δ ∈ 𝒟, ∀ u : U, ε⁻¹ * ψ u * ε = ψ (δ u))
    (𝒜 : Set (MulAut ↥L))
    (hδ : ∀ δ ∈ 𝒟, δ z = z → ∃ α ∈ 𝒜, ∀ s ∈ Q ⊔ L, ∀ l : ↥L, s * (l : U)⁻¹ ∈ Q →
      δ s * ((α l : ↥L) : U)⁻¹ ∈ Q) :
    ∀ ε ∈ E, ∃ (δ : MulAut U) (α : MulAut ↥L), δ ∈ 𝒟 ∧
      (∀ u : U, ε⁻¹ * ψ u * ε = ψ (δ u)) ∧ α ∈ 𝒜 ∧
      (∀ s ∈ Q ⊔ L, ∀ l : ↥L, s * (l : U)⁻¹ ∈ Q →
        δ s * ((α l : ↥L) : U)⁻¹ ∈ Q) := by
  intro ε hε
  obtain ⟨δ, hδmem, hδact⟩ := hact ε hε
  have hδz : δ z = z := by
    apply hψ
    rw [← hδact z]
    have hcomm : ε * ψ z = ψ z * ε :=
      Subgroup.mem_centralizer_singleton_iff.mp (hE hε)
    calc ε⁻¹ * ψ z * ε = ε⁻¹ * (ψ z * ε) := by group
      _ = ε⁻¹ * (ε * ψ z) := by rw [hcomm]
      _ = ψ z := by group
  obtain ⟨α, hαA, hα⟩ := hδ δ hδmem hδz
  exact ⟨δ, α, hδmem, hδact, hαA, hα⟩

private theorem le_normalizer_map_sup {U G : Type} [Group U] [Group G]
    {𝒟 : Subgroup (MulAut U)} {z : U} {Q L : Subgroup U} {ψ : U →* G} {E : Subgroup G}
    (hψ : Function.Injective ψ) (hE : E ≤ Subgroup.centralizer ({ψ z} : Set G))
    (hact : ∀ ε ∈ E, ∃ δ ∈ 𝒟, ∀ u : U, ε⁻¹ * ψ u * ε = ψ (δ u))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set U)) (hQL : Q ⊓ L = ⊥)
    (𝒜 : Set (MulAut ↥L))
    (hδ : ∀ δ ∈ 𝒟, δ z = z → ∃ α ∈ 𝒜, ∀ s ∈ Q ⊔ L, ∀ l : ↥L, s * (l : U)⁻¹ ∈ Q →
      δ s * ((α l : ↥L) : U)⁻¹ ∈ Q) :
    E ≤ Subgroup.normalizer (((Q ⊔ L).map ψ : Subgroup G) : Set G) := by
  obtain ⟨πU, -, -, hπUuniq⟩ := exists_sup_proj (Q := Q) (L := L) hLQ hQL
  have hπUmem : ∀ x : ↥(Q ⊔ L), (x : U) * ((πU x : ↥L) : U)⁻¹ ∈ Q :=
    sup_proj_mem hLQ πU hπUuniq
  have hδα := exists_delta_alpha hψ hE hact 𝒜 hδ
  have hmap_le : ∀ ε ∈ E, Subgroup.map (MulAut.conj ε⁻¹) ((Q ⊔ L).map ψ) ≤
      (Q ⊔ L).map ψ := by
    intro ε hε
    obtain ⟨δ, α, hδmem, hδact, hαA, hα⟩ := hδα ε hε
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨δ s, ?_, ?_⟩
    · have hq := hα s hs (πU ⟨s, hs⟩) (hπUmem ⟨s, hs⟩)
      have hmem : ((α (πU ⟨s, hs⟩) : ↥L) : U) ∈ L := (α (πU ⟨s, hs⟩)).2
      have heq : δ s = (δ s * ((α (πU ⟨s, hs⟩) : ↥L) : U)⁻¹) *
          ((α (πU ⟨s, hs⟩) : ↥L) : U) := by group
      rw [heq]
      exact (Q ⊔ L).mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hmem)
    · simpa [MulAut.conj_apply] using (hδact s).symm
  have hmap_le' : ∀ ε ∈ E, Subgroup.map (MulAut.conj ε) ((Q ⊔ L).map ψ) ≤
      (Q ⊔ L).map ψ := by
    intro ε hε
    simpa using hmap_le ε⁻¹ (E.inv_mem hε)
  intro ε hε
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hmap_le' ε hε) ?_
  intro x hx
  have hx' : (MulAut.conj ε⁻¹) x ∈ (Q ⊔ L).map ψ :=
    hmap_le' ε⁻¹ (E.inv_mem hε) ⟨x, hx, rfl⟩
  exact ⟨(MulAut.conj ε⁻¹) x, hx', by
    show (MulAut.conj ε) ((MulAut.conj ε⁻¹) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group⟩

private theorem gGRCSKGPiece_map_sup {U G : Type} [Group U] [Group G]
    {𝒟 : Subgroup (MulAut U)} {z : U} {Q L : Subgroup U} {ψ : U →* G} {E : Subgroup G}
    (hψ : Function.Injective ψ) (hE : E ≤ Subgroup.centralizer ({ψ z} : Set G))
    (hact : ∀ ε ∈ E, ∃ δ ∈ 𝒟, ∀ u : U, ε⁻¹ * ψ u * ε = ψ (δ u))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set U)) (hQL : Q ⊓ L = ⊥)
    (𝒜 : Set (MulAut ↥L))
    (hδ : ∀ δ ∈ 𝒟, δ z = z → ∃ α ∈ 𝒜, ∀ s ∈ Q ⊔ L, ∀ l : ↥L, s * (l : U)⁻¹ ∈ Q →
      δ s * ((α l : ↥L) : U)⁻¹ ∈ Q)
    (hQmap : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) = Q.map ψ)
    (hJsub : (Q ⊔ L).map ψ ≤ ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G))
    (hJN : ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G) ≤
      Subgroup.normalizer (((Q ⊔ L).map ψ : Subgroup G) : Set G))
    (hperfJ : ⁅(Q ⊔ L).map ψ, (Q ⊔ L).map ψ⁆ = (Q ⊔ L).map ψ)
    (hQ1 : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ≤
      (Q ⊔ L).map ψ ⊔ (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ⊓
        Subgroup.centralizer (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) :
          Set G)))
    (hQ2 : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ≤
      ⁅(Q ⊔ L).map ψ, pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G))⁆ ⊔
        (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ⊓
          Subgroup.centralizer (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) :
            Set G)))
    (hLq : CFSG.Assembly.IsQuasisimple ↥L)
    (hLm : LargeEvenMarking ↥L (fun lab R _ I _ θ => GGChevStTag lab ∧ ∀ α ∈ 𝒜, ∃ φ ∈ I,
      ∀ y : ↥L, φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))))
    (hEJ : E ≤ Subgroup.normalizer (((Q ⊔ L).map ψ : Subgroup G) : Set G)) :
    GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) E ((Q ⊔ L).map ψ) := by
  obtain ⟨πU, hπUsurj, hπUker, hπUuniq⟩ := exists_sup_proj (Q := Q) (L := L) hLQ hQL
  have hπUmem : ∀ x : ↥(Q ⊔ L), (x : U) * ((πU x : ↥L) : U)⁻¹ ∈ Q :=
    sup_proj_mem hLQ πU hπUuniq
  have hδα := exists_delta_alpha hψ hE hact 𝒜 hδ
  let e : ↥(Q ⊔ L) ≃* ↥((Q ⊔ L).map ψ) := Subgroup.equivMapOfInjective (Q ⊔ L) ψ hψ
  let eJ : ↥((Q ⊔ L).map ψ) ≃* ↥(Q ⊔ L) := e.symm
  let π : ↥((Q ⊔ L).map ψ) →* ↥L := πU.comp eJ.toMonoidHom
  have heJ : ∀ x : ↥((Q ⊔ L).map ψ), ψ ((eJ x : ↥(Q ⊔ L)) : U) = (x : G) := by
    intro x
    have h := congrArg Subtype.val (e.apply_symm_apply x)
    rw [Subgroup.coe_equivMapOfInjective_apply] at h
    exact h
  have hπsurj : Function.Surjective π := by
    intro l
    obtain ⟨x, hx⟩ := hπUsurj l
    refine ⟨e x, ?_⟩
    show πU (eJ (e x)) = l
    rw [show eJ (e x) = x from by simp [eJ]]
    exact hx
  have hπker : π.ker = (Q.map ψ).subgroupOf ((Q ⊔ L).map ψ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (eJ x : ↥(Q ⊔ L)) ∈ πU.ker := by
        rw [MonoidHom.mem_ker]
        exact hx
      rw [hπUker, Subgroup.mem_subgroupOf] at hx'
      rw [← heJ x]
      exact Subgroup.mem_map_of_mem ψ hx'
    · rintro ⟨u, hu, hux⟩
      have hu' : u ∈ Q ⊔ L := Subgroup.mem_sup_left hu
      have hxu : eJ x = ⟨u, hu'⟩ := by
        apply Subtype.ext
        apply hψ
        rw [heJ x, ← hux]
      rw [show π x = πU (eJ x) from rfl, hxu]
      rw [← MonoidHom.mem_ker, hπUker, Subgroup.mem_subgroupOf]
      exact hu
  have hπact : ∀ ε ∈ E, ∃ α ∈ 𝒜, ∀ s s' : ↥((Q ⊔ L).map ψ),
      (s' : G) = ε⁻¹ * (s : G) * ε → π s' = α (π s) := by
    intro ε hε
    obtain ⟨δ, α, hδmem, hδact, hαA, hα⟩ := hδα ε hε
    refine ⟨α, hαA, ?_⟩
    intro s s' hss'
    have hδs : δ ((eJ s : ↥(Q ⊔ L)) : U) = ((eJ s' : ↥(Q ⊔ L)) : U) := by
      apply hψ
      calc ψ (δ ((eJ s : ↥(Q ⊔ L)) : U)) = ε⁻¹ * ψ ((eJ s : ↥(Q ⊔ L)) : U) * ε :=
            (hδact _).symm
        _ = ε⁻¹ * (s : G) * ε := by rw [heJ s]
        _ = (s' : G) := hss'.symm
        _ = ψ ((eJ s' : ↥(Q ⊔ L)) : U) := (heJ s').symm
    have huniq := hπUuniq (eJ s') (α (πU (eJ s))) ?_
    · exact huniq
    · rw [← hδs]
      exact hα ((eJ s : ↥(Q ⊔ L)) : U) (eJ s).2 (πU (eJ s)) (hπUmem (eJ s))
  have hπker' : π.ker =
      (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G))).subgroupOf
        ((Q ⊔ L).map ψ) := by
    rw [hQmap]
    exact hπker
  exact ggRCSKGPiece_of_marking hJsub hJN hperfJ hQ1 hQ2 hEJ hLq 𝒜 hLm π hπsurj hπker' hπact

theorem kgPiecesD_of_decomp {U : Type} [Group U] {𝒟 : Subgroup (MulAut U)} {z : U}
    {Q L : Subgroup U}
    (hQ : pCoreOf 2 (Subgroup.centralizer ({z} : Set U)) = Q)
    (hJC : Q ⊔ L ≤ Subgroup.centralizer ({z} : Set U))
    (hcomm : ⁅Subgroup.centralizer ({z} : Set U), Subgroup.centralizer ({z} : Set U)⁆ ≤ Q ⊔ L)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set U)) (hQL : Q ⊓ L = ⊥)
    (hperf : ⁅Q ⊔ L, Q ⊔ L⁆ = Q ⊔ L) (hLq : CFSG.Assembly.IsQuasisimple ↥L)
    (𝒜 : Set (MulAut ↥L))
    (hLm : LargeEvenMarking ↥L (fun lab R _ I _ θ => GGChevStTag lab ∧ ∀ α ∈ 𝒜, ∃ φ ∈ I,
      ∀ y : ↥L, φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))))
    (hδ : ∀ δ ∈ 𝒟, δ z = z → ∃ α ∈ 𝒜, ∀ s ∈ Q ⊔ L, ∀ l : ↥L, s * (l : U)⁻¹ ∈ Q →
      δ s * ((α l : ↥L) : U)⁻¹ ∈ Q) :
    KGPiecesD 𝒟 z := by
  classical
  intro G _ _ ψ hψ E hE hact
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCnorm : Subgroup.centralizer ({z} : Set U) ≤
      Subgroup.normalizer ((Q ⊔ L : Subgroup U) : Set U) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl hJC).trans hcomm
  have hC₀ : ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G) =
      (Subgroup.centralizer ({z} : Set U)).map ψ :=
    RCSTSp.range_inf_centralizer_of_injective hψ z
  have hQmap : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) = Q.map ψ := by
    rw [KGSp.pCoreOf_range_inf_centralizer hψ z, hQ]
  have hJsub : (Q ⊔ L).map ψ ≤ ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G) := by
    rw [hC₀]
    exact Subgroup.map_mono hJC
  have hperfJ : ⁅(Q ⊔ L).map ψ, (Q ⊔ L).map ψ⁆ = (Q ⊔ L).map ψ := by
    rw [← Subgroup.map_commutator, hperf]
  have hJN : ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G) ≤
      Subgroup.normalizer (((Q ⊔ L).map ψ : Subgroup G) : Set G) := by
    rw [hC₀]
    exact ggRCST_map_le_normalizer ψ hCnorm
  have hQJ : Q.map ψ ≤ (Q ⊔ L).map ψ := Subgroup.map_mono le_sup_left
  have hQ1 : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ≤
      (Q ⊔ L).map ψ ⊔ (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ⊓
        Subgroup.centralizer (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) :
          Set G)) := by
    rw [hQmap]
    exact hQJ.trans le_sup_left
  have hQ2grp : IsPGroup 2 (Q.map ψ) :=
    hQmap ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G))
  have hLQmap : L.map ψ ≤ Subgroup.normalizer ((Q.map ψ : Subgroup G) : Set G) :=
    ggRCST_map_le_normalizer ψ hLQ
  have hperf₀ : ⁅Q.map ψ ⊔ L.map ψ, Q.map ψ ⊔ L.map ψ⁆ = Q.map ψ ⊔ L.map ψ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_commutator, hperf, Subgroup.map_sup]
  have hdisj : Q.map ψ ⊓ L.map ψ = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_map hψ (disjoint_iff.mpr hQL))
  have hQ2' : Q.map ψ ≤ ⁅Q.map ψ ⊔ L.map ψ, Q.map ψ⁆ := by
    have h := le_commutator_sup_of_perfect (p := 2) hQ2grp hLQmap hperf₀
    rwa [hdisj, sup_bot_eq] at h
  have hQ2 : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ≤
      ⁅(Q ⊔ L).map ψ, pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G))⁆ ⊔
        (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) ⊓
          Subgroup.centralizer (pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) :
            Set G)) := by
    rw [hQmap, Subgroup.map_sup]
    exact hQ2'.trans le_sup_left
  have hEJ := le_normalizer_map_sup hψ hE hact hLQ hQL 𝒜 hδ
  have hpiece := gGRCSKGPiece_map_sup hψ hE hact hLQ hQL 𝒜 hδ hQmap hJsub hJN hperfJ hQ1 hQ2
    hLq hLm hEJ
  refine ⟨{(Q ⊔ L).map ψ}, ?_, ?_⟩
  · intro P hP hperfP
    rw [sSup_singleton]
    calc P = ⁅P, P⁆ := hperfP.symm
      _ ≤ ⁅ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G),
            ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)⁆ :=
          Subgroup.commutator_mono hP hP
      _ = ((⁅Subgroup.centralizer ({z} : Set U),
            Subgroup.centralizer ({z} : Set U)⁆).map ψ) := by
          rw [hC₀, Subgroup.map_commutator]
      _ ≤ (Q ⊔ L).map ψ := Subgroup.map_mono hcomm
  · intro J' hJ'
    rw [Set.mem_singleton_iff] at hJ'
    subst hJ'
    exact hpiece

end KGND

end CFSG.StandardType
