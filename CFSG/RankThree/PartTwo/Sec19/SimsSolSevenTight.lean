module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenDefs
public import CFSG.CGT.PushingUpLit.SolK.TightOrders
public import CFSG.CGT.Timmesfeld75.FinalNodeRest
public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.RankThree.GF2n.Item310BridgesSporadic
import CFSG.RankThree.GF2n.Item310BridgesLie
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
import CFSG.GF2Type.Aschbacher1976Common.DihedralRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.PushingUpLit.SolK (pCoreOf_normalized isMaximalTwoLocal_conj local_le_of_unique
  mem_centralizer_zpowers_iff isPGroup_pCoreOf' pCoreOf_le_self eq_one_of_odd_card
  comm_of_cyclic_or_elem two_element_mem_of_sylow tightSmallGroupOrders)
open CFSG.Assembly (InCatalog pCoreOf)
open CFSG.CGT.Timmesfeld75 (ListGroup)

theorem nodeStatement_holds :
    CFSG.CGT.Timmesfeld75.NodeStatement :=
  CFSG.CGT.Timmesfeld75.node_final_rest ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩

theorem inCatalog_of_listGroup
    {G : Type} [Group G]
    (h : ListGroup G) : InCatalog G := by
  rcases h with ⟨m, s, -, -, h⟩ | ⟨s, -, h⟩ | ⟨s, -, -, h⟩ | ⟨k, hk, -, ⟨e⟩⟩ | h | h | h
  · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all G m 2 s h
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 3 2 s h
  · exact GF2n.suzukiBridge G s (GF2n.suzukiModel_of_lieModel h)
  · exact GF2n.inCatalog_of_alternating (by omega) e
  · exact GF2n.sporadicBridge_M22 G h
  · exact GF2n.sporadicBridge_M23 G h
  · exact GF2n.sporadicBridge_M24 G h

namespace Setting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : Setting G M X)
include S

theorem mem_of_conj_le (g : G) (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ M) : g ∈ M := by
  have hmax : CFSG.IsMaximalTwoLocal (M.map (MulAut.conj g⁻¹).toMonoidHom) :=
    isMaximalTwoLocal_conj S.maxLocal g⁻¹
  have hXM : (X : Set G) ⊆ M.map (MulAut.conj g⁻¹).toMonoidHom := fun x hx =>
    ⟨g * x * g⁻¹, hg x hx, by simp [mul_assoc]⟩
  have hmem : M.map (MulAut.conj g⁻¹).toMonoidHom ∈
      CFSG.maximalTwoLocalsContaining (X : Set G) := ⟨hmax, hXM⟩
  rw [S.uniq] at hmem
  simpa using M.inv_mem (Late.mem_of_map_conj_eq_of_isMaximalTwoLocal S.maxLocal hmem)

theorem mem_of_common_involution {g z : G} (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hz2 : orderOf z = 2) (hgz : g * z * g⁻¹ ∈ Subgroup.centralizer (X : Set G)) : g ∈ M := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; simp)
  have hZ : Subgroup.zpowers z ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hz1
  have hloc : CFSG.IsPLocal 2
      (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) := ⟨_, hZ, hZ2, rfl⟩
  have hCN : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hxz : ∀ x ∈ X, x * z * x⁻¹ = z := fun x hx => by
    have := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [this]
    group
  have hXN : X ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun x hx =>
    hCN (mem_centralizer_zpowers_iff.2 (hxz x hx))
  have hle := local_le_of_unique S.uniq hloc hXN
  have hconj : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ ∈ M := by
    intro x hx
    rw [inv_inv]
    have hc := Subgroup.mem_centralizer_iff.1 hgz x hx
    refine hle (hCN (mem_centralizer_zpowers_iff.2 ?_))
    calc g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by group
      _ = z := by rw [hc]; group
  simpa using M.inv_mem (S.mem_of_conj_le g⁻¹ hconj)

theorem le_normalizer_C :
    M ≤ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ c ∈ Subgroup.centralizer (X : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : m⁻¹ * x * m ∈ X := by simpa using S.normal (M.inv_mem hm) hx
    have h1 := hc _ hx'
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * x := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨key m hm c, fun h => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ h⟩

theorem normalizer_C_eq (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = M := by
  refine le_antisymm (fun g hg => ?_) S.le_normalizer_C
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (X : Set G))) 2
    (even_iff_two_dvd.1 hev)
  have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  exact S.mem_of_common_involution z.2 hz2 ((Subgroup.mem_normalizer_iff.1 hg (z : G)).1 z.2)

theorem tightlyEmbedded_C (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    TightlyEmbedded (Subgroup.centralizer (X : Set G)) :=
  StandardSubgroupAPI.tightlyEmbedded_of_involution hev fun g _ hz hz2 =>
    S.le_normalizer_C (S.mem_of_common_involution (Subgroup.mem_inf.1 hz).1 hz2
      ((mem_rightConjugate_iff _ g _).1 (Subgroup.mem_inf.1 hz).2))

theorem card_blockU_mul_le {B : ℕ} (hP : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card P ≤ B)
    (hWC : ∀ w ∈ blockU X, w ∈ Subgroup.centralizer (X : Set G) → w = 1)
    {T : Subgroup G} (hTC : T ≤ Subgroup.centralizer (X : Set G)) (hT2 : IsPGroup 2 T) :
    Nat.card (blockU X) * Nat.card T ≤ B := by
  classical
  have hW2 : IsPGroup 2 (blockU X) := fun w => ⟨1, Subtype.ext (by simpa using S.elemU.2 w w.2)⟩
  have hc : ∀ t ∈ T, ∀ w ∈ blockU X, t * w * t⁻¹ = w := fun t ht w hw => by
    rw [← Subgroup.mem_centralizer_iff.1 (hTC ht) w (blockU_le_self X hw)]
    group
  have hTN : T ≤ Subgroup.normalizer (blockU X : Set G) := fun t ht => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hc t ht h hh]; exact hh, fun hh => ?_⟩
    have h1 := hc t⁻¹ (T.inv_mem ht) _ hh
    have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
    rw [e] at h1
    exact h1.symm ▸ hh
  have hP2 : IsPGroup 2 (blockU X ⊔ T : Subgroup G) := hW2.to_sup_of_normal_left' hT2 hTN
  let f : ↥(blockU X) × ↥T → ↥(blockU X ⊔ T : Subgroup G) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨w, hw⟩, ⟨t, ht⟩⟩ ⟨⟨w', hw'⟩, ⟨t', ht'⟩⟩ h
    have h1 : w * t = w' * t' := congrArg Subtype.val h
    have h2 : w'⁻¹ * w = t' * t⁻¹ := by
      calc w'⁻¹ * w = w'⁻¹ * (w * t) * t⁻¹ := by group
        _ = w'⁻¹ * (w' * t') * t⁻¹ := by rw [h1]
        _ = t' * t⁻¹ := by group
    have hW : w'⁻¹ * w ∈ blockU X := (blockU X).mul_mem ((blockU X).inv_mem hw') hw
    have hTt : w'⁻¹ * w ∈ T := h2 ▸ T.mul_mem ht' (T.inv_mem ht)
    have h3 : w'⁻¹ * w = 1 := hWC _ hW (hTC hTt)
    have hww : w = w' := by
      calc w = w' * (w'⁻¹ * w) := by group
        _ = w' := by rw [h3, mul_one]
    subst hww
    have : t = t' := mul_left_cancel h1
    subst this
    rfl
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  exact hcard.trans (hP _ hP2)

end Setting

theorem inCatalog_or_tightData
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : Setting G M X)
    (hW16 : Nat.card ↥(CFSG.QuasithinUnique.blockU X) = 16)
    (hWC : ∀ w ∈ CFSG.QuasithinUnique.blockU X, w ∈ Subgroup.centralizer (X : Set G) → w = 1) :
    CFSG.Assembly.InCatalog G ∨
      ((∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)),
          ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)), a * b = b * a) ∧
        ∀ c ∈ Subgroup.centralizer (X : Set G), ∀ k : ℕ, c ^ (2 ^ k) = 1 →
          c ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) := by
  classical
  by_cases hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer (X : Set G))) := inferInstance
    have hN := S.normalizer_C_eq hev
    have hmax : CFSG.IsMaximalTwoLocal
        (Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) := by
      rw [hN]; exact S.maxLocal
    have hF : Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer
          ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer
          ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) := by
      rw [hN]; exact S.charTwo M S.maxLocal.1
    have hTC : (T : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.map_subtype_le _
    have hT2 : IsPGroup 2 ((T : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype) := T.isPGroup'.map _
    rcases hST G S.kProper S.simple S.nonab (Subgroup.centralizer (X : Set G))
        (S.tightlyEmbedded_C hev) hmax hF T with ⟨hTO, hab, -⟩ | ⟨-, hdih⟩ | ⟨hQ8, hgrp⟩ |
        ⟨⟨H, -, hHT, ⟨hHe⟩, -⟩, hL34⟩ | hSz | ⟨-, hel, h4, hTI, hNT, hWT⟩
    ·
      refine Or.inr ⟨fun a ha b hb => ?_, fun c hc k hk => two_element_mem_of_sylow T hTO hc hk⟩
      rw [← hTO] at ha hb
      exact comm_of_cyclic_or_elem hab a ha b hb
    ·
      have := GF2Type.Aschbacher1976Common.card_le_four_of_dihedral_or_semidihedral hdih S.elemU
      omega
    ·
      have hb : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64 := by
        rcases hgrp with h | h | h | h | h
        · exact tightSmallGroupOrders G (Or.inl h)
        · exact tightSmallGroupOrders G (Or.inr (Or.inl h))
        · exact tightSmallGroupOrders G (Or.inr (Or.inr (Or.inl h)))
        · exact tightSmallGroupOrders G (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact tightSmallGroupOrders G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      have h128 := S.card_blockU_mul_le hb hWC hTC hT2
      have hT8 : Nat.card ↥((T : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
          (Subgroup.centralizer (X : Set G)).subtype) = 8 := by
        rw [Nat.card_congr hQ8.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      rw [hW16, hT8] at h128
      omega
    ·
      have h256 := S.card_blockU_mul_le
        (tightSmallGroupOrders G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL34)))))) hWC hTC hT2
      have hH16 : Nat.card ↥H = 16 := by
        rw [Nat.card_congr hHe.toEquiv, Nat.card_prod,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4), Nat.card_zmod]
      have hle := Subgroup.card_le_of_le hHT
      rw [hW16] at h256
      omega
    ·
      refine Or.inl (inCatalog_of_listGroup ?_)
      rcases hSz with ⟨s, hs, hs3, h⟩ | ⟨s, hs, h⟩
      · exact Or.inr (Or.inr (Or.inl ⟨s, hs, hs3, h⟩))
      · exact Or.inr (Or.inl ⟨s, hs, h⟩)
    ·
      have := S.simple
      exact Or.inl (inCatalog_of_listGroup (nodeStatement_holds G S.nonab _ hel h4
        (fun g => hTI g⁻¹) (fun g hg => hWT.2 g⁻¹ (hg.trans hNT.le))))
  ·
    have hodd : Odd (Nat.card ↥(Subgroup.centralizer (X : Set G))) := Nat.not_even_iff_odd.1 hev
    have h1 : ∀ r ∈ pCoreOf 2 (Subgroup.centralizer (X : Set G)), r = 1 := fun r hr => by
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G)) ⟨r, hr⟩
      exact eq_one_of_odd_card hodd (pCoreOf_le_self _ hr) (j := j)
        (by simpa using congrArg Subtype.val hj)
    refine Or.inr ⟨fun a ha b hb => by rw [h1 a ha, h1 b hb], fun c hc k hk => ?_⟩
    rw [eq_one_of_odd_card hodd hc hk]
    exact Subgroup.one_mem _

end CFSG.RankThree.PartTwo.Sec19.SolSeven
