module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.EmptyFaithful.T1515Der

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem conjByElt_mul1516 (x y : G) (K : Subgroup G) :
    conjByElt (x * y) K = conjByElt x (conjByElt y K) := by
  ext z
  simp only [mem_conjByElt, mul_inv_rev, mul_assoc]

theorem conjByElt_one1516 (K : Subgroup G) : conjByElt 1 K = K := by
  ext z
  simp [mem_conjByElt]

theorem conjByElt_injective1516 (x : G) {A B : Subgroup G} (h : conjByElt x A = conjByElt x B) :
    A = B := by
  ext z
  have := Iff.of_eq (congrArg (fun K : Subgroup G => x * z * x⁻¹ ∈ K) h)
  simpa [mem_conjByElt, mul_assoc] using this

theorem conjByElt_eq_of_odd1516 {x : G} (hx : Odd (orderOf x)) {S : Set (Subgroup G)}
    (hS : S.ncard = 2) (hcl : ∀ K ∈ S, conjByElt x K ∈ S) {K : Subgroup G} (hK : K ∈ S) :
    conjByElt x K = K := by
  by_contra hne
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hK1 : conjByElt x K ∈ S := hcl K hK
  have hK2 : conjByElt x (conjByElt x K) ∈ S := hcl _ hK1
  have h2 : conjByElt x (conjByElt x K) = K := by
    by_contra hne2
    have hne3 : conjByElt x K ≠ conjByElt x (conjByElt x K) := fun h =>
      hne (conjByElt_injective1516 x h.symm)
    have h3 : ({K, conjByElt x K, conjByElt x (conjByElt x K)} : Set (Subgroup G)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨K, conjByElt x K, conjByElt x (conjByElt x K), fun h => hne h.symm,
        fun h => hne2 h.symm, hne3, rfl⟩
    have hsub : ({K, conjByElt x K, conjByElt x (conjByElt x K)} : Set (Subgroup G)) ⊆ S := by
      intro a ha
      rcases ha with rfl | rfl | rfl <;> assumption
    have := Set.ncard_le_ncard hsub hfin
    omega
  have hpow : ∀ m : ℕ, conjByElt (x ^ (2 * m)) K = K := by
    intro m
    induction m with
    | zero => simpa using conjByElt_one1516 K
    | succ m ih =>
      have e : x ^ (2 * (m + 1)) = (x * x) * x ^ (2 * m) := by
        rw [show 2 * (m + 1) = 2 + 2 * m by ring, pow_add, pow_two]
      rw [e, conjByElt_mul1516, ih, conjByElt_mul1516, h2]
  obtain ⟨m, hm⟩ := hx
  have h1 : conjByElt (x ^ orderOf x) K = K := by
    rw [pow_orderOf_eq_one, conjByElt_one1516]
  rw [hm, pow_succ', conjByElt_mul1516, hpow] at h1
  exact hne h1

theorem mem_normalizer_of_conjByElt_eq1516 {x : G} {K : Subgroup G} (h : conjByElt x K = K) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have := Iff.of_eq (congrArg (fun L : Subgroup G => x * z * x⁻¹ ∈ L) h)
  simp only [mem_conjByElt] at this
  have e : x⁻¹ * (x * z * x⁻¹) * x = z := by group
  rw [e] at this
  exact this

theorem odd_mem_normalizer_conjSubgroupsBy1516 {H L : Subgroup G} (hLH : L ≤ H)
    (h : (L.subgroupOf H).Normal ∨ (conjSubgroupsBy H L).ncard = 2) {x : G} (hxH : x ∈ H)
    (hx : Odd (orderOf x)) {K : Subgroup G} (hK : K ∈ conjSubgroupsBy H L) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  refine mem_normalizer_of_conjByElt_eq1516 ?_
  rcases h with hn | hc
  · have hN : H ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hn
    have hfix : ∀ t ∈ H, conjByElt t L = L := by
      intro t ht
      ext z
      rw [mem_conjByElt]
      have := Subgroup.mem_normalizer_iff.mp (hN (H.inv_mem ht)) z
      simpa using this.symm
    obtain ⟨t, htH, rfl⟩ := hK
    show conjByElt x (conjByElt t L) = conjByElt t L
    rw [hfix t htH, hfix x hxH]
  · refine conjByElt_eq_of_odd1516 hx hc ?_ hK
    rintro K' ⟨t, htH, rfl⟩
    exact ⟨x * t, H.mul_mem hxH htH, (conjByElt_mul1516 x t L).symm⟩

theorem mem_normalizer_conj_of_mem_normalizer_conjByElt1516 {x v : G} {L : Subgroup G}
    (h : x ∈ Subgroup.normalizer ((conjByElt v⁻¹ L : Subgroup G) : Set G)) :
    v * x * v⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro z
  have h1 := h (v⁻¹ * z * v)
  simp only [mem_conjByElt, inv_inv] at h1
  have e1 : v * (v⁻¹ * z * v) * v⁻¹ = z := by group
  have e2 : v * (x * (v⁻¹ * z * v) * x⁻¹) * v⁻¹ = v * x * v⁻¹ * z * (v * x * v⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

variable [Finite G]

theorem lemma_15_1_19_seven (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) :
    ∀ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      ¬ L ≤ mZ1516 Mc Z₁ →
      oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ⊔ V₂ ≤ Subgroup.normalizer (L : Set G) ∧
        ⁅L, V₂⁆ ≠ ⊥ := by
  intro L hL _ hLM
  have hLH : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL
  have hH : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hc : (L.subgroupOf (g1_1516 Z₁)).Normal ∨ (conjSubgroupsBy (g1_1516 Z₁) L).ncard = 2 :=
    (lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hH hL).imp id And.left
  have hXN : ∀ K ∈ conjSubgroupsBy (g1_1516 Z₁) L,
      oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ≤ Subgroup.normalizer (K : Set G) := by
    intro K hK
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact odd_mem_normalizer_conjSubgroupsBy1516 hLH hc hx.1.2 hx.2 hK
  have hLmem : L ∈ conjSubgroupsBy (g1_1516 Z₁) L :=
    ⟨1, Subgroup.one_mem _, (conjByElt_one1516 L).symm⟩
  have hXL : oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ≤ Subgroup.normalizer (L : Set G) :=
    hXN L hLmem
  have hV2L : V₂ ≤ Subgroup.normalizer (L : Set G) := by
    have hv2 : ⁅V₂, oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G))⁆ = V₂ := hS.v2_comm
    refine hv2.symm.le.trans ?_
    rw [Subgroup.commutator_le]
    intro v hv x hx
    have hvG : v ∈ g1_1516 Z₁ := hS.V_le_g1 hq hM (hS.v2_le hv)
    have hK : conjByElt v⁻¹ L ∈ conjSubgroupsBy (g1_1516 Z₁) L := ⟨v⁻¹, Subgroup.inv_mem _ hvG, rfl⟩
    have h1 := mem_normalizer_conj_of_mem_normalizer_conjByElt1516 (hXN _ hK hx)
    have h2 : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ (hXL hx)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 h2
  refine ⟨sup_le hXL hV2L, fun hbot => hLM ?_⟩
  have hbot' : ⁅V₂, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hbot
  have hLV : L ≤ Subgroup.centralizer (V₂ : Set G) := le_centralizer_of_commutator_eq_bot hbot'
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hq.omegaOneCenter_ne_bot
  have hzZ : (a : G) ∈ quasithinOmegaOneCenter T := a.2
  have hz1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hlez : (a : G) ∈ Z₁ ⊔ V₂ := hS.z_le hzZ
  have hLMc : Subgroup.centralizer ({(a : G)} : Set G) ≤ Mc :=
    centralizer_singleton_le_mc_of_mem_omegaOneCenter hq hzZ hz1
  intro l hl
  refine ⟨hLH hl, hLMc ?_⟩
  have hlC : l ∈ Subgroup.centralizer ((Z₁ ⊔ V₂ : Subgroup G) : Set G) :=
    mem_centralizer_sup1516 (hLH hl) (hLV hl)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact Subgroup.mem_centralizer_iff.mp hlC (a : G) hlez

end CFSG.Quasithin
