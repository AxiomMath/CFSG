module

public import CFSG.StronglyEmbedded.UniqueCosetBasic
public import CFSG.GH74.Uniqueness.CorZD
public import CFSG.LocalAnalysis.Asc75.EndBender

public section

namespace CFSG.StronglyEmbedded.UniqueCoset

open CFSG.GH74.Uniqueness
open scoped commutatorElement

variable {G : Type} [Group G]

section Socle

variable {F : Subgroup G} [hFn : F.Normal] (hFs : IsSimpleGroup ↥F)
include hFs

theorem le_or_le_centralizer {N : Subgroup G} (hN : ∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N) :
    F ≤ N ∨ N ≤ Subgroup.centralizer (F : Set G) := by
  have hK : ((N ⊓ F).subgroupOf F).Normal := by
    refine ⟨fun k hk f => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨hkN, -⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨?_, (f * k * f⁻¹).2⟩
    simpa using hN f f.2 k hkN
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hFs _ hK with hb | ht
  · right
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfn : n * f⁻¹ * n⁻¹ ∈ F := hFn.conj_mem _ (F.inv_mem hf) n
    have hmem : f * n * f⁻¹ * n⁻¹ ∈ N ⊓ F := by
      refine Subgroup.mem_inf.2 ⟨N.mul_mem (hN f hf n hn) (N.inv_mem hn), ?_⟩
      simpa [mul_assoc] using F.mul_mem hf hfn
    have hsub : (⟨f * n * f⁻¹ * n⁻¹, (Subgroup.mem_inf.1 hmem).2⟩ : F) ∈
        (N ⊓ F).subgroupOf F := Subgroup.mem_subgroupOf.2 hmem
    rw [hb, Subgroup.mem_bot] at hsub
    have h1 : f * n * f⁻¹ * n⁻¹ = 1 := congrArg Subtype.val hsub
    calc f * n = f * n * f⁻¹ * n⁻¹ * (n * f) := by group
      _ = n * f := by rw [h1, one_mul]
  · left
    intro f hf
    have hf' : (⟨f, hf⟩ : F) ∈ (N ⊓ F).subgroupOf F := ht ▸ Subgroup.mem_top _
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hf')).1

theorem le_of_normal (hFc : Subgroup.centralizer (F : Set G) = ⊥) {N : Subgroup G}
    [hN : N.Normal] (hN1 : N ≠ ⊥) : F ≤ N := by
  rcases le_or_le_centralizer hFs (N := N) (fun f _ n hn => hN.conj_mem n hn f) with h | h
  · exact h
  · exact absurd (le_bot_iff.1 (hFc ▸ h)) hN1

theorem pPrimeCore_eq_bot [Finite G] (hFc : Subgroup.centralizer (F : Set G) = ⊥)
    (hFeven : Even (Nat.card ↥F)) {L : Subgroup G} (hFL : F ≤ L) :
    pPrimeCore 2 ↥L = ⊥ := by
  have hnorm : ∀ f ∈ F, ∀ n ∈ (pPrimeCore 2 ↥L).map L.subtype,
      f * n * f⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    rintro f hf _ ⟨o, ho, rfl⟩
    have hO : (pPrimeCore 2 ↥L).Normal := inferInstance
    exact ⟨⟨f, hFL hf⟩ * o * ⟨f, hFL hf⟩⁻¹, hO.conj_mem o ho _, by simp⟩
  rcases le_or_le_centralizer hFs hnorm with h | h
  · exfalso
    have hdvd : Nat.card ↥F ∣ Nat.card ↥((pPrimeCore 2 ↥L).map L.subtype) :=
      Subgroup.card_dvd_of_le h
    rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
    have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥L)) :=
      Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥L))
    exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd hdvd)) hFeven
  · rw [hFc, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at h
    exact h

end Socle

theorem normalClosure_singleton_eq (z : G) :
    Subgroup.normalClosure ({z} : Set G) = Subgroup.closure (conjugatesOf z) := by
  have hset : Group.conjugatesOfSet ({z} : Set G) = conjugatesOf z := by
    ext x
    rw [Group.mem_conjugatesOfSet_iff]
    constructor
    · rintro ⟨a, ha, h⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact h
    · intro h
      exact ⟨z, Set.mem_singleton z, h⟩
  rw [Subgroup.normalClosure, hset]

section Analysis

variable {z : G}

theorem closure_conjugatesOf_eq_and_isBenderGroup [Finite G] (hz : orderOf z = 2)
    {F : Subgroup G} [hFn : F.Normal] (hFs : IsSimpleGroup ↥F)
    (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) (hFc : Subgroup.centralizer (F : Set G) = ⊥)
    {L : Subgroup G} (hL : Subgroup.closure (conjugatesOf z) = L) {M : Subgroup ↥L}
    (hZD : ZDConclusion ↥L {l | (l : G) ∈ conjugatesOf z} M) :
    L = F ∧ BenderSuzuki.IsBenderGroup ↥L ∧ ∀ t ∈ L, orderOf t = 2 → IsConj z t := by
  have hLn : L.Normal := hL ▸ (isInvariantInvolutionSet hz).normal_closure
  have hzL : z ∈ L := hL ▸ Subgroup.subset_closure mem_conjugatesOf_self
  have hL1 : L ≠ ⊥ := by
    intro h
    have hz1 : z = 1 := by rw [← Subgroup.mem_bot, ← h]; exact hzL
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hFL : F ≤ L := le_of_normal hFs hFc hL1
  have : IsSimpleGroup ↥F := hFs
  have hFnab' : ∃ a b : ↥F, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, h⟩ := hFnab
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun e => h (congrArg Subtype.val e)⟩
  have hFeven : Even (Nat.card ↥F) := CFSG.GH74.even_card_of_nonabelian_simple hFnab'
  rcases hZD with hrank | ⟨u, -, -, hDu, -, hcomm, -, -, hBender, -, -⟩
  · exfalso
    have h2 : 2 ≤ CFSG.Assembly.twoRank ↥F :=
      CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound ↥F hFnab' hFeven
    have h3 : CFSG.Open.twoRank ↥F ≤ CFSG.Open.twoRank ↥L :=
      CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective (Subgroup.inclusion hFL)
        (Subgroup.inclusion_injective hFL)
    have h4 : CFSG.Assembly.twoRank ↥F = CFSG.Open.twoRank ↥F := rfl
    omega
  have hO : pPrimeCore 2 ↥L = ⊥ := pPrimeCore_eq_bot hFs hFc hFeven hFL
  have hcomm' : ∀ d ∈ commutator ↥L, u * d = d * u := by
    intro d hd
    have hmem : ⁅u, d⁆ ∈ pPrimeCore 2 ↥L :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hd)
    rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hcent : ∀ l : ↥L, l * u = u * l := by
    have hle : commutator ↥L ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer {u} := by
      refine sup_le (fun d hd => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm' d hd).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    intro l
    have hl : l ∈ Subgroup.centralizer {u} := hle (by rw [hDu]; exact Subgroup.mem_top l)
    exact Subgroup.mem_centralizer_singleton_iff.1 hl
  have hu1 : u = 1 := by
    have huc : (u : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val (hcent ⟨f, hFL hf⟩)
    rw [hFc, Subgroup.mem_bot] at huc
    exact Subtype.ext huc
  have hD : commutator ↥L = ⊤ := by
    rw [hu1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hDu
    exact hDu
  obtain ⟨e, -⟩ := exists_mulEquiv_derivedBar ↥L hD hO
  have hLB : BenderSuzuki.IsBenderGroup ↥L := isBenderGroup_of_mulEquiv e hBender
  have hconj : ∀ t ∈ L, orderOf t = 2 → IsConj z t := by
    intro t ht ht2
    have h := CFSG.Asc75.isConj_of_involutions_bender hLB
      (x := (⟨z, hzL⟩ : ↥L)) (y := ⟨t, ht⟩) (by rw [Subgroup.orderOf_mk, hz])
      (by rw [Subgroup.orderOf_mk, ht2])
    exact L.subtype.map_isConj h
  refine ⟨le_antisymm ?_ hFL, hLB, hconj⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hFeven)
  have htz : IsConj z (t : G) := hconj _ (hFL t.2) (by rw [Subgroup.orderOf_coe, ht])
  have hzF : z ∈ F := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htz.symm
    rw [← hc]
    exact hFn.conj_mem _ t.2 c
  rw [← hL, Subgroup.closure_le]
  intro x hx
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  exact hFn.conj_mem _ hzF c

theorem isStronglyEmbeddedOrder_subgroupOf [Finite G] {H : Subgroup G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c) (hPD : IsProductDisconnected (conjugatesOf z) H)
    (hconj : ∀ t ∈ Subgroup.closure (conjugatesOf z), orderOf t = 2 → IsConj z t) :
    BenderSuzuki.IsStronglyEmbeddedOrder (H.subgroupOf (Subgroup.closure (conjugatesOf z))) := by
  set L := Subgroup.closure (conjugatesOf z) with hL
  obtain ⟨-, ⟨x, hx, hxH⟩, hb, -⟩ := hPD
  have hxL : x ∈ L := Subgroup.subset_closure hx
  have hx2 : orderOf x = 2 := (isInvariantInvolutionSet hz).1 x hx
  refine isStronglyEmbeddedOrder_of_involutions (t₀ := ⟨x, hxL⟩) ?_
    (Subgroup.mem_subgroupOf.2 hxH) (by rw [Subgroup.orderOf_mk, hx2]) ?_
  · intro htop
    apply hH
    have hLH : L ≤ H := Subgroup.subgroupOf_eq_top.1 htop
    obtain ⟨c, -, huniq⟩ := h1
    have hall : ∀ a : G, z • (a : G ⧸ H) = a := fun a =>
      (smul_coe_eq_iff H z a).2 (hLH (Subgroup.subset_closure (isConj_iff.2 ⟨a⁻¹, by group⟩)))
    rw [eq_top_iff]
    intro g _
    have hg : (g : G ⧸ H) = ((1 : G) : G ⧸ H) := (huniq _ (hall g)).trans (huniq _ (hall 1)).symm
    simpa using QuotientGroup.eq.1 hg
  · intro t htM ht2 g hg
    rw [Subgroup.mem_subgroupOf] at htM hg ⊢
    have htz : IsConj z (t : G) := hconj _ t.2 (by rw [Subgroup.orderOf_coe, ht2])
    have hg' : (g : G)⁻¹ * t * g ∈ H := by simpa using hg
    exact (hb _ htz htM (g : G)).1 hg'

end Analysis

section Lemma39

variable [Finite G] {H : Subgroup G} {z : G}

theorem lemma_3_9_of_ZD (hZD : S_ZD) (hH : H ≠ ⊤) (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {F : Subgroup G} [F.Normal] (hFs : IsSimpleGroup ↥F)
    (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) (hFc : Subgroup.centralizer (F : Set G) = ⊥) :
    Subgroup.normalClosure ({z} : Set G) = F ∧ BenderSuzuki.IsBenderGroup ↥F ∧
      BenderSuzuki.IsStronglyEmbeddedOrder
        (H.subgroupOf (Subgroup.normalClosure ({z} : Set G))) := by
  have hPD := isProductDisconnected hH hz h1 h2
  obtain ⟨hLF, hLB, hconj⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz hFs hFnab hFc rfl
    (hZD G (conjugatesOf z) H (isInvariantInvolutionSet hz) hPD)
  rw [normalClosure_singleton_eq]
  exact ⟨hLF, hLF ▸ hLB, isStronglyEmbeddedOrder_subgroupOf hH hz h1 hPD hconj⟩

theorem lemma_3_9_simple_of_ZD (hZD : S_ZD) [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hH : H ≠ ⊤) (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c) :
    BenderSuzuki.IsBenderGroup G ∧ BenderSuzuki.IsStronglyEmbeddedOrder H := by
  have hPD := isProductDisconnected hH hz h1 h2
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  obtain ⟨hLT, hLB, hconj⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz hTs hTnab hTc rfl
    (hZD G (conjugatesOf z) H (isInvariantInvolutionSet hz) hPD)
  refine ⟨?_, ?_⟩
  · rw [hLT] at hLB
    exact isBenderGroup_of_mulEquiv Subgroup.topEquiv.symm hLB
  · obtain ⟨-, ⟨x, hx, hxH⟩, hb, -⟩ := hPD
    refine isStronglyEmbeddedOrder_of_involutions hH hxH
      ((isInvariantInvolutionSet hz).1 x hx) ?_
    intro t htH ht2 g hg
    have htz : IsConj z t := hconj t (by rw [hLT]; exact Subgroup.mem_top t) ht2
    exact (hb t htz htH g).1 hg

end Lemma39

end CFSG.StronglyEmbedded.UniqueCoset
