module

public import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation
public import Mathlib.GroupTheory.IsPerfect

public noncomputable section

namespace CFSG.Quasithin.SteinbergBQ

open Module

section MaxAbNormal

variable {G : Type*} [Group G]

@[expose] def IsMaxAbNormal (A : Subgroup G) : Prop :=
  A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
    ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → A ≤ B → B = A

theorem le_centralizer_of_comm {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    A ≤ Subgroup.centralizer (A : Set G) :=
  fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => hA b hb a ha

theorem comm_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hAB : B ≤ Subgroup.centralizer (A : Set G)) :
    ∀ a ∈ A ⊔ B, ∀ b ∈ A ⊔ B, a * b = b * a := by
  have h1 : A ⊔ B ≤ Subgroup.centralizer (A : Set G) := sup_le (le_centralizer_of_comm hA) hAB
  have h2 : A ⊔ B ≤ Subgroup.centralizer (B : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.1 hAB) (le_centralizer_of_comm hB)
  have h3 : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.1 h1) (Subgroup.le_centralizer_iff.1 h2)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (h3 hb) a ha)

theorem exists_isMaxAbNormal [Finite G] : ∃ A : Subgroup G, IsMaxAbNormal A := by
  let S : Set (Subgroup G) := {B | B.Normal ∧ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a}
  have hS : S.Nonempty := ⟨⊥, ⟨inferInstance, fun a ha b hb => by
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩⟩
  obtain ⟨A, hA⟩ := S.toFinite.exists_maximal hS
  exact ⟨A, hA.1.1, hA.1.2, fun B hBn hBc hAB => le_antisymm (hA.2 ⟨hBn, hBc⟩ hAB) hAB⟩

theorem center_le_of_isMaxAbNormal {A : Subgroup G} (hA : IsMaxAbNormal A) :
    Subgroup.center G ≤ A := by
  have := hA.1
  have hc : ∀ a ∈ Subgroup.center G, ∀ b ∈ Subgroup.center G, a * b = b * a :=
    fun a ha _ _ => (Subgroup.mem_center_iff.1 ha _).symm
  have h := hA.2.2 (A ⊔ Subgroup.center G) (Subgroup.sup_normal _ _)
    (comm_sup hA.2.1 hc (Subgroup.center_le_centralizer _)) le_sup_left
  rw [← h]
  exact le_sup_right

theorem centralizer_eq_of_isMaxAbNormal [Finite G] {ℓ : ℕ} [Fact ℓ.Prime] (hG : IsPGroup ℓ G)
    {A : Subgroup G} (hA : IsMaxAbNormal A) : Subgroup.centralizer (A : Set G) = A := by
  have := hA.1
  refine le_antisymm ?_ (le_centralizer_of_comm hA.2.1)
  by_contra hle
  set C := Subgroup.centralizer (A : Set G)
  set π := QuotientGroup.mk' A
  have hQ : Group.IsNilpotent (G ⧸ A) := (hG.to_quotient A).isNilpotent
  have hCn : (C.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective A)
  have hC0 : C.map π ≠ ⊥ := by
    intro h
    apply hle
    intro c hc
    have : π c ∈ C.map π := Subgroup.mem_map_of_mem π hc
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hC0)
  obtain ⟨⟨x, hxC, rfl⟩, hyZ⟩ := Subgroup.mem_inf.1 hy
  have hy1' : π x ≠ 1 := fun h => hy1 (Subtype.ext h)
  let B := (Subgroup.zpowers (π x)).comap π
  have hBn : B.Normal := by
    refine Subgroup.Normal.comap ⟨fun n hn g => ?_⟩ π
    obtain ⟨m, rfl⟩ := hn
    have hz : (π x) ^ m ∈ Subgroup.center (G ⧸ A) := Subgroup.zpow_mem _ hyZ m
    show g * (π x) ^ m * g⁻¹ ∈ _
    rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ m
  have hAB : A ≤ B := fun a ha => by
    change π a ∈ Subgroup.zpowers (π x)
    rw [show π a = 1 from (QuotientGroup.eq_one_iff a).2 ha]
    exact Subgroup.one_mem _
  have hBsup : B ≤ A ⊔ Subgroup.zpowers x := by
    intro b hb
    obtain ⟨m, hm⟩ := hb
    have hm' : π (x ^ m) = π b := by rw [map_zpow]; exact hm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hm'
    have e : b = x ^ m * ((x ^ m)⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x m))
      (Subgroup.mem_sup_left hm')
  have hxcomm : Subgroup.zpowers x ≤ C := (Subgroup.zpowers_le).2 hxC
  have hcx : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    simp only [← zpow_add, add_comm]
  have hcomm := comm_sup hA.2.1 hcx hxcomm
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    hcomm a (hBsup ha) b (hBsup hb)
  have hBA := hA.2.2 B hBn hBc hAB
  apply hy1'
  have hxB : x ∈ B := ⟨1, zpow_one (π x)⟩
  rw [hBA] at hxB
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hxB

theorem sup_eq_top_and_inf_eq_center {A A' : Subgroup G} (hA : IsMaxAbNormal A)
    (hA' : IsMaxAbNormal A') (hne : A ≠ A') {ℓ : ℕ} (hℓ : ℓ.Prime) (hidx : A.index = ℓ) :
    A ⊔ A' = ⊤ ∧ A ⊓ A' = Subgroup.center G := by
  have := hA.1
  have hnle : ¬ A' ≤ A := fun h => hne (hA'.2.2 A hA.1 hA.2.1 h)
  have hsup : A ⊔ A' = ⊤ := by
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ A')
    rw [hidx] at h1
    have h2 : A.relIndex (A ⊔ A') ≠ 1 := fun h =>
      hnle ((Subgroup.relIndex_eq_one.1 h).trans' le_sup_right)
    rcases (Nat.dvd_prime hℓ).1 (Dvd.intro _ h1) with h | h
    · exact absurd h h2
    · rw [h] at h1
      exact Subgroup.index_eq_one.1 (by
        have := hℓ.pos
        nlinarith [h1])
  refine ⟨hsup, le_antisymm ?_ (le_inf (center_le_of_isMaxAbNormal hA)
    (center_le_of_isMaxAbNormal hA'))⟩
  have h1 : A ≤ Subgroup.centralizer ((A ⊓ A' : Subgroup G) : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun z hz => hA.2.1 z hz.1 a ha
  have h2 : A' ≤ Subgroup.centralizer ((A ⊓ A' : Subgroup G) : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun z hz => hA'.2.1 z hz.2 a ha
  have h3 := Subgroup.le_centralizer_iff.1 (sup_le h1 h2)
  rw [hsup, Subgroup.coe_top, Subgroup.centralizer_univ] at h3
  exact h3

theorem card_le_of_inf_eq [Finite G] {Z : Subgroup G} {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (M : Finset (Subgroup G)) (hMZ : ∀ A ∈ M, Z ≤ A ∧ Nat.card A = ℓ * Nat.card Z)
    (hM : ∀ A ∈ M, ∀ A' ∈ M, A ≠ A' → A ⊓ A' = Z) (hG : Nat.card G = ℓ ^ 2 * Nat.card Z) :
    M.card ≤ ℓ + 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  let S : Subgroup G → Finset G := fun A => (A : Set G).toFinset \ (Z : Set G).toFinset
  have hcardS : ∀ A ∈ M, (S A).card = (ℓ - 1) * Nat.card Z := by
    intro A hA
    rw [Finset.card_sdiff_of_subset (Set.toFinset_subset_toFinset.2 (hMZ A hA).1),
      ← Nat.card_eq_card_toFinset, ← Nat.card_eq_card_toFinset]
    change Nat.card A - Nat.card Z = _
    rw [(hMZ A hA).2, Nat.sub_one_mul]
  have hdisj : (M : Set (Subgroup G)).PairwiseDisjoint S := by
    intro A hA A' hA' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [S, Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hx hx'
    have : x ∈ A ⊓ A' := ⟨hx.1, hx'.1⟩
    rw [hM A hA A' hA' hne] at this
    exact hx.2 this
  have hsub : M.biUnion S ⊆ Finset.univ \ (Z : Set G).toFinset := by
    intro x hx
    obtain ⟨A, -, hx⟩ := Finset.mem_biUnion.1 hx
    simp only [S, Finset.mem_sdiff] at hx
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcardS, Finset.sum_const, smul_eq_mul,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    ← Nat.card_eq_card_toFinset, ← Nat.card_eq_fintype_card, hG] at h1
  have h2 : M.card * (ℓ - 1) * Nat.card Z ≤ (ℓ + 1) * (ℓ - 1) * Nat.card Z := by
    have e : (ℓ + 1) * (ℓ - 1) = ℓ ^ 2 - 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      symm
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [e, Nat.sub_one_mul]
    calc M.card * (ℓ - 1) * Nat.card Z = M.card * ((ℓ - 1) * Nat.card Z) := by ring
      _ ≤ ℓ ^ 2 * Nat.card Z - Nat.card Z := h1
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_right h2 hZpos) (by omega)

end MaxAbNormal

section Weights

open CFSG.LinearAlgebra.SteinbergBQ TensorProduct
open CFSG.Walter.JT (weightSpace mem_weightSpace weights)

theorem sum_finrank_ne_bot {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {W : ι → Submodule K E} (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤)
    [Fintype {i // W i ≠ ⊥}] : ∑ i : {i // W i ≠ ⊥}, finrank K (W i) = finrank K E := by
  classical
  have e := (iSupIndep_ne_bot.2 hind).linearEquiv (by rw [iSup_ne_bot_subtype]; exact htop)
  rw [← e.finrank_eq]
  exact (Module.finrank_directSum K (fun i : {i // W i ≠ ⊥} => W i)).symm

theorem exists_smul_of_finrank_eq_one {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {W : Submodule K E} (hW : finrank K W = 1) (f : E →ₗ[K] E) (hf : ∀ v ∈ W, f v ∈ W) :
    ∃ c : K, ∀ v ∈ W, f v = c • v := by
  obtain ⟨w₀, -, hspan⟩ := finrank_eq_one_iff'.1 hW
  obtain ⟨c, hc⟩ := hspan ⟨f w₀, hf w₀ w₀.2⟩
  refine ⟨c, fun v hv => ?_⟩
  obtain ⟨t, ht⟩ := hspan ⟨v, hv⟩
  have hv' : v = t • (w₀ : E) := (congrArg Subtype.val ht).symm
  have hc' : f w₀ = c • (w₀ : E) := (congrArg Subtype.val hc).symm
  rw [hv', map_smul, hc', smul_comm]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L]

omit [FiniteDimensional k V] [IsAlgClosed L] in
theorem bcRep_comm {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ a ∈ (⊤ : Subgroup A), ∀ b ∈ (⊤ : Subgroup A),
      bcRep L A a * bcRep L A b = bcRep L A b * bcRep L A a := by
  intro a _ b _
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hAcomm a a.2 b b.2)

omit [FiniteDimensional k V] [Algebra k L] [IsAlgClosed L] in
theorem natCard_top_ne_zero {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hAchar : ((Nat.card A : ℕ) : L) ≠ 0) : ((Nat.card (⊤ : Subgroup A) : ℕ) : L) ≠ 0 := by
  rw [Subgroup.card_top]
  exact hAchar

omit [FiniteDimensional k V] [IsAlgClosed L] in
theorem bcEnd_mem_weightSpace_of_mem_centralizer {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    {g : LinearMap.GeneralLinearGroup k V}
    (hg : g ∈ Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    {χ : (⊤ : Subgroup A) → L} {v : L ⊗[k] V} (hv : v ∈ weightSpace (bcRep L A) ⊤ χ) :
    bcEnd L g v ∈ weightSpace (bcRep L A) ⊤ χ := by
  rw [mem_weightSpace] at hv ⊢
  intro n
  rw [bcRep_apply, ← Module.End.mul_apply, ← bcEnd_mul,
    Subgroup.mem_centralizer_iff.1 hg _ n.1.2, bcEnd_mul, Module.End.mul_apply, ← bcRep_apply,
    hv n, map_smul]

theorem commute_of_card_weights_eq_finrank {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    [Finite A] (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAchar : ((Nat.card A : ℕ) : L) ≠ 0)
    (hcard : Nat.card (weights (bcRep L A) ⊤) = finrank k V) :
    ∀ g ∈ Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V)),
      ∀ h ∈ Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V)), g * h = h * g := by
  classical
  obtain ⟨hind, htop⟩ := CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top (bcRep L A) ⊤
    (bcRep_comm L hAcomm) (natCard_top_ne_zero L hAchar)
  let : Fintype {χ // weightSpace (bcRep L A) ⊤ χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  have hsum := sum_finrank_ne_bot hind htop
  rw [Module.finrank_baseChange] at hsum
  have hcard' : Fintype.card {χ // weightSpace (bcRep L A) ⊤ χ ≠ ⊥} = finrank k V := by
    rw [← hcard, Nat.card_eq_fintype_card]
  have hone : ∀ χ : {χ // weightSpace (bcRep L A) ⊤ χ ≠ ⊥},
      finrank L (weightSpace (bcRep L A) ⊤ χ) = 1 := by
    have hle : ∀ χ ∈ (Finset.univ : Finset {χ // weightSpace (bcRep L A) ⊤ χ ≠ ⊥}),
        (fun _ => 1) χ ≤ finrank L (weightSpace (bcRep L A) ⊤ χ) :=
      fun χ _ => Submodule.one_le_finrank_iff.2 χ.2
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by
      rw [hsum, Finset.sum_const, Finset.card_univ, hcard', smul_eq_mul, mul_one])
    exact fun χ => (heq χ (Finset.mem_univ _)).symm
  intro g hg h hh
  have hloc : ∀ χ, weightSpace (bcRep L A) ⊤ χ ≤
      LinearMap.eqLocus (bcEnd L (g * h)) (bcEnd L (h * g)) := by
    intro χ v hv
    by_cases hχ : weightSpace (bcRep L A) ⊤ χ = ⊥
    · rw [hχ, Submodule.mem_bot] at hv
      rw [hv]
      exact (LinearMap.eqLocus _ _).zero_mem
    · have h1 := hone ⟨χ, hχ⟩
      obtain ⟨c, hc⟩ := exists_smul_of_finrank_eq_one h1 (bcEnd L g)
        fun w hw => bcEnd_mem_weightSpace_of_mem_centralizer L hg hw
      obtain ⟨d, hd⟩ := exists_smul_of_finrank_eq_one h1 (bcEnd L h)
        fun w hw => bcEnd_mem_weightSpace_of_mem_centralizer L hh hw
      change bcEnd L (g * h) v = bcEnd L (h * g) v
      rw [bcEnd_mul, bcEnd_mul, Module.End.mul_apply, Module.End.mul_apply, hd v hv, hc v hv,
        map_smul, map_smul, hc v hv, hd v hv, smul_comm]
  have htop' : LinearMap.eqLocus (bcEnd L (g * h)) (bcEnd L (h * g)) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le hloc
  exact bcEnd_injective L (LinearMap.eqLocus_eq_top.mp htop')

theorem isSolvable_normalizer_of_card_weights_eq_finrank (hV : finrank k V ≤ 4)
    {A : Subgroup (LinearMap.GeneralLinearGroup k V)} [Finite A]
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAchar : ((Nat.card A : ℕ) : L) ≠ 0)
    (hcard : Nat.card (weights (bcRep L A) ⊤) = finrank k V) :
    Group.IsSolvable (Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) := by
  obtain ⟨hfin, -⟩ := CFSG.Walter.JT.finite_weights_and_card_le (bcRep L A) ⊤
    (bcRep_comm L hAcomm) (natCard_top_ne_zero L hAchar)
  have hker := ker_weightPermGL L hAcomm hAchar
  have hcomm := commute_of_card_weights_eq_finrank L hAcomm hAchar hcard
  have : Group.IsSolvable (weightPermGL L A).ker := Group.isSolvable_of_comm fun x y => by
    have hx : ((x : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) :
        LinearMap.GeneralLinearGroup k V) ∈
        Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V)) :=
      Subgroup.mem_subgroupOf.1 (hker ▸ x.2)
    have hy : ((y : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) :
        LinearMap.GeneralLinearGroup k V) ∈
        Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V)) :=
      Subgroup.mem_subgroupOf.1 (hker ▸ y.2)
    exact Subtype.ext (Subtype.ext (hcomm _ hx _ hy))
  have : Group.IsSolvable (Equiv.Perm (weights (bcRep L A) ⊤)) :=
    Equiv.Perm.isSolvable (by rw [hcard]; exact hV)
  exact Group.isSolvable_of_ker_le_range (weightPermGL L A).ker.subtype (weightPermGL L A)
    (by rw [Subgroup.range_subtype])

omit [IsAlgClosed L] in
theorem finrank_weightSpace_weightPermGL {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (g : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (χ : weights (bcRep L A) ⊤) :
    finrank L (weightSpace (bcRep L A) ⊤ (weightPermGL L A g χ).1) =
      finrank L (weightSpace (bcRep L A) ⊤ χ.1) := by
  have hinj : ∀ x : LinearMap.GeneralLinearGroup k V, Function.Injective (bcEnd L x) :=
    fun x u w huw => by rw [← bcEnd_inv_apply L x u, huw, bcEnd_inv_apply]
  have key : ∀ (x : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
      (ψ : (⊤ : Subgroup A) → L), finrank L (weightSpace (bcRep L A) ⊤ ψ) ≤
        finrank L (weightSpace (bcRep L A) ⊤ (twistGL L x ψ)) := by
    intro x ψ
    let f : weightSpace (bcRep L A) ⊤ ψ →ₗ[L] weightSpace (bcRep L A) ⊤ (twistGL L x ψ) :=
      (bcEnd L (x : LinearMap.GeneralLinearGroup k V)).restrict
        fun v hv => map_mem_weightSpace_twistGL L x hv
    exact LinearMap.finrank_le_finrank_of_injective (f := f) fun u w huw =>
      Subtype.ext (hinj _ (congrArg Subtype.val huw))
  rw [weightPermGL_apply_val]
  refine le_antisymm ?_ (key g χ.1)
  have h := key g⁻¹ (twistGL L g χ.1)
  rwa [← twistGL_mul, inv_mul_cancel, twistGL_one] at h

end Weights

section Conj

variable {G : Type*} [Group G]

@[expose] def normConj (P : Subgroup G) : Subgroup.normalizer (P : Set G) →* MulAut P where
  toFun n :=
    { toFun := fun x => ⟨n * x * n⁻¹, (Subgroup.mem_normalizer_iff.1 n.2 x).1 x.2⟩
      invFun := fun x => ⟨n⁻¹ * x * n, by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ n.2) x).1 x.2
        simpa using this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' n m := MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem coe_normConj_apply (P : Subgroup G) (n : Subgroup.normalizer (P : Set G)) (x : P) :
    ((normConj P n x : P) : G) = n * x * n⁻¹ := rfl

theorem map_symm_map (σ : MulAut G) (B : Subgroup G) :
    (B.map σ.toMonoidHom).map σ.symm.toMonoidHom = B := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id B
  ext x
  simp

theorem map_map_symm (σ : MulAut G) (B : Subgroup G) :
    (B.map σ.symm.toMonoidHom).map σ.toMonoidHom = B := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id B
  ext x
  simp

theorem isMaxAbNormal_map {A : Subgroup G} (hA : IsMaxAbNormal A) (σ : MulAut G) :
    IsMaxAbNormal (A.map σ.toMonoidHom) := by
  have := hA.1
  refine ⟨Subgroup.Normal.map hA.1 σ.toMonoidHom σ.surjective, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.2.1 a ha b hb]
  · intro B hBn hBc hAB
    have h1 : A ≤ B.map σ.symm.toMonoidHom := by
      rw [← map_symm_map σ A]
      exact Subgroup.map_mono hAB
    have h2 := hA.2.2 (B.map σ.symm.toMonoidHom)
      (Subgroup.Normal.map hBn σ.symm.toMonoidHom σ.symm.surjective)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hBc a ha b hb]) h1
    rw [← h2]
    exact (map_map_symm σ B).symm

@[expose] def maxAbPermFun (σ : MulAut G) : Equiv.Perm {A : Subgroup G // IsMaxAbNormal A} where
  toFun A := ⟨A.1.map σ.toMonoidHom, isMaxAbNormal_map A.2 σ⟩
  invFun A := ⟨A.1.map σ.symm.toMonoidHom, isMaxAbNormal_map A.2 σ.symm⟩
  left_inv A := Subtype.ext (map_symm_map σ A.1)
  right_inv A := Subtype.ext (map_map_symm σ A.1)

theorem coe_maxAbPermFun (σ : MulAut G) (A : {A : Subgroup G // IsMaxAbNormal A}) :
    ((maxAbPermFun σ A : {A : Subgroup G // IsMaxAbNormal A}) : Subgroup G) =
      A.1.map σ.toMonoidHom := rfl

@[expose] def maxAbPerm (G : Type*) [Group G] :
    MulAut G →* Equiv.Perm {A : Subgroup G // IsMaxAbNormal A} where
  toFun := maxAbPermFun
  map_one' := Equiv.ext fun A => Subtype.ext (Subgroup.map_id A.1)
  map_mul' σ τ := Equiv.ext fun A => Subtype.ext (by
    rw [Equiv.Perm.mul_apply, coe_maxAbPermFun, coe_maxAbPermFun, coe_maxAbPermFun,
      Subgroup.map_map]
    rfl)

end Conj

theorem card_eq_mul_card_center {G : Type*} [Group G] {A A' : Subgroup G} (hA : IsMaxAbNormal A)
    (hA' : IsMaxAbNormal A') (hne : A ≠ A') {ℓ : ℕ} (hℓ : ℓ.Prime) (hidx : A.index = ℓ) :
    Nat.card A' = ℓ * Nat.card (Subgroup.center G) := by
  obtain ⟨hsup, hinf⟩ := sup_eq_top_and_inf_eq_center hA hA' hne hℓ hidx
  have := hA.1
  have h1 : (A' ⊓ A).relIndex A' = ℓ := by
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_sup_left A' A, hsup,
      Subgroup.relIndex_top_right, hidx]
  have h2 := Subgroup.relIndex_mul_card (H := A' ⊓ A) (K := A')
  rw [h1, inf_right_comm, inf_idem, inf_comm, hinf] at h2
  exact h2.symm

section Core

open CFSG.LinearAlgebra.SteinbergBQ TensorProduct
open CFSG.Walter.JT (weightSpace mem_weightSpace weights)

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L]

omit [FiniteDimensional k V] in
theorem le_normalizer_map {P : Subgroup (LinearMap.GeneralLinearGroup k V)} (A : Subgroup P)
    (hA : A.Normal) :
    P ≤ Subgroup.normalizer
      ((A.map P.subtype : Subgroup (LinearMap.GeneralLinearGroup k V)) :
        Set (LinearMap.GeneralLinearGroup k V)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨x, hx⟩ * a * ⟨x, hx⟩⁻¹, hA.conj_mem a ha _, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨x, hx⟩⁻¹ * a * ⟨x, hx⟩, ?_, ?_⟩
    · have := hA.conj_mem a ha ⟨x, hx⟩⁻¹
      simpa using this
    · have he' : (a : LinearMap.GeneralLinearGroup k V) = x * h * x⁻¹ := he
      change (x⁻¹ * (a : LinearMap.GeneralLinearGroup k V) * x) = h
      rw [he']
      group

@[expose] def weightPermP {P : Subgroup (LinearMap.GeneralLinearGroup k V)} (A : Subgroup P)
    (hA : A.Normal) : P →* Equiv.Perm (weights (bcRep L (A.map P.subtype)) ⊤) :=
  (weightPermGL L (A.map P.subtype)).comp (Subgroup.inclusion (le_normalizer_map A hA))

omit [FiniteDimensional k V] [Algebra k L] [IsAlgClosed L] in
theorem map_subtype_facts {P : Subgroup (LinearMap.GeneralLinearGroup k V)} [Finite P]
    (hP : ((Nat.card P : ℕ) : L) ≠ 0) (A : Subgroup P)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Finite (A.map P.subtype) ∧
      (∀ a ∈ A.map P.subtype, ∀ b ∈ A.map P.subtype, a * b = b * a) ∧
      ((Nat.card (A.map P.subtype) : ℕ) : L) ≠ 0 := by
  refine ⟨Finite.of_equiv _ (A.equivMapOfInjective P.subtype P.subtype_injective).toEquiv, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAcomm a ha b hb]
  · rw [Subgroup.card_map_of_injective P.subtype_injective]
    intro h
    apply hP
    obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card A
    rw [hm, Nat.cast_mul, h, zero_mul]

theorem ker_weightPermP {P : Subgroup (LinearMap.GeneralLinearGroup k V)} [Finite P]
    (hP : ((Nat.card P : ℕ) : L) ≠ 0) (A : Subgroup P) (hA : A.Normal)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    (weightPermP L A hA).ker = Subgroup.centralizer (A : Set P) := by
  obtain ⟨hfin, hAcomm', hAchar⟩ := map_subtype_facts L hP A hAcomm
  ext g
  rw [MonoidHom.mem_ker, weightPermP, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    ker_weightPermGL L hAcomm' hAchar, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro H a ha
    exact Subtype.ext (H _ ⟨a, ha, rfl⟩)
  · rintro H _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (H a ha)

theorem isMaxAbNormal_weights_and_index (hV : finrank k V = 3) {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Subgroup (LinearMap.GeneralLinearGroup k V)} [Finite P] (hP : IsPGroup ℓ P)
    (hPchar : ((Nat.card P : ℕ) : L) ≠ 0) (hnab : ¬ ∀ a b : P, a * b = b * a) {A : Subgroup P}
    (hA : IsMaxAbNormal A) :
    Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) = 3 ∧ A.index = ℓ ∧ (ℓ = 2 ∨ ℓ = 3) := by
  classical
  have := hA.1
  obtain ⟨hfinA, hAcomm', hAchar⟩ := map_subtype_facts L hPchar A hA.2.1
  have hcent := centralizer_eq_of_isMaxAbNormal hP hA
  have hker := ker_weightPermP L hPchar A hA.1 hA.2.1
  rw [hcent] at hker
  obtain ⟨hind, htop⟩ := CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top
    (bcRep L (A.map P.subtype)) ⊤ (bcRep_comm L hAcomm') (natCard_top_ne_zero L hAchar)
  let : Fintype {χ // weightSpace (bcRep L (A.map P.subtype)) ⊤ χ ≠ ⊥} :=
    hind.fintypeNeBotOfFiniteDimensional
  have hsum := sum_finrank_ne_bot hind htop
  rw [Module.finrank_baseChange, hV] at hsum
  have hfin : Finite (weights (bcRep L (A.map P.subtype)) ⊤) := inferInstance
  have hdvd : A.index ∣ (Nat.card (weights (bcRep L (A.map P.subtype)) ⊤)).factorial := by
    have h := Subgroup.index_ker (weightPermP L A hA.1)
    rw [hker] at h
    rw [h, ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card _
  have hAtop : A ≠ ⊤ := fun h => hnab fun a b =>
    hA.2.1 a (h ▸ Subgroup.mem_top a) b (h ▸ Subgroup.mem_top b)
  have hidx1 : A.index ≠ 1 := fun h => hAtop (Subgroup.index_eq_one.1 h)
  have hcardr : Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) =
      Fintype.card {χ // weightSpace (bcRep L (A.map P.subtype)) ⊤ χ ≠ ⊥} :=
    Nat.card_eq_fintype_card
  have hle : Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) ≤ 3 := by
    have := (CFSG.Walter.JT.finite_weights_and_card_le (bcRep L (A.map P.subtype)) ⊤
      (bcRep_comm L hAcomm') (natCard_top_ne_zero L hAchar)).2
    rwa [Module.finrank_baseChange, hV] at this
  have hr : Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) = 3 := by
    rcases (by omega : Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) ≤ 1 ∨
        Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) = 2 ∨
        Nat.card (weights (bcRep L (A.map P.subtype)) ⊤) = 3) with h1 | h2 | h3
    · exfalso
      have h1' : (Nat.card (weights (bcRep L (A.map P.subtype)) ⊤)).factorial = 1 := by
        interval_cases (Nat.card (weights (bcRep L (A.map P.subtype)) ⊤)) <;> rfl
      rw [h1'] at hdvd
      exact hidx1 (Nat.dvd_one.1 hdvd)
    · exfalso
      obtain ⟨g, hg⟩ : ∃ g : P, g ∉ A := by
        by_contra hcon
        push Not at hcon
        exact hAtop (eq_top_iff.2 fun g _ => hcon g)
      have hg1 : weightPermP L A hA.1 g ≠ 1 := fun h1 => hg (hker ▸ MonoidHom.mem_ker.2 h1)
      obtain ⟨χ, hχ⟩ : ∃ χ, weightPermP L A hA.1 g χ ≠ χ := by
        by_contra hcon
        push Not at hcon
        exact hg1 (Equiv.ext hcon)
      have heqd := finrank_weightSpace_weightPermGL L
        (Subgroup.inclusion (le_normalizer_map A hA.1) g) χ
      have huniv : ({χ, weightPermP L A hA.1 g χ} :
          Finset {χ // weightSpace (bcRep L (A.map P.subtype)) ⊤ χ ≠ ⊥}) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [Finset.card_pair hχ.symm, ← hcardr, h2])
      rw [← huniv, Finset.sum_pair hχ.symm] at hsum
      change finrank L (weightSpace (bcRep L (A.map P.subtype)) ⊤ χ.1) +
        finrank L (weightSpace (bcRep L (A.map P.subtype)) ⊤
          (weightPermGL L (A.map P.subtype)
            (Subgroup.inclusion (le_normalizer_map A hA.1) g) χ).1) = 3 at hsum
      rw [heqd] at hsum
      omega
    · exact h3
  refine ⟨hr, ?_⟩
  rw [hr] at hdvd
  obtain ⟨n, hn⟩ := hP.index A
  rw [hn] at hdvd hidx1 ⊢
  have hn0 : n ≠ 0 := fun h => hidx1 (by rw [h, pow_zero])
  have hℓ := (Fact.out : ℓ.Prime)
  have hℓ6 : ℓ ∣ 6 := (dvd_pow_self ℓ hn0).trans hdvd
  have hℓ23 : ℓ = 2 ∨ ℓ = 3 := by
    rcases (Nat.Prime.dvd_mul hℓ).1 (show ℓ ∣ 2 * 3 from hℓ6) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h)
  refine ⟨?_, hℓ23⟩
  have hn1 : n = 1 := by
    by_contra hn1
    have h2 : ℓ ^ 2 ∣ 6 := (pow_dvd_pow ℓ (by omega)).trans hdvd
    rcases hℓ23 with rfl | rfl <;> norm_num at h2
  rw [hn1, pow_one]

theorem isSolvable_normalizer_of_not_comm (hV : finrank k V = 3) {ℓ : ℕ} [Fact ℓ.Prime]
    (P : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite P] (hP : IsPGroup ℓ P)
    (hPchar : ((Nat.card P : ℕ) : L) ≠ 0) (hnab : ¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    Group.IsSolvable (Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) ∧
      (ℓ = 2 ∨ ℓ = 3) := by
  classical
  have hnab' : ¬ ∀ a b : P, a * b = b * a := fun h =>
    hnab fun a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
  have hℓ := (Fact.out : ℓ.Prime)
  obtain ⟨A₀, hA₀⟩ := exists_isMaxAbNormal (G := P)
  obtain ⟨hw3, -, hℓ23⟩ := isMaxAbNormal_weights_and_index L hV hP hPchar hnab' hA₀
  obtain ⟨hfinA₀, hAcomm₀, hAchar₀⟩ := map_subtype_facts L hPchar A₀ hA₀.2.1
  have hsolA₀ := isSolvable_normalizer_of_card_weights_eq_finrank L (by omega) hAcomm₀ hAchar₀
    (by rw [hw3, hV])
  have : Fintype (Subgroup P) := Fintype.ofFinite _
  set M : Finset (Subgroup P) := Finset.univ.filter IsMaxAbNormal with hMdef
  have hmem : ∀ A, A ∈ M ↔ IsMaxAbNormal A := fun A => by simp [hMdef]
  have hcardM : Nat.card {A : Subgroup P // IsMaxAbNormal A} = M.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hidx : ∀ A ∈ M, A.index = ℓ := fun A hA =>
    (isMaxAbNormal_weights_and_index L hV hP hPchar hnab' ((hmem A).1 hA)).2.1
  have hM : M.card ≤ 4 := by
    by_cases h1 : M.card ≤ 1
    · omega
    · push Not at h1
      obtain ⟨A₁, hA₁, A₂, hA₂, hne⟩ := Finset.one_lt_card.1 h1
      have hc₁ : Nat.card A₁ = ℓ * Nat.card (Subgroup.center P) :=
        card_eq_mul_card_center ((hmem _).1 hA₂) ((hmem _).1 hA₁) (Ne.symm hne) hℓ (hidx _ hA₂)
      have hle := card_le_of_inf_eq (Z := Subgroup.center P) hℓ.two_le M
        (fun A hA => ⟨center_le_of_isMaxAbNormal ((hmem A).1 hA), by
          by_cases hA1 : A = A₁
          · rw [hA1]
            exact hc₁
          · exact card_eq_mul_card_center ((hmem _).1 hA₁) ((hmem _).1 hA) (Ne.symm hA1) hℓ
              (hidx _ hA₁)⟩)
        (fun A hA A' hA' hne' =>
          (sup_eq_top_and_inf_eq_center ((hmem _).1 hA) ((hmem _).1 hA') hne' hℓ (hidx A hA)).2)
        (by
          have h2 := Subgroup.card_mul_index A₁
          rw [hc₁, hidx _ hA₁] at h2
          rw [← h2]
          ring)
      rcases hℓ23 with rfl | rfl <;> omega
  set Ψ := (maxAbPerm P).comp (normConj P) with hΨ
  have hkerle : ∀ n ∈ Ψ.ker,
      ((n : Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) :
        LinearMap.GeneralLinearGroup k V) ∈ Subgroup.normalizer
          (((A₀.map P.subtype) : Subgroup (LinearMap.GeneralLinearGroup k V)) :
            Set (LinearMap.GeneralLinearGroup k V)) := by
    intro n hn
    have h1 : A₀.map (normConj P n).toMonoidHom = A₀ := by
      have := congrArg (fun τ : Equiv.Perm {A : Subgroup P // IsMaxAbNormal A} =>
        ((τ ⟨A₀, hA₀⟩ : {A : Subgroup P // IsMaxAbNormal A}) : Subgroup P))
        (MonoidHom.mem_ker.1 hn)
      exact this
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : normConj P n a ∈ A₀ := by
        rw [← h1]
        exact ⟨a, ha, rfl⟩
      exact ⟨_, ha', rfl⟩
    · rintro ⟨b, hb, he⟩
      rw [← h1] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      refine ⟨a, ha, ?_⟩
      have he' : ((n : Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) :
          LinearMap.GeneralLinearGroup k V) * (a : LinearMap.GeneralLinearGroup k V) *
            ((n : Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) :
              LinearMap.GeneralLinearGroup k V)⁻¹ =
          (n : LinearMap.GeneralLinearGroup k V) * h *
            (n : LinearMap.GeneralLinearGroup k V)⁻¹ := he
      exact mul_left_cancel (mul_right_cancel he')
  let f : Ψ.ker →* Subgroup.normalizer
      (((A₀.map P.subtype) : Subgroup (LinearMap.GeneralLinearGroup k V)) :
        Set (LinearMap.GeneralLinearGroup k V)) :=
    { toFun := fun x => ⟨((x : Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) :
        LinearMap.GeneralLinearGroup k V), hkerle x x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y h => by
    have h' := congrArg (fun z : Subgroup.normalizer
      (((A₀.map P.subtype) : Subgroup (LinearMap.GeneralLinearGroup k V)) :
        Set (LinearMap.GeneralLinearGroup k V)) => (z : LinearMap.GeneralLinearGroup k V)) h
    exact Subtype.ext (Subtype.ext h')
  have : Group.IsSolvable Ψ.ker := Group.isSolvable_of_isSolvable_injective hf
  have : Group.IsSolvable (Equiv.Perm {A : Subgroup P // IsMaxAbNormal A}) :=
    Equiv.Perm.isSolvable (by rw [hcardM]; exact hM)
  exact ⟨Group.isSolvable_of_ker_le_range Ψ.ker.subtype Ψ (by rw [Subgroup.range_subtype]),
    hℓ23⟩

end Core

theorem le_of_perfect_of_isSolvable_quotient {G : Type*} [Group G] {N C : Subgroup G}
    [(C.subgroupOf N).Normal] (hsol : Group.IsSolvable (N ⧸ C.subgroupOf N)) {H : Subgroup G}
    (hHN : H ≤ N) (hH : ⁅H, H⁆ = H) : H ≤ C := by
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.2 hH
  let f : H →* N ⧸ C.subgroupOf N :=
    (QuotientGroup.mk' (C.subgroupOf N)).comp (Subgroup.inclusion hHN)
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro h hh
  have h1 : f ⟨h, hh⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩⟩ : f.range) 1)
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  exact h1

theorem degree_three_coprime_automizer_solvable {k V : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime]
    [CharP k p] [AddCommGroup V] [Module k V] (hV : finrank k V = 3) {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite P]
    (hP : IsPGroup ℓ P) :
    Group.IsSolvable (↥(Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) ⧸
      (Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V))).subgroupOf
        (Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V)))) ∧
    ((¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → ℓ = 2 ∨ ℓ = 3) ∧
    ∀ H : Subgroup (LinearMap.GeneralLinearGroup k V),
      H ≤ Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V)) → ⁅H, H⁆ = H →
        H ≤ Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V)) := by
  classical
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hcop : Nat.Coprime (Nat.card P) p := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.coprime_primes hℓ.out hp.out).2 hℓp)
  set L := AlgebraicClosure k
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have hPchar : ((Nat.card P : ℕ) : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L p] at h
    exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) h)
  have hsol : Group.IsSolvable (↥(Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V)))
      ⧸ (Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V))).subgroupOf
        (Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V)))) := by
    by_cases hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
    · obtain ⟨r, -, -, f, -, hsolv⟩ :=
        CFSG.LinearAlgebra.abelian_coprime_matrix_automizer_permutation_embedding (by omega) P hab
          hcop
      exact hsolv (by omega)
    · have := (isSolvable_normalizer_of_not_comm L hV P hP hPchar hab).1
      infer_instance
  exact ⟨hsol, fun hab => (isSolvable_normalizer_of_not_comm L hV P hP hPchar hab).2,
    fun H hHN hH => le_of_perfect_of_isSolvable_quotient hsol hHN hH⟩

theorem cross_characteristic_two_group_degree_three_automizer_solvable {k V : Type*} [Field k]
    {p : ℕ} [Fact p.Prime] [CharP k p] (hp2 : p ≠ 2) [AddCommGroup V] [Module k V]
    (hV : finrank k V = 3) (P : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite P]
    (hP : IsPGroup 2 P) :
    Group.IsSolvable (↥(Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V))) ⧸
      (Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V))).subgroupOf
        (Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V)))) ∧
    ∀ H : Subgroup (LinearMap.GeneralLinearGroup k V),
      H ≤ Subgroup.normalizer (P : Set (LinearMap.GeneralLinearGroup k V)) → ⁅H, H⁆ = H →
        H ≤ Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup k V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, -, h3⟩ := degree_three_coprime_automizer_solvable hV (Ne.symm hp2) P hP
  exact ⟨h1, h3⟩

end CFSG.Quasithin.SteinbergBQ
