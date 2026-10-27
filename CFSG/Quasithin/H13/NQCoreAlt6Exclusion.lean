module

public import CFSG.Quasithin.H13.NQCoreAlt6Lift
public import CFSG.Quasithin.H13.NQCoreEscapingResidual
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.Quasithin.H13.NQCoreEscapingCenter
public import CFSG.Quasithin.H13.NQCoreEscapingCore

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

theorem alternatingGroup_six_exists_mul_ne :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  by_contra hab
  push Not at hab
  have hc : center (alternatingGroup (Fin 6)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 6))
  have h1 : a ∈ center (alternatingGroup (Fin 6)) := mem_center_iff.mpr fun g => hab g a
  rw [hc, mem_bot] at h1
  exact ha h1

theorem center_eq_bot_of_mulEquiv_alt6 {S : Type*} [Group S] (e : S ≃* alternatingGroup (Fin 6)) :
    center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : center (alternatingGroup (Fin 6)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
  have h1 : e z ∈ center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y']
  rw [hc, mem_bot] at h1
  rw [mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem layer_eq_top_center_eq_bot_of_alt6 {S : Type*} [Group S]
    (e : S ≃* alternatingGroup (Fin 6)) : CFSG.layer S = ⊤ ∧ center S = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit)
    (S := fun _ => alternatingGroup (Fin 6)) (fun _ => alternatingGroup_six_exists_mul_ne)
    (e.trans (MulEquiv.piUnique fun _ : Unit => alternatingGroup (Fin 6)).symm),
    center_eq_bot_of_mulEquiv_alt6 e⟩

section Quotient

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_two_pow_mem_of_sup_eq_top {T Y : Subgroup Q} [Y.Normal] (hT : IsPGroup 2 T)
    (hYT : Y ⊔ T = ⊤) (x : Q) : ∃ k : ℕ, x ^ 2 ^ k ∈ Y := by
  have hx : x ∈ Y ⊔ T := hYT ▸ mem_top x
  obtain ⟨y, hy, t, ht, hyt⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hyt, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow]
  have ht1 : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [ht1, QuotientGroup.mk_one]

theorem eq_bot_of_isPGroup_quotient_kerIn {T X : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hTX : T ≤ X) (N : Subgroup (Q ⧸ kerIn X ⊤)) [hN : N.Normal] (hN2 : IsPGroup 2 N) :
    N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (kerIn X ⊤) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNT : N ≤ T.map π :=
    (E1.isSylowIn_two_map_top hπs hT).le_of_normal le_top inferInstance hN2
  have hNX : N.comap π ≤ X := by
    intro x hx
    obtain ⟨t, htT, hteq⟩ := hNT hx
    have h1 : t⁻¹ * x ∈ kerIn X ⊤ := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show π (t⁻¹ * x) = 1
      rw [map_mul, map_inv, hteq, inv_mul_cancel]
    have h2 : x = t * (t⁻¹ * x) := by group
    rw [h2]
    exact X.mul_mem (hTX htT) (kerIn_le h1)
  have hNJ : N.comap π ≤ kerIn X ⊤ :=
    le_kerIn_of_le_normalizer hNX (normalizer_eq_top_iff.mpr (hN.comap π)).ge
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨x, rfl⟩ := hπs n
  exact (mem_bot).mpr ((QuotientGroup.eq_one_iff x).mpr (hNJ hn))

theorem centralizer_map_eq_bot {T X Y : Subgroup Q} [Y.Normal] (hT : IsSylowIn 2 T ⊤)
    (hTX : T ≤ X) (hYT : Y ⊔ T = ⊤)
    (hZ : center ↥(Y.map (QuotientGroup.mk' (kerIn X ⊤))) = ⊥) :
    centralizer ((Y.map (QuotientGroup.mk' (kerIn X ⊤)) : Subgroup (Q ⧸ kerIn X ⊤)) :
      Set (Q ⧸ kerIn X ⊤)) = ⊥ := by
  set π := QuotientGroup.mk' (kerIn X ⊤) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hYn : (Y.map π).Normal := Subgroup.Normal.map ‹_› π hπs
  refine eq_bot_of_isPGroup_quotient_kerIn hT hTX _ fun c => ?_
  obtain ⟨x, hx⟩ := hπs c
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top hT.isPGroup hYT x
  have hcY : (c : Q ⧸ kerIn X ⊤) ^ 2 ^ k ∈ Y.map π := by
    rw [← hx, ← map_pow]
    exact mem_map_of_mem π hk
  have hcC : (c : Q ⧸ kerIn X ⊤) ^ 2 ^ k ∈
      centralizer ((Y.map π : Subgroup (Q ⧸ kerIn X ⊤)) : Set (Q ⧸ kerIn X ⊤)) :=
    pow_mem c.2 _
  have hz : (⟨_, hcY⟩ : ↥(Y.map π)) ∈ center ↥(Y.map π) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (mem_centralizer_iff.mp hcC s s.2)
  rw [hZ, mem_bot] at hz
  have hz' : (c : Q ⧸ kerIn X ⊤) ^ 2 ^ k = 1 := congrArg Subtype.val hz
  exact ⟨k, Subtype.ext ((Subgroup.coe_pow _ c (2 ^ k)).trans hz')⟩

omit [Finite Q] in
theorem kerIn_le_pCore_sup {T X Y : Subgroup Q} [Y.Normal] (hT : IsPGroup 2 T)
    (hYT : Y ⊔ T = ⊤)
    (hJodd : Odd (Nat.card ((kerIn X ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))))) :
    kerIn X ⊤ ≤ CFSG.Open.pCore 2 Q ⊔ (Y ⊓ kerIn X ⊤) := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top hT hYT x
  have hm : x ^ Nat.card ((kerIn X ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))) ∈
      CFSG.Open.pCore 2 Q := by
    have h1 := pow_card_eq_one'
      (x := (⟨QuotientGroup.mk' (CFSG.Open.pCore 2 Q) x, mem_map_of_mem _ hx⟩ :
        ↥((kerIn X ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q)))))
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_pow]
    exact congrArg Subtype.val h1
  refine E1.mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hJodd))
    (mem_sup_right (mem_inf.mpr ⟨hk, pow_mem hx _⟩)) (mem_sup_left hm)

theorem commutator_mem_pCore_of_center {Y J : Subgroup Q} [Y.Normal]
    (hcen : ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) ≤
      center (↥Y ⧸ CFSG.Open.pCore 2 ↥Y)) :
    ∀ c ∈ Y ⊓ J, ∀ y ∈ Y, ⁅c, y⁆ ∈ CFSG.Open.pCore 2 Q := by
  intro c hc y hy
  have hcY := (mem_inf.mp hc).1
  have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y) ⟨c, hcY⟩ ∈
      center (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) :=
    hcen (mem_map_of_mem _ (show (⟨c, hcY⟩ : ↥Y) ∈ (Y ⊓ J).subgroupOf Y from hc))
  have h2 : ⁅(⟨c, hcY⟩ : ↥Y), ⟨y, hy⟩⁆ ∈ CFSG.Open.pCore 2 ↥Y := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y) ⁅(⟨c, hcY⟩ : ↥Y), ⟨y, hy⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (mem_center_iff.mp h1 _).symm
  have h3 := mem_map_of_mem Y.subtype h2
  rw [pCore_map_eq_inf_of_normal, map_commutatorElement] at h3
  exact (mem_inf.mp h3).2

theorem inEFor_one_of_alt6_section {Q : Type} [Group Q]
    [Finite Q] {T X Y : Subgroup Q} [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hTX : T ≤ X)
    (hY : ⁅Y, Y⁆ = Y) (hYT : Y ⊔ T = ⊤)
    (hJodd : Odd (Nat.card ((kerIn X ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q)))))
    (hcen : ((Y ⊓ kerIn X ⊤).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) ≤
      center (↥Y ⧸ CFSG.Open.pCore 2 ↥Y))
    (he : Nonempty (↥(Y.map (QuotientGroup.mk' (kerIn X ⊤))) ≃* alternatingGroup (Fin 6))) :
    E1.InEFor 1 ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  refine inEFor_one_of_alt6_quotient hT (kerIn_le_pCore_sup hT.isPGroup hYT hJodd)
    (commutator_mem_pCore_of_center hcen) hY ⟨e⟩
    (centralizer_map_eq_bot hT hTX hYT (center_eq_bot_of_mulEquiv_alt6 e)) ?_
  rw [E1.pCoreOf_top_eq]
  exact eq_bot_of_isPGroup_quotient_kerIn hT hTX _
    (CFSG.LieType.BorelTits.pCore_isPGroup 2)

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem nq_original_HY_alt6_central_quotient_excluded_of_normalizer
    {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H₀ H : Subgroup G} (hH₀ : quasithinIsMaxTwoLocal H₀) (hTH₀ : T ≤ H₀)
    (hTH : T ≤ H) (hHH₀ : H ≤ H₀) (hHM : ¬ H ≤ M)
    (hmin : ∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K) :
    IsEmpty (↥((CFSG.perfectResidual ↥H).map
      (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) ≃* alternatingGroup (Fin 6)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun e => ?_⟩
  have hbasic := minimal_escaping_basic h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨hT'syl, hTn, hT'X', hX'lt, hmax', hns⟩ :=
    minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨⟨hRJ, -⟩, ⟨hJnil, hJodd, -⟩, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT'syl hTn hT'X' hX'lt hmax'
  obtain ⟨-, hYT, -, hYp, hYc⟩ :=
    perfectResidual_minimal_structure hT'syl hTn hT'X' hX'lt hmax' hns
  have := hYc
  have hYn : (CFSG.perfectResidual ↥H).Normal := inferInstance
  have hcen := (center_eq_of_odd_kernel CFSG.SectionRank.oddKernelCentralization
    hbasic.2.2.1.1 hYn hYp hRJ hJnil hJodd pCore_map_eq_inf_of_normal
    (layer_eq_top_center_eq_bot_of_alt6 e)).1
  have hT' : IsSylowIn 2 (T.subgroupOf H) ⊤ := hT'syl
  have hE1 : E1.InEFor 1 (⊤ : Subgroup ↥H) (T.subgroupOf H) :=
    inEFor_one_of_alt6_section hT' hT'X' (Subgroup.isPerfect_iff.mp hYp) hYT hJodd hcen.le ⟨e⟩
  have hE1' : E1.InEFor 1 H T := by
    have h1 := (E1.inEFor_map_subtype_iff 1 H (T.subgroupOf H)).mpr hE1
    rwa [Subgroup.map_subgroupOf_eq_of_le hTH] at h1
  exact hHM (le_of_inEFor_one h hTI hW hTH hE1')

end CFSG.Quasithin.H13.NQCore
