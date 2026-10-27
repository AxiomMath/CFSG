module

public import CFSG.Quasithin.Vol2.Ch11SecOE9A
public import CFSG.Quasithin.Vol2.Ch11SecOE9C
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace Sp4

variable {G : Type} [Group G]

theorem transfer_dichotomy {S : Type} [Group S] {X : Subgroup S} {θ : S →* G}
    (hθ : Function.Injective θ) {L : Subgroup G} (hL : θ.range = L)
    (hX : ∀ R : Subgroup S, X ≤ R →
      (∃ N : Subgroup S, N ≤ R ∧ (N.subgroupOf R).Normal ∧ IsPGroup 2 N ∧ X ≤ N) ∨
      (¬ Group.IsSolvable ↥R ∧ ∀ N : Subgroup S, N ≤ R → (N.subgroupOf R).Normal →
        Group.IsSolvable ↥N → X ⊓ N = ⊥))
    (R : Subgroup G) (hRL : R ≤ L) (hAR : X.map θ ≤ R) :
    (∃ N : Subgroup G, N ≤ R ∧ (N.subgroupOf R).Normal ∧ IsPGroup 2 N ∧ X.map θ ≤ N) ∨
      (¬ Group.IsSolvable ↥R ∧ ∀ N : Subgroup G, N ≤ R → (N.subgroupOf R).Normal →
        Group.IsSolvable ↥N → X.map θ ⊓ N = ⊥) := by
  have hRmap : (R.comap θ).map θ = R :=
    Subgroup.map_comap_eq_self (hL ▸ hRL)
  have hinj : ∀ H : Subgroup G, Function.Injective (θ.subgroupComap H) := fun H a b h =>
    Subtype.ext (hθ (congrArg Subtype.val h))
  rcases hX (R.comap θ) (Subgroup.map_le_iff_le_comap.mp hAR) with
    ⟨N, hNR, hNn, hN2, hXN⟩ | ⟨hns, hsol⟩
  · refine Or.inl ⟨N.map θ, ?_, ?_, hN2.map θ, Subgroup.map_mono hXN⟩
    · exact hRmap ▸ Subgroup.map_mono hNR
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hRmap ▸ Subgroup.map_mono hNR)]
      rw [← hRmap]
      exact (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mp hNn)).trans
        (Subgroup.le_normalizer_map θ)
  · refine Or.inr ⟨fun hs => hns (Group.isSolvable_of_isSolvable_injective (hinj R)),
      fun N hNR hNn hNs => ?_⟩
    have hN'R : N.comap θ ≤ R.comap θ := Subgroup.comap_mono hNR
    have hN'n : ((N.comap θ).subgroupOf (R.comap θ)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN'R]
      intro x hx
      have hxN := (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mp hNn hx
      rw [Subgroup.mem_normalizer_iff] at hxN ⊢
      intro y
      have := hxN (θ y)
      simpa only [Subgroup.mem_comap, map_mul, map_inv] using this
    have hN's : Group.IsSolvable ↥(N.comap θ) :=
      Group.isSolvable_of_isSolvable_injective (hinj N)
    have h0 := hsol _ hN'R hN'n hN's
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨x, hx, rfl⟩, hxN⟩
    have : x ∈ X ⊓ N.comap θ := ⟨hx, hxN⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _

omit [Group G] in
theorem two_le_of_isPSp4 {X : Type} [Group X] {n : ℕ} (h : IsPSp4 2 n X) : 2 ≤ n := by
  obtain ⟨⟨-, hn1, -, hne⟩, -⟩ := h
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact hne (by simp)

theorem conjSub_eq_of_normal {L : Subgroup G} [L.Normal] (g : G) : A1b.conjSub g L = L := by
  rw [A1b.conjSub_eq_iff_mem_normalizer, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact Subgroup.mem_top g

end Sp4

variable {G : Type} [Group G] [Finite G]

open Sp4 in
theorem le_nParam_of_isPSp4 {T : Subgroup G} {n : ℕ}
    (hS : IsPSp4 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := two_le_of_isPSp4 hS
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set L := CFSG.generalizedFitting G with hLdef
  set ψ : ↥(StatedSp 2 K) ≃* ↥L :=
    (MulEquiv.ofBijective (proj 2 K) ⟨CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩).trans e.symm
    with hψdef
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    have hf₀ : CFSG.RankThree.SubgroupLists.spForm 2 K e₀ (Pi.single (Sum.inr 0) 1) = 1 := by
      rw [CFSG.RankThree.SubgroupLists.spForm_apply]
      simp [e₀, Pi.single_apply]
    refine ⟨ψ (CFSG.RankThree.PartOne.SEITZ4.planeHom hf₀
        (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K 1)),
      ψ (CFSG.RankThree.PartOne.SEITZ4.planeHom hf₀
        (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K 1)), fun h => ?_⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
    exact sl2Upper_mul_sl2Lower_ne (planeHom_injective h4 hf₀ (ψ.injective h))
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.1 hFT
  have hTsyl : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  have hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN h2 =>
    le_bot_iff.mp ((CFSG.LieType.BorelTits.le_pCore 2 hN h2).trans
      (E3.pCore_two_le_solvableRadical.trans hAS.solvableRadical_eq_bot.le))
  set θ : ↥(StatedSp 2 K) →* G := L.subtype.comp ψ.toMonoidHom with hθdef
  have hθi : Function.Injective θ := L.subtype_injective.comp ψ.injective
  have hθr : θ.range = L := by
    rw [hθdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hXel := isElemAbelian_rootX (K := K)
  have hX2 : IsPGroup 2 (rootX (K := K)) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hXel.2 x x.2)⟩
  obtain ⟨g, hg⟩ := E1.exists_conjSub_le_of_isSylowIn hTsyl (hX2.map θ)
  set θ' : ↥(StatedSp 2 K) →* G := (MulAut.conj g).toMonoidHom.comp θ with hθ'def
  have hθ'i : Function.Injective θ' := (MulAut.conj g).injective.comp hθi
  have := hAS.normal
  have hθ'r : θ'.range = L := by
    rw [hθ'def, MonoidHom.range_comp, hθr]
    exact conjSub_eq_of_normal g
  have hAeq : A1b.conjSub g ((rootX (K := K)).map θ) = (rootX (K := K)).map θ' := by
    rw [A1b.conjSub, Subgroup.map_map]
  rw [hAeq] at hg
  have hcard : Nat.card ((rootX (K := K)).map θ') = 2 ^ n := by
    rw [Subgroup.card_map_of_injective hθ'i, card_rootX, hK]
  refine le_nParam_of_overgroups (L := L) hn hTsyl hO2 hg ?_ (E1.isElemAbelian_map' θ' hXel)
    ?_ hcard.ge (transfer_dichotomy hθ'i hθ'r fun R hR => rootX_dichotomy h4 hR)
  · rw [← hθ'r]
    exact Subgroup.map_le_range _ _
  · intro h0
    rw [h0, Subgroup.card_bot] at hcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
