module

public import CFSG.Quasithin.H13.A6S13821zz20
public import CFSG.Quasithin.H13.A6S13821z

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.RankThree.PartTwo.Sec4

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_of_slPi
    (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    {π : Bool} {f : ℕ} {F : Type} [Field F] (hF : PiField π 2 f F) (hq3 : ModThree π (2 ^ f))
    (hq2 : 2 < 2 ^ f) (e : ↥(S.KSt H K) ≃* slPi π 3 (2 ^ f) F) : S.L1 ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hL1K
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hQN : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := (pCoreOf_le 2 H).trans hKn
  obtain ⟨x, hxL1, m, hm, hxm, hxKQ⟩ :
      ∃ x ∈ S.L1, ∃ m : ℕ, Odd m ∧ x ^ m = 1 ∧ x ∉ K ⊔ pCoreOf 2 H := by
    by_contra hcon
    push Not at hcon
    apply hL1K
    change oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ K
    rw [oTwoRes, Subgroup.closure_le]
    rintro y ⟨hyA, k, hk, hyk⟩
    have hyL1 : y ∈ S.L1 := Subgroup.subset_closure ⟨hyA, k, hk, hyk⟩
    exact A5.mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 H) hQN (hcon y hyL1 k hk hyk) hk hyk
  have hxH : x ∈ H := hL1H hxL1
  have hx3 : x ^ 3 = 1 := by
    have h3 : x ^ 3 ∈ pCoreOf 2 S.L1 := by
      by_cases hhat : IsHatA6 L
      · exact S.cube_mem_pCoreOf_L1_hat hhat hxL1
      · exact S.cube_mem_pCoreOf_L1 hhat hxL1
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, h3⟩
    have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
      (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk')
  have hF91 := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF91.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF91.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF91.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  set φ := actH hV₁ hIH with hφ
  have hker : ∀ y : ↥H, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H := by
    intro y
    rw [hφ, A6Tv.actH_eq_one_iff hV₁ hIHN hIH, hF91.pCoreOf_eq_centralizerMod, mem_centralizerMod]
    exact ⟨fun h1 => ⟨y.2, hV₁ y.2, h1⟩, fun h1 => h1.2.2⟩
  have hKSt : S.KSt H K = (K.subgroupOf H).map φ := autOn_tilde_eq_map_actH hV₁ hIH hKH
  set φ' : ↥H →* ↥φ.range := φ.rangeRestrict with hφ'
  have hφ's : Function.Surjective φ' := MonoidHom.rangeRestrict_surjective φ
  have hφ'1 : ∀ y : ↥H, φ' y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y => by
    rw [← hker y, hφ']
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set S' : Subgroup ↥φ.range := (K.subgroupOf H).map φ' with hS'
  have hKnH : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hS'n : S'.Normal := hKnH.map φ' hφ's
  have hS'map : S'.map φ.range.subtype = S.KSt H K := by
    rw [hS', Subgroup.map_map, hφ', MonoidHom.subtype_comp_rangeRestrict, hKSt]
  let e₁ : ↥S' ≃* ↥(S.KSt H K) :=
    (S'.equivMapOfInjective φ.range.subtype φ.range.subtype_injective).trans
      (MulEquiv.subgroupCongr hS'map)
  let e' : ↥S' ≃* slPi π 3 (2 ^ f) F := e₁.trans e
  obtain ⟨e₀⟩ := S.kst_equiv hS hH hK
  have hQ' : CFSG.IsQuasisimple ↥S' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e₀.trans e₁.symm) hq
  have hX : CFSG.Open.pRank 3 (⊤ : Subgroup ↥φ.range) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact A6Tv.pRank_range_le_two hF91 S.h13.qtke φ hker
  set xs : ↥φ.range := φ' ⟨x, hxH⟩ with hxs
  have hxs1 : xs ≠ 1 := by
    intro h
    exact hxKQ (Subgroup.mem_sup_right ((hφ'1 _).mp h))
  have hxs3 : xs ^ 3 = 1 := by
    have h1 : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [hxs, ← map_pow, h1, map_one]
  have hxsS : xs ∉ S' := by
    rintro ⟨k, hk, hkx⟩
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have h1 : φ' (k⁻¹ * ⟨x, hxH⟩) = 1 := by rw [map_mul, map_inv, hkx, hxs, inv_mul_cancel]
    have h2 := (hφ'1 _).mp h1
    apply hxKQ
    have e2 : x = (k : G) * ((k⁻¹ * ⟨x, hxH⟩ : ↥H) : G) := by simp
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right h2)
  have hTK := S.isSylowTwoOf_TK hH hKH hKn
  set P : Subgroup ↥φ.range := ((T ⊓ K).subgroupOf H).map φ' with hP
  have hPS : P ≤ S' := Subgroup.map_mono fun y hy => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hy.2
  have hP2 : IsPGroup 2 ↥P := by
    have h1 : IsPGroup 2 ↥((T ⊓ K).subgroupOf H) :=
      hTK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hKH)).symm
    exact h1.map φ'
  have hNTK := S.L1T_le_normalizer_TK h1334 hS hH hKH hKn hn hLie
  have hxP : ∀ g ∈ P, xs * g * xs⁻¹ ∈ P := by
    rintro _ ⟨y, hy, rfl⟩
    have hyTK : (y : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hy
    have hconj : x * (y : G) * x⁻¹ ∈ T ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp (hNTK (Subgroup.mem_sup_left hxL1)) y).mp hyTK
    refine ⟨⟨x, hxH⟩ * y * (⟨x, hxH⟩ : ↥H)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hconj
    · rw [map_mul, map_mul, map_inv]
  have hP1 : P ≠ ⊥ := by
    intro hbot
    let σ : ↥K →* ↥S' :=
      { toFun := fun k => ⟨φ' (Subgroup.inclusion hKH k),
          ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) }
    have hσs : Function.Surjective σ := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
    have hle : (T ⊓ K).subgroupOf K ≤ σ.ker := by
      intro y hy
      have hyP : φ' (Subgroup.inclusion hKH y) ∈ P :=
        ⟨Subgroup.inclusion hKH y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy),
          rfl⟩
      rw [hbot, Subgroup.mem_bot] at hyP
      exact Subtype.ext hyP
    have hcard : Nat.card ↥S' ∣ ((T ⊓ K).subgroupOf K).index := by
      have h1 := Subgroup.index_dvd_of_le hle
      rwa [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hσs, Subgroup.card_top] at h1
    have hFin : Finite F := hF.finite
    have hKc : Nat.card F = 2 ^ (cond π f (2 * f)) := by
      rw [hF.card]
      cases π
      · simp [piCard, ← pow_mul, mul_comm]
      · simp [piCard]
    have hfpos : 1 ≤ cond π f (2 * f) := by
      have := hF.one_le
      cases π <;> simp <;> omega
    have : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hfpos hKc
    have h2 : 2 ∣ Nat.card ↥S' := by
      rw [Nat.card_congr e'.toEquiv]
      exact A6S20.two_dvd_card_slPi (fun h => by subst h; exact hF.unitary)
    exact hTK.2.2 (h2.trans hcard)
  exact A6S20.false_of_normalizes_slPi hQ' hX hF hq3 hq2 e' (orderOf_eq_prime hxs3 hxs1) hxsS hPS
    hP2 hP1 hxP

end Setting4

end CFSG.Quasithin.H13.A6
