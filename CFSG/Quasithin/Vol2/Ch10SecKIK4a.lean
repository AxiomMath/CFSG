module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankSmall

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem pCore_le_subgroupOf_oTwoZIn (J : Subgroup G) :
    CFSG.pCore 2 ↥J ≤ (oTwoZIn J).subgroupOf J := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine ⟨x, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥J) x ∈ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
  exact Subgroup.one_mem _

theorem exists_quot_surj {J : Subgroup G} (hA : IsAltQuotient J (oTwoZIn J) 7) :
    ∃ ψ : ↥J ⧸ CFSG.pCore 2 ↥J →* ↥(alternatingGroup (Fin 7)), Function.Surjective ψ := by
  obtain ⟨φ, hφs, hφk⟩ := hA
  have hle : CFSG.pCore 2 ↥J ≤ φ.ker := hφk ▸ pCore_le_subgroupOf_oTwoZIn J
  refine ⟨QuotientGroup.lift _ φ hle, fun a => ?_⟩
  obtain ⟨j, rfl⟩ := hφs a
  exact ⟨QuotientGroup.mk j, rfl⟩

theorem exists_surj {J : Subgroup G} (hA : IsAltQuotient J (oTwoZIn J) 7) {S : Type*} [Group S]
    (α : ↥J →* S) (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥J) :
    ∃ ψ : S →* ↥(alternatingGroup (Fin 7)), Function.Surjective ψ := by
  obtain ⟨ψ, hψ⟩ := exists_quot_surj hA
  let e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  exact ⟨ψ.comp e.symm.toMonoidHom, hψ.comp e.symm.surjective⟩

theorem card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [SecA.card_alt 7 (by norm_num)]
  decide

theorem card_eq_of_simple {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (ψ : S →* ↥(alternatingGroup (Fin 7))) (hψ : Function.Surjective ψ) : Nat.card S = 2520 := by
  have : Nontrivial ↥(alternatingGroup (Fin 7)) :=
    (alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)).toNontrivial
  refine (Nat.card_congr (MulEquiv.ofBijective ψ ⟨?_, hψ⟩).toEquiv).trans card_alt7
  rcases hS.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff ψ).1 h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin 7)))
    obtain ⟨g, rfl⟩ := hψ x
    exact hx (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))

theorem sl2_card_ne (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 2520 := by
  intro h
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp_all
  · have h16 : 16 ∣ 2 ^ n * (4 ^ n - 1) :=
      Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 hn) _
    rw [h] at h16
    norm_num at h16

theorem eq_seven_of_factorial {m : ℕ} (h : m.factorial / 2 = 2520) : m = 7 := by
  rcases Nat.lt_or_ge m 8 with hm | hm
  · interval_cases m <;> simp_all [Nat.factorial]
  · have h8 : Nat.factorial 8 ≤ m.factorial := Nat.factorial_le hm
    have : 40320 ≤ m.factorial := by simpa [Nat.factorial] using h8
    omega

variable [Finite G]

omit [Finite G] in
theorem shape_of_block {H J : Subgroup G} (hA : IsAltQuotient J (oTwoZIn J) 7)
    (hblk : IsChiBlock H J ∨ (IsBlock2 H J ∧ (CFSG.Quasithin.IsExcA7Block J ∨
      IsAltBlockType J 6 ∨ CFSG.Quasithin.IsHatA6Block J))) :
    IsShort2 J ∧ (IsAltType J 7 ∨ CFSG.Quasithin.IsExcA7Block J) := by
  rcases hblk with ⟨hB, ⟨n, hn, F, _, _, hF, α, hαs, hαk, -⟩ | ⟨m, hm, h3, hAlt⟩⟩ |
      ⟨hB, hexc | ⟨-, α, hαs, hαk, -⟩ | ⟨-, hhat, -, -⟩⟩
  · exfalso
    obtain ⟨ψ, hψ⟩ := exists_surj hA α hαs hαk
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have hs := Ch11.SecA.isSimpleGroup_SL2 (K := F) (n := n) (by omega) hF'
    have h1 := card_eq_of_simple hs ψ hψ
    rw [SecA.card_SL_two_pow hF'] at h1
    exact sl2_card_ne n h1
  · refine ⟨hB.1, Or.inl ?_⟩
    have ⟨α, hαs, hαk, _⟩ := hAlt
    obtain ⟨ψ, hψ⟩ := exists_surj hA α hαs hαk
    rcases Nat.lt_or_ge m 5 with hm5 | hm5
    · exfalso
      have hm3 : m = 3 := by
        obtain ⟨k, hk⟩ := hm
        omega
      subst hm3
      have hd := Subgroup.card_dvd_of_surjective hψ
      rw [card_alt7, SecA.card_alt 3 (by norm_num)] at hd
      norm_num [Nat.factorial] at hd
    · have h1 := card_eq_of_simple (SecA.isSimpleGroup_alt hm5) ψ hψ
      rw [SecA.card_alt m (by omega)] at h1
      have hm7 := eq_seven_of_factorial h1
      subst hm7
      exact hAlt
  · exact ⟨hexc.1, Or.inr hexc⟩
  · exfalso
    obtain ⟨ψ, hψ⟩ := exists_surj hA α hαs hαk
    have hd := Subgroup.card_dvd_of_surjective hψ
    rw [card_alt7, SecA.card_alt 6 (by norm_num)] at hd
    norm_num [Nat.factorial] at hd
  · exfalso
    obtain ⟨ψ, hψ⟩ := exists_quot_surj hA
    obtain ⟨-, hc, ⟨e⟩⟩ := hhat
    have hd := Subgroup.card_dvd_of_surjective hψ
    rw [card_alt7, Lin2.OddRank.card_of_cover_alt (m := 6) (by norm_num) hc e] at hd
    norm_num [Nat.factorial] at hd

omit [Finite G] in
theorem exists_alpha {J : Subgroup G} (h : IsAltType J 7 ∨ CFSG.Quasithin.IsExcA7Block J) :
    ∃ α : ↥J →* ↥(alternatingGroup (Fin 7)), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥J := by
  rcases h with ⟨α, hαs, hαk, -⟩ | ⟨-, hα, -⟩
  · exact ⟨α, hαs, hαk⟩
  · exact hα

theorem pCoreOf_le_centralizer {H J V : Subgroup G} (hred : IsTwoReducedIn H V) (hJH : J ≤ H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) :
    pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 J ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJH
  have hN : H ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    hHJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  refine hred.2.2.2 _ hle hN fun d hd => ?_
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

theorem inf_centralizer_eq_pCoreOf {H J V : Subgroup G} (hred : IsTwoReducedIn H V)
    (hJH : J ≤ H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hJV : ¬ J ≤ Subgroup.centralizer (V : Set G))
    (α : ↥J →* ↥(alternatingGroup (Fin 7))) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥J) :
    J ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 J := by
  have hO := pCoreOf_le_centralizer hred hJH hHJ
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 J) hO)
  set K := (J ⊓ Subgroup.centralizer (V : Set G)).subgroupOf J with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk j => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨J.mul_mem (J.mul_mem j.2 hk.1) (J.inv_mem j.2), ?_⟩
    have hmem : (j : G) * (k : G) * (j : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hj' : (j : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ (hJN j.2)
      have hv' : (j : G)⁻¹ * v * (j : G)⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hj' v).mp hv
      rw [inv_inv] at hv'
      have hc := Subgroup.mem_centralizer_iff.mp hk.2 _ hv'
      calc v * ((j : G) * (k : G) * (j : G)⁻¹)
          = (j : G) * ((j : G)⁻¹ * v * j * k) * (j : G)⁻¹ := by group
        _ = (j : G) * (k * ((j : G)⁻¹ * v * j)) * (j : G)⁻¹ := by rw [hc]
        _ = (j : G) * (k : G) * (j : G)⁻¹ * v := by group
    simpa using hmem
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  have := hKn.map α hαs
  rcases hs.eq_bot_or_eq_top_of_normal (K.map α) with h | h
  · intro x hx
    have hxK : (⟨x, hx.1⟩ : ↥J) ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf]
      exact hx
    have h1 : α ⟨x, hx.1⟩ ∈ K.map α := ⟨_, hxK, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hx.1⟩ : ↥J) ∈ CFSG.pCore 2 ↥J := hαk ▸ MonoidHom.mem_ker.2 h1
    exact (C1Pack.coe_mem_pCoreOf_iff J _).2 h2
  · exfalso
    apply hJV
    intro j hj
    have h1 : α ⟨j, hj⟩ ∈ K.map α := h ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkj⟩ := h1
    have h2 : k⁻¹ * ⟨j, hj⟩ ∈ CFSG.pCore 2 ↥J := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hkj, inv_mul_cancel]
    have h3 := hO ((C1Pack.coe_mem_pCoreOf_iff J _).2 h2)
    have hk' : (k : G) ∈ J ⊓ Subgroup.centralizer (V : Set G) := Subgroup.mem_subgroupOf.1 hk
    have e1 : j = (k : G) * ((k⁻¹ * ⟨j, hj⟩ : ↥J) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e1]
    exact Subgroup.mul_mem _ hk'.2 h3

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
