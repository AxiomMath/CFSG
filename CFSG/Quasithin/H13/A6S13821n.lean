module

public import CFSG.Quasithin.H13.A6S13821m
public import CFSG.Quasithin.H13.A6S13816m
public import CFSG.Quasithin.H13.A6S13821f
public import CFSG.Quasithin.H13.A6S13821l

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem relIndex_pCoreOf_L1 (hhat : ¬ IsHatA6 L) :
    (pCoreOf 2 S.L1).relIndex S.L1 = 3 := by
  have P := S14.plusData_L1 S hhat
  obtain ⟨c, hcL, hρ, hc3⟩ := P.exists_c012_cube
  exact A6L32.relIndex_eq_three_of_decomp hcL hc3 (S14.PlusData.not_mem hρ hc3)
    (fun x hx => P.decomp hcL hρ hx)

theorem le_normalizer_L1_of_comm {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hHeq : H = K ⊔ (S.L1 ⊔ T))
    (hcomm : ∀ x ∈ S.L1, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    H ≤ Subgroup.normalizer (S.L1 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := by rw [hHeq]; exact le_sup_left
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hQL : pCoreOf 2 H ≤ Subgroup.normalizer (S.L1 : Set G) :=
    hQT.trans S.T_le_normalizer_L1
  have hQn : ∀ g ∈ H, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ ∈ S.L1 ⊔ pCoreOf 2 H :=
    fun g hg q hq => Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) q).mp hq)
  have hl1N : S.L1 ⊔ T ≤ Subgroup.normalizer (S.L1 : Set G) :=
    sup_le Subgroup.le_normalizer S.T_le_normalizer_L1
  have hLQ : H ≤ Subgroup.normalizer ((S.L1 ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    calc H = K ⊔ (S.L1 ⊔ T) := hHeq
      _ ≤ _ := by
        refine sup_le (fun k hk => ?_) (fun g hg => ?_)
        · refine L32A.C.mem_normalizer_sup_of hQL (fun l hl => ?_) (hQn k (hKH hk))
          have h1 := hcomm l⁻¹ (S.L1.inv_mem hl) k hk
          have e : k * l * k⁻¹ = l * (l⁻¹ * k * l⁻¹⁻¹ * k⁻¹) := by group
          rw [e]
          exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right h1)
        · refine L32A.C.mem_normalizer_sup_of hQL (fun l hl => Subgroup.mem_sup_left
            ((Subgroup.mem_normalizer_iff.mp (hl1N hg) l).mp hl)) (hQn g ?_)
          exact hH.1.1 hg
  have hL1 : S.L1 = oTwoUpper S.L1 := by
    rw [Setting4.L1, L₁Of, oTwoRes_eq_oTwoUpper, oTwoUpper_oTwoUpper]
  have hO : oTwoUpper (S.L1 ⊔ pCoreOf 2 H) = S.L1 :=
    le_antisymm (L32A.oTwoUpper_sup_le_two' (pCoreOf_isPGroup 2 H) hQL)
      (calc S.L1 = oTwoUpper S.L1 := hL1
        _ ≤ _ := oTwoUpper_mono le_sup_left)
  rw [← hO]
  exact hLQ.trans (normalizer_le_normalizer_oTwoUpper _)

theorem false_of_inner (h13 : Lem13813) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHeq : H = K ⊔ (S.L1 ⊔ T))
    (hP : IsPSL 3 2 1 (L32A.cStar K)) (hL3 : (pCoreOf 2 S.L1).relIndex S.L1 = 3)
    (hcomm : ∀ x ∈ S.L1, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    (hout : ∀ t ∈ T, ∃ k ∈ K, ∀ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∈ pCoreOf 2 K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hl1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hTl1 : T ≤ Subgroup.normalizer (S.L1 : Set G) := S.T_le_normalizer_L1
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  set π₀ : ↥K →* SL3.S := φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := Subgroup.inf_subgroupOf_right T K ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := L32A.C.exists_conj_map_eq_of_sylow π₀ hπ₀ hS2 hSi SL3.P0_sylow.1
    SL3.P0_sylow.2
  set π : ↥K →* SL3.S := (MulAut.conj h⁻¹).toMonoidHom.comp π₀ with hπdef
  have hπ : Function.Surjective π := (MulAut.conj h⁻¹).surjective.comp hπ₀
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hD : (T.subgroupOf K).map π = SL3.P0 := by
    rw [← hhD, Subgroup.map_map]
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := L32A.C.indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    L32A.C.indHom_apply π hπ hker hKn hHN
  have hL1β : ∀ x (hx : x ∈ S.L1), β ⟨x, hl1H hx⟩ = 1 := by
    intro x hx
    apply MulEquiv.ext
    intro a
    obtain ⟨k, rfl⟩ := hπ a
    rw [hβ, MulAut.one_apply]
    have h1 : ((conjK (hKn (hl1H hx)) k * k⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply]
      exact hcomm x hx k k.2
    have h2 := (hker _).mpr h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2
  set Inn := CFSG.ComponentClassification.OuterAutomorphisms.inner SL3.S with hInndef
  have hTin : ∀ t (ht : t ∈ T), β ⟨t, hTH ht⟩ ∈ Inn := by
    intro t ht
    obtain ⟨k, hk, hkx⟩ := hout t ht
    refine ⟨π ⟨k, hk⟩, ?_⟩
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    have h1 := hkx (k * x * k⁻¹) (K.mul_mem (K.mul_mem hk x.2) (K.inv_mem hk))
    have e : t * k⁻¹ * (k * x * k⁻¹) * (t * k⁻¹)⁻¹ * (k * x * k⁻¹)⁻¹ =
        (t * x * t⁻¹) * (k * x * k⁻¹)⁻¹ := by group
    rw [e] at h1
    have h2 : π (conjK (hKn (hTH ht)) x * (⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹) = 1 := by
      refine (hker _).mpr ?_
      have e3 : ((conjK (hKn (hTH ht)) x * (⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ : ↥K) : G) =
          (t * x * t⁻¹) * (k * x * k⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply]
      rw [e3]
      exact h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2.symm
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = MulAut.conj (π ⟨k, hk⟩) := by
    intro k hk
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ Inn := by
    have hle : K ⊔ (S.L1 ⊔ T) ≤ ((Inn).comap β).map H.subtype := by
      refine sup_le (fun k hk => ⟨⟨k, hKH hk⟩, ⟨π ⟨k, hk⟩, (hKin k hk).symm⟩, rfl⟩)
        (sup_le (fun x hx => ⟨⟨x, hl1H hx⟩, ?_, rfl⟩) (fun t ht => ⟨⟨t, hTH ht⟩, hTin t ht, rfl⟩))
      show β ⟨x, hl1H hx⟩ ∈ Inn
      rw [hL1β x hx]
      exact (Inn).one_mem
    rw [← hHeq] at hle
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have e : y = y' := Subtype.ext hyy'.symm
    rw [e]
    exact hy'
  let e := MonoidHom.ofInjective L32A.C.sl3_conj_injective
  set ψ : ↥H →* SL3.S := e.symm.toMonoidHom.comp (β.codRestrict _ hInn) with hψdef
  have hψ : ∀ y : ↥H, MulAut.conj (ψ y) = β y := by
    intro y
    have := congrArg Subtype.val (e.apply_symm_apply (β.codRestrict _ hInn y))
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = π ⟨k, hk⟩ := fun k hk =>
    L32A.C.sl3_conj_injective (by rw [hψ, hKin])
  have hψs : Function.Surjective ψ := fun g => by
    obtain ⟨k, rfl⟩ := hπ g
    exact ⟨⟨k, hKH k.2⟩, hψK k k.2⟩
  have hψl1 : ∀ x (hx : x ∈ S.L1), ψ ⟨x, hl1H hx⟩ = 1 := fun x hx =>
    L32A.C.sl3_conj_injective (by rw [hψ, hL1β x hx, map_one])
  have hψT : ∀ t (ht : t ∈ T), ψ ⟨t, hTH ht⟩ ∈ SL3.P0 := by
    intro t ht
    refine L32A.C.sl3_normalizer_P0 _ fun p hp => ?_
    have hpP : p ∈ (T.subgroupOf K).map π := hD ▸ SL3.P0list_mem le_rfl p hp
    obtain ⟨s, hsT, rfl⟩ := hpP
    have e1 : ψ ⟨t, hTH ht⟩ * π s * (ψ ⟨t, hTH ht⟩)⁻¹ = π (conjK (hKn (hTH ht)) s) := by
      rw [← MulAut.conj_apply, hψ, hβ]
    rw [e1]
    have hmem : π (conjK (hKn (hTH ht)) s) ∈ SL3.P0 := by
      rw [← hD]
      refine ⟨_, ?_, rfl⟩
      show ((conjK (hKn (hTH ht)) s : ↥K) : G) ∈ T
      rw [conjK_apply]
      exact T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht)
    exact hmem
  obtain ⟨c, hc⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
  have hcK : Nat.card K = 168 * 2 ^ c := by
    have hle : pCoreOf 2 K ≤ K := Subgroup.map_subtype_le _
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 K).subgroupOf K),
      Nat.card_congr φ.toEquiv, SL3.card_S,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hc]
  have hJK : S.L1 ⊔ T ≤ Subgroup.normalizer (K : Set G) := (sup_le hl1H hTH).trans hKn
  have hidx : L32A.C.IsTwoThree (K.relIndex H) := by
    have h1 : K.relIndex H = K.relIndex (S.L1 ⊔ T) := by
      rw [hHeq, sup_comm, L32A.C.relIndex_sup_eq hJK]
    rw [h1]
    have h2 := L32A.C.isTwoThree_card_sup hL3 hTsylH.2.1 hTl1
    rw [sup_comm] at h2
    exact h2.of_dvd (Subgroup.index_dvd_card _)
  have hcH : Nat.card H = K.relIndex H * (168 * 2 ^ c) := by
    have := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [inf_eq_left.mpr hKH, hcK] at this
    exact this.symm
  have hparab : ∀ X : Subgroup SL3.S, Nat.card X = 24 → SL3.P0 ≤ X →
      (X.comap ψ).map H.subtype ≤ Subgroup.normalizer (L : Set G) := by
    intro X hX24 hPX
    have hXidx : X.index = 7 := by
      have := X.card_mul_index
      rw [hX24, SL3.card_S] at this
      omega
    have hcP : Nat.card ((X.comap ψ).map H.subtype) = K.relIndex H * (24 * 2 ^ c) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      have h1 := (X.comap ψ).card_mul_index
      rw [Subgroup.index_comap_of_surjective X hψs, hXidx, hcH] at h1
      have h2 : Nat.card (X.comap ψ) * 7 = K.relIndex H * (24 * 2 ^ c) * 7 := by
        rw [h1]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
    have hsolv : Group.IsSolvable ↥((X.comap ψ).map H.subtype) := by
      refine L32A.C.isSolvable_of_isTwoThree ?_
      rw [hcP]
      exact hidx.mul (⟨3 + c, 1, by ring⟩ : L32A.C.IsTwoThree (24 * 2 ^ c))
    refine h13 G T L V S hS _ (sup_le ?_ ?_) ((Subgroup.map_subtype_le _).trans hH.2.1) hsolv
    · intro x hx
      refine ⟨⟨x, hl1H hx⟩, ?_, rfl⟩
      show ψ ⟨x, hl1H hx⟩ ∈ X
      rw [hψl1 x hx]
      exact X.one_mem
    · intro t ht
      exact ⟨⟨t, hTH ht⟩, hPX (hψT t ht), rfl⟩
  have hM1 := hparab SL3.X1 SL3.card_X1 inf_le_left
  have hM2 := hparab SL3.X2 SL3.card_X2 inf_le_right
  apply hH.2.2
  have htop : (⊤ : Subgroup ↥H) = SL3.X1.comap ψ ⊔ SL3.X2.comap ψ := by
    rw [Subgroup.comap_sup_eq ψ _ _ hψs, L32A.C.sl3_sup_X, Subgroup.comap_top]
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥H) ∈ SL3.X1.comap ψ ⊔ SL3.X2.comap ψ :=
    htop ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem H.subtype hy'
  rw [Subgroup.map_sup] at this
  exact sup_le hM1 hM2 this

theorem L1_le_of_l32_of_not_hat (hA21 : AsA21SQTKSection)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (h13 : Lem13813) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hF : HypF918 T V L (fsuV1 T V) S.V3 H K) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHeq : H = K ⊔ (S.L1 ⊔ T)) (hP : IsPSL 3 2 1 (L32A.cStar K)) (hhat : ¬ IsHatA6 L) :
    S.L1 ≤ K := by
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc : K ∈ cComp H := hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hl1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKn
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hTN ht) k).mp hk) (le_conjClosure K T)
  have hSQ : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hL3 := S.relIndex_pCoreOf_L1 hhat
  have hL1eq : S.L1 = oTwoUpper (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) := by
    rw [Setting4.L1, L₁Of, oTwoRes_eq_oTwoUpper]
  have hcommK : ∀ x ∈ S.L1, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    rw [hL1eq]
    refine A6L32.comm_of_not_le hKc hKn hTsylH hP ?_ ?_ ?_ ?_
    · rw [← hL1eq]
      exact hL3
    · rw [← hL1eq]
      exact hl1H
    · rw [← hL1eq]
      exact S.T_le_normalizer_L1
    · rw [← hL1eq]
      exact hnot
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hcommH : ∀ x ∈ S.L1, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    fun x hx k hk => hO2K (hcommK x hx k hk)
  have hHL := S.le_normalizer_L1_of_comm hH hHeq hcommH
  have P := S14.plusData_L1 S hhat
  obtain ⟨c, hcL, hρ, hc3⟩ := P.exists_c012_cube
  have hcH : (c : G) ∈ H := hl1H hcL
  have hOL : pCoreOf 2 S.L1 ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hl1H)
      (hHL.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hconj : ∀ h ∈ H, h * (c : G) * h⁻¹ * (c : G)⁻¹ ∈ pCoreOf 2 H ∨
      h * (c : G) * h⁻¹ * (c : G) ∈ pCoreOf 2 H := by
    intro h hh
    have hx : h * (c : G) * h⁻¹ ∈ S.L1 := (Subgroup.mem_normalizer_iff.mp (hHL hh) _).mp hcL
    have hccc : (c : G) * c * c = 1 := by rw [← pow_three', hc3]
    rcases P.decomp hcL hρ hx with h1 | h1 | h1
    · exfalso
      apply S14.PlusData.not_mem (Lp := H) hρ hc3
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hh)) _).mp (hOL h1)
      simpa [mul_assoc] using h2
    · left
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHQ hcH) _).mp (hOL h1)
      have e : h * (c : G) * h⁻¹ * (c : G)⁻¹ =
          (c : G) * ((c : G) * c * (h * c * h⁻¹)) * (c : G)⁻¹ := by
        calc h * (c : G) * h⁻¹ * (c : G)⁻¹ = ((c : G) * c * c) * (h * c * h⁻¹) * (c : G)⁻¹ := by
              rw [hccc, one_mul]
          _ = (c : G) * ((c : G) * c * (h * c * h⁻¹)) * (c : G)⁻¹ := by group
      rw [e]
      exact h2
    · right
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hcH)) _).mp (hOL h1)
      have e : h * (c : G) * h⁻¹ * (c : G) =
          (c : G)⁻¹ * ((c : G) * (h * c * h⁻¹)) * (c : G)⁻¹⁻¹ := by group
      rw [e]
      exact h2
  have hN := S.norm_mem_V1 hS hH hcH hc3 hρ (P.le_NV3 hcL) hconj
  by_cases hout : ∃ t ∈ T, ∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K
  · obtain ⟨t, ht, hto⟩ := hout
    exact A6L32.false_of_outer hA21 hD310 hD391 hI4 hSQ hF hK₀ hP hcH hc3 hN
      (fun k hk => hcommH c hcL k hk) ht hto
  · push Not at hout
    exact S.false_of_inner h13 hS hH hKc hKn hHeq hP hL3 hcommK hout

end Setting4

end CFSG.Quasithin.H13.A6
