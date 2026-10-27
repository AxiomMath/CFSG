module

public import CFSG.Quasithin.H13.A6S13821M22d
public import CFSG.Quasithin.H13.A6S13821M22e
public import CFSG.Quasithin.H13.A6S13821M22f
public import CFSG.Quasithin.H13.A6S13821M22c
public import CFSG.Quasithin.H13.A6S13821e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.ComponentClassification.WittDesign MulAction
open CFSG.Quasithin.H13.A6.Hat6 (Kq)
open CFSG.Quasithin.H13.A6.HatM22
open scoped Pointwise

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_hatM22
    (hF318 : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hHat6 : Case13821Hat6) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1K := S.L1_le_of_hatM22 hF318 h36 h38 hH hK hKn hHat
  obtain ⟨φ⟩ := hHat.2.2
  obtain ⟨h₀, hh₀, -, -, hTinv, hL1B⟩ := S.exists_hexad_hatM22 hS hH hKn hK hL1K φ
  have hQ : commutator (Kq K) = ⊤ := Group.isPerfect_def.mp hHat.1.1
  set O := CFSG.pCore 2 ↥K with hO
  set Bst := stabilizer M22 h₀ with hBst
  set Q₁ := Bst.comap (rhoM φ) with hQ₁
  set W := perfectCore Q₁ with hW
  set P' : Subgroup ↥K := Q₁.comap (QuotientGroup.mk' O) with hP'
  set K₁' := perfectCore P' with hK₁'
  set K₁ := K₁'.map K.subtype with hK₁
  have hmk : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have hK₁perf : ⁅K₁, K₁⁆ = K₁ := by
    rw [hK₁, ← Subgroup.map_commutator, perfectCore_perfect]
  have hK₁K : K₁ ≤ K := Subgroup.map_subtype_le K₁'
  have hW1 : K₁'.map (QuotientGroup.mk' O) = W := by
    rw [hK₁', map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hmk]
  have hHatW := isHat_perfectCore hHat φ hh₀
  have hmemW : ∀ k : ↥K₁', QuotientGroup.mk' O (k : ↥K) ∈ W := fun k => by
    rw [← hW1]
    exact Subgroup.mem_map_of_mem _ k.2
  let g₀ : ↥K₁' →* ↥W := ((QuotientGroup.mk' O).comp K₁'.subtype).codRestrict W hmemW
  have hg₀ : Function.Surjective g₀ := by
    rintro ⟨w, hw⟩
    rw [← hW1] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    exact ⟨⟨k, hk⟩, rfl⟩
  have hk₀ : IsPGroup 2 g₀.ker := by
    intro x
    have hxO : ((x : ↥K₁') : ↥K) ∈ O := by
      have h1 : g₀ x = 1 := x.2
      have h2 : QuotientGroup.mk' O ((x : ↥K₁') : ↥K) = 1 := congrArg Subtype.val h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 O) ⟨_, hxO⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  let e₁ : ↥K₁' ≃* ↥K₁ := K₁'.equivMapOfInjective K.subtype K.subtype_injective
  have hk₁ : IsPGroup 2 e₁.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e₁.injective]
    exact IsPGroup.of_bot
  obtain ⟨eA⟩ := nonempty_quotPCoreEquiv e₁.toMonoidHom e₁.surjective hk₁
  obtain ⟨eB⟩ := nonempty_quotPCoreEquiv g₀ hg₀ hk₀
  have hHat₁ : IsHat (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (eB.symm.trans eA) hHatW
  have hK₁P : K₁' ≤ P' := perfectCore_le P'
  have hOP : O ≤ P' := fun x hx => by
    show QuotientGroup.mk' O x ∈ Q₁
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Q₁.one_mem
  have hPN : P' ≤ Subgroup.normalizer (K₁' : Set ↥K) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P')
  have hidx : ∃ j, K₁'.relIndex P' = 2 ^ j := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 O)
    have h1 := Subgroup.relIndex_mul_relIndex K₁' (O ⊔ K₁') P' le_sup_right (sup_le hOP hK₁P)
    have h2 : K₁'.relIndex (O ⊔ K₁') ∣ 2 ^ n := by
      rw [A4.relIndex_sup_eq_of_le_normalizer' (hOP.trans hPN), ← hn]
      exact Subgroup.relIndex_dvd_card (H := K₁') (K := O)
    have h3 : (O ⊔ K₁').relIndex P' ∣ 16 := by
      have e : O ⊔ K₁' = W.comap (QuotientGroup.mk' O) := by
        rw [← hW1, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
      rw [e, hP', Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hmk]
      exact relIndex_perfectCore_comap_dvd hQ hHat.2.1 φ hh₀
    have h4 : K₁'.relIndex P' ∣ 2 ^ (n + 4) := by
      rw [← h1, pow_add]
      exact Nat.mul_dvd_mul h2 (by norm_num at h3 ⊢; exact h3)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hidx
  have hL1K₁ : S.L1 ≤ K₁ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxLN, m, hm, hxm⟩
    have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hxLN, m, hm, hxm⟩
    have hxP : (⟨x, hL1K hxL1⟩ : ↥K) ∈ P' := hL1B x hxL1
    have hx1 : (⟨x, hL1K hxL1⟩ : ↥K) ^ m = 1 := Subtype.ext (by simpa using hxm)
    exact ⟨_, mem_of_odd_of_relIndex_two_pow hK₁P hPN hj hxP hm hx1, rfl⟩
  have hK₁eq : K₁ = perfectCore (P'.map K.subtype) := map_perfectCore K.subtype P'
  have hconj : ∀ t ∈ T, ∀ g ∈ P'.map K.subtype, t * g * t⁻¹ ∈ P'.map K.subtype := by
    rintro t ht _ ⟨k, hk, rfl⟩
    have htK := hKn (hTH ht)
    refine ⟨⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK k).mp k.2⟩, ?_, rfl⟩
    show piM φ ⟨t * k * t⁻¹, _⟩ ∈ Bst
    rw [← sigM_piM φ ⟨t, htK⟩ k, ← hTinv t ht]
    exact ⟨_, hk, rfl⟩
  have hTP : T ≤ Subgroup.normalizer ((P'.map K.subtype : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj t ht g hg, fun hg => ?_⟩
    have := hconj t⁻¹ (T.inv_mem ht) _ hg
    have e : t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g := by group
    rwa [e] at this
  have hTN : T ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [hK₁eq]
    exact hTP.trans (normalizer_le_normalizer_perfectCore _)
  set H₁ := K₁ ⊔ (S.L1 ⊔ T) with hH₁
  have hH₁N : H₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le (hL1K₁.trans Subgroup.le_normalizer) hTN)
  have hK₁c : K₁ ∈ cComp H₁ :=
    cComp_mem_of_subnormal (A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hH₁N))
      (mem_cComp_self hK₁perf hHat₁.1)
  have hK₁H : K₁ ≤ H := hK₁K.trans hKH
  have hH₁z : H₁ ∈ S.Hz := S.mem_Hz_of le_sup_right ((sup_le hK₁H hH.1.1).trans hH.2.1)
    fun h => S.false_of_L1_le_perfect hH hK₁perf hK₁H (le_sup_left.trans h) hL1K₁
  exact hHat6 G T L V S hS H₁ hH₁z K₁ hK₁c hHat₁

end Setting4

theorem case13821HatM22_of_hat6
    (h16 : Lem13816)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hHat6 : Case13821Hat6) :
    Case13821HatM22 := by
  intro G _ _ T L V S hS H hH K hK hHat
  exact S.false_of_hatM22 hF318 h36 h38 hHat6 hS hH hK (h16 G T L V S hS H hH K hK).1.1 hHat

end CFSG.Quasithin.H13.A6
