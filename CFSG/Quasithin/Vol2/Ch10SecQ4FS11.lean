module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS10
public import CFSG.Quasithin.Vol2.Ch10SecFComm
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem mem_pCoreOf_of_forall_commute {K : Subgroup G} (hKa : IsAltType K 5) {x : G}
    (hxK : x ∈ K) (hx : ∀ k ∈ K, x * k = k * x) : x ∈ pCoreOf 2 K := by
  obtain ⟨α, hαs, hαk, -⟩ := hKa
  have h1 : α ⟨x, hxK⟩ = 1 := by
    refine SecF.alternatingGroup_five_center _ fun h => ?_
    obtain ⟨k, rfl⟩ := hαs h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx k k.2)
  have hk : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← hαk]
    exact h1
  exact Subgroup.mem_map_of_mem K.subtype hk

theorem orderOf_ne_three_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    orderOf x ≠ 3 := by
  intro h3
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h := orderOf_dvd_of_pow_eq_one hxn
  rw [h3] at h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

variable [Finite G]

theorem not_mem_zpowers_of_forall_commute {A : Subgroup G} (hAa : IsAltType A 5) {a b : G}
    (haA : a ∈ A) (hb3 : orderOf b = 3) (hbc : ∀ x ∈ A, b * x = x * b) :
    b ∉ Subgroup.zpowers a := by
  intro h
  have hbA : b ∈ A := (Subgroup.zpowers_le.mpr haA) h
  exact orderOf_ne_three_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    (mem_pCoreOf_of_forall_commute hAa hbA hbc) hb3

theorem mem_normalizer_of_three {H K L : Subgroup G} (hK : K ∈ cComp H) (hKs : IsShort2 K)
    (hKa : IsAltType K 5) {αL : ↥L →* alternatingGroup (Fin 5)} (hαs : Function.Surjective αL)
    (hαk : αL.ker = CFSG.pCore 2 ↥L) {q : G} (hqK : q ∈ K) (hqL : q ∈ L) (hq3 : orderOf q = 3)
    {x : G} (hxH : x ∈ H) (hxL : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hxn
  have hK'c : K.map (MulAut.conj x).toMonoidHom ∈ cComp H :=
    LocDbl.map_conj_mem_cComp hK (Subgroup.le_normalizer hxH)
  have hK's : IsShort2 (K.map (MulAut.conj x).toMonoidHom) :=
    Lin2.IsShort2.map_equiv hKs (MulAut.conj x)
  have hne : K ≠ K.map (MulAut.conj x).toMonoidHom := fun h =>
    hxn (LocDbl.map_conj_eq_iff.mp h.symm)
  have hcomm := commutator_eq_bot_of_mem_cComp hK hK'c hKs hK's
    (isQuasisimple_of_isAltType hKs hKa) hne
  have hyK' : x * q * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom :=
    ⟨q, hqK, by simp [MulAut.conj_apply]⟩
  have hyL : x * q * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL q).mp hqL
  have hy3 : orderOf (x * q * x⁻¹) = 3 := by
    have h := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective q
    rw [← hq3, ← h]
    simp [MulAut.conj_apply]
  have hyc : ∀ k ∈ K, x * q * x⁻¹ * k = k * (x * q * x⁻¹) := by
    intro k hk
    have hkC := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hk
    exact Subgroup.mem_centralizer_iff.mp hkC _ hyK'
  have h9 := nine_dvd_card_sup hq3 hy3 (hyc q hqK).symm
    (not_mem_zpowers_of_forall_commute hKa hqK hy3 hyc)
  have hle : Subgroup.zpowers q ⊔ Subgroup.zpowers (x * q * x⁻¹) ≤ L :=
    sup_le (Subgroup.zpowers_le.mpr hqL) (Subgroup.zpowers_le.mpr hyL)
  exact not_nine_dvd_card hαs hαk (h9.trans (Subgroup.card_dvd_of_le hle))

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
