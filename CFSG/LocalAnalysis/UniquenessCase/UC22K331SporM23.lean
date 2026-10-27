module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.Quasithin.Background.HSporLatMathieu
public import Certificates.Certificate1089001
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Alt8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.QuasithinUnique.Ch1.SporLat (memberOrTop)
open CFSG.Quasithin.H.MathieuLat

section Card

variable {L : Type} [Group L] [Finite L]

theorem card_sup_eq_of_isAlt_eight {T K : Subgroup L} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hK : IsAlt (Bar2 K) 8) (hTK : T ≤ Subgroup.normalizer (K : Set L)) :
    Nat.card ↥(K ⊔ T) = 315 * Nat.card T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hK
  have hKZ : K ≤ K ⊔ T := le_sup_left
  have hTZ : T ≤ K ⊔ T := le_sup_right
  have hZN : K ⊔ T ≤ Subgroup.normalizer (K : Set L) := sup_le Subgroup.le_normalizer hTK
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    (hT.of_le hTZ le_top).inf_of_le_normalizer hKZ hZN
  have hidx : T.relIndex (K ⊔ T) = (T ⊓ K).relIndex K := by
    haveI : (K.subgroupOf (K ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKZ).mpr hZN
    have h := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (K.subgroupOf (K ⊔ T))
      (T.subgroupOf (K ⊔ T))
    rw [← Subgroup.subgroupOf_sup hKZ hTZ, Subgroup.subgroupOf_self, Subgroup.relIndex_top_right,
      Subgroup.relIndex_subgroupOf hKZ] at h
    rw [Subgroup.inf_relIndex_right]
    exact h
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  have hbar : Nat.card (Bar2 K) = 20160 := by rw [Nat.card_congr e.toEquiv, nat_card_alt_eight]
  have hKc : Nat.card K = 315 * 2 ^ (6 + a) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    rw [show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160 from hbar, ha] at h
    rw [h, pow_add]
    ring
  obtain ⟨b, hb⟩ := hSylK.isPGroup.exists_card_eq
  have hodd : ¬ 2 ∣ (T ⊓ K).relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylK).2.2
  have hm : (T ⊓ K).relIndex K * 2 ^ b = 315 * 2 ^ (6 + a) := by
    have h := Subgroup.relIndex_mul_card (T ⊓ K) K
    rwa [inf_eq_left.mpr inf_le_right, hb, hKc] at h
  have hbc : b = 6 + a := by
    apply le_antisymm
    · have h1 : 2 ^ b ∣ 315 * 2 ^ (6 + a) := ⟨(T ⊓ K).relIndex K, by rw [← hm, mul_comm]⟩
      have h2 : Nat.Coprime (2 ^ b) 315 := Nat.Coprime.pow_left _ (by norm_num)
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h2.dvd_of_dvd_mul_left h1)
    · have h1 : 2 ^ (6 + a) ∣ (T ⊓ K).relIndex K * 2 ^ b := ⟨315, by rw [hm, mul_comm]⟩
      have h2 : Nat.Coprime (2 ^ (6 + a)) ((T ⊓ K).relIndex K) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h2.dvd_of_dvd_mul_left h1)
  rw [hbc] at hm
  have h315 : (T ⊓ K).relIndex K = 315 := Nat.eq_of_mul_eq_mul_right (by positivity) hm
  have hZc := Subgroup.relIndex_mul_card T (K ⊔ T)
  rw [inf_eq_left.mpr hTZ, hidx, h315] at hZc
  exact hZc.symm

theorem exists_orderOf_eq_fifteen_of_isAlt_eight {K : Subgroup L} (hK : IsAlt (Bar2 K) 8) :
    ∃ y ∈ K, orderOf y = 15 := by
  obtain ⟨e⟩ := hK
  obtain ⟨σ, hσ⟩ := CFSG.Quasithin.J4L4.exists_order_fifteen
  let f : ↥K →* alternatingGroup (Fin 8) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨x, hx⟩ := hf σ
  have h15 : 15 ∣ orderOf x := by
    have h := orderOf_map_dvd f x
    rwa [hx, hσ] at h
  refine ⟨((x ^ (orderOf x / 15) : ↥K) : L), (x ^ (orderOf x / 15)).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div (orderOf_pos x).ne' h15]

end Card

section Members


theorem m23Member_orderOf_ne_fifteen {j : ℕ} (hj : j = 2 ∨ j = 5)
    {z : ↥CFSG.Blueprint.NativeSporadic.M23} (hz : z ∈ m23Ctx.Y j) : orderOf z ≠ 15 := by
  rw [m23Ctx_Y] at hz
  exact Certificates.certificate1089001 j hj z hz

private theorem m23_S_isSylowTwoOf : IsSylowTwoOf m23Ctx.S ⊤ := by
  refine CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨m23Ctx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m23Ctx.S
  rw [m23Ctx.S_card, CFSG.Sporadic.Schreier.m23_card] at h1
  have h2 : m23Ctx.S.index = 79695 := by
    have : m23Ctx.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

end Members

private theorem exists_mulEquiv_map_eq {X Γ : Type} [Group X] [Finite X] [Group Γ] [Finite Γ]
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (e : X ≃* Γ) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp
    (CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hT)
  obtain ⟨hp₀, hi₀⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  rw [hST, Subgroup.map_map]
  rfl

theorem k331Idx_m23
    (hbr : Nonempty (Carrier .M23 ≃* TauCeti.SporadicName.M23.Group)) :
    K331Idx (.sporadic .M23) := by
  obtain ⟨b⟩ := hbr
  intro L _ _ _ _ ⟨e⟩ T hT K hK hTK
  exfalso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hP, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq m23_S_isSylowTwoOf (e.trans b.symm)
    (⟨hle, hP, hidx⟩ : IsSylowTwoOf T ⊤)
  have hSZ : m23Ctx.S ≤ (K ⊔ T).map ψ.toMonoidHom := hψ ▸ Subgroup.map_mono le_sup_right
  obtain ⟨j, hj, hZ⟩ := m23Ctx.complete _ hSZ
  have hk : m23Ctx.k = 7 := rfl
  have hTc : Nat.card T = 2 ^ 7 := by
    rw [← hk, ← m23Ctx.S_card, ← hψ, Subgroup.card_map_of_injective ψ.injective]
  have hZc : Nat.card ((K ⊔ T).map ψ.toMonoidHom) = 315 * 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective ψ.injective, card_sup_eq_of_isAlt_eight hT hK hTK, hTc]
  rw [hZ, m23Ctx.member_card, hk] at hZc
  have hjJ : j < m23Ctx.J := by
    by_contra hjJ
    rw [if_neg hjJ, m23_lat_cert.2.1] at hZc
    omega
  rw [if_pos hjJ] at hZc
  have hj16 : j < 16 := m23_J ▸ hjJ
  rw [om_size_eq m23_lat_cert.2.2 (by simpa using hj16)] at hZc
  have hj25 : j = 2 ∨ j = 5 := by
    interval_cases j <;> simp_all
  obtain ⟨y, hyK, hy⟩ := exists_orderOf_eq_fifteen_of_isAlt_eight hK
  have hyZ : ψ y ∈ m23Ctx.Y j := by
    have h := Subgroup.mem_map_of_mem ψ.toMonoidHom (le_sup_left (b := T) hyK)
    rw [hZ] at h
    simpa [memberOrTop, hjJ] using h
  exact m23Member_orderOf_ne_fifteen hj25 hyZ (by rw [MulEquiv.orderOf_eq]; exact hy)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
