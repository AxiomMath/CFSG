module

public import CFSG.Quasithin.H13.L32A72h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

structure Ctx73 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (l₀ : G) : Prop
    extends Ctx72 G T L V l₀ where
  u0_eq : u0 T V = fsuV1 T V
  vh63 : H6.VolI_H_6_3
  vh65 : H6.VolI_H_6_5
  l71 : Lemma14_7_71
  uα : (pCoreOf 2 (hz T V)).relIndex (conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V)) = 2

omit [Finite G] in
theorem mem_normalizer_conjClosure_of {Z H : Subgroup G} {t : G}
    (hZ : t ∈ Subgroup.normalizer (Z : Set G)) (hH : t ∈ Subgroup.normalizer (H : Set G)) :
    t ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (Z : Set G) →
      g ∈ Subgroup.normalizer (H : Set G) →
      ∀ x ∈ conjClosure Z H, g * x * g⁻¹ ∈ conjClosure Z H := by
    intro g hgZ hgH x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      have e : g * (h * z * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hgH h).mp hh)
        ((Subgroup.mem_normalizer_iff.mp hgZ z).mp hz)
    | one => simp
    | mul a b _ _ iha ihb =>
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact inv_mem iha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t hZ hH x, fun hx => ?_⟩
  have := key t⁻¹ (inv_mem hZ) (inv_mem hH) _ hx
  simpa [mul_assoc] using this

theorem perm5_no_comm_invol : ∀ c n : Equiv.Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 → n ^ 2 = 1 →
    n ≠ 1 → Equiv.Perm.sign n = 1 → n * c ≠ c * n := by
  decide +kernel

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem T_le_normalizer_sL : T ≤ Subgroup.normalizer (sL T L V : Set G) := fun _ ht =>
  mem_normalizer_conjClosure_of
    (le_normalizer_conjClosure V _ (C.hF.T_normalizes_V₁ ht)) (C.hyp.normalizes C.h13322 ht)

theorem l1T_le_normalizer_sL :
    L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (sL T L V : Set G) :=
  sup_le ((L32NSet14.Setting.L1_le.trans inf_le_left).trans (le_normalizer_conjClosure _ _))
    C.T_le_normalizer_sL

theorem sL_le_R1 : sL T L V ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 (C.sL_le_T.trans le_sup_right) C.l1T_le_normalizer_sL
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le
      (sL_le_pCoreOf C.setting C.hF C.hMod))

theorem QH_le_R1 : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans C.hF.L₁T_le_H
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le C.hyp hTH).trans le_sup_right)
    ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem sup_eq_R1 :
    sL T L V ⊔ pCoreOf 2 (hz T V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hle : sL T L V ⊔ pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    sup_le C.sL_le_R1 C.QH_le_R1
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (hz T V))
    (sL T L V ⊔ pCoreOf 2 (hz T V)) _ le_sup_right hle
  rw [h4] at hmul
  have hdvd : (pCoreOf 2 (hz T V)).relIndex (sL T L V ⊔ pCoreOf 2 (hz T V)) ∣ 4 :=
    Dvd.intro _ hmul
  have hcases : (pCoreOf 2 (hz T V)).relIndex (sL T L V ⊔ pCoreOf 2 (hz T V)) = 1 ∨
      (pCoreOf 2 (hz T V)).relIndex (sL T L V ⊔ pCoreOf 2 (hz T V)) = 2 ∨
      (pCoreOf 2 (hz T V)).relIndex (sL T L V ⊔ pCoreOf 2 (hz T V)) = 4 := by
    have : (pCoreOf 2 (hz T V)).relIndex (sL T L V ⊔ pCoreOf 2 (hz T V)) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at this
    simpa using this
  have hUαS : conjSub l₀ (fsuU T V) ≤ sL T L V := fun u hu => by
    rw [mem_conjSub] at hu
    have := mem_conjClosure C.mem hu
    rwa [show l₀ * (l₀⁻¹ * u * l₀) * l₀⁻¹ = u by group] at this
  rcases hcases with h1 | h2 | h4'
  · exfalso
    have h1' : conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V) ≤ pCoreOf 2 (hz T V) :=
      (sup_le_sup_right hUαS _).trans (Subgroup.relIndex_eq_one.mp h1)
    have := C.uα
    rw [Subgroup.relIndex_eq_one.mpr h1'] at this
    norm_num at this
  · exfalso
    obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
    have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
    have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans C.hF.L₁T_le_H
    have hR1H : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ hz T V :=
      (pCoreOf_le 2 _).trans (sup_le hL1H hTH)
    have hQ1 : ∀ y (hy : y ∈ hz T V), φ ⟨y, hy⟩ = 1 ↔ y ∈ pCoreOf 2 (hz T V) := by
      intro y hy
      rw [← MonoidHom.mem_ker, hk, ← mem_pCoreOf_iff']
    obtain ⟨s, hs1, hs2⟩ : ∃ s ∈ sL T L V ⊔ pCoreOf 2 (hz T V), s ∉ pCoreOf 2 (hz T V) := by
      by_contra hc
      push Not at hc
      rw [Subgroup.relIndex_eq_one.mpr hc] at h2
      norm_num at h2
    have hsH : s ∈ hz T V := hR1H (hle hs1)
    obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
    have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
    have hxH : x ∈ hz T V := hL1H hxL1
    have hxQ : x ∉ pCoreOf 2 (hz T V) := by
      intro hxQ
      obtain ⟨k, hk'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (hz T V)) ⟨x, hxQ⟩
      have h2k : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk'
      have hord : orderOf x = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
          (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one h2k)
      exact hx1 (orderOf_eq_one_iff.mp hord)
    have hxQH : x ∈ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
      le_normalizer_pCoreOf 2 _ hxH
    have hxS : x ∈ Subgroup.normalizer (sL T L V : Set G) := le_normalizer_conjClosure _ _ hxL
    have hxsup : x ∈ Subgroup.normalizer
        ((sL T L V ⊔ pCoreOf 2 (hz T V) : Subgroup G) : Set G) := by
      rw [← conjSub_eq_self_iff, conjSub, Subgroup.map_sup,
        show (sL T L V).map (MulAut.conj x).toMonoidHom = sL T L V from
          conjSub_eq_self_iff.mpr hxS,
        show (pCoreOf 2 (hz T V)).map (MulAut.conj x).toMonoidHom = pCoreOf 2 (hz T V) from
          conjSub_eq_self_iff.mpr hxQH]
    have hcard : Nat.card ↥(sL T L V ⊔ pCoreOf 2 (hz T V)) =
        2 * Nat.card ↥(pCoreOf 2 (hz T V)) := by
      have := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) (sL T L V ⊔ pCoreOf 2 (hz T V))
      rw [inf_eq_left.mpr le_sup_right, h2] at this
      omega
    have hxs : x * s * x⁻¹ ∈ sL T L V ⊔ pCoreOf 2 (hz T V) :=
      (Subgroup.mem_normalizer_iff.mp hxsup s).mp hs1
    have hxsQ : x * s * x⁻¹ ∉ pCoreOf 2 (hz T V) := fun h =>
      hs2 ((Subgroup.mem_normalizer_iff.mp hxQH s).mpr h)
    have hprod := L32NSet14.mul_mem_of_card_eq_two_mul le_sup_right hcard Nat.card_pos.ne'
      hxs hs1 hxsQ hs2
    have hss := L32NSet14.mul_mem_of_card_eq_two_mul le_sup_right hcard Nat.card_pos.ne'
      hs1 hs1 hs2 hs2
    set c := φ ⟨x, hxH⟩ with hc
    set n := φ ⟨s, hsH⟩ with hn
    have hc3 : c ^ 3 = 1 := by
      rw [hc, ← map_pow, show (⟨x, hxH⟩ : ↥(hz T V)) ^ 3 = 1 from
        Subtype.ext (by simpa using hx3), map_one]
    have hc1 : c ≠ 1 := fun h => hxQ ((hQ1 x hxH).mp h)
    have hn2 : n ^ 2 = 1 := by
      rw [hn, ← map_pow, pow_two]
      exact (hQ1 _ (mul_mem hsH hsH)).mpr hss
    have hn1 : n ≠ 1 := fun h => hs2 ((hQ1 s hsH).mp h)
    have hsign : Equiv.Perm.sign n = 1 :=
      sign_phi_of_card_four hk hR1H h4 hxH hx3 hxQ
        (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL1)) (hle hs1)
    have hcomm : n * c = c * n := by
      have h1 : φ ⟨x * s * x⁻¹ * s, mul_mem (mul_mem (mul_mem hxH hsH) (inv_mem hxH)) hsH⟩ = 1 :=
        (hQ1 _ _).mpr hprod
      have e : (⟨x * s * x⁻¹ * s, mul_mem (mul_mem (mul_mem hxH hsH) (inv_mem hxH)) hsH⟩ :
          ↥(hz T V)) = ⟨x, hxH⟩ * ⟨s, hsH⟩ * (⟨x, hxH⟩)⁻¹ * ⟨s, hsH⟩ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, ← hc, ← hn] at h1
      have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hn2)
      have h2 : c * n * c⁻¹ = n⁻¹ := eq_inv_of_mul_eq_one_left h1
      symm
      calc c * n = (c * n * c⁻¹) * c := by group
        _ = n * c := by rw [h2, hninv]
    exact perm5_no_comm_invol c n hc3 hc1 hn2 hn1 hsign hcomm
  · have h1 : (sL T L V ⊔ pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = 1 :=
      by rw [h4'] at hmul; omega
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)

end Ctx73

end CFSG.Quasithin.H13.L32A
