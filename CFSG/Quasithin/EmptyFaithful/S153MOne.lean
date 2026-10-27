module

public import CFSG.Quasithin.EmptyFaithful.S153MCore
public import CFSG.Quasithin.EmptyFaithful.S153MElt
public import CFSG.Quasithin.EmptyFaithful.S153MLayer
public import CFSG.Quasithin.EmptyFaithful.S1565M13

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565
open scoped Pointwise commutatorElement

namespace S153M

section One

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem eltOne_of_E_ff
    (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (hF : HypF918 T V L V₁ Vp H K) (M : Subgroup G) (hHK : H = K ⊔ T) (hS : SQTKGroup ↥H)
    (hK0 : conjClosure K T = K)
    (hkerchar : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    {n : ℕ} (hn3 : 3 ≤ n) (hnodd : Odd n) (hKs : Shape15365 n (E2.star (H ⊓ M) H K))
    {I : Subgroup G} (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hWK : tildeOf V₁ ⁅conjClosure I H, conjClosure K T⁆ = tildeOf V₁ (conjClosure I H))
    (hne : ¬ tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆)
    (hE : IsFFInt (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
      (tildeOf (conjClosure I H) (conjClosure Vp H)) (hF.isElemAbelian_quotient (conjClosure I H))) :
    FFnatEltConcl hF M I := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFU := factElem hF (le_conjClosure Vp H)
  have hFE : Fact (IsElemAbelian 2 (tildeOf (conjClosure I H) (conjClosure Vp H))) :=
    ⟨hF.isElemAbelian_quotient (conjClosure I H)⟩
  have hWN : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hUN : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure Vp H
  have hV₁W : V₁ ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hWU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 hWU
  have hUV : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hV₁H : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  set φ := actH hWN hUN with hφ
  have hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    actE_eq_one_of_mem_pCoreOf hF hV₁W hWN hUW hx
  have hnt : ¬ K.subgroupOf H ≤ φ.ker := by
    intro h
    refine not_forall_comm_of_ne hWU hWK hne ?_
    intro k hk u hu
    have hk' : k ∈ K := hK0 ▸ hk
    have h1 := h (Subgroup.mem_subgroupOf.mpr hk' : (⟨k, hKH hk'⟩ : ↥H) ∈ K.subgroupOf H)
    exact (actE_eq_one_iff hWN hUN hUW ⟨k, hKH hk'⟩).mp h1 u hu
  have hFF : IsFFModule φ.range := by
    have h1 : IsFFModule (autOn (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
        (tildeOf (conjClosure I H) (conjClosure Vp H))) := hE
    have hXH : conjClosure K T ⊔ T ≤ H := hF.K₀T_le_H
    rw [autOn_tilde_eq_map_actH hWN hUN hXH] at h1
    have h3 : (conjClosure K T ⊔ T).subgroupOf H = ⊤ := by
      rw [Subgroup.subgroupOf_eq_top, hK0, ← hHK]
    rw [h3, ← MonoidHom.range_eq_map] at h1
    exact h1
  obtain ⟨ρK, hρK, hρKφ, hker, -, hKsC, hsh, -, -⟩ :=
    kAction_data hA21 h51 hF (H ⊓ M) hHK hS hK0 hkerchar hn3 hnodd hKs hWN hUN hQ hnt hFF
  obtain ⟨S, hSb⟩ := exists_sylow_borel_lift_of_kernel hKH ρK hρK hker hB
  obtain ⟨b, hbN, r, hr, hbr, hbfix⟩ := ffNatShape_elt hsh hKsC S
  obtain ⟨k, hkM, hkb⟩ := hSb b hbN
  set k' : ↥H := Subgroup.inclusion hKH k with hk'
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k').ne'
  have hco : Nat.Coprime (2 ^ a) r := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hr)
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hco 0 1
  have hdvd : orderOf k' ∣ e * m := by
    have h2a : 2 ^ a ∣ e := (Nat.modEq_zero_iff_dvd).mp he0
    obtain ⟨c, hc⟩ := h2a
    rw [hom, hc]
    exact ⟨c, by ring⟩
  have hkem : (k' ^ e) ^ m = 1 := by
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hbe : b ^ e = b := by
    rw [pow_eq_pow_mod e hbr, he1, ← pow_eq_pow_mod 1 hbr, pow_one]
  have hφt : φ (k' ^ e) = (b : MulAut ↥(tildeOf (conjClosure I H) (conjClosure Vp H))) := by
    rw [map_pow]
    have h1 : φ k' = (b : MulAut ↥(tildeOf (conjClosure I H) (conjClosure Vp H))) := by
      rw [← hkb]
      exact (hρKφ k).symm
    rw [h1, ← Subgroup.coe_pow, hbe]
  have hK₀U : ⁅conjClosure Vp H, K⁆ ≤ conjClosure Vp H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKH.trans hUN)
  have hlayer := layer_transfer (K₀ := K) hV₁W hWU hV₁H hWN hUN hUV hUW hKH hK₀U (k' ^ e)
    (by
      intro e' he' hh
      rw [hφt] at hh
      exact hbfix e' he' hh)
  unfold FFnatEltConcl
  rw [hK0]
  refine ⟨k' ^ e, ?_, m, hm, ?_, hlayer⟩
  · rw [Subgroup.coe_pow]
    exact (M.pow_mem (Subgroup.mem_inf.mp hkM).2 e)
  · intro x _
    rw [← map_pow, hkem, map_one]
    rfl

end One

end S153M

end CFSG.Quasithin
