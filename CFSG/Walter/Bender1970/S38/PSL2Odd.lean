module

public import CFSG.Walter.Bender1970.S38.SmallQ
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.Walter

open scoped MatrixGroups

section General

variable {L : Type*} [Group L] [Finite L]

theorem exists_normalizer_regular_of_card_four (V : Sylow 2 L)
    (hVab : IsMulCommutative (V : Subgroup L)) (hV2 : ∀ x ∈ (V : Subgroup L), x ^ 2 = 1)
    (hV4 : Nat.card (V : Subgroup L) = 4)
    (hconj : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∃ g ∈ Subgroup.normalizer ((V : Subgroup L) : Set L),
      g ∉ Subgroup.centralizer ((V : Subgroup L) : Set L) ∧
      g ^ 3 ∈ Subgroup.centralizer ((V : Subgroup L) : Set L) ∧
      ∀ x ∈ (V : Subgroup L), x ≠ 1 → ∀ y ∈ (V : Subgroup L), y ≠ 1 →
        ∃ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Vg := (V : Subgroup L) with hVg
  let _ : CommGroup Vg := IsMulCommutative.instCommGroup
  set Nr := Subgroup.normalizer (Vg : Set L) with hNr
  set φ : Nr →* MulAut Vg := Vg.normalizerMonoidHom with hφ
  have hφapp : ∀ (n : Nr) (x : Vg), ((φ n x : Vg) : L) = (n : L) * (x : L) * (n : L)⁻¹ :=
    fun _ _ => rfl
  set A : Subgroup (MulAut Vg) := φ.range with hA
  have hcommV : ∀ a b : Vg, a * b = b * a := fun a b => hVab.is_comm.comm a b
  have hAodd : Odd (Nat.card A) := by
    have hVN : Vg ≤ Nr := Subgroup.le_normalizer
    have hker : Vg.subgroupOf Nr ≤ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcommV ⟨y, hy⟩ ⟨x, hx⟩)
    have h1 : φ.ker.index = Nat.card A := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Vg.subgroupOf Nr).index := Subgroup.index_dvd_of_le hker
    have h3 : (Vg.subgroupOf Nr).index ∣ Vg.index := Subgroup.relIndex_dvd_index_of_le hVN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    rw [← h1] at h
    exact V.not_dvd_index (h.trans (h2.trans h3))
  have htrans : ∀ u v : Vg, u ≠ 1 → v ≠ 1 → ∃ a ∈ A, a u = v := by
    intro u v hu hv
    have hu2 : orderOf (u : L) = 2 := by
      rw [Subgroup.orderOf_coe]
      apply orderOf_eq_prime (by exact Subtype.ext (by simpa using hV2 u u.2)) hu
    have hv2 : orderOf (v : L) = 2 := by
      rw [Subgroup.orderOf_coe]
      apply orderOf_eq_prime (by exact Subtype.ext (by simpa using hV2 v v.2)) hv
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ _ hu2 hv2)
    have : IsMulCommutative V := hVab
    obtain ⟨n, hn, hneq⟩ := Sylow.conj_eq_normalizer_conj_of_mem V (u : L) c⁻¹ u.2
      (by rw [inv_inv, hc]; exact v.2)
    refine ⟨φ ⟨n⁻¹, Nr.inv_mem hn⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [hφapp]
    simp only [inv_inv] at hneq ⊢
    rw [← hneq, hc]
  have hV2' : ∀ v : Vg, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV2 v v.2)
  obtain ⟨R, hRA, hRcyc, hRcard, -, hRtrans, -⟩ :=
    exists_regular_of_card_eq hV2' (Or.inl hV4) hAodd htrans
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := R)
  have hrord : orderOf r = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr]
    omega
  obtain ⟨g, hg⟩ := hRA r.2
  have hker : ∀ m : Nr, φ m = 1 → (m : L) ∈ Subgroup.centralizer (Vg : Set L) := by
    intro m hm
    have : m ∈ φ.ker := hm
    rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨g, g.2, fun hgC => ?_, ?_, ?_⟩
  · have : φ g = 1 := by
      ext x
      rw [hφapp]
      change (g : L) * x * (g : L)⁻¹ = x
      rw [(Subgroup.mem_centralizer_iff.mp hgC x x.2).symm, mul_inv_cancel_right]
    have h1 : (r : MulAut Vg) = 1 := by rw [← hg, this]
    have h2 : r = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hrord
    omega
  · have h := hker (g ^ 3) (by
      rw [map_pow, hg, ← Subgroup.coe_pow, ← hrord, pow_orderOf_eq_one]
      rfl)
    simpa using h
  · intro x hx hx1 y hy hy1
    obtain ⟨r', hr', hr'xy⟩ := hRtrans ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hx1 (congrArg Subtype.val h))
      (fun h => hy1 (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hr ⟨r', hr'⟩) :
      (⟨r', hr'⟩ : R) ∈ Submonoid.powers r)
    refine ⟨k, ?_⟩
    have h1 : φ (g ^ k) = r' := by
      rw [map_pow, hg]
      exact congrArg Subtype.val hk
    have h2 : ((φ (g ^ k) ⟨x, hx⟩ : Vg) : L) = ((r' ⟨x, hx⟩ : Vg) : L) := by rw [h1]
    rw [hφapp, Subgroup.coe_pow] at h2
    rw [h2]
    exact congrArg Subtype.val hr'xy

end General

theorem psl2_odd_normalizer_sylow_two {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (V : Sylow 2 PSL(2, GaloisField p f)) :
    ∃ g ∈ Subgroup.normalizer ((V : Subgroup PSL(2, GaloisField p f)) :
        Set PSL(2, GaloisField p f)),
      g ∉ Subgroup.centralizer ((V : Subgroup PSL(2, GaloisField p f)) :
        Set PSL(2, GaloisField p f)) ∧
      g ^ 3 ∈ Subgroup.centralizer ((V : Subgroup PSL(2, GaloisField p f)) :
        Set PSL(2, GaloisField p f)) ∧
      ∀ x ∈ (V : Subgroup PSL(2, GaloisField p f)), x ≠ 1 →
        ∀ y ∈ (V : Subgroup PSL(2, GaloisField p f)), y ≠ 1 →
          ∃ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = y := by
  have hK := psl2_odd_sylow_two_isKleinFour hp hf h8 V
  have hab : IsMulCommutative (V : Subgroup PSL(2, GaloisField p f)) :=
    IsKleinFour.isMulCommutative
  refine exists_normalizer_regular_of_card_four V hab (fun x hx => ?_) hK.card_four
    (fun x y hx hy => psl2_odd_isConj_of_orderOf_eq_two hp hf hx hy)
  have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : (V : Subgroup PSL(2, GaloisField p f)))
  rw [hK.exponent_two] at h
  simpa using congrArg Subtype.val h

end CFSG.Walter
