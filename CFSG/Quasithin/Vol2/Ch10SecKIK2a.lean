module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Nilpotent

variable {Ω : Type*} [Group Ω] [Finite Ω] {X K : Subgroup Ω}

theorem isNilpotent_inf_centralizer (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K) :
    Group.IsNilpotent ↥(X ⊓ Subgroup.centralizer (K : Set Ω)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := X ⊓ Subgroup.centralizer (K : Set Ω) with hC
  have hp : IsPGroup 2 (↥C ⧸ Subgroup.center ↥C) := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨e, he⟩ := h2 c (Subgroup.mem_inf.1 c.2).1
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have hd := (Subgroup.mem_inf.1 d.2).2
    simpa using (Subgroup.mem_centralizer_iff.mp hd _ he).symm
  have := hp.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center ↥C))
    (by rw [QuotientGroup.ker_mk'])

theorem odd_orderOf_of_mem_inf_centralizer (hKn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K) (hO2 : pCoreOf 2 X = ⊥) {c : Ω}
    (hc : c ∈ X ⊓ Subgroup.centralizer (K : Set Ω)) : Odd (orderOf c) := by
  have := isNilpotent_inf_centralizer h2
  refine B1Red.odd_orderOf_of_nilpotent_normal inf_le_left (fun y hy x hx => ?_) hO2 c hc
  obtain ⟨hxX, hxK⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨X.mul_mem (X.mul_mem hy hxX) (X.inv_mem hy), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : y⁻¹ * k * y⁻¹⁻¹ ∈ K := hKn _ (X.inv_mem hy) k hk
  rw [inv_inv] at hk'
  have h := Subgroup.mem_centralizer_iff.mp hxK _ hk'
  calc k * (y * x * y⁻¹) = y * ((y⁻¹ * k * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * k * y)) * y⁻¹ := by rw [h]
    _ = y * x * y⁻¹ * k := by group

omit [Finite Ω] in
theorem eq_one_of_odd_of_two_pow {c : Ω} (hodd : Odd (orderOf c)) {k : ℕ} (hk : c ^ 2 ^ k = 1) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.1 hi
  · exfalso
    rw [hi, pow_succ] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (even_two.mul_left _)

end Nilpotent

section Centralizer

variable {G : Type} [Group G] [Finite G]

theorem convI_eq_one_of_two_pow {H J W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hred : IsTwoReducedIn H W) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) {g : Subgroup.normalizer (W : Set G)}
    (hg : (g : G) ∈ H) {k : ℕ} (hk : (g : G) ^ 2 ^ k = 1)
    (hc : convI hW g ∈ Subgroup.centralizer (autI hW J : Set (MulAut (IntMod W hW)))) :
    convI hW g = 1 := by
  set X := autI hW H with hX
  set K := autI hW J with hK
  have hKn : ∀ x ∈ X, ∀ y ∈ K, x * y * x⁻¹ ∈ K := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (mem_autI hW).1 hx
    obtain ⟨l, hl, rfl⟩ := (mem_autI hW).1 hy
    have hal : (a : G) * l * (a : G)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hHJ ha) l).mp hl
    have e : convI hW a * convI hW l * (convI hW a)⁻¹ = convI hW (a * l * a⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact convI_mem_autI hW hal (a * l * a⁻¹).2
  have h2' : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_autI hW).1 hx
    obtain ⟨e, he⟩ := h2 a ha
    refine ⟨e, ?_⟩
    rw [← map_pow]
    exact convI_mem_autI hW he (a ^ 2 ^ e).2
  have hO2 : pCoreOf 2 X = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hodd := odd_orderOf_of_mem_inf_centralizer hKn h2' hO2
    (Subgroup.mem_inf.2 ⟨(mem_autI hW).2 ⟨g, hg, rfl⟩, hc⟩)
  refine eq_one_of_odd_of_two_pow hodd (k := k) ?_
  rw [← map_pow]
  have : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [this, map_one]

end Centralizer

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
