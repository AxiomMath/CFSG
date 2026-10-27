module

public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Timmesfeld.Special

variable {G : Type*} [Group G] {D : Set G}

@[expose] noncomputable def twoCore (d : G) : Subgroup G :=
  (CFSG.pCore 2 (Subgroup.centralizer ({d} : Set G))).map
    (Subgroup.centralizer ({d} : Set G)).subtype

theorem twoCore_le_centralizer (d : G) : twoCore d ≤ Subgroup.centralizer ({d} : Set G) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem commute_of_mem_twoCore {d q : G} (hq : q ∈ twoCore d) : Commute q d :=
  (Subgroup.mem_centralizer_iff.mp (twoCore_le_centralizer d hq) d rfl).symm

theorem isPGroup_twoCore [Finite G] (d : G) : IsPGroup 2 (twoCore d) :=
  (CFSG.BaerSuzuki.Helpers.pCore_isPGroup
    (G := Subgroup.centralizer ({d} : Set G)) 2).map _

theorem conj_mem_twoCore {d q g : G} (hg : Commute g d) (hq : q ∈ twoCore d) :
    g * q * g⁻¹ ∈ twoCore d := by
  obtain ⟨x, hx, rfl⟩ := hq
  have hgC : g ∈ Subgroup.centralizer ({d} : Set G) := mem_centralizer_singleton hg
  refine ⟨⟨g, hgC⟩ * x * ⟨g, hgC⟩⁻¹, ?_, by simp⟩
  exact (CFSG.BaerSuzuki.Helpers.pCore_normal
    (G := Subgroup.centralizer ({d} : Set G)) 2).conj_mem x hx _

theorem mem_twoCore_iff_of_mem [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d p : G} (hp : p ∈ D) (hpd : Commute p d) :
    p ∈ twoCore d ↔ ∀ g : G, Commute g d →
      ¬ (¬ Commute p (g * p * g⁻¹) ∧ Odd (orderOf (p * (g * p * g⁻¹)))) := by
  set H := Subgroup.centralizer ({d} : Set G) with hH
  have hpH : p ∈ H := mem_centralizer_singleton hpd
  constructor
  · rintro hpQ g hgd ⟨hnc, hodd⟩
    have hgp := conj_mem_twoCore hgd hpQ
    have hprod : p * (g * p * g⁻¹) ∈ twoCore d := (twoCore d).mul_mem hpQ hgp
    have h1 := eq_one_of_mem_of_isPGroup (isPGroup_twoCore d) hprod hodd
    apply hnc
    have : g * p * g⁻¹ = p⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hD.inv_eq hp]
  · intro h
    refine ⟨⟨p, hpH⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
    intro k
    have hkd : Commute (k : G) d := (Subgroup.mem_centralizer_iff.mp k.2 d rfl).symm
    have hcD : (k : G) * p * (k : G)⁻¹ ∈ D := conj_mem_of_isClass hclass k hp
    have h1 : (⟨p, hpH⟩ : H) * ⟨p, hpH⟩ = 1 := Subtype.ext (hD.mul_self_eq_one hp)
    have h2 : (k * ⟨p, hpH⟩ * k⁻¹) * (k * ⟨p, hpH⟩ * k⁻¹) = 1 :=
      Subtype.ext (by simpa using hD.mul_self_eq_one hcD)
    have hord : orderOf (p * ((k : G) * p * (k : G)⁻¹)) =
        orderOf ((⟨p, hpH⟩ : H) * (k * ⟨p, hpH⟩ * k⁻¹)) := by
      rw [← Subgroup.orderOf_coe]
      simp
    rcases hD.orderOf_mul hp hcD with h24 | h24 | hodd
    · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inl (hord ▸ h24))
    · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inl (hord ▸ h24)))
    · by_cases hc : Commute p ((k : G) * p * (k : G)⁻¹)
      · have h2' := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hp)
          (hD.mul_self_eq_one hcD)).1 hc)
        have h1' : orderOf (p * ((k : G) * p * (k : G)⁻¹)) = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 h2' with h | h
          · exact h
          · rw [h] at hodd; exact absurd hodd (by decide)
        exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inr (hord ▸ h1')))
      · exact absurd ⟨hc, hodd⟩ (h k hkd)

theorem mem_twoCore_conj {d q : G} (hq : q ∈ twoCore d) (g : G) :
    g * q * g⁻¹ ∈ twoCore (g * d * g⁻¹) := by
  set H := Subgroup.centralizer ({d} : Set G)
  set H' := Subgroup.centralizer ({g * d * g⁻¹} : Set G)
  have hmem : ∀ x ∈ H, g * x * g⁻¹ ∈ H' := by
    intro x hx
    apply mem_centralizer_singleton
    have := (Commute.conj_iff g).2 (Subgroup.mem_centralizer_iff.mp hx d rfl).symm
    exact this
  have hmem' : ∀ x ∈ H', g⁻¹ * x * g ∈ H := by
    intro x hx
    apply mem_centralizer_singleton
    have := (Commute.conj_iff g⁻¹).2 (Subgroup.mem_centralizer_iff.mp hx (g * d * g⁻¹) rfl).symm
    simpa [mul_assoc] using this
  let φ : H ≃* H' :=
    { toFun := fun x => ⟨g * x * g⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨x, hx, rfl⟩ := hq
  have hmap := CFSG.pCore_map_iso 2 φ
  refine ⟨φ x, ?_, rfl⟩
  rw [← hmap]
  exact ⟨x, hx, rfl⟩

@[expose] def ExcPQ (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ p ∈ D, Commute d p → p ≠ d → d * p ∉ D → p ∉ twoCore d

@[expose] def NoLevi (D : Set G) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → Odd (orderOf (x * y)) → ∀ b ∈ D, Commute b x →
    ¬ Commute b y

theorem exists_levi_of_not_mem_twoCore [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d p : G} (hp : p ∈ D) (hpd : Commute p d)
    (hpQ : p ∉ twoCore d) :
    ∃ p' ∈ D, ¬ Commute p p' ∧ Odd (orderOf (p * p')) ∧ Commute d p ∧ Commute d p' := by
  rw [mem_twoCore_iff_of_mem hclass hD hp hpd] at hpQ
  obtain ⟨g, hg⟩ := not_forall.1 hpQ
  obtain ⟨hgd, hg'⟩ := not_imp.1 hg
  obtain ⟨hnc, hodd⟩ := not_not.1 hg'
  have hdp' : Commute d (g * p * g⁻¹) := by
    have h1 := (Commute.conj_iff g).2 hpd
    rw [show g * d * g⁻¹ = d by rw [hgd.eq, mul_inv_cancel_right]] at h1
    exact h1.symm
  exact ⟨_, conj_mem_of_isClass hclass g hp, hnc, hodd, hpd.symm, hdp'⟩

theorem NoLevi.mem_twoCore [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) {d p : G} (hd : d ∈ D) (hp : p ∈ D)
    (hpd : Commute p d) : p ∈ twoCore d := by
  by_contra hpQ
  obtain ⟨p', hp', hnc, hodd, h1, h2⟩ := exists_levi_of_not_mem_twoCore hclass hD hp hpd hpQ
  exact hNL p hp p' hp' hnc hodd d hd h1 h2

theorem NoLevi.closure_le_twoCore [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) {d : G} (hd : d ∈ D) :
    Subgroup.closure {p | p ∈ D ∧ Commute p d} ≤ twoCore d :=
  (Subgroup.closure_le _).2 fun _ ⟨hp, hpd⟩ => hNL.mem_twoCore hclass hD hd hp hpd

end CFSG.Timmesfeld.Moufang
