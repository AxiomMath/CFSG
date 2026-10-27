module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldExceptional
public import CFSG.RankThree.PartOne.KC.SymplecticInnerActor
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalNoninner

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem noninner_plane_conclusion_of_model {T T₀ : Type*} [Group T] [Group T₀] [Finite T]
    [Finite T₀] (e : T ≃* T₀) {p ℓ f : ℕ} (hp : p.Prime)
    (hcap : ∀ A₀ : Subgroup (MulAut T₀), IsElementaryAbelian p A₀ → Nat.card A₀ = p ^ 2 →
      ¬ A₀ ≤ (MulAut.conj : T₀ →* MulAut T₀).range →
      Nat.card (A₀ ⊓ (MulAut.conj : T₀ →* MulAut T₀).range : Subgroup (MulAut T₀)) = p ∧
        p ∣ f ∧ 2 ^ p ≤ ℓ ^ f)
    (hcore : ∀ B₀ A₀ : Subgroup (MulAut T₀), (MulAut.conj : T₀ →* MulAut T₀).range ≤ B₀ →
      A₀ ≤ B₀ → IsElementaryAbelian p A₀ → Nat.card A₀ = p ^ 2 →
      ¬ A₀ ≤ (MulAut.conj : T₀ →* MulAut T₀).range → ∀ a ∈ A₀,
      a ∉ (MulAut.conj : T₀ →* MulAut T₀).range →
        inSubgroup (aschbacherSolvableCore p) (B₀ ⊓ Subgroup.centralizer {a}) = ⊥)
    (hodd : 3 < ℓ ^ f → ∀ B₀ : Subgroup (MulAut T₀),
      (MulAut.conj : T₀ →* MulAut T₀).range ≤ B₀ →
      ∀ t ∈ (MulAut.conj : T₀ →* MulAut T₀).range, orderOf t = p →
      ∀ A' : Subgroup (MulAut T₀), A' ≤ B₀ ⊓ Subgroup.centralizer {t} → IsPGroup p A' →
        Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B₀ ⊓ Subgroup.centralizer {t}),
          A'⁆ : Subgroup (MulAut T₀))))
    (Q : Prop)
    (hQ : ∀ A₀ : Subgroup (MulAut T₀), IsElementaryAbelian p A₀ → Nat.card A₀ = p ^ 2 →
      ¬ A₀ ≤ (MulAut.conj : T₀ →* MulAut T₀).range → Q)
    (B : Subgroup (MulAut T)) (hB : (MulAut.conj : T →* MulAut T).range ≤ B)
    (A : Subgroup (MulAut T)) (hAB : A ≤ B) (hAel : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hAH : ¬ A ≤ (MulAut.conj : T →* MulAut T).range) :
    Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range : Subgroup (MulAut T)) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧
      (∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      (∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : T →* MulAut T).range → autPlaneProduct p B A t = ⊥)) ∧ Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hAel
  set φ := MulAut.congr e with hφ
  have hconj := map_conj_range_mulAutCongr e
  have hA'el : IsElementaryAbelian p (A.map φ.toMonoidHom) :=
    IsElementaryAbelian.map φ.toMonoidHom
  have hA'card : Nat.card (A.map φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hAcard]
  have hA'H : ¬ A.map φ.toMonoidHom ≤ (MulAut.conj : T₀ →* MulAut T₀).range := by
    intro hle
    apply hAH
    rw [← hconj] at hle
    exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp hle
  obtain ⟨hcap', hpf, hq'⟩ := hcap _ hA'el hA'card hA'H
  have hcapT : Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range :
      Subgroup (MulAut T)) = p := by
    have h1 : (A ⊓ (MulAut.conj : T →* MulAut T).range).map φ.toMonoidHom =
        A.map φ.toMonoidHom ⊓ (MulAut.conj : T₀ →* MulAut T₀).range := by
      rw [Subgroup.map_inf _ _ _ φ.injective, hconj]
    have h2 := Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective
      (K := A ⊓ (MulAut.conj : T →* MulAut T).range)
    rw [h1] at h2
    rw [← h2]
    exact hcap'
  have hcoreT : ∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
    intro a haA haH
    have h1 := hcore (B.map φ.toMonoidHom) (A.map φ.toMonoidHom)
      (by rw [← hconj]; exact Subgroup.map_mono hB) (Subgroup.map_mono hAB) hA'el hA'card hA'H
      (φ a) (Subgroup.mem_map_of_mem _ haA) (by
        intro h'
        apply haH
        rw [← hconj] at h'
        exact (Subgroup.mem_map_iff_mem φ.injective).mp h')
    rw [← map_inSubgroup_theta_centralizer_mulEquiv hp φ B a] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have hoddT : 3 < ℓ ^ f → ∀ t ∈ (MulAut.conj : T →* MulAut T).range, orderOf t = p →
      ∀ A' : Subgroup (MulAut T), A' ≤ B ⊓ Subgroup.centralizer {t} → IsPGroup p A' →
        Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}),
          A'⁆ : Subgroup (MulAut T))) := by
    intro hq3 t htH htp A' hA'le hA'p
    have hA'0 : A'.map φ.toMonoidHom ≤
        B.map φ.toMonoidHom ⊓ Subgroup.centralizer {φ t} := by
      rw [← map_centralizer_singleton_mulEquiv φ t, ← Subgroup.map_inf _ _ _ φ.injective]
      exact Subgroup.map_mono hA'le
    have hA'0p : IsPGroup p ↥(A'.map φ.toMonoidHom) :=
      hA'p.of_equiv (A'.equivMapOfInjective φ.toMonoidHom φ.injective)
    have h1 := hodd hq3 (B.map φ.toMonoidHom)
      (by rw [← hconj]; exact Subgroup.map_mono hB) (φ t)
      (by rw [← hconj]; exact Subgroup.mem_map_of_mem _ htH)
      (by rw [MulEquiv.orderOf_eq]; exact htp) _ hA'0 hA'0p
    rw [← map_inSubgroup_theta_centralizer_mulEquiv hp φ B t, ← Subgroup.map_commutator,
      Subgroup.card_map_of_injective φ.injective] at h1
    exact h1
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := KCOrthogonalNoninner.noninner_plane_conclusion_of_core hp B A
    hAB hAel hAcard hAH hcapT hpf hq' hcoreT hoddT
  exact ⟨c1, c2, c3, c4, c5, c6, hQ _ hA'el hA'card hA'H⟩

end CFSG.RankThree.PartOne.KCSpComm

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)

theorem symplectic_noninner_plane_local_core_product_odd_of_clause
    (hsub : SymplecticSubfieldClause) : SymplecticNoninnerPlaneLocalCoreOdd := by
  intro T _ _ ℓ f r p hmod hp hp3 hpℓ B hB A hAB hAel hAcard hAnot
  obtain ⟨⟨hℓ, hf, hr, -⟩, K, hFld, hFin, hK, ⟨e⟩⟩ := hmod
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r := ⟨by omega⟩
  have hp2 : p ≠ 2 := by omega
  have O := spOuter hℓ hf hr hK
  have hcyc : IsCyclic (K ≃+* K) := by
    obtain ⟨σ, -, -, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, htop⟩
  have hq2 : p ∣ f → 2 ^ p ≤ ℓ ^ f := fun hpf =>
    calc 2 ^ p ≤ ℓ ^ p := Nat.pow_le_pow_left hℓ.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos (Nat.le_of_dvd (by omega) hpf)
  obtain ⟨h1, h2, h3, h4, h5, h6, h8⟩ := noninner_plane_conclusion_of_model (ℓ := ℓ) (f := f) e hp
    (fun A₀ hA₀el hA₀card hA₀H => by
      have := hA₀el
      have hcap := card_inf_inner_eq_prime O hr hp hp2 hcyc hA₀card hA₀H
      obtain ⟨a₀, ha₀A, ha₀H⟩ := IsConcreteLE.not_le_iff_exists.mp hA₀H
      obtain ⟨hpf, -⟩ := noninner_element_data O hp hp2 ha₀A ha₀H
      exact ⟨hcap, hpf, hq2 hpf⟩)
    (fun B₀ A₀ hB₀ _ hA₀el hA₀card hA₀H a ha haH => by
      have := hA₀el
      exact core_eq_bot_of_noninner hsub hℓ hf hr hK O hp hp3 hpℓ hB₀ ha haH)
    (fun hq3 B₀ hB₀ t ht htp A' hA' hA'p =>
      (symplectic_inner_actor_local_core_commutators_odd hℓ hf hr hK hq3 hp hp3 hpℓ B₀ hB₀ t ht
        htp A' hA' hA'p).2.2.1)
    (r = 2 → ℓ = 2 → f = p → p = 5 ∧ ℓ ^ f = 32)
    (fun A₀ hA₀el hA₀card hA₀H => by
      have := hA₀el
      exact noninner_plane_exceptional O hℓ hf hr hK hp hp3 hcyc hA₀card hA₀H)
    B hB A hAB hAel hAcard hAnot
  have h7 : 3 < ℓ ^ f := by
    have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    omega
  exact ⟨h1, h2, h3, h7, h4, h5, h6, h8⟩

end CFSG.RankThree.PartOne
