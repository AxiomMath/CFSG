module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxD4Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxD4Lat
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6

namespace GoldCMax

theorem exists_zpowers_of_card_two {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (h : Nat.card ↥A = 2) : ∃ z : Γ, orderOf z = 2 ∧ A = Subgroup.zpowers z := by
  have hfin : Finite ↥A := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥A)
  have hz1 : (a : Γ) ≠ 1 := fun h' => ha (Subtype.ext h')
  have hz2 : orderOf (a : Γ) = 2 := by
    have hd : orderOf (a : Γ) ∣ 2 := by
      rw [Subgroup.orderOf_coe, ← h]
      exact orderOf_dvd_natCard a
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') hz1
    · exact h'
  refine ⟨a, hz2, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2) ?_
  rw [h, Nat.card_zpowers, hz2]

theorem eq_gen_of_mem_zpowers_two {G : Type*} [Group G] {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) (hx1 : x ≠ 1) : x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h := zpow_mod_orderOf z k
  rw [hz, Nat.cast_ofNat] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at h
    exact absurd h.symm hx1
  · rw [h1, zpow_one] at h
    exact h.symm

theorem normalizer_le_centralizer_of_two {G : Type*} [Group G] {z : G} (hz : orderOf z = 2) :
    Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({z} : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hzA : g * z * g⁻¹ ∈ Subgroup.zpowers z := (hg z).mp (Subgroup.mem_zpowers z)
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h
    have : z = 1 := by simpa using h
    rw [this, orderOf_one] at hz
    omega
  have h := eq_gen_of_mem_zpowers_two hz hzA hne
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h]

theorem normalizer_le_normalizer_centerOf {G : Type*} [Group G] (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (centerOf U : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ x ∈ centerOf U, g * x * g⁻¹ ∈ centerOf U := by
    intro g hg x hx
    rw [Subgroup.mem_normalizer_iff] at hg
    obtain ⟨hxU, hxc⟩ := hx
    refine ⟨(hg x).mp hxU, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U := by
      refine (hg (g⁻¹ * u * g⁻¹⁻¹)).mpr ?_
      have e : g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u := by group
      rw [e]
      exact hu
    have h := Subgroup.mem_centralizer_iff.mp hxc _ hu'
    calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * u := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := Subgroup.inv_mem _ hg
  have h := key g⁻¹ hg' _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

section D4


theorem centMaxProp_d4_of_cent3Data (K : Type) [Field K] [Finite K] (hK : Nat.card K = 8)
    (σ : K ≃+* K) (h3 : Cent3Data ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    CentMaxProp ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨U, hUN⟩ := exists_standard_sylow_d4 hK σ
  have hU2 : IsPGroup 2 ↥(U : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    U.isPGroup'
  have hUi : ¬ 2 ∣ (U : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index :=
    U.not_dvd_index
  obtain ⟨hcard, h3dvd⟩ := h3 _ hU2 hUi
  obtain ⟨z, hz2, hcen⟩ := exists_zpowers_of_card_two hcard
  have hBC : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤
      Subgroup.centralizer ({z} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [← hUN]
    refine (normalizer_le_normalizer_centerOf _).trans ?_
    rw [hcen]
    exact normalizer_le_centralizer_of_two hz2
  have hneB : Subgroup.centralizer ({z} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    intro h
    have h3B : 3 ∣ Nat.card ((graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← h, ← centralizer_zpowers_eq, ← hcen]
      exact h3dvd
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedRootBorel_le TwistTag.D4 K σ.toRingHom)).toEquiv] at h3B
    exact not_three_dvd_card_graphFixedRootBorel_d4 hK σ h3B
  have hnetop : Subgroup.centralizer
      ({z} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ ⊤ := by
    intro htop
    have hzc : z ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer
          ({z} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [exceptional_fixed_center_trivial _ _ σ, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz2
    omega
  exact centMaxProp_of_data hU2 hUi hz2 hcen
    (isMaxSubgroupIn_d4_of_borel K σ hBC hneB hnetop)

end D4

end GoldCMax

open GoldCMax in
theorem centMaxProp_3d4
    {X : Type} [Group X] [Finite X] (h : ChevalleyExceptionalModel X .trialityD4 2 1) :
    CentMaxProp X := by
  obtain ⟨-, K, hFld, hFin, σ, hK, -, ⟨e⟩⟩ := exists_mulEquiv_triality_model h
  have hK8 : Nat.card K = 8 := by norm_num at hK; exact hK
  exact (centMaxProp_d4_of_cent3Data K hK8 σ
    ((cent3Data_of_trialityD4 h).of_mulEquiv e)).of_mulEquiv e.symm

theorem centMax_3d4
    (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q) (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index)
    (hQ : Is3D4 2 1 Q) (W : Subgroup Q) (hW : W ≤ centerOf P) (hW0 : W ≠ ⊥) :
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) :=
  centMaxProp_3d4 hQ P hP2 hPi W hW hW0

end CFSG.Quasithin
