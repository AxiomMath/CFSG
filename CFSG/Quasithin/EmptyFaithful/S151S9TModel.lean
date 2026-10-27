module

public import CFSG.Quasithin.EmptyFaithful.S151S9TCore
public import CFSG.Quasithin.Background.E2TwoProofSporGen

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Idx3Model (Γ : Type) [Group Γ] [Finite Γ] (S₀ P₀ : Subgroup Γ) : Prop :=
  IsSylowTwoOf S₀ ⊤ ∧ S₀ ≤ P₀ ∧ Nat.card ↥P₀ = 3 * Nat.card ↥S₀ ∧
  (∃ z₀ : Γ, orderOf z₀ = 2 ∧ centerOf S₀ = Subgroup.zpowers z₀ ∧
    ¬ P₀ ≤ Subgroup.centralizer ({z₀} : Set Γ)) ∧
  (∃ x₀ ∈ P₀, orderOf x₀ = 3 ∧ ∃ r : Fin 5 → Γ, (∀ i, r i ∈ S₀) ∧ (∀ i, x₀⁻¹ * r i * x₀ ∈ S₀) ∧
    (∀ i, x₀ * r i * x₀⁻¹ ∈ S₀) ∧ Function.Injective fun i => ⁅⁅r i, x₀⁆, x₀⁆) ∧
  (∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ → P₀.map α.toMonoidHom = P₀)

@[expose] def Idx3Data (Γ : Type) [Group Γ] [Finite Γ] (S₀ P₀ : Subgroup Γ) : Prop :=
  IsSylowTwoOf S₀ ⊤ ∧ S₀ ≤ P₀ ∧ Nat.card ↥P₀ = 3 * Nat.card ↥S₀ ∧
  (∃ z₀ : Γ, orderOf z₀ = 2 ∧ centerOf S₀ = Subgroup.zpowers z₀ ∧
    ¬ P₀ ≤ Subgroup.centralizer ({z₀} : Set Γ)) ∧
  (∃ x₀ ∈ P₀, orderOf x₀ = 3 ∧ ∃ r : Fin 5 → Γ, (∀ i, r i ∈ S₀) ∧ (∀ i, x₀⁻¹ * r i * x₀ ∈ S₀) ∧
    (∀ i, x₀ * r i * x₀⁻¹ ∈ S₀) ∧ Function.Injective fun i => ⁅⁅r i, x₀⁆, x₀⁆)

theorem Idx3Model.data {Γ : Type} [Group Γ] [Finite Γ] {S₀ P₀ : Subgroup Γ}
    (h : Idx3Model Γ S₀ P₀) : Idx3Data Γ S₀ P₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem Idx3Model.inv {Γ : Type} [Group Γ] [Finite Γ] {S₀ P₀ : Subgroup Γ}
    (h : Idx3Model Γ S₀ P₀) :
    ∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ → P₀.map α.toMonoidHom = P₀ :=
  h.2.2.2.2.2

section Pull

variable {G : Type} [Group G] {L : Subgroup G} {Γ : Type} [Group Γ]

@[expose] def pullG (e : ↥L ≃* Γ) (P₀ : Subgroup Γ) : Subgroup G :=
  (P₀.map e.symm.toMonoidHom).map L.subtype

@[expose] noncomputable def autN (e : ↥L ≃* Γ) (t : G) (ht : t ∈ Subgroup.normalizer (L : Set G)) :
    MulAut Γ :=
  e.symm.trans ((L.normalizerMonoidHom ⟨t, ht⟩).trans e)

theorem pullG_injective (e : ↥L ≃* Γ) : Function.Injective (pullG e) :=
  E2P.pull_injective e

theorem coe_symm_autN (e : ↥L ≃* Γ) {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G)) (c : Γ) :
    ((e.symm (autN e t ht c) : ↥L) : G) = t * ((e.symm c : ↥L) : G) * t⁻¹ := by
  simp [autN]

theorem map_conj_pullG (e : ↥L ≃* Γ) {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (X : Subgroup Γ) :
    (pullG e X).map (MulAut.conj t).toMonoidHom = pullG e (X.map (autN e t ht).toMonoidHom) := by
  unfold pullG
  simp only [Subgroup.map_map]
  congr 1
  ext c
  simp [coe_symm_autN e ht c]

theorem mem_normalizer_pullG_iff (e : ↥L ≃* Γ) {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (X : Subgroup Γ) :
    t ∈ Subgroup.normalizer ((pullG e X : Subgroup G) : Set G) ↔
      X.map (autN e t ht).toMonoidHom = X := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (pullG e X).map (MulAut.conj t).toMonoidHom = pullG e X ↔ _
  rw [map_conj_pullG e ht X]
  exact (pullG_injective e).eq_iff

theorem normalizes_pullG_of_inv (e : ↥L ≃* Γ) {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    {X : Subgroup Γ} (h : X.map (autN e t ht).toMonoidHom = X) :
    t ∈ Subgroup.normalizer ((pullG e X : Subgroup G) : Set G) :=
  (mem_normalizer_pullG_iff e ht X).mpr h

theorem map_autN_eq_of_mem {S : Subgroup G} (e : ↥L ≃* Γ) {S₀ : Subgroup Γ}
    (he : ((S ⊓ L).subgroupOf L).map e.toMonoidHom = S₀) {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (htS : t ∈ S) :
    S₀.map (autN e t ht).toMonoidHom = S₀ := by
  have hS : pullG e S₀ = S ⊓ L := by
    rw [← he]
    exact E2P.pull_map e inf_le_right
  rw [← mem_normalizer_pullG_iff e ht S₀, hS]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htS, ht⟩

end Pull

section Centre

variable {Γ : Type} [Group Γ]

theorem eq_of_mem_centerOf_of_orderOf_two {S₀ : Subgroup Γ} {z₀ w : Γ} (hz₀ : orderOf z₀ = 2)
    (hc : centerOf S₀ = Subgroup.zpowers z₀) (hw : w ∈ centerOf S₀) (hw1 : w ≠ 1) : w = z₀ := by
  rw [hc] at hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← zpow_mod_orderOf, hz₀] at hw1 ⊢
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · rw [h, zpow_zero] at hw1
    exact absurd rfl hw1
  · rw [h, zpow_one]

theorem conj_mem_centerOf_of_mem_normalizer {S₀ : Subgroup Γ} {p w : Γ}
    (hp : p ∈ Subgroup.normalizer (S₀ : Set Γ)) (hw : w ∈ centerOf S₀) :
    p * w * p⁻¹ ∈ centerOf S₀ := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hp w).mp hw.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro s hs
  have hs' : p⁻¹ * s * p ∈ S₀ := (Subgroup.mem_normalizer_iff''.mp hp s).mp hs
  have key := Subgroup.mem_centralizer_iff.mp hw.2 _ hs'
  calc s * (p * w * p⁻¹) = p * ((p⁻¹ * s * p) * w) * p⁻¹ := by group
    _ = p * (w * (p⁻¹ * s * p)) * p⁻¹ := by rw [key]
    _ = p * w * p⁻¹ * s := by group

theorem le_centralizer_of_le_normalizer_of_centerOf_eq {S₀ P₀ : Subgroup Γ} {z₀ : Γ}
    (hz₀ : orderOf z₀ = 2) (hc : centerOf S₀ = Subgroup.zpowers z₀)
    (hN : P₀ ≤ Subgroup.normalizer (S₀ : Set Γ)) :
    P₀ ≤ Subgroup.centralizer ({z₀} : Set Γ) := by
  intro p hp
  have hz : z₀ ∈ centerOf S₀ := hc ▸ Subgroup.mem_zpowers z₀
  have hz1 : z₀ ≠ 1 := fun h => by simp [h] at hz₀
  have h1 := conj_mem_centerOf_of_mem_normalizer (hN hp) hz
  have h2 : p * z₀ * p⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
  have h3 := eq_of_mem_centerOf_of_orderOf_two hz₀ hc h1 h2
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

theorem mem_centerOf_map_iff_of_injective {G : Type} [Group G] {ι : Γ →* G}
    (hι : Function.Injective ι) {S₀ : Subgroup Γ} {c : Γ} :
    ι c ∈ centerOf (S₀.map ι) ↔ c ∈ centerOf S₀ := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(Subgroup.mem_map_iff_mem hι).mp h1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp h2 (ι s) (Subgroup.mem_map_of_mem ι hs)
    exact hι (by simpa using this)
  · rintro ⟨h1, h2⟩
    refine ⟨Subgroup.mem_map_of_mem ι h1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    obtain ⟨s', hs', rfl⟩ := hs
    have := Subgroup.mem_centralizer_iff.mp h2 s' hs'
    simpa using congrArg ι this

end Centre

theorem threeD_of_pull {G : Type} [Group G] [Finite G] {L S : Subgroup G} {z : G}
    (hS2 : IsPGroup 2 ↥S) (hz : z ∈ centerOf (S ⊓ L))
    (hnc : ¬ L ≤ Subgroup.centralizer ({z} : Set G))
    {Γ : Type} [Group Γ] [Finite Γ] (e : ↥L ≃* Γ) {S₀ P₀ : Subgroup Γ}
    (he : ((S ⊓ L).subgroupOf L).map e.toMonoidHom = S₀) (hM : Idx3Data Γ S₀ P₀)
    (hinv : S ≤ Subgroup.normalizer ((pullG e P₀ : Subgroup G) : Set G)) :
    pullG e P₀ ≤ L ∧ S ⊓ L ≤ pullG e P₀ ∧
      S ≤ Subgroup.normalizer ((pullG e P₀ : Subgroup G) : Set G) ∧
      ¬ pullG e P₀ ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo (pullG e P₀) ∧
      IsMinParabolicOf (pullG e P₀ ⊔ S) (pullG e P₀ ⊔ S) ∧ NumC126 (pullG e P₀ ⊔ S) ∧
      oPrimeResidualOf 3 (pullG e P₀) ⊔ (S ⊓ L) = pullG e P₀ := by
  obtain ⟨-, hSP₀, hcard₀, ⟨z₀, hz₀o, hz₀c, hz₀nc⟩,
    ⟨x₀, hx₀P, hx₀o, r, hr0, hr1, hr2, hrinj⟩⟩ := hM
  set ι : Γ →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hpull : ∀ X : Subgroup Γ, pullG e X = X.map ι := fun X => Subgroup.map_map _ _ _
  have hSι : S₀.map ι = S ⊓ L := by
    rw [← hpull, ← he]
    exact E2P.pull_map e inf_le_right
  have hmemS : ∀ c ∈ S₀, ι c ∈ S ⊓ L := fun c hc => by
    rw [← hSι]
    exact Subgroup.mem_map_of_mem ι hc
  have hmemP : ∀ c ∈ P₀, ι c ∈ pullG e P₀ := fun c hc => by
    rw [hpull]
    exact Subgroup.mem_map_of_mem ι hc
  have hPL : pullG e P₀ ≤ L := E2P.pull_le e P₀
  have hBP : S ⊓ L ≤ pullG e P₀ := by
    rw [← hSι, hpull]
    exact Subgroup.map_mono hSP₀
  have hcard : Nat.card ↥(pullG e P₀) = 3 * Nat.card ↥(S ⊓ L) := by
    rw [hpull, ← hSι, Subgroup.card_map_of_injective hι, Subgroup.card_map_of_injective hι]
    exact hcard₀
  obtain ⟨w, rfl⟩ : ∃ w : Γ, ι w = z := ⟨e ⟨z, hz.1.2⟩, by simp [ι]⟩
  have hz1 : ι w ≠ 1 := by
    intro h
    apply hnc
    rw [h]
    intro l _
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      simp
  have hw1 : w ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hwc : w ∈ centerOf S₀ := by
    rw [← hSι] at hz
    exact (mem_centerOf_map_iff_of_injective hι).mp hz
  have hwz₀ : w = z₀ := eq_of_mem_centerOf_of_orderOf_two hz₀o hz₀c hwc hw1
  have hPz : ¬ pullG e P₀ ≤ Subgroup.centralizer ({ι w} : Set G) := by
    intro hP
    apply hz₀nc
    intro c hc
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    have h1 := Subgroup.mem_centralizer_iff.mp (hP (hmemP c hc)) (ι w) rfl
    rw [hy, ← hwz₀]
    exact hι (by rw [map_mul, map_mul]; exact h1)
  have hnN : ¬ pullG e P₀ ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro hP
    apply hz₀nc
    refine le_centralizer_of_le_normalizer_of_centerOf_eq hz₀o hz₀c fun c hc => ?_
    have h1 := hP (hmemP c hc)
    rw [← hSι] at h1
    exact (E2P.mem_normalizer_map_iff_of_injective hι).mp h1
  have hr0' : ∀ i, ι (r i) ∈ S ⊓ L := fun i => hmemS _ (hr0 i)
  have hr1' : ∀ i, (ι x₀)⁻¹ * ι (r i) * ι x₀ ∈ S ⊓ L := fun i => by
    have := hmemS _ (hr1 i)
    rwa [map_mul, map_mul, map_inv] at this
  have hr2' : ∀ i, ι x₀ * ι (r i) * (ι x₀)⁻¹ ∈ S ⊓ L := fun i => by
    have := hmemS _ (hr2 i)
    rwa [map_mul, map_mul, map_inv] at this
  have hinj : Function.Injective fun i => ⁅⁅ι (r i), ι x₀⁆, ι x₀⁆ := by
    intro i j h
    apply hrinj
    apply hι
    simpa only [map_commutatorElement] using h
  obtain ⟨hchar, hmin, hnum, hoP⟩ := idx3_core (x₀ := ι x₀) (r := fun i => ι (r i)) hS2 hPL hBP
    hinv hcard hnN (hmemP x₀ hx₀P) (by rw [orderOf_injective ι hι, hx₀o]) hr0' hr1' hr2' hinj
  exact ⟨hPL, hBP, hinv, hPz, hchar, hmin, hnum, hoP⟩

theorem threeD_of_idx3Model {G : Type} [Group G] [Finite G] {L S : Subgroup G} {z : G}
    (hS2 : IsPGroup 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSyl : IsSylowTwoOf (S ⊓ L) L) (hz : z ∈ centerOf (S ⊓ L))
    (hnc : ¬ L ≤ Subgroup.centralizer ({z} : Set G))
    {Γ : Type} [Group Γ] [Finite Γ] (e₀ : ↥L ≃* Γ) {S₀ P₀ : Subgroup Γ}
    (hM : Idx3Model Γ S₀ P₀) :
    ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
      IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
      oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  obtain ⟨e, he⟩ := E2P.SporB.exists_equiv_sylow e₀ hSyl hM.1
  have hSP : S ≤ Subgroup.normalizer ((pullG e P₀ : Subgroup G) : Set G) := fun t ht =>
    normalizes_pullG_of_inv e (hSN ht)
      (hM.inv _ (map_autN_eq_of_mem e he (hSN ht) ht))
  exact ⟨pullG e P₀, threeD_of_pull hS2 hz hnc e he hM.data hSP⟩

end CFSG.Quasithin.S151S9T
