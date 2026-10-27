module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaGen
public import CFSG.RankThree.PartTwo.Sec21.Hering214EFTrans
public import CFSG.GH74.Exceptional.LinearFourTwo
public import Certificates.Certificate799101

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open Equiv Hering214Even
open scoped commutatorElement

section F3At

variable {G G' : Type*} [Group G] [Group G']

@[expose] def F3At (K E C : Subgroup G) : Prop :=
  E ≤ ⁅K ⊓ C, K ⊓ C⁆ ∧ ∀ P : Subgroup G, IsPGroup 2 P → P ≤ ⁅K ⊓ C, K ⊓ C⁆ →
    ⁅K ⊓ C, K ⊓ C⁆ ≤ Subgroup.normalizer (P : Set G) → P = ⊥

theorem F3At.map {K E C : Subgroup G} (h : F3At K E C) (φ : G ≃* G') :
    F3At (K.map φ.toMonoidHom) (E.map φ.toMonoidHom) (C.map φ.toMonoidHom) := by
  have hD : ⁅K.map φ.toMonoidHom ⊓ C.map φ.toMonoidHom,
      K.map φ.toMonoidHom ⊓ C.map φ.toMonoidHom⁆ = ⁅K ⊓ C, K ⊓ C⁆.map φ.toMonoidHom := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.injective, Subgroup.map_commutator]
  rw [F3At, hD]
  refine ⟨Subgroup.map_mono h.1, fun P hP hPD hDN => ?_⟩
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := φ.toMonoidHom) φ.surjective P]
    at hPD hDN ⊢
  rw [Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective] at hPD
  rw [← Subgroup.map_equiv_normalizer_eq,
    Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective] at hDN
  rw [h.2 _ (hP.comap_of_injective φ.toMonoidHom φ.injective) hPD hDN, Subgroup.map_bot]

theorem map_centralizer_equiv (φ : G ≃* G') (U : Subgroup G) :
    (Subgroup.centralizer (U : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro H h hh
    have := H _ (Subgroup.mem_map_equiv.mp hh)
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact this
  · intro H h hh
    have := H (φ h) (Subgroup.mem_map_of_mem _ hh)
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this

end F3At

theorem card_e0 : Nat.card (Subgroup.closure ({a8C1, a8C2} : Set (Perm (Fin 8)))) = 9 :=
  Asc83Table.card_closure_pair_eq_nine (by decide) (by decide)
    (show a8C1 * a8C2 = a8C2 * a8C1 by decide) (by decide)
    (Asc83Table.not_mem_zpowers_of_ne (by decide) (by decide) (by decide) (by decide))

theorem exists_map_conj_eq_of_card_nine {A B : Subgroup (Perm (Fin 8))} (hA : Nat.card A = 9)
    (hB : Nat.card B = 9) : ∃ g : Perm (Fin 8), A.map (MulAut.conj g).toMonoidHom = B := by
  have hidx : ∀ H : Subgroup (Perm (Fin 8)), Nat.card H = 9 → ¬ 3 ∣ H.index := by
    intro H hH h3
    have h := Subgroup.index_mul_card (H := H)
    rw [hH, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      show Nat.factorial 8 = 4480 * 9 from rfl] at h
    have h' : H.index = 4480 := by omega
    rw [h'] at h3
    norm_num at h3
  have hp : ∀ H : Subgroup (Perm (Fin 8)), Nat.card H = 9 → IsPGroup 3 H := fun H hH =>
    IsPGroup.of_card (n := 2) (by rw [hH]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 8)) ((hp A hA).toSylow (hidx A hA))
    ((hp B hB).toSylow (hidx B hB))
  refine ⟨g, ?_⟩
  have h := congrArg (fun P : Sylow 3 (Perm (Fin 8)) => (P : Subgroup (Perm (Fin 8)))) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.pointwise_smul_def] at h
  exact h

theorem pow_128_eq_one {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P) {p : Perm (Fin 8)}
    (hp : p ∈ P) : p ^ 128 = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨p, hp⟩
  have hk' : orderOf p = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨p, hp⟩ : P)
  have hd : orderOf p ∣ 2 ^ 7 * 315 := by
    have := orderOf_dvd_natCard p
    rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      show Nat.factorial 8 = 2 ^ 7 * 315 from rfl] at this
  rw [← orderOf_dvd_iff_pow_eq_one, show (128 : ℕ) = 2 ^ 7 from rfl]
  rw [hk'] at hd ⊢
  exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 315)).dvd_of_dvd_mul_right hd

theorem mem_a8_inf_centralizer {x : Perm (Fin 8)} (h1 : Perm.sign x = 1)
    (h2 : x * a8Tau = a8Tau * x) :
    x ∈ alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau} :=
  Subgroup.mem_inf.mpr ⟨Perm.mem_alternatingGroup.mpr h1,
    Subgroup.mem_centralizer_singleton_iff.mpr h2⟩

theorem e0_le_d : Subgroup.closure {a8C1, a8C2} ≤
    ⁅alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau},
      alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau}⁆ := by
  have hx := mem_a8_inf_centralizer (x := swap 0 1 * swap 3 4) (by decide) (by decide)
  rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · have h := Subgroup.commutator_mem_commutator hx
      (mem_a8_inf_centralizer (x := swap 0 2 * swap 3 4) (by decide) (by decide))
    rwa [show ⁅swap (0 : Fin 8) 1 * swap 3 4, swap 0 2 * swap 3 4⁆ = a8C1 by decide] at h
  · have h := Subgroup.commutator_mem_commutator hx
      (mem_a8_inf_centralizer (x := swap 0 1 * swap 3 5) (by decide) (by decide))
    rwa [show ⁅swap (0 : Fin 8) 1 * swap 3 4, swap 0 1 * swap 3 5⁆ = a8C2 by decide] at h


theorem f3At_e0 : F3At (alternatingGroup (Fin 8)) (Subgroup.closure {a8C1, a8C2})
    (Subgroup.centralizer {a8Tau}) := by
  refine ⟨e0_le_d, fun P hP hPD hDN => ?_⟩
  by_contra hne
  obtain ⟨⟨p, hpP⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
  have hDle : ⁅alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau},
      alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau}⁆ ≤
      alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau} :=
    Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  obtain ⟨hpA, hpC⟩ := Subgroup.mem_inf.mp (hDle (hPD hpP))
  have hcomm : ∀ d ∈ ⁅alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau},
      alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {a8Tau}⁆, p * d * p⁻¹ * d⁻¹ ∈ P := by
    intro d hd
    have hd' := (Subgroup.mem_normalizer_iff.mp (hDN hd) p⁻¹).mp (inv_mem hpP)
    rw [show p * d * p⁻¹ * d⁻¹ = p * (d * p⁻¹ * d⁻¹) by group]
    exact mul_mem hpP hd'
  have hc1 : a8C1 ∈ Subgroup.closure ({a8C1, a8C2} : Set (Perm (Fin 8))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hc2 : a8C2 ∈ Subgroup.closure ({a8C1, a8C2} : Set (Perm (Fin 8))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rcases Certificates.certificate799101.2 p (Perm.mem_alternatingGroup.mp hpA)
    (Subgroup.mem_centralizer_singleton_iff.mp hpC) hp1' (pow_128_eq_one hP hpP) with h | h
  · exact h (pow_128_eq_one hP (hcomm _ (e0_le_d hc2)))
  · exact h (pow_128_eq_one hP (hcomm _ (e0_le_d (mul_mem hc1 hc2))))

theorem f3At_perm_eight {E U : Subgroup (Perm (Fin 8))} (hE : Nat.card E = 9)
    (hU : ∀ u ∈ U, u ^ 2 = 1) (hU1 : U ≠ ⊥) (hcomm : ∀ u ∈ U, ∀ e ∈ E, u * e = e * u) :
    F3At (alternatingGroup (Fin 8)) E (Subgroup.centralizer (U : Set (Perm (Fin 8)))) := by
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine card_e0 hE
  have hUτ : ∀ u ∈ U, u = 1 ∨ u = g * a8Tau * g⁻¹ := by
    intro u hu
    have hc : ∀ c ∈ ({a8C1, a8C2} : Set (Perm (Fin 8))),
        g⁻¹ * u * g * c = c * (g⁻¹ * u * g) := by
      intro c hc
      have hgc : g * c * g⁻¹ ∈ E := by
        rw [← hg]
        exact ⟨c, Subgroup.subset_closure hc, rfl⟩
      have h := hcomm u hu _ hgc
      calc g⁻¹ * u * g * c = g⁻¹ * (u * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * u) * g := by rw [h]
        _ = c * (g⁻¹ * u * g) := by group
    have h2 : (g⁻¹ * u * g) ^ 2 = 1 := by
      rw [show g⁻¹ * u * g = MulAut.conj g⁻¹ u by rw [MulAut.conj_apply, inv_inv], ← map_pow,
        hU u hu, map_one]
    rcases Certificates.certificate799101.1 _ (hc _ (Set.mem_insert _ _))
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h2 with h | h
    · left
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = g * a8Tau * g⁻¹ := by rw [h]
  have hC : Subgroup.centralizer (U : Set (Perm (Fin 8))) =
      (Subgroup.centralizer {a8Tau}).map (MulAut.conj g).toMonoidHom := by
    obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have hτU : g * a8Tau * g⁻¹ ∈ U := by
      rcases hUτ u₀ hu₀ with h | h
      · exact absurd (Subtype.ext h) hu₀1
      · rw [← h]
        exact hu₀
    have hτ : (Subgroup.centralizer {a8Tau}).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer {g * a8Tau * g⁻¹} := by
      ext x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
      constructor
      · intro h
        calc x * (g * a8Tau * g⁻¹) = g * ((g⁻¹ * x * g) * a8Tau) * g⁻¹ := by group
          _ = g * (a8Tau * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
          _ = g * a8Tau * g⁻¹ * x := by group
      · intro h
        calc g⁻¹ * x * g * a8Tau = g⁻¹ * (x * (g * a8Tau * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * a8Tau * g⁻¹) * x) * g := by rw [h]
          _ = a8Tau * (g⁻¹ * x * g) := by group
    rw [hτ]
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun h => (h _ hτU).symm, fun h u hu => ?_⟩
    rcases hUτ u hu with rfl | rfl
    · rw [one_mul, mul_one]
    · exact h.symm
  have hA8 : (alternatingGroup (Fin 8)).map (MulAut.conj g).toMonoidHom =
      alternatingGroup (Fin 8) :=
    Subgroup.Normal.map_conj_eq _ g
  have hF := f3At_e0.map (MulAut.conj g)
  rwa [hA8, hg, ← hC] at hF

def a8Basis : Asc83Table.E9Basis (alternatingGroup (Fin 8)) where
  a := ⟨a8C1, Perm.mem_alternatingGroup.mpr (by decide)⟩
  b := ⟨a8C2, Perm.mem_alternatingGroup.mpr (by decide)⟩
  ha := Subtype.ext (show a8C1 ^ 3 = 1 by decide)
  hb := Subtype.ext (show a8C2 ^ 3 = 1 by decide)
  hab := Subtype.ext (show a8C1 * a8C2 = a8C2 * a8C1 by decide)
  card := Asc83Table.card_closure_pair_eq_nine (Subtype.ext (show a8C1 ^ 3 = 1 by decide))
    (Subtype.ext (show a8C2 ^ 3 = 1 by decide))
    (Subtype.ext (show a8C1 * a8C2 = a8C2 * a8C1 by decide))
    (fun h => (show a8C1 ≠ 1 by decide) (congrArg Subtype.val h))
    (Asc83Table.not_mem_zpowers_of_ne (Subtype.ext (show a8C1 ^ 3 = 1 by decide))
      (fun h => (show a8C2 ≠ 1 by decide) (congrArg Subtype.val h))
      (fun h => (show a8C2 ≠ a8C1 by decide) (congrArg Subtype.val h))
      (fun h => (show a8C2 ≠ a8C1 ^ 2 by decide) (congrArg Subtype.val h)))

theorem evenThetaFacts_a8 : EvenThetaFacts ↥(alternatingGroup (Fin 8)) := by
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
    (by norm_num)
  set ψ : Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective MulAut.conjNormal hbij with hψ
  have hψc : ∀ a : alternatingGroup (Fin 8), ψ a = MulAut.conj a := fun _ =>
    MulAut.conjNormal_val
  have hInn : (alternatingGroup (Fin 8)).map ψ.toMonoidHom =
      (MulAut.conj : alternatingGroup (Fin 8) →* MulAut (alternatingGroup (Fin 8))).range := by
    ext σ
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨⟨π, hπ⟩, (hψc ⟨π, hπ⟩).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, hψc a⟩
  refine ⟨alternatingGroup.center_eq_bot (by simp), fun σ hσ => ?_,
    exists_e9_of_e9Basis a8Basis (MulEquiv.refl _), ?_⟩
  ·
    obtain ⟨π, rfl⟩ := ψ.surjective σ
    have hπ3 : π ^ 3 = 1 := ψ.injective (by rw [map_pow, hσ, map_one])
    have hsign : Perm.sign π = 1 := by
      rcases Int.units_eq_one_or (Perm.sign π) with h | h
      · exact h
      · have h3 := congrArg Perm.sign hπ3
        rw [map_pow, h, map_one] at h3
        exact absurd h3 (by decide)
    rw [← hInn]
    exact ⟨π, Perm.mem_alternatingGroup.mpr hsign, rfl⟩
  ·
    intro Ē Ū _ _ hĒ9 hŪ hŪ1 _ hcomm
    have hĒm : (Ē.comap ψ.toMonoidHom).map ψ.toMonoidHom = Ē :=
      Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective Ē
    have hŪm : (Ū.comap ψ.toMonoidHom).map ψ.toMonoidHom = Ū :=
      Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective Ū
    have hE9 : Nat.card (Ē.comap ψ.toMonoidHom) = 9 := by
      rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hĒm, hĒ9]
    have hU2 : ∀ u ∈ Ū.comap ψ.toMonoidHom, u ^ 2 = 1 := fun u hu =>
      ψ.injective (by rw [map_pow, map_one]; exact hŪ.2 (ψ u) hu)
    have hU1 : Ū.comap ψ.toMonoidHom ≠ ⊥ := fun h =>
      hŪ1 (by rw [← hŪm, h, Subgroup.map_bot])
    have hcomm' : ∀ u ∈ Ū.comap ψ.toMonoidHom, ∀ e ∈ Ē.comap ψ.toMonoidHom, u * e = e * u :=
      fun u hu e he => ψ.injective (by rw [map_mul, map_mul]; exact hcomm (ψ u) hu (ψ e) he)
    have hF := (f3At_perm_eight hE9 hU2 hU1 hcomm').map ψ
    rw [hInn, hĒm, map_centralizer_equiv, hŪm] at hF
    exact hF

theorem evenThetaFacts_of_L42 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 4 2 1) :
    EvenThetaFacts X := by
  obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
    (Or.inl ⟨by decide, h⟩)
  exact evenThetaFacts_of_mulEquiv e evenThetaFacts_a8

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
