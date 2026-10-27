module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessU
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Tori

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Open (pCoreOf)

variable {X : Type} [Group X] [Finite X]

section General

theorem map_pCoreOf_mulAut (p : ℕ) (φ : MulAut X) (H : Subgroup X) :
    (pCoreOf p H).map φ.toMonoidHom = pCoreOf p (H.map φ.toMonoidHom) := by
  have hpc : (CFSG.pCore p ↥H).map (φ.subgroupMap H).toMonoidHom =
      CFSG.pCore p ↥(H.map φ.toMonoidHom) := CFSG.pCore_map_iso p _
  unfold pCoreOf
  erw [← hpc, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_conj_centralizer_singleton (n b : X) :
    (Subgroup.centralizer ({b} : Set X)).map (MulAut.conj n).toMonoidHom =
      Subgroup.centralizer ({n * b * n⁻¹} : Set X) := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g * (n * b * n⁻¹) = n * (n⁻¹ * g * n * b) * n⁻¹ := by group
      _ = n * (b * (n⁻¹ * g * n)) * n⁻¹ := by rw [h]
      _ = n * b * n⁻¹ * g := by group
  · intro h
    calc n⁻¹ * g * n * b = n⁻¹ * (g * (n * b * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * b * n⁻¹ * g) * n := by rw [h]
      _ = b * (n⁻¹ * g * n) := by group

theorem centralizer_singleton_eq_of_zpowers_eq {y y' : X}
    (h : Subgroup.zpowers y = Subgroup.zpowers y') :
    Subgroup.centralizer ({y} : Set X) = Subgroup.centralizer ({y'} : Set X) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, h,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem map_conj_hessU (n b : X) :
    (pCoreOf 2 (Subgroup.centralizer ({b} : Set X))).map (MulAut.conj n).toMonoidHom =
      pCoreOf 2 (Subgroup.centralizer ({n * b * n⁻¹} : Set X)) := by
  rw [map_pCoreOf_mulAut, map_conj_centralizer_singleton]

theorem map_conj_hessU_of_map_zpowers {n x x' : X}
    (h : (Subgroup.zpowers x).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers x') :
    (pCoreOf 2 (Subgroup.centralizer ({x} : Set X))).map (MulAut.conj n).toMonoidHom =
      pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)) := by
  rw [map_conj_hessU, centralizer_singleton_eq_of_zpowers_eq]
  rw [← h, MonoidHom.map_zpowers]
  rfl

end General

section Hessian

variable {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp2 : p ≠ 2) (hiso : Sec4.IsoLThreePi X p e)
  {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
  (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
    ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
include he hp2 hiso hEe hE9 htr

theorem hessU_one_eq_bot : pCoreOf 2 (Subgroup.centralizer ({1} : Set X)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCoreOf 2 (Subgroup.centralizer ({1} : Set X)) with hN
  have hconj : ∀ w : X, N.map (MulAut.conj w).toMonoidHom = N := by
    intro w
    rw [hN, map_conj_hessU, mul_one, mul_inv_cancel]
  have hmem : ∀ w h : X, h ∈ N → w * h * w⁻¹ ∈ N := fun w h hh => by
    rw [← hconj w]
    exact Subgroup.mem_map_of_mem _ hh
  have hN2 : IsPGroup 2 N :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({1} : Set X)))).map _
  have hEN : E ≤ Subgroup.normalizer (N : Set X) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨hmem g h, fun hh => by simpa [mul_assoc] using hmem g⁻¹ _ hh⟩
  obtain ⟨b, hbE, hb1, hNb⟩ := hessU_exists he hp2 hiso hEe hE9 htr hN2 hEN
  obtain ⟨c, hcE, hcb⟩ := exists_mem_not_mem_zpowers_of_hessian he hp2 hiso hEe hE9 htr hbE
  have hc1 : c ≠ 1 := fun h => hcb (h ▸ Subgroup.one_mem _)
  obtain ⟨w, -, hwc⟩ := htr b hbE hb1 c hcE hc1
  have hNc : N ≤ Subgroup.centralizer ({c} : Set X) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj w).toMonoidHom) hNb
    rw [hconj, map_conj_hessU, hwc] at h1
    exact h1.trans (Subgroup.map_subtype_le _)
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  refine hessU_fixed he hp2 hiso hEe hE9 htr hbE hb1 hcE hcb u (hNb hu) ?_
  have huc := Subgroup.mem_centralizer_singleton_iff.mp (hNc hu)
  calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [huc]
    _ = u := by group

theorem kl3HessTori_one :
    ∀ W : Subgroup X, IsPGroup 2 W → E ≤ Subgroup.normalizer (W : Set X) → W ≠ ⊥ →
      ∃ x ∈ E, W ≤ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) := by
  intro W hW2 hEW _
  obtain ⟨b, hbE, -, hb⟩ := hessU_exists he hp2 hiso hEe hE9 htr hW2 hEW
  exact ⟨b, hbE, hb⟩

theorem kl3HessTori_two_of_core
    (hcore : ∀ b (hbE : b ∈ E) (hb1 : b ≠ 1) b' (hb'E : b' ∈ E) (hb'1 : b' ≠ 1),
      Subgroup.zpowers b ≠ Subgroup.zpowers b' →
        ∃ n ∈ (layer (pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
                (hessU_comm he hp2 hiso hEe hE9 htr hbE hb1) 1 ⊔
              layer (pCoreOf 2 (Subgroup.centralizer ({b'} : Set X)))
                (hessU_comm he hp2 hiso hEe hE9 htr hb'E hb'1) 1) ⊓
            Subgroup.normalizer (E : Set X),
          (Subgroup.zpowers b).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers b') :
    ∀ x ∈ E, ∀ x' ∈ E, ∀ W W' : Subgroup X, W ≠ ⊥ → W' ≠ ⊥ →
      W ≤ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) →
      W' ≤ pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)) →
      E ≤ Subgroup.normalizer (W : Set X) → E ≤ Subgroup.normalizer (W' : Set X) →
      ∃ n ∈ (W ⊔ W') ⊓ Subgroup.normalizer (E : Set X),
        (pCoreOf 2 (Subgroup.centralizer ({x} : Set X))).map (MulAut.conj n).toMonoidHom =
          pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)) := by
  intro x hxE x' hx'E W W' hW hW' hWU hW'U hEW hEW'
  have hU1 := hessU_one_eq_bot he hp2 hiso hEe hE9 htr
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hW (eq_bot_iff.mpr (hWU.trans hU1.le))
  have hx'1 : x' ≠ 1 := by
    rintro rfl
    exact hW' (eq_bot_iff.mpr (hW'U.trans hU1.le))
  by_cases hxx : Subgroup.zpowers x = Subgroup.zpowers x'
  · refine ⟨1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, ?_⟩
    rw [map_conj_hessU, one_mul, inv_one, mul_one, centralizer_singleton_eq_of_zpowers_eq hxx]
  · obtain ⟨n, ⟨hnV, hnN⟩, hmap⟩ := hcore x hxE hx1 x' hx'E hx'1 hxx
    refine ⟨n, ⟨sup_le_sup (hessU_layer_one_le he hp2 hiso hEe hE9 htr hxE hx1 hWU hEW hW)
      (hessU_layer_one_le he hp2 hiso hEe hE9 htr hx'E hx'1 hW'U hEW' hW') hnV, hnN⟩, ?_⟩
    exact map_conj_hessU_of_map_zpowers hmap

end Hessian

theorem kl3HessTori_of_core
    (hcore : ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
      (hp2 : p ≠ 2) (hiso : Sec4.IsoLThreePi X p e) (E : Subgroup X)
      (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
      (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
      (b : X) (hbE : b ∈ E) (hb1 : b ≠ 1) (b' : X) (hb'E : b' ∈ E) (hb'1 : b' ≠ 1),
      Subgroup.zpowers b ≠ Subgroup.zpowers b' →
        ∃ n ∈ (layer (pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
                (hessU_comm he hp2 hiso hEe hE9 htr hbE hb1) 1 ⊔
              layer (pCoreOf 2 (Subgroup.centralizer ({b'} : Set X)))
                (hessU_comm he hp2 hiso hEe hE9 htr hb'E hb'1) 1) ⊓
            Subgroup.normalizer (E : Set X),
          (Subgroup.zpowers b).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers b') :
    Sec14.KL3HessTori := by
  intro X _ _ p f _ hp2 hf hiso E hEe hE9 htr
  exact ⟨kl3HessTori_one hf hp2 hiso hEe hE9 htr,
    kl3HessTori_two_of_core hf hp2 hiso hEe hE9 htr (hcore X p f hf hp2 hiso E hEe hE9 htr)⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
