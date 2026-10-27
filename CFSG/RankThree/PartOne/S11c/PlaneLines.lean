module

public import CFSG.RankThree.PartOne.KS.Lines
public import CFSG.RankThree.PartOne.S11c.PlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG

theorem twoPart_le_of_lines_cent {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (hPR : P ≤ R) {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i))) {k : ℕ}
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, centralizer ({xs j} : Set M) =
        centralizer ({g * xs i * g⁻¹} : Set M)) ∧
      ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({xs i} : Set M) →
        Nat.card R2 ≤ k) :
    ∀ y ∈ P, orderOf y = p → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
      R2 ≤ R ⊓ centralizer ({y} : Set M) → Nat.card R2 ≤ k := by
  intro y hyP hord R2 hR2 hle
  obtain ⟨g, hgP, j, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  obtain ⟨i, ⟨g', hg'R, hg'⟩, hgood⟩ := hrep j
  have hcR : g * g' ∈ R := R.mul_mem (hPR hgP) hg'R
  let R3 : Subgroup M := R2.map (MulAut.conj (g * g')⁻¹).toMonoidHom
  have hR3le : R3 ≤ R ⊓ centralizer ({xs i} : Set M) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrR, hrC⟩ := hle hr
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · show (g * g')⁻¹ * r * (g * g')⁻¹⁻¹ ∈ R
      exact R.mul_mem (R.mul_mem (R.inv_mem hcR) hrR) (by simpa using hcR)
    · have hrC' : r ∈ centralizer ({y} : Set M) := hrC
      have hyr : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.mp hrC'
      have h1 : (g⁻¹ * r * g) ∈ centralizer ({g⁻¹ * y * g} : Set M) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g⁻¹ * r * g) * (g⁻¹ * y * g) = g⁻¹ * (r * y) * g := by group
          _ = g⁻¹ * (y * r) * g := by rw [hyr]
          _ = (g⁻¹ * y * g) * (g⁻¹ * r * g) := by group
      rw [hcent, hg', Subgroup.mem_centralizer_singleton_iff] at h1
      show ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹) * xs i = xs i * ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹)
      calc ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹) * xs i
          = g'⁻¹ * ((g⁻¹ * r * g) * (g' * xs i * g'⁻¹)) * g' := by group
        _ = g'⁻¹ * ((g' * xs i * g'⁻¹) * (g⁻¹ * r * g)) * g' := by rw [h1]
        _ = xs i * ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹) := by group
  have hcard : Nat.card R3 = Nat.card R2 :=
    Subgroup.card_map_of_injective (MulAut.conj (g * g')⁻¹).injective
  have h2 : IsPGroup 2 R3 := hR2.map (MulAut.conj (g * g')⁻¹).toMonoidHom
  rw [← hcard]
  exact hgood R3 h2 hR3le

theorem twoPart_le_of_lines {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (hPR : P ≤ R) {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i))) {k : ℕ}
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({xs i} : Set M) →
        Nat.card R2 ≤ k) :
    ∀ y ∈ P, orderOf y = p → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
      R2 ≤ R ⊓ centralizer ({y} : Set M) → Nat.card R2 ≤ k := by
  refine twoPart_le_of_lines_cent hp hPR hSyl hlines (fun j => ?_)
  obtain ⟨i, ⟨g, hg, hgj⟩, hgood⟩ := hrep j
  exact ⟨i, ⟨g, hg, by rw [hgj]⟩, hgood⟩

theorem planeRBoundMove_of_lines {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (hPR : P ≤ R) {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i))) {k : ℕ}
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      ∀ f ∈ R, orderOf f = p → f * xs i = xs i * f → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
        R2 ≤ R ⊓ centralizer ({xs i} : Set M) → (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) →
        (∃ r ∈ R2, f * r * f⁻¹ ≠ r) → Nat.card R2 ≤ k) :
    ∀ y ∈ P, orderOf y = p → ∀ f ∈ P, orderOf f = p → f * y = y * f →
      ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({y} : Set M) →
        (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) → Nat.card R2 ≤ k := by
  intro y hyP hord f hfP hford hfy R2 hR2 hle hfR2 hmove
  obtain ⟨g, hgP, j, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  obtain ⟨i, ⟨g', hg'R, hg'⟩, hgood⟩ := hrep j
  have hcR : g * g' ∈ R := R.mul_mem (hPR hgP) hg'R
  have hcR' : (g * g')⁻¹ ∈ R := R.inv_mem hcR
  let φ : MulAut M := MulAut.conj (g * g')⁻¹
  have hφ : ∀ x : M, φ x = (g * g')⁻¹ * x * (g * g') := fun x => by
    rw [show φ x = (g * g')⁻¹ * x * ((g * g')⁻¹)⁻¹ from MulAut.conj_apply _ _]
    group
  have key : ∀ c : M, c * y = y * c → φ c * xs i = xs i * φ c := fun c hc => by
    have h1 : (g⁻¹ * c * g) ∈ centralizer ({g⁻¹ * y * g} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g⁻¹ * c * g) * (g⁻¹ * y * g) = g⁻¹ * (c * y) * g := by group
        _ = g⁻¹ * (y * c) * g := by rw [hc]
        _ = (g⁻¹ * y * g) * (g⁻¹ * c * g) := by group
    rw [hcent, Subgroup.mem_centralizer_singleton_iff, ← hg'] at h1
    rw [hφ]
    calc (g * g')⁻¹ * c * (g * g') * xs i
        = g'⁻¹ * ((g⁻¹ * c * g) * (g' * xs i * g'⁻¹)) * g' := by group
      _ = g'⁻¹ * ((g' * xs i * g'⁻¹) * (g⁻¹ * c * g)) * g' := by rw [h1]
      _ = xs i * ((g * g')⁻¹ * c * (g * g')) := by group
  let R3 : Subgroup M := R2.map φ.toMonoidHom
  have hR3le : R3 ≤ R ⊓ centralizer ({xs i} : Set M) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrR, hrC⟩ := hle hr
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr
      (key r (Subgroup.mem_centralizer_singleton_iff.mp hrC))⟩
    show φ r ∈ R
    rw [hφ]
    exact R.mul_mem (R.mul_mem hcR' hrR) hcR
  have hf3R : φ f ∈ R := by
    rw [hφ]
    exact R.mul_mem (R.mul_mem hcR' (hPR hfP)) hcR
  have hf3ord : orderOf (φ f) = p := (MulEquiv.orderOf_eq φ f).trans hford
  have hf3comm : φ f * xs i = xs i * φ f := key f hfy
  have hnorm : ∀ r ∈ R3, φ f * r * (φ f)⁻¹ ∈ R3 := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨f * r * f⁻¹, hfR2 r hr, ?_⟩
    show φ (f * r * f⁻¹) = φ f * φ r * (φ f)⁻¹
    simp [map_mul, map_inv]
  have hmove3 : ∃ r ∈ R3, φ f * r * (φ f)⁻¹ ≠ r := by
    obtain ⟨r, hr, hne⟩ := hmove
    refine ⟨φ r, ⟨r, hr, rfl⟩, fun h => hne (φ.injective ?_)⟩
    have : φ (f * r * f⁻¹) = φ f * φ r * (φ f)⁻¹ := by simp [map_mul, map_inv]
    rw [this]
    exact h
  have hcard : Nat.card R3 = Nat.card R2 := Subgroup.card_map_of_injective φ.injective
  rw [← hcard]
  exact hgood (φ f) hf3R hf3ord hf3comm R3 (hR2.map φ.toMonoidHom) hR3le hnorm hmove3

theorem centralizerTwoPartLe_of_native {T : Type} {M : Type*} [Group T] [Group M] (φ : T →* M)
    (hφ : Function.Injective φ) {P R : Subgroup M} (hφP : ∀ t, φ t ∈ P) (hPR : P ≤ R) {p k : ℕ}
    (hb : ∀ y ∈ P, orderOf y = p → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
      R2 ≤ R ⊓ centralizer ({y} : Set M) → Nat.card R2 ≤ k) :
    CentralizerTwoPartLe T p k := by
  intro b hb' R' hR' hRC
  have hord : orderOf (φ b) = p := by rw [orderOf_injective φ hφ b, hb']
  have hle : R'.map φ ≤ R ⊓ centralizer ({φ b} : Set M) := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨hPR (hφP r), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
    rw [← map_mul, ← map_mul, this]
  have h := hb (φ b) (hφP b) hord (R'.map φ) (hR'.map φ) hle
  rwa [Subgroup.card_map_of_injective hφ] at h

theorem planeRBoundMove_of_native_abel {T : Type} {M : Type*} [Group T] [Group M] (φ : T →* M)
    (hφ : Function.Injective φ) {P R : Subgroup M} (hφP : ∀ t, φ t ∈ P) (hPR : P ≤ R) {p k : ℕ}
    (hb : ∀ y ∈ P, orderOf y = p → ∀ f ∈ P, orderOf f = p → f * y = y * f →
      ∀ R2 : Subgroup M, IsPGroup 2 R2 → R2 ≤ R ⊓ centralizer ({y} : Set M) →
        (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) →
        (p = 7 → Nat.card R2 = 8 → IsElementaryAbelian 2 R2) → Nat.card R2 ≤ k) :
    PlaneRBoundMove T p k := by
  intro b f hbo hfo hbf _ R' hR' hRC hfR' hmove hel
  have hbord : orderOf (φ b) = p := by rw [orderOf_injective φ hφ b, hbo]
  have hford : orderOf (φ f) = p := by rw [orderOf_injective φ hφ f, hfo]
  have hcomm : φ f * φ b = φ b * φ f := by rw [← map_mul, ← map_mul, ← hbf]
  have hle : R'.map φ ≤ R ⊓ centralizer ({φ b} : Set M) := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨hPR (hφP r), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
    rw [← map_mul, ← map_mul, this]
  have hnorm : ∀ r ∈ R'.map φ, φ f * r * (φ f)⁻¹ ∈ R'.map φ := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨f * r * f⁻¹, hfR' r hr, by simp [map_mul, map_inv]⟩
  have hmove' : ∃ r ∈ R'.map φ, φ f * r * (φ f)⁻¹ ≠ r := by
    obtain ⟨r, hr, hne⟩ := hmove
    refine ⟨φ r, ⟨r, hr, rfl⟩, fun h => hne (hφ ?_)⟩
    have : φ (f * r * f⁻¹) = φ f * φ r * (φ f)⁻¹ := by simp [map_mul, map_inv]
    rw [this]
    exact h
  have hcard : Nat.card (R'.map φ) = Nat.card R' := Subgroup.card_map_of_injective hφ
  have hel' : p = 7 → Nat.card (R'.map φ) = 8 → IsElementaryAbelian 2 (R'.map φ) := by
    intro hp7 h8
    have : IsElementaryAbelian 2 R' := hel hp7 (hcard ▸ h8)
    exact IsElementaryAbelian.map φ
  have h := hb (φ b) (hφP b) hbord (φ f) (hφP f) hford hcomm (R'.map φ) (hR'.map φ) hle hnorm
    hmove' hel'
  rwa [hcard] at h

end CFSG.RankThree.PartOne
