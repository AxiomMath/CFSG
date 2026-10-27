module

public import CFSG.Permutation.FixingGeneration
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

public section

namespace CFSG.Permutation.DeletionChart

open Equiv
open CFSG.Permutation.FixingGeneration

variable {X H I : Type*} [Group X] [Group H] [DecidableEq I]

theorem conj_mem_pair {ρ : Equiv.Perm I →* X} {P : I → I → Subgroup X}
    (hequiv : ∀ (σ : Equiv.Perm I) (i j : I),
      (P i j).map (MulAut.conj (ρ σ)).toMonoidHom = P (σ i) (σ j))
    (σ : Equiv.Perm I) {i j : I} (x : P i j) :
    ρ σ * (x : X) * (ρ σ)⁻¹ ∈ P (σ i) (σ j) := by
  rw [← hequiv σ i j]
  exact Subgroup.mem_map_of_mem (MulAut.conj (ρ σ)).toMonoidHom x.2

theorem centralizer_of_fixing_pair
    {A : Subgroup X} (ρ : Equiv.Perm I →* X) (a : A →* H) (t : Equiv.Perm I →* H)
    {P : Subgroup X} (hPA : P ≤ A)
    {u v c d : I}
    (hcu : c ≠ u) (hcv : c ≠ v) (hdu : d ≠ u) (hdv : d ≠ v) (hcd : c ≠ d)
    (hcommon : ∀ σ : Equiv.Perm I, σ d = d → ∃ h : ρ σ ∈ A, a ⟨ρ σ, h⟩ = t σ)
    (hfix3 : ∀ (σ : Equiv.Perm I) (x : P), σ u = u → σ v = v → σ d = d →
      ρ σ * (x : X) = (x : X) * ρ σ)
    (hswap : ∀ x : P,
      t (Equiv.swap c d) * a (Subgroup.inclusion hPA x) =
        a (Subgroup.inclusion hPA x) * t (Equiv.swap c d)) :
    ∀ (σ : Equiv.Perm I), σ u = u → σ v = v → ∀ x : P,
      t σ * a (Subgroup.inclusion hPA x) =
        a (Subgroup.inclusion hPA x) * t σ := by
  intro σ hσu hσv x
  have hcS : c ∉ ({u, v} : Set I) := by simp [hcu, hcv]
  have hdS : d ∉ ({u, v} : Set I) := by simp [hdu, hdv]
  have hσmem : σ ∈ fixingSubgroup (Equiv.Perm I) ({u, v} : Set I) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rcases hy with rfl | rfl
    · simpa using hσu
    · simpa using hσv
  have hfix_le : fixingSubgroup (Equiv.Perm I) ({u, v} : Set I) ≤
      (Subgroup.centralizer ({a (Subgroup.inclusion hPA x)} : Set H)).comap t := by
    rw [fixingSubgroup_eq_sup_insert_zpowers_swap ({u, v} : Set I) hcS hdS hcd]
    refine sup_le ?_ ?_
    · intro τ hτ
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      have hτu : τ u = u := by
        simpa using (mem_fixingSubgroup_iff (Equiv.Perm I)).mp hτ u (by simp)
      have hτv : τ v = v := by
        simpa using (mem_fixingSubgroup_iff (Equiv.Perm I)).mp hτ v (by simp)
      have hτd : τ d = d := by
        simpa using (mem_fixingSubgroup_iff (Equiv.Perm I)).mp hτ d (by simp)
      obtain ⟨hτA, hτa⟩ := hcommon τ hτd
      have hcommA : (⟨ρ τ, hτA⟩ : A) * Subgroup.inclusion hPA x =
          Subgroup.inclusion hPA x * ⟨ρ τ, hτA⟩ := by
        apply Subtype.ext
        simpa using hfix3 τ x hτu hτv hτd
      calc
        t τ * a (Subgroup.inclusion hPA x)
            = a (⟨ρ τ, hτA⟩ : A) * a (Subgroup.inclusion hPA x) := by rw [hτa]
        _ = a ((⟨ρ τ, hτA⟩ : A) * Subgroup.inclusion hPA x) :=
          (map_mul a (⟨ρ τ, hτA⟩ : A) (Subgroup.inclusion hPA x)).symm
        _ = a (Subgroup.inclusion hPA x * (⟨ρ τ, hτA⟩ : A)) := by rw [hcommA]
        _ = a (Subgroup.inclusion hPA x) * a (⟨ρ τ, hτA⟩ : A) :=
          map_mul a (Subgroup.inclusion hPA x) (⟨ρ τ, hτA⟩ : A)
        _ = a (Subgroup.inclusion hPA x) * t τ := by rw [hτa]
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact hswap x
  have hσC : t σ ∈ Subgroup.centralizer ({a (Subgroup.inclusion hPA x)} : Set H) :=
    Subgroup.mem_comap.mp (hfix_le hσmem)
  exact Subgroup.mem_centralizer_singleton_iff.mp hσC

theorem deletionChart_covariance
    {A : Subgroup X} (ρ : Equiv.Perm I →* X) (a : A →* H) (t : Equiv.Perm I →* H)
    (P : I → I → Subgroup X)
    {u v c d : I}
    (huv : u ≠ v) (hcu : c ≠ u) (hcv : c ≠ v)
    (hdu : d ≠ u) (hdv : d ≠ v) (hcd : c ≠ d)
    (hequiv : ∀ (σ : Equiv.Perm I) (i j : I),
      (P i j).map (MulAut.conj (ρ σ)).toMonoidHom = P (σ i) (σ j))
    (hcontain : ∀ {i j : I}, i ≠ j → i ≠ d → j ≠ d → P i j ≤ A)
    (hcommon : ∀ σ : Equiv.Perm I, σ d = d → ∃ h : ρ σ ∈ A, a ⟨ρ σ, h⟩ = t σ)
    (hbase : ∀ (σ : Equiv.Perm I) (x : P u v), σ u = u → σ v = v →
      ρ σ * (x : X) = (x : X) * ρ σ)
    (hcross : ∀ x : P u v,
      t (Equiv.swap c d) * a (Subgroup.inclusion (hcontain huv hdu.symm hdv.symm) x) =
        a (Subgroup.inclusion (hcontain huv hdu.symm hdv.symm) x) * t (Equiv.swap c d))
    {i j : I} (hij : i ≠ j) (hid : i ≠ d) (hjd : j ≠ d)
    (σ : Equiv.Perm I) (hσi : σ i ≠ d) (hσj : σ j ≠ d)
    (x : P i j) :
    a (Subgroup.inclusion (hcontain (σ.injective.ne hij) hσi hσj)
        (⟨ρ σ * (x : X) * (ρ σ)⁻¹, conj_mem_pair hequiv σ x⟩ : P (σ i) (σ j))) =
      t σ * a (Subgroup.inclusion (hcontain hij hid hjd) x) * (t σ)⁻¹ := by
  let f : Fin 3 → I := ![u, v, d]
  let g : Fin 3 → I := ![i, j, d]
  let g' : Fin 3 → I := ![σ i, σ j, d]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f, huv, huv.symm, hdu, hdu.symm, hdv, hdv.symm]
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [g, hij, hij.symm, hid, hid.symm, hjd, hjd.symm]
  have hg' : Function.Injective g' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [g', σ.injective.ne hij, (σ.injective.ne hij).symm,
        hσi, hσi.symm, hσj, hσj.symm]
  obtain ⟨lam, hlam⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  obtain ⟨mu, hmu⟩ := Equiv.Perm.exists_extending_pair f g' hf hg'
  have hlamu : lam u = i := by simpa [f, g] using hlam 0
  have hlamv : lam v = j := by simpa [f, g] using hlam 1
  have hlamd : lam d = d := by simpa [f, g] using hlam 2
  have hmuu : mu u = σ i := by simpa [f, g'] using hmu 0
  have hmuv : mu v = σ j := by simpa [f, g'] using hmu 1
  have hmud : mu d = d := by simpa [f, g'] using hmu 2
  have hxmap : (x : X) ∈ (P u v).map (MulAut.conj (ρ lam)).toMonoidHom := by
    rw [hequiv lam u v, hlamu, hlamv]
    exact x.2
  obtain ⟨x0, hx0P, hx0⟩ := (Subgroup.mem_map).mp hxmap
  let x0P : P u v := ⟨x0, hx0P⟩
  have hx_eq : ρ lam * (x0 : X) * (ρ lam)⁻¹ = (x : X) := by
    simpa using hx0
  let δ : Equiv.Perm I := mu⁻¹ * σ * lam
  have hδu : δ u = u := by
    change (mu⁻¹ * σ * lam) u = u
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hlamu, ← hmuu]
    simp
  have hδv : δ v = v := by
    change (mu⁻¹ * σ * lam) v = v
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hlamv, ← hmuv]
    simp
  have hσlam_eq : σ * lam = mu * δ := by
    simp only [δ]
    group
  obtain ⟨hlamA, hlam_a⟩ := hcommon lam hlamd
  obtain ⟨hmuA, hmu_a⟩ := hcommon mu hmud
  let hPA : P u v ≤ A := hcontain huv hdu.symm hdv.symm
  have hx0A : (x0 : X) ∈ A := hPA hx0P
  have hcommδ : t δ * a (Subgroup.inclusion hPA x0P) =
      a (Subgroup.inclusion hPA x0P) * t δ := by
    exact centralizer_of_fixing_pair (A := A) (P := P u v)
      ρ a t hPA hcu hcv hdu hdv hcd hcommon
      (fun σ x hσu hσv _ => hbase σ x hσu hσv) hcross δ hδu hδv x0P
  let q : A := ⟨x0, hx0A⟩
  let plam : A := ⟨ρ lam, hlamA⟩
  let pmu : A := ⟨ρ mu, hmuA⟩
  let xA : A := Subgroup.inclusion (hcontain hij hid hjd) x
  let yP : P (σ i) (σ j) :=
    ⟨ρ σ * (x : X) * (ρ σ)⁻¹, conj_mem_pair hequiv σ x⟩
  let yA : A := Subgroup.inclusion (hcontain (σ.injective.ne hij) hσi hσj) yP
  change a yA = t σ * a xA * (t σ)⁻¹
  have hplam : a plam = t lam := by simpa [plam] using hlam_a
  have hpmu : a pmu = t mu := by simpa [pmu] using hmu_a
  have hxAeq : xA = plam * q * plam⁻¹ := by
    apply Subtype.ext
    exact hx_eq.symm
  have hax : a xA = t lam * a q * (t lam)⁻¹ := by
    rw [hxAeq]
    calc
      a (plam * q * plam⁻¹) = a (plam * q) * a plam⁻¹ :=
        map_mul a (plam * q) plam⁻¹
      _ = a (plam * q) * (a plam)⁻¹ := by rw [map_inv]
      _ = (a plam * a q) * (a plam)⁻¹ := by rw [map_mul]
      _ = (t lam * a q) * (t lam)⁻¹ := by rw [hplam]
  have hbaseδ : ρ δ * (x0 : X) * (ρ δ)⁻¹ = (x0 : X) := by
    have hcomm : ρ δ * (x0 : X) = (x0 : X) * ρ δ := hbase δ x0P hδu hδv
    rw [hcomm]
    group
  have hy_eq : ρ σ * (x : X) * (ρ σ)⁻¹ = ρ mu * (x0 : X) * (ρ mu)⁻¹ := by
    rw [← hx_eq]
    calc
      ρ σ * (ρ lam * (x0 : X) * (ρ lam)⁻¹) * (ρ σ)⁻¹
          = (ρ σ * ρ lam) * (x0 : X) * (ρ σ * ρ lam)⁻¹ := by group
      _ = ρ (σ * lam) * (x0 : X) * (ρ (σ * lam))⁻¹ := by rw [map_mul]
      _ = ρ (mu * δ) * (x0 : X) * (ρ (mu * δ))⁻¹ := by rw [hσlam_eq]
      _ = (ρ mu * ρ δ) * (x0 : X) * (ρ mu * ρ δ)⁻¹ := by rw [map_mul]
      _ = ρ mu * (ρ δ * (x0 : X) * (ρ δ)⁻¹) * (ρ mu)⁻¹ := by group
      _ = ρ mu * (x0 : X) * (ρ mu)⁻¹ := by rw [hbaseδ]
  have hyAeq : yA = pmu * q * pmu⁻¹ := by
    apply Subtype.ext
    exact hy_eq
  have hay : a yA = t mu * a q * (t mu)⁻¹ := by
    rw [hyAeq]
    calc
      a (pmu * q * pmu⁻¹) = a (pmu * q) * a pmu⁻¹ :=
        map_mul a (pmu * q) pmu⁻¹
      _ = a (pmu * q) * (a pmu)⁻¹ := by rw [map_inv]
      _ = (a pmu * a q) * (a pmu)⁻¹ := by rw [map_mul]
      _ = (t mu * a q) * (t mu)⁻¹ := by rw [hpmu]
  have hcommδ' : t δ * a q = a q * t δ := by
    have hq : q = Subgroup.inclusion hPA x0P := by
      apply Subtype.ext
      rfl
    rw [hq]
    exact hcommδ
  have hHside : t σ * a xA * (t σ)⁻¹ = t mu * a q * (t mu)⁻¹ := by
    rw [hax]
    calc
      t σ * (t lam * a q * (t lam)⁻¹) * (t σ)⁻¹
          = (t σ * t lam) * a q * (t σ * t lam)⁻¹ := by group
      _ = t (σ * lam) * a q * (t (σ * lam))⁻¹ := by rw [map_mul]
      _ = t (mu * δ) * a q * (t (mu * δ))⁻¹ := by rw [hσlam_eq]
      _ = (t mu * t δ) * a q * (t mu * t δ)⁻¹ := by rw [map_mul]
      _ = t mu * (t δ * a q * (t δ)⁻¹) * (t mu)⁻¹ := by group
      _ = t mu * a q * (t mu)⁻¹ := by rw [hcommδ']; group
  exact hay.trans hHside.symm

end CFSG.Permutation.DeletionChart

end
