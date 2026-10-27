module

public import CFSG.Quasithin.EmptyFaithful.S146R5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G]

namespace IsDec12

variable {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem swap (h : IsDec12 T M H p H₀ H₁ H₂ t) : IsDec12 T M H p H₀ H₂ H₁ t⁻¹ := by
  have hconj : conjSub t⁻¹ H₂ = H₁ := by
    rw [h.conj]
    exact conjSub_conjSub_inv t H₁
  refine
    { le := h.le
      index := h.index
      Q₁ := h.Q₂
      Q₂ := h.Q₁
      le₁ := h.le₂
      le₂ := h.le₁
      sup := by rw [sup_comm]; exact h.sup
      inf := by rw [inf_comm]; exact h.inf
      comm := by rw [Subgroup.commutator_comm]; exact h.comm
      dihedral₁ := h.dihedral₂
      dihedral₂ := h.dihedral₁
      t_mem := T.inv_mem h.t_mem
      t_not := ?_
      conj := hconj.symm
      dir_inf := by rw [inf_comm]; exact h.dir_inf
      dir_sup := by rw [sup_comm]; exact h.dir_sup
      cent₁ := h.cent₂
      cent₂ := h.cent₁
      rank₁ := h.rank₂
      rank₂ := h.rank₁ }
  intro hmem
  have h1 : conjSub t⁻¹ H₂ = H₂ := conjSub_eq_of_mem_normalizer hmem
  have h12 : H₁ = H₂ := by rw [← hconj, h1]
  apply h.t_not
  have h2 : conjSub t H₁ = H₁ := by rw [← h.conj, ← h12]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h2

theorem inf_normalizer_eq (h : IsDec12 T M H p H₀ H₁ H₂ t) (hTH : T ≤ H) :
    T ⊓ Subgroup.normalizer (H₁ : Set G) = T ⊓ H₀ :=
  le_antisymm (le_inf inf_le_left (h.inf_normalizer_le hTH))
    (le_inf inf_le_left (inf_le_right.trans h.H₀_le_normalizer_H₁))

theorem inf_normalizer_eq_swap (h : IsDec12 T M H p H₀ H₁ H₂ t) (hTH : T ≤ H) :
    T ⊓ Subgroup.normalizer (H₂ : Set G) = T ⊓ Subgroup.normalizer (H₁ : Set G) := by
  rw [h.inf_normalizer_eq hTH, h.swap.inf_normalizer_eq hTH]

theorem le_normalizer_H₀ (h : IsDec12 T M H p H₀ H₁ H₂ t) : H ≤ Subgroup.normalizer (H₀ : Set G) := by
  have h2 : (H₀.subgroupOf H).index = 2 := h.index
  have hn : (H₀.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two h2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mp hn

section Fin

variable [Finite G]

theorem le_normalizer_uHi₁ {T M : Subgroup G} (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) := by
  rw [h.sup]
  exact sup_le (h.le_normalizer_uHi S hred)
    (S146A.le_normalizer_of_commutator_le (Z_le_uHi T M H H₁) h.cent₁)

theorem le_normalizer_uHi₂ {T M : Subgroup G} (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (uHi T M H H₂ : Set G) :=
  h.swap.le_normalizer_uHi₁ S hred

end Fin

section Fin2

variable [Finite G] {T M : Subgroup G}

theorem conjSub_uHi_of_not_mem (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {s : G} (hsH : s ∈ H) (hs : s ∉ H₀) :
    conjSub s (uHi T M H H₁) = uHi T M H H₂ := by
  have hTH : T ≤ H := hred.isHTM.1.1
  have hst : s * t⁻¹ ∈ H₀ := mul_inv_mem_of_relIndex_two h.index hsH (hTH h.t_mem) hs
    (fun ht0 => h.t_not (h.H₀_le_normalizer_H₁ ht0))
  have e : s = (s * t⁻¹) * t := by group
  rw [e, conjSub_mul, h.conjSub_uHi hred]
  exact conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₂ S hred hst)

theorem centralizerMod_le (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) :
    centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ≤ H₀ := by
  intro x hx
  by_contra hx0
  obtain ⟨hxH, -, hxc⟩ := hx
  have hconj := h.conjSub_uHi_of_not_mem S hred hxH hx0
  have hc : x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := hxc u (Subgroup.mem_zpowers u)
  have h2 : x * u * x⁻¹ ∈ uHi T M H H₂ := by
    rw [← hconj]
    exact mem_conjSub.mpr (by simpa [mul_assoc] using hu)
  have h1 : x * u * x⁻¹ ∈ uHi T M H H₁ := by
    have e : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact (uHi T M H H₁).mul_mem (Z_le_uHi T M H H₁ hc) hu
  have h3 : x * u * x⁻¹ ∈ quasithinOmegaOneCenter T := by
    rw [← h.dir_inf]
    exact ⟨h1, h2⟩
  apply huZ
  have hxG : x ∈ mcOf T := S.le_mcOf hred.isHTM hxH
  have hcomm : x⁻¹ * (x * u * x⁻¹) = (x * u * x⁻¹) * x⁻¹ := S146T.comm_Z (Subgroup.inv_mem _ hxG) h3
  have e : u = x⁻¹ * (x * u * x⁻¹) * x := by group
  rw [e, hcomm]
  simpa [mul_assoc] using h3

theorem tZero_eq (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) :
    tZero T u = T ⊓ Subgroup.normalizer (H₁ : Set G) := by
  have hTH : T ≤ H := hred.isHTM.1.1
  refine le_antisymm ?_ huT
  have hle : tZero T u ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) :=
    centralizerMod_mono_left _ hTH
  rw [h.inf_normalizer_eq hTH]
  exact le_inf (S146T.tZero_le T u) ((hle.trans (h.centralizerMod_le S hred hu huZ)))

end Fin2

end IsDec12

end CFSG.Quasithin
