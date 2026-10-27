module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveCent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem Hyp612H3.swapH3 {n : ℕ} {M V : Subgroup G} {g : G} (h : Hyp612H3 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹) :
    Hyp612H3 n (conjSubgroup M g) (conjSubgroup V g) g⁻¹ :=
  ⟨h.toHyp612Sym.swap, hd⟩

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem commutator_conj_mem_NOf (h : Hyp612Sym n M V g) {v w k : G} (hv : v ∈ LOf V g)
    (hvw : ⁅v, w⁆ ∈ CKOf M V g) (hk : k ∈ KOf M V g) (hkw : ⁅k, w⁆ ∈ NOf M V g) :
    ⁅v * k * v⁻¹, w⁆ ∈ NOf M V g := by
  set d : G := ⁅v, w⁆ with hd
  set k' : G := v * k * v⁻¹ with hk'
  have hdD : d ∈ CKOf M V g := by simpa [hd] using hvw
  have hdL : d ∈ LOf V g := CKOf_le_LOf M V g hdD
  have hdL' : d⁻¹ ∈ LOf V g := (LOf V g).inv_mem hdL
  have hk'K : k' ∈ KOf M V g := by
    rw [hk']
    exact (Subgroup.mem_normalizer_iff.1 (LOf_le_normalizer_KOf h hv) k).1 hk
  have hn1 : ⁅w, k⁆ ∈ NOf M V g := by
    have h1 := (NOf M V g).inv_mem hkw
    rwa [commutatorElement_inv k w] at h1
  have hn2 : ⁅d⁻¹, k'⁆ ∈ NOf M V g := by
    have h2 : ⁅k', d⁻¹⁆ ∈ NOf M V g :=
      ((mem_CKOf_iff h).1 ((CKOf M V g).inv_mem hdD)).2 k' hk'K
    have h3 := (NOf M V g).inv_mem h2
    rwa [commutatorElement_inv k' d⁻¹] at h3
  have hcen1 : v * ⁅w, k⁆ * v⁻¹ = ⁅w, k⁆ := by
    rw [← mul_comm_of_mem_NOf h hn1 hv]; group
  have hcen2 : d⁻¹ * ⁅w, k⁆ * d = ⁅w, k⁆ := by
    rw [← mul_comm_of_mem_NOf h hn1 hdL']; group
  have hwv : w * v = d⁻¹ * v * w := by
    rw [hd, commutatorElement_def]; group
  have hwk : w * k * w⁻¹ = ⁅w, k⁆ * k := by
    rw [commutatorElement_def]; group
  have hdk' : d⁻¹ * k' * d = ⁅d⁻¹, k'⁆ * k' := by
    rw [commutatorElement_def]; group
  have hmain : w * k' * w⁻¹ = ⁅w, k⁆ * ⁅d⁻¹, k'⁆ * k' := by
    rw [show w * k' * w⁻¹ = (w * v) * k * (w * v)⁻¹ by rw [hk']; group]
    rw [hwv]
    rw [show (d⁻¹ * v * w) * k * (d⁻¹ * v * w)⁻¹
          = d⁻¹ * (v * (w * k * w⁻¹) * v⁻¹) * d by group]
    rw [hwk]
    rw [show v * (⁅w, k⁆ * k) * v⁻¹ = (v * ⁅w, k⁆ * v⁻¹) * (v * k * v⁻¹) by group]
    rw [hcen1, ← hk']
    rw [show d⁻¹ * (⁅w, k⁆ * k') * d
          = (d⁻¹ * ⁅w, k⁆ * d) * (d⁻¹ * k' * d) by group]
    rw [hcen2, hdk']
    group
  have hcomm : ⁅w, k'⁆ ∈ NOf M V g := by
    have he : ⁅w, k'⁆ = ⁅w, k⁆ * ⁅d⁻¹, k'⁆ := by
      rw [commutatorElement_def, hmain]; group
    rw [he]
    exact (NOf M V g).mul_mem hn1 hn2
  have hfinal := (NOf M V g).inv_mem hcomm
  rwa [commutatorElement_inv w k'] at hfinal

theorem normalizer_UOf_of_conj_mem_sup (h : Hyp612Sym n M V g) {x : G} (hx : x ∈ LOf V g)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V ⊔ KOf M V g) :
    x ∈ normalizer ((UOf M V g : Subgroup G) : Set G) := by
  have hex : ∃ v : G, v ∈ V ∧ v ∉ UOf M V g := by
    by_contra hc
    rw [not_exists] at hc
    have hle : V ≤ UOf M V g := by
      intro y hy
      by_contra hyU
      exact hc y ⟨hy, hyU⟩
    exact h.not_V_le_conjM (hle.trans inf_le_right)
  obtain ⟨v, hvV, hvU⟩ := hex
  have hVL : V ≤ LOf V g := by rw [LOf]; exact le_sup_left
  have hVK : V ≤ normalizer ((KOf M V g : Subgroup G) : Set G) :=
    hVL.trans (LOf_le_normalizer_KOf h)
  have hcoe : ((V ⊔ KOf M V g : Subgroup G) : Set G) = (V : Set G) * (KOf M V g : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right V (KOf M V g) hVK
  have hxv : x * v * x⁻¹ ∈ ((V ⊔ KOf M V g : Subgroup G) : Set G) := hxV v hvV
  rw [hcoe, Set.mem_mul] at hxv
  obtain ⟨v', hv'V, kap, hkapK, hxv_eq⟩ := hxv
  have hv'U : v' ∉ UOf M V g := by
    intro hv'U
    have hxvK : x * v * x⁻¹ ∈ KOf M V g := by
      rw [← hxv_eq]
      exact (KOf M V g).mul_mem (by rw [KOf]; exact Subgroup.mem_sup_left hv'U) hkapK
    have h0 := (Subgroup.mem_normalizer_iff.1
      (LOf_le_normalizer_KOf h ((LOf V g).inv_mem hx)) (x * v * x⁻¹)).1 hxvK
    have hvK : v ∈ KOf M V g := by
      rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group] at h0
    exact hvU (by rw [← h.V_inf_KOf]; exact Subgroup.mem_inf.2 ⟨hvV, hvK⟩)
  have hstep : ∀ u ∈ UOf M V g, x * u * x⁻¹ ∈ UOf M V g := by
    intro u hu
    have hkK : x * u * x⁻¹ ∈ KOf M V g :=
      (Subgroup.mem_normalizer_iff.1
        (LOf_le_normalizer_KOf h hx) u).1 (by rw [KOf]; exact Subgroup.mem_sup_left hu)
    have huv : u * v = v * u := h.elemAbelian.comm hu.1 hvV
    have hconj1 : (x * u * x⁻¹) * (x * v * x⁻¹) = x * (u * v) * x⁻¹ := by group
    have hconj2 : (x * v * x⁻¹) * (x * u * x⁻¹) = x * (v * u) * x⁻¹ := by group
    have hconj : (x * u * x⁻¹) * (x * v * x⁻¹) = (x * v * x⁻¹) * (x * u * x⁻¹) := by
      rw [hconj1, hconj2, huv]
    have hcomm : ⁅x * u * x⁻¹, x * v * x⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 hconj
    have hcomm' : ⁅x * u * x⁻¹, v' * kap⁆ = 1 := by
      rw [hxv_eq]; exact hcomm
    have hn : ⁅x * u * x⁻¹, kap⁆ ∈ NOf M V g := commutator_KOf_KOf_mem_N h hkK hkapK
    have hv'L : v' ∈ LOf V g := by rw [LOf]; exact Subgroup.mem_sup_left hv'V
    have hcen : v' * ⁅x * u * x⁻¹, kap⁆ * v'⁻¹ = ⁅x * u * x⁻¹, kap⁆ := by
      rw [← mul_comm_of_mem_NOf h hn hv'L]; group
    have h1 : ⁅x * u * x⁻¹, v'⁆ * v' * ⁅x * u * x⁻¹, kap⁆ * v'⁻¹ = 1 := by
      rw [← commutatorElement_mul_right_eq_mul_conj]
      exact hcomm'
    rw [show ⁅x * u * x⁻¹, v'⁆ * v' * ⁅x * u * x⁻¹, kap⁆ * v'⁻¹
          = ⁅x * u * x⁻¹, v'⁆ * (v' * ⁅x * u * x⁻¹, kap⁆ * v'⁻¹) by group,
        hcen] at h1
    have h2 : ⁅x * u * x⁻¹, v'⁆ = (⁅x * u * x⁻¹, kap⁆)⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    have h3 : ⁅x * u * x⁻¹, v'⁆ ∈ NOf M V g := by
      rw [h2]
      exact (NOf M V g).inv_mem hn
    exact mem_UOf_of_commutator_mem_N h hv'V hv'U hkK h3
  have hconjU : conjSubgroup (UOf M V g) x⁻¹ ≤ UOf M V g := by
    intro y hy
    rw [mem_conjSubgroup_iff, inv_inv] at hy
    have h1 := hstep (x⁻¹ * y * x) hy
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h1
  have heq : conjSubgroup (UOf M V g) x⁻¹ = UOf M V g :=
    Subgroup.eq_of_le_of_card_ge hconjU (by rw [E3.card_conjSubgroup])
  have hxmem : x⁻¹ ∈ normalizer ((UOf M V g : Subgroup G) : Set G) :=
    (conjSubgroup_eq_iff_mem_normalizer).1 heq
  simpa using (normalizer ((UOf M V g : Subgroup G) : Set G)).inv_mem hxmem

end Hyp612Sym

structure KLPair (M V : Subgroup G) (g : G) (A C : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 A
  le_L : A ≤ LOf V g
  exists_conj : ∃ x : G, A = conjSubgroup V x
  le : C ≤ A
  le_K : C ≤ KOf M V g
  NOf_le : NOf M V g ≤ C
  mem_of_commutator_mem : ∀ a ∈ A, a ∉ C → ∀ k ∈ KOf M V g, ⁅k, a⁆ ∈ NOf M V g → k ∈ C
  card_eq : Nat.card C = Nat.card (UOf M V g)
  mQuot_eq : E3.mQuot A C = E3.mQuot V (UOf M V g)

namespace KLPair

variable {n : ℕ} {M V A C : Subgroup G} {g : G}

theorem ofV (h : Hyp612Sym n M V g) : KLPair M V g V (UOf M V g) :=
  ⟨h.elemAbelian, le_sup_left, ⟨1, (conjSubgroup_one V).symm⟩, inf_le_left,
    le_sup_left, inf_le_left,
    fun a ha haU k hk hc => h.mem_UOf_of_commutator_mem_N ha haU hk hc, rfl, rfl⟩

theorem ofConjV (h : Hyp612Sym n M V g) : KLPair M V g (conjSubgroup V g) (BOf M V g) :=
  ⟨h.elemAbelian_conj, le_sup_right, ⟨g, rfl⟩, inf_le_left, le_sup_right, inf_le_right,
    fun a ha haB k hk hc => h.mem_BOf_of_commutator_mem_N ha haB hk hc,
    h.card_UOf_eq_card_BOf.symm, h.mQuot_conjV_BOf⟩

theorem mem_conjSubgroup_iff (h : Hyp612Sym n M V g) (P : KLPair M V g A C) {a h' k : G}
    (ha : a ∈ A) (haC : a ∉ C) (hh' : h' ∈ LOf V g) (hk : k ∈ KOf M V g) :
    ⁅k, h'⁻¹ * a * h'⁆ ∈ NOf M V g ↔ k ∈ conjSubgroup C h' := by
  constructor
  · intro hn
    have hk₀ : h' * k * h'⁻¹ ∈ KOf M V g :=
      (Subgroup.mem_normalizer_iff.1 (Hyp612Sym.LOf_le_normalizer_KOf h hh') k).1 hk
    have hcomm : ⁅h' * k * h'⁻¹, a⁆ = h' * ⁅k, h'⁻¹ * a * h'⁆ * h'⁻¹ := by
      rw [commutatorElement_def]; group
    have hN : ⁅h' * k * h'⁻¹, a⁆ ∈ NOf M V g := by
      rw [hcomm]
      have hcen : h' * ⁅k, h'⁻¹ * a * h'⁆ * h'⁻¹ = ⁅k, h'⁻¹ * a * h'⁆ := by
        rw [← Hyp612Sym.mul_comm_of_mem_NOf h hn hh']; group
      rw [hcen]; exact hn
    exact CFSG.Quasithin.mem_conjSubgroup_iff.2
      (P.mem_of_commutator_mem a ha haC (h' * k * h'⁻¹) hk₀ hN)
  · intro hkc
    have hc : h' * k * h'⁻¹ ∈ C := CFSG.Quasithin.mem_conjSubgroup_iff.1 hkc
    have hcA : h' * k * h'⁻¹ ∈ A := P.le hc
    have hcomm : ⁅k, h'⁻¹ * a * h'⁆ = h'⁻¹ * ⁅h' * k * h'⁻¹, a⁆ * h' := by
      rw [commutatorElement_def]; group
    rw [hcomm]
    have hca : ⁅h' * k * h'⁻¹, a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (P.elemAbelian.comm hcA ha)
    rw [hca, mul_one, inv_mul_cancel]
    exact (NOf M V g).one_mem

end KLPair

end CFSG.LocalAnalysis.WeakClosure81
