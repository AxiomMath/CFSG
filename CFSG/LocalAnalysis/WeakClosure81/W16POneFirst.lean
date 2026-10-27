module

public import CFSG.LocalAnalysis.WeakClosure81.W16POneSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg161

variable {M V₀ V U : Subgroup G} {g : G}

private theorem mQuot_inf_centralizer_le_rk {A V₀ : Subgroup G} (hA : IsElemAbelian 2 A) {v : G}
    (hcomm : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ V₀ ⊓ A) :
    E3.mQuot A (A ⊓ Subgroup.centralizer ({v} : Set G)) ≤ rk ↥(V₀ ⊓ A) := by
  let f : A →* G :=
    { toFun := fun a => (a : G) * v * (a : G)⁻¹ * v⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        let ca : G := (a : G) * v * (a : G)⁻¹ * v⁻¹
        let cb : G := (b : G) * v * (b : G)⁻¹ * v⁻¹
        have haA : ca ∈ A := (hcomm a a.2).2
        have hbA : cb ∈ A := (hcomm b b.2).2
        have hcbv : (b : G) * v * (b : G)⁻¹ = cb * v := by
          change (b : G) * v * (b : G)⁻¹ = ((b : G) * v * (b : G)⁻¹ * v⁻¹) * v
          group
        have hcav : (a : G) * v * (a : G)⁻¹ = ca * v := by
          change (a : G) * v * (a : G)⁻¹ = ((a : G) * v * (a : G)⁻¹ * v⁻¹) * v
          group
        have hacb : (a : G) * cb = cb * (a : G) := B2F.isElemAbelian_comm hA a.2 hbA
        have hconjb : (a : G) * cb * (a : G)⁻¹ = cb := by rw [hacb]; group
        have hcab : ca * cb = cb * ca := B2F.isElemAbelian_comm hA haA hbA
        show ((a * b : A) : G) * v * ((a * b : A) : G)⁻¹ * v⁻¹ = ca * cb
        rw [Subgroup.coe_mul]
        calc ((a : G) * (b : G)) * v * ((a : G) * (b : G))⁻¹ * v⁻¹
            = (a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹ * v⁻¹ := by group
          _ = (a : G) * (cb * v) * (a : G)⁻¹ * v⁻¹ := by rw [hcbv]
          _ = ((a : G) * cb * (a : G)⁻¹) * ((a : G) * v * (a : G)⁻¹) * v⁻¹ := by group
          _ = cb * ((a : G) * v * (a : G)⁻¹) * v⁻¹ := by rw [hconjb]
          _ = cb * (ca * v) * v⁻¹ := by rw [hcav]
          _ = cb * ca := by group
          _ = ca * cb := hcab.symm }
  have hker : f.ker = (A ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, fun y hy => ?_⟩
      have hyv : y = v := Set.mem_singleton_iff.mp hy
      have h1 : (x : G) * v * (x : G)⁻¹ = v := mul_inv_eq_one.1 h
      calc y * (x : G) = v * (x : G) := by rw [hyv]
        _ = ((x : G) * v * (x : G)⁻¹) * (x : G) := by rw [h1]
        _ = (x : G) * v := by group
        _ = (x : G) * y := by rw [hyv]
    · rintro ⟨-, hc⟩
      have hv : v * (x : G) = (x : G) * v := hc v (Set.mem_singleton v)
      show (x : G) * v * (x : G)⁻¹ * v⁻¹ = 1
      rw [show (x : G) * v = v * (x : G) from hv.symm]
      group
  have hrel : (A ⊓ Subgroup.centralizer ({v} : Set G)).relIndex A = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hrange : f.range ≤ V₀ ⊓ A := by
    rintro z ⟨a, rfl⟩
    exact hcomm a a.2
  have hdvd : Nat.card f.range ∣ Nat.card ↥(V₀ ⊓ A) := Subgroup.card_dvd_of_le hrange
  have hdvd' : (A ⊓ Subgroup.centralizer ({v} : Set G)).relIndex A ∣ Nat.card ↥(V₀ ⊓ A) := by
    rw [hrel]; exact hdvd
  calc E3.mQuot A (A ⊓ Subgroup.centralizer ({v} : Set G))
      = padicValNat 2 ((A ⊓ Subgroup.centralizer ({v} : Set G)).relIndex A) := rfl
    _ ≤ padicValNat 2 (Nat.card ↥(V₀ ⊓ A)) := padicValNat_two_le_of_dvd (Nat.card_pos.ne') hdvd'
    _ = rk ↥(V₀ ⊓ A) := rfl

theorem false_of_le_centralizer (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (h0 : V₀ ≤ centralizer (conjSubgroup V g : Set G)) : False := by
  have hAe : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian g
  have hnc : ∃ v ∈ V, ∃ y ∈ conjSubgroup V g, v * y ≠ y * v := by
    by_contra h
    refine c.not_comm fun x hx y hy => ?_
    by_contra hne
    exact h ⟨x, hx, y, hy, hne⟩
  obtain ⟨vx, hvxV, yx, hyxA, hxyx⟩ := hnc
  have hyx_ct : yx ∈ F11.CTilde M V₀ V := c.conj_le_cTilde hyxA
  have hxV : ¬ V ≤ Subgroup.centralizer ({yx} : Set G) := by
    intro hle
    exact hxyx (Subgroup.mem_centralizer_iff.1 (hle hvxV) yx rfl).symm
  have hle_sup : U ⊔ V₀ ≤ V ⊓ Subgroup.centralizer ({yx} : Set G) := by
    refine le_inf (sup_le c.le c.hyp.h6.le) (sup_le ?_ ?_)
    · intro u hu
      refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      have h := Subgroup.mem_centralizer_iff.1 (c.conj_le hyxA).2 u hu
      simpa [Set.mem_singleton_iff.mp ha] using h.symm
    · intro w hw
      refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      have h := Subgroup.mem_centralizer_iff.1 (h0 hw) yx hyxA
      simpa [Set.mem_singleton_iff.mp ha] using h
  have h14_6 : rk ↥(conjSubgroup V₀ g⁻¹ ⊓ V) ≤
      E3.mQuot V (V ⊓ Subgroup.centralizer ({yx} : Set G)) :=
    mQuot_centralizer_ge_rk_conjSubgroup_inf (M := M) (V₀ := V₀) (V := V)
      c.hyp.h6.elemAbelian c.hyp.h6.le c.hyp.h6.normalizer_eq.symm.le c.hyp.normalizer₀
      c.hyp.isTI (c.hyp.h6.conjGenerated c.hyp.ne_bot)
      (g := g⁻¹) (fun hg => c.not_mem (by simpa using M.inv_mem hg)) hyx_ct hxV
  have hx_lt : E3.mQuot V (V ⊓ Subgroup.centralizer ({yx} : Set G)) <
      mBar M V₀ V c.hyp.h6.elemAbelian :=
    lt_of_le_of_lt (E3.mQuot_mono hle_sup) c.lt
  have hrk_lt : rk ↥(conjSubgroup V₀ g⁻¹ ⊓ V) < mBar M V₀ V c.hyp.h6.elemAbelian :=
    lt_of_le_of_lt h14_6 hx_lt
  have key : ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x := by
    intro x hx y hy
    set t : G := g * x * g⁻¹ with htdef
    have htM : t ∈ M := by
      have h := mem_conjSubgroup_iff.1 (c.le_conjSubgroup h152 hx)
      simpa [htdef] using h
    have htS : t ∈ conjSubgroup V g⁻¹ := by
      rw [mem_conjSubgroup_iff, htdef]
      convert hx using 1
      group
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (E3.isPGroup_conjSubgroup c.hyp.isPGroup g⁻¹))
      ⟨t, htS⟩
    have ht2 : ∃ k : ℕ, orderOf t = 2 ^ k :=
      ⟨k, by rw [← hk]; exact Subgroup.orderOf_coe (⟨t, htS⟩ : conjSubgroup V g⁻¹)⟩
    have hmq_eq : E3.mQuot V
        (conjSubgroup (conjSubgroup V g ⊓ Subgroup.centralizer ({x} : Set G)) g⁻¹) =
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer ({x} : Set G)) := by
      have h := E3.mQuot_conjSubgroup (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.centralizer ({x} : Set G)) g⁻¹
      rwa [E3.conjSubgroup_conj_inv] at h
    have hrk_eq : rk ↥(V₀ ⊓ conjSubgroup V g) = rk ↥(conjSubgroup V₀ g⁻¹ ⊓ V) := by
      have h1 : conjSubgroup (V₀ ⊓ conjSubgroup V g) g⁻¹ = conjSubgroup V₀ g⁻¹ ⊓ V := by
        rw [E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv]
      rw [← h1]
      simp only [rk, E3.card_conjSubgroup]
    have hmq_lt : E3.mQuot V
        (conjSubgroup (conjSubgroup V g ⊓ Subgroup.centralizer ({x} : Set G)) g⁻¹) <
        mBar M V₀ V c.hyp.h6.elemAbelian := by
      rw [hmq_eq]
      exact lt_of_le_of_lt (hrk_eq ▸ mQuot_inf_centralizer_le_rk hAe (v := x)
        (c.commutator_mem h152 x hx)) hrk_lt
    have ht_ct : t ∈ F11.CTilde M V₀ V :=
      mem_cTilde_of_mQuot_lt_mod c.hyp.h6.elemAbelian c.hyp.h6.le
        c.hyp.h6.normalizer_eq.symm.le c.hyp.normalizer₀.symm.le htM ht2
        (C := conjSubgroup (conjSubgroup V g ⊓ Subgroup.centralizer ({x} : Set G)) g⁻¹)
        (by rw [E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv]; exact inf_le_left)
        (by
          intro d hd
          have hda : g⁻¹ * d * g ∈ conjSubgroup V g ⊓ Subgroup.centralizer ({x} : Set G) := by
            simpa only [inv_inv] using mem_conjSubgroup_iff.1 hd
          have hxd : x * (g⁻¹ * d * g) = (g⁻¹ * d * g) * x :=
            Subgroup.mem_centralizer_iff.1 hda.2 x rfl
          have hct : t * d = d * t := by
            rw [htdef]
            calc g * x * g⁻¹ * d = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by group
              _ = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by rw [hxd]
              _ = d * (g * x * g⁻¹) := by group
          rw [hct]
          convert (V₀.one_mem) using 1
          group)
        (by exact_mod_cast hmq_lt)
    have hw := (FourteenTwo.mem_cTilde_iff_comm.1 ht_ct).2.2
    have hyV : g * y * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
    have hcomm_gt : x * y * x⁻¹ * y⁻¹ ∈ conjSubgroup V₀ g := by
      rw [mem_conjSubgroup_iff]
      convert hw (g * y * g⁻¹) hyV using 1
      rw [htdef]
      group
    have hcomm_V₀ : x * y * x⁻¹ * y⁻¹ ∈ V₀ := by
      have h := (c.commutator_mem h152 x hx y hy).1
      have h2 : (y * x * y⁻¹ * x⁻¹)⁻¹ ∈ V₀ := V₀.inv_mem h
      convert h2 using 1
      group
    have hbot : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← c.hyp.conj_inf_eq_bot c.not_mem]
        exact Subgroup.mem_inf.2 ⟨hcomm_gt, hcomm_V₀⟩
      simpa using hmem
    have hxy : x * y * x⁻¹ = y := mul_inv_eq_one.1 hbot
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hxy]
  exact c.not_comm key

end Cfg161

end CFSG.LocalAnalysis.WeakClosure81

end
