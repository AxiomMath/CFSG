module

public import CFSG.Quasithin.EmptyFaithful.S153E56F3
public import CFSG.Quasithin.EmptyFaithful.S153E56In

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem conj_mem_V {g v : G} (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) (hv : v ∈ VZ T M) :
    g * v * g⁻¹ ∈ VZ T M :=
  (Subgroup.mem_normalizer_iff.1 hg v).1 hv

omit [Finite G] in
theorem conj_inv_mem_V {g v : G} (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) (hv : v ∈ VZ T M) :
    g⁻¹ * v * g ∈ VZ T M := by
  have := conj_mem_V (T := T) (M := M) (Subgroup.inv_mem _ hg) hv
  simpa using this

omit [Finite G] in
theorem X_facts {y x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) :
    ∃ u ∈ UH153 T M V₁ Mc, x = y⁻¹ * u * y :=
  ⟨y * x * y⁻¹, (mem_conjSubgroup_iff.1 hx).1, by group⟩

omit [Finite G] in
theorem mem_conj_Z {y z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    y⁻¹ * z * y ∈ conjSubgroup (quasithinOmegaOneCenter T) y := by
  rw [mem_conjSubgroup_iff]
  have : y * (y⁻¹ * z * y) * y⁻¹ = z := by group
  rw [this]
  exact hz

end Basic

end S153E56f

namespace S153E

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E56f
open scoped commutatorElement Pointwise

section Lemma

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem geo56_X_perp (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) {y : G}
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
    (iJ : JStruct56 T Mc M V₁ N₁ y) :
    ∀ x ∈ Xgp153 T M V₁ Mc y, ∀ v ∈ VZ T M ⊓ UH153 T M V₁ Mc,
      x * v * x⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := by
  intro x hx v hv
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨hyN, hybN₁, hyb1, hyb3, hybfix⟩ := yb_facts h113 cx c hy
  obtain ⟨z, hzZ, hz1, hzu⟩ := exists_z cx
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hzZ
  have hexp : ∀ w : Wd cx, w * w = 1 := fun w => by rw [← pow_two]; exact IntMod.sq_eq_one w
  have hcard : Nat.card (Wd cx) = 16 := cx.c.hyp.card_VZ
  have hyY : y ∈ Y153 Mc M := (oTwoUpper_le _ hy.1).1
  have hyM : y ∈ M := Y153_le Mc M hyY
  set zW : Wd cx := IntMod.mk hV ⟨z, hzV⟩ with hzW
  have hzW1 : zW ≠ 1 := fun h => hz1 (congrArg IntMod.val h)
  have hqz : qW cx zW = 0 := qW_Z cx hzZ
  obtain ⟨hz'1, hz'z, hqz', hzz', hqzz', h0⟩ :=
    pair_of_order_three hexp (cb_mem_O cx hyM hyN) hyb3 hybfix hzW1 hqz
  obtain ⟨u, huU, hxu⟩ := X_facts hx
  have huN : u ∈ Subgroup.normalizer (VZ T M : Set G) := U_le_N cx huU
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := by
    rw [hxu]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) huN) hyN
  have hxM : x ∈ M := by
    rw [hxu]
    exact M.mul_mem (M.mul_mem (M.inv_mem hyM) (T_le_M cx (U_le_T cx huU))) hyM
  have hxb_eq : cb cx x hxN = (cb cx y hyN)⁻¹ * cb cx u huN * cb cx y hyN := by
    subst hxu
    exact cb_conj cx y u hyN huN hxN
  obtain ⟨Ω, hΩ, hΩsup, hΩeq⟩ := c.h53one.omega
  have huΩ : cb cx u huN ∈ Ω := by
    rw [← hΩsup]
    exact Subgroup.mem_sup_left (convI_mem_autI hV huU huN)
  have hybΩ : cb cx y hyN ∈ Ω := by
    rw [← hΩeq]
    exact Subgroup.mem_sup_left hybN₁
  have hxbΩ : cb cx x hxN ∈ Ω := by
    rw [hxb_eq]
    exact Ω.mul_mem (Ω.mul_mem (Ω.inv_mem hybΩ) huΩ) hybΩ
  have hev : Even (rk (commV (Subgroup.zpowers (cb cx x hxN)))) := ((hΩ _).1 hxbΩ).2
  have hxx : cb cx x hxN * cb cx x hxN = 1 := by
    have hxxC : x * x ∈ Subgroup.centralizer (VZ T M : Set G) := by
      have e : x * x = y⁻¹ * (u * u) * y := by
        rw [hxu]
        group
      rw [e]
      exact B2F.le_centralizer_self hV
        (conj_inv_mem_V hyN (cx.c.hyp.Z_le_VZ (sq_U_mem cx huU)))
    rw [← cb_mul cx x x hxN hxN]
    exact (cb_eq_one_iff cx _ _).2 hxxC
  have hxR : x ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
    rw [iJ.R_eq]
    exact Subgroup.mem_sup_right hx
  have hxC : x ∈ Subgroup.centralizer
      ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) := by
    have := hxR
    rw [iJ.R_cent] at this
    exact this.2
  have hfix : ∀ w ∈ quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y,
      x * w * x⁻¹ = w := by
    intro w hw
    have h1 := Subgroup.mem_centralizer_iff.1 hxC w hw
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [h1]
      _ = w := by group
  have hxz : cb cx x hxN zW = zW := by
    refine IntMod.val_injective ?_
    rw [cb_val]
    exact hfix z (Subgroup.mem_sup_left hzZ)
  have hxz' : cb cx x hxN ((cb cx y hyN)⁻¹ zW) = (cb cx y hyN)⁻¹ zW := by
    refine IntMod.val_injective ?_
    rw [cb_val, cb_inv_val]
    exact hfix _ (Subgroup.mem_sup_right (mem_conj_Z hzZ))
  obtain ⟨P', hP', -, hVU, -⟩ := c.h53two.perp
  have hvP : v ∈ P' := hVU ▸ hv
  obtain ⟨hvV, hvort⟩ := (hP' v).1 hvP
  obtain ⟨hzV', hvV', hB⟩ := hvort z hzZ
  have hcore := x_perp_core (W := Wd cx) (qW_spec cx).1 (qW_spec cx).2.1 hexp hcard hzW1 hz'1
    (Ne.symm hz'z) hqz hqz' h0 (cb_mem_O cx hxM hxN) hxx hev hxz hxz' (v := IntMod.mk hV ⟨v, hvV⟩) hB
  have hval : x * v * x⁻¹ * v⁻¹ =
      (cb cx x hxN (IntMod.mk hV ⟨v, hvV⟩) * (IntMod.mk hV ⟨v, hvV⟩)⁻¹).val := by
    rw [IntMod.val_mul, cb_val, IntMod.val_inv]
    rfl
  rw [hval]
  rcases hcore with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact hzZ

end Lemma

end S153E

end CFSG.Quasithin
