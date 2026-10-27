module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOvergroupAux

public section

namespace CFSG.StandardType.E6QTwo

open Module
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableBExc.E6Three

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] {h : Fin 6 → V}
  {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

private theorem coord_apply
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (v : V) :
    (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) = e6ModelCoordVal (α := α) v := rfl

private theorem coord_reflection
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hα : ∀ i, α i (h i) = 2) (i : Fin Tag.E6.rank) (v : V) :
    (e6ModelCoord hP hV (reflection (hα i) v) : Fin Tag.E6.rank → ZMod 3) =
      adRefl .E6 3 i (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) := by
  rw [coord_apply, coord_apply, adRefl_eq]
  funext j
  simp only [e6ModelCoordVal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e6ModelCol]
  rw [Module.reflection_apply, map_sub, map_smul, smul_eq_mul, hP j i]
  rfl

private theorem overgroup_case_x2
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hW : Nat.card (e6Weyl hα) = 51840) {x2 : V} (hx2 : B x2 x2 = 2)
    (hcoord : (e6ModelCoord hP hV x2 : Fin Tag.E6.rank → ZMod 3) = ovgE2)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hH : H ≤ e6Weyl hα)
    (hS : ∀ g ∈ e6Weyl hα, g x2 = x2 → g ∈ H) :
    H = e6Weyl hα ∨ ∀ g ∈ H, g x2 = x2 ∨ g x2 = -x2 := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (by simpa using congrFun h))
  letI : Fintype V := Fintype.ofFinite V
  have hx2_ne : x2 ≠ 0 := by
    intro h0
    have hB0 : (B (0 : V)) (0 : V) = (0 : ZMod 3) := by simp
    rw [h0, hB0] at hx2
    exact (by decide : ¬((0 : ZMod 3) = 2)) hx2
  have hstab : Nat.card (MulAction.stabilizer (e6Weyl hα) x2) = 720 := by
    rcases stabilizer_cases hP hV hB hα hW hx2_ne with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [hx2] at h
      exact absurd h (by decide)
    · rw [hx2] at h
      exact absurd h (by decide)
  let S : Subgroup (V ≃ₗ[ZMod 3] V) := MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x2
  have hSH : S ⊓ H = S ⊓ (e6Weyl hα) := by
    apply le_antisymm
    · exact le_inf inf_le_left (le_trans inf_le_right hH)
    · refine le_inf inf_le_left ?_
      rintro g ⟨hgS, hgW⟩
      have hgx : g x2 = x2 := by
        simpa [S, MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hgS
      exact hS g hgW hgx
  have hmapH : (MulAction.stabilizer H x2).map H.subtype = S ⊓ H := by
    rw [← MulAction.stabilizer_subgroupOf (G := V ≃ₗ[ZMod 3] V) H x2]
    exact Subgroup.subgroupOf_map_subtype S H
  have hmapW : (MulAction.stabilizer (e6Weyl hα) x2).map (e6Weyl hα).subtype =
      S ⊓ (e6Weyl hα) := by
    rw [← MulAction.stabilizer_subgroupOf (G := V ≃ₗ[ZMod 3] V) (e6Weyl hα) x2]
    exact Subgroup.subgroupOf_map_subtype S (e6Weyl hα)
  have hstabH : Nat.card (MulAction.stabilizer H x2) = 720 := by
    calc Nat.card (MulAction.stabilizer H x2)
        = Nat.card ((MulAction.stabilizer H x2).map H.subtype) :=
          (Subgroup.card_map_of_injective (fun _ _ h => Subtype.ext h)).symm
      _ = Nat.card ↥(S ⊓ H) := by rw [hmapH]
      _ = Nat.card ↥(S ⊓ (e6Weyl hα)) := by rw [hSH]
      _ = Nat.card ((MulAction.stabilizer (e6Weyl hα) x2).map (e6Weyl hα).subtype) := by
          rw [← hmapW]
      _ = Nat.card (MulAction.stabilizer (e6Weyl hα) x2) :=
          Subgroup.card_map_of_injective (fun _ _ h => Subtype.ext h)
      _ = 720 := hstab
  have hos : Nat.card (MulAction.orbit H x2) *
      Nat.card (MulAction.stabilizer H x2) = Nat.card ↥H := by
    let : Fintype ↥H := Fintype.ofFinite _
    let : Fintype ↥(MulAction.orbit H x2) := Fintype.ofFinite _
    let : Fintype ↥(MulAction.stabilizer H x2) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H x2
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
  have hdvdHW : Nat.card ↥H ∣ Nat.card ↥(e6Weyl hα) := by
    have h := Subgroup.card_subgroup_dvd_card (H.subgroupOf (e6Weyl hα))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv] at h
  have hO_dvd : Nat.card (MulAction.orbit H x2) ∣ 72 := by
    have hH_dvd : Nat.card ↥H ∣ 72 * 720 := by
      rw [show (72 * 720 : ℕ) = 51840 by norm_num, ← hW]
      exact hdvdHW
    have hmul : Nat.card (MulAction.orbit H x2) * 720 ∣ 72 * 720 := by
      rwa [← hos, hstabH] at hH_dvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hmul
  let φ : V → (Fin Tag.E6.rank → ZMod 3) := fun v =>
    (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3)
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply (e6ModelCoord hP hV).injective
    exact Subtype.ext hab
  let O : Set V := MulAction.orbit H x2
  let A : Finset (Fin Tag.E6.rank → ZMod 3) := O.toFinset.image φ
  have hAcard : A.card = Nat.card O := by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ hφ_inj, ← Set.ncard_eq_toFinset_card',
      ← Nat.card_coe_set_eq]
  have hAsub : A ⊆ ovgPoints.toFinset := by
    intro y hy
    dsimp only [A] at hy
    obtain ⟨v, hvO, hvy⟩ := Finset.mem_image.mp hy
    rw [Set.mem_toFinset, MulAction.mem_orbit_iff] at hvO
    obtain ⟨g, hgv⟩ := hvO
    have hgv' : (g : V ≃ₗ[ZMod 3] V) x2 = v := by
      simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hgv
    have hgW : (g : V ≃ₗ[ZMod 3] V) ∈ e6Weyl hα := hH g.2
    obtain ⟨w, hw⟩ := exists_adAct_of_mem_e6Weyl hP hV hα hgW
    have hφv : φ v = adAct .E6 3 w ovgE2 := by
      rw [← hgv']
      exact (hw x2).trans (by rw [hcoord])
    rw [← hvy, hφv]
    exact ovgPoints_adAct_mem w
  have he2A : ovgE2 ∈ A := by
    dsimp only [A]
    refine Finset.mem_image.mpr ⟨x2, ?_, hcoord⟩
    rw [Set.mem_toFinset]
    exact MulAction.mem_orbit_iff.mpr ⟨1, one_smul _ _⟩
  have hclA : ∀ y ∈ A, ∀ i : Fin Tag.E6.rank, i.val ≠ 1 → adRefl .E6 3 i y ∈ A := by
    intro y hy i hi
    dsimp only [A] at hy ⊢
    obtain ⟨v, hvO, hvy⟩ := Finset.mem_image.mp hy
    rw [Set.mem_toFinset, MulAction.mem_orbit_iff] at hvO
    obtain ⟨g, hgv⟩ := hvO
    have hgv' : (g : V ≃ₗ[ZMod 3] V) x2 = v := by
      simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hgv
    have hrefl_mem : reflection (hα i) ∈ e6Weyl hα := Subgroup.subset_closure ⟨i, rfl⟩
    have hfix : reflection (hα i) x2 = x2 := by
      apply (e6ModelCoord hP hV).injective
      apply Subtype.ext
      rw [coord_reflection hP hV hα, hcoord, adRefl_fixed_iff]
      fin_cases i <;> simp_all [ovgE2] <;> decide +kernel
    have hrefl_H : reflection (hα i) ∈ H := hS _ hrefl_mem hfix
    refine Finset.mem_image.mpr ⟨reflection (hα i) v, ?_, ?_⟩
    · rw [Set.mem_toFinset, MulAction.mem_orbit_iff]
      refine ⟨⟨reflection (hα i) * g, mul_mem hrefl_H g.2⟩, ?_⟩
      rw [MulAction.subgroup_smul_def]
      change ((reflection (hα i) : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V)) x2 =
        (reflection (hα i) : V ≃ₗ[ZMod 3] V) v
      rw [LinearEquiv.mul_apply, hgv']
    · rw [← hvy]
      exact coord_reflection hP hV hα i v
  have hcomb := ovg_eq_allPoints_or_subset hAsub he2A hclA (by rwa [hAcard])
  rcases hcomb with htop | hsmall
  · left
    have hAcard72 : A.card = 72 := by
      rw [htop, List.toFinset_card_of_nodup ovgPoints_nodup, ovgPoints_length]
    have hOH : Nat.card O = 72 := by rw [← hAcard, hAcard72]
    have hHcard : Nat.card ↥H = 51840 := by
      rw [← hos, hOH, hstabH]
    exact Subgroup.eq_of_le_of_card_ge hH (by rw [hW, hHcard])
  · right
    intro g hg
    have hmem : φ (g x2) ∈ A := by
      dsimp only [A]
      refine Finset.mem_image.mpr ⟨g x2, ?_, rfl⟩
      rw [Set.mem_toFinset]
      exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, rfl⟩
    have hsmall' := hsmall hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall'
    rcases hsmall' with h | h
    · left
      exact (e6ModelCoord hP hV).injective (Subtype.ext (h.trans hcoord.symm))
    · right
      have hneg : (e6ModelCoord hP hV (-x2) : Fin Tag.E6.rank → ZMod 3) =
          -((e6ModelCoord hP hV x2 : Fin Tag.E6.rank → ZMod 3)) := by
        funext j
        exact map_neg (α j) x2
      exact (e6ModelCoord hP hV).injective
        (Subtype.ext (h.trans (by rw [hneg, hcoord])))

theorem eq_e6Weyl_or_forall_apply_eq_of_stabilizer_le
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hW : Nat.card (e6Weyl hα) = 51840) {x : V} (hx : B x x = 2)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hH : H ≤ e6Weyl hα)
    (hS : ∀ g ∈ e6Weyl hα, g x = x → g ∈ H) :
    H = e6Weyl hα ∨ ∀ g ∈ H, g x = x ∨ g x = -x := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (by simpa using congrFun h))
  let x2 : V := h (0 : Fin 6) + 2 • h (1 : Fin 6) + 2 • h (2 : Fin 6) +
    2 • h (4 : Fin 6) + h (5 : Fin 6)
  have hcoord6 : (fun i : Fin 6 => α i x2) = ![0, 1, 0, 0, 0, 0] := by
    funext j
    simp only [x2, map_add, map_smul]
    fin_cases j <;> simp [hP, ovgE2] <;> decide +kernel
  have hcoord : (e6ModelCoord hP hV x2 : Fin Tag.E6.rank → ZMod 3) = ovgE2 := by
    rw [coord_apply]
    change (fun i : Fin 6 => α i x2) = ovgE2
    exact hcoord6
  have hx2 : B x2 x2 = 2 := by
    have h := e6ModelForm_e6Coord hP hV hB x2 x2
    rw [hcoord] at h
    have hQ : e6ModelForm ovgE2 ovgE2 = (1 : ZMod 3) := by decide +kernel
    rw [hQ] at h
    have h2 : (2 : ZMod 3) = 2 * (2 * B x2 x2) := congrArg (fun z : ZMod 3 => 2 * z) h
    rw [show (2 : ZMod 3) * (2 * B x2 x2) = B x2 x2 by
      rw [← mul_assoc, show (2 * 2 : ZMod 3) = 1 by decide, one_mul]] at h2
    exact h2.symm
  have hB0 : (B (0 : V)) (0 : V) = (0 : ZMod 3) := by simp
  have hx2_ne : x2 ≠ 0 := by
    intro h0
    rw [h0, hB0] at hx2
    exact (by decide : ¬((0 : ZMod 3) = 2)) hx2
  have hx_ne : x ≠ 0 := by
    intro h0
    rw [h0, hB0] at hx
    exact (by decide : ¬((0 : ZMod 3) = 2)) hx
  obtain ⟨g0, hg0W, hg0x⟩ :=
    exists_mem_e6Weyl_apply_eq hP hV hB hα hx_ne hx2_ne (by rw [hx, hx2])
  have hginv : g0⁻¹ x2 = x := by
    rw [← hg0x]
    exact LinearEquiv.symm_apply_apply g0 x
  let K : Subgroup (V ≃ₗ[ZMod 3] V) := H.map (MulAut.conj g0).toMonoidHom
  have hKle : K ≤ e6Weyl hα := by
    intro k hk
    obtain ⟨h', hh', hk'⟩ := Subgroup.mem_map.mp hk
    rw [← hk']
    have hconj : (MulAut.conj g0).toMonoidHom h' = g0 * h' * g0⁻¹ := by
      simp [MulAut.conj_apply]
    rw [hconj]
    exact mul_mem (mul_mem hg0W (hH hh')) (inv_mem hg0W)
  have hKS : ∀ g ∈ e6Weyl hα, g x2 = x2 → g ∈ K := by
    intro g hgW hgx
    have hhW : g0⁻¹ * g * g0 ∈ e6Weyl hα :=
      mul_mem (mul_mem (inv_mem hg0W) hgW) hg0W
    have hhx : (g0⁻¹ * g * g0) x = x := by
      change g0⁻¹ (g (g0 x)) = x
      rw [hg0x, hgx, hginv]
    have hhH : g0⁻¹ * g * g0 ∈ H := hS _ hhW hhx
    refine Subgroup.mem_map.mpr ⟨g0⁻¹ * g * g0, hhH, ?_⟩
    change g0 * (g0⁻¹ * g * g0) * g0⁻¹ = g
    group
  have hmain := overgroup_case_x2 hP hV hB hα hW hx2 hcoord hKle hKS
  rcases hmain with hKtop | hKfix
  · left
    have hcardK : Nat.card ↥K = Nat.card ↥H :=
      Subgroup.card_map_of_injective (MulAut.conj g0).injective
    rw [hKtop] at hcardK
    exact Subgroup.eq_of_le_of_card_ge hH hcardK.le
  · right
    intro g hg
    have hmemK : (MulAut.conj g0).toMonoidHom g ∈ K :=
      Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hk := hKfix _ hmemK
    have hkx : ((MulAut.conj g0).toMonoidHom g) x2 = g0 (g x) := by
      change g0 (g (g0⁻¹ x2)) = g0 (g x)
      rw [hginv]
    rcases hk with hk | hk
    · left
      exact g0.injective (hkx.symm.trans (hk.trans hg0x.symm))
    · right
      have hnegx : g0 (-x) = -x2 := by rw [map_neg, hg0x]
      exact g0.injective (hkx.symm.trans (hk.trans hnegx.symm))

theorem exists_mem_e6Weyl_apply_ne
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {x : V} (hx : B x x = 2) :
    ∃ g ∈ e6Weyl hα, g x ≠ x ∧ g x ≠ -x := by
  classical
  have hB0 : (B (0 : V)) (0 : V) = (0 : ZMod 3) := by simp
  have hx_ne : x ≠ 0 := by
    intro h0
    rw [h0, hB0] at hx
    exact (by decide : ¬((0 : ZMod 3) = 2)) hx
  have horb : Nat.card (MulAction.orbit (e6Weyl hα) x) = 72 := by
    rcases orbit_cases hP hV hB hα hx_ne with ⟨h, hn⟩ | ⟨h, hn⟩ | ⟨h, hn⟩
    · exact hn
    · rw [hx] at h
      exact absurd h (by decide)
    · rw [hx] at h
      exact absurd h (by decide)
  by_contra hcon
  have hcon' : ∀ g ∈ e6Weyl hα, g x ≠ x → g x = -x := by
    intro g hg hgx
    by_contra hneg
    exact hcon ⟨g, hg, hgx, hneg⟩
  have hsub : MulAction.orbit (e6Weyl hα) x ⊆ ({x, -x} : Set V) := by
    intro y hy
    obtain ⟨g, -, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    have hgx : (g : V ≃ₗ[ZMod 3] V) x = x ∨ (g : V ≃ₗ[ZMod 3] V) x = -x := by
      by_cases h : (g : V ≃ₗ[ZMod 3] V) x = x
      · exact Or.inl h
      · exact Or.inr (hcon' g g.2 h)
    simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hgx
  have hpair : ({x, -x} : Set V).ncard ≤ 2 := by
    by_cases h : x = -x
    · rw [show -x = x from h.symm]
      simp
    · rw [Set.ncard_pair h]
  have hle : Nat.card (MulAction.orbit (e6Weyl hα) x) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit (e6Weyl hα) x).ncard
        ≤ ({x, -x} : Set V).ncard := Set.ncard_le_ncard hsub
      _ ≤ 2 := hpair
  omega

end CFSG.StandardType.E6QTwo

end
