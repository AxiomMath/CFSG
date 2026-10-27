module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

namespace O8Out

open CFSG.EvenSmallLie.OmegaEight
open CFSG.Monster.B.Co2 (Rep getElem!_ofFn_nat)

@[expose] def blk (p : Fin 360) : Fin 3 := ⟨(p : ℕ) / 120, by omega⟩

theorem blk_val (p : Fin 360) : (blk p : ℕ) = (p : ℕ) / 120 := rfl

theorem blk_surjective : Function.Surjective blk := fun k =>
  ⟨⟨120 * k, by omega⟩, Fin.ext (by simp [blk_val])⟩

theorem perm_apply_inv {α : Type*} (g : Equiv.Perm α) (p : α) : g (g⁻¹ p) = p := by
  rw [Equiv.Perm.coe_inv]
  exact g.apply_symm_apply p

theorem perm_inv_apply {α : Type*} (g : Equiv.Perm α) (p : α) : g⁻¹ (g p) = p := by
  rw [Equiv.Perm.coe_inv]
  exact g.symm_apply_apply p

@[expose] def K0 : Subgroup (Equiv.Perm (Fin 360)) where
  carrier := {g | ∀ p, blk (g p) = blk p}
  mul_mem' {g h} hg hh p := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.mul_apply] at hg hh ⊢
    rw [hg, hh]
  one_mem' p := rfl
  inv_mem' {g} hg p := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h := hg (g⁻¹ p)
    rw [perm_apply_inv] at h
    exact h.symm

theorem rho_apply (p : Fin 360) : ((gen 8 p : Fin 360) : ℕ) = ((p : ℕ) + 120) % 360 := by
  rw [← rep_gen (by norm_num : 8 < 10) p]
  exact structure_ok.2 p p.2

theorem rho_inv_apply (p : Fin 360) :
    (((gen 8)⁻¹ p : Fin 360) : ℕ) = ((p : ℕ) + 240) % 360 := by
  have h : gen 8 ⟨((p : ℕ) + 240) % 360, by omega⟩ = p := by
    apply Fin.ext
    rw [rho_apply]
    simp only
    omega
  rw [Equiv.Perm.inv_eq_iff_eq.mpr h.symm]

theorem omegaT_le_K0 : omegaT ≤ K0 := by
  intro g hg p
  have h0 : ∀ x ∈ omegaT, ∀ q : Fin 360, ((q : ℕ) < 120 ↔ ((x q : Fin 360) : ℕ) < 120) :=
    fun x hx q => omegaT_le_stab0 hx q
  have hρA : gen 8 ∈ autT := gen_mem_autT (by norm_num)
  have hconj : ∀ x ∈ omegaT, (gen 8)⁻¹ * x * gen 8 ∈ omegaT := fun x hx => by
    have h := (conj_mem_omegaT (inv_mem hρA)).1 hx
    rwa [inv_inv] at h
  apply Fin.ext
  simp only [blk_val]
  rcases (show (p : ℕ) / 120 = 0 ∨ (p : ℕ) / 120 = 1 ∨ (p : ℕ) / 120 = 2 by omega) with h | h | h
  · have := (h0 g hg p).1 (by omega)
    omega
  ·
    set g₁ := (gen 8)⁻¹ * g * gen 8 with hg₁
    have hg₁m : g₁ ∈ omegaT := hconj g hg
    have hq : (((gen 8)⁻¹ p : Fin 360) : ℕ) < 120 := by rw [rho_inv_apply]; omega
    have h1 := (h0 g₁ hg₁m _).1 hq
    have hgp : g p = gen 8 (g₁ ((gen 8)⁻¹ p)) := by
      rw [hg₁, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_apply_inv, perm_apply_inv]
    rw [hgp, rho_apply]
    omega
  · set g₂ := (gen 8)⁻¹ * ((gen 8)⁻¹ * g * gen 8) * gen 8 with hg₂
    have hg₂m : g₂ ∈ omegaT := hconj _ (hconj g hg)
    have hq : (((gen 8)⁻¹ ((gen 8)⁻¹ p) : Fin 360) : ℕ) < 120 := by
      rw [rho_inv_apply, rho_inv_apply]; omega
    have h1 := (h0 g₂ hg₂m _).1 hq
    have hgp : g p = gen 8 (gen 8 (g₂ ((gen 8)⁻¹ ((gen 8)⁻¹ p)))) := by
      rw [hg₂, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, perm_apply_inv, perm_apply_inv, perm_apply_inv, perm_apply_inv]
    rw [hgp, rho_apply, rho_apply]
    omega

@[expose] def Blk : Subgroup (Equiv.Perm (Fin 360)) where
  carrier := {g | ∃ f : Equiv.Perm (Fin 3), ∀ p, blk (g p) = f (blk p)}
  mul_mem' := by
    rintro g h ⟨f, hf⟩ ⟨f', hf'⟩
    exact ⟨f * f', fun p => by simp only [Equiv.Perm.mul_apply, hf, hf']⟩
  one_mem' := ⟨1, fun _ => rfl⟩
  inv_mem' := by
    rintro g ⟨f, hf⟩
    refine ⟨f⁻¹, fun p => ?_⟩
    have h := hf (g⁻¹ p)
    rw [perm_apply_inv] at h
    rw [h, perm_inv_apply]

theorem genArrs_nine : genArrs[9]! = tauArr := by
  have hlen : rootPairs.length = 8 := rfl
  rw [genArrs, getElem!_pos _ 9 (by simp [hlen]),
    Array.getElem_append_right (by simp [hlen])]
  simp [hlen]

theorem trans_ok : ∀ v < 256, qNat v = true → transNat 136 v < 256 ∧ qNat (transNat 136 v) = true := by
  decide +kernel

theorem tau_blk (p : Fin 360) : blk (gen 9 p) = Equiv.swap 1 2 (blk p) := by
  have hp := rep_gen (by norm_num : 9 < 10) p
  rw [genArrs_nine, tauArr, getElem!_ofFn_nat _ p.2] at hp
  have hj : (p : ℕ) % 120 < 120 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hv1, hv2, -⟩ := ns_ok.2.2.1 _ hj
  obtain ⟨ht1, ht2⟩ := trans_ok _ hv1 hv2
  have hr := (ns_ok.2.2.2 _ ht1 ht2).1
  have hval : ((gen 9 p : Fin 360) : ℕ) / 120 = (3 - (p : ℕ) / 120) % 3 := by
    rw [← hp]
    simp only
    omega
  have hsw : ∀ k : Fin 3, ((Equiv.swap (1 : Fin 3) 2 k : Fin 3) : ℕ) = (3 - (k : ℕ)) % 3 := by
    decide +kernel
  apply Fin.ext
  rw [hsw, blk_val, blk_val, hval]

theorem rho_blk (p : Fin 360) : blk (gen 8 p) = finRotate 3 (blk p) := by
  have hrot : ∀ k : Fin 3, ((finRotate 3 k : Fin 3) : ℕ) = ((k : ℕ) + 1) % 3 := by decide +kernel
  apply Fin.ext
  rw [hrot, blk_val, blk_val, rho_apply]
  omega

theorem omegaT_le_Blk : omegaT ≤ Blk := fun g hg =>
  ⟨1, fun p => by rw [omegaT_le_K0 hg p]; rfl⟩

theorem autT_le_Blk : autT ≤ Blk := by
  rw [autT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  by_cases h8 : i < 8
  · exact omegaT_le_Blk (gen_mem_omegaT h8)
  · by_cases h9 : i = 8
    · subst h9
      exact ⟨finRotate 3, rho_blk⟩
    · obtain rfl : i = 9 := by omega
      exact ⟨Equiv.swap 1 2, tau_blk⟩

noncomputable def copyPerm (g : Blk) : Equiv.Perm (Fin 3) := Classical.choose g.2

theorem copyPerm_spec (g : Blk) (p : Fin 360) :
    blk ((g : Equiv.Perm (Fin 360)) p) = copyPerm g (blk p) :=
  Classical.choose_spec g.2 p

theorem copyPerm_eq (g : Blk) (f : Equiv.Perm (Fin 3))
    (hf : ∀ p, blk ((g : Equiv.Perm (Fin 360)) p) = f (blk p)) : copyPerm g = f := by
  ext k
  obtain ⟨p, rfl⟩ := blk_surjective k
  rw [← copyPerm_spec, hf]

noncomputable def copyHomB : Blk →* Equiv.Perm (Fin 3) where
  toFun := copyPerm
  map_one' := copyPerm_eq 1 1 fun _ => rfl
  map_mul' g h := copyPerm_eq (g * h) (copyPerm g * copyPerm h) fun p => by
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, copyPerm_spec, copyPerm_spec,
      Equiv.Perm.mul_apply]

noncomputable def copyHom : autT →* Equiv.Perm (Fin 3) :=
  copyHomB.comp (Subgroup.inclusion autT_le_Blk)

theorem copyHom_spec (a : autT) (p : Fin 360) :
    blk ((a : Equiv.Perm (Fin 360)) p) = copyHom a (blk p) :=
  copyPerm_spec (Subgroup.inclusion autT_le_Blk a) p

theorem copyHom_eq (a : autT) (f : Equiv.Perm (Fin 3))
    (hf : ∀ p, blk ((a : Equiv.Perm (Fin 360)) p) = f (blk p)) : copyHom a = f :=
  copyPerm_eq (Subgroup.inclusion autT_le_Blk a) f hf

theorem rhoA_val :
    ((⟨gen 8, gen_mem_autT (by norm_num)⟩ : autT) : Equiv.Perm (Fin 360)) = gen 8 := rfl

theorem tauA_val :
    ((⟨gen 9, gen_mem_autT (by norm_num)⟩ : autT) : Equiv.Perm (Fin 360)) = gen 9 := rfl

theorem copyHom_rho : copyHom ⟨gen 8, gen_mem_autT (by norm_num)⟩ = finRotate 3 :=
  copyHom_eq _ _ fun p => by rw [rhoA_val]; exact rho_blk p

theorem copyHom_tau : copyHom ⟨gen 9, gen_mem_autT (by norm_num)⟩ = Equiv.swap 1 2 :=
  copyHom_eq _ _ fun p => by rw [tauA_val]; exact tau_blk p

theorem perm3_cases : ∀ f : Equiv.Perm (Fin 3), f = 1 ∨ f = finRotate 3 ∨
    f = finRotate 3 * finRotate 3 ∨ f = Equiv.swap 1 2 ∨ f = finRotate 3 * Equiv.swap 1 2 ∨
    f = finRotate 3 * finRotate 3 * Equiv.swap 1 2 := by
  decide +kernel

theorem copyHom_surjective : Function.Surjective copyHom := by
  intro f
  set rA : autT := ⟨gen 8, gen_mem_autT (by norm_num)⟩
  set tA : autT := ⟨gen 9, gen_mem_autT (by norm_num)⟩
  rcases perm3_cases f with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨rA, copyHom_rho⟩
  · exact ⟨rA * rA, by rw [map_mul, copyHom_rho]⟩
  · exact ⟨tA, copyHom_tau⟩
  · exact ⟨rA * tA, by rw [map_mul, copyHom_rho, copyHom_tau]⟩
  · exact ⟨rA * rA * tA, by rw [map_mul, map_mul, copyHom_rho, copyHom_tau]⟩

theorem omegaT_le_ker : omegaT.subgroupOf autT ≤ copyHom.ker := by
  intro a ha
  rw [Subgroup.mem_subgroupOf] at ha
  rw [MonoidHom.mem_ker]
  exact copyHom_eq a 1 fun p => by rw [omegaT_le_K0 ha p]; rfl

theorem ker_copyHom : copyHom.ker = omegaT.subgroupOf autT := by
  haveI : Finite autT := Nat.finite_of_card_ne_zero (by rw [card_autT]; norm_num)
  have hcard : Nat.card autT = Nat.card (copyHom.ker) * 6 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup copyHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective copyHom
      copyHom_surjective).toEquiv] at h1
    rw [h1, mul_comm, Nat.card_perm, Nat.card_fin]
    rfl
  have hO : Nat.card (omegaT.subgroupOf autT) = Nat.card omegaT :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe omegaT_le_autT).toEquiv
  refine (Subgroup.eq_of_le_of_card_ge omegaT_le_ker ?_).symm
  rw [hO]
  have h6 := card_autT_eq
  omega

theorem perm3_eq_one : ∀ f : Equiv.Perm (Fin 3), f ^ 3 = 1 → ∀ k, f k = k → f = 1 := by
  decide +kernel

theorem mem_omegaT_of_fix_copy (a : autT) (ha3 : a ^ 3 = 1) (p : Fin 360)
    (hp : blk ((a : Equiv.Perm (Fin 360)) p) = blk p) : (a : Equiv.Perm (Fin 360)) ∈ omegaT := by
  have h1 : copyHom a = 1 := by
    refine perm3_eq_one _ (by rw [← map_pow, ha3, map_one]) (blk p) ?_
    rw [← copyHom_spec, hp]
  have h2 : a ∈ copyHom.ker := h1
  rw [ker_copyHom, Subgroup.mem_subgroupOf] at h2
  exact h2

end O8Out

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
