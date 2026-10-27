module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Br

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

structure LabHyp (L : ZLab Γ G) : Prop where
  prod : ∀ β a b c : V, valence Γ β = 3 → Γ.neighborSet β = {a, b, c} → a ≠ b → a ≠ c → b ≠ c →
    L.z a * L.z b * L.z c = 1
  ker : ∀ δ l : V, valence Γ δ = 5 → Γ.dist δ l = 2 → L.z l ∈ nbrStab Γ G δ
  dist : ∀ l d : V, l ≠ d → valence Γ l = 5 → valence Γ d = 5 →
    (Γ.dist l d = 2 ∨ Γ.dist l d = 4) → L.z l ≠ L.z d
  triple : ∀ δ l₁ l₂ l₃ : V, valence Γ δ = 5 → Γ.dist δ l₁ = 2 → Γ.dist δ l₂ = 2 →
    Γ.dist δ l₃ = 2 → L.z l₁ * L.z l₂ * L.z l₃ ∉ Subgroup.zpowers (L.z δ)

@[expose] def NC (L : ZLab Γ G) (l m : V) : Prop := L.z l * L.z m ≠ L.z m * L.z l

variable {L : ZLab Γ G} {v : V}

theorem NC.symm {l m : V} (h : NC L l m) : NC L m l := fun e => h e.symm

theorem z_sq (hv : valence Γ v = 5) : L.z v * L.z v = 1 := (L.isCentral v hv).2.2.1

theorem z_inv (hv : valence Γ v = 5) : (L.z v)⁻¹ = L.z v :=
  inv_eq_of_mul_eq_one_right (z_sq hv)

theorem z_ne_one (hv : valence Γ v = 5) : L.z v ≠ 1 := (L.isCentral v hv).2.1

theorem z_comm (hv : valence Γ v = 5) {g : G} (hg : g ∈ MulAction.stabilizer G v) :
    g * L.z v = L.z v * g := (L.isCentral v hv).2.2.2 g hg

theorem z_smul (hv : valence Γ v = 5) (g : G) : L.z (g • v) = g * L.z v * g⁻¹ :=
  L.equivariant g v hv

theorem NC.smul {l m : V} (hl : valence Γ l = 5) (hm : valence Γ m = 5) (g : G) :
    NC L (g • l) (g • m) ↔ NC L l m := by
  unfold NC
  rw [z_smul hl, z_smul hm]
  constructor
  · intro h e
    apply h
    calc g * L.z l * g⁻¹ * (g * L.z m * g⁻¹) = g * (L.z l * L.z m) * g⁻¹ := by group
      _ = g * (L.z m * L.z l) * g⁻¹ := by rw [e]
      _ = g * L.z m * g⁻¹ * (g * L.z l * g⁻¹) := by group
  · intro h e
    apply h
    have := congrArg (fun y => g⁻¹ * y * g) e
    simpa [mul_assoc] using this

variable (F : FanTree Γ G) (H : LabHyp L)
include F H

theorem sib_label {d ν l l' : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) (h' : Br Γ d ν l')
    (hne : l ≠ l') : L.z l' = L.z l * L.z d := by
  obtain ⟨l'', hl'', hne'', hset⟩ := exists_sibling F hd h
  have hl'l' : l'' = l' := by
    have hmem : l' ∈ Γ.neighborSet ν := h'.2.1
    rw [hset] at hmem
    rcases hmem with e | e | e
    · exact absurd e h'.2.2
    · exact absurd e.symm hne
    · exact e.symm
  subst hl'l'
  have hp := H.prod ν d l l'' (Br.valence F hd h).1 hset h.2.2.symm hl''.2.2.symm hne''.symm
  have hvl := (Br.valence F hd h).2
  have hvl' := (Br.valence F hd hl'').2
  have e1 : L.z l'' = (L.z d * L.z l)⁻¹ := eq_inv_of_mul_eq_one_right hp
  rw [e1, mul_inv_rev, z_inv hd, z_inv hvl]

theorem z_comm_dist {d l : V} (hd : valence Γ d = 5) (hl : Γ.dist d l = 2) :
    L.z l * L.z d = L.z d * L.z l :=
  z_comm hd (F.nbrStab_le_stabilizer d (H.ker d l hd hl))

theorem nc_iff {d ν l m : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) (hm : Γ.dist d m = 2) :
    NC L l m ↔ L.z m • l ≠ l := by
  obtain ⟨μ, hμ⟩ := exists_br F hm
  have hvl := (Br.valence F hd h).2
  have hvm := (Br.valence F hd hμ).2
  have hkl : Br Γ d ν (L.z m • l) := Br.of_mem_nbrStab F (H.ker d m hd hm) h
  have hz := z_smul (L := L) hvl (L.z m)
  rw [z_inv hvm] at hz
  constructor
  · intro hnc hfix
    rw [hfix] at hz
    apply hnc
    calc L.z l * L.z m = (L.z m * L.z l * L.z m) * L.z m := by rw [← hz]
      _ = L.z m * L.z l := by rw [mul_assoc, z_sq hvm, mul_one]
  · intro hmove hcomm
    have hs := sib_label F H hd h hkl hmove.symm
    rw [hz] at hs
    have h1 : L.z m * L.z l * L.z m = L.z l := by
      rw [← hcomm, mul_assoc, z_sq hvm, mul_one]
    rw [h1] at hs
    exact z_ne_one hd (by simpa using hs)

theorem swap_conj {d ν l m : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) (hm : Γ.dist d m = 2)
    (hne : L.z m • l ≠ l) : L.z m * L.z l * L.z m = L.z l * L.z d := by
  obtain ⟨μ, hμ⟩ := exists_br F hm
  have hvl := (Br.valence F hd h).2
  have hvm := (Br.valence F hd hμ).2
  have hkl : Br Γ d ν (L.z m • l) := Br.of_mem_nbrStab F (H.ker d m hd hm) h
  have hs := sib_label F H hd h hkl hne.symm
  rw [z_smul hvl (L.z m), z_inv hvm] at hs
  exact hs

theorem nc_sq {d l m : V} (hd : valence Γ d = 5) (hl : Γ.dist d l = 2) (hm : Γ.dist d m = 2)
    (hnc : NC L l m) : (L.z l * L.z m) * (L.z l * L.z m) = L.z d := by
  obtain ⟨ν, hν⟩ := exists_br F hl
  have hvl := (Br.valence F hd hν).2
  have hmove := (nc_iff F H hd hν hm).1 hnc
  have hc := swap_conj F H hd hν hm hmove
  calc L.z l * L.z m * (L.z l * L.z m) = L.z l * (L.z m * L.z l * L.z m) := by
        simp only [mul_assoc]
    _ = L.z d := by rw [hc, ← mul_assoc, z_sq hvl, one_mul]

theorem nc_br {d ν l l' m : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) (h' : Br Γ d ν l')
    (hm : Γ.dist d m = 2) : NC L l m ↔ NC L l' m := by
  by_cases hll : l = l'
  · subst hll
    exact Iff.rfl
  · have hs := sib_label F H hd h h' hll
    have hc := (z_comm_dist F H hd hm).symm
    have e1 : L.z l * L.z d * L.z m = L.z l * L.z m * L.z d := by
      rw [mul_assoc, hc, ← mul_assoc]
    have e2 : L.z m * (L.z l * L.z d) = L.z m * L.z l * L.z d := by rw [mul_assoc]
    unfold NC
    rw [hs, e1, e2]
    exact (mul_left_inj (L.z d)).not.symm

theorem br_ne_of_nc {d ν ν' l m : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) (h' : Br Γ d ν' m)
    (hnc : NC L l m) : ν ≠ ν' := by
  rintro rfl
  have := (nc_br F H hd h' h (Br.dist_two F h)).1 hnc.symm
  exact this rfl

end P62

end CFSG.Quasithin.Fan86
