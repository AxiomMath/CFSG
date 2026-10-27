module

public import CFSG.Sporadic.HNOddCore.RAction
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Equiv

abbrev RV :
    Subgroup RH := MulAction.stabilizer RH x0

theorem jR_mem_RV_iff
    (g : JH) : jR g ∈ RV ↔ g ∈ HJ := by
  rw [MulAction.mem_stabilizer_iff, jR_smul, mem_HJ_iff_fix]

theorem cR_mem_RV :
    cR ∈ RV := cR_smul_x0

theorem jR_mul_cR_mem_RV_iff
    (g : JH) : jR g * cR ∈ RV ↔ g ∈ HJ := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, cR_smul_x0, jR_smul, mem_HJ_iff_fix]

abbrev HR : Subgroup RH := HJ.map jR

theorem mem_RV_iff
    (r : RH) :
    r ∈ RV ↔ (∃ h ∈ HJ, r = jR h) ∨ ∃ h ∈ HJ, r = jR h * cR := by
  constructor
  · intro hr
    rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inl ⟨g, (jR_mem_RV_iff g).1 hr, rfl⟩
    · exact Or.inr ⟨g, (jR_mul_cR_mem_RV_iff g).1 hr, rfl⟩
  · rintro (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
    · exact (jR_mem_RV_iff h).2 hh
    · exact (jR_mul_cR_mem_RV_iff h).2 hh

theorem RV_eq_sup :
    RV = HR ⊔ Subgroup.zpowers cR := by
  apply le_antisymm
  · intro r hr
    rcases (mem_RV_iff r).1 hr with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
    · exact Subgroup.mem_sup_left ⟨h, hh, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h, hh, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers cR))
  · rw [sup_le_iff, Subgroup.zpowers_le]
    refine ⟨?_, cR_mem_RV⟩
    rintro _ ⟨h, hh, rfl⟩
    exact (jR_mem_RV_iff h).2 hh

@[expose] def IsOuter
    (r : RH) : Prop := (r : GL (Fin hnsData.d) (ZMod 5)) ∉ JH

theorem not_isOuter_jR
    (g : JH) : ¬ IsOuter (jR g) := fun h => h (by rw [jR_val]; exact g.2)

theorem isOuter_jR_mul_cR
    (g : JH) : IsOuter (jR g * cR) := fun h =>
  jR_mul_cR_not_mem g ((mem_range_jR_iff _).2 h)

theorem exists_of_not_isOuter
    {r : RH} (h : ¬ IsOuter r) : ∃ g : JH, r = jR g := by
  rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨g, rfl⟩
  · exact absurd (isOuter_jR_mul_cR g) h

theorem exists_of_isOuter
    {r : RH} (h : IsOuter r) : ∃ g : JH, r = jR g * cR := by
  rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact absurd h (not_isOuter_jR g)
  · exact ⟨g, rfl⟩

open Classical in
@[expose] def jPart
    (r : RH) : JH :=
  if h : IsOuter r then Classical.choose (exists_of_isOuter h)
  else Classical.choose (exists_of_not_isOuter h)

theorem jPart_spec_of_not
    {r : RH} (h : ¬ IsOuter r) : r = jR (jPart r) := by
  rw [jPart, dite_eq_right h]
  exact Classical.choose_spec (exists_of_not_isOuter h)

theorem jPart_spec_of_isOuter
    {r : RH} (h : IsOuter r) : r = jR (jPart r) * cR := by
  rw [jPart, dite_eq_left h]
  exact Classical.choose_spec (exists_of_isOuter h)

theorem jPart_jR
    (g : JH) : jPart (jR g) = g :=
  jR_injective (jPart_spec_of_not (not_isOuter_jR g)).symm

theorem jPart_jR_mul_cR
    (g : JH) : jPart (jR g * cR) = g := by
  have := jPart_spec_of_isOuter (isOuter_jR_mul_cR g)
  exact jR_injective (mul_right_cancel this).symm

theorem jPart_mem_HJ
    {r : RH} (hr : r ∈ RV) : jPart r ∈ HJ := by
  rcases (mem_RV_iff r).1 hr with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
  · rwa [jPart_jR]
  · rwa [jPart_jR_mul_cR]

open Classical in
@[expose] def thetaFn
    (r : RH) : Perm (Fin 12) :=
  if hr : r ∈ RV then
    (thetaJ ⟨jPart r, jPart_mem_HJ hr⟩ : Perm (Fin 12)) * if IsOuter r then swap 0 1 else 1
  else 1

theorem thetaFn_jR
    {h : JH} (hh : h ∈ HJ) : thetaFn (jR h) = (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := by
  rw [thetaFn, dite_eq_left ((jR_mem_RV_iff h).2 hh), ite_eq_right (not_isOuter_jR h), mul_one]
  congr 3
  exact jPart_jR h

theorem thetaFn_jR_mul_cR
    {h : JH} (hh : h ∈ HJ) :
    thetaFn (jR h * cR) = (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * swap 0 1 := by
  rw [thetaFn, dite_eq_left ((jR_mul_cR_mem_RV_iff h).2 hh), ite_eq_left (isOuter_jR_mul_cR h)]
  congr 4
  exact jPart_jR_mul_cR h

theorem thetaJ_mul
    (a b : JH) (ha : a ∈ HJ) (hb : b ∈ HJ) :
    (thetaJ ⟨a * b, mul_mem ha hb⟩ : Perm (Fin 12)) =
      (thetaJ ⟨a, ha⟩ : Perm (Fin 12)) * (thetaJ ⟨b, hb⟩ : Perm (Fin 12)) := by
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

theorem thetaJ_conjC
    (b : JH) (hb : b ∈ HJ) :
    (thetaJ ⟨conjC b, conjC_mem_HJ hb⟩ : Perm (Fin 12)) =
      swap 0 1 * (thetaJ ⟨b, hb⟩ : Perm (Fin 12)) * swap 0 1 :=
  thetaJ_conjCH ⟨b, hb⟩

theorem thetaJ_one :
    (thetaJ ⟨1, one_mem _⟩ : Perm (Fin 12)) = 1 := by
  rw [show (⟨1, one_mem _⟩ : HJ) = 1 from rfl, map_one, Subgroup.coe_one]

theorem swap01_mul_self : swap (0 : Fin 12) 1 * swap 0 1 = 1 := swap_mul_self 0 1

theorem thetaFn_mul
    {r s : RH} (hr : r ∈ RV) (hs : s ∈ RV) :
    thetaFn (r * s) = thetaFn r * thetaFn s := by
  rcases (mem_RV_iff r).1 hr with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    rcases (mem_RV_iff s).1 hs with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · rw [← map_mul, thetaFn_jR (mul_mem ha hb), thetaFn_jR ha, thetaFn_jR hb, thetaJ_mul]
  · rw [← mul_assoc, ← map_mul, thetaFn_jR_mul_cR (mul_mem ha hb), thetaFn_jR ha,
      thetaFn_jR_mul_cR hb, thetaJ_mul, mul_assoc]
  · have hcb := conjC_mem_HJ hb
    rw [mul_assoc, cR_mul_jR, ← mul_assoc, ← map_mul, thetaFn_jR_mul_cR (mul_mem ha hcb),
      thetaFn_jR_mul_cR ha, thetaFn_jR hb, thetaJ_mul a (conjC b) ha hcb, thetaJ_conjC b hb]
    simp only [mul_assoc, swap01_mul_self, mul_one]
  · have hcb := conjC_mem_HJ hb
    rw [show jR a * cR * (jR b * cR) = jR (a * conjC b) by
      rw [← mul_assoc, mul_assoc (jR a), cR_mul_jR, map_mul, ← mul_assoc, mul_assoc _ cR,
        cR_mul_self, mul_one], thetaFn_jR (mul_mem ha hcb), thetaFn_jR_mul_cR ha,
      thetaFn_jR_mul_cR hb, thetaJ_mul a (conjC b) ha hcb, thetaJ_conjC b hb]
    simp only [mul_assoc]

@[expose] def thetaRHom :
    RV →* Perm (Fin 12) where
  toFun r := thetaFn r
  map_one' := by
    rw [Subgroup.coe_one, ← map_one jR, thetaFn_jR (one_mem _), thetaJ_one]
  map_mul' r s := by
    rw [Subgroup.coe_mul]
    exact thetaFn_mul r.2 s.2

theorem thetaRHom_apply
    (r : RV) : thetaRHom r = thetaFn r := rfl

theorem thetaRHom_jR
    {h : JH} (hh : h ∈ HJ) :
    thetaRHom ⟨jR h, (jR_mem_RV_iff h).2 hh⟩ = (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := by
  rw [thetaRHom_apply, Subtype.coe_mk, thetaFn_jR hh]

theorem thetaRHom_cR :
    thetaRHom ⟨cR, cR_mem_RV⟩ = swap 0 1 := by
  rw [thetaRHom_apply, Subtype.coe_mk, ← one_mul cR, ← map_one jR, thetaFn_jR_mul_cR (one_mem _),
    thetaJ_one, one_mul]

theorem swap01_not_mem : swap (0 : Fin 12) 1 ∉ alternatingGroup (Fin 12) := tau_not_mem

theorem thetaRHom_injective :
    Function.Injective thetaRHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨r, hr⟩ hk
  rw [MonoidHom.mem_ker, thetaRHom_apply, Subtype.coe_mk] at hk
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Subtype.coe_mk, Subgroup.coe_one]
  rcases (mem_RV_iff r).1 hr with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [thetaFn_jR ha] at hk
    have h1 : thetaJ ⟨a, ha⟩ = 1 := Subtype.ext hk
    rw [← map_one thetaJ] at h1
    have h2 : a = 1 := congrArg Subtype.val (thetaJ.injective h1)
    rw [h2, map_one]
  · rw [thetaFn_jR_mul_cR ha] at hk
    exfalso
    have h3 : (thetaJ ⟨a, ha⟩ : Perm (Fin 12)) = swap 0 1 := by
      rw [← mul_one (thetaJ ⟨a, ha⟩ : Perm (Fin 12)), ← swap01_mul_self, ← mul_assoc, hk,
        one_mul]
    exact swap01_not_mem (h3 ▸ (thetaJ ⟨a, ha⟩).2)

theorem alt_le_range :
    alternatingGroup (Fin 12) ≤ thetaRHom.range := by
  intro σ hσ
  obtain ⟨⟨h, hh⟩, he⟩ := thetaJ.surjective ⟨σ, hσ⟩
  refine ⟨⟨jR h, (jR_mem_RV_iff h).2 hh⟩, ?_⟩
  rw [thetaRHom_jR hh, he]

theorem thetaRHom_surjective :
    Function.Surjective thetaRHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro σ _
  have hτ : swap (0 : Fin 12) 1 ∈ thetaRHom.range := ⟨_, thetaRHom_cR⟩
  by_cases hσ : σ ∈ alternatingGroup (Fin 12)
  · exact alt_le_range hσ
  · have h1 : σ * swap 0 1 ∈ alternatingGroup (Fin 12) := by
      rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide)]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hσ
      · rw [h]
        decide
    have := mul_mem (alt_le_range h1) hτ
    rwa [mul_assoc, swap01_mul_self, mul_one] at this

@[expose] def thetaR :
    RV ≃* Perm (Fin 12) :=
  MulEquiv.ofBijective thetaRHom ⟨thetaRHom_injective, thetaRHom_surjective⟩

theorem thetaR_apply
    (r : RV) : thetaR r = thetaRHom r := rfl

theorem thetaR_jR
    {h : JH} (hh : h ∈ HJ) :
    thetaR ⟨jR h, (jR_mem_RV_iff h).2 hh⟩ = (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) :=
  thetaRHom_jR hh

theorem thetaR_cR :
    thetaR ⟨cR, cR_mem_RV⟩ = swap 0 1 := thetaRHom_cR

theorem card_RV :
    Nat.card RV = Nat.factorial 12 := by
  rw [Nat.card_congr thetaR.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.Sporadic.HNOddCore
