module

public import CFSG.Quasithin.H13.L32A773a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem L_le_normalizer_V : L ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_left.trans (C.hMod G T L V C.hyp.hyp C.hyp.fsu).2.2.1

theorem pCoreOf_eq : pCoreOf 2 L = L ⊓ Subgroup.centralizer (V : Set G) := by
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  exact (C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2).cent_eq.symm

theorem mem_v_of_comm_mem {s : G} (hs : s ∈ sL T L V)
    (hsL : ∀ l ∈ L, l * s * l⁻¹ * s⁻¹ ∈ V) : s ∈ V := by
  have hLV := C.L_le_normalizer_V
  have hSV := C.sL_le_normalizer
  let N : Subgroup G :=
    { carrier := {s | s ∈ sL T L V ∧ ∀ l ∈ L, l * s * l⁻¹ * s⁻¹ ∈ V}
      one_mem' := ⟨one_mem _, fun l _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun l hl => by
        rw [show l * (a * b) * l⁻¹ * (a * b)⁻¹ =
          (l * a * l⁻¹ * a⁻¹) * (a * (l * b * l⁻¹ * b⁻¹) * a⁻¹) by group]
        exact mul_mem (ha.2 l hl) ((Subgroup.mem_normalizer_iff.mp (hSV ha.1) _).mp (hb.2 l hl))⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun l hl => by
        rw [show l * a⁻¹ * l⁻¹ * a⁻¹⁻¹ = a⁻¹ * (l * a * l⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group]
        exact (Subgroup.mem_normalizer_iff.mp (hSV (inv_mem ha.1)) _).mp
          (inv_mem (ha.2 l hl))⟩ }
  have hVN : V ≤ N := fun v hv => ⟨v_le_fsuU.trans (le_conjClosure _ _) hv, fun l hl =>
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp hv) (inv_mem hv)⟩
  have hNL : L ≤ Subgroup.normalizer (N : Set G) := le_normalizer_of_conj_mem' fun l hl n hn =>
    ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hl) n).mp hn.1,
      fun l' hl' => by
        have h1 := hn.2 (l⁻¹ * l' * l) (mul_mem (mul_mem (inv_mem hl) hl') hl)
        have h2 := (Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp h1
        rwa [show l * (l⁻¹ * l' * l * n * (l⁻¹ * l' * l)⁻¹ * n⁻¹) * l⁻¹ =
          l' * (l * n * l⁻¹) * l'⁻¹ * (l * n * l⁻¹)⁻¹ by group] at h2⟩
  by_contra hsV
  have hNe : N ≠ V := fun h => hsV (h ▸ (⟨hs, hsL⟩ : s ∈ N))
  have hNS := C.eq_sL_of C.u0_eq C.vh63 C.vh65 C.l71 hVN (fun n hn => hn.1) hNL hNe
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU C.u0_eq
  have huN : u ∈ N := by
    rw [hNS]
    exact le_conjClosure _ _ hu
  exact C.comm_not_mem C.u0_eq hxL1 hx3 hx1 hu huV (huN.2 x hxL)

theorem pCoreOf_le_pCoreOf_sup : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 L)
      (F7.le_normalizer_pCoreOf_of_le_normalizer (C.hyp.normalizes C.h13322)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem comm_mem_sL_of_mem_pCoreOf {p l : G} (hp : p ∈ pCoreOf 2 L) (hl : l ∈ L) :
    l * p * l⁻¹ * p⁻¹ ∈ sL T L V := by
  have h := (C.l71 G T L V C.hyp).2.2
    (Subgroup.commutator_mem_commutator (C.pCoreOf_le_pCoreOf_sup hp) hl)
  have := inv_mem h
  rwa [commutatorElement_def, show (p * l * p⁻¹ * l⁻¹)⁻¹ = l * p * l⁻¹ * p⁻¹ by group] at this

theorem comm_mem_v_sL {p s : G} (hp : p ∈ pCoreOf 2 L) (hs : s ∈ sL T L V) :
    p * s * p⁻¹ * s⁻¹ ∈ V := by
  rw [C.pCoreOf_eq] at hp
  exact C.comm_mem_of_mem_centralizer C.u0_eq (Subgroup.mem_inf.mp hp).1
    (Subgroup.mem_inf.mp hp).2 hs

theorem comm_v_pCoreOf {p v : G} (hp : p ∈ pCoreOf 2 L) (hv : v ∈ V) : p * v = v * p := by
  rw [C.pCoreOf_eq] at hp
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hp).2 v hv).symm

theorem comm_mem_v_of_mem_pCoreOf {p p' : G} (hp : p ∈ pCoreOf 2 L) (hp' : p' ∈ pCoreOf 2 L) :
    p * p' * p⁻¹ * p'⁻¹ ∈ V := by
  have hPL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hc : p * p' * p⁻¹ * p'⁻¹ ∈ sL T L V := C.comm_mem_sL_of_mem_pCoreOf hp' (hPL hp)
  refine C.mem_v_of_comm_mem hc fun l hl => ?_
  set c := p * p' * p⁻¹ * p'⁻¹ with hcdef
  set a := l * p * l⁻¹ * p⁻¹ with ha
  set b := l * p' * l⁻¹ * p'⁻¹ with hb
  have haS : a ∈ sL T L V := C.comm_mem_sL_of_mem_pCoreOf hp hl
  have hbS : b ∈ sL T L V := C.comm_mem_sL_of_mem_pCoreOf hp' hl
  have haP : a ∈ pCoreOf 2 L := C.sL_le_pCoreOf_L C.u0_eq haS
  have hbP : b ∈ pCoreOf 2 L := C.sL_le_pCoreOf_L C.u0_eq hbS
  have hlp : l * p * l⁻¹ = a * p := by rw [ha]; group
  have hlp' : l * p' * l⁻¹ = b * p' := by rw [hb]; group
  have hq : p * p' * p⁻¹ ∈ pCoreOf 2 L := mul_mem (mul_mem hp hp') (inv_mem hp)
  set v₁ := p * b * p⁻¹ * b⁻¹ with hv₁
  have hv₁V : v₁ ∈ V := C.comm_mem_v_sL hp hbS
  set v₂ := (p * p' * p⁻¹) * a⁻¹ * (p * p' * p⁻¹)⁻¹ * a⁻¹⁻¹ with hv₂
  have hv₂V : v₂ ∈ V := C.comm_mem_v_sL hq (inv_mem haS)
  have hac : a⁻¹ * c ∈ sL T L V := mul_mem (inv_mem haS) hc
  set v₃ := b * (a⁻¹ * c) * b⁻¹ * (a⁻¹ * c)⁻¹ with hv₃
  have hv₃V : v₃ ∈ V := C.comm_mem C.u0_eq hbS hac
  have h1 : p * b = v₁ * b * p := by rw [hv₁]; group
  have h2 : (p * p' * p⁻¹) * a⁻¹ = v₂ * a⁻¹ * (p * p' * p⁻¹) := by rw [hv₂]; group
  have h3 : b * (a⁻¹ * c) * b⁻¹ = v₃ * (a⁻¹ * c) := by rw [hv₃]; group
  have h4 : b * v₂ = v₂ * b := C.comm_v_pCoreOf hbP hv₂V
  have h5 : a * (v₁ * v₂ * v₃) = (v₁ * v₂ * v₃) * a :=
    C.comm_v_pCoreOf haP (mul_mem (mul_mem hv₁V hv₂V) hv₃V)
  have e : l * c * l⁻¹ = v₁ * v₂ * v₃ * c := by
    calc l * c * l⁻¹ = (l * p * l⁻¹) * (l * p' * l⁻¹) * (l * p * l⁻¹)⁻¹ *
          (l * p' * l⁻¹)⁻¹ := by rw [hcdef]; group
      _ = (a * p) * (b * p') * (a * p)⁻¹ * (b * p')⁻¹ := by rw [hlp, hlp']
      _ = a * (p * b) * p' * p⁻¹ * a⁻¹ * p'⁻¹ * b⁻¹ := by group
      _ = a * (v₁ * b * p) * p' * p⁻¹ * a⁻¹ * p'⁻¹ * b⁻¹ := by rw [h1]
      _ = a * v₁ * b * ((p * p' * p⁻¹) * a⁻¹) * p'⁻¹ * b⁻¹ := by group
      _ = a * v₁ * b * (v₂ * a⁻¹ * (p * p' * p⁻¹)) * p'⁻¹ * b⁻¹ := by rw [h2]
      _ = a * v₁ * (b * v₂) * (a⁻¹ * c) * b⁻¹ := by rw [hcdef]; group
      _ = a * v₁ * (v₂ * b) * (a⁻¹ * c) * b⁻¹ := by rw [h4]
      _ = a * v₁ * v₂ * (b * (a⁻¹ * c) * b⁻¹) := by group
      _ = a * v₁ * v₂ * (v₃ * (a⁻¹ * c)) := by rw [h3]
      _ = a * (v₁ * v₂ * v₃) * a⁻¹ * c := by group
      _ = (v₁ * v₂ * v₃) * a * a⁻¹ * c := by rw [h5]
      _ = v₁ * v₂ * v₃ * c := by group
  rw [e, show v₁ * v₂ * v₃ * c * c⁻¹ = v₁ * v₂ * v₃ by group]
  exact mul_mem (mul_mem hv₁V hv₂V) hv₃V

end Ctx73

end CFSG.Quasithin.H13.L32A
