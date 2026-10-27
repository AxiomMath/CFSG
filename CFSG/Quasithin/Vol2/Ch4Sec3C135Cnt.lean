module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Rep
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Tri
public import CFSG.Quasithin.Vol2.Ch4Sec3C135VEl

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} (H : Hyp135 G₀ L α)

@[expose] noncomputable def qU : QC (centerOf (c134Q G₀ L)) ⊥ F where
  κ u := crd H.nat u 0
  mul u v := by rw [crd_mul]; rfl
  surj v := by
    obtain ⟨u, hu⟩ := crd_surjective H.nat (fun _ => v)
    exact ⟨u, by show crd H.nat u 0 = v; rw [hu]⟩
  ker u := by
    rw [← crd_eq_zero_iff H.nat]
    constructor
    · intro h
      funext i
      rw [Subsingleton.elim i 0]
      exact h
    · intro h
      rw [h]
      rfl

theorem qU_κ (u : ↥(centerOf (c134Q G₀ L))) : H.qU.κ u = crd H.nat u 0 := rfl

theorem qU_injective : Function.Injective H.qU.κ := fun u v h => by
  rw [QC.κ_eq_iff, Subgroup.mem_bot] at h
  have h1 : u⁻¹ * v = 1 := Subtype.ext h
  exact inv_mul_eq_one.mp h1

theorem qU_nat (g : ↥L) (u : ↥(centerOf (c134Q G₀ L))) :
    H.qU.κ (cnj (H.le_normalizer_U (H.le g.2)) u) =
      ((slNat α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ H.qU.κ u := by
  rw [qU_κ, qU_κ, crd_conj_false H.nat g u _ rfl]
  rfl

namespace Adapted

variable {H} (C : H.Adapted)

@[expose] noncomputable def qW : QC C.W (centerOf (c134Q G₀ L)) F where
  κ := C.eW
  mul := C.eW_mul
  surj := C.eW_surj
  ker w := ⟨C.mem_U_of_eW, fun h => by
    show C.e (C.wQ w) 0 = 0
    rw [(C.ker (C.wQ w)).mpr h]
    rfl⟩

@[expose] noncomputable def q2 : QC (c134Q G₀ L) C.W F where
  κ q := C.e q 1
  mul q q' := by rw [C.mul]; rfl
  surj v := by
    obtain ⟨q, hq⟩ := C.surj (fun i => if i = 0 then 0 else v)
    exact ⟨q, by show C.e q 1 = v; rw [hq]; simp⟩
  ker q := (C.mem_W_iff q).symm

theorem qW_nat (g : ↥L) (w : ↥C.W) :
    C.qW.κ (cnj (C.le_normalizer_W g.2) w) =
      ((dualHom (slNat α g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        C.qW.κ w :=
  C.eW_cnj g w

theorem q2_nat (g : ↥L) (q : ↥(c134Q G₀ L)) :
    C.q2.κ (cnj (H.le_normalizer_Q (H.le g.2)) q) =
      ((dualHom (slNat α g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        C.q2.κ q :=
  C.e_cnj_one g q

end Adapted

end Hyp135

theorem le_normalizer_bot (A : Subgroup G) : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
  fun g _ => Subgroup.mem_normalizer_iff.mpr fun h => by
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h1
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [this, h1]
      group

theorem semi_eq_one {f : Equiv.Perm (Fin 3 → F)} (hadd : ∀ v w, f (v + w) = f v + f w)
    {σ : F ≃+* F} (hσ : ∀ (c : F) v, f (c • v) = σ c • f v)
    (hlin : ∀ (c : F) v, f (c • v) = c • f v) : σ = 1 := by
  have e0 : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h => by simpa using congrFun h 0
  have hz : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hne : f (Pi.single 0 1) ≠ 0 := fun h => e0 (f.injective (h.trans hz.symm))
  refine RingEquiv.ext fun c => ?_
  have h1 := (hσ c (Pi.single 0 1)).symm.trans (hlin c (Pi.single 0 1))
  exact smul_left_injective F hne h1

namespace Hyp135.Adapted

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {H : Hyp135 G₀ L α} (C : H.Adapted)

theorem offender [Finite G] [Finite F] [CharP F 2] (hTQ : ¬ pCoreOf 2 G₀ ≤ c134Q G₀ L)
    {A : Subgroup G} (hAG : A ≤ G₀) (hA : IsElemAbelian 2 A)
    (hne : (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range ≠ ⊥) :
    Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
        Nat.card F * Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U)
          (le_normalizer_bot A))) *
        Nat.card (fixAll (C.qW.rep (hAG.trans (C.le_normalizer_W_of_ne hTQ))
          (hAG.trans H.le_normalizer_U))) < 2 * Nat.card F ^ 6 ∧
      Nat.card (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A)).range *
        Nat.card (fixAll (H.qU.rep (hAG.trans H.le_normalizer_U) (le_normalizer_bot A))) *
        Nat.card (fixAll (C.q2.rep (hAG.trans H.le_normalizer_Q)
          (hAG.trans (C.le_normalizer_W_of_ne hTQ)))) < 2 * Nat.card F ^ 6 := by
  have hAU := hAG.trans H.le_normalizer_U
  have hAb := le_normalizer_bot A
  have hAW := hAG.trans (C.le_normalizer_W_of_ne hTQ)
  have hAQ := hAG.trans H.le_normalizer_Q
  have hAL := hAG.trans H.norm
  have hLU : L ≤ Subgroup.normalizer (centerOf (c134Q G₀ L) : Set G) :=
    H.le.trans H.le_normalizer_U
  have hLW : L ≤ Subgroup.normalizer (C.W : Set G) := fun g hg => C.le_normalizer_W hg
  have hLQ : L ≤ Subgroup.normalizer (c134Q G₀ L : Set G) := H.le.trans H.le_normalizer_Q
  have hρ := slNat_surjective H.surj.1
  set ρ₀ := H.qU.rep hAU hAb with hρ₀
  set ρ₁ := C.qW.rep hAW hAU with hρ₁
  set ρ₂ := C.q2.rep hAQ hAW with hρ₂
  have hsq : ∀ x : ↥A, x * x = 1 := fun x => Subtype.ext (by
    have := hA.2 x x.2
    rw [sq] at this
    exact this)
  have hnat₀ : ∀ (g : ↥L) (x : ↥(centerOf (c134Q G₀ L))), H.qU.κ (cnj (hLU g.2) x) =
      ((slNat α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ H.qU.κ x :=
    fun g x => H.qU_nat g x
  have hnat₁ : ∀ (g : ↥L) (x : ↥C.W), C.qW.κ (cnj (hLW g.2) x) =
      ((dualHom (slNat α g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        C.qW.κ x := fun g x => C.qW_nat g x
  have hnat₂ : ∀ (g : ↥L) (x : ↥(c134Q G₀ L)), C.q2.κ (cnj (hLQ g.2) x) =
      ((dualHom (slNat α g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        C.q2.κ x := fun g x => C.q2_nat g x
  have hρd : Function.Surjective (dualHom.comp (slNat α)) := H.ρd_surjective
  choose σ hσ using fun x => H.qU.exists_semi hAU hAb (slNat α) hLU hnat₀ hAL hρ x
  choose σ₁ hσ₁ using fun x => C.qW.exists_semi hAW hAU (dualHom.comp (slNat α)) hLW
    (fun g x => hnat₁ g x) hAL hρd x
  choose σ₂ hσ₂ using fun x => C.q2.exists_semi hAQ hAW (dualHom.comp (slNat α)) hLQ
    (fun g x => hnat₂ g x) hAL hρd x
  refine tri_offender ρ₀ ρ₁ ρ₂ σ σ₁ σ₂ hsq (H.qU.rep_add hAU hAb) (C.qW.rep_add hAW hAU)
    (C.q2.rep_add hAQ hAW) hσ hσ₁ hσ₂ ?_ ?_ ?_ hne
  · intro x hx h1
    apply hx
    refine semi_eq_one (H.qU.rep_add hAU hAb x) (hσ x) ?_
    refine lin_of_dual H.qU C.qW hAU hAb hAW hAU (slNat α) hρ hLU hLW hnat₀ hnat₁ hAL x (hsq x)
      fun c v => ?_
    rw [hσ₁, h1]
    rfl
  · intro x hx h1
    apply hx
    refine semi_eq_one (H.qU.rep_add hAU hAb x) (hσ x) ?_
    refine lin_of_dual H.qU C.q2 hAU hAb hAQ hAW (slNat α) hρ hLU hLQ hnat₀ hnat₂ hAL x (hsq x)
      fun c v => ?_
    rw [hσ₂, h1]
    rfl
  · intro x hx
    have hlin : ∀ (c : F) v, ρ₀ x (c • v) = c • ρ₀ x v := fun c v => by
      rw [hσ, hx]
      rfl
    obtain ⟨P, hP₀, hP₁⟩ := lin_dual H.qU C.qW hAU hAb hAW hAU (slNat α) hρ hLU hLW hnat₀ hnat₁
      hAL x (hsq x) hlin
    obtain ⟨P', hP₀', hP₂⟩ := lin_dual H.qU C.q2 hAU hAb hAQ hAW (slNat α) hρ hLU hLQ hnat₀
      hnat₂ hAL x (hsq x) hlin
    have hPP : P' = P := Subtype.ext (matrix_eq_of_mulVec_eq fun v => by rw [← hP₀', hP₀])
    exact ⟨P, hP₀, hP₁, fun v => by rw [hP₂, hPP]⟩

end Hyp135.Adapted

end CFSG.Quasithin.H13.Ch4.C135

end
