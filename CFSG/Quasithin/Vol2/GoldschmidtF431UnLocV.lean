module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocLift
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdBase

public section

namespace CFSG.Quasithin.H13.F431.Un

set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift

section V

variable {D C : Type} [Group D] [Finite D] [Group C] (A : LieAmalgamExt D)
  (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
  (ε : D ≃* C) (hodd : ¬ 2 ∣ (iK A hgen).range.index)
  {NQ : Subgroup ↥A.K} {Q : Subgroup D}
  (hNQ : NQ ⊓ (iK A hgen).range = Q.map (iK A hgen))

include hcen hodd hNQ in
theorem perfectCore_eq_map_of_inf : perfectCore NQ = (perfectCore Q).map (iK A hgen) := by
  have := range_normal A hgen
  have hodd' : Odd (iK A hgen).range.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  rw [perfectCore_eq_inf_of_odd (Inn := (iK A hgen).range) NQ hodd', hNQ,
    perfectCore_map_of_injective _ (iK_injective A hgen hcen)]

include hcen hodd hNQ in
theorem pCoreOf_eq_map_of_inf : pCoreOf 2 NQ = (pCoreOf 2 Q).map (iK A hgen) := by
  have := range_normal A hgen
  have hodd' : Odd (iK A hgen).range.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  rw [pCoreOf_eq_inf_of_odd (Inn := (iK A hgen).range) NQ hodd', hNQ,
    pCoreOf_map_of_injective _ (iK_injective A hgen hcen)]

variable {U P P' : Subgroup C} {z t : C} {V4 : Subgroup C} (SV : UnStdV C U P P' z t V4)
  (hQP : Q.map ε.toMonoidHom = P) (hU : A.TD.map ε.toMonoidHom = U)

include hcen hodd hNQ SV hQP in
theorem lamK_z_mem_centerOf_perfectCore : lamK A hgen ε z ∈ centerOf (perfectCore NQ) := by
  have hperf : perfectCore P = (perfectCore Q).map ε.toMonoidHom := by
    rw [← hQP]
    exact perfectCore_map_of_injective ε.toMonoidHom ε.injective Q
  have hcenter : centerOf (perfectCore P) = (centerOf (perfectCore Q)).map ε.toMonoidHom := by
    rw [hperf]
    exact centerOf_map_of_injective ε.toMonoidHom ε.injective _
  have h1 := SV.z_ZP
  rw [hcenter] at h1
  have h2 : ε.symm z ∈ centerOf (perfectCore Q) := by
    obtain ⟨x, hx, hxz⟩ := h1
    have : ε.symm z = x := by rw [← hxz]; simp
    rwa [this]
  rw [perfectCore_eq_map_of_inf A hgen hcen hodd hNQ, centerOf_map_of_injective _
    (iK_injective A hgen hcen)]
  exact ⟨ε.symm z, h2, rfl⟩

include hU in
theorem lamK_map_U : U.map (lamK A hgen ε) = A.TD.map (iK A hgen) := by
  have hTD : A.TD = U.map ε.symm.toMonoidHom := (map_symm_eq_of_map_eq ε hU).symm
  rw [hTD, Subgroup.map_map]
  rfl

include hU SV in
theorem lamK_V4_le : V4.map (lamK A hgen ε) ≤ A.TD.map (iK A hgen) := by
  rw [← lamK_map_U A hgen ε hU]
  exact Subgroup.map_mono SV.V4_le

include SV in
theorem lamK_V4_ab : ∀ a ∈ V4.map (lamK A hgen ε), ∀ b ∈ V4.map (lamK A hgen ε), a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, SV.V4_ab a ha b hb]

include SV in
theorem lamK_V4_sq : ∀ a ∈ V4.map (lamK A hgen ε), a ^ 2 = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, SV.V4_sq a ha, map_one]

variable {NQ' : Subgroup ↥A.K} {Q' : Subgroup D}

include hcen hodd SV in
theorem lamK_V4_eq (hNQ' : NQ' ⊓ (iK A hgen).range = Q'.map (iK A hgen))
    (hQP' : Q'.map ε.toMonoidHom = P') :
    V4.map (lamK A hgen ε) = centerOf (pCoreOf 2 NQ') := by
  have h1 : pCoreOf 2 P' = (pCoreOf 2 Q').map ε.toMonoidHom := by
    rw [← hQP']
    exact pCoreOf_map_of_injective _ ε.injective Q'
  have h2 : V4 = (centerOf (pCoreOf 2 Q')).map ε.toMonoidHom := by
    rw [SV.V4_eq, h1]
    exact centerOf_map_of_injective _ ε.injective _
  have h3 : V4.map ε.symm.toMonoidHom = centerOf (pCoreOf 2 Q') := by
    rw [h2, Subgroup.map_map]
    have : ε.symm.toMonoidHom.comp ε.toMonoidHom = MonoidHom.id D := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rw [pCoreOf_eq_map_of_inf A hgen hcen hodd hNQ',
    centerOf_map_of_injective _ (iK_injective A hgen hcen), ← h3, Subgroup.map_map]
  rfl

include hcen hU SV in
theorem lamK_V4_unique (E : Subgroup ↥A.K) (hE : E ≤ A.TD.map (iK A hgen))
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1)
    (hcard : Nat.card E = Nat.card (V4.map (lamK A hgen ε))) : E = V4.map (lamK A hgen ε) := by
  have hinj := lamK_injective (A := A) (hgen := hgen) (ε := ε) hcen
  set lam := lamK A hgen ε with hlam
  have hEU : E ≤ U.map lam := by
    rw [hlam, lamK_map_U A hgen ε hU]
    exact hE
  set E' : Subgroup C := E.comap lam with hE'
  have hEeq : E'.map lam = E := Subgroup.map_comap_eq_self (fun x hx => by
    obtain ⟨u, _, rfl⟩ := hEU hx
    exact ⟨u, rfl⟩)
  have hE'U : E' ≤ U := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hEU hx
    exact hinj hux ▸ hu
  have hE'ab : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    hinj (by rw [map_mul, map_mul]; exact hab _ ha _ hb)
  have hE'sq : ∀ a ∈ E', a ^ 2 = 1 := fun a ha =>
    hinj (by rw [map_pow, map_one]; exact hsq _ ha)
  have hcard' : Nat.card E' = Nat.card V4 := by
    rw [← Subgroup.card_map_of_injective hinj (K := E'), hEeq, hcard,
      Subgroup.card_map_of_injective hinj]
  rw [← hEeq, SV.V4_unique E' hE'U hE'ab hE'sq hcard']

end V

end CFSG.Quasithin.H13.F431.Un
