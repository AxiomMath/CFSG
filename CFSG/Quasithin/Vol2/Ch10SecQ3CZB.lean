module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZA
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZ
public import CFSG.Quasithin.Vol2.Ch10SecQ3CV
public import CFSG.Quasithin.Vol2.Ch10SecEL0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

section General

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem conj_mem_autI {V X : Subgroup Γ} (hV : IsElemAbelian 2 V)
    {g : Subgroup.normalizer (V : Set Γ)} (hg : (g : Γ) ∈ Subgroup.normalizer (X : Set Γ))
    {φ : MulAut (IntMod V hV)} (hφ : φ ∈ autI hV X) :
    convI hV g * φ * (convI hV g)⁻¹ ∈ autI hV X := by
  obtain ⟨s, hsX, rfl⟩ := (mem_autI hV).mp hφ
  rw [← map_inv, ← map_mul, ← map_mul]
  refine convI_mem_autI hV ?_ _
  exact (Subgroup.mem_normalizer_iff.mp hg _).mp hsX

omit [Finite Γ] in
theorem apply_mem_fixV_autI {V X : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set Γ)) {g : Subgroup.normalizer (V : Set Γ)}
    (hg : (g : Γ) ∈ Subgroup.normalizer (X : Set Γ)) {c : IntMod V hV}
    (hc : c ∈ fixV (autI hV X)) : convI hV g c ∈ fixV (autI hV X) := by
  rw [mem_fixV_autI hV hXN] at hc ⊢
  rw [convI_apply_val, Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : (g : Γ)⁻¹ * x * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa [mul_assoc] using this
  have h := Subgroup.mem_centralizer_iff.mp hc _ hx'
  calc x * ((g : Γ) * c.val * (g : Γ)⁻¹)
      = (g : Γ) * ((g : Γ)⁻¹ * x * g * c.val) * (g : Γ)⁻¹ := by group
    _ = (g : Γ) * (c.val * ((g : Γ)⁻¹ * x * g)) * (g : Γ)⁻¹ := by rw [h]
    _ = (g : Γ) * c.val * (g : Γ)⁻¹ * x := by group

theorem exists_pair_of_card_two {Y : Type*} [DecidableEq Y] {I : Finset Y} (h2 : I.card = 2)
    {K₀ : Y} (hK₀ : K₀ ∈ I) : ∃ K₁, K₁ ≠ K₀ ∧ I = {K₀, K₁} := by
  obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp h2
  rcases Finset.mem_insert.mp hK₀ with rfl | h
  · exact ⟨B, Ne.symm hAB, rfl⟩
  · rw [Finset.mem_singleton] at h
    subst h
    exact ⟨A, hAB, Finset.pair_comm _ _⟩

theorem mem_fixV_of_E23 {H T W : Subgroup Γ} {hW : IsElemAbelian 2 W}
    {I : Finset (Subgroup (MulAut (IntMod W hW)))} (hD : E23Data H T W hW I)
    {K₀ : Subgroup (MulAut (IntMod W hW))} (hK₀ : K₀ ∈ I) {m : ℕ}
    (hnat : E2.IsL2Natural K₀ (fixV (autI hW (twoResidual H))) m)
    {φ : MulAut (IntMod W hW)} (hφK : φ ∈ K₀) (hφ2 : φ * φ ≠ 1)
    (hφC : φ ∈ autI hW (twoResidual H))
    (hTC : ∀ s ∈ autI hW T, ∀ c ∈ fixV (autI hW (twoResidual H)),
      s c ∈ fixV (autI hW (twoResidual H)))
    {w : IntMod W hW} (hφw : φ w = w) (hTw : ∀ s ∈ autI hW T, s w = w) :
    w ∈ fixV (autI hW (twoResidual H)) := by
  classical
  set C := fixV (autI hW (twoResidual H)) with hC
  have hφC' : ∀ c ∈ C, φ c = c := fun c hc => hc φ hφC
  rcases hD.card with h1 | h2
  · obtain ⟨L, hL⟩ := Finset.card_eq_one.mp h1
    have hKL : K₀ = L := by rw [hL] at hK₀; exact Finset.mem_singleton.mp hK₀
    have hspan : C ⊔ commV K₀ = ⊤ := by
      have := hD.span
      rwa [hL, Finset.iSup_singleton, ← hKL] at this
    exact mem_of_fix_one hnat hspan hφK hφ2 hφC' hφw
  · obtain ⟨K₁, hne, hI⟩ := exists_pair_of_card_two h2 hK₀
    have hK₁ : K₁ ∈ I := by rw [hI]; simp
    have hspan : C ⊔ (commV K₀ ⊔ commV K₁) = ⊤ := by
      have := hD.span
      rwa [hI, Finset.iSup_insert, Finset.iSup_singleton] at this
    have hdir : commV K₀ ⊓ (C ⊔ commV K₁) ≤ C := by
      have := hD.dir K₀ hK₀
      rwa [hI, Finset.iSup_insert, Finset.iSup_singleton, iSup_neg (not_not.mpr rfl),
        bot_sup_eq, iSup_pos hne] at this
    have hbK : ∀ k ∈ K₁, φ * k = k * φ := fun k hk => hD.comm K₀ hK₀ K₁ hK₁ hne.symm φ hφK k hk
    obtain ⟨s, hs, hsK⟩ := hD.trans K₁ hK₁ K₀ hK₀
    exact mem_of_fix_two hnat hspan hdir hφK hbK hφ2 hφC' (hTC s hs) hsK hφw (hTw s hs)

end General

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem b_mem_normalizer : b ∈ Subgroup.normalizer (VZ T H : Set G) :=
  le_normalizer_conjClosure _ H c.hbHM.1

theorem T_le_H : T ≤ H := c.hHK ▸ le_sup_right

theorem K_le_twoResidual : K ≤ twoResidual H := by
  rw [SecE.twoResidual_eq_oTwoUpper, eq_oTwoUpper_of_perfect (perfect_of_mem_cComp c.hKc)]
  exact oTwoUpper_mono (le_of_mem_cComp c.hKc)

theorem b_mem_twoResidual : b ∈ twoResidual H := by
  rw [SecE.twoResidual_eq_oTwoUpper]
  exact mem_oTwoUpper_of_odd c.hbHM.1 c.hbo

noncomputable abbrev autB : MulAut (IntMod (VZ T H) hel) := convI hel ⟨b, c.b_mem_normalizer⟩

theorem autB_mem : c.autB ∈ oTwoUpper K₀ :=
  c.hKA ▸ convI_mem_autI hel c.hbK c.b_mem_normalizer

theorem autB_odd : Odd (orderOf c.autB) := by
  refine c.hbo.of_dvd_nat ((orderOf_map_dvd (convI hel) _).trans ?_)
  rw [Subgroup.orderOf_mk]

theorem autB_ne_one : c.autB ≠ 1 := by
  intro h
  apply c.hbZ
  have h1 := (convI_eq_one_iff hel _).mp h
  exact Subgroup.centralizer_le (le_conjClosure _ H) h1

theorem autB_sq_ne_one : c.autB * c.autB ≠ 1 := by
  intro h
  apply c.autB_ne_one
  have h2 : orderOf c.autB ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
  · exact orderOf_eq_one_iff.mp h'
  · exact absurd (h' ▸ c.autB_odd) (by decide)

theorem isL2Natural : E2.IsL2Natural K₀ (fixV (autI hel (twoResidual H))) k := by
  rcases c.hnat with h | ⟨h5, -⟩
  · exact h
  exfalso
  have hall := isA5Module_of_isA5Module c.hD c.hK₀ h5
  obtain ⟨h3a, -, h3c⟩ := c.hD.three hall
  have hJ : c.autB ∈ ⨆ L ∈ I', L := by
    rw [← c.hD.jeq]
    exact convI_mem_autI hel (c.h2J c.b_mem_twoResidual) c.b_mem_normalizer
  apply c.autB_ne_one
  refine eq_one_of_A5_components c.hD.card c.hD.comm c.hD.indep h3c hJ c.autB_odd ?_
  intro x hx
  rw [← h3a] at hx ⊢
  exact conj_mem_autI hel c.hbS hx

theorem T_apply_mem_fixV : ∀ s ∈ autI hel T, ∀ w ∈ fixV (autI hel (twoResidual H)),
    s w ∈ fixV (autI hel (twoResidual H)) := by
  intro s hs w hw
  obtain ⟨g, hgT, rfl⟩ := (mem_autI hel).mp hs
  have hRN : twoResidual H ≤ Subgroup.normalizer (VZ T H : Set G) :=
    (twoResidual_le H).trans (le_normalizer_conjClosure _ H)
  refine apply_mem_fixV_autI hel hRN ?_ hw
  rw [SecE.twoResidual_eq_oTwoUpper]
  exact le_normalizer_oTwoUpper H (c.T_le_H hgT)

theorem mem_centralizer_of_fix {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hbz : b * z * b⁻¹ = z) : z ∈ Subgroup.centralizer (H : Set G) := by
  have hzW : z ∈ VZ T H := le_conjClosure _ H hz
  have hzT := quasithinOmegaOneCenter_le_center T hz
  set w : IntMod (VZ T H) hel := IntMod.mk hel ⟨z, hzW⟩ with hw
  have hwv : w.val = z := rfl
  have hφw : c.autB w = w := IntMod.val_injective (by rw [convI_apply_val, hwv]; exact hbz)
  have hTw : ∀ s ∈ autI hel T, s w = w := by
    intro s hs
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hel).mp hs
    refine IntMod.val_injective ?_
    rw [convI_apply_val, hwv, Subgroup.mem_centralizer_iff.mp hzT.2 _ hgT, mul_inv_cancel_right]
  have hRN : twoResidual H ≤ Subgroup.normalizer (VZ T H : Set G) :=
    (twoResidual_le H).trans (le_normalizer_conjClosure _ H)
  have hmem := mem_fixV_of_E23 c.hD c.hK₀ c.isL2Natural (oTwoUpper_le _ c.autB_mem)
    c.autB_sq_ne_one (convI_mem_autI hel c.b_mem_twoResidual c.b_mem_normalizer)
    c.T_apply_mem_fixV hφw hTw
  rw [mem_fixV_autI hel hRN, hwv] at hmem
  have hle : H ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [c.hHK]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hmem x (c.K_le_twoResidual hx)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzT.2 x hx
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx))

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
