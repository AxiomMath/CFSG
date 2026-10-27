module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddFA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

@[expose] def Cmax {H M : Subgroup G} (α : Geo H M) : Subgroup G :=
  sSup {C : Subgroup G | C ≤ Wn α ∧ Zv α ≤ C ∧ stab α ≤ Subgroup.normalizer (C : Set G) ∧
    ⁅C, Lres α⁆ ≤ Zv α}

omit [Finite G] in
theorem Cmax_le_Wn : Cmax α ≤ Wn α :=
  sSup_le fun _ hC => hC.1

theorem Zv_le_Cmax (hA : F53Amalgam H M S) (hZW : Zv α ≤ Wn α) : Zv α ≤ Cmax α :=
  le_sSup ⟨hZW, le_rfl, stab_le_normalizer_Zv hA α, F.commutator_le_left_of_le_normalizer
    ((oTwoRes_le (stab α)).trans (stab_le_normalizer_Zv hA α))⟩

theorem Cmax_eq_fixSecIn (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α) :
    Cmax α = fixSecIn (Lres α) (Zv α) (Wn α) := by
  have hXZ := stab_le_normalizer_Zv hA α
  have hWZ : Wn α ≤ Subgroup.normalizer (Zv α : Set G) := hW.Wn_le_stab.trans hXZ
  have hLX : Lres α ≤ stab α := oTwoRes_le (stab α)
  have hmem : ∀ x, x ∈ fixSecIn (Lres α) (Zv α) (Wn α) ↔
      x ∈ Wn α ∧ ∀ l ∈ Lres α, l * x * l⁻¹ * x⁻¹ ∈ Zv α := fun x => mem_fixSecIn_iff hWZ
  apply le_antisymm
  · refine sSup_le fun C hC x hx => (hmem x).mpr ⟨hC.1 hx, fun l hl => ?_⟩
    have h1 := (Zv α).inv_mem (hC.2.2.2 (Subgroup.commutator_mem_commutator hx hl))
    rwa [commutatorElement_inv, commutatorElement_def] at h1
  · refine le_sSup ⟨fun x hx => ((hmem x).mp hx).1, fun z hz => (hmem z).mpr ⟨hZW hz,
      fun l hl => (Zv α).mul_mem ((Subgroup.mem_normalizer_iff.mp (hXZ (hLX hl)) z).mp hz)
        ((Zv α).inv_mem hz)⟩, ?_, ?_⟩
    · refine Sit43.le_normalizer_of_conj_mem fun x hx w hw => ?_
      obtain ⟨hwW, hwL⟩ := (hmem w).mp hw
      refine (hmem _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hW.stab_le_normalizer hx) w).mp hwW,
        fun l hl => ?_⟩
      have hl' : x⁻¹ * l * x ∈ Lres α := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_oTwoRes (stab α) ((stab α).inv_mem hx)) l).mp hl
        rwa [inv_inv] at this
      have e : l * (x * w * x⁻¹) * l⁻¹ * (x * w * x⁻¹)⁻¹ =
          x * ((x⁻¹ * l * x) * w * (x⁻¹ * l * x)⁻¹ * w⁻¹) * x⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hXZ hx) _).mp (hwL _ hl')
    · rw [Subgroup.commutator_le]
      intro x hx l hl
      have h1 := (Zv α).inv_mem (((hmem x).mp hx).2 l hl)
      have e : (l * x * l⁻¹ * x⁻¹)⁻¹ = ⁅x, l⁆ := by rw [commutatorElement_def]; group
      rwa [e] at h1

theorem mem_Cmax_iff (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α) {w : G} :
    w ∈ Cmax α ↔ w ∈ Wn α ∧ ∀ l ∈ Lres α, l * w * l⁻¹ * w⁻¹ ∈ Zv α := by
  rw [Cmax_eq_fixSecIn hA hW hZW]
  exact mem_fixSecIn_iff (hW.Wn_le_stab.trans (stab_le_normalizer_Zv hA α))

theorem stab_le_normalizer_Cmax (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α) :
    stab α ≤ Subgroup.normalizer (Cmax α : Set G) := by
  refine Sit43.le_normalizer_of_conj_mem fun x hx w hw => ?_
  obtain ⟨hwW, hwL⟩ := (mem_Cmax_iff hA hW hZW).mp hw
  refine (mem_Cmax_iff hA hW hZW).mpr
    ⟨(Subgroup.mem_normalizer_iff.mp (hW.stab_le_normalizer hx) w).mp hwW, fun l hl => ?_⟩
  have hl' : x⁻¹ * l * x ∈ Lres α := by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_oTwoRes (stab α) ((stab α).inv_mem hx)) l).mp hl
    rwa [inv_inv] at this
  have e : l * (x * w * x⁻¹) * l⁻¹ * (x * w * x⁻¹)⁻¹ =
      x * ((x⁻¹ * l * x) * w * (x⁻¹ * l * x)⁻¹ * w⁻¹) * x⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hx) _).mp (hwL _ hl')

theorem comm_Cmax_le (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α) :
    ⁅Cmax α, Lres α⁆ ≤ Zv α := by
  rw [Subgroup.commutator_le]
  intro x hx l hl
  have h1 := (Zv α).inv_mem (((mem_Cmax_iff hA hW hZW).mp hx).2 l hl)
  have e : (l * x * l⁻¹ * x⁻¹)⁻¹ = ⁅x, l⁆ := by rw [commutatorElement_def]; group
  rwa [e] at h1

theorem le_Cmax (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α) {D : Subgroup G}
    (hDW : D ≤ Wn α) (hD : ∀ l ∈ Lres α, ∀ d ∈ D, l * d * l⁻¹ * d⁻¹ ∈ Zv α) : D ≤ Cmax α :=
  fun d hd => (mem_Cmax_iff hA hW hZW).mpr ⟨hDW hd, fun l hl => hD l hl d hd⟩

theorem mem_Cmax_of_forall (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α) {w : G}
    (hw : w ∈ Wn α) (h : ∀ l ∈ Lres α, l * w * l⁻¹ * w⁻¹ ∈ Cmax α) : w ∈ Cmax α := by
  refine (mem_Cmax_iff hA hW hZW).mpr ⟨hw, ?_⟩
  refine F.comm_mem_of_oTwoRes (stab_le_normalizer_Zv hA α) fun l hlX m hm hlm => ?_
  have hlL : l ∈ Lres α := Subgroup.subset_closure ⟨hlX, m, hm, hlm⟩
  refine F.comm_mem_of_odd (E₁ := Cmax α) hm hlm (stab_le_normalizer_Zv hA α hlX)
    (fun c hc => ((mem_Cmax_iff hA hW hZW).mp hc).2 l hlL) (fun c hc => ?_) (h l hlL)
  have h2 := hW.sq_mem c (Cmax_le_Wn hc)
  rwa [pow_two] at h2

namespace F

omit [Finite G] in
theorem chain_mono {X U : Subgroup G} {Wc : ℕ → Subgroup G} {r : ℕ}
    (hstep : ∀ i, i < r → IsChiefStep X U (Wc i) (Wc (i + 1))) :
    ∀ i j, i ≤ j → j ≤ r → Wc i ≤ Wc j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (hstep j (by omega)).2.2.1.le

theorem comm_mem_of_central (hA : F53Amalgam H M S) (hW : W17Hyp α) {Wc : ℕ → Subgroup G}
    {r : ℕ} (h0 : Wc 0 = Zv α) (hr : Wc r = Wn α)
    (hstep : ∀ i, i < r → IsChiefStep (stab α) (pCoreOf 2 (stab α)) (Wc i) (Wc (i + 1)))
    {j₀ j₁ : ℕ} (hj : j₀ ≤ j₁) (hj₁ : j₁ ≤ r)
    (hc : ∀ i, j₀ ≤ i → i < j₁ → IsCentralStep (stab α) (Wc i) (Wc (i + 1))) :
    ∀ l ∈ Lres α, ∀ v ∈ Wc j₁, l * v * l⁻¹ * v⁻¹ ∈ Wc j₀ := by
  have hmono := chain_mono hstep
  have hnorm : ∀ j, j ≤ r → stab α ≤ Subgroup.normalizer (Wc j : Set G) := by
    intro j hj
    cases j with
    | zero => rw [h0]; exact stab_le_normalizer_Zv hA α
    | succ i => exact normalizer_right (hstep i (by omega))
  have hsq : ∀ i, i ≤ j₁ - j₀ → ∀ c ∈ Wc (j₀ + i), c * c ∈ Wc (j₀ + 0) := by
    intro i hi c hc'
    have hcW : c ∈ Wn α := hr ▸ hmono (j₀ + i) r (by omega) (by omega) hc'
    have h2 := hW.sq_mem c hcW
    rw [pow_two, ← h0] at h2
    exact hmono 0 (j₀ + 0) (Nat.zero_le _) (by omega) h2
  intro l hl v hv
  refine comm_mem_of_oTwoRes (hnorm j₀ (by omega)) (fun g hgX m hm hgm => ?_) l hl
  have hv' : v ∈ Wc (j₀ + (j₁ - j₀)) := by rw [show j₀ + (j₁ - j₀) = j₁ by omega]; exact hv
  exact comm_mem_of_odd_chain (E := fun i => Wc (j₀ + i)) (s := j₁ - j₀) hm hgm
    (hnorm j₀ (by omega) hgX) (fun i hi u hu => hc (j₀ + i) (by omega) (by omega) g hgX u hu)
    hsq v hv'

theorem exists_central_cut (hA : F53Amalgam H M S) (hW : W17Hyp α) (hZW : Zv α ≤ Wn α)
    (h : AtMostOneNoncentral α) :
    ∃ B : Subgroup G, B ≤ Wn α ∧ stab α ≤ Subgroup.normalizer (B : Set G) ∧
      (∀ l ∈ Lres α, ∀ v ∈ Wn α, l * v * l⁻¹ * v⁻¹ ∈ B) ∧
      ∀ q ∈ Qv α, ∀ y ∈ B, q * y * q⁻¹ * y⁻¹ ∈ Cmax α := by
  obtain ⟨r, Wc, h0, hr, hstep, hone⟩ := h
  have hmono := chain_mono hstep
  have hvr : ∀ v ∈ Wn α, v ∈ Wc r := fun v hv => by rw [hr]; exact hv
  by_cases hc : ∀ i, i < r → IsCentralStep (stab α) (Wc i) (Wc (i + 1))
  · refine ⟨Zv α, hZW, stab_le_normalizer_Zv hA α, fun l hl v hv => ?_, fun q hq y hy => ?_⟩
    · have := comm_mem_of_central hA hW h0 hr hstep (Nat.zero_le r) le_rfl
        (fun i _ hi => hc i hi) l hl v (hvr v hv)
      rwa [h0] at this
    · refine Zv_le_Cmax hA hZW ((Zv α).mul_mem ?_ ((Zv α).inv_mem hy))
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α (pCoreOf_le 2 _ hq)) y).mp
        hy
  · push Not at hc
    obtain ⟨k, hk, hnk⟩ := hc
    have hcen : ∀ i, i < r → i ≠ k → IsCentralStep (stab α) (Wc i) (Wc (i + 1)) :=
      fun i hi hik => (hone i k hi hk hik).resolve_right hnk
    refine ⟨Wc (k + 1), ?_, normalizer_right (hstep k hk), fun l hl v hv => ?_,
      fun q hq y hy => ?_⟩
    · rw [← hr]; exact hmono (k + 1) r (by omega) le_rfl
    · exact comm_mem_of_central hA hW h0 hr hstep (j₀ := k + 1) (j₁ := r) (by omega) le_rfl
        (fun i hi hi' => hcen i hi' (by omega)) l hl v (hvr v hv)
    · have hkC : Wc k ≤ Cmax α := by
        refine le_Cmax hA hW hZW (by rw [← hr]; exact hmono k r (by omega) le_rfl)
          fun l hl d hd => ?_
        have := comm_mem_of_central hA hW h0 hr hstep (j₀ := 0) (j₁ := k) (Nat.zero_le k)
          (by omega) (fun i _ hi => hcen i (by omega) (by omega)) l hl d hd
        rwa [h0] at this
      exact hkC (commutator_pCoreOf_mem le_rfl (hstep k hk) q hq y hy)

end F

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
