module

public import CFSG.LocalAnalysis.WeakClosure81.W183L313Borel
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.Goldschmidt.Steps.G76U34
import CFSG.RankThree.PartTwo.Sec3.SectionModuleBound
import CFSG.LocalAnalysis.WeakClosure81.W183L313DichAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement
open Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem w183l313_key_odd {Q S D Lm : Subgroup Γ} (hB : BorelU34 Q S D) (hS : IsSylowIn 2 S Q)
    (hL : ∀ n ∈ Q ⊓ Subgroup.normalizer (S : Set Γ), ∀ l ∈ Lm, n * l * n⁻¹ ∈ Lm)
    (hZL : sylowCenter S ≤ Lm) (hLZ : ∀ l ∈ Lm, ∀ z ∈ sylowCenter S, l * z = z * l)
    {k : Γ} (hkL : k ∈ Lm) (hkN : k ∈ Q ⊓ Subgroup.normalizer (S : Set Γ)) (hkS : k ∉ S)
    (hkodd : Odd (orderOf k)) : S ≤ Lm := by
  set Z := sylowCenter S with hZ
  have hZS : Z ≤ S := inf_le_left
  set X := Lm ⊓ S with hX
  have hZX : Z ≤ X := le_inf hZL hZS
  have hXS : X ≤ S := inf_le_right
  have hDX : D ≤ Subgroup.normalizer (X : Set Γ) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨hL d ⟨hB.le_Q hd, hB.le_normalizer hd⟩ x hx.1,
        (Subgroup.mem_normalizer_iff.mp (hB.le_normalizer hd) x).mp hx.2⟩
    · intro hx
      have hd' : d⁻¹ ∈ D := D.inv_mem hd
      have hxL : x ∈ Lm := by
        have h1 : d⁻¹ * (d * x * d⁻¹) * (d⁻¹)⁻¹ ∈ Lm :=
          hL d⁻¹ ⟨hB.le_Q hd', hB.le_normalizer hd'⟩ (d * x * d⁻¹) hx.1
        rwa [show d⁻¹ * (d * x * d⁻¹) * (d⁻¹)⁻¹ = x by group] at h1
      exact ⟨hxL, (Subgroup.mem_normalizer_iff.mp (hB.le_normalizer hd) x).mpr hx.2⟩
  rcases hB.irred X hZX hXS hDX with hXZ | hXS'
  · exfalso
    have hkcent : ∀ p ∈ S, k * p * k⁻¹ = p := by
      have hcomm : ∀ p ∈ S, k * p * k⁻¹ * p⁻¹ ∈ Z := by
        intro p hp
        have h1 : p * k * p⁻¹ ∈ Lm :=
          hL p ⟨hS.le hp, Subgroup.le_normalizer hp⟩ k hkL
        have h2 : p * k * p⁻¹ * k⁻¹ ∈ Lm := Lm.mul_mem h1 (Lm.inv_mem hkL)
        have h3 : p * k * p⁻¹ * k⁻¹ ∈ S := by
          have h4 : k * p⁻¹ * k⁻¹ ∈ S :=
            (Subgroup.mem_normalizer_iff.mp hkN.2 p⁻¹).mp (S.inv_mem hp)
          have h5 : p * (k * p⁻¹ * k⁻¹) ∈ S := S.mul_mem hp h4
          rwa [show p * (k * p⁻¹ * k⁻¹) = p * k * p⁻¹ * k⁻¹ by group] at h5
        have hmem : p * k * p⁻¹ * k⁻¹ ∈ X := ⟨h2, h3⟩
        rw [hXZ] at hmem
        rw [show k * p * k⁻¹ * p⁻¹ = (p * k * p⁻¹ * k⁻¹)⁻¹ by group]
        exact Z.inv_mem hmem
      exact fun p hp =>
        CFSG.RankThree.PartTwo.Sec3.commute_of_odd_of_stabilizes (P := S) (W' := Z)
          hS.isPGroup hZS hkodd hcomm (fun w hw => by rw [hLZ k hkL w hw]; group) hp
    have hkSD : k ∈ S ⊔ D := by rw [hB.sup_eq]; exact hkN
    have hkDS : k ∈ (↑(D ⊔ S) : Set Γ) := by
      rw [sup_comm]; exact hkSD
    rw [coe_mul_of_left_le_normalizer_right D S hB.le_normalizer] at hkDS
    obtain ⟨d, hd, s, hs, hds⟩ := hkDS
    have hconj : ∀ t ∈ S, d⁻¹ * t * d = s * t * s⁻¹ := by
      intro t ht
      have hkt : k * t * k⁻¹ = t := hkcent t ht
      rw [← hds] at hkt
      calc d⁻¹ * t * d = d⁻¹ * ((d * s) * t * (d * s)⁻¹) * d := by rw [hkt]
        _ = s * t * s⁻¹ := by group
    have hdcent : ∀ t ∈ S, d⁻¹ * t * d = t := by
      have h := w183l313_odd_conj_eq hB.odd (D.inv_mem hd) (hB.le_normalizer (D.inv_mem hd))
        (S.inv_mem hs) hS.isPGroup (by simpa using hconj)
      simpa using h
    have hdC : d ∈ Subgroup.centralizer (S : Set Γ) := by
      refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
      have h := hdcent t ht
      calc t * d = d * (d⁻¹ * t * d) := by group
        _ = d * t := by rw [h]
    have hd1 : d = 1 := by
      have : d ∈ D ⊓ Subgroup.centralizer (S : Set Γ) := ⟨hd, hdC⟩
      rw [hB.inf_centralizer] at this
      exact Subgroup.mem_bot.mp this
    have hs_eq : s = k := by simpa [hd1] using hds
    exact hkS (hs_eq ▸ hs)
  · rw [← hXS']; exact inf_le_left

theorem w183l313_outer_involution {Y Q S D Pk : Subgroup Γ} (hQ : IsU3 ↥Q 2) (hB : BorelU34 Q S D)
    (hS : IsSylowIn 2 S Q) (hQY : Q ≤ Y) (hYQ : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hcent : ∀ y ∈ Y, (∀ q ∈ Q, y * q = q * y) → y = 1)
    (hPY : Pk ≤ Y) (hPS : Pk ≤ Subgroup.normalizer (S : Set Γ))
    (hPN : ∀ n ∈ Y ⊓ Subgroup.normalizer (S : Set Γ), ∀ p ∈ Pk, n * p * n⁻¹ ∈ Pk)
    (hK : ∀ k ∈ Pk, k ∈ Q → k ∈ S) {f : Γ} (hf : f ∈ Pk) (hf2 : f * f = 1) (hfQ : f ∉ Q) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf_inv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  set Z := sylowCenter S with hZ
  have hZS : Z ≤ S := inf_le_left
  have hfY : f ∈ Y := hPY hf
  have hfN : f ∈ Subgroup.normalizer (S : Set Γ) := hPS hf
  have hfZ : f ∈ Subgroup.normalizer (Z : Set Γ) := w183l313_normalizes_center hfN
  have hF1 : ∀ d ∈ D, ∃ c ∈ S, f * d * f⁻¹ = c * d := by
    intro d hd
    refine ⟨f * d * f⁻¹ * d⁻¹, ?_, by group⟩
    have hdY : d ∈ Y := hQY (hB.le_Q hd)
    have hdN : d ∈ Subgroup.normalizer (S : Set Γ) := hB.le_normalizer hd
    have hdf : d * f * d⁻¹ ∈ Pk := hPN d ⟨hdY, hdN⟩ f hf
    have h1 : d * f⁻¹ * d⁻¹ ∈ Pk := by
      rw [show d * f⁻¹ * d⁻¹ = (d * f * d⁻¹)⁻¹ by group]
      exact Pk.inv_mem hdf
    have h2 : f * d * f⁻¹ * d⁻¹ ∈ Pk := by
      have := Pk.mul_mem hf h1
      rwa [show f * (d * f⁻¹ * d⁻¹) = f * d * f⁻¹ * d⁻¹ by group] at this
    have h3 : f * d * f⁻¹ * d⁻¹ ∈ Q := by
      have : f * d * f⁻¹ ∈ Q := hYQ f hfY d (hB.le_Q hd)
      exact Q.mul_mem this (Q.inv_mem (hB.le_Q hd))
    exact hK _ h2 h3
  have hF2 : ∀ z ∈ Z, f * z * f⁻¹ = z := by
    have hf2' : f ^ 2 = 1 := by rw [pow_two]; exact hf2
    have hmod := CFSG.Goldschmidt.G76.card_modEq_card_inf_centralizer (p := 2) hf2' hfZ
    rw [hB.card_center] at hmod
    set C := Z ⊓ Subgroup.centralizer ({f} : Set Γ) with hC
    have heven : 2 ∣ Nat.card C := by
      have h0 : Nat.card C % 2 = 0 := by
        have h : 4 % 2 = Nat.card C % 2 := hmod
        rw [show 4 % 2 = 0 by norm_num] at h
        exact h.symm
      exact Nat.dvd_iff_mod_eq_zero.mpr h0
    have hne : C ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card C = 1 := (Subgroup.eq_bot_iff_card C).mp hbot
      rw [h1] at heven
      norm_num at heven
    obtain ⟨z₀, hz₀, hz₀1⟩ := (Subgroup.bot_or_exists_ne_one C).resolve_left hne
    have hz₀Z : z₀ ∈ Z := (Subgroup.mem_inf.mp hz₀).1
    have hz₀C : z₀ ∈ Subgroup.centralizer ({f} : Set Γ) := (Subgroup.mem_inf.mp hz₀).2
    have hz₀f : f * z₀ * f⁻¹ = z₀ := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hz₀C]; group
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; group
    · obtain ⟨d, hd, hdz⟩ := hB.trans_center z₀ hz₀Z z hz hz₀1 hz1
      obtain ⟨c, hcS, hcfd⟩ := hF1 d hd
      have hfd_inv : f * d⁻¹ * f⁻¹ = d⁻¹ * c⁻¹ := by
        rw [show f * d⁻¹ * f⁻¹ = (f * d * f⁻¹)⁻¹ by group, hcfd, mul_inv_rev]
      have hcz : c⁻¹ * z₀ = z₀ * c⁻¹ := (mem_sylowCenter.mp hz₀Z).2 c⁻¹ (S.inv_mem hcS)
      rw [← hdz]
      calc f * (d⁻¹ * z₀ * d) * f⁻¹
          = (f * d⁻¹ * f⁻¹) * (f * z₀ * f⁻¹) * (f * d * f⁻¹) := by group
        _ = (d⁻¹ * c⁻¹) * z₀ * (c * d) := by rw [hfd_inv, hcfd, hz₀f]
        _ = d⁻¹ * (c⁻¹ * z₀) * (c * d) := by group
        _ = d⁻¹ * (z₀ * c⁻¹) * (c * d) := by rw [hcz]
        _ = d⁻¹ * z₀ * d := by group
  have hF3 : ∀ s ∈ S, f * s * f⁻¹ * s⁻¹ ∈ Z := by
    let W : Subgroup Γ :=
      { carrier := {s | s ∈ S ∧ f * s * f⁻¹ * s⁻¹ ∈ Z}
        one_mem' := by
          refine ⟨S.one_mem, ?_⟩
          rw [show f * 1 * f⁻¹ * 1⁻¹ = 1 by group]
          exact Z.one_mem
        mul_mem' := by
          rintro a b ⟨haS, haZ⟩ ⟨hbS, hbZ⟩
          refine ⟨S.mul_mem haS hbS, ?_⟩
          set x := f * a * f⁻¹ * a⁻¹ with hx
          set y := f * b * f⁻¹ * b⁻¹ with hy
          have ha_eq : f * a * f⁻¹ = x * a := by rw [hx]; group
          have hb_eq : f * b * f⁻¹ = y * b := by rw [hy]; group
          have hy_comm_a : y * a = a * y := ((mem_sylowCenter.mp hbZ).2 a haS).symm
          have hfinal : f * (a * b) * f⁻¹ * (a * b)⁻¹ = x * y := by
            calc f * (a * b) * f⁻¹ * (a * b)⁻¹
                = (f * a * f⁻¹) * (f * b * f⁻¹) * b⁻¹ * a⁻¹ := by group
              _ = (x * a) * (y * b) * b⁻¹ * a⁻¹ := by rw [ha_eq, hb_eq]
              _ = x * (a * y) * (b * b⁻¹) * a⁻¹ := by group
              _ = x * (y * a) * (b * b⁻¹) * a⁻¹ := by rw [← hy_comm_a]
              _ = x * y := by group
          rw [hfinal]
          exact Z.mul_mem haZ hbZ
        inv_mem' := by
          rintro a ⟨haS, haZ⟩
          refine ⟨S.inv_mem haS, ?_⟩
          set x := f * a * f⁻¹ * a⁻¹ with hx
          have ha_eq : f * a * f⁻¹ = x * a := by rw [hx]; group
          have h1 : f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
          have hx_comm : a⁻¹ * x⁻¹ = x⁻¹ * a⁻¹ :=
            (mem_sylowCenter.mp (Z.inv_mem haZ)).2 a⁻¹ (S.inv_mem haS)
          have hfinal : f * a⁻¹ * f⁻¹ * a = x⁻¹ := by
            calc f * a⁻¹ * f⁻¹ * a = (f * a * f⁻¹)⁻¹ * a := by rw [h1]
              _ = (a⁻¹ * x⁻¹) * a := by rw [ha_eq]; group
              _ = (x⁻¹ * a⁻¹) * a := by rw [hx_comm]
              _ = x⁻¹ := by group
          rw [inv_inv, hfinal]
          exact Z.inv_mem haZ }
    have hZW : Z ≤ W := by
      intro z hz
      refine ⟨hZS hz, ?_⟩
      rw [hF2 z hz]
      simpa using Z.one_mem
    have hWS : W ≤ S := fun x hx => hx.1
    have hstep : ∀ d ∈ D, ∀ s ∈ W, d * s * d⁻¹ ∈ W := by
      intro d hd s hs
      obtain ⟨hsS, hsZ⟩ := hs
      obtain ⟨c, hcS, hcfd⟩ := hF1 d hd
      have hfd_inv : f * d⁻¹ * f⁻¹ = d⁻¹ * c⁻¹ := by
        rw [show f * d⁻¹ * f⁻¹ = (f * d * f⁻¹)⁻¹ by group, hcfd, mul_inv_rev]
      have hz' : d * (f * s * f⁻¹ * s⁻¹) * d⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (w183l313_normalizes_center (hB.le_normalizer hd))
          (f * s * f⁻¹ * s⁻¹)).mp hsZ
      have hs'S : d * s * d⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hB.le_normalizer hd) s).mp hsS
      have hz'' : c * (d * s * d⁻¹) * c⁻¹ * (d * s * d⁻¹)⁻¹ ∈ Z :=
        hB.comm_mem c hcS (d * s * d⁻¹) hs'S
      refine ⟨hs'S, ?_⟩
      have hz_eq : f * s * f⁻¹ = (f * s * f⁻¹ * s⁻¹) * s := by group
      have hfinal : f * (d * s * d⁻¹) * f⁻¹ * (d * s * d⁻¹)⁻¹ =
          (d * (f * s * f⁻¹ * s⁻¹) * d⁻¹) *
            (c * (d * s * d⁻¹) * c⁻¹ * (d * s * d⁻¹)⁻¹) := by
        calc f * (d * s * d⁻¹) * f⁻¹ * (d * s * d⁻¹)⁻¹
            = (f * d * f⁻¹) * (f * s * f⁻¹) * (f * d⁻¹ * f⁻¹) * (d * s⁻¹ * d⁻¹) := by
              group
          _ = (c * d) * ((f * s * f⁻¹ * s⁻¹) * s) * (d⁻¹ * c⁻¹) * (d * s⁻¹ * d⁻¹) := by
                rw [hcfd, hfd_inv, hz_eq]; group
          _ = (c * (d * (f * s * f⁻¹ * s⁻¹) * d⁻¹) * (d * s * d⁻¹) * c⁻¹) *
                (d * s * d⁻¹)⁻¹ := by
                rw [show d * s⁻¹ * d⁻¹ = (d * s * d⁻¹)⁻¹ by group]; group
          _ = ((d * (f * s * f⁻¹ * s⁻¹) * d⁻¹) * c * (d * s * d⁻¹) * c⁻¹) *
                (d * s * d⁻¹)⁻¹ := by
                rw [show c * (d * (f * s * f⁻¹ * s⁻¹) * d⁻¹) =
                    (d * (f * s * f⁻¹ * s⁻¹) * d⁻¹) * c from
                  (mem_sylowCenter.mp hz').2 c hcS]
          _ = (d * (f * s * f⁻¹ * s⁻¹) * d⁻¹) *
                (c * (d * s * d⁻¹) * c⁻¹ * (d * s * d⁻¹)⁻¹) := by group
      rw [hfinal]
      exact Z.mul_mem hz' hz''
    have hDW : D ≤ Subgroup.normalizer (W : Set Γ) := by
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro s
      exact ⟨hstep d hd s, fun hs => by
        have h := hstep d⁻¹ (D.inv_mem hd) (d * s * d⁻¹) hs
        rwa [show d⁻¹ * (d * s * d⁻¹) * (d⁻¹)⁻¹ = s by group] at h⟩
    have hWS' : W = S := by
      rcases hB.irred W hZW hWS hDW with hWZ | hWS'
      · exfalso
        have hSe : S ≤ W := by
          intro s hs
          have hcS : f * s * f⁻¹ * s⁻¹ ∈ S :=
            S.mul_mem ((Subgroup.mem_normalizer_iff.mp hfN s).mp hs) (S.inv_mem hs)
          have hcW : f * s * f⁻¹ * s⁻¹ ∈ W := by
            refine ⟨hcS, ?_⟩
            rw [w183l313_conj_commutator_self hf2]
            simpa [mul_inv_rev] using Z.inv_mem (hB.sq_mem (f * s * f⁻¹ * s⁻¹) hcS)
          rw [hWZ] at hcW
          exact ⟨hs, hcW⟩
        have hZneS : Z ≠ S := by
          intro h
          obtain ⟨x, hx, y, hy, hxy⟩ := hB.nonabelian
          have hxZ : x ∈ Z := by rw [h]; exact hx
          exact hxy ((mem_sylowCenter.mp hxZ).2 y hy).symm
        exact hZneS (hWZ.symm.trans (le_antisymm hWS hSe))
      · exact hWS'
    intro s hs
    have : s ∈ W := by rw [hWS']; exact hs
    exact this.2
  obtain ⟨e⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 hQ
  have hfQN : f ∈ Subgroup.normalizer (Q : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq; exact hYQ f hfY q hq
    · intro hq
      have h1 : f * (f * q * f⁻¹) * f⁻¹ ∈ Q := hYQ f hfY (f * q * f⁻¹) hq
      have hq_eq : f * (f * q * f⁻¹) * f⁻¹ = q := by
        rw [hf_inv]
        rw [show f * (f * q * f) * f = (f * f) * q * (f * f) by group]
        simp [hf2]
      rwa [hq_eq] at h1
  let fN : Subgroup.normalizer (Q : Set Γ) := ⟨f, hfQN⟩
  let α : MulAut ↥Q := Subgroup.normalizerMonoidHom (H := Q) fN
  have hα2 : α ^ 2 = 1 := by
    rw [← map_pow, ← map_one (Subgroup.normalizerMonoidHom (H := Q))]
    congr 1
    apply Subtype.ext
    show f ^ 2 = 1
    rw [pow_two]; exact hf2
  have hαS : ∀ s ∈ (hS.toSylow : Subgroup ↥Q), α s ∈ (hS.toSylow : Subgroup ↥Q) := by
    intro s hs
    rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hs ⊢
    change f * (s : Γ) * f⁻¹ ∈ S
    exact (Subgroup.mem_normalizer_iff.mp hfN (s : Γ)).mp hs
  have hαZ : ∀ z ∈ sylowCenter (hS.toSylow : Subgroup ↥Q), α z = z := by
    intro z hz
    have hzZ : (z : Γ) ∈ Z := by
      rw [← w183l313_mem_sylowCenter_subgroupOf hS.le]
      rw [IsSylowIn.coe_toSylow] at hz
      exact hz
    apply Subtype.ext
    change f * (z : Γ) * f⁻¹ = (z : Γ)
    exact hF2 (z : Γ) hzZ
  have hαinner : ∀ s ∈ (hS.toSylow : Subgroup ↥Q), α ≠ MulAut.conj s := by
    intro s hs hconj
    have hforall : ∀ q : ↥Q, f * (q : Γ) * f⁻¹ = (s : Γ) * (q : Γ) * (s : Γ)⁻¹ := by
      intro q
      have h := congrArg (fun β : MulAut ↥Q => (β q : Γ)) hconj
      simpa [α, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    have hsS : (s : Γ) ∈ S := by
      simpa [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] using hs
    have hsQ : (s : Γ) ∈ Q := hS.le hsS
    have hcent' : ∀ q ∈ Q, ((s : Γ)⁻¹ * f) * q = q * ((s : Γ)⁻¹ * f) := by
      intro q hq
      have h := hforall ⟨q, hq⟩
      calc (s : Γ)⁻¹ * f * q = (s : Γ)⁻¹ * (f * q * f⁻¹) * f := by group
        _ = (s : Γ)⁻¹ * ((s : Γ) * q * (s : Γ)⁻¹) * f := by rw [h]
        _ = q * ((s : Γ)⁻¹ * f) := by group
    have hmemY : (s : Γ)⁻¹ * f ∈ Y := Y.mul_mem (hQY (Q.inv_mem hsQ)) hfY
    have h1 : (s : Γ)⁻¹ * f = 1 := hcent ((s : Γ)⁻¹ * f) hmemY hcent'
    have hfs : f = s := (inv_mul_eq_one.mp h1).symm
    exact hfQ (by rw [hfs]; exact hsQ)
  have hAC := CFSG.ComponentClassification.AschbacherToolkit.Bender.autControlAt_of_mulEquiv_psu3
    (X := ↥Q) (f := 2) le_rfl e (hS.toSylow)
  obtain ⟨-, -, t, ht, hnot⟩ := hAC α hαS hαZ ⟨1, by rw [pow_one]; exact hα2⟩ hαinner
  apply hnot
  rw [IsSylowIn.coe_toSylow, w183l313_mem_sylowCenter_subgroupOf hS.le]
  have htS : (t : Γ) ∈ S := by
    rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at ht
    exact ht
  have hαt : (α t : Γ) = f * (t : Γ) * f⁻¹ := by
    simp [α, fN, Subgroup.normalizerMonoidHom_apply_apply_coe]
  change (t : Γ)⁻¹ * (α t : Γ) ∈ sylowCenter S
  rw [hαt]
  have hz := hF3 (t : Γ) htS
  have hcz : (t : Γ)⁻¹ * (f * (t : Γ) * f⁻¹ * (t : Γ)⁻¹) =
      (f * (t : Γ) * f⁻¹ * (t : Γ)⁻¹) * (t : Γ)⁻¹ :=
    (mem_sylowCenter.mp hz).2 (t : Γ)⁻¹ (S.inv_mem htS)
  have hfinal : (t : Γ)⁻¹ * (f * (t : Γ) * f⁻¹) =
      f * (t : Γ) * f⁻¹ * (t : Γ)⁻¹ := by
    calc (t : Γ)⁻¹ * (f * (t : Γ) * f⁻¹)
        = (t : Γ)⁻¹ * (f * (t : Γ) * f⁻¹ * (t : Γ)⁻¹) * (t : Γ) := by group
      _ = f * (t : Γ) * f⁻¹ * (t : Γ)⁻¹ := by rw [hcz]; group
  rw [hfinal]
  exact hz


section Certified


theorem w183l313_dichotomy {Y Q S Lm Pk : Subgroup Γ} (hQ : IsU3 ↥Q 2) (hS : IsSylowIn 2 S Q)
    (hQY : Q ≤ Y) (hYQ : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hcent : ∀ y ∈ Y, (∀ q ∈ Q, y * q = q * y) → y = 1)
    (hPY : Pk ≤ Y) (hPS : Pk ≤ Subgroup.normalizer (S : Set Γ))
    (hPN : ∀ n ∈ Y ⊓ Subgroup.normalizer (S : Set Γ), ∀ p ∈ Pk, n * p * n⁻¹ ∈ Pk)
    (hLN : ∀ n ∈ Y ⊓ Subgroup.normalizer (S : Set Γ), ∀ l ∈ Lm, n * l * n⁻¹ ∈ Lm)
    (hZL : sylowCenter S ≤ Lm) (hLZ : ∀ l ∈ Lm, ∀ z ∈ sylowCenter S, l * z = z * l)
    (hodd : ∀ k ∈ Pk, Odd (orderOf k) → k ∈ Lm) :
    S ≤ Lm ∨ ∀ f ∈ Pk, f * f = 1 → f ∈ Q := by
  obtain ⟨D, hB⟩ := w183l313_borel_exists hQ hS
  by_cases hSL : S ≤ Lm
  · exact Or.inl hSL
  · refine Or.inr fun f hf hf2 => ?_
    by_contra hfQ
    have hKle : Pk ⊓ Q ≤ S := by
      by_contra hnot
      obtain ⟨k₀, hk₀, hk₀S⟩ := Set.not_subset.mp hnot
      have hKnot : ¬ IsPGroup 2 (Pk ⊓ Q : Subgroup Γ) := by
        intro hKpg
        apply hk₀S
        let K' : Subgroup ↥Q := (Pk ⊓ Q : Subgroup Γ).subgroupOf Q
        have hK'pg : IsPGroup 2 K' :=
          hKpg.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
        have hK'N : K' ≤ Subgroup.normalizer ((hS.toSylow : Subgroup ↥Q) : Set ↥Q) := by
          intro k hk
          have hkPk : (k : Γ) ∈ Pk := (Subgroup.mem_subgroupOf.mp hk).1
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hy ⊢
            exact (Subgroup.mem_normalizer_iff.mp (hPS hkPk) (y : Γ)).mp hy
          · intro hy
            rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hy ⊢
            exact (Subgroup.mem_normalizer_iff.mp (hPS hkPk) (y : Γ)).mpr hy
        have hK'le : K' ≤ (hS.toSylow : Subgroup ↥Q) :=
          (IsPGroup.sylow_mem_fixedPoints_iff (P := K') hK'pg).mp
            ((Subgroup.sylow_mem_fixedPoints_iff K' (P := hS.toSylow)).mpr hK'N)
        have hk' : (⟨k₀, hk₀.2⟩ : ↥Q) ∈ K' := by
          rw [Subgroup.mem_subgroupOf]; exact hk₀
        have hk'' := hK'le hk'
        rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hk''
        exact hk''
      have hcard_ne : ∀ n : ℕ, Nat.card (Pk ⊓ Q : Subgroup Γ) ≠ 2 ^ n := by
        intro n hn
        exact hKnot ((IsPGroup.iff_card).mpr ⟨n, hn⟩)
      have hnotall : ¬ (∀ {p : ℕ}, Nat.Prime p → p ∣ Nat.card (Pk ⊓ Q : Subgroup Γ) → p = 2) := by
        intro hall
        have hpos : Nat.card (Pk ⊓ Q : Subgroup Γ) ≠ 0 :=
          (Nat.card_pos (α := ↥(Pk ⊓ Q))).ne'
        have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hpos
          (fun hp hdvd => hall hp hdvd)
        exact hcard_ne _ hpow
      rw [not_forall] at hnotall
      obtain ⟨r, hr⟩ := hnotall
      rw [not_imp] at hr
      obtain ⟨hrp, hr'⟩ := hr
      rw [not_imp] at hr'
      obtain ⟨hrdvd, hrne⟩ := hr'
      haveI : Fact (Nat.Prime r) := ⟨hrp⟩
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Pk ⊓ Q)) r hrdvd
      have hrodd : Odd r := hrp.odd_of_ne_two hrne
      have hkPk : (k : Γ) ∈ Pk := k.2.1
      have hkQ : (k : Γ) ∈ Q := k.2.2
      have horder : orderOf (k : Γ) = r := by rw [orderOf_coe, hk]
      have hkL : (k : Γ) ∈ Lm := hodd (k : Γ) hkPk (by rw [horder]; exact hrodd)
      have hkN : (k : Γ) ∈ Q ⊓ Subgroup.normalizer (S : Set Γ) := ⟨hkQ, hPS hkPk⟩
      have hkS : (k : Γ) ∉ S := by
        intro h
        obtain ⟨n, hn⟩ := hS.isPGroup ⟨(k : Γ), h⟩
        have hpow : (k : Γ) ^ 2 ^ n = 1 := by
          have := congrArg Subtype.val hn
          simpa using this
        have hdvd : r ∣ 2 ^ n := by
          rw [← horder]
          exact orderOf_dvd_of_pow_eq_one hpow
        exact hrne ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp (hrp.dvd_of_dvd_pow hdvd))
      have hL : ∀ n ∈ Q ⊓ Subgroup.normalizer (S : Set Γ), ∀ l ∈ Lm, n * l * n⁻¹ ∈ Lm :=
        fun n hn l hl => hLN n ⟨hQY hn.1, hn.2⟩ l hl
      exact hSL (w183l313_key_odd hB hS hL hZL hLZ hkL hkN hkS (by rw [horder]; exact hrodd))
    exact w183l313_outer_involution hQ hB hS hQY hYQ hcent hPY hPS hPN
      (fun k hkPk hkQ => hKle ⟨hkPk, hkQ⟩) hf hf2 hfQ


end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
