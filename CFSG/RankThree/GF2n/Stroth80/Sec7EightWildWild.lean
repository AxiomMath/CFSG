module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Pair
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightAssembly
public import CFSG.RankThree.GF2n.Stroth80.Sec7WildJoin

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step76EightWildWitnessStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∃ g' ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g' Z0, ⁅z, y⁆ ∈ Q) ∧
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g' * t * g'⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) ∧
      Ut Q Z (g' * t * g'⁻¹) ≤ Vt M (LB M Q B) B Z t ⊔ Ut Q Z (g * t * g⁻¹) ∧
      ¬ Ut Q Z (g' * t * g'⁻¹) ≤ Vt M (LB M Q B) B Z t

section Assembly

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conjSubgroup_eq_of_forall_mem {A R : Subgroup G}
    (h : ∀ r ∈ R, ∀ p ∈ A, r * p * r⁻¹ ∈ A) : ∀ r ∈ R, conjSubgroup r A = A := by
  intro r hr
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · have hy' : r⁻¹ * y * r ∈ A := mem_conjSubgroup.mp hy
    have := h r hr _ hy'
    simpa [mul_assoc] using this
  · rw [mem_conjSubgroup]
    have := h r⁻¹ (R.inv_mem hr) y hy
    simpa using this

theorem step76EightKWildWild_of_witness (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (h310chi : Stroth310ChiStatement) (hSec : Sec7WVSecCardStatement) (h71 : Stroth71Statement)
    (hZV : Sec7ZVStatement) (hW : Step76EightWildWitnessStatement)
    (hTW : Step76EightKTameWildStatement) : Step76EightKWildWildStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ hw₁ g₂ hg₂ hΓ₂ hw₂ a ha b hb
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hQM : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hQM m hm) y).mp hy
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hVU : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs.toSec5.notQ
  have hUt : ∀ h ∈ M, Ut Q Z (h * t * h⁻¹) = conjSubgroup h (Vt M (LB M Q B) B Z t) :=
    fun h hh => by
      rw [Ut_conj_of_normalizes (hc.conj_Q_eq hh) (hc.conj_Z_eq hh) t, hVU]
  have hcommt : ∀ h : G, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup h Z0, ⁅z, y⁆ ∈ Q) →
      ⁅h * t * h⁻¹, t⁆ ∈ Q := by
    intro h hΓ
    have hxmem : h * t * h⁻¹ ∈ conjSubgroup h Z0 := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using htZ0
    have := Q.inv_mem (hΓ t htZ0 _ hxmem)
    rwa [commutatorElement_inv] at this
  let 𝒲 : Set G := {b' | ∃ h ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup h Z0, ⁅z, y⁆ ∈ Q) ∧
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅h * t * h⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) ∧
      b' ∈ Ut Q Z (h * t * h⁻¹)}
  have hb𝒲 : b ∈ 𝒲 := ⟨g₂, hg₂, hΓ₂, hw₂, hb⟩
  have hrZ0 : ∀ r ∈ Rt M (LB M Q B) t, r ∈ Subgroup.normalizer (Z0 : Set G) := fun r hr =>
    hZ0.mem_normalizer (fun ρ hρ y hy => (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy) hr
  have hW𝒲 : ∀ r ∈ Rt M (LB M Q B) t, ∀ b' ∈ 𝒲, r * b' * r⁻¹ ∈ 𝒲 := by
    rintro r hr b' ⟨h, hh, hΓh, ⟨w₀, hw₀, hw₀V⟩, hb'⟩
    have hrM : r ∈ M := hRM hr
    have hrN : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
      hc.Rt_normalizes_Vt ht hr
    refine ⟨r * h, M.mul_mem hrM hh, ?_, ?_, ?_⟩
    · intro z hz y hy
      have hy' : (r * h)⁻¹ * y * (r * h) ∈ Z0 := mem_conjSubgroup.mp hy
      have hy1 : r⁻¹ * y * r ∈ conjSubgroup h Z0 := by
        rw [mem_conjSubgroup]
        have e : h⁻¹ * (r⁻¹ * y * r) * h = (r * h)⁻¹ * y * (r * h) := by group
        rw [e]
        exact hy'
      have hz1 : r⁻¹ * z * r ∈ Z0 := by
        have := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ (hrZ0 r hr)) z).mp hz
        simpa using this
      have h1 := hΓh _ hz1 _ hy1
      have e : ⁅z, y⁆ = r * ⁅r⁻¹ * z * r, r⁻¹ * y * r⁆ * r⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hQn r hrM _ h1
    · refine ⟨r * w₀ * r⁻¹, conj_mem_Wt (hQM r hrM) hrN hw₀, fun hmem => hw₀V ?_⟩
      have e : ⁅(r * h) * t * (r * h)⁻¹, r * w₀ * r⁻¹⁆ = r * ⁅h * t * h⁻¹, w₀⁆ * r⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e] at hmem
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) _).mp hmem
      simpa [mul_assoc] using h1
    · rw [hUt (r * h) (M.mul_mem hrM hh), conjSubgroup_mul]
      rw [hUt h hh] at hb'
      rw [mem_conjSubgroup]
      have : r⁻¹ * (r * b' * r⁻¹) * r = b' := by group
      rw [this]
      exact hb'
  let S : Subgroup G := Subgroup.centralizer 𝒲
  have hSR : ∀ r ∈ Rt M (LB M Q B) t, ∀ p ∈ S, r * p * r⁻¹ ∈ S := by
    intro r hr p hp
    rw [Subgroup.mem_centralizer_iff] at hp ⊢
    intro b' hb'
    have h1 := hp (r⁻¹ * b' * r) (by
      have := hW𝒲 r⁻¹ ((Rt M (LB M Q B) t).inv_mem hr) b' hb'
      simpa using this)
    calc b' * (r * p * r⁻¹) = r * ((r⁻¹ * b' * r) * p) * r⁻¹ := by group
      _ = r * (p * (r⁻¹ * b' * r)) * r⁻¹ := by rw [h1]
      _ = (r * p * r⁻¹) * b' := by group
  have hVS : Vt M (LB M Q B) B Z t ≤ S := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    rintro b' ⟨h, hh, hΓh, -, hb'⟩
    have hb'' : h⁻¹ * b' * h ∈ Vt M (LB M Q B) B Z t := by
      rw [hUt h hh] at hb'
      exact mem_conjSubgroup.mp hb'
    have hbW := sec7_pair_mem_W h71 h310chi hc hs hno hh (s := h * t * h⁻¹) (by simp)
      (hcommt h hΓh) _ hb''
    have e : h * (h⁻¹ * b' * h) * h⁻¹ = b' := by group
    rw [e] at hbW
    exact (Subgroup.mem_centralizer_iff.mp hbW.2 v hv).symm
  have hx₁M : g₁ * t * g₁⁻¹ ∈ M := M.mul_mem (M.mul_mem hg₁ htM) (M.inv_mem hg₁)
  have hx₁t : ⁅g₁ * t * g₁⁻¹, t⁆ ∈ Q := hcommt g₁ hΓ₁
  have hx₁V : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g₁ * t * g₁⁻¹, v⁆ ∈ Z :=
    sec7_pair_vanish h71 hc hs hno hg₁ (s := g₁ * t * g₁⁻¹) (by simp) hx₁t
  have hQx : ∀ w ∈ Q, ⁅g₁ * t * g₁⁻¹, w⁆ ∈ conjSubgroup g₁ (Vt M (LB M Q B) B Z t) := by
    intro w hw
    have h1 : ⁅w, g₁ * t * g₁⁻¹⁆ ∈ ⁅Q, Subgroup.zpowers (g₁ * t * g₁⁻¹)⁆ :=
      Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers _)
    have h2 : ⁅g₁ * t * g₁⁻¹, w⁆ ∈ Ut Q Z (g₁ * t * g₁⁻¹) := by
      rw [← commutatorElement_inv]
      exact (Ut Q Z (g₁ * t * g₁⁻¹)).inv_mem (Subgroup.mem_sup_left h1)
    rwa [hUt g₁ hg₁] at h2
  obtain ⟨hVinf, hVlt, hPW, hPR, hPcard⟩ := sec7_wild_join h52a hA h310chi hSec hc hs h4 hg₁
    hx₁M hx₁t hx₁V hQx hw₁
  obtain ⟨g', hg'M, hΓ', htame', hUtle, hUtnot⟩ :=
    hW G M Q Z B hc n t hs hno h4 Z0 hZ0 g₁ hg₁ hΓ₁ hw₁
  rw [hUt g₁ hg₁] at hUtle
  have hUtS : Ut Q Z (g' * t * g'⁻¹) ≤ S := by
    intro a' ha'
    rw [Subgroup.mem_centralizer_iff]
    rintro b' ⟨h, hh, hΓh, hwh, hb'⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hTW G M Q Z B hc n t hs hno h4 Z0 hZ0 g'
      hg'M hΓ' htame' h hh hΓh hwh a' ha' b' hb')).symm
  let A' : Subgroup G := S ⊓ (Vt M (LB M Q B) B Z t ⊔ conjSubgroup g₁ (Vt M (LB M Q B) B Z t))
  have hVA : Vt M (LB M Q B) B Z t ≤ A' := le_inf hVS le_sup_left
  have hAP : A' ≤ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g₁ (Vt M (LB M Q B) B Z t) := inf_le_right
  have hAW : A' ≤ Wt Q (Vt M (LB M Q B) B Z t) := hAP.trans hPW
  have hAR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A' = A' := by
    refine conjSubgroup_eq_of_forall_mem fun r hr p hp => ⟨hSR r hr p hp.1, ?_⟩
    have h1 : r * p * r⁻¹ ∈ conjSubgroup r (Vt M (LB M Q B) B Z t ⊔
        conjSubgroup g₁ (Vt M (LB M Q B) B Z t)) := by
      rw [mem_conjSubgroup]
      have e : r⁻¹ * (r * p * r⁻¹) * r = p := by group
      rw [e]
      exact hp.2
    rwa [hPR r hr] at h1
  have hUtA : Ut Q Z (g' * t * g'⁻¹) ≤ A' := le_inf hUtS hUtle
  have hVlt' : Vt M (LB M Q B) B Z t < A' := by
    refine lt_of_le_of_ne hVA fun h => hUtnot ?_
    rw [h]
    exact hUtA
  obtain ⟨k, hk⟩ := (hSec G M Q Z B hc n t hs A' hVA hAW hAR 4 (by norm_num)).2 h4 (by norm_num)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hP1 : Nat.card ↥A' ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hk]
      simp
    exact hVlt'.ne (Subgroup.eq_of_le_of_card_ge hVA hP1)
  have hAcard : Nat.card ↥A' ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊔
      conjSubgroup g₁ (Vt M (LB M Q B) B Z t)) := Subgroup.card_le_of_le hAP
  rw [hPcard] at hAcard
  have hk1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have h8 : 2 ^ (4 - 1) * k = 8 * k := by norm_num
    rw [h8] at hk
    have hpow : Nat.card ↥Z ^ 16 ≤ Nat.card ↥Z ^ (8 * k) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 16 ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 :=
      calc Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 16 ≤
          Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (8 * k) :=
            Nat.mul_le_mul_left _ hpow
        _ = Nat.card ↥A' := hk.symm
        _ ≤ _ := hAcard
    have h2 : Nat.card ↥Z ^ 16 ≤ Nat.card ↥Z ^ 8 := Nat.le_of_mul_le_mul_left h1 hVpos
    have h3 : Nat.card ↥Z ^ 8 < Nat.card ↥Z ^ 16 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  subst hk1
  have hA8 : Nat.card ↥A' = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 := by
    rw [hk]
    norm_num
  have hAeq : A' = Vt M (LB M Q B) B Z t ⊔ conjSubgroup g₁ (Vt M (LB M Q B) B Z t) :=
    Subgroup.eq_of_le_of_card_ge hAP (by rw [hA8, ← hPcard])
  have haP : a ∈ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g₁ (Vt M (LB M Q B) B Z t) := by
    rw [hUt g₁ hg₁] at ha
    exact Subgroup.mem_sup_right ha
  rw [← hAeq] at haP
  have h1 := Subgroup.mem_centralizer_iff.mp haP.1 b hb𝒲
  exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm

end Assembly

end CFSG.RankThree.GF2n.Stroth80
