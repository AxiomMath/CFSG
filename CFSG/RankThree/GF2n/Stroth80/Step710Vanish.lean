module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7NoWildPlusSix
public import CFSG.RankThree.GF2n.Stroth80.Sec7WildSubgroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Step710VanishStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → (Conc71b hc n t ∨ Conc71c hc n t ∨ Conc71d hc n t) →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) →
    ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z

theorem conj_centralizes_sq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {g : G} (hg : g ∈ M) :
    (∀ z ∈ Z, (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = z) ∧ (g * t * g⁻¹) ^ 2 ∈ Q := by
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  refine ⟨fun z hz => ?_, ?_⟩
  · have hz' : g⁻¹ * z * g ∈ Z := by simpa using hZn g⁻¹ (M.inv_mem hg) z hz
    have h1 := hc.LB_centralizes_Z ht _ hz'
    calc (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = g * (t * (g⁻¹ * z * g) * t⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
      _ = z := by group
  · have ht2 : t ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB ht
    rw [conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) (t ^ 2)).mp ht2

theorem step710Wv_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hty : Conc71b hc n t ∨ Conc71c hc n t ∨ Conc71d hc n t)
    {g : G} (hg : g ∈ M) (hxt : ⁅g * t * g⁻¹, t⁆ ∈ Q)
    (hvan : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hx : ConjMod M Q t (g * t * g⁻¹) := ⟨hxM, g, hg, by simpa using Q.one_mem⟩
  obtain ⟨hxZ, hx2⟩ := conj_centralizes_sq hc ht hg
  have hQx := comm_conjMod_mem_conj h310chi hc hs hx
  rcases hty with ⟨hMi, -⟩ | ⟨hp, -⟩ | ⟨hp, hn⟩
  · exact no_wild_minus6_of hA hPts h52a h52b h310chi hc hs hMi hxM hxt hvan hx2 hQx
  · exact no_wild_plus6_of h34 hA hPts h52a h52b h310chi hc hs hp hxM hxt hvan hxZ hx2 hQx
  · exact no_wild_plus8_of hA hPts h52a h52b h310chi hc hs hp (by omega) hxM hxt hvan hx2 hQx

theorem step710Core_of_vanish (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hK : Sec7CRWStatement)
    (hSch : Sec7SchurStatement) (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hVan : Step710VanishStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hty : Conc71b hc n t ∨ Conc71c hc n t ∨ Conc71d hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hH1 : ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) :
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0 := by
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hSV := sec7SV_of_parts h34 h310chi hZc hZV
  have hSW := sec7SW_of_parts h34 h310chi hZc hZV
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0H : Z0 ≤ H0 M Z := fun z hz => hc.Rt_le_H0 t (hZ0.le hz)
  have hQn : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hadm : ∀ {g : G}, g ∈ M → (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y ∈ conjSubgroup g Z0, Sec7Adm hc t y := by
    intro g hg hΓ y hy
    have hcommt : ∀ y' ∈ conjSubgroup g Z0, ⁅y', t⁆ ∈ Q := by
      intro y' hy'
      have := Q.inv_mem (hΓ t htZ0 y' hy')
      rwa [commutatorElement_inv] at this
    have hyM : ∀ y' ∈ conjSubgroup g Z0, y' ∈ M := by
      intro y' hy'
      have hz := hZ0M (mem_conjSubgroup.mp hy')
      have := M.mul_mem (M.mul_mem hg hz) (M.inv_mem hg)
      simpa [mul_assoc] using this
    have hxmem : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using htZ0
    have hxt : ⁅g * t * g⁻¹, t⁆ ∈ Q := hcommt _ hxmem
    have hvan := hVan G M Q Z B hc n t hs hty Z0 hZ0 hH1 g hg hΓ
    have hwv := step710Wv_of h34 hA hPts h52a h52b h310chi hc hs hty hg hxt hvan
    exact ⟨hyM y hy, hcommt y hy, hSV G M Q Z B hc n t hs Z0 hZ0 g hg hvan y hy,
      hSW G M Q Z B hc n t hs Z0 hZ0 g hg hwv y hy⟩
  have hcomm : ∀ y : G, Sec7Adm hc t y → ∀ k ∈ hc.CN t, ⁅k, y⁆ ∈ Z0 := fun y hy k hk =>
    comm_N_of_vanish h34 h310chi hK h52a hA hc hs hZ0 hy.mem hy.comm_t hy.vanish hy.wv k hk
  refine commutator_Egen_le hQZ0 ?_
  intro g₁ hg₁ hΓ₁ g₂ hg₂ hΓ₂ y₁ hy₁ y₂ hy₂
  have hnz : ∀ {g : G}, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y ∈ conjSubgroup g Z0, y ∈ Subgroup.normalizer (Z0 : Set G) := fun hΓ y hy =>
    conj_centre_normalizes hQZ0 (fun z hz => hΓ z hz y hy)
  have hy₁' : y₁⁻¹ ∈ conjSubgroup g₁ Z0 := (conjSubgroup g₁ Z0).inv_mem hy₁
  have hy₂' : y₂⁻¹ ∈ conjSubgroup g₂ Z0 := (conjSubgroup g₂ Z0).inv_mem hy₂
  have h₁ := hadm hg₁ hΓ₁ y₁ hy₁
  have h₁' := hadm hg₁ hΓ₁ _ hy₁'
  have h₂ := hadm hg₂ hΓ₂ y₂ hy₂
  have h₂' := hadm hg₂ hΓ₂ _ hy₂'
  have hw3 := commutator_adm_comm_R hc hs hZ0 hcomm h₁ h₁' h₂ h₂' (hnz hΓ₁ y₁ hy₁)
    (hnz hΓ₂ y₂ hy₂)
  have hwM : ⁅y₁, y₂⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem h₁.mem h₂.mem) (M.inv_mem h₁.mem)) (M.inv_mem h₂.mem)
  have hwH : ⁅y₁, y₂⁆ ∈ H0 M Z := by
    have h1 := conjSubgroup_mem_H0 hc hZ0H hg₁ hy₁
    have h2 := conjSubgroup_mem_H0 hc hZ0H hg₂ hy₂
    rw [commutatorElement_def]
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem ((H0 M Z).mul_mem h1 h2) ((H0 M Z).inv_mem h1))
      ((H0 M Z).inv_mem h2)
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  have hVW := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  obtain ⟨hy₁W, hy₁W'⟩ := h₁.conj_Wt hc
  obtain ⟨hy₂W, hy₂W'⟩ := h₂.conj_Wt hc
  refine hSch G M Q Z B hc n t hs Z0 hZ0 _ hwH
    (commutator_R_comm_of_comm hc hs hZ0 hwM hw3) ?_
  exact commutator_comm_mem_Z hQn hS.conj sec39_Z_le_Vt hVW hWQ h₁.mem h₂.mem hy₁W hy₁W'
    hy₂W hy₂W' h₁.vanish h₂.vanish h₁.wv h₂.wv

theorem step710E_of_vanish (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h77 : Stroth77Statement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hNC : Sec7ConjStatement) (hK : Sec7CRWStatement) (hSch : Sec7SchurStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hVan : Step710VanishStatement) :
    Step710EStatement := by
  intro G _ _ M Q Z B hc n t hs hty Z0 hZ0 hH1
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZL : Z0 ≤ LB M Q B := fun z hz => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hN : ∀ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ν ∈ Subgroup.normalizer (Z0 : Set G) := by
    intro ν hν hνL
    have hsub : conjSubgroup ν Z0 ≤ LB M Q B :=
      (Subgroup.map_mono hZL).trans (conjSubgroup_eq_self_iff.mpr hνL).le
    exact conjSubgroup_eq_self_iff.mp (hH1 ν hν hsub)
  have hZCN := Z0_le_CN_of_34 h34 hZc hc hs hZ0
  have hnom : ¬ OmegaMinusNat hc t 2 := not_omegaMinus_two_of_cases hty
  rcases h77 G M Q Z B hc n t hs with ha | hb | hc3 | hd
  · obtain ⟨s, hsR, hsc, g, hg, hgL, hgN⟩ := ha
    have hsZ0 : s ∈ Z0 := (hZ0 s).mpr ⟨hsR, hsc⟩
    have hsM : s ∈ M := hc.Rt_le_M t hsR
    have hxM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
    have hconj : ConjMod M Q s (g * s * g⁻¹) := ⟨hxM, g, hg, by simp [Q.one_mem]⟩
    obtain ⟨ν, hνM, hνL, hνQ⟩ :=
      hNC G M Q Z B hc n t hs hnom Z0 hZ0 s hsZ0 _ hgL hconj
    have hνs : ν * s * ν⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp (hN ν hνM hνL) s).mp hsZ0
    have hgs : g * s * g⁻¹ ∈ Z0 := by
      have e : g * s * g⁻¹ = (g * s * g⁻¹ * (ν * s * ν⁻¹)⁻¹) * (ν * s * ν⁻¹) := by group
      rw [e]
      exact Z0.mul_mem (hQZ0 hνQ) hνs
    exact absurd (hZCN hgs) hgN
  · exact step710Core_of_vanish h34 h310chi hZc hZV hK hSch hA hPts h52a h52b hVan hc hs
      (Or.inl hb) hZ0 hH1
  · exact step710Core_of_vanish h34 h310chi hZc hZV hK hSch hA hPts h52a h52b hVan hc hs
      (Or.inr (Or.inl hc3)) hZ0 hH1
  · exact step710Core_of_vanish h34 h310chi hZc hZV hK hSch hA hPts h52a h52b hVan hc hs
      (Or.inr (Or.inr hd)) hZ0 hH1

end CFSG.RankThree.GF2n.Stroth80
