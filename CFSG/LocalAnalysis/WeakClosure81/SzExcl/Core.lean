module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCMin
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveMod
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem exists_mem_not_mem_inv_mul_conj_mem {A C : Subgroup G} {g : G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1)
    (hgA : ∀ a ∈ A, g⁻¹ * a * g ∈ A)
    (hg2 : ∀ a ∈ A, a⁻¹ * (g⁻¹ * (g⁻¹ * a * g) * g) ∈ C) {y : G} (hyA : y ∈ A)
    (hyC : y ∉ C) : ∃ x ∈ A, x ∉ C ∧ x⁻¹ * (g⁻¹ * x * g) ∈ C := by
  by_cases h : y⁻¹ * (g⁻¹ * y * g) ∈ C
  · exact ⟨y, hyA, hyC, h⟩
  · have hyg : g⁻¹ * y * g ∈ A := hgA y hyA
    have hsqy : y * y = 1 := hsq y hyA
    have hsqyg : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := hsq _ hyg
    have hcommy : y * (g⁻¹ * y * g) = (g⁻¹ * y * g) * y := hcomm y hyA _ hyg
    refine ⟨y * (g⁻¹ * y * g), A.mul_mem hyA hyg, ?_, ?_⟩
    · rwa [show y * (g⁻¹ * y * g) = y⁻¹ * (g⁻¹ * y * g) by
        rw [show y⁻¹ = y by exact inv_eq_of_mul_eq_one_right hsqy]]
    · have hmain : (y * (g⁻¹ * y * g))⁻¹ * (g⁻¹ * (y * (g⁻¹ * y * g)) * g) =
          y * (g⁻¹ * (g⁻¹ * y * g) * g) := by
        calc
          (y * (g⁻¹ * y * g))⁻¹ * (g⁻¹ * (y * (g⁻¹ * y * g)) * g)
              = ((g⁻¹ * y * g)⁻¹ * y⁻¹) *
                  ((g⁻¹ * y * g) * (g⁻¹ * (g⁻¹ * y * g) * g)) := by group
          _ = ((g⁻¹ * y * g) * y) *
                  ((g⁻¹ * y * g) * (g⁻¹ * (g⁻¹ * y * g) * g)) := by
                rw [inv_eq_of_mul_eq_one_right hsqyg, inv_eq_of_mul_eq_one_right hsqy]
          _ = (y * (g⁻¹ * y * g)) *
                  ((g⁻¹ * y * g) * (g⁻¹ * (g⁻¹ * y * g) * g)) := by rw [← hcommy]
          _ = y * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) *
                  (g⁻¹ * (g⁻¹ * y * g) * g) := by group
          _ = y * (g⁻¹ * (g⁻¹ * y * g) * g) := by rw [hsqyg]; group
      have hgy := hg2 y hyA
      rw [hmain]
      rwa [show y⁻¹ = y by exact inv_eq_of_mul_eq_one_right hsqy] at hgy

theorem conj_conj_eq_of_mul_self_eq {g j v y : G} (hg : g * g = j * v)
    (hb : ⁅y⁻¹, j⁻¹⁆ * v = v * ⁅y⁻¹, j⁻¹⁆) :
    g⁻¹ * (g⁻¹ * y * g) * g = y * ⁅y⁻¹, v⁻¹⁆ * ⁅y⁻¹, j⁻¹⁆ := by
  rw [show g⁻¹ * (g⁻¹ * y * g) * g = (g * g)⁻¹ * y * (g * g) by group, hg]
  have h1 : (j * v)⁻¹ * y * (j * v) = v⁻¹ * (j⁻¹ * y * j) * v := by group
  have h2 : j⁻¹ * y * j = y * ⁅y⁻¹, j⁻¹⁆ := by rw [commutatorElement_def]; group
  have h3 : v⁻¹ * y * v = y * ⁅y⁻¹, v⁻¹⁆ := by rw [commutatorElement_def]; group
  have h4 : v⁻¹ * ⁅y⁻¹, j⁻¹⁆ * v = ⁅y⁻¹, j⁻¹⁆ := by
    rw [show v⁻¹ * ⁅y⁻¹, j⁻¹⁆ * v = v⁻¹ * (⁅y⁻¹, j⁻¹⁆ * v) by group, hb]
    group
  rw [h1, h2]
  calc v⁻¹ * (y * ⁅y⁻¹, j⁻¹⁆) * v = (v⁻¹ * y * v) * (v⁻¹ * ⁅y⁻¹, j⁻¹⁆ * v) := by group
    _ = (y * ⁅y⁻¹, v⁻¹⁆) * ⁅y⁻¹, j⁻¹⁆ := by rw [h3, h4]
    _ = y * ⁅y⁻¹, v⁻¹⁆ * ⁅y⁻¹, j⁻¹⁆ := by group

private theorem inv_mul_conj_mul_eq {A : Subgroup G} {g : G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hgA : ∀ a ∈ A, g⁻¹ * a * g ∈ A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    (a * b)⁻¹ * (g⁻¹ * (a * b) * g) =
      (a⁻¹ * (g⁻¹ * a * g)) * (b⁻¹ * (g⁻¹ * b * g)) := by
  have ha' : g⁻¹ * a * g ∈ A := hgA a ha
  have hb' : g⁻¹ * b * g ∈ A := hgA b hb
  have h1 : (a * b)⁻¹ * (g⁻¹ * (a * b) * g) =
      b⁻¹ * (a⁻¹ * (g⁻¹ * a * g)) * (g⁻¹ * b * g) := by
    rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group]
    group
  have hbcomm : b⁻¹ * (a⁻¹ * (g⁻¹ * a * g)) =
      (a⁻¹ * (g⁻¹ * a * g)) * b⁻¹ := by
    have h1 := hcomm b⁻¹ (A.inv_mem hb) a⁻¹ (A.inv_mem ha)
    have h2 := hcomm b⁻¹ (A.inv_mem hb) (g⁻¹ * a * g) ha'
    calc b⁻¹ * (a⁻¹ * (g⁻¹ * a * g)) = (b⁻¹ * a⁻¹) * (g⁻¹ * a * g) := by group
      _ = (a⁻¹ * b⁻¹) * (g⁻¹ * a * g) := by rw [h1]
      _ = a⁻¹ * (b⁻¹ * (g⁻¹ * a * g)) := by group
      _ = a⁻¹ * ((g⁻¹ * a * g) * b⁻¹) := by rw [h2]
      _ = (a⁻¹ * (g⁻¹ * a * g)) * b⁻¹ := by group
  rw [h1, hbcomm]
  group

end General

section Core

variable {G : Type} [Group G] [Finite G]


variable {V H E J V₁ V₂ V₃ A : Subgroup G}

private theorem isElemAbelian_of_sevenSevenMinimal (h : Hyp73 V H E J)
    (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) : IsElemAbelian 2 A :=
  (seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le).mono hA.le_iSub

private theorem commutator_ne_bot_of_sevenSevenMinimal (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) :
    ⁅A, V₁⁆ ≠ ⊥ := by
  intro hbot
  have hcard := card_eq_card_commutator_pow h hc hA.toSevenSevenModule
  rw [hbot, Subgroup.card_bot] at hcard
  exact hA.ne_bot (Subgroup.card_eq_one.mp (by simpa using hcard))

private theorem sup_commutator_inf_centralizer_eq (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) :
    ⁅A, V₂⁆ ⊔ (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) =
      ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := by
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAea.comm ha hb
  have hA₁leA : ⁅A, V₁⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).1.le.trans inf_le_left
  have hA₂leA : ⁅A, V₂⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).2.1.le.trans inf_le_left
  have hBleA : A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) ≤ A := inf_le_left
  have hprops := inf_centralizer_properties h hc hA.toSevenSevenModule
    (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) rfl
  refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right hprops.1) ?_
  rw [card_sup_eq_mul_card_of_commute
      (fun p hp q hq => hAab p (hA₂leA hp) q (hBleA hq))
      (by rw [inf_comm]; exact hprops.2.2.1),
    card_sup_eq_mul_card_of_commute
      (fun p hp q hq => hAab p (hA₁leA hp) q (hA₂leA hq))
      (commutator_inf_commutator_eq_bot h hc hA.toSevenSevenModule).1,
    hprops.2.2.2.2.2]
  exact le_of_eq (Nat.mul_comm _ _)

private theorem inf_centralizer_eq_sup_commutator_of_sevenSeven (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) :
    A ⊓ Subgroup.centralizer (V₁ : Set G) =
      ⁅A, V₁⁆ ⊔ (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) := by
  have hprops := inf_centralizer_properties h hc hA.toSevenSevenModule
    (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) rfl
  rw [(inf_centralizer_eq_sup_commutator h hc hA.toSevenSevenModule).1, ← hprops.2.2.2.2.1]

theorem conj_mem_of_conj_eq (h : Hyp73 V H E J) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    {c g : G} (hcU : c ∈ U) (hc1 : c ≠ 1) (hgc : g⁻¹ * c * g = c) {x : G} (hx : x ∈ U) :
    g⁻¹ * x * g ∈ U := by
  have hcg : c * g = g * c := by
    calc c * g = g * (g⁻¹ * c * g) := by group
      _ = g * c := by rw [hgc]
  have hcle : g ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcg.symm
  have hgN : g ∈ Subgroup.normalizer (U : Set G) :=
    centralizer_le_normalizer_of_isTI (isTI_of_mem_omegaSet hU h.ti) hcU hc1 hcle
  have hginv : g⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normalizer (U : Set G)).inv_mem hgN
  have hmem : g⁻¹ * x * g⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hginv x).mp hx
  simpa using hmem

theorem exists_conj_conj_eq (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) {v g : G} (hv : v ∈ V₁)
    (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃) (hgJ : g * g * v⁻¹ ∈ J) {y : G} (hy : y ∈ A) :
    ∃ b ∈ A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G),
      g⁻¹ * (g⁻¹ * y * g) * g = y * ⁅y⁻¹, v⁻¹⁆ * b := by
  have hvX : v ∈ V₁ ⊔ V₂ ⊔ V₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hv)
  have hjX : g * g * v⁻¹ ∈ V₁ ⊔ V₂ ⊔ V₃ :=
    (V₁ ⊔ V₂ ⊔ V₃).mul_mem ((V₁ ⊔ V₂ ⊔ V₃).mul_mem hgX hgX)
      ((V₁ ⊔ V₂ ⊔ V₃).inv_mem hvX)
  have hjP : g * g * v⁻¹ ∈ J ⊓ (V₁ ⊔ V₂ ⊔ V₃) := ⟨hgJ, hjX⟩
  have hb : ⁅y⁻¹, (g * g * v⁻¹)⁻¹⁆ ∈ A ⊓ Subgroup.centralizer
      ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) :=
    commutator_le_inf_centralizer_of_sevenSevenMinimal h hc hA rfl
      (Subgroup.commutator_mem_commutator (A.inv_mem hy) ((J ⊓ (V₁ ⊔ V₂ ⊔ V₃)).inv_mem hjP))
  refine ⟨⁅y⁻¹, (g * g * v⁻¹)⁻¹⁆, hb, ?_⟩
  have hcomm : ⁅y⁻¹, (g * g * v⁻¹)⁻¹⁆ * v = v * ⁅y⁻¹, (g * g * v⁻¹)⁻¹⁆ :=
    ((Subgroup.mem_centralizer_iff.mp hb.2) v hvX).symm
  have hg : g * g = (g * g * v⁻¹) * v := by group
  exact conj_conj_eq_of_mul_self_eq hg hcomm

private theorem conj_eq_of_mem_centralizer_sup {g : G} (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃) {b : G}
    (hb : b ∈ A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :
    g⁻¹ * b * g = b := by
  have hcomm_bg : b * g = g * b := ((Subgroup.mem_centralizer_iff.mp hb.2) g hgX).symm
  calc g⁻¹ * b * g = g⁻¹ * (b * g) := by group
    _ = g⁻¹ * (g * b) := by rw [hcomm_bg]
    _ = b := by group

private theorem mem_normalizer_commutator_one (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) :
    g ∈ Subgroup.normalizer ((⁅A, V₁⁆ : Subgroup G) : Set G) := by
  have hv1 : v ≠ 1 := fun h1 => hvI (h1 ▸ (iSub V H E).one_mem)
  have hgcent : g ∈ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * v = g * (g⁻¹ * v * g) := by rw [hgv]
        _ = v * g := by group)
  have hgV₁ : g ∈ Subgroup.normalizer (V₁ : Set G) :=
    centralizer_le_normalizer_of_isTI (isTI_of_mem_omegaSet hc.mem₁ h.ti) hv hv1 hgcent
  have h := le_normalizer_commutator_of_le_of_le (P := Subgroup.zpowers g)
    (A := A) (B := V₁) (Subgroup.zpowers_le.mpr (hA.normalizes hgX))
    (Subgroup.zpowers_le.mpr hgV₁)
  exact h (Subgroup.mem_zpowers g)

private theorem conj_conj_eq_of_mem_commutator (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) {a : G} (ha : a ∈ ⁅A, V₁⁆) :
    g⁻¹ * (g⁻¹ * a * g) * g = a := by
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by simpa [pow_two] using hAea.2 x hx
  have hA₁eq : ⁅A, V₁⁆ = A ⊓ V₁ := (commutator_eq_inf h hc hA.toSevenSevenModule).1
  have haA₁ : a ∈ A ⊓ V₁ := hA₁eq ▸ ha
  obtain ⟨haA, haV₁⟩ := Subgroup.mem_inf.mp haA₁
  have hgA₁ := mem_normalizer_commutator_one h hc hA hv hvI hgX hgv
  obtain ⟨b, hbB, heq⟩ := exists_conj_conj_eq h hc hA hv hgX hgJ haA
  have hcab : ⁅a⁻¹, v⁻¹⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (isElemAbelian_of_mem_omegaSet h.elemAbelian hc.mem₁).comm
      (V₁.inv_mem haV₁) (V₁.inv_mem hv)
  have hb_eq : b = a⁻¹ * (g⁻¹ * (g⁻¹ * a * g) * g) := by rw [heq, hcab, mul_one]; group
  have ha₁g : g⁻¹ * a * g ∈ ⁅A, V₁⁆ := (Subgroup.mem_normalizer_iff''.mp hgA₁ a).mp ha
  have ha₁g2 : g⁻¹ * (g⁻¹ * a * g) * g ∈ ⁅A, V₁⁆ :=
    (Subgroup.mem_normalizer_iff''.mp hgA₁ (g⁻¹ * a * g)).mp ha₁g
  have hbA₁ : b ∈ ⁅A, V₁⁆ := by
    rw [hb_eq]
    exact (⁅A, V₁⁆).mul_mem ((⁅A, V₁⁆).inv_mem ha) ha₁g2
  have hbBot : b ∈ ⁅A, V₁⁆ ⊓
      (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) := ⟨hbA₁, hbB⟩
  have hprops := inf_centralizer_properties h hc hA.toSevenSevenModule
    (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) rfl
  have hbot : ⁅A, V₁⁆ ⊓
      (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) = ⊥ := by
    rw [inf_comm]; exact hprops.2.1
  rw [hbot] at hbBot
  have hb1 : b = 1 := Subgroup.mem_bot.mp hbBot
  rw [heq, hcab, mul_one, hb1, mul_one]

private theorem exists_ne_one_mem_commutator_conj_fixed (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) :
    ∃ a ∈ ⁅A, V₁⁆, a ≠ 1 ∧ g⁻¹ * a * g = a := by
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAea.comm ha hb
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hAea.2 a ha
  have hA₁eq : ⁅A, V₁⁆ = A ⊓ V₁ := (commutator_eq_inf h hc hA.toSevenSevenModule).1
  have hA₁leA : ⁅A, V₁⁆ ≤ A := hA₁eq.le.trans inf_le_left
  have hgA₁ := mem_normalizer_commutator_one h hc hA hv hvI hgX hgv
  have hA₁ne : ⁅A, V₁⁆ ≠ ⊥ := commutator_ne_bot_of_sevenSevenMinimal h hc hA
  obtain ⟨y₀, hy₀A₁, hy₀bot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hA₁ne)
  obtain ⟨a₀, ha₀A₁, ha₀bot, ha₀fix⟩ :=
    exists_mem_not_mem_inv_mul_conj_mem (A := ⁅A, V₁⁆) (C := ⊥) (g := g)
      (fun a ha b hb => hAab a (hA₁leA ha) b (hA₁leA hb))
      (fun a ha => hsq a (hA₁leA ha))
      (fun a ha => (Subgroup.mem_normalizer_iff''.mp hgA₁ a).mp ha)
      (fun a ha => by
        rw [conj_conj_eq_of_mem_commutator h hc hA hv hvI hgX hgv hgJ ha, inv_mul_cancel]
        exact (⊥ : Subgroup G).one_mem)
      hy₀A₁ hy₀bot
  have ha₀fix' : g⁻¹ * a₀ * g = a₀ := by
    have h1 : a₀⁻¹ * (g⁻¹ * a₀ * g) = 1 := Subgroup.mem_bot.mp ha₀fix
    calc g⁻¹ * a₀ * g = a₀ * (a₀⁻¹ * (g⁻¹ * a₀ * g)) := by group
      _ = a₀ := by rw [h1, mul_one]
  exact ⟨a₀, ha₀A₁, fun h1 => ha₀bot (h1 ▸ (⊥ : Subgroup G).one_mem), ha₀fix'⟩

theorem conj_mem_two (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) {v g : G} (hv : v ∈ V₁)
    (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃) (hgv : g⁻¹ * v * g = v)
    (hgJ : g * g * v⁻¹ ∈ J) {x : G} (hx : x ∈ V₂) : g⁻¹ * x * g ∈ V₂ := by
  classical
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAea.comm ha hb
  have hA₁leA : ⁅A, V₁⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).1.le.trans inf_le_left
  have hA₂leA : ⁅A, V₂⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).2.1.le.trans inf_le_left
  have hBleA : A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) ≤ A := inf_le_left
  have hprops := inf_centralizer_properties h hc hA.toSevenSevenModule
    (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) rfl
  obtain ⟨a₀, ha₀A₁, ha₀ne, ha₀fix⟩ :=
    exists_ne_one_mem_commutator_conj_fixed h hc hA hv hvI hgX hgv hgJ
  have hA₂B := sup_commutator_inf_centralizer_eq h hc hA
  obtain ⟨c₀, hc₀A₂, b₀, hb₀B, hab⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (A := ⁅A, V₂⁆) (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G))
      (fun p hp q hq => hAab p (hA₂leA hp) q (hBleA hq))
      (by rw [hA₂B]; exact Subgroup.mem_sup_left ha₀A₁)
  have hc₀V₂ : c₀ ∈ V₂ := ((commutator_eq_inf h hc hA.toSevenSevenModule).2.1 ▸ hc₀A₂).2
  have hc₀1 : c₀ ≠ 1 := by
    intro h1
    have ha₀B : a₀ ∈ A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) := by
      rw [← hab, h1, one_mul]
      exact hb₀B
    have hmem : a₀ ∈ ⁅A, V₁⁆ ⊓
        (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) := ⟨ha₀A₁, ha₀B⟩
    have hbot : ⁅A, V₁⁆ ⊓
        (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) = ⊥ := by
      rw [inf_comm]; exact hprops.2.1
    rw [hbot] at hmem
    exact ha₀ne (Subgroup.mem_bot.mp hmem)
  have hc₀fix : g⁻¹ * c₀ * g = c₀ := by
    have hc₀eq : c₀ = a₀ * b₀⁻¹ := by rw [← hab]; group
    rw [hc₀eq]
    calc g⁻¹ * (a₀ * b₀⁻¹) * g = (g⁻¹ * a₀ * g) * (g⁻¹ * b₀ * g)⁻¹ := by group
      _ = a₀ * b₀⁻¹ := by rw [ha₀fix, conj_eq_of_mem_centralizer_sup hgX hb₀B]
  exact conj_mem_of_conj_eq h hc.mem₂ hc₀V₂ hc₀1 hc₀fix hx

private theorem map_conj_commutator_two_le (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) :
    (⁅A, V₂⁆).map (MulAut.conj g⁻¹ : G →* G) ≤ ⁅A, V₂⁆ := by
  have hAle : A.map (MulAut.conj g⁻¹ : G →* G) ≤ A := by
    rintro x ⟨a, ha, rfl⟩
    have hmem : g⁻¹ * a * g ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp (hA.normalizes hgX) a).mp ha
    simpa [MulAut.conj_apply] using hmem
  have hV₂le : V₂.map (MulAut.conj g⁻¹ : G →* G) ≤ V₂ := by
    rintro x ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using conj_mem_two h hc hA hv hvI hgX hgv hgJ ha
  have hmap : (⁅A, V₂⁆).map (MulAut.conj g⁻¹ : G →* G) =
      ⁅A.map (MulAut.conj g⁻¹ : G →* G), V₂.map (MulAut.conj g⁻¹ : G →* G)⁆ :=
    Subgroup.map_commutator (H₁ := A) (H₂ := V₂) (f := (MulAut.conj g⁻¹ : G →* G))
  rw [hmap]
  exact Subgroup.commutator_mono hAle hV₂le

private theorem conj_eq_of_mul_of_mem_commutator_two (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) {a c' b' : G}
    (ha : a ∈ ⁅A, V₁⁆) (hc'A₂ : c' ∈ ⁅A, V₂⁆)
    (hb'B : b' ∈ A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G))
    (hab' : c' * b' = a) : g⁻¹ * a * g = a := by
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAea.comm ha hb
  have hA₂leA : ⁅A, V₂⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).2.1.le.trans inf_le_left
  have hBleA : A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) ≤ A := inf_le_left
  have hA₁A₂bot : ⁅A, V₁⁆ ⊓ ⁅A, V₂⁆ = ⊥ :=
    (commutator_inf_commutator_eq_bot h hc hA.toSevenSevenModule).1
  have hgA₁ := mem_normalizer_commutator_one h hc hA hv hvI hgX hgv
  have hb'g : g⁻¹ * b' * g = b' := conj_eq_of_mem_centralizer_sup hgX hb'B
  have hc'gA₂ : g⁻¹ * c' * g ∈ ⁅A, V₂⁆ := by
    apply map_conj_commutator_two_le h hc hA hv hvI hgX hgv hgJ
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹ : G →* G) hc'A₂
  have hd_mul := inv_mul_conj_mul_eq (A := A) hAab
    (fun x hx => (Subgroup.mem_normalizer_iff''.mp (hA.normalizes hgX) x).mp hx)
    (hA₂leA hc'A₂) (hBleA hb'B)
  have hdb' : b'⁻¹ * (g⁻¹ * b' * g) = 1 := by rw [hb'g]; group
  have hd_eq : a⁻¹ * (g⁻¹ * a * g) = c'⁻¹ * (g⁻¹ * c' * g) := by
    rw [← hab', hd_mul, hdb', mul_one]
  have hda : a⁻¹ * (g⁻¹ * a * g) ∈ ⁅A, V₁⁆ :=
    (⁅A, V₁⁆).mul_mem ((⁅A, V₁⁆).inv_mem ha)
      ((Subgroup.mem_normalizer_iff''.mp hgA₁ a).mp ha)
  have hdc'A₁ : c'⁻¹ * (g⁻¹ * c' * g) ∈ ⁅A, V₁⁆ := by rw [← hd_eq]; exact hda
  have hdc'A₂ : c'⁻¹ * (g⁻¹ * c' * g) ∈ ⁅A, V₂⁆ :=
    (⁅A, V₂⁆).mul_mem ((⁅A, V₂⁆).inv_mem hc'A₂) hc'gA₂
  have hdc'1 : c'⁻¹ * (g⁻¹ * c' * g) = 1 := by
    have hmem : c'⁻¹ * (g⁻¹ * c' * g) ∈ ⁅A, V₁⁆ ⊓ ⁅A, V₂⁆ := ⟨hdc'A₁, hdc'A₂⟩
    rw [hA₁A₂bot] at hmem
    exact Subgroup.mem_bot.mp hmem
  calc g⁻¹ * a * g = a * (a⁻¹ * (g⁻¹ * a * g)) := by group
    _ = a := by rw [hd_eq, hdc'1, mul_one]

private theorem conj_eq_of_mem_commutator (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) {a : G} (ha : a ∈ ⁅A, V₁⁆) :
    g⁻¹ * a * g = a := by
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAea.comm ha hb
  have hA₂leA : ⁅A, V₂⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).2.1.le.trans inf_le_left
  have hBleA : A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) ≤ A := inf_le_left
  have hA₂B := sup_commutator_inf_centralizer_eq h hc hA
  obtain ⟨c', hc'A₂, b', hb'B, hab'⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (A := ⁅A, V₂⁆) (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G))
      (fun p hp q hq => hAab p (hA₂leA hp) q (hBleA hq))
      (by rw [hA₂B]; exact Subgroup.mem_sup_left ha)
  exact conj_eq_of_mul_of_mem_commutator_two h hc hA hv hvI hgX hgv hgJ ha hc'A₂ hb'B hab'

private theorem conj_conj_eq_mem_inf_centralizer (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃) (hgJ : g * g * v⁻¹ ∈ J) {y : G}
    (hy : y ∈ A) :
    y⁻¹ * (g⁻¹ * (g⁻¹ * y * g) * g) ∈ A ⊓ Subgroup.centralizer (V₁ : Set G) := by
  obtain ⟨b, hbB, heq⟩ := exists_conj_conj_eq h hc hA hv hgX hgJ hy
  have hd_eq : y⁻¹ * (g⁻¹ * (g⁻¹ * y * g) * g) = ⁅y⁻¹, v⁻¹⁆ * b := by rw [heq]; group
  have hCeq := inf_centralizer_eq_sup_commutator_of_sevenSeven h hc hA
  have hmem : ⁅y⁻¹, v⁻¹⁆ * b ∈
      ⁅A, V₁⁆ ⊔ (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :=
    (⁅A, V₁⁆ ⊔ (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G))).mul_mem
      (Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator (A.inv_mem hy) (V₁.inv_mem hv)))
      (Subgroup.mem_sup_right hbB)
  rw [hd_eq, hCeq]
  exact hmem

private theorem inf_centralizer_lt (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) :
    A ⊓ Subgroup.centralizer (V₁ : Set G) < A := by
  refine lt_of_le_of_ne inf_le_left fun hCA => ?_
  have hAle : A ≤ Subgroup.centralizer (V₁ : Set G) := inf_eq_left.mp hCA
  have hbot : ⁅A, V₁⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hAle
  exact commutator_ne_bot_of_sevenSevenMinimal h hc hA hbot

private theorem false_of_mem_not_mem_inf_centralizer (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) {x : G} (hxA : x ∈ A)
    (hxC : x ∉ A ⊓ Subgroup.centralizer (V₁ : Set G))
    (hxgg : g⁻¹ * (g⁻¹ * x * g) * g = x) : False := by
  obtain ⟨b, hbB, heq⟩ := exists_conj_conj_eq h hc hA hv hgX hgJ hxA
  have h1 : x * ⁅x⁻¹, v⁻¹⁆ * b = x := by rw [← heq, hxgg]
  have h2 : ⁅x⁻¹, v⁻¹⁆ * b = 1 := by
    have hx1 : x⁻¹ * (x * ⁅x⁻¹, v⁻¹⁆ * b) = ⁅x⁻¹, v⁻¹⁆ * b := by group
    have hx2 : x⁻¹ * x = 1 := by group
    have h := congrArg (fun t => x⁻¹ * t) h1
    rwa [hx1, hx2] at h
  have hprops := inf_centralizer_properties h hc hA.toSevenSevenModule
    (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) rfl
  have hc_bot : ⁅x⁻¹, v⁻¹⁆ = 1 := by
    have hmem : ⁅x⁻¹, v⁻¹⁆ ∈ ⁅A, V₁⁆ ⊓
        (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) := by
      refine ⟨Subgroup.commutator_mem_commutator (A.inv_mem hxA) (V₁.inv_mem hv), ?_⟩
      rw [mul_eq_one_iff_eq_inv.mp h2]
      exact (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)).inv_mem hbB
    have hbot : ⁅A, V₁⁆ ⊓
        (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) = ⊥ := by
      rw [inf_comm]; exact hprops.2.1
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hxv : x * v = v * x := by
    have h := commutatorElement_eq_one_iff_mul_comm.mp hc_bot
    calc x * v = (v⁻¹ * x⁻¹)⁻¹ := by group
      _ = (x⁻¹ * v⁻¹)⁻¹ := by rw [h]
      _ = v * x := by group
  have hxcent : x ∈ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxv
  have hxC' : x ∈ A ⊓ Subgroup.centralizer (V₁ : Set G) := by
    rw [← inf_centralizer_singleton_eq_inf_centralizer h hc.mem₁ (hc.small V₁ hc.mem₁)
      hA.le_iSub hv hvI]
    exact ⟨hxA, hxcent⟩
  exact hxC hxC'

theorem conj_eq_of_mem_inf_centralizer (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    {v g : G} (hv : v ∈ V₁) (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃)
    (hgv : g⁻¹ * v * g = v) (hgJ : g * g * v⁻¹ ∈ J) {c : G}
    (hcC : c ∈ A ⊓ Subgroup.centralizer (V₁ : Set G)) : g⁻¹ * c * g = c := by
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => (isElemAbelian_of_sevenSevenMinimal h hA).comm ha hb
  have hprops := inf_centralizer_properties h hc hA.toSevenSevenModule
    (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) rfl
  have hA₁B : ⁅A, V₁⁆ ⊔ (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) =
      ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := hprops.2.2.2.2.1
  have hcA₁A₂ : c ∈ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := by
    have h1 := (inf_centralizer_eq_sup_commutator h hc hA.toSevenSevenModule).1
    rw [h1] at hcC
    exact hcC
  have hA₁leA : ⁅A, V₁⁆ ≤ A :=
    (commutator_eq_inf h hc hA.toSevenSevenModule).1.le.trans inf_le_left
  have hBleA : A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) ≤ A := inf_le_left
  obtain ⟨a, ha, b, hb, hab⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := ⁅A, V₁⁆)
      (B := A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G))
      (fun p hp q hq => hAab p (hA₁leA hp) q (hBleA hq)) (by rw [hA₁B]; exact hcA₁A₂)
  rw [← hab]
  rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group,
    conj_eq_of_mem_commutator h hc hA hv hvI hgX hgv hgJ ha,
    conj_eq_of_mem_centralizer_sup hgX hb]

theorem false_of_mul_self_mem (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A) {v g : G} (hv : v ∈ V₁)
    (hvI : v ∉ iSub V H E) (hgX : g ∈ V₁ ⊔ V₂ ⊔ V₃) (hgv : g⁻¹ * v * g = v)
    (hgJ : g * g * v⁻¹ ∈ J) : False := by
  classical
  have hAea := isElemAbelian_of_sevenSevenMinimal h hA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAea.comm ha hb
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hAea.2 a ha
  have hClt := inf_centralizer_lt h hc hA
  obtain ⟨y, hyA, hyC⟩ := SetLike.exists_of_lt hClt
  obtain ⟨x, hxA, hxC, hxd⟩ :=
    exists_mem_not_mem_inv_mul_conj_mem (A := A) (C := A ⊓ Subgroup.centralizer (V₁ : Set G))
      (g := g) hAab hsq
      (fun a ha => (Subgroup.mem_normalizer_iff''.mp (hA.normalizes hgX) a).mp ha)
      (fun y hy => conj_conj_eq_mem_inf_centralizer h hc hA hv hgX hgJ hy) hyA hyC
  set c : G := x⁻¹ * (g⁻¹ * x * g) with hcdef
  have hcC : c ∈ A ⊓ Subgroup.centralizer (V₁ : Set G) := hxd
  have hcA : c ∈ A := hcC.1
  have hcg : g⁻¹ * c * g = c :=
    conj_eq_of_mem_inf_centralizer h hc hA hv hvI hgX hgv hgJ hcC
  have hxc : g⁻¹ * x * g = x * c := by rw [hcdef]; group
  have hxgg : g⁻¹ * (g⁻¹ * x * g) * g = x := by
    calc g⁻¹ * (g⁻¹ * x * g) * g = (g⁻¹ * x * g) * (g⁻¹ * c * g) := by
          rw [hcdef]; group
      _ = (x * c) * c := by rw [hxc, hcg]
      _ = x := by rw [show (x * c) * c = x * (c * c) by group, hsq c hcA, mul_one]
  exact false_of_mem_not_mem_inf_centralizer h hc hA hv hvI hgX hgv hgJ hxA hxC hxgg

end Core

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
