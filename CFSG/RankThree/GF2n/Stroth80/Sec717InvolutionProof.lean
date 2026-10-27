module

public import CFSG.RankThree.GF2n.Stroth80.Sec717CorBHypProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveBridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75

section Abstract

variable {X : Type*} [Group X]

private theorem conjBy_trans {S : Subgroup X} {x y z : X} (h₁ : ∃ h ∈ S, h * x * h⁻¹ = y)
    (h₂ : ∃ h ∈ S, h * y * h⁻¹ = z) : ∃ h ∈ S, h * x * h⁻¹ = z := by
  obtain ⟨a, ha, rfl⟩ := h₁
  obtain ⟨b, hb, rfl⟩ := h₂
  exact ⟨b * a, S.mul_mem hb ha, by group⟩

private theorem conjBy_symm {S : Subgroup X} {x y : X} (h₁ : ∃ h ∈ S, h * x * h⁻¹ = y) :
    ∃ h ∈ S, h * y * h⁻¹ = x := by
  obtain ⟨a, ha, rfl⟩ := h₁
  exact ⟨a⁻¹, S.inv_mem ha, by group⟩

variable {V L : Subgroup X}

theorem exists_normalizer_conj_eq_of_mem_ti (hVL : V ≤ L)
    (hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hti : ∀ g : X, ∀ a ∈ V, a ≠ 1 → g * a * g⁻¹ ∈ V → g ∈ normalizer (V : Set X))
    (hsemi : ∀ z ∈ L, z ∉ V → ∀ w ∈ V, ∃ m ∈ normalizer (L : Set X), m * z * m⁻¹ = w * z)
    {k : X} (hkL : k ∈ normalizer (L : Set X)) (hkV : k ∉ normalizer (V : Set X))
    {a c : X} (ha : a ∈ V) (ha1 : a ≠ 1) (hc : c ∈ V) (hc1 : c ≠ 1) :
    ∃ h ∈ normalizer (L : Set X), h * a * h⁻¹ = c := by
  have hkL' : k⁻¹ ∈ normalizer (L : Set X) := inv_mem hkL
  have ha' : k * a * k⁻¹ ∈ L := (mem_normalizer_iff.mp hkL a).mp (hVL ha)
  have ha'V : k * a * k⁻¹ ∉ V := fun h => hkV (hti k a ha ha1 h)
  have hc' : k⁻¹ * c * k ∈ L := by
    have h := (mem_normalizer_iff.mp hkL' c).mp (hVL hc)
    rwa [inv_inv] at h
  have hc'V : k⁻¹ * c * k ∉ V := by
    intro h
    have h1 := hti k⁻¹ c hc hc1 (by rwa [inv_inv])
    exact hkV (by simpa using inv_mem h1)
  obtain ⟨m₁, hm₁L, hm₁⟩ := hsemi _ ha' ha'V c hc
  obtain ⟨m₂, hm₂L, hm₂⟩ := hsemi _ hc' hc'V a ha
  have hca : k * (a * (k⁻¹ * c * k)) * k⁻¹ = c * (k * a * k⁻¹) := by
    rw [hLc c (hVL hc) _ ha']
    group
  refine conjBy_trans ⟨k, hkL, rfl⟩ (conjBy_trans ⟨m₁, hm₁L, hm₁⟩
    (conjBy_trans (conjBy_symm ⟨k, hkL, hca⟩)
      (conjBy_trans (conjBy_symm ⟨m₂, hm₂L, hm₂⟩) ⟨k, hkL, ?_⟩)))
  group

theorem exists_normalizer_conj_eq_of_ti_of_irred (hVL : V ≤ L)
    (hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hti : ∀ g : X, ∀ a ∈ V, a ≠ 1 → g * a * g⁻¹ ∈ V → g ∈ normalizer (V : Set X))
    (hsemi : ∀ z ∈ L, z ∉ V → ∀ w ∈ V, ∃ m ∈ normalizer (L : Set X), m * z * m⁻¹ = w * z)
    {k : X} (hkL : k ∈ normalizer (L : Set X)) (hkV : k ∉ normalizer (V : Set X))
    (hirr : ∀ T : Subgroup X, V ≤ T → T ≤ L →
      (∀ g ∈ normalizer (L : Set X), g ∈ normalizer (T : Set X)) → T = V ∨ T = L)
    {x y : X} (hx : x ∈ L) (hy : y ∈ L) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ h ∈ normalizer (L : Set X), h * x * h⁻¹ = y := by
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ V, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    apply hkV
    rw [mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hcon n hn, mul_one, mul_inv_cancel]
      exact V.one_mem
    · intro hn
      have h1 : n = 1 := calc
        n = k⁻¹ * (k * n * k⁻¹) * k := by group
        _ = 1 := by rw [hcon _ hn]; group
      rw [h1]
      exact V.one_mem
  set s : Set X := {u | ∃ g ∈ normalizer (L : Set X), g⁻¹ * u * g ∈ V} with hs
  have hsL : s ⊆ L := by
    rintro u ⟨g, hg, hu⟩
    have h := (mem_normalizer_iff.mp hg _).mp (hVL hu)
    rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at h
  have hTL : closure s ≤ L := (closure_le L).mpr hsL
  have hVT : V ≤ closure s := fun v hv =>
    subset_closure ⟨1, one_mem _, by rwa [inv_one, one_mul, mul_one]⟩
  have hconj : ∀ g ∈ normalizer (L : Set X), ∀ z ∈ closure s, g * z * g⁻¹ ∈ closure s := by
    intro g hg z hz
    induction hz using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨g', hg', hu'⟩ := hu
      refine subset_closure ⟨g * g', mul_mem hg hg', ?_⟩
      rwa [show (g * g')⁻¹ * (g * u * g⁻¹) * (g * g') = g'⁻¹ * u * g' by group]
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul u w _ _ hu hw =>
      rw [show g * (u * w) * g⁻¹ = g * u * g⁻¹ * (g * w * g⁻¹) by group]
      exact mul_mem hu hw
    | inv u _ hu =>
      rw [show g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ by group]
      exact inv_mem hu
  have hTn : ∀ g ∈ normalizer (L : Set X), g ∈ normalizer ((closure s : Subgroup X) : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro n
    refine ⟨hconj g hg n, fun hn => ?_⟩
    have h := hconj g⁻¹ (inv_mem hg) _ hn
    rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at h
  have hTeq : closure s = L := by
    rcases hirr _ hVT hTL hTn with h | h
    · exfalso
      apply hkV
      apply hti k a₀ ha₀ ha₀1
      rw [← h]
      refine subset_closure ⟨k, hkL, ?_⟩
      rwa [show k⁻¹ * (k * a₀ * k⁻¹) * k = a₀ by group]
    · exact h
  have step : ∀ u ∈ s, ∀ w ∈ closure s,
      (w = 1 ∨ ∃ h ∈ normalizer (L : Set X), h * a₀ * h⁻¹ = w) →
        (u * w = 1 ∨ ∃ h ∈ normalizer (L : Set X), h * a₀ * h⁻¹ = u * w) := by
    rintro u ⟨g, hg, hv⟩ w hw ih
    have hw' : g⁻¹ * w * g ∈ L := by
      have h := (mem_normalizer_iff.mp (inv_mem hg) w).mp (hTL hw)
      rwa [inv_inv] at h
    have huw : g * (g⁻¹ * u * g * (g⁻¹ * w * g)) * g⁻¹ = u * w := by group
    by_cases hwV : g⁻¹ * w * g ∈ V
    · by_cases h1 : g⁻¹ * u * g * (g⁻¹ * w * g) = 1
      · left
        rw [← huw, h1]
        group
      · right
        exact conjBy_trans (exists_normalizer_conj_eq_of_mem_ti hVL hLc hti hsemi hkL hkV ha₀
          ha₀1 (V.mul_mem hv hwV) h1) ⟨g, hg, huw⟩
    · right
      have hw1 : w ≠ 1 := by
        rintro rfl
        apply hwV
        rw [mul_one, inv_mul_cancel]
        exact V.one_mem
      obtain ⟨m, hmL, hm⟩ := hsemi _ hw' hwV _ hv
      exact conjBy_trans (ih.resolve_left hw1) (conjBy_trans ⟨g⁻¹, inv_mem hg, by group⟩
        (conjBy_trans ⟨m, hmL, hm⟩ ⟨g, hg, huw⟩))
  have key : ∀ z ∈ closure s, z = 1 ∨ ∃ h ∈ normalizer (L : Set X), h * a₀ * h⁻¹ = z := by
    intro z hz
    induction hz using Subgroup.closure_induction_left with
    | one => exact Or.inl rfl
    | mul_left u hu w hw ih => exact step u hu w hw ih
    | inv_mul_cancel u hu w hw ih =>
      obtain ⟨g, hg, hv⟩ := hu
      refine step u⁻¹ ⟨g, hg, ?_⟩ w hw ih
      have h := V.inv_mem hv
      rwa [show (g⁻¹ * u * g)⁻¹ = g⁻¹ * u⁻¹ * g by group] at h
  have hxs : x ∈ closure s := by rw [hTeq]; exact hx
  have hys : y ∈ closure s := by rw [hTeq]; exact hy
  exact conjBy_trans (conjBy_symm ((key x hxs).resolve_left hx1)) ((key y hys).resolve_left hy1)

end Abstract

section Stroth

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem sec717_bar_eq_or_eq_of_inv (hInv : Sec717InvStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {L : Subgroup G} (hL : Sec717L hc t Z0 L)
    (T : Subgroup ↥(bar M Q (H0 M Z)))
    (hVT : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤ T)
    (hTL : T ≤ (bar M Q L).subgroupOf (bar M Q (H0 M Z)))
    (hTn : ∀ g ∈ normalizer (((bar M Q L).subgroupOf (bar M Q (H0 M Z)) :
        Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z))),
      g ∈ normalizer ((T : Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z)))) :
    T = (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ∨
      T = (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQL : Q ≤ L := hL.1
  have hLCN : L ≤ hc.CN t := hL.2.1
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLH : L ≤ H0 M Z := fun x hx => hc.Rt_le_H0 t (hCNR (hLCN hx))
  have hbL : bar M Q L ≤ bar M Q (H0 M Z) := bar_mono' hLH
  have hbZ : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans (hc.Rt_le_H0 t))
  obtain ⟨A, hQA, hAM, hA⟩ := exists_pre hQM (T.map (bar M Q (H0 M Z)).subtype)
  have hbA : bar M Q A ≤ bar M Q (H0 M Z) := by
    rw [hA]
    exact map_subtype_le T
  have hTA : T = (bar M Q A).subgroupOf (bar M Q (H0 M Z)) := by
    rw [hA]
    exact (comap_map_eq_self_of_injective (bar M Q (H0 M Z)).subtype_injective T).symm
  have hZA : Z0 ≤ A := by
    intro z hz
    have hzM : z ∈ M := hc.centre_le_M t hZ0 hz
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hzM⟩ : M) ∈ bar M Q Z0 :=
      (mk_mem_bar_iff_sec4 hQZ0 _).mpr hz
    have h3 : (⟨_, hbZ h1⟩ : ↥(bar M Q (H0 M Z))) ∈ T := hVT (mem_subgroupOf.mpr h1)
    have h4 : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hzM⟩ : M) ∈ bar M Q A := by
      rw [hA]
      exact ⟨_, h3, rfl⟩
    exact (mk_mem_bar_iff_sec4 hQA _).mp h4
  have hAL : A ≤ L := by
    intro a ha
    have haM : a ∈ M := hAM ha
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨a, haM⟩ : M) ∈ bar M Q A :=
      (mk_mem_bar_iff_sec4 hQA _).mpr ha
    rw [hA] at h1
    obtain ⟨b, hbT, hb⟩ := mem_map.mp h1
    have h2 : (b : Mbar M Q) ∈ bar M Q L := mem_subgroupOf.mp (hTL hbT)
    have hb' : (b : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) (⟨a, haM⟩ : M) := hb
    rw [hb'] at h2
    exact (mk_mem_bar_iff_sec4 hQL _).mp h2
  have hAR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A := by
    intro r hr
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have hrL : r ∈ normalizer (L : Set G) := conjSubgroup_eq_self_iff.mp (hL.2.2.2.1 r hr)
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) (⟨r, hrM⟩ : M) ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr (hc.Rt_le_H0 t hr)
    have h1 : (⟨_, hmem⟩ : ↥(bar M Q (H0 M Z))) ∈ normalizer
        (((bar M Q L).subgroupOf (bar M Q (H0 M Z)) : Subgroup ↥(bar M Q (H0 M Z))) :
          Set ↥(bar M Q (H0 M Z))) := by
      rw [mem_normalizer_subgroupOf_iff' hbL]
      exact mk_mem_normalizer_bar_of_normalizer hQL _ hrL
    have h2 := hTn _ h1
    rw [hTA, mem_normalizer_subgroupOf_iff' hbA] at h2
    exact conjSubgroup_eq_self_iff.mpr (mem_normalizer_of_mk_mem_normalizer_bar hQA hAM _ h2)
  rcases hInv G M Q Z B hc n t hs hp3 Z0 hZ0 A hZA (hAL.trans hLCN) hAR with h | h | h
  · left
    rw [hTA, h]
  · right
    have hAeq : A = L := le_antisymm hAL (by rw [h]; exact hLCN)
    rw [hTA, hAeq]
  · right
    have hAeq : A = L := eq_of_le_of_card_ge hAL (le_of_eq (by rw [h.2.2.1, hL.2.2.1]))
    rw [hTA, hAeq]

theorem sec717_exists_bar_move (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {L : Subgroup G}
    (hL : Sec717L hc t Z0 L) (hmove : ¬ NormH0L M Z L ≤ NormH0 M Z Z0) :
    ∃ k : ↥(bar M Q (H0 M Z)),
      k ∈ normalizer (((bar M Q L).subgroupOf (bar M Q (H0 M Z)) :
        Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z))) ∧
      k ∉ normalizer (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :
        Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z))) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQL : Q ≤ L := hL.1
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLH : L ≤ H0 M Z := fun x hx => hc.Rt_le_H0 t (hCNR (hL.2.1 hx))
  have hbL : bar M Q L ≤ bar M Q (H0 M Z) := bar_mono' hLH
  have hbZ : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans (hc.Rt_le_H0 t))
  obtain ⟨k, hk, hkN⟩ := SetLike.not_le_iff_exists.mp hmove
  have hkH : k ∈ H0 M Z := (mem_inf.mp hk).1
  have hkV : k ∉ normalizer (Z0 : Set G) := fun h => hkN (mem_inf.mpr ⟨hkH, h⟩)
  have hkM : k ∈ M := (mem_inf.mp hkH).1
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) (⟨k, hkM⟩ : M) ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr hkH
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [mem_normalizer_subgroupOf_iff' hbL]
    exact mk_mem_normalizer_bar_of_normalizer hQL _ (mem_inf.mp hk).2
  · rw [mem_normalizer_subgroupOf_iff' hbZ]
    exact fun h => hkV (mem_normalizer_of_mk_mem_normalizer_bar hQZ0 hZ0M _ h)

theorem sec717Involution_of_frame (hF : Sec717MoveFrameStatement) (hInv : Sec717InvStatement) :
    Sec717InvolutionStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hcase hmove x hx y hy hx1 hy1 _ _
  obtain ⟨K, _, E, _, _, _, B', φ, Tt, q, F⟩ :=
    hF G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn
  obtain ⟨k, hkL, hkV⟩ := sec717_exists_bar_move hc hs hZ0 hL hmove
  have hNbL : ∀ m ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      m ∈ normalizer (((bar M Q L).subgroupOf (bar M Q (H0 M Z)) :
        Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z))) := by
    intro m hm
    have hmV := F.Rb_le_K m (F.Nb_le_Rb hm)
    rw [mem_normalizer_iff]
    intro l
    refine ⟨F.L_norm m hmV l, fun hl => ?_⟩
    have h := F.L_norm m⁻¹ (inv_mem hmV) _ hl
    rwa [show m⁻¹ * (m * l * m⁻¹) * m⁻¹⁻¹ = l by group] at h
  obtain ⟨h, -, hh⟩ := exists_normalizer_conj_eq_of_ti_of_irred F.V_le_L F.L_comm F.ti
    (fun z hz hzV w hw => by
      obtain ⟨m, hm, hmz⟩ := F.Nb_semi z (F.L_le_Nb hz) hzV w hw
      exact ⟨m, hNbL m hm, hmz⟩)
    hkL hkV (fun T h1 h2 h3 => sec717_bar_eq_or_eq_of_inv hInv hc hs hp3 hZ0 hL T h1 h2 h3)
    hx hy hx1 hy1
  exact ⟨h, hh⟩

end Stroth

end CFSG.RankThree.GF2n.Stroth80
