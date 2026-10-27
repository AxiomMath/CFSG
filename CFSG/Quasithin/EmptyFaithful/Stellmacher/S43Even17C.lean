module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  unfold conjSub
  rw [Subgroup.map_sup]
  have h1 : conjSub g A = A := conjSub_eq_of_mem_normalizer hA
  have h2 : conjSub g B = B := conjSub_eq_of_mem_normalizer hB
  unfold conjSub at h1 h2
  rw [h1, h2]

omit [Finite G] in
theorem le_normalizer_sup {K A B : Subgroup G} (hA : K ≤ Subgroup.normalizer (A : Set G))
    (hB : K ≤ Subgroup.normalizer (B : Set G)) :
    K ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun _ hk =>
  mem_normalizer_sup (hA hk) (hB hk)

namespace Sit43'

variable {α : Geo H M}

theorem Vn_le_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {δ : Geo H M} (hδ : δ ∈ nbrs α) : Vn δ ≤ stab α :=
  (hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hδ).trans (pCoreOf_le 2 _)

theorem not_comm_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {δ : Geo H M} (hδ : δ ∈ nbrs α) {x : G} (hxα : x ∈ stab α)
    (hxM : x ∉ Mab α δ) {E : Subgroup G} (hE : stab α ≤ Subgroup.normalizer (E : Set G))
    (hEW : E ≤ Wn α)
    (hVE : Vn δ ⊔ E ≠ Wn α) : ¬ ∀ v ∈ Vn δ, x * v * x⁻¹ * v⁻¹ ∈ E := by
  intro hcon
  have hxn : x ∈ Subgroup.normalizer ((Vn δ ⊔ E : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun n hn => ?_
    rw [sup_comm] at hn ⊢
    have hVn : Vn δ ≤ Subgroup.normalizer (E : Set G) := (Vn_le_stab hA h26 hs hb hδ).trans hE
    obtain ⟨e, he, v, hv, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hVn).mp hn
    have e1 : x * (e * v) * x⁻¹ = (x * e * x⁻¹) * ((x * v * x⁻¹ * v⁻¹) * v) := by group
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (hcon v hv)) (Subgroup.mem_sup_right hv))
    exact (Subgroup.mem_normalizer_iff.mp (hE hxα) e).mp he
  have hgen := hs.sup_Qv_zpowers_eq_stab hA h26 hδ hxα hxM
  have hn : stab α ≤ Subgroup.normalizer ((Vn δ ⊔ E : Subgroup G) : Set G) := by
    rw [← hgen]
    refine sup_le (le_normalizer_sup ((pCoreOf_le 2 _).trans (stab_le_normalizer_Vn δ))
      ((Qv_le_stab_of_mem_nbrs hA (nbrs_symm hδ)).trans hE)) (Subgroup.zpowers_le.mpr hxn)
  exact hVE (sup_eq_Wn hA h26 hs hδ hEW hn)

theorem Vn_inf_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {δ : Geo H M} (hδ : δ ∈ nbrs α) {x : G} (hxα : x ∈ stab α)
    (hxM : x ∉ Mab α δ)
    (htwo : ∀ v₁ ∈ Vn δ, ∀ v₂ ∈ Vn δ, x * v₁ * x⁻¹ * v₁⁻¹ ∉ Zv α →
      x * v₂ * x⁻¹ * v₂⁻¹ ∉ Zv α → (x * v₁ * x⁻¹ * v₁⁻¹)⁻¹ * (x * v₂ * x⁻¹ * v₂⁻¹) ∈ Zv α)
    {E : Subgroup G} (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hZE : Zv α ≤ E)
    (hEW : E ≤ Wn α) (hVE : Vn δ ⊔ E ≠ Wn α) : Vn δ ⊓ E = Zv α := by
  have hQ := not_comm_le hA h26 hs hb hδ hxα hxM hE hEW hVE
  have hkey : ∀ v ∈ Vn δ ⊓ E, x * v * x⁻¹ * v⁻¹ ∈ Zv α := by
    intro v hv
    by_contra hv'
    apply hQ
    intro v' hv'V
    by_cases h' : x * v' * x⁻¹ * v'⁻¹ ∈ Zv α
    · exact hZE h'
    · have h1 := hZE (htwo v hv.1 v' hv'V hv' h')
      have h2 : x * v * x⁻¹ * v⁻¹ ∈ E := by
        have h3 : x * v * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hE hxα) v).mp hv.2
        exact E.mul_mem h3 (E.inv_mem hv.2)
      have e : x * v' * x⁻¹ * v'⁻¹ =
          (x * v * x⁻¹ * v⁻¹) * ((x * v * x⁻¹ * v⁻¹)⁻¹ * (x * v' * x⁻¹ * v'⁻¹)) := by group
      rw [e]
      exact E.mul_mem h2 h1
  have hZN : Zv α ≤ Vn δ ⊓ E := le_inf (Sit43.Zv_le_Vn hδ) hZE
  have hxn : x ∈ Subgroup.normalizer ((Vn δ ⊓ E : Subgroup G) : Set G) :=
    mem_normalizer_of_comm_mem hZN hkey
  have hQn : Qv δ ≤ Subgroup.normalizer ((Vn δ ⊓ E : Subgroup G) : Set G) := by
    intro q hq
    have h1 := (pCoreOf_le 2 _).trans (stab_le_normalizer_Vn δ) hq
    have h2 := ((Qv_le_stab_of_mem_nbrs hA (nbrs_symm hδ)).trans hE) hq
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    simp only [Subgroup.mem_inf]
    rw [h1 y, h2 y]
  have hgen := hs.sup_Qv_zpowers_eq_stab hA h26 hδ hxα hxM
  have hn : stab α ≤ Subgroup.normalizer ((Vn δ ⊓ E : Subgroup G) : Set G) := by
    rw [← hgen]
    exact sup_le hQn (Subgroup.zpowers_le.mpr hxn)
  exact hs.S13 hA h26 hδ hn hZN inf_le_left

theorem fix_eq_bot (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {δ : Geo H M} (hδ : δ ∈ nbrs α) {E : Subgroup G}
    (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hZE : Zv α ≤ E) (hEW : E ≤ Wn α)
    (hVE : Vn δ ⊔ E ≠ Wn α)
    (hP : ∀ X : Subgroup G, stab α ≤ Subgroup.normalizer (X : Set G) → E < X → X ≤ Wn α →
      Vn δ ⊔ X = Wn α) :
    ∀ w ∈ Wn α, (∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E) → w ∈ E := by
  have hWα : Wn α ≤ stab α := (hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)
  have hEc : ∀ {g y : G}, g ∈ stab α → y ∈ E → g * y * g⁻¹ ∈ E := fun hg hy =>
    (Subgroup.mem_normalizer_iff.mp (hE hg) _).mp hy
  let X : Subgroup G :=
    { carrier := {w | w ∈ Wn α ∧ ∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E}
      one_mem' := ⟨(Wn α).one_mem, fun g _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨(Wn α).mul_mem ha hb', fun g hg => ?_⟩
        rw [comm_mul_eq]
        exact E.mul_mem (ha' g hg) (hEc (hWα ha) (hb'' g hg))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(Wn α).inv_mem ha, fun g hg => ?_⟩
        have e : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hEc ((stab α).inv_mem (hWα ha)) (E.inv_mem (ha' g hg)) }
  have hXmem : ∀ w, w ∈ X ↔ w ∈ Wn α ∧ ∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E := fun _ => Iff.rfl
  have hEX : E ≤ X := fun e he => ⟨hEW he, fun g hg => E.mul_mem (hEc hg he) (E.inv_mem he)⟩
  have hXW : X ≤ Wn α := fun w hw => hw.1
  have hXn : stab α ≤ Subgroup.normalizer (X : Set G) := by
    refine Sit43.le_normalizer_of_conj_mem fun h hh w hw => ⟨?_, fun g hg => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hh) w).mp hw.1
    · have e : g * (h * w * h⁻¹) * g⁻¹ * (h * w * h⁻¹)⁻¹ =
          h * ((h⁻¹ * g * h) * w * (h⁻¹ * g * h)⁻¹ * w⁻¹) * h⁻¹ := by group
      rw [e]
      exact hEc hh (hw.2 _ ((stab α).mul_mem ((stab α).mul_mem ((stab α).inv_mem hh) hg) hh))
  intro w hw hfix
  by_contra hwE
  have hlt : E < X := lt_of_le_of_ne hEX fun h => hwE (h ▸ (show w ∈ X from ⟨hw, hfix⟩))
  have hVX := hP X hXn hlt hXW
  obtain ⟨D⟩ := hs.exists_dict hA hδ
  obtain ⟨k, hk, hkα, hψ⟩ := hs.exists_Qst_of_S5That hA h26 hδ D
    (Subgroup.subset_closure (by simp) : (Equiv.swap 0 2 : Equiv.Perm (Fin 5)) ∈ S5That)
  obtain ⟨C, hC, -, hCn⟩ := exists_centralizer_quotient hE (stab_le_normalizer_Wn α)
  have hkC : k ∈ C := by
    refine (hC k).mpr ⟨hkα, fun n hn => ?_⟩
    rw [← hVX, sup_comm] at hn
    obtain ⟨y, hy, v, hv, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      ((Vn_le_stab hA h26 hs hb hδ).trans hXn)).mp hn
    have h1 : k * y * k⁻¹ * y⁻¹ ∈ E := hy.2 k hkα
    have h2 : k * v * k⁻¹ * v⁻¹ ∈ E := hZE (hs.comm_Qst_Vn_mem hA h26 hδ hk hv)
    have h3 : k * (y * v) * k⁻¹ * (y * v)⁻¹ ∈ E := by
      rw [comm_mul_eq]
      exact E.mul_mem h1 (hEc (hWα hy.1) h2)
    have e : ⁅y * v, k⁆ = (k * (y * v) * k⁻¹ * (y * v)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact E.inv_mem h3
  have hLC : oTwoRes (stab α) ≤ C := D.oTwoRes_le_of_swap hCn hkC hkα hψ
  have hLn : Lres α ≤ Subgroup.normalizer ((Vn δ ⊔ E : Subgroup G) : Set G) := by
    intro l hl
    have hlα : l ∈ stab α := oTwoRes_le _ hl
    refine mem_normalizer_of_conj_mem fun n hn => ?_
    rw [sup_comm] at hn ⊢
    obtain ⟨e, he, v, hv, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      ((Vn_le_stab hA h26 hs hb hδ).trans hE)).mp hn
    have h1 : ⁅v, l⁆ ∈ E := ((hC l).mp (hLC hl)).2 v (hs.Vn_le_Wn hA h26 hδ hv)
    have e1 : l * (e * v) * l⁻¹ = (l * e * l⁻¹) * (⁅v, l⁆⁻¹ * v) := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hEc hlα he))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (E.inv_mem h1)) (Subgroup.mem_sup_right hv))
  have hSn : stab α ⊓ stab δ ≤ Subgroup.normalizer ((Vn δ ⊔ E : Subgroup G) : Set G) :=
    le_normalizer_sup (inf_le_right.trans (stab_le_normalizer_Vn δ)) (inf_le_left.trans hE)
  have hTL : stab α ⊓ stab δ ≤ Subgroup.normalizer (Lres α : Set G) :=
    inf_le_left.trans (le_normalizer_oTwoRes (stab α))
  have hn : stab α ≤ Subgroup.normalizer ((Vn δ ⊔ E : Subgroup G) : Set G) := fun g hg => by
    obtain ⟨a, ha, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTL).mp
      (le_oTwoRes_sup_of_isSylowTwoOf (sylow_stab_inf_left hA hδ) hg)
    exact Subgroup.mul_mem _ (hLn ha) (hSn ht)
  exact hVE (sup_eq_Wn hA h26 hs hδ hEW hn)

omit [Finite G] in
theorem isNormalIn_of {K : Subgroup G} (hK : stab α ≤ Subgroup.normalizer (K : Set G))
    (hKW : K ≤ Wn α) : IsNormalIn (stab α) (Wn α) K :=
  ⟨hKW, fun _ hg y hy => (Subgroup.mem_normalizer_iff.mp (hK hg) y).mp hy⟩

theorem step5 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb4 : bMin H M = 4) {δ : Geo H M} (hδ : δ ∈ nbrs α) {x : G} (hxα : x ∈ stab α)
    (hxM : x ∉ Mab α δ)
    (htwo : ∀ v₁ ∈ Vn δ, ∀ v₂ ∈ Vn δ, x * v₁ * x⁻¹ * v₁⁻¹ ∉ Zv α →
      x * v₂ * x⁻¹ * v₂⁻¹ ∉ Zv α → (x * v₁ * x⁻¹ * v₁⁻¹)⁻¹ * (x * v₂ * x⁻¹ * v₂⁻¹) ∈ Zv α) :
    ∃ E F : Subgroup G, stab α ≤ Subgroup.normalizer (E : Set G) ∧
      stab α ≤ Subgroup.normalizer (F : Set G) ∧ Zv α ≤ E ∧ E < F ∧ F ≤ Wn α ∧
      Vn δ ⊓ E = Zv α ∧ Nat.card (Vn δ) = 2 ^ 6 ∧
      (∀ q ∈ Qv α, ∀ w ∈ Wn α, q * w * q⁻¹ * w⁻¹ ∈ E) ∧
      ((IsOrthSec (stab α) E F ∧ F = Wn α) ∨
        (IsNatSec (stab α) E F ∧ F.relIndex (Wn α) ≤ 2 ∧
          E.relIndex ((Vn δ ⊔ E) ⊓ F) ≤ 2)) := by
  have hb : 3 ≤ bMin H M := by omega
  have hb' : 4 ≤ bMin H M := by omega
  have hVW := hs.Vn_le_Wn hA h26 hδ
  let P : Subgroup G → Prop := fun E => stab α ≤ Subgroup.normalizer (E : Set G) ∧ Zv α ≤ E ∧
    E ≤ Wn α ∧ Vn δ ⊔ E ≠ Wn α
  have hZP : P (Zv α) := by
    refine ⟨stab_le_normalizer_Zv hA α, le_rfl, hs.Zv_le_Wn hA h26, fun h => ?_⟩
    rw [sup_eq_left.mpr (Sit43.Zv_le_Vn hδ)] at h
    exact not_stab_le_normalizer_Vn hA h26 hs hb hδ (h ▸ stab_le_normalizer_Wn α)
  obtain ⟨E, ⟨hE, hZE, hEW, hVE⟩, hEmax⟩ := WellFounded.has_min wellFounded_gt {E | P E}
    ⟨Zv α, hZP⟩
  have hP : ∀ X : Subgroup G, stab α ≤ Subgroup.normalizer (X : Set G) → E < X →
      X ≤ Wn α → Vn δ ⊔ X = Wn α := by
    intro X hX hEX hXW
    by_contra h
    exact hEmax X ⟨hX, hZE.trans hEX.le, hXW, h⟩ hEX
  have hR := Vn_inf_eq hA h26 hs hb hδ hxα hxM htwo hE hZE hEW hVE
  have hC := fix_eq_bot hA h26 hs hb hδ hE hZE hEW hVE hP
  have hEW' : E < Wn α := lt_of_le_of_ne hEW fun h => hVE (by rw [h]; exact sup_eq_right.mpr hVW)
  obtain ⟨F, ⟨hF, hEF, hFW⟩, hFmin⟩ := WellFounded.has_min wellFounded_lt
    {F : Subgroup G | stab α ≤ Subgroup.normalizer (F : Set G) ∧ E < F ∧ F ≤ Wn α}
    ⟨Wn α, stab_le_normalizer_Wn α, hEW', le_rfl⟩
  have hchief : IsChiefStep (stab α) (Wn α) E F := by
    refine ⟨isNormalIn_of hF hFW, isNormalIn_of hE hEW, hEF, fun K hK hEK hKF => ?_⟩
    by_cases hKE : K = E
    · exact Or.inl hKE
    · right
      have hEK' : E < K := lt_of_le_of_ne hEK (Ne.symm hKE)
      by_contra hKF'
      exact hFmin K ⟨Sit43.le_normalizer_of_conj_mem hK.2, hEK', hK.1⟩
        (lt_of_le_of_ne hKF hKF')
  have hnc : ¬ IsCentralStep (stab α) E F := by
    intro hcen
    obtain ⟨f, hfF, hfE⟩ := IsConcreteLE.exists_of_lt hEF
    exact hfE (hC f (hFW hfF) fun g hg => hcen g hg f hfF)
  have hVF := hP F hF hEF hFW
  obtain ⟨hQ, -, hidx, hcase⟩ := hs.S17' hA h26 hb' hδ hE hF hZE hEF hFW hchief hnc hC hVF
  have hD4 : Nat.card (Vn δ) = 2 ^ 6 := by
    have h1 : E.relIndex (Vn δ ⊔ E) = (Zv α).relIndex (Vn δ) := by
      rw [Sit43.relIndex_sup_of_le_normalizer ((Vn_le_stab hA h26 hs hb hδ).trans hE),
        ← Subgroup.inf_relIndex_right, inf_comm, hR]
    have h2 := Subgroup.relIndex_mul_card (Zv α) (Vn δ)
    rw [inf_eq_left.mpr (Sit43.Zv_le_Vn hδ), hs.card_Zv_false hs.vα] at h2
    have hδv : vtype δ = true := Sit43.vtype_true_of_adj hs.vα hδ
    rcases hs.card_Vn_cases hA h26 hb hδv with h | h | h
    · exact h
    · rw [h] at h2; omega
    · rw [h] at h2; omega
  exact ⟨E, F, hE, hF, hZE, hEF, hFW, hR, hD4, hQ, hcase⟩

end Sit43'

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
