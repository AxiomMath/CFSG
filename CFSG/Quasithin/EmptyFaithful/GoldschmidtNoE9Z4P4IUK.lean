module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4IM
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4IMod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Main
public import CFSG.Quasithin.EmptyFaithful.S146F9
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Rec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

section UK

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9_exists_conj_uK (h35 : Lemma1435) (h5 : Stage1461Five) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s)
    {u : G} (hu : u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex (tZero T u) = 2) :
    ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧ ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥ := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHK : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  have hKU : uK T M H ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer hHU
  have hZK := e9_Z_le_uK h5 S hred
  have hR₁H : R₁ ≤ H := hdat.plane₁.2.1.trans hred.le
  have hHi : uHi T M H R₁ ≤ uK T M H :=
    sup_le (Subgroup.commutator_mono le_rfl hR₁H) hZK
  have huG : u ∈ mcOf T := by
    rcases hu with hu | hu
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure hR₁H hu)
    · exact S.mem_mcOf_of_mem_conjClosure hH
        (uHi_le_conjClosure (hdat.plane₂.2.1.trans hred.le) hu)
  obtain ⟨g, -, hUle, -, hall⟩ := e9z4_lemma_14_6_13 h35 S hred hshape
  obtain ⟨hnorm, hnc⟩ := hall R₁ hdat.plane₁
  obtain ⟨a, ha, x, hx, hax⟩ : ∃ a ∈ uHi T M H R₁, ∃ x ∈ conjSub g⁻¹ (uK T M H),
      a * x * a⁻¹ * x⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hcon
    push Not at hcon
    exact hnc (Subgroup.commutator_le.mpr fun a ha x hx => hcon a ha x hx)
  have hxN : x ∈ Subgroup.normalizer (uHi T M H R₁ : Set G) :=
    hnorm (conjSub_mono g⁻¹ hKU hx)
  have hu'₁ : a * x * a⁻¹ * x⁻¹ ∈ uHi T M H R₁ := by
    have h2 : x * a⁻¹ * x⁻¹ ∈ uHi T M H R₁ :=
      (Subgroup.mem_normalizer_iff.mp hxN a⁻¹).mp ((uHi T M H R₁).inv_mem ha)
    have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact (uHi T M H R₁).mul_mem ha h2
  have hu'K : g * (a * x * a⁻¹ * x⁻¹) * g⁻¹ ∈ uK T M H := by
    have ha' : g * a * g⁻¹ ∈ H := by
      have := mem_conjSub.mp (hUle (hKU (hHi ha)))
      simpa using this
    have hx' : g * x * g⁻¹ ∈ uK T M H := by
      have := mem_conjSub.mp hx
      simpa using this
    have e : g * (a * x * a⁻¹ * x⁻¹) * g⁻¹ =
        ((g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹) * (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact (uK T M H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHK ha') _).mp hx')
      ((uK T M H).inv_mem hx')
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁, hR₂⟩ := hdat.setup h35 S hred hshape
  subst hR₁ hR₂
  obtain ⟨c, hcH, hc⟩ := e9_exists_conj_of_mem_uHi S hH h98.toHypF91 hsplit hstr hpp
    (Or.inl hu'₁) hax hu huZ
  have hζ : (c * (a * x * a⁻¹ * x⁻¹) * c⁻¹ * u⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T :=
    (quasithinOmegaOneCenter T).inv_mem hc
  obtain ⟨t₀, ht₀T, ht₀⟩ := S.exists_conj_eq_mul_Z huG h1 hζ
  have hhu : (t₀ * c) * (a * x * a⁻¹ * x⁻¹) * (t₀ * c)⁻¹ = u := by
    have e1 : (t₀ * c) * (a * x * a⁻¹ * x⁻¹) * (t₀ * c)⁻¹ =
        t₀ * (c * (a * x * a⁻¹ * x⁻¹) * c⁻¹ * u⁻¹) * t₀⁻¹ * (t₀ * u * t₀⁻¹) := by group
    rw [e1, S146T.conj_Z (hHG (hTH ht₀T)) hc, ht₀]
    group
  have hhH : t₀ * c ∈ H := H.mul_mem (hTH ht₀T) hcH
  refine ⟨g * (t₀ * c)⁻¹, ?_, ?_⟩
  · rw [mem_conjSubgroup_iff]
    have e : g * (t₀ * c)⁻¹ * u * (g * (t₀ * c)⁻¹)⁻¹ = g * (a * x * a⁻¹ * x⁻¹) * g⁻¹ := by
      rw [← hhu]
      group
    rw [e]
    exact hu'K
  · intro hbot
    have hmem : ((t₀ * c) * a * (t₀ * c)⁻¹) * ((t₀ * c) * x * (t₀ * c)⁻¹) *
        ((t₀ * c) * a * (t₀ * c)⁻¹)⁻¹ * ((t₀ * c) * x * (t₀ * c)⁻¹)⁻¹ ∈
        ⁅uK T M H, conjSubgroup (uK T M H) (g * (t₀ * c)⁻¹)⁆ := by
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact (Subgroup.mem_normalizer_iff.mp (hHK hhH) a).mp (hHi ha)
      · rw [mem_conjSubgroup_iff]
        have e : g * (t₀ * c)⁻¹ * ((t₀ * c) * x * (t₀ * c)⁻¹) * (g * (t₀ * c)⁻¹)⁻¹ =
            g * x * g⁻¹ := by group
        rw [e]
        have := mem_conjSub.mp hx
        simpa using this
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hax
    have e : a * x * a⁻¹ * x⁻¹ = (t₀ * c)⁻¹ * (((t₀ * c) * a * (t₀ * c)⁻¹) *
        ((t₀ * c) * x * (t₀ * c)⁻¹) * ((t₀ * c) * a * (t₀ * c)⁻¹)⁻¹ *
          ((t₀ * c) * x * (t₀ * c)⁻¹)⁻¹) * (t₀ * c) := by group
    rw [e, hmem]
    simp

end UK

end CFSG.Quasithin
