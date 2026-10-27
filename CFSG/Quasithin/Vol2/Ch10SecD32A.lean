module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Vol2.Ch10SecD211D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem autOn_L_V1_eq_top (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) :
    autOn L (fsuUL T L I) = ⊤ := by
  obtain ⟨-, hcomm, hnat⟩ := h3
  rw [cV1_eq_bot hc] at hnat
  exact G64.BinaryNaturalSL.eq_top hnat

theorem card_le_four_of_isElemAbelian2 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥)
    [IsMulCommutative ↥(fsuUL T L I)] {E : Subgroup (MulAut ↥(fsuUL T L I))}
    (hE : IsElemAbelian2 E) : Nat.card E ≤ 4 := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  exact D.elemAbelian_card_le_four (by rw [autOn_L_V1_eq_top h3 hc]; exact le_top) hE

omit [Finite G] in
theorem exists_conj_eq_of_mem_V1 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {a b : G}
    (ha : a ∈ fsuUL T L I) (hb : b ∈ fsuUL T L I) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ l ∈ L, l * a * l⁻¹ = b := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  set ua : ↥(⊤ : Subgroup ↥(fsuUL T L I)) := ⟨⟨a, ha⟩, trivial⟩
  set ub : ↥(⊤ : Subgroup ↥(fsuUL T L I)) := ⟨⟨b, hb⟩, trivial⟩
  have hne : ∀ (u : ↥(⊤ : Subgroup ↥(fsuUL T L I))), ((u : ↥(fsuUL T L I)) : G) ≠ 1 →
      Multiplicative.toAdd (D.β u) ≠ 0 := by
    intro u hu h0
    apply hu
    have h1 : D.β u = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 := hβinj (h1.trans (map_one D.β).symm)
    rw [h2]
    rfl
  obtain ⟨γ, hγ⟩ := L3.act_trans _ _ (hne ua ha1) (hne ub hb1)
  obtain ⟨⟨l, hlN⟩, hlL, hlσ⟩ := D.rho_mem γ
  refine ⟨l, Subgroup.mem_subgroupOf.mp hlL, ?_⟩
  have h2 := D.β_rho γ (⟨a, ha⟩ : ↥(fsuUL T L I)) trivial trivial
  rw [show (⟨(⟨a, ha⟩ : ↥(fsuUL T L I)), trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = ua from rfl,
    hγ] at h2
  have h3' : (⟨D.rho γ ⟨a, ha⟩, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = ub :=
    hβinj (by rw [h2]; simp)
  have h4 := congrArg (fun u : ↥(⊤ : Subgroup ↥(fsuUL T L I)) => ((u : ↥(fsuUL T L I)) : G)) h3'
  simp only at h4
  rw [← hlσ] at h4
  exact h4

omit [Finite G] in
theorem exists_conj_eq_of_mem_V2 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G}
    (ht : t ∈ T) {a b : G} (ha : a ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hb : b ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ l ∈ CFSG.conjugate L t, l * a * l⁻¹ = b := by
  rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.mem_conjugate_iff] at ha hb
  have hne : ∀ x : G, x ≠ 1 → t * x * t⁻¹ ≠ 1 := fun x hx h' => hx (by
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h']; group)
  obtain ⟨l, hl, hlab⟩ := exists_conj_eq_of_mem_V1 h3 hc ha hb (hne a ha1) (hne b hb1)
  refine ⟨t⁻¹ * l * t, ?_, ?_⟩
  · rw [SecA.mem_conjugate_iff]
    have e : t * (t⁻¹ * l * t) * t⁻¹ = l := by group
    rw [e]
    exact hl
  · calc t⁻¹ * l * t * a * (t⁻¹ * l * t)⁻¹ = t⁻¹ * (l * (t * a * t⁻¹) * l⁻¹) * t := by group
      _ = t⁻¹ * (t * b * t⁻¹) * t := by rw [hlab]
      _ = b := by group

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_comm {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

omit [Finite G] in
theorem eq_of_mul_eq_mul_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a a' b b' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have hb1 : b' * b⁻¹ = 1 := h1 ▸ hmem
  exact ⟨(inv_mul_eq_one.mp hmem).symm, (mul_inv_eq_one.mp hb1).symm⟩

theorem commute_V1_V2 (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    ∀ a ∈ fsuUL T L I, ∀ b ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, a * b = b * a := by
  obtain ⟨hcomm, -⟩ := h.three
  intro a ha b hb
  have hbV : b ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hb
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, V1_le_V ha⟩ ⟨b, hbV⟩)

theorem exists_isData10_2_11 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) : ∃ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have hS := SecA.isSylowTwoOf_inf h.fsu.maximal.1
  have h2 := card_inf_centralizer_of_isSylowTwoOf h3 hc hS
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (show
    fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ≠ ⊥ by
      intro h0; rw [h0, Subgroup.card_bot] at h2; norm_num at h2)
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  have hwT1 : w ∈ Subgroup.centralizer (T1 T L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsV1 : s ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
      SecA.le_normalizer_commutator (X := T1 T L) (inf_le_left.trans
        (SecA.le_normalizer_fsuVM T L I)) inf_le_right hs
    have hsTL : s ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_inf (Subgroup.le_normalizer hs.1) hs.2
    have hmem : s * w * s⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      ⟨(Subgroup.mem_normalizer_iff.mp hsV1 w).mp hw.1, conj_mem_centralizer hsTL hw.2⟩
    have hne : s * w * s⁻¹ ≠ 1 := fun h' => hw1' (by
      calc w = s⁻¹ * (s * w * s⁻¹) * s := by group
        _ = 1 := by rw [h']; group)
    have heq := eq_of_card_le_two h2.le hmem hw hne hw1'
    calc s * w = s * w * s⁻¹ * s := by group
      _ = w * s := by rw [heq]
  refine ⟨t, w, t⁻¹ * w * t, ht, htn, ⟨hw.1, hwT1⟩, hw1', ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.mem_conjugate_iff]
      simpa [mul_assoc] using hw.1
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hts : t * s * t⁻¹ ∈ T1 T L :=
        (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_T1 h37 h38 h ht) s).mp hs
      have := (Subgroup.mem_centralizer_iff.mp hwT1) _ hts
      calc s * (t⁻¹ * w * t) = t⁻¹ * ((t * s * t⁻¹) * w) * t := by group
        _ = t⁻¹ * (w * (t * s * t⁻¹)) * t := by rw [this]
        _ = t⁻¹ * w * t * s := by group
  · intro h'
    apply hw1'
    calc w = t * (t⁻¹ * w * t) * t⁻¹ := by group
      _ = 1 := by rw [h']; group

end CFSG.Quasithin.Vol2.Ch10.SecD
