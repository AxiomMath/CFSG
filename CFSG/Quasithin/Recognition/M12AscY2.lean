module

public import CFSG.Quasithin.Recognition.M12AscY1
public import Certificates.Certificate2950
public import CFSG.Quasithin.Recognition.M12AscS6

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

structure YRel {m : AscModel z} (c : AscCox m) (y : G) : Prop where
  y_sq : y * y = m.ψ mA
  y_z : y * z = (z * m.ψ mA) * y
  y_cp : y * c.ρ pcp = (m.ψ mA * (c.u' * z)) * y
  y_u : y * c.u' = (z * c.ρ pcp) * y

namespace YRel

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem y_a (h : YRel c y) : y * m.ψ mA = m.ψ mA * y := by
  rw [← h.y_sq]
  group

theorem conj_z (h : YRel c y) : y * z * y⁻¹ = z * m.ψ mA := by
  rw [h.y_z]
  group

theorem conj_a (h : YRel c y) : y * m.ψ mA * y⁻¹ = m.ψ mA := by
  rw [h.y_a]
  group

theorem conj_cp (h : YRel c y) : y * c.ρ pcp * y⁻¹ = m.ψ mA * (c.u' * z) := by
  rw [h.y_cp]
  group

theorem conj_u (h : YRel c y) : y * c.u' * y⁻¹ = z * c.ρ pcp := by
  rw [h.y_u]
  group

end YRel

namespace AscModel

variable {m : AscModel z}

theorem ncard_tb_mem [Finite G] (L : List (List (Fin 12))) (hL : ∀ t ∈ L, t ∈ ascHTabs)
    (hnd : L.Nodup) : {g : G | g ∈ ascH z ∧ m.tb g ∈ L}.ncard = L.length := by
  have h : Nat.card {g : G // g ∈ ascH z ∧ m.tb g ∈ L} = Nat.card {t // t ∈ L} := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨m.tb g.1, g.2.2⟩) ⟨?_, ?_⟩)
    · intro g g' e
      exact Subtype.ext (m.tb_inj g.2.1 g'.2.1 (congrArg Subtype.val e))
    · rintro ⟨t, ht⟩
      obtain ⟨g, hg, hgt⟩ := m.exists_tb (hL t ht)
      exact ⟨⟨g, hg, by rw [hgt]; exact ht⟩, Subtype.ext hgt⟩
  have h2 : Nat.card {t // t ∈ L} = Nat.card ↥L.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight (by simp))
  rw [← Nat.card_coe_set_eq]
  have h3 : Nat.card ↥{g : G | g ∈ ascH z ∧ m.tb g ∈ L} =
      Nat.card {g : G // g ∈ ascH z ∧ m.tb g ∈ L} := rfl
  rw [h3, h, h2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem norm_list_iff {W : List G} (hW : ∀ w ∈ W, w ∈ ascH z) {h : G} (hh : h ∈ ascH z) :
    (∀ w ∈ W, ∃ w' ∈ W, h * w = w' * h) ↔
      ∀ t ∈ W.map m.tb, ∃ t' ∈ W.map m.tb, tmul (m.tb h) t = tmul t' (m.tb h) := by
  constructor
  · intro H t ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    obtain ⟨w', hw', e⟩ := H w hw
    refine ⟨m.tb w', List.mem_map_of_mem hw', ?_⟩
    rw [← m.tb_mul hh (hW w hw), ← m.tb_mul (hW w' hw') hh, e]
  · intro H w hw
    obtain ⟨t', ht', e⟩ := H (m.tb w) (List.mem_map_of_mem hw)
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 ht'
    exact ⟨w', hw', (m.tmul_eq_iff hh (hW w hw) (hW w' hw') hh).2 e⟩

end AscModel

theorem normAbar_iff (uT t : List (Fin 12)) : normAbar uT t = true ↔
    ∀ w ∈ AbarTabs uT, ∃ w' ∈ AbarTabs uT, tmul t w = tmul w' t := by
  unfold normAbar
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq]

namespace AscModel

variable {m : AscModel z}

theorem tb_a : m.tb (m.ψ mA) = aFTab := by
  rw [m.tb_ψ mA]
  exact tabOf_aFPerm

theorem tb_u'_cases (c : AscCox m) : m.tb c.u' = uTab ∨ m.tb c.u' = uzTab := by
  rcases c.hu' with e | e
  · left; rw [e, m.tb_ψ_mU]
  · right
    rw [e, map_mul, m.ψ_hz, m.tb_mul (m.ψ_mem mU) (z_mem_ascH z), m.tb_ψ_mU, m.tb_z]
    rfl

theorem tb_cp (c : AscCox m) : m.tb (c.ρ pcp) = cpTab (m.tb c.u') := by
  have hu := c.mem_H
  have hx := m.ψ_mem mX
  have ha := m.ψ_mem mA
  rw [c.ρ_pcp, m.tb_mul (mul_mem (mul_mem hu hx) ha) (mul_mem hu hx),
    m.tb_mul (mul_mem hu hx) ha, m.tb_mul hu hx, tb_a, m.tb_ψ_mX]
  rfl

theorem cp_mem_H (c : AscCox m) : c.ρ pcp ∈ ascH z := by
  rw [c.ρ_pcp]
  exact mul_mem (mul_mem (mul_mem c.mem_H (m.ψ_mem mX)) (m.ψ_mem mA))
    (mul_mem c.mem_H (m.ψ_mem mX))

theorem X_ncard [Finite G] (c : AscCox m) :
    {h : G | h ∈ ascH z ∧ ∀ w ∈ [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp],
      ∃ w' ∈ [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp], h * w = w' * h}.ncard = 48 := by
  have hW : ∀ w ∈ [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp], w ∈ ascH z := by
    intro w hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact m.ψ_mem mA
    · exact cp_mem_H c
    · exact mul_mem (m.ψ_mem mA) (cp_mem_H c)
  have hmap : [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp].map m.tb = AbarTabs (m.tb c.u') := by
    have hcp := cp_mem_H c
    simp only [List.map, m.tb_one, tb_a, tb_cp c, m.tb_mul (m.ψ_mem mA) hcp, AbarTabs, tid]
  have hset : {h : G | h ∈ ascH z ∧ ∀ w ∈ [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp],
      ∃ w' ∈ [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp], h * w = w' * h} =
      {h : G | h ∈ ascH z ∧ m.tb h ∈ ascHTabs.filter (normAbar (m.tb c.u'))} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hh, H⟩
      refine ⟨hh, List.mem_filter.2 ⟨m.tb_mem hh, ?_⟩⟩
      exact (normAbar_iff _ _).2 (by rw [← hmap]; exact (norm_list_iff (m := m) hW hh).1 H)
    · rintro ⟨hh, hL⟩
      refine ⟨hh, (norm_list_iff (m := m) hW hh).2 ?_⟩
      rw [hmap]
      exact (normAbar_iff _ _).1 (List.mem_filter.1 hL).2
  rw [hset, ncard_tb_mem _ (fun t ht => (List.mem_filter.1 ht).1) (ascHTabs_nodup.filter _)]
  rcases tb_u'_cases c with e | e
  · rw [e]; exact normAbar_count_u
  · rw [e]; exact normAbar_count_uz

end AscModel

namespace AscCox

variable {m : AscModel z}

@[expose] def C1 (c : AscCox m) : Subgroup G :=
  (Subgroup.centralizer ({swap 0 1} : Set (Perm (Fin 6)))).map c.ρ

@[expose] def C2 (c : AscCox m) : Subgroup G :=
  (Subgroup.centralizer ({ps} : Set (Perm (Fin 6)))).map c.ρ

theorem mem_C1 {c : AscCox m} {g : G} :
    g ∈ c.C1 ↔ ∃ γ : Perm (Fin 6), γ * swap 0 1 = swap 0 1 * γ ∧ c.ρ γ = g := by
  unfold C1
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, Subgroup.mem_centralizer_singleton_iff.1 hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, Subgroup.mem_centralizer_singleton_iff.2 hγ, rfl⟩

theorem mem_C2 {c : AscCox m} {g : G} :
    g ∈ c.C2 ↔ ∃ γ : Perm (Fin 6), γ * ps = ps * γ ∧ c.ρ γ = g := by
  unfold C2
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, Subgroup.mem_centralizer_singleton_iff.1 hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, Subgroup.mem_centralizer_singleton_iff.2 hγ, rfl⟩

theorem card_C1 (c : AscCox m) : Nat.card c.C1 = 48 :=
  (Subgroup.card_map_of_injective c.ρ_inj).trans CFSG.Quasithin.card_C1

theorem card_C2 (c : AscCox m) : Nat.card c.C2 = 48 :=
  (Subgroup.card_map_of_injective c.ρ_inj).trans CFSG.Quasithin.card_C2

@[expose] noncomputable def Wab (c : AscCox m) : List G := [1, m.ψ mA, c.ρ pcp, m.ψ mA * c.ρ pcp]

@[expose] noncomputable def W2 (c : AscCox m) : List G :=
  [1, m.ψ mA, m.ψ mA * (c.u' * z), c.u' * z]

@[expose] noncomputable def Xset (c : AscCox m) : Set G :=
  {h | h ∈ ascH z ∧ ∀ w ∈ Wab c, ∃ w' ∈ Wab c, h * w = w' * h}

theorem Wab_lift (c : AscCox m) : ∀ w ∈ Wab c, ∃ wp ∈ [1, pa, pcp, pa * pcp], c.ρ wp = w := by
  intro w hw
  simp only [Wab, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp, map_one _⟩
  · exact ⟨pa, by simp, c.ρ_pa⟩
  · exact ⟨pcp, by simp, rfl⟩
  · exact ⟨pa * pcp, by simp, by rw [map_mul, c.ρ_pa]⟩

theorem Wab_lower (c : AscCox m) : ∀ wp ∈ [1, pa, pcp, pa * pcp], c.ρ wp ∈ Wab c := by
  intro w hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  simp only [Wab, List.mem_cons, List.mem_nil_iff, or_false]
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact map_one _
  · right; left; exact c.ρ_pa
  · right; right; left; rfl
  · right; right; right; rw [map_mul, c.ρ_pa]

theorem W2_lift (c : AscCox m) : ∀ w ∈ W2 c, ∃ wp ∈ [1, pa, pa * pb, pb], c.ρ wp = w := by
  intro w hw
  simp only [W2, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp, map_one _⟩
  · exact ⟨pa, by simp, c.ρ_pa⟩
  · exact ⟨pa * pb, by simp, by rw [map_mul, c.ρ_pa, c.ρ_pb]⟩
  · exact ⟨pb, by simp, c.ρ_pb⟩

theorem W2_lower (c : AscCox m) : ∀ wp ∈ [1, pa, pa * pb, pb], c.ρ wp ∈ W2 c := by
  intro w hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  simp only [W2, List.mem_cons, List.mem_nil_iff, or_false]
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact map_one _
  · right; left; exact c.ρ_pa
  · right; right; left; rw [map_mul, c.ρ_pa, c.ρ_pb]
  · right; right; right; exact c.ρ_pb

end AscCox

namespace AscModel

variable {m : AscModel z}

theorem Xset_ncard [Finite G] (c : AscCox m) : (AscCox.Xset c).ncard = 48 := X_ncard c

theorem C1_sub_X (c : AscCox m) : (c.C1 : Set G) ⊆ AscCox.Xset c := by
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := AscCox.mem_C1.1 hg
  refine ⟨?_, ?_⟩
  · apply Subgroup.mem_centralizer_singleton_iff.2
    have := congrArg c.ρ hγ
    rwa [map_mul, map_mul, c.ρ_z] at this
  · intro w hw
    obtain ⟨wp, hwp, rfl⟩ := AscCox.Wab_lift c w hw
    obtain ⟨wq, hwq, e⟩ := C1_norm γ hγ wp hwp
    refine ⟨c.ρ wq, AscCox.Wab_lower c wq hwq, ?_⟩
    rw [← map_mul, ← map_mul, e]

end AscModel

namespace YRel

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem conj_acp (h : YRel c y) : y * (m.ψ mA * c.ρ pcp) * y⁻¹ = c.u' * z := by
  calc y * (m.ψ mA * c.ρ pcp) * y⁻¹ = (y * m.ψ mA * y⁻¹) * (y * c.ρ pcp * y⁻¹) := by group
    _ = m.ψ mA * (m.ψ mA * (c.u' * z)) := by rw [h.conj_a, h.conj_cp]
    _ = c.u' * z := by rw [← mul_assoc, AscModel.a_sq, one_mul]

theorem conj_Wab (h : YRel c y) : ∀ w ∈ AscCox.Wab c, y * w * y⁻¹ ∈ AscCox.W2 c := by
  intro w hw
  simp only [AscCox.Wab, List.mem_cons, List.mem_nil_iff, or_false] at hw
  simp only [AscCox.W2, List.mem_cons, List.mem_nil_iff, or_false]
  rcases hw with rfl | rfl | rfl | rfl
  · left; group
  · right; left; exact h.conj_a
  · right; right; left; exact h.conj_cp
  · right; right; right; exact h.conj_acp

theorem conj_W2 (h : YRel c y) : ∀ w ∈ AscCox.W2 c, y⁻¹ * w * y ∈ AscCox.Wab c := by
  intro w hw
  simp only [AscCox.W2, List.mem_cons, List.mem_nil_iff, or_false] at hw
  simp only [AscCox.Wab, List.mem_cons, List.mem_nil_iff, or_false]
  rcases hw with rfl | rfl | rfl | rfl
  · left; group
  · right; left
    calc y⁻¹ * m.ψ mA * y = y⁻¹ * (m.ψ mA * y) := by rw [mul_assoc]
      _ = y⁻¹ * (y * m.ψ mA) := by rw [h.y_a]
      _ = m.ψ mA := by group
  · right; right; left
    rw [← h.conj_cp]
    group
  · right; right; right
    rw [← h.conj_acp]
    group

end YRel

namespace AscModel

variable {m : AscModel z}

theorem conj_C2_sub_X {y : G} {c : AscCox m} (hy : YRel c y) :
    ∀ g ∈ c.C2, y⁻¹ * g * y ∈ AscCox.Xset c := by
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := AscCox.mem_C2.1 hg
  have hs : c.ρ γ * (z * m.ψ mA) = (z * m.ψ mA) * c.ρ γ := by
    have := congrArg c.ρ hγ
    rwa [map_mul, map_mul, c.ρ_ps] at this
  have hyz : y * z = (z * m.ψ mA) * y := hy.y_z
  refine ⟨?_, ?_⟩
  · apply Subgroup.mem_centralizer_singleton_iff.2
    calc y⁻¹ * c.ρ γ * y * z = y⁻¹ * c.ρ γ * (y * z) := by rw [mul_assoc]
      _ = y⁻¹ * c.ρ γ * ((z * m.ψ mA) * y) := by rw [hyz]
      _ = y⁻¹ * (c.ρ γ * (z * m.ψ mA)) * y := by group
      _ = y⁻¹ * ((z * m.ψ mA) * c.ρ γ) * y := by rw [hs]
      _ = (y⁻¹ * (z * m.ψ mA) * y) * (y⁻¹ * c.ρ γ * y) := by group
      _ = z * (y⁻¹ * c.ρ γ * y) := by
        have e : y⁻¹ * (z * m.ψ mA) * y = z := by
          calc y⁻¹ * (z * m.ψ mA) * y = y⁻¹ * ((z * m.ψ mA) * y) := by rw [mul_assoc]
            _ = y⁻¹ * (y * z) := by rw [hyz]
            _ = z := by group
        rw [e]
  · intro w hw
    have hw2 : y * w * y⁻¹ ∈ AscCox.W2 c := hy.conj_Wab w hw
    obtain ⟨wp, hwp, hwpe⟩ := AscCox.W2_lift c _ hw2
    obtain ⟨wq, hwq, e⟩ := C2_norm γ hγ wp hwp
    have hg2 : c.ρ γ * (y * w * y⁻¹) = c.ρ wq * c.ρ γ := by
      rw [← hwpe, ← map_mul, ← map_mul, e]
    refine ⟨y⁻¹ * c.ρ wq * y, hy.conj_W2 _ (AscCox.W2_lower c wq hwq), ?_⟩
    calc y⁻¹ * c.ρ γ * y * w = y⁻¹ * (c.ρ γ * (y * w * y⁻¹)) * y := by group
      _ = y⁻¹ * (c.ρ wq * c.ρ γ) * y := by rw [hg2]
      _ = (y⁻¹ * c.ρ wq * y) * (y⁻¹ * c.ρ γ * y) := by group

end AscModel

namespace AscModel

variable {m : AscModel z}

theorem Xset_eq [Finite G] {y : G} {c : AscCox m} (hy : YRel c y) :
    (fun g => y⁻¹ * g * y) '' (c.C2 : Set G) = AscCox.Xset c := by
  have hinj : Function.Injective (fun g : G => y⁻¹ * g * y) := fun g g' e => by simpa using e
  have hC2 : (c.C2 : Set G).ncard = 48 := by
    rw [← Nat.card_coe_set_eq]
    exact AscCox.card_C2 c
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_C2_sub_X hy g hg
  · rw [Set.ncard_image_of_injective _ hinj, hC2, Xset_ncard c]

theorem conj_C1 [Finite G] {y : G} {c : AscCox m} (hy : YRel c y) :
    ∀ g ∈ c.C1, y * g * y⁻¹ ∈ c.C2 := by
  intro g hg
  have hX : g ∈ AscCox.Xset c := C1_sub_X c hg
  rw [← Xset_eq hy] at hX
  obtain ⟨g', hg', e⟩ := hX
  have : y * g * y⁻¹ = g' := by
    rw [← e]
    group
  rw [this]
  exact hg'

theorem a_mem_C1 (c : AscCox m) : m.ψ mA ∈ c.C1 :=
  AscCox.mem_C1.2 ⟨pa, pa_comm_pz, c.ρ_pa⟩

theorem conj_C2 [Finite G] {y : G} {c : AscCox m} (hy : YRel c y) :
    ∀ g ∈ c.C2, y * g * y⁻¹ ∈ c.C1 := by
  have hinj : Function.Injective (fun g : G => y * g * y⁻¹) := fun g g' e => by simpa using e
  have hC1 : (c.C1 : Set G).ncard = 48 := by
    rw [← Nat.card_coe_set_eq]
    exact AscCox.card_C1 c
  have hC2 : (c.C2 : Set G).ncard = 48 := by
    rw [← Nat.card_coe_set_eq]
    exact AscCox.card_C2 c
  have himg : (fun g => y * g * y⁻¹) '' (c.C1 : Set G) = (c.C2 : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨g, hg, rfl⟩
      exact conj_C1 hy g hg
    · rw [Set.ncard_image_of_injective _ hinj, hC1, hC2]
  intro g hg
  have hg' : g ∈ (fun g => y * g * y⁻¹) '' (c.C1 : Set G) := by
    rw [himg]
    exact hg
  obtain ⟨c1, hc1, e⟩ := hg'
  have ha := a_mem_C1 c
  have hyy : y * y = m.ψ mA := hy.y_sq
  have hai : (m.ψ mA)⁻¹ = m.ψ mA := inv_eq_of_mul_eq_one_right AscModel.a_sq
  have hcalc : y * g * y⁻¹ = m.ψ mA * c1 * (m.ψ mA)⁻¹ := by
    have e' : y * c1 * y⁻¹ = g := e
    rw [← e']
    calc y * (y * c1 * y⁻¹) * y⁻¹ = (y * y) * c1 * (y * y)⁻¹ := by group
      _ = m.ψ mA * c1 * (m.ψ mA)⁻¹ := by rw [hyy]
  rw [hcalc]
  exact c.C1.mul_mem (c.C1.mul_mem ha hc1) (c.C1.inv_mem ha)

end AscModel

namespace AscModel

variable {m : AscModel z}

theorem C1_le_range (c : AscCox m) : c.C1 ≤ c.ρ.range := Subgroup.map_le_range _ _

theorem C2_le_range (c : AscCox m) : c.C2 ≤ c.ρ.range := Subgroup.map_le_range _ _

theorem conj_gen_C1 [Finite G] {y : G} {c : AscCox m} (hy : YRel c y) {γ : Perm (Fin 6)}
    (hγ : γ * swap 0 1 = swap 0 1 * γ) : y * c.ρ γ * y⁻¹ ∈ c.ρ.range :=
  C2_le_range c (conj_C1 hy _ (AscCox.mem_C1.2 ⟨γ, hγ, rfl⟩))

theorem conj_gen1 [Finite G] {y : G} {c : AscCox m} (hy : YRel c y) :
    y * c.ρ (swap 1 2) * y⁻¹ ∈ c.ρ.range := by
  have h1 : c.ρ (pcp * (swap 0 2 * swap 1 3)) ∈ c.C2 :=
    AscCox.mem_C2.2 ⟨_, z2_conj_mem, rfl⟩
  have h4 : c.ρ (swap 3 4) ∈ c.C1 := AscCox.mem_C1.2 ⟨swap 3 4, Certificates.certificate2950.1, rfl⟩
  have e : y * c.ρ (swap 1 2) * y⁻¹ =
      (y * c.ρ (pcp * (swap 0 2 * swap 1 3)) * y⁻¹) * (y * c.ρ (swap 3 4) * y⁻¹) *
        (y * c.ρ (pcp * (swap 0 2 * swap 1 3)) * y⁻¹)⁻¹ := by
    conv_lhs => rw [z2_conj]
    rw [map_mul, map_mul, map_inv]
    group
  rw [e]
  have a1 := C1_le_range c (conj_C2 hy _ h1)
  have a2 := C2_le_range c (conj_C1 hy _ h4)
  exact mul_mem (mul_mem a1 a2) (inv_mem a1)

theorem y_normalizes [Finite G] {y : G} {c : AscCox m} (hy : YRel c y) :
    ∀ σ : Perm (Fin 6), y * c.ρ σ * y⁻¹ ∈ c.ρ.range := by
  let T : Subgroup (Perm (Fin 6)) :=
    c.ρ.range.comap ((MulAut.conj y).toMonoidHom.comp c.ρ)
  have hgen : ∀ i : Fin 5, swapGen i ∈ T := by
    intro i
    show y * c.ρ (swapGen i) * y⁻¹ ∈ c.ρ.range
    fin_cases i
    · exact conj_gen_C1 hy (γ := swap 0 1) rfl
    · exact conj_gen1 hy
    · exact conj_gen_C1 hy (γ := swap 2 3) Certificates.certificate2950.2.1
    · exact conj_gen_C1 hy (γ := swap 3 4) Certificates.certificate2950.2.2.1
    · exact conj_gen_C1 hy (γ := swap 4 5) Certificates.certificate2950.2.2.2
  have hT : T = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swapGen i) := by
      rw [show (fun i : Fin 5 => swapGen i) = fun i : Fin 5 => Equiv.swap i.castSucc i.succ from rfl,
        Equiv.Perm.mclosure_swap_castSucc_succ 5]
      trivial
    exact (Submonoid.closure_le.2 (by rintro _ ⟨i, rfl⟩; exact hgen i)) hσ
  intro σ
  have : σ ∈ T := by rw [hT]; trivial
  exact this

end AscModel

end CFSG.Quasithin
