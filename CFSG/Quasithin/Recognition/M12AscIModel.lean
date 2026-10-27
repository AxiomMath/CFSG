module

public import CFSG.Quasithin.Recognition.M12AscModel

public section

namespace CFSG.Quasithin

@[expose] def centTabs (tt : List (Fin 12)) : List (List (Fin 12)) :=
  ascHTabs.filter fun h => tmul h tt = tmul tt h

theorem mem_centTabs_iff {tt h : List (Fin 12)} :
    h ∈ centTabs tt ↔ h ∈ ascHTabs ∧ tmul h tt = tmul tt h := by
  simp [centTabs]

theorem centTabs_sub (tt : List (Fin 12)) : ∀ s ∈ centTabs tt, s ∈ ascHTabs := fun _ hs =>
  (mem_centTabs_iff.1 hs).1

theorem centTabs_one : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid → tid ∈ centTabs t := by
  decide +kernel

theorem centTabs_mul : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid →
    ∀ s ∈ centTabs t, ∀ s' ∈ centTabs t, tmul s s' ∈ centTabs t := by decide +kernel

theorem centTabs_inv : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid →
    ∀ s ∈ centTabs t, ∃ s' ∈ centTabs t, tmul s s' = tid := by decide +kernel

theorem centTabs_length : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid → (centTabs t).length = 16 := by
  decide +kernel

theorem centTabs_nodup : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid → (centTabs t).Nodup := by
  decide +kernel

theorem centTabs_le_q : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid → ∀ s ∈ centTabs t, s ∈ qTabs := by
  decide +kernel

theorem centTabs_center : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid →
    ∀ c ∈ centTabs t, (∀ s ∈ centTabs t, tmul c s = tmul s c) →
      c = tid ∨ c = zTab ∨ c = t ∨ c = tmul zTab t := by decide +kernel

theorem centTabs_exists_r : ∀ t ∈ qTabs, t ∉ FTabs → tmul t t = tid →
    ∃ r ∈ centTabs t, tmul r r = tid ∧ r ∉ FTabs ∧ tmul r t ∉ FTabs := by decide +kernel

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

namespace AscModel

variable (m : AscModel z)

include m

theorem tb_facts [Finite G] (hyp : Asc03Hyp G z) {t : G} (htQ : t ∈ ascQ z) (htF : t ∉ m.fSub)
    (ht2 : t * t = 1) :
    m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid := by
  have h1 := (m.mem_ascQ_iff_tb hyp).1 htQ
  refine ⟨h1.2, fun h => htF (m.mem_fSub_iff.2 ⟨h1.1, h⟩), (m.mul_self_eq_one_iff h1.1).1 ht2⟩

@[expose] noncomputable def cSub {t : G} (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧
    tmul (m.tb t) (m.tb t) = tid) : Subgroup G :=
  m.subOf (centTabs (m.tb t)) (centTabs_sub _) (centTabs_one _ hf.1 hf.2.1 hf.2.2)
    (centTabs_mul _ hf.1 hf.2.1 hf.2.2) (centTabs_inv _ hf.1 hf.2.1 hf.2.2)

theorem mem_cSub_iff {t : G} (htQ : t ∈ ascQ z)
    (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid) {x : G} :
    x ∈ m.cSub hf ↔ x ∈ ascH z ∧ x * t = t * x := by
  have htH : t ∈ ascH z := ascQ_le_ascH z htQ
  rw [cSub, m.mem_subOf_iff, mem_centTabs_iff]
  constructor
  · rintro ⟨hx, -, hc⟩
    exact ⟨hx, (m.comm_iff hx htH).2 hc⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, m.tb_mem hx, (m.comm_iff hx htH).1 hc⟩

theorem card_cSub [Finite G] {t : G} (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧
    tmul (m.tb t) (m.tb t) = tid) : Nat.card (m.cSub hf) = 16 := by
  rw [cSub, m.card_subOf (centTabs_nodup _ hf.1 hf.2.1 hf.2.2), centTabs_length _ hf.1 hf.2.1 hf.2.2]

theorem cSub_le_ascQ [Finite G] (hyp : Asc03Hyp G z) {t : G}
    (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid) {x : G}
    (hx : x ∈ m.cSub hf) : x ∈ ascQ z := by
  have hx' : x ∈ ascH z ∧ m.tb x ∈ centTabs (m.tb t) := m.mem_subOf_iff.1 hx
  exact (m.mem_ascQ_iff_tb hyp).2 ⟨hx'.1, centTabs_le_q _ hf.1 hf.2.1 hf.2.2 _ hx'.2⟩

theorem center_cSub [Finite G] {t : G} (htQ : t ∈ ascQ z)
    (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid) {c : G}
    (hc : c ∈ m.cSub hf) (hcen : ∀ s ∈ m.cSub hf, c * s = s * c) :
    c = 1 ∨ c = z ∨ c = t ∨ c = z * t := by
  have htH : t ∈ ascH z := ascQ_le_ascH z htQ
  have hc' : c ∈ ascH z ∧ m.tb c ∈ centTabs (m.tb t) := m.mem_subOf_iff.1 hc
  have key := centTabs_center _ hf.1 hf.2.1 hf.2.2 _ hc'.2 (fun s' hs' => by
    obtain ⟨g, hg, hgs⟩ := m.exists_tb (centTabs_sub _ s' hs')
    have hgS : g ∈ m.cSub hf := m.mem_subOf_iff.2 ⟨hg, by rw [hgs]; exact hs'⟩
    have := (m.comm_iff hc'.1 hg).1 (hcen g hgS)
    rwa [hgs] at this)
  rcases key with h | h | h | h
  · left; exact (m.eq_one_iff hc'.1).2 h
  · right; left; exact (m.eq_z_iff hc'.1).2 h
  · right; right; left; exact m.tb_inj hc'.1 htH h
  · right; right; right
    exact m.tb_inj hc'.1 (mul_mem (z_mem_ascH z) htH)
      (by rw [m.tb_mul (z_mem_ascH z) htH, m.tb_z]; exact h)

theorem exists_r_cSub [Finite G] {t : G} (htQ : t ∈ ascQ z)
    (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid) :
    ∃ r ∈ m.cSub hf, r * r = 1 ∧ r ∉ m.fSub ∧ r * t ∉ m.fSub := by
  have htH : t ∈ ascH z := ascQ_le_ascH z htQ
  obtain ⟨rt, hrt, hr2, hrF, hrtF⟩ := centTabs_exists_r _ hf.1 hf.2.1 hf.2.2
  obtain ⟨r, hrH, hrr⟩ := m.exists_tb (centTabs_sub _ rt hrt)
  refine ⟨r, m.mem_subOf_iff.2 ⟨hrH, by rw [hrr]; exact hrt⟩,
    (m.mul_self_eq_one_iff hrH).2 (by rw [hrr]; exact hr2), fun h => hrF ?_, fun h => hrtF ?_⟩
  · rw [← hrr]; exact (m.mem_fSub_iff.1 h).2
  · have := (m.mem_fSub_iff.1 h).2
    rw [m.tb_mul hrH htH, hrr] at this
    exact this

end AscModel

end CFSG.Quasithin
