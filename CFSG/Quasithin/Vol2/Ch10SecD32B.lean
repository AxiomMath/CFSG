module

public import CFSG.Quasithin.Vol2.Ch10SecD32A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem V2_eq_conjugate {t : G} (ht : t ∈ T) :
    ⁅fsuVM T L I, CFSG.conjugate L t⁆ = CFSG.conjugate (fsuUL T L I) t :=
  (SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)).symm

theorem conjugate_V1_eq_or (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {m : G}
    (hm : m ∈ fsuM T L) :
    CFSG.conjugate (fsuUL T L I) m = fsuUL T L I ∨
      CFSG.conjugate (fsuUL T L I) m = ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  rw [SecA.conjugate_commutator_fsuVM hm]
  rcases SecA.conjugate_eq_or h37 h38 h ht htn hm with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])

theorem conjugate_V2_eq_or (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {m : G}
    (hm : m ∈ fsuM T L) :
    CFSG.conjugate ⁅fsuVM T L I, CFSG.conjugate L t⁆ m = fsuUL T L I ∨
      CFSG.conjugate ⁅fsuVM T L I, CFSG.conjugate L t⁆ m = ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  rw [V2_eq_conjugate ht, SecA.conjugate_conjugate, ← V2_eq_conjugate ht]
  exact conjugate_V1_eq_or h37 h38 h ht htn ((fsuM T L).mul_mem (SecA.le_fsuM T L ht) hm)

theorem conj_mem_V12 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {m : G}
    (hm : m ∈ fsuM T L) {w : G} (hw : w ∈ fsuUL T L I ∨ w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) :
    m⁻¹ * w * m ∈ fsuUL T L I ∨ m⁻¹ * w * m ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  have key : ∀ X : Subgroup G, w ∈ X → m⁻¹ * w * m ∈ CFSG.conjugate X m := fun X hX => by
    rw [SecA.mem_conjugate_iff]
    have e : m * (m⁻¹ * w * m) * m⁻¹ = w := by group
    rw [e]
    exact hX
  rcases hw with hw | hw
  · rcases conjugate_V1_eq_or h37 h38 h ht htn hm with h1 | h1
    · exact Or.inl (h1 ▸ key _ hw)
    · exact Or.inr (h1 ▸ key _ hw)
  · rcases conjugate_V2_eq_or h37 h38 h ht htn hm with h1 | h1
    · exact Or.inl (h1 ▸ key _ hw)
    · exact Or.inr (h1 ▸ key _ hw)

theorem eq_one_of_commute_t (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : G}
    (hw : w ∈ fsuUL T L I ∨ w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hwt : t * w = w * t) :
    w = 1 := by
  have hconj : t * w * t⁻¹ = w := by rw [hwt]; group
  have hmem : w ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rcases hw with hw | hw
    · refine Subgroup.mem_inf.mpr ⟨hw, ?_⟩
      rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff, hconj]
      exact hw
    · refine Subgroup.mem_inf.mpr ⟨?_, hw⟩
      have h1 := hw
      rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff, hconj] at h1
      exact h1
  rw [V1_inf_V2 h37 h38 h hc ht htn] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem exists_diag (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {z : G} (hzV : z ∈ fsuVM T L I) (hz1 : z ≠ 1)
    (hzt : t * z = z * t) :
    ∃ a ∈ fsuUL T L I, ∃ b ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, a ≠ 1 ∧ b ≠ 1 ∧ z = a * b := by
  have hzV' : z ∈ fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rw [← SecA.fsuVM_eq_sup h37 h38 h ht htn]
    exact hzV
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm (commute_V1_V2 h ht) hzV'
  refine ⟨a, ha, b, hb, ?_, ?_, rfl⟩
  · rintro rfl
    rw [one_mul] at hz1 hzt
    exact hz1 (eq_one_of_commute_t h37 h38 h hc ht htn (Or.inr hb) hzt)
  · rintro rfl
    rw [mul_one] at hz1 hzt
    exact hz1 (eq_one_of_commute_t h37 h38 h hc ht htn (Or.inl ha) hzt)

theorem exists_conj_diag (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {a b a' b' : G}
    (ha : a ∈ fsuUL T L I) (hb : b ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (ha' : a' ∈ fsuUL T L I)
    (hb' : b' ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha1' : a' ≠ 1)
    (hb1' : b' ≠ 1) : ∃ x ∈ fsuL0 T L, x * (a * b) * x⁻¹ = a' * b' := by
  obtain ⟨l, hl, hla⟩ := exists_conj_eq_of_mem_V1 h3 hc ha ha' ha1 ha1'
  obtain ⟨l', hl', hlb⟩ := exists_conj_eq_of_mem_V2 h3 hc ht hb hb' hb1 hb1'
  have hl'a : l' * a = a * l' :=
    ((Subgroup.mem_centralizer_iff.mp (conjugate_le_centralizer_V1 h ht htn hl')) a ha).symm
  have hlb' : l * b' = b' * l :=
    (Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hb')) l hl
  refine ⟨l * l', (fsuL0 T L).mul_mem (SecA.le_fsuL0 T L hl) (SecA.conjugate_le_fsuL0 ht hl'), ?_⟩
  calc l * l' * (a * b) * (l * l')⁻¹ = l * (l' * a) * (b * l'⁻¹) * l⁻¹ := by group
    _ = l * (a * l') * (b * l'⁻¹) * l⁻¹ := by rw [hl'a]
    _ = l * a * l⁻¹ * (l * (l' * b * l'⁻¹) * l⁻¹) := by group
    _ = a' * (l * b' * l⁻¹) := by rw [hla, hlb]
    _ = a' * (b' * l * l⁻¹) := by rw [hlb']
    _ = a' * b' := by group

theorem conj_z_or_mem (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {z : G} (hzV : z ∈ fsuVM T L I)
    (hz1 : z ≠ 1) (hzt : t * z = z * t) {u : G} (hu : u ∈ fsuVM T L I) :
    (∃ x ∈ fsuL0 T L, x * z * x⁻¹ = u) ∨
      u ∈ fsuUL T L I ∨ u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  obtain ⟨a₀, ha₀, b₀, hb₀, ha₀1, hb₀1, rfl⟩ := exists_diag h37 h38 h hc ht htn hzV hz1 hzt
  have hu' : u ∈ fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rw [← SecA.fsuVM_eq_sup h37 h38 h ht htn]
    exact hu
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm (commute_V1_V2 h ht) hu'
  by_cases ha1 : a = 1
  · subst ha1
    rw [one_mul]
    exact Or.inr (Or.inr hb)
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one]
    exact Or.inr (Or.inl ha)
  exact Or.inl (exists_conj_diag h37 h38 h h3 hc ht htn ha₀ hb₀ ha hb ha₀1 hb₀1 ha1 hb1)

theorem not_conj_z_mem (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {z : G}
    (hzT : T ≤ Subgroup.centralizer ({z} : Set G)) {w y : G}
    (hw : w ∈ fsuUL T L I ∨ w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hw1 : w ≠ 1)
    (hyw : y * z * y⁻¹ = w) : False := by
  have hwM : Subgroup.centralizer ({w} : Set G) ≤ fsuM T L := by
    rcases hw with hw | hw
    · exact (h1029 G T L I h L (Or.inl rfl)).1 w hw hw1
    · exact (h1029 G T L I h _ (Or.inr ⟨t, ht, htn, rfl⟩)).1 w hw hw1
  have hT'C : T.map (MulAut.conj y).toMonoidHom ≤ Subgroup.centralizer ({w} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hzT hs)
    change y * s * y⁻¹ * w = w * (y * s * y⁻¹)
    rw [← hyw]
    calc y * s * y⁻¹ * (y * z * y⁻¹) = y * (s * z) * y⁻¹ := by group
      _ = y * (z * s) * y⁻¹ := by rw [hsz]
      _ = y * z * y⁻¹ * (y * s * y⁻¹) := by group
  have hTs : quasithinIsSylowTwo T := h.fsu.sylow
  have hT's : quasithinIsSylowTwo (T.map (MulAut.conj y).toMonoidHom) := by
    refine ⟨hTs.1.map _, ?_⟩
    rw [Subgroup.index_map_eq _ (MulAut.conj y).surjective (by
      rw [MonoidHom.ker_eq_bot_iff _ |>.mpr (MulAut.conj y).injective]
      exact bot_le)]
    exact hTs.2
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo hTs (SecA.le_fsuM T L)
  have hS' := isSylowTwoOf_of_quasithinIsSylowTwo hT's (hT'C.trans hwM)
  obtain ⟨m, hm, hmT⟩ := A4.exists_conj_of_isSylowTwoOf hS hS'
  have hTw : t * (m⁻¹ * w * m) = m⁻¹ * w * m * t := by
    have h1 : m * t * m⁻¹ ∈ T.map (MulAut.conj y).toMonoidHom := by
      rw [hmT]
      have e : m⁻¹ * (m * t * m⁻¹) * m = t := by group
      rw [e]
      exact ht
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hT'C h1)
    calc t * (m⁻¹ * w * m) = m⁻¹ * ((m * t * m⁻¹) * w) * m := by group
      _ = m⁻¹ * (w * (m * t * m⁻¹)) * m := by rw [h2]
      _ = m⁻¹ * w * m * t := by group
  have hw1' : m⁻¹ * w * m ≠ 1 := fun h' => hw1 (by
    calc w = m * (m⁻¹ * w * m) * m⁻¹ := by group
      _ = 1 := by rw [h']; group)
  exact hw1' (eq_one_of_commute_t h37 h38 h hc ht htn (conj_mem_V12 h37 h38 h ht htn hm hw) hTw)

theorem centralizer_le_fsuM (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {z : G} (hzV : z ∈ fsuVM T L I) (hz1 : z ≠ 1) (hzt : t * z = z * t)
    (hzM : Subgroup.centralizer ({z} : Set G) ≤ fsuM T L) {u : G} (hu : u ∈ fsuVM T L I)
    (hu1 : u ≠ 1) : Subgroup.centralizer ({u} : Set G) ≤ fsuM T L := by
  rcases conj_z_or_mem h37 h38 h h3 hc ht htn hzV hz1 hzt hu with ⟨x, hx, rfl⟩ | hu' | hu'
  · intro y hy
    have hxM : x ∈ fsuM T L := SecA.fsuL0_le_fsuM T L hx
    have hyu := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hyz : x⁻¹ * y * x ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * y * x * z = x⁻¹ * (y * (x * z * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * z * x⁻¹) * y) * x := by rw [hyu]
        _ = z * (x⁻¹ * y * x) := by group
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact (fsuM T L).mul_mem ((fsuM T L).mul_mem hxM (hzM hyz)) ((fsuM T L).inv_mem hxM)
  · exact (h1029 G T L I h L (Or.inl rfl)).1 u hu' hu1
  · exact (h1029 G T L I h _ (Or.inr ⟨t, ht, htn, rfl⟩)).1 u hu' hu1

omit [Finite G] in
theorem exists_conj_nondiag (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G}
    (ht : t ∈ T) {w w' : G}
    (hw : w ∈ fsuUL T L I ∨ w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hw' : w' ∈ fsuUL T L I ∨ w' ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hw1 : w ≠ 1)
    (hw1' : w' ≠ 1) : ∃ m ∈ fsuM T L, w' = m⁻¹ * w * m := by
  have key : ∀ v : G, (v ∈ fsuUL T L I ∨ v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) → v ≠ 1 →
      ∃ s ∈ fsuM T L, s * v * s⁻¹ ∈ fsuUL T L I ∧ s * v * s⁻¹ ≠ 1 := by
    intro v hv hv1
    have hne : ∀ s : G, s * v * s⁻¹ ≠ 1 := fun s h' => hv1 (by
      calc v = s⁻¹ * (s * v * s⁻¹) * s := by group
        _ = 1 := by rw [h']; group)
    rcases hv with hv | hv
    · exact ⟨1, (fsuM T L).one_mem, by rw [one_mul, inv_one, mul_one]; exact hv, hne 1⟩
    · refine ⟨t, SecA.le_fsuM T L ht, ?_, hne t⟩
      rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff] at hv
      exact hv
  obtain ⟨s, hs, hsw, hsw1⟩ := key w hw hw1
  obtain ⟨s', hs', hsw', hsw1'⟩ := key w' hw' hw1'
  obtain ⟨l, hl, hlw⟩ := exists_conj_eq_of_mem_V1 h3 hc hsw hsw' hsw1 hsw1'
  have hlM : l ∈ fsuM T L := SecA.fsuL0_le_fsuM T L (SecA.le_fsuL0 T L hl)
  refine ⟨s⁻¹ * l⁻¹ * s', (fsuM T L).mul_mem ((fsuM T L).mul_mem ((fsuM T L).inv_mem hs)
    ((fsuM T L).inv_mem hlM)) hs', ?_⟩
  calc w' = s'⁻¹ * (s' * w' * s'⁻¹) * s' := by group
    _ = s'⁻¹ * (l * (s * w * s⁻¹) * l⁻¹) * s' := by rw [hlw]
    _ = (s⁻¹ * l⁻¹ * s')⁻¹ * w * (s⁻¹ * l⁻¹ * s') := by group

end CFSG.Quasithin.Vol2.Ch10.SecD
