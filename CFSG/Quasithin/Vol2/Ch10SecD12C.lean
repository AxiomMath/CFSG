module

public import CFSG.Quasithin.Vol2.Ch10SecD12B
public import CFSG.Quasithin.Vol2.Ch10SecD12A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem V1_inf_V2_le (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤
      Subgroup.centralizer (fsuL0 T L : Set G) := by
  intro x hx
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := V2_le_centralizer_L h37 h38 h ht htn hx.2
  have hxLt : x ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (conjugate_le_centralizer_V1 h ht htn hl) x hx.1).symm
  rw [SecA.fsuL0_eq_sup h37 h38 h ht htn]
  have hle : L ⊔ CFSG.conjugate L t ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun l hl => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxL l hl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxLt l hl)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem inf_centralizer_le_of_mem (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h : Hyp10 G T L I)
    (hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥) {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) {b : G}
    (hbW : b ∈ conjSubgroup X g) (hbM : b ∈ fsuM T L)
    (hbN : b ∈ Subgroup.normalizer (fsuUL T L I : Set G))
    (hbL : b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g) :
    fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer ((conjSubgroup X g ⊓ fsuM T L : Subgroup G) : Set G) := by
  obtain ⟨K, hK, rfl⟩ : ∃ K, IsLi T L K ∧ X = ⁅fsuVM T L I, K⁆ := by
    rcases hX with rfl | rfl
    · exact ⟨L, Or.inl rfl, rfl⟩
    · exact ⟨CFSG.conjugate L t, Or.inr ⟨t, ht, htn, rfl⟩, rfl⟩
  have hY : ⁅fsuVM T L I, K⁆ = fsuUL T L I ∨
      ⁅fsuVM T L I, K⁆ = ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rcases hK with rfl | ⟨s, hs, hsn, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (by rw [SecA.conjugate_eq_of_not_mem h37 h38 h ht htn hs hsn])
  have hVab : ∀ x ∈ fsuVM T L I, ∀ y ∈ fsuVM T L I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((SecA.isElemAbelian_fsuVM h).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I
  have hV1V : fsuUL T L I ≤ fsuVM T L I := V1_le_V
  have hXV : ⁅fsuVM T L I, K⁆ ≤ fsuVM T L I := by
    rcases hY with hY | hY <;> rw [hY]
    · exact hV1V
    · exact commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hWV : conjSubgroup ⁅fsuVM T L I, K⁆ g ≤ conjSubgroup (fsuVM T L I) g :=
    conjSubgroup_mono_left g hXV
  have hVgab : ∀ x ∈ conjSubgroup (fsuVM T L I) g, ∀ y ∈ conjSubgroup (fsuVM T L I) g,
      x * y = y * x := by
    intro x hx y hy
    rw [mem_conjSubgroup_iff] at hx hy
    have h1 := hVab _ hx _ hy
    have e1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (y * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e1)
  have hVMg : conjSubgroup (fsuM T L) g ≤
      Subgroup.normalizer ((conjSubgroup (fsuVM T L I) g : Subgroup G) : Set G) := by
    rw [← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left g hMV
  have hCb := centralizer_le_conjSubgroup_inf h1029 h hK g hbW hbL
  rw [conjSubgroup_inf, conjSubgroup_normalizer ⁅fsuVM T L I, K⁆ g] at hCb
  have hC1N : fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer ((conjSubgroup ⁅fsuVM T L I, K⁆ g : Subgroup G) : Set G) :=
    fun x hx => (hCb hx.2).2
  have hV0W : ⁅conjSubgroup ⁅fsuVM T L I, K⁆ g ⊓ fsuM T L,
      fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ conjSubgroup ⁅fsuVM T L I, K⁆ g :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (commutator_le_left_of_le_normalizer hC1N)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  by_contra hne
  obtain ⟨⟨v0, hv0⟩, hv01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hv01' : v0 ≠ 1 := fun h1 => hv01 (Subtype.ext h1)
  have hv0V : v0 ∈ fsuVM T L I := by
    have h1 : ⁅conjSubgroup ⁅fsuVM T L I, K⁆ g ⊓ fsuM T L,
        fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ fsuVM T L I := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono (inf_le_left.trans hV1V) le_rfl).trans
        (commutator_le_left_of_le_normalizer (inf_le_right.trans hMV))
    exact h1 hv0
  have hVMg' : fsuVM T L I ≤ conjSubgroup (fsuM T L) g := fun x hx =>
    centralizer_le_conjSubgroup h1029 h hK g (hV0W hv0) hv01'
      (Subgroup.mem_centralizer_singleton_iff.mpr (hVab x hx v0 hv0V))
  rcases hgf with hw | hGF
  · have hVN : fsuVM T L I ≤ Subgroup.normalizer
        ((conjSubgroup (fsuVM T L I) g : Subgroup G) : Set G) := by
      refine hVMg'.trans ?_
      rw [← conjSubgroup_normalizer]
      exact conjSubgroup_mono_left g hMV
    exact hnc (E3.commutator_eq_bot_iff_le_centralizer'.2
      ((E3.e3_25_centralizer_iff_normalizer (SecA.isElemAbelian_fsuVM h) (hypE322 h) hw g).2
        hVN))
  obtain ⟨a, haA, haN⟩ : ∃ a ∈ conjSubgroup ⁅fsuVM T L I, K⁆ g ⊓ fsuM T L,
      a ∉ Subgroup.normalizer (fsuUL T L I : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hle : ⁅conjSubgroup ⁅fsuVM T L I, K⁆ g ⊓ fsuM T L,
        fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ fsuUL T L I := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
        (commutator_le_left_of_le_normalizer hcon)
    have hbot := V_inf_conjSubgroup_eq_bot h10210 h ht htn hg (Or.inl rfl) hY
    rw [eq_bot_iff, ← hbot]
    exact le_inf hle hV0W
  have haM : a ∈ fsuM T L := haA.2
  obtain ⟨ha1, ha2⟩ : CFSG.conjugate (fsuUL T L I) a = ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧
      CFSG.conjugate ⁅fsuVM T L I, CFSG.conjugate L t⁆ a = fsuUL T L I := by
    rcases mem_normalizer_V12_or h37 h38 h ht htn haM with h1 | h1
    · exact absurd h1.1 haN
    · exact h1
  have hbN2 : b ∈ Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) :
      Set G) := by
    rcases mem_normalizer_V12_or h37 h38 h ht htn hbM with h1 | h1
    · exact h1.2
    · exact absurd ((SecA.conjugate_eq_self_iff.mpr hbN).symm.trans h1.1)
        (V1_ne_V2 h37 h38 h ht htn)
  have haV : ∀ v ∈ fsuUL T L I, a * v * a⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    intro v hv
    rw [← ha2] at hv
    exact SecA.mem_conjugate_iff.mp hv
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hcomm : ∀ v ∈ fsuVM T L I, (a * v * a⁻¹ * v⁻¹) * b = b * (a * v * a⁻¹ * v⁻¹) := by
    intro v hv
    have haVg : a ∈ conjSubgroup (fsuVM T L I) g := hWV haA.1
    have hvN := hVMg (hVMg' hv)
    have h1 : v * a⁻¹ * v⁻¹ ∈ conjSubgroup (fsuVM T L I) g :=
      (Subgroup.mem_normalizer_iff.mp hvN _).mp ((conjSubgroup _ g).inv_mem haVg)
    have h2 : a * v * a⁻¹ * v⁻¹ ∈ conjSubgroup (fsuVM T L I) g := by
      have e : a * v * a⁻¹ * v⁻¹ = a * (v * a⁻¹ * v⁻¹) := by group
      rw [e]
      exact (conjSubgroup _ g).mul_mem haVg h1
    exact hVgab _ h2 _ (hWV hbW)
  have hbC : b ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    refine hGF.faithful b ⟨hbM, hbN⟩ fun v hv => ?_
    have hu := haV v hv
    set u := a * v * a⁻¹ with hu_def
    set w := a * v * a⁻¹ * v⁻¹ with hw_def
    have hwb : w * b = b * w := hcomm v (hV1V hv)
    have hwV : w ∈ fsuVM T L I :=
      (fsuVM T L I).mul_mem (hV2V hu) ((fsuVM T L I).inv_mem (hV1V hv))
    have hbu : b * u * b⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
      (Subgroup.mem_normalizer_iff.mp hbN2 u).mp hu
    have hx : b * u * b⁻¹ * u⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
      Subgroup.mul_mem _ hbu (Subgroup.inv_mem _ hu)
    have hvw : v = w⁻¹ * u := by rw [hw_def, hu_def]; group
    have e : b * v * b⁻¹ * v⁻¹ = b * u * b⁻¹ * u⁻¹ := by
      have hbw' : b * w⁻¹ = w⁻¹ * b := (Commute.inv_left hwb).eq.symm
      have hwc := hVab _ ((fsuVM T L I).mul_mem (hV2V hbu) ((fsuVM T L I).inv_mem (hV2V hu)))
        _ hwV
      rw [hvw]
      calc b * (w⁻¹ * u) * b⁻¹ * (w⁻¹ * u)⁻¹ = (b * w⁻¹) * u * b⁻¹ * u⁻¹ * w := by group
        _ = w⁻¹ * (b * u * b⁻¹ * u⁻¹) * w := by rw [hbw']; group
        _ = w⁻¹ * (w * (b * u * b⁻¹ * u⁻¹)) := by rw [mul_assoc, ← hwc]
        _ = b * u * b⁻¹ * u⁻¹ := by group
    have hxV1 : b * v * b⁻¹ * v⁻¹ ∈ fsuUL T L I :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hbN v).mp hv) (Subgroup.inv_mem _ hv)
    exact V1_inf_V2_le h37 h38 h ht htn ⟨hxV1, e ▸ hx⟩
  have hLMg : L ≤ conjSubgroup (fsuM T L) g := by
    refine hGF.gen _ fun v1 hv1 hv1L => ?_
    have hv1b : v1 ∈ fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨hv1, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hbC v1 hv1)⟩
    have hw1 : a * v1 * a⁻¹ * v1⁻¹ ∈ ⁅conjSubgroup ⁅fsuVM T L I, K⁆ g ⊓ fsuM T L,
        fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G)⁆ :=
      Subgroup.commutator_mem_commutator haA hv1b
    have hu1 := haV v1 hv1
    have hw11 : a * v1 * a⁻¹ * v1⁻¹ ≠ 1 := by
      intro h1
      apply hv1L
      have e : v1 = a * v1 * a⁻¹ := by
        have := congrArg (fun x => x * v1) h1
        simpa [mul_assoc] using this.symm
      exact V1_inf_V2_le h37 h38 h ht htn ⟨hv1, e ▸ hu1⟩
    intro l hl
    refine centralizer_le_conjSubgroup h1029 h hK g (hV0W hw1) hw11 ?_
    have hlu : l * (a * v1 * a⁻¹) = (a * v1 * a⁻¹) * l :=
      Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hu1) l hl.1
    have hlv : l * v1 = v1 * l := Subgroup.mem_centralizer_singleton_iff.mp hl.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlv' : l * v1⁻¹ = v1⁻¹ * l := (Commute.inv_right hlv).eq
    calc l * (a * v1 * a⁻¹ * v1⁻¹) = (l * (a * v1 * a⁻¹)) * v1⁻¹ := by group
      _ = (a * v1 * a⁻¹) * (l * v1⁻¹) := by rw [hlu]; group
      _ = a * v1 * a⁻¹ * v1⁻¹ * l := by rw [hlv']; group
  have haMg : a ∈ conjSubgroup (fsuM T L) g :=
    conjSubgroup_mono_left g (SecA.fsuVM_le_fsuM h.fsu) (hWV haA.1)
  have hLa : CFSG.conjugate L a = CFSG.conjugate L t := by
    refine (SecA.conjugate_eq_or h37 h38 h ht htn haM).resolve_left fun h1 => ?_
    apply V1_ne_V2 h37 h38 h ht htn
    rw [← ha1, SecA.conjugate_commutator_fsuVM haM, h1]
  have hLtMg : CFSG.conjugate L t ≤ conjSubgroup (fsuM T L) g := by
    rw [← hLa]
    intro x hx
    have hx' := hLMg (SecA.mem_conjugate_iff.mp hx)
    have e : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [e]
    exact (conjSubgroup _ g).mul_mem ((conjSubgroup _ g).mul_mem
      ((conjSubgroup _ g).inv_mem haMg) hx') haMg
  have hL0 : fsuL0 T L ≤ conjSubgroup (fsuM T L) g := by
    rw [SecA.fsuL0_eq_sup h37 h38 h ht htn]
    exact sup_le hLMg hLtMg
  obtain ⟨p, hp, hp2, hpL⟩ := hGF.odd_prime
  exact hg (mem_fsuM_of_le_conjSubgroup h1013 h hp hp2 hpL hL0)

end CFSG.Quasithin.Vol2.Ch10.SecD
