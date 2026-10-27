module

public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10SecC9W

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def ClaimOut (T L I : Subgroup G) (t w : G) : Prop :=
  w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧ w ∉ fsuUL T L I ∧
    ¬ Subgroup.centralizer ({w} : Set G) ≤ fsuM T L ∧
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G)) (Subgroup.centralizer ({w} : Set G)) ∧
    thompsonJ T ≤ Subgroup.centralizer ({w} : Set G) ∧
    (Case10_1_1Three T L I → ∀ s ∈ T1 T L, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I)

theorem conj_V_pair (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {m : G} (hm : m ∈ fsuM T L) :
    (∀ x, x ∈ fsuUL T L I ↔ m⁻¹ * x * m ∈ fsuUL T L I) ∧
        (∀ x, x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔
          m⁻¹ * x * m ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) ∨
      (∀ x, x ∈ fsuUL T L I ↔ m⁻¹ * x * m ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) ∧
        (∀ x, x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔ m⁻¹ * x * m ∈ fsuUL T L I) := by
  have htM := SecA.le_fsuM T L ht
  have htm : t * m ∈ fsuM T L := (fsuM T L).mul_mem htM hm
  have key : ∀ s ∈ fsuM T L, ∀ y, y ∈ ⁅fsuVM T L I, CFSG.conjugate L s⁆ ↔
      s * y * s⁻¹ ∈ fsuUL T L I := fun s hs y => by
    rw [← SecA.conjugate_commutator_fsuVM (I := I) hs, SecA.mem_conjugate_iff]
  have hA : ∀ x, x ∈ fsuUL T L I ↔ m⁻¹ * x * m ∈ ⁅fsuVM T L I, CFSG.conjugate L m⁆ := fun x => by
    rw [key m hm, show m * (m⁻¹ * x * m) * m⁻¹ = x by group]
  have hB : ∀ x, x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔
      m⁻¹ * x * m ∈ ⁅fsuVM T L I, CFSG.conjugate L (t * m)⁆ := fun x => by
    rw [key (t * m) htm, key t htM, show t * m * (m⁻¹ * x * m) * (t * m)⁻¹ = t * x * t⁻¹ by group]
  have hne : CFSG.conjugate L m ≠ CFSG.conjugate L (t * m) := by
    intro h
    have h' := congrArg (fun Y => CFSG.conjugate Y m⁻¹) h
    simp only [SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one,
      mul_inv_cancel_right] at h'
    exact SecA.ne_conjugate htn h'
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn hm with h1 | h1 <;>
    rcases SecA.conjugate_eq_or h37 h38 hyp ht htn htm with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · left
    exact ⟨fun x => by rw [hA, h1], fun x => by rw [hB, h2]⟩
  · right
    exact ⟨fun x => by rw [hA, h1], fun x => by rw [hB, h2]⟩
  · exact absurd (h1.trans h2.symm) hne

theorem exists_conj_in_V2 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (huV1 : u ∉ fsuUL T L I) :
    ∃ m ∈ fsuM T L, m * u * m⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧
      m * u * m⁻¹ ∉ fsuUL T L I ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G))
        (fsuM T L ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G)) ∧
      ∀ x ∈ T ⊓ Subgroup.centralizer ({u} : Set G),
        m * x * m⁻¹ ∈ T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
  have hTM : IsSylowTwoOf T (fsuM T L) :=
    ⟨SecA.le_fsuM T L, hyp.fsu.sylow.1, fun h => hyp.fsu.sylow.2
      (h.trans (Subgroup.relIndex_dvd_index_of_le (SecA.le_fsuM T L)))⟩
  obtain ⟨m₀, hm₀, hSyl, hcon⟩ := exists_isSylowTwoOf_centralizer hTM u
  have eu : m₀⁻¹ * (m₀ * u * m₀⁻¹) * m₀ = u := by group
  rcases conj_V_pair h37 h38 hyp ht htn hm₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨m₀, hm₀, (h2 _).mpr (by rw [eu]; exact hu), fun h => huV1 ?_, hSyl, hcon⟩
    have := (h1 _).mp h
    rwa [eu] at this
  ·
    have hw₀ : m₀ * u * m₀⁻¹ ∈ fsuUL T L I := (h1 _).mpr (by rw [eu]; exact hu)
    have hw₀' : m₀ * u * m₀⁻¹ ∉ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := fun h => by
      have := (h2 _).mp h
      rw [eu] at this
      exact huV1 this
    have htM := SecA.le_fsuM T L ht
    have htiM : t⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem htM
    rcases conj_V_pair h37 h38 hyp ht htn htiM with ⟨k1, k2⟩ | ⟨k1, k2⟩
    ·
      exfalso
      apply huV1
      have hkey : u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔ t * u * t⁻¹ ∈ fsuUL T L I := by
        rw [← SecA.conjugate_commutator_fsuVM (I := I) htM, SecA.mem_conjugate_iff]
      have := (k1 u).mpr (by simpa using hkey.mp hu)
      exact this
    · set m := t⁻¹ * m₀ with hmdef
      have hm : m ∈ fsuM T L := (fsuM T L).mul_mem htiM hm₀
      have e : m * u * m⁻¹ = t⁻¹ * (m₀ * u * m₀⁻¹) * t⁻¹⁻¹ := by rw [hmdef]; group
      have et : ∀ z : G, t⁻¹⁻¹ * (t⁻¹ * z * t⁻¹⁻¹) * t⁻¹ = z := fun z => by group
      refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
      · rw [e]
        exact (k2 _).mpr (by rw [et]; exact hw₀)
      · rw [e]
        intro h
        have := (k1 _).mp h
        rw [et] at this
        exact hw₀' this
      · have h3 := B6.isSylowTwoOf_conjSub hSyl t⁻¹
        rw [conjSub_inf_centralizer (T.inv_mem ht), conjSub_inf_centralizer htiM] at h3
        rw [e]
        exact h3
      · intro x hx
        have hx' := hcon x hx
        have hmx : m * x * m⁻¹ = t⁻¹ * (m₀ * x * m₀⁻¹) * t⁻¹⁻¹ := by rw [hmdef]; group
        rw [e, hmx, ← conjSub_inf_centralizer (T.inv_mem ht), B6.mem_conjSub, et]
        exact hx'

end CFSG.Quasithin.Vol2.Ch10.SecC
