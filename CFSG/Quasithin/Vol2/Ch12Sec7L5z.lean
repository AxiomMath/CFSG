module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5y
public import CFSG.Quasithin.Vol2.Ch10SecG31J
public import CFSG.Quasithin.Vol2.Ch10SecG31K

public section

namespace CFSG.Quasithin.G31

open CFSG.Open CFSG.Quasithin.ASInputs

variable {V : Type} [CommGroup V]

@[expose] def orbitOn (A : Subgroup (MulAut V)) (X : Subgroup V) : Set (Subgroup V) :=
  {Y | ∃ g ∈ A, X.map (g : MulAut V).toMonoidHom = Y}

theorem map_map_mulAut (X : Subgroup V) (g h : MulAut V) :
    (X.map g.toMonoidHom).map h.toMonoidHom = X.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem mem_orbitOn_self (A : Subgroup (MulAut V)) (X : Subgroup V) : X ∈ orbitOn A X :=
  ⟨1, A.one_mem, by
    ext x
    simp⟩

theorem orbitOn_symm {A : Subgroup (MulAut V)} {X Y : Subgroup V} (h : Y ∈ orbitOn A X) :
    X ∈ orbitOn A Y := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, A.inv_mem hg, ?_⟩
  rw [map_map_mulAut, inv_mul_cancel]
  ext x
  simp

theorem orbitOn_trans {A : Subgroup (MulAut V)} {X Y Z : Subgroup V} (h1 : Y ∈ orbitOn A X)
    (h2 : Z ∈ orbitOn A Y) : Z ∈ orbitOn A X := by
  obtain ⟨g, hg, rfl⟩ := h1
  obtain ⟨h, hh, rfl⟩ := h2
  exact ⟨h * g, A.mul_mem hh hg, (map_map_mulAut X g h).symm⟩

theorem orbitOn_eq {A : Subgroup (MulAut V)} {X Y : Subgroup V} (h : Y ∈ orbitOn A X) :
    orbitOn A Y = orbitOn A X := by
  ext Z
  exact ⟨fun hZ => orbitOn_trans h hZ, fun hZ => orbitOn_trans (orbitOn_symm h) hZ⟩

theorem orbitOn_mono {A B : Subgroup (MulAut V)} (hAB : A ≤ B) {X : Subgroup V} :
    orbitOn A X ⊆ orbitOn B X := fun _ ⟨g, hg, he⟩ => ⟨g, hAB hg, he⟩

theorem g31G_le (Gm : Subgroup (MulAut V)) (Δ : Set (Subgroup V)) : g31G Gm Δ ≤ Gm :=
  iSup₂_le fun _ _ => (Subgroup.closure_le _).mpr fun _ hg => hg.1

theorem exists_orbit_partition [Finite V] (Gm : Subgroup (MulAut V)) (X₀ : Subgroup V) :
    ∃ (s : ℕ) (hs : 0 < s) (Δ : Fin s → Set (Subgroup V)), X₀ ∈ Δ ⟨0, hs⟩ ∧
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧ (⋃ i, Δ i) = orbitOn Gm X₀ ∧
      (∀ i, (Δ i).Nonempty) ∧
      (∀ i, ∀ X ∈ Δ i, ∀ g ∈ g31G Gm (orbitOn Gm X₀), X.map (g : MulAut V).toMonoidHom ∈ Δ i) ∧
      (∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ g31G Gm (orbitOn Gm X₀),
        X.map (g : MulAut V).toMonoidHom = Y) := by
  classical
  set Δ₀ := orbitOn Gm X₀ with hΔ₀
  set G₀ := g31G Gm Δ₀ with hG₀
  have hG₀Gm : G₀ ≤ Gm := g31G_le Gm Δ₀
  set O : Set (Set (Subgroup V)) := (fun X => orbitOn G₀ X) '' Δ₀ with hO
  have hOfin : O.Finite := (Set.toFinite Δ₀).image _
  set F := hOfin.toFinset with hF
  have ho₀ : orbitOn G₀ X₀ ∈ F :=
    (Set.Finite.mem_toFinset hOfin).mpr ⟨X₀, mem_orbitOn_self Gm X₀, rfl⟩
  have hs : 0 < F.card := Finset.card_pos.mpr ⟨_, ho₀⟩
  set e : ↥F ≃ Fin F.card := F.equivFin with he
  set i₀ := e ⟨_, ho₀⟩ with hi₀
  set σ := Equiv.swap (⟨0, hs⟩ : Fin F.card) i₀ with hσ
  set Δ : Fin F.card → Set (Subgroup V) := fun i => (e.symm (σ i) : Set (Subgroup V)) with hΔ
  have hmemF : ∀ i, (e.symm (σ i) : Set (Subgroup V)) ∈ O := fun i =>
    (Set.Finite.mem_toFinset hOfin).mp (e.symm (σ i)).2
  have hΔorb : ∀ i, ∃ X ∈ Δ₀, Δ i = orbitOn G₀ X := fun i => by
    obtain ⟨X, hX, he'⟩ := hmemF i
    exact ⟨X, hX, he'.symm⟩
  have hsub : ∀ X ∈ Δ₀, orbitOn G₀ X ⊆ Δ₀ := fun X hX Y hY =>
    orbitOn_trans hX (orbitOn_mono hG₀Gm hY)
  refine ⟨F.card, hs, Δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : σ ⟨0, hs⟩ = i₀ := Equiv.swap_apply_left _ _
    show X₀ ∈ (e.symm (σ ⟨0, hs⟩) : Set (Subgroup V))
    rw [h0, hi₀, Equiv.symm_apply_apply]
    exact mem_orbitOn_self G₀ X₀
  · intro i j hij
    rw [Set.disjoint_left]
    intro Y hYi hYj
    apply hij
    obtain ⟨X, -, hXi⟩ := hΔorb i
    obtain ⟨X', -, hXj⟩ := hΔorb j
    have h1 : Δ i = Δ j := by
      rw [hXi, hXj]
      rw [hXi] at hYi
      rw [hXj] at hYj
      rw [← orbitOn_eq hYi, ← orbitOn_eq hYj]
    have h2 : e.symm (σ i) = e.symm (σ j) := Subtype.ext h1
    exact σ.injective (e.symm.injective h2)
  · ext Y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨X, hX, hXi⟩ := hΔorb i
      rw [hXi] at hi
      exact hsub X hX hi
    · intro hY
      have hOY : orbitOn G₀ Y ∈ F := (Set.Finite.mem_toFinset hOfin).mpr ⟨Y, hY, rfl⟩
      refine ⟨σ.symm (e ⟨_, hOY⟩), ?_⟩
      show Y ∈ (e.symm (σ (σ.symm (e ⟨_, hOY⟩))) : Set (Subgroup V))
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      exact mem_orbitOn_self G₀ Y
  · intro i
    obtain ⟨X, -, hXi⟩ := hΔorb i
    exact ⟨X, hXi ▸ mem_orbitOn_self G₀ X⟩
  · intro i X hX g hg
    obtain ⟨Y, -, hYi⟩ := hΔorb i
    rw [hYi] at hX ⊢
    exact orbitOn_trans hX ⟨g, hg, rfl⟩
  · intro i X hX Y hY
    obtain ⟨Z, -, hZi⟩ := hΔorb i
    rw [hZi] at hX hY
    exact orbitOn_trans (orbitOn_symm hX) hY

theorem exists_mulHyp [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 Gm = ⊥) {X₀ : Subgroup V} (hX₀ : Nat.card ↥X₀ = 2)
    (h4 : 4 ≤ Nat.card ↥(transvGroup Gm X₀)) :
    ∃ (s : ℕ) (hs : 0 < s) (Δ : Fin s → Set (Subgroup V)), X₀ ∈ Δ ⟨0, hs⟩ ∧
      MulHyp Gm (orbitOn Gm X₀) Δ := by
  obtain ⟨s, hs, Δ, h0, hdisj, hunion, hne, hginv, hgtrans⟩ := exists_orbit_partition Gm X₀
  refine ⟨s, hs, Δ, h0, ⟨hV, hO2, ?_, ?_, ?_, ?_, hdisj, hunion, hne, hginv, hgtrans⟩⟩
  · rintro _ ⟨g, -, rfl⟩
    rw [Subgroup.card_map_of_injective g.injective, hX₀]
  · rintro _ ⟨g, hg, rfl⟩ h hh
    exact ⟨h * g, Gm.mul_mem hh hg, (map_map_mulAut X₀ g h).symm⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    refine ⟨h * g⁻¹, Gm.mul_mem hh (Gm.inv_mem hg), ?_⟩
    rw [map_map_mulAut, mul_assoc, inv_mul_cancel, mul_one]
  · rintro _ ⟨g, hg, rfl⟩
    rw [hO2, inf_bot_eq, Subgroup.relIndex_bot_left, ← map_conj_transvGroup hg,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h4

end CFSG.Quasithin.G31

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.L715 S127.L716 G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem exists_mulHyp
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    ∃ (n : ℕ) (hn : 0 < n) (Δ : Fin n → Set (Subgroup ↥(Ut T L V z))), X1 T L V z ∈ Δ ⟨0, hn⟩ ∧
      MulHyp (Hs T L V z) (orbitOn (Hs T L V z) (X1 T L V z)) Δ :=
  G31.exists_mulHyp (fun v => Subtype.ext ((s.elemAbelian_Ut h1222).2 _ v.2))
    (s.pCoreOf_Hs h1222) (s.card_X1 h1222) (s.four_le_card_transvGroup h1222 hU)

end CFSG.Quasithin.H13.S127.L715.Set714
