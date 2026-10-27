module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Clos
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Gens
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Tab

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

theorem comm_of_gen_tabs {gens : List G24}
    (hc : ∀ g ∈ gens.map (tab 24), ∀ h ∈ gens.map (tab 24), compTab g h = compTab h g) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gens}, ∀ y ∈ Subgroup.closure {g | g ∈ gens},
      x * y = y * x :=
  comm_of_gens _ fun _ hg _ hh =>
    comm_of_tab (n := 24) (hc _ (List.mem_map_of_mem hg) _ (List.mem_map_of_mem hh))

theorem sq_of_gen_tabs {gens : List G24}
    (hc : ∀ g ∈ gens.map (tab 24), ∀ h ∈ gens.map (tab 24), compTab g h = compTab h g)
    (hsq : ∀ g ∈ gens.map (tab 24), compTab g g = List.range 24) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gens}, x * x = 1 :=
  sq_of_gens _ (fun _ hg _ hh =>
    comm_of_tab (n := 24) (hc _ (List.mem_map_of_mem hg) _ (List.mem_map_of_mem hh)))
    fun g hg => eq_of_tab_eq (n := 24) (by
      rw [tab_mul, tab_one_L]
      exact hsq _ (List.mem_map_of_mem hg))

theorem isE2_of_enum {k : ℕ} {gens : List G24} {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK 24 (gens.map (tab 24)) L par)
    (hc : ∀ g ∈ gens.map (tab 24), ∀ h ∈ gens.map (tab 24), compTab g h = compTab h g)
    (hsq : ∀ g ∈ gens.map (tab 24), compTab g g = List.range 24) (hlen : L.length = 2 ^ k) :
    IsE2 k ↥(Subgroup.closure {x | x ∈ gens}) := by
  obtain ⟨-, hcard, -⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective gens h
  exact PermLat.isElemAbelianOfRank_of_card
    (fun x y => Subtype.ext (comm_of_gen_tabs hc x.1 x.2 y.1 y.2))
    (fun x => Subtype.ext (sq_of_gen_tabs hc hsq x.1 x.2)) (hcard.trans hlen)

theorem isExtraspecial2_of_enum {gens : List G24} {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK 24 (gens.map (tab 24)) L par) {zT : List ℕ} (hzL : zT ∈ L)
    (hz1 : zT ≠ List.range 24) (hzc : ∀ t ∈ L, compTab t zT = compTab zT t)
    (hzz : compTab zT zT = List.range 24)
    (hgsq : ∀ g ∈ gens.map (tab 24), compTab g g = List.range 24 ∨ compTab g g = zT)
    (hgc : ∀ g ∈ gens.map (tab 24), ∀ h ∈ gens.map (tab 24),
      compTab g h = compTab h g ∨ compTab g h = compTab zT (compTab h g))
    (hcen : ∀ t ∈ L, (∀ g ∈ gens.map (tab 24), compTab t g = compTab g t) →
      t = List.range 24 ∨ t = zT) {m : ℕ} (hlen : L.length = 2 ^ (1 + 2 * m)) (hm : 1 ≤ m) :
    IsExtraspecial2 m ↥(Subgroup.closure {x | x ∈ gens}) := by
  obtain ⟨hmem, hcard, hreach⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective gens h
  obtain ⟨z, hzmem, hzT⟩ := hreach zT hzL
  have hgens : ∀ g : G24, g ∈ gens → g ∈ Subgroup.closure {x | x ∈ gens} :=
    fun g hg => Subgroup.subset_closure hg
  let zV : ↥(Subgroup.closure {x | x ∈ gens}) := ⟨z, hzmem⟩
  refine isExtraspecial2_of_gens (z := zV)
    (((↑) : ↥(Subgroup.closure {x | x ∈ gens}) → G24) ⁻¹' {x | x ∈ gens})
    Subgroup.closure_closure_coe_preimage ?_ ?_ ?_ ?_ ?_ ?_ (hcard.trans hlen) hm
  · intro hz
    apply hz1
    have := congrArg (fun x : ↥(Subgroup.closure {x | x ∈ gens}) => tab 24 x.1) hz
    simpa [zV, hzT, tab_one_L] using this
  · intro y
    apply Subtype.ext
    apply comm_of_tab (n := 24)
    rw [hzT]
    exact hzc _ ((hmem y.1).mp y.2)
  · apply Subtype.ext
    apply eq_of_tab_eq (n := 24)
    show tab 24 (z * z) = tab 24 1
    rw [tab_mul, hzT, tab_one_L]
    exact hzz
  · intro g hg h hh
    have hgT : tab 24 g.1 ∈ gens.map (tab 24) := List.mem_map_of_mem hg
    have hhT : tab 24 h.1 ∈ gens.map (tab 24) := List.mem_map_of_mem hh
    rcases hgc _ hgT _ hhT with e | e
    · left
      apply Subtype.ext
      exact eq_of_tab_eq (n := 24)
        (by rw [Subgroup.coe_mul, Subgroup.coe_mul, tab_mul, tab_mul]; exact e)
    · right
      apply Subtype.ext
      apply eq_of_tab_eq (n := 24)
      show tab 24 (g.1 * h.1) = tab 24 (z * (h.1 * g.1))
      rw [tab_mul, tab_mul, tab_mul, hzT]
      exact e
  · intro g hg
    have hgT : tab 24 g.1 ∈ gens.map (tab 24) := List.mem_map_of_mem hg
    rcases hgsq _ hgT with e | e
    · left
      apply Subtype.ext
      apply eq_of_tab_eq (n := 24)
      show tab 24 (g.1 * g.1) = tab 24 1
      rw [tab_mul, tab_one_L]
      exact e
    · right
      apply Subtype.ext
      apply eq_of_tab_eq (n := 24)
      show tab 24 (g.1 * g.1) = tab 24 z
      rw [tab_mul, hzT]
      exact e
  · intro x hx
    have hxT : tab 24 x.1 ∈ L := (hmem x.1).mp x.2
    have hcT : ∀ g ∈ gens.map (tab 24), compTab (tab 24 x.1) g = compTab g (tab 24 x.1) := by
      intro gt hgt
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgt
      have := hx ⟨g, hgens g hg⟩ hg
      have h2 := congrArg (fun y : ↥(Subgroup.closure {x | x ∈ gens}) => tab 24 y.1) this
      simpa [tab_mul] using h2
    rcases hcen _ hxT hcT with e | e
    · left
      apply Subtype.ext
      exact eq_of_tab_eq (n := 24) (by rw [e, Subgroup.coe_one, tab_one_L])
    · right
      apply Subtype.ext
      exact eq_of_tab_eq (n := 24) (by rw [e, hzT])

theorem mem_normalizer_of_enum {gens : List G24} {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK 24 (gens.map (tab 24)) L par) {g : G24}
    (h1 : ∀ t ∈ L, ∃ s ∈ L, compTab (tab 24 g) t = compTab s (tab 24 g))
    (h2 : ∀ t ∈ L, ∃ s ∈ L, compTab t (tab 24 g) = compTab (tab 24 g) s) :
    g ∈ Subgroup.normalizer (Subgroup.closure {x | x ∈ gens} : Set G24) := by
  obtain ⟨hmem, -, hreach⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective gens h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨s, hs, hsc⟩ := h1 _ ((hmem x).mp hx)
    obtain ⟨y, hy, rfl⟩ := hreach s hs
    have h3 : g * x = y * g :=
      eq_of_tab_eq (n := 24) (by rw [tab_mul g x, tab_mul y g]; exact hsc)
    have h4 : g * x * g⁻¹ = y := by rw [h3]; group
    rwa [h4]
  · intro hx
    obtain ⟨s, hs, hsc⟩ := h2 _ ((hmem (g * x * g⁻¹)).mp hx)
    obtain ⟨y, hy, rfl⟩ := hreach s hs
    have h3 : g * x * g⁻¹ * g = g * y :=
      eq_of_tab_eq (n := 24) (by rw [tab_mul (g * x * g⁻¹) g, tab_mul g y]; exact hsc)
    have h4 : g * x = g * y := by simpa [mul_assoc] using h3
    rwa [mul_left_cancel h4]

theorem closure_le_normalizer_of_enum {gens gensV : List G24} {gT : List (List ℕ)}
    (hgT : gens.map (tab 24) = gT) {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (hV : EnumOK 24 (gensV.map (tab 24)) L par)
    (h : ∀ gt ∈ gT, (∀ t ∈ L, ∃ s ∈ L, compTab gt t = compTab s gt) ∧
      ∀ t ∈ L, ∃ s ∈ L, compTab t gt = compTab gt s) :
    Subgroup.closure {x | x ∈ gens} ≤
      Subgroup.normalizer (Subgroup.closure {x | x ∈ gensV} : Set G24) := by
  rw [Subgroup.closure_le]
  intro g hg
  have hmem : tab 24 g ∈ gT := hgT ▸ List.mem_map_of_mem hg
  exact mem_normalizer_of_enum hV (h _ hmem).1 (h _ hmem).2

end CFSG.Quasithin.A312M24
