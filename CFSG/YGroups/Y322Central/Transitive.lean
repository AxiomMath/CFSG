module

public import CFSG.YGroups.Exact.Model

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.YGroups.ModelNative

theorem chain_transitive {n : ℕ} {O : Array (Array ℕ)} {W : Array (List ℤ)} {base : Array ℕ}
    (h : chainOK n O W base = true) (hbase : 0 < base.size)
    (h0 : (chainSizes n O W base)[0]? = some n) :
    ∃ b : Fin n, (b : ℕ) = base[0]! ∧ ∀ y : Fin n, ∃ g ∈ arrClosure n O, g b = y := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hO, hS⟩, hSinv⟩, hinit⟩, hinv⟩, hder⟩, hbase'⟩, horb⟩ := h
  set S := (strongOf n O W).1 with hSdef
  set Sinv := (strongOf n O W).2 with hSinvdef
  have hinit' : ∀ k < O.size, eqA n S[k]! O[k]! = true := fun k hk => allLt_spec hinit hk
  have hinv' : ∀ j < S.size, isInvA n S[j]! Sinv[j]! = true := fun j hj => allLt_spec hinv hj
  have hder' : ∀ i < W.size, lettersOK (O.size + i) W[i]! = true ∧
      eqA n S[O.size + i]! (wordA n S Sinv W[i]!) = true := by
    intro i hi
    have := allLt_spec hder hi
    simpa [Bool.and_eq_true] using this
  have hmem := strong_mem hO hinv' hinit' hder' hS
  have hSmem : ∀ t ∈ S, Rep n t (permOfArr n t) ∧ permOfArr n t ∈ arrClosure n O := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ht
    have hj' : j < S.size := hj
    rw [← getElem!_pos S j hj']
    exact ⟨(rep_permOfArr (hinv' j hj')).1, hmem j hj'⟩
  have hor := allLt_spec horb hbase
  have hsteps : ∀ t ∈ levelGens S base 0,
      Rep n t (permOfArr n t) ∧ permOfArr n t ∈ arrClosure n O :=
    fun t ht => hSmem t (mem_levelGens.1 ht).1
  obtain ⟨b, hb, P, hPcard, hP⟩ := orbit_reach hsteps hor
  have hsz : (orbitSearch n base[0]! (levelGens S base 0)).pts.size = n := by
    have hsizes : chainSizes n O W base = (List.range base.size).map
        (fun i => (orbitSearch n base[i]! (levelGens S base i)).pts.size) := rfl
    rw [hsizes, List.getElem?_map, List.getElem?_range hbase] at h0
    exact Option.some.inj h0
  refine ⟨b, hb, fun y => ?_⟩
  have hP' : P = Finset.univ :=
    Finset.eq_univ_of_card P (by rw [hPcard, hsz, Fintype.card_fin])
  exact hP y (hP' ▸ Finset.mem_univ y)

theorem normalCore_eq_ker_of_transitive {G X : Type*} [Group G] [Finite G] [Finite X]
    (ρ : G →* Equiv.Perm X) (b : X) (H : Subgroup G) (hfix : ∀ h ∈ H, ρ h b = b)
    (htrans : ∀ y : X, ∃ g : G, ρ g b = y) (hcard : Nat.card G ≤ Nat.card H * Nat.card X) :
    H.normalCore = ρ.ker := by
  let _ : MulAction G X := MulAction.compHom X ρ
  have hsmul : ∀ (g : G) (x : X), g • x = ρ g x := fun g x => rfl
  have horb : MulAction.orbit G b = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := htrans y
    exact ⟨g, (hsmul g b).trans hg⟩
  have h1 := MulAction.index_stabilizer G b
  rw [horb, Set.ncard_univ] at h1
  have h2 := (MulAction.stabilizer G b).card_mul_index
  rw [h1] at h2
  have : Nonempty X := ⟨b⟩
  have hXpos : 0 < Nat.card X := Nat.card_pos (α := X)
  have hHle : H ≤ MulAction.stabilizer G b := fun h hh => by
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact hfix h hh
  have hHeq : H = MulAction.stabilizer G b := by
    refine Subgroup.eq_of_le_of_card_ge hHle ?_
    refine Nat.le_of_mul_le_mul_right ?_ hXpos
    rw [h2]
    exact hcard
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker]
    ext y
    obtain ⟨a, rfl⟩ := htrans y
    have hmem : a⁻¹ * g * a⁻¹⁻¹ ∈ H := hg a⁻¹
    rw [hHeq, MulAction.mem_stabilizer_iff, hsmul] at hmem
    simp only [inv_inv, map_mul, map_inv, Equiv.Perm.mul_apply] at hmem
    have := congrArg (ρ a) hmem
    simpa using this
  · intro hg a
    rw [hHeq, MulAction.mem_stabilizer_iff, hsmul]
    have : ρ g = 1 := hg
    simp [this]

end CFSG.YGroups
