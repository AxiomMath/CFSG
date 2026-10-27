module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3WrMono
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Syl

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.B6 CFSG.QuasithinUnique

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

@[expose] noncomputable def fourKU (hF : Nat.card F = p ^ 2) : Subgroup (↥(muU hF) × ↥(muU hF)) :=
  (powMonoidHom 4 : ↥(muU hF) × ↥(muU hF) →* ↥(muU hF) × ↥(muU hF)).ker

theorem isPGroup_fourKU (hF : Nat.card F = p ^ 2) : IsPGroup 2 (fourKU hF) := fun g =>
  ⟨2, Subtype.ext (by simpa using (MonoidHom.mem_ker.mp g.2))⟩

@[expose] noncomputable def evenCU (hF : Nat.card F = p ^ 2) : Subgroup (PSU3F p F) :=
  ((fourKU hF).map (diagHomU hF)).map (piU p F)

theorem isPGroup_evenCU (hF : Nat.card F = p ^ 2) : IsPGroup 2 (evenCU hF) :=
  ((isPGroup_fourKU hF).map (diagHomU hF)).map (piU p F)

@[expose] noncomputable def diagCU (hF : Nat.card F = p ^ 2) : Subgroup (PSU3F p F) :=
  (diagU hF).map (piU p F)

@[expose] noncomputable def monoCU (hF : Nat.card F = p ^ 2) : Subgroup (PSU3F p F) :=
  (monoU hF).map (piU p F)

theorem evenCU_le_diagCU (hF : Nat.card F = p ^ 2) : evenCU hF ≤ diagCU hF :=
  Subgroup.map_mono (fun _ ⟨ab, _, h⟩ => h ▸ diagHomU_mem hF ab)

theorem diagCU_le_monoCU (hF : Nat.card F = p ^ 2) : diagCU hF ≤ monoCU hF :=
  Subgroup.map_mono (diagU_le_monoU hF)

theorem monoCU_le_leviCU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : monoCU hF ≤ leviCU hF :=
  Subgroup.map_mono (monoU_le_leviU hp2 hF)

theorem ker_piU_le_diagU (hF : Nat.card F = p ^ 2) : (piU p F).ker ≤ diagU hF := by
  intro g hg
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_ker hF hg
  rw [mem_diagU_iff, hc]
  simp [Matrix.scalar_apply]

theorem ker_piU_le_monoU (hF : Nat.card F = p ^ 2) : (piU p F).ker ≤ monoU hF :=
  (ker_piU_le_diagU hF).trans (diagU_le_monoU hF)

theorem odd_index_monoCU [Finite F] (hF : Nat.card F = p ^ 2) (hp : p % 4 = 3) :
    Odd (monoCU hF).index := by
  rw [monoCU, Subgroup.index_map_eq _ piU_surjective (ker_piU_le_monoU hF)]
  exact odd_index_monoU hF hp

theorem relIndex_diagCU_monoCU [Finite F] (hF : Nat.card F = p ^ 2) :
    (diagCU hF).relIndex (monoCU hF) = 2 := by
  have h1 := Subgroup.relIndex_mul_index (diagU_le_monoU hF)
  rw [relIndex_diagU_monoU hF] at h1
  have h2 := Subgroup.relIndex_mul_index (diagCU_le_monoCU hF)
  rw [diagCU, monoCU, Subgroup.index_map_eq _ piU_surjective (ker_piU_le_diagU hF),
    Subgroup.index_map_eq _ piU_surjective (ker_piU_le_monoU hF), ← h1] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2

theorem exists_wreathed_sylow_u [Finite F] (hF : Nat.card F = p ^ 2) (hp : p % 4 = 3) :
    ∃ U : Subgroup (PSU3F p F), IsSylowTwoOf U ⊤ ∧ U ≤ monoCU hF ∧ evenCU hF ≤ U ∧
      ¬ U ≤ diagCU hF := by
  obtain ⟨S, hS, hES⟩ := exists_isSylowTwoOf_ge (isPGroup_evenCU hF)
    ((evenCU_le_diagCU hF).trans (diagCU_le_monoCU hF))
  refine ⟨S, isSylowTwoOf_top_of_odd_index (odd_index_monoCU hF hp) hS, hS.1, hES, fun hSD => ?_⟩
  have h := Subgroup.relIndex_mul_relIndex S (diagCU hF) (monoCU hF) hSD (diagCU_le_monoCU hF)
  rw [relIndex_diagCU_monoCU hF] at h
  exact hS.2.2 (Dvd.intro_left _ h)

end CFSG.Quasithin.E2P.Asc80
