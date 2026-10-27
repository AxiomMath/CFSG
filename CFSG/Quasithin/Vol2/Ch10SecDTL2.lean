module

public import CFSG.Quasithin.Vol2.Ch10SecDTL
public import CFSG.Quasithin.Vol2.Ch10SecG31A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Quasithin.ASInputs

variable {V : Type} [CommGroup V]

theorem map_one_mulAut (X : Subgroup V) : X.map (1 : MulAut V).toMonoidHom = X := by
  ext x
  simp

theorem map_mul_mulAut (g k : MulAut V) (X : Subgroup V) :
    (X.map g.toMonoidHom).map k.toMonoidHom = X.map (k * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

@[expose] def orbitSetoid (H : Subgroup (MulAut V)) : Setoid (Subgroup V) where
  r X Y := ∃ g ∈ H, X.map g.toMonoidHom = Y
  iseqv := by
    refine ⟨fun X => ⟨1, H.one_mem, map_one_mulAut X⟩, ?_, ?_⟩
    · rintro X Y ⟨g, hg, rfl⟩
      refine ⟨g⁻¹, H.inv_mem hg, ?_⟩
      rw [map_mul_mulAut, inv_mul_cancel, map_one_mulAut]
    · rintro X Y Z ⟨g, hg, rfl⟩ ⟨k, hk, rfl⟩
      exact ⟨k * g, H.mul_mem hk hg, (map_mul_mulAut g k X).symm⟩

variable [Finite V]

theorem false_of_g31_aux (hV : ∀ v : V, v ^ 2 = 1) {Gm G0 : Subgroup (MulAut V)} {a b : V}
    (hab : a ≠ b) (hb : b ≠ 1) (hfix : ∀ g ∈ Gm, g (a * b) = a * b)
    (hG0le : G0 ≤ Gm) {X0 : Subgroup V} (hX0 : X0 = Subgroup.zpowers a) {s : ℕ} {hs : 0 < s}
    {Δ : Fin s → Set (Subgroup V)} {Δ₀ : Set (Subgroup V)} (hX00 : X0 ∈ Δ ⟨0, hs⟩)
    (hXbΔ : Subgroup.zpowers b ∈ Δ₀) (hunion : (⋃ i, Δ i) = Δ₀)
    (hsup : (⨆ i, g31G Gm (Δ i)) = G0)
    (hcent : ∀ i j, i ≠ j → ∀ x ∈ g31G Gm (Δ i), ∀ v ∈ g31V (Δ j), x v = v)
    (hpts : Δ ⟨0, hs⟩ = {X | X ≤ g31V (Δ ⟨0, hs⟩) ∧ Nat.card X = 2})
    (h8 : 8 ≤ Nat.card (g31V (Δ ⟨0, hs⟩)))
    (hGtrans : ∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ G0, X.map g.toMonoidHom = Y) : False := by
  have hle : ∀ i, ∀ X ∈ Δ i, X ≤ g31V (Δ i) := fun i X hX =>
    le_iSup₂ (f := fun (Y : Subgroup V) (_ : Y ∈ Δ i) => Y) X hX
  have ha0 : a ∈ g31V (Δ ⟨0, hs⟩) := hle _ X0 hX00 (hX0 ▸ Subgroup.mem_zpowers a)
  have key : ∀ P ∈ Δ ⟨0, hs⟩, ∀ Q ∈ Δ ⟨0, hs⟩, P ≠ Q →
      (∀ g ∈ G0, P.map g.toMonoidHom = P) → False := by
    intro P hP Q hQ hPQ hPfix
    obtain ⟨g, hg, hgPQ⟩ := hGtrans _ P hP Q hQ
    exact hPQ ((hPfix g hg).symm.trans hgPQ)
  have hfix0 : ∀ g ∈ G0, g (a * b) = a * b := fun g hg => hfix g (hG0le hg)
  have hmemG0 : ∀ i, ∀ g ∈ g31G Gm (Δ i), g ∈ G0 := fun i g hg =>
    hsup ▸ (le_iSup (fun i => g31G Gm (Δ i)) i) hg
  obtain ⟨j, hj⟩ : ∃ j, Subgroup.zpowers b ∈ Δ j := by
    rw [← hunion] at hXbΔ
    exact Set.mem_iUnion.mp hXbΔ
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV])
  have hab1 : a * b ≠ 1 := fun h1 => hab (by rw [← hbinv]; exact eq_inv_of_mul_eq_one_left h1)
  by_cases hj0 : j = ⟨0, hs⟩
  · subst hj0
    have hb0 : b ∈ g31V (Δ ⟨0, hs⟩) := hle _ _ hj (Subgroup.mem_zpowers b)
    have hP : Subgroup.zpowers (a * b) ∈ Δ ⟨0, hs⟩ := by
      rw [hpts]
      exact ⟨(Subgroup.zpowers_le).mpr (Subgroup.mul_mem _ ha0 hb0),
        card_zpowers_of_sq (hV _) hab1⟩
    refine key _ hP X0 hX00 ?_ fun g hg => by rw [map_zpowers_mulAut, hfix0 g hg]
    intro hPX
    have hmem : a * b ∈ X0 := hPX ▸ Subgroup.mem_zpowers (a * b)
    rw [hX0] at hmem
    rcases (mem_zpowers_iff_of_sq (hV a)).mp hmem with h1 | h1
    · exact hab1 h1
    · exact hb (by
        calc b = a⁻¹ * (a * b) := by group
          _ = 1 := by rw [h1, inv_mul_cancel])
  have hfixa : ∀ g ∈ G0, g a = a := by
    have hstab : G0 ≤ MulAction.stabilizer (MulAut V) a := by
      rw [← hsup]
      refine iSup_le fun i g hg => ?_
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      by_cases hi : i = ⟨0, hs⟩
      · subst hi
        have hgb : g b = b := hcent _ j (fun h => hj0 h.symm) g hg b
          (hle _ _ hj (Subgroup.mem_zpowers b))
        have hgab := hfix0 g (hmemG0 _ g hg)
        rw [map_mul, hgb] at hgab
        exact mul_right_cancel hgab
      · exact hcent i ⟨0, hs⟩ hi g hg a ha0
    intro g hg
    have := hstab hg
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  obtain ⟨u, hu, hu1, hua⟩ : ∃ u ∈ g31V (Δ ⟨0, hs⟩), u ≠ 1 ∧ u ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (g31V (Δ ⟨0, hs⟩) : Set V) ⊆ {1, a} := fun u hu => by
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · exact Or.inr (hcon u hu hu1)
    have h2 : Nat.card (g31V (Δ ⟨0, hs⟩)) ≤ 2 := by
      rw [show Nat.card (g31V (Δ ⟨0, hs⟩)) = (g31V (Δ ⟨0, hs⟩) : Set V).ncard from
        Nat.card_coe_set_eq _]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  have hQ : Subgroup.zpowers u ∈ Δ ⟨0, hs⟩ := by
    rw [hpts]
    exact ⟨(Subgroup.zpowers_le).mpr hu, card_zpowers_of_sq (hV u) hu1⟩
  refine key X0 hX00 _ hQ ?_ fun g hg => by rw [hX0, map_zpowers_mulAut, hfixa g hg]
  intro hXQ
  have hmem : u ∈ X0 := hXQ ▸ Subgroup.mem_zpowers u
  rw [hX0] at hmem
  rcases (mem_zpowers_iff_of_sq (hV a)).mp hmem with h1 | h1
  · exact hu1 h1
  · exact hua h1

theorem false_of_g31 (hG31 : AS_G_3_1_O2) (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 Gm = ⊥) {a b : V} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hA : 4 ≤ Nat.card (transvGroup Gm (Subgroup.zpowers a))) {g₁ : MulAut V} (hg₁ : g₁ ∈ Gm)
    (hg₁a : g₁ a = b) (hfix : ∀ g ∈ Gm, g (a * b) = a * b) : False := by
  classical
  set X0 := Subgroup.zpowers a with hX0
  set Δ₀ : Set (Subgroup V) := {X | ∃ g ∈ Gm, X0.map g.toMonoidHom = X} with hΔ₀
  set G0 := g31G Gm Δ₀ with hG0
  have hG0le : G0 ≤ Gm := iSup₂_le fun X _ => transvGroup_le Gm X
  have hX0Δ : X0 ∈ Δ₀ := ⟨1, Gm.one_mem, map_one_mulAut X0⟩
  have hXbΔ : Subgroup.zpowers b ∈ Δ₀ := ⟨g₁, hg₁, by rw [hX0, map_zpowers_mulAut, hg₁a]⟩
  have hcard : ∀ X ∈ Δ₀, Nat.card X = 2 := by
    rintro X ⟨g, hg, rfl⟩
    rw [hX0, map_zpowers_mulAut]
    exact card_zpowers_of_sq (hV _) (fun h1 => ha (g.injective (h1.trans (map_one g).symm)))
  have hinv : ∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map g.toMonoidHom ∈ Δ₀ := by
    rintro X ⟨h, hh, rfl⟩ g hg
    exact ⟨g * h, Gm.mul_mem hg hh, (map_mul_mulAut h g X0).symm⟩
  have htrans : ∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map g.toMonoidHom = Y := by
    rintro X ⟨h, hh, rfl⟩ Y ⟨k, hk, rfl⟩
    refine ⟨k * h⁻¹, Gm.mul_mem hk (Gm.inv_mem hh), ?_⟩
    rw [map_mul_mulAut, mul_assoc, inv_mul_cancel, mul_one]
  have hrel : ∀ X ∈ Δ₀, 4 ≤ (transvGroup Gm X ⊓ pCoreOf 2 Gm).relIndex (transvGroup Gm X) := by
    rintro X ⟨g, hg, rfl⟩
    rw [hO2, inf_bot_eq, Subgroup.relIndex_bot_left]
    exact hA.trans (card_transvGroup_le hg X0)
  have : Finite (Subgroup V) :=
    Finite.of_injective (fun H : Subgroup V => (H : Set V)) SetLike.coe_injective
  set r := orbitSetoid G0 with hr
  set Q0 : Set (Quotient r) := (Quotient.mk r) '' Δ₀ with hQ0
  have hq0 : Quotient.mk r X0 ∈ Q0 := ⟨X0, hX0Δ, rfl⟩
  have : Nonempty ↥Q0 := ⟨⟨_, hq0⟩⟩
  have hs : 0 < Nat.card ↥Q0 := Nat.card_pos
  set e' : ↥Q0 ≃ Fin (Nat.card ↥Q0) := Finite.equivFin ↥Q0 with he'
  set e : ↥Q0 ≃ Fin (Nat.card ↥Q0) := e'.trans (Equiv.swap (e' ⟨_, hq0⟩) ⟨0, hs⟩) with he
  have he0 : e ⟨_, hq0⟩ = ⟨0, hs⟩ := by
    rw [he, Equiv.trans_apply, Equiv.swap_apply_left]
  set Δ : Fin (Nat.card ↥Q0) → Set (Subgroup V) :=
    fun i => {X | ∃ hX : X ∈ Δ₀, e ⟨Quotient.mk r X, X, hX, rfl⟩ = i} with hΔ
  have hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro X ⟨hX, rfl⟩ ⟨hX', h'⟩
    exact hij h'
  have hunion : (⋃ i, Δ i) = Δ₀ := by
    ext X
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hX, -⟩
      exact hX
    · intro hX
      exact ⟨_, hX, rfl⟩
  have hne : ∀ i, (Δ i).Nonempty := by
    intro i
    obtain ⟨X, hX, hXq⟩ := (e.symm i).2
    refine ⟨X, hX, ?_⟩
    rw [show (⟨Quotient.mk r X, X, hX, rfl⟩ : ↥Q0) = e.symm i from Subtype.ext hXq,
      Equiv.apply_symm_apply]
  have hGinv : ∀ i, ∀ X ∈ Δ i, ∀ g ∈ G0, X.map g.toMonoidHom ∈ Δ i := by
    rintro i X ⟨hX, rfl⟩ g hg
    refine ⟨hinv X hX g (hG0le hg), ?_⟩
    congr 1
    exact Subtype.ext (Quotient.sound (show r.r X (X.map g.toMonoidHom) from ⟨g, hg, rfl⟩)).symm
  have hGtrans : ∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ G0, X.map g.toMonoidHom = Y := by
    rintro i X ⟨hX, hXi⟩ Y ⟨hY, hYi⟩
    exact Quotient.exact (congrArg Subtype.val (e.injective (hXi.trans hYi.symm)))
  have hX00 : X0 ∈ Δ ⟨0, hs⟩ := ⟨hX0Δ, he0⟩
  obtain ⟨⟨-, -, -, hsup, -, hcent, -⟩, ⟨-, hpts, -, -⟩, h8⟩ := hG31 V hV Gm hO2 Δ₀ ⟨X0, hX0Δ⟩
    hcard hinv htrans hrel _ hs Δ hdisj hunion hne hGinv hGtrans
  exact false_of_g31_aux hV hab hb hfix hG0le hX0 hX00 hXbΔ hunion hsup hcent hpts h8
    hGtrans

end CFSG.Quasithin.Vol2.Ch10.SecD
