module

public import CFSG.Quasithin.EmptyFaithful.ModHJ4Def
public import CFSG.Quasithin.EmptyFaithful.ModHCfg2
public import CFSG.Quasithin.EmptyFaithful.ModHSolv

public section

namespace CFSG.Quasithin.ModH.J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem map_conj_eq_of_mem_normalizer {Q : Type} [Group Q] {N : Subgroup Q} {q : Q}
    (hq : q ∈ Subgroup.normalizer (N : Set Q)) : N.map (MulAut.conj q).toMonoidHom = N := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hq y).1 hy
  · intro hx
    refine ⟨q⁻¹ * x * q, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.1 hq (q⁻¹ * x * q)).2 (by simpa [mul_assoc] using hx)
    exact this

theorem false_of_config2_inner {Q : Type} [Group Q] [Finite Q] (hF : FactJ4TwoLocals2)
    (e : Nonempty (Q ≃* NativeSporadic.Carrier .J4)) (hsimple : IsSimpleGroup Q)
    {A : Set (MulAut Q)} {Sb Yb : Subgroup Q} (c : Config2 Q A Sb Yb)
    (hA : ∀ α ∈ A, ∃ q ∈ Sb, α = MulAut.conj q)
    (h1 : ∀ Z : Subgroup Q, Group.IsSolvable ↥Z → Sb ≤ Z →
      ∃ N : Subgroup Q, IsPGroup 2 ↥N ∧ N ≠ ⊥ ∧ Z ≤ Subgroup.normalizer (N : Set Q)) : False := by
  have h2 := hF Q e Sb c.sylow
  set Z : Subgroup Q := Yb ⊔ Sb with hZdef
  have hSZ : Sb ≤ Z := le_sup_right
  have hYZ : Yb ≤ Z := le_sup_left
  have hZs : Group.IsSolvable ↥Z := isSolvable_sup_of_le_normalizer c.solvable c.sylow.2.1 c.normalizes
  obtain ⟨N0, hN0p, hN0, hZN0⟩ := h1 Z hZs hSZ
  have hN0top : Subgroup.normalizer (N0 : Set Q) ≠ ⊤ := by
    intro htop
    have hnorm : N0.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases hsimple.eq_bot_or_eq_top_of_normal N0 with h | h
    · exact hN0 h
    · apply c.nonsolvable
      have hp : IsPGroup 2 Q := by
        have := hN0p
        rw [h] at this
        exact this.of_equiv Subgroup.topEquiv
      have : Group.IsNilpotent Q := hp.isNilpotent
      infer_instance
  have hloc0 : IsTwoLocalSub (Subgroup.normalizer (N0 : Set Q)) := ⟨hN0top, N0, hN0p, hN0, rfl⟩
  obtain ⟨M, ⟨hMloc, hZM⟩, hMmax⟩ : ∃ M ∈ {M : Subgroup Q | IsTwoLocalSub M ∧ Z ≤ M},
      ∀ M' ∈ {M : Subgroup Q | IsTwoLocalSub M ∧ Z ≤ M}, Nat.card ↥M' ≤ Nat.card ↥M :=
    Set.exists_max_image {M : Subgroup Q | IsTwoLocalSub M ∧ Z ≤ M} (fun M => Nat.card ↥M)
      (Set.toFinite _) ⟨_, hloc0, hZN0⟩
  have hmaxloc : IsMaxTwoLocal M := by
    refine ⟨hMloc, fun M' hM' hMM' => ?_⟩
    have hle := hMmax M' ⟨hM', hZM.trans hMM'⟩
    exact (Subgroup.eq_of_le_of_card_ge hMM' hle).symm
  obtain ⟨hMtop, N, hNp, hN1, hNM⟩ := hMloc
  have hZN : Yb ⊔ Sb ≤ Subgroup.normalizer (N : Set Q) := by rw [hNM]; exact hZM
  have hinv : ∀ α ∈ A, N.map α.toMonoidHom = N := by
    intro α hα
    obtain ⟨q, hq, rfl⟩ := hA α hα
    exact map_conj_eq_of_mem_normalizer (hZN (hSZ hq))
  have hMY : Subgroup.normalizer (N : Set Q) ≤ Subgroup.normalizer (Yb : Set Q) :=
    c.maximal N hNp hN1 hZN hinv (by rw [hNM]; exact hMtop)
  rw [hNM] at hMY
  exact h2 M hmaxloc (hSZ.trans hZM) Yb hMY (hYZ.trans hZM) c.solvable c.nine

end CFSG.Quasithin.ModH.J4
