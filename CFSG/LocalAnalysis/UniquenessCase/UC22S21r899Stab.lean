module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r899_map_conj_mem {M L : Subgroup G} {g : G} (hg : g ∈ M) {N : Subgroup G}
    (hN : N ∈ conjSetOf M L) : N.map (MulAut.conj g).toMonoidHom ∈ conjSetOf M L := by
  obtain ⟨h, hh, rfl⟩ := hN
  exact ⟨g * h, M.mul_mem hg hh, uc22p22d_map_conj_map_conj L h g⟩

theorem uc22r899_mem_normalizer_of_fix {M L : Subgroup G} (hc3 : (conjSetOf M L).ncard = 3)
    {g : G} (hg : g ∈ M) {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hgk : g ^ q ^ k = 1)
    (hfix : q = 3 → ∃ N ∈ conjSetOf M L, g ∈ normalizer (N : Set G)) :
    ∀ N ∈ conjSetOf M L, g ∈ normalizer (N : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite ↥(conjSetOf M L) := Set.toFinite _
  letI : Fintype ↥(conjSetOf M L) := Fintype.ofFinite _
  let f : Function.End ↥(conjSetOf M L) := fun N =>
    ⟨(N : Subgroup G).map (MulAut.conj g).toMonoidHom, uc22r899_map_conj_mem hg N.2⟩
  have hfpow : ∀ m : ℕ, ∀ N : ↥(conjSetOf M L),
      ((f ^ m) N : Subgroup G) = (N : Subgroup G).map (MulAut.conj (g ^ m)).toMonoidHom := by
    intro m
    induction m with
    | zero => intro N; rw [pow_zero]; show (N : Subgroup G) = _; ext x; simp
    | succ m ih =>
      intro N
      rw [pow_succ]
      show (((f ^ m) (f N) : ↥(conjSetOf M L)) : Subgroup G) = _
      rw [ih, show ((f N : ↥(conjSetOf M L)) : Subgroup G) =
        (N : Subgroup G).map (MulAut.conj g).toMonoidHom from rfl,
        uc22p22d_map_conj_map_conj, ← pow_succ]
  have hf : f ^ q ^ k = 1 := by
    funext N
    apply Subtype.ext
    rw [hfpow, hgk]
    show _ = (N : Subgroup G)
    ext x
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥(conjSetOf M L)) (p := q) (n := k) hf
  have hcard : Fintype.card ↥(conjSetOf M L) = 3 := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hc3]
  have hfix_iff : ∀ N : ↥(conjSetOf M L), f N = N ↔ g ∈ normalizer ((N : Subgroup G) : Set G) := by
    intro N
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subtype.ext_iff]
    exact Iff.rfl
  have hle : Fintype.card f.fixedPoints ≤ 3 := by
    rw [← hcard]; exact Fintype.card_subtype_le _
  have h3 : Fintype.card f.fixedPoints = 3 := by
    by_cases hq3 : q = 3
    · subst hq3
      obtain ⟨N, hN, hgN⟩ := hfix rfl
      have hpos : 0 < Fintype.card f.fixedPoints :=
        Fintype.card_pos_iff.2 ⟨⟨⟨N, hN⟩, (hfix_iff ⟨N, hN⟩).2 hgN⟩⟩
      unfold Nat.ModEq at hmod
      omega
    · have hq4 : 3 < q := by have := hq.two_le; omega
      unfold Nat.ModEq at hmod
      rw [hcard, Nat.mod_eq_of_lt hq4, Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  intro N hN
  by_contra hNn
  have hlt : Fintype.card f.fixedPoints < Fintype.card ↥(conjSetOf M L) :=
    Fintype.card_subtype_lt (p := fun N' : ↥(conjSetOf M L) => N' ∈ f.fixedPoints)
      (x := ⟨N, hN⟩) (fun h => hNn ((hfix_iff ⟨N, hN⟩).1 h))
  omega

theorem uc22r899_exists_elemAbelian_stab {M L P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hc3 : (conjSetOf M L).ncard = 3) (hPM : P ≤ M) (hPe : IsElemAbelian p P)
    (hPc : Nat.card P = p ^ 4) :
    ∃ A : Subgroup G, A ≤ P ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3 ∧
      ∀ a ∈ A, ∀ N ∈ conjSetOf M L, a ∈ normalizer (N : Set G) := by
  classical
  have hL : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext x; simp⟩
  letI : SMul ↥P (Subgroup G) := ⟨fun a N => N.map (MulAut.conj (a : G)).toMonoidHom⟩
  letI : MulAction ↥P (Subgroup G) :=
    { one_smul := fun N => by
        show N.map (MulAut.conj ((1 : ↥P) : G)).toMonoidHom = N
        ext x
        simp
      mul_smul := fun a b N => by
        show N.map (MulAut.conj ((a * b : ↥P) : G)).toMonoidHom =
          (N.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj (a : G)).toMonoidHom
        rw [uc22p22d_map_conj_map_conj]
        rfl }
  set K := MulAction.stabilizer ↥P L with hKdef
  have hK : ∀ a : ↥P, a ∈ K ↔ (a : G) ∈ normalizer (L : Set G) := fun a => by
    rw [hKdef, MulAction.mem_stabilizer_iff, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have hidx : K.index ≤ 3 := by
    rw [hKdef, MulAction.index_stabilizer, ← hc3]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro N ⟨a, rfl⟩
    exact ⟨(a : G), hPM a.2, rfl⟩
  have hmul : K.index * Nat.card K = p ^ 4 := by
    rw [← hPc]
    exact Subgroup.index_mul_card K
  set A₁ : Subgroup G := K.map P.subtype with hA₁
  have hA₁P : A₁ ≤ P := Subgroup.map_subtype_le _
  have hA₁c : Nat.card A₁ = Nat.card K := Subgroup.card_map_of_injective P.subtype_injective
  have hA₁el : IsElemAbelian p A₁ := hPe.mono hA₁P
  obtain ⟨j, hj4, hj⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ hmul)
  have hj3 : 3 ≤ j := by
    by_contra h
    have hj2 : p ^ j ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hp9 : 9 ≤ p ^ 2 := by nlinarith
    have h1 : K.index * p ^ j ≤ 3 * p ^ 2 := Nat.mul_le_mul hidx hj2
    rw [hj] at hmul
    have h2 : p ^ 4 = p ^ 2 * p ^ 2 := by ring
    nlinarith [pow_pos hp.pos 2]
  have hA₁N : ∀ a ∈ A₁, ∀ N ∈ conjSetOf M L, a ∈ normalizer (N : Set G) := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    have hpow : (a' : G) ^ p ^ 1 = 1 := by rw [pow_one]; exact hPe.2 _ a'.2
    exact uc22r899_mem_normalizer_of_fix hc3 (hPM a'.2) hp hp2 hpow
      (fun _ => ⟨L, hL, (hK a').1 ha'⟩)
  have hrank : 3 ≤ CFSG.Open.pRank p A₁ :=
    hj3.trans (UC6S846.le_pRank' hp le_rfl hA₁el
      (hA₁c.trans hj))
  obtain ⟨A, hAA₁, hAel, hAc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp hrank
  exact ⟨A, hAA₁.trans hA₁P, hAel, hAc, fun a ha => hA₁N a (hAA₁ ha)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
