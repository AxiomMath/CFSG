module

public import CFSG.Sporadic.Schreier.TitsEnum
public import CFSG.Sporadic.Schreier.TitsBasic

public section

namespace CFSG.Quasithin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier.Tits

variable {n : ℕ}

theorem prod_ofFn_four {M : Type*} [Monoid M] {k : ℕ} (hk : k = 4) (f : Fin k → M) :
    (List.ofFn f).prod = f ⟨0, by omega⟩ * f ⟨1, by omega⟩ * f ⟨2, by omega⟩ * f ⟨3, by omega⟩ := by
  subst hk
  simp [List.ofFn_succ, mul_assoc]

@[expose] def table4 (n : ℕ) (L : Array Level) : Array (Array ℕ) :=
  ((List.range L[0]!.pts.size).flatMap fun a => (List.range L[1]!.pts.size).flatMap fun b =>
    (List.range L[2]!.pts.size).flatMap fun c => (List.range L[3]!.pts.size).map fun d =>
      compA n (compA n (compA n L[0]!.tr[a]! L[1]!.tr[b]!) L[2]!.tr[c]!) L[3]!.tr[d]!).toArray

theorem table4_spec {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) (h4 : Q.baseCount = 4) :
    (∀ i < (table4 n (rawLevels n S base)).size,
      ∃ g ∈ Q.originalSubgroup, Rep n (table4 n (rawLevels n S base))[i]! g) ∧
    (∀ g ∈ Q.originalSubgroup,
      ∃ i < (table4 n (rawLevels n S base)).size, Rep n (table4 n (rawLevels n S base))[i]! g) := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  have hmem : ∀ {i k : ℕ} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size),
      levT n S base i k ∈ Q.originalSubgroup := fun {i k} hi hk => by
    rw [← Q.levelSubgroup_zero_eq_original hQ]
    exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) (hA.levT_mem hF hi hk)
  have hTl : (table4 n (rawLevels n S base)).toList =
      (List.range (rawLevels n S base)[0]!.pts.size).flatMap fun a =>
        (List.range (rawLevels n S base)[1]!.pts.size).flatMap fun b =>
        (List.range (rawLevels n S base)[2]!.pts.size).flatMap fun c =>
        (List.range (rawLevels n S base)[3]!.pts.size).map fun d =>
        compA n (compA n (compA n (rawLevels n S base)[0]!.tr[a]! (rawLevels n S base)[1]!.tr[b]!)
          (rawLevels n S base)[2]!.tr[c]!) (rawLevels n S base)[3]!.tr[d]! := by
    rw [table4, List.toList_toArray]
  constructor
  · intro i hi
    have hmemi : (table4 n (rawLevels n S base))[i]! ∈ (table4 n (rawLevels n S base)).toList := by
      rw [getElem!_pos _ i hi]
      exact Array.getElem_mem_toList _
    rw [hTl] at hmemi
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hmemi
    obtain ⟨a, ha, b, hb, c, hc', d, hd, he⟩ := hmemi
    have ra := hA.rep_levT hF (by omega : 0 < Q.baseCount) ha
    have rb := hA.rep_levT hF (by omega : 1 < Q.baseCount) hb
    have rc := hA.rep_levT hF (by omega : 2 < Q.baseCount) hc'
    have rd := hA.rep_levT hF (by omega : 3 < Q.baseCount) hd
    refine ⟨levT n S base 0 a * levT n S base 1 b * levT n S base 2 c * levT n S base 3 d,
      Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem
        (hmem (by omega) ha) (hmem (by omega) hb)) (hmem (by omega) hc')) (hmem (by omega) hd), ?_⟩
    rw [← he]
    exact rep_compA (rep_compA (rep_compA ra rb) rc) rd
  · intro g hg
    obtain ⟨c, hc', hprod⟩ := exists_levT_prod hA hc h hg
    rw [prod_ofFn_four h4] at hprod
    have ha := hc' ⟨0, by omega⟩
    have hb := hc' ⟨1, by omega⟩
    have hc2 := hc' ⟨2, by omega⟩
    have hd := hc' ⟨3, by omega⟩
    have ra := hA.rep_levT hF (by omega : 0 < Q.baseCount) ha
    have rb := hA.rep_levT hF (by omega : 1 < Q.baseCount) hb
    have rc := hA.rep_levT hF (by omega : 2 < Q.baseCount) hc2
    have rd := hA.rep_levT hF (by omega : 3 < Q.baseCount) hd
    have hmemT : (compA n (compA n (compA n (rawLevels n S base)[0]!.tr[c ⟨0, by omega⟩]!
        (rawLevels n S base)[1]!.tr[c ⟨1, by omega⟩]!) (rawLevels n S base)[2]!.tr[c ⟨2, by omega⟩]!)
        (rawLevels n S base)[3]!.tr[c ⟨3, by omega⟩]!) ∈
        (table4 n (rawLevels n S base)).toList := by
      rw [hTl]
      simp only [List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨_, ha, _, hb, _, hc2, _, hd, rfl⟩
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hmemT
    refine ⟨i, by simpa using hi, ?_⟩
    rw [getElem!_pos _ i (by simpa using hi)]
    have : (table4 n (rawLevels n S base))[i] =
        (table4 n (rawLevels n S base)).toList[i] := by simp
    rw [this, hie, ← hprod]
    exact rep_compA (rep_compA (rep_compA ra rb) rc) rd

theorem eq_one_of_fix_base {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) (hfix : ∀ b ∈ Q.base.toList, g b = b) :
    g = 1 := by
  have hmem : g ∈ Q.levelSubgroup Q.baseCount := by
    rw [Q.mem_levelSubgroup_iff hQ Q.baseCount le_rfl]
    refine ⟨hg, fun b hb => hfix b ?_⟩
    rwa [List.take_of_length_le (by simp)] at hb
  rw [Q.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact hmem

theorem eq_of_agree_base {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {g h : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) (hh : h ∈ Q.originalSubgroup)
    (hbase : ∀ b ∈ Q.base.toList, g b = h b) : g = h := by
  have := eq_one_of_fix_base hQ (Q.originalSubgroup.mul_mem (Q.originalSubgroup.inv_mem hh) hg)
    (fun b hb => by rw [Equiv.Perm.mul_apply, hbase b hb]; exact perm_inv_apply h b)
  exact (inv_mul_eq_one.1 this).symm

end CFSG.Quasithin
