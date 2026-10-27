module

public import CFSG.Sporadic.Co2Schreier.ThreeBasic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Lang.E6Descent.SylowNormal
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Open

theorem exists_conj_le_locP0
    {F : Subgroup (Equiv.Perm (Fin 2300))} (hFC : F ≤ locC)
    (hF : IsPGroup 3 F) :
    ∃ c ∈ locC, F.map (MulAut.conj c).toMonoidHom ≤ locP0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card locC).factorization 3 = 4 := by
    rw [card_locC, show (743178240 : ℕ) = 3 ^ 4 * 9175040 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (p := 3) (by norm_num : ¬ 3 ∣ 9175040)]
  have hPcard : Nat.card (locP0.subgroupOf locC) =
      3 ^ (Nat.card locC).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe locP0_le_C).toEquiv, card_locP0, hfac]
    norm_num
  let P : Sylow 3 ↥locC := Sylow.ofCard (locP0.subgroupOf locC) hPcard
  have hFsub : IsPGroup 3 (F.subgroupOf locC) :=
    hF.of_equiv (Subgroup.subgroupOfEquivOfLe hFC).symm
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_mem_sylow P hFsub
  refine ⟨(g : Equiv.Perm (Fin 2300)), g.2, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hmem := hg (⟨x, hFC hx⟩ : ↥locC) hx
  have hmem' : (↑(g * (⟨x, hFC hx⟩ : ↥locC) * g⁻¹) : Equiv.Perm (Fin 2300)) ∈ locP0 :=
    hmem
  simpa [MulAut.conj_apply] using hmem'

theorem eltE_four_pow_three_ne_one :
    eltE enumP0 4 ^ 3 ≠ 1 := by
  intro h
  have hrep : Rep 2300 enumP0.elems[4]! (eltE enumP0 4) :=
    enumP0_facts.rep (k := 4) (by norm_num)
  have hcomp : Rep 2300
      (compA 2300 enumP0.elems[4]! (compA 2300 enumP0.elems[4]! enumP0.elems[4]!))
      (eltE enumP0 4 * (eltE enumP0 4 * eltE enumP0 4)) :=
    rep_compA hrep (rep_compA hrep hrep)
  have htrue : eqA 2300
      (compA 2300 enumP0.elems[4]! (compA 2300 enumP0.elems[4]! enumP0.elems[4]!))
      (idA 2300) = true := by
    rw [eqA_iff hcomp rep_idA]
    rw [pow_three] at h
    exact h
  have hfalse := p0Cube_check
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

theorem card_le_of_isElemAbelian_locC
    {F : Subgroup (Equiv.Perm (Fin 2300))} (hFC : F ≤ locC)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 ^ 3 := by
  have hFp : IsPGroup 3 F := hF.isPGroup
  obtain ⟨n, hn⟩ := hFp.exists_card_eq
  have hn_le : n ≤ 4 := by
    have hdvd0 : 3 ^ n ∣ Nat.card locC := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le hFC
    rw [card_locC, show (743178240 : ℕ) = 3 ^ 4 * 9175040 by norm_num] at hdvd0
    have hcop : Nat.Coprime (3 ^ n) 9175040 :=
      (Nat.prime_three.coprime_pow_of_not_dvd (a := 9175040) (m := n)
        (by norm_num)).symm
    have hdvd : 3 ^ n ∣ 3 ^ 4 :=
      (Nat.Coprime.dvd_mul_right (m := 3 ^ 4) hcop).mp hdvd0
    obtain ⟨k, hk4, hkn⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have : n = k := Nat.pow_right_injective (show 2 ≤ 3 by norm_num) hkn
    omega
  by_cases hn4 : n = 4
  · exfalso
    have hcardF : Nat.card F = 81 := by rw [hn, hn4]; norm_num
    obtain ⟨c, hc, hle⟩ := exists_conj_le_locP0 hFC hFp
    have hmapcard : Nat.card (F.map (MulAut.conj c).toMonoidHom) = 81 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcardF]
    have heq : F.map (MulAut.conj c).toMonoidHom = locP0 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hmapcard, card_locP0])
    have hmem4 : eltE enumP0 4 ∈ F.map (MulAut.conj c).toMonoidHom := by
      rw [heq]
      exact eltE_mem_locP0 (by norm_num)
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 hmem4
    have hx3 : x ^ 3 = 1 := hF.2 x hx
    apply eltE_four_pow_three_ne_one
    rw [← hxeq, ← map_pow (MulAut.conj c).toMonoidHom x 3, hx3, map_one]
  · have hn3 : n ≤ 3 := by omega
    calc Nat.card F = 3 ^ n := hn
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3

theorem eltE_mem_of_le_locP0
    {F : Subgroup (Equiv.Perm (Fin 2300))} (hFP : F ≤ locP0)
    (hF : IsMulCommutative F) (h27 : Nat.card F = 27) {m : ℕ} (hm : m ∈ p0MarkedIdx) :
    eltE enumP0 m ∈ F := by
  classical
  let T : Finset ℕ := (Finset.range 81).filter fun k => eltE enumP0 k ∈ F
  have hT1 : T.card ≤ Nat.card F := by
    rw [← Fintype.card_coe T, Nat.card_eq_fintype_card (α := F)]
    refine Fintype.card_le_of_injective
      (fun k : T => (⟨eltE enumP0 k.1, (Finset.mem_filter.1 k.2).2⟩ : F)) ?_
    intro k l hkl
    have hval : eltE enumP0 k.1 = eltE enumP0 l.1 := congrArg Subtype.val hkl
    exact Subtype.ext (enumP0_facts.elt_inj
      (Finset.mem_range.1 (Finset.mem_filter.1 k.2).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 l.2).1) hval)
  have hT2 : Nat.card F ≤ T.card := by
    let ind : F → ℕ := fun x => Classical.choose (exists_eltE_of_mem_locP0 (hFP x.2))
    have hind_lt : ∀ x : F, ind x < 81 := fun x =>
      (Classical.choose_spec (exists_eltE_of_mem_locP0 (hFP x.2))).1
    have hind : ∀ x : F, eltE enumP0 (ind x) = x := fun x =>
      (Classical.choose_spec (exists_eltE_of_mem_locP0 (hFP x.2))).2
    let idx : F → T := fun x =>
      ⟨ind x, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.2 (hind_lt x), by rw [hind x]; exact x.2⟩⟩
    have hidx : ∀ x : F, eltE enumP0 (idx x).1 = x := fun x => hind x
    rw [← Fintype.card_coe T, Nat.card_eq_fintype_card (α := F)]
    refine Fintype.card_le_of_injective idx ?_
    intro x y hxy
    exact Subtype.ext (by rw [← hidx x, ← hidx y, congrArg Subtype.val hxy])
  have hTcard : T.card = 27 := by omega
  have hcent : ∀ k ∈ T, 27 ≤ (p0CentIdx k).length := by
    intro k hk
    have hsub : T ⊆ (p0CentIdx k).toFinset := by
      intro j hj
      rw [List.mem_toFinset, p0CentIdx, List.mem_filter]
      refine ⟨List.mem_range.2 (Finset.mem_range.1 (Finset.mem_filter.1 hj).1), ?_⟩
      have hjF : eltE enumP0 j ∈ F := (Finset.mem_filter.1 hj).2
      have hkF : eltE enumP0 k ∈ F := (Finset.mem_filter.1 hk).2
      have hcomm : eltE enumP0 j * eltE enumP0 k = eltE enumP0 k * eltE enumP0 j := by
        letI := hF
        exact congrArg Subtype.val (mul_comm' (⟨eltE enumP0 j, hjF⟩ : F)
          ⟨eltE enumP0 k, hkF⟩)
      exact (commA_iff (enumP0_facts.rep (Finset.mem_range.1
        (Finset.mem_filter.1 hj).1)) (enumP0_facts.rep (Finset.mem_range.1
        (Finset.mem_filter.1 hk).1))).2 hcomm
    have hle := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup (by
      rw [p0CentIdx]
      exact (List.nodup_range).filter _)] at hle
    omega
  have hTM : T ⊆ p0MarkedIdx.toFinset := by
    intro k hk
    rw [List.mem_toFinset, p0MarkedIdx, List.mem_filter]
    refine ⟨List.mem_range.2 (Finset.mem_range.1 (Finset.mem_filter.1 hk).1), ?_⟩
    simpa using hcent k hk
  have hnd : p0MarkedIdx.Nodup := by
    rw [p0MarkedIdx]
    exact (List.nodup_range).filter _
  have hlenM : p0MarkedIdx.length = 27 := by
    rw [p0Marked_check]
    decide
  have hMcard : p0MarkedIdx.toFinset.card = 27 := by
    rw [List.toFinset_card_of_nodup hnd, hlenM]
  have hTeq : T = p0MarkedIdx.toFinset :=
    Finset.eq_of_subset_of_card_le hTM (by rw [hMcard, hTcard])
  have hmM : m ∈ p0MarkedIdx.toFinset := by
    rw [List.mem_toFinset]
    exact hm
  rw [← hTeq] at hmM
  exact (Finset.mem_filter.1 hmM).2

end CFSG.Sporadic.Co2Schreier
