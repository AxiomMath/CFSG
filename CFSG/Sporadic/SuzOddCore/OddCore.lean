module

public import CFSG.Sporadic.SuzOddCore.OddCoreCheck
public import CFSG.Sporadic.SuzOddCore.OddCoreLines
public import CFSG.Sporadic.SuzOddCore.SylowFusion

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four

theorem factorization_eq_of {n p e m : ℕ} (hp : p.Prime) (hn : n = p ^ e * m) (hm : ¬ p ∣ m) :
    n.factorization p = e := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [hn, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem oddRecord_of_prime {i : ℕ} (hi : i < 4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ invInnerOrders.getD i 0) :
    ∃ r < (invOddCoreShapes.getD i []).length, (oddShape i r).getD 0 0 = p ∧
      (oddShape i r).getD 1 0 = p ^ (invInnerOrders.getD i 0).factorization p := by
  have hn : invInnerOrders.getD i 0 ≠ 0 := by interval_cases i <;> simp [invInnerOrders]
  have hmem := (Nat.mem_primeFactorsList hn).2 ⟨hp, hdvd⟩
  interval_cases i
  · simp only [invInnerOrders, List.getD_cons_zero] at hmem ⊢
    simp only [Nat.primeFactorsList_ofNat, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> first
      | exact absurd rfl hp2
      | refine ⟨0, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_three (show 161280 = 3 ^ 2 * 17920 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨1, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_five (show 161280 = 5 ^ 1 * 32256 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨2, by decide, rfl, ?_⟩
        rw [factorization_eq_of (by norm_num : Nat.Prime 7)
          (show 161280 = 7 ^ 1 * 23040 by norm_num) (by norm_num)]; rfl
  · simp only [invInnerOrders, List.getD_cons_succ, List.getD_cons_zero] at hmem ⊢
    simp only [Nat.primeFactorsList_ofNat, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact absurd rfl hp2
      | refine ⟨0, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_three (show 3317760 = 3 ^ 4 * 40960 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨1, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_five (show 3317760 = 5 ^ 1 * 663552 by norm_num)
          (by norm_num)]; rfl
  · simp only [invInnerOrders, List.getD_cons_succ, List.getD_cons_zero] at hmem ⊢
    simp only [Nat.primeFactorsList_ofNat, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hp2
      | refine ⟨0, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_three (show 190080 = 3 ^ 3 * 7040 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨1, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_five (show 190080 = 5 ^ 1 * 38016 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨2, by decide, rfl, ?_⟩
        rw [factorization_eq_of (by norm_num : Nat.Prime 11)
          (show 190080 = 11 ^ 1 * 17280 by norm_num) (by norm_num)]; rfl
  · simp only [invInnerOrders, List.getD_cons_succ, List.getD_cons_zero] at hmem ⊢
    simp only [Nat.primeFactorsList_ofNat, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> first
      | exact absurd rfl hp2
      | refine ⟨0, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_three (show 1209600 = 3 ^ 3 * 44800 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨1, by decide, rfl, ?_⟩
        rw [factorization_eq_of Nat.prime_five (show 1209600 = 5 ^ 2 * 48384 by norm_num)
          (by norm_num)]; rfl
      | refine ⟨2, by decide, rfl, ?_⟩
        rw [factorization_eq_of (by norm_num : Nat.Prime 7)
          (show 1209600 = 7 ^ 1 * 172800 by norm_num) (by norm_num)]; rfl

theorem oddEntry_check
    {i : ℕ} (hi : i < 4) : oddEntryOK i = true := by
  interval_cases i
  exacts [oddEntry_check0, oddEntry_check1, oddEntry_check2, oddEntry_check3]

theorem oddRecord_facts
    {i r : ℕ} (hi : i < 4) (hr : r < (invOddCoreShapes.getD i []).length) :
    (∀ k < (invOddGenArrs i r).size, permOK 1782 (invOddGenArrs i r)[k]! = true ∧
      inM (invOddGenArrs i r)[k]! = true ∧ commutesA (invOddGenArrs i r)[k]! (tArr i) = true) ∧
    enumOK 1782 (invOddGenArrs i r) (oddEnum i r) = true ∧
    (oddEnum i r).tabs.size = (oddShape i r).getD 1 0 ∧
    (∀ k < (oddEnum i r).tabs.size,
      (!(eqA 1782 (powA 1782 (oddEnum i r).tabs[k]! ((oddShape i r).getD 0 0)) (idA 1782)) ||
        eqA 1782 (oddEnum i r).tabs[k]! (idA 1782) ||
        anyBelow ((oddShape i r).getD 0 0) fun j => anyBelow (invOddLineArrs i r).size fun l =>
          eqA 1782 (powA 1782 (oddEnum i r).tabs[k]! j) (invOddLineArrs i r)[l]!) = true) ∧
    (∀ l < (invOddLineArrs i r).size, oddLineOK i r l = true) := by
  have h := oddEntry_check hi
  rw [oddEntryOK, allBelow_eq_true] at h
  have h' := h r hr
  simp only [oddRecordOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, and_assoc] at h'
  exact h'

theorem rep_invInnerGen
    {i j : ℕ} (hi : i < 4) (hj : j < (invInnerGenArrs i).size) :
    Rep 1782 (invInnerGenArrs i)[j]! (invInnerGen i j) := by
  have hk : invInnerStart i + j < invRunCount i := by
    have : j < invInnerGenCounts.getD i 0 := by simpa [invInnerGenArrs] using hj
    have h2 := invRunCount_ge i
    simp only [invOddStart] at h2
    omega
  have h := invRun_inv hi hk
  rw [← invInnerGenArrs_get hj] at h
  exact (rep_permC h).1

theorem invInnerGen_mem
    {i j : ℕ} (hi : i < 4) (hj : j < (invInnerGenArrs i).size) :
    invInnerGen i j ∈ invE i := by
  have hj' : j < (invInnerChain i).originalCount := hj
  have hrep := (invInnerChain_arrays hi).orig ⟨j, hj'⟩
  rw [(rep_invInnerGen hi hj).unique hrep]
  exact Subgroup.subset_closure (schreier_vector_get_mem_toList _ _)

theorem innerWordArr_cons (i h : ℕ) (w : List ℕ) :
    innerWordArr i (h :: w) = compA 1782 (invInnerGenArrs i)[h - 1]! (innerWordArr i w) := by
  simp only [innerWordArr, List.foldr_cons]

theorem rep_innerWordArr {i : ℕ} (hi : i < 4) : ∀ w : List ℕ,
    (w.all fun h => decide (1 ≤ h ∧ h ≤ (invInnerGenArrs i).size)) = true →
      Rep 1782 (innerWordArr i w) ((w.map fun l => invInnerGen i (l - 1)).prod) ∧
        (w.map fun l => invInnerGen i (l - 1)).prod ∈ invE i
  | [], _ => ⟨by simpa [innerWordArr] using (rep_idA (n := 1782)), (invE i).one_mem⟩
  | h :: w, hw => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨h1, h2⟩ := rep_innerWordArr hi w hw.2
    have hh : h - 1 < (invInnerGenArrs i).size := by omega
    refine ⟨?_, ?_⟩
    · rw [innerWordArr_cons, List.map_cons, List.prod_cons]
      exact rep_compA (rep_invInnerGen hi hh) h1
    · rw [List.map_cons, List.prod_cons]
      exact (invE i).mul_mem (invInnerGen_mem hi hh) h2

@[expose] def oddGens (i r : ℕ) : Set (Equiv.Perm (Fin 1782)) :=
  {g | ∃ k < (invOddGenArrs i r).size, permC 1782 (invOddGenArrs i r)[k]! = g}

@[expose] def oddSylow (i r : ℕ) : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (oddGens i r)

theorem oddSylow_enumerates
    {i r : ℕ} (hi : i < 4) (hr : r < (invOddCoreShapes.getD i []).length) :
    Enumerates (oddSylow i r) (oddEnum i r).tabs.toList := by
  obtain ⟨hg, hE, -⟩ := oddRecord_facts hi hr
  refine enumerates_closure ?_ ?_ hE
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, tabRep_of_permOK (hg k hk).1⟩
  · intro k hk
    exact ⟨_, ⟨k, hk, rfl⟩, tabRep_of_permOK (hg k hk).1⟩

theorem oddSylow_le
    {i r : ℕ} (hi : i < 4) (hr : r < (invOddCoreShapes.getD i []).length) :
    oddSylow i r ≤ invE i := by
  rw [oddSylow, Subgroup.closure_le, invE_eq_centM hi]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨hp, hm, hc⟩ := (oddRecord_facts hi hr).1 k hk
  have hrep := (tabRep_of_permOK hp).2
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 ((commutesA_iff hrep (rep_suzInv hi)).1 hc),
    (inM_iff hrep).1 hm⟩

theorem card_oddSylow
    {i r : ℕ} (hi : i < 4) (hr : r < (invOddCoreShapes.getD i []).length) :
    Nat.card (oddSylow i r) = (oddShape i r).getD 1 0 := by
  rw [(oddSylow_enumerates hi hr).card, Array.length_toList, (oddRecord_facts hi hr).2.2.1]

theorem oddSylow_lines
    {i r : ℕ} (hi : i < 4) (hr : r < (invOddCoreShapes.getD i []).length)
    {y : Equiv.Perm (Fin 1782)} (hy : y ∈ oddSylow i r) (hyp : orderOf y = (oddShape i r).getD 0 0)
    (hp1 : (oddShape i r).getD 0 0 ≠ 1) :
    ∃ x ∈ Subgroup.zpowers y, ∃ g ∈ invE i, ∃ k : ℕ, orderOf ((x * (g * x * g⁻¹)) ^ k) = 2 := by
  obtain ⟨-, -, -, hlines, hl⟩ := oddRecord_facts hi hr
  obtain ⟨t, ht, hrep⟩ := (oddSylow_enumerates hi hr).complete y hy
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  have h := hlines k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', anyBelow_eq_true] at h
  have hrep' : Rep 1782 (oddEnum i r).tabs[k]! y := hrep.2
  have hyp1 : y ^ ((oddShape i r).getD 0 0) = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyp
    exact hp1 hyp.symm
  rcases h with (h | h) | ⟨j, -, l, hl', hjl⟩
  · rw [← Bool.not_eq_true, eqA_iff (rep_powA hrep' _) rep_idA] at h
    exact absurd hyp1 h
  · exact absurd ((eqA_iff hrep' rep_idA).1 h) hy1
  · have hline := hl l hl'
    simp only [oddLineOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hline
    obtain ⟨hx, hw, hinv, hww, hw1⟩ := hline
    have hxrep := (tabRep_of_permOK hx).2
    set x := permC 1782 (invOddLineArrs i r)[l]! with hxdef
    have hxy : x = y ^ j := ((eqA_iff (rep_powA hrep' j) hxrep).1 hjl).symm
    obtain ⟨hgrep, hgmem⟩ := rep_innerWordArr hi _ hw
    set g := ((oddWord i r l).map fun l => invInnerGen i (l - 1)).prod with hgdef
    have hginv := rep_inv_of_isInvA hgrep hinv
    have hrw : Rep 1782 (powA 1782 (xgxgArr (invOddLineArrs i r)[l]!
        (innerWordArr i (oddWord i r l)) (invCand 1782 (innerWordArr i (oddWord i r l))))
        (oddOrder i r l / 2)) ((x * (g * (x * g⁻¹))) ^ (oddOrder i r l / 2)) :=
      rep_powA (rep_compA hxrep (rep_compA hgrep (rep_compA hxrep hginv))) _
    refine ⟨x, Subgroup.mem_zpowers_iff.2 ⟨j, by rw [hxy, zpow_natCast]⟩, g, hgmem,
      oddOrder i r l / 2, ?_⟩
    have e0 : x * (g * x * g⁻¹) = x * (g * (x * g⁻¹)) := by simp only [mul_assoc]
    rw [e0]
    refine orderOf_eq_prime (by rw [pow_two]; exact (eqA_iff (rep_compA hrw hrw) rep_idA).1 hww) ?_
    rw [← Bool.not_eq_true, eqA_iff hrw rep_idA] at hw1
    exact hw1

theorem oddShape_prime_ne_one {i r : ℕ} (hi : i < 4)
    (hr : r < (invOddCoreShapes.getD i []).length) : (oddShape i r).getD 0 0 ≠ 1 := by
  interval_cases i <;> simp [invOddCoreShapes] at hr <;> interval_cases r <;> decide

theorem invE_oddCore
    {i : ℕ} (hi : i < 4) : CFSG.oddCore (invE i) = ⊥ := by
  apply oddCore_eq_bot_of_lines
  intro p hp hp2 hdvd
  rw [card_invE hi] at hdvd ⊢
  obtain ⟨r, hr, hpr, hcard⟩ := oddRecord_of_prime hi hp hp2 hdvd
  refine ⟨oddSylow i r, oddSylow_le hi hr, by rw [card_oddSylow hi hr, hcard], ?_⟩
  intro y hy hyp
  exact oddSylow_lines hi hr hy (by rw [hpr]; exact hyp) (oddShape_prime_ne_one hi hr)

theorem invD_oddCore
    {i : ℕ} (hi : i < 4) : CFSG.oddCore (invD i) = ⊥ :=
  oddCore_eq_bot_of_index_two (invE_le_invD hi) (invE_index hi) (invE_oddCore hi)

theorem map_conj_inf_centralizer {Γ : Subgroup (Equiv.Perm (Fin 1782))}
    {c : Equiv.Perm (Fin 1782)} (hΓ : ∀ g, g ∈ Γ ↔ c * g * c⁻¹ ∈ Γ) (t : Equiv.Perm (Fin 1782)) :
    (Γ ⊓ Subgroup.centralizer {t}).map (MulAut.conj c).toMonoidHom =
      Γ ⊓ Subgroup.centralizer {c * t * c⁻¹} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨g, ⟨hg, hgt⟩, rfl⟩
    refine ⟨(hΓ g).1 hg, ?_⟩
    calc c * g * c⁻¹ * (c * t * c⁻¹) = c * (g * t) * c⁻¹ := by group
      _ = c * (t * g) * c⁻¹ := by rw [hgt]
      _ = c * t * c⁻¹ * (c * g * c⁻¹) := by group
  · rintro ⟨hy, hyt⟩
    refine ⟨c⁻¹ * y * c, ⟨(hΓ _).2 (by rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group]), ?_⟩,
      by group⟩
    calc c⁻¹ * y * c * t = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * t * c⁻¹ * y) * c := by rw [hyt]
      _ = t * (c⁻¹ * y * c) := by group

theorem oddCore_conj {Γ : Subgroup (Equiv.Perm (Fin 1782))} {c t : Equiv.Perm (Fin 1782)}
    (hΓ : ∀ g, g ∈ Γ ↔ c * g * c⁻¹ ∈ Γ) (h : CFSG.oddCore ↥(Γ ⊓ Subgroup.centralizer {t}) = ⊥) :
    CFSG.oddCore ↥(Γ ⊓ Subgroup.centralizer {c * t * c⁻¹}) = ⊥ := by
  rw [← map_conj_inf_centralizer hΓ t]
  exact oddCore_eq_bot_of_mulEquiv' (Subgroup.equivMapOfInjective _ _
    (MulAut.conj c).injective) h

theorem suzM_conj_iff
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) (g : Equiv.Perm (Fin 1782)) :
    g ∈ suzM ↔ c * g * c⁻¹ ∈ suzM := by
  refine ⟨fun h => suzT_conj_mem_suzM hc h, fun h => ?_⟩
  have := suzT_conj_mem_suzM (suzT.inv_mem hc) h
  rwa [show c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g by group] at this

theorem suzT_conj_iff {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) (g : Equiv.Perm (Fin 1782)) :
    g ∈ suzT ↔ c * g * c⁻¹ ∈ suzT := by
  refine ⟨fun h => suzT.mul_mem (suzT.mul_mem hc h) (suzT.inv_mem hc), fun h => ?_⟩
  have := suzT.mul_mem (suzT.mul_mem (suzT.inv_mem hc) h) hc
  rwa [show c⁻¹ * (c * g * c⁻¹) * c = g by group] at this

theorem CTUC_Suz_all_involution_centralizers_odd_core_free :
    ∀ a ∈ suzT, orderOf a = 2 →
      CFSG.oddCore ↥(suzM ⊓ Subgroup.centralizer {a}) = ⊥ ∧
      CFSG.oddCore ↥(suzT ⊓ Subgroup.centralizer {a}) = ⊥ := by
  intro a ha h2
  obtain ⟨i, ⟨hi, c, hc, rfl⟩, -⟩ := suzT_involution_class ha h2
  have hM : CFSG.oddCore ↥(suzM ⊓ Subgroup.centralizer {suzInv i}) = ⊥ := by
    have h := invE_oddCore hi
    rwa [invE_eq_centM hi, centM, inf_comm] at h
  have hT : CFSG.oddCore ↥(suzT ⊓ Subgroup.centralizer {suzInv i}) = ⊥ := by
    have h := invD_oddCore hi
    rwa [invD_eq_centT hi, centT, inf_comm] at h
  exact ⟨oddCore_conj (suzM_conj_iff hc) hM, oddCore_conj (suzT_conj_iff hc) hT⟩

end CFSG.Sporadic.SuzOddCore
