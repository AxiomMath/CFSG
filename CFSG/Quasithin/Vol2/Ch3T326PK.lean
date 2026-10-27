module

public import CFSG.Quasithin.Vol2.Ch3T326PE

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

namespace O2Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (h : O2Sit M Mp T L V t)
include h

theorem exists_odd_ne_one :
    ∃ c ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)), c ≠ 1 ∧ Odd (orderOf c) := by
  have hM := h.hB.hD.hyp.Mp_normal
  let _i := qAct hM
  obtain ⟨y, hyM, hyL, hy5, hymove⟩ := h.side.five
  obtain ⟨a, m, hm5, hym⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 5
    (by norm_num)
  set y' := y ^ m with hy'
  have hy'M : y' ∈ M := M.pow_mem hyM m
  have hy'n : y' ^ 5 ^ a = 1 := by
    rw [hy', ← pow_mul, mul_comm, ← hym, pow_orderOf_eq_one]
  have hy'L : ∀ l ∈ L, y' * l = l * y' := fun l hl => (Commute.pow_left (hyL l hl) m)
  have h5j : ∀ q ∈ tilde Mp ⊤ (commV L), ∀ j : ℕ, (⟨y, hyM⟩ : ↥M) ^ (5 * j) • q = q := by
    intro q hq j
    induction j with
    | zero => rw [mul_zero, pow_zero, one_smul]
    | succ j ih => rw [mul_add, mul_one, pow_add, mul_smul, hy5 q hq, ih]
  have hy'move : ∃ q ∈ tilde Mp ⊤ (commV L), (⟨y', hy'M⟩ : ↥M) • q ≠ q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hq, hqy⟩ := hymove
    apply hqy
    have hcop : Nat.Coprime m 5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm5 |>.symm
    obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
    have hme : (⟨y, hyM⟩ : ↥M) ^ (m * e) • q = q := by
      have key : ∀ i : ℕ, (⟨y', hy'M⟩ : ↥M) ^ i • q = q := fun i => by
        induction i with
        | zero => rw [pow_zero, one_smul]
        | succ i ih => rw [pow_succ, mul_smul, hcon q hq, ih]
      have h1 : (⟨y, hyM⟩ : ↥M) ^ (m * e) = (⟨y', hy'M⟩ : ↥M) ^ e :=
        Subtype.ext (by simp [hy', pow_mul])
      rw [h1, key]
    have hsplit : m * e = 5 * (m * e / 5) + 1 := by
      have := Nat.div_add_mod (m * e) 5
      omega
    have hyq : (⟨y, hyM⟩ : ↥M) • q ∈ tilde Mp ⊤ (commV L) := by
      obtain ⟨u, hu, rfl⟩ := hq
      exact ⟨_, B15P4.map_commV_mem (mem_normalizer_of_comm hyL) u hu, rfl⟩
    rw [hsplit, pow_succ, mul_smul, h5j _ hyq] at hme
    exact hme
  have hy'N : y' ∈ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    mem_normalizer_iff_conjAutSub.2
      (h.hB.conj_Lt_of_mem_normalizer hy'M (mem_normalizer_of_comm hy'L))
  have houtt := out_two_of_cases (Or.inl (isPSL32_conjAutSub t h.hL3) :
      IsPSL 3 2 1 ↥(conjAutSub t L) ∨ Nonempty (↥(conjAutSub t L) ≃* alternatingGroup (Fin 5)))
    (G := Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)))
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 hg l).1 hl)
  obtain ⟨l, hl, hconj⟩ := inner_of_odd_of_out_two houtt hy'N (Odd.pow (by decide)) hy'n
  set c := l⁻¹ * y' with hc
  have hcLt : ∀ x ∈ conjAutSub t L, c * x = x * c := by
    intro x hx
    have h1 := hconj x hx
    calc c * x = l⁻¹ * (y' * x * y'⁻¹) * y' := by rw [hc]; group
      _ = l⁻¹ * (l * x * l⁻¹) * y' := by rw [h1]
      _ = x * c := by rw [hc]; group
  have hcL : ∀ x ∈ L, c * x = x * c := by
    intro x hx
    have h1 := hy'L x hx
    have h2 : l⁻¹ * x = x * l⁻¹ := by
      have h3 : x * l = l * x := h.hB.comm x hx l hl
      calc l⁻¹ * x = l⁻¹ * (x * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * x) * l⁻¹ := by rw [h3]
        _ = x * l⁻¹ := by group
    calc c * x = l⁻¹ * (y' * x) := by rw [hc]; group
      _ = l⁻¹ * (x * y') := by rw [h1]
      _ = (l⁻¹ * x) * y' := by group
      _ = x * c := by rw [h2, hc]; group
  have hcM : c ∈ M := M.mul_mem (M.inv_mem (h.hB.Lt_le hl)) hy'M
  have hcC : c ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
    refine ⟨hcM, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := h.hB.exists_mul_of_mem_Mp hx
    rw [mul_assoc, ← hcLt v hv, ← mul_assoc, ← hcL u hu, mul_assoc]
  refine ⟨c, hcC, ?_, ?_⟩
  ·
    intro hc1
    obtain ⟨q, hq, hqy⟩ := hy'move
    apply hqy
    obtain ⟨u, hu, rfl⟩ := hq
    have hlu : l u = u := (mem_fixV.1 (h.hB.commV_le_fixV h.hVt hu)) l hl
    have hy'l : y' = l * c := by rw [hc]; group
    show (QuotientGroup.mk (y' u) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk u
    rw [hy'l, hc1, mul_one, hlu]
  · have hcomm : Commute l c := (hcLt l hl).symm
    have hy'lc : y' = l * c := by rw [hc]; group
    have hck : c ^ 5 ^ a = 1 := by
      have h1 : l ^ 5 ^ a * c ^ 5 ^ a = 1 := by rw [← hcomm.mul_pow, ← hy'lc, hy'n]
      have hmemLt : c ^ 5 ^ a ∈ conjAutSub t L := by
        rw [eq_inv_of_mul_eq_one_right h1]
        exact (conjAutSub t L).inv_mem ((conjAutSub t L).pow_mem hl _)
      have hmem : c ^ 5 ^ a ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ⊓ Mp :=
        ⟨(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).pow_mem hcC _, h.hB.Lt_le_Mp hmemLt⟩
      rw [h.hB.cent_inf_Mp] at hmem
      exact Subgroup.mem_bot.1 hmem
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hck)

end O2Sit

end CFSG.Quasithin.H13.T326
