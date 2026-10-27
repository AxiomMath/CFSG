module

public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.Sec66K1Plane
public import CFSG.RankThree.PartOne.S11c.Sec66Degen

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut proj_surjective)
open CFSG.RankThree.CASymplecticSubfield (subfieldFixedGroup)
open CFSG.LieType.BorelTits (natRep natRep_injective exists_fixed_ne_zero)

section Cyclic5

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {H : Type} [Group H]
  (ρ : H →* Module.End K V)

theorem cyc5_mem_ker_sub_one_iff (g : H) (v : V) :
    v ∈ LinearMap.ker (ρ g - 1) ↔ ρ g v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

theorem cyc5_card_modEq [Finite V] {g : H} (hg : g ^ 5 = 1) (F : Submodule K V)
    (hF : ∀ v ∈ F, ρ g v ∈ F) :
    Nat.card F ≡ Nat.card ↥(F ⊓ LinearMap.ker (ρ g - 1)) [MOD 5] := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let G : Subgroup H := Subgroup.zpowers g
  have hG : IsPGroup 5 G := by
    have hord : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one hg
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  let _ : MulAction G V := MulAction.compHom V (ρ.comp G.subtype)
  have hsmul : ∀ (x : G) (v : V), x • v = ρ x v := fun _ _ => rfl
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hg⟩
  have hpow : ∀ m : ℕ, ∀ v ∈ F, ρ (g ^ m) v ∈ F := by
    intro m
    induction m with
    | zero => intro v hv; simpa using hv
    | succ m ih =>
      intro v hv
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact ih _ (hF v hv)
  have hmem : ∀ x : G, ∃ m : ℕ, g ^ m = (x : H) := fun x =>
    Submonoid.mem_powers_iff _ _ |>.mp ((hfin.mem_powers_iff_mem_zpowers).mpr x.2)
  let Fs : SubMulAction G V :=
    { carrier := (F : Set V)
      smul_mem' := fun x v hv => by
        obtain ⟨m, hm⟩ := hmem x
        rw [hsmul, ← hm]
        exact hpow m v hv }
  have hmod := hG.card_modEq_card_fixedPoints Fs
  have hfix : Nat.card (MulAction.fixedPoints G Fs) =
      Nat.card ↥(F ⊓ LinearMap.ker (ρ g - 1)) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y.1 : V), y.1.2, by
          have h := y.2 ⟨g, Subgroup.mem_zpowers g⟩
          have h2 := congrArg Subtype.val h
          exact (cyc5_mem_ker_sub_one_iff ρ g _).mpr h2⟩
        invFun := fun w => ⟨⟨(w : V), w.2.1⟩, fun x => by
          obtain ⟨m, hm⟩ := hmem x
          apply Subtype.ext
          change ρ x (w : V) = (w : V)
          rw [← hm]
          have hw : ρ g (w : V) = (w : V) := (cyc5_mem_ker_sub_one_iff ρ g _).mp w.2.2
          have : ∀ n : ℕ, ρ (g ^ n) (w : V) = (w : V) := by
            intro n
            induction n with
            | zero => simp
            | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hw, ih]
          exact this m⟩
        left_inv := fun y => rfl
        right_inv := fun w => rfl }
  rw [hfix] at hmod
  exact hmod

theorem cyc5_eq_bot_or_eq_top [Finite V] (hK : Nat.card K = 32) (hV : Module.finrank K V = 4)
    {g : H} (hg : g ^ 5 = 1) (hg1 : ρ g ≠ 1) (F : Submodule K V) (hF : ∀ v ∈ F, ρ g v ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  have hfinV : Module.Finite K V := by
    by_contra h
    rw [Module.finrank_of_not_finite h] at hV
    omega
  have hcard : ∀ W : Submodule K V, Nat.card W = 32 ^ Module.finrank K W := fun W => by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := W), hK]
  have harith : ∀ d, d ≤ 4 → ∀ e, e ≤ 4 → 32 ^ d ≡ 32 ^ e [MOD 5] →
      d = e ∨ (d = 0 ∧ e = 4) ∨ (d = 4 ∧ e = 0) := by decide
  have hle : ∀ W : Submodule K V, Module.finrank K W ≤ 4 := fun W => by
    rw [← hV]
    exact Submodule.finrank_le W
  have hker : LinearMap.ker (ρ g - 1) = ⊥ := by
    have h1 := cyc5_card_modEq ρ hg ⊤ (fun v _ => Submodule.mem_top)
    rw [top_inf_eq, hcard, hcard, finrank_top, hV] at h1
    rcases harith _ (le_refl _) _ (hle _) h1 with h | h | h
    · exfalso
      apply hg1
      have htop : LinearMap.ker (ρ g - 1) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [← h, hV])
      refine LinearMap.ext fun v => ?_
      exact (cyc5_mem_ker_sub_one_iff ρ g v).mp (by rw [htop]; exact Submodule.mem_top)
    · exfalso
      omega
    · exact Submodule.finrank_eq_zero.mp h.2
  have h2 := cyc5_card_modEq ρ hg F hF
  rw [hker, inf_bot_eq, hcard, hcard, finrank_bot] at h2
  rcases harith _ (hle _) _ (by omega) h2 with h | h | h
  · left
    exact Submodule.finrank_eq_zero.mp h
  · left
    exact Submodule.finrank_eq_zero.mp h.1
  · right
    exact Submodule.eq_top_of_finrank_eq (by rw [h.1, hV])

theorem cyc5_false_of_commuting_two_group [Finite V] [CharP K 2] (hK : Nat.card K = 32)
    (hV : Module.finrank K V = 4) (hρ : Function.Injective ρ) {R : Subgroup H}
    (hR : IsPGroup 2 ↥R) (hRne : R ≠ ⊥) {g : H} (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1)
    (hcomm : ∀ r ∈ R, g * r = r * g) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := K) (show 0 < Module.finrank K V by omega)
  obtain ⟨v, hv0, hvfix⟩ := exists_fixed_ne_zero ρ 2 R hR
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  have hρg : ρ g ≠ 1 := fun h => hg1 (hρ (by rw [h, map_one]))
  have hF : ∀ w ∈ LinearMap.ker (ρ (s : H) - 1), ρ g w ∈ LinearMap.ker (ρ (s : H) - 1) := by
    intro w hw
    rw [cyc5_mem_ker_sub_one_iff] at hw ⊢
    have hc : ρ (s : H) * ρ g = ρ g * ρ (s : H) := by
      rw [← map_mul, ← map_mul, (hcomm s s.2).symm]
    calc ρ (s : H) (ρ g w) = (ρ (s : H) * ρ g) w := rfl
      _ = (ρ g * ρ (s : H)) w := by rw [hc]
      _ = ρ g w := by rw [Module.End.mul_apply, hw]
  rcases cyc5_eq_bot_or_eq_top ρ hK hV hg5 hρg _ hF with h | h
  · apply hv0
    have hv : v ∈ LinearMap.ker (ρ (s : H) - 1) :=
      (cyc5_mem_ker_sub_one_iff ρ _ v).mpr (hvfix s s.2)
    rw [h] at hv
    exact (Submodule.mem_bot K).mp hv
  · apply hs1
    apply Subtype.ext
    apply hρ
    refine LinearMap.ext fun w => ?_
    rw [Subgroup.coe_one, map_one]
    exact (cyc5_mem_ker_sub_one_iff ρ _ w).mp (by rw [h]; exact Submodule.mem_top)

end Cyclic5

theorem false_of_isElementaryAbelian_card_sixteen_perm_six (R : Subgroup (Equiv.Perm (Fin 6)))
    (hR : IsElementaryAbelian 2 ↥R) (hcard : Nat.card R = 16) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 R := IsElementaryAbelian.isPGroup 2 R
  set x : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 with hx
  have hx2 : x ^ 2 ≠ 1 := by decide
  have hx4 : x ^ 4 = 1 := by decide
  have hord : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) hx2 (by simpa using hx4)
    simpa using this
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
  obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
  have hcardG : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hQcard : Nat.card Q = 16 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp Q.isPGroup'
    have hdvd : Nat.card Q ∣ Nat.card (Equiv.Perm (Fin 6)) :=
      Subgroup.card_subgroup_dvd_card (Q : Subgroup (Equiv.Perm (Fin 6)))
    rw [hcardG] at hdvd
    have h16 : Nat.card R ≤ Nat.card Q := Subgroup.card_le_of_le hRQ
    rw [hcard] at h16
    rw [hk] at hdvd h16 ⊢
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    by_cases hk5 : 5 ≤ k
    · have h4 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 hk5
      have : 2 ^ 5 ∣ 720 := h4.trans hdvd
      omega
    · have : k = 4 := by omega
      rw [this]
      norm_num
  have hRQeq : R = Q := Subgroup.eq_of_le_of_card_ge hRQ (by rw [hcard, hQcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) Q P
  have hxmem : x ∈ ((g • Q : Sylow 2 (Equiv.Perm (Fin 6))) : Subgroup (Equiv.Perm (Fin 6))) := by
    rw [hg]
    exact hxP (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hRQeq] at hxmem
  have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hxmem
  apply hx2
  have h3 : (MulAut.conj g)⁻¹ • (x ^ 2) = 1 := by rw [smul_pow']; exact h2
  exact (MulEquiv.map_eq_one_iff ((MulAut.conj g)⁻¹ : MulAut (Equiv.Perm (Fin 6)))).mp h3

theorem sp4_proj_injective_of_charTwo {K : Type} [Field K] [CharP K 2] :
    Function.Injective (proj 2 K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : proj 2 K 1 = proj 2 K g := by rw [hg, map_one]
  obtain ⟨c, hc2, hc⟩ := CFSG.RankThree.CASymplecticSubfield.exists_smul_of_proj_eq
    (show 1 ≤ 2 by norm_num) h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h5 : ((c : K) - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - (c : K)) * h2
  have hc1 : (c : K) = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  rw [hc1, one_smul] at hc
  exact Subtype.ext (Units.ext hc)

theorem sp4_center_eq_bot {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hperf : Group.IsPerfect (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 K (Or.inl ⟨s, hs⟩)
  exact center_eq_bot_of_simple' (exists_noncomm_of_perfect hperf.commutator_eq_top)

theorem fixSub_nonempty_equiv_of_conj {T C : Type} [Group T] [Group C] (e : T ≃* C)
    (α : MulAut T) (β ψ : MulAut C) (hψ : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β) :
    Nonempty (↥(fixSub α) ≃* ↥(fixSub β)) :=
  ⟨((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
    (MulEquiv.subgroupCongr hψ)⟩

theorem sp4_nonempty_fixSub_equiv_perm_six {T : Type} [Group T] {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ p)
    (e : T ≃* StatedProj (StatedSp 2 K)) {α : MulAut T} (hord : orderOf α = p)
    (hαinn : α ∉ innerAut T) : Nonempty (↥(fixSub α) ≃* Equiv.Perm (Fin 6)) := by
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ p := hp.one_lt.le
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp 2 K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'ord : orderOf (MulAut.congr e α) = p := (orderOf_congr e α).trans hord
  have hα'p : MulAut.congr e α ^ p = 1 := by
    have := pow_orderOf_eq_one (MulAut.congr e α)
    rwa [hα'ord] at this
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf (le_refl 2) hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup 2 K := by
    have hidx' : (spSemilinearAutGroup 2 K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup 2 K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ p - 1) = 1 := by
      have h1 : (2 : ℕ) ^ p % 2 = 0 := by
        obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hf
        rw [pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ p := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, σ, hσord, -, h, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  obtain ⟨-, -, -, -, -, hfixiff, -, -, hS6, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      Nat.prime_two hp (by omega) hp2 hf (le_refl 2) hK σ hσord
  obtain ⟨hperm, -, -⟩ := hS6 ⟨rfl, by rw [Nat.div_self hp.pos]; norm_num⟩
  have hfixeq : fixSub (fieldAut 2 K σ) = subfieldFixedGroup K 2 σ := by
    ext x
    exact (hfixiff x).symm
  obtain ⟨e1⟩ := fixSub_nonempty_equiv_of_conj e α (fieldAut 2 K σ) h⁻¹ (by
    rw [hαh]
    group)
  obtain ⟨e2⟩ := hperm
  exact ⟨e1.trans ((MulEquiv.subgroupCongr hfixeq).trans e2)⟩

theorem sp4SubfieldCaseExcluded : Sp4SubfieldCaseExcluded := by
  intro T _ _ p hp hp5 hM α q U hord hαinn hq1 hqp hαq _ hU2 hαU hqU hmv
  have hC : StatedClassicalModel T .PSp 2 2 p := (lieModel_classical_iff (by decide)).mp hM
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hp2 : p ≠ 2 := by omega
  obtain ⟨eα⟩ := sp4_nonempty_fixSub_equiv_perm_six hp hp5 hK e hord hαinn
  have hcard : Nat.card (fixSub α) = 720 := by
    rw [Nat.card_congr eα.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have : Fact p.Prime := ⟨hp⟩
  have hordq : orderOf q = p := orderOf_eq_prime hqp hq1
  have hqfix : q ∈ fixSub α := hαq
  have hdvd : p ∣ 720 := by
    have h1 := orderOf_dvd_natCard (⟨q, hqfix⟩ : fixSub α)
    rw [Subgroup.orderOf_mk, hordq, hcard] at h1
    exact h1
  have hp5eq : p = 5 := by
    have h720 : p ∣ 2 ^ 4 * 3 ^ 2 * 5 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h720 with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
  have h4K : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp5
  have hcenter : Subgroup.center T = ⊥ := center_eq_bot_of_mulEquiv e (sp4_center_eq_bot h4K)
  obtain ⟨R, β₁, hRne, hR2, h5, -, -, h16el, -, -, hβfix, hcases⟩ :=
    exists_fixed_line_of_K1 hcenter hp hp5 hord hαinn hq1 hqp hαq hU2 hαU hqU hmv
  have h16 : 16 ≤ Nat.card R := h5 hp5eq
  rcases hcases with ⟨b, hb, hbord⟩ | ⟨hβinn, hβord⟩
  ·
    subst hp5eq
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 5) (by
      rw [← Nat.card_eq_fintype_card, hK])
    let φ : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
      MulEquiv.ofBijective (proj 2 K) ⟨sp4_proj_injective_of_charTwo, proj_surjective⟩
    let ρ : T →* Module.End K (Fin 2 ⊕ Fin 2 → K) :=
      (natRep (StatedSp 2 K)).comp (e.trans φ.symm).toMonoidHom
    have hρ : Function.Injective ρ := (natRep_injective _).comp (e.trans φ.symm).injective
    have hb1 : b ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hbord
      omega
    have hb5 : b ^ 5 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
    have hcomm : ∀ r ∈ R, b * r = r * b := by
      intro r hr
      have h1 : β₁ r = r := hβfix r hr
      rw [← hb, MulAut.conj_apply] at h1
      calc b * r = (b * r * b⁻¹) * b := by group
        _ = r * b := by rw [h1]
    have hK32 : Nat.card K = 32 := by rw [hK]; norm_num
    have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    exact cyc5_false_of_commuting_two_group ρ hK32 hV hρ hR2 hRne hb5 hb1 hcomm
  ·
    obtain ⟨eβ⟩ := sp4_nonempty_fixSub_equiv_perm_six hp hp5 hK e hβord hβinn
    have hle : R ≤ fixSub β₁ := fun r hr => hβfix r hr
    have hcardβ : Nat.card (fixSub β₁) = 720 := by
      rw [Nat.card_congr eβ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR2
    have hdvdR : Nat.card R ∣ 720 := by
      rw [← hcardβ]
      exact Subgroup.card_dvd_of_le hle
    have hR16 : Nat.card R = 16 := by
      rw [hk] at hdvdR h16 ⊢
      have hk4 : 4 ≤ k := by
        by_contra hlt
        have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      by_cases hk5 : 5 ≤ k
      · have h4 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 hk5
        have : 2 ^ 5 ∣ 720 := h4.trans hdvdR
        omega
      · have : k = 4 := by omega
        rw [this]
        norm_num
    have hel : IsElementaryAbelian 2 ↥R := h16el hp5eq hR16
    let R' : Subgroup (Equiv.Perm (Fin 6)) := (R.subgroupOf (fixSub β₁)).map eβ.toMonoidHom
    have hR'card : Nat.card R' = 16 := by
      rw [Subgroup.card_map_of_injective eβ.injective, ← hR16]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hel' : IsElementaryAbelian 2 ↥R' := by
      have h1 : IsElementaryAbelian 2 ↥(R.subgroupOf (fixSub β₁)) :=
        IsElementaryAbelian.subgroupOf hle
      exact IsElementaryAbelian.map eβ.toMonoidHom
    exact false_of_isElementaryAbelian_card_sixteen_perm_six R' hel' hR'card

end CFSG.RankThree.PartOne.Sec66T
