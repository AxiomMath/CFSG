module

public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuNorm
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuCent
public meta import CFSG.Monster.Code.Basis
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2198
public import Certificates.Certificate2202
public import Certificates.Certificate2204
public import Certificates.Certificate2205
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3046
public import Certificates.Certificate3157
public import CFSG.Quasithin.Background.HMathieuCodeCentInputs
public import Certificates.Certificate7061
public import Certificates.Certificate7060
public import Certificates.Certificate7065

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.Blueprint

theorem certC11_mem :
    ∀ a ∈ centC11H ++ centC11S, inAutOK a = true ∧ a[0]! = 0 :=
  Certificates.certificate7061.1

theorem certC11_fix0 : ∀ a ∈ centC11H, actC11 a 1299 = 1299 :=
  Certificates.certificate7061.2.1

theorem certC11_fix :
    ∀ m < 2048, (∀ a ∈ centC11H, actC11 a m = m) → m = 0 ∨ m = 1299 :=
  Certificates.certificate7061.2.2.1

theorem certC11_span :
    ∀ m < 2048, m ∈ combos (centC11S.map fun a => actC11 a 1299) :=
  Certificates.certificate7061.2.2.2.1

theorem certC10_mem :
    ∀ a ∈ centC10H ++ centC10S, inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1 :=
  Certificates.certificate7061.2.2.2.2.1

theorem certC10_fix0 : ∀ a ∈ centC10H, actC10 a 608 = 608 :=
  Certificates.certificate7061.2.2.2.2.2.1

theorem certC10_fix :
    ∀ m < 1024, (∀ a ∈ centC10H, actC10 a m = m) → m = 0 ∨ m = 608 :=
  Certificates.certificate7061.2.2.2.2.2.2.1

theorem certC10_span :
    ∀ m < 1024, m ∈ combos (centC10S.map fun a => actC10 a 608) :=
  Certificates.certificate7061.2.2.2.2.2.2.2.1

theorem centralizer_rhoC11_mog23 :
    Subgroup.centralizer ((rhoC11 mog23 inf_le_left).range : Set (MulAut W11)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 11) actC11 centC11H centC11S (fun a ha => ?_)
    actC11_lt (v0 := 1299) (by norm_num) (by norm_num) certC11_fix0 certC11_fix certC11_span
  obtain ⟨hok, ha0⟩ := certC11_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  exact ⟨rhoC11 mog23 inf_le_left ⟨σ, mem_mog23_of_arr hσ hσa ha0⟩, ⟨_, rfl⟩,
    fun m _ => rhoC11_toW mog23 inf_le_left ⟨σ, _⟩ hσa m⟩

theorem centralizer_rhoC11_autPerm :
    Subgroup.centralizer ((rhoC11 AutPerm le_rfl).range : Set (MulAut W11)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 11) actC11 centC11H centC11S (fun a ha => ?_)
    actC11_lt (v0 := 1299) (by norm_num) (by norm_num) certC11_fix0 certC11_fix certC11_span
  obtain ⟨hok, -⟩ := certC11_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  exact ⟨rhoC11 AutPerm le_rfl ⟨σ, hσ⟩, ⟨_, rfl⟩,
    fun m _ => rhoC11_toW AutPerm le_rfl ⟨σ, _⟩ hσa m⟩

theorem centralizer_rhoC10_mog22 :
    Subgroup.centralizer ((rhoC10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 10) actC10 centC10H centC10S (fun a ha => ?_)
    actC10_lt (v0 := 608) (by norm_num) (by norm_num) certC10_fix0 certC10_fix certC10_span
  obtain ⟨hok, ha0, ha1⟩ := certC10_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  exact ⟨rhoC10 mog22 mog22_le_mog22plus ⟨σ, mem_mog22_of_arr hσ hσa ha0 ha1⟩, ⟨_, rfl⟩,
    fun m _ => rhoC10_toW mog22 mog22_le_mog22plus ⟨σ, _⟩ hσa m⟩

theorem B_col : ∀ (i : Fin 12) (p : Fin 24), B i p = bvec 12 (syndCols.getD p 0) i := by
  decide

theorem syndCols_getD_lt : ∀ p < 24, syndCols.getD p 0 < 2 ^ 12 := by decide

theorem syndCols_translate : ∀ e < 4096,
    (∀ p < 24, ∃ q < 24, syndCols.getD q 0 = syndCols.getD p 0 ^^^ e) → e = 0 :=
  Certificates.certificate7061.2.2.2.2.2.2.2.2.1

theorem syndCols_inj : ∀ p < 24, ∀ q < 24, syndCols.getD p 0 = syndCols.getD q 0 → p = q := by
  decide

theorem eq_one_of_permWord_B {σ : Equiv.Perm (Fin 24)}
    (h : ∀ i : Fin 12, ∃ c : ZMod 2, permWord σ (B i) = B i + c • Ω) : σ = 1 := by
  choose ε hε using h
  obtain ⟨e, he, hee⟩ := toW_surj 12 (Multiplicative.ofAdd ε)
  have hε' : bvec 12 e = ε := congrArg Multiplicative.toAdd hee
  have hcol : ∀ p : Fin 24,
      syndCols.getD (σ⁻¹ p) 0 = syndCols.getD p 0 ^^^ e := by
    intro p
    refine bvec_inj (syndCols_getD_lt _ (σ⁻¹ p).2)
      (Nat.xor_lt_two_pow (syndCols_getD_lt _ p.2) he) ?_
    funext i
    rw [bvec_xor, Pi.add_apply, ← B_col, ← B_col, hε']
    have := congrFun (hε i) p
    simp only [permWord, Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Ω,
      mul_one] at this
    exact this
  have he0 : e = 0 := syndCols_translate e he fun p hp =>
    ⟨σ⁻¹ ⟨p, hp⟩, (σ⁻¹ ⟨p, hp⟩).2, hcol ⟨p, hp⟩⟩
  refine (inv_eq_one.1 (Equiv.ext fun p => Fin.ext ?_))
  rw [Equiv.Perm.one_apply]
  have := hcol p
  rw [he0, Nat.xor_zero] at this
  exact syndCols_inj _ (σ⁻¹ p).2 _ p.2 this

theorem rhoC11_injective (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm) :
    Function.Injective (rhoC11 Γ hΓ) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  refine eq_one_of_permWord_B fun i => ?_
  have hm : (Multiplicative.ofAdd (B i) : G6.PermMod 24) ∈ golayC := B_mem_C i
  have h1 := SecCoords.κ_permAct_rho codeCoords Γ (fun _ hσ => preserves_code (hΓ hσ)) σ hm
  have h2 : codeCoords.κ (G6.permAct 24 σ (Multiplicative.ofAdd (B i))) =
      codeCoords.κ (Multiplicative.ofAdd (B i)) := by
    rw [h1]
    exact congrArg (fun f : MulAut W11 => f (codeCoords.κ (Multiplicative.ofAdd (B i)))) hσ
  have hmem : G6.permAct 24 σ (Multiplicative.ofAdd (B i)) * Multiplicative.ofAdd (B i) ∈
      golayC := golayC.mul_mem ((preserves_code (hΓ σ.2)).1 _ hm) hm
  have hsq : ∀ x : W11, x * x = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h3 : codeCoords.κ (G6.permAct 24 σ (Multiplicative.ofAdd (B i)) *
      Multiplicative.ofAdd (B i)) = 1 := by
    rw [map_mul, h2]
    exact hsq _
  have hz1 : ∀ a b : ZMod 2, a + b = 1 → a = b + 1 := by decide
  rcases (mem_zpowers_allOnes _).1 ((codeCoords.ker_iff _ hmem).1 h3) with h4 | h4
  · refine ⟨0, ?_⟩
    rw [toAdd_mul, toAdd_permAct, toAdd_ofAdd] at h4
    rw [zero_smul, add_zero]
    funext p
    exact zmod2_eq_of_add (congrFun h4 p)
  · refine ⟨1, ?_⟩
    rw [toAdd_mul, toAdd_permAct, toAdd_ofAdd] at h4
    rw [one_smul]
    funext p
    exact hz1 _ _ (congrFun h4 p)

theorem lift22_col : ∀ (j : Fin 10) (p : Fin 24),
    bvec 24 (lift22Cols.getD j 0) p = bvec 10 (cc10Cols.getD p 0) j := by
  decide

theorem cc10Cols_getD_lt : ∀ p < 24, cc10Cols.getD p 0 < 2 ^ 10 := by decide

theorem cc10Cols_translate : ∀ e < 1024,
    (∀ p < 24, ∃ q < 24, cc10Cols.getD q 0 = cc10Cols.getD p 0 ^^^ e) → e = 0 :=
  Certificates.certificate7061.2.2.2.2.2.2.2.2.2

theorem cc10Cols_inj : ∀ p < 24, ∀ q < 24, cc10Cols.getD p 0 = cc10Cols.getD q 0 →
    p = q ∨ (p ≤ 1 ∧ q ≤ 1) := by
  decide

theorem eq_one_of_permWord_lift22
    {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus)
    (h : ∀ j : Fin 10, ∃ c : ZMod 2,
      permWord σ (bvec 24 (lift22Cols.getD j 0)) = bvec 24 (lift22Cols.getD j 0) + c • Ω) :
    σ = 1 := by
  choose ε hε using h
  obtain ⟨e, he, hee⟩ := toW_surj 10 (Multiplicative.ofAdd ε)
  have hε' : bvec 10 e = ε := congrArg Multiplicative.toAdd hee
  have hcol : ∀ p : Fin 24,
      cc10Cols.getD (σ⁻¹ p) 0 = cc10Cols.getD p 0 ^^^ e := by
    intro p
    refine bvec_inj (cc10Cols_getD_lt _ (σ⁻¹ p).2)
      (Nat.xor_lt_two_pow (cc10Cols_getD_lt _ p.2) he) ?_
    funext j
    rw [bvec_xor, Pi.add_apply, ← lift22_col, ← lift22_col, hε']
    have := congrFun (hε j) p
    simp only [permWord, Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Ω,
      mul_one] at this
    exact this
  have he0 : e = 0 := cc10Cols_translate e he fun p hp =>
    ⟨σ⁻¹ ⟨p, hp⟩, (σ⁻¹ ⟨p, hp⟩).2, hcol ⟨p, hp⟩⟩
  have hfix : ∀ p : Fin 24, p ≠ 0 → p ≠ 1 → σ p = p := by
    intro p hp0 hp1
    have h1 := hcol p
    rw [he0, Nat.xor_zero] at h1
    rcases cc10Cols_inj _ (σ⁻¹ p).2 _ p.2 h1 with h2 | ⟨-, h2⟩
    · have h3 : σ⁻¹ p = p := Fin.ext h2
      calc σ p = σ (σ⁻¹ p) := by rw [h3]
        _ = p := by simp
    · exfalso
      interval_cases hpv : (p : ℕ)
      · exact hp0 (Fin.ext hpv)
      · exact hp1 (Fin.ext hpv)
  rcases hσ.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.one_apply]
    by_cases hi0 : i = 0
    · rw [hi0, h0]
    by_cases hi1 : i = 1
    · rw [hi1, h1]
    exact hfix i hi0 hi1
  · exfalso
    refine swap_not_mem_autPerm (σ := σ) (fun i => ?_) hσ.1
    by_cases hi0 : i = 0
    · rw [hi0, h0]
      rfl
    by_cases hi1 : i = 1
    · rw [hi1, h1]
      rfl
    rw [hfix i hi0 hi1, swap01Arr_spec i hi0 hi1]

theorem rhoC10_mog22plus_injective :
    Function.Injective (rhoC10 mog22plus le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  refine eq_one_of_permWord_lift22 σ.2 fun j => ?_
  set n := bvec 24 (lift22Cols.getD j 0) with hn
  have hnl : n = lift22 (bvec 10 (2 ^ (j : ℕ))) := (lift22_cols j j.2).symm
  have hm : (Multiplicative.ofAdd n : G6.PermMod 24) ∈ golayC ⊓ pairKer 0 1 := by
    rw [hnl]
    exact (mem_code22 _).2 ⟨lift22_mem _, lift22_pair _⟩
  have hpres : ∀ τ ∈ mog22plus, Preserves (golayC ⊓ pairKer 0 1)
      (Subgroup.zpowers (G6.allOnes 24)) τ := fun _ hτ => preserves_code22 hτ
  have h1 := SecCoords.κ_permAct_rho code22Coords mog22plus hpres σ hm
  have h2 : code22Coords.κ (G6.permAct 24 σ (Multiplicative.ofAdd n)) =
      code22Coords.κ (Multiplicative.ofAdd n) := by
    rw [h1]
    exact congrArg (fun f : MulAut W10 => f (code22Coords.κ (Multiplicative.ofAdd n))) hσ
  have hmem : G6.permAct 24 σ (Multiplicative.ofAdd n) * Multiplicative.ofAdd n ∈
      golayC ⊓ pairKer 0 1 := (golayC ⊓ pairKer 0 1).mul_mem ((hpres σ σ.2).1 _ hm) hm
  have hsq : ∀ x : W10, x * x = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h3 : code22Coords.κ (G6.permAct 24 σ (Multiplicative.ofAdd n) * Multiplicative.ofAdd n) =
      1 := by
    rw [map_mul, h2]
    exact hsq _
  have hz1 : ∀ a b : ZMod 2, a + b = 1 → a = b + 1 := by decide
  rcases (mem_zpowers_allOnes _).1 ((code22Coords.ker_iff _ hmem).1 h3) with h4 | h4
  · refine ⟨0, ?_⟩
    rw [toAdd_mul, toAdd_permAct, toAdd_ofAdd] at h4
    rw [zero_smul, add_zero]
    funext p
    exact zmod2_eq_of_add (congrFun h4 p)
  · refine ⟨1, ?_⟩
    rw [toAdd_mul, toAdd_permAct, toAdd_ofAdd] at h4
    rw [one_smul]
    funext p
    exact hz1 _ _ (congrFun h4 p)

theorem range_rhoC10_mog22 : (rhoC10 mog22 mog22_le_mog22plus).range =
    (mog22.subgroupOf mog22plus).map (rhoC10 mog22plus le_rfl) := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨⟨σ, mog22_le_mog22plus σ.2⟩, by simp [Subgroup.mem_subgroupOf],
      MulEquiv.ext fun w => rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, (Subgroup.mem_subgroupOf).1 hσ⟩, MulEquiv.ext fun w => rfl⟩

theorem normalizer_rhoC10_mog22 :
    Subgroup.normalizer ((rhoC10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) =
      (rhoC10 mog22plus le_rfl).range := by
  have := finite_mulAut W10
  rw [range_rhoC10_mog22]
  refine normalizer_map_eq _ rhoC10_mog22plus_injective _ ?_ ?_
  · rw [← range_rhoC10_mog22]
    exact centralizer_rhoC10_mog22
  · rw [card_mulAut_congr ((Subgroup.subgroupOfEquivOfLe mog22_le_mog22plus).trans mog22EquivM22),
      card_mog22plus]
    have h := CFSG.Sporadic.Schreier.m22_mulAut_card
    rw [CFSG.Sporadic.Schreier.m22_card] at h
    exact h

theorem range_rhoC11_eq_map_top (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    (rhoC11 Γ hΓ).range = (⊤ : Subgroup ↥Γ).map (rhoC11 Γ hΓ) := by
  rw [MonoidHom.range_eq_map]

theorem normalizer_rhoC11_mog23 :
    Subgroup.normalizer ((rhoC11 mog23 inf_le_left).range : Set (MulAut W11)) =
      (rhoC11 mog23 inf_le_left).range := by
  have := finite_mulAut W11
  have hcard : Nat.card (MulAut ↥(⊤ : Subgroup ↥mog23)) ≤ Nat.card ↥mog23 := by
    rw [card_mulAut_congr (Subgroup.topEquiv.trans mog23EquivM23)]
    have h := CFSG.Sporadic.Schreier.m23_mulAut_card
    rw [CFSG.Sporadic.Schreier.m23_card] at h
    rw [card_mog23]
    exact h
  have h := normalizer_map_eq (rhoC11 mog23 inf_le_left) (rhoC11_injective _ _) ⊤
    (by rw [← range_rhoC11_eq_map_top]; exact centralizer_rhoC11_mog23) hcard
  rwa [← range_rhoC11_eq_map_top] at h

theorem normalizer_rhoC11_autPerm :
    Subgroup.normalizer ((rhoC11 AutPerm le_rfl).range : Set (MulAut W11)) =
      (rhoC11 AutPerm le_rfl).range := by
  have := finite_mulAut W11
  have hcard : Nat.card (MulAut ↥(⊤ : Subgroup ↥AutPerm)) ≤ Nat.card ↥AutPerm := by
    rw [card_mulAut_congr (Subgroup.topEquiv.trans autPermEquivM24')]
    have h := CFSG.Sporadic.Schreier.m24_mulAut_card
    rw [CFSG.Sporadic.Schreier.m24_card] at h
    rw [card_AutPerm]
    exact h
  have h := normalizer_map_eq (rhoC11 AutPerm le_rfl) (rhoC11_injective _ _) ⊤
    (by rw [← range_rhoC11_eq_map_top]; exact centralizer_rhoC11_autPerm) hcard
  rwa [← range_rhoC11_eq_map_top] at h

end CFSG.Quasithin.H.Mathieu
