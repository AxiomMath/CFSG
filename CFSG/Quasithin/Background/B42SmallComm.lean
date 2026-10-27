module

public import CFSG.Quasithin.Background.B51SumOffenders
public import CFSG.Quasithin.H13.A6S1372Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

namespace B42Small

variable {V : Type} [CommGroup V]

theorem mk_eq_mk_iff {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (m m' : ↥(FFModel.nat Γ).sec) :
    (QuotientGroup.mk m : ↥(FFModel.nat Γ).sec ⧸
        (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) = QuotientGroup.mk m' ↔ m = m' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : ((m⁻¹ * m' : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb) = 1 :=
      Subgroup.mem_bot.1 h
    apply Subtype.ext
    have h2 : (m : (FFModel.nat Γ).Amb)⁻¹ * m' = 1 := h1
    rw [inv_mul_eq_one] at h2
    exact h2
  · rintro rfl
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _

theorem card_field_le_card_commV [Finite V] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)}
    {π : (FFModel.nat Γ).Gam →* ↥H} (h : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : A ≠ ⊥) : Nat.card K ≤ Nat.card (commV A) := by
  classical
  obtain ⟨hπ, -, -, -, -, -, -, β, hβ, -, hβe⟩ := h
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨γ, hγ⟩ := hπ ⟨a, hAH haA⟩
  set γ' : ↥Γ := γ with hγ'
  set M : Matrix ι ι K := ((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) with hM
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ι → K, M.mulVec v₀ ≠ v₀ := by
    by_contra hno
    push Not at hno
    apply ha1'
    have hγ1 : γ' = 1 := Subtype.ext (Units.ext (B51Sum.matrix_eq_one_of_mulVec hno))
    have h1 : π γ' = 1 := by rw [hγ1]; exact map_one π
    rw [hγ] at h1
    exact congrArg Subtype.val h1
  set w : ι → K := M.mulVec v₀ - v₀ with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hv₀
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hw0 (funext hno)
  have hpre : ∀ c : K, ∃ u : ↥(⊤ : Subgroup V), β u =
      QuotientGroup.mk (⟨Multiplicative.ofAdd (c • v₀), Subgroup.mem_top _⟩ :
        ↥(FFModel.nat Γ).sec) := fun c => hβ _
  choose u hu using hpre
  have hmem : ∀ c : K, a (u c : V) * (u c : V)⁻¹ ∈ commV A := fun c =>
    Subgroup.subset_closure ⟨a, haA, (u c : V), rfl⟩
  let f : K → ↥(commV A) := fun c => ⟨a (u c : V) * (u c : V)⁻¹, hmem c⟩
  have hval : ∀ c : K, β ⟨a (u c : V) * (u c : V)⁻¹, Subgroup.mem_top _⟩ =
      QuotientGroup.mk (⟨Multiplicative.ofAdd (c • w), Subgroup.mem_top _⟩ :
        ↥(FFModel.nat Γ).sec) := by
    intro c
    have hu' : ((π γ : ↥H) : MulAut V) (u c : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
    have h1 := hβe γ (u c) ⟨Multiplicative.ofAdd (c • v₀), Subgroup.mem_top _⟩ hu'
      (Subgroup.mem_top _) (hu c)
    have e : (⟨a (u c : V) * (u c : V)⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) =
        ⟨((π γ : ↥H) : MulAut V) (u c : V), hu'⟩ * (u c)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hγ]
    rw [e, map_mul, map_inv, h1, hu c, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show natAct Γ γ' (Multiplicative.ofAdd (c • v₀)) * (Multiplicative.ofAdd (c • v₀))⁻¹ =
      Multiplicative.ofAdd (c • w)
    apply Multiplicative.toAdd.injective
    simp only [natAct, toAdd_mul, toAdd_inv, toAdd_ofAdd, Matrix.mulVec_smul, hw, hM, smul_sub]
    abel
  have hinj : Function.Injective f := by
    intro c d hcd
    have h1 : (a (u c : V) * (u c : V)⁻¹ : V) = a (u d : V) * (u d : V)⁻¹ :=
      congrArg Subtype.val hcd
    have h2 := hval c
    have h3 := hval d
    have e : (⟨a (u c : V) * (u c : V)⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) =
        ⟨a (u d : V) * (u d : V)⁻¹, Subgroup.mem_top _⟩ := Subtype.ext h1
    rw [e, h3, mk_eq_mk_iff] at h2
    have h4 := congrArg (fun m : ↥(FFModel.nat Γ).sec =>
      (Multiplicative.toAdd (((m : (FFModel.nat Γ).Amb) : Multiplicative (ι → K)))) i₀) h2
    exact (mul_right_cancel₀ hi₀ h4).symm
  exact Nat.card_le_card_of_injective f hinj

theorem natural_two_of_case1 [Finite V] {G L A : Subgroup (MulAut V)} (h1 : B42Case1 G L A)
    (hB4 : B4Hyp G L) (hA : A ≠ ⊥) (hc : Nat.card (commV A) ≤ 4) :
    BinaryNaturalSL L ⊤ ⊥ 2 2 := by
  obtain ⟨-, ⟨n, K, _, _, hK, π, hR⟩, hSyl, -⟩ := h1
  have hAL : A ≤ L := hSyl.1
  have hle := (card_field_le_card_commV hR hAL hA).trans hc
  rw [hK] at hle
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at hK1
  have hn : n = 1 ∨ n = 2 := by
    rcases n with _ | _ | _ | n
    · simp at hK1
    · left; rfl
    · right; rfl
    · exfalso
      have : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rcases hn with rfl | rfl
  · exfalso
    have : Fintype K := Fintype.ofFinite K
    have hcard : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) = 2 ^ 1 * 3 ^ 1 := by
      rw [← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv,
        Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
      decide
    have : Finite (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K)).Gam :=
      inferInstanceAs (Finite ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    have hsol : Group.IsSolvable (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K)).Gam :=
      Vol2Native.A312L.isSolvable_of_card_two_three hcard
    have hsolL : Group.IsSolvable ↥L := Group.isSolvable_of_surjective hR.1
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hB4.2.2.1 hsolL
  · exact ⟨K, inferInstance, inferInstance, hK, π, hR⟩

theorem swap_check : Core.pslLit6.all (fun a => Core.pslLit6.all (fun b =>
    !(Core.cmul a a == Core.cid6 && Core.cmul b b == Core.cid6 && !(a == Core.cid6) &&
      !(b == Core.cid6) && !(a == b) && Core.cmul a b == Core.cmul b a) ||
    Core.pslLit6.any (fun s => Core.cmul s a == Core.cmul b s && Core.cmul s b == Core.cmul a s)))
    = true := by
  decide +kernel

theorem a6_swap {a b : Equiv.Perm (Fin 6)} (ha : a ∈ alternatingGroup (Fin 6))
    (hb : b ∈ alternatingGroup (Fin 6)) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    ∃ s ∈ alternatingGroup (Fin 6), s * a = b * s ∧ s * b = a * s := by
  have h := swap_check
  rw [List.all_eq_true] at h
  have h1 := h _ (CFSG.Quasithin.H13.A6.A6Fin.codeN_mem_pslLit6 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 _ (CFSG.Quasithin.H13.A6.A6Fin.codeN_mem_pslLit6 hb)
  have e1 : (Core.cmul (codeN 6 a) (codeN 6 a) == Core.cid6) = true := by
    rw [← codeN_mul, ha2, codeN_one, beq_iff_eq]
    rfl
  have e2 : (Core.cmul (codeN 6 b) (codeN 6 b) == Core.cid6) = true := by
    rw [← codeN_mul, hb2, codeN_one, beq_iff_eq]
    rfl
  have e3 : (codeN 6 a == Core.cid6) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => ha1 ((CFSG.Quasithin.H13.A6.A6Fin.codeN_eq_cid6_iff a).1 h)
  have e4 : (codeN 6 b == Core.cid6) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hb1 ((CFSG.Quasithin.H13.A6.A6Fin.codeN_eq_cid6_iff b).1 h)
  have e5 : (codeN 6 a == codeN 6 b) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hab (codeN_injective h)
  have e6 : (Core.cmul (codeN 6 a) (codeN 6 b) == Core.cmul (codeN 6 b) (codeN 6 a)) = true := by
    rw [← codeN_mul, ← codeN_mul, hc, beq_iff_eq]
  have hcond : (Core.cmul (codeN 6 a) (codeN 6 a) == Core.cid6 &&
      Core.cmul (codeN 6 b) (codeN 6 b) == Core.cid6 && !(codeN 6 a == Core.cid6) &&
      !(codeN 6 b == Core.cid6) && !(codeN 6 a == codeN 6 b) &&
      Core.cmul (codeN 6 a) (codeN 6 b) == Core.cmul (codeN 6 b) (codeN 6 a)) = true := by
    rw [e1, e2, e3, e4, e5, e6]
    rfl
  rw [hcond, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨c, hc', hce⟩ := h2
  obtain ⟨s, hs, rfl⟩ := CFSG.Quasithin.H13.A6.A6Fin.exists_of_mem_pslLit6 hc'
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ← codeN_mul, ← codeN_mul, ← codeN_mul,
    ← codeN_mul] at hce
  exact ⟨s, hs, codeN_injective hce.1, codeN_injective hce.2⟩

section Linear

variable {K : Type} [Field K] [Finite K]

theorem two_eq_zero_of_card_four (hK : Nat.card K = 4) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  have h4 : (2 : K) * 2 = 0 := by
    have e : (2 : K) * 2 = ((4 : ℕ) : K) := by push_cast; ring
    rw [e, h]
  exact mul_self_eq_zero.mp h4

omit [Finite K] in
theorem eq_smul_of_axis {a b : Matrix.GeneralLinearGroup (Fin 3) K} {W : Submodule K (Fin 3 → K)}
    (hW : Module.finrank K W = 2)
    (haW : ∀ w ∈ W, (a : Matrix (Fin 3) (Fin 3) K).mulVec w = w)
    (hbW : ∀ w ∈ W, (b : Matrix (Fin 3) (Fin 3) K).mulVec w = w)
    (ha1 : a ≠ 1) {S : Set (Fin 3 → K)} (hS : S.Finite) (hSc : S.ncard ≤ Nat.card K)
    (haS : ∀ v, (a : Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ S)
    (hbS : ∀ v, (b : Matrix (Fin 3) (Fin 3) K).mulVec v - v ∈ S) :
    ∃ c : K, ∀ v, (b : Matrix (Fin 3) (Fin 3) K).mulVec v - v =
      c • ((a : Matrix (Fin 3) (Fin 3) K).mulVec v - v) := by
  classical
  set Ma : Matrix (Fin 3) (Fin 3) K := (a : Matrix (Fin 3) (Fin 3) K) with hMa
  set Mb : Matrix (Fin 3) (Fin 3) K := (b : Matrix (Fin 3) (Fin 3) K) with hMb
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin 3 → K, Ma.mulVec v₀ ≠ v₀ := by
    by_contra hno
    push Not at hno
    exact ha1 (Units.ext (B51Sum.matrix_eq_one_of_mulVec hno))
  set c₀ : Fin 3 → K := Ma.mulVec v₀ - v₀ with hc₀
  have hc₀0 : c₀ ≠ 0 := sub_ne_zero.mpr hv₀
  have hline : S = Set.range fun c : K => c • c₀ := by
    have hsub : (Set.range fun c : K => c • c₀) ⊆ S := by
      rintro _ ⟨c, rfl⟩
      have := haS (c • v₀)
      rwa [Matrix.mulVec_smul, ← smul_sub] at this
    have hinj : Function.Injective fun c : K => c • c₀ := fun c d hcd =>
      smul_left_injective K hc₀0 hcd
    have hcard : (Set.range fun c : K => c • c₀).ncard = Nat.card K := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    exact (Set.eq_of_subset_of_ncard_le hsub (hSc.trans hcard.ge) hS).symm
  obtain ⟨c, hc⟩ : ∃ c : K, Mb.mulVec v₀ - v₀ = c • c₀ := by
    have := hbS v₀
    rw [hline] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  refine ⟨c, fun v => ?_⟩
  set D : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    Matrix.toLin' (Mb - 1) - c • Matrix.toLin' (Ma - 1) with hD
  have hDv : ∀ u, D u = (Mb.mulVec u - u) - c • (Ma.mulVec u - u) := by
    intro u
    simp [hD, Matrix.toLin'_apply]
  have hWker : W ≤ LinearMap.ker D := by
    intro w hw
    rw [LinearMap.mem_ker, hDv, haW w hw, hbW w hw, sub_self, smul_zero, sub_zero]
  have hv₀ker : v₀ ∈ LinearMap.ker D := by
    rw [LinearMap.mem_ker, hDv, hc, ← hc₀, sub_self]
  have hv₀W : v₀ ∉ W := fun h => hv₀ (haW v₀ h)
  have hlt : W < W ⊔ K ∙ v₀ :=
    lt_of_le_of_ne le_sup_left fun h => hv₀W (h ▸ (le_sup_right : K ∙ v₀ ≤ W ⊔ K ∙ v₀)
      (Submodule.mem_span_singleton_self v₀))
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have htop : W ⊔ K ∙ v₀ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
    have hle := Submodule.finrank_le (W ⊔ K ∙ v₀)
    rw [h3] at hle ⊢
    omega
  have hker : W ⊔ K ∙ v₀ ≤ LinearMap.ker D :=
    sup_le hWker ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₀ker)
  have hvD : D v = 0 := by
    have : v ∈ LinearMap.ker D := hker (htop ▸ Submodule.mem_top)
    exact this
  rw [hDv, sub_eq_zero] at hvD
  exact hvD

theorem eq_of_swap (hK : Nat.card K = 4) {a b τ : Matrix.GeneralLinearGroup (Fin 3) K}
    (ha1 : a ≠ 1) {c : K}
    (hc : ∀ v, (b : Matrix (Fin 3) (Fin 3) K).mulVec v - v =
      c • ((a : Matrix (Fin 3) (Fin 3) K).mulVec v - v))
    (hτa : τ * a = b * τ) (hτb : τ * b = a * τ) : a = b := by
  classical
  set Ma : Matrix (Fin 3) (Fin 3) K := (a : Matrix (Fin 3) (Fin 3) K)
  set Mb : Matrix (Fin 3) (Fin 3) K := (b : Matrix (Fin 3) (Fin 3) K)
  set Mt : Matrix (Fin 3) (Fin 3) K := (τ : Matrix (Fin 3) (Fin 3) K)
  have hcM : Mb - 1 = c • (Ma - 1) := by
    ext i j
    have := congrFun (hc (Pi.single j 1)) i
    simpa [Matrix.sub_mulVec, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
      eq_comm] using this
  have hta : Mt * (Ma - 1) = (Mb - 1) * Mt := by
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) K =>
      ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hτa
    simp only [Units.val_mul] at this
    rw [mul_sub, sub_mul, this, mul_one, one_mul]
  have htb : Mt * (Mb - 1) = (Ma - 1) * Mt := by
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) K =>
      ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hτb
    simp only [Units.val_mul] at this
    rw [mul_sub, sub_mul, this, mul_one, one_mul]
  have h1 : (c * c) • ((Ma - 1) * Mt) = (Ma - 1) * Mt := by
    calc (c * c) • ((Ma - 1) * Mt) = c • ((c • (Ma - 1)) * Mt) := by
          rw [smul_mul_assoc, smul_smul]
      _ = c • ((Mb - 1) * Mt) := by rw [hcM]
      _ = c • (Mt * (Ma - 1)) := by rw [hta]
      _ = Mt * (c • (Ma - 1)) := by rw [mul_smul_comm]
      _ = Mt * (Mb - 1) := by rw [hcM]
      _ = (Ma - 1) * Mt := htb
  have hNa : Ma - 1 ≠ 0 := by
    intro h
    apply ha1
    apply Units.ext
    rw [sub_eq_zero] at h
    exact h
  have hNt : (Ma - 1) * Mt ≠ 0 := by
    intro h
    apply hNa
    have hinv := congrArg
      (· * ((τ⁻¹ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    simp only [zero_mul] at hinv
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at hinv
    exact hinv
  have hcc : c * c = 1 := by
    by_contra hne
    apply hNt
    have h2 : (c * c - 1) • ((Ma - 1) * Mt) = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  have h2 := two_eq_zero_of_card_four hK
  have hc1 : c = 1 := by
    have h3 : (c - 1) * (c - 1) = 0 := by
      have e : (c - 1) * (c - 1) = c * c - 2 * c + 1 := by ring
      rw [e, hcc, h2, zero_mul, sub_zero]
      have e2 : (1 : K) + 1 = 2 := by norm_num
      rw [e2, h2]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  apply Units.ext
  have h4 : Mb - 1 = Ma - 1 := by rw [hcM, hc1, one_smul]
  exact (sub_left_injective h4).symm

end Linear

theorem injective_of_realizesVia_nat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : (FFModel.nat Γ).Gam →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨-, -, -, -, -, -, -, β, hβ, -, hβe⟩ := h
  set γ' : ↥Γ := γ with hγ'
  have hfix : ∀ v : ι → K, ((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v = v := by
    intro v
    obtain ⟨u, hu⟩ := hβ (QuotientGroup.mk ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩)
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := by
      rw [hγ]
      exact u.2
    have h1 := hβe γ u ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ hu' (Subgroup.mem_top _) hu
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := by
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (u : V) = (u : V)
      rw [hγ]
      rfl
    rw [h2, hu, mk_eq_mk_iff] at h1
    have h3 := congrArg (fun m : ↥(FFModel.nat Γ).sec =>
      Multiplicative.toAdd (((m : (FFModel.nat Γ).Amb) : Multiplicative (ι → K)))) h1
    exact h3.symm
  exact Subtype.ext (Units.ext (B51Sum.matrix_eq_one_of_mulVec hfix))

theorem eq_one_of_mem_of_card_three {Γ : Type} [Group Γ] {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    {z : Γ} (hz : z ∈ Z) (h2 : z * z = 1) : z = 1 := by
  have h3 : orderOf (⟨z, hz⟩ : ↥Z) ∣ 3 := hZ ▸ orderOf_dvd_natCard _
  have h2' : orderOf (⟨z, hz⟩ : ↥Z) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h2))
  have h1 : orderOf (⟨z, hz⟩ : ↥Z) = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h3 h2'
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

theorem not_case8 [Finite V] {G L A : Subgroup (MulAut V)} (h8 : B42Case8 G L A)
    (hA : IsFFStarOffender G A) (hc : Nat.card (commV A) ≤ 4) : False := by
  classical
  obtain ⟨-, -, -, K, _, _, Γ₀, hK4, -, hhat, -, π, hR, hT⟩ := h8
  have hπinj := injective_of_realizesVia_nat hR
  obtain ⟨hπ, -, -, -, -, -, -, β, hβ, -, hβe⟩ := hR
  have hrep : ∀ x : V, ∃ w : Fin 3 → K, β ⟨x, Subgroup.mem_top _⟩ =
      QuotientGroup.mk (⟨Multiplicative.ofAdd w, Subgroup.mem_top _⟩ :
        ↥(FFModel.nat Γ₀).sec) := by
    intro x
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨x, Subgroup.mem_top _⟩)
    refine ⟨Multiplicative.toAdd ((m : (FFModel.nat Γ₀).Amb) : Multiplicative (Fin 3 → K)), ?_⟩
    rw [← hm]
    rfl
  choose rep hrep using hrep
  set S : Set (Fin 3 → K) := rep '' (commV A : Set V) with hS
  have hSfin : S.Finite := Set.toFinite _
  have hSc : S.ncard ≤ Nat.card K := by
    calc S.ncard ≤ (commV A : Set V).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card ↥(commV A) := (Nat.card_coe_set_eq _).symm
      _ ≤ Nat.card K := hK4 ▸ hc
  have hmemS : ∀ γ : ↥Γ₀, ((π γ : ↥L) : MulAut V) ∈ A → ∀ v : Fin 3 → K,
      (((γ : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v -
        v ∈ S := by
    intro γ hγA v
    obtain ⟨u, hu⟩ := hβ (QuotientGroup.mk ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩)
    have hx : ((π γ : ↥L) : MulAut V) (u : V) * (u : V)⁻¹ ∈ commV A :=
      Subgroup.subset_closure ⟨_, hγA, (u : V), rfl⟩
    refine ⟨_, hx, ?_⟩
    have hu' : ((π γ : ↥L) : MulAut V) (u : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
    have h1 : β ⟨((π γ : ↥L) : MulAut V) (u : V), hu'⟩ =
        QuotientGroup.mk (⟨natAct Γ₀ γ (Multiplicative.ofAdd v), Subgroup.mem_top _⟩ :
          ↥(FFModel.nat Γ₀).sec) :=
      hβe γ u ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ hu' (Subgroup.mem_top _) hu
    have e : (⟨((π γ : ↥L) : MulAut V) (u : V) * (u : V)⁻¹, Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup V)) = ⟨((π γ : ↥L) : MulAut V) (u : V), hu'⟩ * u⁻¹ := rfl
    have h2 : β ⟨((π γ : ↥L) : MulAut V) (u : V) * (u : V)⁻¹, Subgroup.mem_top _⟩ =
        QuotientGroup.mk (⟨Multiplicative.ofAdd
          ((((γ : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
            v - v), Subgroup.mem_top _⟩ : ↥(FFModel.nat Γ₀).sec) := by
      rw [e, map_mul, map_inv, h1, hu, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show natAct Γ₀ γ (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ =
        Multiplicative.ofAdd
          ((((γ : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
            v - v)
      apply Multiplicative.toAdd.injective
      simp only [natAct, toAdd_mul, toAdd_inv, toAdd_ofAdd]
      abel
    have h3 := hrep (((π γ : ↥L) : MulAut V) (u : V) * (u : V)⁻¹)
    rw [h2, mk_eq_mk_iff] at h3
    have h4 := congrArg (fun m : ↥(FFModel.nat Γ₀).sec =>
      Multiplicative.toAdd (((m : (FFModel.nat Γ₀).Amb) : Multiplicative (Fin 3 → K)))) h3
    exact h4.symm
  obtain ⟨hcard4, W, hW2, hfix⟩ := hT
  set A₀ := ((A.subgroupOf L).comap π).map Γ₀.subtype with hA₀
  have hmemA₀ : ∀ g ∈ A₀, ∃ γ : ↥Γ₀, ((π γ : ↥L) : MulAut V) ∈ A ∧
      (γ : Matrix.GeneralLinearGroup (Fin 3) K) = g := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ, hγ, rfl⟩
  have hAel := hA.2.2.1
  have hsq : ∀ g ∈ A₀, g * g = 1 := by
    intro g hg
    obtain ⟨γ, hγA, rfl⟩ := hmemA₀ g hg
    have h1 : π (γ * γ) = 1 := by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, ← pow_two]
      exact hAel.2 _ hγA
    rw [← map_one π] at h1
    have h2 := hπinj h1
    rw [← Subgroup.coe_mul, h2]
    rfl
  have hcomm : ∀ g ∈ A₀, ∀ h ∈ A₀, g * h = h * g := by
    intro g hg h hh
    obtain ⟨γ, hγA, rfl⟩ := hmemA₀ g hg
    obtain ⟨δ, hδA, rfl⟩ := hmemA₀ h hh
    have h1 : π (γ * δ) = π (δ * γ) := by
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hAel.1 _ hγA _ hδA
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hπinj h1]
  obtain ⟨a, haA₀, ha1⟩ : ∃ a ∈ A₀, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : A₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    rw [this, Subgroup.card_bot] at hcard4
    norm_num at hcard4
  obtain ⟨b, hbA₀, hb1, hba⟩ : ∃ b ∈ A₀, b ≠ 1 ∧ b ≠ a := by
    by_contra hno
    push Not at hno
    have hle : A₀ ≤ Subgroup.zpowers a := by
      intro g hg
      by_cases hg1 : g = 1
      · rw [hg1]; exact Subgroup.one_mem _
      · rw [hno g hg hg1]; exact Subgroup.mem_zpowers a
    have h2 : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hsq a haA₀) ha1
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨c, hcb⟩ := eq_smul_of_axis hW2 (hfix a haA₀ ha1).1 (hfix b hbA₀ hb1).1 ha1 hSfin hSc
    (by
      obtain ⟨γ, hγA, rfl⟩ := hmemA₀ a haA₀
      exact hmemS γ hγA)
    (by
      obtain ⟨γ, hγA, rfl⟩ := hmemA₀ b hbA₀
      exact hmemS γ hγA)
  obtain ⟨-, hZ3, ⟨e⟩⟩ := hhat
  set f : ↥Γ₀ →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Γ₀)) with hf
  have hfsurj : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : ∀ x : ↥Γ₀, f x = 1 ↔ x ∈ Subgroup.center ↥Γ₀ := by
    intro x
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨a', ha'A, rfl⟩ := hmemA₀ a haA₀
  obtain ⟨b', hb'A, rfl⟩ := hmemA₀ b hbA₀
  have ha'2 : a' * a' = 1 := Subtype.ext (by simpa using hsq _ haA₀)
  have hb'2 : b' * b' = 1 := Subtype.ext (by simpa using hsq _ hbA₀)
  have hab' : a' * b' = b' * a' := Subtype.ext (by simpa using hcomm _ haA₀ _ hbA₀)
  have ha'1 : a' ≠ 1 := fun h => ha1 (by rw [h]; rfl)
  have hb'1 : b' ≠ 1 := fun h => hb1 (by rw [h]; rfl)
  have hne' : a' ≠ b' := fun h => hba (by rw [h])
  have hs := a6_swap (f a').2 (f b').2
    (by rw [← Subgroup.coe_mul, ← map_mul, ha'2, map_one]; rfl)
    (by rw [← Subgroup.coe_mul, ← map_mul, hb'2, map_one]; rfl)
    (fun h => ha'1 (eq_one_of_mem_of_card_three hZ3
      ((hfker a').1 (Subtype.ext h)) ha'2))
    (fun h => hb'1 (eq_one_of_mem_of_card_three hZ3
      ((hfker b').1 (Subtype.ext h)) hb'2))
    (fun h => by
      have h1 : f (a' * b'⁻¹) = 1 := by
        rw [map_mul, map_inv, Subtype.ext h, mul_inv_cancel]
      have h2 : a' * b'⁻¹ * (a' * b'⁻¹) = 1 := by
        have hbinv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'2
        rw [hbinv]
        calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
          _ = a' * (a' * b') * b' := by rw [hab']
          _ = (a' * a') * (b' * b') := by group
          _ = 1 := by rw [ha'2, hb'2, one_mul]
      have h3 := eq_one_of_mem_of_card_three hZ3 ((hfker _).1 h1) h2
      exact hne' (mul_inv_eq_one.mp h3))
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab'])
  obtain ⟨s, hsA, hsa, hsb⟩ := hs
  obtain ⟨τ, hτ⟩ := hfsurj ⟨s, hsA⟩
  have hconj : ∀ x y : ↥Γ₀, x * x = 1 → y * y = 1 →
      (s : Equiv.Perm (Fin 6)) * (f x : Equiv.Perm (Fin 6)) = (f y : Equiv.Perm (Fin 6)) * s →
      τ * x = y * τ := by
    intro x y hx2 hy2 hxy
    set z := τ * x * τ⁻¹ * y⁻¹ with hz
    have hzZ : z ∈ Subgroup.center ↥Γ₀ := by
      rw [← hfker]
      apply Subtype.ext
      rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv, hτ]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hxy]
      group
    have hzc := Subgroup.mem_center_iff.mp hzZ
    have hz2 : z * z = 1 := by
      have e1 : τ * x * τ⁻¹ = z * y := by rw [hz]; group
      have e2 : (τ * x * τ⁻¹) * (τ * x * τ⁻¹) = 1 := by
        calc (τ * x * τ⁻¹) * (τ * x * τ⁻¹) = τ * (x * x) * τ⁻¹ := by group
          _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
      rw [e1] at e2
      calc z * z = z * z * (y * y) := by rw [hy2, mul_one]
        _ = z * (z * y) * y := by group
        _ = z * (y * z) * y := by rw [hzc y]
        _ = (z * y) * (z * y) := by group
        _ = 1 := e2
    have h1 := eq_one_of_mem_of_card_three hZ3 hzZ hz2
    rw [hz] at h1
    have h2 : τ * x * τ⁻¹ = y := mul_inv_eq_one.mp h1
    rw [← h2]
    group
  have hτa := hconj a' b' ha'2 hb'2 hsa
  have hτb := hconj b' a' hb'2 ha'2 hsb
  apply hba
  exact (eq_of_swap hK4 ha1 hcb (congrArg Subtype.val hτa) (congrArg Subtype.val hτb)).symm

end B42Small

end CFSG.Quasithin
