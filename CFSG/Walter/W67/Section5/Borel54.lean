module

public import CFSG.Walter.W67.Section5.Torus
public import CFSG.Walter.W67.Section5.Real3

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Glauberman.Dickson

namespace Borel5

section PSL2

variable {F : Type} [Field F]

@[expose] def unipParams (V : Subgroup PSL(2, F)) : AddSubgroup F where
  carrier := {x | psl2QuotientMap F (sl2UpperUnipotent x) ∈ V}
  add_mem' {a b} ha hb := by
    change psl2QuotientMap F (sl2UpperUnipotent (a + b)) ∈ V
    rw [← sl2UpperUnipotent_mul, map_mul]
    exact V.mul_mem ha hb
  zero_mem' := by
    change psl2QuotientMap F (sl2UpperUnipotent 0) ∈ V
    rw [sl2UpperUnipotent_zero, map_one]
    exact V.one_mem
  neg_mem' {a} ha := by
    change psl2QuotientMap F (sl2UpperUnipotent (-a)) ∈ V
    rw [← sl2UpperUnipotent_inv, map_inv]
    exact V.inv_mem ha

theorem unip_eq_bot_or_eq_top [Finite F] {V : Subgroup PSL(2, F)}
    (hVU : V ≤ unip F) (hV : ∀ a : Fˣ, ∀ v ∈ V, torusHom F a * v * (torusHom F a)⁻¹ ∈ V) :
    V = ⊥ ∨ V = unip F := by
  classical
  set W := unipParams V
  let S : AddSubgroup F :=
    { carrier := {c | ∀ x ∈ W, c * x ∈ W}
      add_mem' := fun {a b} ha hb x hx => by rw [add_mul]; exact W.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by rw [zero_mul]; exact W.zero_mem
      neg_mem' := fun {a} ha x hx => by rw [neg_mul]; exact W.neg_mem (ha x hx) }
  have hsq : ∀ a : Fˣ, (a : F) ^ 2 ∈ S := by
    intro a x hx
    have := hV a _ hx
    rw [torusHom_conj] at this
    exact this
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  have hFcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  let sqHom : Fˣ →* Fˣ := powMonoidHom 2
  have hker : Nat.card sqHom.ker ≤ 2 := by
    have hset : (sqHom.ker : Set Fˣ) ⊆ {1, -1} := by
      intro a ha
      have ha' : a ^ 2 = 1 := ha
      have : (a : F) * a = 1 := by
        have := congrArg Units.val ha'
        simpa [pow_two] using this
      rcases mul_self_eq_one_iff.mp this with h | h
      · exact Or.inl (Units.ext h)
      · exact Or.inr (Units.ext h)
    calc Nat.card sqHom.ker = (sqHom.ker : Set Fˣ).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, -1} : Set Fˣ).ncard := Set.ncard_le_ncard hset (Set.toFinite _)
      _ ≤ ({-1} : Set Fˣ).ncard + 1 := Set.ncard_insert_le 1 {-1}
      _ = 2 := by rw [Set.ncard_singleton]
  have hrange : Nat.card F - 1 ≤ 2 * Nat.card sqHom.range := by
    have h1 := Subgroup.card_ker_mul_card_range sqHom
    rw [Nat.card_units] at h1
    calc Nat.card F - 1 = Nat.card sqHom.ker * Nat.card sqHom.range := h1.symm
      _ ≤ 2 * Nat.card sqHom.range := Nat.mul_le_mul_right _ hker
  have hSge : Nat.card F < 2 * Nat.card S := by
    let ι : Option sqHom.range → S := fun o => match o with
      | none => ⟨0, S.zero_mem⟩
      | some y => ⟨((y : Fˣ) : F), by
          obtain ⟨a, ha⟩ := y.2
          rw [← ha]
          exact hsq a⟩
    have hι : Function.Injective ι := by
      intro o₁ o₂ h
      cases o₁ with
      | none =>
        cases o₂ with
        | none => rfl
        | some y =>
          exfalso
          have := congrArg Subtype.val h
          exact (Units.ne_zero (y : Fˣ)) this.symm
      | some y₁ =>
        cases o₂ with
        | none =>
          exfalso
          have := congrArg Subtype.val h
          exact (Units.ne_zero (y₁ : Fˣ)) this
        | some y₂ =>
          have := congrArg Subtype.val h
          simp only [ι] at this
          rw [Subtype.ext (Units.ext this)]
    have hle := Nat.card_le_card_of_injective ι hι
    rw [Finite.card_option] at hle
    have hpos : 1 ≤ Nat.card F := Nat.card_pos
    omega
  have hStop : S = ⊤ := by
    have hdvd : Nat.card S ∣ p ^ (n : ℕ) := by
      rw [← hFcard]
      exact AddSubgroup.card_addSubgroup_dvd_card S
    obtain ⟨d, hd, hSd⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hdn : d = n := by
      by_contra hne
      have hlt : d + 1 ≤ n := by omega
      have h1 : p ^ (d + 1) ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right hp.pos hlt
      rw [hFcard, hSd] at hSge
      have h2 : 2 * p ^ d ≤ p ^ (d + 1) := by
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left _ hp.two_le
      omega
    apply AddSubgroup.eq_top_of_card_eq
    rw [hSd, hdn, ← hFcard]
  rcases AddSubgroup.bot_or_exists_ne_zero W with hW | ⟨w, hw, hw0⟩
  · left
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff v).mp (hVU hv)
    have hx : x ∈ W := hv
    rw [hW, AddSubgroup.mem_bot] at hx
    rw [hx, sl2UpperUnipotent_zero, map_one]
    exact Subgroup.one_mem _
  · right
    apply le_antisymm hVU
    intro u hu
    obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    have hyS : y * (w : F)⁻¹ ∈ S := by rw [hStop]; exact AddSubgroup.mem_top _
    have := hyS w hw
    rw [inv_mul_cancel_right₀ hw0] at this
    exact this

theorem conj_unip_fixed_iff {g : PSL(2, F)} {y : F} (hy : y ≠ 0) (pt : PSL2ProjectiveLine F) :
    (g * psl2QuotientMap F (sl2UpperUnipotent y) * g⁻¹) • pt = pt ↔
      pt = g • psl2ProjectiveInfinity F := by
  rw [mul_smul, mul_smul]
  constructor
  · intro h
    have h1 : psl2QuotientMap F (sl2UpperUnipotent y) • (g⁻¹ • pt) = g⁻¹ • pt := by
      have := congrArg (fun z => g⁻¹ • z) h
      simpa [smul_smul] using this
    rw [unip_fixed_iff hy] at h1
    rw [← h1, smul_inv_smul]
  · rintro rfl
    rw [inv_smul_smul, (unip_fixed_iff hy _).mpr rfl]

theorem exists_fixed_of_isPGroup {p f : ℕ} [Fact p.Prime] [Finite F]
    (hFcard : Nat.card F = p ^ f) {N : Subgroup PSL(2, F)} (hN : IsPGroup p N) (hN1 : N ≠ ⊥) :
    ∃ x : PSL2ProjectiveLine F, ∀ h ∈ Subgroup.normalizer (N : Set PSL(2, F)), h • x = x := by
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F hFcard
  obtain ⟨P, hP⟩ := hN.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, F) Q P
  have hNg : ∀ n ∈ N, ∃ y : F, n = g * psl2QuotientMap F (sl2UpperUnipotent y) * g⁻¹ := by
    intro n hn
    have hnP : n ∈ (P : Subgroup PSL(2, F)) := hP hn
    rw [← hg, Sylow.coe_subgroup_smul, hQ] at hnP
    obtain ⟨u, hu, rfl⟩ := hnP
    obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    exact ⟨y, rfl⟩
  obtain ⟨n₀, hn₀, hn₀1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN1
  obtain ⟨y₀, hy₀⟩ := hNg n₀ hn₀
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    apply hn₀1
    rw [hy₀, sl2UpperUnipotent_zero, map_one, mul_one, mul_inv_cancel]
  refine ⟨g • psl2ProjectiveInfinity F, fun h hh => ?_⟩
  have hc : h⁻¹ * n₀ * h⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) n₀).mp hn₀
  obtain ⟨y₁, hy₁⟩ := hNg _ hc
  have hfix1 : (h⁻¹ * n₀ * h⁻¹⁻¹) • (g • psl2ProjectiveInfinity F) =
      g • psl2ProjectiveInfinity F := by
    rw [hy₁]
    by_cases hy₁0 : y₁ = 0
    · rw [hy₁0, sl2UpperUnipotent_zero, map_one, mul_one, mul_inv_cancel, one_smul]
    · exact (conj_unip_fixed_iff hy₁0 _).mpr rfl
  have hfix2 : n₀ • (h • g • psl2ProjectiveInfinity F) = h • g • psl2ProjectiveInfinity F := by
    calc n₀ • (h • g • psl2ProjectiveInfinity F)
        = (h * (h⁻¹ * n₀ * h⁻¹⁻¹)) • (g • psl2ProjectiveInfinity F) := by
          rw [smul_smul]; congr 1; group
      _ = h • ((h⁻¹ * n₀ * h⁻¹⁻¹) • (g • psl2ProjectiveInfinity F)) := by rw [mul_smul]
      _ = h • g • psl2ProjectiveInfinity F := by rw [hfix1]
  rw [hy₀, conj_unip_fixed_iff hy₀0] at hfix2
  exact hfix2

theorem eq_of_torus_fixed {a : Fˣ} (ha : (a : F) ^ 2 ≠ 1) {x : PSL2ProjectiveLine F}
    (hx : torusHom F a • x = x) :
    x = psl2ProjectiveInfinity F ∨ x = psl2ProjectiveZero F := by
  induction x using Projectivization.ind with
  | h v hv =>
    change psl2QuotientMap F (splitTorusSLHom F a) • Projectivization.mk F v hv = _ at hx
    rw [psl2QuotientMap_smul, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hx
    obtain ⟨c, hc⟩ := hx
    have hTv : splitTorusSLHom F a • v = ![(a : F) * v 0, (a : F)⁻¹ * v 1] := by
      change Matrix.mulVec (splitTorusSLHom F a).val v = _
      ext i
      fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
    rw [hTv] at hc
    have h0 : (c : F) * v 0 = (a : F) * v 0 := by simpa [Units.smul_def] using congrFun hc 0
    have h1 : (c : F) * v 1 = (a : F)⁻¹ * v 1 := by simpa [Units.smul_def] using congrFun hc 1
    by_cases hv1 : v 1 = 0
    · left
      rw [psl2ProjectiveInfinity, Projectivization.mk_eq_mk_iff']
      refine ⟨v 0, ?_⟩
      ext i
      fin_cases i <;> simp [hv1]
    · by_cases hv0 : v 0 = 0
      · right
        rw [psl2ProjectiveZero, Projectivization.mk_eq_mk_iff']
        refine ⟨v 1, ?_⟩
        ext i
        fin_cases i <;> simp [hv0]
      · exfalso
        have hca : (c : F) = a := mul_right_cancel₀ hv0 h0
        have hca' : (c : F) = (a : F)⁻¹ := mul_right_cancel₀ hv1 h1
        apply ha
        rw [pow_two]
        calc (a : F) * a = (a : F) * c := by rw [hca]
          _ = (a : F) * (a : F)⁻¹ := by rw [hca']
          _ = 1 := mul_inv_cancel₀ (Units.ne_zero a)

theorem weyl_smul_infinity : weyl F • psl2ProjectiveInfinity F = psl2ProjectiveZero F := by
  change psl2QuotientMap F (standardSplitWeylSL F) • _ = _
  rw [psl2QuotientMap_smul, psl2ProjectiveInfinity, Projectivization.smul_mk, psl2ProjectiveZero,
    Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  change _ = Matrix.mulVec (standardSplitWeylSL F).val ![1, 0]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

@[expose] noncomputable def unipOpp (F : Type) [Field F] : Subgroup PSL(2, F) :=
  (unip F).map (MulAut.conj (weyl F)).toMonoidHom

theorem torus_conj_weyl : (torus F).map (MulAut.conj (weyl F)).toMonoidHom = torus F := by
  ext d
  constructor
  · rintro ⟨d', hd', rfl⟩
    change weyl F * d' * (weyl F)⁻¹ ∈ torus F
    rw [weyl_conj_torus hd']
    exact (torus F).inv_mem hd'
  · intro hd
    refine ⟨d⁻¹, (torus F).inv_mem hd, ?_⟩
    change weyl F * d⁻¹ * (weyl F)⁻¹ = d
    rw [weyl_conj_torus ((torus F).inv_mem hd), inv_inv]

theorem stab_infinity : MulAction.stabilizer PSL(2, F) (psl2ProjectiveInfinity F) =
    unip F ⊔ torus F := by
  rw [← normalizer_unip, psl2UpperUnipotent_normalizer_eq_borel]
  rfl

theorem stab_zero : MulAction.stabilizer PSL(2, F) (psl2ProjectiveZero F) =
    unipOpp F ⊔ torus F := by
  rw [← weyl_smul_infinity, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stab_infinity,
    Subgroup.map_sup]
  change (unipOpp F) ⊔ (torus F).map (MulAut.conj (weyl F)).toMonoidHom = _
  rw [torus_conj_weyl]

theorem even_mul_sq_sub_one {q : ℕ} (hq : Odd q) : Even (q * (q ^ 2 - 1)) := by
  obtain ⟨k, rfl⟩ := hq
  apply Nat.even_mul.mpr
  right
  have : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
    rw [show (2 * k + 1) ^ 2 = 4 * k * k + 4 * k + 1 by ring]
    rw [Nat.add_sub_cancel]
    ring
  rw [this]
  exact even_two_mul _

theorem even_mul_sq_sub_one_div_two {q : ℕ} (hq : Odd q) : Even (q * (q ^ 2 - 1) / 2) := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    rw [show (2 * k + 1) ^ 2 = 4 * k * k + 4 * k + 1 by ring]
    rw [Nat.add_sub_cancel]
    ring
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  rw [h1, hj, show (2 * k + 1) * (4 * (j + j)) = 2 * ((2 * k + 1) * (2 * (j + j))) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact Nat.even_mul.mpr (Or.inr (even_two_mul _))

theorem le_borel_of_odd
    {p f : ℕ} [hpp : Fact p.Prime] [Finite F] (hFcard : Nat.card F = p ^ f)
    (hp : Odd p) (hF5 : 5 ≤ Nat.card F) {M : Subgroup PSL(2, F)} (hTM : torus F ≤ M)
    (hodd : Odd (Nat.card M)) : M ≤ unip F ⊔ torus F ∨ M ≤ unipOpp F ⊔ torus F := by
  classical
  have hF2 : ringChar F ≠ 2 := by
    have : CharP F p := by
      let : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFcard])
    rw [ringChar.eq F p]
    rintro rfl
    exact absurd hp (by decide)
  have hT := card_torus hF2 (F := F)
  have hTcard2 : 2 ≤ Nat.card (torus F) := by omega
  obtain ⟨t, ht, ht1⟩ := (Subgroup.bot_or_exists_ne_one (torus F)).resolve_left (by
    intro h
    rw [h, Subgroup.card_bot] at hTcard2
    omega)
  obtain ⟨a, rfl⟩ := ht
  have ha : (a : F) ^ 2 ≠ 1 := fun h => ht1 ((torusHom_eq_one_iff a).mpr h)
  have hfix : ∀ x : PSL2ProjectiveLine F, (∀ h ∈ M, h • x = x) →
      M ≤ unip F ⊔ torus F ∨ M ≤ unipOpp F ⊔ torus F := by
    intro x hx
    rcases eq_of_torus_fixed ha (hx _ (hTM ⟨a, rfl⟩)) with rfl | rfl
    · left
      rw [← stab_infinity]
      exact fun h hh => hx h hh
    · right
      rw [← stab_zero]
      exact fun h hh => hx h hh
  have hMT : Nat.card (torus F) ∣ Nat.card M := Subgroup.card_dvd_of_le hTM
  have hcopT : Nat.Coprime p (Nat.card (torus F)) := by
    have hc := coprime_card_unip_torus hF2 (F := F)
    rw [psl2UpperUnipotentSubgroup_card, hFcard] at hc
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by
      rintro rfl
      rw [pow_zero] at hFcard
      omega)) hc
  have hgcd : Nat.gcd (p ^ f - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    have : Odd (p ^ f) := hp.pow
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by omega⟩
  have heq_T : Nat.card M ≤ Nat.card (torus F) → M ≤ unip F ⊔ torus F := by
    intro hle
    have : torus F = M := Subgroup.eq_of_le_of_card_ge hTM hle
    rw [← this]
    exact le_sup_right
  have hoddcard : ∀ (X : Type) [Group X] [Finite X], Nonempty (M ≃* X) → ¬ Even (Nat.card X) := by
    rintro X _ _ ⟨e⟩ hX
    rw [← Nat.card_congr e.toEquiv] at hX
    exact (Nat.not_even_iff_odd.mpr hodd) hX
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hFcard M with
    hEl | ⟨z, hz, hzc, -⟩ | ⟨z, -, hzc, -⟩ | ⟨-, hA4⟩ | ⟨-, hS4⟩ | ⟨-, hA5⟩ |
      ⟨m, t, -, ht, N, C, hNn, -, hNc, -, hCc, -, hNC⟩ | ⟨m, hm, -, hPSL⟩ | ⟨m, hm, -, hPGL⟩
  ·
    exfalso
    have hpg : IsPGroup p M := IsElementaryAbelian.isPGroup p M
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    rw [hk] at hMT
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp.out).mp hMT
    rw [hj] at hcopT
    have : j = 0 := by
      by_contra hj0
      exact hpp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcopT (dvd_pow_self p hj0))
    rw [hj, this, pow_zero] at hTcard2
    omega
  ·
    have hTeq : Nat.card (torus F) = (p ^ f - 1) / 2 := by rw [← hFcard]; omega
    rw [hFcard, hgcd] at hz
    rcases hz with hz | hz
    · left
      apply heq_T
      rw [hzc]
      exact Nat.le_of_dvd (by omega) (by rw [hTeq]; exact hz)
    · exfalso
      have h1 : Nat.card (torus F) ∣ (p ^ f + 1) / 2 := by
        rw [← hzc] at hz
        exact hMT.trans hz
      have h2 : (p ^ f + 1) / 2 = Nat.card (torus F) + 1 := by
        rw [hTeq]
        have : Odd (p ^ f) := hp.pow
        obtain ⟨k, hk⟩ := this
        rw [hk]
        omega
      rw [h2] at h1
      have h3 := (Nat.dvd_add_right (dvd_refl _)).mp h1
      have := Nat.le_of_dvd one_pos h3
      omega
  · exact absurd (hzc ▸ even_two_mul z) (Nat.not_even_iff_odd.mpr hodd)
  · exfalso
    apply hoddcard _ hA4
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  · exfalso
    apply hoddcard _ hS4
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  · exfalso
    apply hoddcard _ hA5
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  ·
    by_cases hN : N = ⊥
    · left
      apply heq_T
      have hCtop : C = ⊤ := by rw [← hNC, hN, bot_sup_eq]
      have hMC : Nat.card M = t := by
        rw [← hCc, hCtop, Subgroup.card_top]
      rw [hMC]
      rw [hgcd] at ht
      have hTeq : Nat.card (torus F) = (p ^ f - 1) / 2 := by rw [← hFcard]; omega
      exact Nat.le_of_dvd (by omega) (by rw [hTeq]; exact ht)
    · obtain ⟨x, hx⟩ := exists_fixed_of_isPGroup hFcard (N := N.map M.subtype)
        ((IsPGroup.of_card hNc).map _)
        (by
          intro h
          apply hN
          rw [← Subgroup.map_eq_bot_iff_of_injective N M.subtype_injective]
          exact h)
      apply hfix x
      intro h hh
      apply hx
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        exact ⟨⟨h, hh⟩ * y' * ⟨h, hh⟩⁻¹, hNn.conj_mem y' hy' ⟨h, hh⟩, rfl⟩
      · exact (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  · exfalso
    apply hoddcard _ hPSL
    have hm' : 0 < m := Nat.pos_of_ne_zero hm
    have hcardm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    rw [psl2_card_formula _ ⟨p, m, hpp.out, hp, hm', hcardm⟩, hcardm]
    exact even_mul_sq_sub_one_div_two hp.pow
  · exfalso
    have : Finite (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
      Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
    apply hoddcard _ hPGL
    have hcardm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    rw [BenderSuzuki.External.huppertXI13_card_pgl2, hcardm]
    exact even_mul_sq_sub_one hp.pow

theorem le_unip_of_isPGroup {p f : ℕ} [Fact p.Prime] [Finite F] (hFcard : Nat.card F = p ^ f)
    (hF2 : ringChar F ≠ 2) {X : Subgroup PSL(2, F)} (hX : IsPGroup p X)
    (hXB : X ≤ unip F ⊔ torus F) : X ≤ unip F := by
  intro x hx
  rw [← stab_infinity] at hXB
  set Bo := psl2Borel F
  set U := (unip F).subgroupOf Bo
  have hUn : U.Normal := psl2UpperUnipotent_normal_in_borel (K := F)
  have hU : Nat.card U = Nat.card (unip F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl2UpperUnipotent_le_borel).toEquiv
  have hQ : Nat.card (Bo ⧸ U) = Nat.card (torus F) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    rw [hU] at h1
    have h2 := card_borel hF2 (F := F)
    have hpos : 0 < Nat.card (unip F) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h1]
    exact h2.trans (mul_comm _ _)
  set xb : Bo := ⟨x, hXB hx⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : (xb : Bo ⧸ U) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : xb ^ (p ^ k) = 1 := Subtype.ext (by
      change x ^ (p ^ k) = 1
      rw [← hk]
      exact pow_orderOf_eq_one x)
    rw [this, QuotientGroup.mk_one]
  have h2 : (xb : Bo ⧸ U) ^ Nat.card (torus F) = 1 := by
    rw [← hQ]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime (p ^ k) (Nat.card (torus F)) := by
    have hc := coprime_card_unip_torus hF2 (F := F)
    rw [psl2UpperUnipotentSubgroup_card, hFcard] at hc
    rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf
      rw [pow_zero] at hFcard
      exfalso
      have : (1 : ℕ) < Nat.card F := Finite.one_lt_card
      omega
    · exact Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_left (dvd_pow_self p hf.ne') hc)
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hcop, pow_one] at h3
  have h4 : xb ∈ U := (QuotientGroup.eq_one_iff (N := U) xb).mp h3
  exact h4

theorem odd_card_borel [Finite F] (hF2 : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) :
    Odd (Nat.card (unip F ⊔ torus F : Subgroup PSL(2, F))) := by
  rw [← stab_infinity]
  change Odd (Nat.card (psl2Borel F))
  rw [card_borel hF2, psl2UpperUnipotentSubgroup_card]
  have h2 := card_torus hF2 (F := F)
  apply Nat.odd_mul.mpr
  constructor
  · rw [Nat.odd_iff]; omega
  · rw [Nat.odd_iff]; omega

end PSL2

theorem exists_fixed_ne_one {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {R P : Subgroup G} (hR : IsPGroup p R) (hP : IsPGroup p P) (hP1 : P ≠ ⊥)
    (hRP : R ≤ Subgroup.normalizer (P : Set G)) :
    ∃ y ∈ P, y ≠ 1 ∧ ∀ r ∈ R, r * y * r⁻¹ = y := by
  let := JT.conjAct R P hRP
  have hmod := hR.card_modEq_card_fixedPoints P
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hP1
    rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq P hk
  rw [hk] at hmod
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints R P) := by
    have := (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr
      (dvd_pow_self p hk0))))
    exact this
  have hone : (1 : P) ∈ MulAction.fixedPoints R P := fun r => smul_one r
  have : Nonempty (MulAction.fixedPoints R P) := ⟨⟨1, hone⟩⟩
  have h2 : 1 < Nat.card (MulAction.fixedPoints R P) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hdvd)
  have : Nontrivial (MulAction.fixedPoints R P) := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (⟨1, hone⟩ : MulAction.fixedPoints R P)
  refine ⟨y, y.2, fun h => hy1 (Subtype.ext (Subtype.ext h)), fun r hr => ?_⟩
  have hy' : ∀ r : R, r • y = y := hy
  have := hy' ⟨r, hr⟩
  exact congrArg Subtype.val this

end Borel5

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

open Borel5

@[expose] noncomputable def img (s : Std G) (h : PSL(2, GaloisField s.p s.f))
    (H : Subgroup PSL(2, GaloisField s.p s.f)) : Subgroup G :=
  (H.map (MulAut.conj h).toMonoidHom).map (psl2Emb s.iso)

theorem mem_img {h : PSL(2, GaloisField s.p s.f)} {H : Subgroup PSL(2, GaloisField s.p s.f)}
    {x : G} : x ∈ img s h H ↔ ∃ y ∈ H, x = psl2Emb s.iso (h * y * h⁻¹) := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩

theorem img_le_K (h : PSL(2, GaloisField s.p s.f)) (H : Subgroup PSL(2, GaloisField s.p s.f)) :
    img s h H ≤ s.K :=
  PSL2Sub.map_le s.iso _

theorem img_sup (h : PSL(2, GaloisField s.p s.f)) (H H' : Subgroup PSL(2, GaloisField s.p s.f)) :
    img s h (H ⊔ H') = img s h H ⊔ img s h H' := by
  rw [img, img, img, Subgroup.map_sup, Subgroup.map_sup]

theorem card_img (h : PSL(2, GaloisField s.p s.f)) (H : Subgroup PSL(2, GaloisField s.p s.f)) :
    Nat.card (img s h H) = Nat.card H := by
  rw [img, Subgroup.card_map_of_injective (PSL2Sub.emb_injective s.iso),
    Subgroup.card_map_of_injective (MulAut.conj h).injective]

@[expose] noncomputable def pull (s : Std G) (h : PSL(2, GaloisField s.p s.f)) (V : Subgroup G) :
    Subgroup PSL(2, GaloisField s.p s.f) :=
  (V.comap (psl2Emb s.iso)).map (MulAut.conj h⁻¹).toMonoidHom

theorem img_pull (h : PSL(2, GaloisField s.p s.f)) {V : Subgroup G} (hV : V ≤ s.K) :
    img s h (pull s h V) = V := by
  have hid : ((V.comap (psl2Emb s.iso)).map (MulAut.conj h⁻¹).toMonoidHom).map
      (MulAut.conj h).toMonoidHom = V.comap (psl2Emb s.iso) := by
    rw [Subgroup.map_map]
    have : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  rw [img, pull, hid]
  exact PSL2Sub.map_comap_emb s.iso hV

theorem pull_le_iff (h : PSL(2, GaloisField s.p s.f)) {V : Subgroup G} (hV : V ≤ s.K)
    (H : Subgroup PSL(2, GaloisField s.p s.f)) : pull s h V ≤ H ↔ V ≤ img s h H := by
  constructor
  · intro hle
    rw [← img_pull h hV]
    exact Subgroup.map_mono (Subgroup.map_mono hle)
  · intro hle y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzV : psl2Emb s.iso z ∈ V := hz
    obtain ⟨w, hw, hwz⟩ := mem_img.mp (hle hzV)
    have := PSL2Sub.emb_injective s.iso hwz
    rw [this]
    simpa [MulAut.conj_apply, mul_assoc] using hw

theorem irred {h : PSL(2, GaloisField s.p s.f)} (hB : f5.B = img s h (torus _))
    {V : Subgroup G} (hV : V ≤ img s h (unip _))
    (hVB : ∀ b ∈ f5.B, ∀ v ∈ V, b * v * b⁻¹ ∈ V) : V = ⊥ ∨ V = img s h (unip _) := by
  have hVK : V ≤ s.K := hV.trans (img_le_K h _)
  have hle : pull s h V ≤ unip _ := (pull_le_iff h hVK _).mpr hV
  have hinv : ∀ a : (GaloisField s.p s.f)ˣ, ∀ v ∈ pull s h V,
      torusHom _ a * v * (torusHom _ a)⁻¹ ∈ pull s h V := by
    intro a v hv
    obtain ⟨y, hy, rfl⟩ := hv
    have hyV : psl2Emb s.iso y ∈ V := hy
    set b := psl2Emb s.iso (h * torusHom _ a * h⁻¹)
    have hbB : b ∈ f5.B := by rw [hB]; exact mem_img.mpr ⟨_, ⟨a, rfl⟩, rfl⟩
    have h1 := hVB b hbB _ hyV
    refine ⟨(h * torusHom _ a * h⁻¹) * y * (h * torusHom _ a * h⁻¹)⁻¹, ?_, ?_⟩
    · change psl2Emb s.iso _ ∈ V
      rw [map_mul, map_mul, map_inv]
      exact h1
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rcases unip_eq_bot_or_eq_top hle hinv with h0 | h0
  · left
    rw [← img_pull h hVK, h0, img, Subgroup.map_bot, Subgroup.map_bot]
  · right
    rw [← img_pull h hVK, h0]

theorem le_pull_iff (h : PSL(2, GaloisField s.p s.f)) {V : Subgroup G} (hV : V ≤ s.K)
    (H : Subgroup PSL(2, GaloisField s.p s.f)) : H ≤ pull s h V ↔ img s h H ≤ V := by
  constructor
  · intro hle
    rw [← img_pull h hV (V := V)]
    exact Subgroup.map_mono (Subgroup.map_mono hle)
  · intro hle y hy
    have : psl2Emb s.iso (h * y * h⁻¹) ∈ V := hle (mem_img.mpr ⟨y, hy, rfl⟩)
    exact ⟨h * y * h⁻¹, this, by simp [mul_assoc]⟩

theorem card_pull (h : PSL(2, GaloisField s.p s.f)) {V : Subgroup G} (hV : V ≤ s.K) :
    Nat.card (pull s h V) = Nat.card V := by
  rw [pull, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective,
    PSL2Sub.card_comap_emb s.iso hV]

theorem img_map_conj (h k : PSL(2, GaloisField s.p s.f))
    (H : Subgroup PSL(2, GaloisField s.p s.f)) :
    img s h (H.map (MulAut.conj k).toMonoidHom) = img s (h * k) H := by
  ext x
  rw [mem_img, mem_img]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simp [mul_assoc]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨k * z * k⁻¹, ⟨z, hz, rfl⟩, by simp [mul_assoc]⟩

theorem img_unipOpp (g : PSL(2, GaloisField s.p s.f)) :
    img s g (unipOpp _) = img s (g * weyl _) (unip _) := img_map_conj g _ _

theorem img_torus_weyl (g : PSL(2, GaloisField s.p s.f)) :
    img s (g * weyl _) (torus _) = img s g (torus _) := by
  rw [← img_map_conj, torus_conj_weyl]

theorem mem_normalizer_pull (h : PSL(2, GaloisField s.p s.f)) {V : Subgroup G} (hV : V ≤ s.K)
    {y : PSL(2, GaloisField s.p s.f)}
    (hy : psl2Emb s.iso y ∈ Subgroup.normalizer (V : Set G)) :
    h⁻¹ * y * h ∈ Subgroup.normalizer (pull s h V : Set PSL(2, GaloisField s.p s.f)) := by
  have hι := PSL2Sub.emb_injective s.iso
  have h1 : y ∈ Subgroup.normalizer ((V.comap (psl2Emb s.iso)) : Set PSL(2, _)) := by
    have hN : psl2Emb s.iso y ∈ (psl2Emb s.iso).range ⊓
        Subgroup.normalizer (((V.comap (psl2Emb s.iso)).map (psl2Emb s.iso) : Subgroup G) :
          Set G) := by
      rw [PSL2Sub.map_comap_emb s.iso hV]
      exact ⟨⟨y, rfl⟩, hy⟩
    rw [← JT.map_normalizer_of_injective _ hι] at hN
    exact (Subgroup.mem_map_iff_mem hι).mp hN
  have h2 := Subgroup.mem_map_of_mem (MulAut.conj h⁻¹).toMonoidHom h1
  rw [Subgroup.map_equiv_normalizer_eq] at h2
  have e : (MulAut.conj h⁻¹).toMonoidHom y = h⁻¹ * y * h := by simp
  rw [e] at h2
  exact h2

theorem le_of_odd (hp : s.p = 3) {g : PSL(2, GaloisField s.p s.f)}
    (hB : f5.B = img s g (torus _)) {M : Subgroup G} (hMK : M ≤ s.K) (hBM : f5.B ≤ M)
    (hodd : Odd (Nat.card M)) :
    M ≤ img s g (unip _ ⊔ torus _) ∨ M ≤ img s (g * weyl _) (unip _ ⊔ torus _) := by
  have hFcard : Nat.card (GaloisField s.p s.f) = s.p ^ s.f := GaloisField.card s.p s.f s.f_pos.ne'
  have h5 : 5 ≤ Nat.card (GaloisField s.p s.f) := by
    rw [hFcard]
    have := s.three_lt_q
    rw [Hyp.q] at this
    have h4 := s.q_mod_four hp
    rw [Hyp.q] at h4
    omega
  have hT : torus _ ≤ pull s g M := (le_pull_iff g hMK _).mpr (hB ▸ hBM)
  have hodd' : Odd (Nat.card (pull s g M)) := by rw [card_pull g hMK]; exact hodd
  rcases le_borel_of_odd hFcard s.odd_p h5 hT hodd' with h1 | h1
  · left
    exact (pull_le_iff g hMK _).mp h1
  · right
    rw [← img_map_conj, Subgroup.map_sup, torus_conj_weyl]
    exact (pull_le_iff g hMK _).mp h1

theorem normalizer_le (hp : s.p = 3) {g : PSL(2, GaloisField s.p s.f)}
    (hB : f5.B = img s g (torus _)) {P : Subgroup G} (hPK : P ≤ s.K)
    (hP3 : IsPGroup 3 P) (hP1 : P ≠ ⊥) (hBP : f5.B ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ⊓ s.K ≤ img s g (unip _ ⊔ torus _) ∨
      Subgroup.normalizer (P : Set G) ⊓ s.K ≤ img s (g * weyl _) (unip _ ⊔ torus _) := by
  have : Fact s.p.Prime := inferInstance
  have hFcard : Nat.card (GaloisField s.p s.f) = s.p ^ s.f := GaloisField.card s.p s.f s.f_pos.ne'
  set P' := pull s g P
  have hP'3 : IsPGroup s.p P' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP3
    apply IsPGroup.of_card (n := n)
    rw [card_pull g hPK, hn, hp]
  have hP'1 : P' ≠ ⊥ := by
    intro h0
    apply hP1
    have := card_pull g hPK (V := P)
    change Nat.card P' = _ at this
    rw [h0, Subgroup.card_bot] at this
    exact Subgroup.eq_bot_of_card_eq P this.symm
  have hTN : ∀ a : (GaloisField s.p s.f)ˣ,
      torusHom _ a ∈ Subgroup.normalizer (P' : Set PSL(2, GaloisField s.p s.f)) := by
    intro a
    have hb : psl2Emb s.iso (g * torusHom _ a * g⁻¹) ∈ f5.B := by
      rw [hB]
      exact mem_img.mpr ⟨_, ⟨a, rfl⟩, rfl⟩
    have := mem_normalizer_pull g hPK (hBP hb)
    simpa [mul_assoc] using this
  obtain ⟨x, hx⟩ := exists_fixed_of_isPGroup hFcard hP'3 hP'1
  have hF2 : ringChar (GaloisField s.p s.f) ≠ 2 := by
    rw [ringChar.eq (GaloisField s.p s.f) s.p]
    exact s.p_ne_two
  have hTc := card_torus hF2 (F := GaloisField s.p s.f)
  have hq := s.three_lt_q
  rw [Hyp.q] at hq
  have h4 := s.q_mod_four hp
  rw [Hyp.q] at h4
  obtain ⟨t, ht, ht1⟩ := (Subgroup.bot_or_exists_ne_one (torus (GaloisField s.p s.f))).resolve_left
    (by
      intro h0
      rw [h0, Subgroup.card_bot, hFcard] at hTc
      omega)
  obtain ⟨a, rfl⟩ := ht
  have ha : ((a : GaloisField s.p s.f)) ^ 2 ≠ 1 := fun h => ht1 ((torusHom_eq_one_iff a).mpr h)
  have hmem : ∀ z ∈ Subgroup.normalizer (P : Set G) ⊓ s.K,
      ∃ y, z = psl2Emb s.iso (g * y * g⁻¹) ∧
        y ∈ Subgroup.normalizer (P' : Set PSL(2, GaloisField s.p s.f)) := by
    intro z hz
    obtain ⟨hzN, hzK⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq s.iso hzK
    refine ⟨g⁻¹ * y * g, by simp [mul_assoc], mem_normalizer_pull g hPK hzN⟩
  rcases eq_of_torus_fixed ha (hx _ (hTN a)) with rfl | rfl
  · left
    intro z hz
    obtain ⟨y, rfl, hy⟩ := hmem z hz
    refine mem_img.mpr ⟨y, ?_, rfl⟩
    rw [← stab_infinity]
    exact hx y hy
  · right
    rw [← img_map_conj, Subgroup.map_sup, torus_conj_weyl]
    intro z hz
    obtain ⟨y, rfl, hy⟩ := hmem z hz
    refine mem_img.mpr ⟨y, ?_, rfl⟩
    change y ∈ unipOpp _ ⊔ torus _
    rw [← stab_zero]
    exact hx y hy

theorem odd_card_img_borel (hp : s.p = 3) (h : PSL(2, GaloisField s.p s.f)) :
    Odd (Nat.card (img s h (unip _ ⊔ torus _))) := by
  rw [card_img]
  have hF2 : ringChar (GaloisField s.p s.f) ≠ 2 := by
    rw [ringChar.eq (GaloisField s.p s.f) s.p]
    exact s.p_ne_two
  apply odd_card_borel hF2
  rw [GaloisField.card s.p s.f s.f_pos.ne']
  exact s.q_mod_four hp

theorem le_img_unip_of_isPGroup (hp : s.p = 3) (h : PSL(2, GaloisField s.p s.f))
    {X : Subgroup G} (hX : IsPGroup 3 X) (hXB : X ≤ img s h (unip _ ⊔ torus _)) :
    X ≤ img s h (unip _) := by
  have hXK : X ≤ s.K := hXB.trans (img_le_K h _)
  have hF2 : ringChar (GaloisField s.p s.f) ≠ 2 := by
    rw [ringChar.eq (GaloisField s.p s.f) s.p]
    exact s.p_ne_two
  have : Fact s.p.Prime := inferInstance
  have hX' : IsPGroup s.p (pull s h X) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
    apply IsPGroup.of_card (n := n)
    rw [card_pull h hXK, hn, hp]
  have h1 := le_unip_of_isPGroup (GaloisField.card s.p s.f s.f_pos.ne') hF2 hX'
    ((pull_le_iff h hXK _).mpr hXB)
  exact (pull_le_iff h hXK _).mp h1

end Frame5

end CFSG.Walter.W67
