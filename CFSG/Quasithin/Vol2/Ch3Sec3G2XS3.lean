module

public import CFSG.Quasithin.Vol2.Ch3Sec3G2Rho
public import CFSG.Quasithin.Vol2.Ch3Sec3G2Data
public import CFSG.Quasithin.Background.S1549DL3N

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

namespace G2XS3

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.H13.G2Dat CFSG.Quasithin.H13.Par32
open scoped commutatorElement

variable {G : Type} [Group G]

section Par

variable {Γ : Type} [Group Γ] {T L : Subgroup G} (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ)
  (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))

theorem pre_isPGroup' [Finite G] {Q : Subgroup Γ} (hQ : IsPGroup 2 ↥Q)
    (hK : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 → g ∈ qL L T) :
    IsPGroup 2 ↥(pre ρ hLTN Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  rintro ⟨g, hg⟩
  obtain ⟨hgLT, hgQ⟩ := (mem_pre ρ hLTN).mp hg
  obtain ⟨k, hk⟩ := hQ ⟨_, hgQ⟩
  have hk' : ρ ⟨g, hLTN hgLT⟩ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hgk : g ^ 2 ^ k ∈ L ⊔ T := (L ⊔ T).pow_mem hgLT _
  have hsq : g ^ 2 ^ k ∈ qL L T := by
    apply hK _ hgk
    have e : (⟨g ^ 2 ^ k, hLTN hgk⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hLTN hgLT⟩ ^ 2 ^ k := rfl
    rw [e, map_pow]
    exact hk'
  obtain ⟨m, hm⟩ := hQ2 ⟨_, hsq⟩
  have hm' : (g ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  refine ⟨k + m, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
  exact hm'

theorem parabolic_gen' [Finite G] [Finite Γ]
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hK : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 → g ∈ qL L T)
    {p r : Subgroup Γ}
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ ∈ p) (hrp : r ≤ p)
    (hpr : p ≤ Subgroup.normalizer (r : Set Γ)) (hr2 : IsPGroup 2 ↥r)
    (h6 : Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ p) =
        6 * Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ r) ∨
      Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ p) =
        3 * Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ r))
    {ℓa ℓb : G} (hℓa : ℓa ∈ L) (hℓb : ℓb ∈ L)
    (hap : ρ ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩ ∈ p)
    (hbp : ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩ ∈ p)
    (hab : (ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩ * ρ ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩)⁻¹ *
      (ρ ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩ * ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩) ∉ r) :
    oTwoUpper (pre ρ hLTN p) ⊔ T = pre ρ hLTN p ∧
      Nonempty (↥(pre ρ hLTN p) ⧸ CFSG.pCore 2 ↥(pre ρ hLTN p) ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 (pre ρ hLTN p) = pre ρ hLTN r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pre ρ hLTN p with hPdef
  set R := pre ρ hLTN r with hRdef
  have hTP : T ≤ P := fun t ht =>
    (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_right ht, hρT t ht⟩
  have hRP : R ≤ P := pre_mono ρ hLTN hrp
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := pre_le_normalizer ρ hLTN hpr
  have hR2 : IsPGroup 2 ↥R := pre_isPGroup' ρ hLTN hr2 hK
  have hTsyl : IsSylowTwoOf T P :=
    ⟨hTP, hT2, fun h2 => hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le hTP))⟩
  have hNn : (R.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hℓaP : ℓa ∈ P := (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓa, hap⟩
  have hℓbP : ℓb ∈ P := (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓb, hbp⟩
  have hne : (QuotientGroup.mk ⟨ℓa, hℓaP⟩ : ↥P ⧸ R.subgroupOf P) * QuotientGroup.mk ⟨ℓb, hℓbP⟩ ≠
      QuotientGroup.mk ⟨ℓb, hℓbP⟩ * QuotientGroup.mk ⟨ℓa, hℓaP⟩ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    intro h
    have h1 := QuotientGroup.eq.mp h.symm
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨hm, hmr⟩ := (mem_pre ρ hLTN).mp h1
    apply hab
    have e : (⟨_, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩ * ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩)⁻¹ *
          (⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩ *
            ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩) := rfl
    rw [e, map_mul, map_inv, map_mul, map_mul] at hmr
    exact hmr
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  have hrel : ∀ k, Nat.card ↥P = k * Nat.card ↥R → R.relIndex P = k := by
    intro k hk
    have := Subgroup.relIndex_mul_card (H := R) (K := P)
    rw [inf_of_le_left hRP, hk] at this
    exact Nat.eq_of_mul_eq_mul_right hRpos (by rw [this])
  have hQ6 : Nat.card (↥P ⧸ R.subgroupOf P) = 6 := by
    rcases h6 with h6 | h3
    · apply hrel 6
      rw [card_pre ρ hLTN p, card_pre ρ hLTN r, h6]
      ring
    · exfalso
      have h3' : Nat.card (↥P ⧸ R.subgroupOf P) = 3 := by
        apply hrel 3
        rw [card_pre ρ hLTN p, card_pre ρ hLTN r, h3]
        ring
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic (↥P ⧸ R.subgroupOf P) := isCyclic_of_prime_card h3'
      exact hne (hcyc.commGroup.mul_comm _ _)
  obtain ⟨ψ⟩ := CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hQ6 _ _ hne
  have hRp : IsPGroup 2 ↥(R.subgroupOf P) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hR2 ⟨x, hx⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hcore : ∀ C : Subgroup ↥P, C.Normal → IsPGroup 2 ↥C → C ≤ R.subgroupOf P := by
    intro C hCn hCp
    have h1 : C.map (QuotientGroup.mk' (R.subgroupOf P)) = ⊥ :=
      CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot ψ _
        (hCn.map _ (QuotientGroup.mk'_surjective _)) (hCp.map _)
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact h1
  have hcore1 : CFSG.pCore 2 ↥P = R.subgroupOf P :=
    le_antisymm (hcore _ CFSG.pCore_normal CFSG.pCore_isPGroup)
      (le_sSup ⟨hNn, hRp⟩)
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hcore1).trans ψ⟩, ?_⟩
  · rw [sup_comm, ← CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper]
    exact CFSG.Quasithin.sup_twoResidual_eq hTsyl
  · rw [pCoreOf, hcore1]
    exact Subgroup.map_subgroupOf_eq_of_le hRP

end Par

section Sub

@[expose] def r₀ : Subgroup ↥(quasithinG2 (ZMod 2)) where
  carrier := {g | ∃ k < 32, sEltG (2 * k) = g}
  mul_mem' := by
    rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
    obtain ⟨m, hm, e⟩ := r₀_checks.1 k hk l hl
    refine ⟨m, hm, eq_of_code ?_⟩
    rw [matCode_mulG, matCode_sEltG (by omega), matCode_sEltG (by omega),
      matCode_sEltG (by omega)]
    exact e.symm
  one_mem' := ⟨0, by norm_num, Subtype.ext sElt_zero⟩
  inv_mem' := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨l, hl, e⟩ := r₀_checks.2.1 k hk
    refine ⟨l, hl, (inv_eq_of_mul_eq_one_right (eq_of_code ?_)).symm⟩
    rw [matCode_mulG, matCode_sEltG (by omega), matCode_sEltG (by omega), e]
    exact matCode_one.symm

theorem r₀_le : r₀ ≤ sSubG := by
  rintro _ ⟨k, hk, rfl⟩
  exact mem_sSubG.mpr ⟨2 * k, by omega, rfl⟩

theorem isPGroup_sSubG : IsPGroup 2 ↥sSubG :=
  IsPGroup.of_card (n := 6) (by rw [card_sSubG]; norm_num)

theorem isPGroup_r₀ : IsPGroup 2 ↥r₀ := isPGroup_sSubG.to_le r₀_le

@[expose] def pw (w : ModQ) : Subgroup ↥(quasithinG2 (ZMod 2)) where
  carrier := {g | g2QAct (ZMod 2) g w = w}
  mul_mem' := by
    intro a b ha hb
    show g2QAct (ZMod 2) (a * b) w = w
    rw [map_mul, MulAut.mul_apply]
    rw [show g2QAct (ZMod 2) b w = w from hb]
    exact ha
  one_mem' := by
    show g2QAct (ZMod 2) 1 w = w
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    show g2QAct (ZMod 2) a⁻¹ w = w
    rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact (show g2QAct (ZMod 2) a w = w from ha).symm

theorem mem8 : (8 : ℕ) ∈ o0Codes := by decide

theorem mem2 : (2 : ℕ) ∈ o0Codes := by decide

@[expose] def w₀ : ModQ := codeQ ⟨8, mem8⟩

theorem fix_of_fixQB {g : ↥(quasithinG2 (ZMod 2))} {m : List ℕ} (hm : matCode g.1 = m)
    {c : O0C} (h : fixQB m c.1 = true) : g2QAct (ZMod 2) g (codeQ c) = codeQ c := by
  rw [g2QAct_codeQ, codeQ_eq_iff]
  have hm' : mact m c.1 ∈ o0Codes := by
    rw [← hm]
    exact (o0Act g c).2
  have h1 := (fixQB_iff m c.2 hm').1 h
  change c.1 = mact (matCode g.1) c.1 ∨ c.1 = mact (matCode g.1) c.1 ^^^ 129
  rw [hm]
  rcases h1 with h1 | h1
  · exact Or.inl h1.symm
  · right
    rw [h1, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem sSubG_le_pw : sSubG ≤ pw w₀ := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.mp hg
  exact fix_of_fixQB (matCode_sEltG hi) (fix_w₀.1 i hi)

theorem b₀_mem_pw : b₀ ∈ pw w₀ := fix_of_fixQB matCode_b₀ fix_w₀.2

theorem w₀_ne_one : w₀ ≠ 1 := by
  intro h
  have := (codeQ_eq_one_iff ⟨8, mem8⟩).mp h
  simp at this

theorem sSubG_le_normalizer : sSubG ≤ Subgroup.normalizer (r₀ : Set ↥(quasithinG2 (ZMod 2))) := by
  have key : ∀ g ∈ sSubG, ∀ x ∈ r₀, g * x * g⁻¹ ∈ r₀ := by
    intro g hg x hx
    obtain ⟨i, hi, rfl⟩ := mem_sSubG.mp hg
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, e⟩ := r₀_checks.2.2.1 i hi k hk
    have e2 : sEltG i * sEltG (2 * k) = sEltG (2 * l) * sEltG i := by
      apply eq_of_code
      rw [matCode_mulG, matCode_mulG, matCode_sEltG hi, matCode_sEltG (by omega),
        matCode_sEltG (by omega)]
      exact e
    refine ⟨l, hl, ?_⟩
    rw [e2]
    group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (sSubG.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem b₀_mem_normalizer : b₀ ∈ Subgroup.normalizer (r₀ : Set ↥(quasithinG2 (ZMod 2))) := by
  have key : ∀ x ∈ r₀, b₀ * x * b₀⁻¹ ∈ r₀ := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, e⟩ := r₀_checks.2.2.2 k hk
    have e2 : b₀ * sEltG (2 * k) = sEltG (2 * l) * b₀ := by
      apply eq_of_code
      rw [matCode_mulG, matCode_mulG, matCode_b₀, matCode_sEltG (by omega),
        matCode_sEltG (by omega)]
      exact e
    refine ⟨l, hl, ?_⟩
    rw [e2]
    group
  have hb3 : b₀ * (b₀ * b₀) = 1 := by
    apply eq_of_code
    rw [matCode_mulG, matCode_mulG, matCode_b₀]
    rw [b₀_checks.1]
    exact matCode_one.symm
  have hbi : b₀⁻¹ = b₀ * b₀ := inv_eq_of_mul_eq_one_right hb3
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key x
  · intro hx
    have h1 := key _ (key _ hx)
    have e : b₀ * (b₀ * (b₀ * x * b₀⁻¹) * b₀⁻¹) * b₀⁻¹ = x := by
      have h3 : b₀ * b₀ * b₀ = 1 := by rw [mul_assoc]; exact hb3
      calc b₀ * (b₀ * (b₀ * x * b₀⁻¹) * b₀⁻¹) * b₀⁻¹ =
          (b₀ * b₀ * b₀) * x * (b₀ * b₀ * b₀)⁻¹ := by group
        _ = x := by rw [h3]; group
    rwa [e] at h1

end Sub

section Orbit

theorem exists_derived_apply (q : ModQ) (hq : q ≠ 1) :
    ∃ g ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) g (codeQ ⟨2, mem2⟩) = q := by
  obtain ⟨c, rfl⟩ := codeQ_surjective q
  have hc : c.1 ≠ 0 ∧ c.1 ≠ 129 := by
    have h1 : ¬ (c.1 = 0 ∨ c.1 = 129) := fun h1 => hq ((codeQ_eq_one_iff c).mpr h1)
    push Not at h1
    exact h1
  rcases singular_or c.1 c.2 hc.1 hc.2 with ⟨hn, h0, h1⟩ | ⟨hn, h0, h1⟩
  · obtain ⟨hw1, hw2⟩ := singular_word c.2 hn h0 h1
    exact ⟨wordGG _, wordGG_mem_derived _, codeQ_word_e hw2 c.2 mem2 hw1⟩
  · have h129 : (129 : ℕ) ∈ o0Codes := by decide
    let c' : O0C := o0Xor c ⟨129, h129⟩
    have hcc : codeQ c' = codeQ c := (codeQ_eq_iff c' c).mpr (Or.inr (by
      show c.1 = (c.1 ^^^ 129) ^^^ 129
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]))
    obtain ⟨hw1, hw2⟩ := singular_word c'.2 hn h0 h1
    exact ⟨wordGG _, wordGG_mem_derived _, (codeQ_word_e hw2 c'.2 mem2 hw1).trans hcc⟩

theorem card_inf_pw_mul (H : Subgroup ↥(quasithinG2 (ZMod 2))) (hH : g2Derived (ZMod 2) ≤ H) :
    Nat.card ↥(H ⊓ pw w₀) * 63 = Nat.card ↥H := by
  classical
  let _ : MulAction ↥H ModQ := MulAction.compHom ModQ ((g2QAct (ZMod 2)).comp H.subtype)
  have hsmul : ∀ (h : ↥H) (q : ModQ), h • q = g2QAct (ZMod 2) h q := fun _ _ => rfl
  have horb : MulAction.orbit ↥H w₀ = {q | q ≠ 1} := by
    ext q
    simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, rfl⟩
      rw [hsmul]
      intro h1
      apply w₀_ne_one
      have := congrArg (g2QAct (ZMod 2) (h : ↥(quasithinG2 (ZMod 2))))⁻¹ h1
      simpa using this
    · intro hq
      obtain ⟨g₁, hg₁, e₁⟩ := exists_derived_apply q hq
      obtain ⟨g₀, hg₀, e₀⟩ := exists_derived_apply w₀ w₀_ne_one
      refine ⟨⟨g₁ * g₀⁻¹, hH (Subgroup.mul_mem _ hg₁ (Subgroup.inv_mem _ hg₀))⟩, ?_⟩
      rw [hsmul]
      show g2QAct (ZMod 2) (g₁ * g₀⁻¹) w₀ = q
      rw [map_mul, MulAut.mul_apply, map_inv, ← e₀, MulAut.inv_apply, MulEquiv.symm_apply_apply,
        e₁]
  have hcard_orb : (MulAction.orbit ↥H w₀).ncard = 63 := by
    rw [horb, ← Nat.card_coe_set_eq]
    have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
    have := Fintype.ofFinite ModQ
    have h1 : Nat.card ↥{q : ModQ | q ≠ 1} + 1 = Nat.card ModQ := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      rw [show (Fintype.card ↥{q : ModQ | q ≠ 1}) = Fintype.card {q : ModQ // q ≠ 1} from rfl,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have : 0 < Fintype.card ModQ := Fintype.card_pos
      omega
    rw [card_ModQ] at h1
    omega
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥H w₀)
  rw [MulAction.index_stabilizer, hcard_orb] at h1
  have h2 : Nat.card ↥(MulAction.stabilizer ↥H w₀) = Nat.card ↥(H ⊓ pw w₀) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.1, x.1.2,
      (show g2QAct (ZMod 2) x.1.1 w₀ = w₀ from x.2)⟩) ⟨?_, ?_⟩)
    · intro x y hxy
      have h3 := congrArg (fun z : ↥(H ⊓ pw w₀) => (z : ↥(quasithinG2 (ZMod 2)))) hxy
      exact Subtype.ext (Subtype.ext h3)
    · rintro ⟨g, hgH, hgp⟩
      exact ⟨⟨⟨g, hgH⟩, (show (⟨g, hgH⟩ : ↥H) • w₀ = w₀ from hgp)⟩, rfl⟩
  rw [← h2]
  exact h1

theorem card_pw : Nat.card ↥(pw w₀) = 192 := by
  have h1 := card_inf_pw_mul ⊤ le_top
  rw [top_inf_eq, Subgroup.card_top, card_g2Two] at h1
  omega

theorem pw_le_normalizer : pw w₀ ≤ Subgroup.normalizer (r₀ : Set ↥(quasithinG2 (ZMod 2))) := by
  have hle : sSubG ⊔ Subgroup.zpowers b₀ ≤ pw w₀ :=
    sup_le sSubG_le_pw (Subgroup.zpowers_le.mpr b₀_mem_pw)
  have hN : sSubG ⊔ Subgroup.zpowers b₀ ≤ Subgroup.normalizer (r₀ : Set ↥(quasithinG2 (ZMod 2))) :=
    sup_le sSubG_le_normalizer (Subgroup.zpowers_le.mpr b₀_mem_normalizer)
  have hb3 : orderOf b₀ = 3 := by
    have hb : b₀ ^ 3 = 1 := by
      apply eq_of_code
      rw [pow_three, matCode_mulG, matCode_mulG, matCode_b₀, b₀_checks.1]
      exact matCode_one.symm
    refine orderOf_eq_prime hb ?_
    intro h1
    apply b₀_checks.2.1
    rw [← matCode_b₀, h1]
    exact matCode_one
  have h64 : 64 ∣ Nat.card ↥(sSubG ⊔ Subgroup.zpowers b₀) := by
    rw [← card_sSubG]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card ↥(sSubG ⊔ Subgroup.zpowers b₀) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers b₀ ≤ sSubG ⊔ _)
    rwa [Nat.card_zpowers, hb3] at this
  have h192 : 192 ∣ Nat.card ↥(sSubG ⊔ Subgroup.zpowers b₀) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h3
  have hle' : Nat.card ↥(pw w₀) ≤ Nat.card ↥(sSubG ⊔ Subgroup.zpowers b₀) := by
    rw [card_pw]
    exact Nat.le_of_dvd Nat.card_pos h192
  rw [← Subgroup.eq_of_le_of_card_ge hle hle']
  exact hN

end Orbit

section XS3

theorem card_g2Derived :
    Nat.card ↥(g2Derived (ZMod 2)) = 6048 := by
  rw [g2Derived, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Subgroup.commutator_le_self _ : ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≤ _)).toEquiv]
  exact CFSG.Quasithin.S1549D.card_commutator_quasithinG2_two (Nat.card_zmod 2)

theorem card_r₀ : Nat.card ↥r₀ = 32 := by
  have hbij : Function.Bijective fun k : Fin 32 =>
      (⟨sEltG (2 * k.1), ⟨k.1, k.2, rfl⟩⟩ : ↥r₀) := by
    constructor
    · intro a b h
      have h1 := sEltG_injective (by omega) (by omega) (congrArg Subtype.val h)
      exact Fin.ext (by omega)
    · rintro ⟨g, k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem eq_of_le_of_odd {Γ : Type*} [Group Γ] [Finite Γ] {P Q : Subgroup Γ} (hPQ : P ≤ Q)
    (hQ : IsPGroup 2 ↥Q) (hP : ¬ 2 ∣ P.index) : P = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm hPQ
  have h1 : ¬ 2 ∣ P.relIndex Q := fun h2 => hP (h2.trans (Subgroup.relIndex_dvd_index_of_le hPQ))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have h2 : P.relIndex Q ∣ 2 ^ n := by
    rw [← hn]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := P) (K := Q))
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hm0 : m = 0 := by
    by_contra hm0
    exact h1 (hm' ▸ dvd_pow_self 2 hm0)
  rw [hm0, pow_zero] at hm'
  exact Subgroup.relIndex_eq_one.mp hm'

theorem cZ_eq [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2))) (β : ↥(blockU L) →* ModQ)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hρL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ g2Derived (ZMod 2))
    (hρL' : ∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sSubG) :
    oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
      oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) (pw w₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have : Finite ↥(quasithinG2 (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_g2Two]; norm_num)
  have hsylL : IsSylowTwoOf (T ⊓ L) L := by
    have hTsyl : IsSylowTwoOf T (L ⊔ T) :=
      ⟨le_sup_right, hT2, fun h2 =>
        hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    exact A4.isSylowTwoOf_inf_normal hTsyl le_sup_left hLTN
  have hSD : ∀ y ∈ sSubG, y ∈ g2Derived (ZMod 2) → ∃ t ∈ T, ∃ ht : t ∈ L,
      ρ ⟨t, Subgroup.le_normalizer ht⟩ = y := by
    let ρL : ↥L →* ↥(g2Derived (ZMod 2)) :=
      (ρ.comp (Subgroup.inclusion Subgroup.le_normalizer)).codRestrict _ (fun ℓ => hρL ℓ.1 ℓ.2)
    have hρLs : Function.Surjective ρL := by
      intro y
      obtain ⟨ℓ, hℓ, e⟩ := hρL' y.1 y.2
      exact ⟨⟨ℓ, hℓ⟩, Subtype.ext e⟩
    have hPQ : ((T ⊓ L).subgroupOf L).map ρL ≤ sSubG.subgroupOf (g2Derived (ZMod 2)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hρT x.1 (Subgroup.mem_subgroupOf.mp hx).1)
    have hQ2 : IsPGroup 2 ↥(sSubG.subgroupOf (g2Derived (ZMod 2))) :=
      isPGroup_sSubG.comap_of_injective (g2Derived (ZMod 2)).subtype
        (g2Derived (ZMod 2)).subtype_injective
    have hPidx : ¬ 2 ∣ (((T ⊓ L).subgroupOf L).map ρL).index := fun h2 => hsylL.2.2
      (h2.trans (Subgroup.index_map_dvd _ hρLs))
    have hPQeq := eq_of_le_of_odd hPQ hQ2 hPidx
    intro y hyS hyD
    have hyQ : (⟨y, hyD⟩ : ↥(g2Derived (ZMod 2))) ∈ ((T ⊓ L).subgroupOf L).map ρL := by
      rw [hPQeq]
      exact Subgroup.mem_subgroupOf.mpr hyS
    obtain ⟨x, hx, e⟩ := hyQ
    exact ⟨x.1, (Subgroup.mem_subgroupOf.mp hx).1, x.2, congrArg Subtype.val e⟩
  have hfix : ∀ q : ModQ, (∀ t (ht : t ∈ T), g2QAct (ZMod 2) (ρ ⟨t, hTL ht⟩) q = q) →
      q = 1 ∨ q = w₀ := by
    intro q hq
    have hc : ∀ i (hi : i < 64), sEltG i ∈ g2Derived (ZMod 2) →
        g2QAct (ZMod 2) (sEltG i) q = q := by
      intro i hi hiD
      obtain ⟨t, ht, htL, e⟩ := hSD _ (mem_sSubG.mpr ⟨i, hi, rfl⟩) hiD
      rw [← e]
      exact hq t ht
    have h44 := hc 44 (by norm_num) (c₁_eq ▸ commutator_mem_g2Derived _ _)
    have h30 := hc 30 (by norm_num) (c₂_eq ▸ commutator_mem_g2Derived _ _)
    obtain ⟨cq, rfl⟩ := codeQ_surjective q
    have hfq : ∀ i (hi : i < 64), g2QAct (ZMod 2) (sEltG i) (codeQ cq) = codeQ cq →
        fixQB (sM i) cq.1 = true := by
      intro i hi h1
      rw [g2QAct_codeQ, codeQ_eq_iff, o0Act_sEltG hi] at h1
      have hm : mact (sM i) cq.1 ∈ o0Codes := by
        rw [← o0Act_sEltG hi]
        exact (o0Act (sEltG i) cq).2
      refine (fixQB_iff (sM i) cq.2 hm).2 ?_
      rcases h1 with h1 | h1
      · exact Or.inl h1.symm
      · right
        calc mact (sM i) cq.1 = (mact (sM i) cq.1 ^^^ 129) ^^^ 129 := by
              rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          _ = cq.1 ^^^ 129 := by rw [← h1]
    rcases fix_c₁₂ cq.1 cq.2 (hfq 44 (by norm_num) h44) (hfq 30 (by norm_num) h30) with
      h0 | h0 | h0 | h0
    · left
      exact (codeQ_eq_one_iff cq).mpr (Or.inl h0)
    · left
      exact (codeQ_eq_one_iff cq).mpr (Or.inr h0)
    · right
      exact (codeQ_eq_iff ⟨8, mem8⟩ cq).mpr (Or.inl h0) |>.symm
    · right
      exact ((codeQ_eq_iff ⟨8, mem8⟩ cq).mpr (Or.inr h0)).symm
  let act : ↥(quasithinG2 (ZMod 2)) → Additive ModQ → Additive ModQ :=
    fun x w => Additive.ofMul (g2QAct (ZMod 2) x (Additive.toMul w))
  let β' : ↥(blockU L) →* Multiplicative (Additive ModQ) :=
    { toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (β u))
      map_one' := by simp
      map_mul' := fun u v => by simp }
  have hβk' : β'.ker = (blockZ L).subgroupOf (blockU L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hβk u]
    show Multiplicative.ofAdd (Additive.ofMul (β u)) = 1 ↔ β u = 1
    simp
  exact CZCore.cZ_core h38 h39 h hG2.1 hTL ρ β' hβk' act
    (fun x => by simp [act]) (fun g u u' hu' => by
      show Additive.ofMul (β u') = Additive.ofMul (g2QAct (ZMod 2) (ρ g) (β u))
      rw [hβe g u u' hu'])
    (w₀ := Additive.ofMul w₀) (p := pw w₀)
    (fun v hv => by
      rcases hfix (Additive.toMul v) (fun t ht => by
        have := hv t ht
        exact congrArg Additive.toMul this) with h1 | h1
      · left
        rw [← ofMul_toMul v, h1]
        rfl
      · right
        rw [← ofMul_toMul v, h1])
    (fun x hx => congrArg Additive.toMul hx) (fun x hx => congrArg Additive.ofMul hx)

theorem parabolic_of_rho [Finite G]
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (hρL' : ∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sSubG)
    (hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ qL L T) :
    oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) (pw w₀)) ⊔ T =
        pre ρ (sup_le Subgroup.le_normalizer hTL) (pw w₀) ∧
      Nonempty (↥(pre ρ (sup_le Subgroup.le_normalizer hTL) (pw w₀)) ⧸
        CFSG.pCore 2 ↥(pre ρ (sup_le Subgroup.le_normalizer hTL) (pw w₀)) ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 (pre ρ (sup_le Subgroup.le_normalizer hTL) (pw w₀)) =
        pre ρ (sup_le Subgroup.le_normalizer hTL) r₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have : Finite ↥(quasithinG2 (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_g2Two]; norm_num)
  set R := (ρ.comp (Subgroup.inclusion hLTN)).range with hR
  have hDR : g2Derived (ZMod 2) ≤ R := by
    intro x hx
    obtain ⟨ℓ, hℓ, e⟩ := hρL' x hx
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have hRp := card_inf_pw_mul R hDR
  have hD := card_g2Derived
  have hRcard : Nat.card ↥R = 6048 ∨ Nat.card ↥R = 12096 := by
    have h1 : 6048 ∣ Nat.card ↥R := hD ▸ Subgroup.card_dvd_of_le hDR
    have h2 : Nat.card ↥R ∣ 12096 := card_g2Two ▸ Subgroup.card_subgroup_dvd_card R
    obtain ⟨k, hk⟩ := h1
    rw [hk] at h2
    have hk2 : k ∣ 2 := by
      have : 6048 * k ∣ 6048 * 2 := by simpa using h2
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
    · left
      rw [hk]
    · right
      rw [hk]
  have h6 : Nat.card ↥(R ⊓ pw w₀) = 6 * Nat.card ↥(R ⊓ r₀) ∨
      Nat.card ↥(R ⊓ pw w₀) = 3 * Nat.card ↥(R ⊓ r₀) := by
    have hr₀ : Nat.card ↥(R ⊓ r₀) * R.relIndex r₀ = 32 := by
      have h1 := Subgroup.relIndex_mul_card (H := R) (K := r₀)
      rw [card_r₀] at h1
      rw [mul_comm]
      exact h1
    have hrel : R.relIndex r₀ ≤ 2 := by
      calc R.relIndex r₀ ≤ R.relIndex ⊤ :=
            Subgroup.relIndex_le_of_le_right le_top Subgroup.index_ne_zero_of_finite
        _ = R.index := Subgroup.relIndex_top_right R
        _ ≤ 2 := by
          have h1 := Subgroup.card_mul_index R
          rw [card_g2Two] at h1
          rcases hRcard with h2 | h2 <;> rw [h2] at h1 <;> omega
    have hrel0 : 1 ≤ R.relIndex r₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases hRcard with h2 | h2
    · rw [h2] at hRp
      interval_cases hk : R.relIndex r₀
      · right
        rw [mul_one] at hr₀
        omega
      · left
        omega
    · have hRtop : R = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h2, card_g2Two])
      have h3 : R.relIndex r₀ = 1 := by
        rw [hRtop, Subgroup.relIndex_top_left]
      rw [h2] at hRp
      rw [h3, mul_one] at hr₀
      left
      omega
  have ha₀D : sEltG 45 ∈ g2Derived (ZMod 2) := a₀_eq ▸ commutator_mem_g2Derived _ _
  have hb₀D : b₀ ∈ g2Derived (ZMod 2) := commutator_mem_g2Derived _ _
  obtain ⟨ℓa, hℓa, ea⟩ := hρL' _ ha₀D
  obtain ⟨ℓb, hℓb, eb⟩ := hρL' _ hb₀D
  have hab : (b₀ * sEltG 45)⁻¹ * (sEltG 45 * b₀) ∉ r₀ := by
    rintro ⟨k, hk, e⟩
    apply b₀_checks.2.2 k hk
    have e2 : sEltG 45 * b₀ = b₀ * sEltG 45 * sEltG (2 * k) := by
      rw [e]
      group
    have e3 := congrArg (fun g : ↥(quasithinG2 (ZMod 2)) => matCode g.1) e2
    simp only [matCode_mulG, matCode_sEltG (show 45 < 64 by norm_num),
      matCode_sEltG (show 2 * k < 64 by omega), matCode_b₀] at e3
    exact e3
  exact parabolic_gen' ρ hLTN hT2 hTidx (fun g hg h1 => hK g hg (hLTN hg) h1)
    (p := pw w₀) (r := r₀) (fun t ht => sSubG_le_pw (hρT t ht))
    (r₀_le.trans sSubG_le_pw) pw_le_normalizer isPGroup_r₀ h6 hℓa hℓb
    (by
      show ρ ⟨ℓa, Subgroup.le_normalizer hℓa⟩ ∈ pw w₀
      rw [ea]
      exact sSubG_le_pw (mem_sSubG.mpr ⟨45, by norm_num, rfl⟩))
    (by
      show ρ ⟨ℓb, Subgroup.le_normalizer hℓb⟩ ∈ pw w₀
      rw [eb]
      exact b₀_mem_pw)
    (by
      show (ρ ⟨ℓb, Subgroup.le_normalizer hℓb⟩ * ρ ⟨ℓa, Subgroup.le_normalizer hℓa⟩)⁻¹ *
        (ρ ⟨ℓa, Subgroup.le_normalizer hℓa⟩ * ρ ⟨ℓb, Subgroup.le_normalizer hℓb⟩) ∉ r₀
      rw [ea, eb]
      exact hab)

theorem xs3_g2 [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) :
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ⧸
      CFSG.pCore 2
        ↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨ρ, β, -, hβk, hβe, hρL, hρL', hρT, hK⟩ := G2Rho.exists_rho h38 h39 h51 h hTL hG2
  have hX := cZ_eq h38 h39 h hTL hG2 ρ β hβk hβe hρL hρL' hρT
  obtain ⟨hXT, ⟨e⟩, -⟩ := parabolic_of_rho h hTL ρ hρL' hρT hK
  exact nonempty_quot_pCore_congr (by rw [hX, hXT]) ⟨e⟩

end XS3

section Insp27

theorem commute_of_commute_pow_two_pow {Γ : Type*} [Group Γ] {x c : Γ} (hc : c ^ 3 = 1) (k : ℕ)
    (h : x * c ^ 2 ^ k = c ^ 2 ^ k * x) : x * c = c * x := by
  have h4 : 2 ^ k * 2 ^ k % 3 = 1 := by
    rw [← mul_pow, Nat.pow_mod]
    norm_num
  have e : (c ^ 2 ^ k) ^ 2 ^ k = c := by
    rw [← pow_mul, pow_eq_pow_mod _ hc, h4, pow_one]
  have h2 : Commute x ((c ^ 2 ^ k) ^ 2 ^ k) := Commute.pow_right h _
  rw [e] at h2
  exact h2

@[expose] def b₁ : ↥(quasithinG2 (ZMod 2)) := sEltG 16 * b₀ * sEltG 16

theorem matCode_b₁ : matCode b₁.1 = b1Code := by
  rw [b₁, matCode_mulG, matCode_mulG, matCode_b₀, matCode_sEltG (by norm_num)]
  exact b₁_checks.2.1

theorem b₀_b₁_mem :
    (b₀ ∈ g2Derived (ZMod 2) ∧ b₀ ∈ pw w₀ ∧ b₀ ^ 3 = 1) ∧
      (b₁ ∈ g2Derived (ZMod 2) ∧ b₁ ∈ pw w₀ ∧ b₁ ^ 3 = 1) := by
  have hn : (g2Derived (ZMod 2)).Normal := by
    rw [g2Derived_eq_commutator]
    infer_instance
  have hb₀D : b₀ ∈ g2Derived (ZMod 2) := commutator_mem_g2Derived _ _
  have hs : (sEltG 16)⁻¹ = sEltG 16 := by
    refine inv_eq_of_mul_eq_one_right (eq_of_code ?_)
    rw [matCode_mulG, matCode_sEltG (by norm_num), b₁_checks.1]
    exact matCode_one.symm
  have hs16 : sEltG 16 ∈ pw w₀ := sSubG_le_pw (mem_sSubG.mpr ⟨16, by norm_num, rfl⟩)
  refine ⟨⟨hb₀D, b₀_mem_pw, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · apply eq_of_code
    rw [pow_three, matCode_mulG, matCode_mulG, matCode_b₀, b₀_checks.1]
    exact matCode_one.symm
  · have := hn.conj_mem _ hb₀D (sEltG 16)
    rwa [hs] at this
  · exact (pw w₀).mul_mem ((pw w₀).mul_mem hs16 b₀_mem_pw) hs16
  · apply eq_of_code
    rw [pow_three, matCode_mulG, matCode_mulG, matCode_b₁, b₁_checks.2.2.1]
    exact matCode_one.symm

theorem eq_one_of_commute_b₀_b₁ {s : ↥(quasithinG2 (ZMod 2))} (hs : s ∈ sSubG)
    (h₀ : s * b₀ = b₀ * s) (h₁ : s * b₁ = b₁ * s) : s = 1 := by
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.mp hs
  have e₀ := congrArg (fun g : ↥(quasithinG2 (ZMod 2)) => matCode g.1) h₀
  have e₁ := congrArg (fun g : ↥(quasithinG2 (ZMod 2)) => matCode g.1) h₁
  simp only [matCode_mulG, matCode_sEltG hi, matCode_b₀, matCode_b₁] at e₀ e₁
  have hi0 : i = 0 := b₁_checks.2.2.2 i hi e₀ e₁
  subst hi0
  exact Subtype.ext sElt_zero

theorem eq_one_of_commute [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L)
    {z : MulAut ↥(vPlus L T)} (hz : z ∈ autOn T (vPlus L T))
    (hy : ∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G))) (vPlus L T), z * y = y * z) : z = 1 := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hG2.1 hTL
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  obtain ⟨ρ, β, hβs, hβk, hβe, hρL, hρL', hρT, hK⟩ := G2Rho.exists_rho h38 h39 h51 h hTL hG2
  have hX := cZ_eq h38 h39 h hTL hG2 ρ β hβk hβe hρL hρL' hρT
  have hker : ∀ (g : G) (hg : g ∈ L ⊔ T), conjAct (vPlus L T) ⟨g, hLTV hg⟩ = 1 →
      ρ ⟨g, hLTN hg⟩ = 1 := by
    intro g hg h1
    have hgC : g ∈ Subgroup.centralizer (vPlus L T : Set G) := A4.conjAct_eq_one_iff.mp h1
    apply g2QAct_injective
    rw [map_one]
    refine MulEquiv.ext fun m => ?_
    obtain ⟨u, rfl⟩ := hβs m
    have hu : (u : G) = g * u * g⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp hgC _ (hUV u.2)]
      group
    rw [MulAut.one_apply, ← hβe ⟨g, hLTN hg⟩ u u hu]
  have hconj : ∀ (a b : G) (ha : a ∈ L ⊔ T) (hb : b ∈ L ⊔ T),
      conjAct (vPlus L T) ⟨a, hLTV ha⟩ = conjAct (vPlus L T) ⟨b, hLTV hb⟩ →
        ρ ⟨a, hLTN ha⟩ = ρ ⟨b, hLTN hb⟩ := by
    intro a b ha hb h1
    have hab : a⁻¹ * b ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ha) hb
    have e1 : (conjAct (vPlus L T) ⟨a, hLTV ha⟩)⁻¹ * conjAct (vPlus L T) ⟨b, hLTV hb⟩ =
        conjAct (vPlus L T) ⟨a⁻¹ * b, hLTV hab⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    have e2 : (ρ ⟨a, hLTN ha⟩)⁻¹ * ρ ⟨b, hLTN hb⟩ = ρ ⟨a⁻¹ * b, hLTN hab⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [← inv_mul_eq_one, e2]
    apply hker _ hab
    rw [← e1, h1, inv_mul_cancel]
  obtain ⟨g, hgT, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hz
  have hgLT : (g : G) ∈ L ⊔ T := Subgroup.mem_sup_right hgT
  have hcomm : ∀ c ∈ g2Derived (ZMod 2), c ∈ pw w₀ → c ^ 3 = 1 →
      ρ ⟨g, hLTN hgLT⟩ * c = c * ρ ⟨g, hLTN hgLT⟩ := by
    intro c hcD hcp hc3
    obtain ⟨ℓ, hℓ, hρℓ⟩ := hρL' c hcD
    have hℓLT : ℓ ∈ L ⊔ T := Subgroup.mem_sup_left hℓ
    have hℓP : ℓ ∈ pre ρ hLTN (pw w₀) := (mem_pre ρ hLTN).mpr ⟨hℓLT, hρℓ ▸ hcp⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ hℓP
    rw [← hX] at hk
    have hkLT : ℓ ^ 2 ^ k ∈ L ⊔ T := (L ⊔ T).pow_mem hℓLT _
    have hyk := hy (conjAct (vPlus L T) ⟨ℓ ^ 2 ^ k, hLTV hkLT⟩)
      (CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨ℓ ^ 2 ^ k, hLTV hkLT⟩, hk, rfl⟩)
    have hgk : (g : G) * ℓ ^ 2 ^ k ∈ L ⊔ T := (L ⊔ T).mul_mem hgLT hkLT
    have hkg : ℓ ^ 2 ^ k * (g : G) ∈ L ⊔ T := (L ⊔ T).mul_mem hkLT hgLT
    have e1 : conjAct (vPlus L T) ⟨(g : G) * ℓ ^ 2 ^ k, hLTV hgk⟩ =
        conjAct (vPlus L T) ⟨ℓ ^ 2 ^ k * (g : G), hLTV hkg⟩ := by
      rw [show (⟨(g : G) * ℓ ^ 2 ^ k, hLTV hgk⟩ : ↥(Subgroup.normalizer (vPlus L T : Set G))) =
          g * ⟨ℓ ^ 2 ^ k, hLTV hkLT⟩ from rfl,
        show (⟨ℓ ^ 2 ^ k * (g : G), hLTV hkg⟩ : ↥(Subgroup.normalizer (vPlus L T : Set G))) =
          ⟨ℓ ^ 2 ^ k, hLTV hkLT⟩ * g from rfl, map_mul, map_mul]
      exact hyk
    have e2 := hconj _ _ hgk hkg e1
    rw [show (⟨(g : G) * ℓ ^ 2 ^ k, hLTN hgk⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hLTN hgLT⟩ * ⟨ℓ, hLTN hℓLT⟩ ^ 2 ^ k from rfl,
      show (⟨ℓ ^ 2 ^ k * (g : G), hLTN hkg⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨ℓ, hLTN hℓLT⟩ ^ 2 ^ k * ⟨g, hLTN hgLT⟩ from rfl, map_mul, map_mul, map_pow,
      show ρ ⟨ℓ, hLTN hℓLT⟩ = c from hρℓ] at e2
    exact commute_of_commute_pow_two_pow hc3 k e2
  obtain ⟨⟨h0D, h0p, h03⟩, ⟨h1D, h1p, h13⟩⟩ := b₀_b₁_mem
  have hρg : ρ ⟨g, hLTN hgLT⟩ = 1 :=
    eq_one_of_commute_b₀_b₁ (hρT g hgT) (hcomm b₀ h0D h0p h03) (hcomm b₁ h1D h1p h13)
  exact A4.conjAct_eq_one_iff.mpr (hQV (hK g hgLT (hLTN hgLT) hρg))

end Insp27

end G2XS3

namespace CZA6

@[expose] def Fact3_3_25XS3Hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → CFSG.Quasithin.IsHatA6Block L →
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ⧸
      CFSG.pCore 2
        ↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ≃*
      Equiv.Perm (Fin 3))

theorem fact3_3_25XS3Rest_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (hHat : Fact3_3_25XS3Hat) :
    Fact3_3_25XS3Rest := by
  intro G _ _ T M L D h hTL hb
  rcases hb with hH | hG
  · exact hHat G T M L D h hTL hH
  · exact G2XS3.xs3_g2 h38 h39 h51 h hTL hG

theorem insp3_3_27Rest_holds
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) : Insp3_3_27Rest := by
  intro G _ _ T M L D h hTL hG z₁ hz₁ z₂ _ _ _ _ _ hn₁ _ hy₁ _
  exact absurd (G2XS3.eq_one_of_commute h38 h39 h51 h hTL hG hz₁ hy₁) hn₁

end CZA6

end CFSG.Quasithin.H13
