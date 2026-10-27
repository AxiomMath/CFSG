module

public import CFSG.Quasithin.Background.C134Case4Kappa
public import CFSG.Quasithin.Background.C134L32CorrM

public section

namespace CFSG.Quasithin.C134Case4Kappa

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.CubicCount CFSG.Quasithin.C134CorrLocal
open CFSG.Quasithin.OperatorJH (mem_normalizer_of_conj_mem_of mem_normalizer_inf_of)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_of_isSum {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ}
    {dual : Bool} {k : ℕ} (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    V ≤ Subgroup.normalizer (Z : Set G) := by
  obtain ⟨-, hZV, β, -, hβk, -⟩ := h
  have hn : (Z.subgroupOf V).Normal := hβk ▸ β.normal_ker
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hZV).mp hn

theorem kappa_eq_of_case4CorrW [Finite G] {G₀ R L : Subgroup G} (h4 : C134Case4Min G₀ R L)
    {α₂ : ↥L →* ↥(StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hLN : L ≤ Subgroup.normalizer (pCoreOf 2 G₀ : Set G)) {h : G} (hhL : h ∈ L) (hh7 : h ^ 7 = 1)
    (hh1 : h ≠ 1) : kappa false h ⊥ (c134Q G₀ L) = kappa true h ⊥ (c134Q G₀ L) := by
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hZQ, -, hU, ⟨Φ, CΦ, hΦ, hCΦ, hQ⟩, -⟩, -⟩ := h4
  have hF := card_eq_two_of_modO2Surj hα₂ hFc hα
  set Q := c134Q G₀ L with hQdef
  set ZQ := centerOf Q with hZQdef
  set U := ⁅ZQ, L⁆ with hUdef
  have hx7 : (α ⟨h, hhL⟩ : Matrix.GeneralLinearGroup (Fin 3) F) ^ 7 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow]
    have : (⟨h, hhL⟩ : ↥L) ^ 7 = 1 := Subtype.ext hh7
    rw [this, map_one, Subgroup.coe_one]
  have hx1 : (α ⟨h, hhL⟩ : Matrix.GeneralLinearGroup (Fin 3) F) ≠ 1 := by
    intro h1
    have hk : (⟨h, hhL⟩ : ↥L) ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    rw [hα.2] at hk
    obtain ⟨k, hk2⟩ := CFSG.pCore_isPGroup ⟨_, hk⟩
    have h2 : (⟨h, hhL⟩ : ↥L) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => (y : ↥L)) hk2
      simpa using this
    have h7 : (⟨h, hhL⟩ : ↥L) ^ 7 = 1 := Subtype.ext hh7
    have hcop : Nat.gcd 7 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have hg := pow_gcd_eq_one.mpr ⟨h7, h2⟩
    rw [hcop, pow_one] at hg
    exact hh1 (congrArg Subtype.val hg)
  obtain ⟨b, hb₁, hb₂⟩ := exists_cubic hF _ hx7 hx1
  have hUZ : U ≤ ZQ := hZQ ▸ le_sup_right
  have hCZ : c134CQ G₀ L ≤ ZQ := hZQ ▸ le_sup_left
  have hZΦ : ZQ ≤ Φ := hΦ.2.1
  have hΦC : Φ ≤ CΦ := hCΦ.2.1
  have hCQ : CΦ ≤ Q := hQ.2.1
  have hZQQ : ZQ ≤ Q := inf_le_left
  have hΦQ : Φ ≤ Q := hΦC.trans hCQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 G₀) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
  have hQO : Q ≤ pCoreOf 2 G₀ := by
    rw [hQdef, c134Q, Subgroup.commutator_le]
    intro a ha l hl
    have hl' : l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 G₀ :=
      (Subgroup.mem_normalizer_iff.mp (hLN hl) a⁻¹).mp ((pCoreOf 2 G₀).inv_mem ha)
    have e : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 G₀).mul_mem ha hl'
  have hQ2 : IsPGroup 2 ↥Q := hO2.to_le hQO
  have hNbot : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun _ =>
    Subgroup.le_normalizer_of_normal
  have hhB : h ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := hNbot ⊤ (Subgroup.mem_top h)
  have hhQ : h ∈ Subgroup.normalizer (Q : Set G) :=
    mem_normalizer_commutator (hLN hhL) (Subgroup.le_normalizer hhL)
  have hhZ : h ∈ Subgroup.normalizer (ZQ : Set G) := mem_normalizer_centerOf hhQ
  have hhU : h ∈ Subgroup.normalizer (U : Set G) :=
    mem_normalizer_commutator hhZ (Subgroup.le_normalizer hhL)
  have hhΦ : h ∈ Subgroup.normalizer (Φ : Set G) := hΦ.1 hhL
  have hhC : h ∈ Subgroup.normalizer (CΦ : Set G) := hCΦ.1 hhL
  have hZU : ZQ ≤ Subgroup.normalizer (U : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp hz.2 u (hZQQ (hUZ hu)))
  have hΦZ : Φ ≤ Subgroup.normalizer (ZQ : Set G) := fun x hx =>
    mem_normalizer_centerOf (Subgroup.le_normalizer (hΦQ hx))
  have hCΦN : CΦ ≤ Subgroup.normalizer (Φ : Set G) := le_normalizer_of_isSum hCΦ
  have hQC : Q ≤ Subgroup.normalizer (CΦ : Set G) := le_normalizer_of_isSum hQ
  have hfix : Fixes h U ZQ := by
    intro z hz
    have hCUN : c134CQ G₀ L ≤ Subgroup.normalizer (U : Set G) := hCZ.trans hZU
    have hz' : z ∈ (c134CQ G₀ L : Set G) * (U : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCUN, ← hZQ]
      exact hz
    obtain ⟨c, hc, u, hu, rfl⟩ := hz'
    have hhc : h * c = c * h := Subgroup.mem_centralizer_iff.mp hc.2 h hhL
    have hu' : h * u * h⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp hhU u).mp hu) (U.inv_mem hu)
    have e : h * (c * u) * h⁻¹ * (c * u)⁻¹ = c * (h * u * h⁻¹ * u⁻¹) * c⁻¹ := by
      calc h * (c * u) * h⁻¹ * (c * u)⁻¹ = h * c * u * h⁻¹ * u⁻¹ * c⁻¹ := by group
        _ = c * h * u * h⁻¹ * u⁻¹ * c⁻¹ := by rw [hhc]
        _ = c * (h * u * h⁻¹ * u⁻¹) * c⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hCUN hc) _).mp hu'
  have hsplit : ∀ b' : Bool, kappa b' h ⊥ Q = kappa b' h ⊥ U * kappa b' h U ZQ *
      kappa b' h ZQ Φ * kappa b' h Φ CΦ * kappa b' h CΦ Q := by
    intro b'
    rw [kappa_trans bot_le hCQ (hNbot _) hQC hhB hhC hhQ b',
      kappa_trans bot_le hΦC (hNbot _) hCΦN hhB hhΦ hhC b',
      kappa_trans bot_le hZΦ (hNbot _) hΦZ hhB hhZ hhΦ b',
      kappa_trans bot_le hUZ (hNbot _) hZU hhB hhU hhZ b']
  have v1 : kappa b h ⊥ U = Nat.card (Fin 1 → Fin 3 → F) := by
    rw [kappa_of_kills bot_le (hNbot _) hhB hhU (kills_of_sumNat hU hhL hb₁),
      relIndex_of_sumNat hU]
  have v1' : kappa (!b) h ⊥ U = 1 :=
    kappa_eq_one_of_kills bot_le (hNbot _) hhB hhU (hQ2.to_le (hUZ.trans hZQQ))
      (by rw [Bool.not_not]; exact kills_of_sumNat hU hhL hb₁)
  have v2 : ∀ b' : Bool, kappa b' h U ZQ = 1 := fun b' =>
    kappa_eq_one_of_fixes hUZ hZU hhU hhZ (hQ2.to_le hZQQ) hfix b'
  have v3 : kappa b h ZQ Φ = 1 :=
    kappa_eq_one_of_kills hZΦ hΦZ hhZ hhΦ (hQ2.to_le hΦQ) (kills_of_sumNat hΦ hhL hb₂)
  have v3' : kappa (!b) h ZQ Φ = Nat.card (Fin 1 → Fin 3 → F) := by
    rw [kappa_of_kills hZΦ hΦZ hhZ hhΦ (kills_of_sumNat hΦ hhL hb₂), relIndex_of_sumNat hΦ]
  have v4 : kappa b h Φ CΦ = 1 :=
    kappa_eq_one_of_kills hΦC hCΦN hhΦ hhC (hQ2.to_le hCQ) (kills_of_sumNat hCΦ hhL hb₂)
  have v4' : kappa (!b) h Φ CΦ = Nat.card (Fin 2 → Fin 3 → F) := by
    rw [kappa_of_kills hΦC hCΦN hhΦ hhC (kills_of_sumNat hCΦ hhL hb₂), relIndex_of_sumNat hCΦ]
  have v5 : kappa b h CΦ Q = Nat.card (Fin 2 → Fin 3 → F) := by
    rw [kappa_of_kills hCQ hQC hhC hhQ (kills_of_sumNat hQ hhL hb₁), relIndex_of_sumNat hQ]
  have v5' : kappa (!b) h CΦ Q = 1 :=
    kappa_eq_one_of_kills hCQ hQC hhC hhQ hQ2
      (by rw [Bool.not_not]; exact kills_of_sumNat hQ hhL hb₁)
  have key : kappa b h ⊥ Q = kappa (!b) h ⊥ Q := by
    rw [hsplit b, hsplit (!b), v1, v1', v2, v2, v3, v3', v4, v4', v5, v5']
    ring
  cases b with
  | false => exact key
  | true => exact key.symm


end CFSG.Quasithin.C134Case4Kappa
