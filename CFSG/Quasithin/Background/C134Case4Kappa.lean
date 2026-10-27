module

public import CFSG.Quasithin.Background.C41PfCorr
public import CFSG.Quasithin.Background.SevenL4Model

public section

namespace CFSG.Quasithin.C134Case4Kappa

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.CubicCount CFSG.Quasithin.C134CorrLocal
open CFSG.Quasithin.OperatorJH (mem_normalizer_of_conj_mem_of mem_normalizer_inf_of)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G]

theorem moduleAct_pow {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] (dual : Bool)
    (x : Matrix.GeneralLinearGroup ι F) (k : ℕ) :
    moduleAct dual (x ^ k) = moduleAct dual x ^ k := by
  cases dual with
  | false => exact Units.val_pow_eq_pow_val x k
  | true =>
    show (((x ^ k)⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).transpose =
      (((x⁻¹ : Matrix.GeneralLinearGroup ι F)) : Matrix ι ι F).transpose ^ k
    rw [← inv_pow, Units.val_pow_eq_pow_val, Matrix.transpose_pow]

theorem kills_of_sumNat {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ} {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k) {h : G} (hh : h ∈ A) {b : Bool}
    (hp : moduleAct dual (α ⟨h, hh⟩ : Matrix.GeneralLinearGroup ι F) ^ 3 +
      moduleAct dual (α ⟨h, hh⟩ : Matrix.GeneralLinearGroup ι F) ^ midExp b + 1 = 0) :
    Kills b h Z V := by
  obtain ⟨hAV, -, β, -, hβk, hβe⟩ := hV
  intro v hv
  have hpow : ∀ m : ℕ, h ^ m * v * (h ^ m)⁻¹ ∈ V := fun m => pow_conj_mem (hAV hh) hv m
  have hβpow : ∀ m : ℕ, ∀ i, Multiplicative.toAdd (β ⟨h ^ m * v * (h ^ m)⁻¹, hpow m⟩) i =
      (moduleAct dual (α ⟨h, hh⟩ : Matrix.GeneralLinearGroup ι F)) ^ m *ᵥ
        Multiplicative.toAdd (β ⟨v, hv⟩) i := by
    intro m i
    rw [hβe ⟨h ^ m, A.pow_mem hh m⟩ ⟨v, hv⟩ ⟨h ^ m * v * (h ^ m)⁻¹, hpow m⟩ rfl i]
    congr 1
    rw [show (⟨h ^ m, A.pow_mem hh m⟩ : ↥A) = ⟨h, hh⟩ ^ m from rfl, map_pow, Subgroup.coe_pow,
      moduleAct_pow]
  have hc : cubAct b h v ∈ V := cubAct_mem (hAV hh) hv b
  have hβc : β ⟨cubAct b h v, hc⟩ = 1 := by
    have e : (⟨cubAct b h v, hc⟩ : ↥V) = ⟨h ^ 3 * v * (h ^ 3)⁻¹, hpow 3⟩ *
        ⟨h ^ midExp b * v * (h ^ midExp b)⁻¹, hpow _⟩ * ⟨v, hv⟩ := rfl
    rw [e, map_mul, map_mul]
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_mul, toAdd_mul, Pi.add_apply, Pi.add_apply, hβpow, hβpow, toAdd_one, Pi.zero_apply]
    have e2 : ∀ (N : Matrix ι ι F) (w : ι → F),
        N ^ 3 *ᵥ w + N ^ midExp b *ᵥ w + w = (N ^ 3 + N ^ midExp b + 1) *ᵥ w := by
      intro N w
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    rw [e2, hp, Matrix.zero_mulVec]
  have hker : (⟨cubAct b h v, hc⟩ : ↥V) ∈ β.ker := hβc
  rw [hβk] at hker
  exact Subgroup.mem_subgroupOf.mp hker

theorem relIndex_of_sumNat {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ} {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k) :
    Z.relIndex V = Nat.card (Fin k → ι → F) := by
  obtain ⟨-, -, β, hβs, hβk, -⟩ := hV
  rw [Subgroup.relIndex, ← hβk, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem card_eq_two_of_modO2Surj [Finite G] {L : Subgroup G}
    {α₂ : ↥L →* ↥(StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂) {n : ℕ} {F : Type} [Field F]
    [Fintype F] (hFc : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) :
    Fintype.card F = 2 := by
  have e1 := Subgroup.card_ker_mul_card_of_surjective hα.1
  have e2 := Subgroup.card_ker_mul_card_of_surjective hα₂.1
  rw [hα.2] at e1
  rw [hα₂.2] at e2
  have hpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥L) := Nat.card_pos
  have hcard : Nat.card ↥(StatedSL 3 F) = Nat.card ↥(StatedSL 3 (ZMod 2)) :=
    Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
    ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num),
    Finset.prod_pair (by norm_num)] at hcard
  simp only [Nat.card_eq_fintype_card, hFc] at hcard
  norm_num at hcard
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    have := Fintype.one_lt_card (α := F)
    omega
  have hn : n ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hdvd : (2 ^ n) ^ 3 ∣ 168 := by
      rw [← hcard]
      exact Dvd.intro _ rfl
    have h16 : 16 ∣ (2 ^ n) ^ 3 := by
      rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    omega
  rw [hFc, show n = 1 by omega]
  norm_num

theorem exists_cubic {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (x : Matrix.GeneralLinearGroup (Fin 3) F) (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) :
    ∃ b : Bool, moduleAct false x ^ 3 + moduleAct false x ^ midExp b + 1 = 0 ∧
      moduleAct true x ^ 3 + moduleAct true x ^ midExp (!b) + 1 = 0 := by
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])
  let f : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) (ZMod 2) := e.toRingHom.mapMatrix
  have hf : Function.Injective f := fun A B hAB => by
    ext i j
    have := congrFun₂ hAB i j
    exact e.injective this
  set M : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) with hM
  have hM7 : M ^ 7 = 1 := by
    rw [hM, ← Units.val_pow_eq_pow_val, hx7, Units.val_one]
  have hM1 : M ≠ 1 := fun h => hx1 (Units.ext h)
  have hinv : ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M ^ 6 := by
    have : x⁻¹ = x ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hx7])
    rw [this, Units.val_pow_eq_pow_val]
  have h0 : moduleAct false x = M := rfl
  have h1 : moduleAct true x = (M ^ 6).transpose := by
    show ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose = _
    rw [hinv]
  have hf7 : f M ^ 7 = 1 := by rw [← map_pow, hM7, map_one]
  have hf1 : f M ≠ 1 := fun h => hM1 (hf (by rw [h, map_one]))
  have hT : f (M ^ 6).transpose = (f M ^ 6).transpose := by
    rw [← map_pow]
    rfl
  have hTf : ∀ A : Matrix (Fin 3) (Fin 3) F, f A.transpose = (f A).transpose := fun _ => rfl
  have hback : ∀ A : Matrix (Fin 3) (Fin 3) F, f A = 0 → A = 0 := fun A hA =>
    hf (by rw [hA, map_zero])
  rcases SevenL4Model.sl3_seven (f M) hf7 hf1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨false, ?_, ?_⟩
    · rw [h0]
      exact hback _ (by simpa [map_add, map_pow, midExp] using ha)
    · rw [h1]
      refine hback _ ?_
      simpa [map_add, map_pow, midExp, hTf] using hb
  · refine ⟨true, ?_, ?_⟩
    · rw [h0]
      exact hback _ (by simpa [map_add, map_pow, midExp] using ha)
    · rw [h1]
      refine hback _ ?_
      simpa [map_add, map_pow, midExp, hTf] using hb

theorem mem_normalizer_centralizer {S : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ y ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      y * c * y⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro y hy c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : y⁻¹ * s * y⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem hy) s).mp hs
    have h1 := hc _ hs'
    have e1 : s * (y * c * y⁻¹) = y * ((y⁻¹ * s * y⁻¹⁻¹) * c) * y⁻¹ := by group
    have e2 : y * c * y⁻¹ * s = y * (c * (y⁻¹ * s * y⁻¹⁻¹)) * y⁻¹ := by group
    rw [e1, e2, h1]
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x hx c, fun hc => ?_⟩
  have := key x⁻¹ ((Subgroup.normalizer (S : Set G)).inv_mem hx) _ hc
  simpa [mul_assoc] using this

theorem mem_normalizer_centerOf {S : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    x ∈ Subgroup.normalizer (centerOf S : Set G) :=
  mem_normalizer_inf_of hx (mem_normalizer_centralizer hx)

theorem mem_normalizer_frattiniIn [Finite G] {P : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (P : Set G)) :
    m ∈ Subgroup.normalizer (frattiniIn P : Set G) := by
  refine mem_normalizer_of_conj_mem_of fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have hmP : ∀ z : ↥P, m * (z : G) * m⁻¹ ∈ P := fun z =>
    (Subgroup.mem_normalizer_iff.1 hm z).1 z.2
  have hmP' : ∀ z : ↥P, m⁻¹ * (z : G) * m⁻¹⁻¹ ∈ P := fun z =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (P : Set G)).inv_mem hm) z).1 z.2
  let σ : ↥P ≃* ↥P :=
    { toFun := fun z => ⟨m * z * m⁻¹, hmP z⟩
      invFun := fun z => ⟨m⁻¹ * z * m⁻¹⁻¹, hmP' z⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun z w => Subtype.ext (by simp [mul_assoc]) }
  have hσ : (frattini ↥P).map σ.toMonoidHom = frattini ↥P :=
    (Subgroup.characteristic_iff_map_eq.mp frattini_characteristic) σ
  have hmem : σ y ∈ frattini ↥P := by
    rw [← hσ]
    exact ⟨y, hy, rfl⟩
  exact ⟨σ y, hmem, rfl⟩

theorem mem_normalizer_commutator {H₁ H₂ : Subgroup G} {x : G}
    (h₁ : x ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : x ∈ Subgroup.normalizer (H₂ : Set G)) :
    x ∈ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_commutator, h₁, h₂]

theorem kappa_eq_of_case4Corr [Finite G] {G₀ R L : Subgroup G} (h4 : IsC134Case4Corr G₀ R L)
    {α₂ : ↥L →* ↥(StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hLN : L ≤ Subgroup.normalizer (pCoreOf 2 G₀ : Set G)) {h : G} (hhL : h ∈ L) (hh7 : h ^ 7 = 1)
    (hh1 : h ≠ 1) : kappa false h ⊥ (c134Q G₀ L) = kappa true h ⊥ (c134Q G₀ L) := by
  obtain ⟨⟨n, F, _, _, α, hFc, hα, -, hZQ, -, hU, hΦ, hCΦ, hQ⟩, -⟩ := h4
  have hF := card_eq_two_of_modO2Surj hα₂ hFc hα
  set Q := c134Q G₀ L with hQdef
  set ZQ := centerOf Q with hZQdef
  set U := ⁅ZQ, L⁆ with hUdef
  set Φ := frattiniIn Q with hΦdef
  set CΦ := Q ⊓ Subgroup.centralizer (Φ : Set G) with hCΦdef
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
  have hCQ : CΦ ≤ Q := inf_le_left
  have hZQQ : ZQ ≤ Q := inf_le_left
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
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
  have hhΦ : h ∈ Subgroup.normalizer (Φ : Set G) := mem_normalizer_frattiniIn hhQ
  have hhC : h ∈ Subgroup.normalizer (CΦ : Set G) :=
    mem_normalizer_inf_of hhQ (mem_normalizer_centralizer hhΦ)
  have hZU : ZQ ≤ Subgroup.normalizer (U : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp hz.2 u (hZQQ (hUZ hu)))
  have hΦZ : Φ ≤ Subgroup.normalizer (ZQ : Set G) := fun x hx =>
    mem_normalizer_centerOf (Subgroup.le_normalizer (hΦQ hx))
  have hCΦN : CΦ ≤ Subgroup.normalizer (Φ : Set G) := fun x hx =>
    mem_normalizer_frattiniIn (Subgroup.le_normalizer (hCQ hx))
  have hQC : Q ≤ Subgroup.normalizer (CΦ : Set G) := fun x hx =>
    mem_normalizer_inf_of (Subgroup.le_normalizer hx)
      (mem_normalizer_centralizer (mem_normalizer_frattiniIn (Subgroup.le_normalizer hx)))
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
