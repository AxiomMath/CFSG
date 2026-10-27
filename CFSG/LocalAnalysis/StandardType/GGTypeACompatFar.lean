module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFarCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] def GGTypeACompatFarExCfgInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
        Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i))

theorem ggTypeACompatFarExInput_of_cfg (h : GGTypeACompatFarExCfgInput) :
    GGTypeACompatFarExInput :=
  fun G _ _ p B Bs x L D J n f y K hN => h G p B Bs x L D J n f y K hN.toNbrCfg

section ActsDiag

variable {X : Type*} [Group X] {m : ℕ} {F : Type} [Field F]

@[expose] def GGActsDiag (φ : SpecialLinearGroup (Fin m) F →* X) (g : X) : Prop :=
  ∃ h : Fin m → Fˣ, ∀ s, g * φ s * g⁻¹ = φ (ggDiagConj h s)

theorem GGActsDiag.pow {φ : SpecialLinearGroup (Fin m) F →* X} {g : X} {h : Fin m → Fˣ}
    (hg : ∀ s, g * φ s * g⁻¹ = φ (ggDiagConj h s)) (k : ℕ) :
    ∀ s, g ^ k * φ s * (g ^ k)⁻¹ = φ (ggDiagConj (h ^ k) s) := by
  induction k with
  | zero =>
    intro s
    rw [pow_zero, pow_zero, ggDiagConj_eq_self_of_const (fun _ _ => rfl)]
    group
  | succ k ih =>
    intro s
    calc g ^ (k + 1) * φ s * (g ^ (k + 1))⁻¹ = g * (g ^ k * φ s * (g ^ k)⁻¹) * g⁻¹ := by group
      _ = φ (ggDiagConj (h ^ (k + 1)) s) := by
        rw [ih, hg, ggDiagConj_ggDiagConj, pow_succ', mul_comm]

theorem weylRep_mem_normalizer_of_actsDiag (h2 : (2 : F) = 0) {p : ℕ} {Bs : Subgroup X}
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs) {n : ℕ}
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) (k : Fin n) :
    φ (weylRep n F k) ∈ Subgroup.normalizer (Bs : Set X) := by
  set w := weylRep n F k with hw
  set a := φ w with ha_def
  have hn2 : w * w = 1 := weylRep_mul_self n h2 k
  have ha2 : a * a = 1 := by rw [ha_def, ← map_mul, hn2, map_one]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have key : ∀ b ∈ Bs, a * b * a⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨t, ht⟩ := hdiag b hb
    set π := Equiv.swap k.castSucc k.succ
    set r : Fin (n + 1) → Fˣ := fun i => (t i)⁻¹ * t (π i) with hr
    set d := ggDiagConj t⁻¹ w * w with hd
    have hP2 : signedPerm π (1 : Fin (n + 1) → F) * signedPerm π 1 = 1 := by
      rw [signedPerm_mul_signedPerm, Equiv.swap_mul_self, signedPerm_one]
      simp
    have hPt : signedPerm π (1 : Fin (n + 1) → F) * diagonal (fun i => (t i : F)) =
        diagonal (fun i => (t (π i) : F)) * signedPerm π 1 := by
      rw [signedPerm_mul_diagonal]
      rfl
    have hdmat : (d : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
        diagonal (fun i => (r i : F)) := by
      rw [hd, Matrix.SpecialLinearGroup.coe_mul, coe_ggDiagConj, hw, coe_weylRep_of_two n h2 k]
      simp only [Pi.inv_apply, inv_inv]
      calc diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)) * signedPerm π 1 *
            diagonal (fun i => (t i : F)) * signedPerm π 1
          = diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)) *
              (signedPerm π 1 * diagonal (fun i => (t i : F))) * signedPerm π 1 := by
            simp only [Matrix.mul_assoc]
        _ = diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)) * diagonal (fun i => (t (π i) : F)) *
              (signedPerm π 1 * signedPerm π 1) := by
            rw [hPt]
            simp only [Matrix.mul_assoc]
        _ = diagonal (fun i => (r i : F)) := by
            rw [hP2, Matrix.mul_one, diagonal_mul_diagonal]
            simp [hr]
    have hcent : φ d ∈ Subgroup.centralizer (Bs : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      obtain ⟨t', ht'⟩ := hdiag b' hb'
      have e : ggDiagConj t' d = d := by
        apply Subtype.ext
        ext i j
        rw [ggDiagConj_apply, hdmat, diagonal_apply]
        by_cases hij : i = j
        · subst hij
          simp only [ite_true]
          have := (t' i).ne_zero
          rw [Units.val_inv_eq_inv_val]
          field_simp
        · simp [hij]
      calc b' * φ d = b' * φ d * b'⁻¹ * b' := by group
        _ = φ d * b' := by rw [ht', e]
    have htp : ∀ i j, t i ^ p = t j ^ p := by
      have e : ∀ s, φ (ggDiagConj (t ^ p) s) = φ (ggDiagConj 1 s) := by
        intro s
        rw [← GGActsDiag.pow ht p s, hBp b hb, ggDiagConj_eq_self_of_const (fun _ _ => rfl)]
        group
      intro i j
      have := ratio_eq_of_ggDiagConj hker e i j
      simpa using this
    have hdp : d ^ p = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hdmat, Matrix.diagonal_pow,
        Matrix.SpecialLinearGroup.coe_one]
      rw [← diagonal_one]
      congr 1
      funext i
      simp only [Pi.pow_apply, hr]
      rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, htp i (π i), inv_mul_cancel,
        Units.val_one]
    have hdB : φ d ∈ Bs := hBs _ hcent (by rw [← map_pow, hdp, map_one])
    have hinv : b⁻¹ * a * b = φ (ggDiagConj t⁻¹ w) := by
      have e := ht (ggDiagConj t⁻¹ w)
      rw [ggDiagConj_ggDiagConj, mul_inv_cancel,
        ggDiagConj_eq_self_of_const (t := (1 : Fin (n + 1) → Fˣ)) (fun _ _ => rfl)] at e
      rw [ha_def, ← e]
      group
    have hw' : a⁻¹ = φ w := ha'
    have e : a * b * a⁻¹ = b * φ d := by
      calc a * b * a⁻¹ = b * (b⁻¹ * a * b) * a⁻¹ := by group
        _ = b * φ d := by rw [hinv, hw', mul_assoc, ← map_mul]
    rw [e]
    exact Bs.mul_mem hb hdB
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key b, fun hb => ?_⟩
  have e : b = a * (a * b * a⁻¹) * a⁻¹ := by
    calc b = (a * a) * b * (a * a)⁻¹ := by rw [ha2, one_mul, inv_one, mul_one]
      _ = a * (a * b * a⁻¹) * a⁻¹ := by group
  rw [e]
  exact key _ hb

end ActsDiag

@[expose] def GGTypeACompatDiagInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ c ∈ Subgroup.centralizer (Bs : Set G), GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c

@[expose] def GGTypeABstarFarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∀ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      φ₂.range = K →
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J →
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) →
      (∀ c ∈ Subgroup.centralizer (Bs : Set G), GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c) →
      ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
        φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) *
            φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) ∈
          Subgroup.centralizer (Bs : Set G)

@[expose] def GGBstarCentralizerOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    Odd (Nat.card (Subgroup.centralizer (Bs : Set G)))

theorem weylRep_mem_normalizer_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hk : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hdiag : ∀ c ∈ Subgroup.centralizer (Bs : Set G), GGActsDiag φ c) (k : Fin n) :
    φ (weylRep n (GaloisField 2 f) k) ∈ Subgroup.normalizer (Bs : Set G) := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, hmod, -⟩ := id hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hBC : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (Bs : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (hBs.2.1.1.is_comm.comm ⟨g, hg⟩ ⟨b, hb⟩)
  exact weylRep_mem_normalizer_of_actsDiag h2 hBs.2.1.2 hBs.2.2.2 hk
    (fun b hb => hdiag b (hBC b hb)) k

theorem odd_natCard_units_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card Kˣ) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hk]
  obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by have := k.pos; omega⟩
  rw [hj, pow_succ]
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem eq_one_of_mul_self_of_odd {X : Type*} [Group X] {H : Subgroup X}
    (hH : Odd (Nat.card H)) {g : X} (hg : g ∈ H) (h : g * g = 1) : g = 1 := by
  have h1 : (⟨g, hg⟩ : H) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact h)
  have h2 : orderOf (⟨g, hg⟩ : H) ∣ Nat.gcd 2 (Nat.card H) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  have hcop : Nat.gcd 2 (Nat.card H) = 1 := (Odd.coprime_two_right hH).symm
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact congrArg Subtype.val h2

theorem ggTypeACompatFarExCfgInput_of_diag (hD : GGTypeACompatDiagInput)
    (hF : GGTypeABstarFarInput) (hO : GGBstarCentralizerOddInput) :
    GGTypeACompatFarExCfgInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨-, -, -, -, hmod, -, hn, -⟩ := id hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, hdiag⟩ := hD G p B Bs x L D J n f y K hN
  refine ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, fun i j hi hj => ?_⟩
  have hu := hF G p B Bs x L D J n f y K hN φ₁ φ₂ hL hk₁ hK hk₂ hJ hc hdiag i j hi hj
  obtain ⟨h, hh⟩ := (hdiag _ hu).1
  obtain ⟨h', hh'⟩ := (hdiag _ hu).2
  exact commute_of_ggDiagConj h2 odd_natCard_units_of_charTwo hn hk₁ hk₂ hc hi hj rfl hh hh'
    (fun _ => eq_one_of_mul_self_of_odd (hO G p B Bs x L D J n f y K hN) hu)

theorem ggTypeACompatFarExInput_of_diag (hD : GGTypeACompatDiagInput)
    (hF : GGTypeABstarFarInput) (hO : GGBstarCentralizerOddInput) :
    GGTypeACompatFarExInput :=
  ggTypeACompatFarExInput_of_cfg (ggTypeACompatFarExCfgInput_of_diag hD hF hO)

theorem ggTypeAFarCommute_of_bstarFar (hF : GGTypeABstarFarInput)
    (hO : GGBstarCentralizerOddInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} (hL : φ₁.range = L)
    (hk₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hK : φ₂.range = K)
    (hk₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (hc : φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
      φ₂.comp (slUpperBlockHom n (GaloisField 2 f)))
    (hdiag : ∀ c ∈ Subgroup.centralizer (Bs : Set G), GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) :
    Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i)) := by
  obtain ⟨-, -, -, -, hmod, -, hn, -⟩ := id hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hu := hF G p B Bs x L D J n f y K hN φ₁ φ₂ hL hk₁ hK hk₂ hJ hc hdiag i j hi hj
  obtain ⟨h, hh⟩ := (hdiag _ hu).1
  obtain ⟨h', hh'⟩ := (hdiag _ hu).2
  exact commute_of_ggDiagConj h2 odd_natCard_units_of_charTwo hn hk₁ hk₂ hc hi hj rfl hh hh'
    (fun _ => eq_one_of_mul_self_of_odd (hO G p B Bs x L D J n f y K hN) hu)

theorem ggTypeAEndBlockLExGenInput_of_diag (hD : GGTypeACompatDiagInput) :
    GGTypeAEndBlockLExGenInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨φ₁, -, hL, hk₁, -, -, hJ, -, -⟩ := hD G p B Bs x L D J n f y K hN
  exact ⟨φ₁, hL, hk₁, hJ⟩

theorem ggTypeAEndBlockKGenInput_of_diag (hD : GGTypeACompatDiagInput) :
    GGTypeAEndBlockKGenInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨φ₁, φ₂, -, -, hK, hk₂, hJ, hc, -⟩ := hD G p B Bs x L D J n f y K hN
  exact ⟨φ₂, hK, hk₂, by rw [← hc]; exact hJ⟩

end CFSG.StandardType
