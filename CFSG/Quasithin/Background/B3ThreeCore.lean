module

public import CFSG.Quasithin.Background.B3ThreeBot
public import CFSG.Quasithin.Background.B3ThreeCoh
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem u0_le_ut0 : Mod.W n Mod.u0 ≤ Mod.W n Mod.ut0 := fun _ hw => hw

theorem u0_N_le (w : U n) (_ : w ∈ Mod.W n Mod.u0) (hw : w ∈ Mod.N n Mod.u0) :
    w ∈ Mod.N n Mod.ut0 := by
  have h : w = 1 := Subgroup.mem_bot.1 hw
  rw [h]
  exact Subgroup.one_mem _

@[expose] noncomputable def projU0 (n : ℕ) : Mod.V n Mod.u0 →* Mod.V n Mod.ut0 :=
  incl n Mod.u0 Mod.ut0 u0_le_ut0 u0_N_le

@[expose] noncomputable def c0 (n : ℕ) (hn : n % 2 = 0) : Mod.V n Mod.u0 :=
  QuotientGroup.mk ⟨eVec n, eVec_mem_U0_iff.2 hn⟩

theorem projU0_surjective : Function.Surjective (projU0 n) := by
  intro v
  induction v using QuotientGroup.induction_on with
  | H w => exact ⟨QuotientGroup.mk w, rfl⟩

theorem projU0_ker {hn : n % 2 = 0} {a : Mod.V n Mod.u0} (ha : a ∈ (projU0 n).ker) :
    a = 1 ∨ a = c0 n hn := by
  induction a using QuotientGroup.induction_on with
  | H w =>
    have h1 : (QuotientGroup.mk (Subgroup.inclusion u0_le_ut0 w) : Mod.V n Mod.ut0) = 1 := ha
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 : (w : U n) ∈ Esub n := h1
    rcases (mem_Esub_iff _).1 h2 with h | h
    · left
      have : w = 1 := Subtype.ext h
      rw [this]
      rfl
    · right
      have : w = ⟨eVec n, eVec_mem_U0_iff.2 hn⟩ := Subtype.ext h
      rw [this]
      rfl

theorem c0_mem_ker (hn : n % 2 = 0) : c0 n hn ∈ (projU0 n).ker := by
  show (QuotientGroup.mk (Subgroup.inclusion u0_le_ut0 ⟨eVec n, eVec_mem_U0_iff.2 hn⟩) :
    Mod.V n Mod.ut0) = 1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

theorem c0_ne_one (hn1 : 1 ≤ n) (hn : n % 2 = 0) : c0 n hn ≠ 1 := by
  intro h
  have h1 := (QuotientGroup.eq_one_iff _).1 h
  have h2 : eVec n = 1 := Subgroup.mem_bot.1 h1
  exact eVec_ne_one hn1 h2

theorem actL_c0 (hn : n % 2 = 0) (g : LG n) : actL n Mod.u0 g (c0 n hn) = c0 n hn := by
  show Mod.act n Mod.u0 g.1 (QuotientGroup.mk ⟨eVec n, eVec_mem_U0_iff.2 hn⟩) = _
  rw [act_mk]
  congr 1

theorem pair_mul_pair_inv {p q r : Fin n} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    pair p r * (pair p q)⁻¹ = pair q r := by
  apply U.ext
  intro s
  simp only [U.val_mul, U.val_inv, pair]
  by_cases h1 : s = p
  · subst h1
    simp [hpq, hpr]
    decide
  · by_cases h2 : s = q
    · subst h2
      simp [h1, hqr]
      decide
    · by_cases h3 : s = r
      · subst h3
        simp [h1, h2]
        decide
      · simp [h1, h2, h3]
        decide

theorem c0_mem_commG (hn5 : 5 ≤ n) (hn : n % 2 = 0) :
    c0 n hn ∈ commG (actL n Mod.u0) := by
  let π₁ : ↥(U0 n) →* Mod.V n Mod.u0 :=
    QuotientGroup.mk' ((⊥ : Subgroup (U n)).subgroupOf (U0 n))
  let X : Subgroup (U n) := ((commG (actL n Mod.u0)).comap π₁).map (U0 n).subtype
  have hXinv : ∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ X, permAct n g x ∈ X := by
    rintro g hg _ ⟨w, hw, rfl⟩
    refine ⟨⟨permAct n g w, isInv_U0 n g w w.2⟩, ?_, rfl⟩
    have h1 : π₁ ⟨permAct n g w, isInv_U0 n g w w.2⟩ = actL n Mod.u0 ⟨g, hg⟩ (π₁ w) := rfl
    show π₁ _ ∈ commG (actL n Mod.u0)
    rw [h1]
    exact isInv_commG (actL n Mod.u0) ⟨g, hg⟩ (π₁ w) hw
  have hn4 : 4 ≤ n := by omega
  obtain ⟨p, q, r, hpq, hpr, hqr⟩ : ∃ p q r : Fin n, p ≠ q ∧ p ≠ r ∧ q ≠ r :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  obtain ⟨τ, hτ, hτp, hτq⟩ := exists_perm_alt_pair hn4 hpq hpr
  let v : ↥(U0 n) := ⟨pair p q, pair_mem_U0 hpq⟩
  have hx₀ : pair q r ∈ X := by
    refine ⟨(⟨permAct n τ (pair p q), isInv_U0 n τ _ (pair_mem_U0 hpq)⟩ : ↥(U0 n)) * v⁻¹, ?_, ?_⟩
    · show π₁ _ ∈ commG (actL n Mod.u0)
      rw [map_mul, map_inv]
      have : π₁ ⟨permAct n τ (pair p q), isInv_U0 n τ _ (pair_mem_U0 hpq)⟩ =
          actL n Mod.u0 ⟨τ, hτ⟩ (π₁ v) := rfl
      rw [this]
      exact mul_inv_mem_commG _ _
    · show permAct n τ (pair p q) * (pair p q)⁻¹ = pair q r
      rw [permAct_pair, hτp, hτq]
      exact pair_mul_pair_inv hpq hpr hqr
  have hU : U0 n ≤ X := U0_le_of_invariant hn4 hXinv hx₀
    (fun h => pair_not_mem_Esub (by omega) q r (by rw [h]; exact Subgroup.one_mem _))
    (fun h => pair_not_mem_Esub (by omega) q r (by rw [h]; exact Subgroup.mem_zpowers _))
  obtain ⟨w, hw, hwe⟩ := hU (eVec_mem_U0_iff.2 hn)
  have hw' : w = ⟨eVec n, eVec_mem_U0_iff.2 hn⟩ := Subtype.ext hwe
  rw [hw'] at hw
  exact hw

theorem extBot_u0 (hn : n % 2 = 0) :
    ExtBot n (actL n Mod.u0) (projU0 n).ker (projU0 n) where
  sq := V_sq' Mod.u0
  surj := projU0_surjective
  equiv g m := incl_act u0_le_ut0 u0_N_le g.1 m
  ker m := MonoidHom.mem_ker
  fix g a ha := by
    rcases projU0_ker (hn := hn) ha with h | h
    · rw [h, map_one]
    · rw [h]
      exact actL_c0 hn g

theorem dlt_eq_one_iff {M : Type*} [CommGroup M] {ρ : LG n →* MulAut M} {A : Subgroup M}
    {π : M →* WV n} (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w)
    {lam : A →* ℤˣ} {c : M} (hc : c ∈ A) (hA : ∀ a ∈ A, a = 1 ∨ a = c) (hlam : lam ⟨c, hc⟩ = -1)
    (hc1 : c ≠ 1) {D : LG n → WV n} (hD : ∀ g, Theta n (D g) = flam E hσ lam g) (g : LG n)
    (w : WV n) : dlt ρ σ g w = 1 ↔ Theta n (D g) w = 1 := by
  have h1 : Theta n (D g) w = lam ⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ := by
    rw [hD g]
    rfl
  rw [h1]
  rcases hA _ (dlt_mem E hσ g w) with h | h
  · have : (⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ : A) = 1 := Subtype.ext h
    rw [this, map_one]
    simp [h]
  · have : (⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ : A) = ⟨c, hc⟩ := Subtype.ext h
    rw [this, hlam]
    simp [h, hc1]

theorem exists_iso_core (hn5 : 5 ≤ n) (hn : n = 6 ∨ n = 8) {M : Type*} [CommGroup M] [Finite M]
    {ρ : LG n →* MulAut M} {A : Subgroup M} {π : M →* WV n} (E : ExtBot n ρ A π)
    (hcomm : A ≤ commG ρ) (hA2 : Nat.card A = 2) :
    ∃ Φ : M ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ := by
  have hev : n % 2 = 0 := by rcases hn with rfl | rfl <;> decide
  have ht := H1_natural_even hn
  obtain ⟨c, hc, hc1⟩ : ∃ c ∈ A, c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      exact Subgroup.mem_bot.2 (hcon a ha)
    rw [hbot, Subgroup.card_bot] at hA2
    omega
  have hA : ∀ a ∈ A, a = 1 ∨ a = c := by
    intro a ha
    by_cases h1 : a = 1
    · exact Or.inl h1
    · right
      have := (Nat.card_eq_two_iff' (1 : A)).1 hA2
      obtain ⟨y, -, hy⟩ := this
      have h2 : (⟨a, ha⟩ : A) = y := hy _ (fun h => h1 (by simpa using congrArg Subtype.val h))
      have h3 : (⟨c, hc⟩ : A) = y := hy _ (fun h => hc1 (by simpa using congrArg Subtype.val h))
      exact congrArg Subtype.val (h2.trans h3.symm)
  obtain ⟨σ, hσ, lam, hlam, hD⟩ := exists_section_adjust hn5 E hcomm ht hc hc1
  have E₀ := extBot_u0 (n := n) hev
  obtain ⟨σ₀, hσ₀, lam₀, hlam₀, hD₀⟩ := exists_section_adjust hn5 E₀
    (fun a ha => by
      rcases projU0_ker (hn := hev) ha with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact c0_mem_commG hn5 hev)
    ht (c0_mem_ker hev) (c0_ne_one (by omega) hev)
  have hA₀ : ∀ a ∈ (projU0 n).ker, a = 1 ∨ a = c0 n hev := fun a ha => projU0_ker ha
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_dlt E E₀ hc hc1 hA (c0_mem_ker hev) (c0_ne_one (by omega) hev) hA₀
    hσ hσ₀ (fun g w => by
      rw [dlt_eq_one_iff E hσ hc hA hlam hc1 (fun g => hD g) g w,
        dlt_eq_one_iff E₀ hσ₀ (c0_mem_ker hev) hA₀ hlam₀ (c0_ne_one (by omega) hev)
          (fun g => hD₀ g) g w])
  exact ⟨Φ, hΦ⟩

theorem exists_iso_top_gen {k k' : Mod} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (hW : k.W n ≤ k'.W n) (hN : ∀ w ∈ k.W n, w ∈ k.N n → w ∈ k'.N n)
    (hinj : ∀ w ∈ k.W n, w ∈ k'.N n → w ∈ k.N n) (hk : k = Mod.u0 ∨ k = Mod.ut0)
    (hkW : ∀ m, inWk n k m = popPar n m) (hk'W : ∀ m, inWk n k' m = true)
    (hNW : ∀ w ∈ k'.N n, w ∈ U0 n) {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {ρ : LG n →* MulAut V} {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M)
    (φ₁ : ↥M ≃* Mod.V n k)
    (hφ₁ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) (actL n k) φ₁) {s : V} (hs : s ∉ M)
    (hVs : M ⊔ Subgroup.zpowers s = ⊤)
    (hcoc : ∀ x, ρ x s * s⁻¹ = ((φ₁.symm (d0 n k x) : ↥M) : V)) :
    ∃ Φ : V ≃* Mod.V n k', IsModIso ρ (actL n k') Φ := by
  classical
  have h1 : popPar n 1 = false := popPar_one_false hn
  let f : Mod.V n k →* Mod.V n k' := incl n k k' hW hN
  have hfinj : Function.Injective f := incl_injective hW hN hinj
  let M' : Subgroup (Mod.V n k') := f.range
  have hM' : ∀ g (v : Mod.V n k'), actL n k' g v * v⁻¹ ∈ M' := fun g v =>
    ext_trivQ hW hN hkW g.1 v
  let ι : Mod.V n k ≃* ↥M' := MonoidHom.ofInjective hfinj
  let φ : ↥M ≃* ↥M' := φ₁.trans ι
  have hφ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) (resAct (actL n k') M' (isInv_of_trivQ hM'))
      φ := by
    intro g m
    apply Subtype.ext
    show f (φ₁ (resAct ρ M (isInv_of_trivQ hM) g m)) = actL n k' g (f (φ₁ m))
    rw [hφ₁ g m]
    exact incl_act hW hN g.1 _
  have hs' : toV n k' 1 ∉ M' := ext_not_mem hW hN hkW hk'W h1 hNW
  have hVs' : M' ⊔ Subgroup.zpowers (toV n k' 1) = ⊤ := ext_sup hW hN hkW hk'W h1
  have hcoc' : ∀ x, ((φ (dsM ρ hM s x) : ↥M') : Mod.V n k') =
      actL n k' x (toV n k' 1) * (toV n k' 1)⁻¹ := by
    intro x
    have e1 : dsM ρ hM s x = φ₁.symm (d0 n k x) := Subtype.ext (hcoc x)
    have e2 : ((φ (dsM ρ hM s x) : ↥M') : Mod.V n k') = f (d0 n k x) := by
      rw [e1]
      show f (φ₁ (φ₁.symm (d0 n k x))) = _
      rw [MulEquiv.apply_symm_apply]
    rw [e2]
    exact incl_d0 hW hN hn hk hk'W x
  exact exists_modIso_ext hV (V_sq' k') hM hM' φ hφ hs hs' hVs hVs' hcoc'

theorem exists_iso_top_ut (hn : n = 6 ∨ n = 8) {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {ρ : LG n →* MulAut V} {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M)
    (φ₁ : ↥M ≃* Mod.V n Mod.ut0)
    (hφ₁ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) (actL n Mod.ut0) φ₁) {s : V} (hs : s ∉ M)
    (hVs : M ⊔ Subgroup.zpowers s = ⊤)
    (hcoc : ∀ x, ρ x s * s⁻¹ = ((φ₁.symm (d0 n Mod.ut0 x) : ↥M) : V)) :
    ∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ := by
  have hev : n % 2 = 0 := by rcases hn with rfl | rfl <;> decide
  exact exists_iso_top_gen (k := Mod.ut0) (k' := Mod.ut) (by rcases hn with rfl | rfl <;> simp)
    (fun _ _ => Subgroup.mem_top _) (fun _ _ h => h) (fun _ _ h => h) (Or.inr rfl)
    (fun _ => rfl) (fun _ => rfl)
    (fun w hw => Subgroup.zpowers_le.2 (eVec_mem_U0_iff.2 hev) hw) hV hM φ₁ hφ₁ hs hVs hcoc

theorem exists_iso_top_u (hn : n = 6 ∨ n = 8) {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {ρ : LG n →* MulAut V} {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M)
    (φ₁ : ↥M ≃* Mod.V n Mod.u0)
    (hφ₁ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) (actL n Mod.u0) φ₁) {s : V} (hs : s ∉ M)
    (hVs : M ⊔ Subgroup.zpowers s = ⊤)
    (hcoc : ∀ x, ρ x s * s⁻¹ = ((φ₁.symm (d0 n Mod.u0 x) : ↥M) : V)) :
    ∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ :=
  exists_iso_top_gen (k := Mod.u0) (k' := Mod.u) (by rcases hn with rfl | rfl <;> simp)
    (fun _ _ => Subgroup.mem_top _) (fun _ _ h => h) (fun _ _ h => h) (Or.inl rfl)
    (fun _ => rfl) (fun _ => rfl)
    (fun w hw => by
      have h : w = 1 := Subgroup.mem_bot.1 hw
      rw [h]
      exact Subgroup.one_mem _) hV hM φ₁ hφ₁ hs hVs hcoc

end CFSG.Quasithin.B3
