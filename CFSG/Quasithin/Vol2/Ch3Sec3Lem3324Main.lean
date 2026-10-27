module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Chief
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Gen
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Gen3324
open scoped commutatorElement

namespace Main3324

variable {G : Type} [Group G]

theorem le_normalizer_of_conj {X K : Subgroup G} (h : ∀ x ∈ X, ∀ g ∈ K, x * g * x⁻¹ ∈ K) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h x hx g, fun hg => ?_⟩
  have h1 := h x⁻¹ (X.inv_mem hx) _ hg
  have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
  rwa [e] at h1

theorem mem_normalizer_comm {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hA, Subgroup.mem_normalizer_iff_map_conj_eq.mp hB]

theorem oTwoUpper_conjClosure {X D : Subgroup G} (hX : oTwoUpper X = X) :
    oTwoUpper (conjClosure X D) = conjClosure X D := by
  refine le_antisymm (oTwoUpper_le _) (conjClosure_le fun d hd x hx => ?_)
  rw [← hX] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine mem_oTwoUpper_of_odd (mem_conjClosure hd hy.1) ?_
    have e := orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [e]
    exact hy.2
  | one => simp
  | mul y z _ _ ihy ihz =>
    have e : d * (y * z) * d⁻¹ = d * y * d⁻¹ * (d * z * d⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
    have e : d * y⁻¹ * d⁻¹ = (d * y * d⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihy

variable [Finite G] {T M L D : Subgroup G}

theorem false_of_config (h20 : Stmt3_3_20) (h : Hyp331 G T M L D) {X W : Subgroup G} {z₀ : G}
    (hXX : oTwoUpper X = X) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hS3 : Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)))
    (hD : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G))
    (h5 : ¬ HasNoncentralTwoChief X 5)
    (hz₀Z : z₀ ∈ quasithinOmegaOneCenter T) (hz₀W : z₀ ∈ W)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hWX : W ≤ ⁅W, X⁆) (hWO : W ≤ pCoreOf 2 X)
    (hirr : ∀ W' : Subgroup G, W' ≤ W → z₀ ∈ W' → X ≤ Subgroup.normalizer (W' : Set G) →
      (∃ w ∈ W', w ∉ Subgroup.zpowers z₀) → W ≤ W')
    (hcomm : ∃ r₀ ∈ pCoreOf 2 X, ∃ v₀ ∈ pCoreOf 2 X, ⁅r₀, v₀⁆ = z₀)
    (hv₁ : ∃ v₁ ∈ W, v₁ ∉ Subgroup.zpowers z₀ ∧ ∀ t ∈ T, ⁅v₁, t⁆ ∈ Subgroup.zpowers z₀)
    {a₁ a₂ : G} (ha₁ : a₁ ∈ pCoreOf 2 (X ⊔ T)) (ha₂ : a₂ ∈ pCoreOf 2 (X ⊔ T))
    (hmove : ∀ a, (a = a₁ ∨ a = a₂ ∨ a = a₁ * a₂) →
      ∃ r ∈ ⁅pCoreOf 2 X, X⁆, ⁅r, a⁆ ∉ Subgroup.zpowers z₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hXTD, -⟩, -, ⟨hOXY, ⟨hRn, ⟨eD⟩⟩, -⟩, -, h5'⟩ := h20 G T M L D X h hXX hTX hS3 hD
  obtain ⟨⟨-, hY2, -, -⟩, hΦ, -⟩ := h5' h5
  set Y := conjClosure X D with hY
  set H := Y ⊔ T with hH
  set RY := pCoreOf 2 (Y ⊔ T) with hRY
  set Z₀ := Subgroup.zpowers z₀ with hZ₀
  have hXY : X ≤ Y := le_conjClosure X D
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := (le_sup_right.trans le_sup_left).trans hXTD
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hTY
  have hYH : Y ≤ H := le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hRYT : RY ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    ⟨hTH, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hHRY : H ≤ Subgroup.normalizer (RY : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hOY : H ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  obtain ⟨r₀, hr₀, v₀, hv₀, hrv⟩ := hcomm
  have hzY : ∀ y ∈ Y, y * z₀ = z₀ * y := by
    have : Fact (IsPGroup 2 ↥(pCoreOf 2 X)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X⟩
    have hc : ⁅(⟨r₀, hr₀⟩ : ↥(pCoreOf 2 X)), ⟨v₀, hv₀⟩⁆ ∈ frattini ↥(pCoreOf 2 X) :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have hz : z₀ ∈ (frattini ↥(pCoreOf 2 X)).map (pCoreOf 2 X).subtype :=
      ⟨_, hc, by rw [← hrv]; simp [commutatorElement_def]⟩
    obtain ⟨c, hc', hcz⟩ := hΦ hz
    intro y hy
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at h2
    rw [← hcz]
    exact h2
  have hzT : ∀ t ∈ T, t * z₀ = z₀ * t := fun t ht => (Subgroup.mem_centralizer_iff.mp
    (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht) z₀ hz₀Z).symm
  have hHz : H ≤ Subgroup.centralizer ({z₀} : Set G) := by
    refine sup_le (fun y hy => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (hzY y hy).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (hzT t ht).symm
  have hcZ₀ : ∀ g ∈ H, ∀ c ∈ Z₀, g * c * g⁻¹ = c := by
    intro g hg c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hgz : Commute g z₀ :=
      (Subgroup.mem_centralizer_iff.mp (hHz hg) z₀ (Set.mem_singleton z₀)).symm
    rw [(hgz.zpow_right k).eq, mul_inv_cancel_right]
  let K₀ : Subgroup G :=
    { carrier := {g | g ∈ H ∧ ∀ s ∈ RY, ⁅g, s⁆ ∈ Z₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, fun s hs => ?_⟩
        have e : ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcZ₀ a ha _ (hb' s hs)]
        exact Z₀.mul_mem (hb' s hs) (ha' s hs)
      one_mem' := ⟨H.one_mem, fun s _ => by
        rw [commutatorElement_one_left]
        exact Z₀.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, fun s hs => ?_⟩
        have e : ⁅a⁻¹, s⁆ = a⁻¹ * ⁅a, s⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcZ₀ a⁻¹ (H.inv_mem ha) _ (Z₀.inv_mem (ha' s hs))]
        exact Z₀.inv_mem (ha' s hs) }
  have hK₀N : H ≤ Subgroup.normalizer (K₀ : Set G) := le_normalizer_of_conj fun x hx g hg => by
    refine ⟨H.mul_mem (H.mul_mem hx hg.1) (H.inv_mem hx), fun s hs => ?_⟩
    have hs' : x⁻¹ * s * x⁻¹⁻¹ ∈ RY :=
      (Subgroup.mem_normalizer_iff.mp (hHRY (H.inv_mem hx)) s).mp hs
    have e : ⁅x * g * x⁻¹, s⁆ = x * ⁅g, x⁻¹ * s * x⁻¹⁻¹⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hcZ₀ x hx _ (hg.2 _ hs')]
    exact hg.2 _ hs'
  obtain ⟨v₁, hv₁W, hv₁z, hv₁T⟩ := hv₁
  have hWY : W ≤ Y := hWO.trans (hOXY.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  have hWK : W ≤ K₀ := by
    refine (hirr (W ⊓ K₀) inf_le_left ⟨hz₀W, hYH (hWY hz₀W), fun s hs => ?_⟩
      (fun x hx => ChiefCount.mem_normalizer_inf (hXW hx) (hK₀N (hYH (hXY hx))))
      ⟨v₁, ⟨hv₁W, hYH (hWY hv₁W), fun s hs => hv₁T s (hRYT hs)⟩, hv₁z⟩).trans inf_le_right
    have e : ⁅z₀, s⁆ = 1 := by
      rw [commutatorElement_def, ← hzT s (hRYT hs)]
      group
    rw [e]
    exact Z₀.one_mem
  set U := conjClosure W H with hU
  have hUK : U ≤ K₀ := conjClosure_le fun x hx w hw =>
    (Subgroup.mem_normalizer_iff.mp (hK₀N hx) w).mp (hWK hw)
  have hUN : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure W H
  have hUO : U ≤ pCoreOf 2 Y := conjClosure_le fun x hx w hw =>
    (Subgroup.mem_normalizer_iff.mp (hOY hx) w).mp (hOXY (hWO hw))
  have hUY : U ≤ Y := hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hU2 : IsPGroup 2 U := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hUO
  have hU1 : U ≠ ⊥ := by
    intro hU0
    have h1 : v₁ ∈ U := le_conjClosure W H hv₁W
    rw [hU0, Subgroup.mem_bot] at h1
    exact hv₁z (h1 ▸ Z₀.one_mem)
  have hUc : U ≤ ⁅U, Y⁆ := conjClosure_le fun x hx w hw =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_comm (hUN hx) (hHY hx)) w).mp
      ((hWX.trans (Subgroup.commutator_mono (le_conjClosure W H) hXY)) hw)
  obtain ⟨B, hUB, hUBn⟩ := exists_top_factor hUY (hYH.trans hUN) hU2 hU1 hUc
  have h0 : NCAtMost Y U (pCoreOf 2 Y) 0 := by
    rintro ⟨A, B', hAB, -⟩
    obtain ⟨hc, hn, hUB', -⟩ := hAB 0
    exact hY2 (Chief3323.hasNoncentralTwoChief_two ⟨hUB, hUBn⟩ ⟨hc, hn⟩ hUB')
  have hOYc : ⁅pCoreOf 2 Y, Y⁆ ≤ U := commutator_le_of_ncAtMost (oTwoUpper_conjClosure hXX)
    hUO (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) (hYH.trans hUN)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) h0
  have hOXc : ⁅pCoreOf 2 X, X⁆ ≤ K₀ :=
    (Subgroup.commutator_mono hOXY hXY).trans (hOYc.trans hUK)
  have hnot : ∀ a, (a = a₁ ∨ a = a₂ ∨ a = a₁ * a₂) → a ∉ RY := by
    intro a ha haR
    obtain ⟨r, hr, hra⟩ := hmove a ha
    exact hra ((hOXc hr).2 a haR)
  set φ : ↥(X ⊔ T) →* DihedralGroup 6 := eD.toMonoidHom.comp (QuotientGroup.mk' _) with hφ
  have hφs : Function.Surjective φ := eD.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφ1 : ∀ x : ↥(X ⊔ T), φ x = 1 → (x : G) ∈ RY := by
    intro x hx
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    exact hx
  have hRX : pCoreOf 2 (X ⊔ T) ≤ X ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have himg : ∀ a (ha : a ∈ pCoreOf 2 (X ⊔ T)),
      φ ⟨a, hRX ha⟩ = 1 ∨ φ ⟨a, hRX ha⟩ = DihedralGroup.r 3 := by
    intro a ha
    by_contra hc
    rw [not_or] at hc
    obtain ⟨g, hg1, hg3⟩ := dih_check _ hc.1 hc.2
    obtain ⟨y, rfl⟩ := hφs g
    have hmem : a * ((y : G) * a * (y : G)⁻¹) ∈ pCoreOf 2 (X ⊔ T) :=
      (pCoreOf 2 (X ⊔ T)).mul_mem ha ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T) y.2) a).mp ha)
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)) ⟨_, hmem⟩
    have hk' : (φ ⟨a, hRX ha⟩ * (φ y * φ ⟨a, hRX ha⟩ * (φ y)⁻¹)) ^ 2 ^ k = 1 := by
      have e : φ ⟨a, hRX ha⟩ * (φ y * φ ⟨a, hRX ha⟩ * (φ y)⁻¹) = φ ⟨_, hRX hmem⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      have e2 : (⟨_, hRX hmem⟩ : ↥(X ⊔ T)) ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [e, ← map_pow, e2, map_one]
    have h1 := pow_gcd_eq_one.mpr ⟨hg3, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at h1
    exact hg1 h1
  rcases himg a₁ ha₁ with h1 | h1
  · exact hnot a₁ (Or.inl rfl) (hφ1 _ h1)
  rcases himg a₂ ha₂ with h2 | h2
  · exact hnot a₂ (Or.inr (Or.inl rfl)) (hφ1 _ h2)
  have h12 : φ (⟨a₁, hRX ha₁⟩ * ⟨a₂, hRX ha₂⟩) = 1 := by
    rw [map_mul, h1, h2]
    exact r3_sq
  exact hnot (a₁ * a₂) (Or.inr (Or.inr rfl)) (hφ1 _ h12)

end Main3324

end CFSG.Quasithin.H13
