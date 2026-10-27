module

public import CFSG.Quasithin.EmptyFaithful.S146zCtx
public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.Background.F9Sixteen

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section SLe

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem commutator_le_of_cosets (S : Setting146 G T M) {Dg Ug N : Subgroup G} {a : G}
    (hDgQ : Dg ≤ pCoreOf 2 (mcOf T)) (haH : a ∈ mcOf T) (ha2 : a * a = 1)
    (hmem : ∀ b ∈ Ug, b ∈ Dg ∨ b * a ∈ Dg) (hZN : Zz ≤ N)
    (hNa : ∀ x ∈ uOfL22 T M, a * x * a⁻¹ * x⁻¹ ∈ N) :
    ⁅uOfL22 T M, Ug⁆ ≤ N := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ haH
  rw [Subgroup.commutator_le]
  intro x hx b hb
  have e : ⁅x, b⁆ = ⁅b, x⁆⁻¹ := by rw [commutatorElement_def, commutatorElement_def]; group
  rcases hmem b hb with hbD | hbD
  · rw [e]
    exact hZN (Subgroup.inv_mem _ (S.comm_mem_Z hG hx (hDgQ hbD)))
  · set d := b * a with hd
    have hbd : b = d * a := by
      rw [hd, mul_assoc, ha2, mul_one]
    have hdQ : d ∈ pCoreOf 2 (mcOf T) := hDgQ hbD
    have hxa : ⁅x, a⁆ ∈ uOfL22 T M := by
      have h1 : a * x⁻¹ * a⁻¹ ∈ uOfL22 T M :=
        (Subgroup.mem_normalizer_iff.mp haU x⁻¹).mp ((uOfL22 T M).inv_mem hx)
      have e1 : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [e1]
      exact (uOfL22 T M).mul_mem hx h1
    have h1 : ⁅x, d⁆ ∈ Zz := by
      have e1 : ⁅x, d⁆ = ⁅d, x⁆⁻¹ := by rw [commutatorElement_def, commutatorElement_def]; group
      rw [e1]
      exact Subgroup.inv_mem _ (S.comm_mem_Z hG hx hdQ)
    have h2 : ⁅d, ⁅x, a⁆⁆ ∈ Zz := S.comm_mem_Z hG hxa hdQ
    have h3 : ⁅x, a⁆ ∈ N := by
      have e1 : ⁅x, a⁆ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [e1]
      exact N.inv_mem (hNa x hx)
    have e2 : ⁅x, b⁆ = ⁅x, d⁆ * ⁅d, ⁅x, a⁆⁆ * ⁅x, a⁆ := by
      rw [hbd]
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact N.mul_mem (N.mul_mem (hZN h1) (hZN h2)) h3

end SLe

section Geo

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem A₁_le_commutator (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (h2 : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) = 1) {a : G}
    (haUg : a ∈ F8.Uγ (VZ T M) (mcOf T) (g : G)) (ha2 : a * a = 1)
    (haU : conjSub a U₁ = U₁) (haQ : a ∉ pCoreOf 2 (mcOf T)) :
    F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hUgH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have haH : a ∈ mcOf T := hUgH haUg
  have hDHle : ⁅F8.DH (VZ T M) Zz (mcOf T) (g : G), F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ≤
      F8.A₁ Zz (g : G) :=
    Subgroup.commutator_le.mpr fun d hd x hx => hd.2.2 x hx
  have hDHU : F8.DH (VZ T M) Zz (mcOf T) (g : G) ≤ uOfL22 T M := centralizerMod_le_left _ _ _
  have hne : ⁅F8.DH (VZ T M) Zz (mcOf T) (g : G), F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ≠ ⊥ := by
    intro hbot
    have hDC : F8.DH (VZ T M) Zz (mcOf T) (g : G) ≤
        centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) := by
      intro d hd
      refine ⟨hDHU hd, S.conjClosure_le_normalizer_Z hG (hDHU hd), fun b hb => ?_⟩
      have hbU : b ∈ F8.Uγ (VZ T M) (mcOf T) (g : G) := Subgroup.zpowers_le.mpr haUg hb
      have h1 : ⁅d, b⁆ ∈ ⁅F8.DH (VZ T M) Zz (mcOf T) (g : G),
          F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := Subgroup.commutator_mem_commutator hd hbU
      rw [hbot, Subgroup.mem_bot] at h1
      rw [commutatorElement_def] at h1
      rw [h1]
      exact Subgroup.one_mem _
    have hdvd := Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hDC
    have hrel : (F8.DH (VZ T M) Zz (mcOf T) (g : G)).relIndex (uOfL22 T M) = 2 := by
      rw [HypF98.relIndex_eq_two_pow_mIdx hUp, h2]; norm_num
    rw [hrel] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hgt := c.index_gt_two S haH ha2 haU haQ
    omega
  have hcardA := hF98.card_A₁ (g := g)
  have hcardge : Nat.card (F8.A₁ Zz (g : G)) ≤
      Nat.card ↥⁅F8.DH (VZ T M) Zz (mcOf T) (g : G), F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := by
    rw [hcardA]
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have heq := Subgroup.eq_of_le_of_card_ge hDHle hcardge
  rw [← heq]
  exact Subgroup.commutator_mono hDHU le_rfl

end Geo

section PureNC

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.pure_not_conj (S : Setting146 G T M) (h4 : Stage1463Four) (c : FCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ U₁ ∨ x ∈ U₂) (hxZ : x ∉ Zz) :
    ∀ (y z : G), z ∈ Zz → z ≠ 1 → y * z * y⁻¹ ≠ x := by
  intro y z hz hz1 hyz
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨h, hh, hhu⟩ := c.pure_conj S hx hxZ
  apply (h4 G T M S (mcOf T) hG u c.hinv).2.2 (h⁻¹ * y) z hz hz1
  calc (h⁻¹ * y) * z * (h⁻¹ * y)⁻¹ = h⁻¹ * (y * z * y⁻¹) * h := by group
    _ = h⁻¹ * x * h := by rw [hyz]
    _ = u := by rw [← hhu]; group

end PureNC

section Core

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem core_pure (S : Setting146 G T M) (h4 : Stage1463Four) (c : FCtx T M K U₁ U₂ s u)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (h1 : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) = 1)
    (h2 : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) = 1) :
    (∃ w ∈ ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆, (w ∈ U₁ ∨ w ∈ U₂) ∧ w ∉ Zz) ∧
    ∀ w ∈ ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆, w ≠ 1 →
      (∀ (x z : G), z ∈ Zz → z ≠ 1 → x * z * x⁻¹ ≠ w) → (w ∈ U₁ ∨ w ∈ U₂) ∧ w ∉ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hUgH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hUgab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUgp : IsPGroup 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := isPGroup_of_isElemAbelian hUgab
  have hDgeq : F8.Dγ (VZ T M) Zz (mcOf T) (g : G) =
      F8.Uγ (VZ T M) (mcOf T) (g : G) ⊓ pCoreOf 2 (mcOf T) := hF98.Dγ_eq_inf_pCoreOf hsetup
  have hrel1 : (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)).relIndex
      (F8.Uγ (VZ T M) (mcOf T) (g : G)) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUgp, h1]; norm_num
  have hdvd2 : (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)).relIndex
      (F8.Uγ (VZ T M) (mcOf T) (g : G)) ∣ 2 := by rw [hrel1]
  obtain ⟨a, haUg, hmem⟩ := Subgroup.relIndex_dvd_two_iff.mp hdvd2
  have haD : a ∉ F8.Dγ (VZ T M) Zz (mcOf T) (g : G) := by
    intro haD
    have hle : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ F8.Dγ (VZ T M) Zz (mcOf T) (g : G) := fun b hb => by
      rcases hmem b hb with h | h
      · have := (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)).mul_mem h
          ((F8.Dγ (VZ T M) Zz (mcOf T) (g : G)).inv_mem haD)
        simpa using this
      · exact h
    have := Subgroup.relIndex_eq_one.mpr hle
    omega
  have haH : a ∈ mcOf T := hUgH haUg
  have ha2 : a * a = 1 := by
    have := isElemAbelian_pow_eq_one hUgab haUg
    simpa [pow_two] using this
  have haQ : a ∉ pCoreOf 2 (mcOf T) := fun hq => haD (hDgeq ▸ ⟨haUg, hq⟩)
  have hmem' : ∀ b ∈ F8.Uγ (VZ T M) (mcOf T) (g : G),
      b ∈ F8.Dγ (VZ T M) Zz (mcOf T) (g : G) ∨ b * a ∈ F8.Dγ (VZ T M) Zz (mcOf T) (g : G) :=
    fun b hb => (hmem b hb).symm
  have hDgQ : F8.Dγ (VZ T M) Zz (mcOf T) (g : G) ≤ pCoreOf 2 (mcOf T) := hDgeq ▸ inf_le_right
  have hpos : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := by
    rw [h1]; norm_num
  have hle : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := by
    rw [h1, h2]
  have hQ := (hF98.F916_2_aux hsetup hpos hle).1
  have hoff := hQ.2.2.2.2
  rw [← hDgeq, hrel1] at hoff
  have hoff' : (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G))).relIndex
      (uOfL22 T M) ≤ 2 ^ 2 := hoff
  rcases c.normalizer_or S haH with hin | hsw
  · obtain ⟨⟨x₁, hx₁U, hx₁⟩, u₁, hu₁, u₂, hu₂, hstruct⟩ := c.inner_struct S haH ha2 hin haQ
    set N : Subgroup G := (Zz ⊔ Subgroup.zpowers u₁) ⊔ Subgroup.zpowers u₂ with hN
    have hZN : Zz ≤ N := le_sup_left.trans le_sup_left
    have hSN : ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ≤ N :=
      commutator_le_of_cosets S hDgQ haH ha2 hmem' hZN hstruct
    have hA₁S := A₁_le_commutator S c hsetup h2 haUg ha2 hin haQ
    have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
    have hu₁U : u₁ ∈ uOfL22 T M := c.hU₁U hu₁
    have hu₂U : u₂ ∈ uOfL22 T M := c.hU₂U hu₂
    have hu₁2 : u₁ ^ 2 = 1 := isElemAbelian_pow_eq_one hUab hu₁U
    have hu₂2 : u₂ ^ 2 = 1 := isElemAbelian_pow_eq_one hUab hu₂U
    have hZ1 : ∀ y ∈ Zz, y * u₁ = u₁ * y := fun y hy => S.comm_of_mem_conjClosure (hZU hy) hu₁U
    have hAU : Zz ⊔ Subgroup.zpowers u₁ ≤ uOfL22 T M :=
      sup_le hZU (Subgroup.zpowers_le.mpr hu₁U)
    have hA2 : ∀ y ∈ Zz ⊔ Subgroup.zpowers u₁, y * u₂ = u₂ * y := fun y hy =>
      S.comm_of_mem_conjClosure (hAU hy) hu₂U
    have hSU : ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ≤ uOfL22 T M :=
      S145.commutator_le_of_le_normalizer (hUgH.trans (le_normalizer_conjClosure _ _))
    obtain ⟨z₀, hz₀, hz₀1⟩ := S.exists_ne_one_Z
    set zg := (g : G) * z₀ * (g : G)⁻¹ with hzg
    have hzgA : zg ∈ F8.A₁ Zz (g : G) := by
      rw [hzg]; exact mem_conjSub.mpr (by simpa [mul_assoc] using hz₀)
    have hzgS := hA₁S hzgA
    have hzgZ : zg ∉ Zz := S.conj_not_mem_Z hG hsetup hz₀ hz₀1
    have hpureNC := fun x (hx : x ∈ U₁ ∨ x ∈ U₂) (hxZ : x ∉ Zz) => c.pure_not_conj S h4 hx hxZ
    have hzgN := hSN hzgS
    rw [mem_sup_two_iff hu₁2 hu₂2 hZ1 hA2] at hzgN
    have hzg3 : zg * u₂⁻¹ * u₁⁻¹ ∈ Zz := by
      rcases hzgN with (h | h) | (h | h)
      · exact absurd h hzgZ
      · exfalso
        have hzgU₁ : zg ∈ U₁ := by
          have e : zg = (zg * u₁⁻¹) * u₁ := by group
          rw [e]; exact U₁.mul_mem (c.hSec.le h) hu₁
        exact hpureNC zg (Or.inl hzgU₁) hzgZ g z₀ hz₀ hz₀1 rfl
      · exfalso
        have hzgU₂ : zg ∈ U₂ := by
          have e : zg = (zg * u₂⁻¹) * u₂ := by group
          rw [e]; exact U₂.mul_mem (c.hZU₂ h) hu₂
        exact hpureNC zg (Or.inr hzgU₂) hzgZ g z₀ hz₀ hz₀1 rfl
      · exact h
    constructor
    · have haN₁ : a ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq hin
      refine ⟨a * x₁ * a⁻¹ * x₁⁻¹, ?_, Or.inl ?_, hx₁⟩
      · have h1 : ⁅a, x₁⁆ ∈ ⁅F8.Uγ (VZ T M) (mcOf T) (g : G), uOfL22 T M⁆ :=
          Subgroup.commutator_mem_commutator haUg (c.hU₁U hx₁U)
        rw [Subgroup.commutator_comm] at h1
        simpa [commutatorElement_def] using h1
      · exact U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₁ x₁).mp hx₁U) (U₁.inv_mem hx₁U)
    · intro w hwS hw1 hwnc
      have hwZ : w ∉ Zz := fun hZ => hwnc 1 w hZ hw1 (by simp)
      have hwN := hSN hwS
      rw [mem_sup_two_iff hu₁2 hu₂2 hZ1 hA2] at hwN
      rcases hwN with (h | h) | (h | h)
      · exact absurd h hwZ
      · refine ⟨Or.inl ?_, hwZ⟩
        have e : w = (w * u₁⁻¹) * u₁ := by group
        rw [e]; exact U₁.mul_mem (c.hSec.le h) hu₁
      · refine ⟨Or.inr ?_, hwZ⟩
        have e : w = (w * u₂⁻¹) * u₂ := by group
        rw [e]; exact U₂.mul_mem (c.hZU₂ h) hu₂
      · exfalso
        have hwU := hSU hwS
        have hzgU := hSU hzgS
        have hzw : zg⁻¹ * w ∈ Zz := by
          have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzg3) h
          have hyU : zg⁻¹ * w ∈ uOfL22 T M := (uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem hzgU) hwU
          have hc₂ : u₂ * (zg⁻¹ * w) * u₂⁻¹ = zg⁻¹ * w := by
            rw [S.comm_of_mem_conjClosure hu₂U hyU]; group
          have hc₁ : u₁ * (zg⁻¹ * w) * u₁⁻¹ = zg⁻¹ * w := by
            rw [S.comm_of_mem_conjClosure hu₁U hyU]; group
          have e : (zg * u₂⁻¹ * u₁⁻¹)⁻¹ * (w * u₂⁻¹ * u₁⁻¹) = zg⁻¹ * w := by
            calc (zg * u₂⁻¹ * u₁⁻¹)⁻¹ * (w * u₂⁻¹ * u₁⁻¹)
                = u₁ * (u₂ * (zg⁻¹ * w) * u₂⁻¹) * u₁⁻¹ := by group
              _ = u₁ * (zg⁻¹ * w) * u₁⁻¹ := by rw [hc₂]
              _ = zg⁻¹ * w := hc₁
          rwa [e] at h1
        by_cases hz1 : zg⁻¹ * w = 1
        · apply hwnc g z₀ hz₀ hz₀1
          have : w = zg := by
            have := congrArg (zg * ·) hz1
            simpa using this
          rw [this]
        · have hzgU12 : zg ∈ U₁ ⊔ U₂ := by
            have e : zg = ((zg * u₂⁻¹ * u₁⁻¹) * u₁) * u₂ := by group
            rw [e]
            exact (U₁ ⊔ U₂).mul_mem
              (Subgroup.mem_sup_left (U₁.mul_mem (c.hSec.le hzg3) hu₁)) (Subgroup.mem_sup_right hu₂)
          obtain ⟨q, hq, z', hz', hz'1, hqz⟩ := c.exists_q_move S hzgU12 hzgZ
          have hzz' : zg⁻¹ * w = z' := S.Z_eq_of_iff hzw hz' (by simp only [hz1, hz'1])
          apply hwnc (q * g) z₀ hz₀ hz₀1
          have e : w = zg * (zg⁻¹ * w) := by group
          calc (q * g) * z₀ * (q * g)⁻¹ = q * zg * q⁻¹ := by rw [hzg]; group
            _ = zg * z' := hqz
            _ = w := by rw [← hzz', e]; group
  · exfalso
    have h8 := c.not_swap S haH ha2 hsw
    have hCle : centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G)) ≤
        centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) :=
      centralizerMod_anti_right _ (Subgroup.zpowers_le.mpr haUg)
    have hdvd := Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hCle
    have hpos' : 0 < (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G))).relIndex
        (uOfL22 T M) := Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
    have := Nat.le_of_dvd hpos' hdvd
    omega

end Core

section FourA

theorem input14624FourA_of (h4 : Stage1463Four) : Input14624FourA := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull h3 h2 hinv h1
  classical
  obtain ⟨hctx, -, hgeom⟩ := hfull
  obtain ⟨hsetup, hDlt, hpos, hle, -, -⟩ := hgeom
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have c : FCtx T M K U₁ U₂ s u := FCtx.ofCtx24 S hctx h3 h2 hinv
  have hpos' : 0 < mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) := hpos
  have hle' : mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) := hle
  have h2' : mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 1 := by
    omega
  obtain ⟨⟨w, hwS, hwpure, hwZ⟩, -⟩ := core_pure S h4 c hsetup h1 h2'
  have hn := hF98.not_Vγ_le_ballStab_of_lt hsetup hDlt
  obtain ⟨δ, δ', k, y, hsetup', hyγ, hyγ₁, hUδ, hUy, hDHδ, hDγδ⟩ := hF98.exists_symmetric_setup hsetup hn
  have h1' : mIdx (F8.Uγ (VZ T M) (mcOf T) (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G)) = 1 := by
    rw [hUδ, hDγδ, F9.mIdx_conjSub]
    exact h2'
  have h2'' : mIdx (uOfL22 T M) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G)) = 1 := by
    rw [hDHδ]
    have e : uOfL22 T M = conjSub (y : G) (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hUy.symm
    rw [e, F9.mIdx_conjSub]
    exact h1
  obtain ⟨-, hcore2⟩ := core_pure S h4 c hsetup' h1' h2''
  have hwne1 : w ≠ 1 := fun h => hwZ (h ▸ (quasithinOmegaOneCenter T).one_mem)
  have hwnc := c.pure_not_conj S h4 hwpure hwZ
  have hw'S : (y : G) * w * (y : G)⁻¹ ∈
      ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (k : G)⁆ := by
    have h1 : (y : G) * w * (y : G)⁻¹ ∈
        conjSub (y : G) ⁅uOfL22 T M, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ := mul_mem_conjSub hwS
    rw [conjSub_commutator', hUy] at h1
    rw [hUδ, Subgroup.commutator_comm]
    exact h1
  have hw'1 : (y : G) * w * (y : G)⁻¹ ≠ 1 := fun h => hwne1 (by
    have h' := congrArg (fun t => (y : G)⁻¹ * t * (y : G)) h
    have e : (y : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) * (y : G) = w := by group
    simp only [e] at h'
    simpa using h')
  have hw'nc : ∀ (x z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 →
      x * z * x⁻¹ ≠ (y : G) * w * (y : G)⁻¹ := by
    intro x z hz hz1 hxz
    apply hwnc ((y : G)⁻¹ * x) z hz hz1
    calc ((y : G)⁻¹ * x) * z * ((y : G)⁻¹ * x)⁻¹ = (y : G)⁻¹ * (x * z * x⁻¹) * (y : G) := by group
      _ = (y : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) * (y : G) := by rw [hxz]
      _ = w := by group
  obtain ⟨hw'pure, hw'Z⟩ := hcore2 _ hw'S hw'1 hw'nc
  obtain ⟨h₁, hh₁, hh₁u⟩ := c.pure_conj S hwpure hwZ
  obtain ⟨h₂, hh₂, hh₂u⟩ := c.pure_conj S hw'pure hw'Z
  intro hcen
  have hxu : (h₂⁻¹ * (y : G) * h₁) * u * (h₂⁻¹ * (y : G) * h₁)⁻¹ = u := by
    calc (h₂⁻¹ * (y : G) * h₁) * u * (h₂⁻¹ * (y : G) * h₁)⁻¹
        = h₂⁻¹ * (y : G) * (h₁ * u * h₁⁻¹) * (y : G)⁻¹ * h₂ := by group
      _ = h₂⁻¹ * ((y : G) * w * (y : G)⁻¹) * h₂ := by rw [hh₁u]; group
      _ = h₂⁻¹ * (h₂ * u * h₂⁻¹) * h₂ := by rw [hh₂u]
      _ = u := by group
  have hxC : h₂⁻¹ * (y : G) * h₁ ∈ Subgroup.centralizer ({u} : Set G) := by
    have hcomm : (h₂⁻¹ * (y : G) * h₁) * u = u * (h₂⁻¹ * (y : G) * h₁) := by
      calc (h₂⁻¹ * (y : G) * h₁) * u
          = ((h₂⁻¹ * (y : G) * h₁) * u * (h₂⁻¹ * (y : G) * h₁)⁻¹) * (h₂⁻¹ * (y : G) * h₁) := by
            group
        _ = u * (h₂⁻¹ * (y : G) * h₁) := by rw [hxu]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hcomm.symm
  have hxH := hcen hxC
  have hyH : (y : G) ∈ mcOf T := by
    have e : (y : G) = h₂ * (h₂⁻¹ * (y : G) * h₁) * h₁⁻¹ := by group
    rw [e]
    exact (mcOf T).mul_mem ((mcOf T).mul_mem hh₂ hxH) ((mcOf T).inv_mem hh₁)
  have hygH : (y : G) * (g : G) ∈ mcOf T := by
    have h1'' : (y * g) • F8.γ₁ T (yOfL22 T M) (mcOf T) = F8.γ₁ T (yOfL22 T M) (mcOf T) := by
      rw [mul_smul, hsetup.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1''
    rwa [stab_γ₁ hF98.amalgamHypV.le₂] at this
  have hgH : (g : G) ∈ mcOf T := by
    have e : (g : G) = (y : G)⁻¹ * ((y : G) * (g : G)) := by group
    rw [e]
    exact (mcOf T).mul_mem ((mcOf T).inv_mem hyH) hygH
  obtain ⟨z₀, hz₀, hz₀1⟩ := S.exists_ne_one_Z
  apply S.conj_not_mem_Z hG hsetup hz₀ hz₀1
  have hgN : (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.normalizer_Z.ge hgH
  exact (Subgroup.mem_normalizer_iff.mp hgN z₀).mp hz₀

end FourA

end CFSG.Quasithin
