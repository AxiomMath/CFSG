module

public import CFSG.Quasithin.EmptyFaithful.S146F10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Aux

variable {G : Type} [Group G]

theorem comm_mul_mem_P6 {Z : Subgroup G} {τ x y : G} (hx : ∀ b ∈ Z, b * x = x * b)
    (h₁ : τ * x * τ⁻¹ * x⁻¹ ∈ Z) (h₂ : τ * y * τ⁻¹ * y⁻¹ ∈ Z) :
    τ * (x * y) * τ⁻¹ * (x * y)⁻¹ ∈ Z := by
  have e : τ * (x * y) * τ⁻¹ * (x * y)⁻¹ =
      (τ * x * τ⁻¹ * x⁻¹) * (x * (τ * y * τ⁻¹ * y⁻¹) * x⁻¹) := by group
  have e2 : x * (τ * y * τ⁻¹ * y⁻¹) * x⁻¹ = τ * y * τ⁻¹ * y⁻¹ := by
    rw [← hx _ h₂]; group
  rw [e, e2]
  exact Z.mul_mem h₁ h₂

theorem comm_left_mem_P6 {Z : Subgroup G} {τ x y : G} (hx : ∀ b ∈ Z, b * x = x * b)
    (h₁ : τ * (x * y) * τ⁻¹ * (x * y)⁻¹ ∈ Z) (h₂ : τ * y * τ⁻¹ * y⁻¹ ∈ Z) :
    τ * x * τ⁻¹ * x⁻¹ ∈ Z := by
  have e : τ * x * τ⁻¹ * x⁻¹ =
      (τ * (x * y) * τ⁻¹ * (x * y)⁻¹) * (x * (τ * y * τ⁻¹ * y⁻¹) * x⁻¹)⁻¹ := by group
  have e2 : x * (τ * y * τ⁻¹ * y⁻¹) * x⁻¹ = τ * y * τ⁻¹ * y⁻¹ := by
    rw [← hx _ h₂]; group
  rw [e, e2]
  exact Z.mul_mem h₁ (Z.inv_mem h₂)

theorem swap_comm_mem_P6 {U U₁ U₂ Z : Subgroup G} {t a₁ a₂ : G}
    (hcom : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU₁ : U₁ ≤ U) (hU₂ : U₂ ≤ U)
    (hZ₂ : Z ≤ U₂) (hinf : U₁ ⊓ U₂ = Z)
    (ht₁ : ∀ x ∈ U₁, t * x * t⁻¹ ∈ U₂) (ht₂ : ∀ x ∈ U₂, t * x * t⁻¹ ∈ U₁)
    (ha₁ : a₁ ∈ U₁) (ha₂ : a₂ ∈ U₂)
    (hk : t * (a₁ * a₂) * t⁻¹ * (a₁ * a₂)⁻¹ ∈ Z) :
    t * a₂ * t⁻¹ * a₁⁻¹ ∈ Z := by
  have hb₁ : t * a₁ * t⁻¹ ∈ U₂ := ht₁ a₁ ha₁
  have hb₂ : t * a₂ * t⁻¹ ∈ U₁ := ht₂ a₂ ha₂
  have hx : t * a₂ * t⁻¹ * a₁⁻¹ ∈ U₁ := U₁.mul_mem hb₂ (U₁.inv_mem ha₁)
  have hy : t * a₁ * t⁻¹ * a₂⁻¹ ∈ U₂ := U₂.mul_mem hb₁ (U₂.inv_mem ha₂)
  have e : t * (a₁ * a₂) * t⁻¹ * (a₁ * a₂)⁻¹ =
      (t * a₂ * t⁻¹ * a₁⁻¹) * (t * a₁ * t⁻¹ * a₂⁻¹) := by
    have c1 : (t * a₁ * t⁻¹) * (t * a₂ * t⁻¹) = (t * a₂ * t⁻¹) * (t * a₁ * t⁻¹) :=
      hcom _ (hU₂ hb₁) _ (hU₁ hb₂)
    have c2 : (t * a₁ * t⁻¹ * a₂⁻¹) * a₁⁻¹ = a₁⁻¹ * (t * a₁ * t⁻¹ * a₂⁻¹) :=
      hcom _ (hU₂ hy) _ (hU₁ (U₁.inv_mem ha₁))
    calc t * (a₁ * a₂) * t⁻¹ * (a₁ * a₂)⁻¹
        = (t * a₁ * t⁻¹) * (t * a₂ * t⁻¹) * a₂⁻¹ * a₁⁻¹ := by group
      _ = (t * a₂ * t⁻¹) * (t * a₁ * t⁻¹) * a₂⁻¹ * a₁⁻¹ := by rw [c1]
      _ = (t * a₂ * t⁻¹) * ((t * a₁ * t⁻¹ * a₂⁻¹) * a₁⁻¹) := by group
      _ = (t * a₂ * t⁻¹) * (a₁⁻¹ * (t * a₁ * t⁻¹ * a₂⁻¹)) := by rw [c2]
      _ = (t * a₂ * t⁻¹ * a₁⁻¹) * (t * a₁ * t⁻¹ * a₂⁻¹) := by group
  rw [e] at hk
  have hx₂ : t * a₂ * t⁻¹ * a₁⁻¹ ∈ U₂ := by
    have : t * a₂ * t⁻¹ * a₁⁻¹ =
        ((t * a₂ * t⁻¹ * a₁⁻¹) * (t * a₁ * t⁻¹ * a₂⁻¹)) * (t * a₁ * t⁻¹ * a₂⁻¹)⁻¹ := by group
    rw [this]
    exact U₂.mul_mem (hZ₂ hk) (U₂.inv_mem hy)
  rw [← hinf]
  exact ⟨hx, hx₂⟩

end Aux

@[expose] def Input14617VDec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ w ∈ conjClosure (VZ T M) H,
        (∀ τ ∈ T, τ * w * τ⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T) →
          ∃ k ∈ uK T M H, ∃ c ∈ conjClosure (VZ T M) H,
            (∀ h ∈ H, h * c * h⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T) ∧
              w * (k * c)⁻¹ ∈ quasithinOmegaOneCenter T

theorem input14617V_of_dec (iD : Input14617VDec) : Input14617V := by
  intro G _ _ T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have htT : t ∈ T := hdec.t_mem
  have htH : t ∈ H := hTH htT
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hcom : ∀ a, a ∈ conjClosure (VZ T M) H → ∀ b, b ∈ conjClosure (VZ T M) H →
      a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUab ha hb
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H := hZV.trans hVU
  have hZc2 : Nat.card (quasithinOmegaOneCenter T) = 2 := S.card_Z
  have hVc4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hU₁U : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hU₂U : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hZc : ∀ x ∈ conjClosure (VZ T M) H, ∀ b ∈ quasithinOmegaOneCenter T, b * x = x * b :=
    fun x hx b hb => hcom b (hZU hb) x hx
  have hTZ : ∀ τ ∈ T, ∀ z ∈ quasithinOmegaOneCenter T, τ * z * τ⁻¹ = z := by
    intro τ hτ z hz
    have := Subgroup.mem_centralizer_iff.mp (le_centralizer_quasithinOmegaOneCenter T hτ) z hz
    rw [← this]
    group
  have hHZ : ∀ h ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, h * z * h⁻¹ = z := by
    intro h hh z hz
    have := S146T.comm_Z (hHG hh) hz
    rw [this]
    group
  have hrel : (quasithinOmegaOneCenter T).relIndex (VZ T M) = 2 := by
    have e := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := VZ T M)
    rw [inf_eq_left.mpr hZV, hZc2, hVc4] at e
    omega
  have hne : ¬ VZ T M ≤ quasithinOmegaOneCenter T := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨v, hvV, hvZ⟩ := Set.not_subset.mp fun hs => hne (SetLike.coe_subset_coe.mp hs)
  have hvgen : VZ T M = quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v := by
    have hle : quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v ≤ VZ T M :=
      sup_le hZV (Subgroup.zpowers_le.mpr hvV)
    have hd1 : Nat.card (quasithinOmegaOneCenter T) ∣
        Nat.card ↥(quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥(quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v) ∣ Nat.card (VZ T M) :=
      Subgroup.card_dvd_of_le hle
    have hne2 : Nat.card ↥(quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v) ≠ 2 := by
      intro hc
      have heq : quasithinOmegaOneCenter T = quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, hZc2])
      exact hvZ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
    rw [hZc2] at hd1
    rw [hVc4] at hd2
    have hc4 : Nat.card ↥(quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v) = 4 := by
      have hle4 : Nat.card ↥(quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v) ≤ 4 :=
        Nat.le_of_dvd (by norm_num) hd2
      generalize Nat.card ↥(quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v) = c at *
      interval_cases c <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc4, hVc4])).symm
  have hTv : ∀ τ ∈ T, τ * v * τ⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro τ hτ
    have hτV : τ * v * τ⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure (quasithinOmegaOneCenter T) M (hTM hτ)) v).mp hvV
    have hτZ : τ * v * τ⁻¹ ∉ quasithinOmegaOneCenter T := by
      intro hz
      apply hvZ
      have h1 := hTZ τ⁻¹ (T.inv_mem hτ) _ hz
      have e : τ⁻¹ * (τ * v * τ⁻¹) * τ⁻¹⁻¹ = v := by group
      rw [e] at h1
      rw [h1]
      exact hz
    exact mul_inv_mem_of_relIndex_two hrel hτV hvV hτZ hvZ
  obtain ⟨k, hkK, c, hcU, hcH, hkc⟩ := iD G T M S H PQ p hred v (hVU hvV) hTv
  obtain ⟨ζ, hζ, hζv⟩ : ∃ ζ ∈ quasithinOmegaOneCenter T, v = ζ * (k * c) :=
    ⟨v * (k * c)⁻¹, hkc, by group⟩
  have hkU : k ∈ uHi T M H H₁ ⊔ uHi T M H H₂ := by
    rw [hdec.dir_sup]
    exact Subgroup.mem_sup_left hkK
  have hcom₁₂ : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    hcom x (hU₁U hx) y (hU₂U hy)
  obtain ⟨-, hprod⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁) (uHi T M H H₂) hcom₁₂
  have hk' : k ∈ ((uHi T M H H₁ : Set G) * (uHi T M H H₂ : Set G)) := by
    rw [← hprod]
    exact hkU
  obtain ⟨a₁, ha₁, a₂, ha₂, hka⟩ := Set.mem_mul.mp hk'
  have hkU' : k ∈ conjClosure (VZ T M) H := by
    rw [← hka]
    exact (conjClosure (VZ T M) H).mul_mem (hU₁U ha₁) (hU₂U ha₂)
  have hτk : ∀ τ ∈ T, τ * k * τ⁻¹ * k⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro τ hτ
    have hz₀ : (ζ⁻¹) ∈ quasithinOmegaOneCenter T := (quasithinOmegaOneCenter T).inv_mem hζ
    have hkc' : k * c = ζ⁻¹ * v := by rw [hζv]; group
    have h1 : τ * (k * c) * τ⁻¹ * (k * c)⁻¹ ∈ quasithinOmegaOneCenter T := by
      rw [hkc']
      refine comm_mul_mem_P6 (fun b hb => hZc ζ⁻¹ (hZU hz₀) b hb) ?_ (hTv τ hτ)
      rw [hTZ τ hτ _ hz₀, mul_inv_cancel]
      exact (quasithinOmegaOneCenter T).one_mem
    exact comm_left_mem_P6 (fun b hb => hZc k hkU' b hb) h1 (hcH τ (hTH hτ))
  have htH₀ : t ∉ H₀ := fun ht0 => hdec.t_not (hdec.H₀_le_normalizer_H₁ ht0)
  have htinvH₀ : t⁻¹ ∉ H₀ := fun ht0 => htH₀ (by simpa using H₀.inv_mem ht0)
  have htt₀ : t * t ∈ H₀ := by
    have h1 : t * t⁻¹⁻¹ ∈ H₀ :=
      mul_inv_mem_of_relIndex_two hdec.index htH (H.inv_mem htH) htH₀ htinvH₀
    simpa using h1
  have hU₁₂ : conjSub t (uHi T M H H₁) = uHi T M H H₂ := hdec.conjSub_uHi hred
  have hU₂₁ : conjSub t (uHi T M H H₂) = uHi T M H H₁ := by
    rw [← hU₁₂, ← conjSub_mul]
    exact conjSub_eq_of_mem_normalizer (hdec.le_normalizer_uHi₁ S hred htt₀)
  have ht₁ : ∀ x ∈ uHi T M H H₁, t * x * t⁻¹ ∈ uHi T M H H₂ := by
    intro x hx
    have : t * x * t⁻¹ ∈ conjSub t (uHi T M H H₁) :=
      mem_conjSub.mpr (by simpa [mul_assoc] using hx)
    rwa [hU₁₂] at this
  have ht₂ : ∀ x ∈ uHi T M H H₂, t * x * t⁻¹ ∈ uHi T M H H₁ := by
    intro x hx
    have : t * x * t⁻¹ ∈ conjSub t (uHi T M H H₂) :=
      mem_conjSub.mpr (by simpa [mul_assoc] using hx)
    rwa [hU₂₁] at this
  have hswap : t * a₂ * t⁻¹ * a₁⁻¹ ∈ quasithinOmegaOneCenter T :=
    swap_comm_mem_P6 hcom hU₁U hU₂U (Z_le_uHi T M H H₂) hdec.dir_inf ht₁ ht₂ ha₁ ha₂
      (by rw [hka]; exact hτk t htT)
  have h12 : a₂ ∈ quasithinOmegaOneCenter T → a₁ ∈ quasithinOmegaOneCenter T := by
    intro h2
    rw [hTZ t htT a₂ h2] at hswap
    have h3 : a₁⁻¹ ∈ quasithinOmegaOneCenter T := by
      have := (quasithinOmegaOneCenter T).mul_mem ((quasithinOmegaOneCenter T).inv_mem h2) hswap
      have e : a₂⁻¹ * (a₂ * a₁⁻¹) = a₁⁻¹ := by group
      rwa [e] at this
    simpa using (quasithinOmegaOneCenter T).inv_mem h3
  have h21 : a₁ ∈ quasithinOmegaOneCenter T → a₂ ∈ quasithinOmegaOneCenter T := by
    intro h1
    have h3 : t * a₂ * t⁻¹ ∈ quasithinOmegaOneCenter T := by
      have := (quasithinOmegaOneCenter T).mul_mem hswap h1
      have e : t * a₂ * t⁻¹ * a₁⁻¹ * a₁ = t * a₂ * t⁻¹ := by group
      rwa [e] at this
    have h4 := hTZ t⁻¹ (T.inv_mem htT) _ h3
    have e : t⁻¹ * (t * a₂ * t⁻¹) * t⁻¹⁻¹ = a₂ := by group
    rw [e] at h4
    rw [h4]
    exact h3
  have hbad : a₁ ∈ quasithinOmegaOneCenter T → False := by
    intro h1
    have h2 := h21 h1
    have hkZ : k ∈ quasithinOmegaOneCenter T := by
      rw [← hka]
      exact (quasithinOmegaOneCenter T).mul_mem h1 h2
    have hw₀ : ζ * k ∈ quasithinOmegaOneCenter T := (quasithinOmegaOneCenter T).mul_mem hζ hkZ
    have hvw : v = (ζ * k) * c := by rw [hζv]; group
    have hHv : ∀ h ∈ H, h * v * h⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := by
      intro h hh
      rw [hvw]
      refine comm_mul_mem_P6 (fun b hb => hZc (ζ * k) (hZU hw₀) b hb) ?_ (hcH h hh)
      rw [hHZ h hh _ hw₀, mul_inv_cancel]
      exact (quasithinOmegaOneCenter T).one_mem
    have hHV : ∀ h ∈ H, ∀ y ∈ VZ T M, h * y * h⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := by
      intro h hh y hy
      by_cases hyZ : y ∈ quasithinOmegaOneCenter T
      · rw [hHZ h hh y hyZ, mul_inv_cancel]
        exact (quasithinOmegaOneCenter T).one_mem
      · have hy' : y * v⁻¹ ∈ quasithinOmegaOneCenter T :=
          mul_inv_mem_of_relIndex_two hrel hy hvV hyZ hvZ
        have e : y = (y * v⁻¹) * v := by group
        rw [e]
        refine comm_mul_mem_P6 (fun b hb => hZc _ (hZU hy') b hb) ?_ (hHv h hh)
        rw [hHZ h hh _ hy', mul_inv_cancel]
        exact (quasithinOmegaOneCenter T).one_mem
    have hUV : conjClosure (VZ T M) H ≤ VZ T M := by
      refine conjClosure_le fun h hh y hy => ?_
      have e : h * y * h⁻¹ = (h * y * h⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact (VZ T M).mul_mem (hZV (hHV h hh y hy)) hy
    have hKZ : uK T M H ≤ quasithinOmegaOneCenter T := by
      refine Subgroup.commutator_le.mpr fun u hu h hh => ?_
      have h1 := (quasithinOmegaOneCenter T).inv_mem (hHV h hh u (hUV hu))
      have e : (h * u * h⁻¹ * u⁻¹)⁻¹ = ⁅u, h⁆ := by rw [commutatorElement_def]; group
      rwa [e] at h1
    have hU₁Z : uHi T M H H₁ = quasithinOmegaOneCenter T := by
      refine le_antisymm ?_ (Z_le_uHi T M H H₁)
      exact (le_sup_left.trans hdec.dir_sup.le).trans (sup_le hKZ le_rfl)
    have e := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := uHi T M H H₁)
    rw [inf_eq_left.mpr (Z_le_uHi T M H H₁), (hdec.relIndex_uHi_eq_four S hred hp3 hOF).1,
      hZc2] at e
    have h8 : Nat.card ↥(uHi T M H H₁) = 2 := by
      rw [hU₁Z]
      exact hZc2
    omega
  have ha₁Z : a₁ ∉ quasithinOmegaOneCenter T := hbad
  have ha₂Z : a₂ ∉ quasithinOmegaOneCenter T := fun h2 => hbad (h12 h2)
  refine ⟨a₁, ha₁, ha₁Z, a₂, ha₂, ha₂Z, c, hcU, hcH, ?_⟩
  rw [hvgen]
  have hq : a₁ * a₂ * c = ζ⁻¹ * v := by rw [hka, hζv]; group
  have hv' : v = ζ * (a₁ * a₂ * c) := by rw [hka]; exact hζv
  refine le_antisymm (sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_))
    (sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_))
  · rw [hv']
    exact (quasithinOmegaOneCenter T ⊔ Subgroup.zpowers (a₁ * a₂ * c)).mul_mem
      (Subgroup.mem_sup_left hζ) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · rw [hq]
    exact (quasithinOmegaOneCenter T ⊔ Subgroup.zpowers v).mul_mem
      (Subgroup.mem_sup_left ((quasithinOmegaOneCenter T).inv_mem hζ))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end CFSG.Quasithin
