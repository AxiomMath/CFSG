module

public import CFSG.Quasithin.EmptyFaithful.S14610P0b
public import CFSG.Quasithin.Background.A1bReduced
public import CFSG.Quasithin.EmptyFaithful.S14610P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

private theorem eq_mul_of_card_four {V : Subgroup G} (hV : Nat.card V = 4)
    (hV2 : ∀ u ∈ V, u * u = 1) {v₁ v₂ w : G} (h₁ : v₁ ∈ V) (h₂ : v₂ ∈ V) (hw : w ∈ V)
    (h₁1 : v₁ ≠ 1) (h₂1 : v₂ ≠ 1) (h₁₂ : v₁ ≠ v₂) (hw1 : w ≠ 1) (hw₁ : w ≠ v₁)
    (hw₂ : w ≠ v₂) : w = v₁ * v₂ := by
  have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right (hV2 v₁ h₁)
  have hne : v₁ * v₂ ≠ 1 := fun h => h₁₂ (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hv₁inv])
  have hb : (1 : V) ≠ ⟨v₁, h₁⟩ := fun h => h₁1 (congrArg Subtype.val h).symm
  have hc : (1 : V) ≠ ⟨v₂, h₂⟩ := fun h => h₂1 (congrArg Subtype.val h).symm
  have hd : (1 : V) ≠ ⟨v₁ * v₂, V.mul_mem h₁ h₂⟩ := fun h => hne (congrArg Subtype.val h).symm
  have hbc : (⟨v₁, h₁⟩ : V) ≠ ⟨v₂, h₂⟩ := fun h => h₁₂ (congrArg Subtype.val h)
  have hbd : (⟨v₁, h₁⟩ : V) ≠ ⟨v₁ * v₂, V.mul_mem h₁ h₂⟩ := fun h => h₂1 (by
    have := congrArg Subtype.val h
    simpa using this.symm)
  have hcd : (⟨v₂, h₂⟩ : V) ≠ ⟨v₁ * v₂, V.mul_mem h₁ h₂⟩ := fun h => h₁1 (by
    have := congrArg Subtype.val h
    simpa using this.symm)
  rcases eq_or_eq_or_eq_or_eq_of_card_four hV hb hc hd hbc hbd hcd ⟨w, hw⟩ with h | h | h | h
  · exact absurd (congrArg Subtype.val h) hw1
  · exact absurd (congrArg Subtype.val h) hw₁
  · exact absurd (congrArg Subtype.val h) hw₂
  · exact congrArg Subtype.val h

private theorem conj_eq_mul_of_fixes {V : Subgroup G} (hV : Nat.card V = 4)
    (hV2 : ∀ u ∈ V, u * u = 1) {g v w : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hgC : g ∉ Subgroup.centralizer (V : Set G)) (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hvw : w ≠ v) (hf : g * v * g⁻¹ = v) : g * w * g⁻¹ = v * w := by
  have hgw : g * w * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  refine eq_mul_of_card_four hV hV2 hv hw hgw hv1 hw1 hvw.symm ?_ ?_ ?_
  · intro h
    apply hw1
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hvw
    have e : g * w * g⁻¹ = g * v * g⁻¹ := h.trans hf.symm
    exact mul_left_cancel (mul_right_cancel e)
  · intro h
    apply hgC
    refine mem_centralizer_of_commute_two hV hV2 hv hw hv1 hw1 hvw ?_ ?_
    · calc g * v = (g * v * g⁻¹) * g := by group
        _ = v * g := by rw [hf]
    · calc g * w = (g * w * g⁻¹) * g := by group
        _ = w * g := by rw [h]

private theorem not_pow_two_pow_eq_one_of_fixes {V : Subgroup G} (hV : Nat.card V = 4)
    (hV2 : ∀ u ∈ V, u * u = 1) {v₁ v₂ a₁ a₂ : G} (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (hv₁1 : v₁ ≠ 1)
    (hv₂1 : v₂ ≠ 1) (hv₁₂ : v₁ ≠ v₂) (ha₁ : a₁ ∈ Subgroup.normalizer (V : Set G))
    (ha₂ : a₂ ∈ Subgroup.normalizer (V : Set G)) (hf₁ : a₁ * v₁ * a₁⁻¹ = v₁)
    (hf₂ : a₂ * v₂ * a₂⁻¹ = v₂) (hn₁ : a₁ ∉ Subgroup.centralizer (V : Set G))
    (hn₂ : a₂ ∉ Subgroup.centralizer (V : Set G)) (k : ℕ) : (a₂ * a₁) ^ 2 ^ k ≠ 1 := by
  intro hk
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h1 := hV2 (x * y) (V.mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
        rw [inv_eq_of_mul_eq_one_right (hV2 x hx), inv_eq_of_mul_eq_one_right (hV2 y hy)]
  have e1 : a₁ * v₂ * a₁⁻¹ = v₁ * v₂ :=
    conj_eq_mul_of_fixes hV hV2 ha₁ hn₁ hv₁ hv₂ hv₁1 hv₂1 hv₁₂.symm hf₁
  have e2 : a₂ * v₁ * a₂⁻¹ = v₂ * v₁ :=
    conj_eq_mul_of_fixes hV hV2 ha₂ hn₂ hv₂ hv₁ hv₂1 hv₁1 hv₁₂ hf₂
  have hv12 : v₁ * v₂ = v₂ * v₁ := hcomm v₁ hv₁ v₂ hv₂
  obtain ⟨x, hx⟩ : ∃ x : G, x = a₂ * a₁ := ⟨_, rfl⟩
  rw [← hx] at hk
  have hx1 : x * v₁ * x⁻¹ = v₂ * v₁ := by
    calc x * v₁ * x⁻¹ = a₂ * (a₁ * v₁ * a₁⁻¹) * a₂⁻¹ := by rw [hx]; group
      _ = v₂ * v₁ := by rw [hf₁, e2]
  have hx2 : x * v₂ * x⁻¹ = v₁ := by
    calc x * v₂ * x⁻¹ = a₂ * (a₁ * v₂ * a₁⁻¹) * a₂⁻¹ := by rw [hx]; group
      _ = a₂ * (v₁ * v₂) * a₂⁻¹ := by rw [e1]
      _ = (a₂ * v₁ * a₂⁻¹) * (a₂ * v₂ * a₂⁻¹) := by group
      _ = (v₂ * v₁) * v₂ := by rw [e2, hf₂]
      _ = (v₁ * v₂) * v₂ := by rw [hv12]
      _ = v₁ * (v₂ * v₂) := by rw [mul_assoc]
      _ = v₁ := by rw [hV2 v₂ hv₂, mul_one]
  have hx12 : x * (v₂ * v₁) * x⁻¹ = v₂ := by
    calc x * (v₂ * v₁) * x⁻¹ = (x * v₂ * x⁻¹) * (x * v₁ * x⁻¹) := by group
      _ = v₁ * (v₂ * v₁) := by rw [hx2, hx1]
      _ = v₁ * (v₁ * v₂) := by rw [← hv12]
      _ = (v₁ * v₁) * v₂ := by rw [← mul_assoc]
      _ = v₂ := by rw [hV2 v₁ hv₁, one_mul]
  have hx3₁ : x * x * x * v₁ * (x * x * x)⁻¹ = v₁ := by
    calc x * x * x * v₁ * (x * x * x)⁻¹ = x * (x * (x * v₁ * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = v₁ := by rw [hx1, hx12, hx2]
  have hx3₂ : x * x * x * v₂ * (x * x * x)⁻¹ = v₂ := by
    calc x * x * x * v₂ * (x * x * x)⁻¹ = x * (x * (x * v₂ * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = v₂ := by rw [hx2, hx1, hx12]
  have hfix : ∀ {s v : G}, s * v * s⁻¹ = v → s * v = v * s := fun {s v} h => by
    calc s * v = (s * v * s⁻¹) * s := by group
      _ = v * s := by rw [h]
  have hx3C : x ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    rw [pow_three']
    exact mem_centralizer_of_commute_two hV hV2 hv₁ hv₂ hv₁1 hv₂1 hv₁₂.symm (hfix hx3₁) (hfix hx3₂)
  have hxC : x ∉ Subgroup.centralizer (V : Set G) := by
    intro h
    have hc := Subgroup.mem_centralizer_iff.mp h v₁ hv₁
    have h' : x * v₁ * x⁻¹ = v₁ := by
      calc x * v₁ * x⁻¹ = (v₁ * x) * x⁻¹ := by rw [← hc]
        _ = v₁ := by group
    rw [hx1] at h'
    exact hv₂1 (by simpa using h')
  have hcop : Nat.Coprime 3 (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (Nat.Coprime.pow_right k (by norm_num))
  exact hxC (Subgroup.zpowers_le_of_mem hx3C (A4.mem_zpowers_pow_of_coprime hcop))

private theorem exists_pow_two_pow_eq_one_of_odd {X : Subgroup G} {c : G} (hc : c ∈ X)
    (hX : ∀ y ∈ X, Odd (orderOf y) → y = 1) : ∃ k : ℕ, c ^ 2 ^ k = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨k, hX _ (X.pow_mem hc _) ?_⟩
  have h1 : orderOf (c ^ 2 ^ k) = orderOf c / Nat.gcd (orderOf c) (2 ^ k) :=
    orderOf_pow' c (pow_ne_zero _ two_ne_zero)
  have h2 : Nat.gcd (orderOf c) (2 ^ k) = 2 ^ k := by
    rw [hkm]
    exact Nat.gcd_eq_right (Dvd.intro _ rfl)
  rw [h1, h2, hkm, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem Setting146.facts14610_c3 (h9 : Stage1469W) (h3 : Stage1463Three) {H : Subgroup G} {u : G}
    {I I₂ : Subgroup G} (c : Hyp14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (P : Subgroup G) (hPI : P ≤ I) (hPinv : i1Of1469 T M I ≤ Subgroup.normalizer (P : Set G)) :
    lI T M I ≤ P ∨ P ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  by_cases hn1 : lI T M I ≤ P
  · exact Or.inl hn1
  right
  by_contra hn2
  have S : Setting146 G T M := c.setting
  have hlIinv : lI T M I ≤ Subgroup.normalizer (P : Set G) := le_sup_left.trans hPinv
  have hTIinv : T ⊓ I ≤ Subgroup.normalizer (P : Set G) := le_sup_right.trans hPinv
  have step0 : ∀ y ∈ yOfL22 T M ⊓ P, Odd (orderOf y) → y = 1 := fun y hy hodd =>
    S.no_odd_of_not_lI_le hPI hlIinv hn1 hy.1 hy.2 hodd
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hNV : Subgroup.normalizer (VZ T M : Set G) = M := S.hyp1281.normalizer_VZ
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hsq : ∀ w ∈ VZ T M, w * w = 1 := by
    obtain ⟨hVred, -⟩ := S.hyp1281.isTwoReducedIn
    intro w hw
    simpa [sq] using hVred.2.2.1.2 w hw
  have step1 : P ≤ mcOf T → P ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    intro hPG
    obtain ⟨g, hg, hgG⟩ := IsConcreteLE.not_le_iff_exists.mp (S.not_lI_le_mcOf hLT)
    obtain ⟨z, hzZ, hzg⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * g = g * z) := by
      by_contra hno
      push Not at hno
      exact hgG (Subgroup.mem_centralizer_iff.mpr hno)
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hzg (by simp)
    have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
    have hgL : g ∈ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left hg
    have hgM : g ∈ M := S.hyp1281.le hgL
    have hwV : g * z * g⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hgM) z).mp hzV
    have hw1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hwz : g * z * g⁻¹ ≠ z := by
      intro h
      apply hzg
      calc z * g = (g * z * g⁻¹) * g := by rw [h]
        _ = g * z := by group
    have hPC : P ≤ Subgroup.centralizer (VZ T M : Set G) := by
      intro p hp
      refine mem_centralizer_of_commute_two hV4 hsq hzV hwV hz1 hw1 hwz ?_ ?_
      · exact (Subgroup.mem_centralizer_iff.mp (hPG hp) z hzZ).symm
      · have hgp : g⁻¹ * p * g ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (hlIinv ((lI T M I).inv_mem hg)) p).mp hp
          simpa using this
        have hc := Subgroup.mem_centralizer_iff.mp (hPG hgp) z hzZ
        calc p * (g * z * g⁻¹) = g * ((g⁻¹ * p * g) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * p * g)) * g⁻¹ := by rw [← hc]
          _ = (g * z * g⁻¹) * p := by group
    refine le_inf (fun p hp => ?_) hPC
    rw [← hNV]
    exact Subgroup.centralizer_le_normalizer _ (hPC hp)
  have step2 : P ≤ M → P ≤ mcOf T := by
    intro hPM p hp
    by_contra hpG
    obtain ⟨z, hzZ, hzp⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * p = p * z) := by
      by_contra hno
      push Not at hno
      exact hpG (Subgroup.mem_centralizer_iff.mpr hno)
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hzp (by simp)
    have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
    have hpM : p ∈ M := hPM hp
    have hpN : p ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hpM
    obtain ⟨a, ha, haV⟩ := S.exists_mem_not_centralizer_V (h3 G T M S H c.hH u c.hu).2.1
    have haQ : a ∈ pCoreOf 2 (mcOf T) := ha.1
    have haT : a ∈ T := hQ1T haQ
    have haN : a ∈ Subgroup.normalizer (VZ T M : Set G) := hMV (hTM haT)
    have haI : a ∈ I := c.hI.1.1.1 ((S146T.mem_tU_iff).mpr ⟨haT,
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp ha.2 u rfl).symm⟩)
    have haP : a ∈ Subgroup.normalizer (P : Set G) := hTIinv ⟨haT, haI⟩
    have hza : z * a = a * z := Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ haQ) z hzZ
    have haz : a * z * a⁻¹ = z := by
      calc a * z * a⁻¹ = (z * a) * a⁻¹ := by rw [hza]
        _ = z := by group
    have hv₂ : p * z * p⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hpN z).mp hzV
    have hv₂1 : p * z * p⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
        _ = 1 := by rw [h]; group
    have hv₁₂ : z ≠ p * z * p⁻¹ := by
      intro h
      apply hzp
      calc z * p = (p * z * p⁻¹) * p := by rw [← h]
        _ = p * z := by group
    have hf₁ : a⁻¹ * z * a⁻¹⁻¹ = z := by
      calc a⁻¹ * z * a⁻¹⁻¹ = a⁻¹ * z * a := by group
        _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [haz]
        _ = z := by group
    have hf₂ : (p * a * p⁻¹) * (p * z * p⁻¹) * (p * a * p⁻¹)⁻¹ = p * z * p⁻¹ := by
      calc (p * a * p⁻¹) * (p * z * p⁻¹) * (p * a * p⁻¹)⁻¹ = p * (a * z * a⁻¹) * p⁻¹ := by group
        _ = p * z * p⁻¹ := by rw [haz]
    have hn₁ : a⁻¹ ∉ Subgroup.centralizer (VZ T M : Set G) := fun h =>
      haV (by simpa using (Subgroup.centralizer (VZ T M : Set G)).inv_mem h)
    have hn₂ : p * a * p⁻¹ ∉ Subgroup.centralizer (VZ T M : Set G) := by
      intro h
      apply haV
      have := A1b.conj_mem_centralizer_of_mem_normalizer
        ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hpN) h
      have e : p⁻¹ * (p * a * p⁻¹) * p⁻¹⁻¹ = a := by group
      rwa [e] at this
    set x : G := (p * a * p⁻¹) * a⁻¹ with hxdef
    have hxP : x ∈ P := by
      have h1' : a * p⁻¹ * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp haP p⁻¹).mp (P.inv_mem hp)
      have e : x = p * (a * p⁻¹ * a⁻¹) := by rw [hxdef]; group
      rw [e]
      exact P.mul_mem hp h1'
    have hxL : x ∈ yOfL22 T M ⊔ pCoreOf 2 (mcOf T) := by
      have h1' : p * a * p⁻¹ ∈ yOfL22 T M ⊔ pCoreOf 2 (mcOf T) :=
        (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_L_sup_Q1 hpM) a).mp
          (Subgroup.mem_sup_right haQ)
      exact Subgroup.mul_mem _ h1' (Subgroup.inv_mem _ (Subgroup.mem_sup_right haQ))
    have hQL : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (yOfL22 T M : Set G) := fun q hq =>
      S.hyp1281.normal (hTM (hQ1T hq))
    have hodd : ∀ y ∈ P ⊓ (yOfL22 T M ⊔ pCoreOf 2 (mcOf T)), Odd (orderOf y) → y = 1 :=
      fun y hy hyodd => step0 y ⟨mem_of_odd_orderOf_of_sup_pGroup (pCoreOf_isPGroup 2 (mcOf T))
        hQL hy.2 hyodd, hy.1⟩ hyodd
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_odd (X := P ⊓ (yOfL22 T M ⊔ pCoreOf 2 (mcOf T)))
      ⟨hxP, hxL⟩ hodd
    exact not_pow_two_pow_eq_one_of_fixes hV4 hsq hzV hv₂ hz1 hv₂1 hv₁₂
      ((Subgroup.normalizer (VZ T M : Set G)).inv_mem haN)
      ((Subgroup.normalizer (VZ T M : Set G)).mul_mem
        ((Subgroup.normalizer (VZ T M : Set G)).mul_mem hpN haN)
        ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hpN)) hf₁ hf₂ hn₁ hn₂ k hk
  have hnPG : ¬ P ≤ mcOf T := fun h => hn2 (step1 h)
  have hnPM : ¬ P ≤ M := fun h => hnPG (step2 h)
  have hJI : P ⊔ (T ⊓ I) ≤ I := sup_le hPI inf_le_right
  have hTIJ : T ⊓ I ≤ P ⊔ (T ⊓ I) := le_sup_right
  have hT2 : IsPGroup 2 (T ⊓ I : Subgroup G) := hsyl.2.1
  have hQJ : pCoreOf 2 I ≤ pCoreOf 2 (P ⊔ (T ⊓ I)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_two_le_of_isSylowTwoOf hsyl).trans hTIJ)
      (hJI.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  have hTu : tU T u ≤ T ⊓ I := le_inf inf_le_left c.hI.1.1.1
  have hJ : IsI T M u (P ⊔ (T ⊓ I)) :=
    ⟨⟨hTu.trans hTIJ, fun hbot => c.hI.1.1.2 (le_bot_iff.mp (hQJ.trans hbot.le))⟩,
      fun h => hnPG (le_sup_left.trans h), fun h => hnPM (le_sup_left.trans h)⟩
  obtain ⟨hJstar, -⟩ := c.hI.of_le_inf hJ hTIJ
  have hconc := h9 G T M H u S c.hH c.hu _ hJstar c.hT c.hrank
  have hlJ : lI T M (P ⊔ (T ⊓ I)) = ⊥ := by
    refine eq_bot_iff.mpr ((Subgroup.closure_le _).mpr fun x hx => ?_)
    obtain ⟨⟨hxL, hxJ⟩, hxodd⟩ := hx
    have hxP : x ∈ P := mem_of_odd_orderOf_of_sup_pGroup hT2 hTIinv hxJ hxodd
    rw [step0 x ⟨hxL, hxP⟩ hxodd]
    exact Subgroup.one_mem _
  rw [hlJ, bot_sup_eq] at hconc
  have hW2 : IsPGroup 2 (T ⊓ (P ⊔ (T ⊓ I)) : Subgroup G) := S.hyp.sylow.1.to_le inf_le_left
  have hWN : T ⊓ (P ⊔ (T ⊓ I)) ≤ Subgroup.normalizer (pCoreOf 2 (yOfL22 T M ⊔ T) : Set G) :=
    (inf_le_left.trans le_sup_right).trans (le_normalizer_pCoreOf 2 _)
  have hLbot : yOfL22 T M = ⊥ := by
    rw [← S.hyp1281.residual]
    refine eq_bot_iff.mpr ((Subgroup.closure_le _).mpr fun x hx => ?_)
    obtain ⟨hxL, hxodd⟩ := hx
    have hxLT : x ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hxL
    rw [hconc, sup_comm] at hxLT
    rw [eq_one_of_mem_isPGroup_of_odd_orderOf (pCoreOf_isPGroup 2 _)
      (mem_of_odd_orderOf_of_sup_pGroup hW2 hWN hxLT hxodd) hxodd]
    exact Subgroup.one_mem _
  exact S.not_yOfL22_le_mcOf (hLbot ▸ bot_le)

end CFSG.Quasithin
