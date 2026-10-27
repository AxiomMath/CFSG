module

public import CFSG.Quasithin.Vol2.Ch12Sec8OnePara
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

theorem exists_transvection {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {P : Submodule (ZMod 2) W} {a b : W} (hb : b ∉ P ⊔ (ZMod 2) ∙ a) :
    ∃ τ : W ≃ₗ[ZMod 2] W, (∀ x, τ (τ x) = x) ∧ τ a = a ∧ τ b = a + b ∧
      (∀ x ∈ P, τ x = x) ∧ ∀ x, ∃ t : ZMod 2, τ x = x + t • a := by
  obtain ⟨f₀, hf, hP⟩ := Submodule.exists_le_ker_of_notMem hb
  set f := (f₀ b)⁻¹ • f₀ with hfdef
  have hf1 : f b = 1 := by
    rw [hfdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
  have hker : ∀ {x : W}, f₀ x = 0 → f x = 0 := fun h => by
    rw [hfdef, LinearMap.smul_apply, h, smul_zero]
  have hfa : f a = 0 :=
    hker (LinearMap.mem_ker.1 (hP (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))))
  have hfP : ∀ x ∈ P, f x = 0 := fun x hx =>
    hker (LinearMap.mem_ker.1 (hP (Submodule.mem_sup_left hx)))
  have hadd : ∀ t : ZMod 2, t + t = 0 := by decide
  let τ0 : W →ₗ[ZMod 2] W := LinearMap.id + f.smulRight a
  have hτ0 : ∀ x, τ0 x = x + f x • a := fun x => rfl
  have h2 : ∀ x, τ0 (τ0 x) = x := by
    intro x
    rw [hτ0 (τ0 x), hτ0 x, map_add, map_smul, hfa, smul_zero, add_zero, add_assoc, ← add_smul,
      hadd, zero_smul, add_zero]
  let τ : W ≃ₗ[ZMod 2] W := LinearEquiv.ofLinearMap τ0 τ0 (LinearMap.ext fun x => h2 x)
    (LinearMap.ext fun x => h2 x)
  refine ⟨τ, h2, ?_, ?_, fun x hx => ?_, fun x => ⟨f x, hτ0 x⟩⟩
  · show τ0 a = a
    rw [hτ0, hfa, zero_smul, add_zero]
  · show τ0 b = a + b
    rw [hτ0, hf1, one_smul, add_comm]
  · show τ0 x = x
    rw [hτ0, hfP x hx, zero_smul, add_zero]

namespace L128P

variable {G : Type} [Group G]

theorem exists_conj_pair {X : Subgroup G} {k l a b : G} (hk : k ∈ X) (hl : l ∈ X)
    (hka : k * a * k⁻¹ = b) (hkb : k * b * k⁻¹ = a * b) (hla : l * a * l⁻¹ = a)
    (hlb : l * b * l⁻¹ = a * b) (hcomm : a * b = b * a) (hb2 : b * b = 1)
    {a' b' : G} (ha' : a' = a ∨ a' = b ∨ a' = a * b) (hb' : b' = a ∨ b' = b ∨ b' = a * b)
    (hne : a' ≠ b') : ∃ p ∈ X, p * a * p⁻¹ = a' ∧ p * b * p⁻¹ = b' := by
  have hc : ∀ p y z : G, p * (y * z) * p⁻¹ = (p * y * p⁻¹) * (p * z * p⁻¹) := fun p y z => by
    group
  have hm : ∀ p q y : G, (p * q) * y * (p * q)⁻¹ = p * (q * y * q⁻¹) * p⁻¹ := fun p q y => by
    group
  have hkab : k * (a * b) * k⁻¹ = a := by
    rw [hc, hka, hkb, ← mul_assoc, ← hcomm, mul_assoc, hb2, mul_one]
  rcases ha' with e1 | e1 | e1 <;> rcases hb' with e2 | e2 | e2 <;> rw [e1, e2] at hne ⊢
  · exact absurd rfl hne
  · exact ⟨1, X.one_mem, by group, by group⟩
  · exact ⟨l, hl, hla, hlb⟩
  · exact ⟨k * l, X.mul_mem hk hl, by rw [hm, hla, hka], by rw [hm, hlb, hkab]⟩
  · exact absurd rfl hne
  · exact ⟨k, hk, hka, hkb⟩
  · exact ⟨k * k, X.mul_mem hk hk, by rw [hm, hka, hkb], by rw [hm, hkb, hkab]⟩
  · exact ⟨k * k * l, X.mul_mem (X.mul_mem hk hk) hl, by rw [hm, hla, hm, hka, hkb],
      by rw [hm, hlb, hm, hkab, hka]⟩
  · exact absurd rfl hne

variable [Finite G]

theorem exists_transvection_mem (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) {a b : G} (ha : a ∈ V₁) (hb : b ∈ V₂)
    (hbV₁ : b ∉ V₁) : ∃ l ∈ p128 T L V, l * a * l⁻¹ = a ∧ l * b * l⁻¹ = a * b := by
  classical
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  have haV : a ∈ V := hV₁.1 ha
  have hbV : b ∈ V := hV₂.1 hb
  let _ := zmodModuleOf hsq
  set a' : Additive ↥V := Additive.ofMul ⟨a, haV⟩ with ha'
  set b' : Additive ↥V := Additive.ofMul ⟨b, hbV⟩ with hb'
  have hb'' : b' ∉ (⊥ : Submodule (ZMod 2) (Additive ↥V)) ⊔ (ZMod 2) ∙ a' := by
    rw [bot_sup_eq]
    intro hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
    have h1 := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) ht
    rcases zmod_two_cases t with rfl | rfl
    · simp only [zero_smul, toMul_zero, OneMemClass.coe_one, hb', toMul_ofMul] at h1
      exact hbV₁ (h1 ▸ V₁.one_mem)
    · simp only [one_smul, ha', hb', toMul_ofMul] at h1
      exact hbV₁ (h1 ▸ ha)
  obtain ⟨τ, -, hτa, hτb, -, hτx⟩ := exists_transvection hb''
  have hαL : mulAutOfLin τ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ = ((mulAutOfLin τ ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hlα]
    rfl
  have hmod : ∀ x (hx : x ∈ V), ((mulAutOfLin τ ⟨x, hx⟩ : ↥V) : G) * x⁻¹ ∈ V₁ := by
    intro x hx
    obtain ⟨t, ht⟩ := hτx (Additive.ofMul ⟨x, hx⟩)
    rw [mulAutOfLin_apply, ht]
    rcases zmod_two_cases t with rfl | rfl
    · simp
    · rw [one_smul, toMul_add, toMul_ofMul, ha', toMul_ofMul, Subgroup.coe_mul, hab x hx a haV,
        mul_inv_cancel_right]
      exact ha
  have hlP : l ∈ p128 T L V := mem_p128_of_conj h1222 h hV₂ hlL' hlN fun x hx => by
    rw [hconj x hx]
    exact hle (hmod x hx)
  refine ⟨l, hlP, ?_, ?_⟩
  · rw [hconj a haV, mulAutOfLin_apply, ← ha', hτa, ha', toMul_ofMul]
  · rw [hconj b hbV, mulAutOfLin_apply, ← hb', hτb, toMul_add, ha', hb', toMul_ofMul,
      toMul_ofMul, Subgroup.coe_mul]

theorem exists_mem_mul_mem_centralizer (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) {x : G}
    (hx : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    ∃ p ∈ p128 T L V, p⁻¹ * x ∈ Subgroup.centralizer (V₂ : Set G) := by
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ := exists_rotation_mem h1222 h hV₁ hV₂ hle ha ha1 hb hbV₁
  obtain ⟨l, hl, hla, hlb⟩ := exists_transvection_mem h1222 h hV₁ hV₂ hle ha hb hbV₁
  have haV : a ∈ V := hV₁.1 ha
  have hbV : b ∈ V := hV₂.1 hb
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hsq b hbV
  have hxa : x * a * x⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hx a).mp (hle ha)
  have hxb : x * b * x⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hx b).mp hb
  have hinj : ∀ y z : G, x * y * x⁻¹ = x * z * x⁻¹ → y = z := fun y z e => by
    have := congrArg (fun w => x⁻¹ * w * x) e
    simpa [mul_assoc] using this
  have hb1 : b ≠ 1 := fun e => hbV₁ (e ▸ V₁.one_mem)
  have hsel : ∀ {y : G}, y ∈ V₂ → y ≠ 1 → y = a ∨ y = b ∨ y = a * b := fun hy hy1 => by
    rcases eq_of_mem_four hle hV₁2 hV₂4 ha ha1 hbV₁ hb hy with e | e | e | e
    · exact absurd e hy1
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  have hne1 : ∀ y : G, y ≠ 1 → x * y * x⁻¹ ≠ 1 := fun y hy e =>
    hy (hinj y 1 (by rw [e]; group))
  obtain ⟨p, hp, hpa, hpb⟩ := exists_conj_pair (X := p128 T L V) (oTwoUpper_le _ hk) hl hka hkb
    hla hlb (hab a haV b hbV) hb2 (hsel hxa (hne1 a ha1)) (hsel hxb (hne1 b hb1))
    (fun e => hbV₁ (hinj a b e ▸ ha))
  refine ⟨p, hp, ?_⟩
  have hfix : ∀ {y : G}, p * y * p⁻¹ = x * y * x⁻¹ → (p⁻¹ * x) * y * (p⁻¹ * x)⁻¹ = y := by
    intro y e
    calc (p⁻¹ * x) * y * (p⁻¹ * x)⁻¹ = p⁻¹ * (x * y * x⁻¹) * p := by group
      _ = p⁻¹ * (p * y * p⁻¹) * p := by rw [e]
      _ = y := by group
  have hfa := hfix hpa
  have hfb := hfix hpb
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases eq_of_mem_four hle hV₁2 hV₂4 ha ha1 hbV₁ hb hv with e | e | e | e <;> rw [e]
  · group
  · calc a * (p⁻¹ * x) = ((p⁻¹ * x) * a * (p⁻¹ * x)⁻¹) * (p⁻¹ * x) := by rw [hfa]
      _ = (p⁻¹ * x) * a := by group
  · calc b * (p⁻¹ * x) = ((p⁻¹ * x) * b * (p⁻¹ * x)⁻¹) * (p⁻¹ * x) := by rw [hfb]
      _ = (p⁻¹ * x) * b := by group
  · calc a * b * (p⁻¹ * x) =
        ((p⁻¹ * x) * a * (p⁻¹ * x)⁻¹) * ((p⁻¹ * x) * b * (p⁻¹ * x)⁻¹) * (p⁻¹ * x) := by
          rw [hfa, hfb]
      _ = (p⁻¹ * x) * (a * b) := by group

theorem oTwoUpper_sup_eq {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n) :
    oTwoUpper (p128 T L V) ⊔ T = p128 T L V :=
  C1Pack12.oTwoUpper_sup_eq_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.sylow le_p128)

theorem exists_mul_eq {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n) {g : G}
    (hg : g ∈ p128 T L V) : ∃ t ∈ T, ∃ k ∈ oTwoUpper (p128 T L V), g = t * k := by
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper (p128 T L V) : Set G) :=
    le_p128.trans (le_normalizer_oTwoUpper _)
  have hmem : g ∈ (T : Set G) * (oTwoUpper (p128 T L V) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK, sup_comm, oTwoUpper_sup_eq h]
    exact hg
  obtain ⟨t, ht, k, hk, rfl⟩ := hmem
  exact ⟨t, ht, k, hk, rfl⟩

theorem exists_conjugate_eq {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {g : G} (hg : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    ∃ k ∈ oTwoUpper (p128 T L V), k ∉ Subgroup.normalizer (V₁ : Set G) ∧
      ∀ Y : Subgroup G, T ≤ Subgroup.normalizer (Y : Set G) →
        CFSG.conjugate Y g = CFSG.conjugate Y k := by
  obtain ⟨t, ht, k, hk, rfl⟩ := exists_mul_eq h hg
  exact ⟨k, hk, fun hkN => hgN (Subgroup.mul_mem _ (hV₁.2.2 ht) hkN),
    fun Y hY => rconj_mul_eq_of_mem_normalizer (hY ht) k⟩

theorem exists_not_mem_normalizer (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    ∃ k ∈ oTwoUpper (p128 T L V), k ∉ Subgroup.normalizer (V₁ : Set G) := by
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, -, -⟩ := exists_rotation_mem h1222 hs.hyp hs.v1 hs.v2 hs.le ha ha1 hb hbV₁
  exact ⟨k, hk, fun hkN => hbV₁ (hka ▸ (Subgroup.mem_normalizer_iff.mp hkN a).mp ha)⟩

theorem i128_eq_sup (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    i128 T L V V₁ = oTwoUpper (p128 T L V) ⊔ u128 V V₁ := by
  have hA2 := almostSpecialL2Hyp h1222 h12213 hs
  have hA := hs.almostSpecial h1222 h12213
  obtain ⟨k, hk, hkN⟩ := exists_not_mem_normalizer h1222 hs
  have h2 := hA2.G23_two hk hkN
  rw [← lemma12_8_8_six h1222 hs] at h2
  have hUT : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) := hA.G22_three.2
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper (p128 T L V) : Set G) :=
    le_p128.trans (le_normalizer_oTwoUpper _)
  apply le_antisymm
  · have hPN : p128 T L V ≤ Subgroup.normalizer
        ((oTwoUpper (p128 T L V) ⊔ u128 V V₁ : Subgroup G) : Set G) := by
      exact (oTwoUpper_sup_eq hs.hyp).ge.trans (sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (LieType.Steinberg.le_normalizer_sup hTK hUT))
    exact conjClosure_le fun p hp u hu =>
      (Subgroup.mem_normalizer_iff.mp (hPN hp) u).mp (Subgroup.mem_sup_right hu)
  · rw [← h2]
    refine sup_le (le_conjClosure _ _) fun y hy => ?_
    rw [mem_rconj] at hy
    have e : y = k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ := by group
    rw [e]
    exact mem_conjClosure (Subgroup.inv_mem _ (oTwoUpper_le _ hk)) hy

theorem i128_eq_sup_conjugate (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) {g : G}
    (hg : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    i128 T L V V₁ = u128 V V₁ ⊔ CFSG.conjugate (u128 V V₁) g := by
  have hA2 := almostSpecialL2Hyp h1222 h12213 hs
  have hA := hs.almostSpecial h1222 h12213
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  have h2 := hA2.G23_two hk hkN
  rw [← lemma12_8_8_six h1222 hs] at h2
  rw [hkY _ hA.G22_three.2, i128_eq_sup h1222 h12213 hs, ← h2]
  rfl

theorem i128_le_p128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    i128 T L V V₁ ≤ p128 T L V := by
  have hUT : u128 V V₁ ≤ T := (hs.almostSpecial h1222 h12213).G22_three.1
  exact conjClosure_le fun p hp u hu =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hp (le_p128 (hUT hu))) (Subgroup.inv_mem _ hp)

theorem i128_inf_centralizer (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    i128 T L V V₁ ⊓ Subgroup.centralizer (V₂ : Set G) = pCoreOf 2 (i128 T L V V₁) := by
  have hUT : u128 V V₁ ≤ T := (hs.almostSpecial h1222 h12213).G22_three.1
  have hIP := i128_le_p128 h1222 h12213 hs
  have hIN : i128 T L V V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    hIP.trans (p128_le_normalizer le_rfl hs.v2)
  have hTI : T ≤ Subgroup.normalizer (i128 T L V V₁ : Set G) :=
    le_p128.trans (le_normalizer_conjClosure _ _)
  have hKI : oTwoUpper (p128 T L V) ≤ i128 T L V V₁ := by
    rw [i128_eq_sup h1222 h12213 hs]
    exact le_sup_left
  apply le_antisymm
  · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer
        (hIN.trans (normalizer_le_normalizer_centralizer'' V₂))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      ((isPGroup_centralizer_p128 h1222 hs.hyp hs.v1 hs.le).to_le (inf_le_inf_right _ hIP))
  · refine le_inf (LieType.BorelTits.pCoreOf_le 2 _) ((LieType.BorelTits.le_pCoreOf_of_le_normalizer
      2 ?_ ?_ (LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans
      (pCoreOf_le_centralizer h1222 hs.hyp hs.v1 hs.v2 hs.le))
    · refine (LieType.BorelTits.pCoreOf_le 2 _).trans ?_
      rw [i128_eq_sup h1222 h12213 hs]
      exact sup_le_sup_left hUT _
    · exact sup_le (hKI.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (hTI.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))

theorem centralizer_le_normalizer_i128 {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) :
    Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (i128 T L V V₁ : Set G) := by
  have hPN : p128 T L V ≤ Subgroup.normalizer (Subgroup.centralizer (V₂ : Set G) : Set G) :=
    (p128_le_normalizer le_rfl hs.v2).trans (normalizer_le_normalizer_centralizer'' V₂)
  have hCU : Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    (Subgroup.centralizer_le (show (V₁ : Set G) ⊆ V₂ from hs.le)).trans
      ((Subgroup.centralizer_le_normalizer _).trans (le_normalizer_conjClosure V _))
  have key : ∀ c ∈ Subgroup.centralizer (V₂ : Set G), ∀ y ∈ i128 T L V V₁,
      c * y * c⁻¹ ∈ i128 T L V V₁ := by
    intro c hc y hy
    have hle : i128 T L V V₁ ≤ (i128 T L V V₁).comap (MulAut.conj c).toMonoidHom := by
      refine conjClosure_le fun p hp u hu => ?_
      rw [Subgroup.mem_comap]
      have hc' : p⁻¹ * c * p ∈ Subgroup.centralizer (V₂ : Set G) := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPN hp)) c).mp hc
        simpa using this
      have hu' : (p⁻¹ * c * p) * u * (p⁻¹ * c * p)⁻¹ ∈ u128 V V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hCU hc') u).mp hu
      have e : (MulAut.conj c).toMonoidHom (p * u * p⁻¹) =
          p * ((p⁻¹ * c * p) * u * (p⁻¹ * c * p)⁻¹) * p⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact mem_conjClosure hp hu'
    have := hle hy
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key c hc y, fun hy => ?_⟩
  have e : y = c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ := by group
  rw [e]
  exact key c⁻¹ (Subgroup.inv_mem _ hc) _ hy

theorem normalizer_le_normalizer_i128 (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (i128 T L V V₁ : Set G) := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := exists_mem_mul_mem_centralizer h1222 hs.hyp hs.v1 hs.v2 hs.le hx
  have e : x = p * (p⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (le_normalizer_conjClosure _ _ hp)
    (centralizer_le_normalizer_i128 hs hpx)

theorem oTwoUpper_i128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    oTwoUpper (i128 T L V V₁) = oTwoUpper (p128 T L V) := by
  refine le_antisymm (oTwoUpper_mono (i128_le_p128 h1222 h12213 hs)) ?_
  rw [← oTwoUpper_oTwoUpper (p128 T L V)]
  refine oTwoUpper_mono ?_
  rw [i128_eq_sup h1222 h12213 hs]
  exact le_sup_left

theorem normalizer_le_normalizer_oTwoUpper_p128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (oTwoUpper (p128 T L V) : Set G) := by
  rw [← oTwoUpper_i128 h1222 h12213 hs]
  exact (normalizer_le_normalizer_i128 h1222 hs).trans (normalizer_le_normalizer_oTwoUpper _)

theorem lemma12_8_9_one (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) {g : G} (hg : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    (i128 T L V V₁ = oTwoUpper (p128 T L V) ⊔ u128 V V₁ ∧
        i128 T L V V₁ = u128 V V₁ ⊔ CFSG.conjugate (u128 V V₁) g) ∧
      i128 T L V V₁ ⊓ Subgroup.centralizer (V₂ : Set G) = pCoreOf 2 (i128 T L V V₁) ∧
      Subgroup.normalizer (V₂ : Set G) ≤
        Subgroup.normalizer (oTwoUpper (p128 T L V) : Set G) ∧
      Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (i128 T L V V₁ : Set G) :=
  ⟨⟨i128_eq_sup h1222 h12213 hs, i128_eq_sup_conjugate h1222 h12213 hs hg hgN⟩,
    i128_inf_centralizer h1222 h12213 hs, normalizer_le_normalizer_oTwoUpper_p128 h1222 h12213 hs,
    normalizer_le_normalizer_i128 h1222 hs⟩

end L128P

end CFSG.Quasithin.H13
