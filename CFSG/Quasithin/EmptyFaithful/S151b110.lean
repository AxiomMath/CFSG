module

public import CFSG.Quasithin.EmptyFaithful.S151bW3Grp
public import CFSG.Quasithin.EmptyFaithful.S151bW3Five
public import CFSG.Quasithin.EmptyFaithful.S151b13Six
public import CFSG.Quasithin.EmptyFaithful.S151Dual
public import CFSG.Quasithin.EmptyFaithful.S15113

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem exists_sixData151b {T M V : Subgroup G} {A₀ : Subgroup (MulAut ↥V)}
    (hV : IsElemAbelian 2 V) (hTM : T ≤ M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hA0 : A₀ = Jhat (autI hV M)) {p : ℕ} (hp : p = 3 ∨ p = 5) (c6 : Case1517Six T M V A₀ p) :
    ∃ S : SixData151b (IntMod V hV) p, S.A₁ ≤ autI hV M ∧ S.A₂ ≤ autI hV M ∧ S.τ ∈ autI hV T ∧
      S.A₁ ⊔ S.A₂ = Jhat (autI hV M) ∧ Nat.card (IntMod V hV) = 256 := by
  subst hA0
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hcard : Nat.card V = 256 := c6.1
  obtain ⟨A₁, A₂, ⟨hA₀eq, hA12, hcomm⟩, ⟨e₁⟩, ⟨e₂⟩, ⟨t, htT, hconj⟩, hdsum⟩ :
      ∃ A₁ A₂ : Subgroup (MulAut (IntMod V hV)),
        IsInternalDirect (Jhat (autI hV M)) A₁ A₂ ∧ Nonempty (↥A₁ ≃* DihedralGroup p) ∧
        Nonempty (↥A₂ ≃* DihedralGroup p) ∧
        (∃ t ∈ T, (preOn M V A₁).map (MulAut.conj t).toMonoidHom = preOn M V A₂) ∧
        IsDirectSumOfCommutators M V A₁ A₂ := by
    obtain ⟨-, A₁, A₂, h⟩ := c6
    exact ⟨A₁, A₂, h⟩
  have hA₀X : Jhat (autI hV M) ≤ autI hV M := Jhat_le (autI hV M)
  have hA₁J : A₁ ≤ Jhat (autI hV M) := by rw [hA₀eq]; exact le_sup_left
  have hA₂J : A₂ ≤ Jhat (autI hV M) := by rw [hA₀eq]; exact le_sup_right
  have hA₁X : A₁ ≤ autI hV M := hA₁J.trans hA₀X
  have hA₂X : A₂ ≤ autI hV M := hA₂J.trans hA₀X
  obtain ⟨hW12inf, hW12sup⟩ := six_bridge151b hV hMN hA₁X hA₂X hdsum
  have htN : t ∈ Subgroup.normalizer (V : Set G) := hTN htT
  have hconj' : A₁.map (MulAut.conj (convI hV ⟨t, htN⟩)).toMonoidHom = A₂ := by
    have h1 := autI_cjSub hV htN (preOn M V A₁)
    have e₁' : autI hV (preOn M V A₁) = A₁ := autOn_preOn hA₁X
    have e₂' : autI hV (preOn M V A₂) = A₂ := autOn_preOn hA₂X
    have h2 : cjSub t (preOn M V A₁) = preOn M V A₂ := hconj
    rw [e₁', h2, e₂'] at h1
    exact h1
  set tb := convI hV ⟨t, htN⟩ with htb
  have htbX : tb ∈ autI hV M := convI_mem_autI hV (hTM htT) htN
  have hτ₁₂ : ∀ x ∈ A₁, tb * x * tb⁻¹ ∈ A₂ := by
    intro x hx
    rw [← hconj']
    exact ⟨x, hx, by simp⟩
  have hτ₂₁ : ∀ b ∈ A₂, tb * b * tb⁻¹ ∈ A₁ := by
    intro b hb
    have hbA₀ : tb * b * tb⁻¹ ∈ A₁ ⊔ A₂ := by
      rw [← hA₀eq]
      exact mem_Jhat_conj htbX (hA₂J hb)
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ A₁, ∃ y ∈ A₂, x * y = tb * b * tb⁻¹ := by
      have hset := (card_sup_mul_card_inf_of_commute151b A₁ A₂ hcomm).2
      have h1 : tb * b * tb⁻¹ ∈ ((A₁ ⊔ A₂ : Subgroup _) : Set _) := hbA₀
      rw [hset] at h1
      exact h1
    have hyc : ∀ c ∈ A₂, y * c = c * y := by
      intro c hc
      rw [← hconj'] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      have hcA₂ : tb * a * tb⁻¹ ∈ A₂ := hτ₁₂ a ha
      have hca : (MulAut.conj tb).toMonoidHom a = tb * a * tb⁻¹ := by simp
      rw [hca]
      have hxc : x * (tb * a * tb⁻¹) = (tb * a * tb⁻¹) * x := hcomm x hx _ hcA₂
      have hzc : (x * y) * (tb * a * tb⁻¹) = (tb * a * tb⁻¹) * (x * y) := by
        rw [hxy]
        have hab := hcomm a ha b hb
        calc tb * b * tb⁻¹ * (tb * a * tb⁻¹) = tb * (b * a) * tb⁻¹ := by group
          _ = tb * (a * b) * tb⁻¹ := by rw [hab]
          _ = tb * a * tb⁻¹ * (tb * b * tb⁻¹) := by group
      apply mul_left_cancel (a := x)
      calc x * (y * (tb * a * tb⁻¹)) = (x * y) * (tb * a * tb⁻¹) := by group
        _ = (tb * a * tb⁻¹) * (x * y) := hzc
        _ = ((tb * a * tb⁻¹) * x) * y := by group
        _ = (x * (tb * a * tb⁻¹)) * y := by rw [hxc]
        _ = x * ((tb * a * tb⁻¹) * y) := by group
    have hcentral : ∀ w : ↥A₂, (⟨y, hy⟩ : ↥A₂) * w = w * ⟨y, hy⟩ := fun w =>
      Subtype.ext (hyc w.1 w.2)
    have hd : ∀ d' : DihedralGroup p, e₂ ⟨y, hy⟩ * d' = d' * e₂ ⟨y, hy⟩ := by
      intro d'
      obtain ⟨w, rfl⟩ := e₂.surjective d'
      rw [← map_mul, ← map_mul, hcentral w]
    have h1 := dih_center_one151b hp _ hd
    have h3 : (⟨y, hy⟩ : ↥A₂) = 1 := e₂.injective (h1.trans (map_one e₂).symm)
    have hy1 : y = 1 := congrArg Subtype.val h3
    rw [← hxy, hy1, mul_one]
    exact hx
  exact ⟨⟨A₁, A₂, e₁, e₂, hcomm, hA12, hW12inf, hW12sup, tb, hτ₁₂, hτ₂₁⟩, hA₁X, hA₂X,
    convI_mem_autI hV htT htN, hA₀eq.symm, hcard⟩

omit [Finite G] in
theorem normal_two_subgroup_eq_bot151b {W : Type*} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (hO2 : pCoreOf 2 X = ⊥) :
    ∀ N : Subgroup ↥X, N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hNp
  have hle : N ≤ CFSG.Open.pCore 2 ↥X := le_pCore_open151b hN hNp
  have hbot : CFSG.Open.pCore 2 ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hO2
  exact le_bot_iff.mp (hbot ▸ hle)

theorem pRank_three_top_le_two151b (hK : quasithinIsQTKECat G) {M : Subgroup G}
    (hM2 : pCoreOf 2 M ≠ ⊥) : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 2 := by
  rw [pRank_top_subtype (p := 3) M]
  exact pRank_le_two_of_pCoreOf_ne_bot hK hM2 (by norm_num) (by norm_num)

theorem lemma15110_of151b {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hred : IsTwoReducedIn M (V154 T Mc M))
    (hsolv : Group.IsSolvable ↥(autOn M (V154 T Mc M))) :
    Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 3 →
      Nonempty (↥(autOn M (V154 T Mc M)) ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) := by
  intro c6
  have hV : IsElemAbelian 2 (V154 T Mc M) := hred.2.2.1
  have hTM : T ≤ M := hM.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hA0 : mBar0 T Mc M = Jhat (autI hV M) := JhatOn_eq hV
  obtain ⟨S, hA₁X, hA₂X, hτX, hsup, hcard⟩ :=
    exists_sixData151b hV hTM hMN hA0 (Or.inl rfl) c6
  have hW : ∀ w : IntMod (V154 T Mc M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hnorm : ∀ g ∈ autI hV M, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂ := by
    rw [hsup]
    intro g hg z hz
    exact mem_Jhat_conj hg hz
  have hM2 : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1.1.1
  have hO2 : pCoreOf 2 (autI hV M) = ⊥ := pCoreOf_autOn_eq_bot_of_isTwoReducedIn hred
  exact S.nonempty_mulEquiv_wreath3_of_solvable hW hcard hA₁X hA₂X ((autI_mono hV hTM) hτX) hnorm hsolv
    (normal_two_subgroup_eq_bot151b hO2) (autISurj151b hV M hMN) (autISurj151b_surjective hV M hMN)
    (pRank_three_top_le_two151b h.qtke hM2)

theorem rank_bound_five151b {T Mc M : Subgroup G} (hM : IsMf T Mc M)
    (hV : IsElemAbelian 2 (V154 T Mc M)) :
    Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 5 →
      ∀ E : Subgroup (MulAut (IntMod (V154 T Mc M) hV)), E ≤ autI hV T → IsElemAbelian2 E →
        Nat.card E ≤ 4 := by
  intro c6 E hET hE
  have hTM : T ≤ M := hM.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hA0 : mBar0 T Mc M = Jhat (autI hV M) := JhatOn_eq hV
  obtain ⟨S, hA₁X, hA₂X, hτX, hsup, hcard⟩ :=
    exists_sixData151b hV hTM hMN hA0 (Or.inr rfl) c6
  have hW : ∀ w : IntMod (V154 T Mc M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hnorm : ∀ g ∈ E, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂ := by
    rw [hsup]
    intro g hg z hz
    exact mem_Jhat_conj ((autI_mono hV hTM) (hET hg)) hz
  exact S.card_le_four_of_elemAbelian hW hcard hE hnorm

theorem stageLemma15110_of (h1416 : StageLemma1416) (h1515 : StageLemma1515) : StageLemma15110 := by
  intro G _ _ T Mc M h hM _ c6
  have hred := (h1515 G T Mc M h hM).reduced
  exact lemma15110_of151b h hM hred
    (isSolvable_autOn_of_perfectCore_le hred.2.1 ((h1416 G T Mc h).1 M _ hM.1.1 hred)) c6

theorem stageLemma15113Three_of (h157 : StageLemma1517) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h1515 : StageLemma1515) (h15110 : StageLemma15110) :
    StageLemma15113Three := by
  intro G _ _ T Mc M h hM hCE
  have hred := (h1515 G T Mc M h hM).reduced
  exact lemma15113Three_of_cases151b h hM (h157 G T Mc M h hM hCE) (h158 G T Mc M h hM hCE)
    (h159 G T Mc M h hM hCE) hred (h15110 G T Mc M h hM hCE)
    (fun hV => rank_bound_five151b hM hV)

theorem stageLemma15113Four_of (h157 : StageLemma1517) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h1515 : StageLemma1515) (h15110 : StageLemma15110)
    (h1512four : StageLemma15112Four) : StageLemma15113Four := by
  intro G _ _ T Mc M h hM hCE
  have hred := (h1515 G T Mc M h hM).reduced
  have hone := lemma_15_1_13_one h hM (fun H hH => h1512four G T Mc M h hM hCE H hH)
  have h2 := lemma_15_1_13_two h hM (h157 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE) hone
  exact lemma15113Four_of_cases151b h hM (h157 G T Mc M h hM hCE) (h158 G T Mc M h hM hCE)
    (h159 G T Mc M h hM hCE) hred (h15110 G T Mc M h hM hCE)
    (fun hV => rank_bound_five151b hM hV) h2

end CFSG.Quasithin
