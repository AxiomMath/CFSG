module

public import CFSG.Quasithin.EmptyFaithful.S152He7Seven
public import CFSG.Quasithin.EmptyFaithful.S152He7Wr

public section

namespace CFSG.Quasithin.He7

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin CFSG.Quasithin.He6
open scoped commutatorElement

section Reduce

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem iii_shape_reduce (hpure : PureShapeSeven)
    {K T X Q E Lc Lt A N : Subgroup Γ} {t : Γ}
    (hXKT : X = K ⊔ T) (hXn : ∀ g ∈ X, ∀ κ ∈ K, g * κ * g⁻¹ ∈ K) (hsyl : IsSylowTwoOf T X)
    (hK : K = Lc ⊔ Lt) (hperf : ⁅Lc, Lc⁆ = Lc)
    (hLt : Mv t⁻¹ Lt Lc) (hLc : Mv t⁻¹ Lc Lt) (ht : t ∈ T)
    (hTperm : ∀ s ∈ T, (Mv s⁻¹ Lc Lc ∧ Mv s⁻¹ Lt Lt) ∨ (Mv s⁻¹ Lc Lt ∧ Mv s⁻¹ Lt Lc))
    (hcomm : ⁅Lc, Lt⁆ ≤ Q) (hO2L : ∀ x : ↥Lc, x ∈ CFSG.Open.pCore 2 ↥Lc → (x : Γ) ∈ Q)
    (hFamQ : IsL2Prime 7 (OTwoQuot Lc)) (hQ2 : IsPGroup 2 Q)
    (hQn : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hQX : Q ≤ X)
    (hET : E ≤ T) (hEn : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hchief : IsChiefStep X Q A N) (hnot : ¬ ⁅N, E⁆ ≤ A)
    (hbound : Nat.card ↥(⁅N, E⁆ ⊔ A) ≤ 4 * Nat.card A) (hSQX : SQTKGroup (OTwoQuot X)) :
    Nonempty (OTwoQuot X ≃* L32WrZ2) := by
  classical
  have hLcK : Lc ≤ K := by rw [hK]; exact le_sup_left
  have hLtK : Lt ≤ K := by rw [hK]; exact le_sup_right
  have hKX : K ≤ X := by rw [hXKT]; exact le_sup_left
  have hTX : T ≤ X := hsyl.1
  have hLcX : Lc ≤ X := hLcK.trans hKX
  have hLtX : Lt ≤ X := hLtK.trans hKX
  have hEX : E ≤ X := hET.trans hTX
  have hXL : X ≤ Subgroup.normalizer (A : Set Γ) := D14.le_normalizer_of_isNormalIn hchief.2.1
  have hXN : X ≤ Subgroup.normalizer (N : Set Γ) := D14.le_normalizer_of_isNormalIn hchief.1
  have hNQ : N ≤ Q := hchief.1.1
  have hNL : N ≤ Subgroup.normalizer (A : Set Γ) := (hNQ.trans hQX).trans hXL
  have hLN : A ≤ N := hchief.2.2.1.le
  have hE' : IsElemAbelian 2 (Ch3z.chiefMod A N) := isElemAbelian_chiefMod hchief hQX hQ2
  let _ : CommGroup ↥(Ch3z.chiefMod A N) := Ch3z.chiefCG hE'
  have hW : ∀ w : ↥(Ch3z.chiefMod A N), w * w = 1 := fun w => by
    simpa [sq] using Ch3z.chiefMod_sq hE' w
  set ψ : ↥X →* MulAut ↥(Ch3z.chiefMod A N) := Ch3z.chiefPsi hXL hXN with hψ
  set X' : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := Ch3z.chiefAut X A N with hX'
  have hψX' : ∀ g, ψ g ∈ X' := Ch3z.chiefPsi_mem hXL hXN
  have hsurj : ∀ x ∈ X', ∃ g, ψ g = x := by
    intro x hx
    obtain ⟨g, hg⟩ := Ch3z.chiefHom_surjective hXL hXN ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  have hO2 : ∀ Q' : Subgroup (MulAut ↥(Ch3z.chiefMod A N)), Q' ≤ X' →
      (Q'.subgroupOf X').Normal → IsPGroup 2 Q' → Q' = ⊥ :=
    fun Q' h1 h2 h3 => D15Proof.normal_two_eq_bot hQX hchief hE' Q' h1 h2 h3
  have hQψ : ∀ g : ↥X, (g : Γ) ∈ Q → ψ g = 1 := fun g hg =>
    map_eq_one_of_normal_two152 ψ hψX' hsurj hO2 hQn hQ2 hg
  have hnotAll : ∃ e₁ : ↥X, (e₁ : Γ) ∈ E ∧ ψ e₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnot
    exact Subgroup.commutator_le.mpr fun n hn e he =>
      commutator_mem_of_chiefPsi_eq_one hXL hXN hNL (hall ⟨e, hEX he⟩ he) hn
  set Ab : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (Lc.subgroupOf X).map ψ with hAb
  set Ab' : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (Lt.subgroupOf X).map ψ with hAb'
  set Tb : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (T.subgroupOf X).map ψ with hTb
  set Vb : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) := (E.subgroupOf X).map ψ with hVb
  set tX : ↥X := ⟨t, hTX ht⟩ with htX
  set τ : MulAut ↥(Ch3z.chiefMod A N) := ψ tX with hτ
  have hLt' : Mv t Lc Lt := by simpa using hLt.inv
  have hLc' : Mv t Lt Lc := by simpa using hLc.inv
  have hmvt : Mv τ Ab Ab' := Mv_map ψ tX hLt'
  have hmvt' : Mv τ Ab' Ab := Mv_map ψ tX hLc'
  have hKimg : (K.subgroupOf X).map ψ = Ab ⊔ Ab' := by
    rw [hK, Subgroup.subgroupOf_sup hLcX hLtX, Subgroup.map_sup]
  have hAbX : Ab ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hAb'X : Ab' ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hTbX : Tb ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hXKT' : ∀ x ∈ X', ∃ κ ∈ Ab ⊔ Ab', ∃ s ∈ Tb, x = κ * s := by
    intro x hx
    obtain ⟨g, rfl⟩ := hsurj x hx
    have hgsup : (g : Γ) ∈ K ⊔ T := by
      rw [← hXKT]
      exact g.2
    obtain ⟨κ, hκ, s, hs, hgks⟩ := mem_sup_eq_mul
      (fun s hs κ hκ => hXn s (hTX hs) κ hκ) hgsup
    refine ⟨ψ ⟨κ, hKX hκ⟩, ?_, ψ ⟨s, hTX hs⟩, ⟨⟨s, hTX hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, ?_⟩
    · rw [← hKimg]
      exact ⟨⟨κ, hKX hκ⟩, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
    · rw [← map_mul]
      congr 1
      exact Subtype.ext hgks
  by_cases hAb0 : Ab = ⊥
  ·
    exfalso
    have hAb'0 : Ab' = ⊥ := by
      rw [← map_conj_eq_of_Mv hmvt, hAb0, Subgroup.map_bot]
    have hK'bot : (K.subgroupOf X).map ψ = ⊥ := by
      rw [hKimg, hAb0, hAb'0, sup_bot_eq]
    have h2pow : ∀ x ∈ X', ∃ m : ℕ, x ^ 2 ^ m ∈ (K.subgroupOf X).map ψ := by
      intro x hx
      obtain ⟨g, rfl⟩ := hsurj x hx
      have hgsup : (g : Γ) ∈ K ⊔ T := by
        rw [← hXKT]
        exact g.2
      obtain ⟨κ, hκ, s, hs, hgks⟩ := mem_sup_eq_mul
        (fun s hs κ hκ => hXn s (hTX hs) κ hκ) hgsup
      obtain ⟨m, hm⟩ := hsyl.2.1 ⟨s, hs⟩
      have hsm : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hκ1 : ψ ⟨κ, hKX hκ⟩ = 1 := by
        have : ψ ⟨κ, hKX hκ⟩ ∈ (K.subgroupOf X).map ψ :=
          ⟨⟨κ, hKX hκ⟩, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
        rw [hK'bot] at this
        exact Subgroup.mem_bot.mp this
      refine ⟨m, ?_⟩
      have hg : g = ⟨κ, hKX hκ⟩ * ⟨s, hTX hs⟩ := Subtype.ext hgks
      have : ψ g ^ 2 ^ m = 1 := by
        rw [hg, map_mul, hκ1, one_mul, ← map_pow]
        have : (⟨s, hTX hs⟩ : ↥X) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hsm)
        rw [this, map_one]
      rw [this]
      exact Subgroup.one_mem _
    have hX'bot : X' = ⊥ := eq_bot_of_two_pow152 hO2 h2pow (fun k hk => by
      rw [hK'bot] at hk
      exact Subgroup.mem_bot.mp hk)
    obtain ⟨e₁, -, he₁⟩ := hnotAll
    apply he₁
    have := hψX' e₁
    rw [hX'bot] at this
    exact Subgroup.mem_bot.mp this
  let ψL : ↥Lc →* MulAut ↥(Ch3z.chiefMod A N) := ψ.comp (Subgroup.inclusion hLcX)
  have hle : CFSG.Open.pCore 2 ↥Lc ≤ ψL.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hQψ (Subgroup.inclusion hLcX x) (hO2L x hx)
  let π0 : OTwoQuot Lc →* MulAut ↥(Ch3z.chiefMod A N) := QuotientGroup.lift _ ψL hle
  have hπ0range : π0.range = Ab := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨Subgroup.inclusion hLcX x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨QuotientGroup.mk ⟨(g : Γ), Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩
  obtain ⟨e7⟩ := hFamQ
  have hsimple : IsSimpleGroup (OTwoQuot Lc) :=
    famPSL_simple (Or.inr ⟨7, Nat.prime_seven, by norm_num, ⟨e7⟩⟩)
  have hinj : Function.Injective π0 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal π0.ker with h | h
    · exact h
    · exfalso
      apply hAb0
      rw [← hπ0range, eq_bot_iff]
      rintro _ ⟨q, rfl⟩
      have : q ∈ π0.ker := by rw [h]; exact Subgroup.mem_top q
      rw [MonoidHom.mem_ker] at this
      rw [this]
      exact Subgroup.one_mem _
  let eAb : OTwoQuot Lc ≃* ↥Ab :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hπ0range)
  have hAb7 : IsL2Prime 7 ↥Ab := ⟨eAb.symm.trans e7⟩
  have hsimpAb : IsSimpleGroup ↥Ab := eAb.symm.isSimpleGroup
  let eAbAb' : ↥Ab ≃* ↥Ab' :=
    (Subgroup.equivMapOfInjective Ab (MulAut.conj τ).toMonoidHom
      (MulAut.conj τ).injective).trans (MulEquiv.subgroupCongr (map_conj_eq_of_Mv hmvt))
  have hsimpAb' : IsSimpleGroup ↥Ab' := eAbAb'.symm.isSimpleGroup
  have hperfAb : ⁅Ab, Ab⁆ = Ab := by
    rw [hAb, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLcX, hperf]
  have hperfAb' : ⁅Ab', Ab'⁆ = Ab' := by
    rw [← map_conj_eq_of_Mv hmvt, ← Subgroup.map_commutator, hperfAb]
  have hcommAb : ∀ x ∈ Ab, ∀ y ∈ Ab', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hq : ((⁅a, b⁆ : ↥X) : Γ) ∈ Q := by
      have := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb))
      simpa [commutatorElement_def] using this
    have h1 : ψ ⁅a, b⁆ = 1 := hQψ _ hq
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let Stab2 : Subgroup (MulAut ↥(Ch3z.chiefMod A N)) :=
    { carrier := {g | (Mv g Ab Ab ∧ Mv g Ab' Ab') ∨ (Mv g Ab Ab' ∧ Mv g Ab' Ab)}
      one_mem' := Or.inl ⟨fun x => by simp, fun x => by simp⟩
      mul_mem' := by
        rintro g h (⟨hg1, hg2⟩ | ⟨hg1, hg2⟩) (⟨hh1, hh2⟩ | ⟨hh1, hh2⟩)
        · exact Or.inl ⟨hh1.mul hg1, hh2.mul hg2⟩
        · exact Or.inr ⟨hh1.mul hg2, hh2.mul hg1⟩
        · exact Or.inr ⟨hh1.mul hg1, hh2.mul hg2⟩
        · exact Or.inl ⟨hh1.mul hg2, hh2.mul hg1⟩
      inv_mem' := by
        rintro g (⟨hg1, hg2⟩ | ⟨hg1, hg2⟩)
        · exact Or.inl ⟨hg1.inv, hg2.inv⟩
        · exact Or.inr ⟨hg2.inv, hg1.inv⟩ }
  have hAbS : Ab ≤ Stab2 := by
    intro g hg
    exact Or.inl ⟨Mv.refl_of_mem hg, Mv.of_commute fun x hx => hcommAb g hg x hx⟩
  have hAb'S : Ab' ≤ Stab2 := by
    intro g hg
    exact Or.inl ⟨Mv.of_commute fun x hx => (hcommAb x hx g hg).symm, Mv.refl_of_mem hg⟩
  have hTbS : Tb ≤ Stab2 := by
    rintro _ ⟨s, hs, rfl⟩
    have hsT : (s : Γ) ∈ T := Subgroup.mem_subgroupOf.mp hs
    have hinv : ψ s⁻¹ ∈ Stab2 := by
      rcases hTperm (s : Γ) hsT with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Mv_map ψ s⁻¹ h1, Mv_map ψ s⁻¹ h2⟩
      · exact Or.inr ⟨Mv_map ψ s⁻¹ h1, Mv_map ψ s⁻¹ h2⟩
    have := Stab2.inv_mem hinv
    rwa [map_inv, inv_inv] at this
  have hX'S : X' ≤ Stab2 := by
    intro x hx
    obtain ⟨κ, hκ, s, hs, rfl⟩ := hXKT' x hx
    exact Stab2.mul_mem ((sup_le hAbS hAb'S) hκ) (hTbS hs)
  let P : PairData ↥(Ch3z.chiefMod A N) :=
    { A := Ab, A' := Ab', Xb := X', hW := hW, comm := hcommAb, simpA := hsimpAb,
      simpA' := hsimpAb', perfA := hperfAb, perfA' := hperfAb',
      irr := fun U hU => Ch3z.chiefMod_irr hchief hQX U hU,
      norm := fun g hg => hX'S hg }
  have hT2 : IsPGroup 2 Tb := (hsyl.2.1.comap_subtype (K := X)).map ψ
  have hconj2 : ∀ S : Subgroup (MulAut ↥(Ch3z.chiefMod A N)), S ≤ X' → IsPGroup 2 S →
      ∃ g ∈ X', ∀ s ∈ S, g * s * g⁻¹ ∈ Tb := by
    intro S hSX hS2
    let φ : ↥X →* ↥X' := Ch3z.chiefHom hXL hXN
    have hφ : Function.Surjective φ := Ch3z.chiefHom_surjective hXL hXN
    have hφψ : ∀ g : ↥X, ((φ g : ↥X') : MulAut ↥(Ch3z.chiefMod A N)) = ψ g := fun g => rfl
    set Pm : Subgroup ↥X' := (T.subgroupOf X).map φ with hPm
    have hPm2 : IsPGroup 2 Pm := (hsyl.2.1.comap_subtype (K := X)).map φ
    have hPmidx : ¬ 2 ∣ Pm.index := by
      intro h2
      exact hsyl.2.2 (h2.trans (Subgroup.index_map_dvd (T.subgroupOf X) hφ))
    have hS' : IsPGroup 2 (S.subgroupOf X') := hS2.comap_subtype
    obtain ⟨g', hg'⟩ := exists_conj_le_of_two_sylow hPm2 hPmidx hS'
    refine ⟨(g' : MulAut ↥(Ch3z.chiefMod A N)), g'.2, fun s hs => ?_⟩
    have h1 := hg' ⟨s, hSX hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
    obtain ⟨u, hu, hu'⟩ := h1
    refine ⟨u, hu, ?_⟩
    have := congrArg Subtype.val hu'
    simpa [hφψ] using this
  have hτTb : τ ∈ Tb := ⟨tX, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hVT : Vb ≤ Tb := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Subgroup.mem_subgroupOf.mpr (hET (Subgroup.mem_subgroupOf.mp he)), rfl⟩
  have hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
    refine ⟨s * e * s⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa using hEn (s : Γ) (Subgroup.mem_subgroupOf.mp hs) (e : Γ) (Subgroup.mem_subgroupOf.mp he)
  have hVne : Vb ≠ ⊥ := by
    intro h
    obtain ⟨e₁, he₁E, he₁⟩ := hnotAll
    apply he₁
    have : ψ e₁ ∈ Vb := ⟨e₁, Subgroup.mem_subgroupOf.mpr he₁E, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hbd : ∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ 4 := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := index_fixV_chiefPsi_mul_le hXL hXN hNL hLN hEX hE' (e := e)
      (Subgroup.mem_subgroupOf.mp he)
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h2 : (@fixV ↥(Ch3z.chiefMod A N) (Ch3z.chiefCG hE')
        (Subgroup.zpowers (Ch3z.chiefPsi hXL hXN e))).index * Nat.card A ≤ 4 * Nat.card A :=
      h1.trans hbound
    have h3 := Nat.le_of_mul_le_mul_right h2 hApos
    rw [← index_fixV_zpowers_eq_card_cmt]
    exact h3
  have hpn : (CFSG.Open.pCore 2 ↥X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥X) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hlePC : CFSG.Open.pCore 2 ↥X ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine map_eq_one_of_normal_two152 ψ hψX' hsurj hO2
      (P := (CFSG.Open.pCore 2 ↥X).map X.subtype) ?_ (hp2.map X.subtype) (g := x)
      ⟨x, hx, rfl⟩
    rintro g hg _ ⟨p, hp, rfl⟩
    refine ⟨⟨g, hg⟩ * p * ⟨g, hg⟩⁻¹, hpn.conj_mem p hp ⟨g, hg⟩, ?_⟩
    simp
  let πX : ↥X →* OTwoQuot X := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)
  have hπX : Function.Surjective πX := QuotientGroup.mk'_surjective _
  let φ : OTwoQuot X →* MulAut ↥(Ch3z.chiefMod A N) := QuotientGroup.lift _ ψ hlePC
  have hφπ : ∀ g : ↥X, φ (πX g) = ψ g := fun g => rfl
  have hQπ : ∀ g : ↥X, (g : Γ) ∈ Q → πX g = 1 := by
    intro g hg
    have hQn' : (Q.subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hQX]
      exact fun q g hq hg => hQn g hg q hq
    have hQ2' : IsPGroup 2 (Q.subgroupOf X) := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
    have : g ∈ Q.subgroupOf X := Subgroup.mem_subgroupOf.mpr hg
    exact (QuotientGroup.eq_one_iff g).2 (CFSG.LieType.BorelTits.le_pCore 2 hQn' hQ2' this)
  have hF1 : ∀ l : ↥X, (l : Γ) ∈ Lc → ψ l = 1 → (l : Γ) ∈ Q := by
    intro l hl hψl
    have h1 : QuotientGroup.mk (⟨(l : Γ), hl⟩ : ↥Lc) = (1 : OTwoQuot Lc) := by
      apply hinj
      rw [map_one]
      show ψL ⟨(l : Γ), hl⟩ = 1
      exact hψl
    rw [QuotientGroup.eq_one_iff] at h1
    exact hO2L _ h1
  have hF1' : ∀ l : ↥X, (l : Γ) ∈ Lt → ψ l = 1 → (l : Γ) ∈ Q := by
    intro l hl hψl
    have hl₀ : t⁻¹ * (l : Γ) * t ∈ Lc := by
      have := (hLt (l : Γ)).1 hl
      simpa using this
    have hl₀' : ((tX⁻¹ * l * tX : ↥X) : Γ) = t⁻¹ * (l : Γ) * t := by simp [htX]
    have hψl₀ : ψ (tX⁻¹ * l * tX) = 1 := by
      have : ψ (tX⁻¹ * l * tX) = (ψ tX)⁻¹ * ψ l * ψ tX := by simp [map_mul, map_inv]
      rw [this, hψl]
      group
    have hl₀Q : ((tX⁻¹ * l * tX : ↥X) : Γ) ∈ Q := hF1 _ (by rw [hl₀']; exact hl₀) hψl₀
    have : (l : Γ) = t * ((tX⁻¹ * l * tX : ↥X) : Γ) * t⁻¹ := by rw [hl₀']; group
    rw [this]
    exact hQn t (hTX ht) _ hl₀Q
  have hcommG : ∀ a ∈ (Lc.subgroupOf X).map πX, ∀ b ∈ (Lt.subgroupOf X).map πX, a * b = b * a := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    have hq : ((⁅l, l'⁆ : ↥X) : Γ) ∈ Q := by
      have := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hl)
        (Subgroup.mem_subgroupOf.mp hl'))
      simpa [commutatorElement_def] using this
    have h1 : πX ⁅l, l'⁆ = 1 := hQπ _ hq
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hKker : ∀ y : ↥X, (y : Γ) ∈ K → ψ y = 1 → πX y = 1 := by
    intro y hy hψy
    have hmem : πX y ∈ (Lc.subgroupOf X).map πX ⊔ (Lt.subgroupOf X).map πX := by
      rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLcX hLtX, ← hK]
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := He6.mem_sup_of_commute hcommG hmem
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨l', hl', rfl⟩ := hb
    have h1 : ψ l * ψ l' = 1 := by
      have := congrArg φ hab
      rw [hφπ, map_mul, hφπ, hφπ, hψy] at this
      exact this.symm
    have hlA : ψ l ∈ Ab := ⟨l, hl, rfl⟩
    have hlA' : ψ l' ∈ Ab' := ⟨l', hl', rfl⟩
    have h2 : ψ l = (ψ l')⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : ψ l ∈ Ab ⊓ Ab' := ⟨hlA, by rw [h2]; exact Ab'.inv_mem hlA'⟩
    rw [P.inf_eq_bot, Subgroup.mem_bot] at h3
    have h4 : ψ l' = 1 := by
      rw [h3] at h2
      exact inv_eq_one.1 h2.symm
    have h5 := hQπ l (hF1 l (Subgroup.mem_subgroupOf.mp hl) h3)
    have h6 := hQπ l' (hF1' l' (Subgroup.mem_subgroupOf.mp hl') h4)
    rw [hab, h5, h6, one_mul]
  have hkerP : IsPGroup 2 ψ.ker := by
    rintro ⟨x, hx⟩
    have hxψ : ψ x = 1 := hx
    have hgsup : (x : Γ) ∈ K ⊔ T := by
      rw [← hXKT]
      exact x.2
    obtain ⟨κ, hκ, s, hs, hgks⟩ := mem_sup_eq_mul
      (fun s hs κ hκ => hXn s (hTX hs) κ hκ) hgsup
    obtain ⟨m, hm⟩ := PairData.exists_two_pow_mem
      (fun s hs κ hκ => hXn s (hTX hs) κ hκ) hsyl.2.1 hκ hs hgks
    have hyK : (((x ^ 2 ^ m : ↥X)) : Γ) ∈ K := by simpa using hm
    have hyψ : ψ (x ^ 2 ^ m) = 1 := by rw [map_pow, hxψ, one_pow]
    have hπy : πX (x ^ 2 ^ m) = 1 := hKker _ hyK hyψ
    have hypc : x ^ 2 ^ m ∈ CFSG.Open.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).1 hπy
    obtain ⟨j, hj⟩ := hp2 ⟨_, hypc⟩
    refine ⟨m + j, Subtype.ext ?_⟩
    have hj' : (x ^ 2 ^ m) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show x ^ 2 ^ (m + j) = 1
    rw [pow_add, pow_mul]
    exact hj'
  have hkerle : ψ.ker ≤ CFSG.Open.pCore 2 ↥X :=
    CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ψ) hkerP
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := hπX q
    have : x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hφπ]
      exact hq
    exact (QuotientGroup.eq_one_iff x).2 (hkerle this)
  have hφX' : ∀ q, φ q ∈ X' := by
    intro q
    obtain ⟨x, rfl⟩ := hπX q
    rw [hφπ]
    exact hψX' x
  let eX : OTwoQuot X ≃* ↥X' := MulEquiv.ofBijective (φ.codRestrict X' hφX')
    ⟨fun a b h => hφinj (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
      obtain ⟨g, hg⟩ := hsurj y hy
      exact ⟨πX g, Subtype.ext (by
        show φ (πX g) = y
        rw [hφπ, hg])⟩⟩
  have hSQ' : SQTKGroup ↥X' := sqtkGroup_of_mulEquiv' eX.symm hSQX
  have hno := hpure ↥(Ch3z.chiefMod A N) P Tb Vb τ hAb7 hSQ' hAbX hAb'X hTbX hT2 hconj2 hXKT' hO2
    hτTb hmvt hmvt' hVT hVn hVne hbd
  obtain ⟨eW⟩ := wreath_of_noOuter P hAbX hAb'X hTbX hT2 hXKT' hO2 hτTb hmvt hmvt' hAb7 hno
  exact ⟨eX.trans eW⟩

end Reduce

section Top

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.Quasithin.insp15227ShapeSeven_of_pure (h : PureShapeSeven) :
    Insp15227ShapeSeven := by
  intro G _ _ T Mc M H hs hH hVQ L t hL ht htN hKc hcomm hquot A N hstep hZA hnot hle4
  refine Or.inr ?_
  set K : Subgroup G := conjClosure (oTwoUpper H) Mc with hKdef
  set Lt : Subgroup G := conjSub t L with hLtdef
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hTM : T ≤ M := hs.mf.1.1.2
  have hsyl : ∀ P : Subgroup G, T ≤ P → IsSylowTwoOf T P := fun P hTP =>
    isSylowTwoOf_of_le151 hs.qtfe.sylow hTP
  have hQT : pCoreOf 2 Mc ≤ T := pCoreOf_le_of_isSylowTwoOf (hsyl Mc hTMc)
  have hQ2 : IsPGroup 2 (pCoreOf 2 Mc) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc
  have hLMc : L ≤ Mc := le_of_mem_cComp hL
  have hLtMc : Lt ≤ Mc := by
    intro x hx
    have h1 : t⁻¹ * x * t ∈ L := mem_conjSub.mp hx
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ ∈ Mc :=
      Mc.mul_mem (Mc.mul_mem (hTMc ht) (hLMc h1)) (Mc.inv_mem (hTMc ht))
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h2
  have hKMc : K ≤ Mc := by rw [hKc]; exact sup_le hLMc hLtMc
  have hXMc : K ⊔ T ≤ Mc := sup_le hKMc hTMc
  have hMcn : Mc ≤ Subgroup.normalizer (K : Set G) := le_normalizer_conjClosure (oTwoUpper H) Mc
  have hXn : ∀ g ∈ K ⊔ T, ∀ κ ∈ K, g * κ * g⁻¹ ∈ K := fun g hg κ hκ =>
    (Subgroup.mem_normalizer_iff.mp (hMcn (hXMc hg)) κ).mp hκ
  have hQn : ∀ g ∈ K ⊔ T, ∀ q ∈ pCoreOf 2 Mc, g * q * g⁻¹ ∈ pCoreOf 2 Mc := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc (hXMc hg)) q).mp hq
  have hQX : pCoreOf 2 Mc ≤ K ⊔ T := hQT.trans le_sup_right
  have hLt_mem : Lt ∈ cComp Mc := map_conj_mem_cComp hL (hTMc ht)
  have hLne : L ≠ Lt := by
    intro h'
    apply htN
    exact A38.map_conj_eq_iff.mp h'.symm
  have hconjK : ∀ g ∈ Mc, conjSub g K = K := fun g hg => A38.map_conj_eq_iff.mpr (hMcn hg)
  have hperm : ∀ g ∈ Mc, (conjSub g L = L ∧ conjSub g Lt = Lt) ∨
      (conjSub g L = Lt ∧ conjSub g Lt = L) := by
    intro g hg
    have ha : conjSub g L ∈ cComp Mc := map_conj_mem_cComp hL hg
    have hb : conjSub g Lt ∈ cComp Mc := map_conj_mem_cComp hLt_mem hg
    have h1 : conjSub g (L ⊔ Lt) = L ⊔ Lt := by rw [← hKc]; exact hconjK g hg
    have ha' : conjSub g L ≤ L ⊔ Lt :=
      calc conjSub g L ≤ conjSub g (L ⊔ Lt) := conjSub_mono g le_sup_left
        _ = L ⊔ Lt := h1
    have hb' : conjSub g Lt ≤ L ⊔ Lt :=
      calc conjSub g Lt ≤ conjSub g (L ⊔ Lt) := conjSub_mono g le_sup_right
        _ = L ⊔ Lt := h1
    rcases cComp_eq_of_le_sup ha hL hLt_mem ha' with h2 | h2 <;>
      rcases cComp_eq_of_le_sup hb hL hLt_mem hb' with h3 | h3
    · exact absurd (conjSub_inj' (h3.trans h2.symm)).symm hLne
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr ⟨h2, h3⟩
    · exact absurd (conjSub_inj' (h2.trans h3.symm)) hLne
  have hTperm : ∀ s ∈ T, (Mv s⁻¹ L L ∧ Mv s⁻¹ Lt Lt) ∨ (Mv s⁻¹ L Lt ∧ Mv s⁻¹ Lt L) := by
    intro s hsT
    rcases hperm s (hTMc hsT) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Mv_of_conjSub h1, Mv_of_conjSub h2⟩
    · exact Or.inr ⟨Mv_of_conjSub h2, Mv_of_conjSub h1⟩
  have hLt' : Mv t⁻¹ Lt L := Mv_of_conjSub rfl
  have hLc' : Mv t⁻¹ L Lt := by
    rcases hperm t (hTMc ht) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1.symm hLne
    · exact Mv_of_conjSub h2
  have hO2L : ∀ x : ↥L, x ∈ CFSG.Open.pCore 2 ↥L → (x : G) ∈ pCoreOf 2 Mc := by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL) h1
  have hVT : V154 T Mc M ≤ T := S152N.V154_le_T hs
  have hVM : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hEn : ∀ s ∈ T, ∀ e ∈ V154 T Mc M, s * e * s⁻¹ ∈ V154 T Mc M := fun s hsT e he =>
    (Subgroup.mem_normalizer_iff.mp (hVM (hTM hsT)) e).mp he
  have hPMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have hSQMc : SQTKGroup ↥Mc :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hPMc
  have hSQX : SQTKGroup ↥(K ⊔ T) := sqtkGroup_of_le hSQMc hXMc
  have hSQ : SQTKGroup (OTwoQuot (K ⊔ T)) := by
    refine InternalSec.sqtkGroup_of_surjective (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(K ⊔ T)))
      (QuotientGroup.mk'_surjective _) ?_ hSQX
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  exact iii_shape_reduce h rfl hXn (hsyl _ le_sup_right) hKc (perfect_of_mem_cComp hL) hLt' hLc' ht
    hTperm hcomm hO2L hquot hQ2 hQn hQX hVT hEn hstep hnot hle4 hSQ

end Top

end CFSG.Quasithin.He7

theorem CFSG.Quasithin.insp15227ShapeSeven_of_b42
    (hB42 : AsB42) :
    Insp15227ShapeSeven :=
  insp15227ShapeSeven_of_pure (pureShapeSeven_of_b42 hB42)
