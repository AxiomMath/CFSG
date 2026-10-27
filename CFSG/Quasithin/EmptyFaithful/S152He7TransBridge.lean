module

public import CFSG.Quasithin.EmptyFaithful.S152He7Defs
public import CFSG.Quasithin.EmptyFaithful.T1531InspMod
public import CFSG.Quasithin.EmptyFaithful.S152He6Iii

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X1 He6
open scoped commutatorElement

section Reduce

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem ii_reduce (hfinal : PureTransIi) {T X Q E A N : Subgroup Γ} {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hsyl : IsSylowTwoOf T X) (hQ2 : IsPGroup 2 Q) (hQX : Q ≤ X)
    (hET : E ≤ T) (hEn : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hchief : IsChiefStep X Q A N) (hnot : ¬ ⁅N, E⁆ ≤ A)
    (hbound : Nat.card ↥(⁅N, E⁆ ⊔ A) ≤ 2 * Nat.card A)
    (hiso : IsAutLnTwo n (OTwoQuot X)) (hSQ : SQTKGroup (OTwoQuot X)) : False := by
  classical
  have hTX : T ≤ X := hsyl.1
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
  have hnt : Nontrivial ↥(Ch3z.chiefMod A N) := by
    obtain ⟨x, hxN, hxA⟩ := Set.exists_of_ssubset (SetLike.coe_ssubset_coe.mpr hchief.2.2.1)
    refine nontrivial_of_ne (Ch3z.chiefIota hNL ⟨x, hxN⟩) 1 ?_
    intro h
    exact hxA ((Ch3z.chiefIota_eq_one_iff hNL ⟨x, hxN⟩).1 h)
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
  have hnotAll : ∃ e₁ : ↥X, (e₁ : Γ) ∈ E ∧ ψ e₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnot
    exact Subgroup.commutator_le.mpr fun n hn e he =>
      commutator_mem_of_chiefPsi_eq_one hXL hXN hNL (hall ⟨e, hEX he⟩ he) hn
  have hpn : (CFSG.Open.pCore 2 ↥X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥X) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hle : CFSG.Open.pCore 2 ↥X ≤ ψ.ker := by
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
  let φ : OTwoQuot X →* MulAut ↥(Ch3z.chiefMod A N) := QuotientGroup.lift _ ψ hle
  have hφπ : ∀ g : ↥X, φ (πX g) = ψ g := fun g => rfl
  have hirr : ∀ U : Subgroup ↥(Ch3z.chiefMod A N), (∀ y : OTwoQuot X, ∀ u ∈ U, φ y u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine Ch3z.chiefMod_irr hchief hQX U (fun x hx u hu => ?_)
    obtain ⟨g, rfl⟩ := hsurj x hx
    exact hU (πX g) u hu
  set T₀ : Subgroup (OTwoQuot X) := (T.subgroupOf X).map πX with hT₀
  set V₀ : Subgroup (OTwoQuot X) := (E.subgroupOf X).map πX with hV₀
  have hT₀syl : IsSylowTwoOf T₀ ⊤ := by
    refine ⟨le_top, (hsyl.2.1.comap_subtype (K := X)).map πX, ?_⟩
    intro h2
    apply hsyl.2.2
    have h3 : (T₀.subgroupOf ⊤).index = T₀.index := Subgroup.relIndex_top_right T₀
    rw [h3] at h2
    exact h2.trans (Subgroup.index_map_dvd (T.subgroupOf X) hπX)
  have hVT : V₀ ≤ T₀ := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Subgroup.mem_subgroupOf.mpr (hET (Subgroup.mem_subgroupOf.mp he)), rfl⟩
  have hVn : ∀ s ∈ T₀, ∀ v ∈ V₀, s * v * s⁻¹ ∈ V₀ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
    refine ⟨s * e * s⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa using hEn (s : Γ) (Subgroup.mem_subgroupOf.mp hs) (e : Γ) (Subgroup.mem_subgroupOf.mp he)
  have hbd : ∀ v ∈ V₀, (fixV (Subgroup.zpowers (φ v))).index ≤ 2 := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := index_fixV_chiefPsi_mul_le hXL hXN hNL hLN hEX hE' (e := e)
      (Subgroup.mem_subgroupOf.mp he)
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h2 : (@fixV ↥(Ch3z.chiefMod A N) (Ch3z.chiefCG hE')
        (Subgroup.zpowers (Ch3z.chiefPsi hXL hXN e))).index * Nat.card A ≤ 2 * Nat.card A :=
      h1.trans hbound
    exact Nat.le_of_mul_le_mul_right h2 hApos
  have hall := hfinal (OTwoQuot X) n hn hiso hSQ _ hW hnt φ hirr T₀ V₀ hT₀syl hVT hVn hbd
  obtain ⟨e₁, he₁E, he₁⟩ := hnotAll
  apply he₁
  rw [← hφπ]
  exact hall _ ⟨e₁, Subgroup.mem_subgroupOf.mpr he₁E, rfl⟩

end Reduce

section Final

open CFSG.Quasithin.InternalSec

theorem insp15227TransIi_of_pure (h : PureTransIi) : Insp15227TransIi := by
  intro G _ _ T Mc M H hs hH hVQ hcase A N hstep heq
  obtain ⟨-, hK, n, hn, hiso⟩ := hcase
  set K : Subgroup G := conjClosure (oTwoUpper H) Mc with hKdef
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hTM : T ≤ M := hs.mf.1.1.2
  have hsyl : ∀ P : Subgroup G, T ≤ P → IsSylowTwoOf T P := fun P hTP =>
    isSylowTwoOf_of_le151 hs.qtfe.sylow hTP
  have hQT : pCoreOf 2 Mc ≤ T := pCoreOf_le_of_isSylowTwoOf (hsyl Mc hTMc)
  have hQ2 : IsPGroup 2 (pCoreOf 2 Mc) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc
  have hKMc : K ≤ Mc := le_of_mem_cComp hK
  have hXMc : K ⊔ T ≤ Mc := sup_le hKMc hTMc
  have hQX : pCoreOf 2 Mc ≤ K ⊔ T := hQT.trans le_sup_right
  have hVT : V154 T Mc M ≤ T := S152N.V154_le_T hs
  have hVM : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hEn : ∀ s ∈ T, ∀ e ∈ V154 T Mc M, s * e * s⁻¹ ∈ V154 T Mc M := fun s hsT e he =>
    (Subgroup.mem_normalizer_iff.mp (hVM (hTM hsT)) e).mp he
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hPMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have hSQMc : SQTKGroup ↥Mc :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hPMc
  have hSQX : SQTKGroup ↥(K ⊔ T) := sqtkGroup_of_le hSQMc hXMc
  have hSQ : SQTKGroup (OTwoQuot (K ⊔ T)) := by
    refine sqtkGroup_of_surjective (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(K ⊔ T)))
      (QuotientGroup.mk'_surjective _) ?_ hSQX
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  refine ii_reduce h hn (hsyl _ le_sup_right) hQ2 hQX hVT hEn hstep ?_ heq.le hiso hSQ
  intro hle
  have : ⁅N, V154 T Mc M⁆ ⊔ A = A := sup_eq_right.mpr hle
  rw [this] at heq
  omega

end Final

end CFSG.Quasithin
