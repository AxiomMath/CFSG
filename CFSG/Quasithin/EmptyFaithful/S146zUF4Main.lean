module

public import CFSG.Quasithin.EmptyFaithful.S146zUF4Pkg
public import CFSG.Quasithin.Background.F918C8
public import CFSG.Quasithin.EmptyFaithful.S1565G

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565
open scoped Pointwise commutatorElement

namespace S146zU

namespace UF4

section Alt

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem false_of_ffAlt (hA21 : AsA21SQTKSection) (h56 : AsB56) (S : Setting146 G T M)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hK₂ : conjSub s K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G)) (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (hK₀eq : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {J : Subgroup G} (hZJ : quasithinOmegaOneCenter T ≤ J)
    (hJU : J ≤ conjClosure (VZ T M) (mcOf T))
    (hntE : ¬ ⁅J, conjClosure K₁ T⁆ ≤ quasithinOmegaOneCenter T)
    (hntF : ¬ ⁅conjClosure (VZ T M) (mcOf T), conjClosure K₁ T⁆ ≤ J)
    (hJN : mcOf T ≤ Subgroup.normalizer (J : Set G))
    (hb : FFAlt15365 hF J hJU) : False := by
  have hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hF.H_le_normalizer_V₁
  have hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
    le_normalizer_conjClosure (VZ T M) (mcOf T)
  have hJU' : J ≤ uOfL22 T M := hJU
  have hJZ : J ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hJU'.trans (UF3.uOfL22_le_normalizer_Z S)
  have hUJ : uOfL22 T M ≤ Subgroup.normalizer (J : Set G) :=
    UF3.uOfL22_le_normalizer_of_le S hJU'
  have hK₀H : conjClosure K₁ T ≤ mcOf T := hF.K₀_le_H
  have hFE : Fact (IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) J)) :=
    ⟨UF3.isElemAbelian_tildeOf_of_le S _ hJU'⟩
  have hFF : Fact (IsElemAbelian 2 (tildeOf J (uOfL22 T M))) :=
    ⟨UF3.isElemAbelian_tildeOf_of_le S J le_rfl⟩
  have hntE' : ¬ (conjClosure K₁ T).subgroupOf (mcOf T) ≤ (actH hZN hJN).ker :=
    not_le_ker_actH hZN hJN hJZ hK₀H hntE
  have hntF' : ¬ (conjClosure K₁ T).subgroupOf (mcOf T) ≤ (actH hJN hUN).ker :=
    not_le_ker_actH hJN hUN hUJ hK₀H hntF
  rcases hb with ⟨hbE, hbF⟩ | hc | hc
  · have hFFE := isFFModule_of_isFFInt (W₀ := quasithinOmegaOneCenter T) (J₀ := J) hK₀ hZN hJN
      _ hbE
    have hFFF := isFFModule_of_isFFInt (W₀ := J) (J₀ := uOfL22 T M) hK₀ hJN hUN _ hbF
    exact false_of_ff_sections hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF hZJ hJU' hZN hJN hUN
      hntE' hntF' hFFE hFFF
  · have hstrong := isStrongFFModule_of_isStrongFFInt (W₀ := quasithinOmegaOneCenter T) (J₀ := J)
      hK₀ hZN hJN _ hc
    exact false_of_strong_section hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF le_rfl hZJ hJU' hZN
      hJN hntE' hstrong
  · have hstrong := isStrongFFModule_of_isStrongFFInt (W₀ := J) (J₀ := uOfL22 T M) hK₀ hJN hUN _ hc
    exact false_of_strong_section hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF hZJ hJU' le_rfl hJN hUN
      hntF' hstrong

end Alt

end UF4

section Claim

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem claim_of_setting (hA21 : AsA21SQTKSection) (h56 : AsB56) (S : Setting146 G T M)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hK₂ : conjSub s K₁ ∈ cComp (mcOf T))
    (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK₀ : conjClosure K₁ T ⊔ T = mcOf T) (hK₀eq : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {I : Subgroup G} (hV₁I : quasithinOmegaOneCenter T ≤ I)
    (hIU : I ≤ conjClosure (VZ T M) (mcOf T))
    (W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))))
    (hW : ∀ t ∈ autIH (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) T, ∀ w ∈ W, t w ∈ W)
    (hirr : IsIrrPlusTildeU hF I W) :
    tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) =
      tildeOf (quasithinOmegaOneCenter T) ⁅conjClosure (VZ T M) (mcOf T), conjClosure K₁ T⁆ := by
  by_cases ha : tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) =
      tildeOf (quasithinOmegaOneCenter T) ⁅conjClosure (VZ T M) (mcOf T), conjClosure K₁ T⁆
  · exact ha
  exfalso
  have hIT := isIrrPlusTildeT_of_ambient hF hIU W hW hirr
  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hIT
  have hIHU : conjClosure I (mcOf T) ≤ conjClosure (VZ T M) (mcOf T) :=
    conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K₁ T ⊔ T ≤ Subgroup.normalizer (conjClosure I (mcOf T) : Set G) :=
    hF.K₀T_le_H.trans (le_normalizer_conjClosure I (mcOf T))
  have hWK := hF.tilde_commutator_conjClosure hIU hI
  have hW0 := tildeOf_conjClosure_ne_bot hF hIU hI
  have hZJ : quasithinOmegaOneCenter T ≤ conjClosure I (mcOf T) :=
    hV₁I.trans (le_conjClosure I (mcOf T))
  have hntE : ¬ ⁅conjClosure I (mcOf T), conjClosure K₁ T⁆ ≤ quasithinOmegaOneCenter T := by
    intro hle
    exact hW0 (hWK ▸ tildeOf_eq_bot_of_le hle)
  have hntF : ¬ ⁅conjClosure (VZ T M) (mcOf T), conjClosure K₁ T⁆ ≤ conjClosure I (mcOf T) := by
    intro hle
    exact ha (le_antisymm (hWK.symm.le.trans (secImg_mono (Subgroup.commutator_mono hIHU le_rfl)))
      (secImg_mono hle))
  rcases hF.F918_6 hZJ hIHU hIHN hW0 hWK with h | hb
  · exact ha h
  · exact UF4.false_of_ffAlt hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF hZJ hIHU hntE hntF
      (le_normalizer_conjClosure I (mcOf T)) hb

end Claim

end S146zU

end CFSG.Quasithin
