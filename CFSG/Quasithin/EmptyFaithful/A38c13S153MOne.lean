module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1565B
public import CFSG.Quasithin.Background.F918C8
public import CFSG.Quasithin.EmptyFaithful.S153MC1
public import CFSG.Quasithin.EmptyFaithful.S153MC1b
public import CFSG.Quasithin.EmptyFaithful.S153MCross
public import CFSG.Quasithin.EmptyFaithful.S153MOne

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

namespace S153M

section One

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem noStrong_one_of_hypC
    (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (hF : HypF918 T V L V₁ Vp H K) (M' : Subgroup G) (hHK : H = K ⊔ T) (hS : SQTKGroup ↥H)
    (hK0 : conjClosure K T = K) (hE : E2.E22CasesW H T M' K) (hn : 1 < E1.nParam H)
    (hodd : ∀ n : ℕ, 2 ≤ n → Shape15365 n (E2.star M' H K) →
      E2.IsBorelIn (E2.star M' H K) (E2.star M' H (M' ⊓ K)) → 3 ≤ n ∧ Odd n)
    {I : Subgroup G} (hIU : I ≤ conjClosure Vp H)
    (hWK : tildeOf V₁ ⁅conjClosure I H, conjClosure K T⁆ = tildeOf V₁ (conjClosure I H))
    (hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥)
    (hs : F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I H))
      (hF.isElemAbelian_tilde_of_le (conjClosure_le_conjClosure_U hIU le_rfl))) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hsub : IsSubnormal K H := subnormal_of_mem_cComp hF.K_cComp
  have hWU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hFE : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))) :=
    ⟨hF.isElemAbelian_tilde_of_le hWU⟩
  have hWN : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hUN : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hUW : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ hIU
  obtain ⟨hkerchar, hB⟩ := e22CasesW_two_data hE hn hK0
  obtain ⟨n, hn2, hKs, hSplit⟩ := e22CasesW_two_shape_split hE hn hK0
  obtain ⟨hn3, hnodd⟩ := hodd n hn2 hKs hB
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hK0 ▸ le_normalizer_conjClosure K T
  set φ := actH hWN hUN with hφ
  have hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    hF.actH_eq_one_of_mem_pCoreOf hIU hx
  have hnt : ¬ K.subgroupOf H ≤ φ.ker := by
    intro h
    have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have hk' : k ∈ K := hK0 ▸ hk
      have h1 := h (Subgroup.mem_subgroupOf.mpr hk' : (⟨k, hKH hk'⟩ : ↥H) ∈ K.subgroupOf H)
      have h2 := (actE_eq_one_iff hWN hUN hUW ⟨k, hKH hk'⟩).mp h1 u hu
      have h3 := V₁.inv_mem h2
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at h3
    apply hW0
    rw [← hWK, eq_bot_iff]
    intro y hy
    obtain ⟨a, haJ, rfl⟩ := mem_secImg.mp hy
    exact Subgroup.mem_bot.mpr (secMk_eq_one_iff.mpr (hle haJ))
  have hXH : conjClosure K T ⊔ T ≤ H := hF.K₀T_le_H
  have h3 : (conjClosure K T ⊔ T).subgroupOf H = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top, hK0, ← hHK]
  have hSt : IsStrongFFModule φ.range := by
    have h1 : IsStrongFFModule (autOn (tildeOf V₁ (conjClosure K T ⊔ T))
        (tildeOf V₁ (conjClosure I H))) := hs
    rw [autOn_tilde_eq_map_actH hWN hUN hXH, h3, ← MonoidHom.range_eq_map] at h1
    exact h1
  have hFF : IsFFModule φ.range := by
    have h1 : IsFFModule (autOn (tildeOf V₁ (conjClosure K T ⊔ T))
        (tildeOf V₁ (conjClosure I H))) := F9.IsStrongFFInt.isFFInt hs
    rw [autOn_tilde_eq_map_actH hWN hUN hXH, h3, ← MonoidHom.range_eq_map] at h1
    exact h1
  obtain ⟨ρK, hρK, hρKφ, -, hqL, -, hsh, hJ, σ, hσ, hz, hσρ⟩ :=
    kAction_data hA21 h51 hF M' hHK hS hK0 hkerchar hn3 hnodd hKs hWN hUN hQ hnt hFF
  have hV : ∀ v : ↥(tildeOf V₁ (conjClosure I H)), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hFE.out.2 v v.2)
  rcases hsh with ⟨K₁, hfld, hfin, m, hK₁, hreal⟩ | hNat
  · exact false_of_strong_natural_sl2 hV hJ ⟨K₁, hfld, hfin, hK₁, hreal⟩ hSt
  · rcases hSplit with hBen | hDiag
    · exact not_natOutcome_of_bender hqL hn3 hnodd hBen σ hσ hz hNat
    · exact not_isDiagramNontrivial_of_natOutcome M' hKH hsub hF.sylow_H hTK φ ρK hρK hρKφ σ hσ
        hz hσρ hNat hDiag

theorem noStrongOne_holdsC
    (hA21 : AsA21SQTKSection) (h51 : AsB51) :
    Input15365NoStrongFFOneC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hs
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hI := isIrrPlusTilde_of_module D.hF hV₁I hIU hIT
  have hWK := D.hF.tilde_commutator_conjClosure hIU hI
  have hW0 := tildeOf_conjClosure_ne_bot D.hF hIU hI
  exact noStrong_one_of_hypC hA21 h51 D.hF (H ⊓ M) D.H_eq D.sqtk hK0 D.e22 D.n_gt D.n_odd hIU hWK
    hW0 hs

end One

section Top

attribute [local instance] commGroupOfFact

theorem eltOne_holdsC
    (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (hNS : Input15365NoStrongFFOneC) : Input15365FFnatEltOneC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hFF
  have hn := D.n_gt
  obtain ⟨hkerchar, hB⟩ := e22CasesW_two_data D.e22 hn hK0
  obtain ⟨n, hn2, hKs⟩ := e22CasesW_two_shape D.e22 hn hK0
  obtain ⟨hn3, hnodd⟩ := D.n_odd n hn2 hKs hB
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hI := isIrrPlusTilde_of_module D.hF hV₁I hIU hIT
  have hWK := D.hF.tilde_commutator_conjClosure hIU hI
  have hEFF : IsFFInt (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
      (tildeOf (conjClosure I H) (conjClosure (ZS153 T M V₁) H))
      (D.hF.isElemAbelian_quotient (conjClosure I H)) := by
    rcases hFF with ⟨-, hE⟩ | hs | hs
    · exact hE
    · exact (hNS G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hs).elim
    · exact F9.IsStrongFFInt.isFFInt hs
  exact eltOne_of_E_ff hA21 h51 D.hF M D.H_eq D.sqtk hK0 hkerchar hB hn3 hnodd hKs hV₁I hIU hWK hne
    hEFF

end Top

end S153M

end CFSG.Quasithin
