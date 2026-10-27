module

public import CFSG.Quasithin.H13.A6S1372L74i
public import CFSG.Quasithin.H13.A6S1372L74x
public import CFSG.Quasithin.Background.L3SplitNat
public import CFSG.Quasithin.H13.A6S1372L74w

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1374OneSimpleMod : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Γ K R : Subgroup (MulAut V)) (ω : MulAut V), SQTKGroup ↥K → K ≤ Γ →
      Γ ≤ Subgroup.normalizer (K : Set (MulAut V)) →
      (Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) →
      Γ ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥ → commV K = ⊤ →
      ω ^ 3 = 1 → (∀ v : V, ω v = v → v = 1) → (∀ g ∈ Γ, ω * g = g * ω) →
      IsSylowTwoOf R Γ → (∃ A : Subgroup (MulAut V), IsFFStarOffender R A) →
      ∃ A : Subgroup (MulAut V), (∀ B, IsFFStarOffender R B → B = A) ∧
        A = R ⊓ centSub (fixV A) ∧
        ∃ δ ∈ K, δ ^ 3 = 1 ∧ δ ≠ 1 ∧ δ ∈ Subgroup.normalizer (A : Set (MulAut V))

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Simple

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G}
  (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
  (hKL1 : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K)
include hNS h13315 h1356two hH hab hKH hHK hKL1

theorem false_of_simple (hMod : Lem1374OneSimpleMod)
    (h1227 : U3.Stmt13_2_2_7) (h1337 : Stmt13_3_7) (hhat : ¬ IsHatA6 L)
    (hB : ¬ H13.IsA6Block L) (hK2 : oTwoRes K = K)
    (hKC : ∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
      k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) (hL1K : ¬ S.L1 ≤ K)
    (hsimp : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiso : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    hsimp.imp id nonempty_equiv_SL32_of_lieModel
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
    · obtain ⟨e⟩ := he
      exact (MulEquiv.isSimpleGroup_congr e).mpr L3Small.isSimpleGroup_Γ
  have hnc : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨a, b, hab'⟩ : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
        ⟨⟨swap 0 1 * swap 1 2, by decide⟩, ⟨swap 0 1 * swap 2 3, by decide⟩, by decide⟩
      exact ⟨e.symm a, e.symm b, fun h => hab' (by simpa using congrArg e h)⟩
    · obtain ⟨e⟩ := he
      obtain ⟨a, b, hab'⟩ := L3Split.L3_not_comm
      exact ⟨e.symm a, e.symm b, fun h => hab' (by simpa using congrArg e h)⟩
  obtain ⟨U, hUU₀, hX'U, hCU, hOXU, hUK, hcfpf⟩ :=
    exists_U_simple hNS h13315 h1356two hH hab hKH hHK hKL1 hhat hK2 hKC hKM hs
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hR2 : IsPGroup 2 (pCoreOf 2 (S.L1 ⊔ T)) := pCoreOf_isPGroup 2 _
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  set X := K ⊔ R with hX
  set c : G := (S.cL1 hhat : G) with hcdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hUe : IsElemAbelian 2 U := A1b.isElemAbelian_of_le (hUU₀.trans inf_le_left) hab
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hX'U
  have hcU : c ∈ Subgroup.normalizer (U : Set G) :=
    hX'U (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hXU
  have hRU : R ≤ Subgroup.normalizer (U : Set G) := le_sup_right.trans hXU
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hUR : U ≤ R := hUU₀.trans (inf_le_left.trans
    (hF.conjClosure_Vp_le_pCoreOf.trans (QH_le_R1 hH)))
  have hOU : pCoreOf 2 K ≤ Subgroup.centralizer (U : Set G) :=
    calc pCoreOf 2 K = K ⊓ Subgroup.centralizer (U : Set G) := hCU.symm
      _ ≤ _ := inf_le_right
  have hCX := A6L74.inf_centralizer_le_pCoreOf hR2 hRK hXU hCU.le
  have hred : IsTwoReducedIn X U :=
    A6L74.isTwoReducedIn_of_le (hUR.trans le_sup_right) hXU hUe hCX hOXU
  have hsyl : IsSylowTwoOf R X := isSylowTwoOf_R1_simple hH hKH hHK hKL1
  have hOXR : pCoreOf 2 X ≤ R := pCoreOf_le_of_isSylowTwoOf hsyl
  have hCR : X ⊓ Subgroup.centralizer (U : Set G) ≤ R := hCX.trans hOXR
  have hRC : R ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 X :=
    le_antisymm (fun r hr => hCX ⟨Subgroup.mem_sup_right hr.1, hr.2⟩) (le_inf hOXR hOXU)
  have hJ := not_thompsonJ_le_of_eq h1227 hhat hB hKM hUe hUR hRC
  obtain ⟨e⟩ := A6L74.nonempty_mulEquiv_autI hUe hKU hCU
  have hKpΓ : autI hUe K ≤ autI hUe X := autI_mono hUe le_sup_left
  have hΓK : autI hUe X ≤
      Subgroup.normalizer (autI hUe K : Set (MulAut (IntMod U hUe))) := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hUe).1 hγ
    exact A6L19.mem_normalizer_of_conj fun φ hφ => A6L74.convI_conj_mem hUe g.2 (hXK hg) hφ
  have hKpiso : Nonempty (↥(autI hUe K) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥(autI hUe K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rcases hiso with he | he
    · obtain ⟨e'⟩ := he
      exact Or.inl ⟨e.symm.trans e'⟩
    · obtain ⟨e'⟩ := he
      exact Or.inr ⟨e.symm.trans e'⟩
  have hZ : ∀ φ ∈ autI hUe K, (∀ ψ ∈ autI hUe K, φ * ψ = ψ * φ) → φ = 1 := by
    have hsK : IsSimpleGroup ↥(autI hUe K) := (MulEquiv.isSimpleGroup_congr e).mp hs
    intro φ hφ hcφ
    have hcen : (⟨φ, hφ⟩ : ↥(autI hUe K)) ∈ Subgroup.center ↥(autI hUe K) :=
      Subgroup.mem_center_iff.mpr fun ψ => Subtype.ext (hcφ ψ ψ.2).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autI hUe K)) with h | h
    · rw [h, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · exfalso
      obtain ⟨a, b, hab'⟩ := hnc
      apply hab'
      have ha : e a ∈ Subgroup.center ↥(autI hUe K) := by
        rw [h]
        exact Subgroup.mem_top _
      have h1 := Subgroup.mem_center_iff.mp ha (e b)
      apply e.injective
      rw [map_mul, map_mul]
      exact h1.symm
  have hCΓ := A6L74.inf_centralizer_autI_eq_bot hUe hR2 hRK hred hZ
  have hSQH : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have hSQ := A6L74.sqtkGroup_autI hUe hSQH hKH hKU hCU
  have hcomm := A6L74.commV_autI_eq_top_of_commutator hUe hKU hUK
  have hω3 : convI hUe ⟨c, hcU⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcU⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hωfpf : ∀ v : IntMod U hUe, convI hUe ⟨c, hcU⟩ v = v → v = 1 := by
    intro v hv
    have h1 := congrArg IntMod.val hv
    rw [convI_apply_val] at h1
    exact IntMod.val_injective (by rw [hcfpf _ v.val_mem h1, IntMod.val_one])
  have hωΓ : ∀ g ∈ autI hUe X, convI hUe ⟨c, hcU⟩ * g = g * convI hUe ⟨c, hcU⟩ :=
    fun g hg => commute_convI_cL1 hH hKH hHK hKL1 hhat hUe hcU hXU hOU hOXU hg
  have hRsyl : IsSylowTwoOf (autI hUe R) (autI hUe X) := B2F.isSylowTwoOf_autI hUe hXU hsyl
  have hoff : ∃ A, IsFFStarOffender (autI hUe R) A := by
    obtain ⟨B, hB'⟩ := (offenderImages_nonempty_iff_not_le hUe).2 hJ
    exact ⟨B, offenderImages_isFFStarOffender hUe hUR hRU hB'⟩
  obtain ⟨A, hu, hAC, δ, hδK, hδ3, hδ1, hδA⟩ :=
    hMod (IntMod U hUe) (fun v => IntMod.sq_eq_one v) (autI hUe X) (autI hUe K) (autI hUe R)
      (convI hUe ⟨c, hcU⟩) hSQ hKpΓ hΓK hKpiso hCΓ hcomm hω3 hωfpf hωΓ hRsyl hoff
  obtain ⟨hAJ, hJB⟩ := B2_20 hUe hUR hRU hJ hu hAC
  have hAR : A ≤ autI hUe R := by
    rw [hAJ]
    exact autI_mono hUe (thompsonJ_le_self R)
  have hBA : autI hUe (baum R) ≤ A := by
    rw [hAJ, hJB]
  obtain ⟨d, hdK, hd3, hd1, hdU, hdδ⟩ := A6L74.exists_lift_three hUe hCU hδK hδ3 hδ1
  have hdX : d ∈ X := Subgroup.mem_sup_left hdK
  have hdA : convI hUe ⟨d, hXU hdX⟩ ∈
      Subgroup.normalizer (A : Set (MulAut (IntMod U hUe))) :=
    (Subgroup.zpowers_le.2 hδA) hdδ
  have hdB := A6L74.mem_normalizer_baum le_sup_right hUe hXU hCR hAR hBA hdX hdA
  have hdM : d ∈ Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact normalizer_baum_R1_le_M h hdB
    · exact absurd h hB
  exact hd1 (eq_one_of_cube_of_mem_M hH h1337 hhat hKH hHK hL1K hdK hd3 hdM)

end Simple

end Setting4

theorem lem1374OneFinalSimple_of (hMod : Lem1374OneSimpleMod)
    (h1227 : U3.Stmt13_2_2_7) (h1337 : Stmt13_3_7) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) : Lem1374OneFinalSimple := by
  intro G _ _ T L V S hNS _ hhat H hH hab hB K hKH hHK hK2 hKC _ _ hKM hL1K hKL1 hsimp
  exact Setting4.false_of_simple hNS h13315 h1356two hH hab hKH hHK hKL1 hMod h1227 h1337 hhat hB
    hK2 hKC hKM hL1K hsimp

end CFSG.Quasithin.H13.A6
