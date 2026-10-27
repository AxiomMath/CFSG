module

public import CFSG.Quasithin.Background.RonanE43Out
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.RonanE43Basic

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.E2P B6
  CFSG.Quasithin.E2P.SporB

variable {G : Type} [Group G]

theorem card_sup_eq_relIndex_mul {P T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (P : Set G)) :
    Nat.card ↥(P ⊔ T) = P.relIndex T * Nat.card P := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hT
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T P hT
  have h1 : Nat.card (↥T ⧸ P.subgroupOf T) =
      Nat.card (↥(T ⊔ P) ⧸ P.subgroupOf (T ⊔ P)) := Nat.card_congr e.toEquiv
  have h2 : P.relIndex (T ⊔ P) * Nat.card ↥(P ⊓ (T ⊔ P)) = Nat.card ↥(T ⊔ P) :=
    Subgroup.relIndex_mul_card (H := P) (K := T ⊔ P)
  rw [inf_eq_left.mpr le_sup_right] at h2
  rw [sup_comm, ← h2]
  have h3 : P.relIndex (T ⊔ P) = P.relIndex T := by
    unfold Subgroup.relIndex Subgroup.index
    exact h1.symm
  rw [h3]

variable [Finite G]

theorem card_le_two_mul_pCoreOf {T H : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (h3 : Nat.card H = 3 * Nat.card T) : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H) := by
  set K : Subgroup ↥H := T.subgroupOf H with hK
  have hKcard : Nat.card K = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hKidx : K.index = 3 := by
    have h1 := Subgroup.card_mul_index K
    rw [hKcard] at h1
    have : Nat.card T * K.index = Nat.card T * 3 := by rw [h1, h3]; ring
    exact Nat.eq_of_mul_eq_mul_left hTpos this
  have hKp : IsPGroup 2 K := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  set C : Subgroup ↥H := K.normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal K
  have hCp : IsPGroup 2 C := hKp.to_le (Subgroup.normalCore_le K)
  have hCle : C.map H.subtype ≤ pCoreOf 2 H :=
    Subgroup.map_mono (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hCp)
  have hCcard : Nat.card C ≤ Nat.card (pCoreOf 2 H) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective (K := C)]
    exact Subgroup.card_le_of_le hCle
  have hidx : C.index ≤ 6 := by
    have := Subgroup.index_normalCore_le_factorial_index K
    rw [hKidx] at this
    simpa [Nat.factorial] using this
  have hH : Nat.card C * C.index = Nat.card H := Subgroup.card_mul_index C
  have hHcard : Nat.card H = Nat.card ↥H := rfl
  have h6 : Nat.card H ≤ 6 * Nat.card C := by
    calc Nat.card H = Nat.card C * C.index := hH.symm
      _ ≤ Nat.card C * 6 := Nat.mul_le_mul_left _ hidx
      _ = 6 * Nat.card C := by ring
  omega


theorem aParam_le_of_normal_family (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hLT : L ⊔ T = ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    {Γ : Type} [Group Γ] [Finite Γ] (e₀ : ↥L ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (F : Finset (Subgroup Γ)) (hF : F.Nonempty) (hSF : ∀ Y ∈ F, S₀ ≤ Y)
    (h3 : ∀ Y ∈ F, Nat.card Y = 3 * Nat.card S₀) (hgen : (⨆ Y ∈ F, Y) = ⊤)
    (hinv : ∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ → ∀ Y ∈ F, Y.map α.toMonoidHom = Y) :
    aParam ρ.range ≤ F.card := by
  classical
  have hK : L.Normal := normal_of_generalizedFitting hLF
  have hSK : IsSylowTwoOf (T ⊓ L) L :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e, he⟩ := exists_equiv_sylow e₀ hSK hS₀
  have hα : ∀ t ∈ T, S₀.map (autK e t).toMonoidHom = S₀ := fun t ht => by
    rw [← he]
    exact map_autK_of_mem_normalizer' e inf_le_right (le_normalizer_inf hK ht)
  let pull : Subgroup Γ → Subgroup G := fun P => (P.map e.symm.toMonoidHom).map L.subtype
  have hpullS : pull S₀ = T ⊓ L := by
    show (S₀.map e.symm.toMonoidHom).map L.subtype = T ⊓ L
    rw [← he]
    exact pull_map e inf_le_right
  have hpullcard : ∀ P : Subgroup Γ, Nat.card (pull P) = Nat.card P := fun P => by
    show Nat.card ((P.map e.symm.toMonoidHom).map L.subtype) = Nat.card P
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hTn : ∀ Y ∈ F, T ≤ Subgroup.normalizer ((pull Y : Subgroup G) : Set G) :=
    fun Y hY t ht => mem_normalizer_pull e (hinv _ (hα t ht) Y hY)
  let Δ : Finset (Subgroup G) := F.image (fun Y => pull Y ⊔ T)
  have hΔT : ∀ H ∈ Δ, T ≤ H := by
    intro H hH
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.mp hH
    exact le_sup_right
  have h2 : ∀ H ∈ Δ, Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H) := by
    intro H hH
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hH
    have hPL : pull Y ≤ L := pull_le e Y
    have hSP : T ⊓ L ≤ pull Y := by
      rw [← hpullS]
      exact pull_mono e (hSF Y hY)
    have hPT : pull Y ⊓ T = T ⊓ L := by
      apply le_antisymm
      · intro x hx
        exact ⟨hx.2, hPL hx.1⟩
      · exact le_inf hSP inf_le_left
    have hcardH : Nat.card ↥(pull Y ⊔ T) = 3 * Nat.card T := by
      rw [card_sup_eq_relIndex_mul (hTn Y hY), hpullcard, h3 Y hY]
      have h1 := Subgroup.relIndex_mul_card (H := pull Y) (K := T)
      rw [hPT] at h1
      have hS : Nat.card ↥(T ⊓ L) = Nat.card S₀ := by rw [← hpullS, hpullcard]
      rw [hS] at h1
      calc (pull Y).relIndex T * (3 * Nat.card S₀) = 3 * ((pull Y).relIndex T * Nat.card S₀) := by
            ring
        _ = 3 * Nat.card T := by rw [h1]
    exact card_le_two_mul_pCoreOf le_sup_right hT.isPGroup hcardH
  have hΔgen : (⨆ H ∈ Δ, H) = ⊤ := by
    have hLle : L ≤ ⨆ H ∈ Δ, H := by
      have h1 : pull (⨆ Y ∈ F, Y) = ⨆ Y ∈ F, pull Y := by
        simp only [pull, Subgroup.map_iSup]
      have h2' : pull (⊤ : Subgroup Γ) = L := pull_top e
      rw [← h2', ← hgen, h1]
      exact iSup₂_le fun Y hY =>
        le_iSup₂_of_le (pull Y ⊔ T) (Finset.mem_image.mpr ⟨Y, hY, rfl⟩) le_sup_left
    obtain ⟨Y0, hY0⟩ := hF
    have hTle : T ≤ ⨆ H ∈ Δ, H :=
      le_iSup₂_of_le (pull Y0 ⊔ T) (Finset.mem_image.mpr ⟨Y0, hY0, rfl⟩) le_sup_right
    rw [eq_top_iff, ← hLT]
    exact sup_le hLle hTle
  have hmain := aParam_le_card_of_family V ρ hρ hO2 Δ hT hLF hLq hLT hlt hΔgen hΔT h2
  exact hmain.trans Finset.card_image_le

end CFSG.Quasithin.RonanE43
