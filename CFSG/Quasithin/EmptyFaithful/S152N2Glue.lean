module

public import CFSG.Quasithin.EmptyFaithful.S152N2Star
public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem le_T_of_mem_sigmaSet [Finite G] {T H V B : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) (hB : B ∈ sigmaSet H V) : B ≤ T := by
  obtain ⟨A, -, rfl⟩ := hB
  exact inf_le_right.trans (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le151 hT hTH))

theorem mem_qsetOn_of_le {X Y V : Subgroup G} {A : Subgroup (MulAut V)} (hA : A ∈ QsetOn X V)
    (hAY : A ≤ autOn Y V) : A ∈ QsetOn Y V := by
  unfold QsetOn at hA ⊢
  by_cases hV : IsElemAbelian 2 V
  · simp only [hV, ↓reduceDIte] at hA ⊢
    obtain ⟨⟨⟨-, hne, hel⟩, hr⟩, hcs⟩ := hA
    exact ⟨⟨⟨hAY, hne, hel⟩, hr⟩, hcs⟩
  · simp only [hV, ↓reduceDIte] at hA
    exact absurd hA (by simp)

theorem commutator_preOn_eq {T M V B : Subgroup G} (hV : IsElemAbelian 2 V) (hBT : B ≤ T)
    (hTM : T ≤ M) (hMV : M ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, preOn T V (autOn B V)⁆ = ⁅V, B⁆ := by
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBT.trans (hTM.trans hMV)
  have hPN : preOn T V (autOn B V) ≤ Subgroup.normalizer (V : Set G) :=
    (preOn_le T V _).trans (hTM.trans hMV)
  have hBT' : autOn B V ≤ autOn T V := A4.autOn_mono hBT
  rw [commutator_eq_map_commV hV hPN, commutator_eq_map_commV hV hBN, autOn_preOn hBT']

theorem fixV_eq_commV_of_card_two {V : Type*} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16) {Bb : Subgroup (MulAut V)}
    (h2 : Nat.card Bb = 2) (h4 : Nat.card (commV Bb) = 4) : fixV Bb = commV Bb := by
  obtain ⟨b, -, hb, rfl⟩ := exists_zpowers_eq_of_card_two h2
  exact fixV_eq_commV_of_card hV2 hb hcard h4

theorem exists_w₀ [Finite G] {T V W : Subgroup G} (hT : IsPGroup 2 T) (hWV : W ≤ V) (hVT : V ≤ T)
    (hVE : IsElemAbelian 2 V) (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hW1 : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ quasithinOmegaOneCenter T := by
  obtain ⟨w, hwW, hw1, hwc⟩ := exists_central_of_normalized hT (hWV.trans hVT) hTW hW1
  refine ⟨w, hwW, hw1, Subgroup.subset_closure ⟨⟨(hWV.trans hVT) hwW, ?_⟩, hVE.2 w (hWV hwW)⟩⟩
  exact Subgroup.mem_centralizer_iff.mpr fun h hh => hwc h hh

theorem le_normalizer_map_subtype' {A : Type*} [Group A] (X : Subgroup A) (K : Subgroup X)
    [K.Normal] : X ≤ Subgroup.normalizer ((K.map X.subtype : Subgroup A) : Set A) := by
  have key : ∀ g ∈ X, ∀ n ∈ K.map X.subtype, g * n * g⁻¹ ∈ K.map X.subtype := by
    rintro g hg _ ⟨k, hk, rfl⟩
    exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨g, hg⟩, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g hg h
  · intro hh
    have := key g⁻¹ (X.inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at this

theorem le_fittingIn_of_comm {A : Type*} [Group A] {X K : Subgroup A} (hKX : K ≤ X)
    (hn : X ≤ Subgroup.normalizer (K : Set A)) (hc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) :
    K ≤ fittingIn X := by
  have hnorm : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hn
  have hnil : Group.IsNilpotent (K.subgroupOf X) := by
    let _ : CommGroup (K.subgroupOf X) :=
      { (inferInstance : Group (K.subgroupOf X)) with
        mul_comm := fun a b => Subtype.ext (Subtype.ext (hc a a.2 b b.2)) }
    infer_instance
  have hle : K.subgroupOf X ≤ CFSG.fittingSubgroup X := le_sSup ⟨hnorm, hnil⟩
  have := Subgroup.map_mono (f := X.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hKX] at this

theorem fittingIn_le {A : Type*} [Group A] (X : Subgroup A) : fittingIn X ≤ X :=
  Subgroup.map_subtype_le _

end S152N2

end CFSG.Quasithin
