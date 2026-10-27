module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Milestones.ASVolI.F431.JRed

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section F440

set_option linter.unusedSectionVars false

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_F_4_40_inst (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z)
    (hS : ChF.IsSylowOf 2 (SinM Gp β ε) ⊤)
    (h35 : ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)))
    (v : ↥(M₁ ⊓ M₂)) (hvS : (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hv1 : v ≠ 1)
    (hv2 : v * v = 1)
    (hsyl : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(v : E)} : Set E))
      (Gp ⊓ Subgroup.centralizer ({(v : E)} : Set E))) :
    ChF.IsSylowOf 2 (SinM Gp β ε ⊓ Subgroup.centralizer ({bM β ε v} : Set M))
      (Subgroup.centralizer ({bM β ε v} : Set M)) := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb₁ : Function.Injective (burnsideF4d_bOne β ε) :=
    hyp.inj.comp (f1_injective β hyp.faithful)
  have hbM : Function.Injective (bM β ε) :=
    burnsideF4ja_bM_injective β hyp.faithful ε hyp.inj
  have hSbH : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hSbGp : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSbP : IsPGroup 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSeq : SinM Gp β ε = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
    burnsideF4d_SinM_eq Gp β ε
  obtain ⟨u, hu⟩ : ∃ u : M, bM β ε v = u := ⟨_, rfl⟩
  have hu1 : u ≠ 1 := fun h => hv1 (hbM (by rw [hu, h, map_one]))
  have hu2 : u * u = 1 := by rw [← hu, ← map_mul, hv2, map_one]
  have huC : u ∈ Subgroup.centralizer ({u} : Set M) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨P, hP, hPu⟩ := burnsideF4ja_exists_isSylowOf_ge (burnsideF4ja_isPGroup_zpowers hu2)
    (Subgroup.zpowers_le.mpr huC)
  have huP : u ∈ P := hPu (Subgroup.mem_zpowers u)
  obtain ⟨x, -, hPx⟩ := F7.isSylowTwoOf_exists_conj_le (T := SinM Gp β ε) (H := ⊤) hS le_top
    hP.2.1
  obtain ⟨u', hu'⟩ : ∃ u' : M, u' = x⁻¹ * u * x := ⟨_, rfl⟩
  have hu'S : u' ∈ SinM Gp β ε := by rw [hu']; exact mem_conjSub.mp (hPx huP)
  have hP'S : conjSub x⁻¹ P ≤ SinM Gp β ε ⊓ Subgroup.centralizer ({u'} : Set M) := by
    refine le_inf ?_ ?_
    · have h1 := conjSub_mono x⁻¹ hPx
      rwa [conjSub_conjSub_inv] at h1
    · have h1 := conjSub_mono x⁻¹ hP.1
      rwa [← burnsideF4d_Z1_centralizer_conj, inv_inv, ← hu'] at h1
  rw [hSeq] at hu'S
  obtain ⟨w, hwM₁, hwS, hbw⟩ := mem_subImg.mp hu'S
  obtain ⟨v', hv'⟩ : ∃ v' : ↥(M₁ ⊓ M₂), v' = ⟨w, hSbH hwS⟩ := ⟨_, rfl⟩
  have hv'w : (v' : E) = w := by rw [hv']
  have hbv' : bM β ε v' = u' := by
    rw [hv', burnsideF4ja_bM_eq]
    exact hbw
  have hv'S : (v' : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by rw [hv'w]; exact hwS
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hu1
    have h1 : u' = 1 := by rw [← hbv', h, map_one]
    calc u = x * u' * x⁻¹ := by rw [hu']; group
      _ = 1 := by rw [h1]; group
  have hv'2 : v' * v' = 1 := by
    apply hbM
    rw [map_mul, hbv', map_one, hu']
    calc x⁻¹ * u * x * (x⁻¹ * u * x) = x⁻¹ * (u * u) * x := by group
      _ = 1 := by rw [hu2]; group
  have hconj : IsConj (bM β ε v) (bM β ε v') := by
    rw [isConj_iff, hu, hbv', hu']
    exact ⟨x⁻¹, by rw [inv_inv]⟩
  obtain ⟨g, hgGp, hgv⟩ :=
    (h35 v v' hvS hv'S hv1 hv'1 hv2 hv'2).mpr hconj
  have hconjC : conjSub g (Gp ⊓ Subgroup.centralizer ({(v : E)} : Set E)) =
      Gp ⊓ Subgroup.centralizer ({w} : Set E) := by
    rw [conjSub_inf, burnsideF4ja_conjSub_of_mem hgGp, ← burnsideF4d_Z1_centralizer_conj, hgv,
      hv'w]
  have hA' : ChF.IsSylowOf 2 (conjSub g (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓
      Subgroup.centralizer ({(v : E)} : Set E))) (Gp ⊓ Subgroup.centralizer ({w} : Set E)) := by
    rw [← hconjC]
    exact F7.isSylowTwoOf_conj hsyl g
  have hle1 : Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({w} : Set E)) ≤
      Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(v : E)} : Set E)) := by
    have h1 := burnsideF4ja_card_le_of_isSylowOf hA' (inf_le_inf_right _ hSbGp)
      (hSbP.to_le inf_le_left)
    rwa [burnsideF4ja_card_conjSub] at h1
  have hCSv : SinM Gp β ε ⊓ Subgroup.centralizer ({bM β ε v} : Set M) =
      subImg (burnsideF4d_bOne β ε)
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(v : E)} : Set E)) := by
    rw [hSeq, burnsideF4ja_bM_eq]
    exact burnsideF4ja_subImg_inf_centralizer hb₁ _ v.2.1
  have hCSv' : SinM Gp β ε ⊓ Subgroup.centralizer ({u'} : Set M) =
      subImg (burnsideF4d_bOne β ε)
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({w} : Set E)) := by
    rw [hSeq, ← hbw]
    exact burnsideF4ja_subImg_inf_centralizer hb₁ _ hwM₁
  have hM₁ : ∀ X : Subgroup E, pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ X ≤ M₁ := fun X =>
    inf_le_left.trans (hSbH.trans inf_le_left)
  have hle2 : Nat.card ↥P ≤ Nat.card ↥(SinM Gp β ε ⊓ Subgroup.centralizer ({u'} : Set M)) := by
    rw [← burnsideF4ja_card_conjSub x⁻¹ P]
    exact Subgroup.card_le_of_le hP'S
  rw [hCSv', L3.card_subImg _ hb₁ (hM₁ _)] at hle2
  have hfinal : Nat.card ↥P ≤
      Nat.card ↥(SinM Gp β ε ⊓ Subgroup.centralizer ({bM β ε v} : Set M)) := by
    rw [hCSv, L3.card_subImg _ hb₁ (hM₁ _)]
    exact hle2.trans hle1
  rw [hu] at hfinal ⊢
  exact burnsideF4ja_isSylowOf_of_card_le hP inf_le_right (hS.2.1.to_le inf_le_left) hfinal

end F440

end CFSG.ASVolI
