module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Smear
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux1

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] {p : ℕ} {A X Y X₁ X₂ N : Subgroup Γ}

section Transport

variable (h : NearAsolvAction p A X) (hX : X ≤ AChief.nrm N) (hA : A ≤ AChief.nrm N)

include h hX hA

theorem cenIn_qimg :
    cenIn (AChief.qimg N X) ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) =
      AChief.qimg N (cenIn X (A : Set Γ)) :=
  (AChief.qimg_inf_centralizer h.prime h.elemAbelian h.admits hA hX h.nearPSolvable.1).symm

theorem isDAIn_qimg {Z : Subgroup Γ} (hZ : IsDAIn A X Z) :
    IsDAIn (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Z) := by
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hX
  refine ⟨SolQuot.qimg_mono hZ.1, ?_⟩
  rw [cenIn_qimg h hX hA, ← SolQuot.qimg_sup hDn hA]
  exact AChief.qimg_le_normalizer hZ.2

theorem qimg_mem_iUset (hYA : Admits A Y) (hYD : Y ≤ cenIn X (A : Set Γ)) {Z : Subgroup Γ}
    (hZ : Z ∈ iUset A X Y) :
    AChief.qimg N Z ∈ iUset (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := by
  obtain ⟨hZDA, hDZ, hZY⟩ := hZ
  have hZX : Z ≤ X := hZDA.1
  have hZn : Z ≤ AChief.nrm N := hZX.trans hX
  have hYn : Y ≤ AChief.nrm N := (hYD.trans inf_le_left).trans hX
  refine ⟨isDAIn_qimg h hX hA hZDA, ?_, ?_⟩
  · rw [cenIn_qimg h hX hA]
    exact SolQuot.qimg_mono hDZ
  · rw [cenIn_qimg h hX hA, ← SolQuot.qimg_orbitClosure hYn hZn]
    have hYZ : Y ≤ Z := hYD.trans hDZ
    have hZ₀ : orbitClosure Y Z ≤ Z := orbitClosure_le_of_admits hYZ Subgroup.le_normalizer
    have hZ₀A : Admits A (orbitClosure Y Z) := admits_orbitClosure hYA hZDA.admits_left
    have hcop : Nat.Coprime p (Nat.card ↥(orbitClosure Y Z)) :=
      h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le (hZ₀.trans hZX))
    have key := AChief.qimg_inf_centralizer (N := N) h.prime h.elemAbelian hZ₀A hA
      (hZ₀.trans hZn) hcop
    have h1 : AChief.qimg N (orbitClosure Y Z) ≤ AChief.qimg N X :=
      SolQuot.qimg_mono (hZ₀.trans hZX)
    have h2 : orbitClosure Y Z ⊓ Subgroup.centralizer (A : Set Γ) = Y := by
      have h3 : orbitClosure Y Z ⊓ cenIn X (A : Set Γ) =
          orbitClosure Y Z ⊓ Subgroup.centralizer (A : Set Γ) := by
        unfold cenIn
        rw [← inf_assoc, inf_eq_left.mpr (hZ₀.trans hZX)]
      rw [← h3]
      exact hZY
    calc AChief.qimg N (orbitClosure Y Z) ⊓ AChief.qimg N (cenIn X (A : Set Γ))
        = AChief.qimg N (orbitClosure Y Z) ⊓ (AChief.qimg N X ⊓
            Subgroup.centralizer ((AChief.qimg N A : Subgroup (AChief.QG N)) :
              Set (AChief.QG N))) := by
          rw [← cenIn_qimg h hX hA]
          rfl
      _ = AChief.qimg N (orbitClosure Y Z) ⊓ Subgroup.centralizer
            ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) := by
          rw [← inf_assoc, inf_eq_left.mpr h1]
      _ = AChief.qimg N Y := by
          rw [← key, h2]

end Transport

section Pairs

theorem inf_sup_le_of_inf_le (hP : (X₁, X₂) ∈ iPairsY A X Y) (hX : X ≤ AChief.nrm N)
    (hN : N ⊓ X₁ ≤ X₂) : N ⊓ (X₁ ⊔ cenIn X (A : Set Γ)) ≤ X₂ := by
  intro n hn
  obtain ⟨hnN, hnH₀⟩ := Subgroup.mem_inf.mp hn
  have hnH : n ∈ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A := Subgroup.mem_sup_left hnH₀
  have hmem : n ∈ secCenIn (X₁ ⊔ cenIn X (A : Set Γ)) X₁ X₂ := by
    refine Subgroup.mem_inf.mpr ⟨hnH₀, ?_⟩
    rw [mem_sectionCentralizer_iff]
    refine ⟨pair_admits_H₂ hP hnH, pair_admits_H hP hnH, fun y hy => ?_⟩
    apply hN
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hyn : y ∈ AChief.nrm N := hX (pair_le hP hy)
      rw [commutatorElement_def]
      have h1 : y * n⁻¹ * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hyn n⁻¹).mp (inv_mem hnN)
      have : n * y * n⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by group
      rw [this]
      exact mul_mem hnN h1
    · rw [commutatorElement_def]
      have h1 : n * y * n⁻¹ ∈ X₁ :=
        (Subgroup.mem_normalizer_iff.mp (pair_admits_H hP hnH) y).mp hy
      exact mul_mem h1 (inv_mem hy)
  rwa [pair_secCenIn hP] at hmem

theorem inf_dsub_le (hP : (X₁, X₂) ∈ iPairsY A X Y) (hX : X ≤ AChief.nrm N)
    (hN : N ⊓ X₁ ≤ X₂) : N ⊓ cenIn X (A : Set Γ) ≤ Y := by
  intro x hx
  have h1 : x ∈ X₂ := inf_sup_le_of_inf_le hP hX hN
    (Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_sup_right hx.2⟩)
  rw [← pair_inf hP]
  exact Subgroup.mem_inf.mpr ⟨h1, hx.2⟩

theorem chief_qimg (hP : (X₁, X₂) ∈ iPairsY A X Y) (hX : X ≤ AChief.nrm N)
    (hA : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂) :
    IsChiefFactorOf (AChief.qimg N (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A)) (AChief.qimg N X₁)
      (AChief.qimg N X₂) := by
  have hX₁n : X₁ ≤ AChief.nrm N := (pair_le hP).trans hX
  have hX₂n : X₂ ≤ AChief.nrm N := (pair_le₂ hP).trans hX₁n
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hX
  have hHn : X₁ ⊔ cenIn X (A : Set Γ) ⊔ A ≤ AChief.nrm N := sup_le (sup_le hX₁n hDn) hA
  have hH₀ := inf_sup_le_of_inf_le hP hX hN
  refine ⟨⟨SolQuot.qimg_mono ((pair_le₂ hP).trans le_H),
    AChief.qimg_le_normalizer (pair_admits_H₂ hP)⟩,
    ⟨SolQuot.qimg_mono le_H, AChief.qimg_le_normalizer (pair_admits_H hP)⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne (SolQuot.qimg_mono (pair_le₂ hP)) fun heq => ?_
    refine absurd (fun x hx => ?_ : X₁ ≤ X₂) (not_le_of_gt (pair_lt hP))
    have hxn : x ∈ AChief.nrm N := hX₁n hx
    have hmem : AChief.qmap N ⟨x, hxn⟩ ∈ AChief.qimg N X₂ := by
      rw [heq]
      exact (AChief.mem_qimg_iff N X₁ _).mpr ⟨⟨x, hxn⟩, hx, rfl⟩
    exact SolQuot.mem_of_qmap_mem_qimg (Y := X₁ ⊔ cenIn X (A : Set Γ)) (R := N) (M := X₂)
      ((pair_le₂ hP).trans le_sup_left) (by rwa [inf_comm]) (Subgroup.mem_sup_left hx) hmem
  · intro K hK hX₂K hKX₁
    have hqn : SolQuot.qpre N K ≤ AChief.nrm N := SolQuot.qpre_le_nrm K
    have hHM : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (SolQuot.qpre N K) := by
      refine (SolQuot.qimg_le_normalizer_iff (R := N) (Y := AChief.nrm N) hqn
        (inf_le_right.trans (SolQuot.le_qpre K)) le_rfl hHn).mp ?_
      rw [SolQuot.qimg_qpre]
      exact hK.2
    have hX₂M : X₂ ≤ X₁ ⊓ SolQuot.qpre N K :=
      le_inf (pair_le₂ hP) ((SolQuot.qimg_le_iff hX₂n).mp hX₂K)
    have hKM : K = AChief.qimg N (X₁ ⊓ SolQuot.qpre N K) := by
      apply le_antisymm
      · intro z hz
        obtain ⟨y, hyX₁, hy⟩ := (AChief.mem_qimg_iff N X₁ z).mp (hKX₁ hz)
        refine (AChief.mem_qimg_iff N _ z).mpr ⟨y, Subgroup.mem_inf.mpr ⟨hyX₁, ?_⟩, hy⟩
        exact SolQuot.mem_qpre_iff.mpr ⟨y.2, hy ▸ hz⟩
      · exact (SolQuot.qimg_le_iff (inf_le_left.trans hX₁n)).mpr inf_le_right
    rcases (pair_chief hP).2.2.2 (X₁ ⊓ SolQuot.qpre N K)
      ⟨inf_le_left.trans le_H, (pair_admits_H hP).inf hHM⟩ hX₂M inf_le_left with h | h
    · left
      rw [hKM, h]
    · right
      rw [hKM, h]

theorem secCenIn_qimg (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hX : X ≤ AChief.nrm N) (hA : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂) :
    secCenIn (AChief.qimg N X₁ ⊔ cenIn (AChief.qimg N X)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N))) (AChief.qimg N X₁)
      (AChief.qimg N X₂) = AChief.qimg N X₂ := by
  have hX₁n : X₁ ≤ AChief.nrm N := (pair_le hP).trans hX
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hX
  have hH₀ := inf_sup_le_of_inf_le hP hX hN
  rw [cenIn_qimg h hX hA, ← SolQuot.qimg_sup hX₁n hDn]
  apply le_antisymm
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨g, hg, rfl⟩ := (AChief.mem_qimg_iff N _ z).mp hz1
    obtain ⟨-, -, hz3⟩ := (mem_sectionCentralizer_iff.mp hz2)
    have hgH : (g : Γ) ∈ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A := Subgroup.mem_sup_left hg
    have hgsec : (g : Γ) ∈ secCenIn (X₁ ⊔ cenIn X (A : Set Γ)) X₁ X₂ := by
      refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
      rw [mem_sectionCentralizer_iff]
      refine ⟨pair_admits_H₂ hP hgH, pair_admits_H hP hgH, fun y hy => ?_⟩
      have hyn : y ∈ AChief.nrm N := hX₁n hy
      have hc1 : ((⁅g, (⟨y, hyn⟩ : ↥(AChief.nrm N))⁆ : ↥(AChief.nrm N)) : Γ) ∈ X₁ := by
        show (g : Γ) * y * (g : Γ)⁻¹ * y⁻¹ ∈ X₁
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (pair_admits_H hP hgH) y).mp hy)
          (inv_mem hy)
      have hc : ((⁅g, (⟨y, hyn⟩ : ↥(AChief.nrm N))⁆ : ↥(AChief.nrm N)) : Γ) ∈ X₂ := by
        refine SolQuot.mem_of_qmap_mem_qimg (Y := X₁ ⊔ cenIn X (A : Set Γ)) (R := N) (M := X₂)
          ((pair_le₂ hP).trans le_sup_left) (by rwa [inf_comm])
          (Subgroup.mem_sup_left hc1) ?_
        rw [map_commutatorElement]
        exact hz3 _ ((AChief.mem_qimg_iff N X₁ _).mpr ⟨⟨y, hyn⟩, hy, rfl⟩)
      exact hc
    rw [pair_secCenIn hP] at hgsec
    exact (AChief.mem_qimg_iff N X₂ _).mpr ⟨g, hgsec, rfl⟩
  · intro z hz
    obtain ⟨x₂, hx₂, rfl⟩ := (AChief.mem_qimg_iff N X₂ z).mp hz
    refine Subgroup.mem_inf.mpr ⟨(AChief.mem_qimg_iff N _ _).mpr
      ⟨x₂, ((pair_le₂ hP).trans le_sup_left) hx₂, rfl⟩, ?_⟩
    rw [mem_sectionCentralizer_iff]
    refine ⟨Subgroup.le_normalizer hz,
      Subgroup.le_normalizer (SolQuot.qimg_mono (pair_le₂ hP) hz), fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff N X₁ y).mp hy
    rw [← map_commutatorElement]
    refine (AChief.mem_qimg_iff N X₂ _).mpr ⟨⁅x₂, x⁆, ?_, rfl⟩
    show (x₂ : Γ) * x * (x₂ : Γ)⁻¹ * x⁻¹ ∈ X₂
    have h1 : (x : Γ) * (x₂ : Γ)⁻¹ * x⁻¹ ∈ X₂ :=
      (Subgroup.mem_normalizer_iff.mp (pair_admits_H₂ hP (le_H hx)) _).mp (inv_mem hx₂)
    have : (x₂ : Γ) * x * (x₂ : Γ)⁻¹ * x⁻¹ = (x₂ : Γ) * ((x : Γ) * (x₂ : Γ)⁻¹ * x⁻¹) := by
      group
    rw [this]
    exact mul_mem hx₂ h1

theorem inf_qimg (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hX : X ≤ AChief.nrm N) (hA : A ≤ AChief.nrm N) :
    AChief.qimg N X₂ ⊓ cenIn (AChief.qimg N X)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) = AChief.qimg N Y := by
  have hX₂X : X₂ ≤ X := (pair_le₂ hP).trans (pair_le hP)
  have hX₂n : X₂ ≤ AChief.nrm N := hX₂X.trans hX
  have hA₂ : A ≤ Subgroup.normalizer (X₂ : Set Γ) := le_sup_right.trans (pair_admits_H₂ hP)
  have hcop : Nat.Coprime p (Nat.card ↥X₂) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hX₂X)
  have key := AChief.qimg_inf_centralizer (N := N) h.prime h.elemAbelian hA₂ hA hX₂n hcop
  have h1 : AChief.qimg N X₂ ≤ AChief.qimg N X := SolQuot.qimg_mono hX₂X
  have h2 : X₂ ⊓ Subgroup.centralizer (A : Set Γ) = Y := by
    have h3 : X₂ ⊓ cenIn X (A : Set Γ) = X₂ ⊓ Subgroup.centralizer (A : Set Γ) := by
      unfold cenIn
      rw [← inf_assoc, inf_eq_left.mpr hX₂X]
    rw [← h3]
    exact pair_inf hP
  show AChief.qimg N X₂ ⊓ (AChief.qimg N X ⊓ Subgroup.centralizer
    ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N))) = AChief.qimg N Y
  rw [← inf_assoc, inf_eq_left.mpr h1, ← key, h2]

theorem qimg_mem_iPairsY (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hX : X ≤ AChief.nrm N) (hA : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂) :
    (AChief.qimg N X₁, AChief.qimg N X₂) ∈
      iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := by
  have hX₁n : X₁ ≤ AChief.nrm N := (pair_le hP).trans hX
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hX
  refine ⟨⟨isDAIn_qimg h hX hA ⟨pair_le hP, pair_admits_left hP⟩,
    isDAIn_qimg h hX hA ⟨(pair_le₂ hP).trans (pair_le hP), pair_admits_DA₂ hP⟩, ?_, ?_⟩,
    inf_qimg h hP hX hA⟩
  · rw [cenIn_qimg h hX hA, ← SolQuot.qimg_sup hX₁n hDn, ← SolQuot.qimg_sup (sup_le hX₁n hDn) hA]
    exact chief_qimg hP hX hA hN
  · exact secCenIn_qimg h hP hX hA hN

end Pairs

section QuotientStep

@[expose] def Thm33aBelow.{v} (p n : ℕ) : Prop :=
  ∀ (Γ : Type v) [Group Γ] [Finite Γ] (A X Y : Subgroup Γ), Nat.card ↥X < n →
    NearAsolvAction p A X → (iPairsY A X Y).Nonempty → iThetaU A X Y ∈ iUset A X Y

theorem lift_orbitClosure (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hX : X ≤ AChief.nrm N) (hA : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂)
    (hbar : orbitClosure (AChief.qimg N Y) (AChief.qimg N X) ⊓
      cenIn (AChief.qimg N X)
        ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) = AChief.qimg N Y) :
    orbitClosure Y X ⊓ cenIn X (A : Set Γ) = Y := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_orbitClosure _ _) (pair_Y_le hP))
  have hxD : x ∈ cenIn X (A : Set Γ) := hx.2
  have hxn : x ∈ AChief.nrm N := hX hxD.1
  have hYn : Y ≤ AChief.nrm N := ((pair_Y_le hP).trans inf_le_left).trans hX
  have hmem : AChief.qmap N ⟨x, hxn⟩ ∈ orbitClosure (AChief.qimg N Y) (AChief.qimg N X) ⊓
      cenIn (AChief.qimg N X)
        ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← SolQuot.qimg_orbitClosure hYn hX]
      exact (AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxn⟩, hx.1, rfl⟩
    · rw [cenIn_qimg h hX hA]
      exact (AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxn⟩, hxD, rfl⟩
  rw [hbar] at hmem
  obtain ⟨y, hyY, hyx⟩ := (AChief.mem_qimg_iff N Y _).mp hmem
  obtain ⟨r, hrN, hr⟩ := Thm211.exists_mem_of_qmap_eq (R := N) (x := ⟨x, hxn⟩) (y := y) hyx.symm
  have hrD : r ∈ cenIn X (A : Set Γ) := by
    have hyD : (y : Γ) ∈ cenIn X (A : Set Γ) := pair_Y_le hP hyY
    have : r = x⁻¹ * (y : Γ) := by
      rw [hr]
      group
    rw [this]
    exact mul_mem (inv_mem hxD) hyD
  have hrY : r ∈ Y := inf_dsub_le hP hX hN (Subgroup.mem_inf.mpr ⟨hrN, hrD⟩)
  have : x = (y : Γ) * r⁻¹ := by
    rw [hr]
    group
  rw [this]
  exact mul_mem hyY (inv_mem hrY)

theorem quotient_step [Finite Γ] {n : ℕ} (ih : Thm33aBelow.{u} p n) (hn : Nat.card ↥X = n)
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y) (hθ : iThetaU A X Y = X)
    (hNX : N ≤ X) (hX : X ≤ AChief.nrm N) (hA : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂)
    (hN1 : N ≠ ⊥) : orbitClosure Y X ⊓ cenIn X (A : Set Γ) = Y := by
  have hYA : Admits A Y := le_sup_right.trans (pair_admits_Y hP)
  have hbarP := qimg_mem_iPairsY h hP hX hA hN
  have hlt : Nat.card ↥(AChief.qimg N X) < n := hn ▸ Thm211.card_qimg_lt hNX hX hN1
  have hih := ih (AChief.QG N) (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) hlt
    (Thm211.nearAsolvAction_qimg h hX hA) ⟨_, hbarP⟩
  have hle : AChief.qimg N X ≤
      iThetaU (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := by
    calc AChief.qimg N X = AChief.qimg N (iThetaU A X Y) := by rw [hθ]
      _ = ⨆ Z ∈ iUset A X Y, AChief.qimg N Z :=
          SolQuot.qimg_biSup (S := fun Z => Z) (s := iUset A X Y)
            fun Z hZ => hZ.1.1.trans hX
      _ ≤ _ := iSup₂_le fun Z hZ => le_iThetaU (qimg_mem_iUset h hX hA hYA (pair_Y_le hP) hZ)
  have heq : iThetaU (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) =
      AChief.qimg N X := le_antisymm iThetaU_le hle
  rw [heq] at hih
  exact lift_orbitClosure h hP hX hA hN hih.2.2

end QuotientStep

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a
