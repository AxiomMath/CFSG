module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux3

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

@[expose] def Thm36Below.{v} (p n : ℕ) : Prop :=
  ∀ (Γ : Type v) [Group Γ] [Finite Γ] (A W Y X₁ X₂ : Subgroup Γ),
    Nat.card ↥W + Nat.card ↥X₁ < n → NearAsolvAction p A W → (iPairsY A W Y).Nonempty →
    IsDAIn A W X₁ → IsDAIn A W X₂ →
    IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂ → ¬ IsSolvableSection X₁ X₂ →
    X₂ ⊓ cenIn W (A : Set Γ) ≤ Y →
    X₁ ⊓ cenIn W (A : Set Γ) ≤ Y ∨ secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y

variable {Γ : Type u} [Group Γ]

theorem chief_qimg {p : ℕ} {A W X₁ X₂ N : Subgroup Γ} (h : NearAsolvAction p A W)
    (hX₁ : IsDAIn A W X₁)
    (hc : IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂)
    (hWN : W ≤ AChief.nrm N) (hAN : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂) :
    IsChiefFactorOf (AChief.qimg N X₁ ⊔ cenIn (AChief.qimg N W)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ⊔ AChief.qimg N A)
      (AChief.qimg N X₁) (AChief.qimg N X₂) := by
  have hX₁n : X₁ ≤ AChief.nrm N := hX₁.1.trans hWN
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  have hX₂n : X₂ ≤ AChief.nrm N := hX₂X₁.trans hX₁n
  have hDn : cenIn W (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hWN
  have hHn : X₁ ⊔ cenIn W (A : Set Γ) ⊔ A ≤ AChief.nrm N := sup_le (sup_le hX₁n hDn) hAN
  rw [Thm33a.cenIn_qimg h hWN hAN, ← SolQuot.qimg_sup hX₁n hDn,
    ← SolQuot.qimg_sup (sup_le hX₁n hDn) hAN]
  have hX₁H : X₁ ≤ X₁ ⊔ cenIn W (A : Set Γ) ⊔ A := le_sup_left.trans le_sup_left
  refine ⟨⟨SolQuot.qimg_mono (hX₂X₁.trans hX₁H), AChief.qimg_le_normalizer hc.1.2⟩,
    ⟨SolQuot.qimg_mono hX₁H, AChief.qimg_le_normalizer hc.2.1.2⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne (SolQuot.qimg_mono hX₂X₁) fun heq => hc.2.2.1.not_ge ?_
    intro x hx
    have hxn : x ∈ AChief.nrm N := hX₁n hx
    have hmem : AChief.qmap N ⟨x, hxn⟩ ∈ AChief.qimg N X₂ := by
      rw [heq]
      exact (AChief.mem_qimg_iff N X₁ _).mpr ⟨⟨x, hxn⟩, hx, rfl⟩
    exact SolQuot.mem_of_qmap_mem_qimg (Y := X₁) (R := N) (M := X₂) hX₂X₁
      (by rwa [inf_comm]) hx hmem
  · intro K hK hX₂K hKX₁
    have hqn : SolQuot.qpre N K ≤ AChief.nrm N := SolQuot.qpre_le_nrm K
    have hHM : Admits (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (SolQuot.qpre N K) := by
      refine (SolQuot.qimg_le_normalizer_iff (R := N) (Y := AChief.nrm N) hqn
        (inf_le_right.trans (SolQuot.le_qpre K)) le_rfl hHn).mp ?_
      rw [SolQuot.qimg_qpre]
      exact hK.2
    have hX₂M : X₂ ≤ X₁ ⊓ SolQuot.qpre N K :=
      le_inf hX₂X₁ ((SolQuot.qimg_le_iff hX₂n).mp hX₂K)
    have hKM : K = AChief.qimg N (X₁ ⊓ SolQuot.qpre N K) := by
      apply le_antisymm
      · intro z hz
        obtain ⟨y, hyX₁, hy⟩ := (AChief.mem_qimg_iff N X₁ z).mp (hKX₁ hz)
        refine (AChief.mem_qimg_iff N _ z).mpr ⟨y, Subgroup.mem_inf.mpr ⟨hyX₁, ?_⟩, hy⟩
        exact SolQuot.mem_qpre_iff.mpr ⟨y.2, hy ▸ hz⟩
      · exact (SolQuot.qimg_le_iff (inf_le_left.trans hX₁n)).mpr inf_le_right
    rcases hc.2.2.2 (X₁ ⊓ SolQuot.qpre N K) ⟨inf_le_left.trans hX₁H, Admits.inf hc.2.1.2 hHM⟩
      hX₂M inf_le_left with h0 | h0
    · left
      rw [hKM, h0]
    · right
      rw [hKM, h0]

theorem isSolvableSection_of_qimg {X₁ X₂ N : Subgroup Γ} (hX₁n : X₁ ≤ AChief.nrm N)
    (hX₂X₁ : X₂ ≤ X₁) (hN : N ⊓ X₁ ≤ X₂)
    (h : IsSolvableSection (AChief.qimg N X₁) (AChief.qimg N X₂)) : IsSolvableSection X₁ X₂ := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (SolQuot.qres_surjective hX₁n) n,
    SolQuot.subgroupOf_qimg hX₁n hX₂X₁] at hn
  calc derivedSeries ↥X₁ n
      ≤ ((X₂.subgroupOf X₁).map (SolQuot.qres N X₁ hX₁n)).comap (SolQuot.qres N X₁ hX₁n) :=
        Subgroup.map_le_iff_le_comap.mp hn
    _ = X₂.subgroupOf X₁ ⊔ (SolQuot.qres N X₁ hX₁n).ker := Subgroup.comap_map_eq _ _
    _ ≤ X₂.subgroupOf X₁ := by
        refine sup_le le_rfl ?_
        rw [SolQuot.ker_qres hX₁n]
        intro x hx
        exact Subgroup.mem_subgroupOf.mpr (hN ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩)

theorem inf_cenIn_qimg_le {p : ℕ} {A W Y X₂ N : Subgroup Γ} (h : NearAsolvAction p A W)
    (hX₂ : IsDAIn A W X₂) (hWN : W ≤ AChief.nrm N) (hAN : A ≤ AChief.nrm N)
    (hX₂Y : X₂ ⊓ cenIn W (A : Set Γ) ≤ Y) :
    AChief.qimg N X₂ ⊓ cenIn (AChief.qimg N W)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ≤ AChief.qimg N Y := by
  have hX₂n : X₂ ≤ AChief.nrm N := hX₂.1.trans hWN
  have hcop : Nat.Coprime p (Nat.card ↥X₂) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hX₂.1)
  have key := AChief.qimg_inf_centralizer (N := N) h.prime h.elemAbelian hX₂.admits_left hAN
    hX₂n hcop
  intro z hz
  obtain ⟨hz₂, hzD⟩ := Subgroup.mem_inf.mp hz
  have hzC : z ∈ Subgroup.centralizer
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) :=
    (Subgroup.mem_inf.mp hzD).2
  have hz3 : z ∈ AChief.qimg N (X₂ ⊓ Subgroup.centralizer (A : Set Γ)) := by
    rw [key]
    exact ⟨hz₂, hzC⟩
  have hle : X₂ ⊓ Subgroup.centralizer (A : Set Γ) ≤ Y := fun x hx =>
    hX₂Y (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, Subgroup.mem_inf.mpr
      ⟨hX₂.1 (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩⟩)
  exact SolQuot.qimg_mono hle hz3

theorem mem_of_qmap_mem_qimg_cen {A W Y N : Subgroup Γ} {x : Γ}
    (hYD : Y ≤ cenIn W (A : Set Γ)) (hNY : N ⊓ cenIn W (A : Set Γ) ≤ Y)
    (hxD : x ∈ cenIn W (A : Set Γ)) (hxn : x ∈ AChief.nrm N)
    (hx : AChief.qmap N ⟨x, hxn⟩ ∈ AChief.qimg N Y) : x ∈ Y := by
  obtain ⟨y, hyY, hyx⟩ := (AChief.mem_qimg_iff N Y _).mp hx
  obtain ⟨r, hrN, hr⟩ := Thm211.exists_mem_of_qmap_eq hyx
  have hr' : x = (y : Γ) * r := hr
  have hrD : r ∈ cenIn W (A : Set Γ) := by
    have : r = (y : Γ)⁻¹ * x := by rw [hr']; group
    rw [this]
    exact mul_mem (inv_mem (hYD hyY)) hxD
  rw [hr']
  exact mul_mem hyY (hNY ⟨hrN, hrD⟩)

theorem inf_le_of_qimg {p : ℕ} {A W Y X₁ N : Subgroup Γ} (h : NearAsolvAction p A W)
    (hX₁ : IsDAIn A W X₁) (hWN : W ≤ AChief.nrm N) (hAN : A ≤ AChief.nrm N)
    (hYD : Y ≤ cenIn W (A : Set Γ)) (hNY : N ⊓ cenIn W (A : Set Γ) ≤ Y)
    (hbar : AChief.qimg N X₁ ⊓ cenIn (AChief.qimg N W)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ≤ AChief.qimg N Y) :
    X₁ ⊓ cenIn W (A : Set Γ) ≤ Y := by
  intro x hx
  obtain ⟨hxX, hxD⟩ := Subgroup.mem_inf.mp hx
  have hxn : x ∈ AChief.nrm N := hWN (hX₁.1 hxX)
  refine mem_of_qmap_mem_qimg_cen hYD hNY hxD hxn (hbar ?_)
  refine Subgroup.mem_inf.mpr ⟨(AChief.mem_qimg_iff N X₁ _).mpr ⟨⟨x, hxn⟩, hxX, rfl⟩, ?_⟩
  rw [Thm33a.cenIn_qimg h hWN hAN]
  exact (AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxn⟩, hxD, rfl⟩

theorem secCenIn_eq_of_qimg {p : ℕ} {A W Y X₁ X₂ N : Subgroup Γ} (h : NearAsolvAction p A W)
    (hX₁ : IsDAIn A W X₁) (hX₂ : IsDAIn A W X₂) (hWN : W ≤ AChief.nrm N)
    (hAN : A ≤ AChief.nrm N) (hN : N ⊓ X₁ ≤ X₂) (hX₂X₁ : X₂ ≤ X₁)
    (hYD : Y ≤ cenIn W (A : Set Γ)) (hNY : N ⊓ cenIn W (A : Set Γ) ≤ Y)
    (hbar : secCenIn (cenIn (AChief.qimg N W)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)))
      (AChief.qimg N X₁) (AChief.qimg N X₂) = AChief.qimg N Y) :
    secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y := by
  have hX₁n : X₁ ≤ AChief.nrm N := hX₁.1.trans hWN
  have hX₂n : X₂ ≤ AChief.nrm N := hX₂X₁.trans hX₁n
  have hDn : cenIn W (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hWN
  have hDW : cenIn W (A : Set Γ) ≤ W := inf_le_left
  have hDX₁ : cenIn W (A : Set Γ) ≤ Subgroup.normalizer (X₁ : Set Γ) :=
    le_sup_left.trans hX₁.2
  have hDX₂ : cenIn W (A : Set Γ) ≤ Subgroup.normalizer (X₂ : Set Γ) :=
    le_sup_left.trans hX₂.2
  rw [Thm33a.cenIn_qimg h hWN hAN] at hbar
  refine le_antisymm (fun d hd => ?_) (fun y hy => ?_)
  · obtain ⟨hdD, hdsc⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨-, -, hdcomm⟩ := mem_sectionCentralizer_iff.mp hdsc
    have hdn : d ∈ AChief.nrm N := hDn hdD
    have hbd : AChief.qmap N ⟨d, hdn⟩ ∈ AChief.qimg N (cenIn W (A : Set Γ)) :=
      (AChief.mem_qimg_iff N _ _).mpr ⟨⟨d, hdn⟩, hdD, rfl⟩
    have hbdq : AChief.qmap N ⟨d, hdn⟩ ∈ secCenIn (AChief.qimg N (cenIn W (A : Set Γ)))
        (AChief.qimg N X₁) (AChief.qimg N X₂) := by
      refine Subgroup.mem_inf.mpr ⟨hbd, mem_sectionCentralizer_iff.mpr ⟨?_, ?_, ?_⟩⟩
      · exact AChief.qimg_le_normalizer hDX₂ hbd
      · exact AChief.qimg_le_normalizer hDX₁ hbd
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff N X₁ z).mp hz
        rw [← map_commutatorElement]
        exact (AChief.mem_qimg_iff N X₂ _).mpr ⟨⁅(⟨d, hdn⟩ : ↥(AChief.nrm N)), y⁆,
          hdcomm _ hy, rfl⟩
    rw [hbar] at hbdq
    exact mem_of_qmap_mem_qimg_cen hYD hNY hdD hdn hbdq
  · have hyD : y ∈ cenIn W (A : Set Γ) := hYD hy
    have hyn : y ∈ AChief.nrm N := hDn hyD
    have hbyq : AChief.qmap N ⟨y, hyn⟩ ∈ secCenIn (AChief.qimg N (cenIn W (A : Set Γ)))
        (AChief.qimg N X₁) (AChief.qimg N X₂) := by
      rw [hbar]
      exact (AChief.mem_qimg_iff N Y _).mpr ⟨⟨y, hyn⟩, hy, rfl⟩
    obtain ⟨-, hysc⟩ := Subgroup.mem_inf.mp hbyq
    obtain ⟨-, -, hycomm⟩ := mem_sectionCentralizer_iff.mp hysc
    refine Subgroup.mem_inf.mpr ⟨hyD, mem_sectionCentralizer_iff.mpr ⟨hDX₂ hyD, hDX₁ hyD,
      fun x hx => ?_⟩⟩
    have hxn : x ∈ AChief.nrm N := hX₁n hx
    have hmem := hycomm (AChief.qmap N ⟨x, hxn⟩)
      ((AChief.mem_qimg_iff N X₁ _).mpr ⟨⟨x, hxn⟩, hx, rfl⟩)
    rw [← map_commutatorElement] at hmem
    have hcX₁ : ⁅y, x⁆ ∈ X₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hDX₁ hyD) x).mp hx
      exact mul_mem this (inv_mem hx)
    exact SolQuot.mem_of_qmap_mem_qimg (Y := X₁) (R := N) (M := X₂) hX₂X₁
      (by rwa [inf_comm]) (z := ⟨⁅y, x⁆, hX₁n hcX₁⟩) hcX₁ hmem

theorem quotient_step [Finite Γ] {p n : ℕ} (ih : Thm36Below.{u} p n)
    {A W Y X₁ X₂ Z₁ Z₂ N : Subgroup Γ} (hn : Nat.card ↥W + Nat.card ↥X₁ ≤ n)
    (h : NearAsolvAction p A W) (hZ : (Z₁, Z₂) ∈ iPairsY A W Y)
    (hX₁ : IsDAIn A W X₁) (hX₂ : IsDAIn A W X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    (hX₂Y : X₂ ⊓ cenIn W (A : Set Γ) ≤ Y)
    (hNW : N ≤ W) (hWN : W ≤ AChief.nrm N) (hAN : A ≤ AChief.nrm N) (hN : N ⊓ Z₁ ≤ Z₂)
    (hN1 : N ≠ ⊥) :
    X₁ ⊓ cenIn W (A : Set Γ) ≤ Y ∨ secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y := by
  have hNY : N ⊓ cenIn W (A : Set Γ) ≤ Y := Thm33a.inf_dsub_le hZ hWN hN
  have hYD : Y ≤ cenIn W (A : Set Γ) := Thm33a.pair_Y_le hZ
  have hX₁n : X₁ ≤ AChief.nrm N := hX₁.1.trans hWN
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  by_cases hdeg : X₁ ≤ X₂ ⊔ N
  · left
    intro x hx
    obtain ⟨hxX, hxD⟩ := Subgroup.mem_inf.mp hx
    have hcop : Nat.Coprime p (Nat.card ↥X₂) :=
      h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hX₂.1)
    obtain ⟨m, hm, r, hr, rfl⟩ := exists_mul_of_mem_sup_cen h.prime h.elemAbelian
      hX₂.admits_left hAN (hX₂.1.trans hWN) hcop (hdeg hxX) (Subgroup.mem_inf.mp hxD).2
    exact mul_mem (hX₂Y ⟨hm.1, Subgroup.mem_inf.mpr ⟨hX₂.1 hm.1, hm.2⟩⟩)
      (hNY ⟨hr.1, Subgroup.mem_inf.mpr ⟨hNW hr.1, hr.2⟩⟩)
  · have hHN : X₁ ⊔ cenIn W (A : Set Γ) ⊔ A ≤ AChief.nrm N :=
      sup_le (sup_le hX₁n (inf_le_left.trans hWN)) hAN
    have hNX₁ : N ⊓ X₁ ≤ X₂ := by
      have hadm : Admits (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (N ⊓ X₁) :=
        Admits.inf hHN hc.2.1.2
      rcases Thm33a.chief_dichotomy hc hadm inf_le_right with h1 | h1
      · exact h1
      · exfalso
        apply hdeg
        rw [← h1]
        exact sup_le_sup_right inf_le_left X₂ |>.trans (by rw [sup_comm])
    have hnear : NearAsolvAction p (AChief.qimg N A) (AChief.qimg N W) :=
      Thm211.nearAsolvAction_qimg h hWN hAN
    have hpair : (iPairsY (AChief.qimg N A) (AChief.qimg N W) (AChief.qimg N Y)).Nonempty :=
      ⟨_, Thm33a.qimg_mem_iPairsY h hZ hWN hAN hN⟩
    have hcardW : Nat.card ↥(AChief.qimg N W) < Nat.card ↥W :=
      Thm211.card_qimg_lt hNW hWN hN1
    have hcardX : Nat.card ↥(AChief.qimg N X₁) ≤ Nat.card ↥X₁ :=
      Nat.card_le_card_of_surjective _ (SolQuot.qres_surjective hX₁n)
    have hlt : Nat.card ↥(AChief.qimg N W) + Nat.card ↥(AChief.qimg N X₁) < n := by omega
    have hqns : ¬ IsSolvableSection (AChief.qimg N X₁) (AChief.qimg N X₂) := fun hs =>
      hns (isSolvableSection_of_qimg hX₁n hX₂X₁ hNX₁ hs)
    rcases ih (AChief.QG N) (AChief.qimg N A) (AChief.qimg N W) (AChief.qimg N Y)
      (AChief.qimg N X₁) (AChief.qimg N X₂) hlt hnear hpair
      (Thm33a.isDAIn_qimg h hWN hAN hX₁) (Thm33a.isDAIn_qimg h hWN hAN hX₂)
      (chief_qimg h hX₁ hc hWN hAN hNX₁) hqns
      (inf_cenIn_qimg_le h hX₂ hWN hAN hX₂Y) with h1 | h1
    · exact Or.inl (inf_le_of_qimg h hX₁ hWN hAN hYD hNY h1)
    · exact Or.inr (secCenIn_eq_of_qimg h hX₁ hX₂ hWN hAN hNX₁ hX₂X₁ hYD hNY h1)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36
