module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypAAuxNonsolv

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G]

@[expose] def HypA5 (H A D D₂ : Subgroup G) : Prop :=
  ∀ X₁ X₂ : Subgroup G, X₁ ≤ H → X₂ ≤ H → Admits (D ⊔ A) X₁ → Admits (D ⊔ A) X₂ →
    IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂ → ¬ IsSolvableSection X₁ X₂ →
      X₂ ⊓ D ≤ D₂ → X₁ ⊓ D ≤ D₂

@[expose] def HypA6 (H A D D₁ D₂ : Subgroup G) : Prop :=
  ∀ N L R : Subgroup G, N ≤ H → L ≤ H → R ≤ H →
    Admits (D ⊔ A) N → Admits (D ⊔ A) L → Admits (D ⊔ A) R → L ≤ R →
    IsChiefFactorOf (R ⊔ D ⊔ A) L N →
    A ⊔ R ≤ secCenIn (R ⊔ D ⊔ A) L N →
    R ⊓ D = D₁ → D ⊓ N ≤ D₂ → IsDirectProductMod N (D₁ ⊔ N) (D₂ ⊔ N) L →
    ∃ B : Subgroup G, B ≤ R ∧ Admits (R ⊔ D ⊔ A) B ∧ B ⊓ D = D₂ ∧ R = B ⊔ D₁

structure HypA15 (p : ℕ) (H A D D₁ D₂ : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  a1_elemAbelian : IsElemAbelian p A
  a1_admits : Admits A H
  a1_near : NearASolvable p A H
  a3 : D = H ⊓ Subgroup.centralizer (A : Set G)
  a4_chief : IsChiefFactorOf D D₁ D₂
  a4_unique : ∀ M : Subgroup G, IsChiefFactorOf D M D₂ → M = D₁
  a4c : secCenIn D D₁ D₂ = D₁
  a5 : HypA5 H A D D₂

structure HypA (p : ℕ) (H A D D₁ D₂ : Subgroup G) : Prop extends HypA15 p H A D D₁ D₂ where
  a6 : HypA6 H A D D₁ D₂

@[expose] def ssSet (H A D D₂ : Subgroup G) : Set (Subgroup G) :=
  {M | M ≤ H ∧ Admits (D ⊔ A) M ∧ M ⊓ D = D₂}

section Basic

variable {p : ℕ} {H A D D₁ D₂ : Subgroup G}

theorem HypA15.D_le (h : HypA15 p H A D D₁ D₂) : D ≤ H := h.a3.le.trans inf_le_left

theorem HypA15.D_le_centralizer (h : HypA15 p H A D D₁ D₂) :
    D ≤ Subgroup.centralizer (A : Set G) := h.a3.le.trans inf_le_right

theorem HypA15.mem_D (h : HypA15 p H A D D₁ D₂) {y : G} (hy : y ∈ H)
    (hyC : y ∈ Subgroup.centralizer (A : Set G)) : y ∈ D :=
  h.a3 ▸ Subgroup.mem_inf.mpr ⟨hy, hyC⟩

theorem HypA15.D₂_le (h : HypA15 p H A D D₁ D₂) : D₂ ≤ D := h.a4_chief.1.1

theorem HypA15.D₁_le (h : HypA15 p H A D D₁ D₂) : D₁ ≤ D := h.a4_chief.2.1.1

theorem HypA15.D₂_lt (h : HypA15 p H A D D₁ D₂) : D₂ < D₁ := h.a4_chief.2.2.1

theorem HypA15.coprime (h : HypA15 p H A D D₁ D₂) : Nat.Coprime p (Nat.card H) :=
  h.a1_near.1.1

theorem admits_of_le_centralizer {Q X : Subgroup G} (h : X ≤ Subgroup.centralizer (Q : Set G)) :
    Admits Q X :=
  (Subgroup.le_centralizer_iff.mp h).trans (Subgroup.centralizer_le_normalizer _)

theorem HypA15.admits_D (h : HypA15 p H A D D₁ D₂) : Admits (D ⊔ A) D :=
  sup_le Subgroup.le_normalizer (admits_of_le_centralizer h.D_le_centralizer)

theorem HypA15.admits_D₂ (h : HypA15 p H A D D₁ D₂) : Admits (D ⊔ A) D₂ :=
  sup_le h.a4_chief.1.2 (admits_of_le_centralizer (h.D₂_le.trans h.D_le_centralizer))

theorem HypA15.admits_D₁ (h : HypA15 p H A D D₁ D₂) : Admits (D ⊔ A) D₁ :=
  sup_le h.a4_chief.2.1.2 (admits_of_le_centralizer (h.D₁_le.trans h.D_le_centralizer))

theorem HypA15.D₂_mem (h : HypA15 p H A D D₁ D₂) : D₂ ∈ ssSet H A D D₂ :=
  ⟨h.D₂_le.trans h.D_le, h.admits_D₂, inf_eq_left.mpr h.D₂_le⟩

theorem HypA15.inf_sup_le_of_le (h : HypA15 p H A D D₁ D₂) {H₀ : Subgroup G} (hH₀ : H₀ ≤ H)
    (hA : Admits A H₀) : H ⊓ (H₀ ⊔ A) ≤ H₀ := by
  intro x hx
  obtain ⟨hxH, hxDA⟩ := Subgroup.mem_inf.mp hx
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left H₀ A hA
  have hx' : x ∈ (H₀ : Set G) * (A : Set G) := by
    rw [← hmul]
    exact hxDA
  obtain ⟨d, hd, a, ha, rfl⟩ := Set.mem_mul.mp hx'
  have hd' : d ∈ H₀ := hd
  have ha' : a ∈ A := ha
  have haH : a ∈ H := by
    have := mul_mem (inv_mem (hH₀ hd')) hxH
    simpa using this
  have hord : orderOf a = 1 := by
    have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (h.a1_elemAbelian.2 a ha')
    have h2 : orderOf a ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H haH
    exact Nat.Coprime.eq_one_of_dvd (h.coprime.coprime_dvd_left h1) h2
  have : a = 1 := orderOf_eq_one_iff.mp hord
  simpa [this] using hd'

theorem HypA15.inf_sup_le (h : HypA15 p H A D D₁ D₂) : H ⊓ (D ⊔ A) ≤ D :=
  h.inf_sup_le_of_le h.D_le (admits_of_le_centralizer h.D_le_centralizer)

end Basic

theorem HypA5.mono {H H' A D D₂ : Subgroup G} (h : HypA5 H A D D₂) (hH : H' ≤ H) :
    HypA5 H' A D D₂ :=
  fun X₁ X₂ h₁ h₂ => h X₁ X₂ (h₁.trans hH) (h₂.trans hH)

theorem HypA6.mono {H H' A D D₁ D₂ : Subgroup G} (h : HypA6 H A D D₁ D₂) (hH : H' ≤ H) :
    HypA6 H' A D D₁ D₂ :=
  fun N L R hN hL hR => h N L R (hN.trans hH) (hL.trans hH) (hR.trans hH)

theorem HypA15.restrict [Finite G] {p : ℕ} {H H' A D D₁ D₂ : Subgroup G}
    (h : HypA15 p H A D D₁ D₂) (hH : H' ≤ H) (hD : D ≤ H') (hadm : Admits (D ⊔ A) H') :
    HypA15 p H' A D D₁ D₂ where
  prime := h.prime
  odd := h.odd
  a1_elemAbelian := h.a1_elemAbelian
  a1_admits := hadm.mono_left le_sup_right
  a1_near := nearASolvable_of_le h.prime h.a1_near hH (hadm.mono_left le_sup_right)
  a3 := le_antisymm (le_inf hD (h.a3.le.trans inf_le_right))
    ((inf_le_inf_right _ hH).trans h.a3.ge)
  a4_chief := h.a4_chief
  a4_unique := h.a4_unique
  a4c := h.a4c
  a5 := h.a5.mono hH

theorem HypA.restrict [Finite G] {p : ℕ} {H H' A D D₁ D₂ : Subgroup G}
    (h : HypA p H A D D₁ D₂) (hH : H' ≤ H) (hD : D ≤ H') (hadm : Admits (D ⊔ A) H') :
    HypA p H' A D D₁ D₂ :=
  { h.toHypA15.restrict hH hD hadm with a6 := h.a6.mono hH }

theorem HypA15.sup_inf_le [Finite G] {p : ℕ} {H A D D₁ D₂ M N : Subgroup G}
    (h : HypA15 p H A D D₁ D₂) (hMH : M ≤ H) (hNH : N ≤ H) (hMA : Admits A M) (hNA : Admits A N)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hM : M ⊓ D ≤ D₂) (hN : N ⊓ D ≤ D₂) :
    (M ⊔ N) ⊓ D ≤ D₂ := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := HypAAux.exists_mul_of_mem_sup_of_centralizer h.prime
    h.a1_elemAbelian (h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hMH)) hMA hNA hMN
    hx.1 (h.D_le_centralizer hx.2)
  exact mul_mem (hM (Subgroup.mem_inf.mpr ⟨ha.1, h.mem_D (hMH ha.1) ha.2⟩))
    (hN (Subgroup.mem_inf.mpr ⟨hb.1, h.mem_D (hNH hb.1) hb.2⟩))

theorem HypA5.qimg {H A D D₂ N : Subgroup G} (h : HypA5 H A D D₂) (hDH : D ≤ H)
    (hD₂D : D₂ ≤ D) (hNH : N ≤ H) (hN : Admits (H ⊔ A) N) (hND : N ⊓ D ≤ D₂) :
    HypA5 (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₂) := by
  intro X₁' X₂' hX₁ hX₂ hadm₁ hadm₂ hchief hns h₂
  have hHn : H ≤ AChief.nrm N := le_sup_left.trans hN
  have hAn : A ≤ AChief.nrm N := le_sup_right.trans hN
  have hDn : D ≤ AChief.nrm N := hDH.trans hHn
  have hD₂n : D₂ ≤ AChief.nrm N := hD₂D.trans hDn
  have hDAn : D ⊔ A ≤ AChief.nrm N := sup_le hDn hAn
  have hX₁H : SolQuot.qpre N X₁' ≤ H := HypAAux.qpre_le_of_le_qimg hHn hNH hX₁
  have hX₂H : SolQuot.qpre N X₂' ≤ H := HypAAux.qpre_le_of_le_qimg hHn hNH hX₂
  have hX₁n : SolQuot.qpre N X₁' ≤ AChief.nrm N := hX₁H.trans hHn
  have hX₂n : SolQuot.qpre N X₂' ≤ AChief.nrm N := hX₂H.trans hHn
  have hadm₁' : Admits (D ⊔ A) (SolQuot.qpre N X₁') :=
    HypAAux.admits_qpre hDAn (by rwa [SolQuot.qimg_sup hDn hAn])
  have hadm₂' : Admits (D ⊔ A) (SolQuot.qpre N X₂') :=
    HypAAux.admits_qpre hDAn (by rwa [SolQuot.qimg_sup hDn hAn])
  have hML : SolQuot.qpre N X₂' ≤ SolQuot.qpre N X₁' := SolQuot.qpre_mono hchief.2.2.1.le
  have hY : SolQuot.qpre N X₁' ⊔ D ⊔ A ≤ AChief.nrm N := sup_le (sup_le hX₁n hDn) hAn
  have hchief' : IsChiefFactorOf (SolQuot.qpre N X₁' ⊔ D ⊔ A) (SolQuot.qpre N X₁')
      (SolQuot.qpre N X₂') := by
    refine (HypAAux.isChiefFactorOf_qimg_iff (N := N) (le_sup_left.trans le_sup_left) hML hY
      (inf_le_right.trans (SolQuot.le_qpre X₂'))).mp ?_
    rw [SolQuot.qimg_sup (sup_le hX₁n hDn) hAn, SolQuot.qimg_sup hX₁n hDn, SolQuot.qimg_qpre,
      SolQuot.qimg_qpre]
    exact hchief
  have hns' : ¬ IsSolvableSection (SolQuot.qpre N X₁') (SolQuot.qpre N X₂') := fun hsol =>
    hns (by
      have := HypAAux.isSolvableSection_qimg hX₁n hML hsol
      rwa [SolQuot.qimg_qpre, SolQuot.qimg_qpre] at this)
  have hX₂D : SolQuot.qpre N X₂' ⊓ D ≤ D₂ := by
    rw [inf_comm]
    refine HypAAux.inf_le_of_qimg_inf_le hDn hD₂D (by rwa [inf_comm]) (SolQuot.le_qpre X₂') hX₂n ?_
    rw [SolQuot.qimg_qpre, inf_comm]
    exact h₂
  have key := h _ _ hX₁H hX₂H hadm₁' hadm₂' hchief' hns' hX₂D
  have hmem : AChief.qimg N (D ⊓ SolQuot.qpre N X₁') ≤ AChief.qimg N D₂ := SolQuot.qimg_mono
    (by rw [inf_comm]; exact key)
  rw [SolQuot.qimg_inf_of_le hX₁n (SolQuot.le_qpre X₁'), SolQuot.qimg_qpre, inf_comm] at hmem
  exact hmem

theorem HypA6.qimg_of_le [Finite G] {p : ℕ} {H H₀ A D D₁ D₂ N : Subgroup G}
    (h15 : HypA15 p H A D D₁ D₂) (hH₀ : H₀ ≤ H) (hDH₀ : D ≤ H₀) (hadm₀ : Admits (D ⊔ A) H₀)
    (h : HypA6 H₀ A D D₁ D₂) (hNH : N ≤ H) (hN : Admits (H ⊔ A) N) (hND : N ⊓ D ≤ D₂) :
    HypA6 (AChief.qimg N H₀) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₁)
      (AChief.qimg N D₂) := by
  have hHn : H ≤ AChief.nrm N := le_sup_left.trans hN
  have hAn : A ≤ AChief.nrm N := le_sup_right.trans hN
  have hH₀n : H₀ ≤ AChief.nrm N := hH₀.trans hHn
  have hDn : D ≤ AChief.nrm N := hDH₀.trans hH₀n
  have hD₂D : D₂ ≤ D := h15.D₂_le
  have hD₁D : D₁ ≤ D := h15.D₁_le
  have hD₁₂ : D₂ ≤ D₁ := h15.D₂_lt.le
  have hD₁n : D₁ ≤ AChief.nrm N := hD₁D.trans hDn
  have hD₂n : D₂ ≤ AChief.nrm N := hD₂D.trans hDn
  have hDAn : D ⊔ A ≤ AChief.nrm N := sup_le hDn hAn
  have hND' : D ⊓ N ≤ D₂ := by rwa [inf_comm]
  have hAH₀ : Admits A H₀ := hadm₀.mono_left le_sup_right
  have hqDA : AChief.qimg N (D ⊔ A) = AChief.qimg N D ⊔ AChief.qimg N A :=
    SolQuot.qimg_sup hDn hAn
  intro N' L' R' hN'H hL'H hR'H hN'adm hL'adm hR'adm hLR hchief hcen hRD hDN' hdir
  have hqN₁ : AChief.qimg N (H₀ ⊓ SolQuot.qpre N N') = N' := HypAAux.qimg_inf_qpre hN'H
  have hqL₁ : AChief.qimg N (H₀ ⊓ SolQuot.qpre N L') = L' := HypAAux.qimg_inf_qpre hL'H
  have hqR₁ : AChief.qimg N (H₀ ⊓ SolQuot.qpre N R') = R' := HypAAux.qimg_inf_qpre hR'H
  have hR₁n : H₀ ⊓ SolQuot.qpre N R' ≤ AChief.nrm N := inf_le_left.trans hH₀n
  have hLR' : H₀ ⊓ SolQuot.qpre N L' ≤ H₀ ⊓ SolQuot.qpre N R' :=
    inf_le_inf_left H₀ (SolQuot.qpre_mono hLR)
  have hY : (H₀ ⊓ SolQuot.qpre N R') ⊔ D ⊔ A ≤ AChief.nrm N := sup_le (sup_le hR₁n hDn) hAn
  have hqY : AChief.qimg N ((H₀ ⊓ SolQuot.qpre N R') ⊔ D ⊔ A) =
      R' ⊔ AChief.qimg N D ⊔ AChief.qimg N A := by
    rw [SolQuot.qimg_sup (sup_le hR₁n hDn) hAn, SolQuot.qimg_sup hR₁n hDn, hqR₁]
  have hYN : ((H₀ ⊓ SolQuot.qpre N R') ⊔ D ⊔ A) ⊓ N ≤ H₀ ⊓ SolQuot.qpre N N' := fun x hx =>
    Subgroup.mem_inf.mpr
      ⟨h15.inf_sup_le_of_le hH₀ hAH₀ (Subgroup.mem_inf.mpr ⟨hNH hx.2,
        (sup_le (sup_le (inf_le_left.trans le_sup_left) (hDH₀.trans le_sup_left)) le_sup_right)
          hx.1⟩), SolQuot.le_qpre N' hx.2⟩
  have hchief' : IsChiefFactorOf ((H₀ ⊓ SolQuot.qpre N R') ⊔ D ⊔ A) (H₀ ⊓ SolQuot.qpre N L')
      (H₀ ⊓ SolQuot.qpre N N') := by
    refine (HypAAux.isChiefFactorOf_qimg_iff (N := N)
      (hLR'.trans (le_sup_left.trans le_sup_left))
      (inf_le_inf_left H₀ (SolQuot.qpre_mono hchief.2.2.1.le)) hY hYN).mp ?_
    rw [hqY, hqL₁, hqN₁]
    exact hchief
  have hcen' : A ⊔ (H₀ ⊓ SolQuot.qpre N R') ≤ secCenIn ((H₀ ⊓ SolQuot.qpre N R') ⊔ D ⊔ A)
      (H₀ ⊓ SolQuot.qpre N L') (H₀ ⊓ SolQuot.qpre N N') := by
    refine le_inf (sup_le le_sup_right (le_sup_left.trans le_sup_left)) ?_
    refine HypAAux.le_sectionCentralizer_inf_qpre (sup_le hAn hR₁n)
      (sup_le hAH₀ (inf_le_left.trans Subgroup.le_normalizer)) ?_
    rw [SolQuot.qimg_sup hAn hR₁n, hqR₁]
    exact hcen.trans inf_le_right
  have hRD' : (H₀ ⊓ SolQuot.qpre N R') ⊓ D = D₁ := by
    have hqD : D ⊓ SolQuot.qpre N R' ≤ D₁ := by
      refine HypAAux.inf_le_of_qimg_inf_le hDn hD₁D (hND'.trans hD₁₂) (SolQuot.le_qpre R')
        (SolQuot.qpre_le_nrm R') ?_
      rw [SolQuot.qimg_qpre, inf_comm, hRD]
    refine le_antisymm (fun x hx => hqD (Subgroup.mem_inf.mpr
      ⟨hx.2, (Subgroup.mem_inf.mp hx.1).2⟩)) (le_inf (le_inf (hD₁D.trans hDH₀) ?_) hD₁D)
    refine (SolQuot.qimg_le_iff hD₁n).mp ?_
    rw [← hRD]
    exact inf_le_left
  have hDN₁ : D ⊓ (H₀ ⊓ SolQuot.qpre N N') ≤ D₂ := by
    have hq : D ⊓ SolQuot.qpre N N' ≤ D₂ := by
      refine HypAAux.inf_le_of_qimg_inf_le hDn hD₂D hND' (SolQuot.le_qpre N')
        (SolQuot.qpre_le_nrm N') ?_
      rw [SolQuot.qimg_qpre]
      exact hDN'
    exact fun x hx => hq (Subgroup.mem_inf.mpr ⟨hx.1, (Subgroup.mem_inf.mp hx.2).2⟩)
  have hdir' := HypAAux.isDirectProductMod_inf_qpre hH₀n (hD₁D.trans hDH₀) (hD₂D.trans hDH₀)
    hN'H hL'H hdir
  obtain ⟨B, hBR, hBadm, hBD, hRB⟩ := h _ _ _ inf_le_left inf_le_left inf_le_left
    (hadm₀.inf (HypAAux.admits_qpre hDAn (by rwa [hqDA])))
    (hadm₀.inf (HypAAux.admits_qpre hDAn (by rwa [hqDA])))
    (hadm₀.inf (HypAAux.admits_qpre hDAn (by rwa [hqDA]))) hLR' hchief' hcen' hRD' hDN₁ hdir'
  have hBH₀ : B ≤ H₀ := hBR.trans inf_le_left
  have hBn : B ≤ AChief.nrm N := hBH₀.trans hH₀n
  have hBND : (B ⊔ N) ⊓ D ≤ D₂ :=
    h15.sup_inf_le (hBH₀.trans hH₀) hNH (le_sup_right.trans hBadm) hAn hBn hBD.le hND
  have hD₂B : D₂ ≤ B := by
    rw [← hBD]
    exact inf_le_left
  have hBNeq : (B ⊔ N) ⊓ D = D₂ := le_antisymm hBND (le_inf (hD₂B.trans le_sup_left) hD₂D)
  have hqB : AChief.qimg N (B ⊔ N) = AChief.qimg N B := by
    rw [SolQuot.qimg_sup hBn Subgroup.le_normalizer, SolQuot.qimg_self, sup_bot_eq]
  refine ⟨AChief.qimg N B, ?_, ?_, ?_, ?_⟩
  · have := SolQuot.qimg_mono (R := N) hBR
    rwa [hqR₁] at this
  · have := HypAAux.admits_qimg (N := N) hBadm
    rwa [hqY] at this
  · have h1 : AChief.qimg N (D ⊓ (B ⊔ N)) = AChief.qimg N D ⊓ AChief.qimg N (B ⊔ N) :=
      SolQuot.qimg_inf_of_le (sup_le hBn Subgroup.le_normalizer) le_sup_right
    rw [inf_comm D (B ⊔ N), hBNeq, hqB] at h1
    rw [inf_comm]
    exact h1.symm
  · have h1 : AChief.qimg N (B ⊔ D₁) = AChief.qimg N B ⊔ AChief.qimg N D₁ :=
      SolQuot.qimg_sup hBn hD₁n
    rw [← h1, ← hRB, hqR₁]

theorem HypA6.qimg [Finite G] {p : ℕ} {H A D D₁ D₂ N : Subgroup G}
    (h15 : HypA15 p H A D D₁ D₂) (h : HypA6 H A D D₁ D₂) (hNH : N ≤ H)
    (hN : Admits (H ⊔ A) N) (hND : N ⊓ D ≤ D₂) :
    HypA6 (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₁)
      (AChief.qimg N D₂) :=
  HypA6.qimg_of_le h15 le_rfl h15.D_le
    (sup_le (h15.D_le.trans Subgroup.le_normalizer) h15.a1_admits) h hNH hN hND

theorem HypA15.qimg [Finite G] {p : ℕ} {H A D D₁ D₂ N : Subgroup G}
    (h : HypA15 p H A D D₁ D₂) (hNH : N ≤ H) (hN : Admits (H ⊔ A) N) (hND : N ⊓ D ≤ D₂) :
    HypA15 p (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₁)
      (AChief.qimg N D₂) := by
  have hHn : H ≤ AChief.nrm N := le_sup_left.trans hN
  have hAn : A ≤ AChief.nrm N := le_sup_right.trans hN
  have hDH : D ≤ H := h.D_le
  have hD₂D : D₂ ≤ D := h.D₂_le
  have hD₁D : D₁ ≤ D := h.D₁_le
  have hDD₂ : D ≤ Subgroup.normalizer (D₂ : Set G) := h.a4_chief.1.2
  have hDD₁ : D ≤ Subgroup.normalizer (D₁ : Set G) := h.a4_chief.2.1.2
  have hD₁₂ : D₂ ≤ D₁ := h.D₂_lt.le
  have hDn : D ≤ AChief.nrm N := hDH.trans hHn
  have hcop : Nat.Coprime p (Nat.card H) := h.coprime
  have hND' : D ⊓ N ≤ D₂ := by rwa [inf_comm]
  refine
    { prime := h.prime
      odd := h.odd
      a1_elemAbelian := AChief.isElemAbelian_qimg h.a1_elemAbelian
      a1_admits := AChief.qimg_le_normalizer h.a1_admits
      a1_near := HypAAux.nearASolvable_qimg h.prime h.a1_elemAbelian h.a1_admits hHn hAn
        h.a1_near
      a3 := ?_
      a4_chief := ?_
      a4_unique := ?_
      a4c := ?_
      a5 := h.a5.qimg hDH hD₂D hNH hN hND }
  · rw [← AChief.qimg_inf_centralizer h.prime h.a1_elemAbelian h.a1_admits hAn hHn hcop, ← h.a3]
  · exact (HypAAux.isChiefFactorOf_qimg_iff hD₁D hD₁₂ hDn hND').mpr h.a4_chief
  · intro M' hM'
    have hqM : AChief.qimg N (D ⊓ SolQuot.qpre N M') = M' := by
      rw [SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm M') (SolQuot.le_qpre M'),
        SolQuot.qimg_qpre]
      exact inf_eq_right.mpr hM'.2.1.1
    have hD₂M : D₂ ≤ D ⊓ SolQuot.qpre N M' :=
      le_inf hD₂D ((SolQuot.qimg_le_iff (hD₂D.trans hDn)).mp hM'.2.2.1.le)
    have hchief : IsChiefFactorOf D (D ⊓ SolQuot.qpre N M') D₂ := by
      refine (HypAAux.isChiefFactorOf_qimg_iff inf_le_left hD₂M hDn hND').mp ?_
      rw [hqM]
      exact hM'
    rw [← hqM, h.a4_unique _ hchief]
  · exact HypAAux.secCenIn_qimg_eq hDn hD₁₂ hD₁D hDD₂ hDD₁ hND h.a4c

theorem HypA.qimg [Finite G] {p : ℕ} {H A D D₁ D₂ N : Subgroup G}
    (h : HypA p H A D D₁ D₂) (hNH : N ≤ H) (hN : Admits (H ⊔ A) N) (hND : N ⊓ D ≤ D₂) :
    HypA p (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₁)
      (AChief.qimg N D₂) :=
  { h.toHypA15.qimg hNH hN hND with a6 := h.a6.qimg h.toHypA15 hNH hN hND }

theorem exists_max_ssSet_of_qimg [Finite G] {p : ℕ} {H A D D₁ D₂ N : Subgroup G}
    (h : HypA15 p H A D D₁ D₂) (hNH : N ≤ H) (hN : Admits (H ⊔ A) N) (hND : N ⊓ D ≤ D₂)
    (hmax : ∃ M₀ ∈ ssSet (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D)
        (AChief.qimg N D₂),
      ∀ M ∈ ssSet (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₂),
        M ≤ M₀) :
    ∃ M₀ ∈ ssSet H A D D₂, ∀ M ∈ ssSet H A D D₂, M ≤ M₀ := by
  obtain ⟨M', ⟨hM'H, hM'adm, hM'D⟩, hM'max⟩ := hmax
  have hHn : H ≤ AChief.nrm N := le_sup_left.trans hN
  have hAn : A ≤ AChief.nrm N := le_sup_right.trans hN
  have hDH : D ≤ H := h.a3.le.trans inf_le_left
  have hD₂D : D₂ ≤ D := h.a4_chief.1.1
  have hDn : D ≤ AChief.nrm N := hDH.trans hHn
  have hDAn : D ⊔ A ≤ AChief.nrm N := sup_le hDn hAn
  have hqDA : AChief.qimg N (D ⊔ A) = AChief.qimg N D ⊔ AChief.qimg N A :=
    SolQuot.qimg_sup hDn hAn
  have hND' : D ⊓ N ≤ D₂ := by rwa [inf_comm]
  refine ⟨SolQuot.qpre N M', ⟨?_, ?_, ?_⟩, fun M hM => ?_⟩
  · exact HypAAux.qpre_le_of_le_qimg hHn hNH hM'H
  · exact HypAAux.admits_qpre hDAn (by rwa [hqDA])
  · refine le_antisymm ?_ (le_inf ((SolQuot.qimg_le_iff (hD₂D.trans hDn)).mp ?_) hD₂D)
    · rw [inf_comm]
      refine HypAAux.inf_le_of_qimg_inf_le hDn hD₂D hND' (SolQuot.le_qpre M')
        (SolQuot.qpre_le_nrm M') ?_
      rw [SolQuot.qimg_qpre, inf_comm, hM'D]
    · rw [← hM'D]
      exact inf_le_left
  · obtain ⟨hMH, hMadm, hMD⟩ := hM
    have hMn : M ≤ AChief.nrm N := hMH.trans hHn
    have hMN : M ⊔ N ≤ AChief.nrm N := sup_le hMn Subgroup.le_normalizer
    have hD₂M : D₂ ≤ M := by
      rw [← hMD]
      exact inf_le_left
    have hglue : (M ⊔ N) ⊓ D ≤ D₂ := h.sup_inf_le hMH hNH (hMadm.mono_left le_sup_right)
      (hN.mono_left le_sup_right) hMn hMD.le hND
    have hM'' : AChief.qimg N M ⊓ AChief.qimg N D = AChief.qimg N D₂ := by
      refine le_antisymm ?_ (le_inf (SolQuot.qimg_mono hD₂M) (SolQuot.qimg_mono hD₂D))
      have h1 : AChief.qimg N (D ⊓ (M ⊔ N)) = AChief.qimg N D ⊓ AChief.qimg N (M ⊔ N) :=
        SolQuot.qimg_inf_of_le hMN le_sup_right
      have h2 : AChief.qimg N (M ⊔ N) = AChief.qimg N M := by
        rw [SolQuot.qimg_sup hMn Subgroup.le_normalizer, SolQuot.qimg_self, sup_bot_eq]
      rw [h2] at h1
      rw [inf_comm, ← h1]
      exact SolQuot.qimg_mono (by rw [inf_comm]; exact hglue)
    refine (SolQuot.qimg_le_iff hMn).mp (hM'max _ ⟨SolQuot.qimg_mono hMH, ?_, hM''⟩)
    rw [← hqDA]
    exact HypAAux.admits_qimg hMadm

theorem HypA15.D₁_le_sup [Finite G] {p : ℕ} {H A D D₁ D₂ N : Subgroup G}
    (h : HypA15 p H A D D₁ D₂) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hND : ¬ N ⊓ D ≤ D₂) : D₁ ≤ D₂ ⊔ (D₁ ⊓ N) := by
  set K : Subgroup G := D₂ ⊔ (D ⊓ N) with hK
  have hDN' : Admits D (D ⊓ N) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hDN hg⟩
  have hKD : K ≤ D := sup_le h.D₂_le inf_le_left
  have hDK : Admits D K := Admits.sup (show Admits D D₂ from h.a4_chief.1.2) hDN'
  have hlt : D₂ < K := by
    refine lt_of_le_of_ne le_sup_left fun heq => hND ?_
    rw [inf_comm]
    exact (le_sup_right.trans heq.symm.le)
  obtain ⟨M₁, ⟨hM₁1, hM₁2, hM₁3, hM₁4⟩, hmin⟩ := (Set.toFinite {M : Subgroup G | D₂ ≤ M ∧
    M ≤ K ∧ Admits D M ∧ M ≠ D₂}).exists_minimal ⟨K, le_sup_left, le_rfl, hDK, hlt.ne'⟩
  have hchief : IsChiefFactorOf D M₁ D₂ := by
    refine ⟨h.a4_chief.1, ⟨hM₁2.trans hKD, hM₁3⟩, lt_of_le_of_ne hM₁1 hM₁4.symm,
      fun K' hK' hK'1 hK'2 => ?_⟩
    by_cases hK'D₂ : K' = D₂
    · exact Or.inl hK'D₂
    · exact Or.inr (le_antisymm hK'2 (hmin ⟨hK'1, hK'2.trans hM₁2, hK'.2, hK'D₂⟩ hK'2))
  have hM₁eq : M₁ = D₁ := h.a4_unique M₁ hchief
  have hD₁K : D₁ ≤ K := hM₁eq ▸ hM₁2
  have hded := HypAAux.inf_sup_le_sup_inf (S := D₂) (U := D₁) (X := D ⊓ N) h.D₂_lt.le
    (h.D₂_le.trans hDN')
  exact (le_inf le_rfl hD₁K).trans
    (hded.trans (sup_le_sup_left (inf_le_inf_left D₁ inf_le_right) D₂))

structure MinCex (p : ℕ) (H A D D₁ D₂ : Subgroup G) : Prop where
  hyp : HypA p H A D D₁ D₂
  no_max : ¬ ∃ M₀ ∈ ssSet H A D D₂, ∀ M ∈ ssSet H A D D₂, M ≤ M₀
  restrict : ∀ H' : Subgroup G, H' ≤ H → D ≤ H' → Admits (D ⊔ A) H' → H' ⊔ A ≠ H ⊔ A →
    ∃ M₀ ∈ ssSet H' A D D₂, ∀ M ∈ ssSet H' A D D₂, M ≤ M₀
  quot : ∀ N : Subgroup G, N ≤ H → Admits (H ⊔ A) N → N ≠ ⊥ → N ⊓ D ≤ D₂ →
    ∃ M₀ ∈ ssSet (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₂),
      ∀ M ∈ ssSet (AChief.qimg N H) (AChief.qimg N A) (AChief.qimg N D) (AChief.qimg N D₂),
        M ≤ M₀

structure MinCex.NData (H A D D₂ N : Subgroup G) : Prop where
  le : N ≤ H
  admits : Admits (H ⊔ A) N
  ne_bot : N ≠ ⊥
  min : ∀ M : Subgroup G, M ≤ N → Admits (H ⊔ A) M → M = ⊥ ∨ M = N
  comm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x
  not_inf_le : ¬ N ⊓ D ≤ D₂

theorem admits_sSup_ssSet (H A D D₂ : Subgroup G) :
    Admits (D ⊔ A) (sSup (ssSet H A D D₂)) := by
  rw [sSup_eq_iSup]
  exact Admits.iSup fun M => Admits.iSup fun hM => hM.2.1

theorem sSup_ssSet_le (H A D D₂ : Subgroup G) : sSup (ssSet H A D D₂) ≤ H :=
  sSup_le fun _ hM => hM.1

theorem mul_comm_of_mem_bot {x y : G} (h : x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G)) :
    x * y = y * x :=
  (commutatorElement_eq_one_iff_mul_comm (g₁ := x) (g₂ := y)).mp (Subgroup.mem_bot.mp h)

namespace MinCex

variable {p : ℕ} {H A D D₁ D₂ : Subgroup G}

theorem not_forall_le_D (c : MinCex p H A D D₁ D₂) (hle : ∀ M ∈ ssSet H A D D₂, M ≤ D) :
    False :=
  c.no_max ⟨D₂, c.hyp.D₂_mem, fun M hM =>
    ((inf_eq_left.mpr (hle M hM)).symm.trans hM.2.2).le⟩

theorem sup_eq (c : MinCex p H A D D₁ D₂) : sSup (ssSet H A D D₂) ⊔ D ⊔ A = H ⊔ A := by
  by_contra hne
  have hSH := sSup_ssSet_le H A D D₂
  obtain ⟨M₀, hM₀, hmax⟩ := c.restrict (sSup (ssSet H A D D₂) ⊔ D) (sup_le hSH c.hyp.D_le)
    le_sup_right ((admits_sSup_ssSet H A D D₂).sup c.hyp.admits_D) hne
  exact c.no_max ⟨M₀, ⟨hM₀.1.trans (sup_le hSH c.hyp.D_le), hM₀.2.1, hM₀.2.2⟩, fun M hM =>
    hmax M ⟨(le_sSup hM).trans le_sup_left, hM.2.1, hM.2.2⟩⟩

theorem sSup_ne_bot (c : MinCex p H A D D₁ D₂) : sSup (ssSet H A D D₂) ≠ ⊥ := fun h0 =>
  c.not_forall_le_D fun _ hM => (le_sSup hM).trans (h0.le.trans bot_le)

theorem not_inf_le [Finite G] (c : MinCex p H A D D₁ D₂) {K : Subgroup G} (hKH : K ≤ H)
    (hK : Admits (H ⊔ A) K) (hK0 : K ≠ ⊥) : ¬ K ⊓ D ≤ D₂ := fun hKD =>
  c.no_max (exists_max_ssSet_of_qimg c.hyp.toHypA15 hKH hK hKD (c.quot K hKH hK hK0 hKD))

theorem step37 [Finite G] (c : MinCex p H A D D₁ D₂) {N : Subgroup G} (hN : NData H A D D₂ N)
    {M : Subgroup G} (hM : M ∈ ssSet H A D D₂) : N ⊔ M ⊔ D ⊔ A ≠ H ⊔ A := by
  intro heq
  have h := c.hyp
  obtain ⟨hMH, hMadm, hMD⟩ := hM
  have hDG : D ≤ H ⊔ A := h.D_le.trans le_sup_left
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := (hMH.trans le_sup_left).trans hN.admits
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := hDG.trans hN.admits
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := le_sup_right.trans hN.admits
  have hgen : ∀ X : Subgroup G, N ≤ Subgroup.normalizer (X : Set G) →
      M ≤ Subgroup.normalizer (X : Set G) → D ≤ Subgroup.normalizer (X : Set G) →
      A ≤ Subgroup.normalizer (X : Set G) → Admits (H ⊔ A) X := fun X h1 h2 h3 h4 => by
    rw [← heq]
    exact sup_le (sup_le (sup_le h1 h2) h3) h4
  have hNcen : ∀ X : Subgroup G, N ≤ Subgroup.normalizer ((X ⊓ N : Subgroup G) : Set G) :=
    fun X n hn => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => hN.comm y (Subgroup.mem_inf.mp hy).2 n hn)
  have hD₁N : D₁ ⊓ N ≠ ⊥ := by
    intro h0
    have h36 := h.D₁_le_sup hDN hN.not_inf_le
    rw [h0, sup_bot_eq] at h36
    exact lt_irrefl _ (lt_of_lt_of_le h.D₂_lt h36)
  have hMMN : M ⊓ N = ⊥ := by
    have hadm : Admits (H ⊔ A) (M ⊓ N) := hgen _ (hNcen M)
      (fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hm, hMN hm⟩)
      (fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMadm (Subgroup.mem_sup_left hd), hDN hd⟩)
      (fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMadm (Subgroup.mem_sup_right ha), hAN ha⟩)
    rcases hN.min _ inf_le_right hadm with h0 | hNN
    · exact h0
    · exfalso
      have hNM : N ≤ M := inf_eq_right.mp hNN
      refine hN.not_inf_le fun x hx => ?_
      rw [← hMD]
      exact Subgroup.mem_inf.mpr ⟨hNM hx.1, hx.2⟩
  have hND₁ : N ≤ M ⊔ D₁ := by
    have hMD₁ : Admits (D ⊔ A) (M ⊔ D₁) := hMadm.sup h.admits_D₁
    have hadm : Admits (H ⊔ A) ((M ⊔ D₁) ⊓ N) := hgen _ (hNcen (M ⊔ D₁))
      (fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (Subgroup.mem_sup_left hm), hMN hm⟩)
      (fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMD₁ (Subgroup.mem_sup_left hd), hDN hd⟩)
      (fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMD₁ (Subgroup.mem_sup_right ha), hAN ha⟩)
    rcases hN.min _ inf_le_right hadm with h0 | hNN
    · exact absurd (le_bot_iff.mp ((inf_le_inf_right N le_sup_right).trans h0.le)) hD₁N
    · exact inf_eq_right.mp hNN
  have hHA : H ⊔ A ≤ M ⊔ D ⊔ A := by
    rw [← heq]
    exact sup_le (sup_le (sup_le ((hND₁.trans (sup_le_sup_left h.D₁_le M)).trans le_sup_left)
      (le_sup_left.trans le_sup_left)) (le_sup_right.trans le_sup_left)) le_sup_right
  have hMG : Admits (H ⊔ A) M := hHA.trans (sup_le (sup_le Subgroup.le_normalizer
    (le_sup_left.trans hMadm)) (le_sup_right.trans hMadm))
  have hM0 : M = ⊥ := by
    by_contra hM0
    exact c.not_inf_le hMH hMG hM0 hMD.le
  rw [hM0, bot_sup_eq] at hHA
  have hHD : H ≤ D := fun x hx =>
    h.inf_sup_le (Subgroup.mem_inf.mpr ⟨hx, hHA (Subgroup.mem_sup_left hx)⟩)
  exact c.not_forall_le_D fun M' hM' => hM'.1.trans hHD

theorem step39 [Finite G] (c : MinCex p H A D D₁ D₂) {N : Subgroup G} (hN : NData H A D D₂ N) :
    ∀ M ∈ ssSet H A D D₂, M ⊓ N = ⊥ := by
  have h := c.hyp
  have hDG : D ≤ H ⊔ A := h.D_le.trans le_sup_left
  have hMN : ∀ M ∈ ssSet H A D D₂, M ≤ Subgroup.normalizer (N : Set G) := fun M hM =>
    (hM.1.trans le_sup_left).trans hN.admits
  have hNDA : Admits (D ⊔ A) N := (sup_le hDG le_sup_right).trans hN.admits
  have key : ∀ M ∈ ssSet H A D D₂, ∃ Ms ∈ ssSet (N ⊔ M ⊔ D) A D D₂,
      ∀ X ∈ ssSet (N ⊔ M ⊔ D) A D D₂, X ≤ Ms := fun M hM =>
    c.restrict (N ⊔ M ⊔ D) (sup_le (sup_le hN.le hM.1) h.D_le) le_sup_right
      ((hNDA.sup hM.2.1).sup h.admits_D) (c.step37 hN hM)
  choose! star hmem hmax using key
  have hD₂M : ∀ M ∈ ssSet H A D D₂, D₂ ≤ M := fun M hM => by
    rw [← hM.2.2]
    exact inf_le_left
  have hMstar : ∀ M ∈ ssSet H A D D₂, M ≤ star M := fun M hM =>
    hmax M hM M ⟨le_sup_right.trans le_sup_left, hM.2.1, hM.2.2⟩
  have hD₂star : ∀ M ∈ ssSet H A D D₂, D₂ ≤ star M := fun M hM => by
    rw [← (hmem M hM).2.2]
    exact inf_le_left
  have hsD := hmem D₂ h.D₂_mem
  have h38 : ∀ M ∈ ssSet H A D D₂, star M ⊓ N = star D₂ ⊓ N := by
    intro M hM
    have hsM := hmem M hM
    refine le_antisymm ?_ (inf_le_inf_right N ?_)
    · have hX : (star M ⊓ N) ⊔ D₂ ∈ ssSet (N ⊔ D₂ ⊔ D) A D D₂ := by
        refine ⟨sup_le (inf_le_right.trans (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left), (hsM.2.1.inf hNDA).sup h.admits_D₂, ?_⟩
        refine le_antisymm ?_ (le_inf le_sup_right h.D₂_le)
        calc ((star M ⊓ N) ⊔ D₂) ⊓ D ≤ star M ⊓ D :=
              inf_le_inf_right D (sup_le inf_le_left (hD₂star M hM))
          _ = D₂ := hsM.2.2
      exact le_inf (le_sup_left.trans (hmax D₂ h.D₂_mem _ hX)) inf_le_right
    · exact hmax M hM _ ⟨hsD.1.trans (sup_le_sup_right (sup_le_sup_left (hD₂M M hM) N) D),
        hsD.2.1, hsD.2.2⟩
  have hW₀adm : Admits (H ⊔ A) (star D₂ ⊓ N) := by
    rw [← c.sup_eq]
    refine sup_le (sup_le (sSup_le fun M hM => ?_) ?_) ?_
    · rw [← h38 M hM]
      exact fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (hMstar M hM hm), hMN M hM hm⟩
    · exact fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hsD.2.1 (Subgroup.mem_sup_left hd), hNDA (Subgroup.mem_sup_left hd)⟩
    · exact fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hsD.2.1 (Subgroup.mem_sup_right ha), hNDA (Subgroup.mem_sup_right ha)⟩
  have hW₀bot : star D₂ ⊓ N = ⊥ := by
    rcases hN.min _ inf_le_right hW₀adm with h0 | h0
    · exact h0
    · exfalso
      have hNs : N ≤ star D₂ := inf_eq_right.mp h0
      refine hN.not_inf_le fun x hx => ?_
      rw [← hsD.2.2]
      exact Subgroup.mem_inf.mpr ⟨hNs hx.1, hx.2⟩
  exact fun M hM => le_bot_iff.mp (((inf_le_inf_right N (hMstar M hM)).trans (h38 M hM).le).trans
    hW₀bot.le)

theorem final [Finite G] (c : MinCex p H A D D₁ D₂) {N : Subgroup G} (hN : NData H A D D₂ N)
    (h39 : ∀ M ∈ ssSet H A D D₂, M ⊓ N = ⊥) : False := by
  have h := c.hyp
  have hDG : D ≤ H ⊔ A := h.D_le.trans le_sup_left
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := hDG.trans hN.admits
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := le_sup_right.trans hN.admits
  have hNDA : Admits (D ⊔ A) N := (sup_le hDG le_sup_right).trans hN.admits
  have hbot : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  have h36 := h.D₁_le_sup hDN hN.not_inf_le
  have hD₁N : D₁ ⊓ N ≠ ⊥ := by
    intro h0
    rw [h0, sup_bot_eq] at h36
    exact lt_irrefl _ (lt_of_lt_of_le h.D₂_lt h36)
  have hS : sSup (ssSet H A D D₂) ≤ Subgroup.centralizer ((D ⊓ N : Subgroup G) : Set G) := by
    refine sSup_le fun M hM x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨hyD, hyN⟩ := Subgroup.mem_inf.mp hy
    have hxN : x ∈ Subgroup.normalizer (N : Set G) := (hM.1.trans le_sup_left |>.trans hN.admits) hx
    have hyM : y ∈ Subgroup.normalizer (M : Set G) := hM.2.1 (Subgroup.mem_sup_left hyD)
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ M ⊓ N := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := mul_mem hx ((Subgroup.mem_normalizer_iff.mp hyM x⁻¹).mp (inv_mem hx))
        simpa [mul_assoc] using this
      · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hyN) (inv_mem hyN)
    rw [h39 M hM] at h1
    exact (mul_comm_of_mem_bot h1).symm
  have hND₁ : N ≤ D₁ := by
    have hadm : Admits (H ⊔ A) (D₁ ⊓ N) := by
      rw [← c.sup_eq]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (hS.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
          (inf_le_inf_right N h.D₁_le)))).trans (Subgroup.centralizer_le_normalizer _)
      · exact fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨h.a4_chief.2.1.2 hd, hDN hd⟩
      · exact admits_of_le_centralizer (inf_le_left.trans (h.D₁_le.trans h.D_le_centralizer))
    rcases hN.min _ inf_le_right hadm with h0 | h0
    · exact absurd h0 hD₁N
    · exact inf_eq_right.mp h0
  have hNle : N ≤ D := hND₁.trans h.D₁_le
  have hSN : sSup (ssSet H A D D₂) ≤ Subgroup.centralizer (N : Set G) := by
    have := hS
    rwa [inf_eq_right.mpr hNle] at this
  have hNiD₂ : N ⊓ D₂ = ⊥ := by
    have hadm : Admits (H ⊔ A) (N ⊓ D₂) := by
      rw [← c.sup_eq]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (hSN.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
          inf_le_left))).trans (Subgroup.centralizer_le_normalizer _)
      · exact fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hDN hd, h.a4_chief.1.2 hd⟩
      · exact admits_of_le_centralizer (inf_le_left.trans (hNle.trans h.D_le_centralizer))
    rcases hN.min _ inf_le_left hadm with h0 | h0
    · exact h0
    · exact absurd (inf_le_left.trans (inf_eq_left.mp h0)) hN.not_inf_le
  have hD₁eq : D₁ = D₂ ⊔ N :=
    le_antisymm (h36.trans (sup_le_sup_left inf_le_right D₂)) (sup_le h.D₂_lt.le hND₁)
  have hD₂N : ∀ d ∈ D₂, ∀ n ∈ N, d * n = n * d := by
    intro d hd n hn
    have h1 : d * n * d⁻¹ * n⁻¹ ∈ D₂ ⊓ N := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := mul_mem hd ((Subgroup.mem_normalizer_iff.mp (h.a4_chief.1.2 (hNle hn)) d⁻¹).mp
          (inv_mem hd))
        simpa [mul_assoc] using this
      · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hDN (h.D₂_le hd)) n).mp hn) (inv_mem hn)
    rw [inf_comm, hNiD₂] at h1
    exact mul_comm_of_mem_bot h1
  set R : Subgroup G := H ⊓ Subgroup.centralizer (N : Set G) with hR
  have hSR : sSup (ssSet H A D D₂) ≤ R := le_inf (sSup_ssSet_le H A D D₂) hSN
  have hRH : R ≤ H := inf_le_left
  have hRG : R ⊔ D ⊔ A = H ⊔ A := by
    refine le_antisymm (sup_le (sup_le (hRH.trans le_sup_left) hDG) le_sup_right) ?_
    rw [← c.sup_eq]
    exact sup_le_sup_right (sup_le_sup_right hSR D) A
  have hRD : R ⊓ D = D₁ := by
    refine le_antisymm ?_ (le_inf (le_inf (h.D₁_le.trans h.D_le) ?_) h.D₁_le)
    · intro g hg
      obtain ⟨hgR, hgD⟩ := Subgroup.mem_inf.mp hg
      have hgC : g ∈ Subgroup.centralizer (N : Set G) := (Subgroup.mem_inf.mp hgR).2
      have hmem : g ∈ secCenIn D D₁ D₂ := by
        refine Subgroup.mem_inf.mpr ⟨hgD, McBride.mem_sectionCentralizer_iff.mpr
          ⟨h.a4_chief.1.2 hgD, h.a4_chief.2.1.2 hgD, fun y hy => ?_⟩⟩
        rw [hD₁eq] at hy
        have hmul := Subgroup.coe_mul_of_left_le_normalizer_right D₂ N (h.D₂_le.trans hDN)
        have hy' : y ∈ (D₂ : Set G) * (N : Set G) := by
          rw [← hmul]
          exact hy
        obtain ⟨d, hd, n, hn, rfl⟩ := hy'
        have hd' : d ∈ D₂ := hd
        have hn' : n ∈ N := hn
        have hgn : g * n * g⁻¹ = n := by
          have := Subgroup.mem_centralizer_iff.mp hgC n hn'
          rw [← this]
          group
        have h1 : g * d * g⁻¹ ∈ D₂ := (Subgroup.mem_normalizer_iff.mp (h.a4_chief.1.2 hgD) d).mp hd'
        have h2 : g * (d * n) * g⁻¹ * (d * n)⁻¹ = (g * d * g⁻¹) * d⁻¹ := by
          calc g * (d * n) * g⁻¹ * (d * n)⁻¹
              = (g * d * g⁻¹) * (g * n * g⁻¹) * n⁻¹ * d⁻¹ := by group
            _ = (g * d * g⁻¹) * n * n⁻¹ * d⁻¹ := by rw [hgn]
            _ = (g * d * g⁻¹) * d⁻¹ := by group
        rw [commutatorElement_def, h2]
        exact mul_mem h1 (inv_mem hd')
      rw [h.a4c] at hmem
      exact hmem
    · rw [hD₁eq]
      refine sup_le (fun d hd => ?_) (fun n hn => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hD₂N d hd y hy).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun y hy => hN.comm y hy n hn
  have hNR : N ≤ R := le_inf hN.le (fun n hn => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    hN.comm y hy n hn)
  have hHadm : Admits (D ⊔ A) H := sup_le (h.D_le.trans Subgroup.le_normalizer) h.a1_admits
  have hRadm : Admits (D ⊔ A) R := fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hHadm hg, (hNDA.trans (HypAAux.normalizer_le_normalizer_centralizer N)) hg⟩
  have hchief : IsChiefFactorOf (R ⊔ D ⊔ A) N ⊥ := by
    rw [hRG]
    exact ⟨⟨bot_le, fun g _ => hbot g⟩, ⟨hN.le.trans le_sup_left, hN.admits⟩,
      bot_lt_iff_ne_bot.mpr hN.ne_bot, fun K hK _ hKN => hN.min K hKN hK.2⟩
  have hcen : A ⊔ R ≤ secCenIn (R ⊔ D ⊔ A) N ⊥ := by
    refine le_inf (sup_le le_sup_right (le_sup_left.trans le_sup_left)) (sup_le ?_ ?_)
    · intro a ha
      refine McBride.mem_sectionCentralizer_iff.mpr ⟨hbot a, hAN ha, fun y hy => ?_⟩
      have hyC : y ∈ Subgroup.centralizer (A : Set G) := h.D_le_centralizer (hNle hy)
      exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hyC a ha))
    · intro g hg
      refine McBride.mem_sectionCentralizer_iff.mpr ⟨hbot g, hN.admits (Subgroup.mem_sup_left hg.1),
        fun y hy => ?_⟩
      exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hg.2 y hy).symm)
  have hdir : IsDirectProductMod ⊥ (D₁ ⊔ ⊥) (D₂ ⊔ ⊥) N := by
    refine ⟨bot_le, bot_le, ?_, ?_, ?_⟩
    · rw [sup_bot_eq, sup_bot_eq]
      exact hD₁eq.symm
    · rw [sup_bot_eq, inf_comm]
      exact hNiD₂
    · rw [sup_bot_eq]
      exact Subgroup.commutator_le.mpr fun d hd n hn => Subgroup.mem_bot.mpr
        (commutatorElement_eq_one_iff_mul_comm.mpr (hD₂N d hd n hn))
  obtain ⟨B, hBR, hBadm, hBD, hRB⟩ := h.a6 ⊥ N R bot_le hN.le hRH (fun g _ => hbot g) hNDA hRadm
    hNR hchief hcen hRD (by simp) hdir
  have hBG : Admits (H ⊔ A) B := by
    rw [← hRG]
    exact hBadm
  have hB0 : B = ⊥ := by
    by_contra hB0
    exact c.not_inf_le (hBR.trans hRH) hBG hB0 hBD.le
  rw [hB0, bot_sup_eq] at hRB
  exact c.not_forall_le_D fun M hM => (le_sSup hM).trans (hSR.trans (hRB.le.trans h.D₁_le))

end MinCex

namespace MinCex

theorem false_of [Finite G] {p : ℕ} {H A D D₁ D₂ : Subgroup G} (c : MinCex p H A D D₁ D₂) :
    False := by
  have h := c.hyp
  have hH0 : H ≠ ⊥ := fun h0 =>
    c.sSup_ne_bot (le_bot_iff.mp ((sSup_ssSet_le H A D D₂).trans h0.le))
  have hHadm : Admits (H ⊔ A) H := sup_le Subgroup.le_normalizer h.a1_admits
  obtain ⟨N, hNH, hN0, hNG, hmin⟩ := HypAAux.exists_minimal_admits hH0 hHadm
  have h34 : ¬ N ⊓ D ≤ D₂ := c.not_inf_le hNH hNG hN0
  have hsol : Group.IsSolvable ↥N := by
    by_contra hns
    exact h34 (HypAAux.inf_le_of_nonsolvable_minimal_normal h.prime h.a1_elemAbelian h.coprime
      h.a3 h.a5 hNH hNG hmin hns)
  have hN : NData H A D D₂ N := ⟨hNH, hNG, hN0, hmin,
    HypAAux.forall_mul_comm_of_solvable_minimal hNG hN0 hmin hsol, h34⟩
  exact c.final hN (c.step39 hN)

end MinCex

theorem exists_max_ssSet_aux (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {H A D D₁ D₂ : Subgroup Γ},
      Nat.card ↥(H ⊔ A) = n → HypA p H A D D₁ D₂ →
        ∃ M₀ ∈ ssSet H A D D₂, ∀ M ∈ ssSet H A D D₂, M ≤ M₀ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ _ _ p H A D D₁ D₂ hn h
    by_contra hno
    refine MinCex.false_of ⟨h, hno, ?_, ?_⟩
    · intro H' hH' hD hadm hne
      have hlt : Nat.card ↥(H' ⊔ A) < n := by
        rw [← hn]
        exact HypAAux.card_lt_of_ne (sup_le_sup_right hH' A) hne
      exact ih _ hlt rfl (h.restrict hH' hD hadm)
    · intro N hNH hN hN0 hND
      have hHn : H ≤ AChief.nrm N := le_sup_left.trans hN
      have hAn : A ≤ AChief.nrm N := le_sup_right.trans hN
      have hlt : Nat.card ↥(AChief.qimg N H ⊔ AChief.qimg N A) < n := by
        rw [← hn, ← SolQuot.qimg_sup hHn hAn]
        exact HypAAux.card_qimg_lt (hNH.trans le_sup_left) hN hN0
      exact ih _ hlt rfl (h.qimg hNH hN hND)

theorem exists_max_ssSet [Finite G] {p : ℕ} {H A D D₁ D₂ : Subgroup G}
    (h : HypA p H A D D₁ D₂) :
    ∃ M₀ ∈ ssSet H A D D₂, ∀ M ∈ ssSet H A D D₂, M ≤ M₀ :=
  exists_max_ssSet_aux _ rfl h

end CFSG.SignalizerFunctorTheorem.McBride.Near
