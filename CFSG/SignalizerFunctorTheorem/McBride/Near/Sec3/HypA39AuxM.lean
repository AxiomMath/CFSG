module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxK1Data

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R K₁ : Subgroup Γ}

namespace Red

theorem G_eq_K₁ (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁) :
    H ⊔ A = K₁ ⊔ (D ⊔ A) := by
  rw [← c.G_eq, ← d.sup_D₁]
  apply le_antisymm
  · refine sup_le (sup_le (sup_le le_sup_left ?_) ?_) ?_
    · exact c.D₁_le_D.trans (le_sup_left.trans le_sup_right)
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  · refine sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) (sup_le ?_ ?_)
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

theorem K₁_cen (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁) :
    ∀ x ∈ K₁, ∀ y ∈ L, x * y = y * x := fun x hx y hy => c.R_cen x (d.le_R hx) y hy

theorem K₁_le_H (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁) : K₁ ≤ H :=
  d.le_R.trans c.R_le_H

theorem L_le_K₁ (d : K1Data H A D₁ E L R K₁) : L ≤ K₁ := d.L_lt.le

theorem exists_noncomm [Finite Γ] (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁) :
    ∃ x ∈ K₁, ∃ y ∈ K₁, ⁅x, y⁆ ∉ L := by
  by_contra hcon
  push Not at hcon
  have hK₁H := c.K₁_le_H d
  have hLK₁ := L_le_K₁ d
  have hEab : IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (commute_of_mem c.h15.a1_elemAbelian.1 (c.hEA a.2)
      (c.hEA b.2)).eq⟩⟩, fun x hx => c.h15.a1_elemAbelian.2 x (c.hEA hx)⟩
  have hEK₁ : E ≤ Subgroup.normalizer (K₁ : Set Γ) :=
    (c.hEA.trans le_sup_right).trans d.admits
  have hgen := McBride.iSup_centralizer_nonidentity c.h15.prime hEab c.hE.ge hEK₁
    (c.h15.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK₁H))
  have hG := c.G_eq_K₁ d
  have hLN : ∀ e : Γ, L ≤ Subgroup.normalizer ((K₁ ⊓ Subgroup.centralizer {e} : Subgroup Γ) :
      Set Γ) := fun e => admits_of_centralizes fun l hl x hx =>
    (c.R_cen x (d.le_R (Subgroup.mem_inf.mp hx).1) l hl).symm
  have hTadm : ∀ e ∈ E, Admits (H ⊔ A) ((K₁ ⊓ Subgroup.centralizer {e}) ⊔ L) := by
    intro e he
    have heA : e ∈ A := c.hEA he
    have hDC := c.D_le_centralizer_singleton heA
    have hAC := c.A_le_centralizer heA
    rw [hG]
    refine sup_le ?_ (sup_le ?_ ?_)
    · refine admits_of_forall_conj fun k hk t ht => ?_
      obtain ⟨c', hc', l, hl, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' (hLN e)).mp ht
      have hkl : k * l * k⁻¹ = l := by
        rw [c.K₁_cen d k hk l hl, mul_assoc, mul_inv_cancel, mul_one]
      have h1 : k * (c' * l) * k⁻¹ = ⁅k, c'⁆ * c' * (k * l * k⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [h1, hkl]
      exact mul_mem (mul_mem (Subgroup.mem_sup_right (hcon k hk c' (Subgroup.mem_inf.mp hc').1))
        (Subgroup.mem_sup_left hc')) (Subgroup.mem_sup_right hl)
    · have h1 : Admits D (K₁ ⊓ Subgroup.centralizer {e}) :=
        (d.admits.mono_left (le_sup_left.trans c.DA_le_G)).inf (admits_centralizer_singleton hDC)
      exact h1.sup (c.hLG.mono_left (le_sup_left.trans c.DA_le_G))
    · have h1 : Admits A (K₁ ⊓ Subgroup.centralizer {e}) :=
        (d.admits.mono_left le_sup_right).inf (admits_centralizer_singleton hAC)
      exact h1.sup (c.hLG.mono_left le_sup_right)
  have hTcases : ∀ e ∈ E, (K₁ ⊓ Subgroup.centralizer {e}) ⊔ L = L ∨
      (K₁ ⊓ Subgroup.centralizer {e}) ⊔ L = K₁ :=
    fun e he => d.min _ (hTadm e he) le_sup_right (sup_le inf_le_left hLK₁)
  by_cases hall : ∀ e ∈ E, e ≠ 1 → (K₁ ⊓ Subgroup.centralizer {e}) ⊔ L = L
  · have hle : K₁ ≤ L := by
      refine le_of_eq_of_le hgen.symm ?_
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      exact le_sup_left.trans (hall a ha ha1).le
    exact absurd d.L_lt (not_lt_of_ge hle)
  · push Not at hall
    obtain ⟨e, he, he1, hne⟩ := hall
    have hTK : (K₁ ⊓ Subgroup.centralizer {e}) ⊔ L = K₁ := (hTcases e he).resolve_left hne
    refine he1 (d.faithful e he fun x hx => ?_)
    rw [← hTK] at hx
    obtain ⟨c', hc', l, hl, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' (hLN e)).mp hx
    have hel : e * l = l * e := c.A_cen e (c.hEA he) l hl
    rw [commutator_mul_of_commute hel]
    have : ⁅e, c'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2).symm
    rw [this]
    exact one_mem _

theorem qK_min (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁)
    {M' : Subgroup (AChief.QG L)} (hM' : M' ≤ AChief.qimg L K₁)
    (hadm : Admits (AChief.qimg L (H ⊔ A)) M') : M' = ⊥ ∨ M' = AChief.qimg L K₁ := by
  have hK₁n : K₁ ≤ AChief.nrm L := (c.K₁_le_H d).trans (le_sup_left.trans c.hLG)
  have hMK₁ : SolQuot.qpre L M' ≤ K₁ := by
    refine (SolQuot.qpre_mono hM').trans ?_
    rw [SolQuot.qpre_qimg hK₁n, sup_eq_left.mpr (L_le_K₁ d)]
  rcases d.min (SolQuot.qpre L M') (HypAAux.admits_qpre c.hLG hadm) (SolQuot.le_qpre M') hMK₁
    with h | h
  · left
    rw [← SolQuot.qimg_qpre (R := L) M', h, SolQuot.qimg_self]
  · right
    rw [← SolQuot.qimg_qpre (R := L) M', h]

theorem qK_isASimple (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁)
    (hnc : ∃ x ∈ K₁, ∃ y ∈ K₁, ⁅x, y⁆ ∉ L) :
    Nonsolvable.IsASimple (AChief.qimg L (H ⊔ A)) (AChief.qimg L K₁) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hK₁n : K₁ ≤ AChief.nrm L := (c.K₁_le_H d).trans (le_sup_left.trans c.hLG)
  refine ⟨HypAAux.admits_qimg d.admits, ?_, fun N hN _ hadm => qK_min c d hN hadm⟩
  refine ⟨AChief.qmap L ⟨x, hK₁n hx⟩, (AChief.mem_qimg_iff L K₁ _).mpr ⟨_, hx, rfl⟩,
    AChief.qmap L ⟨y, hK₁n hy⟩, (AChief.mem_qimg_iff L K₁ _).mpr ⟨_, hy, rfl⟩, fun hcomm => hxy ?_⟩
  rw [← SolQuot.qpre_bot (R := L)]
  refine (HypAAux.commutator_mem_qpre_iff (hK₁n hx) (hK₁n hy)).mpr ?_
  exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr hcomm)

theorem qK_not_solvable (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁)
    (hnc : ∃ x ∈ K₁, ∃ y ∈ K₁, ⁅x, y⁆ ∉ L) : ¬ Group.IsSolvable ↥(AChief.qimg L K₁) := by
  intro hsol
  obtain ⟨hA, ⟨a, ha, b, hb, hab⟩, -⟩ := c.qK_isASimple d hnc
  have hne : AChief.qimg L K₁ ≠ ⊥ := fun h0 => hab (by
    have ha' : a ∈ (⊥ : Subgroup (AChief.QG L)) := h0 ▸ ha
    rw [Subgroup.mem_bot.mp ha', one_mul, mul_one])
  have := HypAAux.forall_mul_comm_of_solvable_minimal hA hne
    (fun M hM hadm => c.qK_min d hM hadm) hsol
  exact hab (this a ha b hb)

theorem commutator_eq [Finite Γ] (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁)
    (hnc : ∃ x ∈ K₁, ∃ y ∈ K₁, ⁅x, y⁆ ∉ L) : ⁅K₁, K₁⁆ = K₁ := by
  have hK₁H := c.K₁_le_H d
  have hLK₁ := L_le_K₁ d
  have hK₁n : K₁ ≤ AChief.nrm L := hK₁H.trans (le_sup_left.trans c.hLG)
  have hle : ⁅K₁, K₁⁆ ≤ K₁ := Thm210.commutator_le_of_normalizes Subgroup.le_normalizer
  have hadm : Admits (H ⊔ A) ⁅K₁, K₁⁆ := fun g hg =>
    Thm210.mem_normalizer_commutator (d.admits hg) (d.admits hg)
  have hsup : ⁅K₁, K₁⁆ ⊔ L = K₁ := by
    rcases d.min (⁅K₁, K₁⁆ ⊔ L) (hadm.sup c.hLG) le_sup_right (sup_le hle hLK₁) with h | h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hnc
      exact hxy (h ▸ Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy))
    · exact h
  rcases c.hLmin (⁅K₁, K₁⁆ ⊓ L) inf_le_right (hadm.inf c.hLG) with h | h
  ·
    exfalso
    have hK₁'H : ⁅K₁, K₁⁆ ≤ H := hle.trans hK₁H
    have hK₁'n : ⁅K₁, K₁⁆ ≤ AChief.nrm L := hle.trans hK₁n
    have hne0 : ⁅K₁, K₁⁆ ≠ ⊥ := by
      intro h0
      rw [h0, bot_sup_eq] at hsup
      exact absurd hsup (ne_of_lt d.L_lt)
    have hLcen : ∀ x ∈ ⁅K₁, K₁⁆, ∀ l ∈ L, l * x = x * l := fun x hx l hl =>
      (c.K₁_cen d x (hle hx) l hl).symm
    have hDN : D ≤ Subgroup.normalizer ((⁅K₁, K₁⁆ : Subgroup Γ) : Set Γ) :=
      (c.D_le.trans le_sup_left).trans hadm
    have hAN : A ≤ Subgroup.normalizer ((⁅K₁, K₁⁆ : Subgroup Γ) : Set Γ) :=
      le_sup_right.trans hadm
    have hchief : IsChiefFactorOf (⁅K₁, K₁⁆ ⊔ D ⊔ A) ⁅K₁, K₁⁆ ⊥ := by
      refine ⟨⟨bot_le, fun g _ => mem_normalizer_bot g⟩, ⟨le_sup_left.trans le_sup_left,
        sup_le (sup_le Subgroup.le_normalizer hDN) hAN⟩, bot_lt_iff_ne_bot.mpr hne0,
        fun K hK _ hKK₁' => ?_⟩
      have hKN : ⁅K₁, K₁⁆ ⊔ D ⊔ A ≤ Subgroup.normalizer (K : Set Γ) := hK.2
      have hLK : L ≤ Subgroup.normalizer (K : Set Γ) :=
        admits_of_centralizes fun l hl x hx => (c.K₁_cen d x (hle (hKK₁' hx)) l hl).symm
      have hK₁N : K₁ ≤ Subgroup.normalizer (K : Set Γ) := by
        rw [← hsup]
        exact sup_le (le_sup_left.trans (le_sup_left.trans hKN)) hLK
      have hKG : Admits (H ⊔ A) K := by
        rw [c.G_eq_K₁ d]
        exact sup_le hK₁N (sup_le ((le_sup_right.trans le_sup_left).trans hKN)
          (le_sup_right.trans hKN))
      have hKL : K ⊔ L ≤ K₁ := sup_le (hKK₁'.trans hle) hLK₁
      rcases d.min (K ⊔ L) (hKG.sup c.hLG) le_sup_right hKL with h1 | h1
      · left
        have h2 : K ≤ ⁅K₁, K₁⁆ ⊓ L := le_inf hKK₁' (le_sup_left.trans h1.le)
        rw [h] at h2
        exact le_bot_iff.mp h2
      · right
        have h2 : ⁅K₁, K₁⁆ ≤ K ⊔ (⁅K₁, K₁⁆ ⊓ L) := by
          refine (le_inf le_rfl ?_).trans (inf_sup_le_sup_inf' hKK₁' hLK)
          exact hle.trans h1.symm.le
        rw [h, sup_bot_eq] at h2
        exact le_antisymm hKK₁' h2
    have hnsol : ¬ IsSolvableSection ⁅K₁, K₁⁆ ⊥ := by
      rw [HypAAux.isSolvableSection_bot_iff]
      intro hsol
      have himg : AChief.qimg L ⁅K₁, K₁⁆ = AChief.qimg L K₁ := by
        conv_rhs => rw [← hsup]
        rw [SolQuot.qimg_sup hK₁'n Subgroup.le_normalizer, SolQuot.qimg_self, sup_bot_eq]
      refine c.qK_not_solvable d hnc ?_
      rw [← himg]
      exact Group.isSolvable_of_surjective (SolQuot.qres_surjective hK₁'n)
    have h5 := c.h15.a5 ⁅K₁, K₁⁆ ⊥ hK₁'H bot_le (hadm.mono_left c.DA_le_G) (admits_bot _) hchief
      hnsol (by simp)
    exact hne0 (c.eq_bot_of_normal hK₁'H hadm h5)
  ·
    have hL : L ≤ ⁅K₁, K₁⁆ := inf_eq_right.mp h
    rw [sup_eq_left.mpr hL] at hsup
    exact hsup

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
