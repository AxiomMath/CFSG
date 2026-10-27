module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2WeakClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem imgTil_mono' {V₀ V A B : Subgroup G} (hV : IsElemAbelian 2 V) (h : A ≤ B) :
    imgTil V₀ V hV A ≤ imgTil V₀ V hV B := by
  unfold imgTil
  exact Subgroup.map_mono fun x hx => h hx

private theorem imgTil_sup_V₀' {V₀ V N : Subgroup G} (hV : IsElemAbelian 2 V) (hN : N ≤ V)
    (hV₀ : V₀ ≤ V) : imgTil V₀ V hV (N ⊔ V₀) = imgTil V₀ V hV N := by
  have h1 : intSub V hV (N ⊔ V₀) = intSub V hV N ⊔ intSub V hV V₀ :=
    Subgroup.subgroupOf_sup hN hV₀
  have h2 : (intSub V hV V₀).map (mkTil V₀ V hV) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hx
  unfold imgTil
  rw [h1, Subgroup.map_sup, h2, sup_bot_eq]

theorem commutator_le_of_pairing {V W N₁ N₂ D : Subgroup G} {y : G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hN₁ : N₁ ≤ V) (hN₂ : N₂ ≤ W) (hD : D ≤ V ⊓ W) (hVW : ⁅V, W⁆ ≤ V ⊓ W)
    (hN₁W : ⁅N₁, W⁆ ≤ D) (hVN₂ : ⁅V, N₂⁆ ≤ D)
    (hyV : y ∈ normalizer (V : Set G)) (hyW : y ∈ normalizer (W : Set G))
    (hyN₁ : y ∈ normalizer (N₁ : Set G))
    (hyD : ∀ z ∈ V ⊓ W, ⁅z, y⁆ ∈ D) (hW₂ : ∀ w ∈ W, ⁅w, y⁆ ∈ N₂)
    (hV₁ : ∀ v ∈ V, ⁅v, y⁆ ∈ N₁ → v ∈ N₁) :
    ⁅V, W⁆ ≤ D := by
  have hDV : D ≤ V := hD.trans inf_le_left
  have hyV' : ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.1 hyV v).1 hv
  have hyW' : ∀ w ∈ W, y * w * y⁻¹ ∈ W := fun w hw => (Subgroup.mem_normalizer_iff.1 hyW w).1 hw
  have hyN₁' : ∀ n ∈ N₁, y * n * y⁻¹ ∈ N₁ :=
    fun n hn => (Subgroup.mem_normalizer_iff.1 hyN₁ n).1 hn
  have hδmem : ∀ v ∈ V, ⁅v, y⁆ ∈ V := by
    intro v hv
    have h1 : y * v⁻¹ * y⁻¹ ∈ V := hyV' v⁻¹ (V.inv_mem hv)
    have h2 : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact V.mul_mem hv h1
  let δ : ↥V →* ↥V :=
    { toFun := fun v => ⟨⁅(v : G), y⁆, hδmem (v : G) v.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show ⁅((a : ↥V) : G) * ((b : ↥V) : G), y⁆ = ⁅(a : G), y⁆ * ⁅(b : G), y⁆
        rw [commutatorElement_mul_left_eq_conj_mul,
          Commute.mul_inv_cancel (hVab (a : G) a.2 ⁅(b : G), y⁆ (hδmem (b : G) b.2))]
        exact hVab ⁅(b : G), y⁆ (hδmem (b : G) b.2) ⁅(a : G), y⁆ (hδmem (a : G) a.2) }
  have hδ_apply : ∀ a : ↥V, (δ a : G) = ⁅(a : G), y⁆ := fun a => rfl
  let N : Subgroup ↥V := N₁.subgroupOf V
  have hNmem : ∀ a : ↥V, a ∈ N ↔ (a : G) ∈ N₁ := fun a => Subgroup.mem_subgroupOf ..
  haveI : IsMulCommutative ↥V :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hVab a.1 a.2 b.1 b.2)
  let φ : ↥V →* (↥V ⧸ N) := (QuotientGroup.mk' N).comp δ
  have hφ_apply : ∀ a : ↥V, φ a = QuotientGroup.mk' N (δ a) := fun a => rfl
  have hφker : φ.ker = N := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : δ a ∈ N := by
        have h' : QuotientGroup.mk' N (δ a) = 1 := by rw [← hφ_apply]; exact h
        simpa only [QuotientGroup.mk'_apply] using (QuotientGroup.eq_one_iff (N := N) (δ a)).1 h'
      have h2 : (a : G) ∈ N₁ := by
        have h3 : ⁅(a : G), y⁆ ∈ N₁ := by
          have h4 : ((δ a : ↥V) : G) ∈ N₁ := (hNmem (δ a)).1 h1
          rwa [hδ_apply a] at h4
        exact hV₁ (a : G) a.2 h3
      exact (hNmem a).2 h2
    · intro ha
      have h1 : δ a ∈ N := by
        rw [hNmem]
        rw [hδ_apply a]
        have h2 : (a : G) ∈ N₁ := (hNmem a).1 ha
        have h3 : y * (a : G)⁻¹ * y⁻¹ ∈ N₁ := by
          have h4 := hyN₁' (a : G)⁻¹ (N₁.inv_mem h2)
          simpa only [inv_inv] using h4
        have h5 : ⁅(a : G), y⁆ = (a : G) * (y * (a : G)⁻¹ * y⁻¹) := by
          rw [commutatorElement_def]; group
        rw [h5]
        exact N₁.mul_mem h2 h3
      have h6 : QuotientGroup.mk' N (δ a) = 1 := (QuotientGroup.eq_one_iff (N := N) (δ a)).2 h1
      rw [hφ_apply]
      exact h6
  have hφrange : φ.range = ⊤ := by
    have he : Nat.card (↥V ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hφker] at he
    exact (Subgroup.card_eq_iff_eq_top (H := φ.range)).mp he.symm
  have key : ∀ a : G, a ∈ V → ∀ w ∈ W, ⁅⁅a, y⁆, w⁆ ∈ D := by
    intro a ha w hw
    have huV : y * a * y⁻¹ ∈ V := hyV' a ha
    have hzVW : ⁅a, w⁆ ∈ V ⊓ W := hVW (Subgroup.commutator_mem_commutator ha hw)
    have hzV : ⁅a, w⁆ ∈ V := hzVW.1
    have hzW : ⁅a, w⁆ ∈ W := hzVW.2
    have hzu : ⁅⁅a, w⁆, y⁆ ∈ D := hyD _ hzVW
    have hnu : ⁅w, y⁆ ∈ N₂ := hW₂ w hw
    have hXW : y * ⁅a, w⁆ * y⁻¹ ∈ W := hyW' _ hzW
    have huw_inf : ⁅y * a * y⁻¹, w⁆ ∈ V ⊓ W :=
      hVW (Subgroup.commutator_mem_commutator huV hw)
    have hzy : y * ⁅a, w⁆ * y⁻¹ = ⁅⁅a, w⁆, y⁆⁻¹ * ⁅a, w⁆ := by
      rw [commutatorElement_def]; group
    have huw₁ : ⁅y * a * y⁻¹, y * w * y⁻¹⁆ = y * ⁅a, w⁆ * y⁻¹ :=
      (conjugate_commutatorElement a w y).symm
    have hw_eq : w = ⁅w, y⁆ * (y * w * y⁻¹) := by
      rw [commutatorElement_def]; group
    have h_uw : ⁅y * a * y⁻¹, w⁆ = ⁅y * a * y⁻¹, ⁅w, y⁆⁆ * (y * ⁅a, w⁆ * y⁻¹) := by
      conv_lhs => rw [hw_eq]
      rw [commutatorElement_mul_right_eq_mul_conj, huw₁]
      have hcx : ⁅w, y⁆ * (y * ⁅a, w⁆ * y⁻¹) = (y * ⁅a, w ⁆ * y⁻¹) * ⁅w, y⁆ :=
        hWab _ (hN₂ hnu) _ hXW
      have hconj : ⁅w, y⁆ * (y * ⁅a, w⁆ * y⁻¹) * (⁅w, y⁆)⁻¹ = y * ⁅a, w⁆ * y⁻¹ :=
        Commute.mul_inv_cancel hcx
      calc ⁅y * a * y⁻¹, ⁅w, y⁆⁆ * ⁅w, y⁆ * (y * ⁅a, w⁆ * y⁻¹) * (⁅w, y⁆)⁻¹
          = ⁅y * a * y⁻¹, ⁅w, y⁆⁆ * (⁅w, y⁆ * (y * ⁅a, w⁆ * y⁻¹) * (⁅w, y⁆)⁻¹) := by
              group
        _ = ⁅y * a * y⁻¹, ⁅w, y⁆⁆ * (y * ⁅a, w⁆ * y⁻¹) := by rw [hconj]
    have h_uw' : ⁅y * a * y⁻¹, w⁆ =
        (⁅y * a * y⁻¹, ⁅w, y⁆⁆ * ⁅⁅a, w⁆, y⁆⁻¹) * ⁅a, w⁆ := by
      rw [h_uw, hzy]
      group
    have hdD : ⁅y * a * y⁻¹, ⁅w, y⁆⁆ * ⁅⁅a, w⁆, y⁆⁻¹ ∈ D :=
      D.mul_mem (hVN₂ (Subgroup.commutator_mem_commutator huV hnu)) (D.inv_mem hzu)
    have hu_inv : ⁅(y * a * y⁻¹)⁻¹, w⁆ = ⁅y * a * y⁻¹, w⁆⁻¹ := by
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      simpa only [inv_inv] using Commute.mul_inv_cancel
        (hVab (y * a * y⁻¹)⁻¹ (V.inv_mem huV) _ (V.inv_mem huw_inf.1))
    have hδa : ⁅a, y⁆ = a * (y * a * y⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    have hmain : ⁅⁅a, y⁆, w⁆ =
        (⁅y * a * y⁻¹, ⁅w, y⁆⁆ * ⁅⁅a, w⁆, y⁆⁻¹)⁻¹ := by
      rw [hδa, commutatorElement_mul_left_eq_conj_mul, hu_inv]
      rw [Commute.mul_inv_cancel (hVab a ha _ (V.inv_mem huw_inf.1))]
      rw [h_uw']
      rw [mul_inv_rev]
      simpa only [inv_inv] using Commute.mul_inv_cancel
        (hVab (⁅a, w⁆)⁻¹ (V.inv_mem hzV) _ (V.inv_mem (hDV hdD)))
    rw [hmain]
    exact D.inv_mem hdD
  rw [Subgroup.commutator_le]
  intro v hv w hw
  have hmem : QuotientGroup.mk' N (⟨v, hv⟩ : ↥V) ∈ φ.range := by
    rw [hφrange]; exact Subgroup.mem_top _
  obtain ⟨a, ha⟩ := hmem
  have hmk : QuotientGroup.mk' N (δ a) = QuotientGroup.mk' N (⟨v, hv⟩ : ↥V) := by
    change φ a = QuotientGroup.mk' N (⟨v, hv⟩ : ↥V)
    exact ha
  obtain ⟨m, hmN, hm_eq⟩ := (QuotientGroup.mk'_eq_mk' (N := N)).1 hmk
  have hmG : (m : G) ∈ N₁ := (hNmem m).1 hmN
  have hm_eqG : (δ a : G) * (m : G) = v := by
    have h := congrArg (fun x : ↥V => (x : G)) hm_eq
    simpa using h
  have hδaV : (δ a : G) ∈ V := by rw [hδ_apply a]; exact hδmem a.1 a.2
  have hcomm_m : ⁅(m : G), w⁆ ∈ D := hN₁W (Subgroup.commutator_mem_commutator hmG hw)
  have hcomm_mV : ⁅(m : G), w⁆ ∈ V := hDV hcomm_m
  have hkey : ⁅(δ a : G), w⁆ ∈ D := by
    rw [hδ_apply a]
    exact key a a.2 w hw
  have hfinal : ⁅v, w⁆ = ⁅(m : G), w⁆ * ⁅(δ a : G), w⁆ := by
    calc ⁅v, w⁆ = ⁅(δ a : G) * (m : G), w⁆ := by rw [hm_eqG]
      _ = (δ a : G) * ⁅(m : G), w⁆ * (δ a : G)⁻¹ * ⁅(δ a : G), w⁆ := by
            rw [commutatorElement_mul_left_eq_conj_mul]
      _ = ⁅(m : G), w⁆ * ⁅(δ a : G), w⁆ := by
            rw [Commute.mul_inv_cancel (hVab _ hδaV _ hcomm_mV)]
  rw [hfinal]
  exact D.mul_mem hcomm_m hkey

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section Certified


theorem inf_conjSubgroup_eq_of_pGroup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G} (hh : h ∈ H) (hhM : h ∉ M)
    (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) :
    V ⊓ conjSubgroup V h = (U ⊔ V₀) ⊓ conjSubgroup (U ⊔ V₀) h ∧
      ⁅V, conjSubgroup V h⁆ ≤ V ⊓ conjSubgroup V h := by
  have hU'V : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hc := c.comm_of_isPGroup h1 h5 h15 hS Mo hh hhM hP
  obtain ⟨⟨-, -, hVleMh, hWleM⟩, -, -⟩ := hc
  have hVnormW : V ≤ normalizer (conjSubgroup V h : Set G) := by
    rw [← E3.conjSubgroup_normalizer, c.cex.hyp.h6.normalizer_eq]
    exact hVleMh
  have hWnormV : conjSubgroup V h ≤ normalizer (V : Set G) :=
    hWleM.trans (le_of_eq c.cex.hyp.h6.normalizer_eq.symm)
  have hVWle : ⁅V, conjSubgroup V h⁆ ≤ V ⊓ conjSubgroup V h :=
    le_inf ((Subgroup.le_normalizer_iff_commutator_le_left).1 hWnormV)
      ((Subgroup.le_normalizer_iff_commutator_le_right).1 hVnormW)
  let C : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)
  have hVI : ⁅V, conjClosure (U ⊔ V₀) H⁆ ≤ V₀ := by
    have h := comm_conj_conjClosure_le h1 hS c (Subgroup.one_mem H)
    simpa only [conjSubgroup_one] using h
  have hWI : ⁅conjSubgroup V h, conjClosure (U ⊔ V₀) H⁆ ≤ conjSubgroup V₀ h :=
    comm_conj_conjClosure_le h1 hS c hh
  have hbot : V₀ ⊓ conjSubgroup V₀ h = ⊥ := by
    rw [inf_comm]
    exact c.cex.hyp.conj_inf_eq_bot hhM
  have hVW_le_C : V ⊓ conjSubgroup V h ≤ C := by
    intro x hx
    obtain ⟨hxV, hxW⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (c.cex.V_le_S.trans (c.S_le.trans c.mem.1)) hxV
    · rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have hxi : ⁅x, i⁆ = 1 := by
        refine Subgroup.mem_bot.1 ?_
        rw [← hbot]
        exact Subgroup.mem_inf.2 ⟨(Subgroup.commutator_le.1 hVI) x hxV i hi,
          (Subgroup.commutator_le.1 hWI) x hxW i hi⟩
      exact (commutatorElement_eq_one_iff_mul_comm.1 hxi).symm
  have hCnorm : conjSubgroup C h = C := by
    change conjSubgroup (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) h = _
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
    have hH : conjSubgroup H h = H :=
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hh)
    have hI : conjSubgroup (conjClosure (U ⊔ V₀) H) h = conjClosure (U ⊔ V₀) H :=
      conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure (U ⊔ V₀) H hh)
    rw [hH, hI]
  have hVW_le : V ⊓ conjSubgroup V h ≤ (U ⊔ V₀) ⊓ conjSubgroup (U ⊔ V₀) h := by
    refine le_inf ?_ ?_
    · have h1' : V ⊓ conjSubgroup V h ≤ V ⊓ C := le_inf inf_le_left hVW_le_C
      have h2' : V ⊓ C = U ⊔ V₀ := inf_centralizer_eq_sup h1 h5 h15 hS c
      rwa [h2'] at h1'
    · have h1' : V ⊓ conjSubgroup V h ≤ conjSubgroup V h ⊓ C :=
        le_inf inf_le_right hVW_le_C
      have h2' : conjSubgroup V h ⊓ C = conjSubgroup (U ⊔ V₀) h := by
        have h3' : conjSubgroup (V ⊓ C) h = conjSubgroup V h ⊓ C := by
          rw [E3.conjSubgroup_inf, hCnorm]
        rw [← h3', inf_centralizer_eq_sup h1 h5 h15 hS c]
      rwa [h2'] at h1'
  refine ⟨le_antisymm hVW_le (le_inf (inf_le_left.trans hU'V)
    (inf_le_right.trans (E3.conjSubgroup_mono_left h hU'V))), hVWle⟩

theorem not_comm_le_sup_of_pGroup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G} (hh : h ∈ H) (hhM : h ∉ M)
    (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) :
    ¬ ⁅V, conjSubgroup V h⁆ ≤ V₀ ⊔ conjSubgroup V₀ h := by
  intro hle
  have hV := c.cex.hyp.h6.elemAbelian
  have hMnormV : M ≤ normalizer (V : Set G) := le_of_eq c.cex.hyp.h6.normalizer_eq.symm
  have hMnormV₀ : M ≤ normalizer (V₀ : Set G) := c.cex.hyp.h6.le_normalizer₀
  have hc := c.comm_of_isPGroup h1 h5 h15 hS Mo hh hhM hP
  obtain ⟨⟨hcomm1, -, -, hWleM⟩, -, hWnotC⟩ := hc
  have hcommB : conjSubgroup V₀ h ≤ Subgroup.centralizer (V₀ : Set G) :=
    (Subgroup.le_centralizer_iff).1
      (c.cex.hyp.h6.le.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm1))
  have hnorm : V₀ ≤ Subgroup.normalizer (conjSubgroup V₀ h : Set G) :=
    ((Subgroup.le_centralizer_iff).1 hcommB).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨w, hwW, hwnotC⟩ := SetLike.not_le_iff_exists.1 hWnotC
  have hwM : w ∈ M := hWleM hwW
  have hwst : w ∈ stabTil V₀ V := le_stabTil hMnormV hMnormV₀ hwM
  have hzpw : Subgroup.zpowers w ≤ conjSubgroup V h := Subgroup.zpowers_le.2 hwW
  have hcomm_le : ⁅V, Subgroup.zpowers w⁆ ≤ V₀ ⊔ (V ⊓ conjSubgroup V₀ h) := by
    have h1' : ⁅V, Subgroup.zpowers w⁆ ≤ V ⊓ (V₀ ⊔ conjSubgroup V₀ h) := by
      refine le_inf ?_ ?_
      · have hz : Subgroup.zpowers w ≤ normalizer (V : Set G) :=
          hzpw.trans (hWleM.trans (le_of_eq c.cex.hyp.h6.normalizer_eq.symm))
        exact (Subgroup.le_normalizer_iff_commutator_le_left).1 hz
      · exact (Subgroup.commutator_mono le_rfl hzpw).trans hle
    have hmod_le : V ⊓ (V₀ ⊔ conjSubgroup V₀ h) ≤ V₀ ⊔ (V ⊓ conjSubgroup V₀ h) := by
      intro x hx
      obtain ⟨hxV, hxsup⟩ := Subgroup.mem_inf.1 hx
      have hxmul : x ∈ (V₀ : Set G) * (conjSubgroup V₀ h : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right V₀ (conjSubgroup V₀ h) hnorm]
        exact hxsup
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hxmul
      have hbV : b ∈ V := by
        have hb' : b = a⁻¹ * x := by rw [← hab]; group
        rw [hb']
        exact V.mul_mem (V.inv_mem (c.cex.hyp.h6.le ha)) hxV
      have hbX : b ∈ V ⊓ conjSubgroup V₀ h := Subgroup.mem_inf.2 ⟨hbV, hb⟩
      rw [show x = a * b from hab.symm]
      exact (V₀ ⊔ (V ⊓ conjSubgroup V₀ h)).mul_mem
        (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbX)
    exact h1'.trans hmod_le
  have hrank : rk ↥(commV (Subgroup.zpowers (actTil V₀ V hV ⟨w, hwst⟩))) ≤
      E3.mQuot V (U ⊔ V₀) := by
    rw [commV_zpowers_actTil_eq_imgTil_commutator hV hwst]
    have himg : imgTil V₀ V hV ⁅V, Subgroup.zpowers w⁆ ≤
        imgTil V₀ V hV (conjSubgroup V₀ h ⊓ V) := by
      have hstep := imgTil_mono' (V₀ := V₀) hV hcomm_le
      have hsup : imgTil V₀ V hV (V₀ ⊔ (V ⊓ conjSubgroup V₀ h)) =
          imgTil V₀ V hV (conjSubgroup V₀ h ⊓ V) := by
        rw [sup_comm, inf_comm]
        exact imgTil_sup_V₀' (V₀ := V₀) hV inf_le_right c.cex.hyp.h6.le
      rwa [hsup] at hstep
    calc rk ↥(imgTil V₀ V hV ⁅V, Subgroup.zpowers w⁆)
        ≤ rk ↥(imgTil V₀ V hV (conjSubgroup V₀ h ⊓ V)) := rk_mono himg
      _ ≤ rk ↥(conjSubgroup V₀ h ⊓ V) := imgTil_rank_le hV inf_le_right
      _ ≤ E3.mQuot V (U ⊔ V₀) := c.rk_conjSubgroup_inf_le (x := h) hhM
  have hne : actTil V₀ V hV ⟨w, hwst⟩ ≠ 1 := by
    intro h1'
    exact hwnotC ((mem_cTilde_iff hV hMnormV).2 ⟨hwM, ⟨hwst, h1'⟩⟩)
  have hsq : actTil V₀ V hV ⟨w, hwst⟩ * actTil V₀ V hV ⟨w, hwst⟩ = 1 := by
    rw [← map_mul]
    have hww : (⟨w, hwst⟩ : stabTil V₀ V) * ⟨w, hwst⟩ = 1 := by
      apply Subtype.ext
      show w * w = 1
      have hWab := E3.isElemAbelian_conjSubgroup hV h
      simpa [pow_two] using hWab.2 w hwW
    rw [hww, map_one]
  have hA1 : Subgroup.zpowers (actTil V₀ V hV ⟨w, hwst⟩) ≠ ⊥ := by
    intro hbot
    refine hne ?_
    have hmem := Subgroup.mem_zpowers (actTil V₀ V hV ⟨w, hwst⟩)
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hAp : IsPGroup 2 (Subgroup.zpowers (actTil V₀ V hV ⟨w, hwst⟩)) := by
    have ho2 : orderOf (actTil V₀ V hV ⟨w, hwst⟩) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).1 ho2 with ho1 | ho2'
    · exact absurd (orderOf_eq_one_iff.1 ho1) hne
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho2', pow_one])
  have hAle : Subgroup.zpowers (actTil V₀ V hV ⟨w, hwst⟩) ≤ Mbar M V₀ V hV :=
    Subgroup.zpowers_le.2 (actTil_mem_barSub V₀ V hV hwM hwst)
  have hmp : mBar M V₀ V hV ≤ rk ↥(commV (Subgroup.zpowers (actTil V₀ V hV ⟨w, hwst⟩))) := by
    have h1' := E3.mParam_le_rkIdx_fixV hAle hAp hA1
    rwa [rkIdx_fixV_zpowers] at h1'
  exact absurd (lt_of_lt_of_le c.cex.n_lt_mBar (hmp.trans hrank)) (lt_irrefl _)

theorem false_of_fixedPointFree (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G} (hh : h ∈ H) (hhM : h ∉ M)
    (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) {y : G} (hyM : y ∈ M)
    (hyMh : y ∈ conjSubgroup M h) (hyU : ∀ u ∈ U ⊔ V₀, ⁅u, y⁆ ∈ V₀)
    (hfpf : ∀ v ∈ V, ⁅v, y⁆ ∈ U ⊔ V₀ → v ∈ U ⊔ V₀)
    (htriv : ∀ w ∈ conjSubgroup V h, ⁅w, y⁆ ∈ conjSubgroup (U ⊔ V₀) h) : False := by
  have hV := c.cex.hyp.h6.elemAbelian
  have hW : IsElemAbelian 2 (conjSubgroup V h) := E3.isElemAbelian_conjSubgroup hV h
  have hMnormV : M ≤ normalizer (V : Set G) := le_of_eq c.cex.hyp.h6.normalizer_eq.symm
  have hMnormV₀ : M ≤ normalizer (V₀ : Set G) := c.cex.hyp.h6.le_normalizer₀
  have hU'V : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hc := c.comm_of_isPGroup h1 h5 h15 hS Mo hh hhM hP
  obtain ⟨⟨-, -, hVleMh, hWleM⟩, -, -⟩ := hc
  have hinf := inf_conjSubgroup_eq_of_pGroup h1 h5 h15 hS c Mo hh hhM hP
  have hnot := not_comm_le_sup_of_pGroup h1 h5 h15 hS c Mo hh hhM hP
  have hVnormW : V ≤ normalizer (conjSubgroup V h : Set G) := by
    rw [← E3.conjSubgroup_normalizer, c.cex.hyp.h6.normalizer_eq]
    exact hVleMh
  have hyV : y ∈ normalizer (V : Set G) := hMnormV hyM
  have hyW : y ∈ normalizer (conjSubgroup V h : Set G) := by
    rw [← E3.conjSubgroup_normalizer, c.cex.hyp.h6.normalizer_eq]
    exact hyMh
  have hyH1 : ∀ u ∈ (U ⊔ V₀ : Subgroup G), y * u * y⁻¹ ∈ U ⊔ V₀ := by
    intro u hu
    have h1' : ⁅u, y⁆ ∈ V₀ := hyU u hu
    have h2' : y * u * y⁻¹ = ⁅u, y⁆⁻¹ * u := by rw [commutatorElement_def]; group
    rw [h2']
    exact (U ⊔ V₀).mul_mem ((U ⊔ V₀).inv_mem ((le_sup_right : V₀ ≤ U ⊔ V₀) h1')) hu
  have hyN₁ : y ∈ normalizer ((U ⊔ V₀ : Subgroup G) : Set G) := by
    have hle : conjSubgroup (U ⊔ V₀) y⁻¹ ≤ U ⊔ V₀ := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hx2 : y⁻¹ * x * y ∈ U ⊔ V₀ := by simpa only [inv_inv] using hx
      have hx' : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      rw [hx']
      exact hyH1 _ hx2
    have heq : conjSubgroup (U ⊔ V₀) y⁻¹ = U ⊔ V₀ :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (E3.card_conjSubgroup (U ⊔ V₀) y⁻¹).symm)
    have hyinv : y⁻¹ ∈ normalizer ((U ⊔ V₀ : Subgroup G) : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.1 heq
    simpa using (normalizer ((U ⊔ V₀ : Subgroup G) : Set G)).inv_mem hyinv
  have hN₁W : ⁅U ⊔ V₀, conjSubgroup V h⁆ ≤
      (V ⊓ conjSubgroup V₀ h) ⊔ (conjSubgroup V h ⊓ V₀) := by
    refine Subgroup.commutator_le.2 fun n hn w hw => ?_
    have hnV : n ∈ V := hU'V hn
    have hnI : n ∈ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H hn
    have hwM : w ∈ M := hWleM hw
    have hcomm_V : ⁅n, w⁆ ∈ V :=
      (Subgroup.le_normalizer_iff_commutator_le_left).1
        (Subgroup.zpowers_le.2 (hMnormV hwM))
        (Subgroup.commutator_mem_commutator hnV (Subgroup.mem_zpowers w))
    have hcomm_V₀' : ⁅n, w⁆ ∈ conjSubgroup V₀ h := by
      have hwn : ⁅w, n⁆ ∈ conjSubgroup V₀ h :=
        (Subgroup.commutator_le.1 (comm_conj_conjClosure_le h1 hS c hh)) w hw n hnI
      have heq : ⁅n, w⁆ = ⁅w, n⁆⁻¹ := (commutatorElement_inv w n).symm
      rw [heq]
      exact (conjSubgroup V₀ h).inv_mem hwn
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hcomm_V, hcomm_V₀'⟩)
  have hVI : ⁅V, conjClosure (U ⊔ V₀) H⁆ ≤ V₀ := by
    have h := comm_conj_conjClosure_le h1 hS c (Subgroup.one_mem H)
    simpa only [conjSubgroup_one] using h
  have hVN₂ : ⁅V, conjSubgroup (U ⊔ V₀) h⁆ ≤
      (V ⊓ conjSubgroup V₀ h) ⊔ (conjSubgroup V h ⊓ V₀) := by
    refine Subgroup.commutator_le.2 fun v hv n hn => ?_
    have hnI : n ∈ conjClosure (U ⊔ V₀) H := conjSubgroup_le_conjClosure_of_mem hh le_rfl hn
    have hnW : n ∈ conjSubgroup V h := E3.conjSubgroup_mono_left h hU'V hn
    have hcomm_W : ⁅v, n⁆ ∈ conjSubgroup V h :=
      (Subgroup.commutator_le.1 ((Subgroup.le_normalizer_iff_commutator_le_right).1 hVnormW))
        v hv n hnW
    have hnv_V₀ : ⁅n, v⁆ ∈ V₀ := by
      have hmem : ⁅n, v⁆ ∈ ⁅conjClosure (U ⊔ V₀) H, V⁆ :=
        Subgroup.commutator_mem_commutator hnI hv
      rw [Subgroup.commutator_comm] at hmem
      exact hVI hmem
    have hv_V₀ : ⁅v, n⁆ ∈ V₀ := by
      have heq : ⁅v, n⁆ = ⁅n, v⁆⁻¹ := (commutatorElement_inv n v).symm
      rw [heq]
      exact V₀.inv_mem hnv_V₀
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hcomm_W, hv_V₀⟩)
  have hyD : ∀ z ∈ V ⊓ conjSubgroup V h, ⁅z, y⁆ ∈
      (V ⊓ conjSubgroup V₀ h) ⊔ (conjSubgroup V h ⊓ V₀) := by
    intro z hz
    obtain ⟨hzV, hzW⟩ := Subgroup.mem_inf.1 hz
    have hz' : z ∈ (U ⊔ V₀) ⊓ conjSubgroup (U ⊔ V₀) h := by
      rw [← hinf.1]
      exact Subgroup.mem_inf.2 ⟨hzV, hzW⟩
    have hzy_V₀ : ⁅z, y⁆ ∈ V₀ := hyU z hz'.1
    have hzy_W : ⁅z, y⁆ ∈ conjSubgroup V h := by
      have hyzi : y * z⁻¹ * y⁻¹ ∈ conjSubgroup V h :=
        (Subgroup.mem_normalizer_iff.1 hyW z⁻¹).1 ((conjSubgroup V h).inv_mem hzW)
      have heq : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [heq]
      exact (conjSubgroup V h).mul_mem hzW hyzi
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hzy_W, hzy_V₀⟩)
  have hD : (V ⊓ conjSubgroup V₀ h) ⊔ (conjSubgroup V h ⊓ V₀) ≤
      V ⊓ conjSubgroup V h := by
    refine sup_le ?_ ?_
    · refine le_inf inf_le_left ?_
      exact inf_le_right.trans (E3.conjSubgroup_mono_left h c.cex.hyp.h6.le)
    · refine le_inf (inf_le_right.trans c.cex.hyp.h6.le) inf_le_left
  have hpair := commutator_le_of_pairing (V := V) (W := conjSubgroup V h) (N₁ := U ⊔ V₀)
    (N₂ := conjSubgroup (U ⊔ V₀) h)
    (D := (V ⊓ conjSubgroup V₀ h) ⊔ (conjSubgroup V h ⊓ V₀)) (y := y)
    (fun a ha b hb => B2F.isElemAbelian_comm hV ha hb)
    (fun a ha b hb => B2F.isElemAbelian_comm hW ha hb)
    hU'V (E3.conjSubgroup_mono_left h hU'V) hD hinf.2 hN₁W hVN₂ hyV hyW hyN₁ hyD htriv hfpf
  have hDsup : (V ⊓ conjSubgroup V₀ h) ⊔ (conjSubgroup V h ⊓ V₀) ≤
      V₀ ⊔ conjSubgroup V₀ h :=
    sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left)
  exact hnot (hpair.trans hDsup)

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
