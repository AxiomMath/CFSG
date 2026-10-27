module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecACoprime
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5B0
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_vectors
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) {v : G} (hvU : v ∈ fsuUL T L I)
    (hvC : v ∉ fsuCVM T L I) (hvS : v ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) :
    ∃ w₁ ∈ fsuUL T L I, w₁ ∉ fsuCVM T L I ∧
      w₁ ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ∧
      ∃ w₂ ∈ CFSG.conjugate (fsuUL T L I) t, w₂ ∉ fsuCVM T L I ∧
        w₂ ∈ Subgroup.centralizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) ∧
        ∀ x ∈ D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
          x * w₁ * x⁻¹ * w₁⁻¹ ∈ fsuCVM T L I ∧ x * w₂ * x⁻¹ * w₂⁻¹ ∈ fsuCVM T L I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc := hyp.fsu.maximal.1
  have htM := le_fsuM T L ht
  have hDB := hD.1
  set W := fsuVM T L I ⊓ Subgroup.centralizer (T0 T L : Set G) with hWdef
  have hCN := le_normalizer_fsuCVM T L I
  have hUC := conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have hDL0 : D ≤ fsuL0 T L := fun d hd => (oTwoUpper_le _ (hDB hd)).1
  have hDW : D ≤ Subgroup.normalizer (W : Set G) := hDB.trans (B0_le_normalizer_W T L I)
  have hT0W : T0 T L ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hKD := commutator_B0_le hyp hD hT0W hDW
  have hv2U : t⁻¹ * v * t ∈ CFSG.conjugate (fsuUL T L I) t := conj_mem_conjugate t hvU
  have hv2C : t⁻¹ * v * t ∉ fsuCVM T L I := fun h => hvC (by
    have := (Subgroup.mem_normalizer_iff.mp (hCN htM) _).mp h
    simpa [mul_assoc] using this)
  have hv2S : t⁻¹ * v * t ∈
      Subgroup.centralizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : t * s * t⁻¹ ∈ T ⊓ L :=
      ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht), mem_conjugate_iff.mp hs.2⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hvS _ hs'
    calc s * (t⁻¹ * v * t) = t⁻¹ * (t * s * t⁻¹ * v) * t := by group
      _ = t⁻¹ * (v * (t * s * t⁻¹)) * t := by rw [h1]
      _ = t⁻¹ * v * t * s := by group
  have hvV := fsuUL_le_fsuVM T L I hvU
  have hv2V := conjugate_fsuUL_le (I := I) htM hv2U
  have hvW : v ∈ W := ⟨hvV, mem_centralizer_T0 h37 h38 h322 hyp ht htn hvV hvS
    (Subgroup.centralizer_le (fun _ hx => hx.2) (hUt hvU))⟩
  have hv2W : t⁻¹ * v * t ∈ W := ⟨hv2V, mem_centralizer_T0 h37 h38 h322 hyp ht htn hv2V
    (Subgroup.centralizer_le (fun _ hx => hx.2) (hUC hv2U)) hv2S⟩
  by_cases hK : ⁅W, B0 T L⁆ = ⊥
  ·
    have hcent : ∀ x ∈ B0 T L, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ = 1 := by
      intro x hx w hw
      have h1 : ⁅w, x⁆ = 1 := by
        have h2 := Subgroup.commutator_mem_commutator hw hx
        rw [hK] at h2
        exact h2
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      rw [← h1, mul_inv_cancel_right, mul_inv_cancel]
    refine ⟨v, hvU, hvC, hvS, t⁻¹ * v * t, hv2U, hv2C, hv2S, fun x hx => ?_⟩
    rw [hcent x (hDB hx.1) v hvW, hcent x (hDB hx.1) _ hv2W]
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  set K := ⁅W, B0 T L⁆ with hKdef
  have hKW : K ≤ W :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (B0_le_normalizer_W T L I)
  have hKT : K ≤ T := hKW.trans (inf_le_left.trans (fsuVM_le_T hyp))
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_commutator (le_normalizer_W T L I) (le_normalizer_B0 T L)
  have hT2 : IsPGroup 2 ↥T := hyp.fsu.sylow.1
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  have : (K.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKT).mpr hTK
  have hKne : K.subgroupOf T ≠ ⊥ := by
    intro h
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have h1 : (⟨k, hKT hk⟩ : ↥T) ∈ K.subgroupOf T := Subgroup.mem_subgroupOf.mpr hk
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨⟨z, hzK, hzZ⟩, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hKne)
  have hwK : (z : G) ∈ K := Subgroup.mem_subgroupOf.mp hzK
  have hwT : ∀ r ∈ T, r * (z : G) = (z : G) * r := by
    intro r hr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨r, hr⟩)
  have hw1 : (z : G) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  set w : G := (z : G) with hwdef
  have hwV : w ∈ fsuVM T L I := (hKW hwK).1
  have hwZ : w ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨z.2, Subgroup.mem_centralizer_iff.mpr hwT⟩,
      (isElemAbelian_fsuVM hyp).2 w hwV⟩
  have hwC : w ∉ fsuCVM T L I := by
    intro hC
    have hwD : w ∈ Subgroup.centralizer (D : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun d hd =>
        Subgroup.mem_centralizer_iff.mp hC.2 d (hDL0 hd)
    have hWab : IsMulCommutative ↥W :=
      ⟨⟨fun a b => Subtype.ext (comm_of_mem_fsuVM hyp a.2.1 b.2.1)⟩⟩
    have h1 := commutator_inf_centralizer_eq_bot (W := W) (D := D)
      (fun u hu => (isElemAbelian_fsuVM hyp).2 u hu.1) hD.2.1 hDW
    have h2 : w ∈ ⁅W, D⁆ ⊓ Subgroup.centralizer (D : Set G) := ⟨hKD hwK, hwD⟩
    rw [h1, Subgroup.mem_bot] at h2
    exact hw1 h2
  have hinter := (ha t ht htn).2.1
  have hnot1 : w ∉ fsuUL T L I ⊔ fsuCVM T L I := by
    intro h
    have hle : fsuUL T L I ⊔ fsuCVM T L I ≤ (CFSG.conjugate (fsuUL T L I) t ⊔
        fsuCVM T L I).comap (MulAut.conj t⁻¹).toMonoidHom := by
      refine sup_le (fun u hu => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left (by simpa using conj_mem_conjugate t hu)
      · rw [Subgroup.mem_comap]
        refine Subgroup.mem_sup_right ?_
        have := (Subgroup.mem_normalizer_iff.mp (hCN ((fsuM T L).inv_mem htM)) c).mp hc
        simpa using this
    have h2 := hle h
    rw [Subgroup.mem_comap] at h2
    have hw' : t⁻¹ * w * t = w := by rw [hwT t⁻¹ (T.inv_mem ht), inv_mul_cancel_right]
    have h3 : w ∈ CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I := by
      rw [← hw']
      simpa using h2
    have h4 : w ∈ (fsuUL T L I ⊔ fsuCVM T L I) ⊓ (CFSG.conjugate (fsuUL T L I) t ⊔
        fsuCVM T L I) := ⟨h, h3⟩
    rw [hinter] at h4
    exact hwC h4
  have hnot2 : w ∉ CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I := by
    intro h
    have hle : CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I ≤ (fsuUL T L I ⊔
        fsuCVM T L I).comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun u hu => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left (by simpa using mem_conjugate_iff.mp hu)
      · rw [Subgroup.mem_comap]
        refine Subgroup.mem_sup_right ?_
        have := (Subgroup.mem_normalizer_iff.mp (hCN htM) c).mp hc
        simpa using this
    have h2 := hle h
    rw [Subgroup.mem_comap] at h2
    have hw' : t * w * t⁻¹ = w := by rw [hwT t ht, mul_inv_cancel_right]
    have h3 : w ∈ fsuUL T L I ⊔ fsuCVM T L I := by
      rw [← hw']
      simpa using h2
    have h4 : w ∈ (fsuUL T L I ⊔ fsuCVM T L I) ⊓ (CFSG.conjugate (fsuUL T L I) t ⊔
        fsuCVM T L I) := ⟨h3, h⟩
    rw [hinter] at h4
    exact hwC h4
  obtain ⟨w₁, hw₁U, w₂, hw₂U, hw12⟩ := exists_mul_of_mem_fsuVM h37 h38 hyp ht htn hwV
  have hw₁C : w₁ ∉ fsuCVM T L I := by
    intro h
    apply hnot2
    rw [← hw12]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h) (Subgroup.mem_sup_left hw₂U)
  have hw₂C : w₂ ∉ fsuCVM T L I := by
    intro h
    apply hnot1
    rw [← hw12]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw₁U) (Subgroup.mem_sup_right h)
  have hw₁S : w₁ ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsw : Commute s w := hwT s hs.1
    have hsw₂ : Commute s w₂ := Subgroup.mem_centralizer_iff.mp (hUC hw₂U) s hs.2
    have e : w₁ = w * w₂⁻¹ := by rw [← hw12, mul_inv_cancel_right]
    rw [e]
    exact (hsw.mul_right hsw₂.inv_right).eq
  have hw₂S : w₂ ∈ Subgroup.centralizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsw : Commute s w := hwT s hs.1
    have hsw₁ : Commute s w₁ := Subgroup.mem_centralizer_iff.mp (hUt hw₁U) s hs.2
    have e : w₂ = w₁⁻¹ * w := by rw [← hw12, inv_mul_cancel_left]
    rw [e]
    exact (hsw₁.inv_right.mul_right hsw).eq
  refine ⟨w₁, hw₁U, hw₁C, hw₁S, w₂, hw₂U, hw₂C, hw₂S, fun x hx => ?_⟩
  have hxw : x * w = w * x := (Subgroup.mem_centralizer_iff.mp hx.2 w hwZ).symm
  have hxL0 := hDL0 hx.1
  have hL0U : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fsuL0_le_normalizer_fsuVM T L I) (fsuL0_le_normalizer hloc)
  have hL0Ut : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I) t : Set G) := by
    rw [conjugate_commutator_fsuVM htM]
    exact le_normalizer_commutator (fsuL0_le_normalizer_fsuVM T L I)
      (fsuL0_le_normalizer_conjugate hloc htM)
  have haU : x * w₁ * x⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp (hL0U hxL0) _).mp hw₁U
  have hbU : x * w₂ * x⁻¹ ∈ CFSG.conjugate (fsuUL T L I) t :=
    (Subgroup.mem_normalizer_iff.mp (hL0Ut hxL0) _).mp hw₂U
  have hab : x * w₁ * x⁻¹ * (x * w₂ * x⁻¹) = w₁ * w₂ := by
    calc x * w₁ * x⁻¹ * (x * w₂ * x⁻¹) = x * (w₁ * w₂) * x⁻¹ := by group
      _ = w₁ * w₂ := by rw [hw12, hxw, mul_inv_cancel_right]
  have hc : x * w₁ * x⁻¹ * w₁⁻¹ = w₂ * (x * w₂ * x⁻¹)⁻¹ := by
    have e : x * w₁ * x⁻¹ = w₁ * (w₂ * (x * w₂ * x⁻¹)⁻¹) := by
      rw [← mul_assoc, ← hab, mul_inv_cancel_right]
    have hcomm := comm_of_mem_fsuVM hyp (fsuUL_le_fsuVM T L I hw₁U)
      ((fsuVM T L I).mul_mem (conjugate_fsuUL_le (I := I) htM hw₂U)
        ((fsuVM T L I).inv_mem (conjugate_fsuUL_le (I := I) htM hbU)))
    rw [e, hcomm, mul_inv_cancel_right]
  have hcC : x * w₁ * x⁻¹ * w₁⁻¹ ∈ fsuCVM T L I := by
    refine inf_conjugate_le_fsuCVM hyp ht htn ⟨(fsuUL T L I).mul_mem haU
      ((fsuUL T L I).inv_mem hw₁U), ?_⟩
    rw [hc]
    exact Subgroup.mul_mem _ hw₂U (Subgroup.inv_mem _ hbU)
  refine ⟨hcC, ?_⟩
  have e2 : x * w₂ * x⁻¹ * w₂⁻¹ = (x * w₁ * x⁻¹ * w₁⁻¹)⁻¹ := by rw [hc]; group
  rw [e2]
  exact Subgroup.inv_mem _ hcC

end CFSG.Quasithin.Vol2.Ch10.SecA
