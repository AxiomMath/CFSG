module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Sup
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Alpha

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183k3_diag_lift {Y L A : Subgroup (LGL 2 V)} (hA : A ≤ Y)
    (hAn : A ≤ Subgroup.normalizer (L : Set (LGL 2 V)))
    (hin : alphaA Y L A ≤ alphaL Y L) {a : LGL 2 V} (ha : a ∈ A) :
    ∃ x ∈ L, a * x⁻¹ ∈ alphaC Y L := by
  have hAX : A ≤ alphaX Y L := le_inf hA hAn
  have haX : a ∈ alphaX Y L := ⟨hA ha, hAn ha⟩
  have hmem : alphaMk Y L ⟨a, haX⟩ ∈ alphaA Y L A :=
    Subgroup.mem_map_of_mem (alphaMk Y L) (Subgroup.mem_subgroupOf.mpr ha)
  obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.mp (hin hmem)
  refine ⟨l.1, Subgroup.mem_subgroupOf.mp hl, ?_⟩
  have hker : alphaMk Y L (⟨a, haX⟩ * l⁻¹) = 1 := by
    rw [map_mul, map_inv, hlq, mul_inv_cancel]
  have hC : ⟨a, haX⟩ * l⁻¹ ∈ (alphaC Y L).subgroupOf (alphaX Y L) :=
    (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L)) _).mp hker
  simpa using Subgroup.mem_subgroupOf.mp hC

theorem w183k3_diag_mem_sup {Y T L₁ L₂ A : Subgroup (LGL 2 V)}
    (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ≤ Y)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hin₁ : alphaA Y L₁ A ≤ alphaL Y L₁) (hin₂ : alphaA Y L₂ A ≤ alphaL Y L₂)
    {a : LGL 2 V} (ha : a ∈ A) : a ∈ L₁ ⊔ L₂ := by
  obtain ⟨x, hxL₁, hx⟩ := w183k3_diag_lift hA hAn₁ hin₁ ha
  obtain ⟨y, hyL₂, hy⟩ := w183k3_diag_lift hA hAn₂ hin₂ ha
  have hxY : a * x⁻¹ ∈ Y := (Subgroup.mem_inf.mp hx).1
  have hxC₁ : a * x⁻¹ ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := (Subgroup.mem_inf.mp hx).2
  have hyY : a * y⁻¹ ∈ Y := (Subgroup.mem_inf.mp hy).1
  have hyC₂ : a * y⁻¹ ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := (Subgroup.mem_inf.mp hy).2
  have hxy : x * y = y * x := htwo.comm x hxL₁ y hyL₂
  have hyY' : y⁻¹ ∈ Y := Y.inv_mem (htwo.le₂ hyL₂)
  have hxC₁' : y⁻¹ ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
    (Subgroup.centralizer (L₁ : Set (LGL 2 V))).inv_mem
      (Subgroup.mem_centralizer_iff.mpr fun l hl => htwo.comm l hl y hyL₂)
  have hyC₂' : x⁻¹ ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.centralizer (L₂ : Set (LGL 2 V))).inv_mem
      (Subgroup.mem_centralizer_iff.mpr fun l hl => (htwo.comm x hxL₁ l hl).symm)
  have hdY : (a * x⁻¹) * y⁻¹ ∈ Y := Y.mul_mem hxY hyY'
  have hdC₁ : (a * x⁻¹) * y⁻¹ ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
    (Subgroup.centralizer (L₁ : Set (LGL 2 V))).mul_mem hxC₁ hxC₁'
  have hdC₂ : (a * y⁻¹) * x⁻¹ ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.centralizer (L₂ : Set (LGL 2 V))).mul_mem hyC₂ hyC₂'
  have hd_eq : (a * x⁻¹) * y⁻¹ = (a * y⁻¹) * x⁻¹ := by
    have hc : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hxy]
    rw [show (a * x⁻¹) * y⁻¹ = a * (x⁻¹ * y⁻¹) by group,
      show (a * y⁻¹) * x⁻¹ = a * (y⁻¹ * x⁻¹) by group, hc]
  have hd : (a * x⁻¹) * y⁻¹ ∈ L₁ ⊔ L₂ :=
    htwo.cent _ hdY
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hdC₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp (hd_eq ▸ hdC₂) l hl).symm)
  obtain ⟨u₀, hu₀, v₀, hv₀, huv₀⟩ := w183k3_exists_mul_of_mem_sup htwo.comm hd
  have haeq : a = (u₀ * x) * (v₀ * y) := by
    calc a = ((a * x⁻¹) * y⁻¹) * y * x := by
          show a = ((a * x⁻¹) * y⁻¹) * y * x; group
      _ = (u₀ * v₀) * y * x := by rw [← huv₀]
      _ = (u₀ * x) * (v₀ * y) := by
        rw [show (u₀ * v₀) * y * x = u₀ * (v₀ * (y * x)) by group,
          show y * x = x * y from hxy.symm,
          show v₀ * (x * y) = x * (v₀ * y) by
            rw [← mul_assoc, (htwo.comm x hxL₁ v₀ hv₀).symm, mul_assoc]]
        group
  rw [haeq]
  exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left (L₁.mul_mem hu₀ hxL₁))
    (Subgroup.mem_sup_right (L₂.mul_mem hv₀ hyL₂))

theorem w183k3_diag_split {Y T L₁ L₂ A : Subgroup (LGL 2 V)}
    (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ≤ Y) (hel : IsElemAbelian 2 A)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hin₁ : alphaA Y L₁ A ≤ alphaL Y L₁) (hin₂ : alphaA Y L₂ A ≤ alphaL Y L₂)
    {a : LGL 2 V} (ha : a ∈ A) :
    ∃ x ∈ L₁, ∃ y ∈ L₂, a = x * y ∧ x * x = 1 ∧ y * y = 1 := by
  have hmem := w183k3_diag_mem_sup htwo hA hAn₁ hAn₂ hin₁ hin₂ ha
  obtain ⟨u, hu, v, hv, huv⟩ := w183k3_exists_mul_of_mem_sup htwo.comm hmem
  have huv2 : (u * v) * (u * v) = 1 := by
    rw [huv, ← pow_two]
    exact hel.2 a ha
  obtain ⟨x, hx, y, hy, hxy, hx2, hy2⟩ := w183k3_split_two htwo.comm htwo.odd₁ hu hv huv2
  exact ⟨x, hx, y, hy, huv.symm.trans hxy, hx2, hy2⟩

theorem w183k3_diag_unique {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (htwo : Br3TwoComp Y T L₁ L₂)
    {x x' y y' : LGL 2 V} (hx : x ∈ L₁) (hx' : x' ∈ L₁)
    (hxsq : x * x = 1) (hx'sq : x' * x' = 1)
    (hy : y ∈ L₂) (hy' : y' ∈ L₂)
    (hysq : y * y = 1) (hy'sq : y' * y' = 1)
    (h : x * y = x' * y') : x = x' ∧ y = y' := by
  have hceq : x'⁻¹ * x = y' * y⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have hcL₁ : x'⁻¹ * x ∈ L₁ := L₁.mul_mem (L₁.inv_mem hx') hx
  have hcL₂ : x'⁻¹ * x ∈ L₂ := by
    rw [hceq]
    exact L₂.mul_mem hy' (L₂.inv_mem hy)
  have hc : x'⁻¹ * x ∈ quasiCentre L₁ := by
    rw [mem_quasiCentre]
    exact ⟨hcL₁, fun l hl => (htwo.comm l hl (x'⁻¹ * x) hcL₂).symm⟩
  have hc2 : (x'⁻¹ * x) * (x'⁻¹ * x) = 1 := by
    have hcx' : Commute (x'⁻¹ * x) x' := (mem_quasiCentre.mp hc).2 x' hx'
    have hsq : (x' * (x'⁻¹ * x)) * (x' * (x'⁻¹ * x)) = 1 := by
      rw [show x' * (x'⁻¹ * x) = x from by group]
      exact hxsq
    rw [show (x' * (x'⁻¹ * x)) * (x' * (x'⁻¹ * x)) =
        (x' * x') * ((x'⁻¹ * x) * (x'⁻¹ * x)) by
      rw [show (x' * (x'⁻¹ * x)) * (x' * (x'⁻¹ * x)) =
          x' * ((x'⁻¹ * x) * x') * (x'⁻¹ * x) by group, hcx'.eq]
      group] at hsq
    rw [hx'sq, one_mul] at hsq
    exact hsq
  have hc1 : x'⁻¹ * x = 1 :=
    quasi_centre_two_pow_eq_one htwo.odd₁ hc (k := 1) (by
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
      exact hc2)
  have hx_eq : x = x' := by
    have h1 : x' * (x'⁻¹ * x) = x' := by rw [hc1, mul_one]
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at h1
  have hy_eq : y = y' := by
    have h2 : y' * y⁻¹ = 1 := hceq.symm.trans hc1
    calc y = 1 * y := (one_mul y).symm
      _ = (y' * y⁻¹) * y := by rw [h2]
      _ = y' := by group
  exact ⟨hx_eq, hy_eq⟩

theorem w183k3_diag_comm_of_quot {Y L A : Subgroup (LGL 2 V)}
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (hLY : L ≤ Y) (hA : A ≤ Y) (hAn : A ≤ Subgroup.normalizer (L : Set (LGL 2 V)))
    (hAcomm : ∀ a b : ↥A, a * b = b * a)
    {x y : LGL 2 V} (hx : x ∈ L) (hy : y ∈ L) (hxsq : x * x = 1) (hysq : y * y = 1)
    {a b : ↥A}
    (hxq : alphaMk Y L ⟨x, ⟨hLY hx, L.le_normalizer hx⟩⟩ =
      alphaMk Y L ⟨(a : LGL 2 V), ⟨hA a.2, hAn a.2⟩⟩)
    (hyq : alphaMk Y L ⟨y, ⟨hLY hy, L.le_normalizer hy⟩⟩ =
      alphaMk Y L ⟨(b : LGL 2 V), ⟨hA b.2, hAn b.2⟩⟩) :
    x * y = y * x := by
  have hxX : x ∈ alphaX Y L := ⟨hLY hx, L.le_normalizer hx⟩
  have hyX : y ∈ alphaX Y L := ⟨hLY hy, L.le_normalizer hy⟩
  have hcxL : x * y * x⁻¹ * y⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
  have hcxX : x * y * x⁻¹ * y⁻¹ ∈ alphaX Y L := ⟨hLY hcxL, L.le_normalizer hcxL⟩
  have hcommq : alphaMk Y L ⟨x, hxX⟩ * alphaMk Y L ⟨y, hyX⟩ =
      alphaMk Y L ⟨y, hyX⟩ * alphaMk Y L ⟨x, hxX⟩ := by
    rw [hxq, hyq]
    have h1 : (⟨(a : LGL 2 V), ⟨hA a.2, hAn a.2⟩⟩ : ↥(alphaX Y L)) *
        ⟨(b : LGL 2 V), ⟨hA b.2, hAn b.2⟩⟩ =
        ⟨(b : LGL 2 V), ⟨hA b.2, hAn b.2⟩⟩ *
        ⟨(a : LGL 2 V), ⟨hA a.2, hAn a.2⟩⟩ :=
      Subtype.ext (congrArg (fun u : ↥A => (u : LGL 2 V)) (hAcomm a b))
    simpa only [map_mul] using congrArg (alphaMk Y L) h1
  have hker : alphaMk Y L (⟨x, hxX⟩ * ⟨y, hyX⟩ * ⟨x, hxX⟩⁻¹ * ⟨y, hyX⟩⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcommq]
    group
  have hC : (⟨x, hxX⟩ * ⟨y, hyX⟩ * ⟨x, hxX⟩⁻¹ * ⟨y, hyX⟩⁻¹) ∈
      (alphaC Y L).subgroupOf (alphaX Y L) :=
    (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L)) _).mp hker
  have hvalC : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set (LGL 2 V)) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hC)).2
  have hqc : x * y * x⁻¹ * y⁻¹ ∈ quasiCentre L := by
    rw [mem_quasiCentre]
    exact ⟨hcxL, fun l hl => (Subgroup.mem_centralizer_iff.mp hvalC l hl).symm⟩
  have hcenter : (⟨x, hx⟩ : ↥L) * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ * (⟨y, hy⟩)⁻¹ ∈
      Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact ((mem_quasiCentre.mp hqc).2 (g : LGL 2 V) g.2).symm
  have hs : (⟨x, hx⟩ : ↥L) * ⟨x, hx⟩ = 1 := Subtype.ext (by simpa using hxsq)
  have ht : (⟨y, hy⟩ : ↥L) * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa using hysq)
  exact congrArg Subtype.val (w183k3_comm_of_sq hodd hs ht hcenter)

end CFSG.LocalAnalysis.WeakClosure81

end
