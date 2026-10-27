module

public import CFSG.Quasithin.H13.L32A724a
public import CFSG.Quasithin.H13.L32A720a

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

omit [Finite G] in
theorem mem_normalizer_sup' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_sup, hA, hB]

theorem relIndex_sup_sup {A B R : Subgroup G} (hBA : B ≤ A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hAR' : A ⊓ R ≤ B) :
    (B ⊔ R).relIndex (A ⊔ R) = B.relIndex A := by
  have m := Subgroup.relIndex_mul_relIndex R (B ⊔ R) (A ⊔ R) le_sup_right
    (sup_le_sup_right hBA R)
  rw [relIndex_sup_eq hAR, relIndex_sup_eq (hBA.trans hAR)] at m
  have hAB : A ⊓ R = B ⊓ R := le_antisymm (le_inf hAR' inf_le_right) (inf_le_inf_right R hBA)
  have m2 := Subgroup.relIndex_mul_relIndex (A ⊓ R) B A hAR' hBA
  rw [hAB] at m2
  have hne : (B ⊓ R).relIndex B ≠ 0 := by
    show ((B ⊓ R).subgroupOf B).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  rw [hAB, ← m2] at m
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) m

theorem relIndex_le_of_le {Y F X : Subgroup G} (hYF : Y ≤ F) (hFX : F ≤ X) :
    F.relIndex X ≤ Y.relIndex X := by
  have m := Subgroup.relIndex_mul_relIndex Y F X hYF hFX
  have hne : Y.relIndex F ≠ 0 := by
    show (Y.subgroupOf F).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  rw [← m]
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)

theorem p_le_l1 (C : Ctx722 G T L V H γ γ' g k) :
    pCoreOf 2 (oTwoUpper H) ≤ L32A.l1 T L V := by
  rw [← C.o2_l1]
  exact pCoreOf_le 2 _

theorem relIndex_inf_centralizer_le (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    {A Z : Subgroup G} (hA : A ≤ pCoreOf 2 H) (hZU : Z ≤ fsuU T V)
    (hAZ : Z ≤ Subgroup.centralizer (A : Set G)) :
    (A ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex A ≤ Z.relIndex (fsuU T V) := by
  have hUe : IsElemAbelian 2 (conjClosure V H) := fsuU_eq_h C D ▸ D.elem_u
  have key := card_mul_card_inf_centralizer C.hypF98.toHypF91 hUe hA (fsuU_eq_h C D).le
  have hZle : Nat.card Z ≤ Nat.card ↥(fsuU T V ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.card_le_of_le (le_inf hZU hAZ)
  have r1 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (fsuU T V : Set G)) A
  rw [inf_eq_left.mpr inf_le_left] at r1
  have r2 := Subgroup.relIndex_mul_card Z (fsuU T V)
  rw [inf_eq_left.mpr hZU] at r2
  have hp1 : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (fsuU T V : Set G)) := Nat.card_pos
  have hp2 : 0 < Nat.card Z := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hp1 hp2)
  calc (A ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex A *
        (Nat.card ↥(A ⊓ Subgroup.centralizer (fsuU T V : Set G)) * Nat.card Z)
      = Nat.card A * Nat.card Z := by rw [← mul_assoc, r1]
    _ ≤ Nat.card A * Nat.card ↥(fsuU T V ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul_left _ hZle
    _ = Nat.card ↥(fsuU T V) * Nat.card ↥(A ⊓ Subgroup.centralizer (fsuU T V : Set G)) := key
    _ = Z.relIndex (fsuU T V) *
        (Nat.card ↥(A ⊓ Subgroup.centralizer (fsuU T V : Set G)) * Nat.card Z) := by
        rw [← r2]; ring

theorem relIndex_s_inf_p_le (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex
      (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H)) ≤ 4 := by
  rw [← C.relIndex_eu]
  refine relIndex_inf_centralizer_le C D (inf_le_right.trans p_le_qh) (e_le_u C D) fun e he => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  exact Subgroup.mem_centralizer_iff.mp (C.r_center (le_conjClosure _ L he)).2 x hx.1

theorem u_inf_centralizer_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper H) : Set G) = fsuV1 T V := by
  rcases C.irred_u _ (le_inf v1_le_u fun v hv => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (v1_comm C ((pCoreOf_le 2 _).trans (oTwoUpper_le H) hx) hv))
    inf_le_left (fun y hy => F7.mem_normalizer_inf (le_normalizer_u C D (oTwoUpper_le H hy))
      (mem_normalizer_centralizer' (le_normalizer_p (oTwoUpper_le H hy)))) with h | h
  · exact h
  · exfalso
    have heq : pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) =
        pCoreOf 2 (oTwoUpper H) := by
      refine le_antisymm inf_le_left fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.mpr
        fun u hu => ?_⟩
      have hu' : u ∈ fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper H) : Set G) := by
        rw [h]; exact hu
      exact (Subgroup.mem_centralizer_iff.mp hu'.2 x hx).symm
    have h1 := C.relIndex_pc
    rw [heq, Subgroup.relIndex_self] at h1
    norm_num at h1

theorem ualpha_le_s (C : Ctx722 G T L V H γ γ' g k) :
    conjSub (k : G) (F8.Uγ V H (g : G)) ≤ L32A.sL T L V := by
  obtain ⟨l, hl, he⟩ := C.ualpha_mem
  rw [he]
  rintro _ ⟨u, hu, rfl⟩
  exact mem_conjClosure hl hu

theorem exists_mem_s_inf_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ∃ x ∈ L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H), x ∉ Subgroup.centralizer (fsuU T V : Set G) := by
  by_contra hall
  push Not at hall
  have hUαS := ualpha_le_s C
  have hUαH : ∀ {a : G}, a ∈ conjSub (k : G) (F8.Uγ V H (g : G)) → a ∈ H := fun ha =>
    s_le_h C D (hUαS ha)
  have key : ∀ p ∈ pCoreOf 2 (oTwoUpper H), ∀ a ∈ conjSub (k : G) (F8.Uγ V H (g : G)),
      ∀ u ∈ fsuU T V, p * (u * (a⁻¹ * u * a)⁻¹) * p⁻¹ * (u * (a⁻¹ * u * a)⁻¹)⁻¹ = 1 := by
    intro p hp a ha u hu
    have hpH : p ∈ H := (pCoreOf_le 2 _).trans (oTwoUpper_le H) hp
    have haH := hUαH ha
    have huH := u_le_h C hu
    set v := a⁻¹ * u * a with hv
    have hvU : v ∈ fsuU T V := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D (inv_mem haH)) u).mp hu
      simpa [hv] using this
    have hvH := u_le_h C hvU
    have hxS : p * a * p⁻¹ * a⁻¹ ∈ L32A.sL T L V := mul_mem
      (conj_mem_s (l1_le_l D (p_le_l1 C hp)) (hUαS ha)) (inv_mem (hUαS ha))
    have hxP : p * a * p⁻¹ * a⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
      have h1 : a * p⁻¹ * a⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_p haH) _).mp (inv_mem hp)
      have e : p * a * p⁻¹ * a⁻¹ = p * (a * p⁻¹ * a⁻¹) := by group
      rw [e]
      exact mul_mem hp h1
    have hx := hall _ ⟨hxS, hxP⟩
    have hxu : (p * a * p⁻¹ * a⁻¹) * u = u * (p * a * p⁻¹ * a⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hx u hu).symm
    set φ := p⁻¹ * v * p * v⁻¹ with hφ
    have hφV : φ ∈ fsuV1 T V := by
      have := comm_mem_v1 C D (inv_mem (p_le_qh hp)) hvU
      simpa [hφ] using this
    have e1 : p * u * p⁻¹ = φ⁻¹ * u := by
      have h1 : (p * a * p⁻¹ * a⁻¹) * u * (p * a * p⁻¹ * a⁻¹)⁻¹ = u := by
        rw [hxu, mul_inv_cancel_right]
      have e : (p * a * p⁻¹ * a⁻¹) * u * (p * a * p⁻¹ * a⁻¹)⁻¹ = p * (a * (φ * v) * a⁻¹) * p⁻¹ := by
        rw [hφ, hv]; group
      rw [e] at h1
      have e2 : a * (φ * v) * a⁻¹ = φ * u := by
        calc a * (φ * v) * a⁻¹ = (a * φ * a⁻¹) * (a * v * a⁻¹) := by group
          _ = φ * u := by rw [conj_v1 C haH hφV, hv]; group
      rw [e2] at h1
      have e3 : p * (φ * u) * p⁻¹ = φ * (p * u * p⁻¹) := by
        calc p * (φ * u) * p⁻¹ = (p * φ * p⁻¹) * (p * u * p⁻¹) := by group
          _ = φ * (p * u * p⁻¹) := by rw [conj_v1 C hpH hφV]
      rw [e3] at h1
      calc p * u * p⁻¹ = φ⁻¹ * (φ * (p * u * p⁻¹)) := by group
        _ = φ⁻¹ * u := by rw [h1]
    have e4 : p * v⁻¹ * p⁻¹ = v⁻¹ * φ := by
      have h2 : p * φ * p⁻¹ = φ := conj_v1 C hpH hφV
      have e : p * φ * p⁻¹ = v * p * v⁻¹ * p⁻¹ := by rw [hφ]; group
      rw [e] at h2
      calc p * v⁻¹ * p⁻¹ = v⁻¹ * (v * p * v⁻¹ * p⁻¹) := by group
        _ = v⁻¹ * φ := by rw [h2]
    have huvH : u * v⁻¹ ∈ H := mul_mem huH (inv_mem hvH)
    have e5 : p * (u * v⁻¹) * p⁻¹ = u * v⁻¹ := by
      calc p * (u * v⁻¹) * p⁻¹ = (p * u * p⁻¹) * (p * v⁻¹ * p⁻¹) := by group
        _ = φ⁻¹ * u * (v⁻¹ * φ) := by rw [e1, e4]
        _ = φ⁻¹ * (u * v⁻¹ * φ) := by group
        _ = φ⁻¹ * (φ * (u * v⁻¹)) := by rw [v1_comm C huvH hφV]
        _ = u * v⁻¹ := by group
    rw [e5, mul_inv_cancel]
  have hcomm : ⁅fsuU T V, conjSub (k : G) (F8.Uγ V H (g : G))⁆ ≤ fsuV1 T V := by
    rw [Subgroup.commutator_le]
    intro u hu a ha
    rw [commutatorElement_def]
    have haH := hUαH ha
    have hw : u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹ ∈ fsuU T V := by
      refine mul_mem hu (inv_mem ?_)
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D haH) u).mp hu
      simpa using this
    have hwP : u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹ ∈
        Subgroup.centralizer (pCoreOf 2 (oTwoUpper H) : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
      have h1 := key p hp a⁻¹ (inv_mem ha) u hu
      calc p * (u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹)
          = (p * (u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹) * p⁻¹ * (u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹)⁻¹) *
            (u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹) * p := by group
        _ = u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹ * p := by rw [h1, one_mul]
    have h2 : u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹ ∈ fsuV1 T V := by
      rw [← u_inf_centralizer_p C D]
      exact ⟨hw, hwP⟩
    have e : u * a * u⁻¹ * a⁻¹ = u * ((a⁻¹)⁻¹ * u * a⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  have hVV : V ≤ fsuV1 T V := (le_of_eq C.comm_ualpha.symm).trans (sup_le hcomm le_rfl)
  have h8 := Subgroup.card_le_of_le hVV
  rw [D.card_v, D.card_v1] at h8
  norm_num at h8

theorem s_le_normalizer_s_inf_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    L32A.sL T L V ≤ Subgroup.normalizer
      ((L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) : Subgroup G) : Set G) := fun _ hs =>
  F7.mem_normalizer_inf (Subgroup.le_normalizer hs) (le_normalizer_p (s_le_h C D hs))

theorem s_le_normalizer_s_inf_pc (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    L32A.sL T L V ≤ Subgroup.normalizer ((L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓
      Subgroup.centralizer (fsuU T V : Set G) : Subgroup G) : Set G) := fun _ hs =>
  F7.mem_normalizer_inf (s_le_normalizer_s_inf_p C D hs)
    (mem_normalizer_centralizer' (le_normalizer_u C D (s_le_h C D hs)))

theorem c_mem_normalizer_s_inf_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    c ∈ Subgroup.normalizer ((L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) : Subgroup G) : Set G) :=
  F7.mem_normalizer_inf (le_normalizer_conjClosure _ L D.c_L) (le_normalizer_p (c_mem_h C D))

theorem c_mem_normalizer_s_inf_pc (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    c ∈ Subgroup.normalizer ((L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓
      Subgroup.centralizer (fsuU T V : Set G) : Subgroup G) : Set G) :=
  F7.mem_normalizer_inf (c_mem_normalizer_s_inf_p C D)
    (mem_normalizer_centralizer' (le_normalizer_u C D (c_mem_h C D)))

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {X : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) (hy : y ∈ X) : x * y * x⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp hx y).mp hy

theorem nu_le_four (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    (cfix c (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊔
        conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔
      (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) ⊔
        conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)).relIndex
      (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ≤
      4 := by
  set R := conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L with hR
  set A := L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) with hA
  set B := L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G)
    with hB
  have hBA : B ≤ A := inf_le_left
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans (s_le_normalizer_r C)
  have hAR' : A ⊓ R ≤ B := fun x hx => ⟨hx.1, r_le_centralizer_u C hx.2⟩
  have h1 : (cfix c (A ⊔ R) ⊔ (B ⊔ R)).relIndex (A ⊔ R) ≤ (B ⊔ R).relIndex (A ⊔ R) :=
    relIndex_le_of_le le_sup_right (sup_le (fun x hx => (mem_cfix.mp hx).1)
      (sup_le_sup_right hBA R))
  rw [relIndex_sup_sup hBA hAR hAR'] at h1
  exact h1.trans (relIndex_s_inf_p_le C D)

theorem one_lt_nu (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    1 < (cfix c (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊔
        conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔
      (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) ⊔
        conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)).relIndex
      (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) := by
  set R := conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L with hR
  set A := L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) with hA
  set B := L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G)
    with hB
  have hRS := r_le_s C D
  have hBA : B ≤ A := inf_le_left
  have hBR : B ≤ Subgroup.normalizer (R : Set G) :=
    (hBA.trans inf_le_left).trans (s_le_normalizer_r C)
  have hAS : A ⊔ R ≤ L32A.sL T L V := sup_le inf_le_left hRS
  have hBS : B ⊔ R ≤ L32A.sL T L V := (sup_le_sup_right hBA R).trans hAS
  have h3 := not_three_dvd_card ((isPGroup_s C D).to_le hBS)
  have hcY : ∀ y ∈ B ⊔ R, c * y * c⁻¹ ∈ B ⊔ R := fun y hy =>
    conj_mem_of_mem_normalizer (mem_normalizer_sup' (c_mem_normalizer_s_inf_pc C D)
      (le_normalizer_r D.c_L)) hy
  have hXY : A ⊔ R ≤ Subgroup.normalizer ((B ⊔ R : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup' (s_le_normalizer_s_inf_pc C D (hAS hx)) (s_le_normalizer_r C (hAS hx))
  have hF := mem_cfix_sup_iff D.c3 (sup_le_sup_right hBA R) h3 hcY hXY
  obtain ⟨x, hx, hxC⟩ := exists_mem_s_inf_p C D
  refine lt_of_le_of_ne (Nat.pos_of_ne_zero ?_) fun h1 => hxC ?_
  · show ((cfix c (A ⊔ R) ⊔ (B ⊔ R)).subgroupOf (A ⊔ R)).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  · have hxF : x ∈ cfix c (A ⊔ R) ⊔ (B ⊔ R) :=
      Subgroup.relIndex_eq_one.mp h1.symm (Subgroup.mem_sup_left hx)
    obtain ⟨-, hcx⟩ := (hF x).mp hxF
    have hcxP : c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
      mul_mem (conj_mem_of_mem_normalizer (le_normalizer_p (c_mem_h C D)) hx.2) (inv_mem hx.2)
    have hBR' : ((B ⊔ R : Subgroup G) : Set G) = (B : Set G) * (R : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B R hBR
    have hcx' : c * x * c⁻¹ * x⁻¹ ∈ ((B ⊔ R : Subgroup G) : Set G) := hcx
    rw [hBR'] at hcx'
    obtain ⟨b, hb, r, hr, hbr⟩ := hcx'
    have hrP : r ∈ pCoreOf 2 (oTwoUpper H) := by
      have e : r = b⁻¹ * (c * x * c⁻¹ * x⁻¹) := by rw [← hbr]; group
      rw [e]
      exact mul_mem (inv_mem hb.1.2) hcxP
    refine fpf_pc C D hx.2 ?_
    rw [← hbr]
    exact mul_mem hb.2 (r_le_centralizer_u C hr)

theorem nu_s (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (hi : ⁅H ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper H⁆ ≤ fsuU T V) :
    (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
        (L32A.sL T L V) =
      4 * (cfix c (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊔
          conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔
        (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) ⊔
          conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)).relIndex
        (L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) ⊔
          conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) := by
  set S := L32A.sL T L V with hS
  set R := conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L with hR
  set A := S ⊓ pCoreOf 2 (oTwoUpper H) with hA
  set B := S ⊓ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) with hB
  set U := fsuU T V with hU
  have hRS : R ≤ S := r_le_s C D
  have hBA : B ≤ A := inf_le_left
  have hAS : A ⊔ R ≤ S := sup_le inf_le_left hRS
  have hBS : B ⊔ R ≤ S := (sup_le_sup_right hBA R).trans hAS
  have hUB : U ≤ B := fun u hu => ⟨⟨u_le_s hu, u_le_p C D hu⟩,
    Subgroup.mem_centralizer_iff.mpr fun u' hu' => u_comm C hu' hu⟩
  have hUS : U ⊔ R ≤ S := (sup_le_sup_right hUB R).trans hBS
  have hSR := s_le_normalizer_r C
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := le_normalizer_r D.c_L
  have hcU : c ∈ Subgroup.normalizer (U : Set G) := le_normalizer_u C D (c_mem_h C D)
  have hNA : S ≤ Subgroup.normalizer ((A ⊔ R : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_sup' (s_le_normalizer_s_inf_p C D hs) (hSR hs)
  have hNB : S ≤ Subgroup.normalizer ((B ⊔ R : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_sup' (s_le_normalizer_s_inf_pc C D hs) (hSR hs)
  have hNU : S ≤ Subgroup.normalizer ((U ⊔ R : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_sup' (le_normalizer_u C D (s_le_h C D hs)) (hSR hs)
  have hcfix : ∀ X : Subgroup G, X ≤ S → cfix c X ≤ S := fun X hX x hx => hX (mem_cfix.mp hx).1
  have m1 := relIndex_cfix_sup_mul c le_sup_right hAS (hcfix S le_rfl |>.trans hSR)
    (hcfix S le_rfl |>.trans hNA)
  have m2 := relIndex_cfix_sup_mul c (Y := R) (Z := B ⊔ R) (X := A ⊔ R) le_sup_right
    (sup_le_sup_right hBA R) ((hcfix _ hAS).trans hSR) ((hcfix _ hAS).trans hNB)
  have m3 := relIndex_cfix_sup_mul c (Y := R) (Z := U ⊔ R) (X := B ⊔ R) le_sup_right
    (sup_le_sup_right hUB R) ((hcfix _ hBS).trans hSR) ((hcfix _ hBS).trans hNU)
  have v1 : cfix c S ⊔ (A ⊔ R) = S := by
    refine cfix_sup_eq_of_comm_le D.c3 hAS (not_three_dvd_card ((isPGroup_s C D).to_le hAS))
      (fun y hy => conj_mem_of_mem_normalizer
        (mem_normalizer_sup' (c_mem_normalizer_s_inf_p C D) hcR) hy) hNA fun s hs => ?_
    exact Subgroup.mem_sup_left (comm_mem_p_of_mem_l1 C D D.c_mem hs)
  have v3 : cfix c (B ⊔ R) ⊔ (U ⊔ R) = B ⊔ R := by
    refine cfix_sup_eq_of_comm_le D.c3 (sup_le_sup_right hUB R)
      (not_three_dvd_card ((isPGroup_s C D).to_le hUS))
      (fun y hy => conj_mem_of_mem_normalizer (mem_normalizer_sup' hcU hcR) hy)
      (fun x hx => hNU (hBS hx)) fun s hs => ?_
    have hBR' : ((B ⊔ R : Subgroup G) : Set G) = (B : Set G) * (R : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B R ((hBA.trans inf_le_left).trans hSR)
    have hs' : s ∈ ((B ⊔ R : Subgroup G) : Set G) := hs
    rw [hBR'] at hs'
    obtain ⟨b, hb, r, hr, rfl⟩ := hs'
    have hbH : b ∈ H := s_le_h C D hb.1.1
    have hcb : c * b * c⁻¹ * b⁻¹ ∈ U := by
      have h1 := hi (Subgroup.commutator_mem_commutator (⟨hbH, hb.2⟩ :
        b ∈ H ⊓ Subgroup.centralizer (fsuU T V : Set G)) (c_mem_k C D))
      rw [commutatorElement_def] at h1
      have e : c * b * c⁻¹ * b⁻¹ = (b * c * b⁻¹ * c⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h1
    have hcr : b * (c * r * c⁻¹ * r⁻¹) * b⁻¹ ∈ R :=
      conj_mem_of_mem_normalizer (hSR hb.1.1) (mul_mem (conj_mem_of_mem_normalizer hcR hr)
        (inv_mem hr))
    have e : c * (b * r) * c⁻¹ * (b * r)⁻¹ =
        (c * b * c⁻¹ * b⁻¹) * (b * (c * r * c⁻¹ * r⁻¹) * b⁻¹) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hcb) (Subgroup.mem_sup_right hcr)
  have v4 : cfix c (U ⊔ R) ⊔ R = R := by
    refine cfix_sup_eq_of_fpf' fun s hs hcs => ?_
    have hUR' : ((U ⊔ R : Subgroup G) : Set G) = (U : Set G) * (R : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right U R (u_le_s.trans hSR)
    have hs' : s ∈ ((U ⊔ R : Subgroup G) : Set G) := hs
    rw [hUR'] at hs'
    obtain ⟨u, hu, r, hr, rfl⟩ := hs'
    have hcr : u * (c * r * c⁻¹ * r⁻¹) * u⁻¹ ∈ R :=
      conj_mem_of_mem_normalizer (hSR (u_le_s hu)) (mul_mem (conj_mem_of_mem_normalizer hcR hr)
        (inv_mem hr))
    have e : c * (u * r) * c⁻¹ * (u * r)⁻¹ =
        (c * u * c⁻¹ * u⁻¹) * (u * (c * r * c⁻¹ * r⁻¹) * u⁻¹) := by group
    rw [e] at hcs
    have hcu : c * u * c⁻¹ * u⁻¹ ∈ R := by
      have := mul_mem hcs (inv_mem hcr)
      rwa [mul_inv_cancel_right] at this
    have huE : u ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
      refine fpf_ue C D hu ?_
      rw [← u_inf_r C D]
      exact Subgroup.mem_inf.mpr ⟨mul_mem (conj_mem_of_mem_normalizer hcU hu) (inv_mem hu), hcu⟩
    exact mul_mem (le_conjClosure _ L huE) hr
  have h4 : (cfix c (U ⊔ R) ⊔ R).relIndex (U ⊔ R) = 4 := by
    rw [v4, relIndex_sup_eq (u_le_s.trans hSR), u_inf_r C D, C.relIndex_eu]
  rw [m1, v1, Subgroup.relIndex_self, one_mul, m2, m3, v3, Subgroup.relIndex_self, one_mul, h4,
    mul_comm]

theorem isoMod_core_s (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (hi : ⁅H ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper H⁆ ≤ fsuU T V)
    [(Subgroup.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) (L32A.sL T L V)).Normal] :
    ∃ ρ : Γ →* AddMonoid.End (Additive (↥(L32A.sL T L V) ⧸
        Subgroup.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) (L32A.sL T L V))),
      (∀ (l : ↥L) (s : ↥(L32A.sL T L V)),
        ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
          Additive.ofMul (QuotientGroup.mk ((secMod_s C D).conjX l s))) ∧ IsoMod ρ ρCore := by
  obtain ⟨ρ, hρ, hcases⟩ := lemma14_7_24_cases C D
  refine ⟨ρ, hρ, ?_⟩
  have hν := nu_s C D hi
  have hlo := one_lt_nu C D
  have hhi := nu_le_four C D
  set ν := (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
    (L32A.sL T L V) with hνdef
  have hmul := Subgroup.relIndex_mul_relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)
    (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) (L32A.sL T L V)
    le_sup_right (sup_le (fun x hx => (mem_cfix.mp hx).1) (r_le_s C D))
  have hne : (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
      (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ≠ 0 := by
    show (Subgroup.subgroupOf _ _).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have key : ∀ n : ℕ, (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex (L32A.sL T L V) =
      n * (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L).relIndex
        (cfix c (L32A.sL T L V) ⊔ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) → ν = n := by
    intro n hn
    rw [← hmul, mul_comm n] at hn
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hn
  rcases hcases with ⟨-, h⟩ | ⟨hiso, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · have := key 4 h; omega
  · exact hiso
  · have := key 64 h; omega
  · have := key 256 h; omega
  · have := key 1024 h; omega

end CFSG.Quasithin.H13.S4
