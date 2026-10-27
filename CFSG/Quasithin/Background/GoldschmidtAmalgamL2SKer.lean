module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SCard

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem inf_inf_centralizer_eq_pCoreOf [Finite D] (hn : IsNaturalAt A (A ⊓ B) z V) :
    A ⊓ B ⊓ Subgroup.centralizer (V : Set D) = pCoreOf 2 A := by
  rw [hn.cT, hn.centralizer_eq]
  exact le_antisymm (pCoreOf_le 2 _)
    (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (pCoreOf_isPGroup 2 A))

section Ker

variable [Finite D] (h : Hyp2 A B z V)

include h

theorem Hyp2.QB_inf_centralizer_eq_coreIn :
    pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) =
      coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  apply le_antisymm
  · have hBN : B ≤ Subgroup.normalizer
        ((pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) : Subgroup D) : Set D) :=
      le_normalizer_inf (le_normalizer_pCoreOf 2 B)
        ((le_normalizer_conjClosure V B).trans (normalizer_le_normalizer_centralizer _))
    refine le_coreIn (inf_le_left.trans (pCoreOf_le 2 B)) hBN fun x hx => ⟨?_, hx.1⟩
    have hmem : x ∈ A ⊓ B ⊓ Subgroup.centralizer (V : Set D) :=
      ⟨h.gold.pCoreOf_right_le hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        Subgroup.mem_centralizer_iff.mp hx.2 v (le_conjClosure V B hv)⟩
    rwa [inf_inf_centralizer_eq_pCoreOf h.natural] at hmem
  · intro x hx
    have hxR : x ∈ pCoreOf 2 A ⊓ pCoreOf 2 B := by simpa using hx.2 1 B.one_mem
    refine ⟨hxR.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hUc : conjClosure V B ≤ Subgroup.centralizer ({x} : Set D) := by
      refine conjClosure_le fun k hk v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hq : k⁻¹ * y * k * v = v * (k⁻¹ * y * k) :=
        Subgroup.mem_centralizer_iff.mp (h.natural.le_center hv).2 _ (hx.2 k hk).1
      calc y * (k * v * k⁻¹) = k * ((k⁻¹ * y * k) * v) * k⁻¹ := by group
        _ = k * (v * (k⁻¹ * y * k)) * k⁻¹ := by rw [hq]
        _ = (k * v * k⁻¹) * y := by group
    exact (Subgroup.mem_centralizer_iff.mp (hUc hu) x rfl).symm

theorem Hyp2.B_le_normalizer_K :
    B ≤ Subgroup.normalizer
      ((pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) : Subgroup D) : Set D) := by
  rw [h.QB_inf_centralizer_eq_coreIn]
  exact le_normalizer_coreIn _ _

theorem Hyp2.K_le_R : pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) ≤
    pCoreOf 2 A ⊓ pCoreOf 2 B := by
  rw [h.QB_inf_centralizer_eq_coreIn]
  exact coreIn_le_right _ _

omit [Finite D] in
theorem Hyp2.K_inf_U : (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) ⊓
    conjClosure V B = centerOf (conjClosure V B) := by
  ext u
  constructor
  · rintro ⟨⟨-, hc⟩, hu⟩
    exact ⟨hu, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp hc w hw)⟩
  · rintro ⟨hu, hc⟩
    exact ⟨⟨h.U_le hu, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp hc w hw)⟩, hu⟩

omit [Finite D] in
theorem Hyp2.center_U_le_K : centerOf (conjClosure V B) ≤
    pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
  rw [← h.K_inf_U]
  exact inf_le_left

theorem Hyp2.four_le_card_K :
    4 ≤ Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) := by
  have := Subgroup.card_le_of_le h.center_U_le_K
  rwa [h.card_center_U] at this

theorem Hyp2.z_mem_center_U : z ∈ centerOf (conjClosure V B) := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  exact g.z_mem_center

theorem Hyp2.K_inf_V : (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) ⊓ V =
    Subgroup.zpowers z := by
  apply le_antisymm
  · intro v hv
    have hvU : v ∈ (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) ⊓
        conjClosure V B := ⟨hv.1, le_conjClosure V B hv.2⟩
    rw [h.K_inf_U] at hvU
    have : v ∈ V ⊓ centerOf (conjClosure V B) := ⟨hv.2, hvU⟩
    rwa [h.V_inf_center] at this
  · exact Subgroup.zpowers_le.mpr ⟨h.center_U_le_K h.z_mem_center_U, h.natural.z_mem_V⟩

end Ker

section Pairing

variable (h : Hyp2 A B z V)

include h

theorem Hyp2.z_mul_z : z * z = 1 := by
  have := h.natural.z_sq
  rwa [pow_two] at this

theorem Hyp2.zpowers_sq (w : ↥(Subgroup.zpowers z)) : w * w = 1 := by
  apply Subtype.ext
  show (w : D) * (w : D) = 1
  rcases h.mem_zpowers w.2 with e | e
  · rw [e, mul_one]
  · rw [e]; exact h.z_mul_z

@[expose] def Hyp2.commHom {p : D} (hp : p ∈ conjClosure V B) :
    ↥(pCoreOf 2 B) →* ↥(Subgroup.zpowers z) where
  toFun q := ⟨p * q * p⁻¹ * (q : D)⁻¹, h.comm_UQ hp q.2⟩
  map_one' := by
    apply Subtype.ext
    show p * (1 : D) * p⁻¹ * (1 : D)⁻¹ = 1
    group
  map_mul' q q' := by
    apply Subtype.ext
    show p * ((q : D) * q') * p⁻¹ * ((q : D) * q')⁻¹ =
      (p * q * p⁻¹ * (q : D)⁻¹) * (p * q' * p⁻¹ * (q' : D)⁻¹)
    have hu := h.comm_UQ hp q'.2
    have hq : (q : D) * (p * q' * p⁻¹ * (q' : D)⁻¹) = (p * q' * p⁻¹ * (q' : D)⁻¹) * q :=
      h.zpowers_comm (pCoreOf_le 2 B q.2) hu
    calc p * ((q : D) * q') * p⁻¹ * ((q : D) * q')⁻¹
        = (p * q * p⁻¹ * (q : D)⁻¹) * ((q : D) * (p * q' * p⁻¹ * (q' : D)⁻¹) * (q : D)⁻¹) := by
          group
      _ = (p * q * p⁻¹ * (q : D)⁻¹) * (p * q' * p⁻¹ * (q' : D)⁻¹) := by rw [hq]; group

theorem Hyp2.commHom_apply {p : D} (hp : p ∈ conjClosure V B) (q : ↥(pCoreOf 2 B)) :
    ((h.commHom hp q : ↥(Subgroup.zpowers z)) : D) = p * q * p⁻¹ * (q : D)⁻¹ := rfl

end Pairing

section Card

variable [Finite D] {x a a₁ a₂ : D}

@[expose] def Gen.comm3 (g : Gen A B z V x a a₁ a₂) :
    ↥(pCoreOf 2 B) →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) :=
  (g.hyp.commHom g.a_mem_U).prod
    ((g.hyp.commHom g.a₁_mem_U).prod (g.hyp.commHom g.a₂_mem_U))

theorem Gen.mem_ker_comm3 (g : Gen A B z V x a a₁ a₂) (q : ↥(pCoreOf 2 B)) :
    q ∈ (Gen.comm3 g).ker ↔
      (q : D) ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
  have hcomm : ∀ {p : D} (hp : p ∈ conjClosure V B),
      (g.hyp.commHom hp q = 1 ↔ p * (q : D) = (q : D) * p) := by
    intro p hp
    constructor
    · intro h1
      have h2 := congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) h1
      simp only [Hyp2.commHom_apply, OneMemClass.coe_one] at h2
      calc p * (q : D) = (p * q * p⁻¹ * (q : D)⁻¹) * ((q : D) * p) := by group
        _ = (q : D) * p := by rw [h2, one_mul]
    · intro h1
      apply Subtype.ext
      rw [Hyp2.commHom_apply]
      calc p * (q : D) * p⁻¹ * (q : D)⁻¹ = ((q : D) * p) * p⁻¹ * (q : D)⁻¹ := by rw [h1]
        _ = 1 := by group
  constructor
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    have h1 : g.hyp.commHom g.a_mem_U q = 1 := congrArg Prod.fst hq
    have h2 : g.hyp.commHom g.a₁_mem_U q = 1 := congrArg (fun w => w.2.1) hq
    have h3 : g.hyp.commHom g.a₂_mem_U q = 1 := congrArg (fun w => w.2.2) hq
    refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hle : conjClosure V B ≤ Subgroup.centralizer ({(q : D)} : Set D) := by
      rw [g.U_eq_closure, Subgroup.closure_le]
      intro w hw
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact ((hcomm g.a_mem_U).mp h1).symm
      · exact g.hyp.z_comm (pCoreOf_le 2 B q.2)
      · exact ((hcomm g.a₁_mem_U).mp h2).symm
      · exact ((hcomm g.a₂_mem_U).mp h3).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) (q : D) rfl).symm
  · intro hq
    rw [MonoidHom.mem_ker]
    have hc : ∀ {p : D}, p ∈ conjClosure V B → p * (q : D) = (q : D) * p := fun {p} hp =>
      Subgroup.mem_centralizer_iff.mp hq.2 p hp
    exact Prod.ext ((hcomm g.a_mem_U).mpr (hc g.a_mem_U))
      (Prod.ext ((hcomm g.a₁_mem_U).mpr (hc g.a₁_mem_U))
        ((hcomm g.a₂_mem_U).mpr (hc g.a₂_mem_U)))

theorem Gen.card_QB_le (g : Gen A B z V x a a₁ a₂) :
    Nat.card ↥(pCoreOf 2 B) ≤
      8 * Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) := by
  have hmul := Subgroup.card_ker_mul_card_range (Gen.comm3 g)
  have hker : Nat.card (Gen.comm3 g).ker =
      Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) := by
    have hmap : (Gen.comm3 g).ker.map (pCoreOf 2 B).subtype =
        pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (Gen.mem_ker_comm3 g q).mp hq
      · intro hy
        exact ⟨⟨y, hy.1⟩, (Gen.mem_ker_comm3 g ⟨y, hy.1⟩).mpr hy, rfl⟩
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (pCoreOf 2 B).subtype_injective).symm
  have hrange : Nat.card (Gen.comm3 g).range ≤ 8 := by
    have h1 := Subgroup.card_le_card_group (Gen.comm3 g).range
    have h2 : Nat.card (↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z)) =
        8 := by
      rw [Nat.card_prod, Nat.card_prod, g.hyp.card_zpowers]
    omega
  calc Nat.card ↥(pCoreOf 2 B) = Nat.card (Gen.comm3 g).ker * Nat.card (Gen.comm3 g).range :=
        hmul.symm
    _ ≤ Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) * 8 :=
        Nat.mul_le_mul (le_of_eq hker) hrange
    _ = 8 * Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) :=
        mul_comm _ _

theorem Gen.sq_mem_K (g : Gen A B z V x a a₁ a₂) {q : D} (hq : q ∈ pCoreOf 2 B) :
    q * q ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
  have hmem : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥(pCoreOf 2 B)) ∈ (Gen.comm3 g).ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact Prod.ext (g.hyp.zpowers_sq _) (Prod.ext (g.hyp.zpowers_sq _) (g.hyp.zpowers_sq _))
  exact (Gen.mem_ker_comm3 g _).mp hmem

section Hyp

variable (h : Hyp2 A B z V)

include h

theorem Hyp2.card_QB_le :
    Nat.card ↥(pCoreOf 2 B) ≤
      8 * Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  exact g.card_QB_le

theorem Hyp2.sq_mem_K {q : D} (hq : q ∈ pCoreOf 2 B) :
    q * q ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  exact g.sq_mem_K hq

theorem Hyp2.card_T_QB : Nat.card ↥(A ⊓ B) = 2 * Nat.card ↥(pCoreOf 2 B) := by
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 B) (A ⊓ B)
  rw [inf_eq_left.mpr h.gold.pCoreOf_right_le, h.gold.relIndex_pCoreOf_T_right] at e
  exact e.symm

theorem Hyp2.card_T_QA : Nat.card ↥(A ⊓ B) = 2 * Nat.card ↥(pCoreOf 2 A) := by
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 A) (A ⊓ B)
  rw [inf_eq_left.mpr h.gold.pCoreOf_left_le, h.gold.relIndex_pCoreOf_T_left] at e
  exact e.symm

theorem Hyp2.card_T_R :
    Nat.card ↥(A ⊓ B) = 4 * Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) := by
  have hne := h.natural.pCoreOf_ne h.gold
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 A ⊓ pCoreOf 2 B) (A ⊓ B)
  rw [inf_eq_left.mpr (inf_le_left.trans h.gold.pCoreOf_left_le),
    h.gold.relIndex_inf_pCoreOf hne] at e
  exact e.symm

end Hyp

end Card

end GoldAmL2S

end F6

end CFSG.Quasithin
