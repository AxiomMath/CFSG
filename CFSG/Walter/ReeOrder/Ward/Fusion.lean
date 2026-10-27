module

public import CFSG.Walter.ReeOrder.Ward.Defs
public import CFSG.Walter.ReeOrder.Ward.Quaternion
public import CFSG.Walter.ReeOrder.JT.Section2
public import Mathlib.Data.Int.Star

public section

open scoped MatrixGroups Pointwise

namespace CFSG.Walter.Ward

open CFSG

variable {G : Type} [Group G]

@[expose] def prodJ (J : G) (hJ : J * J = 1) (H : Subgroup G) (hc : ∀ x ∈ H, x * J = J * x) :
    Subgroup G where
  carrier := {x | x ∈ H ∨ J * x ∈ H}
  one_mem' := Or.inl H.one_mem
  mul_mem' := by
    have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (H.mul_mem hx hy)
    · right
      rw [← mul_assoc, ← hc x hx, mul_assoc]
      exact H.mul_mem hx hy
    · right
      rw [← mul_assoc]
      exact H.mul_mem hx hy
    · left
      have e : J * x * J = x := by
        rw [hc _ hx, ← mul_assoc, hJ, one_mul]
      have : x * y = (J * x) * (J * y) := by rw [← mul_assoc, e]
      rw [this]
      exact H.mul_mem hx hy
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (H.inv_mem hx)
    · right
      have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
      have hw := hc _ (H.inv_mem hx)
      rw [mul_inv_rev, hJinv] at hw
      have : J * x⁻¹ = (J * x)⁻¹ := by
        rw [mul_inv_rev, hJinv]
        calc J * x⁻¹ = J * (x⁻¹ * J) * J := by rw [mul_assoc, mul_assoc, hJ, mul_one]
          _ = x⁻¹ * J * J * J := by rw [hw]
          _ = x⁻¹ * J := by rw [mul_assoc x⁻¹, hJ, mul_one]
      rw [this]
      exact H.inv_mem hx

theorem mem_prodJ {J : G} {hJ : J * J = 1} {H : Subgroup G} {hc : ∀ x ∈ H, x * J = J * x}
    {x : G} : x ∈ prodJ J hJ H hc ↔ x ∈ H ∨ J * x ∈ H := Iff.rfl

theorem card_prodJ [Finite G] {J : G} (hJ : J * J = 1) {H : Subgroup G}
    (hc : ∀ x ∈ H, x * J = J * x) (hJH : J ∉ H) :
    Nat.card (prodJ J hJ H hc) = 2 * Nat.card H := by
  classical
  let f : Bool × H → prodJ J hJ H hc := fun p =>
    if p.1 then ⟨J * p.2, Or.inr (by rw [← mul_assoc, hJ, one_mul]; exact p.2.2)⟩
    else ⟨p.2, Or.inl p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b₁, x₁⟩ ⟨b₂, x₂⟩ h12
      have h12' := congrArg Subtype.val h12
      cases b₁ <;> cases b₂ <;> simp only [f, Bool.false_eq_true, ite_false, ite_true] at h12'
      · rw [Subtype.ext h12']
      · exfalso
        apply hJH
        have : J = x₁ * (x₂ : G)⁻¹ := by rw [h12']; group
        rw [this]
        exact H.mul_mem x₁.2 (H.inv_mem x₂.2)
      · exfalso
        apply hJH
        have : J = x₂ * (x₁ : G)⁻¹ := by rw [← h12']; group
        rw [this]
        exact H.mul_mem x₂.2 (H.inv_mem x₁.2)
      · rw [Subtype.ext (mul_left_cancel h12')]
    · rintro ⟨x, hx | hx⟩
      · exact ⟨(false, ⟨x, hx⟩), rfl⟩
      · refine ⟨(true, ⟨J * x, hx⟩), Subtype.ext ?_⟩
        change J * (J * x) = x
        rw [← mul_assoc, hJ, one_mul]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_bool]

namespace ReeTypeHyp

variable [Finite G] (h : ReeTypeHyp G)

abbrev F : Type := GaloisField h.p h.f

noncomputable instance : Fintype h.F := Fintype.ofFinite _

noncomputable instance : DecidableEq h.F := Classical.decEq _

@[expose] noncomputable def κ : PSL(2, h.F) →* G := h.L.subtype.comp h.iso.symm.toMonoidHom

theorem κ_injective : Function.Injective h.κ :=
  h.L.subtype_injective.comp h.iso.symm.injective

theorem κ_mem (y : PSL(2, h.F)) : h.κ y ∈ h.L := (h.iso.symm y).2

theorem mem_L_iff (x : G) : x ∈ h.L ↔ ∃ y, h.κ y = x :=
  ⟨fun hx => ⟨h.iso ⟨x, hx⟩, by simp [κ]⟩, fun ⟨y, hy⟩ => hy ▸ h.κ_mem y⟩

theorem comm_L {x : G} (hx : x ∈ h.L) : x * h.J = h.J * x :=
  (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx))

theorem κ_comm (y : PSL(2, h.F)) : h.κ y * h.J = h.J * h.κ y := h.comm_L (h.κ_mem y)

theorem κ_ne_J (y : PSL(2, h.F)) : h.κ y ≠ h.J := fun hy => h.J_not_mem (hy ▸ h.κ_mem y)

theorem J_mul_J : h.J * h.J = 1 := by
  rw [← sq, ← h.orderOf_J, pow_orderOf_eq_one]

theorem J_ne_one : h.J ≠ 1 := fun h1 => by
  have := h.orderOf_J
  rw [h1, orderOf_one] at this
  omega

theorem J_inv : h.J⁻¹ = h.J := inv_eq_of_mul_eq_one_right h.J_mul_J

theorem centralizer {g : G} (hg : g * h.J = h.J * g) : ∃ y, g = h.κ y ∨ g = h.J * h.κ y := by
  have hle : Subgroup.zpowers h.J ⊔ h.L ≤ prodJ h.J h.J_mul_J h.L (fun x hx => h.comm_L hx) := by
    refine sup_le ?_ fun x hx => Or.inl hx
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [h.J_mul_J]; exact h.L.one_mem)
  have hgC : g ∈ Subgroup.centralizer ({h.J} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hg
  rw [h.centralizer_eq] at hgC
  rcases hle hgC with hgL | hgL
  · obtain ⟨y, hy⟩ := (h.mem_L_iff g).mp hgL
    exact ⟨y, Or.inl hy.symm⟩
  · obtain ⟨y, hy⟩ := (h.mem_L_iff _).mp hgL
    refine ⟨y, Or.inr ?_⟩
    rw [hy, ← mul_assoc, h.J_mul_J, one_mul]

theorem ringChar_ne_two : ringChar h.F ≠ 2 := by
  rw [ringChar.eq h.F h.p]
  exact h.p_ne_two

theorem exists_four :
    ∃ v₁ v₂ c : PSL(2, h.F), v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧
      v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧ orderOf c = 3 ∧ c * v₁ * c⁻¹ = v₂ ∧ c * v₂ * c⁻¹ = v₁ * v₂ :=
  Quaternion.exists_quaternion h.ringChar_ne_two

include h in
theorem exists_not_commute (S : Sylow 2 G) {z : G} (hzS : z ∈ S) (hz1 : z ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * z ≠ z * n := by
  by_contra hcon
  push Not at hcon
  have hab : IsMulCommutative (S : Subgroup G) := (h.elementary_sylow S).toIsMulCommutative
  obtain ⟨H, hHn, hH⟩ := JT.exists_normal_index_eq_of_commute_normalizer S hab hzS hz1 hcon
  exact h.index_ne_two H hHn hH

include h in
theorem exists_conj_of_mem (S : Sylow 2 G) {x y : G} (hx : x ∈ S) (hx1 : x ≠ 1) (hy : y ∈ S)
    (hy1 : y ≠ 1) : ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  classical
  have hab : IsMulCommutative (S : Subgroup G) := (h.elementary_sylow S).toIsMulCommutative
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let := JT.conjAct N S le_rfl
  set T : Set (S : Subgroup G) := {z | z ≠ 1}
  have hTcard : T.ncard = 7 := by
    have : T = (Set.univ : Set (S : Subgroup G)) \ {1} := by
      ext
      simp [T]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      h.card_sylow S]
  have hTinv : ∀ a : N, ∀ z ∈ T, a • z ∈ T := by
    intro a z hz h1
    apply hz
    have h1' : ((a • z : (S : Subgroup G)) : G) = 1 := congrArg Subtype.val h1
    change (a : G) * z * (a : G)⁻¹ = 1 at h1'
    apply Subtype.ext
    change (z : G) = 1
    have := congrArg (fun w => (a : G)⁻¹ * w * a) h1'
    simpa [mul_assoc] using this
  have horbit : ∀ z ∈ T, MulAction.orbit N z = T := by
    apply JT.orbit_eq_of_ncard_eq_seven T hTcard hTinv
    intro z hz
    rw [← MulAction.index_stabilizer]
    have hle : (S : Subgroup G).subgroupOf N ≤ MulAction.stabilizer N z := by
      intro s hs
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      change (s : G) * z * (s : G)⁻¹ = z
      have := congrArg Subtype.val (hab.is_comm.comm ⟨s, hs⟩ z)
      change (s : G) * z = z * s at this
      rw [this, mul_inv_cancel_right]
    refine ⟨?_, ?_⟩
    · have h1 := Subgroup.index_dvd_of_le hle
      have h2 : ((S : Subgroup G).subgroupOf N).index ∣ (S : Subgroup G).index :=
        Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact fun h3 => S.not_dvd_index (h3.trans (h1.trans h2))
    · intro h1
      rw [Subgroup.index_eq_one] at h1
      obtain ⟨n, hn, hnz⟩ := h.exists_not_commute S z.2 (fun h0 => hz (Subtype.ext h0))
      apply hnz
      have hmem : (⟨n, hn⟩ : N) ∈ MulAction.stabilizer N z := by
        rw [h1]
        exact Subgroup.mem_top _
      have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hmem)
      change n * z * n⁻¹ = z at this
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [this]
  have hxT : (⟨x, hx⟩ : (S : Subgroup G)) ∈ T := fun h0 => hx1 (congrArg Subtype.val h0)
  have hyT : (⟨y, hy⟩ : (S : Subgroup G)) ∈ T := fun h0 => hy1 (congrArg Subtype.val h0)
  rw [← horbit _ hxT] at hyT
  obtain ⟨n, hn⟩ := hyT
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

theorem exists_conj_mem_sylow (S : Sylow 2 G) {x : G} (hx : orderOf x = 2) :
    ∃ g : G, g * x * g⁻¹ ∈ S ∧ g * x * g⁻¹ ≠ 1 := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S', hS'⟩ := hx2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  refine ⟨g, ?_, ?_⟩
  · rw [← hg]
    change g * x * g⁻¹ ∈ MulAut.conj g • (S' : Subgroup G)
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S' : Subgroup G)
      (hS' (Subgroup.mem_zpowers x))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · intro h1
    have := congrArg (fun w => g⁻¹ * w * g) h1
    simp only [mul_one, inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at this
    rw [this, orderOf_one] at hx
    omega

theorem exists_sylow :
    ∃ (S : Sylow 2 G) (v₁ v₂ c : PSL(2, h.F)), v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧
      v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧ orderOf c = 3 ∧ c * v₁ * c⁻¹ = v₂ ∧
      c * v₂ * c⁻¹ = v₁ * v₂ ∧
      (∀ x : G, x ∈ S ↔ (x = 1 ∨ x = h.κ v₁ ∨ x = h.κ v₂ ∨ x = h.κ (v₁ * v₂)) ∨
        (h.J * x = 1 ∨ h.J * x = h.κ v₁ ∨ h.J * x = h.κ v₂ ∨ h.J * x = h.κ (v₁ * v₂))) := by
  obtain ⟨v₁, v₂, c, h1, h2, h12, hv₁, hv₂, hv12, hc, hc1, hc2⟩ := h.exists_four
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions v₁ v₂ h1 h2 h12 with hVdef
  have hV : IsKleinFour V :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ h1 h2 hv₁ hv₂ hv12 h12
  have hmemV : ∀ v, v ∈ V ↔ v = v₁ * v₂ ∨ v = v₁ ∨ v = v₂ ∨ v = 1 := fun v => Iff.rfl
  set H := V.map h.κ with hH
  have hHc : ∀ x ∈ H, x * h.J = h.J * x := by
    rintro x ⟨v, -, rfl⟩
    exact h.κ_comm v
  have hJH : h.J ∉ H := by
    rintro ⟨v, -, hv⟩
    exact h.κ_ne_J v hv
  set T := prodJ h.J h.J_mul_J H hHc with hT
  have hTcard : Nat.card T = 2 ^ 3 := by
    rw [hT, card_prodJ h.J_mul_J hHc hJH, hH,
      Subgroup.card_map_of_injective h.κ_injective, hV.card_four]
    norm_num
  obtain ⟨S, hTS⟩ := (IsPGroup.of_card hTcard).exists_le_sylow
  have hST : (S : Subgroup G) = T := by
    refine (Subgroup.eq_of_le_of_card_ge hTS ?_).symm
    rw [h.card_sylow S, hTcard]
    norm_num
  refine ⟨S, v₁, v₂, c, h1, h2, h12, hv₁, hv₂, hv12, hc, hc1, hc2, fun x => ?_⟩
  have hmemH : ∀ y : G, y ∈ H ↔ y = 1 ∨ y = h.κ v₁ ∨ y = h.κ v₂ ∨ y = h.κ (v₁ * v₂) := by
    intro y
    rw [hH, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases (hmemV v).mp hv with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl (map_one _)
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨1, V.one_mem, map_one _⟩
      · exact ⟨v₁, (hmemV _).mpr (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨v₂, (hmemV _).mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
      · exact ⟨v₁ * v₂, (hmemV _).mpr (Or.inl rfl), rfl⟩
  change x ∈ (S : Subgroup G) ↔ _
  rw [hST, hT, mem_prodJ, hmemH, hmemH]

theorem isConj_J {x : G} (hx : orderOf x = 2) : IsConj x h.J := by
  obtain ⟨S, v₁, v₂, c, -, -, -, -, -, -, -, -, -, hS⟩ := h.exists_sylow
  have hJS : h.J ∈ S := (hS _).mpr (Or.inr (Or.inl h.J_mul_J))
  obtain ⟨g, hgS, hg1⟩ := exists_conj_mem_sylow S hx
  obtain ⟨n, -, hn⟩ := h.exists_conj_of_mem S hgS hg1 hJS h.J_ne_one
  exact isConj_iff.mpr ⟨n * g, by rw [← hn]; group⟩

theorem exists_A : ∃ (A : G) (x : PSL(2, h.F)), orderOf x = 2 ∧ orderOf A = 3 ∧
    A⁻¹ * h.J * A = h.κ x ∧ A⁻¹ * h.κ x * A = h.J * h.κ x := by
  obtain ⟨S, v₁, v₂, c, h1, h2, h12, hv₁, hv₂, hv12, hc, hc1, hc2, hS⟩ := h.exists_sylow
  have hJS : h.J ∈ S := (hS _).mpr (Or.inr (Or.inl h.J_mul_J))
  have hv₁S : h.κ v₁ ∈ S := (hS _).mpr (Or.inl (Or.inr (Or.inl rfl)))
  have hκ1 : ∀ v : PSL(2, h.F), v ≠ 1 → h.κ v ≠ 1 := fun v hv h0 =>
    hv (h.κ_injective (by rw [h0, map_one]))
  obtain ⟨n, hnN, hn⟩ := h.exists_conj_of_mem S hJS h.J_ne_one hv₁S (hκ1 v₁ hv₁)
  have r1 : c⁻¹ * v₁ * c = v₁ * v₂ := by
    have e1 : c⁻¹ * v₂ * c = v₁ := by rw [← hc1]; group
    have e2 : c⁻¹ * (v₁ * v₂) * c = v₂ := by rw [← hc2]; group
    calc c⁻¹ * v₁ * c = (c⁻¹ * (v₁ * v₂) * c) * (c⁻¹ * v₂ * c) := by
          rw [show c⁻¹ * (v₁ * v₂) * c * (c⁻¹ * v₂ * c) = c⁻¹ * (v₁ * (v₂ * v₂)) * c by group,
            h2, mul_one]
      _ = v₂ * v₁ := by rw [e2, e1]
      _ = v₁ * v₂ := h12.symm
  have r2 : c⁻¹ * (v₁ * v₂) * c = v₂ := by rw [← hc2]; group
  have r3 : c⁻¹ * v₂ * c = v₁ := by rw [← hc1]; group
  have hnS : ∀ y ∈ S, n⁻¹ * y * n ∈ S := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) y).mp hy
    rw [inv_inv] at this
    exact this
  set A := n⁻¹ * h.κ c * n with hA
  set X := n⁻¹ * h.κ (v₁ * v₂) * n with hX
  set Y := n⁻¹ * h.κ v₂ * n with hY
  have hJn : h.J = n⁻¹ * h.κ v₁ * n := by rw [← hn]; group
  have key : ∀ w, A⁻¹ * (n⁻¹ * h.κ w * n) * A = n⁻¹ * h.κ (c⁻¹ * w * c) * n := by
    intro w
    rw [hA]
    simp only [map_mul, map_inv]
    group
  have hA1 : A⁻¹ * h.J * A = X := by rw [hJn, key, r1]
  have hA2 : A⁻¹ * X * A = Y := by rw [hX, key, r2]
  have hA3 : A⁻¹ * Y * A = h.J := by rw [hY, key, r3, hJn]
  have hXY : X * Y = h.J := by
    rw [hX, hY, hJn]
    simp only [map_mul]
    rw [show n⁻¹ * (h.κ v₁ * h.κ v₂) * n * (n⁻¹ * h.κ v₂ * n) =
      n⁻¹ * (h.κ v₁ * (h.κ v₂ * h.κ v₂)) * n by group, ← map_mul h.κ v₂, h2, map_one, mul_one]
  have hAord : orderOf A = 3 := by
    rw [hA, show n⁻¹ * h.κ c * n = n⁻¹ * h.κ c * n⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, orderOf_injective h.κ h.κ_injective, hc]
  have hXS : X ∈ S := hnS _ ((hS _).mpr (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))
  have hX1 : X ≠ 1 := by
    intro h0
    rw [hX] at h0
    have : h.κ (v₁ * v₂) = 1 := by
      have := congrArg (fun w => n * w * n⁻¹) h0
      simpa [mul_assoc] using this
    refine hκ1 (v₁ * v₂) ?_ this
    intro h0'
    apply hv12
    calc v₁ = v₁ * (v₂ * v₂) := by rw [h2, mul_one]
      _ = (v₁ * v₂) * v₂ := by group
      _ = v₂ := by rw [h0', one_mul]
  have hXJ : X ≠ h.J := by
    intro h0
    rw [h0] at hXY
    have hY1 : Y = 1 := by
      have := congrArg (fun w => h.J * w) hXY
      simpa [← mul_assoc, h.J_mul_J] using this
    rw [hY] at hY1
    have : h.κ v₂ = 1 := by
      have := congrArg (fun w => n * w * n⁻¹) hY1
      simpa [mul_assoc] using this
    exact hκ1 v₂ hv₂ this
  have hYeq : Y = X * h.J := by
    have hXX : X * X = 1 := by
      rw [hX, show n⁻¹ * h.κ (v₁ * v₂) * n * (n⁻¹ * h.κ (v₁ * v₂) * n) =
        n⁻¹ * (h.κ (v₁ * v₂ * (v₁ * v₂))) * n by simp only [map_mul]; group]
      rw [show v₁ * v₂ * (v₁ * v₂) = (v₁ * v₁) * (v₂ * v₂) by
        rw [mul_assoc, ← mul_assoc v₂, ← h12]; group, h1, h2, mul_one, map_one, mul_one,
        inv_mul_cancel]
    calc Y = X * (X * Y) := by rw [← mul_assoc, hXX, one_mul]
      _ = X * h.J := by rw [hXY]
  have hinv : ∀ v : PSL(2, h.F), v ≠ 1 → v = v₁ ∨ v = v₂ ∨ v = v₁ * v₂ → orderOf v = 2 := by
    intro v hv1 hv
    refine orderOf_eq_prime ?_ hv1
    rw [sq]
    rcases hv with rfl | rfl | rfl
    · exact h1
    · exact h2
    · rw [show v₁ * v₂ * (v₁ * v₂) = (v₁ * v₁) * (v₂ * v₂) by
        rw [mul_assoc, ← mul_assoc v₂, ← h12]; group, h1, h2, mul_one]
  rcases (hS X).mp hXS with hXL | hXL
  ·
    obtain ⟨x, hxX, hxV⟩ : ∃ x, X = h.κ x ∧ (x = v₁ ∨ x = v₂ ∨ x = v₁ * v₂) := by
      rcases hXL with h0 | h0 | h0 | h0
      · exact absurd h0 hX1
      · exact ⟨v₁, h0, Or.inl rfl⟩
      · exact ⟨v₂, h0, Or.inr (Or.inl rfl)⟩
      · exact ⟨v₁ * v₂, h0, Or.inr (Or.inr rfl)⟩
    have hx1 : x ≠ 1 := fun h0 => hX1 (by rw [hxX, h0, map_one])
    refine ⟨A, x, hinv x hx1 hxV, hAord, by rw [hA1, hxX], ?_⟩
    rw [← hxX, hA2, hYeq, hxX, h.κ_comm]
  ·
    obtain ⟨x, hxX, hxV⟩ : ∃ x, h.J * X = h.κ x ∧ (x = v₁ ∨ x = v₂ ∨ x = v₁ * v₂) := by
      rcases hXL with h0 | h0 | h0 | h0
      · exfalso
        apply hXJ
        calc X = h.J * (h.J * X) := by rw [← mul_assoc, h.J_mul_J, one_mul]
          _ = h.J := by rw [h0, mul_one]
      · exact ⟨v₁, h0, Or.inl rfl⟩
      · exact ⟨v₂, h0, Or.inr (Or.inl rfl)⟩
      · exact ⟨v₁ * v₂, h0, Or.inr (Or.inr rfl)⟩
    have hx1 : x ≠ 1 := by
      intro h0
      apply hXJ
      calc X = h.J * (h.J * X) := by rw [← mul_assoc, h.J_mul_J, one_mul]
        _ = h.J := by rw [hxX, h0, map_one, mul_one]
    have hXeq : X = h.J * h.κ x := by
      rw [← hxX, ← mul_assoc, h.J_mul_J, one_mul]
    have hYx : Y = h.κ x := by
      rw [hYeq, hXeq, mul_assoc, h.κ_comm, ← mul_assoc, h.J_mul_J, one_mul]
    have hAord' : orderOf A⁻¹ = 3 := by rw [orderOf_inv, hAord]
    refine ⟨A⁻¹, x, hinv x hx1 hxV, hAord', ?_, ?_⟩
    · rw [inv_inv, ← hYx, ← hA3]
      group
    · rw [inv_inv, ← hXeq, ← hYx, ← hA2]
      group

theorem three_le_q : 3 ≤ h.q := by
  have hp := (Fact.out : h.p.Prime)
  have hp3 : 3 ≤ h.p := by have := hp.two_le; have := h.p_ne_two; omega
  calc 3 ≤ h.p := hp3
    _ ≤ h.p ^ h.f := Nat.le_self_pow (by have := h.f_pos; omega) _

theorem q_odd : Odd h.q := ((Fact.out : h.p.Prime).odd_of_ne_two h.p_ne_two).pow

theorem mod_eight :
    h.q % 8 = 3 ∨ h.q % 8 = 5 := by
  by_cases hq5 : 5 < h.q
  · refine (JT.psl2Facts h.L h.iso h.p_ne_two hq5).mod_eight fun P _ hP => ?_
    obtain ⟨S, hS⟩ := hP.exists_le_sylow
    have hab : IsMulCommutative (S : Subgroup G) := (h.elementary_sylow S).toIsMulCommutative
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have e := congrArg Subtype.val (hab.is_comm.comm ⟨(a : G), hS a.2⟩ ⟨(b : G), hS b.2⟩)
    exact e
  · have h3 := h.three_le_q
    obtain ⟨k, hk⟩ := h.q_odd
    omega

theorem e_eq : h.e = 1 ∨ h.e = -1 := by
  unfold ReeTypeHyp.e wardSign
  split_ifs <;> simp

theorem q_mod :
    (h.q : ℤ) % 8 = 4 + h.e := by
  unfold ReeTypeHyp.e wardSign
  rcases h.mod_eight with h8 | h8
  · rw [ite_eq_left h8]
    omega
  · rw [ite_eq_right (by omega)]
    omega

theorem mem_normalizer_closure {A J' : G} (hJJ' : h.J * J' = J' * h.J) (hJ'2 : J' * J' = 1)
    (h1 : A⁻¹ * h.J * A = J') (h2 : A⁻¹ * J' * A = h.J * J') :
    A ∈ Subgroup.normalizer (Subgroup.closure ({h.J, J'} : Set G) : Set G) := by
  set H := Subgroup.closure ({h.J, J'} : Set G)
  have hJH : h.J ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hJ'H : J' ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have e1 : A * J' * A⁻¹ = h.J := by rw [← h1]; group
  have e2 : A * h.J * A⁻¹ = h.J * J' := by
    have : A⁻¹ * (h.J * J') * A = h.J := by
      rw [show A⁻¹ * (h.J * J') * A = (A⁻¹ * h.J * A) * (A⁻¹ * J' * A) by group, h1, h2,
        ← mul_assoc, ← hJJ', mul_assoc, hJ'2, mul_one]
    calc A * h.J * A⁻¹ = A * (A⁻¹ * (h.J * J') * A) * A⁻¹ := by rw [this]
      _ = h.J * J' := by group
  have hle : H ≤ H.comap (MulAut.conj A).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · change A * h.J * A⁻¹ ∈ H
      rw [e2]
      exact H.mul_mem hJH hJ'H
    · change A * y * A⁻¹ ∈ H
      rw [e1]
      exact hJH
  exact JT.mem_normalizer_of_conj_mem fun y hy => hle hy

theorem q_sub_e_ne_four : (h.q : ℤ) - h.e ≠ 4 := by
  intro h4
  obtain ⟨A, x, hx, hA, h1, h2⟩ := h.exists_A
  have hx2 : orderOf (h.κ x) = 2 := by rw [orderOf_injective h.κ h.κ_injective, hx]
  have hxx : h.κ x * h.κ x = 1 := by
    have := pow_orderOf_eq_one (h.κ x)
    rw [hx2, sq] at this
    exact this
  have hAN := h.mem_normalizer_closure (h.κ_comm x).symm hxx h1 h2
  refine h.not_commute (h.κ x) (h.κ_mem x) hx2 1 h.L.one_mem ?_ (by simp) A hA hAN
    (by simp)
  rw [orderOf_one]
  have : ((h.p ^ h.f : ℕ) : ℤ) - wardSign (h.p ^ h.f) = 4 := h4
  push_cast at this ⊢
  linarith

theorem eleven_le_q : 11 ≤ h.q := by
  have h4 := h.q_sub_e_ne_four
  have h3 := h.three_le_q
  unfold ReeTypeHyp.e wardSign at h4
  rcases h.mod_eight with h8 | h8
  · rw [ite_eq_left h8] at h4
    omega
  · rw [ite_eq_right (by omega)] at h4
    omega

end ReeTypeHyp

end CFSG.Walter.Ward
