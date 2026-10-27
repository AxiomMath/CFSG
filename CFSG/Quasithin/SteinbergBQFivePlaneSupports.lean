module

public import CFSG.Quasithin.SteinbergBQCyclicFiveSupport

public noncomputable section

namespace CFSG.Quasithin.SteinbergBQ

open Module

section Supports

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def dispGroup (M : Submodule (ZMod 2) V) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) where
  carrier := {g | ∀ v, (g : V →ₗ[ZMod 2] V) v - v ∈ M}
  mul_mem' := fun {a b} ha hb v => by
    have e : ((a * b : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v =
        ((a : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) v) - (b : V →ₗ[ZMod 2] V) v) +
          ((b : V →ₗ[ZMod 2] V) v - v) := by
      rw [Units.val_mul, Module.End.mul_apply]
      abel
    rw [e]
    exact M.add_mem (ha _) (hb v)
  one_mem' := fun v => by
    rw [Units.val_one, Module.End.one_apply, sub_self]
    exact M.zero_mem
  inv_mem' := fun {a} ha v => by
    have e : ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v =
        -((a : V →ₗ[ZMod 2] V) (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) v) - ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V) v) := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply, neg_sub]
    rw [e]
    exact M.neg_mem (ha _)

theorem commSpan_le_iff {Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {M : Submodule (ZMod 2) V} : commSpan Q ≤ M ↔ Q ≤ dispGroup M := by
  constructor
  · intro h x hx v
    exact h (sub_mem_commSpan Q hx v)
  · intro h
    rw [commSpan, Submodule.span_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact h hx v

theorem commSpan_mono {Q Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)} (h : Q ≤ Q') :
    commSpan Q ≤ commSpan Q' :=
  Submodule.span_mono (by
    rintro _ ⟨x, hx, v, rfl⟩
    exact ⟨x, h hx, v, rfl⟩)

theorem commSpan_sup (Q Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
    commSpan (Q ⊔ Q') = commSpan Q ⊔ commSpan Q' :=
  le_antisymm
    (commSpan_le_iff.2 (sup_le (commSpan_le_iff.1 le_sup_left) (commSpan_le_iff.1 le_sup_right)))
    (sup_le (commSpan_mono le_sup_left) (commSpan_mono le_sup_right))

theorem map_mem_commSpan_of_commute {Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {y : LinearMap.GeneralLinearGroup (ZMod 2) V} (hy : ∀ x ∈ Q, y * x = x * y) {w : V}
    (hw : w ∈ commSpan Q) : (y : V →ₗ[ZMod 2] V) w ∈ commSpan Q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have e : (y : V →ₗ[ZMod 2] V) ((x : V →ₗ[ZMod 2] V) v - v) =
        (x : V →ₗ[ZMod 2] V) ((y : V →ₗ[ZMod 2] V) v) - (y : V →ₗ[ZMod 2] V) v := by
      rw [map_sub, ← Module.End.mul_apply, ← Units.val_mul, hy x hx, Units.val_mul,
        Module.End.mul_apply]
    rw [e]
    exact sub_mem_commSpan Q hx _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem injective_coe_generalLinearGroup (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    Function.Injective (g : V →ₗ[ZMod 2] V) := fun a b h => by
  have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Module.End.one_apply, Module.End.one_apply] at this

theorem commSpan_map_conj (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    commSpan (Q.map (MulAut.conj g).toMonoidHom) = (commSpan Q).map (g : V →ₗ[ZMod 2] V) := by
  have hgg : ∀ u, (g : V →ₗ[ZMod 2] V) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) u) = u := fun u => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hgg' : ∀ u, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((g : V →ₗ[ZMod 2] V) u) = u := fun u => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hconj : ∀ x u, (((MulAut.conj g).toMonoidHom x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) u = (g : V →ₗ[ZMod 2] V) ((x : V →ₗ[ZMod 2] V)
        (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u)) := fun x u => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply]
  rw [commSpan, commSpan, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, v, rfl⟩
    refine ⟨(x : V →ₗ[ZMod 2] V) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v) - ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) v, ⟨x, hx, _, rfl⟩, ?_⟩
    rw [map_sub, hgg, hconj]
  · rintro ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, (g : V →ₗ[ZMod 2] V) v, ?_⟩
    rw [map_sub, hconj, hgg']

theorem eq_bot_or_eq_of_five [Finite V]
    (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (hQ : IsPGroup 5 Q)
    {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 4)
    (hfix : ∀ w ∈ W, (∀ x ∈ Q, (x : V →ₗ[ZMod 2] V) w = w) → w = 0)
    {U : Submodule (ZMod 2) V} (hUW : U ≤ W) (hU : ∀ x ∈ Q, ∀ u ∈ U, (x : V →ₗ[ZMod 2] V) u ∈ U) :
    U = ⊥ ∨ U = W := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := two_pow_finrank_modEq_one Q hQ U hU fun u hu h' => hfix u (hUW hu) h'
  have hle : finrank (ZMod 2) U ≤ 4 := hW ▸ Submodule.finrank_mono hUW
  by_cases h0 : U = ⊥
  · exact Or.inl h0
  · right
    have hpos : finrank (ZMod 2) U ≠ 0 := fun h' => h0 (Submodule.finrank_eq_zero.1 h')
    have h4 : finrank (ZMod 2) U = 4 := by
      set d := finrank (ZMod 2) U with hd
      interval_cases d <;> first | rfl | exact absurd rfl hpos | exact absurd h (by decide)
    exact Submodule.eq_of_le_of_finrank_eq hUW (h4.trans hW.symm)

end Supports

theorem inf_eq_bot_and_sup_eq_of_card_five {G : Type*} [Group G] [Finite G]
    {P Q₁ Q₂ : Subgroup G} (hP : Nat.card P = 25) (h1 : Q₁ ≤ P) (h2 : Q₂ ≤ P)
    (hc1 : Nat.card Q₁ = 5) (hc2 : Nat.card Q₂ = 5) (hne : Q₁ ≠ Q₂) :
    Q₁ ⊓ Q₂ = ⊥ ∧ Q₁ ⊔ Q₂ = P := by
  constructor
  · have hdvd : Nat.card (Q₁ ⊓ Q₂ : Subgroup G) ∣ 5 := hc1 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hne
      have e1 := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁) (by rw [hc1, h])
      have e2 := Subgroup.eq_of_le_of_card_ge (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂) (by rw [hc2, h])
      rw [← e1, e2]
  · have hle : Q₁ ⊔ Q₂ ≤ P := sup_le h1 h2
    have hdvd : Nat.card (Q₁ ⊔ Q₂ : Subgroup G) ∣ 5 ^ 2 := by
      rw [show (5 : ℕ) ^ 2 = 25 by norm_num, ← hP]
      exact Subgroup.card_dvd_of_le hle
    have h5 : 5 ∣ Nat.card (Q₁ ⊔ Q₂ : Subgroup G) := hc1 ▸ Subgroup.card_dvd_of_le le_sup_left
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
    interval_cases i
    · rw [hci] at h5
      norm_num at h5
    · exfalso
      apply hne
      have e1 := Subgroup.eq_of_le_of_card_ge (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂)
        (by rw [hc1, hci, pow_one])
      have e2 := Subgroup.eq_of_le_of_card_ge (le_sup_right.trans e1.symm.le : Q₂ ≤ Q₁)
        (by rw [hc1, hc2])
      exact e2.symm
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hci]; norm_num)

theorem isElementaryAbelian_of_card_five {G : Type*} [Group G] {Q : Subgroup G}
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQ : Nat.card Q = 5) : IsElementaryAbelian 5 Q :=
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  { is_comm := ⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
      rw [← hQ]
      exact pow_card_eq_one' }

theorem irreducibly_normalized_five_plane_rank_four_supports_fill_whole_module {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (Γ P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (hPΓ : P ≤ Γ)
    (hPn : (P.subgroupOf Γ).Normal) [IsElementaryAbelian 5 P] (hP25 : Nat.card P = 25)
    (hVP : commSpan P = ⊤)
    (hirr : ∀ R : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V), R ≤ P →
      (∀ g ∈ Γ, ∀ x ∈ R, g * x * g⁻¹ ∈ R) → R = ⊥ ∨ R = P)
    (hΔ : ∃ Q ≤ P, Nat.card Q = 5 ∧ finrank (ZMod 2) (commSpan Q) = 4) :
    ∃ P₁ P₂ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V), P₁ ≠ P₂ ∧
      (∀ Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V),
        (Q ≤ P ∧ Nat.card Q = 5 ∧ finrank (ZMod 2) (commSpan Q) = 4) ↔ Q = P₁ ∨ Q = P₂) ∧
      P₁ ⊓ P₂ = ⊥ ∧ P₁ ⊔ P₂ = P ∧ IsCompl (commSpan P₁) (commSpan P₂) ∧
      finrank (ZMod 2) (commSpan P₁) = 4 ∧ finrank (ZMod 2) (commSpan P₂) = 4 ∧
      (∀ x ∈ P₂, ∀ v ∈ commSpan P₁, (x : V →ₗ[ZMod 2] V) v = v) ∧
      (∀ x ∈ P₁, ∀ v ∈ commSpan P₂, (x : V →ₗ[ZMod 2] V) v = v) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := finite_generalLinearGroup (V := V)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative P).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPp : IsPGroup 5 P := isPGroup_of_isElementaryAbelian P
  have hfixQ : ∀ Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V), Q ≤ P →
      Nat.card Q = 5 → ∀ w ∈ commSpan Q, (∀ x ∈ Q, (x : V →ₗ[ZMod 2] V) w = w) → w = 0 := by
    intro Q hQP hQ5
    have : IsElementaryAbelian 5 Q :=
      isElementaryAbelian_of_card_five (fun a ha b hb => hPcomm a (hQP ha) b (hQP hb)) hQ5
    exact (commSpan_decomposition Q (p := 5) (by norm_num)).1
  have hcross : ∀ Q Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V),
      Q ≤ P → Nat.card Q = 5 → finrank (ZMod 2) (commSpan Q) = 4 →
      Q' ≤ P → Nat.card Q' = 5 → finrank (ZMod 2) (commSpan Q') = 4 → Q ≠ Q' →
      ∀ y ∈ Q', ∀ w ∈ commSpan Q, (y : V →ₗ[ZMod 2] V) w = w := by
    intro Q Q' hQP hQ5 hQ4 hQ'P hQ'5 hQ'4 hne
    have hyW : ∀ y ∈ Q', ∀ w ∈ commSpan Q, (y : V →ₗ[ZMod 2] V) w ∈ commSpan Q :=
      fun y hy w hw =>
        map_mem_commSpan_of_commute (fun x hx => hPcomm y (hQ'P hy) x (hQP hx)) hw
    set D : Submodule (ZMod 2) V := Submodule.span (ZMod 2)
      {u | ∃ y ∈ Q', ∃ w ∈ commSpan Q, u = (y : V →ₗ[ZMod 2] V) w - w} with hDdef
    have hDW : D ≤ commSpan Q := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, w, hw, rfl⟩
      exact (commSpan Q).sub_mem (hyW y hy w hw) hw)
    have hDQ : ∀ x ∈ Q, ∀ u ∈ D, (x : V →ₗ[ZMod 2] V) u ∈ D := by
      intro x hx u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨y, hy, w, hw, rfl⟩ := hu
        have e : (x : V →ₗ[ZMod 2] V) ((y : V →ₗ[ZMod 2] V) w - w) =
            (y : V →ₗ[ZMod 2] V) ((x : V →ₗ[ZMod 2] V) w) - (x : V →ₗ[ZMod 2] V) w := by
          rw [map_sub, ← Module.End.mul_apply, ← Units.val_mul, hPcomm x (hQP hx) y (hQ'P hy),
            Units.val_mul, Module.End.mul_apply]
        rw [e]
        exact Submodule.subset_span ⟨y, hy, _, map_mem_commSpan Q hx hw, rfl⟩
      | zero => rw [map_zero]; exact D.zero_mem
      | add a b _ _ ha hb => rw [map_add]; exact D.add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact D.smul_mem c ha
    rcases eq_bot_or_eq_of_five Q (hPp.to_le hQP) hQ4 (hfixQ Q hQP hQ5) hDW hDQ with hD | hD
    · intro y hy w hw
      have h1 : (y : V →ₗ[ZMod 2] V) w - w ∈ D := Submodule.subset_span ⟨y, hy, w, hw, rfl⟩
      rw [hD, Submodule.mem_bot, sub_eq_zero] at h1
      exact h1
    · exfalso
      have hle : D ≤ commSpan Q' := Submodule.span_le.2 (by
        rintro _ ⟨y, hy, w, -, rfl⟩
        exact sub_mem_commSpan Q' hy w)
      rw [hD] at hle
      have hWW' : commSpan Q = commSpan Q' :=
        Submodule.eq_of_le_of_finrank_eq hle (hQ4.trans hQ'4.symm)
      obtain ⟨-, hsup⟩ := inf_eq_bot_and_sup_eq_of_card_five hP25 hQP hQ'P hQ5 hQ'5 hne
      have htop : commSpan Q = ⊤ := by rw [← hVP, ← hsup, commSpan_sup, ← hWW', sup_idem]
      have hV4 : finrank (ZMod 2) V = 4 := by
        rw [← finrank_top (ZMod 2) V, ← htop]
        exact hQ4
      have hP1 : P ≠ ⊥ := fun h => by
        rw [h, Subgroup.card_bot] at hP25
        norm_num at hP25
      have hPfix : ∀ u : V, (∀ x ∈ P, (x : V →ₗ[ZMod 2] V) u = u) → u = 0 := fun u hu =>
        hfixQ Q hQP hQ5 u (htop ▸ Submodule.mem_top) fun x hx => hu x (hQP hx)
      have h5 := (five_support_core hV4 P hPp hP1 hPcomm hPfix).1
      rw [hP25] at h5
      norm_num at h5
  have hthree : ∀ Q₁ Q₂ Q₃ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (Q₁ ≤ P ∧ Nat.card Q₁ = 5 ∧ finrank (ZMod 2) (commSpan Q₁) = 4) →
      (Q₂ ≤ P ∧ Nat.card Q₂ = 5 ∧ finrank (ZMod 2) (commSpan Q₂) = 4) →
      (Q₃ ≤ P ∧ Nat.card Q₃ = 5 ∧ finrank (ZMod 2) (commSpan Q₃) = 4) → Q₁ ≠ Q₂ →
      Q₃ = Q₁ ∨ Q₃ = Q₂ := by
    rintro Q₁ Q₂ Q₃ ⟨h1P, h15, h14⟩ ⟨h2P, h25, h24⟩ ⟨h3P, h35, h34⟩ hne
    by_contra h
    push Not at h
    obtain ⟨h31, h32⟩ := h
    have hc1 := hcross Q₁ Q₃ h1P h15 h14 h3P h35 h34 (Ne.symm h31)
    have hc2 := hcross Q₂ Q₃ h2P h25 h24 h3P h35 h34 (Ne.symm h32)
    obtain ⟨-, hsup⟩ := inf_eq_bot_and_sup_eq_of_card_five hP25 h1P h2P h15 h25 hne
    have hV : commSpan Q₁ ⊔ commSpan Q₂ = ⊤ := by rw [← commSpan_sup, hsup, hVP]
    have hQ3 : Q₃ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      refine Units.ext (LinearMap.ext fun v => ?_)
      have hv : v ∈ commSpan Q₁ ⊔ commSpan Q₂ := hV ▸ Submodule.mem_top
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, hc1 y hy w₁ hw₁, hc2 y hy w₂ hw₂]
      rfl
    rw [hQ3, Subgroup.card_bot] at h35
    norm_num at h35
  obtain ⟨Q₁, hQ₁P, hQ₁5, hQ₁4⟩ := hΔ
  have hconjΔ : ∀ g ∈ Γ, ∀ Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V), Q ≤ P →
      Nat.card Q = 5 → finrank (ZMod 2) (commSpan Q) = 4 →
      Q.map (MulAut.conj g).toMonoidHom ≤ P ∧
        Nat.card (Q.map (MulAut.conj g).toMonoidHom) = 5 ∧
        finrank (ZMod 2) (commSpan (Q.map (MulAut.conj g).toMonoidHom)) = 4 := by
    intro g hg Q hQP hQ5 hQ4
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hPn.conj_mem ⟨x, hPΓ (hQP hx)⟩ (hQP hx) ⟨g, hg⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ5]
    · rw [commSpan_map_conj, ← hQ4]
      exact (Submodule.equivMapOfInjective _ (injective_coe_generalLinearGroup g) _).finrank_eq.symm
  have hsecond : ∃ Q₂ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (Q₂ ≤ P ∧ Nat.card Q₂ = 5 ∧ finrank (ZMod 2) (commSpan Q₂) = 4) ∧ Q₂ ≠ Q₁ := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ g ∈ Γ, ∀ x ∈ Q₁, g * x * g⁻¹ ∈ Q₁ := by
      intro g hg x hx
      have h := hcon _ (hconjΔ g hg Q₁ hQ₁P hQ₁5 hQ₁4)
      rw [← h]
      exact ⟨x, hx, rfl⟩
    rcases hirr Q₁ hQ₁P hinv with h | h
    · rw [h, Subgroup.card_bot] at hQ₁5
      norm_num at hQ₁5
    · rw [h, hP25] at hQ₁5
      norm_num at hQ₁5
  obtain ⟨Q₂, ⟨hQ₂P, hQ₂5, hQ₂4⟩, hne⟩ := hsecond
  obtain ⟨hinf, hsup⟩ := inf_eq_bot_and_sup_eq_of_card_five hP25 hQ₁P hQ₂P hQ₁5 hQ₂5 hne.symm
  have h12 := hcross Q₁ Q₂ hQ₁P hQ₁5 hQ₁4 hQ₂P hQ₂5 hQ₂4 hne.symm
  have h21 := hcross Q₂ Q₁ hQ₂P hQ₂5 hQ₂4 hQ₁P hQ₁5 hQ₁4 hne
  refine ⟨Q₁, Q₂, hne.symm, fun Q => ⟨fun hQ => hthree Q₁ Q₂ Q ⟨hQ₁P, hQ₁5, hQ₁4⟩
    ⟨hQ₂P, hQ₂5, hQ₂4⟩ hQ hne.symm, ?_⟩, hinf, hsup, ⟨?_, ?_⟩, hQ₁4, hQ₂4, h12, h21⟩
  · rintro (rfl | rfl)
    · exact ⟨hQ₁P, hQ₁5, hQ₁4⟩
    · exact ⟨hQ₂P, hQ₂5, hQ₂4⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := Submodule.mem_inf.1 hw
    exact (Submodule.mem_bot _).2 (hfixQ Q₁ hQ₁P hQ₁5 w hw₁ fun x hx => h21 x hx w hw₂)
  · rw [codisjoint_iff, ← commSpan_sup, hsup, hVP]

end CFSG.Quasithin.SteinbergBQ
