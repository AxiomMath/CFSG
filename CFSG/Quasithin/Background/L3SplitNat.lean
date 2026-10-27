module

public import CFSG.Quasithin.Background.L3Split
public import CFSG.Quasithin.Background.L3Small
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin.L3Split

open CFSG.Quasithin L3

theorem L3_not_comm : ∃ a b : Γ, a * b ≠ b * a := by decide

variable {A : Type*} [CommGroup A] [Finite A]

theorem natural_of (hA2 : ∀ a : A, a * a = 1) (ρ : Γ →* MulAut A) {c : Γ} (hc3 : c ^ 3 = 1)
    {E : Subgroup A} (hE4 : Nat.card E = 4) (hcE : ∀ x, ρ c x * x⁻¹ ∈ E)
    (hEc : ∀ e ∈ E, ∃ x, ρ c x * x⁻¹ = e)
    (hgen : ∀ U : Subgroup A, (∀ γ, ∀ u ∈ U, ρ γ u ∈ U) → E ≤ U → U = ⊤)
    {a₀ : Γ} (ha₀ : IsInvol a₀) (hfix : ∀ e ∈ E, ρ a₀ e = e) :
    ∃ (α : Γ ≃* Γ) (β : A ≃* Multiplicative Vec), ∀ γ x,
      β (ρ γ x) = Multiplicative.ofAdd (act (α γ) (Multiplicative.toAdd (β x))) := by
  classical
  have hsimple : IsSimpleGroup Γ := L3Small.isSimpleGroup_Γ
  set θ : A → A := fun y => ρ c y * y⁻¹ with hθdef
  have hθmul : ∀ x y : A, θ (x * y) = θ x * θ y := by
    intro x y
    simp only [hθdef]
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hθρ : ∀ y : A, θ (ρ c y) = ρ c (θ y) := by
    intro y
    simp only [hθdef]
    rw [map_mul, map_inv]
  have hc3' : ∀ x : A, ρ c (ρ c (ρ c x)) = x := by
    intro x
    have h1 : ρ c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have h2 : (ρ c ^ 3) x = x := by rw [h1]; rfl
    simpa [pow_succ, MulAut.mul_apply] using h2
  have hfpf : ∀ e ∈ E, ρ c e = e → e = 1 := by
    intro e he hce
    obtain ⟨x, hx⟩ := hEc e he
    have hn : ρ c (x * ρ c x * ρ c (ρ c x)) = x * ρ c x * ρ c (ρ c x) := by
      rw [map_mul, map_mul, hc3']
      ac_rfl
    have h1 : θ (x * ρ c x * ρ c (ρ c x)) = 1 := by
      simp only [hθdef]
      rw [hn, mul_inv_cancel]
    have hθx : θ x = e := hx
    rw [hθmul, hθmul, hθρ, hθρ, hθρ, hθx, hce, hce] at h1
    have h2 := hA2 e
    calc e = e * e * e := by rw [h2, one_mul]
      _ = 1 := h1
  let C₀ : Subgroup A :=
    { carrier := {a | ∀ γ, ρ γ a = a}
      one_mem' := fun γ => map_one _
      mul_mem' := fun {a b} ha hb γ => by
        show ρ γ (a * b) = a * b
        rw [map_mul, ha γ, hb γ]
      inv_mem' := fun {a} ha γ => by
        show ρ γ a⁻¹ = a⁻¹
        rw [map_inv, ha γ] }
  have hmemC₀ : ∀ a, a ∈ C₀ ↔ ∀ γ, ρ γ a = a := fun a => Iff.rfl
  have hEC₀ : ∀ e ∈ E, e ∈ C₀ → e = 1 := fun e he hC => hfpf e he (hC c)
  have hρinv : ∀ γ (u : A), ρ γ⁻¹ (ρ γ u) = u := by
    intro γ u
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hstab : ∀ γ, ρ γ ∈ stabSub C₀ := by
    intro γ u
    constructor
    · intro hu
      have h2 : ρ γ⁻¹ (ρ γ u) = ρ γ u := hu γ⁻¹
      rw [← hρinv γ u, h2]
      exact hu
    · intro hu
      rw [hu γ]
      exact hu
  set ρB : Γ →* MulAut (A ⧸ C₀) := (quotHom C₀).comp (ρ.codRestrict (stabSub C₀) hstab) with hρB
  have hρBmk : ∀ γ (a : A), ρB γ (a : A ⧸ C₀) = ((ρ γ a : A) : A ⧸ C₀) := fun γ a => rfl
  have hB2 : ∀ b : A ⧸ C₀, b * b = 1 := by
    intro b
    induction b using QuotientGroup.induction_on with
    | H a => rw [← QuotientGroup.mk_mul, hA2 a, QuotientGroup.mk_one]
  set EB : Subgroup (A ⧸ C₀) := E.map (QuotientGroup.mk' C₀) with hEB
  have hEinf : E ⊓ (QuotientGroup.mk' C₀).ker = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [QuotientGroup.ker_mk'] at he
    rw [Subgroup.mem_bot]
    exact hEC₀ e he.1 he.2
  have hEB4 : Nat.card EB = 4 := by
    have h1 := B1More.card_map_mul_card_inf_ker E (QuotientGroup.mk' C₀)
    rw [hEinf, Subgroup.card_bot, mul_one, hE4] at h1
    exact h1
  let θB : (A ⧸ C₀) →* (A ⧸ C₀) :=
    { toFun := fun b => ρB c b * b⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        show ρB c (a * b) * (a * b)⁻¹ = ρB c a * a⁻¹ * (ρB c b * b⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hθBrange : θB.range = EB := by
    ext b
    constructor
    · rintro ⟨b', rfl⟩
      induction b' using QuotientGroup.induction_on with
      | H a =>
        show ρB c (a : A ⧸ C₀) * (a : A ⧸ C₀)⁻¹ ∈ EB
        rw [hρBmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        exact ⟨_, hcE a, rfl⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, rfl⟩ := hEc e he
      refine ⟨(x : A ⧸ C₀), ?_⟩
      show ρB c (x : A ⧸ C₀) * (x : A ⧸ C₀)⁻¹ = _
      rw [hρBmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
  have hθBker : θB.ker = L3Small.fixOf (ρB c) := by
    ext b
    rw [MonoidHom.mem_ker]
    show ρB c b * b⁻¹ = 1 ↔ ρB c b = b
    exact mul_inv_eq_one
  have hcardB : Nat.card (A ⧸ C₀) = 4 * Nat.card (L3Small.fixOf (ρB c)) := by
    have h1 := B1More.card_map_mul_card_inf_ker ⊤ θB
    rw [← MonoidHom.range_eq_map, hθBrange, hEB4, top_inf_eq, hθBker, Subgroup.card_top] at h1
    exact h1.symm
  have hc1 : c ≠ 1 := by
    intro h0
    have h1 : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      obtain ⟨x, rfl⟩ := hEc e he
      rw [h0, map_one, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [h1, Subgroup.card_bot] at hE4
    norm_num at hE4
  have hCB : ∀ b : A ⧸ C₀, (∀ γ, ρB γ b = b) → b = 1 := by
    intro b hb
    induction b using QuotientGroup.induction_on with
    | H a =>
      have hf : ∀ γ, ρ γ a * a⁻¹ ∈ C₀ := by
        intro γ
        have h1 := hb γ
        rw [hρBmk] at h1
        have h2 := C₀.inv_mem (QuotientGroup.eq.mp h1)
        rwa [mul_inv_rev, inv_inv, mul_comm] at h2
      let f : Γ →* ↥C₀ :=
        { toFun := fun γ => ⟨ρ γ a * a⁻¹, hf γ⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun γ δ => Subtype.ext (by
            show ρ (γ * δ) a * a⁻¹ = (ρ γ a * a⁻¹) * (ρ δ a * a⁻¹)
            have h1 : ρ γ (ρ δ a * a⁻¹) = ρ δ a * a⁻¹ := hf δ γ
            have e1 : ρ (γ * δ) a = ρ γ (ρ δ a * a⁻¹) * ρ γ a := by
              rw [← map_mul, map_mul ρ, MulAut.mul_apply, inv_mul_cancel_right]
            rw [e1, h1]
            ac_rfl) }
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hk | hk
      · exfalso
        obtain ⟨g₁, g₂, hg⟩ := L3_not_comm
        apply hg
        apply (MonoidHom.ker_eq_bot_iff f).mp hk
        rw [map_mul, map_mul, mul_comm]
      · have h1 : ∀ γ, ρ γ a = a := by
          intro γ
          have h2 : γ ∈ f.ker := hk ▸ Subgroup.mem_top γ
          have h3 : ρ γ a * a⁻¹ = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp h2)
          exact mul_inv_eq_one.mp h3
        exact (QuotientGroup.eq_one_iff a).mpr h1
  have hEinvc : ∀ e ∈ E, ρ c e ∈ E := by
    intro e he
    have e1 : ρ c e = (ρ c e * e⁻¹) * e := by group
    rw [e1]
    exact E.mul_mem (hcE e) he
  have hEBinv : ∀ b ∈ EB, ρB c b ∈ EB := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨ρ c e, hEinvc e he, rfl⟩
  have hfpfB : ∀ b ∈ EB, ρB c b = b → b = 1 := by
    rintro _ ⟨e, he, rfl⟩ h0
    rw [QuotientGroup.mk'_apply, hρBmk] at h0
    have h1 := QuotientGroup.eq.mp h0
    have h2 : (ρ c e)⁻¹ * e ∈ E := E.mul_mem (E.inv_mem (hEinvc e he)) he
    have h3 := hEC₀ _ h2 h1
    have h4 : ρ c e = e := inv_mul_eq_one.mp h3
    rw [QuotientGroup.mk'_apply, hfpf e he h4, QuotientGroup.mk_one]
  have hirrB : ∀ U : Subgroup (A ⧸ C₀), (∀ γ, ∀ u ∈ U, ρB γ u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hUE : U ⊓ EB = ⊥
    · left
      have hcU : ∀ u ∈ U, ρB c u = u := by
        intro u hu
        have h1 : θB u ∈ U ⊓ EB :=
          ⟨U.mul_mem (hU c u hu) (U.inv_mem hu), hθBrange ▸ ⟨u, rfl⟩⟩
        rw [hUE, Subgroup.mem_bot] at h1
        exact mul_inv_eq_one.mp h1
      let K : Subgroup Γ :=
        { carrier := {γ | ∀ u ∈ U, ρB γ u = u}
          one_mem' := fun u _ => by rw [map_one]; rfl
          mul_mem' := fun {γ δ} hγ hδ u hu => by
            show ρB (γ * δ) u = u
            rw [map_mul, MulAut.mul_apply, hδ u hu, hγ u hu]
          inv_mem' := fun {γ} hγ u hu => by
            show ρB γ⁻¹ u = u
            have h1 := hγ _ (hU γ⁻¹ u hu)
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h1
            exact h1.symm }
      have hKn : K.Normal := by
        refine ⟨fun γ hγ δ u hu => ?_⟩
        show ρB (δ * γ * δ⁻¹) u = u
        rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hγ _ (hU δ⁻¹ u hu),
          ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hk | hk
      · exfalso
        have hcK : c ∈ K := hcU
        rw [hk, Subgroup.mem_bot] at hcK
        exact hc1 hcK
      · rw [eq_bot_iff]
        intro u hu
        rw [Subgroup.mem_bot]
        exact hCB u fun γ => (hk ▸ Subgroup.mem_top γ : γ ∈ K) u hu
    · right
      have hEU : EB ≤ U := by
        obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUE
        have hs1' : s ≠ 1 := fun h0 => hs1 (Subtype.ext h0)
        have hcs : ρB c s ≠ s := fun h0 => hs1' (hfpfB s hs.2 h0)
        have hcs1 : ρB c s ≠ 1 := by
          intro h0
          apply hs1'
          have := congrArg (ρB c⁻¹) h0
          rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_one] at this
        have h3 : 2 < Nat.card ↥(U ⊓ EB) := by
          have : Fintype ↥(U ⊓ EB) := Fintype.ofFinite _
          rw [Nat.card_eq_fintype_card]
          let t₁ : ↥(U ⊓ EB) := ⟨s, hs⟩
          let t₂ : ↥(U ⊓ EB) := ⟨ρB c s, ⟨hU c s hs.1, hEBinv s hs.2⟩⟩
          have h12 : t₁ ≠ t₂ := fun h0 => hcs (congrArg Subtype.val h0).symm
          have h01 : (1 : ↥(U ⊓ EB)) ≠ t₁ := fun h0 => hs1' (congrArg Subtype.val h0).symm
          have h02 : (1 : ↥(U ⊓ EB)) ≠ t₂ := fun h0 => hcs1 (congrArg Subtype.val h0).symm
          have hcard3 : ({1, t₁, t₂} : Finset ↥(U ⊓ EB)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair h12]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨h01, h02⟩
          have := Finset.card_le_univ ({1, t₁, t₂} : Finset ↥(U ⊓ EB))
          omega
        have h4 : Nat.card ↥(U ⊓ EB) ∣ 4 := hEB4 ▸ Subgroup.card_dvd_of_le inf_le_right
        have h5 : Nat.card ↥(U ⊓ EB) = 4 := by
          have h6 := Nat.le_of_dvd (by norm_num) h4
          interval_cases h : Nat.card ↥(U ⊓ EB)
          · norm_num at h4
          · rfl
        have h7 : U ⊓ EB = EB := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, hEB4])
        exact inf_eq_right.mp h7
      have h1 := hgen (U.comap (QuotientGroup.mk' C₀))
        (fun γ u hu => by
          show ((ρ γ u : A) : A ⧸ C₀) ∈ U
          rw [← hρBmk]
          exact hU γ _ hu)
        (fun e he => hEU ⟨e, he, rfl⟩)
      rw [eq_top_iff]
      intro b _
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective C₀ b
      have h2 : a ∈ U.comap (QuotientGroup.mk' C₀) := h1 ▸ Subgroup.mem_top a
      exact h2
  obtain ⟨α, βB, hβB⟩ := L3Small.exists_natural hB2 ρB hirrB hc3 hcardB
  set ρ' : Γ →* MulAut A := ρ.comp α.symm.toMonoidHom with hρ'
  have hρ'apply : ∀ γ x, ρ' γ x = ρ (α.symm γ) x := fun γ x => rfl
  set β : A →* Multiplicative Vec := βB.toMonoidHom.comp (QuotientGroup.mk' C₀) with hβdef
  have hβapply : ∀ x, β x = βB (x : A ⧸ C₀) := fun x => rfl
  have hβs : Function.Surjective β := βB.surjective.comp (QuotientGroup.mk'_surjective C₀)
  have hβeq : ∀ γ x, β (ρ' γ x) =
      Multiplicative.ofAdd (act γ (Multiplicative.toAdd (β x))) := by
    intro γ x
    rw [hβapply, hρ'apply, ← hρBmk, hβB, MulEquiv.apply_symm_apply, hβapply]
  have hkerβ : ∀ x, β x = 1 ↔ x ∈ C₀ := by
    intro x
    rw [hβapply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hEinf' : E ⊓ β.ker = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    exact hEC₀ e he.1 ((hkerβ e).mp he.2)
  have hE'4 : Nat.card (E.map β) = 4 := by
    have h1 := B1More.card_map_mul_card_inf_ker E β
    rw [hEinf', Subgroup.card_bot, mul_one, hE4] at h1
    exact h1
  have ha₀' : IsInvol (α a₀) := by
    refine ⟨?_, fun h0 => ha₀.2 (α.injective (by rw [h0, map_one]))⟩
    rw [← map_mul, ha₀.1, map_one]
  have hfixE' : ∀ x, β x ∈ E.map β → ρ' (α a₀) x = x := by
    intro x hx
    obtain ⟨e, he, hex⟩ := hx
    have hk : x * e⁻¹ ∈ C₀ := (hkerβ _).mp (by rw [map_mul, map_inv, hex]; exact mul_inv_cancel _)
    rw [hρ'apply, MulEquiv.symm_apply_apply]
    have e1 : x = (x * e⁻¹) * e := by group
    rw [e1, map_mul, hk a₀, hfix e he]
  have hgen' : Subgroup.closure {x | ∃ γ y, ρ' γ y * y⁻¹ = x} = ⊤ := by
    apply hgen
    · intro γ u hu
      induction hu using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨δ, y, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨α (γ * α.symm δ * γ⁻¹), ρ γ y, ?_⟩
        have e1 : ρ (γ * α.symm δ * γ⁻¹) (ρ γ y) = ρ γ (ρ (α.symm δ) y) := by
          rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hρinv γ y]
        show ρ' (α (γ * α.symm δ * γ⁻¹)) (ρ γ y) * (ρ γ y)⁻¹ = ρ γ (ρ' δ y * y⁻¹)
        rw [hρ'apply, hρ'apply, MulEquiv.symm_apply_apply, e1, map_mul, map_inv]
      | one => rw [map_one]; exact Subgroup.one_mem _
      | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
      | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
    · intro e he
      obtain ⟨x, rfl⟩ := hEc e he
      exact Subgroup.subset_closure ⟨α c, x, by rw [hρ'apply, MulEquiv.symm_apply_apply]⟩
  have h8 := card_eq_eight ρ' β hβs hβeq ha₀' hE'4 hfixE' hgen'
  have hB8 : Nat.card (A ⧸ C₀) = 8 := by
    rw [Nat.card_congr βB.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hC₀1 : Nat.card C₀ = 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C₀
    rw [h8, hB8] at h1
    omega
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (hkerβ x).mp hx
    have h2 : C₀ = ⊥ := Subgroup.card_eq_one.mp hC₀1
    rw [h2, Subgroup.mem_bot] at h1
    exact h1
  refine ⟨α, MulEquiv.ofBijective β ⟨hβinj, hβs⟩, fun γ x => ?_⟩
  show β (ρ γ x) = _
  have h1 := hβeq (α γ) x
  rw [hρ'apply, MulEquiv.symm_apply_apply] at h1
  exact h1

end CFSG.Quasithin.L3Split
