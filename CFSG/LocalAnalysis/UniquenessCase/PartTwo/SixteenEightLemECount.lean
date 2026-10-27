module

public import CFSG.GH74.QTGen4.Leaves.L14742Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type*} [CommGroup T]

private theorem s16f_not_sq_dvd_168 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 168 := by
  intro h
  have hle : q ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have hq13 : q ≤ 13 := by nlinarith
  interval_cases q <;> first | exact hq2 rfl | (norm_num at h; done) | (norm_num at hq; done)

private theorem s16f_map_eq_of_mem_stabSub {U : Subgroup T} {g : MulAut T}
    (hg : g ∈ stabSub U) : U.map (g : T →* T) = U := by
  ext u
  constructor
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hu
    exact (mem_stabSub.1 hg v).2 hv
  · intro hu
    refine Subgroup.mem_map.2 ⟨g.symm u, ?_, ?_⟩
    · rw [← (mem_stabSub.1 hg (g.symm u))]
      simpa using hu
    · exact MulEquiv.apply_symm_apply g u

theorem s16f_exists_quotHom (U : Subgroup T) :
    ∃ ρ : ↥(stabSub U) →* MulAut (T ⧸ U),
      ∀ (g : ↥(stabSub U)) (x : T),
        ρ g (QuotientGroup.mk x) = QuotientGroup.mk ((g : MulAut T) x) := by
  refine ⟨MonoidHom.mk' (fun g => QuotientGroup.congr U U (g : MulAut T)
      (s16f_map_eq_of_mem_stabSub g.2)) ?_, ?_⟩
  · intro g h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply]
      simp only [QuotientGroup.congr_mk]
      rfl
  · intro g x
    exact QuotientGroup.congr_mk U U (g : MulAut T) (s16f_map_eq_of_mem_stabSub g.2) x

theorem s16f_card_le_sq_of_sup [Finite T] {q : ℕ} (hq : q.Prime) {E : Subgroup (MulAut T)} {a : ℕ}
    (hE : Nat.card E = q ^ a) {W₁ W₂ : Subgroup T} (hsup : W₁ ⊔ W₂ = ⊤)
    (hE₁ : E ≤ stabSub W₁) (hE₂ : E ≤ stabSub W₂) {m₁ m₂ : ℕ}
    (hm₁ : Nat.card (MulAut ↥W₁) = m₁) (hm₂ : Nat.card (MulAut ↥W₂) = m₂)
    (hq₁ : ¬ q ^ 2 ∣ m₁) (hq₂ : ¬ q ^ 2 ∣ m₂) : Nat.card E ≤ q ^ 2 := by
  have h1 := s16n9b_card_le_mul_card_inf_centSub hq hE hE₁ hm₁ hq₁
  have hdvd : Nat.card ↥(E ⊓ centSub W₁) ∣ q ^ a :=
    hE ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hq).1 hdvd
  have h2 := s16n9b_card_le_mul_card_inf_centSub hq hb (inf_le_left.trans hE₂) hm₂ hq₂
  have h3 : E ⊓ centSub W₁ ⊓ centSub W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨-, hx1⟩, hx2⟩ := hx
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro t
    have ht : t ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top t
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 ht
    rw [map_mul, hx1 y hy, hx2 z hz]
    rfl
  rw [h3, Subgroup.card_bot] at h2
  calc Nat.card E ≤ q * Nat.card ↥(E ⊓ centSub W₁) := h1
    _ ≤ q * (q * 1) := Nat.mul_le_mul_left q h2
    _ = q ^ 2 := by ring

theorem s16f_card_le_sq_of_faithful [Finite T] (hT : ∀ v : T, v ^ 2 = 1)
    {A : Subgroup (MulAut T)} {U W₁ W₂ : Subgroup T}
    (hU : ∀ φ ∈ A, U.map φ.toMonoidHom = U)
    (hfaith : ∀ φ ∈ A, (∀ v : T, φ v * v⁻¹ ∈ U) → φ = 1) (hsup : W₁ ⊔ W₂ = ⊤)
    (h₁ : (U ⊓ W₁).relIndex W₁ ≤ 8) (h₂ : (U ⊓ W₂).relIndex W₂ ≤ 8)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut T)} (hEA : E ≤ A)
    (hE₁ : E ≤ stabSub W₁) (hE₂ : E ≤ stabSub W₂) {a : ℕ} (hE : Nat.card E = q ^ a) :
    Nat.card E ≤ q ^ 2 := by
  have hAst : A ≤ stabSub U := fun φ hφ => s16n9b_mem_stabSub_of_map_eq (hU φ hφ)
  obtain ⟨ρ, hρ⟩ := s16f_exists_quotHom U
  let ψ : ↥E →* MulAut (T ⧸ U) :=
    MonoidHom.mk' (fun e => ρ (Subgroup.inclusion (hEA.trans hAst) e)) (by
      intro a b
      simp)
  have hψ_apply : ∀ (e : ↥E) (x : T),
      ψ e (QuotientGroup.mk x) = QuotientGroup.mk ((e : MulAut T) x) :=
    fun e x => hρ (Subgroup.inclusion (hEA.trans hAst) e) x
  have hψ_inj : Function.Injective ψ := by
    intro e f hef
    have hpoint : ∀ x : T, ((e : MulAut T) * (f : MulAut T)⁻¹) x * x⁻¹ ∈ U := by
      intro x
      have h2 : (ψ e) (QuotientGroup.mk ((f : MulAut T).symm x)) =
          (ψ f) (QuotientGroup.mk ((f : MulAut T).symm x)) := by rw [hef]
      rw [hψ_apply e ((f : MulAut T).symm x), hψ_apply f ((f : MulAut T).symm x),
        MulEquiv.apply_symm_apply] at h2
      have h3 : (e : MulAut T) ((f : MulAut T).symm x) * x⁻¹ ∈ U := by
        have h4 := (QuotientGroup.eq_iff_div_mem).1 h2
        rwa [div_eq_mul_inv] at h4
      rwa [MulAut.mul_apply, MulAut.inv_apply]
    have h4 : (e : MulAut T) * (f : MulAut T)⁻¹ = 1 :=
      hfaith _ (A.mul_mem (hEA e.2) (A.inv_mem (hEA f.2))) hpoint
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  let E' : Subgroup (MulAut (T ⧸ U)) := ψ.range
  have hcardE' : Nat.card E' = q ^ a := by
    have h := Nat.card_congr (MonoidHom.ofInjective hψ_inj).toEquiv
    change Nat.card ↥(ψ.range) = q ^ a
    rw [← h]
    exact hE
  let W₁' : Subgroup (T ⧸ U) := W₁.map (QuotientGroup.mk' U)
  let W₂' : Subgroup (T ⧸ U) := W₂.map (QuotientGroup.mk' U)
  have hsup' : W₁' ⊔ W₂' = ⊤ := by
    show W₁.map (QuotientGroup.mk' U) ⊔ W₂.map (QuotientGroup.mk' U) = ⊤
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top, QuotientGroup.range_mk']
  have hle₁ : Nat.card ↥W₁' ≤ 8 := by
    have h := Subgroup.relIndex_ker W₁ (QuotientGroup.mk' U)
    rw [QuotientGroup.ker_mk'] at h
    show Nat.card ↥(W₁.map (QuotientGroup.mk' U)) ≤ 8
    rw [← h, ← Subgroup.inf_relIndex_right]
    exact h₁
  have hle₂ : Nat.card ↥W₂' ≤ 8 := by
    have h := Subgroup.relIndex_ker W₂ (QuotientGroup.mk' U)
    rw [QuotientGroup.ker_mk'] at h
    show Nat.card ↥(W₂.map (QuotientGroup.mk' U)) ≤ 8
    rw [← h, ← Subgroup.inf_relIndex_right]
    exact h₂
  have hpowX : ∀ x : T ⧸ U, x ^ 2 = 1 := fun x =>
    QuotientGroup.induction_on x fun v => by
      rw [← QuotientGroup.mk_pow, hT v, QuotientGroup.mk_one]
  have hpow₁ : ∀ a : ↥W₁', a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa using hpowX (a : T ⧸ U))
  have hpow₂ : ∀ a : ↥W₂', a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa using hpowX (a : T ⧸ U))
  have hdvd₁ : Nat.card (MulAut ↥W₁') ∣ 168 :=
    CFSG.GH74.QTGen4.Leaves.L14742.card_mulAut_dvd_168 (fun a b => mul_comm a b) hpow₁ hle₁
  have hdvd₂ : Nat.card (MulAut ↥W₂') ∣ 168 :=
    CFSG.GH74.QTGen4.Leaves.L14742.card_mulAut_dvd_168 (fun a b => mul_comm a b) hpow₂ hle₂
  have hq₁' : ¬ q ^ 2 ∣ Nat.card (MulAut ↥W₁') :=
    fun h => s16f_not_sq_dvd_168 hq hq2 (h.trans hdvd₁)
  have hq₂' : ¬ q ^ 2 ∣ Nat.card (MulAut ↥W₂') :=
    fun h => s16f_not_sq_dvd_168 hq hq2 (h.trans hdvd₂)
  have hmap₁ : ∀ g : ↥E, W₁'.map (ψ g).toMonoidHom = W₁' := by
    intro g
    show (W₁.map (QuotientGroup.mk' U)).map (ψ g).toMonoidHom =
      W₁.map (QuotientGroup.mk' U)
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      change ψ g (QuotientGroup.mk w) ∈ W₁.map (QuotientGroup.mk' U)
      rw [hψ_apply g w]
      exact Subgroup.mem_map.2 ⟨(g : MulAut T) w, (mem_stabSub.1 (hE₁ g.2) w).2 hw, rfl⟩
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨ψ g⁻¹ (QuotientGroup.mk w), ?_, ?_⟩
      · rw [hψ_apply g⁻¹ w]
        exact Subgroup.mem_map.2
          ⟨(g⁻¹ : MulAut T) w, (mem_stabSub.1 (hE₁ (E.inv_mem g.2)) w).2 hw, rfl⟩
      · show ψ g (ψ g⁻¹ (QuotientGroup.mk w)) = QuotientGroup.mk w
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hmap₂ : ∀ g : ↥E, W₂'.map (ψ g).toMonoidHom = W₂' := by
    intro g
    show (W₂.map (QuotientGroup.mk' U)).map (ψ g).toMonoidHom =
      W₂.map (QuotientGroup.mk' U)
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      change ψ g (QuotientGroup.mk w) ∈ W₂.map (QuotientGroup.mk' U)
      rw [hψ_apply g w]
      exact Subgroup.mem_map.2 ⟨(g : MulAut T) w, (mem_stabSub.1 (hE₂ g.2) w).2 hw, rfl⟩
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨ψ g⁻¹ (QuotientGroup.mk w), ?_, ?_⟩
      · rw [hψ_apply g⁻¹ w]
        exact Subgroup.mem_map.2
          ⟨(g⁻¹ : MulAut T) w, (mem_stabSub.1 (hE₂ (E.inv_mem g.2)) w).2 hw, rfl⟩
      · show ψ g (ψ g⁻¹ (QuotientGroup.mk w)) = QuotientGroup.mk w
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hst₁ : E' ≤ stabSub W₁' := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 (show φ ∈ ψ.range from hφ)
    exact s16n9b_mem_stabSub_of_map_eq (hmap₁ g)
  have hst₂ : E' ≤ stabSub W₂' := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 (show φ ∈ ψ.range from hφ)
    exact s16n9b_mem_stabSub_of_map_eq (hmap₂ g)
  have hmain : Nat.card E' ≤ q ^ 2 :=
    s16f_card_le_sq_of_sup (T := T ⧸ U) (E := E') (W₁ := W₁') (W₂ := W₂')
      (m₁ := Nat.card (MulAut ↥W₁')) (m₂ := Nat.card (MulAut ↥W₂'))
      hq hcardE' hsup' hst₁ hst₂ rfl rfl hq₁' hq₂'
  calc Nat.card E = Nat.card E' := Nat.card_congr (MonoidHom.ofInjective hψ_inj).toEquiv
    _ ≤ q ^ 2 := hmain

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
