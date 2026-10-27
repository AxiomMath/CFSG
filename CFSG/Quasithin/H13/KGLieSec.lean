module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V]

theorem scalars_of_realizes {D : FFModel} {L : Subgroup (MulAut V)} {π : D.Gam →* ↥L}
    (h : D.RealizesVia L ⊤ ⊥ π) {ι : Type} (σ : ι → D.Amb ≃* D.Amb)
    (hsec : ∀ i x, x ∈ D.sec ↔ σ i x ∈ D.sec) (hker : ∀ i x, x ∈ D.ker ↔ σ i x ∈ D.ker)
    (hact : ∀ i γ x, σ i (D.act γ x) = D.act γ (σ i x))
    (hinj : ∀ x ∈ D.sec, x ∉ D.ker → ∀ i j, σ i x * (σ j x)⁻¹ ∈ D.ker → i = j) :
    ∃ m : ι → MulAut V, (∀ i, ∀ l ∈ L, m i * l = l * m i) ∧
      (∀ u : V, u ≠ 1 → Function.Injective fun i => m i u) ∧
      Nat.card V = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨hπs, -, -, -, -, hsecinv, -, β, hβs, hβk, hβe⟩ := h
  set N := D.ker.subgroupOf D.sec with hN
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext this
  set E : V ≃* (↥D.sec ⧸ N) :=
    (Subgroup.topEquiv (G := V)).symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩) with hE
  have hEapp : ∀ w : V, E w = β ⟨w, mem_top w⟩ := fun w => rfl
  have hmap : ∀ i, D.sec.map (σ i).toMonoidHom = D.sec := fun i => by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hsec i y).1 hy
    · intro hx
      refine ⟨(σ i).symm x, (hsec i _).2 (by simpa using hx), by simp⟩
  set ρ : ι → (↥D.sec ≃* ↥D.sec) := fun i =>
    ((σ i).subgroupMap D.sec).trans (MulEquiv.subgroupCongr (hmap i)) with hρ
  have hρapp : ∀ i (x : ↥D.sec), ((ρ i x : ↥D.sec) : D.Amb) = σ i x := fun i x => rfl
  have hNmap : ∀ i, N.map (ρ i).toMonoidHom = N := fun i => by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ((ρ i y : ↥D.sec) : D.Amb) ∈ D.ker
      rw [hρapp]
      exact (hker i _).1 hy
    · intro hx
      refine ⟨(ρ i).symm x, ?_, by simp⟩
      show (((ρ i).symm x : ↥D.sec) : D.Amb) ∈ D.ker
      have h1 : σ i (((ρ i).symm x : ↥D.sec) : D.Amb) = (x : D.Amb) := by
        rw [← hρapp, MulEquiv.apply_symm_apply]
      exact (hker i _).2 (by rw [h1]; exact hx)
  set τ : ι → ((↥D.sec ⧸ N) ≃* (↥D.sec ⧸ N)) := fun i =>
    QuotientGroup.congr N N (ρ i) (hNmap i) with hτ
  have hτmk : ∀ i (x : ↥D.sec), τ i (QuotientGroup.mk x) = QuotientGroup.mk (ρ i x) :=
    fun i x => QuotientGroup.congr_mk N N (ρ i) (hNmap i) x
  refine ⟨fun i => E.trans ((τ i).trans E.symm), ?_, ?_, ?_⟩
  · intro i l hl
    obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
    have hl' : l = ((π γ : ↥L) : MulAut V) := (congrArg Subtype.val hγ).symm
    rw [hl']
    ext w
    apply E.injective
    simp only [MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (E w)
    have hxs : D.act γ (x : D.Amb) ∈ D.sec := hsecinv γ x x.2
    have h1 : E (((π γ : ↥L) : MulAut V) w) = QuotientGroup.mk ⟨D.act γ (x : D.Amb), hxs⟩ := by
      rw [hEapp]
      exact hβe γ ⟨w, mem_top w⟩ x (mem_top _) hxs (by rw [← hEapp, hx])
    set w' := E.symm (τ i (E w)) with hw'
    have hw'E : E w' = QuotientGroup.mk (ρ i x) := by
      rw [hw', MulEquiv.apply_symm_apply, ← hx, hτmk]
    have hys : D.act γ ((ρ i x : ↥D.sec) : D.Amb) ∈ D.sec := hsecinv γ _ (ρ i x).2
    have h2 : E (((π γ : ↥L) : MulAut V) w') =
        QuotientGroup.mk ⟨D.act γ ((ρ i x : ↥D.sec) : D.Amb), hys⟩ := by
      rw [hEapp]
      exact hβe γ ⟨w', mem_top w'⟩ (ρ i x) (mem_top _) hys (by rw [← hEapp, hw'E])
    rw [h1, h2, hτmk]
    congr 1
    apply Subtype.ext
    rw [hρapp]
    show σ i (D.act γ (x : D.Amb)) = D.act γ ((ρ i x : ↥D.sec) : D.Amb)
    rw [hρapp, hact]
  · intro u hu i j hij
    have h1 : τ i (E u) = τ j (E u) := by
      have := congrArg E hij
      simpa using this
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (E u)
    rw [← hx, hτmk, hτmk, QuotientGroup.eq] at h1
    have hxk : (x : D.Amb) ∉ D.ker := by
      intro hk
      apply hu
      apply E.injective
      rw [map_one, ← hx]
      exact (QuotientGroup.eq_one_iff x).2 hk
    have h2 : σ i x * (σ j x)⁻¹ ∈ D.ker := by
      have h3 : ((((ρ i x)⁻¹ * ρ j x : ↥D.sec)) : D.Amb) ∈ D.ker := h1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hρapp, hρapp] at h3
      have h4 := D.ker.inv_mem h3
      rwa [mul_inv_rev, inv_inv, mul_comm] at h4
    exact hinj x x.2 hxk i j h2
  · exact Nat.card_congr E.toEquiv

end CFSG.Quasithin.H13.KGLie
