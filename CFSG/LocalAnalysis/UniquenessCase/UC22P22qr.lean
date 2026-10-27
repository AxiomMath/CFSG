module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22n

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_mem_ctilde {M V₀ V : Subgroup G} {c : G} :
    c ∈ F11.CTilde M V₀ V ↔ c ∈ M ∧ c ∈ normalizer (V₀ : Set G) ∧
      ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀ := by
  simp only [F11.CTilde, Subgroup.mem_iInf, F11.CElt, Subgroup.mem_mk]
  constructor
  · intro h
    exact ⟨(h 1 V.one_mem).1, (h 1 V.one_mem).2.1, fun v hv => (h v hv).2.2⟩
  · rintro ⟨h1, h2, h3⟩ v hv
    exact ⟨h1, h2, h3 v hv⟩

theorem uc22p22q_ctilde_conj_mem {M V₀ V : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hV₀ : M ≤ normalizer (V₀ : Set G)) {m c : G} (hm : m ∈ M) (hc : c ∈ F11.CTilde M V₀ V) :
    m * c * m⁻¹ ∈ F11.CTilde M V₀ V := by
  obtain ⟨hcM, hcN, hcv⟩ := uc22p22q_mem_ctilde.1 hc
  refine uc22p22q_mem_ctilde.2 ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hV₀ hm) hcN) (Subgroup.inv_mem _ (hV₀ hm)), fun v hv => ?_⟩
  have hw : m⁻¹ * v * m ∈ V := by
    have := (mem_normalizer_iff.1 (hV (M.inv_mem hm)) v).1 hv
    simpa using this
  have h2 := (mem_normalizer_iff.1 (hV₀ hm) _).1 (hcv _ hw)
  have e : m * (c * (m⁻¹ * v * m) * c⁻¹ * (m⁻¹ * v * m)⁻¹) * m⁻¹ =
      m * c * m⁻¹ * v * (m * c * m⁻¹)⁻¹ * v⁻¹ := by group
  rwa [e] at h2

theorem uc22p22q_conj_eq_of_trivial_action {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V₀ : Subgroup G}
    (hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1) {e v : G} (hep : e ^ p = 1) (he0 : ∀ d ∈ V₀, e * d * e⁻¹ = d)
    (hv : e * v * e⁻¹ * v⁻¹ ∈ V₀) : e * v * e⁻¹ = v := by
  set f : G := e * v * e⁻¹ * v⁻¹ with hf
  have hfv : e * v * e⁻¹ = f * v := by simp [hf]
  have hf2 : f ^ 2 = 1 := hV₀exp f hv
  have hfe : e * f * e⁻¹ = f := he0 f hv
  have key : ∀ k : ℕ, e ^ k * v * (e ^ k)⁻¹ = f ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc e ^ (k + 1) * v * (e ^ (k + 1))⁻¹ = e * (e ^ k * v * (e ^ k)⁻¹) * e⁻¹ := by group
        _ = e * (f ^ k * v) * e⁻¹ := by rw [ih]
        _ = (e * f * e⁻¹) ^ k * (e * v * e⁻¹) := by rw [conj_pow]; group
        _ = f ^ (k + 1) * v := by rw [hfe, hfv, pow_succ']; group
  have hfp : f ^ p = 1 := by
    have h := key p
    rw [hep] at h
    simp only [inv_one, mul_one, one_mul] at h
    exact (mul_eq_right.1 h.symm)
  obtain ⟨m, hm⟩ := (hp.eq_two_or_odd'.resolve_left hp2)
  have hf1 : f = 1 := by
    have : f ^ p = f := by
      rw [hm, pow_succ, pow_mul, hf2, one_pow, one_mul]
    rw [← this]
    exact hfp
  rw [hfv, hf1, one_mul]

theorem uc22p22q_exists_fixed_in_coset {V₀ V : Subgroup G} {x u : G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1) (hV₀V : V₀ ≤ V)
    (hxV₀ : ∀ w ∈ V₀, x * w * x⁻¹ ∈ V₀) (hx3 : x ^ 3 = 1) (hu : u ∈ V)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ V₀) : ∃ d ∈ V₀, x * (u * d) * x⁻¹ = u * d := by
  set g : G := x * u * x⁻¹ * u⁻¹ with hg
  set g₁ : G := x * g * x⁻¹ with hg₁
  set g₂ : G := x * g₁ * x⁻¹ with hg₂
  have hg₁V₀ : g₁ ∈ V₀ := hxV₀ g hxu
  have hg₂V₀ : g₂ ∈ V₀ := hxV₀ g₁ hg₁V₀
  have hxu' : x * u * x⁻¹ = g * u := by simp [hg]
  have h3 : g₂ * g₁ * g = 1 := by
    have e1 : x * (g * u) * x⁻¹ = g₁ * (g * u) := by
      calc x * (g * u) * x⁻¹ = (x * g * x⁻¹) * (x * u * x⁻¹) := by group
        _ = g₁ * (g * u) := by rw [← hg₁, hxu']
    have e2 : x * (g₁ * (g * u)) * x⁻¹ = g₂ * (g₁ * (g * u)) := by
      calc x * (g₁ * (g * u)) * x⁻¹ = (x * g₁ * x⁻¹) * (x * (g * u) * x⁻¹) := by group
        _ = g₂ * (g₁ * (g * u)) := by rw [← hg₂, e1]
    have hx3' : x * (x * x) = 1 := by simpa [pow_succ, mul_assoc] using hx3
    have e3 : x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ = g₂ * (g₁ * (g * u)) := by
      rw [hxu', e1, e2]
    have e4 : x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ = u := by
      calc x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * u * (x * (x * x))⁻¹ := by group
        _ = u := by rw [hx3']; group
    have e5 : g₂ * g₁ * g * u = 1 * u := by
      calc g₂ * g₁ * g * u = g₂ * (g₁ * (g * u)) := by group
        _ = u := e3.symm.trans e4
        _ = 1 * u := (one_mul u).symm
    exact mul_right_cancel e5
  refine ⟨g₁, hg₁V₀, ?_⟩
  have hgg : g * g₂ = g₁ := by
    have e5 : g₁ = g₂⁻¹ * g⁻¹ := by
      calc g₁ = g₂⁻¹ * (g₂ * g₁ * g) * g⁻¹ := by group
        _ = g₂⁻¹ * 1 * g⁻¹ := by rw [h3]
        _ = g₂⁻¹ * g⁻¹ := by group
    have hg2 : g₂⁻¹ = g₂ := inv_eq_of_mul_eq_one_right (by
      have := hV₀exp g₂ hg₂V₀
      rwa [pow_two] at this)
    have hg1 : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by
      have := hV₀exp g hxu
      rwa [pow_two] at this)
    rw [e5, hg2, hg1]
    exact hVab g (hV₀V hxu) g₂ (hV₀V hg₂V₀)
  have hxg₁ : x * g₁ * x⁻¹ = g₂ := rfl
  calc x * (u * g₁) * x⁻¹ = (x * u * x⁻¹) * (x * g₁ * x⁻¹) := by group
    _ = g * u * g₂ := by rw [hxu', hxg₁]
    _ = u * (g * g₂) := by
      rw [hVab g (hV₀V hxu) u hu]; group
    _ = u * g₁ := by rw [hgg]

theorem uc22p22q_pRank_sub_one_le {p : ℕ} (hp : p.Prime) {M C : Subgroup G}
    [(C.subgroupOf M).Normal] (hC : CFSG.Open.pRank p C ≤ 1) :
    CFSG.Open.pRank p M - 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ C.subgroupOf M)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  set r := CFSG.Open.pRank p M with hr
  let π : ↥M →* ↥M ⧸ C.subgroupOf M := QuotientGroup.mk' (C.subgroupOf M)
  have hE' : IsElemAbelian p (E.subgroupOf M) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p E (E.subgroupOf M)
      (Subgroup.subgroupOfEquivOfLe hEM).symm hE
  let ρ : ↥(E.subgroupOf M) →* ↥M ⧸ C.subgroupOf M := π.comp (E.subgroupOf M).subtype
  have hk : Nat.card ρ.ker * Nat.card ρ.range = Nat.card (E.subgroupOf M) :=
    Subgroup.card_ker_mul_card_range ρ
  have hEcard : Nat.card (E.subgroupOf M) = p ^ r := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  have hrange : ρ.range = (E.subgroupOf M).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hrel : IsElemAbelian p ρ.range := by
    rw [hrange]
    exact CFSG.SectionRank.isElemAbelian_map hE' π
  obtain ⟨k, hk'⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hrel)
  have hkle : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ C.subgroupOf M)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hrel hk'
  have hker : Nat.card ρ.ker ≤ p := by
    have hEC : IsElemAbelian p (E ⊓ C) := uc22p22n_isElemAbelian_of_le inf_le_left hE
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hEC)
    have hj1 : j ≤ 1 := (CFSG.SectionRank.le_pRank hp.one_lt inf_le_right hEC hj).trans hC
    have hmem : ∀ e : ↥ρ.ker, (((e.1 : ↥(E.subgroupOf M)) : ↥M) : G) ∈ E ⊓ C := by
      intro e
      refine ⟨e.1.2, ?_⟩
      have h2 : π ((e.1 : ↥(E.subgroupOf M)) : ↥M) = 1 := e.2
      exact Subgroup.mem_subgroupOf.1
        ((QuotientGroup.eq_one_iff (N := C.subgroupOf M) ((e.1 : ↥(E.subgroupOf M)) : ↥M)).1 h2)
    have hf : Function.Injective (fun e : ↥ρ.ker => (⟨_, hmem e⟩ : ↥(E ⊓ C))) := by
      intro e₁ e₂ h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    have := Nat.card_le_card_of_injective _ hf
    rw [hj] at this
    exact this.trans (by simpa using Nat.pow_le_pow_right hp.pos hj1)
  have h1 : p ^ r ≤ p * p ^ k := by
    rw [← hEcard, ← hk, hk']
    exact Nat.mul_le_mul_right _ hker
  have h2 : r ≤ k + 1 :=
    (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [pow_succ']; exact h1)
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
