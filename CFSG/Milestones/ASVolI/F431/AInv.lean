module

public import CFSG.Milestones.ASVolI.F431.JRed2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF

section Goldschmidt

@[expose] def burnsideF4m_InvCent {D : Type} [Group D] (A : LieAmalgamExt D) : Prop :=
  ∀ x : ↥A.K, orderOf x = 2 → ∃ w : ↥A.K, IsConj x w ∧
    (Subgroup.centralizer ({w} : Set ↥A.K) ≤ A.Mb1 ∨
      Subgroup.centralizer ({w} : Set ↥A.K) ≤ A.Mb2)

theorem burnsideF4m_invCent_of_twoClassD {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (Lift.iK A hgen).range.index) {z0 t0 : D} (H : Lift.TwoClassD A z0 t0) :
    burnsideF4m_InvCent A := by
  intro x hx
  have hxsq : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx])
  obtain ⟨d, rfl⟩ := Lift.mem_range_of_sq_eq_one A hgen hodd hxsq
  have hinj := Lift.iK_injective A hgen hcen
  have hd2 : orderOf d = 2 := by
    rw [← orderOf_injective (Lift.iK A hgen) hinj d]
    exact hx
  rcases H.cls d hd2 with h | h
  · obtain ⟨P, hP, hC⟩ := H.cent_z
    exact ⟨Lift.iK A hgen z0, ((Lift.iK A hgen).map_isConj h).symm,
      Lift.cent_le_Mb A hgen hcen hP hC H.aut_z⟩
  · obtain ⟨P, hP, hC⟩ := H.cent_t
    exact ⟨Lift.iK A hgen t0, ((Lift.iK A hgen).map_isConj h).symm,
      Lift.cent_le_Mb A hgen hcen hP hC H.aut_t⟩

theorem burnsideF4m_map_conj_inv_map {Cg : Type} [Group Cg] (S : Subgroup Cg) (c : Cg) :
    (S.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = S := by
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply]
  constructor <;> intro h <;> simpa [mul_assoc] using h

end Goldschmidt

section Bridge

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_center_Gp (hyp : HypF_4_4g κ 2 f Gp M₁ M₂) : Subgroup.center ↥Gp = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h : (z : E) ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
    exact congrArg Subtype.val this
  rw [hyp.centralizer_trivial, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem burnsideF4m_hgen [Finite E] (hyp : HypF_4_4g κ 2 f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (MulAut.conj : ↥Gp →* MulAut ↥Gp).range ≤ (burnsideF4d_lieExtE hyp hyam).K := by
  haveI := hyp.normal
  intro φ hφ
  have h1 : φ ∈ (burnsideF4d_lieExtE hyp hyam).Mbar := (burnsideF4d_lieExtE hyp hyam).inn_le hφ
  have hK : (burnsideF4d_lieExtE hyp hyam).K = (burnsideF4d_rho Gp).range :=
    burnsideF4d_K_eq hyp hyam
  rw [hK]
  exact h1

theorem burnsideF4m_not_two_dvd [Finite E] (hyp : HypF_4_4g κ 2 f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    (hgen : (MulAut.conj : ↥Gp →* MulAut ↥Gp).range ≤ (burnsideF4d_lieExtE hyp hyam).K)
    (hcen : Subgroup.center ↥Gp = ⊥) (hodd : Odd Gp.index) :
    ¬ 2 ∣ (Lift.iK (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt hgen).range.index := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : Nat.card ↥(burnsideF4d_lieExtE hyp hyam).K = Nat.card E := by
    have hK' : (burnsideF4d_lieExtE hyp hyam).K = (burnsideF4d_rho Gp).range :=
      burnsideF4d_K_eq hyp hyam
    rw [hK', ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hr : Nat.card (Lift.iK (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt hgen).range =
      Nat.card ↥Gp :=
    (Nat.card_congr (MonoidHom.ofInjective
      (Lift.iK_injective (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt hgen hcen)).toEquiv).symm
  have h1 := Subgroup.card_mul_index
    (Lift.iK (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt hgen).range
  have h2 := Subgroup.card_mul_index Gp
  rw [hr, hK] at h1
  have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
  have e : (Lift.iK (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt hgen).range.index =
      Gp.index := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  rw [e]
  exact hodd.not_two_dvd_nat

theorem burnsideF4m_centInput_of_invCent [Finite E] (hyp : HypF_4_4g κ 2 f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    (hI : burnsideF4m_InvCent (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt)
    {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : (burnsideF4d_lieExtE hyp hyam).K = (burnsideF4d_rho Gp).range :=
    burnsideF4d_K_eq hyp hyam
  let θ : E ≃* ↥(burnsideF4d_lieExtE hyp hyam).K :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hK.symm)
  have hθ : ∀ e : E, ((θ e : ↥(burnsideF4d_lieExtE hyp hyam).K) : MulAut ↥Gp) =
      burnsideF4d_rho Gp e := fun e => rfl
  have hN1 : (burnsideF4d_lieExtE hyp hyam).N1 = M₁.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N1_eq hyp hyam
  have hN2 : (burnsideF4d_lieExtE hyp hyam).N2 = M₂.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N2_eq hyp hyam
  have hxo : orderOf (θ x) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact burnsideF4ja_orderOf_eq_two_iff.mpr ⟨hx1, hx2⟩
  obtain ⟨w', hxw, hw'⟩ := hI (θ x) hxo
  refine ⟨θ.symm w', ?_, ?_⟩
  · have := θ.symm.toMonoidHom.map_isConj hxw
    simpa using this
  · have key : ∀ (M : Subgroup E) (N : Subgroup (MulAut ↥Gp)), N = M.map (burnsideF4d_rho Gp) →
        Subgroup.centralizer ({w'} : Set ↥(burnsideF4d_lieExtE hyp hyam).K) ≤
          N.subgroupOf (burnsideF4d_lieExtE hyp hyam).K →
        Subgroup.centralizer ({θ.symm w'} : Set E) ≤ M := by
      intro M N hN hC c hc
      have h1 : θ c ∈ Subgroup.centralizer ({w'} : Set ↥(burnsideF4d_lieExtE hyp hyam).K) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        have := congrArg θ hc
        simpa using this
      have h2 := hC h1
      rw [Subgroup.mem_subgroupOf, hθ, hN] at h2
      obtain ⟨m, hm, hme⟩ := h2
      exact hinj hme ▸ hm
    rcases hw' with h | h
    · exact Or.inl (key M₁ _ hN1 h)
    · exact Or.inr (key M₂ _ hN2 h)

theorem burnsideF4m_centInput_of [Finite E] (hyp : HypF_4_4g κ 2 f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) (hodd : Odd Gp.index)
    (hL : ∀ hgen : (MulAut.conj : ↥Gp →* MulAut ↥Gp).range ≤ (burnsideF4d_lieExtE hyp hyam).K,
      Subgroup.center ↥Gp = ⊥ →
      ¬ 2 ∣ (Lift.iK (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt hgen).range.index →
      burnsideF4m_InvCent (burnsideF4d_lieExtE hyp hyam).toLieAmalgamExt)
    {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  have hgen := burnsideF4m_hgen hyp hyam
  have hcen := burnsideF4m_center_Gp hyp
  exact burnsideF4m_centInput_of_invCent hyp hyam
    (hL hgen hcen (burnsideF4m_not_two_dvd hyp hyam hgen hcen hodd)) hx1 hx2

end Bridge

end CFSG.ASVolI
