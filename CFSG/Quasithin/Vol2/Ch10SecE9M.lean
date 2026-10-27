module

public import CFSG.Quasithin.Vol2.Ch10SecE9L
public import CFSG.Quasithin.Vol2.Ch10SecQ34LK
public import CFSG.Quasithin.Vol2.Ch10SecE9J

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

omit [Finite G] in
theorem exists_pow_of_cyc (hD : ParData A K E) (hD2 : ParData2 K E) {k₀ : L32.Γ}
    (hk₀ : k₀ ∈ K) (hk₀E : k₀ ∉ E) {k : L32.Γ} (hk : k ∈ K) :
    ∃ a : ℕ, k * (k₀ ^ a)⁻¹ ∈ E := by
  rcases hD2.cyc k₀ hk₀ k hk hk₀E with h | h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩
  · refine ⟨2, ?_⟩
    have h3 := hD.cube k₀ hk₀
    rw [show k * (k₀ ^ 2)⁻¹ = (k * k₀) * (k₀ * k₀ * k₀)⁻¹ by group]
    exact E.mul_mem h (E.inv_mem h3)

theorem conj_mem_pCoreOf_of_normalizes (h : MaxCtx T L I t Ψ c) (hD : ParData A K E)
    (hD2 : ParData2 K E) {y : G} (hy3 : orderOf y = 3)
    (hyT : y ∈ Subgroup.normalizer (T1 T L : Set G))
    (hyX : y ∈ Subgroup.normalizer (XOf T L Ψ A : Set G)) {x : G} (hx : x ∈ XOf T L Ψ A) :
    y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (XOf T L Ψ A) := by
  have hXL0 := XOf_le_fsuL0 h hD
  set X := XOf T L Ψ A with hXdef
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := (isXi_XOf h hD).2.1
  obtain ⟨d, hdU, k₀, hk₀K, hnc⟩ := hD.noncomm
  have hd : ∀ k ∈ K, d * k * d⁻¹ * k ∈ E := by
    rcases hD2.sign d hdU with h1 | h1
    · exact absurd (h1 k₀ hk₀K) hnc
    · exact h1
  have hk₀E : k₀ ∉ E := fun hk => hnc (E.mul_mem (hD.normE d (hD.uA hdU) k₀ hk) (E.inv_mem hk))
  have himg := imgIn_XOf h hD
  have hq₁ : (k₀, (1 : L32.Γ)) ∈ imgIn Ψ X := himg ▸ ⟨hk₀K, K.one_mem⟩
  have hq₂ : ((1 : L32.Γ), k₀) ∈ imgIn Ψ X := himg ▸ ⟨K.one_mem, hk₀K⟩
  obtain ⟨x₁, hx₁L, hx₁, hΨx₁⟩ := mem_imgIn.mp hq₁
  obtain ⟨x₂, hx₂L, hx₂, hΨx₂⟩ := mem_imgIn.mp hq₂
  have hT0 := h.hC.T0
  have hd₁ : (d, (1 : L32.Γ)) ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ :=
    hT0 ▸ ⟨hdU, L32.U3.one_mem⟩
  have hd₂ : ((1 : L32.Γ), d) ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ :=
    hT0 ▸ ⟨L32.U3.one_mem, hdU⟩
  obtain ⟨⟨t₁, ht₁L⟩, ht₁, hΨt₁⟩ := hd₁
  obtain ⟨⟨t₂, ht₂L⟩, ht₂, hΨt₂⟩ := hd₂
  have ht₁T : t₁ ∈ T := (Subgroup.mem_subgroupOf.mp ht₁).1
  have ht₂T : t₂ ∈ T := (Subgroup.mem_subgroupOf.mp ht₂).1
  have ht₁T₁ : t₁ ∈ T1 T L := SecA.T0_le_T1 h.hyp.fsu.maximal.1 (Subgroup.mem_subgroupOf.mp ht₁)
  have hX₁ : X.map (MulAut.conj t₁).toMonoidHom = X := A38.map_conj_eq_iff.mpr (hTX ht₁T)
  have hX₂ : X.map (MulAut.conj t₂).toMonoidHom = X := A38.map_conj_eq_iff.mpr (hTX ht₂T)
  have hXy : X.map (MulAut.conj y).toMonoidHom = X := A38.map_conj_eq_iff.mpr hyX
  have hτT₁ : y * t₁ * y⁻¹ ∈ T1 T L := (Subgroup.mem_normalizer_iff.mp hyT t₁).mp ht₁T₁
  have hXτ : X.map (MulAut.conj (y * t₁ * y⁻¹)).toMonoidHom = X :=
    A38.map_conj_eq_iff.mpr (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyX (hTX ht₁T))
      (Subgroup.inv_mem _ hyX))
  have hmem : ∀ {g : G}, X.map (MulAut.conj g).toMonoidHom = X → ∀ x ∈ X, g * x * g⁻¹ ∈ X :=
    fun {g} hg x hx => by
      have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
      rw [hg] at this; exact this
  have c₁ : ∀ x (hx : x ∈ X), Ψ ⟨t₁ * x * t₁⁻¹, hXL0 (hmem hX₁ x hx)⟩ =
      (d * (Ψ ⟨x, hXL0 hx⟩).1 * d⁻¹, (Ψ ⟨x, hXL0 hx⟩).2) := fun x hx => by
    rw [psi_conj ht₁L (hXL0 hx), hΨt₁]
    ext <;> simp
  have c₂ : ∀ x (hx : x ∈ X), Ψ ⟨t₂ * x * t₂⁻¹, hXL0 (hmem hX₂ x hx)⟩ =
      ((Ψ ⟨x, hXL0 hx⟩).1, d * (Ψ ⟨x, hXL0 hx⟩).2 * d⁻¹) := fun x hx => by
    rw [psi_conj ht₂L (hXL0 hx), hΨt₂]
    ext <;> simp
  have hK : ∀ x (hx : x ∈ X), (Ψ ⟨x, hXL0 hx⟩).1 ∈ K ∧ (Ψ ⟨x, hXL0 hx⟩).2 ∈ K := fun x hx =>
    Subgroup.mem_prod.mp (mem_prod_of_mem_XOf h hD hx)
  have hΨ1 : Ψ ⟨1, hXL0 X.one_mem⟩ = 1 := map_one Ψ
  have h3 : ∀ v : ↥X ⧸ CFSG.pCore 2 ↥X, v ^ 3 = 1 := by
    intro v
    obtain ⟨⟨x', hx'⟩, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow]
    exact (SecA.mk_eq_one_iff _).mpr (by simpa using pow_three_mem h hD hx')
  have hσrel : ∀ v, C10P34.conjQuot X X t₂ hX₂ v = (C10P34.conjQuot X X t₁ hX₁ v)⁻¹ := by
    intro v
    obtain ⟨⟨x', hx'⟩, rfl⟩ := QuotientGroup.mk_surjective v
    rw [C10P34.conjQuot_mk hX₂ hx' (hmem hX₂ x' hx'), C10P34.conjQuot_mk hX₁ hx' (hmem hX₁ x' hx'),
      ← QuotientGroup.mk_inv]
    refine (mkO2_eq_iff h hD (hmem hX₂ x' hx') (X.inv_mem (hmem hX₁ x' hx'))).mpr ?_
    rw [c₂ x' hx', psi_inv (hXL0 (hmem hX₁ x' hx')), inv_inv, c₁ x' hx', Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.snd_mul]
    obtain ⟨hk, hk'⟩ := hK x' hx'
    refine ⟨?_, hd _ hk'⟩
    have h1 := hD.normE _ (hD.KA hk) _ (hd _ hk)
    rwa [show (Ψ ⟨x', hXL0 hx'⟩).1 * (d * (Ψ ⟨x', hXL0 hx'⟩).1 * d⁻¹ * (Ψ ⟨x', hXL0 hx'⟩).1) *
        ((Ψ ⟨x', hXL0 hx'⟩).1)⁻¹ = (Ψ ⟨x', hXL0 hx'⟩).1 * (d * (Ψ ⟨x', hXL0 hx'⟩).1 * d⁻¹) by
      group] at h1
  have hβ3 : C10P34.conjQuot X X y hXy ^ 3 = 1 := by
    have := C10P34.conjQuot_pow_orderOf hXy
    rwa [hy3] at this
  have hDc := conjQuot_cases h hD hD2 hd ht₁L ht₂L hΨt₁ hΨt₂ hX₁ hX₂ hτT₁ hXτ
  rw [← conjQuot_conj hXy hX₁ hXτ] at hDc
  have hw : C10P34.conjQuot X X t₁ hX₁ (mkO2 X x₂ hx₂) = mkO2 X x₂ hx₂ := by
    rw [C10P34.conjQuot_mk hX₁ hx₂ (hmem hX₁ x₂ hx₂)]
    refine (mkO2_eq_iff h hD (hmem hX₁ x₂ hx₂) hx₂).mpr ?_
    rw [c₁ x₂ hx₂, hΨx₂, Subgroup.mem_prod]
    simp
  have hw' : C10P34.conjQuot X X t₂ hX₂ (mkO2 X x₁ hx₁) = mkO2 X x₁ hx₁ := by
    rw [C10P34.conjQuot_mk hX₂ hx₁ (hmem hX₂ x₁ hx₁)]
    refine (mkO2_eq_iff h hD (hmem hX₂ x₁ hx₁) hx₁).mpr ?_
    rw [c₂ x₁ hx₁, hΨx₁, Subgroup.mem_prod]
    simp
  have hw1 : mkO2 X x₂ hx₂ ≠ 1 := by
    intro h1
    have h2 := (mkO2_eq_iff h hD hx₂ X.one_mem).mp h1
    rw [hΨx₂, hΨ1, Subgroup.mem_prod] at h2
    exact hk₀E (by simpa using h2.2)
  have hw'1 : mkO2 X x₁ hx₁ ≠ 1 := by
    intro h1
    have h2 := (mkO2_eq_iff h hD hx₁ X.one_mem).mp h1
    rw [hΨx₁, hΨ1, Subgroup.mem_prod] at h2
    exact hk₀E (by simpa using h2.1)
  have hfix : ∀ v, C10P34.conjQuot X X t₁ hX₁ v = v →
      v = 1 ∨ v = mkO2 X x₂ hx₂ ∨ v = (mkO2 X x₂ hx₂)⁻¹ := by
    intro v hv
    obtain ⟨⟨x', hx'⟩, rfl⟩ := QuotientGroup.mk_surjective v
    rw [C10P34.conjQuot_mk hX₁ hx' (hmem hX₁ x' hx')] at hv
    have h1 := (mkO2_eq_iff h hD (hmem hX₁ x' hx') hx').mp hv
    rw [c₁ x' hx', Subgroup.mem_prod] at h1
    simp only [Prod.fst_mul, Prod.fst_inv] at h1
    obtain ⟨hk, hk'⟩ := hK x' hx'
    have hkE := mem_of_inv_act hD hd hk h1.1
    rcases hD2.cyc k₀ hk₀K _ hk' hk₀E with h2 | h2 | h2
    · left
      refine (mkO2_eq_iff h hD hx' X.one_mem).mpr ?_
      rw [hΨ1, Subgroup.mem_prod]
      simpa using ⟨hkE, h2⟩
    · right; left
      refine (mkO2_eq_iff h hD hx' hx₂).mpr ?_
      rw [hΨx₂, Subgroup.mem_prod]
      simpa using ⟨hkE, h2⟩
    · right; right
      rw [← QuotientGroup.mk_inv]
      refine (mkO2_eq_iff h hD hx' (X.inv_mem hx₂)).mpr ?_
      rw [psi_inv (hXL0 hx₂), inv_inv, hΨx₂, Subgroup.mem_prod]
      simpa using ⟨hkE, h2⟩
  have hfix' : ∀ v, C10P34.conjQuot X X t₂ hX₂ v = v →
      v = 1 ∨ v = mkO2 X x₁ hx₁ ∨ v = (mkO2 X x₁ hx₁)⁻¹ := by
    intro v hv
    obtain ⟨⟨x', hx'⟩, rfl⟩ := QuotientGroup.mk_surjective v
    rw [C10P34.conjQuot_mk hX₂ hx' (hmem hX₂ x' hx')] at hv
    have h1 := (mkO2_eq_iff h hD (hmem hX₂ x' hx') hx').mp hv
    rw [c₂ x' hx', Subgroup.mem_prod] at h1
    simp only [Prod.snd_mul, Prod.snd_inv] at h1
    obtain ⟨hk, hk'⟩ := hK x' hx'
    have hkE := mem_of_inv_act hD hd hk' h1.2
    rcases hD2.cyc k₀ hk₀K _ hk hk₀E with h2 | h2 | h2
    · left
      refine (mkO2_eq_iff h hD hx' X.one_mem).mpr ?_
      rw [hΨ1, Subgroup.mem_prod]
      simpa using ⟨h2, hkE⟩
    · right; left
      refine (mkO2_eq_iff h hD hx' hx₁).mpr ?_
      rw [hΨx₁, Subgroup.mem_prod]
      simpa using ⟨h2, hkE⟩
    · right; right
      rw [← QuotientGroup.mk_inv]
      refine (mkO2_eq_iff h hD hx' (X.inv_mem hx₁)).mpr ?_
      rw [psi_inv (hXL0 hx₁), inv_inv, hΨx₁, Subgroup.mem_prod]
      simpa using ⟨h2, hkE⟩
  have hgen : ∀ v, ∃ a b : ℕ, v = mkO2 X x₁ hx₁ ^ a * mkO2 X x₂ hx₂ ^ b := by
    intro v
    obtain ⟨⟨x', hx'⟩, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨hk, hk'⟩ := hK x' hx'
    obtain ⟨a, ha⟩ := exists_pow_of_cyc hD hD2 hk₀K hk₀E hk
    obtain ⟨b, hb⟩ := exists_pow_of_cyc hD hD2 hk₀K hk₀E hk'
    refine ⟨a, b, ?_⟩
    have hm : x₁ ^ a * x₂ ^ b ∈ X := X.mul_mem (X.pow_mem hx₁ a) (X.pow_mem hx₂ b)
    have e : mkO2 X x₁ hx₁ ^ a * mkO2 X x₂ hx₂ ^ b = mkO2 X (x₁ ^ a * x₂ ^ b) hm := by
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
      rfl
    rw [e]
    refine (mkO2_eq_iff h hD hx' hm).mpr ?_
    have hΨm : Ψ ⟨x₁ ^ a * x₂ ^ b, hXL0 hm⟩ = (k₀ ^ a, k₀ ^ b) := by
      have e2 : Ψ ⟨x₁ ^ a * x₂ ^ b, hXL0 hm⟩ = Ψ ⟨x₁, hXL0 hx₁⟩ ^ a * Ψ ⟨x₂, hXL0 hx₂⟩ ^ b := by
        rw [← map_pow, ← map_pow, ← map_mul]; rfl
      rw [e2, hΨx₁, hΨx₂]
      ext <;> simp
    rw [hΨm, Subgroup.mem_prod]
    simpa using ⟨ha, hb⟩
  have hβ1 := eq_one_of_conj_mem_four h3 hσrel hβ3 hDc hw hw1 hfix hw' hw'1 hfix' hgen
  have h4 := congrArg (fun f : MulAut (↥X ⧸ CFSG.pCore 2 ↥X) => f (mkO2 X x hx)) hβ1
  simp only [MulAut.one_apply] at h4
  rw [C10P34.conjQuot_mk hXy hx (hmem hXy x hx)] at h4
  exact (mk_eq_mk_iff (hmem hXy x hx) hx).mp h4

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
