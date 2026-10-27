module

public import CFSG.Quasithin.H13.NQCatG2RadFacts

public section

namespace CFSG.Quasithin.H13.NQCat.G2Rad

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.LieType.BorelTits

section Field

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem eq_top_of_smul {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {D : AddSubgroup (K × K × K × K)} (hD : ∀ s, ∀ t ∈ D, tr s t ∈ D)
    (hW : ∀ β : K, ((0 : K), (0 : K), (0 : K), β) ∈ D → (β, (0 : K), (0 : K), (0 : K)) ∈ D)
    (hS : ∀ v : K, v ≠ 0 → ∀ t ∈ D, v • t ∈ D)
    {β₀ : K} (hβ₀ : β₀ ≠ 0) (h0 : ((0 : K), (0 : K), (0 : K), β₀) ∈ D) : D = ⊤ := by
  have hb : ∀ β : K, ((0 : K), (0 : K), (0 : K), β) ∈ D := fun β => by
    by_cases hβ : β = 0
    · rw [hβ]
      exact D.zero_mem
    · have := hS (β * β₀⁻¹) (mul_ne_zero hβ (inv_ne_zero hβ₀)) _ h0
      simpa [Prod.smul_mk, mul_assoc, inv_mul_cancel₀ hβ₀] using this
  have ha : ∀ β : K, (β, (0 : K), (0 : K), (0 : K)) ∈ D := fun β => hW β (hb β)
  have huv : ∀ s β : K, ((0 : K), s * β, s ^ 2 * β, (0 : K)) ∈ D := by
    intro s β
    have := D.sub_mem (tr_sub_mem hD s (ha β)) (hb (s ^ 3 * β))
    simpa using this
  have hv : ∀ γ : K, ((0 : K), (0 : K), γ, (0 : K)) ∈ D := by
    intro γ
    have hω1' : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
    have := D.sub_mem (huv ω (γ * (ω - 1)⁻¹ * ω⁻¹)) (huv 1 (γ * (ω - 1)⁻¹))
    have e1 : ω * (γ * (ω - 1)⁻¹ * ω⁻¹) - 1 * (γ * (ω - 1)⁻¹) = 0 := by
      field_simp
      ring
    have e2 : ω ^ 2 * (γ * (ω - 1)⁻¹ * ω⁻¹) - 1 ^ 2 * (γ * (ω - 1)⁻¹) = γ := by
      field_simp
    simp only [Prod.mk_sub_mk, sub_self, e1, e2] at this
    exact this
  have hu : ∀ γ : K, ((0 : K), γ, (0 : K), (0 : K)) ∈ D := by
    intro γ
    have := D.sub_mem (huv 1 γ) (hv γ)
    simp only [Prod.mk_sub_mk, sub_self, one_mul, one_pow, sub_zero] at this
    exact this
  rw [eq_top_iff]
  rintro ⟨t₁, t₂, t₃, t₄⟩ -
  have := D.add_mem (D.add_mem (D.add_mem (ha t₁) (hu t₂)) (hv t₃)) (hb t₄)
  simpa using this

end Field

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def torusScal
    (v : Kˣ) : ModGL Tag.G2 K :=
  torusElt Tag.G2 K i0 (v ^ 2) * torusElt Tag.G2 K i1 v

theorem torusScal_mem_parabolic
    (v : Kˣ) : torusScal v ∈ parabolicSubgroup Tag.G2 K {i1} := by
  have h0 := torusGroup_le_borelGroup (torusElt_mem_torusGroup (τ := Tag.G2) (R := K) i0 (v ^ 2))
  have h1 := torusGroup_le_borelGroup (torusElt_mem_torusGroup (τ := Tag.G2) (R := K) i1 v)
  exact (le_sup_left : borelGroup Tag.G2 K ≤ parabolicSubgroup Tag.G2 K {i1}) (mul_mem h0 h1)

theorem torusScal_conj (v : Kˣ)
    {d : Fin Tag.G2.rank → ℤ} (hd : IsRoot Tag.G2 d) (s : K) :
    torusScal v * gX d s * (torusScal v)⁻¹ =
      gX d ((((v ^ 2) ^ (∑ j, Tag.G2.cartan i0 j * d j) *
        v ^ (∑ j, Tag.G2.cartan i1 j * d j) : Kˣ) : K) * s) := by
  have e : torusScal v * gX d s * (torusScal v)⁻¹ = torusElt Tag.G2 K i0 (v ^ 2) *
      (torusElt Tag.G2 K i1 v * gX d s * (torusElt Tag.G2 K i1 v)⁻¹) *
        (torusElt Tag.G2 K i0 (v ^ 2))⁻¹ := by
    rw [torusScal]
    group
  rw [e, root_torus_conjugation i1 hd v s, root_torus_conjugation i0 hd (v ^ 2), ← mul_assoc,
    ← Units.val_mul]

theorem torusScal_conj_A (v : Kˣ)
    (s : K) : torusScal v * gX rA s * (torusScal v)⁻¹ = gX rA ((v : K) * s) := by
  rw [torusScal_conj v (isRoot_pos_iff.2 (Or.inl rfl)).1 s]
  have e0 : (∑ j, Tag.G2.cartan i0 j * rA j) = 2 := by decide
  have e1 : (∑ j, Tag.G2.cartan i1 j * rA j) = -3 := by decide
  rw [e0, e1]
  congr 2
  group

theorem torusScal_conj_U (v : Kˣ)
    (s : K) : torusScal v * gX rU s * (torusScal v)⁻¹ = gX rU ((v : K) * s) := by
  rw [torusScal_conj v (isRoot_pos_iff.2 (Or.inr (Or.inr (Or.inl rfl)))).1 s]
  have e0 : (∑ j, Tag.G2.cartan i0 j * rU j) = 1 := by decide
  have e1 : (∑ j, Tag.G2.cartan i1 j * rU j) = -1 := by decide
  rw [e0, e1]
  congr 2
  group

theorem torusScal_conj_V (v : Kˣ)
    (s : K) : torusScal v * gX rV s * (torusScal v)⁻¹ = gX rV ((v : K) * s) := by
  rw [torusScal_conj v (isRoot_pos_iff.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).1 s]
  have e0 : (∑ j, Tag.G2.cartan i0 j * rV j) = 0 := by decide
  have e1 : (∑ j, Tag.G2.cartan i1 j * rV j) = 1 := by decide
  rw [e0, e1]
  congr 2
  group

theorem torusScal_conj_B (v : Kˣ)
    (s : K) : torusScal v * gX rB s * (torusScal v)⁻¹ = gX rB ((v : K) * s) := by
  rw [torusScal_conj v
    (isRoot_pos_iff.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).1 s]
  have e0 : (∑ j, Tag.G2.cartan i0 j * rB j) = -1 := by decide
  have e1 : (∑ j, Tag.G2.cartan i1 j * rB j) = 3 := by decide
  rw [e0, e1]
  congr 2
  group

theorem torusScal_conj_C (v : Kˣ)
    (s : K) : torusScal v * gX rC s * (torusScal v)⁻¹ = gX rC ((v : K) ^ 2 * s) := by
  rw [torusScal_conj v
    (isRoot_pos_iff.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).1 s]
  have e0 : (∑ j, Tag.G2.cartan i0 j * rC j) = 1 := by decide
  have e1 : (∑ j, Tag.G2.cartan i1 j * rC j) = 0 := by decide
  rw [e0, e1]
  congr 2
  simp

theorem torusScal_conj_nf (v : Kˣ)
    (t : K × K × K × K) (c : K) :
    torusScal v * (nf t * gX rC c) * (torusScal v)⁻¹ =
      nf ((v : K) • t) * gX rC ((v : K) ^ 2 * c) := by
  have key : ∀ x y : ModGL Tag.G2 K, torusScal v * (x * y) * (torusScal v)⁻¹ =
      (torusScal v * x * (torusScal v)⁻¹) * (torusScal v * y * (torusScal v)⁻¹) := fun x y => by
    group
  obtain ⟨t₁, t₂, t₃, t₄⟩ := t
  simp only [nf, key, torusScal_conj_A, torusScal_conj_U, torusScal_conj_V, torusScal_conj_B,
    torusScal_conj_C, Prod.smul_mk, smul_eq_mul]

end Torus

section Group

variable {K : Type} [Field K] [CharP K 2]

theorem smul_mem_coordSet
    {S : Subgroup (ModGL Tag.G2 K)} {v : Kˣ}
    (hv : torusScal v ∈ Subgroup.normalizer (S : Set (ModGL Tag.G2 K))) {t : K × K × K × K}
    (ht : t ∈ coordSet S) : (v : K) • t ∈ coordSet S := by
  obtain ⟨c, hc⟩ := ht
  have hc' : torusScal v * (nf t * gX rC c) * (torusScal v)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 hv _).1 hc
  rw [torusScal_conj_nf] at hc'
  exact ⟨_, hc'⟩

theorem eq_or_eq_of_parabolic_le_normalizer
    [Finite K] (h4 : 4 ≤ Nat.card K) {W : Subgroup (ModGL Tag.G2 K)}
    (hZW : (N1 : Subgroup (ModGL Tag.G2 K)) ≤ W) (hWQ : W ≤ parabolicRadical Tag.G2 K {i1})
    (hPW : parabolicSubgroup Tag.G2 K {i1} ≤ Subgroup.normalizer (W : Set (ModGL Tag.G2 K))) :
    W = N1 ∨ W = parabolicRadical Tag.G2 K {i1} := by
  have hKW : perfectCore (parabolicSubgroup Tag.G2 K {i1}) ≤
      Subgroup.normalizer (W : Set (ModGL Tag.G2 K)) := (perfectCore_le _).trans hPW
  by_cases hW : W ≤ N1
  · exact Or.inl (le_antisymm hW hZW)
  right
  obtain ⟨w, hwW, hwN⟩ := Set.not_subset.1 hW
  have hwQ := hWQ hwW
  obtain ⟨c, hc⟩ := eq_nf_coord hwQ
  have ht0 : coord w ≠ 0 := fun h => hwN ((mem_N1_iff hwQ).2 h)
  have htD : coord w ∈ coordSet W := ⟨c, hc ▸ hwW⟩
  have hD : ∀ s, ∀ t ∈ coordSet W, tr s t ∈ coordSet W := fun s t ht =>
    tr_mem_coordSet hWQ (hKW (xr_mem_perfectCore h4 s)) ht
  obtain ⟨u, hu⟩ := G2.exists_units_ne_one h4
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hu1 : (u : K) ≠ 1 := fun h => hu (Units.ext h)
  obtain ⟨β₀, hβ₀, h0⟩ := exists_b_mem hu0 hu1 hD htD ht0
  have hS : ∀ v : K, v ≠ 0 → ∀ t ∈ coordSet W, v • t ∈ coordSet W := fun v hv t ht =>
    smul_mem_coordSet (v := Units.mk0 v hv) (hPW (torusScal_mem_parabolic _)) ht
  have htop := eq_top_of_smul hu0 hu1 hD
    (fun β hβ => weyl_mem_coordSet (hKW (weyl_mem_perfectCore h4)) hβ) hS hβ₀ h0
  refine le_antisymm hWQ fun g hg => ?_
  obtain ⟨d, hd⟩ := eq_nf_coord hg
  obtain ⟨c', hc'⟩ : coord g ∈ coordSet W := htop ▸ AddSubgroup.mem_top _
  have e : g = nf (coord g) * gX rC c' * gX rC (d - c') := by
    rw [mul_assoc, ← gX_add, add_sub_cancel, ← hd]
  rw [e]
  exact W.mul_mem hc' (hZW (gX_c_mem_N1 _))

end Group

section Amalgam

theorem exists_model_parabolic
    {Y : Type} [Group Y] {n : ℕ} (hY : IsLieOverTwo .G2 0 n Y) {T M₁ M : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M)
    (hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 (perfectCore M))) = 2 ^ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ ι : Y →* ModGL Tag.G2 K, Function.Injective ι ∧
        M.map ι = parabolicSubgroup Tag.G2 K {i1} ∧
        (pCoreOf 2 (perfectCore M)).map ι = parabolicRadical Tag.G2 K {i1} := by
  have hYm : ChevalleyExceptionalModel Y .G2 2 n := by
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  have hn : 2 ≤ n := (exists_mulEquiv_G2_model hYm).1
  obtain ⟨K, _, _, _, hK, θ, i, rfl⟩ := G24X3.exists_eq_parabolic_g2 hYm hpair
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : Finite Y := Finite.of_equiv _ θ.toEquiv
  let ι : Y →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp θ.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (adjointGroup Tag.G2 K).subtype_injective.comp θ.symm.injective
  have hM : (((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)).map
      θ.toMonoidHom).map ι = parabolicSubgroup Tag.G2 K {i} := by
    rw [Subgroup.map_map]
    have e : ι.comp θ.toMonoidHom = (adjointGroup Tag.G2 K).subtype := by
      ext x
      simp [ι]
    rw [e, Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup _ _ _)]
  have hK' : (perfectCore (((parabolicSubgroup Tag.G2 K {i}).subgroupOf
      (adjointGroup Tag.G2 K)).map θ.toMonoidHom)).map ι =
      perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
    rw [map_perfectCore, hM]
  have hO : (pCoreOf 2 (perfectCore (((parabolicSubgroup Tag.G2 K {i}).subgroupOf
      (adjointGroup Tag.G2 K)).map θ.toMonoidHom))).map ι = parabolicRadical Tag.G2 K {i} := by
    rw [← G24X3.pCoreOf_map_of_inj ι hι, hK', pCoreOf_perfectCore_parabolic hK hn i]
  have hi : i = i1 := by
    rcases G2.fin_two_cases i with rfl | rfl
    · exfalso
      have h1 := card_center_eq hι (pCoreOf 2 (perfectCore (((parabolicSubgroup Tag.G2 K
        {i0}).subgroupOf (adjointGroup Tag.G2 K)).map θ.toMonoidHom)))
      rw [hO, hZ] at h1
      have h2 := card_le_card_centerOf_zero (K := K)
      rw [← h1, hK] at h2
      have h3 : 2 ^ n < 2 ^ n * 2 ^ n := by
        have : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
      omega
    · rfl
  subst hi
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, ι, hι, hM, hO⟩

theorem parabolic_irred_full
    {Y : Type} [Group Y] {n : ℕ} {T M₁ M : Subgroup Y} (hn : 2 ≤ n)
    (hY : IsLieOverTwo .G2 0 n Y) (hsp : IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 (perfectCore M)))
    (hpair : IsYAmalgamPair T M₁ M) :
    ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore M) → M ≤ Subgroup.normalizer (W : Set Y) →
        W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M) := by
  intro W hZW hWQ hMW
  obtain ⟨K, _, _, _, hK, ι, hι, hM, hO⟩ := exists_model_parabolic hY hpair hsp.2.2
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZ : (centerOf (pCoreOf 2 (perfectCore M))).map ι = N1 := by
    rw [map_centerOf hι, hO, centerOf_parabolicRadical_one]
  have h := eq_or_eq_of_parabolic_le_normalizer h4 (W := W.map ι) (hZ ▸ Subgroup.map_mono hZW)
    (hO ▸ Subgroup.map_mono hWQ) (hM ▸ map_le_normalizer_map hMW)
  rcases h with h | h
  · exact Or.inl (Subgroup.map_injective hι (h.trans hZ.symm))
  · exact Or.inr (Subgroup.map_injective hι (h.trans hO.symm))

end Amalgam

end CFSG.Quasithin.H13.NQCat.G2Rad
