module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Rows
public import CFSG.Quasithin.Background.HL3NineNorm
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso

public section

namespace CFSG.Quasithin.H13.Prop329.Lie

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine
open CFSG.Assembly.LowTwoRank (StatedSL StatedScalars StatedProj statedSL_eq_range_toGL)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_model_via {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (hK : Nat.card K = (2 ^ n) ^ 2) {π : ↥(StatedSL 3 K) →* ↥H}
    (h : (FFModel.twistTensor n (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) :
    ∃ e : V ≃* HMod n K, H.map (congrHom e) = img hK ∧
      ∀ γ : ↥(StatedSL 3 K), congrHom e ((π γ : ↥H) : MulAut V) =
        rhoT hK (γ : GL (Fin 3) K) := by
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(hermSub n (Fin 3) K) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 3) (Fin 3) K))).subgroupOf
        (hermSub n (Fin 3) K) ≃* HMod n K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot
  let e : V ≃* HMod n K :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q
  have hqs : ∀ x, x = (QuotientGroup.mk (q x) : ↥(hermSub n (Fin 3) K) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 3) (Fin 3) K))).subgroupOf
        (hermSub n (Fin 3) K)) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have he : ∀ (γ : ↥(StatedSL 3 K)) (v : V),
      e (((π γ : ↥H) : MulAut V) v) = rhoT hK (γ : GL (Fin 3) K) (e v) := by
    intro γ v
    have hact : (FFModel.twistTensor n (StatedSL 3 K)).act γ
        ((e v : HMod n K) : Multiplicative (Matrix (Fin 3) (Fin 3) K)) =
        ((rhoT hK (γ : GL (Fin 3) K) (e v) : HMod n K) :
          Multiplicative (Matrix (Fin 3) (Fin 3) K)) := by
      change Multiplicative.ofAdd (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat (e v) *
          (frobPow n ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ) =
        Multiplicative.ofAdd (tw n ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (mat (e v)))
      rw [frobPow_eq_conjM]
      rfl
    have hm : (FFModel.twistTensor n (StatedSL 3 K)).act γ
        ((e v : HMod n K) : Multiplicative (Matrix (Fin 3) (Fin 3) K)) ∈
          (FFModel.twistTensor n (StatedSL 3 K)).sec := by
      rw [hact]
      exact (rhoT hK (γ : GL (Fin 3) K) (e v)).2
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk (e v) := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ (e v) trivial hm h1
    have h3 := congrArg q h2
    refine h3.trans (Subtype.ext ?_)
    exact hact
  have hpair : ∀ γ : ↥(StatedSL 3 K),
      congrHom e ((π γ : ↥H) : MulAut V) = rhoT hK (γ : GL (Fin 3) K) := fun γ =>
    MulEquiv.ext fun w => by
      show e (((π γ : ↥H) : MulAut V) (e.symm w)) = rhoT hK (γ : GL (Fin 3) K) w
      rw [he, MulEquiv.apply_symm_apply]
  refine ⟨e, ?_, hpair⟩
  rw [img_eq_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    refine ⟨Subtype.val (p := fun A => A ∈ StatedSL 3 K) γ, γ.2, ?_⟩
    have h2 : ((π γ : ↥H) : MulAut V) = x := congrArg Subtype.val hγ
    rw [← hpair γ, h2]
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨_, (π ⟨γ, hγ⟩).2, hpair ⟨γ, hγ⟩⟩

omit [Finite K] [CharP K 2] in
theorem det_eq_one_of_mem {γ : GL (Fin 3) K} (hγ : γ ∈ StatedSL 3 K) :
    (γ : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hγ

omit [Finite K] [CharP K 2] in
theorem eq_of_cube_eq_one {c d : K} (hc : c ^ 3 = 1) (hc1 : c ≠ 1) (hd : d ^ 3 = 1) :
    d = 1 ∨ d = c ∨ d = c ^ 2 := by
  have hq : c ^ 2 + c + 1 = 0 := by
    have h1 : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hc1
    · exact h
  have h2 : (d - 1) * (d - c) * (d - c ^ 2) = 0 := by
    linear_combination hd - d ^ 2 * hq + d * hq + (d - 1) * hc
  rcases mul_eq_zero.mp h2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

end CFSG.Quasithin.H13.Prop329.Lie

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H
open CFSG.Assembly.LowTwoRank (StatedSL StatedScalars StatedProj)

theorem row329Orth_holds : Row329Orth := by
  intro V _ _ G L hHyp m hm h
  obtain ⟨K, _, _, _, hK, π, hπ⟩ := h
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs := NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have := Prop329.nontrivial_of_b4Hyp hHyp
  obtain ⟨e⟩ := Prop329.nonempty_mulEquiv_of_simple hs inferInstance ⟨π, hπ⟩
  exact lieModel_psl_two_of_mulEquiv hHyp.2.2.1.1 hK e

theorem row329Nine_holds : Row329Nine := by
  intro V _ _ G L hHyp m hm h
  obtain ⟨K, hKf, hKfin, hKc, hK, π₀, hπ₀⟩ := h
  have hK' : Nat.card K = (2 ^ m) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, he, hpair₀⟩ := Prop329.Lie.exists_model_via hK' hπ₀
  let π : ↥(StatedSL 3 K) →* ↥L := π₀
  have hπ : (FFModel.twistTensor m (StatedSL 3 K)).RealizesVia L ⊤ ⊥ π := hπ₀
  have hpair : ∀ γ : ↥(StatedSL 3 K), congrHom e ((π γ : ↥L) : MulAut V) =
      L3Nine.rhoT hK' (γ : GL (Fin 3) K) := fun γ => hpair₀ γ
  refine ⟨K, hKf, hKfin, hKc, hK, ?_, ?_, π, hπ, ?_⟩
  ·
    by_cases hk : π.ker = ⊥
    · right
      exact ⟨(MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hk, hπ.1⟩).symm⟩
    · left
      have hscal : ∀ γ ∈ π.ker,
          ∃ d : K, ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = d • 1 := by
        intro γ hγ
        apply L3Nine.scalar_of_rhoT_eq_one hK'
        rw [← hpair γ]
        have h1 : ((π γ : ↥L) : MulAut V) = 1 := by
          rw [(MonoidHom.mem_ker).1 hγ]
          rfl
        rw [h1, map_one]
      have hdet : ∀ (γ : ↥(StatedSL 3 K)) (d : K),
          ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = d • 1 → d ^ 3 = 1 := by
        intro γ d hd
        have h1 := Prop329.Lie.det_eq_one_of_mem γ.2
        rw [hd, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
        exact h1
      obtain ⟨⟨γ₀, hγ₀⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hk
      obtain ⟨c, hc⟩ := hscal γ₀ hγ₀
      have hc3 := hdet γ₀ c hc
      have hc1 : c ≠ 1 := by
        rintro rfl
        apply hne
        refine Subtype.ext (Subtype.ext (Units.ext ?_))
        rw [hc, one_smul]
        rfl
      have hker : π.ker = (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) := by
        apply le_antisymm
        · intro γ hγ
          obtain ⟨d, hd⟩ := hscal γ hγ
          have hd0 : d ≠ 0 := by
            intro h0
            have h1 := hdet γ d hd
            rw [h0] at h1
            norm_num at h1
          rw [Subgroup.mem_subgroupOf]
          refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
          rw [hd]
          ext i j
          simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
        · intro γ hγ
          rw [Subgroup.mem_subgroupOf] at hγ
          obtain ⟨u, hu⟩ := hγ
          have hd : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (u : K) • 1 := by
            rw [← hu]
            ext i j
            simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
          rcases Prop329.Lie.eq_of_cube_eq_one hc3 hc1 (hdet γ u hd) with h1 | h1 | h1
          · have : γ = 1 := Subtype.ext (Units.ext (by rw [hd, h1, one_smul]; rfl))
            rw [this]
            exact Subgroup.one_mem _
          · have : γ = γ₀ := Subtype.ext (Units.ext (by rw [hd, h1, hc]))
            rw [this]
            exact hγ₀
          · have hsq : (((γ₀ ^ 2 : ↥(StatedSL 3 K)) : GL (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K) = c ^ 2 • 1 := by
              rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hc, smul_pow, one_pow]
            have : γ = γ₀ ^ 2 := Subtype.ext (Units.ext (by rw [hd, h1, hsq]))
            rw [this]
            exact Subgroup.pow_mem _ hγ₀ 2
      refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩, K, hKf,
        hKfin, hK, ⟨?_⟩⟩
      exact (QuotientGroup.quotientKerEquivOfSurjective π hπ.1).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker)
  ·
    rw [Nat.card_congr e.toEquiv, L3Nine.card_HMod hm hK']
  ·
    intro t ht
    have ht' : congrHom e t ∈ L3Nine.norm hK' := by
      have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
          Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut (L3Nine.HMod m K))) :
            Set (MulAut (L3Nine.HMod m K))) :=
        Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
      rw [L3Nine.norm, ← he, ← h1]
      exact ⟨t, ht, rfl⟩
    obtain ⟨A, σ, hAσ⟩ := L3Nine.exists_eq_rhoT_mul_fldAut hm hK' ht'
    refine ⟨A, σ, fun g hg => ?_⟩
    apply congrHom_injective e
    have hL : congrHom e ((π ⟨_, hg⟩ : ↥L) : MulAut V) = L3Nine.rhoT hK' A *
        L3Nine.rhoT hK' (L3Nine.mapGL σ (g : GL (Fin 3) K)) * (L3Nine.rhoT hK' A)⁻¹ := by
      rw [hpair]
      simp only [map_mul, map_inv]
      rfl
    have hR : congrHom e (t * ((π g : ↥L) : MulAut V) * t⁻¹) =
        congrHom e t * L3Nine.rhoT hK' (g : GL (Fin 3) K) * (congrHom e t)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hpair]
    rw [hL, hR, hAσ, ← L3Nine.fldAut_conj_rhoT hK' σ]
    group

end CFSG.Quasithin.H13
