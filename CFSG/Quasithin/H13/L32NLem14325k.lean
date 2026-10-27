module

public import CFSG.Quasithin.H13.L32NLem14325j

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

theorem s3_commutator_ne_top : commutator (Equiv.Perm (Fin 3)) ≠ ⊤ := by
  intro h
  have h1 : Equiv.swap (0 : Fin 3) 1 ∈ commutator (Equiv.Perm (Fin 3)) := h ▸ Subgroup.mem_top _
  have h2 := Abelianization.commutator_subset_ker Equiv.Perm.sign h1
  rw [MonoidHom.mem_ker, Equiv.Perm.sign_swap (by decide)] at h2
  exact absurd h2 (by decide)

theorem not_surjective_of_perfect {X : Type*} [Group X] [Group.IsPerfect X]
    (f : X →* Equiv.Perm (Fin 3)) : ¬ Function.Surjective f := by
  intro hf
  apply s3_commutator_ne_top
  rw [commutator_def, ← Subgroup.map_top_of_surjective f hf, ← Subgroup.map_commutator,
    ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem s3_alt_comm : ∀ σ τ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 →
    Equiv.Perm.sign τ = 1 → σ * τ = τ * σ := by
  decide +kernel

theorem s3_exists_ne : ∀ τ : Equiv.Perm (Fin 3), ∃ π : Equiv.Perm (Fin 3), π ≠ 1 ∧ π ≠ τ := by
  decide +kernel

theorem perm_not_surjective {n : ℕ} (hn : 5 ≤ n) (f : Equiv.Perm (Fin n) →* Equiv.Perm (Fin 3)) :
    ¬ Function.Surjective f := by
  intro hf
  have hA : (alternatingGroup (Fin n)).map f = ⊥ := by
    set B := (alternatingGroup (Fin n)).map f with hB
    have hBB : ⁅B, B⁆ = B := by
      rw [hB, ← Subgroup.map_commutator,
        commutator_alternatingGroup_eq_self (by rw [Nat.card_fin]; exact hn)]
    have hBs : B ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).ker := by
      rw [← hBB]
      refine (Subgroup.commutator_mono le_top le_top).trans ?_
      rw [← commutator_def]
      exact Abelianization.commutator_subset_ker _
    rw [← hBB, eq_bot_iff, Subgroup.commutator_le]
    intro b hb b' hb'
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact s3_alt_comm _ _ (hBs hb) (hBs hb')
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set τ := f (Equiv.swap i₀ i₁) with hτ
  obtain ⟨π, hπ1, hπτ⟩ := s3_exists_ne τ
  obtain ⟨σ, rfl⟩ := hf π
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · apply hπ1
    have hσ : σ ∈ alternatingGroup (Fin n) := h
    have := Subgroup.mem_map_of_mem f hσ
    rwa [hA] at this
  · apply hπτ
    have hs : σ * Equiv.swap i₀ i₁ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, h, Equiv.Perm.sign_swap h01]
      decide
    have := Subgroup.mem_map_of_mem f hs
    rw [hA, Subgroup.mem_bot, map_mul] at this
    have hτ2 : τ * τ = 1 := by rw [hτ, ← map_mul, Equiv.swap_mul_self, map_one]
    calc f σ = f σ * τ * τ := by rw [mul_assoc, hτ2, mul_one]
      _ = τ := by rw [this, one_mul]

theorem card_mulAut_le_six {M : Type*} [Group M] [Finite M] (h4 : Nat.card M = 4) :
    Nat.card (MulAut M) ≤ 6 := by
  classical
  have := Fintype.ofFinite M
  let f : MulAut M → Equiv.Perm {m : M // m ≠ 1} := fun α =>
    α.toEquiv.subtypeEquiv fun _ => (MulEquiv.map_ne_one_iff α).symm
  have hf : Function.Injective f := by
    intro α β hαβ
    ext m
    by_cases hm : m = 1
    · rw [hm, map_one, map_one]
    · exact congrArg Subtype.val (Equiv.congr_fun hαβ ⟨m, hm⟩)
  have h3 : Nat.card {m : M // m ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, h4]
  calc Nat.card (MulAut M) ≤ Nat.card (Equiv.Perm {m : M // m ≠ 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = 6 := by rw [Nat.card_perm, h3]; rfl

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace CtxI.TransData

variable {C : CtxI G T L V V₂ g D} {x c : G} (X : TransData C x c)
include X

theorem card_vP (h64 : G64.LemmaG64) : Nat.card ↥(vP T V c) = 4 := by
  obtain ⟨e⟩ := C.iso
  obtain ⟨ψ, hψs, hψ⟩ := X.exists_psi e
  obtain ⟨s, Ks, -, hsup, -, hcommK, hcommV, -, ⟨hs0, ha0⟩, -, -, hmod, h3, -⟩ := X.concl h64
  have hKle : ∀ i, Ks i ≤ X.kStar := fun i => (le_iSup Ks i).trans hsup.le
  rcases h3 with ⟨rfl, -⟩ | ⟨rfl, -, t, htA, -, -, -, hsw⟩
  ·
    have hK0 : Ks 0 = X.kStar := (iSup_unique Ks).symm.trans hsup
    have hV0 : commV (Ks 0) = ⊤ := (iSup_unique (fun i => commV (Ks i))).symm.trans hcommV
    set ψ' : ↥(Ks 0) →* Equiv.Perm (Fin 3) := ψ.comp (Subgroup.inclusion (hKle 0)) with hψ'
    have hψ's : Function.Surjective ψ' := by
      intro σ
      obtain ⟨⟨φ, hφ⟩, rfl⟩ := hψs σ
      exact ⟨⟨φ, hK0 ▸ hφ⟩, rfl⟩
    rcases hmod 0 with ⟨n, hn2, -, F, _, _, hF2, π, hπs, -, -, -, -, -, -, β, hβs, hβk, -⟩ |
      ⟨n, hn5, -, π, hπs, -⟩ | ⟨n, hn, π, hπs, -⟩
    · by_cases hn : n = 2
      · subst hn
        have hinj : Function.Injective β := by
          rw [injective_iff_map_eq_one]
          intro u hu
          have := (hβk u).mp hu
          rw [Subgroup.mem_bot] at this
          exact Subtype.ext this
        have h1 := Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
        rw [hV0, Subgroup.card_top] at h1
        show Nat.card (IntMod (vP T V c) X.elem) = 4
        rw [h1]
        change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 2 → F))) ⧸
          (⊥ : Subgroup (Multiplicative (Fin 2 → F))).subgroupOf ⊤) = 4
        rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
          Subgroup.card_top]
        change Nat.card (Fin 2 → F) = 4
        rw [Nat.card_fun, hF2, Nat.card_fin]
        norm_num
      · exfalso
        have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) F) :=
          CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
        exact not_surjective_of_perfect ((ψ'.comp π).comp
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).toMonoidHom)
          ((hψ's.comp hπs).comp
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).surjective)
    · exact absurd (hψ's.comp hπs) (perm_not_surjective hn5 (ψ'.comp π))
    · exact absurd (hψ's.comp hπs) (perm_not_surjective (by omega) (ψ'.comp π))
  ·
    exfalso
    set a := C10E4.transvI X.elem X.x_H with ha
    have ha0' : a ∈ Ks 0 := ha0
    obtain ⟨⟨h, hhN⟩, hh, rfl⟩ := (mem_autI X.elem).mp htA
    have hb1 : convI X.elem ⟨h, hhN⟩ * a * (convI X.elem ⟨h, hhN⟩)⁻¹ ∈ Ks 1 := by
      rw [← hsw 0 1 (by decide)]
      exact ⟨a, ha0', rfl⟩
    have hxK : x ∈ kI T V g := zUg_le_kI X.x_mem
    have hyK : h * x * h⁻¹ ∈ kI T V g := mem_conjClosure hh X.x_mem
    have hφx : ((X.phi ⟨x, hxK⟩ : ↥X.kStar) : MulAut (IntMod (vP T V c) X.elem)) = a := rfl
    have hφy : ((X.phi ⟨h * x * h⁻¹, hyK⟩ : ↥X.kStar) : MulAut (IntMod (vP T V c) X.elem)) =
        convI X.elem ⟨h, hhN⟩ * a * (convI X.elem ⟨h, hhN⟩)⁻¹ := by
      rw [X.phi_coe, ha, C10E4.transvI, ← map_inv, ← map_mul, ← map_mul]
      rfl
    set τ₁ := ψ (X.phi ⟨x, hxK⟩) with hτ₁
    set τ₂ := ψ (X.phi ⟨h * x * h⁻¹, hyK⟩) with hτ₂
    have hsq : ∀ k : ↥(kI T V g),
        ((X.phi k : ↥X.kStar) : MulAut (IntMod (vP T V c) X.elem)) ^ 2 = 1 →
          ψ (X.phi k) * ψ (X.phi k) = 1 := by
      intro k hk
      rw [← map_mul, ← pow_two]
      have : X.phi k ^ 2 = 1 := Subtype.ext hk
      rw [this, map_one]
    have hτ₁2 : τ₁ * τ₁ = 1 := hsq _ X.transvI_sq
    have ha2 : a * a = 1 := by rw [← pow_two]; exact X.transvI_sq
    have hτ₂2 : τ₂ * τ₂ = 1 := hsq _ (by
      rw [hφy, pow_two]
      calc convI X.elem ⟨h, hhN⟩ * a * (convI X.elem ⟨h, hhN⟩)⁻¹ *
            (convI X.elem ⟨h, hhN⟩ * a * (convI X.elem ⟨h, hhN⟩)⁻¹) =
            convI X.elem ⟨h, hhN⟩ * (a * a) * (convI X.elem ⟨h, hhN⟩)⁻¹ := by group
        _ = 1 := by rw [ha2]; group)
    have hne : ∀ k : ↥(kI T V g),
        D.ρ ⟨k, L14332.l32nH_le_normalizer_fsuU T V (C.kI_le k.2)⟩ ≠ 1 → ψ (X.phi k) ≠ 1 := by
      intro k hk h1
      rw [hψ, MulEquiv.map_eq_one_iff] at h1
      exact hk (by rw [← C.rhoK_coe, h1]; rfl)
    have hτ₁1 : τ₁ ≠ 1 := hne _ (X.x_ne _)
    have hτ₂1 : τ₂ ≠ 1 := hne _ (by
      intro h1
      apply X.x_ne (L14332.l32nH_le_normalizer_fsuU T V X.x_H)
      have hN := L14332.l32nH_le_normalizer_fsuU T V hh
      have e1 : (⟨h * x * h⁻¹, L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hyK)⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) =
          ⟨h, hN⟩ * ⟨x, L14332.l32nH_le_normalizer_fsuU T V X.x_H⟩ * (⟨h, hN⟩)⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv] at h1
      calc D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V X.x_H⟩ =
            (D.ρ ⟨h, hN⟩)⁻¹ * (D.ρ ⟨h, hN⟩ * D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V X.x_H⟩ *
              (D.ρ ⟨h, hN⟩)⁻¹) * D.ρ ⟨h, hN⟩ := by group
        _ = 1 := by rw [h1]; group)
    have hcomm12 : τ₁ * τ₂ = τ₂ * τ₁ := by
      have hc : X.phi ⟨x, hxK⟩ * X.phi ⟨h * x * h⁻¹, hyK⟩ =
          X.phi ⟨h * x * h⁻¹, hyK⟩ * X.phi ⟨x, hxK⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hφx, hφy]
        exact hcommK 0 1 (by decide) a ha0' _ hb1
      rw [hτ₁, hτ₂, ← map_mul, hc, map_mul]
    have h12 : τ₁ = τ₂ := s3_comm τ₁ τ₂ ⟨hτ₁2, hτ₁1, hτ₂2, hτ₂1, hcomm12⟩
    have hcent : ∀ y w : ↥X.kStar, ψ w * ψ w = 1 → ψ w ≠ 1 → y * w = w * y →
        ψ y = 1 ∨ ψ y = ψ w := fun y w hw2 hw1 hyw =>
      s3_cent (ψ w) (ψ y) hw2 hw1 (by rw [← map_mul, ← map_mul, hyw])
    have hall : X.kStar ≤ ((Subgroup.zpowers τ₁).comap ψ).map X.kStar.subtype := by
      refine hsup.symm.le.trans (iSup_le fun i => ?_)
      intro y hy
      refine ⟨⟨y, hKle i hy⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have key : ψ ⟨y, hKle i hy⟩ = 1 ∨ ψ ⟨y, hKle i hy⟩ = τ₁ := by
        fin_cases i
        · have := hcent ⟨y, hKle 0 hy⟩ (X.phi ⟨h * x * h⁻¹, hyK⟩) hτ₂2 hτ₂1 (Subtype.ext (by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, hφy]
            exact hcommK 0 1 (by decide) y hy _ hb1))
          rwa [← hτ₂, ← h12] at this
        · exact hcent ⟨y, hKle 1 hy⟩ (X.phi ⟨x, hxK⟩) hτ₁2 hτ₁1 (Subtype.ext (by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, hφx]
            exact (hcommK 0 1 (by decide) a ha0' y hy).symm))
      rcases key with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    obtain ⟨π, hπ1, hπτ⟩ := s3_exists_ne τ₁
    obtain ⟨y, rfl⟩ := hψs π
    obtain ⟨y', hy', hy'y⟩ := hall y.2
    have : y' = y := Subtype.ext hy'y
    have hy'' : ψ y ∈ Subgroup.zpowers τ₁ := by rw [← this]; exact hy'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy''
    have hτ₁2' : τ₁ ^ 2 = 1 := by rw [pow_two]; exact hτ₁2
    rcases C10E4.zpow_eq_one_or_eq hτ₁2' k with h1 | h1
    · exact hπ1 (hk.symm.trans h1)
    · exact hπτ (hk.symm.trans h1)

theorem cent_of_hat (h64 : G64.LemmaG64) {k : G} (hk : k ∈ kI T V g)
    (hkE : k ∈ l32nCHat T V) : k ∈ Subgroup.centralizer (vP T V c : Set G) := by
  obtain ⟨e⟩ := C.iso
  obtain ⟨ψ, hψs, hψ⟩ := X.exists_psi e
  have h6 : Nat.card ↥X.kStar ≤ Nat.card (Equiv.Perm (Fin 3)) := by
    rw [Nat.card_perm, Nat.card_fin]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
      (card_mulAut_le_six (X.card_vP h64))
  have hinj := (hψs.bijective_of_nat_card_le h6).1
  have h1 : X.phi ⟨k, hk⟩ = 1 := by
    apply hinj
    rw [hψ, map_one]
    have : C.rhoK ⟨k, hk⟩ = 1 :=
      Subtype.ext ((L14332.rho_eq_one_iff_mem (C.kI_le hk) _).mpr hkE)
    rw [this, map_one]
  have h2 : convI X.elem ⟨k, H_le_normalizer_vP c (C.kI_le hk)⟩ = 1 := by
    rw [← X.phi_coe ⟨k, hk⟩]
    exact congrArg Subtype.val h1
  exact (convI_eq_one_iff X.elem _).mp h2

end CtxI.TransData

end L14325

end CFSG.Quasithin.H13
