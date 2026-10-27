module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base1
public import CFSG.Quasithin.Background.HSL3Pair

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

theorem isNatIrr_SL3 (U : AddSubgroup (Fin 3 → K))
    (hU : ∀ g ∈ StatedSL 3 K, ∀ u ∈ U, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  refine eq_bot_or_eq_top_of_transvection_inv (by norm_num : 2 ≤ 3) U fun i j hij c u hu => ?_
  have hmem : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero) ∈ StatedSL 3 K :=
    SL3Pair.mem_statedSL_iff.mpr (Matrix.det_transvection_of_ne i j hij c)
  exact hU _ hmem u hu

@[expose] def natVec (a b : K) (u : Fin 3 → K) : I6 → K := Sum.elim (a • u) (b • u)

theorem natVec_inl (a b : K) (u : Fin 3 → K) : natVec a b u ∘ Sum.inl = a • u := rfl

theorem natVec_inr (a b : K) (u : Fin 3 → K) : natVec a b u ∘ Sum.inr = b • u := rfl

theorem natVec_add (a b : K) (u w : Fin 3 → K) :
    natVec a b (u + w) = natVec a b u + natVec a b w := by
  funext i
  rcases i with i | i <;> simp [natVec]

theorem natVec_zero (a b : K) : natVec a b 0 = 0 := by
  funext i
  rcases i with i | i <;> simp [natVec]

@[expose] def natEmb (a b : K) : StdMod (Fin 3) K →* W6 K where
  toFun u := Multiplicative.ofAdd (natVec a b (Multiplicative.toAdd u))
  map_one' := by
    rw [toAdd_one, natVec_zero, ofAdd_zero]
  map_mul' u w := by
    rw [toAdd_mul, natVec_add, ofAdd_add]

theorem toAdd_natEmb (a b : K) (u : StdMod (Fin 3) K) :
    Multiplicative.toAdd (natEmb a b u) = natVec a b (Multiplicative.toAdd u) := rfl

@[expose] def natSub (a b : K) : Subgroup (W6 K) := (natEmb a b).range

theorem mem_natSub {a b : K} {x : W6 K} :
    x ∈ natSub a b ↔ ∃ u : Fin 3 → K, Multiplicative.toAdd x = natVec a b u := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Multiplicative.toAdd u, rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨Multiplicative.ofAdd u, by rw [← ofAdd_toAdd x, hu]; rfl⟩

theorem natEmb_injective {a b : K} (h : a ≠ 0 ∨ b ≠ 0) : Function.Injective (natEmb a b) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 := congrArg Multiplicative.toAdd hu
  rw [toAdd_natEmb, toAdd_one] at h1
  rcases h with ha | hb
  · have h2 := congrArg (fun v : I6 → K => v ∘ Sum.inl) h1
    simp only [natVec_inl] at h2
    have h3 : Multiplicative.toAdd u = 0 := by
      have := congrArg (fun v => a⁻¹ • v) h2
      simpa [smul_smul, inv_mul_cancel₀ ha] using this
    rw [← ofAdd_toAdd u, h3, ofAdd_zero]
  · have h2 := congrArg (fun v : I6 → K => v ∘ Sum.inr) h1
    simp only [natVec_inr] at h2
    have h3 : Multiplicative.toAdd u = 0 := by
      have := congrArg (fun v => b⁻¹ • v) h2
      simpa [smul_smul, inv_mul_cancel₀ hb] using this
    rw [← ofAdd_toAdd u, h3, ofAdd_zero]

theorem card_natSub [Finite K] {a b : K} (h : a ≠ 0 ∨ b ≠ 0) :
    Nat.card ↥(natSub a b) = Nat.card K ^ 3 := by
  rw [natSub, ← Nat.card_congr (MonoidHom.ofInjective (natEmb_injective h)).toEquiv,
    card_stdMod, Fintype.card_fin]

theorem dgHom_mulVec_natVec (g : GL (Fin 3) K) (a b : K) (u : Fin 3 → K) :
    ((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ natVec a b u =
      natVec a b ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) := by
  funext i
  rcases i with i | i
  · have := congrFun (dgHom_mulVec_inl g (natVec a b u)) i
    simp only [Function.comp_apply] at this
    rw [this]
    simp [natVec, Matrix.mulVec_smul]
  · have := congrFun (dgHom_mulVec_inr g (natVec a b u)) i
    simp only [Function.comp_apply] at this
    rw [this]
    simp [natVec, Matrix.mulVec_smul]

theorem matAut_dgHom_natEmb (g : GL (Fin 3) K) (a b : K) (u : StdMod (Fin 3) K) :
    matAut (dgHom g) (natEmb a b u) = natEmb a b (matAut g u) :=
  congrArg Multiplicative.ofAdd (dgHom_mulVec_natVec g a b (Multiplicative.toAdd u))

@[expose] def IsInvD (M : Subgroup (W6 K)) : Prop :=
  ∀ g ∈ StatedSL 3 K, ∀ x ∈ M, matAut (dgHom g) x ∈ M

theorem natSub_isInv (a b : K) : IsInvD (natSub a b) := by
  rintro g - _ ⟨u, rfl⟩
  exact ⟨matAut g u, (matAut_dgHom_natEmb g a b u).symm⟩

theorem eq_natSub_one_of_proj [Finite K] {M : Subgroup (W6 K)} (hM : IsInvD M)
    (hinj : ∀ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = 0 → x = 1)
    (hsurj : ∀ u : Fin 3 → K, ∃ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = u) :
    ∃ c : K, M = natSub 1 c := by
  classical
  choose m hmM hm using hsurj
  have huniq : ∀ x ∈ M, x = m (Multiplicative.toAdd x ∘ Sum.inl) := by
    intro x hx
    have h1 : x * (m (Multiplicative.toAdd x ∘ Sum.inl))⁻¹ = 1 := by
      refine hinj _ (M.mul_mem hx (M.inv_mem (hmM _))) ?_
      funext i
      have := congrFun (hm (Multiplicative.toAdd x ∘ Sum.inl)) i
      simp only [Function.comp_apply] at this
      simp [this]
    exact mul_inv_eq_one.mp h1
  let ψ : (Fin 3 → K) →+ (Fin 3 → K) :=
    { toFun := fun u => Multiplicative.toAdd (m u) ∘ Sum.inr
      map_zero' := by
        have h0 : m 0 = 1 := by
          have := huniq 1 M.one_mem
          rw [toAdd_one] at this
          exact (this.trans (by simp)).symm
        rw [h0, toAdd_one]
        rfl
      map_add' := fun u w => by
        have h1 : m (u + w) = m u * m w := by
          have := huniq _ (M.mul_mem (hmM u) (hmM w))
          rw [toAdd_mul] at this
          rw [this]
          congr 1
          funext i
          simp only [Function.comp_apply, Pi.add_apply]
          have hu := congrFun (hm u) i
          have hw := congrFun (hm w) i
          simp only [Function.comp_apply] at hu hw
          rw [hu, hw]
        rw [h1, toAdd_mul]
        rfl }
  have hψ : ∀ g ∈ StatedSL 3 K, ∀ u, ψ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ψ u := by
    intro g hg u
    have hx := hM g hg _ (hmM u)
    have h1 := huniq _ hx
    have h2 : Multiplicative.toAdd (matAut (dgHom g) (m u)) ∘ Sum.inl =
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u := by
      have := dgHom_mulVec_inl g (Multiplicative.toAdd (m u))
      rw [hm u] at this
      exact this
    rw [h2] at h1
    change Multiplicative.toAdd (m ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u)) ∘ Sum.inr = _
    rw [← h1]
    exact dgHom_mulVec_inr g (Multiplicative.toAdd (m u))
  obtain ⟨c, hc⟩ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3) ψ hψ
  refine ⟨c, le_antisymm (fun x hx => ?_) ?_⟩
  · refine mem_natSub.mpr ⟨Multiplicative.toAdd x ∘ Sum.inl, ?_⟩
    have h1 := huniq x hx
    funext i
    rcases i with i | i
    · simp [natVec]
    · have h2 := congrFun (hc (Multiplicative.toAdd x ∘ Sum.inl)) i
      change Multiplicative.toAdd (m _) (Sum.inr i) = _ at h2
      rw [← h1] at h2
      simpa [natVec] using h2
  · rintro _ ⟨u, rfl⟩
    have h1 : natEmb 1 c u = m (Multiplicative.toAdd u) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_natEmb]
      funext i
      rcases i with i | i
      · have := congrFun (hm (Multiplicative.toAdd u)) i
        simp only [Function.comp_apply] at this
        simp [natVec, this]
      · have := congrFun (hc (Multiplicative.toAdd u)) i
        change Multiplicative.toAdd (m _) (Sum.inr i) = _ at this
        simp [natVec, this]
    rw [h1]
    exact hmM _

theorem natSub_zero_one_eq {x : W6 K} :
    x ∈ natSub 0 1 ↔ Multiplicative.toAdd x ∘ Sum.inl = 0 := by
  rw [mem_natSub]
  constructor
  · rintro ⟨u, hu⟩
    rw [hu, natVec_inl, zero_smul]
  · intro h
    refine ⟨Multiplicative.toAdd x ∘ Sum.inr, ?_⟩
    funext i
    rcases i with i | i
    · have := congrFun h i
      simpa [natVec] using this
    · simp [natVec]

theorem eq_natSub_of_card [Finite K] {M : Subgroup (W6 K)} (hM : IsInvD M)
    (hcard : Nat.card ↥M = Nat.card K ^ 3) :
    M = natSub 0 1 ∨ ∃ c : K, M = natSub 1 c := by
  classical
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  let U₂ : AddSubgroup (Fin 3 → K) :=
    { carrier := {u | natEmb 0 1 (Multiplicative.ofAdd u) ∈ M}
      add_mem' := fun {a b} ha hb => by
        change natEmb 0 1 (Multiplicative.ofAdd (a + b)) ∈ M
        rw [ofAdd_add, map_mul]
        exact M.mul_mem ha hb
      zero_mem' := by
        change natEmb 0 1 (Multiplicative.ofAdd 0) ∈ M
        rw [ofAdd_zero, map_one]
        exact M.one_mem
      neg_mem' := fun {a} ha => by
        change natEmb 0 1 (Multiplicative.ofAdd (-a)) ∈ M
        rw [ofAdd_neg, map_inv]
        exact M.inv_mem ha }
  have hU₂ : ∀ g ∈ StatedSL 3 K, ∀ u ∈ U₂, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U₂ := by
    intro g hg u hu
    have h1 := hM g hg _ hu
    rw [matAut_dgHom_natEmb] at h1
    exact h1
  rcases isNatIrr_SL3 U₂ hU₂ with h2 | h2
  ·
    have hinj : ∀ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = 0 → x = 1 := by
      intro x hx h0
      have hx2 : Multiplicative.toAdd x ∘ Sum.inr ∈ U₂ := by
        change natEmb 0 1 (Multiplicative.ofAdd (Multiplicative.toAdd x ∘ Sum.inr)) ∈ M
        convert hx using 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_natEmb, toAdd_ofAdd]
        funext i
        rcases i with i | i
        · have := congrFun h0 i
          simpa [natVec] using this.symm
        · simp [natVec]
      rw [h2, AddSubgroup.mem_bot] at hx2
      apply Multiplicative.toAdd.injective
      funext i
      rcases i with i | i
      · exact congrFun h0 i
      · exact congrFun hx2 i
    let U₁ : AddSubgroup (Fin 3 → K) :=
      { carrier := {u | ∃ x ∈ M, Multiplicative.toAdd x ∘ Sum.inl = u}
        add_mem' := fun {a b} ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩ => ⟨x * y, M.mul_mem hx hy, by
          rw [← hxa, ← hyb]
          rfl⟩
        zero_mem' := ⟨1, M.one_mem, rfl⟩
        neg_mem' := fun {a} ⟨x, hx, hxa⟩ => ⟨x⁻¹, M.inv_mem hx, by
          rw [← hxa]
          rfl⟩ }
    have hU₁ : ∀ g ∈ StatedSL 3 K, ∀ u ∈ U₁, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U₁ := by
      rintro g hg _ ⟨x, hx, rfl⟩
      exact ⟨matAut (dgHom g) x, hM g hg x hx, dgHom_mulVec_inl g _⟩
    rcases isNatIrr_SL3 U₁ hU₁ with h1 | h1
    · exfalso
      have hbot : M = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : Multiplicative.toAdd x ∘ Sum.inl ∈ U₁ := ⟨x, hx, rfl⟩
        rw [h1, AddSubgroup.mem_bot] at this
        exact hinj x hx this
      rw [hbot, Subgroup.card_bot] at hcard
      have : 1 < Nat.card K ^ 3 := Nat.one_lt_pow (by norm_num) hK1
      omega
    · right
      refine eq_natSub_one_of_proj hM hinj fun u => ?_
      have : u ∈ U₁ := by rw [h1]; trivial
      exact this
  · left
    have hle : natSub (0 : K) 1 ≤ M := by
      rintro _ ⟨u, rfl⟩
      have hu : Multiplicative.toAdd u ∈ U₂ := by rw [h2]; trivial
      change natEmb 0 1 (Multiplicative.ofAdd (Multiplicative.toAdd u)) ∈ M at hu
      rwa [ofAdd_toAdd] at hu
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcard, card_natSub (Or.inr one_ne_zero)]

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
