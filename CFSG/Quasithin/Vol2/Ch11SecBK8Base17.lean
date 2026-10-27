module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base6
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base7
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def scalHom (c : K) : W6 K →* W6 K where
  toFun v := Multiplicative.ofAdd (c • Multiplicative.toAdd v)
  map_one' := by rw [toAdd_one, smul_zero, ofAdd_zero]
  map_mul' a b := by rw [toAdd_mul, smul_add, ofAdd_add]

@[expose] def pr1Hom : W6 K →* W6 K where
  toFun v := Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd v ∘ Sum.inl) 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i <;> rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i
    · rfl
    · exact (add_zero 0).symm

@[expose] def swapHom : W6 K →* W6 K where
  toFun v := Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd v ∘ Sum.inr)
    (Multiplicative.toAdd v ∘ Sum.inl))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i <;> rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i <;> rfl

theorem scalHom_comm (c : K) (g : GL (Fin 3) K) (v : W6 K) :
    scalHom c (matAut (dgHom g) v) = matAut (dgHom g) (scalHom c v) := by
  apply Multiplicative.toAdd.injective
  change c • ((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ Multiplicative.toAdd v =
    ((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ (c • Multiplicative.toAdd v)
  rw [Matrix.mulVec_smul]

theorem pr1Hom_comm (g : GL (Fin 3) K) (v : W6 K) :
    pr1Hom (matAut (dgHom g) v) = matAut (dgHom g) (pr1Hom v) := by
  apply Multiplicative.toAdd.injective
  change Sum.elim ((((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ Multiplicative.toAdd v) ∘ Sum.inl)
      0 = ((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ
      Sum.elim (Multiplicative.toAdd v ∘ Sum.inl) (0 : Fin 3 → K)
  rw [dgHom_mulVec, dgHom_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.mulVec_zero]

theorem swapHom_comm (g : GL (Fin 3) K) (v : W6 K) :
    swapHom (matAut (dgHom g) v) = matAut (dgHom g) (swapHom v) := by
  apply Multiplicative.toAdd.injective
  change Sum.elim ((((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ Multiplicative.toAdd v) ∘ Sum.inr)
      ((((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ Multiplicative.toAdd v) ∘ Sum.inl) =
    ((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ
      Sum.elim (Multiplicative.toAdd v ∘ Sum.inr) (Multiplicative.toAdd v ∘ Sum.inl)
  rw [dgHom_mulVec, dgHom_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem scalHom_natSub (c a b : K) {v : W6 K} (hv : v ∈ natSub a b) : scalHom c v ∈ natSub a b := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨Multiplicative.ofAdd (c • Multiplicative.toAdd u), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_natEmb, toAdd_ofAdd]
  change natVec a b (c • Multiplicative.toAdd u) = c • natVec a b (Multiplicative.toAdd u)
  funext i
  rcases i with i | i <;> simp [natVec, mul_left_comm]

variable {G : Type} [Group G] {W : Subgroup G} {hW : IsElemAbelian 2 W}

@[expose] noncomputable def psiInv (Φ : IntMod W hW ≃* W6 K) {V : Subgroup G} (hVW : V ≤ W) :
    ↥V →* W6 K where
  toFun v := Φ (IntMod.mk hW ⟨v, hVW v.2⟩)
  map_one' := by
    rw [← map_one Φ]
    rfl
  map_mul' a b := by
    rw [← map_mul Φ]
    rfl

theorem psi_psiInv (Φ : IntMod W hW ≃* W6 K) {V : Subgroup G} (hVW : V ≤ W) (v : ↥V) :
    psi Φ (psiInv Φ hVW v) = v := by
  change (Φ.symm (Φ (IntMod.mk hW ⟨v, hVW v.2⟩))).val = v
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem psiInv_psi (Φ : IntMod W hW ≃* W6 K) {V : Subgroup G} (hVW : V ≤ W) (x : W6 K)
    (hx : psi Φ x ∈ V) : psiInv Φ hVW ⟨psi Φ x, hx⟩ = x :=
  psi_injective Φ (psi_psiInv Φ hVW _)

theorem isInvD_comap (Φ : IntMod W hW ≃* W6 K) {L U : Subgroup G}
    (hL : (autI hW L).map (congrHom Φ) = diagSL K) (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    IsInvD (U.comap (psi Φ)) := by
  intro γ hγ x hx
  have hmem : matAut (dgHom γ) ∈ (autI hW L).map (congrHom Φ) := by
    rw [hL]
    exact matAut_dgHom_mem_diagSL hγ
  obtain ⟨l, hl, hlL, hle⟩ := (mem_map_autI Φ).mp hmem
  change psi Φ (matAut (dgHom γ) x) ∈ U
  rw [← hle, psi_hat]
  exact (Subgroup.mem_normalizer_iff.mp (hLU hlL) _).mp hx

theorem psi_mem_of_isEndStable (Φ : IntMod W hW ≃* W6 K) {L V U : Subgroup G}
    (hL : (autI hW L).map (congrHom Φ) = diagSL K) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hVW : V ≤ W) (hUV : U ≤ V) (hU : IsEndStable L V ⊥ U) (T : W6 K →* W6 K)
    (hTV : ∀ x, psi Φ x ∈ V → psi Φ (T x) ∈ V)
    (hT : ∀ γ ∈ StatedSL 3 K, ∀ v, T (matAut (dgHom γ) v) = matAut (dgHom γ) (T v))
    {x : W6 K} (hx : psi Φ x ∈ U) : psi Φ (T x) ∈ U := by
  let φ : ↥V →* ↥V :=
    { toFun := fun v => ⟨psi Φ (T (psiInv Φ hVW v)), hTV _ (by rw [psi_psiInv]; exact v.2)⟩
      map_one' := Subtype.ext (by simp only [map_one]; rfl)
      map_mul' := fun a b => Subtype.ext (by simp only [map_mul]; rfl) }
  have h1 := hU φ (fun c hc => by
      rw [Subgroup.mem_bot] at hc ⊢
      have : c = 1 := Subtype.ext hc
      rw [this, map_one]
      rfl)
    (fun l hl v w hw => by
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      have hlN := hLW hl
      obtain ⟨γ, hγ, hγl⟩ : hat Φ l hlN ∈ diagSL K := by
        rw [← hL]
        exact hat_mem_map_autI Φ hlN hl
      have hγl' : matAut (dgHom γ) = hat Φ l hlN := hγl
      have hw' : psiInv Φ hVW w = hat Φ l hlN (psiInv Φ hVW v) := by
        apply psi_injective Φ
        rw [psi_psiInv, psi_hat, psi_psiInv, hw]
      change psi Φ (T (psiInv Φ hVW w)) = l * psi Φ (T (psiInv Φ hVW v)) * l⁻¹
      rw [hw', ← hγl', hT γ hγ, hγl', psi_hat])
    ⟨psi Φ x, hUV hx⟩ hx
  change psi Φ (T (psiInv Φ hVW ⟨psi Φ x, hUV hx⟩)) ∈ U at h1
  rwa [psiInv_psi] at h1

@[expose] def natCoord (s t : K) : (I6 → K) →+ (Fin 3 → K) where
  toFun v := s • (v ∘ Sum.inl) + t • (v ∘ Sum.inr)
  map_zero' := by simp
  map_add' v w := by
    change s • (v ∘ Sum.inl + w ∘ Sum.inl) + t • (v ∘ Sum.inr + w ∘ Sum.inr) = _
    rw [smul_add, smul_add]
    abel

theorem natCoord_natVec {a b s t : K} (hst : s * a + t * b = 1) (u : Fin 3 → K) :
    natCoord s t (natVec a b u) = u := by
  change s • (natVec a b u ∘ Sum.inl) + t • (natVec a b u ∘ Sum.inr) = u
  rw [natVec_inl, natVec_inr, smul_smul, smul_smul, ← add_smul, hst, one_smul]

theorem exists_coeff {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) : ∃ s t : K, s * a + t * b = 1 := by
  rcases hab with ha | hb
  · exact ⟨a⁻¹, 0, by rw [inv_mul_cancel₀ ha, zero_mul, add_zero]⟩
  · exact ⟨0, b⁻¹, by rw [inv_mul_cancel₀ hb, zero_mul, zero_add]⟩

theorem isEndStable_of_scal (Φ : IntMod W hW ≃* W6 K) {L V U : Subgroup G}
    (hL : (autI hW L).map (congrHom Φ) = diagSL K) (hVW : V ≤ W) {a b : K}
    (hab : a ≠ 0 ∨ b ≠ 0) (hV : V.comap (psi Φ) = natSub a b)
    (hs : ∀ (c : K) (x : W6 K), psi Φ x ∈ U → psi Φ (scalHom c x) ∈ U) :
    IsEndStable L V ⊥ U := by
  intro φ hφC hφL u hu
  obtain ⟨s₀, t₀, hst⟩ := exists_coeff hab
  have hmemV : ∀ y : StdMod (Fin 3) K, psi Φ (natEmb a b y) ∈ V := fun y => by
    have : natEmb a b y ∈ V.comap (psi Φ) := by rw [hV]; exact ⟨y, rfl⟩
    exact this
  let e : StdMod (Fin 3) K →* ↥V :=
    { toFun := fun y => ⟨psi Φ (natEmb a b y), hmemV y⟩
      map_one' := Subtype.ext (show psi Φ (natEmb a b 1) = 1 by rw [map_one, map_one])
      map_mul' := fun y y' => Subtype.ext (show psi Φ (natEmb a b (y * y')) =
        psi Φ (natEmb a b y) * psi Φ (natEmb a b y') by rw [map_mul, map_mul]) }
  let T : (Fin 3 → K) →+ (Fin 3 → K) :=
    { toFun := fun y => natCoord s₀ t₀ (Multiplicative.toAdd
        (psiInv Φ hVW (φ (e (Multiplicative.ofAdd y)))))
      map_zero' := by
        rw [ofAdd_zero, map_one, map_one, map_one, toAdd_one, map_zero]
      map_add' := fun y y' => by
        rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul, map_add] }
  have hnat : ∀ y, psiInv Φ hVW (φ (e y)) ∈ natSub a b := by
    intro y
    rw [← hV]
    change psi Φ (psiInv Φ hVW (φ (e y))) ∈ V
    rw [psi_psiInv]
    exact (φ (e y)).2
  have hTe : ∀ y, psiInv Φ hVW (φ (e y)) =
      natEmb a b (Multiplicative.ofAdd (T (Multiplicative.toAdd y))) := by
    intro y
    obtain ⟨z, hz⟩ := hnat y
    rw [← hz]
    congr 1
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd z = natCoord s₀ t₀ (Multiplicative.toAdd (psiInv Φ hVW (φ (e
      (Multiplicative.ofAdd (Multiplicative.toAdd y))))))
    rw [ofAdd_toAdd, ← hz, toAdd_natEmb, natCoord_natVec hst]
  have hTc : ∀ γ ∈ StatedSL 3 K, ∀ y, T ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ y) =
      (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ T y := by
    intro γ hγ y
    have hmem : matAut (dgHom γ) ∈ (autI hW L).map (congrHom Φ) := by
      rw [hL]
      exact matAut_dgHom_mem_diagSL hγ
    obtain ⟨l, hlN, hlL, hle⟩ := (mem_map_autI Φ).mp hmem
    have hconj : ((e (matAut γ (Multiplicative.ofAdd y)) : ↥V) : G) =
        l * (e (Multiplicative.ofAdd y) : G) * l⁻¹ := by
      change psi Φ (natEmb a b (matAut γ _)) = l * psi Φ (natEmb a b _) * l⁻¹
      rw [← matAut_dgHom_natEmb, ← hle, psi_hat]
    have h1 := hφL l hlL _ _ hconj
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
    have h2 : psiInv Φ hVW (φ (e (matAut γ (Multiplicative.ofAdd y)))) =
        hat Φ l hlN (psiInv Φ hVW (φ (e (Multiplicative.ofAdd y)))) := by
      apply psi_injective Φ
      rw [psi_psiInv, psi_hat, psi_psiInv, h1]
    rw [hle, hTe, hTe, matAut_dgHom_natEmb] at h2
    exact congrArg Multiplicative.toAdd (natEmb_injective hab h2)
  obtain ⟨c, hc⟩ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3) T hTc
  obtain ⟨x, hx⟩ := exists_psi_eq Φ (hVW u.2)
  have hxV : x ∈ natSub a b := by rw [← hV]; change psi Φ x ∈ V; rw [hx]; exact u.2
  obtain ⟨y, rfl⟩ := hxV
  have hu' : u = e y := Subtype.ext hx.symm
  have h4 := hTe y
  rw [hc] at h4
  have h5 : ((φ u : ↥V) : G) = psi Φ (scalHom c (natEmb a b y)) := by
    rw [hu', ← psi_psiInv Φ hVW (φ (e y)), h4]
    congr 1
    apply Multiplicative.toAdd.injective
    change natVec a b (c • Multiplicative.toAdd y) = c • natVec a b (Multiplicative.toAdd y)
    funext i
    rcases i with i | i <;> simp [natVec, mul_left_comm]
  rw [h5]
  exact hs c _ (hx ▸ hu)

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
