module

public import CFSG.Quasithin.Background.F918W6
public import CFSG.Quasithin.Background.F918W9
public import CFSG.Quasithin.Background.F918WA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.D35ValChk Matrix

private theorem expand_kid : expand kid = idm := by decide

private theorem toM_expand_kid : toM (expand kid) = 1 := by
  rw [expand_kid, toM_idm]

private theorem toM_expand_kmul {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) :
    toM (expand (kmul a b)) = toM (expand a) * toM (expand b) := by
  rw [expand_kmul ha hb, toM_bmul]

private theorem code_inj {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (h : toM (expand a) = toM (expand b)) : a = b :=
  expand_inj ha hb (toM_inj (expand_lt a) (expand_lt b) h)

private theorem conj_cancel {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {A B X Y : Matrix n n R} (h : B * A = 1) (e : A * X * B = A * Y * B) : X = Y := by
  calc X = (B * A) * X * (B * A) := by rw [h, Matrix.one_mul, Matrix.mul_one]
    _ = B * (A * X * B) * A := by simp only [Matrix.mul_assoc]
    _ = B * (A * Y * B) * A := by rw [e]
    _ = (B * A) * Y * (B * A) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [h, Matrix.one_mul, Matrix.mul_one]

private theorem card_G0_ge (hF : D35Facts) : 1080 ≤ Nat.card G0 := by
  have hex : ∀ i : Fin gl.length, ∃ g : G0,
      ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        toM (expand (gl.get i)) := fun i => exists_G0 hF (List.get_mem _ _)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j h
    have : gl.get i = gl.get j :=
      code_inj (hF.gl_lt _ (List.get_mem _ _)) (hF.gl_lt _ (List.get_mem _ _)) (by rw [← hf i, ← hf j, h])
    exact (List.nodup_iff_injective_get.mp hF.gl_nodup) this
  have := Nat.card_le_card_of_injective f hinj
  simpa [hF.gl_length] using this

private theorem exists_rho1 {K : Type} [Field K] (C : KCoding K)
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} {Ψ Ψ' : Nat} (h1 : bmul Ψ Ψ' = idm)
    (h2 : bmul Ψ' Ψ = idm) :
    ∃ ρ1 : ↥Γ →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 2), ∀ γ : ↥Γ,
      ((ρ1 γ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        toM Ψ * toM (expand (C.mc (((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K))) * toM Ψ' := by
  have hΨ : toM Ψ * toM Ψ' = 1 := by rw [← toM_bmul, h1, toM_idm]
  have hΨ' : toM Ψ' * toM Ψ = 1 := by rw [← toM_bmul, h2, toM_idm]
  let f : ↥Γ →* Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    { toFun := fun γ => toM Ψ * toM (expand (C.mc (((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))) * toM Ψ'
      map_one' := by
        simp only [Subgroup.coe_one, Units.val_one, C.mc_one, toM_expand_kid, Matrix.mul_one]
        exact hΨ
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, Units.val_mul, C.mc_mul, toM_expand_kmul (C.mc_lt _) (C.mc_lt _)]
        calc toM Ψ * (toM (expand (C.mc (((a : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K))) * toM (expand (C.mc (((b : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K)))) * toM Ψ'
            = toM Ψ * toM (expand (C.mc (((a : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K))) * (toM Ψ' * toM Ψ) * toM (expand (C.mc (((b : ↥Γ) :
              Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) * toM Ψ' := by
              rw [hΨ', Matrix.mul_one]
              simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  exact ⟨f.toHomUnits, fun γ => rfl⟩

private theorem exists_psi {K : Type} [Field K] (C : KCoding K) {Ψ Ψ' : Nat} (h1 : bmul Ψ Ψ' = idm)
    (h2 : bmul Ψ' Ψ = idm) :
    ∃ ψ : (Fin 3 → K) ≃+ (Fin 6 → ZMod 2), ∀ w, ψ w = toM Ψ *ᵥ vecOfBits (C.vc w) := by
  have hΨ : toM Ψ * toM Ψ' = 1 := by rw [← toM_bmul, h1, toM_idm]
  have hΨ' : toM Ψ' * toM Ψ = 1 := by rw [← toM_bmul, h2, toM_idm]
  let g : (Fin 3 → K) →+ (Fin 6 → ZMod 2) :=
    AddMonoidHom.mk' (fun w => toM Ψ *ᵥ vecOfBits (C.vc w)) fun w w' => by
      rw [C.vc_add, vecOfBits_xor, Matrix.mulVec_add]
  have hinj : Function.Injective g := by
    intro w w' h
    have h' : vecOfBits (C.vc w) = vecOfBits (C.vc w') := by
      have := congrArg (fun v => toM Ψ' *ᵥ v) h
      simpa [g, Matrix.mulVec_mulVec, hΨ'] using this
    exact C.vc_inj (vecOfBits_inj (C.vc_lt w) (C.vc_lt w') h')
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨n, hn, hny⟩ := vecOfBits_surj (toM Ψ' *ᵥ y)
    obtain ⟨w, hw⟩ := C.vc_surj hn
    refine ⟨w, ?_⟩
    show toM Ψ *ᵥ vecOfBits (C.vc w) = y
    rw [hw, hny, Matrix.mulVec_mulVec, hΨ, Matrix.one_mulVec]
  exact ⟨AddEquiv.ofBijective g ⟨hinj, hsurj⟩, fun w => rfl⟩

private theorem psi_equivariant {K : Type} [Field K] (C : KCoding K) {Ψ Ψ' : Nat} (h2 : bmul Ψ' Ψ = idm)
    (M : Matrix (Fin 3) (Fin 3) K) (w : Fin 3 → K) :
    toM Ψ *ᵥ vecOfBits (C.vc (M *ᵥ w)) =
      (toM Ψ * toM (expand (C.mc M)) * toM Ψ') *ᵥ (toM Ψ *ᵥ vecOfBits (C.vc w)) := by
  have hΨ' : toM Ψ' * toM Ψ = 1 := by rw [← toM_bmul, h2, toM_idm]
  rw [C.mc_apply, ← toM_expand_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc (toM Ψ * toM (expand (C.mc M))), hΨ', Matrix.mul_one]

theorem valentiner_transfer (hF : D35Facts) {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hv : IsValentiner K Γ) :
    ∃ (ρ : ↥Γ ≃* G0) (ψ : (Fin 3 → K) ≃+ (Fin 6 → ZMod 2)), ∀ (γ : ↥Γ) (w : Fin 3 → K),
      ψ (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        (((ρ γ : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ψ w := by
  obtain ⟨C⟩ := exists_kcoding K hv.1
  obtain ⟨x₁, x₂, x₃, h11, h22, h33, h12, h13, h23, h1, h2, h3, r12, r13, r23, r123⟩ := exists_triple hv
  obtain ⟨Ψ, Ψ', s, -, -, hs, hΨΨ', hΨ'Ψ, e1, e2, e3⟩ :=
    exists_normalization hF hv.1 C hv h11 h22 h33 h12 h13 h23 h1 h2 h3 r12 r13 r23 r123
  obtain ⟨ρ1, hρ1⟩ := exists_rho1 (Γ := Γ) C hΨΨ' hΨ'Ψ
  obtain ⟨ψ, hψ⟩ := exists_psi C hΨΨ' hΨ'Ψ
  have hΨ' : toM Ψ' * toM Ψ = 1 := by rw [← toM_bmul, hΨ'Ψ, toM_idm]
  have val : ∀ (x : ↥Γ) (t : Nat),
      bmul (bmul Ψ (expand (C.mc (((x : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)))) Ψ' = expand t →
      ((ρ1 x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        toM (expand t) := by
    intro x t h
    rw [hρ1, ← h, toM_bmul, toM_bmul]
  have v1 := val x₁ _ e1
  have v2 := val x₂ _ e2
  have v3 := val x₃ _ e3
  have hinj : Function.Injective ρ1 := by
    intro γ δ h
    have hm : ((ρ1 γ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        ((ρ1 δ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by rw [h]
    rw [hρ1, hρ1] at hm
    have hc := conj_cancel hΨ' hm
    have := code_inj (C.mc_lt _) (C.mc_lt _) hc
    exact Subtype.ext (Units.ext (C.mc_inj this))
  have hs' : s = 0 ∨ s = 1 := by omega
  have hS : ρ1 '' ({x₁, x₂, x₃} : Set ↥Γ) = {g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) |
      ∃ i, i < 3 ∧ ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        toM (expand (genK i))} := by
    ext g
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [v1]; rfl⟩
      · rcases hs' with rfl | rfl
        · exact ⟨1, by norm_num, by rw [v2]; rfl⟩
        · exact ⟨2, by norm_num, by rw [v2]; rfl⟩
      · rcases hs' with rfl | rfl
        · exact ⟨2, by norm_num, by rw [v3]; rfl⟩
        · exact ⟨1, by norm_num, by rw [v3]; rfl⟩
    · rintro ⟨i, hi, hg⟩
      interval_cases i
      · exact Or.inl (Units.ext (by rw [hg, v1]; rfl)).symm
      · rcases hs' with rfl | rfl
        · exact Or.inr (Or.inl (Units.ext (by rw [hg, v2]; rfl)).symm)
        · exact Or.inr (Or.inr (Units.ext (by rw [hg, v3]; rfl)).symm)
      · rcases hs' with rfl | rfl
        · exact Or.inr (Or.inr (Units.ext (by rw [hg, v3]; rfl)).symm)
        · exact Or.inr (Or.inl (Units.ext (by rw [hg, v2]; rfl)).symm)
  have hmapH : (Subgroup.closure ({x₁, x₂, x₃} : Set ↥Γ)).map ρ1 = G0 := by
    rw [MonoidHom.map_closure, hS]
    rfl
  have hcardH : Nat.card (Subgroup.closure ({x₁, x₂, x₃} : Set ↥Γ)) = Nat.card G0 := by
    rw [← hmapH, Subgroup.card_map_of_injective hinj]
  have hΓ : Nat.card ↥Γ = 1080 := card_valentiner hv
  have hHle := Subgroup.card_le_card_group (Subgroup.closure ({x₁, x₂, x₃} : Set ↥Γ))
  have hG0 := card_G0_ge hF
  have hHtop : Subgroup.closure ({x₁, x₂, x₃} : Set ↥Γ) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    omega
  have hmem : ∀ γ : ↥Γ, ρ1 γ ∈ G0 := fun γ => by
    have : ρ1 γ ∈ (Subgroup.closure ({x₁, x₂, x₃} : Set ↥Γ)).map ρ1 :=
      Subgroup.mem_map_of_mem ρ1 (by rw [hHtop]; trivial)
    rwa [hmapH] at this
  have hsurj : Function.Surjective (ρ1.codRestrict G0 hmem) := by
    intro g
    have hg : (g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) ∈
        (Subgroup.closure ({x₁, x₂, x₃} : Set ↥Γ)).map ρ1 := by
      rw [hmapH]
      exact g.2
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.mp hg
    exact ⟨γ, Subtype.ext hγ⟩
  refine ⟨MulEquiv.ofBijective (ρ1.codRestrict G0 hmem) ⟨fun a b h => hinj (congrArg Subtype.val h), hsurj⟩, ψ,
    fun γ w => ?_⟩
  rw [hψ, hψ]
  show _ = ((ρ1 γ : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ _
  rw [hρ1 γ]
  exact psi_equivariant C hΨ'Ψ _ w

end CFSG.Quasithin
