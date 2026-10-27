module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProofCrossMat
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.ComponentClassification CFSG.RankThree.CALinearPlane

@[expose] def GGTypeACorankTwoModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G) (y₃ : G) (K₃ : Subgroup G),
    GGTypeANbrCfg p B Bs x L D J n f y K → GGTypeANbr p B Bs x L D J n f y₃ K₃ → p ∣ n + 3 →
    ¬ K₃ ≤ L ⊔ K →
    ∃ π : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) (GaloisField 2 f) →* G,
      π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1 + 1 + 1)) (GaloisField 2 f)) ∧
      (π.comp (slBlockHom₂ n (GaloisField 2 f))).range = L ∧
      K ≤ (coordBlockSL (GaloisField 2 f) (Finset.univ.erase (Fin.last (n + 1 + 1)))).map π ∧
      K₃ ≤ (coordBlockSL (GaloisField 2 f)
        (Finset.univ.erase (Fin.last (n + 1)).castSucc)).map π

section Helpers

variable {N : ℕ} {F : Type} [Field F]

theorem eq_one_of_mem_coordBlockSL_erase {d : Fin N} {u : SpecialLinearGroup (Fin N) F}
    (hu : u ∈ coordBlockSL F (Finset.univ.erase d))
    (hz : u ∈ Subgroup.center (SpecialLinearGroup (Fin N) F)) : u = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 := mem_coordBlockSL_iff.mp hu d d (Or.inl (by simp))
  rw [ite_eq_left rfl, ← hr, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  ext i j
  rw [← hr, h1, map_one]
  rfl

theorem eq_of_map_eq_of_mem_coordBlockSL_erase {X : Type*} [Group X]
    {π : SpecialLinearGroup (Fin N) F →* X}
    (hker : π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin N) F)) {d : Fin N}
    {u v : SpecialLinearGroup (Fin N) F} (hu : u ∈ coordBlockSL F (Finset.univ.erase d))
    (hv : v ∈ coordBlockSL F (Finset.univ.erase d)) (h : π u = π v) : u = v := by
  have hm : u * v⁻¹ ∈ coordBlockSL F (Finset.univ.erase d) := mul_mem hu (inv_mem hv)
  have hk : u * v⁻¹ ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.mp (eq_one_of_mem_coordBlockSL_erase hm (hker hk))

theorem conj_pow_of_mul_eq_one {P Q X : Matrix (Fin N) (Fin N) F} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (k : ℕ) : (P * X * Q) ^ k = P * X ^ k * Q := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPQ]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * X ^ k * Q * (P * X * Q) = P * X ^ k * (Q * P) * X * Q := by
          simp only [Matrix.mul_assoc]
      _ = P * (X ^ k * X) * Q := by rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]

end Helpers

section EndNode

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem val_of_not_mem_ggLeviCoords {k : Fin (n + 1 + 1 + 1)} (hk : k ∉ ggLeviCoords n) :
    k.val = n + 1 ∨ k.val = n + 1 + 1 := by
  rcases not_mem_ggLeviCoords_iff.mp hk with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem ggModel_endNode (h2 : (2 : F) = 0) (hn : 2 ≤ n)
    (π : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F →* X)
    (hker : π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F))
    (A : GL (Fin (n + 1)) F) (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1)
    {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hφ : ∀ g, φ₁ g = π (slBlockHom₂ n F
      ((CatalogueBHigherLinearAction.slConjugation (n + 1) F A *
        CatalogueBHigherLinearField.slFieldAut (Fin (n + 1)) F σ *
          CatalogueBGraphForm.slGraphAut (n + 1) F ^ ε) g)))
    {d e : Fin (n + 1 + 1 + 1)} (hde : d ≠ e) (hd : d ∉ ggLeviCoords n)
    (he : e ∉ ggLeviCoords n) {T : X}
    (hTm : T ∈ (coordBlockSL F (Finset.univ.erase d)).map π) (hT : GGTypeAEndNode φ₁ T) :
    ∃ t ∈ coordBlockSL F (Finset.univ.erase d), π t = T ∧
      ∃ v : Fin (n + 1 + 1 + 1) → F, (∀ i, i ≠ ⟨n, by omega⟩ → i ≠ e → v i = 1) ∧
        v ⟨n, by omega⟩ * v e = 1 ∧
        slBlockMat (n + 1) F (slBlockMat n F (A⁻¹).val) *
            (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) *
          slBlockMat (n + 1) F (slBlockMat n F A.val) =
            signedPerm (Equiv.swap ⟨n, by omega⟩ e) v := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hTm
  set a₀ : Fin (n + 1 + 1 + 1) := ⟨n, by omega⟩ with ha₀
  set m₀ : Fin (n + 1 + 1 + 1) := ⟨n - 1, by omega⟩ with hm₀
  set S := Finset.univ.erase d with hS
  set P := slBlockMat (n + 1) F (slBlockMat n F A.val) with hP
  set Q := slBlockMat (n + 1) F (slBlockMat n F (A⁻¹).val) with hQ
  have hPQ : P * Q = 1 := slBlockMat₂_mul_inv A
  have hQP : Q * P = 1 := slBlockMat₂_inv_mul A
  have hdv := val_of_not_mem_ggLeviCoords hd
  have hev := val_of_not_mem_ggLeviCoords he
  have hdev : d.val ≠ e.val := fun h => hde (Fin.ext h)
  have hLS : ggLeviCoords n ⊆ S := fun k hk =>
    Finset.mem_erase.mpr ⟨fun h => hd (h ▸ hk), Finset.mem_univ _⟩
  have hPS : GGIdOutside S P := (ggIdOutside_slBlockMat₂ _).mono hLS
  have hQS : GGIdOutside S Q := (ggIdOutside_slBlockMat₂ _).mono hLS
  have hβS : ∀ g, slBlockHom₂ n F g ∈ coordBlockSL F S := by
    intro g
    apply ggIdOutside_iff_mem_coordBlockSL.mp
    rw [coe_slBlockHom₂]
    exact (ggIdOutside_slBlockMat₂ _).mono hLS
  have htS : GGIdOutside S (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) :=
    ggIdOutside_iff_mem_coordBlockSL.mpr ht
  set τ := Q * (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) * P with hτ
  have hτdet : τ.det = 1 := by
    rw [hτ, Matrix.det_mul, Matrix.det_mul, t.2, mul_one, ← Matrix.det_mul, hQP, Matrix.det_one]
  set τs : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F := ⟨τ, hτdet⟩ with hτs
  have hτS : GGIdOutside S τ := (hQS.mul htS).mul hPS
  have ht2 : t * t = 1 :=
    eq_of_map_eq_of_mem_coordBlockSL_erase hker (mul_mem ht ht) (one_mem _)
      (by rw [map_mul, hT.1, map_one])
  have hττ : τ * τ = 1 := by
    calc τ * τ = Q * ((t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) * (P * Q) *
          (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F)) * P := by
          simp only [hτ, Matrix.mul_assoc]
      _ = Q * ((t * t : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
          Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) * P := by
          rw [hPQ, Matrix.mul_one, Matrix.SpecialLinearGroup.coe_mul]
      _ = 1 := by rw [ht2, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hQP]
  have hτ2 : τs * τs = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact hττ)
  have hcomm : ∀ i j : Fin (n + 1), i.val < n → j.val < n → ∀ hij : i ≠ j,
      Commute τs (SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) (1 : F)) := by
    intro i j hi hj hij
    obtain ⟨i', j', h', c, hij', he'⟩ := exists_slFieldGraph_transvection σ hε hij
    have hi' : i'.val < n := by rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hj' : j'.val < n := by rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have h3 := hT.2.2 i' j' h' hi' hj' c
    rw [hφ, mul_assoc, MulAut.mul_apply, he'] at h3
    set y := slBlockHom₂ n F (CatalogueBHigherLinearAction.slConjugation (n + 1) F A
      (SpecialLinearGroup.transvection hij 1)) with hy
    have hty : t * y = y * t :=
      eq_of_map_eq_of_mem_coordBlockSL_erase hker (mul_mem ht (hβS _)) (mul_mem (hβS _) ht)
        (by rw [map_mul, map_mul, h3])
    set E := ((slBlockHom₂ n F (SpecialLinearGroup.transvection hij (1 : F)) :
      SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
        Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) with hE
    have hym : ((y : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
        Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) = P * E * Q :=
      coe_slBlockHom₂_slConjugation A _
    have hm : (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) * (P * E * Q) =
        (P * E * Q) * (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) := by
      have h1 := congrArg Subtype.val hty
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
      rwa [hym] at h1
    have hτE : τ * E = E * τ := by
      calc τ * E = Q * ((t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) *
            (P * E * Q)) * P := by
            rw [show τ * E = τ * E * (Q * P) by rw [hQP, Matrix.mul_one]]
            simp only [hτ, Matrix.mul_assoc]
        _ = Q * ((P * E * Q) * (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F)) *
            P := by rw [hm]
        _ = (Q * P) * E * τ := by simp only [hτ, Matrix.mul_assoc]
        _ = E * τ := by rw [hQP, Matrix.one_mul]
    rw [← slBlockHom₂_transvection]
    exact Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hτE)
  have hk1 : (⟨n - 1, by omega⟩ : Fin n).val + 1 = n := by simp only; omega
  have h3 := hT.2.1 ⟨n - 1, by omega⟩ hk1
  rw [hφ, mul_assoc, MulAut.mul_apply, slFieldGraph_weylRep_of_two h2 σ hε] at h3
  set y' := slBlockHom₂ n F (CatalogueBHigherLinearAction.slConjugation (n + 1) F A
    (weylRep n F ⟨n - 1, by omega⟩)) with hy'
  have hty' : (t * y') ^ 3 = 1 :=
    eq_of_map_eq_of_mem_coordBlockSL_erase hker (pow_mem (mul_mem ht (hβS _)) 3) (one_mem _)
      (by rw [map_pow, map_mul, h3, map_one])
  set s := ((slBlockHom₂ n F (weylRep n F ⟨n - 1, by omega⟩) :
    SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
      Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) with hs
  have hsm : s = signedPerm (Equiv.swap m₀ a₀) (1 : Fin (n + 1 + 1 + 1) → F) := by
    rw [hs, slBlockHom₂_weylRep, coe_weylRep_of_two (n + 1 + 1) h2]
    congr 2
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc, ha₀]
    omega
  have hy'm : ((y' : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
      Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) = P * s * Q :=
    coe_slBlockHom₂_slConjugation A _
  have hτs3 : (τ * s) ^ 3 = 1 := by
    have e : τ * s = Q * ((t * y' : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
        Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) * P := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hy'm,
        show τ * s = τ * s * (Q * P) by rw [hQP, Matrix.mul_one]]
      simp only [hτ, Matrix.mul_assoc]
    rw [e, conj_pow_of_mul_eq_one hQP hPQ, ← Matrix.SpecialLinearGroup.coe_pow, hty',
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hQP]
  have hss : s * s = 1 := by
    rw [hsm, signedPerm_mul_signedPerm, Equiv.swap_mul_self, signedPerm_one]
    simp
  have hbraid : τ * s * τ = s * τ * s := by
    have hsts : (s * τ * s) * (s * τ * s) = 1 := by
      calc (s * τ * s) * (s * τ * s) = s * (τ * (s * s) * τ) * s := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hss, Matrix.mul_one, hττ, Matrix.mul_one, hss]
    calc τ * s * τ = τ * s * τ * ((s * τ * s) * (s * τ * s)) := by rw [hsts, Matrix.mul_one]
      _ = (τ * s) ^ 3 * (s * τ * s) := by rw [pow_three]; simp only [Matrix.mul_assoc]
      _ = s * τ * s := by rw [hτs3, Matrix.one_mul]
  have hJ : τs ∈ coordBlockSL F ({a₀, d, e} : Finset (Fin (n + 1 + 1 + 1))) := by
    refine mem_coordBlockSL_of_commute h2 hτ2 _ fun i hi => ?_
    have hia : i ≠ a₀ := fun h => hi (by simp [h])
    have hid : i ≠ d := fun h => hi (by simp [h])
    have hie : i ≠ e := fun h => hi (by simp [h])
    have hiv : i.val < n := by
      have h1 : i.val ≠ n := fun h => hia (Fin.ext h)
      have h2' : i.val ≠ d.val := fun h => hid (Fin.ext h)
      have h3' : i.val ≠ e.val := fun h => hie (Fin.ext h)
      have := i.isLt
      omega
    obtain ⟨i₁, rfl⟩ : ∃ i₁ : Fin (n + 1), i₁.castSucc.castSucc = i :=
      ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    have hi₁ : i₁.val < n := hiv
    obtain ⟨j₁, hj₁n, hij₁⟩ : ∃ j₁ : Fin (n + 1), j₁.val < n ∧ i₁ ≠ j₁ := by
      by_cases h0 : i₁.val = 0
      · exact ⟨⟨1, by omega⟩, by simp only; omega, fun h => by
          have := congrArg Fin.val h; simp only at this; omega⟩
      · exact ⟨⟨0, by omega⟩, by simp only; omega, fun h => by
          have := congrArg Fin.val h; simp only at this; omega⟩
    exact ⟨j₁.castSucc.castSucc,
      (Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij₁),
      hcomm i₁ j₁ hi₁ hj₁n hij₁, hcomm j₁ i₁ hj₁n hi₁ hij₁.symm⟩
  have hτJ : GGIdOutside ({a₀, d, e} : Finset (Fin (n + 1 + 1 + 1))) τ :=
    ggIdOutside_iff_mem_coordBlockSL.mpr hJ
  have hτae : GGIdOutside ({a₀, e} : Finset (Fin (n + 1 + 1 + 1))) τ := by
    intro i j hij
    by_cases hid : i = d
    · exact hτS i j (Or.inl (by simp [hS, hid]))
    by_cases hjd : j = d
    · exact hτS i j (Or.inr (by simp [hS, hjd]))
    exact hτJ i j (by simpa [hid, hjd] using hij)
  have hm₀a₀ : m₀ ≠ a₀ := fun h => by
    have h' : n - 1 = n := congrArg Fin.val h
    omega
  have hm₀e : m₀ ≠ e := fun h => by
    have h' : n - 1 = e.val := congrArg Fin.val h
    omega
  have ha₀e : a₀ ≠ e := fun h => by
    have h' : n = e.val := congrArg Fin.val h
    omega
  rw [hsm] at hbraid
  obtain ⟨haa, hee, hae⟩ := hτae.braid_entries hm₀a₀ hm₀e ha₀e hbraid
  refine ⟨t, ht, rfl, fun i => if i = a₀ then τ e a₀ else if i = e then τ a₀ e else 1,
    fun i hia hie => by simp [hia, hie], ?_, hτae.eq_signedPerm ha₀e haa hee⟩
  dsimp only
  rw [ite_eq_left rfl, ite_eq_right ha₀e.symm, ite_eq_left rfl, mul_comm]
  exact hae

end EndNode

theorem ggTypeACrossInput_of_model (h : GGTypeACorankTwoModelInput) : GGTypeACrossInput := by
  intro G _ _ p B Bs x L D J n f y K y₃ K₃ hNC hN₃ hdiv hK₃ φ₁ hφL hker T₁ hT₁LK hT₁ _ T₃
    hT₃LK hT₃ _
  obtain ⟨π, hπ, hπL, hπK, hπK₃⟩ := h G p B Bs x L D J n f y K y₃ K₃ hNC hN₃ hdiv hK₃
  obtain ⟨-, -, -, -, hmod, -, hn, -⟩ := hNC
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  set a : Fin (n + 1 + 1 + 1) := ⟨n, by omega⟩ with ha
  set b : Fin (n + 1 + 1 + 1) := (Fin.last (n + 1)).castSucc with hb
  set c : Fin (n + 1 + 1 + 1) := Fin.last (n + 1 + 1) with hc
  have hbL : b ∉ ggLeviCoords n := not_mem_ggLeviCoords_iff.mpr (Or.inl rfl)
  have hcL : c ∉ ggLeviCoords n := not_mem_ggLeviCoords_iff.mpr (Or.inr rfl)
  have hab : a ≠ b := fun e => by
    have h' : n = n + 1 := congrArg Fin.val e
    omega
  have hac : a ≠ c := fun e => by
    have h' : n = n + 1 + 1 := congrArg Fin.val e
    omega
  have hbc : b ≠ c := Fin.castSucc_ne_last _
  have hdisj : Disjoint ({b, c} : Finset (Fin (n + 1 + 1 + 1))) (ggLeviCoords n) :=
    Finset.disjoint_left.mpr fun k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact hbL
      · rw [Finset.mem_singleton.mp hk']
        exact hcL
  have hβ : ∀ d, d ∉ ggLeviCoords n → ∀ g, slBlockHom₂ n (GaloisField 2 f) g ∈
      coordBlockSL (GaloisField 2 f) (Finset.univ.erase d) := by
    intro d hd g
    apply ggIdOutside_iff_mem_coordBlockSL.mp
    rw [coe_slBlockHom₂]
    exact (ggIdOutside_slBlockMat₂ _).mono fun k hk =>
      Finset.mem_erase.mpr ⟨fun h => hd (h ▸ hk), Finset.mem_univ _⟩
  have hk₂ : (π.comp (slBlockHom₂ n (GaloisField 2 f))).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
    intro g hg
    have h1 : slBlockHom₂ n (GaloisField 2 f) g = 1 :=
      eq_one_of_mem_coordBlockSL_erase (hβ c hcL g) (hπ hg)
    rw [show g = 1 from slBlockHom₂_injective (h1.trans (map_one _).symm)]
    exact one_mem _
  obtain ⟨α, hα⟩ := exists_mulAut_of_slLift (by omega : 3 ≤ n + 1) (hπL.trans hφL.symm) hk₂ hker
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (by omega : 3 ≤ n + 1) α
  have hφ : ∀ g, φ₁ g = π (slBlockHom₂ n (GaloisField 2 f)
      ((CatalogueBHigherLinearAction.slConjugation (n + 1) (GaloisField 2 f) A *
        CatalogueBHigherLinearField.slFieldAut (Fin (n + 1)) (GaloisField 2 f) σ *
          CatalogueBGraphForm.slGraphAut (n + 1) (GaloisField 2 f) ^ ε) g)) := fun g => by
    rw [hα]
    rfl
  have hLm : ∀ d, d ∉ ggLeviCoords n →
      L ≤ (coordBlockSL (GaloisField 2 f) (Finset.univ.erase d)).map π := by
    intro d hd
    rw [← hπL]
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hβ d hd g, rfl⟩
  obtain ⟨t₁, -, rfl, v, hv, hvab, hτ₁⟩ := ggModel_endNode h2 (by omega) π hπ A σ hε hφ
    hbc.symm hcL hbL ((sup_le (hLm c hcL) hπK) hT₁LK) hT₁
  obtain ⟨t₃, -, rfl, w, hw, hwac, hτ₃⟩ := ggModel_endNode h2 (by omega) π hπ A σ hε hφ
    hbc hbL hcL ((sup_le (hLm b hbL) hπK₃) hT₃LK) hT₃
  obtain ⟨hcube, hY⟩ := ggCross_signedPerm hab hac hbc hv hvab hw hwac
  set P := slBlockMat (n + 1) (GaloisField 2 f) (slBlockMat n (GaloisField 2 f) A.val) with hP
  set Q := slBlockMat (n + 1) (GaloisField 2 f) (slBlockMat n (GaloisField 2 f) (A⁻¹).val)
    with hQ
  have hPQ : P * Q = 1 := slBlockMat₂_mul_inv A
  have hQP : Q * P = 1 := slBlockMat₂_inv_mul A
  have hQPZ : ∀ Z : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) (GaloisField 2 f),
      Q * (P * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hback : ∀ (t : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) (GaloisField 2 f))
      (X : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) (GaloisField 2 f)),
      Q * (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) (GaloisField 2 f)) * P = X →
      (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) (GaloisField 2 f)) =
        P * X * Q := by
    intro t X hX
    rw [← hX]
    calc (t : Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) (GaloisField 2 f)) =
          (P * Q) * t * (P * Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = P * (Q * t * P) * Q := by simp only [Matrix.mul_assoc]
  have ht₁m := hback t₁ _ hτ₁
  have ht₃m := hback t₃ _ hτ₃
  refine ⟨?_, fun g => ?_⟩
  ·
    have h31 : (t₃ * t₁) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, ht₃m, ht₁m,
        Matrix.SpecialLinearGroup.coe_one]
      have e : P * signedPerm (Equiv.swap a c) w * Q * (P * signedPerm (Equiv.swap a b) v * Q) =
          P * (signedPerm (Equiv.swap a c) w * signedPerm (Equiv.swap a b) v) * Q := by
        simp only [Matrix.mul_assoc, hQPZ]
      rw [e, conj_pow_of_mul_eq_one hPQ hQP, hcube, Matrix.mul_one, hPQ]
    rw [← map_mul, ← map_pow, h31, map_one]
  ·
    rw [hφ g]
    simp only [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [ht₁m, ht₃m, coe_slBlockHom₂]
    set Y := signedPerm (Equiv.swap a b) v * signedPerm (Equiv.swap a c) w *
      signedPerm (Equiv.swap a b) v with hYdef
    have hPY : P * Y = Y * P := (ggIdOutside_slBlockMat₂ _).commute hdisj.symm hY
    have h131 : P * signedPerm (Equiv.swap a b) v * Q * (P * signedPerm (Equiv.swap a c) w * Q) *
        (P * signedPerm (Equiv.swap a b) v * Q) = Y := by
      calc P * signedPerm (Equiv.swap a b) v * Q * (P * signedPerm (Equiv.swap a c) w * Q) *
            (P * signedPerm (Equiv.swap a b) v * Q) = P * Y * Q := by
            simp only [hYdef, Matrix.mul_assoc, hQPZ]
        _ = Y := by rw [hPY, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    rw [h131]
    exact hY.commute hdisj (ggIdOutside_slBlockMat₂ _)

end CFSG.StandardType
