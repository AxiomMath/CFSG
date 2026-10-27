module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W6
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7T1
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7QN
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Perfect

variable {Q : Type} [CommGroup Q]

theorem commV_le_of_perfect627 {L : Subgroup (MulAut Q)} (hperf : Group.IsPerfect ↥L)
    {M : Subgroup Q} (hM : ∀ x ∈ L, ∀ n ∈ commV L, x n * n⁻¹ ∈ M) : commV L ≤ M := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  let f : ↥L →* Q ⧸ M :=
    { toFun := fun y => (((y : MulAut Q) v * v⁻¹ : Q) : Q ⧸ M)
      map_one' := by simp
      map_mul' := fun y z => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hw : (z : MulAut Q) v * v⁻¹ ∈ commV L := Subgroup.subset_closure ⟨z, z.2, v, rfl⟩
        have h1 := M.inv_mem (hM y y.2 _ hw)
        convert h1 using 1
        simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel }
  have h1 : (⟨x, hx⟩ : ↥L) ∈ f.ker :=
    Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem fix_commV_of_commute627 {L : Subgroup (MulAut Q)} (hperf : Group.IsPerfect ↥L)
    {δ : MulAut Q} (hδL : ∀ x ∈ L, δ * x = x * δ)
    (hδN : ∀ n ∈ commV L, δ n * n⁻¹ ∈ fixV L) : ∀ q ∈ commV L, δ q = q := by
  intro q hq
  have hle : commV L ≤ fixV (Subgroup.zpowers δ) := by
    refine commV_le_of_perfect627 hperf fun x hx n hn => ?_
    rw [mem_fixV_zpowers627]
    have hxz : x (δ n * n⁻¹) = δ n * n⁻¹ := hδN n hn x hx
    have hxδ : δ (x n) = x (δ n) := by
      rw [← MulAut.mul_apply, hδL x hx, MulAut.mul_apply]
    rw [map_mul, map_inv] at hxz
    rw [map_mul, map_inv, hxδ, mul_inv_eq_iff_eq_mul.mp hxz]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact mem_fixV_zpowers627.mp (hle hq)

end Perfect

section Induced

variable {Q : Type} [CommGroup Q] {W : Type} [Group W] [Finite W]

theorem exists_induced627 {N : Subgroup Q} (β : ↥N →* W) (hβs : Function.Surjective β)
    {δ : MulAut Q} (hN : ∀ n ∈ N, δ n ∈ N) (hN' : ∀ n ∈ N, δ⁻¹ n ∈ N)
    (hker : ∀ n : ↥N, β n = 1 → β ⟨δ n, hN n n.2⟩ = 1) :
    ∃ δW : MulAut W, ∀ n : ↥N, δW (β n) = β ⟨δ n, hN n n.2⟩ := by
  classical
  let δN : ↥N →* ↥N :=
    { toFun := fun n => ⟨δ n, hN n n.2⟩
      map_one' := Subtype.ext (map_one δ)
      map_mul' := fun a b => Subtype.ext (map_mul δ (a : Q) b) }
  have hle : β.ker ≤ (β.comp δN).ker := fun n hn => hker n hn
  let e := QuotientGroup.quotientKerEquivOfSurjective β hβs
  let g : W →* W := (QuotientGroup.lift β.ker (β.comp δN) hle).comp e.symm.toMonoidHom
  have hg : ∀ n : ↥N, g (β n) = β ⟨δ n, hN n n.2⟩ := by
    intro n
    have h1 : e.symm (β n) = (n : ↥N ⧸ β.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift β.ker (β.comp δN) hle (e.symm (β n)) = _
    rw [h1]
    rfl
  have hsurj : Function.Surjective g := by
    intro w
    obtain ⟨m, rfl⟩ := hβs w
    refine ⟨β ⟨δ⁻¹ m, hN' m m.2⟩, ?_⟩
    rw [hg]
    congr 1
    apply Subtype.ext
    show δ (δ⁻¹ (m : Q)) = m
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  exact ⟨MulEquiv.ofBijective g ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩, hg⟩

end Induced

section Matrix

@[expose] def glAut627 {d : ℕ} {F : Type} [Field F] (g : Matrix.GeneralLinearGroup (Fin d) F) :
    MulAut (Multiplicative (Fin d → F)) where
  toFun v := Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) F).mulVec (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec
      (Multiplicative.toAdd v))
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    have : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        (g : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
    rfl
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    have : (g : Matrix (Fin d) (Fin d) F) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
    rfl
  map_mul' a b := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem glAut627_apply {d : ℕ} {F : Type} [Field F] (g : Matrix.GeneralLinearGroup (Fin d) F)
    (v : Multiplicative (Fin d → F)) :
    Multiplicative.toAdd (glAut627 g v) =
      (g : Matrix (Fin d) (Fin d) F).mulVec (Multiplicative.toAdd v) :=
  rfl

@[expose] def glAutHom627 (d : ℕ) (F : Type) [Field F] :
    Matrix.GeneralLinearGroup (Fin d) F →* MulAut (Multiplicative (Fin d → F)) where
  toFun := glAut627
  map_one' := by
    ext v
    apply Multiplicative.toAdd.injective
    rw [glAut627_apply]
    simp
  map_mul' a b := by
    ext v
    apply Multiplicative.toAdd.injective
    rw [glAut627_apply, MulAut.mul_apply, glAut627_apply, glAut627_apply, Matrix.mulVec_mulVec]
    rfl

@[expose] noncomputable def slAct627 :
    ↥(StatedSL 3 (ZMod 2)) →* MulAut (Multiplicative (Fin 3 → ZMod 2)) :=
  (glAutHom627 3 (ZMod 2)).comp (StatedSL 3 (ZMod 2)).subtype

theorem slAct627_apply (γ : ↥(StatedSL 3 (ZMod 2))) (v : Multiplicative (Fin 3 → ZMod 2)) :
    Multiplicative.toAdd (slAct627 γ v) =
      ((γ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (Multiplicative.toAdd v) :=
  rfl

theorem slAct627_injective : Function.Injective slAct627 := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine natAct_faithful _ γ fun m => ?_
  show slAct627 γ m * m⁻¹ = 1
  rw [hγ, MulAut.one_apply]
  exact mul_inv_cancel m

theorem slAct627_surjective : Function.Surjective slAct627 := by
  classical
  intro φ
  let f : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
      map_zero' := by
        show Multiplicative.toAdd (φ 1) = 0
        rw [map_one]
        rfl
      map_add' := fun a b => by
        show Multiplicative.toAdd (φ (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) = _
        rw [map_mul, toAdd_mul] }
  let fl : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c v => by
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        rcases hc c with rfl | rfl
        · simp
        · simp }
  set M := LinearMap.toMatrix' fl with hM
  have hMv : ∀ v, M.mulVec v = f v := fun v => by
    rw [hM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hdet0 : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    apply hv0
    have h1 : φ (Multiplicative.ofAdd v) = φ 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      exact (hMv v).symm.trans hv
    exact Multiplicative.ofAdd.injective (φ.injective h1)
  have hdet : M.det = 1 := by
    revert hdet0
    generalize M.det = c
    revert c
    decide
  refine ⟨specialLinearGroupEquivStatedSL 3 (ZMod 2)
    (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)), ?_⟩
  refine MulEquiv.ext fun v => ?_
  apply Multiplicative.toAdd.injective
  rw [slAct627_apply]
  exact hMv _

end Matrix

section SL32

variable {Q : Type} [CommGroup Q]

theorem centralizes_of_sl32_627 {L S : Subgroup (MulAut Q)}
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1) (hperf : Group.IsPerfect ↥L)
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ (S.subgroupOf L).index) {δ : MulAut Q}
    (hδL : δ ∈ Subgroup.normalizer (L : Set (MulAut Q)))
    (hδS : δ ∈ Subgroup.normalizer (S : Set (MulAut Q))) (hδ3 : δ ^ 3 = 1) :
    (∀ x ∈ L, δ * x = x * δ) ∧ ∀ q ∈ commV L, δ q = q := by
  classical
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  obtain ⟨-, hLN, β, hβs, hβk, hβe⟩ := natReal627 hπ
  set e : ↥(StatedSL 3 (ZMod 2)) ≃* ↥L := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    with he
  have heπ : ∀ γ, e γ = π γ := fun γ => rfl
  set lam : ↥L →* MulAut (Multiplicative (Fin 3 → ZMod 2)) :=
    slAct627.comp e.symm.toMonoidHom with hlam
  have hlam_bij : Function.Bijective lam :=
    ⟨slAct627_injective.comp e.symm.injective, slAct627_surjective.comp e.symm.surjective⟩
  have hlamβ : ∀ (x : ↥L) (n : ↥(commV L)),
      lam x (β n) = β ⟨(x : MulAut Q) n, hLN x n n.2⟩ := by
    intro x n
    have hx : π (e.symm x) = x := (heπ _).symm.trans (e.apply_symm_apply x)
    have hu : ((π (e.symm x) : ↥L) : MulAut Q) (n : Q) ∈ commV L := by
      rw [hx]
      exact hLN x n n.2
    have h1 := hβe (e.symm x) n hu
    have h2 : (⟨(x : MulAut Q) n, hLN x n n.2⟩ : ↥(commV L)) = ⟨_, hu⟩ :=
      Subtype.ext (congrArg (fun y : ↥L => (y : MulAut Q) (n : Q)) hx.symm)
    apply Multiplicative.toAdd.injective
    calc Multiplicative.toAdd (lam x (β n))
        = ((e.symm x : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β n)) := rfl
      _ = Multiplicative.toAdd (β ⟨_, hu⟩) := h1.symm
      _ = Multiplicative.toAdd (β ⟨(x : MulAut Q) n, hLN x n n.2⟩) :=
          congrArg (fun m => Multiplicative.toAdd (β m)) h2.symm
  have hLδ : L.map (MulAut.conj δ).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hδL
  have hLδ' : L.map (MulAut.conj δ⁻¹).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hδL)
  have hδN : ∀ n ∈ commV L, δ n ∈ commV L := by
    intro n hn
    have h1 := commV_conj627 L δ
    rw [hLδ] at h1
    rw [h1]
    exact ⟨n, hn, rfl⟩
  have hδN' : ∀ n ∈ commV L, δ⁻¹ n ∈ commV L := by
    intro n hn
    have h1 := commV_conj627 L δ⁻¹
    rw [hLδ'] at h1
    rw [h1]
    exact ⟨n, hn, rfl⟩
  have hδF : ∀ n ∈ fixV L, δ n ∈ fixV L := by
    intro n hn
    have h1 := fixV_conj627 L δ
    rw [hLδ] at h1
    rw [h1]
    exact ⟨n, hn, rfl⟩
  obtain ⟨δW, hδW⟩ := exists_induced627 β hβs hδN hδN' fun n hn =>
    (hβk _).mpr ⟨hδF n ((hβk n).mp hn).1, hδN n n.2⟩
  have hδWinv : ∀ n : ↥(commV L), δW⁻¹ (β n) = β ⟨δ⁻¹ n, hδN' n n.2⟩ := by
    intro n
    apply δW.injective
    rw [MulAut.apply_inv_self, hδW]
    congr 1
    apply Subtype.ext
    show (n : Q) = δ (δ⁻¹ (n : Q))
    rw [MulAut.apply_inv_self]
  have : Finite (MulAut (Multiplicative (Fin 3 → ZMod 2))) :=
    Finite.of_injective (fun g : MulAut (Multiplicative (Fin 3 → ZMod 2)) =>
      (g : Multiplicative (Fin 3 → ZMod 2) → Multiplicative (Fin 3 → ZMod 2)))
      DFunLike.coe_injective
  set P := (S.subgroupOf L).map lam with hP
  have hP2 : IsPGroup 2 P :=
    (hS2.comap_of_injective L.subtype L.subtype_injective).map lam
  have hPi : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_map_of_bijective hlam_bij]
    exact hSi
  have hδWP : δW ∈ Subgroup.normalizer (P : Set (MulAut (Multiplicative (Fin 3 → ZMod 2)))) := by
    refine mem_normalizer_of_conj_mem627 ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsS : (s : MulAut Q) ∈ S := hs
    have hy : δ * s * δ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hδL s).mp s.2
    refine ⟨⟨δ * s * δ⁻¹, hy⟩, (Subgroup.mem_normalizer_iff.mp hδS s).mp hsS, ?_⟩
    refine MulEquiv.ext fun w => ?_
    obtain ⟨n, rfl⟩ := hβs w
    calc lam ⟨δ * s * δ⁻¹, hy⟩ (β n)
        = β ⟨δ ((s : MulAut Q) (δ⁻¹ n)), hδN _ (hLN s _ (hδN' n n.2))⟩ := hlamβ _ _
      _ = δW (β ⟨(s : MulAut Q) (δ⁻¹ n), hLN s _ (hδN' n n.2)⟩) :=
          (hδW ⟨(s : MulAut Q) (δ⁻¹ n), hLN s _ (hδN' n n.2)⟩).symm
      _ = δW (lam s (β ⟨δ⁻¹ n, hδN' n n.2⟩)) := by rw [hlamβ]
      _ = δW (lam s (δW⁻¹ (β n))) := by rw [hδWinv]
      _ = (δW * lam s * δW⁻¹) (β n) := rfl
  have hδW3 : δW ^ 3 = 1 := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨n, rfl⟩ := hβs w
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hδW, hδW, hδW, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    have := congrArg (fun φ : MulAut Q => φ (n : Q)) hδ3
    simpa [pow_three, MulAut.mul_apply] using this
  have hodd : Odd (orderOf δW) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hδW3)
  have hW : ∀ w : Multiplicative (Fin 3 → ZMod 2), w ^ 2 = 1 := by
    have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
    intro w
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, two_nsmul, toAdd_one]
    funext i
    exact h2 _
  have hδW1 : δW = 1 := eq_one_of_mem_normalizer_sylow_ch627 hW hP2 hPi hδWP hodd
  have hδfix : ∀ n ∈ commV L, δ n * n⁻¹ ∈ fixV L := by
    intro n hn
    have h1 : β ⟨δ n, hδN n hn⟩ = β ⟨n, hn⟩ := by
      rw [← hδW ⟨n, hn⟩, hδW1, MulAut.one_apply]
    have h2 : β (⟨δ n, hδN n hn⟩ * (⟨n, hn⟩ : ↥(commV L))⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      exact mul_inv_cancel _
    exact ((hβk _).mp h2).1
  have hcomm : ∀ x ∈ L, δ * x = x * δ := by
    intro x hx
    have hy : δ * x * δ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hδL x).mp hx
    have h1 : lam ⟨δ * x * δ⁻¹, hy⟩ = lam ⟨x, hx⟩ := by
      refine MulEquiv.ext fun w => ?_
      obtain ⟨n, rfl⟩ := hβs w
      calc lam ⟨δ * x * δ⁻¹, hy⟩ (β n)
          = β ⟨δ (x (δ⁻¹ n)), hδN _ (hLN ⟨x, hx⟩ _ (hδN' n n.2))⟩ := hlamβ _ _
        _ = δW (β ⟨x (δ⁻¹ n), hLN ⟨x, hx⟩ _ (hδN' n n.2)⟩) :=
            (hδW ⟨x (δ⁻¹ n), hLN ⟨x, hx⟩ _ (hδN' n n.2)⟩).symm
        _ = lam ⟨x, hx⟩ (β ⟨δ⁻¹ n, hδN' n n.2⟩) := by
            rw [hδW1, MulAut.one_apply, hlamβ]
        _ = lam ⟨x, hx⟩ (δW⁻¹ (β n)) := by rw [hδWinv]
        _ = lam ⟨x, hx⟩ (β n) := by rw [hδW1, inv_one, MulAut.one_apply]
    have h2 : δ * x * δ⁻¹ = x := congrArg Subtype.val (hlam_bij.1 h1)
    calc δ * x = δ * x * δ⁻¹ * δ := by group
      _ = x * δ := by rw [h2]
  exact ⟨hcomm, fix_commV_of_commute627 hperf hcomm hδfix⟩

end SL32

end CFSG.Quasithin.H13
