module

public import CFSG.RankThree.PartOne.KD4L.TriStd

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KD4T
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

open scoped MatrixGroups

section Torus

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L]

omit hτ in
theorem torusRootChar_neg_of_mem {t : ModGL τ L} (ht : t ∈ torusGroup τ L) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : torusRootChar t (-α) = (torusRootChar t α)⁻¹ := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have key : ∀ β, IsRoot τ β → torusRootChar (rootDiagUnit τ a) β = ((rootChar a β : Lˣ) : L) :=
    fun β hβ => (eq_torusRootChar_of_conj ht hβ
      (fun c => rootDiagUnit_conj_pinnedX a hβ c)).symm
  rw [key _ (IsRoot.neg hα), key _ hα, rootChar_neg', Units.val_inv_eq_inv_val]

omit hτ in
theorem exists_torus_split_of_word {J : Set (Fin τ.rank)} {r : ℕ} (idx : Fin r → Fin τ.rank)
    (hidx : ∀ i ∈ J, ∃ k, idx k = i)
    (hword : ∀ s : Fin r → Lˣ, ∃ T : ModGL τ L, T ∈ subsystemGroup τ L J ∧ T ∈ torusGroup τ L ∧
      ∀ (k : Fin r) (c : L), T * xUnit τ L (idx k) c * T⁻¹ = xUnit τ L (idx k) (s k * c) ∧
        T * yUnit τ L (idx k) c * T⁻¹ = yUnit τ L (idx k) (((s k)⁻¹ : Lˣ) * c))
    {t : ModGL τ L} (ht : t ∈ torusGroup τ L) :
    ∃ t' T : ModGL τ L, t' ∈ torusGroup τ L ∧ T ∈ subsystemGroup τ L J ∧ t = t' * T ∧
      ∀ g ∈ subsystemGroup τ L J, t' * g = g * t' := by
  have hdiag := torusGroup_le_diagonalGroup ht
  set s : Fin r → Lˣ := fun k =>
    Units.mk0 (torusRootChar t (Pi.single (idx k) 1)) (torusRootChar_ne_zero hdiag _) with hs
  obtain ⟨T, hTQ, hTH, hT⟩ := hword s
  refine ⟨t * T⁻¹, T, mul_mem ht (inv_mem hTH), hTQ, by group, ?_⟩
  have hcx : ∀ (k : Fin r) (c : L),
      (t * T⁻¹) * xUnit τ L (idx k) c = xUnit τ L (idx k) c * (t * T⁻¹) := by
    intro k c
    have h1 := (hT k (((s k)⁻¹ : Lˣ) * c)).1
    have e1 : ((s k : Lˣ) : L) * (((s k)⁻¹ : Lˣ) * c) = c := by
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [e1] at h1
    have h2 : T⁻¹ * xUnit τ L (idx k) c * T = xUnit τ L (idx k) (((s k)⁻¹ : Lˣ) * c) := by
      calc T⁻¹ * xUnit τ L (idx k) c * T
          = T⁻¹ * (T * xUnit τ L (idx k) (((s k)⁻¹ : Lˣ) * c) * T⁻¹) * T := by rw [h1]
        _ = _ := by group
    have h3 := conj_pinnedX_of_mem_torusGroup ht (isRoot_single τ (idx k))
      (((s k)⁻¹ : Lˣ) * c)
    rw [pinnedX_single] at h3
    have e3 : torusRootChar t (Pi.single (idx k) 1) * (((s k)⁻¹ : Lˣ) * c) = c := by
      have : torusRootChar t (Pi.single (idx k) 1) = ((s k : Lˣ) : L) := rfl
      rw [this, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [e3] at h3
    calc (t * T⁻¹) * xUnit τ L (idx k) c
        = (t * T⁻¹ * xUnit τ L (idx k) c * (t * T⁻¹)⁻¹) * (t * T⁻¹) := by group
      _ = xUnit τ L (idx k) c * (t * T⁻¹) := by
        have : t * T⁻¹ * xUnit τ L (idx k) c * (t * T⁻¹)⁻¹ = xUnit τ L (idx k) c := by
          calc t * T⁻¹ * xUnit τ L (idx k) c * (t * T⁻¹)⁻¹
              = t * (T⁻¹ * xUnit τ L (idx k) c * T) * t⁻¹ := by group
            _ = t * xUnit τ L (idx k) (((s k)⁻¹ : Lˣ) * c) * t⁻¹ := by rw [h2]
            _ = xUnit τ L (idx k) c := by rw [h3, pinnedX_single]
        rw [this]
  have hcy : ∀ (k : Fin r) (c : L),
      (t * T⁻¹) * yUnit τ L (idx k) c = yUnit τ L (idx k) c * (t * T⁻¹) := by
    intro k c
    have h1 := (hT k (((s k : Lˣ) : L) * c)).2
    have e1 : (((s k)⁻¹ : Lˣ) : L) * (((s k : Lˣ) : L) * c) = c := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [e1] at h1
    have h2 : T⁻¹ * yUnit τ L (idx k) c * T = yUnit τ L (idx k) (((s k : Lˣ) : L) * c) := by
      calc T⁻¹ * yUnit τ L (idx k) c * T
          = T⁻¹ * (T * yUnit τ L (idx k) (((s k : Lˣ) : L) * c) * T⁻¹) * T := by rw [h1]
        _ = _ := by group
    have h3 := conj_pinnedX_of_mem_torusGroup ht (isRoot_neg_single τ (idx k))
      (((s k : Lˣ) : L) * c)
    rw [pinnedX_neg_single, torusRootChar_neg_of_mem ht (isRoot_single τ (idx k))] at h3
    have e3 : (torusRootChar t (Pi.single (idx k) 1))⁻¹ * (((s k : Lˣ) : L) * c) = c := by
      have : torusRootChar t (Pi.single (idx k) 1) = ((s k : Lˣ) : L) := rfl
      rw [this, ← Units.val_inv_eq_inv_val, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
    rw [e3] at h3
    calc (t * T⁻¹) * yUnit τ L (idx k) c
        = (t * T⁻¹ * yUnit τ L (idx k) c * (t * T⁻¹)⁻¹) * (t * T⁻¹) := by group
      _ = yUnit τ L (idx k) c * (t * T⁻¹) := by
        have : t * T⁻¹ * yUnit τ L (idx k) c * (t * T⁻¹)⁻¹ = yUnit τ L (idx k) c := by
          calc t * T⁻¹ * yUnit τ L (idx k) c * (t * T⁻¹)⁻¹
              = t * (T⁻¹ * yUnit τ L (idx k) c * T) * t⁻¹ := by group
            _ = t * yUnit τ L (idx k) (((s k : Lˣ) : L) * c) * t⁻¹ := by rw [h2]
            _ = yUnit τ L (idx k) c := by rw [h3, pinnedX_neg_single]
        rw [this]
  have hle : subsystemGroup τ L J ≤ Subgroup.centralizer ({t * T⁻¹} : Set (ModGL τ L)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ := hidx _ hi
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcx k c).symm
    · obtain ⟨k, rfl⟩ := hidx _ hi
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcy k c).symm
  intro g hg
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  exact this.symm

theorem exists_torus_split [IsAlgClosed L] {t : ModGL τ L} (ht : t ∈ torusGroup τ L) :
    ∃ t' T : ModGL τ L, t' ∈ torusGroup τ L ∧ T ∈ subsystemGroup τ L (d4Set τ) ∧ t = t' * T ∧
      ∀ g ∈ subsystemGroup τ L (d4Set τ), t' * g = g * t' :=
  exists_torus_split_of_word d4Id (fun _ hi => exists_d4Id_eq hi) (fun s => by
    obtain ⟨t₀, hT⟩ := exists_d4TorusWord_scalars (τ := τ) (L := L) s
    exact ⟨d4TorusWord t₀, d4TorusWord_mem_subsystemGroup t₀, d4TorusWord_mem_torusGroup t₀, hT⟩) ht


omit hτ in
theorem torus_sup_eq_mul {J : Set (Fin τ.rank)} {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ subsystemGroup τ L J) :
    ∃ t ∈ torusGroup τ L, ∃ q ∈ subsystemGroup τ L J, y = t * q := by
  have hN : torusGroup τ L ≤
      Subgroup.normalizer (subsystemGroup τ L J : Set (ModGL τ L)) := by
    rw [subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan (fun α hα => hα.1)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy
  obtain ⟨t, ht, q, hq, rfl⟩ := hy
  exact ⟨t, ht, q, hq, rfl⟩

omit hτ in
theorem mem_torusGroup_of_forall_commute {J : Set (Fin τ.rank)} {z : ModGL τ L}
    (hz : z ∈ subsystemGroup τ L J)
    (hc : ∀ g ∈ subsystemGroup τ L J, z * g = g * z) : z ∈ torusGroup τ L := by
  have hcenter : (⟨z, hz⟩ : subsystemGroup τ L J) ∈
      Subgroup.center (subsystemGroup τ L J) :=
    Subgroup.mem_center_iff.2 fun g => (Subtype.ext (hc g g.2)).symm
  have h1 := mem_supportedTorus_of_mem_center hcenter
  rw [← subsystemGroup_inf_torusGroup_eq_supportedTorus] at h1
  exact (Subgroup.mem_inf.1 h1).2

end Torus

section General

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}

omit hτ [IsAlgClosed L] in
theorem commutant_of_split {J : Set (Fin τ.rank)} {U : Subgroup (ModGL τ L)}
    (hUJ : U ≤ subsystemGroup τ L J)
    (hsplit : ∀ t ∈ torusGroup τ L, ∃ t' T : ModGL τ L, t' ∈ torusGroup τ L ∧
      T ∈ subsystemGroup τ L J ∧ t = t' * T ∧ ∀ g ∈ subsystemGroup τ L J, t' * g = g * t')
    (hcc : ∀ q' ∈ subsystemGroup τ L J, (∀ u ∈ U, q' * u = u * q') →
      ∀ g ∈ subsystemGroup τ L J, q' * g = g * q')
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ subsystemGroup τ L J)
    (hc : ∀ u ∈ U, y * u = u * y) :
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (subsystemGroup τ L J : Set (ModGL τ L)) := by
  obtain ⟨t, ht, q, hq, rfl⟩ := torus_sup_eq_mul hy
  obtain ⟨t', T, ht', hT, htT, hcent⟩ := hsplit _ ht
  have hq'Q : T * q ∈ subsystemGroup τ L J := mul_mem hT hq
  have hyeq : t * q = t' * (T * q) := by rw [htT]; group
  have hq'c : ∀ u ∈ U, (T * q) * u = u * (T * q) := by
    intro u hu
    have h1 := hc u hu
    rw [hyeq] at h1
    have h2 := hcent u (hUJ hu)
    calc (T * q) * u = t'⁻¹ * (t' * (T * q) * u) := by group
      _ = t'⁻¹ * (u * (t' * (T * q))) := by rw [h1]
      _ = (t'⁻¹ * u * t') * (T * q) := by group
      _ = u * (T * q) := by
        rw [show t'⁻¹ * u * t' = u from by rw [mul_assoc, ← h2]; group]
  have hcentq := hcc _ hq'Q hq'c
  have hq'T : T * q ∈ torusGroup τ L := mem_torusGroup_of_forall_commute hq'Q hcentq
  rw [hyeq]
  refine ⟨mul_mem ht' hq'T, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  have h1 := hcent g hg
  have h2 := hcentq g hg
  calc g * (t' * (T * q)) = (g * t') * (T * q) := by group
    _ = (t' * g) * (T * q) := by rw [← h1]
    _ = t' * (g * (T * q)) := by group
    _ = t' * ((T * q) * g) := by rw [h2]
    _ = t' * (T * q) * g := by group

theorem commutant_of_facts
    (hcc : ∀ q' ∈ subsystemGroup τ L (d4Set τ), (∀ u ∈ stdLayer ℓ f n₁, q' * u = u * q') →
      ∀ g ∈ subsystemGroup τ L (d4Set τ), q' * g = g * q')
    {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ subsystemGroup τ L (d4Set τ))
    (hc : ∀ u ∈ stdLayer ℓ f n₁, y * u = u * y) :
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) :=
  commutant_of_split inf_le_left (fun _ ht => exists_torus_split ht) hcc hy hc

omit hτ [IsAlgClosed L] in
theorem layer_of_split {J : Set (Fin τ.rank)} {m₀ : Fin τ.rank} (hm₀ : m₀.val = 3)
    {n₁ : ModGL τ L} {U : Subgroup (ModGL τ L)}
    (hU : ∀ g, g ∈ U ↔ g ∈ subsystemGroup τ L J ∧
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g)
    (hsplit : ∀ t ∈ torusGroup τ L, ∃ t' T : ModGL τ L, t' ∈ torusGroup τ L ∧
      T ∈ subsystemGroup τ L J ∧ t = t' * T ∧ ∀ g ∈ subsystemGroup τ L J, t' * g = g * t')
    (hfq : Finite U ∧ CFSG.IsQuasisimple U)
    (hcc : ∀ q' ∈ subsystemGroup τ L J, (∀ u ∈ U, q' * u = u * q') →
      ∀ g ∈ subsystemGroup τ L J, q' * g = g * q')
    (hmid : ∀ (k : Type) [Field k] [Algebra k L], Nat.card k = ℓ ^ f → ∀ Y : SL(2, k),
      simpleRootSL2 τ L m₀ (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∈ U)
    {h n : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ subsystemGroup τ L J, (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (subsystemGroup τ L J : Set (ModGL τ L))) ∧
      ∀ m : Fin τ.rank, m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  have hmem : ∀ g : ModGL τ L, g ∈ P ↔ h * g * h⁻¹ ∈ U := fun g => by
    rw [hP, Subgroup.mem_inf, hU, mem_twistedFixedPoints, hlang g]
    refine and_congr_left fun _ => ⟨fun hg => mul_mem (mul_mem hh hg) (inv_mem hh), fun hg => ?_⟩
    have := mul_mem (mul_mem (inv_mem hh) hg) hh
    simpa [mul_assoc] using this
  let eP : P ≃* U :=
    { toFun := fun g => ⟨h * g * h⁻¹, (hmem g).1 g.2⟩
      invFun := fun u => ⟨h⁻¹ * u * h, (hmem _).2 (by simp [mul_assoc])⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨hfin, hqs⟩ := hfq
  refine ⟨Finite.of_equiv _ eP.symm.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv eP.symm hqs, ?_, ?_⟩
  · intro y hy hc
    have hy' : h * y * h⁻¹ ∈ torusGroup τ L ⊔ subsystemGroup τ L J :=
      mul_mem (mul_mem (Subgroup.mem_sup_right hh) hy) (inv_mem (Subgroup.mem_sup_right hh))
    have hc' : ∀ u ∈ U, (h * y * h⁻¹) * u = u * (h * y * h⁻¹) := by
      intro u hu
      have hu' : h⁻¹ * u * h ∈ P := (hmem _).2 (by simpa [mul_assoc] using hu)
      have h1 := hc _ hu'
      calc h * y * h⁻¹ * u = h * (y * (h⁻¹ * u * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * u * h) * y) * h⁻¹ := by rw [h1]
        _ = u * (h * y * h⁻¹) := by group
    obtain ⟨hT, hC⟩ := commutant_of_split (fun g hg => ((hU g).1 hg).1) hsplit hcc hy' hc'
    have hyh : h * y * h⁻¹ = y := by
      have h6 := Subgroup.mem_centralizer_iff.1 hC h hh
      calc h * y * h⁻¹ = h⁻¹ * (h * (h * y * h⁻¹)) := by group
        _ = h⁻¹ * ((h * y * h⁻¹) * h) := by rw [h6]
        _ = y := by group
    rw [hyh] at hT hC
    exact ⟨hT, hC⟩
  · intro m hm3 k _ _ hk
    refine ⟨h⁻¹, fun Y => (hmem _).2 ?_⟩
    have hm : m = m₀ := Fin.ext (hm3.trans hm₀.symm)
    subst hm
    have := hmid k hk Y
    simpa [mul_assoc] using this

theorem layer_of_facts
    (hfq : Finite (stdLayer ℓ f n₁) ∧ CFSG.IsQuasisimple (stdLayer ℓ f n₁))
    (hcc : ∀ q' ∈ subsystemGroup τ L (d4Set τ), (∀ u ∈ stdLayer ℓ f n₁, q' * u = u * q') →
      ∀ g ∈ subsystemGroup τ L (d4Set τ), q' * g = g * q')
    (hmid : ∀ (k : Type) [Field k] [Algebra k L], Nat.card k = ℓ ^ f → ∀ Y : SL(2, k),
      simpleRootSL2 τ L (d4Id 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∈
        stdLayer ℓ f n₁)
    {h n : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ subsystemGroup τ L (d4Set τ), (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L))) ∧
      ∀ m : Fin τ.rank, m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P :=
  layer_of_split (J := d4Set τ) (m₀ := d4Id 2) rfl (U := stdLayer ℓ f n₁) (fun _ => mem_stdLayer)
    (fun _ ht => exists_torus_split ht) hfq hcc hmid hh hlang hP

theorem StdTwist.commutant (hstd : StdTwist n₁ π e) (hf : 1 ≤ f) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ subsystemGroup τ L (d4Set τ))
    (hc : ∀ u ∈ stdLayer ℓ f n₁, y * u = u * y) :
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) :=
  commutant_of_facts (fun _ hq' hc' => hstd.commute_of_commute hf hq' hc') hy hc

theorem layer_of_standard (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {h n : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ subsystemGroup τ L (d4Set τ), (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L))) ∧
      ∀ m : Fin τ.rank, m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P :=
  layer_of_facts (hstd.finite_quasisimple hf) (fun _ hq' hc' => hstd.commute_of_commute hf hq' hc')
    (fun _ _ _ hk Y => hstd.middle_SL2 hk Y) hh hlang hP

end General

end CFSG.RankThree.PartOne.KD4L
