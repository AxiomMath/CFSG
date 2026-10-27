module

public import CFSG.RankThree.PartOne.KF4.B2Lang
public import CFSG.RankThree.PartOne.KE.SigmaTransport

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE


section Centralizer

variable {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosure k L]

theorem conj_aux (Dm Dm' Mq Mqi Mg : Matrix (Fin 4) (Fin 4) L) (h1 : Dm' * Dm = 1)
    (h2 : Mqi * Mq = 1) (h : Mg = Dm * (Mq * Mg * Mqi) * Dm') :
    Mg * (Dm * Mq) = (Dm * Mq) * Mg := by
  calc Mg * (Dm * Mq) = (Dm * (Mq * Mg * Mqi) * Dm') * (Dm * Mq) := by rw [← h]
    _ = Dm * (Mq * Mg * (Mqi * ((Dm' * Dm) * Mq))) := by simp only [Matrix.mul_assoc]
    _ = Dm * (Mq * Mg * (Mqi * Mq)) := by rw [h1, Matrix.one_mul]
    _ = (Dm * Mq) * Mg := by rw [h2, Matrix.mul_one, ← Matrix.mul_assoc]

theorem f4B2_centralizes {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k) (n A : ModGL Tag.F4 L)
    (hA : A ∈ subsystemGroup Tag.F4 L f4B2Support)
    (htw : ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹)
    (b : Fin Tag.F4.rank → Lˣ) {q : ModGL Tag.F4 L} (hq : q ∈ subsystemGroup Tag.F4 L f4B2Support)
    (hcomm : ∀ g : subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) * n⁻¹ = g →
        rootDiagUnit Tag.F4 b * q * g = g * (rootDiagUnit Tag.F4 b * q)) :
    q ∈ torusGroup Tag.F4 L ∧ ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      rootDiagUnit Tag.F4 b * q * g = g * (rootDiagUnit Tag.F4 b * q) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  set d : ModGL Tag.F4 L := rootDiagUnit Tag.F4 b with hd
  have hS : ∀ r ∈ parabolicRoots Tag.F4 f4B2Support, IsRoot Tag.F4 r := fun r hr => hr.1
  have hdN : ∀ h ∈ subsystemGroup Tag.F4 L f4B2Support,
      d * h * d⁻¹ ∈ subsystemGroup Tag.F4 L f4B2Support := by
    intro h hh
    rw [subsystemGroup_eq_rootSpan] at hh ⊢
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS
        (rootDiagUnit_mem_torusGroup b)) h).1 hh
  set qq : subsystemGroup Tag.F4 L f4B2Support := ⟨q, hq⟩ with hqq
  set Dm : Matrix (Fin 4) (Fin 4) L := Matrix.diagonal (fun j => ((f4B2Chars b j : Lˣ) : L))
    with hDm
  set Dm' : Matrix (Fin 4) (Fin 4) L :=
    Matrix.diagonal (fun j => (((f4B2Chars b j)⁻¹ : Lˣ) : L)) with hDm'
  have hDD : Dm * Dm' = 1 := by
    rw [hDm, hDm', Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hDD' : Dm' * Dm = 1 := by
    rw [hDm, hDm', Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  set Mq : Matrix (Fin 4) (Fin 4) L := ((f4B2Equiv L qq : f4SpGroup L) : GL (Fin 4) L).val
    with hMq
  set Mqi : Matrix (Fin 4) (Fin 4) L :=
    (((f4B2Equiv L qq : f4SpGroup L) : GL (Fin 4) L)⁻¹).val with hMqi
  have hqq1 : Mq * Mqi = 1 := Units.mul_inv _
  have hqq2 : Mqi * Mq = 1 := Units.inv_mul _
  have hMatq : f4B2_data.Mat q = Mq := rfl
  have hconj : ∀ g : subsystemGroup Tag.F4 L f4B2Support,
      f4B2_data.Mat (d * (q * (g : ModGL Tag.F4 L) * q⁻¹) * d⁻¹) =
        Dm * (Mq * ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val * Mqi) * Dm' := by
    intro g
    have hg' : q * (g : ModGL Tag.F4 L) * q⁻¹ ∈ subsystemGroup Tag.F4 L f4B2Support :=
      mul_mem (mul_mem hq g.2) (inv_mem hq)
    rw [f4B2_Mat_conj_rootDiagUnit b hg']
    congr 2
    have := congrArg (fun x : subsystemGroup Tag.F4 L f4B2Support =>
      ((f4B2Equiv L x : f4SpGroup L) : GL (Fin 4) L).val) (show qq * g * qq⁻¹ =
        ⟨q * (g : ModGL Tag.F4 L) * q⁻¹, hg'⟩ from rfl)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at this
    exact this.symm
  have hfixed : ∀ g : subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) * n⁻¹ = g →
        Dm * Mq * ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val =
          ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val * (Dm * Mq) := by
    intro g hg
    have h1 := hcomm g hg
    have h2 : d * (q * (g : ModGL Tag.F4 L) * q⁻¹) * d⁻¹ = g := by
      have : d * (q * (g : ModGL Tag.F4 L) * q⁻¹) * d⁻¹ = d * q * g * (d * q)⁻¹ := by group
      rw [this]
      exact mul_inv_eq_iff_eq_mul.2 h1
    have h3 := hconj g
    rw [h2] at h3
    exact (conj_aux Dm Dm' Mq Mqi _ hDD' hqq2 (by
      have : f4B2_data.Mat (g : ModGL Tag.F4 L) =
          ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val := rfl
      rw [← this]
      exact h3)).symm
  obtain ⟨c, hc⟩ := f4B2_commutant (k := k) hFr n A hA htw (Dm * Mq) hfixed
  have hMq' : Mq = Dm' * (c • (1 : Matrix (Fin 4) (Fin 4) L)) := by
    rw [← hc, ← Matrix.mul_assoc, hDD', Matrix.one_mul]
  have hqT : q ∈ torusGroup Tag.F4 L := by
    refine mem_torusGroup_of_diag hq (fun i j hij => ?_)
    rw [hMatq, hMq', hDm', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
      Matrix.diagonal_apply_ne _ hij, smul_zero]
  refine ⟨hqT, fun g hg => ?_⟩
  have hMi : (Dm * Mq) * (Mqi * Dm') = 1 := by
    calc (Dm * Mq) * (Mqi * Dm') = Dm * (Mq * Mqi) * Dm' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hqq1, Matrix.mul_one, hDD]
  set g' : subsystemGroup Tag.F4 L f4B2Support := ⟨g, hg⟩ with hg'
  have hmat : f4B2_data.Mat (d * (q * g * q⁻¹) * d⁻¹) = f4B2_data.Mat g := by
    have h3 := hconj g'
    rw [h3]
    have hc' : (Dm * Mq) * ((f4B2Equiv L g' : f4SpGroup L) : GL (Fin 4) L).val =
        ((f4B2Equiv L g' : f4SpGroup L) : GL (Fin 4) L).val * (Dm * Mq) := by
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    calc Dm * (Mq * ((f4B2Equiv L g' : f4SpGroup L) : GL (Fin 4) L).val * Mqi) * Dm'
        = (Dm * Mq) * ((f4B2Equiv L g' : f4SpGroup L) : GL (Fin 4) L).val * (Mqi * Dm') := by
          simp only [Matrix.mul_assoc]
      _ = ((f4B2Equiv L g' : f4SpGroup L) : GL (Fin 4) L).val := by
          rw [hc', Matrix.mul_assoc, hMi, Matrix.mul_one]
      _ = f4B2_data.Mat g := rfl
  have hmem : d * (q * g * q⁻¹) * d⁻¹ ∈ subsystemGroup Tag.F4 L f4B2Support :=
    hdN _ (mul_mem (mul_mem hq hg) (inv_mem hq))
  have heq : (⟨d * (q * g * q⁻¹) * d⁻¹, hmem⟩ : subsystemGroup Tag.F4 L f4B2Support) = g' :=
    (f4B2Equiv L).injective (Subtype.ext (Units.ext hmat))
  have h4 : d * (q * g * q⁻¹) * d⁻¹ = g := congrArg Subtype.val heq
  have h5 : d * q * g * (d * q)⁻¹ = g := by
    have : d * (q * g * q⁻¹) * d⁻¹ = d * q * g * (d * q)⁻¹ := by group
    rw [← this]
    exact h4
  exact mul_inv_eq_iff_eq_mul.1 h5

end Centralizer

section Family

variable {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosure k L]

theorem f4B2_family_std {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k)
    (hk : 4 ≤ Nat.card k ∨ Nat.card k = 3) (n : ModGL Tag.F4 L)
    (hnm : n ∈ monomialSubgroup Tag.F4 L) (w₀ : WeylGroup Tag.F4) (hw₀ : MapsRootLines n w₀)
    (hrot : (w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Beta ∧
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Gamma) ∨
        (w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Beta ∧
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Gamma)) :
    IsSigmaFamily n Fr (parabolicRoots Tag.F4 f4B2Support)
        (fun _ : Unit => rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL2 k,
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 1)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
          rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  obtain ⟨A, hA, htw⟩ := f4B2_twist Fr n hnm w₀ hw₀ hrot
  have hGeq : subsystemGroup Tag.F4 L f4B2Support =
      rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) := subsystemGroup_eq_rootSpan _
  set S := parabolicRoots Tag.F4 f4B2Support with hSdef
  have hS : ∀ r ∈ S, IsRoot Tag.F4 r := fun r hr => hr.1
  obtain ⟨hfixeq⟩ := f4B2_fixed_equiv (k := k) hFr n A hA htw
  have hP₀eq : rootSpan Tag.F4 L S ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) =
      subsystemGroup Tag.F4 L f4B2Support ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
    rw [hGeq]
  have hPe : f4SpGroup k ≃* ↥(rootSpan Tag.F4 L S ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr))) :=
    hfixeq.trans (MulEquiv.subgroupCongr hP₀eq.symm)
  refine ⟨?_, ?_⟩
  · refine ⟨fun _ => Finite.of_equiv _ hPe.toEquiv, fun _ =>
      CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe (f4SpGroup_isQuasisimple k hk),
      fun _ => inf_le_left, fun _ => inf_le_right,
      fun _ => inf_le_left.trans (rootSpan_le_adjointGroup L S), fun _ y hy hyR u hu => ?_,
      fun y hy hyR hcomm => ?_⟩
    · have hN : torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S ≤
          Subgroup.normalizer (rootSpan Tag.F4 L S : Set (ModGL Tag.F4 L)) :=
        sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)
          Subgroup.le_normalizer
      have hu' := Subgroup.mem_inf.1 hu
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hN hy) u).1 hu'.1,
        mul_mem (mul_mem hyR hu'.2) (inv_mem hyR)⟩
    · have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup Tag.F4 L)
        (rootSpan Tag.F4 L S) (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)
      have hy' : y ∈ ((torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S : Subgroup (ModGL Tag.F4 L)) :
          Set (ModGL Tag.F4 L)) := hy
      rw [e] at hy'
      obtain ⟨t, ht, q, hq, rfl⟩ := hy'
      obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      have hqG : q ∈ subsystemGroup Tag.F4 L f4B2Support := by
        rw [hGeq]
        exact hq
      obtain ⟨hqT, hcent⟩ := f4B2_centralizes (k := k) hFr n A hA htw b hqG (fun g hg => by
        have hgP : (g : ModGL Tag.F4 L) ∈ rootSpan Tag.F4 L S ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr)) :=
          Subgroup.mem_inf.2 ⟨by rw [← hGeq]; exact g.2, mem_twistedFixedPoints.2 hg⟩
        exact hcomm () g hgP)
      refine ⟨mem_twistedTorusOf.2 ⟨mul_mem ht hqT, mem_twistedFixedPoints.1 hyR⟩,
        Subgroup.mem_centralizer_iff.2 (fun g hg => ?_)⟩
      have hgG : g ∈ subsystemGroup Tag.F4 L f4B2Support := by
        rw [hGeq]
        exact hg
      exact (hcent g hgG).symm
  · obtain ⟨h₀, hh₀G, h⟩ := f4B2_sl2_mem (k := k) hFr n A hA htw
    refine ⟨h₀, ?_, fun Y => ?_⟩
    · rw [hGeq] at hh₀G
      exact rootSpan_le_adjointGroup L _ hh₀G
    · rw [← hGeq]
      exact h Y

omit [Finite k] [IsAlgClosure k L] in
omit
  [Field k] [Algebra k L] in
theorem frob_bijective (Fr : L →+* L) [IsAlgClosed L] (hFr : ∀ c, Fr c = c ^ Nat.card k)
    (hq : 0 < Nat.card k) : Function.Bijective Fr :=
  ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩⟩

theorem f4B2_family {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k)
    (hk : 4 ≤ Nat.card k ∨ Nat.card k = 3) (n : ModGL Tag.F4 L)
    (hnm : n ∈ monomialSubgroup Tag.F4 L) (w₀ : WeylGroup Tag.F4) (hw₀ : MapsRootLines n w₀)
    (v : WeylGroup Tag.F4)
    (hrot : (w₀ • (v • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ)) = v • f4B2Beta ∧
          w₀ • (v • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ)) = -(v • f4B2Gamma)) ∨
        (w₀ • (v • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ)) = -(v • f4B2Beta) ∧
          w₀ • (v • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ)) = v • f4B2Gamma)) :
    ∃ P : Unit → Subgroup (ModGL Tag.F4 L),
      IsSigmaFamily n Fr ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) P ∧
        P () = rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
        ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL2 k,
          h₀ * simpleRootSL2 Tag.F4 L (f4Index 1)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P () := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hFrbij : Function.Bijective Fr := frob_bijective (k := k) Fr hFr hq0
  set V : ModGL Tag.F4 L := canonicalRep (coxeterSystem Tag.F4) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.F4 L := canonicalRep_mem_monomialSubgroup L v
  have hVmaps : MapsRootLines V v := mapsRootLines_canonicalRep v
  set n' : ModGL Tag.F4 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.F4 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hn'maps : MapsRootLines n' (v⁻¹ * w₀ * v) := (hVmaps.inv.mul hw₀).mul hVmaps
  have hrot' : ((v⁻¹ * w₀ * v) • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Beta ∧
      (v⁻¹ * w₀ * v) • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Gamma) ∨
      ((v⁻¹ * w₀ * v) • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Beta ∧
      (v⁻¹ * w₀ * v) • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Gamma) := by
    rcases hrot with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [mul_smul, mul_smul, mul_smul, mul_smul, h1, h2, inv_smul_smul, weyl_smul_neg,
        inv_smul_smul]
      exact ⟨rfl, rfl⟩
    · right
      rw [mul_smul, mul_smul, mul_smul, mul_smul, h1, h2, weyl_smul_neg, inv_smul_smul,
        inv_smul_smul]
      exact ⟨rfl, rfl⟩
  obtain ⟨hfam', h₀', hh₀'C, hh₀'⟩ := f4B2_family_std (k := k) hFr hk n' hn'm (v⁻¹ * w₀ * v)
    hn'maps hrot'
  have hS : ∀ r ∈ parabolicRoots Tag.F4 f4B2Support, IsRoot Tag.F4 r := fun r hr => hr.1
  have hfam := isSigmaFamily_transport Fr hFrbij v n hS hfam'
  set Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L := Units.map (entrywiseHom Fr) with hΦ
  set c : ModGL Tag.F4 L →* ModGL Tag.F4 L := (MulAut.conj V).toMonoidHom with hc
  have hcapp : ∀ x, c x = V * x * V⁻¹ := fun x => by simp [hc, MulAut.conj_apply]
  have hcinj : Function.Injective c := (MulAut.conj V).injective
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hQmap : (rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support)).map c =
      rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) :=
    map_conj_rootSpan v hS
  have hRmap : (twistedFixedPoints n' Φ).map c = twistedFixedPoints n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        exact (mem_twistedFixedPoints_conj hΦV (n := n) (x := V⁻¹ * y * V)).2 (by rw [e]; exact hy)
      · rw [hcapp]
        group
  refine ⟨fun _ => (rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
    twistedFixedPoints n' Φ).map c, hfam, ?_, V * h₀',
    mul_mem (canonicalRep_mem_adjointGroup _ L v) hh₀'C, fun Y => ?_⟩
  · show Subgroup.map c (rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
      twistedFixedPoints n' Φ) = _
    rw [Subgroup.map_inf_eq _ _ c hcinj, hQmap, hRmap]
  · have h := Subgroup.mem_map_of_mem c (hh₀' Y)
    rw [hcapp] at h
    have e : V * (h₀' * simpleRootSL2 Tag.F4 L (f4Index 1)
        (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀'⁻¹) * V⁻¹ =
        V * h₀' * simpleRootSL2 Tag.F4 L (f4Index 1)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * (V * h₀')⁻¹ := by group
    rw [← e]
    exact h

end Family


end CFSG.RankThree.PartOne.KF4
