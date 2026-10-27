module

public import CFSG.RankThree.PartOne.KF4.B2Family
public import CFSG.RankThree.PartOne.KF4.B2SpTwo
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups Pointwise commutatorElement


section Splitting

variable {L : Type} [Field L] [IsAlgClosed L]

@[expose] def f4B2Z (L : Type) [Field L] : Subgroup (ModGL Tag.F4 L) :=
  torusGroup Tag.F4 L ⊓ Subgroup.centralizer
    (subsystemGroup Tag.F4 L f4B2Support : Set (ModGL Tag.F4 L))

theorem rootDiagUnit_mem_f4B2Z (b : Fin Tag.F4.rank → Lˣ) (h1 : b (f4Index 1) = 1)
    (h2 : b (f4Index 2) = 1) : rootDiagUnit Tag.F4 b ∈ f4B2Z L := by
  refine Subgroup.mem_inf.2 ⟨rootDiagUnit_mem_torusGroup b, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro g hg
  have hgen : ∀ i : Fin Tag.F4.rank, i ∈ f4B2Support → ∀ B : SL2 L,
      rootSL2 Tag.F4 L (Pi.single i 1) B * rootDiagUnit Tag.F4 b =
        rootDiagUnit Tag.F4 b * rootSL2 Tag.F4 L (Pi.single i 1) B := by
    intro i hi B
    have h := rootDiagUnit_conj_rootSL2 b (IsRoot.basis i) B
    have hb : b i = 1 := by
      rcases (mem_f4B2Support i).1 hi with rfl | rfl
      exacts [h1, h2]
    rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single, hb] at h
    have h' : rootDiagUnit Tag.F4 b * rootSL2 Tag.F4 L (Pi.single i 1) B *
        (rootDiagUnit Tag.F4 b)⁻¹ = rootSL2 Tag.F4 L (Pi.single i 1) B := by
      rw [h]
      have : diagUnitOne (1 : Lˣ) = 1 := by
        ext a b'
        fin_cases a <;> fin_cases b' <;> simp [diagUnitOne]
      rw [this, conjSL_one]
    exact (mul_inv_eq_iff_eq_mul.1 h').symm
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · have := hgen i hi (uSL c)
      rwa [rootSL2_single_eq_simple, simpleRootSL2_uSL] at this
    · have := hgen i hi (vSL c)
      rwa [rootSL2_single_eq_simple, simpleRootSL2_vSL] at this
  | one => simp
  | mul x y _ _ hx hy =>
    rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    calc x⁻¹ * rootDiagUnit Tag.F4 b = x⁻¹ * (rootDiagUnit Tag.F4 b * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * rootDiagUnit Tag.F4 b) * x⁻¹ := by rw [← hx]
      _ = rootDiagUnit Tag.F4 b * x⁻¹ := by group

theorem torus_eq_f4B2Z_mul {t : ModGL Tag.F4 L} (ht : t ∈ torusGroup Tag.F4 L) :
    ∃ z ∈ f4B2Z L, ∃ τ ∈ subsystemGroup Tag.F4 L f4B2Support, t = z * τ := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨s, t', a, hda, ha1, ha2⟩ := exists_torus2_rootDiag (L := L) (b (f4Index 1))
    (b (f4Index 2))
  refine ⟨rootDiagUnit Tag.F4 (b * a⁻¹), rootDiagUnit_mem_f4B2Z _ ?_ ?_,
    torus2Elt (f4Index 1) (f4Index 2) s t', torus2Elt_mem_f4B2 s t', ?_⟩
  · simp [ha1]
  · simp [ha2]
  · rw [hda, ← rootDiagUnit_mul, inv_mul_cancel_right]

omit [IsAlgClosed L] in
theorem f4B2Z_inf_eq_bot [CharP L 2] :
    f4B2Z L ⊓ subsystemGroup Tag.F4 L f4B2Support = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzZ, hzQ⟩ := Subgroup.mem_inf.1 hz
  rw [Subgroup.mem_bot]
  have hcent := (Subgroup.mem_inf.1 hzZ).2
  have h1 : f4B2Equiv L ⟨z, hzQ⟩ = 1 := by
    apply f4SpGroup_center_eq_one
    intro Y
    obtain ⟨g, rfl⟩ := (f4B2Equiv L).surjective Y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hcent g g.2)
  have h2 : (⟨z, hzQ⟩ : subsystemGroup Tag.F4 L f4B2Support) = 1 :=
    (map_eq_one_iff _ (f4B2Equiv L).injective).1 h1
  exact congrArg Subtype.val h2

end Splitting

section Decomposition

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

omit
  [IsAlgClosed L] [CharP L 2] in
theorem map_entrywise_rootSpan' (σ : L ≃+* L) (S : Set (Fin Tag.F4.rank → ℤ)) :
    (rootSpan Tag.F4 L S).map (Units.map (entrywiseHom σ.toRingHom)) = rootSpan Tag.F4 L S := by
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun α => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => map_entrywise_rootSubgroup σ α

theorem f4B2_decomp {Fr : L →+* L} (hbij : Function.Bijective Fr) (n A : ModGL Tag.F4 L)
    (hnm : n ∈ monomialSubgroup Tag.F4 L) (hA : A ∈ subsystemGroup Tag.F4 L f4B2Support)
    (htw : ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹)
    {y : ModGL Tag.F4 L}
    (hy : y ∈ torusGroup Tag.F4 L ⊔ subsystemGroup Tag.F4 L f4B2Support)
    (hfix : n * Units.map (entrywiseHom Fr) y * n⁻¹ = y) :
    ∃ z ∈ f4B2Z L, ∃ q ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) z * n⁻¹ = z ∧
        n * Units.map (entrywiseHom Fr) q * n⁻¹ = q ∧ y = z * q := by
  classical
  set Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L := Units.map (entrywiseHom Fr) with hΦ
  set Q := subsystemGroup Tag.F4 L f4B2Support with hQ
  have hS : ∀ r ∈ parabolicRoots Tag.F4 f4B2Support, IsRoot Tag.F4 r := fun r hr => hr.1
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij with hσ
  have hσFr : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hQeq : Q = rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) :=
    subsystemGroup_eq_rootSpan _
  have hΦQ : Q.map Φ = Q := by
    rw [hQeq, hΦ, ← hσFr]
    exact map_entrywise_rootSpan' σ _
  have hΦQmem : ∀ g ∈ Q, Φ g ∈ Q := fun g hg => hΦQ ▸ Subgroup.mem_map_of_mem Φ hg
  have hΦQsurj : ∀ q ∈ Q, ∃ g ∈ Q, Φ g = q := fun q hq => by
    rw [← hΦQ] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    exact ⟨g, hg, rfl⟩
  have hθQmem : ∀ g ∈ Q, n * Φ g * n⁻¹ ∈ Q := fun g hg => by
    rw [htw g hg]
    exact mul_mem (mul_mem hA (hΦQmem g hg)) (inv_mem hA)
  have hθQsurj : ∀ q ∈ Q, ∃ g ∈ Q, n * Φ g * n⁻¹ = q := fun q hq => by
    obtain ⟨g, hg, hgq⟩ := hΦQsurj (A⁻¹ * q * A) (mul_mem (mul_mem (inv_mem hA) hq) hA)
    refine ⟨g, hg, ?_⟩
    rw [htw g hg, hgq]
    group
  have hN : torusGroup Tag.F4 L ≤ Subgroup.normalizer (Q : Set (ModGL Tag.F4 L)) := by
    rw [hQeq]
    exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS
  have hy' : y ∈ ((torusGroup Tag.F4 L : Set (ModGL Tag.F4 L)) * (Q : Set (ModGL Tag.F4 L))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN]
    exact hy
  obtain ⟨t, ht, q₀, hq₀, rfl⟩ := hy'
  obtain ⟨z, hz, τ, hτ, rfl⟩ := torus_eq_f4B2Z_mul ht
  set q : ModGL Tag.F4 L := τ * q₀ with hqdef
  have hqQ : q ∈ Q := mul_mem hτ hq₀
  have hyeq : z * τ * q₀ = z * q := by rw [hqdef, mul_assoc]
  beta_reduce at hfix ⊢
  rw [hyeq] at hfix ⊢
  have hzT : z ∈ torusGroup Tag.F4 L := (Subgroup.mem_inf.1 hz).1
  have hθzT : n * Φ z * n⁻¹ ∈ torusGroup Tag.F4 L := by
    have h1 : Φ z ∈ torusGroup Tag.F4 L := by
      rw [hΦ, ← hσFr]
      exact entrywise_mem_torusGroup hzT
    exact (Subgroup.mem_normalizer_iff.1
      (mem_normalizer_torusGroup_of_mem_monomialSubgroup hnm) (Φ z)).1 h1
  have hθzZ : n * Φ z * n⁻¹ ∈ f4B2Z L := by
    refine Subgroup.mem_inf.2 ⟨hθzT, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨g', hg', rfl⟩ := hθQsurj g hg
    have hz' : g' * z = z * g' :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 g' hg'
    calc (n * Φ g' * n⁻¹) * (n * Φ z * n⁻¹) = n * Φ (g' * z) * n⁻¹ := by rw [map_mul]; group
      _ = n * Φ (z * g') * n⁻¹ := by rw [hz']
      _ = (n * Φ z * n⁻¹) * (n * Φ g' * n⁻¹) := by rw [map_mul]; group
  have hθq : n * Φ q * n⁻¹ ∈ Q := hθQmem q hqQ
  have hθ : (n * Φ z * n⁻¹) * (n * Φ q * n⁻¹) = z * q := by
    calc (n * Φ z * n⁻¹) * (n * Φ q * n⁻¹) = n * (Φ z * Φ q) * n⁻¹ := by group
      _ = n * Φ (z * q) * n⁻¹ := by rw [← map_mul]
      _ = z * q := hfix
  have hkey : z⁻¹ * (n * Φ z * n⁻¹) = q * (n * Φ q * n⁻¹)⁻¹ := by
    calc z⁻¹ * (n * Φ z * n⁻¹)
        = z⁻¹ * ((n * Φ z * n⁻¹) * (n * Φ q * n⁻¹)) * (n * Φ q * n⁻¹)⁻¹ := by group
      _ = z⁻¹ * (z * q) * (n * Φ q * n⁻¹)⁻¹ := by rw [hθ]
      _ = q * (n * Φ q * n⁻¹)⁻¹ := by group
  have hbot : z⁻¹ * (n * Φ z * n⁻¹) ∈ f4B2Z L ⊓ Q :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hz) hθzZ, hkey ▸ mul_mem hqQ (inv_mem hθq)⟩
  rw [f4B2Z_inf_eq_bot, Subgroup.mem_bot] at hbot
  refine ⟨z, hz, q, hqQ, (inv_mul_eq_one.1 hbot).symm, ?_, rfl⟩
  rw [hkey] at hbot
  exact (mul_inv_eq_one.1 hbot).symm

end Decomposition

section FamilyEven

variable {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosure k L] [CharP L 2]

omit [Finite k] [IsAlgClosure k L] [CharP L 2] in
theorem commutator_eq_map_commutator {G H : Type*} [Group G] [Group H] (P₀ : Subgroup G)
    (e : H ≃* P₀) :
    ⁅P₀, P₀⁆ = (commutator H).map (P₀.subtype.comp e.toMonoidHom) := by
  rw [commutator_def, Subgroup.map_commutator]
  have h : (⊤ : Subgroup H).map (P₀.subtype.comp e.toMonoidHom) = P₀ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h]

theorem f4B2_family_std_even {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k)
    (hkc : Nat.card k = 2 ∨ 4 ≤ Nat.card k) (n : ModGL Tag.F4 L)
    (hnm : n ∈ monomialSubgroup Tag.F4 L) (w₀ : WeylGroup Tag.F4) (hw₀ : MapsRootLines n w₀)
    (hrot : (w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Beta ∧
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Gamma) ∨
        (w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Beta ∧
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Gamma)) :
    IsSigmaFamily n Fr (parabolicRoots Tag.F4 f4B2Support)
        (fun _ : Unit => ⁅rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr)),
          rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr))⁆) ∧
      (∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
          ∃ z ∈ torusGroup Tag.F4 L ⊓ Subgroup.centralizer
              (rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) : Set (ModGL Tag.F4 L)),
            n * Units.map (entrywiseHom Fr) z * n⁻¹ = z ∧
            ∃ q ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
              twistedFixedPoints n (Units.map (entrywiseHom Fr)), y = z * q) ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL2 k,
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 1)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
          rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have : CharP k 2 := ⟨fun x => by
    rw [← (algebraMap k L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hbij : Function.Bijective Fr := frob_bijective (k := k) Fr hFr Nat.card_pos
  obtain ⟨A, hA, htw⟩ := f4B2_twist Fr n hnm w₀ hw₀ hrot
  set S := parabolicRoots Tag.F4 f4B2Support with hSdef
  have hGeq : subsystemGroup Tag.F4 L f4B2Support = rootSpan Tag.F4 L S :=
    subsystemGroup_eq_rootSpan _
  set Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L := Units.map (entrywiseHom Fr) with hΦ
  set P₀ : Subgroup (ModGL Tag.F4 L) := rootSpan Tag.F4 L S ⊓ twistedFixedPoints n Φ with hP₀
  obtain ⟨hfixeq⟩ := f4B2_fixed_equiv (k := k) hFr n A hA htw
  have hP₀eq : P₀ = subsystemGroup Tag.F4 L f4B2Support ⊓ twistedFixedPoints n Φ := by
    rw [hP₀, hGeq]
  have hPe : f4SpGroup k ≃* ↥P₀ := hfixeq.trans (MulEquiv.subgroupCongr hP₀eq.symm)
  obtain ⟨hdq, hdc⟩ := f4SpGroup_derived (k := k) hkc
  set P : Subgroup (ModGL Tag.F4 L) := ⁅P₀, P₀⁆ with hPdef
  set f : f4SpGroup k →* ModGL Tag.F4 L := P₀.subtype.comp hPe.toMonoidHom with hf
  have hfinj : Function.Injective f := (Subgroup.subtype_injective P₀).comp hPe.injective
  have hPmap : P = (commutator (f4SpGroup k)).map f := commutator_eq_map_commutator P₀ hPe
  have hPle : P ≤ P₀ := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hPe' : ↥(commutator (f4SpGroup k)) ≃* ↥P :=
    ((commutator (f4SpGroup k)).equivMapOfInjective f hfinj).trans
      (MulEquiv.subgroupCongr hPmap.symm)
  have hPfin : Finite P := Finite.of_equiv _ hPe'.toEquiv
  have hPq : CFSG.IsQuasisimple ↥P := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe' hdq
  have hdec : ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S, y ∈ twistedFixedPoints n Φ →
      ∃ z ∈ torusGroup Tag.F4 L ⊓ Subgroup.centralizer (rootSpan Tag.F4 L S : Set (ModGL Tag.F4 L)),
        n * Φ z * n⁻¹ = z ∧ ∃ q ∈ P₀, y = z * q := by
    intro y hy hyfix
    rw [← hGeq] at hy
    obtain ⟨z, hz, q, hq, hzfix, hqfix, rfl⟩ :=
      f4B2_decomp hbij n A hnm hA htw hy (mem_twistedFixedPoints.1 hyfix)
    refine ⟨z, ?_, hzfix, q, ?_, rfl⟩
    · refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1, ?_⟩
      rw [← hGeq]
      exact (Subgroup.mem_inf.1 hz).2
    · exact Subgroup.mem_inf.2 ⟨by rw [← hGeq]; exact hq, mem_twistedFixedPoints.2 hqfix⟩
  have hnorm : ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P, y * u * y⁻¹ ∈ P := by
    intro y hy hyfix u hu
    obtain ⟨z, hz, hzfix, q, hq, rfl⟩ := hdec y hy hyfix
    have hzc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2
    have huQ : u ∈ rootSpan Tag.F4 L S := (Subgroup.mem_inf.1 (hPle hu)).1
    have hqQ : q ∈ rootSpan Tag.F4 L S := (Subgroup.mem_inf.1 hq).1
    have hconj : q * u * q⁻¹ ∈ rootSpan Tag.F4 L S := mul_mem (mul_mem hqQ huQ) (inv_mem hqQ)
    have hcomm : (q * u * q⁻¹) * z = z * (q * u * q⁻¹) := hzc _ hconj
    have h0 : z * q * u * (z * q)⁻¹ = q * u * q⁻¹ := by
      calc z * q * u * (z * q)⁻¹ = z * (q * u * q⁻¹) * z⁻¹ := by group
        _ = q * u * q⁻¹ := by rw [← hcomm]; group
    rw [h0]
    have h1 : q * u * q⁻¹ = ⁅q, u⁆ * u := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact mul_mem (Subgroup.commutator_mem_commutator hq (hPle hu)) hu
  have hcent : ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S, y ∈ twistedFixedPoints n Φ →
      (∀ u ∈ P, y * u = u * y) → y ∈ subtorusSigma n Φ S := by
    intro y hy hyfix hcomm
    obtain ⟨z, hz, hzfix, q, hq, rfl⟩ := hdec y hy hyfix
    have hzc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2
    have hqcomm : ∀ u ∈ P, q * u = u * q := by
      intro u hu
      have h1 := hcomm u hu
      have huQ : u ∈ rootSpan Tag.F4 L S := (Subgroup.mem_inf.1 (hPle hu)).1
      have h2 : u * z = z * u := hzc u huQ
      have h3 : z * (q * u) = z * (u * q) := by
        calc z * (q * u) = z * q * u := by group
          _ = u * (z * q) := h1
          _ = (u * z) * q := by group
          _ = (z * u) * q := by rw [h2]
          _ = z * (u * q) := by group
      exact mul_left_cancel h3
    have hs : hPe.symm ⟨q, hq⟩ = 1 := by
      apply hdc
      intro a ha
      have hfa : f a ∈ P := by
        rw [hPmap]
        exact Subgroup.mem_map_of_mem f ha
      have hfs : f (hPe.symm ⟨q, hq⟩) = q := by simp [hf]
      apply hfinj
      rw [map_mul, map_mul, hfs]
      exact hqcomm (f a) hfa
    have hq1 : q = 1 := by
      have h := congrArg hPe hs
      rw [MulEquiv.apply_symm_apply, map_one] at h
      exact congrArg Subtype.val h
    rw [hq1, mul_one]
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨(Subgroup.mem_inf.1 hz).1, hzfix⟩,
      (Subgroup.mem_inf.1 hz).2⟩
  refine ⟨⟨fun _ => hPfin, fun _ => hPq, fun _ => hPle.trans inf_le_left,
    fun _ => hPle.trans inf_le_right,
    fun _ => hPle.trans (inf_le_left.trans (rootSpan_le_adjointGroup L S)),
    fun _ y hy hyR u hu => hnorm y hy hyR u hu,
    fun y hy hyR hc => hcent y hy hyR (fun u hu => hc () u hu)⟩, hdec, ?_⟩
  obtain ⟨h₀, hh₀G, h⟩ := f4B2_sl2_mem (k := k) hFr n A hA htw
  refine ⟨h₀, ?_, fun Y => ?_⟩
  · rw [hGeq] at hh₀G
    exact rootSpan_le_adjointGroup L _ hh₀G
  · rw [hP₀eq]
    exact h Y

theorem f4B2_family_even {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k)
    (hkc : Nat.card k = 2 ∨ 4 ≤ Nat.card k) (n : ModGL Tag.F4 L)
    (hnm : n ∈ monomialSubgroup Tag.F4 L) (w₀ : WeylGroup Tag.F4) (hw₀ : MapsRootLines n w₀)
    (v : WeylGroup Tag.F4)
    (hrot : (w₀ • (v • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ)) = v • f4B2Beta ∧
          w₀ • (v • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ)) = -(v • f4B2Gamma)) ∨
        (w₀ • (v • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ)) = -(v • f4B2Beta) ∧
          w₀ • (v • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ)) = v • f4B2Gamma)) :
    IsSigmaFamily n Fr ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support)
        (fun _ : Unit =>
          ⁅rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr)),
          rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr))⁆) ∧
      (∀ y ∈ torusGroup Tag.F4 L ⊔
          rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
          ∃ z ∈ torusGroup Tag.F4 L ⊓ Subgroup.centralizer
              (rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) :
                Set (ModGL Tag.F4 L)),
            n * Units.map (entrywiseHom Fr) z * n⁻¹ = z ∧
            ∃ q ∈ rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
              twistedFixedPoints n (Units.map (entrywiseHom Fr)), y = z * q) ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL2 k,
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 1)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
          rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
            twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have hFrbij : Function.Bijective Fr := frob_bijective (k := k) Fr hFr Nat.card_pos
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
  obtain ⟨hfam', hdec', h₀', hh₀'C, hh₀'⟩ :=
    f4B2_family_std_even (k := k) hFr hkc n' hn'm (v⁻¹ * w₀ * v) hn'maps hrot'
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
  have hVN : V ∈ Subgroup.normalizer (torusGroup Tag.F4 L : Set (ModGL Tag.F4 L)) :=
    canonicalRep_mem_normalizer v
  have hcH : ∀ x, c x ∈ torusGroup Tag.F4 L ↔ x ∈ torusGroup Tag.F4 L := fun x => by
    rw [hcapp]
    exact (Subgroup.mem_normalizer_iff.1 hVN x).symm
  have hHmap : (torusGroup Tag.F4 L).map c = torusGroup Tag.F4 L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hcH x).2 hx
    · intro hy
      have hmem : V⁻¹ * y * V ∈ torusGroup Tag.F4 L := by
        refine (hcH _).1 ?_
        rw [hcapp]
        have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      refine ⟨V⁻¹ * y * V, hmem, ?_⟩
      rw [hcapp]
      group
  have hQmap : (rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support)).map c =
      rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) :=
    map_conj_rootSpan v hS
  have hsup : (torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support)).map c =
      torusGroup Tag.F4 L ⊔
        rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) := by
    rw [Subgroup.map_sup, hHmap, hQmap]
  have hRiff : ∀ x, x ∈ twistedFixedPoints n' Φ ↔ c x ∈ twistedFixedPoints n Φ :=
    fun x => by rw [hcapp]; exact mem_twistedFixedPoints_conj hΦV
  have hRmap : (twistedFixedPoints n' Φ).map c = twistedFixedPoints n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hRiff x).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, ?_, ?_⟩
      · refine (hRiff _).2 ?_
        rw [hcapp]
        have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  have hP₀map : (rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
      twistedFixedPoints n' Φ).map c =
      rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
        twistedFixedPoints n Φ := by
    rw [Subgroup.map_inf_eq _ _ c hcinj, hQmap, hRmap]
  have hPmap : (⁅rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
      twistedFixedPoints n' Φ, rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support) ⊓
      twistedFixedPoints n' Φ⁆).map c =
      ⁅rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support) ⊓
        twistedFixedPoints n Φ, rootSpan Tag.F4 L ((fun γ => v • γ) '' parabolicRoots Tag.F4
          f4B2Support) ⊓ twistedFixedPoints n Φ⁆ := by
    rw [Subgroup.map_commutator, hP₀map]
  refine ⟨hPmap ▸ hfam, ?_, V * h₀', mul_mem (canonicalRep_mem_adjointGroup _ L v) hh₀'C,
    fun Y => ?_⟩
  · intro y hy hyfix
    have hy' : y ∈ (torusGroup Tag.F4 L ⊔
        rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4B2Support)).map c := by
      rw [hsup]
      exact hy
    obtain ⟨y', hy'', rfl⟩ := hy'
    obtain ⟨z', hz', hz'fix, q', hq', rfl⟩ := hdec' y' hy'' ((hRiff y').2 hyfix)
    refine ⟨c z', Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_, c q', ?_, map_mul c z' q'⟩
    · exact (hcH z').2 (Subgroup.mem_inf.1 hz').1
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rw [← hQmap] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz').2 g' hg'
      rw [← map_mul, ← map_mul, h1]
    · exact (mem_twistedFixedPoints).1 ((hRiff z').1 (mem_twistedFixedPoints.2 hz'fix))
    · rw [← hP₀map]
      exact Subgroup.mem_map_of_mem c hq'
  · have h := Subgroup.mem_map_of_mem c (hh₀' Y)
    rw [hP₀map, hcapp] at h
    have e : V * (h₀' * simpleRootSL2 Tag.F4 L (f4Index 1)
        (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀'⁻¹) * V⁻¹ =
        V * h₀' * simpleRootSL2 Tag.F4 L (f4Index 1)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * (V * h₀')⁻¹ := by group
    rw [← e]
    exact h

end FamilyEven

end CFSG.RankThree.PartOne.KF4
