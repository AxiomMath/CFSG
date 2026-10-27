module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ConnectedJoint
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FamilyPosition

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.RankThree.PartOne.KE

open CFSG.StandardType.F4ExplicitPos.FamilyPosition CFSG.StandardType.F4ExplicitPos.ConnectedJoint

open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.LangPosition

theorem f4_exists_inv_mul_entrywise_frobenius
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (e : ℕ) (he : 1 ≤ e) {y : ModGL Tag.F4 Ω} (hy : y ∈ adjointGroup Tag.F4 Ω) :
    ∃ z ∈ adjointGroup Tag.F4 Ω,
      z⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 e z = y := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set (Fin Tag.F4.rank → ℤ) := {α | IsRoot Tag.F4 α}
  have hT : torusGroup Tag.F4 Ω ≤ adjointGroup Tag.F4 Ω := by
    apply (Subgroup.closure_le (adjointGroup Tag.F4 Ω)).2
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact torusElt_mem_adjointGroup i u
  have hC : torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω S = adjointGroup Tag.F4 Ω := by
    rw [show rootSpan Tag.F4 Ω S = adjointGroup Tag.F4 Ω from adjointGroup_eq_rootSpan.symm]
    exact sup_eq_right.mpr hT
  have hstable : ∀ g ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω S,
      frobTwistGL Tag.F4 Ω 2 e 1 g ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω S := by
    intro g hg
    rw [hC] at hg ⊢
    simpa [frobTwistGL_apply] using entrywiseFrobGL_mem_adjointGroup_no117 2 e hg
  obtain ⟨z, hz, hzy⟩ := exists_frobTwist_eq_mul_torus_sup_rootSpan_no117
    (τ := Tag.F4) 2 S e he 1 hstable y (by rwa [hC])
  refine ⟨z, by rwa [hC] at hz, ?_⟩
  have h : entrywiseFrobGL Tag.F4 Ω 2 e z = z * y := by
    simpa [frobTwistGL_apply] using hzy
  rw [h, inv_mul_cancel_left]

theorem rootChar_pow_no117 {τ : Tag} {L : Type} [Field L] (b : Fin τ.rank → Lˣ) (n : ℕ)
    (v : Fin τ.rank → ℤ) : rootChar (b ^ n) v = rootChar b v ^ n := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem rootChar_pow_eq_one_no117 {τ : Tag} {L : Type} [Field L] {p : ℕ}
    (b : Fin τ.rank → Lˣ) (hb : ∀ i, b i ^ p = 1) (v : Fin τ.rank → ℤ) :
    rootChar b v ^ p = 1 := by
  rw [← rootChar_pow_no117]
  have : b ^ p = 1 := funext hb
  rw [this]
  simp [rootChar]

theorem entrywiseFrobGL_rootDiagUnit_eq_pow_no117 {τ : Tag} {L : Type} [Field L] (ℓ : ℕ)
    [Fact ℓ.Prime] [CharP L ℓ] (e : ℕ) (b : Fin τ.rank → Lˣ) :
    entrywiseFrobGL τ L ℓ e (rootDiagUnit τ b) = rootDiagUnit τ (b ^ ℓ ^ e) := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_map]
  exact congrArg (rootDiagUnit τ) (by
    funext i
    exact Units.ext (iterateFrobenius_def ℓ e (↑(b i) : L)))

theorem rootDiagUnit_eq_conj_frob_no117 {τ : Tag} {L : Type} [Field L] (ℓ : ℕ)
    [Fact ℓ.Prime] [CharP L ℓ]
    {e : ℕ} {b : Fin τ.rank → Lˣ} {w : WeylGroup τ}
    (hw : ∀ v, rootChar b (w • v) = rootChar b v ^ ℓ ^ e) :
    rootDiagUnit τ b = canonicalRep (coxeterSystem τ) L w *
      entrywiseFrobGL τ L ℓ e (rootDiagUnit τ b) *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_pow_no117, rootDiagUnit_eq_conj_canonicalRep_iff]
  intro v
  rw [hw, rootChar_pow_no117]

theorem image_familyKernel_of_pow_no117 {τ : Tag} {L : Type} [Field L] {ι : Type} {e p : ℕ}
    (hpq : Nat.Coprime p (e)) (a : ι → Fin τ.rank → Lˣ)
    (hexp : ∀ s i, a s i ^ p = 1) {w : WeylGroup τ}
    (hw : ∀ s v, rootChar (a s) (w • v) = rootChar (a s) v ^ e) :
    (fun α => w • α) '' familyKernel a = familyKernel a := by
  have key : ∀ x : Lˣ, x ^ p = 1 → x ^ e = 1 → x = 1 := fun x h1 h2 => by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hpq] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hχ⟩, rfl⟩
    refine ⟨IsRoot.smul hα w, fun s => ?_⟩
    rw [hw, hχ s, one_pow]
  · rintro ⟨hβ, hχ⟩
    refine ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, fun s => ?_⟩, smul_inv_smul w β⟩
    have h := hw s (w⁻¹ • β)
    rw [smul_inv_smul, hχ s] at h
    exact key _ (rootChar_pow_eq_one_no117 (a s) (hexp s) _) h.symm

theorem entrywiseFrobGL_mem_familyGroup_no117 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (e : ℕ) {g : ModGL τ L}
    (hg : g ∈ familyGroup (K := L) a) :
    entrywiseFrobGL τ L ℓ e g ∈ familyGroup (K := L) a := by
  have hmap : (familyGroup (K := L) a).map (entrywiseFrobGL τ L ℓ e) ≤ familyGroup a := by
    rw [familyGroup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [entrywiseFrobGL_rootDiagUnit_eq_map]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [rootSpan, Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hα => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun β (_ : β ∈ familyKernel a) =>
        rootSubgroup τ L β) α hα le_rfl (Subgroup.subset_closure
          ⟨iterateFrobenius L ℓ e c, (entrywiseFrobGL_pinnedX_no117 ℓ e α c).symm⟩))
  exact hmap ⟨g, hg, rfl⟩

theorem f4_exists_lang_datum_of_plane
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {ι : Type} (f : ℕ) (hf : 1 ≤ f) {p : ℕ} (hpq : Nat.Coprime p (2 ^ f))
    (a : ι → Fin Tag.F4.rank → Ωˣ) (hexp : ∀ s i, a s i ^ p = 1)
    {g : ModGL Tag.F4 Ω} (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hn : ∀ s, (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) *
      entrywiseFrobGL Tag.F4 Ω 2 f (rootDiagUnit Tag.F4 (a s)) *
      (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g)⁻¹ = rootDiagUnit Tag.F4 (a s)) :
    ∃ (w' : WeylGroup Tag.F4) (z : ModGL Tag.F4 Ω), z ∈ familyGroup (K := Ω) a ∧
      (g * z)⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f (g * z) =
        canonicalRep (coxeterSystem Tag.F4) Ω w' := by
  have hnG0 : g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g ∈ adjointGroup Tag.F4 Ω :=
    mul_mem (inv_mem hg) (entrywiseFrobGL_mem_adjointGroup_no117 2 f hg)
  obtain ⟨w, hwconj⟩ := f4_exists_weyl_of_conj_family (a := a) (b := fun s => a s ^ 2 ^ f)
    hnG0 (fun s => by rw [← entrywiseFrobGL_rootDiagUnit_eq_pow_no117]; exact hn s)
  have hw : ∀ s v, rootChar (a s) (w • v) = rootChar (a s) v ^ 2 ^ f := by
    intro s v
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (K := Ω) (a s) (a s ^ 2 ^ f) w).1
      (hwconj s) v
    rw [this, rootChar_pow_no117]
  set nw := canonicalRep (coxeterSystem Tag.F4) Ω w with hnwdef
  have hnwG : nw ∈ adjointGroup Tag.F4 Ω :=
    canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) Ω w
  have hc : (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) * nw⁻¹ ∈
      familyCentralizer Tag.F4 Ω a := by
    refine mem_familyCentralizer.2 ⟨mul_mem hnG0 (inv_mem hnwG), fun s => ?_⟩
    have h1 := rootDiagUnit_eq_conj_frob_no117 (τ := Tag.F4) (L := Ω) 2 (hw s)
    rw [← hnwdef] at h1
    have h2 : nw⁻¹ * rootDiagUnit Tag.F4 (a s) * nw =
        entrywiseFrobGL Tag.F4 Ω 2 f (rootDiagUnit Tag.F4 (a s)) := by
      calc nw⁻¹ * rootDiagUnit Tag.F4 (a s) * nw
          = nw⁻¹ * (nw * entrywiseFrobGL Tag.F4 Ω 2 f (rootDiagUnit Tag.F4 (a s)) *
              nw⁻¹) * nw := by rw [← h1]
        _ = entrywiseFrobGL Tag.F4 Ω 2 f (rootDiagUnit Tag.F4 (a s)) := by group
    have h3 : ((g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) * nw⁻¹) *
        rootDiagUnit Tag.F4 (a s) *
        ((g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) * nw⁻¹)⁻¹ = rootDiagUnit Tag.F4 (a s) := by
      calc ((g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) * nw⁻¹) * rootDiagUnit Tag.F4 (a s) *
            ((g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) * nw⁻¹)⁻¹
          = (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) *
              (nw⁻¹ * rootDiagUnit Tag.F4 (a s) * nw) *
              (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g)⁻¹ := by group
        _ = rootDiagUnit Tag.F4 (a s) := by rw [h2]; exact hn s
    rw [mul_inv_eq_iff_eq_mul]
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  obtain ⟨w₁, hw₁, m, hm, hcm⟩ := f4_familyCentralizer_le_mul (a := a) hc
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := Ω) w₁ w
  have hkM : k ∈ familyGroup (K := Ω) a := Subgroup.mem_sup_left hk
  have hn' : g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g = (m * k) *
      canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w) := by
    have h1 : g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g =
        (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) * nw⁻¹ * nw := by group
    rw [h1, hcm, hnwdef, mul_assoc m, hkk]
    group
  have himg := image_familyKernel_of_pow_no117 (τ := Tag.F4) (L := Ω) (e := 2 ^ f)
    hpq a hexp hw
  have hQ : canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w) ∈
      Subgroup.normalizer (familyGroup (K := Ω) a : Set (ModGL Tag.F4 Ω)) := by
    have h1 : canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w) =
        k⁻¹ * (canonicalRep (coxeterSystem Tag.F4) Ω w₁ *
          canonicalRep (coxeterSystem Tag.F4) Ω w) := by
      rw [hkk]; group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.le_normalizer hkM))
      (mul_mem (canonicalRep_mem_normalizer_familyGroup hw₁)
        (canonicalRep_mem_normalizer_of_image himg))
  have hLang : ∀ c ∈ familyGroup (K := Ω) a, ∃ z ∈ familyGroup (K := Ω) a,
      z⁻¹ * (canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w) *
        entrywiseFrobGL Tag.F4 Ω 2 f z *
        (canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w))⁻¹) = c := by
    intro c hc'
    have hQstab : ∀ y ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (familyKernel a),
        frobTwistGL Tag.F4 Ω 2 f (canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w)) y ∈
          torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (familyKernel a) := by
      intro y hy
      rw [frobTwistGL_apply]
      exact (Subgroup.mem_normalizer_iff.1 hQ
        (entrywiseFrobGL Tag.F4 Ω 2 f y)).1
        (entrywiseFrobGL_mem_familyGroup_no117 2 a f hy)
    obtain ⟨z, hz, hzF⟩ := exists_frobTwist_eq_mul_torus_sup_rootSpan_no117
      (τ := Tag.F4) (k := Ω) (p := 2) (S := familyKernel a) f hf
      (canonicalRep (coxeterSystem Tag.F4) Ω (w₁ * w)) hQstab c hc'
    exact ⟨z, hz, by rw [frobTwistGL_apply] at hzF; rw [hzF]; group⟩
  obtain ⟨z, hz, hzF⟩ := exists_mem_lang_conj (entrywiseFrobGL Tag.F4 Ω 2 f)
    (M := familyGroup (K := Ω) a) (mul_mem hm hkM) hn' hLang
  exact ⟨w₁ * w, z, hz, hzF⟩

end CFSG.StandardType.F4ExplicitPos.LangPosition
end

end
