module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggLieLang_map_conj_inv_le {G : Type*} [Group G] {A T : Subgroup G} {g : G}
    (h : A ≤ T.map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g⁻¹).toMonoidHom ≤ T := by
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨t, ht, ht_eq⟩ := h hx
  have hconj : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom t) = t := by
    show MulAut.conj g⁻¹ (MulAut.conj g t) = t
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
    group
  rw [← ht_eq, hconj]
  exact ht

private theorem ggLieLang_cartan_perm_zpow (t : TwistTag) (j : ℤ) (i i' : Fin t.tag.rank) :
    t.tag.cartan ((t.perm ^ j) i) ((t.perm ^ j) i') = t.tag.cartan i i' := by
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact t.cartan_perm_pow n i i'
  · rw [zpow_neg, zpow_natCast]
    exact cartan_perm_symm (t.cartan_perm_pow n) i i'

private theorem ggLieLang_conj_diagramMap_rootDiagUnit
    {L : Type} [Field L] (t : TwistTag)
    (b : Fin t.tag.rank → Lˣ) :
    diagramMap t L * rootDiagUnit t.tag b * (diagramMap t L)⁻¹ =
      rootDiagUnit t.tag (fun i => b (t.perm.symm i)) := by
  rw [diagramMap_mul_rootDiagUnit, mul_assoc, mul_inv_cancel, mul_one]

private theorem ggLieLang_conj_diagramMap_pow_rootDiagUnit
    {L : Type} [Field L] (t : TwistTag) (n : ℕ) :
    ∀ b : Fin t.tag.rank → Lˣ,
      diagramMap t L ^ n * rootDiagUnit t.tag b * (diagramMap t L ^ n)⁻¹ =
        rootDiagUnit t.tag (fun i => b ((t.perm ^ n).symm i)) := by
  induction n with
  | zero => intro b; congr 1
  | succ n ih =>
    intro b
    have hstep : diagramMap t L ^ (n + 1) * rootDiagUnit t.tag b *
        (diagramMap t L ^ (n + 1))⁻¹ =
        diagramMap t L ^ n * (diagramMap t L * rootDiagUnit t.tag b * (diagramMap t L)⁻¹) *
          (diagramMap t L ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev]; group
    rw [hstep, ggLieLang_conj_diagramMap_rootDiagUnit,
      ih (fun i => b (t.perm.symm i))]
    congr 1
    funext i
    rw [pow_succ]
    change b (t.perm.symm ((t.perm ^ n).symm i)) =
      b (((t.perm ^ n * t.perm)⁻¹) i)
    rw [mul_inv_rev, Equiv.Perm.mul_apply]
    rfl

private theorem ggLieLang_conj_diagramMap_zpow_rootDiagUnit
    {L : Type} [Field L] (t : TwistTag) (j : ℤ)
    (b : Fin t.tag.rank → Lˣ) :
    diagramMap t L ^ j * rootDiagUnit t.tag b * (diagramMap t L ^ j)⁻¹ =
      rootDiagUnit t.tag (fun i => b ((t.perm ^ j).symm i)) := by
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact ggLieLang_conj_diagramMap_pow_rootDiagUnit t n b
  · rw [zpow_neg, zpow_natCast]
    have hid : (fun i => b ((t.perm ^ (-(n:ℤ))).symm ((t.perm ^ n).symm i))) = b := by
      funext i
      have h1 : (t.perm ^ (-(n:ℤ))).symm = t.perm ^ n := by
        rw [zpow_neg, zpow_natCast]
        exact Equiv.symm_symm _
      rw [h1, Equiv.apply_symm_apply]
    have hpos :=
      ggLieLang_conj_diagramMap_pow_rootDiagUnit t n (fun i => b ((t.perm ^ (-(n:ℤ))).symm i))
    rw [hid] at hpos
    calc (diagramMap t L ^ n)⁻¹ * rootDiagUnit t.tag b * diagramMap t L ^ n
        = (diagramMap t L ^ n)⁻¹ *
            (diagramMap t L ^ n * rootDiagUnit t.tag (fun i => b ((t.perm ^ (-(n:ℤ))).symm i)) *
              (diagramMap t L ^ n)⁻¹) * diagramMap t L ^ n := by rw [← hpos]
      _ = rootDiagUnit t.tag (fun i => b ((t.perm ^ (-(n:ℤ))).symm i)) := by group

private theorem ggLieLang_frobTwistGL_rootDiagUnit_zpow
    {L : Type} [Field L] [CharP L 2] (t : TwistTag) (j : ℤ)
    (f : ℕ) (b : Fin t.tag.rank → Lˣ) :
    frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (rootDiagUnit t.tag b) =
      rootDiagUnit t.tag (fun i =>
        Units.map (iterateFrobenius L 2 f).toMonoidHom (b ((t.perm ^ j).symm i))) := by
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map,
    ggLieLang_conj_diagramMap_zpow_rootDiagUnit]

private theorem ggLieLang_frobTwistGL_mem_adjointGroup
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (t : TwistTag) (j : ℤ) (f : ℕ)
    {g : ModGL t.tag L} (hg : g ∈ adjointGroup t.tag L) :
    frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g ∈ adjointGroup t.tag L := by
  rw [frobTwistGL_apply]
  have h1 : entrywiseFrobGL t.tag L 2 f g ∈ adjointGroup t.tag L :=
    entrywiseFrobGL_mem 2 f hg
  rw [← map_conj_diagramMap_zpow t L j]
  exact ⟨entrywiseFrobGL t.tag L 2 f g, h1, rfl⟩

private theorem ggLieLang_conj_diagramMap_pow_rootSpan
    {L : Type} [Field L] (t : TwistTag) (n : ℕ) (S : Set (Fin t.tag.rank → ℤ))
    (hS : ∀ α ∈ S, IsRoot t.tag α) :
    (rootSpan t.tag L S).map (MulAut.conj (diagramMap t L ^ n)).toMonoidHom =
      rootSpan t.tag L ((fun α => permLattice (t.perm ^ n) α) '' S) := by
  induction n with
  | zero =>
    have hfun : (fun α : Fin t.tag.rank → ℤ => permLattice (t.perm ^ 0) α) = id := by
      funext α
      funext i
      rfl
    rw [hfun, Set.image_id]
    change Subgroup.map (MonoidHom.id (ModGL t.tag L)) (rootSpan t.tag L S) =
      rootSpan t.tag L S
    rw [Subgroup.map_id]
  | succ n ih =>
    have hstep : (MulAut.conj (diagramMap t L ^ (n + 1))).toMonoidHom =
        (MulAut.conj (diagramMap t L)).toMonoidHom.comp
          (MulAut.conj (diagramMap t L ^ n)).toMonoidHom := by
      rw [pow_succ', map_mul]
      rfl
    rw [hstep, ← Subgroup.map_map, ih]
    have himg : ∀ β ∈ (fun α => permLattice (t.perm ^ n) α) '' S, IsRoot t.tag β := by
      rintro β ⟨α, hα, rfl⟩
      exact (hS α hα).permLattice (t.cartan_perm_pow n)
    have h2 := map_twistHom_rootSpan (t := t) (K := L) (σ := RingHom.id L)
      Function.surjective_id (S := (fun α => permLattice (t.perm ^ n) α) '' S) himg
    rw [← conj_diagramMap_eq_twistHom t L] at h2
    rw [h2, Set.image_image]
    congr 1

private theorem ggLieLang_conj_diagramMap_zpow_torusGroup
    {L : Type} [Field L] (t : TwistTag) (j : ℤ) :
    (torusGroup t.tag L).map (MulAut.conj (diagramMap t L ^ j)).toMonoidHom =
      torusGroup t.tag L := by
  have hP : diagramMap t L ∈
      Subgroup.normalizer (torusGroup t.tag L : Set (ModGL t.tag L)) := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have h := map_twistHom_torusGroup (t := t) (K := L) (σ := RingHom.id L)
      Function.surjective_id
    rw [← conj_diagramMap_eq_twistHom t L] at h
    have h' := congrArg SetLike.coe h
    rw [Subgroup.coe_map] at h'
    exact h'
  exact map_conj_eq_of_mem_normalizer (Subgroup.zpow_mem _ hP j)

private theorem ggLieLang_conj_diagramMap_zpow_rootSpan
    {L : Type} [Field L] (t : TwistTag) (j : ℤ) (S : Set (Fin t.tag.rank → ℤ))
    (hS : ∀ α ∈ S, IsRoot t.tag α) :
    (rootSpan t.tag L S).map (MulAut.conj (diagramMap t L ^ j)).toMonoidHom =
      rootSpan t.tag L ((fun α => permLattice (t.perm ^ j) α) '' S) := by
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact ggLieLang_conj_diagramMap_pow_rootSpan t n S hS
  · rw [zpow_neg, zpow_natCast]
    have himg : ∀ β ∈ (fun α => permLattice (t.perm ^ (-(n:ℤ))) α) '' S, IsRoot t.tag β := by
      rintro β ⟨α, hα, rfl⟩
      exact (hS α hα).permLattice (ggLieLang_cartan_perm_zpow t (-(n:ℤ)))
    have hpos := ggLieLang_conj_diagramMap_pow_rootSpan (L := L) t n _ himg
    have hcompl : (fun α => permLattice (t.perm ^ n) (permLattice (t.perm ^ (-(n:ℤ))) α)) =
        id := by
      funext α
      rw [← permLattice_mul]
      rw [show t.perm ^ n * t.perm ^ (-(n:ℤ)) = 1 from by
        rw [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero]]
      rfl
    rw [Set.image_image, hcompl, Set.image_id] at hpos
    have hsym := congrArg (fun H : Subgroup (ModGL t.tag L) =>
      H.map ((MulAut.conj (diagramMap t L ^ n))⁻¹).toMonoidHom) hpos
    rw [Subgroup.map_map] at hsym
    have hcomp2 : ((MulAut.conj (diagramMap t L ^ n))⁻¹).toMonoidHom.comp
        (MulAut.conj (diagramMap t L ^ n)).toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [hcomp2, Subgroup.map_id] at hsym
    rw [map_inv, ← hsym]

private theorem ggLieLang_mem_normalizer_mul_diagramMap_zpow
    {L : Type} [Field L] (t : TwistTag) (j : ℤ) {ι : Type}
    {a : ι → Fin t.tag.rank → Lˣ} {w : WeylGroup t.tag}
    (himg : (fun α => w • permLattice (t.perm ^ j) α) '' familyKernel a = familyKernel a) :
    canonicalRep (coxeterSystem t.tag) L w * diagramMap t L ^ j ∈
      Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL t.tag L)) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have hP : (familyGroup (K := L) a).map
      (MulAut.conj (diagramMap t L ^ j)).toMonoidHom =
      torusGroup t.tag L ⊔
        rootSpan t.tag L ((fun α => permLattice (t.perm ^ j) α) '' familyKernel a) := by
    rw [familyGroup, Subgroup.map_sup, ggLieLang_conj_diagramMap_zpow_torusGroup,
      ggLieLang_conj_diagramMap_zpow_rootSpan t j (familyKernel a) (fun _ hα => hα.1)]
  have hw : (torusGroup t.tag L ⊔ rootSpan t.tag L
        ((fun α => permLattice (t.perm ^ j) α) '' familyKernel a)).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) L w)).toMonoidHom =
      familyGroup (K := L) a := by
    rw [Subgroup.map_sup,
      map_conj_eq_of_mem_normalizer ((canonical_weyl_root_transport t.tag L).2.2 w),
      (canonical_weyl_root_transport t.tag L).1 w _ (fun β hβ => by
        obtain ⟨α, hα, rfl⟩ := hβ
        exact hα.1.permLattice (ggLieLang_cartan_perm_zpow t j)),
      Set.image_image, himg]
    rfl
  have hsplit : (familyGroup (K := L) a).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) L w * diagramMap t L ^ j)).toMonoidHom =
      ((familyGroup (K := L) a).map (MulAut.conj (diagramMap t L ^ j)).toMonoidHom).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) L w)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  have hmap : (familyGroup (K := L) a).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) L w * diagramMap t L ^ j)).toMonoidHom =
      familyGroup (K := L) a := by
    rw [hsplit, hP, hw]
  have h := congrArg SetLike.coe hmap
  rw [Subgroup.coe_map] at h
  exact h

private theorem ggLieLang_datum_zpow
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (t : TwistTag) (j : ℤ) (f : ℕ) (hf : 1 ≤ f) {ι : Type}
    (a : ι → Fin t.tag.rank → Lˣ) {g : ModGL t.tag L} (hg : g ∈ adjointGroup t.tag L)
    (hn : ∀ s, (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) *
      frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (rootDiagUnit t.tag (a s)) *
      (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g)⁻¹ = rootDiagUnit t.tag (a s)) :
    ∃ (w' : WeylGroup t.tag) (z : ModGL t.tag L), z ∈ familyGroup (K := L) a ∧
      (g * z)⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (g * z) =
        canonicalRep (coxeterSystem t.tag) L w' := by
  classical
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : L →+* L, Fr = iterateFrobenius L 2 f := ⟨_, rfl⟩
  have hFrinj : Function.Injective (Units.map Fr.toMonoidHom) := fun x y h =>
    Units.ext (Fr.injective (congrArg Units.val h))
  obtain ⟨a'', ha''⟩ : ∃ a'' : ι → Fin t.tag.rank → Lˣ,
      a'' = fun s i => Units.map Fr.toMonoidHom (a s ((t.perm ^ j).symm i)) := ⟨_, rfl⟩
  have hFd : ∀ s, frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (rootDiagUnit t.tag (a s)) =
      rootDiagUnit t.tag (a'' s) := fun s => by
    rw [ggLieLang_frobTwistGL_rootDiagUnit_zpow, ← hFrdef, ha'']
  have hnG : g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g ∈ adjointGroup t.tag L :=
    mul_mem (inv_mem hg) (ggLieLang_frobTwistGL_mem_adjointGroup t j f hg)
  obtain ⟨w, hwconj⟩ := exists_weyl_of_conj_family t.tag L a a'' hnG (fun s => by
    rw [← hFd]
    exact hn s)
  have hw : ∀ s v, rootChar (a s) (w • v) =
      Units.map Fr.toMonoidHom (rootChar (a s) (permLattice (t.perm ^ j).symm v)) := by
    intro s v
    rw [(rootDiagUnit_eq_conj_canonicalRep_iff (K := L) (a s) (a'' s) w).1 (hwconj s) v, ha'']
    rw [rootChar_map_tuple Fr (fun i => a s ((t.perm ^ j).symm i)) v,
      rootChar_permLattice (a s) (t.perm ^ j).symm v]
  have h2 : (fun α => w • permLattice (t.perm ^ j) α) '' familyKernel a = familyKernel a := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
      refine ⟨IsRoot.smul (hα.permLattice (ggLieLang_cartan_perm_zpow t j)) w, fun s => ?_⟩
      rw [hw, CFSG.LieType.Chevalley.permLattice_symm_permLattice, hαa s, map_one]
    · rintro ⟨hβ, hβa⟩
      refine ⟨permLattice (t.perm ^ j).symm (w⁻¹ • β), ⟨?_, fun s => ?_⟩, ?_⟩
      · exact (IsRoot.smul hβ w⁻¹).permLattice (π := (t.perm ^ j).symm)
          (cartan_perm_symm (ggLieLang_cartan_perm_zpow t j))
      · apply hFrinj
        rw [map_one, ← hw s (w⁻¹ • β), smul_inv_smul, hβa s]
      · simp only [CFSG.LieType.Chevalley.permLattice_permLattice_symm, smul_inv_smul]
  obtain ⟨nw, hnw⟩ : ∃ nw, nw = canonicalRep (coxeterSystem t.tag) L w := ⟨_, rfl⟩
  have hnwG : nw ∈ adjointGroup t.tag L := hnw ▸ canonicalRep_mem_adjointGroup _ L w
  have hc : (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) * nw⁻¹ ∈
      familyCentralizer t.tag L a := by
    refine mem_familyCentralizer.2 ⟨mul_mem hnG (inv_mem hnwG), fun s => ?_⟩
    have h1 := hwconj s
    rw [← hnw] at h1
    have h2' : nw⁻¹ * rootDiagUnit t.tag (a s) * nw =
        frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (rootDiagUnit t.tag (a s)) := by
      rw [hFd, h1]
      group
    have h3 : ((g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) * nw⁻¹) *
        rootDiagUnit t.tag (a s) *
        ((g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) * nw⁻¹)⁻¹ =
        rootDiagUnit t.tag (a s) := by
      calc ((g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) * nw⁻¹) *
            rootDiagUnit t.tag (a s) *
            ((g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) * nw⁻¹)⁻¹
          = (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) *
              (nw⁻¹ * rootDiagUnit t.tag (a s) * nw) *
              (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g)⁻¹ := by group
        _ = rootDiagUnit t.tag (a s) := by rw [h2']; exact hn s
    rw [mul_inv_eq_iff_eq_mul]
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  obtain ⟨w₁, hw₁, m, hm, hcm⟩ := familyCentralizer_le_mul t.tag L a hc
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) w₁ w
  have hkM : k ∈ familyGroup (K := L) a := Subgroup.mem_sup_left hk
  have hn' : g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g =
      (m * k) * canonicalRep (coxeterSystem t.tag) L (w₁ * w) := by
    have h : g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g =
        (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) * nw⁻¹ * nw := by group
    rw [h, hcm, mul_assoc m, hnw, hkk]
    group
  have himg : (fun α => (w₁ * w) • permLattice (t.perm ^ j) α) '' familyKernel a =
      familyKernel a := by
    have e : (fun α => (w₁ * w) • permLattice (t.perm ^ j) α) =
        (fun α => w₁ • α) ∘ (fun α => w • permLattice (t.perm ^ j) α) :=
      funext fun α => mul_smul w₁ w _
    rw [e, Set.image_comp, h2, image_familyKernel hw₁]
  have hQ : canonicalRep (coxeterSystem t.tag) L (w₁ * w) * diagramMap t L ^ j ∈
      Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL t.tag L)) :=
    ggLieLang_mem_normalizer_mul_diagramMap_zpow t j himg
  have hLang : ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (canonicalRep (coxeterSystem t.tag) L (w₁ * w) *
        frobTwistGL t.tag L 2 f (diagramMap t L ^ j) z *
        (canonicalRep (coxeterSystem t.tag) L (w₁ * w))⁻¹) = c := by
    intro c hc
    obtain ⟨z, hz, hzc⟩ := lang_familyGroup (τ := t.tag) (L := L) (ℓ := 2) (a := a) f hf
      (canonicalRep (coxeterSystem t.tag) L (w₁ * w) * diagramMap t L ^ j) hQ c hc
    refine ⟨z, hz, ?_⟩
    rw [← hzc, frobTwistGL_apply]
    group
  obtain ⟨z, hz, hzF⟩ := exists_mem_lang_conj
    (frobTwistGL t.tag L 2 f (diagramMap t L ^ j)) (M := familyGroup (K := L) a)
    (mul_mem hm hkM) hn' hLang
  exact ⟨w₁ * w, z, hz, hzF⟩

private theorem ggLieLang_twisted_zpow
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (t : TwistTag) (j : ℤ) (f : ℕ) (hf : 1 ≤ f)
    {A : Subgroup (ModGL t.tag L)}
    (hFix : ∀ x ∈ A, frobTwistGL t.tag L 2 f (diagramMap t L ^ j) x = x) {g : ModGL t.tag L}
    (hg : g ∈ adjointGroup t.tag L) (hgA : ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup t.tag L) :
    ∃ v : WeylGroup t.tag, ∃ g0 ∈ adjointGroup t.tag L,
      frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g0 =
        g0 * canonicalRep (coxeterSystem t.tag) L v ∧
      ∀ x ∈ A, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem t.tag) L v)
        (frobTwistGL t.tag L 2 f (diagramMap t L ^ j))).map (MulAut.conj g0).toMonoidHom := by
  classical
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hgA x x.2)
  have hn : ∀ x : A, (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g) *
      frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (rootDiagUnit t.tag (a x)) *
      (g⁻¹ * frobTwistGL t.tag L 2 f (diagramMap t L ^ j) g)⁻¹ = rootDiagUnit t.tag (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix x x.2]
    group
  obtain ⟨w', z, hz, hlang⟩ := ggLieLang_datum_zpow t j f hf a hg hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : frobTwistGL t.tag L 2 f (diagramMap t L ^ j) (g * z) =
      (g * z) * canonicalRep (coxeterSystem t.tag) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', g * z, mul_mem hg hzG, hu,
    mem_lang_torus_of_datum _ hFix hu fun x hx => ?_⟩
  have hzd : z⁻¹ * rootDiagUnit t.tag (a ⟨x, hx⟩) * z = rootDiagUnit t.tag (a ⟨x, hx⟩) := by
    have hthis := hzcomm ⟨x, hx⟩
    rw [mul_inv_eq_iff_eq_mul] at hthis
    calc z⁻¹ * rootDiagUnit t.tag (a ⟨x, hx⟩) * z =
          z⁻¹ * (rootDiagUnit t.tag (a ⟨x, hx⟩) * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit t.tag (a ⟨x, hx⟩)) := by rw [hthis]
      _ = rootDiagUnit t.tag (a ⟨x, hx⟩) := by group
  have ht : (g * z)⁻¹ * x * (g * z) = rootDiagUnit t.tag (a ⟨x, hx⟩) := by
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = rootDiagUnit t.tag (a ⟨x, hx⟩) := by rw [ha ⟨x, hx⟩, hzd]
  rw [ht]
  exact rootDiagUnit_mem_torusGroup _

theorem langDatumOfPosition_transport
    {τ : Tag} {L : Type} [Field L] {q : ℕ} {Φ : ModGL τ L →* ModGL τ L}
    (hΦ : IsSteinbergEnd τ L q Φ) (w : WeylGroup τ) (g : ModGL τ L) (hg : g ∈ adjointGroup τ L)
    (hlang : Φ g = g * canonicalRep (coxeterSystem τ) L w) {A : Subgroup (ModGL τ L)}
    (hT : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) Φ) :
    (ratPoints Φ).map (MulAut.conj g⁻¹).toMonoidHom =
        (langDatumOfPosition hΦ w g hg hlang).model ∧
      A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (langDatumOfPosition hΦ w g hg hlang).torus := by
  constructor
  · apply le_antisymm
    · rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [ratPoints, Subgroup.mem_inf] at hx
      obtain ⟨hxG, hxfix⟩ := hx
      change Φ x = x at hxfix
      have hconj : ∀ z : ModGL τ L, (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g :=
        fun z => by
          show MulAut.conj g⁻¹ z = g⁻¹ * z * g
          rw [MulAut.conj_apply, inv_inv]
      rw [LangDatum.mem_model]
      refine ⟨mul_mem (mul_mem (inv_mem hg) hxG) hg, ?_⟩
      change canonicalRep (coxeterSystem τ) L w * Φ ((MulAut.conj g⁻¹).toMonoidHom x) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = (MulAut.conj g⁻¹).toMonoidHom x
      rw [hconj, map_mul, map_mul, map_inv, hxfix, hlang]
      group
    · rintro y hy
      rw [LangDatum.mem_model] at hy
      obtain ⟨hyG, hyfix⟩ := hy
      change canonicalRep (coxeterSystem τ) L w * Φ y *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = y at hyfix
      rw [Subgroup.mem_map]
      refine ⟨g * y * g⁻¹, ?_, ?_⟩
      · rw [ratPoints, Subgroup.mem_inf]
        refine ⟨mul_mem (mul_mem hg hyG) (inv_mem hg), ?_⟩
        change Φ (g * y * g⁻¹) = g * y * g⁻¹
        rw [map_mul, map_mul, map_inv, hlang]
        calc (g * canonicalRep (coxeterSystem τ) L w) * Φ y *
              (g * canonicalRep (coxeterSystem τ) L w)⁻¹
            = g * (canonicalRep (coxeterSystem τ) L w * Φ y *
                (canonicalRep (coxeterSystem τ) L w)⁻¹) * g⁻¹ := by group
          _ = g * y * g⁻¹ := by rw [hyfix]
      · change g⁻¹ * (g * y * g⁻¹) * g = y
        group
  · exact hT

theorem ggLieLangPosition_holds
    : GGLieLangPosition := by
  intro τ _ L _ _ _ f hf Φ hΦ _ p hp hp2 A hA hAea hAtoral
  obtain ⟨g₁, hg₁, hg₁A⟩ := hAtoral
  obtain ⟨Fr, hFr, P, hP, hΦP⟩ := hΦ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [hFr c, iterateFrobenius_def]
  have hFixΦ : ∀ x ∈ A, Φ x = x := by
    intro x hx
    have hxr := hA hx
    rw [ratPoints, Subgroup.mem_inf] at hxr
    exact hxr.2
  have hpq : Nat.Coprime p (2 ^ f) :=
    Nat.Prime.coprime_pow_of_not_dvd (p := 2) Nat.prime_two
      (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
  rcases hP with hP1 | ⟨t, j, ht, hPt⟩
  · have hΦ_entry : Φ = entrywiseFrobGL τ L 2 f := by
      ext g
      rw [hΦP g, hP1, hFr_eq]
      simp only [one_mul, inv_one, mul_one]
    obtain ⟨w, g0, hg0, hlang0, hT0⟩ :=
      exists_lang_torus_of_conj_torus (ℓ := 2) f hf hpq hAea.2
        (fun x hx => by rw [← hΦ_entry]; exact hFixΦ x hx) hg₁ hg₁A
    refine ⟨w, g0, hg0, ?_, ?_⟩
    · rw [hΦ_entry]; exact hlang0
    · rw [hΦ_entry]
      exact ggLieLang_map_conj_inv_le hT0
  · subst ht
    have hΦ_tw : Φ = frobTwistGL t.tag L 2 f (diagramMap t L ^ j) := by
      ext g
      rw [hΦP g, hPt, hFr_eq]
      rfl
    obtain ⟨w, g0, hg0, hlang0, hT0⟩ :=
      ggLieLang_twisted_zpow t j f hf (fun x hx => by rw [← hΦ_tw]; exact hFixΦ x hx) hg₁ hg₁A
    refine ⟨w, g0, hg0, ?_, ?_⟩
    · rw [hΦ_tw]; exact hlang0
    · rw [hΦ_tw]
      exact ggLieLang_map_conj_inv_le hT0

end CFSG.StandardType.LieCore
