module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtDeg
public import CFSG.Quasithin.Background.SimsG4OrthUPrim
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsMonomial
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSupport

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] noncomputable def impFrame (H : Subgroup (U ≃ₗ[ZMod p] U)) {l : ℕ}
    (e : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)) :
    Set (Submodule (ZMod p) U) :=
  insert (centralizerSpace H) (Set.range fun j =>
    Submodule.span (ZMod p) {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)})

@[expose] noncomputable def impFrameAt (H : Subgroup (U ≃ₗ[ZMod p] U)) {l : ℕ}
    (e : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)) (i : Fin l)
    (M : Submodule (ZMod p) U) : Set (Submodule (ZMod p) U) :=
  insert M {X | ∃ k, k ≠ i ∧
    X = Submodule.span (ZMod p) {((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)}}

namespace ImpExtStd

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
  {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace H)}
  {j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)} {ζ : (ZMod p)ˣ}

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_exists_neg_vec {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    ∃ r, HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {r} ∧ t r = -r := by
  have hVne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    have h := ht.2
    change Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 at h
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨r, hr_mem, hr_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  refine ⟨r, eq_span_singleton_of_mem_of_finrank_eq_one ht.2 hr_mem hr_ne, ?_⟩
  obtain ⟨u, hu⟩ := hr_mem
  rw [← hu]
  have htt : t (t u) = u := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) ht.1
    simpa [LinearEquiv.mul_apply] using this
  change t (t u - u) = -(t u - u)
  rw [map_sub, htt]
  abel

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_neg_component {t : U ≃ₗ[ZMod p] U} {A B : Submodule (ZMod p) U}
    (hAB : A ⊓ B = ⊥) (hA : A.map (t : U →ₗ[ZMod p] U) = A)
    (hB : B.map (t : U →ₗ[ZMod p] U) = B) {r rA rB : U} (htr : t r = -r) (hrA : rA ∈ A)
    (hrB : rB ∈ B) (hrAB : rA + rB = r) : t rA = -rA := by
  have htA : t rA ∈ A := by
    have hmem : t rA ∈ A.map (t : U →ₗ[ZMod p] U) := Submodule.mem_map_of_mem hrA
    rwa [hA] at hmem
  have htB : t rB ∈ B := by
    have hmem : t rB ∈ B.map (t : U →ₗ[ZMod p] U) := Submodule.mem_map_of_mem hrB
    rwa [hB] at hmem
  have h1 : t rA + t rB = -rA - rB := by
    rw [← map_add, hrAB, htr, ← hrAB]
    abel
  have hmem : t rA - (-rA) ∈ A ⊓ B := by
    refine ⟨Submodule.sub_mem _ htA (Submodule.neg_mem _ hrA), ?_⟩
    have h2 : t rA - (-rA) = (-rB) - t rB := by
      rw [sub_eq_sub_iff_add_eq_add, h1]
      abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hrB) htB
  rw [hAB] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_mem_movedSpace_of_neg (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U} {v : U}
    (hv : t v = -v) : v ∈ HardMathSupport.Kantor79.movedSpace t := by
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  refine ⟨(-(2⁻¹ : ZMod p)) • v, ?_⟩
  change t ((-(2⁻¹ : ZMod p)) • v) - ((-(2⁻¹ : ZMod p)) • v) = v
  rw [map_smul, hv, smul_neg, neg_smul, neg_neg, sub_neg_eq_add, ← add_smul]
  have h2sum : (2⁻¹ : ZMod p) + 2⁻¹ = 1 := by
    rw [← two_mul]
    exact mul_inv_cancel₀ h2p
  rw [h2sum, one_smul]

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_movedSpace_le_of_isCompl (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) {A B : Submodule (ZMod p) U} (hcompl : IsCompl A B)
    (hA : A.map (t : U →ₗ[ZMod p] U) = A) (hB : B.map (t : U →ₗ[ZMod p] U) = B) :
    HardMathSupport.Kantor79.movedSpace t ≤ A ∨
      HardMathSupport.Kantor79.movedSpace t ≤ B := by
  obtain ⟨r, hr_span, htr⟩ := zs4j_exists_neg_vec ht
  have hr_decomp : r ∈ A ⊔ B := by rw [hcompl.sup_eq_top]; trivial
  rw [Submodule.mem_sup] at hr_decomp
  obtain ⟨rA, hrA, rB, hrB, hrAB⟩ := hr_decomp
  have htrA := zs4j_neg_component hcompl.inf_eq_bot hA hB htr hrA hrB hrAB
  have hrA_span : rA ∈ Submodule.span (ZMod p) {r} := by
    rw [← hr_span]
    exact zs4j_mem_movedSpace_of_neg hp htrA
  rw [Submodule.mem_span_singleton] at hrA_span
  obtain ⟨a, ha⟩ := hrA_span
  by_cases ha0 : a = 0
  · right
    rw [hr_span, Submodule.span_singleton_le_iff_mem]
    rw [← ha, ha0, zero_smul, zero_add] at hrAB
    rw [← hrAB]
    exact hrB
  · left
    rw [hr_span, Submodule.span_singleton_le_iff_mem]
    have hr_eq : r = a⁻¹ • rA := by
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [hr_eq]
    exact Submodule.smul_mem _ _ hrA

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_mem_commutatorSpace_basisStab (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    {i j : Fin (Module.finrank (ZMod p) U - 1)} (hj : j ≠ i) :
    ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) ∈
      HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) := by
  obtain ⟨g, _k₀, _k₁, _hk, hgj, _⟩ := exists_basis_basisStab hp S i
  let f : Fin (Module.finrank (ZMod p) U - 2) →
      {j : Fin (Module.finrank (ZMod p) U - 1) // j ≠ i} :=
    fun k => ⟨Classical.choose (hgj k), (Classical.choose_spec (hgj k)).1⟩
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ h
    apply g.injective
    apply Subtype.ext
    have h1 := (Classical.choose_spec (hgj k₁)).2
    have h2 := (Classical.choose_spec (hgj k₂)).2
    have h' : Classical.choose (hgj k₁) = Classical.choose (hgj k₂) :=
      congrArg Subtype.val h
    rw [h1, h2, h']
  have hcard : Fintype.card (Fin (Module.finrank (ZMod p) U - 2)) =
      Fintype.card {j : Fin (Module.finrank (ZMod p) U - 1) // j ≠ i} := by
    rw [Fintype.card_fin]
    change Module.finrank (ZMod p) U - 2 =
      Fintype.card {x : Fin (Module.finrank (ZMod p) U - 1) | x ≠ i}
    rw [Set.card_ne_eq, Fintype.card_fin]
    have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
    omega
  have hf_surj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩).2
  obtain ⟨k, hk⟩ := hf_surj ⟨j, hj⟩
  have h1 := (Classical.choose_spec (hgj k)).2
  have h2 : ((e (Classical.choose (hgj k)) : HardMathSupport.Kantor79.commutatorSpace H) : U) =
      ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) := by
    have hk' : Classical.choose (hgj k) = j := congrArg Subtype.val hk
    rw [hk']
  rw [← h2, ← h1]
  exact (g k).2

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_fix_of_movedSpace_le {t : U ≃ₗ[ZMod p] U} {A B : Submodule (ZMod p) U}
    (hAB : A ⊓ B = ⊥) (hB : B.map (t : U →ₗ[ZMod p] U) = B)
    (hle : HardMathSupport.Kantor79.movedSpace t ≤ A) : ∀ v ∈ B, t v = v := by
  intro v hv
  have hmem : t v - v ∈ HardMathSupport.Kantor79.movedSpace t := ⟨v, rfl⟩
  have htv : t v ∈ B := by
    have h' := Submodule.mem_map_of_mem (f := (t : U →ₗ[ZMod p] U)) hv
    rwa [hB] at h'
  have hsub : t v - v ∈ A ⊓ B := ⟨hle hmem, Submodule.sub_mem _ htv hv⟩
  rw [hAB] at hsub
  exact sub_eq_zero.mp (by simpa using hsub)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_map_eq_of_fix {t : U ≃ₗ[ZMod p] U} {W : Submodule (ZMod p) U}
    (h : ∀ v ∈ W, t v = v) : W.map (t : U →ₗ[ZMod p] U) = W := by
  refine le_antisymm ?_ fun v hv => Submodule.mem_map.mpr ⟨v, hv, h v hv⟩
  rintro _ ⟨v, hv, rfl⟩
  change t v ∈ W
  rwa [h v hv]

theorem fix_of_mem_mul_basisStab (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (I : ImpExtInputs G H) (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ G) (har : IsRefl p a)
    (haH : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c)
    (hai : ∃ h ∈ basisStab H e i,
      ∃ c ∈ Subgroup.centralizer (basisStab H e i : Set (U ≃ₗ[ZMod p] U)), a = h * c) :
    ∀ j, j ≠ i → a ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) = e j := by
  intro j hj
  obtain ⟨h, hh, c, hc, rfl⟩ := hai
  have ha_norm : (h * c) ∈ Subgroup.normalizer (basisStab H e i : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer hh)
      (Subgroup.centralizer_le_normalizer _ hc)
  have hmapA : (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)).map
      ((h * c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) :=
    map_commutatorSpace_of_mem_normalizer ha_norm
  have hmapB : (centralizerSpace (basisStab H e i)).map
      ((h * c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      centralizerSpace (basisStab H e i) :=
    map_centralizerSpace_of_mem_normalizer ha_norm
  have hcompl : IsCompl (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))
      (centralizerSpace (basisStab H e i)) := (splitSupport_basisStab hp S i).1
  rcases zs4j_movedSpace_le_of_isCompl hp har hcompl hmapA hmapB with hleA | hleB
  · have hfixVH : ∀ v ∈ centralizerSpace H, (h * c) v = v := fun v hv =>
      zs4j_fix_of_movedSpace_le hcompl.inf_eq_bot hmapB hleA v
        (mem_centralizerSpace.mpr fun k hk => mem_centralizerSpace.mp hv k hk.1)
    exact False.elim (haH (ImpExtSetting.mem_mul_centralizer_of_map_eq S.toImpExtSetting
      I.lemmaOneSeven ha har (Or.inr (zs4j_map_eq_of_fix hfixVH))))
  · exact zs4j_fix_of_movedSpace_le hcompl.symm.inf_eq_bot hmapA hleB _
      (zs4j_mem_commutatorSpace_basisStab hp S hj)


omit [Module.Finite (ZMod p) U] in
private lemma zs4j_false_of_gmmn_le_three (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hmono : movedGroup H = gmmn p e j₀ j₁ ζ) (hζ : orderOf ζ ≤ 3) : False := by
  have hDMax : DMax p (movedGroup H) d :=
    (dmax_movedGroup_iff S.splitSupport d).mpr S.dmax_H
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hDMax.2
  have hx' : x ∈ gmmn p e j₀ j₁ ζ := by rwa [← hmono]
  have hy' : y ∈ gmmn p e j₀ j₁ ζ := by rwa [← hmono]
  have h3 : 3 < d := S.three_lt
  have hsplit := TableFacts.orderOf_mul_le_three_or_dvd_of_mem_gmmn hp e S.ne ζ hx' hy' hxr hyr
  rcases hsplit with hle | hdvd
  · rw [hxy] at hle
    omega
  · have hle : orderOf (x * y) ≤ orderOf ζ := Nat.le_of_dvd (orderOf_pos ζ) hdvd
    rw [hxy] at hle
    omega

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_hexc_gmmn (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (hmono : movedGroup H = gmmn p e j₀ j₁ ζ) :
    ¬ (Module.finrank (ZMod p) U - 1 = 3 ∧
        (orderOf ζ = 2 ∨ orderOf ζ = 3 ∨ orderOf ζ = 4)) ∧
      ¬ (Module.finrank (ZMod p) U - 1 = 4 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 3)) ∧
      ¬ (Module.finrank (ZMod p) U - 1 = 5 ∧ orderOf ζ = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h3, hζ⟩
    rcases hζ with hζ | hζ | hζ
    · exact zs4j_false_of_gmmn_le_three hp S hmono (by omega)
    · exact zs4j_false_of_gmmn_le_three hp S hmono (by omega)
    · exact hM ⟨h3, fun _ => hζ, fun _ => Or.inr hζ⟩
  · rintro ⟨h4, hζ⟩
    rcases hζ with hζ | hζ
    · exact zs4j_false_of_gmmn_le_three hp S hmono (by omega)
    · exact zs4j_false_of_gmmn_le_three hp S hmono (by omega)
  · rintro ⟨h5, hζ⟩
    exact zs4j_false_of_gmmn_le_three hp S hmono (by omega)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_hexc_g2mmn (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (_hmono : movedGroup H = g2mmn p e j₀ j₁ ζ) :
    ¬ (Module.finrank (ZMod p) U - 1 = 3 ∧
        (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4)) := by
  rintro ⟨h3, hζ⟩
  refine hM ⟨h3, ?_, ?_⟩
  · intro hg
    rcases hζ with hζ | hζ | hζ
    · exact (zs4j_false_of_gmmn_le_three hp S hg (by rw [hζ]; norm_num)).elim
    · exact (zs4j_false_of_gmmn_le_three hp S hg (by rw [hζ]; norm_num)).elim
    · exact hζ
  · intro _
    rcases hζ with hζ | hζ | hζ
    · left; rw [hζ]; exact one_dvd 2
    · left; rw [hζ]
    · right; exact hζ

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_span_range_b {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)} :
    Submodule.span (ZMod p) (Set.range fun k => (b k : U)) =
      HardMathSupport.Kantor79.commutatorSpace F := by
  have h := congrArg (Submodule.map
    (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace F))) b.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top] at h
  rw [← Set.range_comp] at h
  simpa [Function.comp_def] using h

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_linearIndependent_b {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)} :
    LinearIndependent (ZMod p) (fun k => (b k : U)) := by
  have h := b.linearIndependent.map' (Submodule.subtype
    (HardMathSupport.Kantor79.commutatorSpace F)) (Submodule.ker_subtype _)
  simpa [Function.comp_def] using h

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_commutatorSpace_le_span_b {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (i : Fin (Module.finrank (ZMod p) U - 1)) (hKF : basisStab H e i ≤ F)
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)} :
    HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) ≤
      Submodule.span (ZMod p) (Set.range fun k => (b k : U)) := by
  rw [zs4j_span_range_b]
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
  rintro w ⟨k, hk', v, rfl⟩
  exact Submodule.subset_span ⟨k, hKF hk', v, rfl⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_monomial_on_b {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (i : Fin (Module.finrank (ZMod p) U - 1)) (hKF : basisStab H e i ≤ F)
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (hbmon : ∀ y ∈ movedGroup F, ∃ (σ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)))
      (c : Fin (Module.finrank (ZMod p) U - 1) → ZMod p), (∀ k, c k ≠ 0) ∧
      ∀ k, y (b k) = c k • b (σ k)) :
    ∀ y ∈ basisStab H e i, ∀ k, ∃ j, ∃ c : ZMod p,
      y ((b k : HardMathSupport.Kantor79.commutatorSpace F) : U) =
        c • ((b j : HardMathSupport.Kantor79.commutatorSpace F) : U) := by
  intro y hy k
  have hyF : y ∈ F := hKF hy
  let y' : HardMathSupport.Kantor79.commutatorSpace F ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace F :=
    restrictHom F (HardMathSupport.Kantor79.commutatorSpace F)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨y, hyF⟩
  have hy' : y' ∈ movedGroup F := ⟨⟨y, hyF⟩, rfl⟩
  obtain ⟨σ, c, hc, h⟩ := hbmon y' hy'
  refine ⟨σ k, c k, ?_⟩
  have h1 := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace F => (w : U)) (h k)
  rw [restrictHom_apply] at h1
  simpa only [Submodule.coe_smul] using h1

private lemma zs4j_span_eq_lines (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (i : Fin (Module.finrank (ZMod p) U - 1))
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (hb_li : LinearIndependent (ZMod p) (fun k => (b k : U)))
    (hmonH : ∀ y ∈ basisStab H e i, ∀ k, ∃ j, ∃ c : ZMod p,
      y ((b k : HardMathSupport.Kantor79.commutatorSpace F) : U) =
        c • ((b j : HardMathSupport.Kantor79.commutatorSpace F) : U))
    (hle_b : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) ≤
      Submodule.span (ZMod p) (Set.range fun k => (b k : U)))
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    {k₀ k₁ : Fin (Module.finrank (ZMod p) U - 2)} (hk : k₀ ≠ k₁)
    (hgmono1 : movedGroup H = gmmn p e j₀ j₁ ζ →
      movedGroup (basisStab H e i) = gmmn p g k₀ k₁ ζ)
    (hgmono2 : movedGroup H = g2mmn p e j₀ j₁ ζ →
      movedGroup (basisStab H e i) = g2mmn p g k₀ k₁ ζ) :
    (∀ k : Fin (Module.finrank (ZMod p) U - 2), ∃ j,
        Submodule.span (ZMod p)
          {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
        Submodule.span (ZMod p)
          {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)}) ∧
      ∃ j : Fin (Module.finrank (ZMod p) U - 1),
        centralizerSpace (basisStab H e i) ⊓
          Submodule.span (ZMod p) (Set.range fun k => (b k : U)) =
        Submodule.span (ZMod p)
          {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)} := by
  have hn3 : 3 ≤ Module.finrank (ZMod p) U - 1 := by
    have h4 := S.four_le_finrank; omega
  rcases S.mono with hmono | hmono
  · exact span_eq_of_splitSupport_gmmn hp hn3 hb_li (reflGen_basisStab S i) hmonH hle_b
      (splitSupport_basisStab hp S i) g hk (hgmono1 hmono) (zs4j_hexc_gmmn hp S hM hmono)
  · exact span_eq_of_splitSupport_g2mmn hp hn3 hb_li (reflGen_basisStab S i) hmonH hle_b
      (splitSupport_basisStab hp S i) g hk (hgmono2 hmono) (zs4j_hexc_g2mmn hp S hM hmono)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_psi_bij (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1))
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    (hgline : ∀ k, ∃ j, j ≠ i ∧
      ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
      ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) :
    ∃ psie : Fin (Module.finrank (ZMod p) U - 2) ≃
        {j : Fin (Module.finrank (ZMod p) U - 1) // j ≠ i},
      ∀ k, ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
        ((e (psie k).1 : HardMathSupport.Kantor79.commutatorSpace H) : U) := by
  let psi : Fin (Module.finrank (ZMod p) U - 2) →
      {j : Fin (Module.finrank (ZMod p) U - 1) // j ≠ i} :=
    fun k => ⟨Classical.choose (hgline k), (Classical.choose_spec (hgline k)).1⟩
  have hpsi_val : ∀ k,
      ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
      ((e (psi k).1 : HardMathSupport.Kantor79.commutatorSpace H) : U) :=
    fun k => (Classical.choose_spec (hgline k)).2
  have hpsi_inj : Function.Injective psi := by
    intro k₁ k₂ h
    have h1 : (psi k₁).1 = (psi k₂).1 := congrArg Subtype.val h
    have h2 : ((g k₁ : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
        ((g k₂ : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) := by
      rw [hpsi_val k₁, hpsi_val k₂, h1]
    exact g.injective (Subtype.coe_injective h2)
  have hpsi_bij : Function.Bijective psi := by
    refine (Fintype.bijective_iff_injective_and_card psi).mpr ⟨hpsi_inj, ?_⟩
    rw [Fintype.card_fin]
    change Module.finrank (ZMod p) U - 2 =
      Fintype.card {x : Fin (Module.finrank (ZMod p) U - 1) | x ≠ i}
    rw [Set.card_ne_eq, Fintype.card_fin]
    have h4 := S.four_le_finrank
    omega
  exact ⟨Equiv.ofBijective psi hpsi_bij, hpsi_val⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_f_inj {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (i : Fin (Module.finrank (ZMod p) U - 1))
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    (f : Fin (Module.finrank (ZMod p) U - 2) → Fin (Module.finrank (ZMod p) U - 1))
    (hf_spec : ∀ k, Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
      Submodule.span (ZMod p)
        {((b (f k) : HardMathSupport.Kantor79.commutatorSpace F) : U)}) :
    Function.Injective f := by
  intro k₁ k₂ h
  by_contra hne
  have hspan_eq' : Submodule.span (ZMod p)
      {((g k₁ : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
      Submodule.span (ZMod p)
        {((g k₂ : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} := by
    rw [hf_spec k₁, hf_spec k₂, h]
  have hmem : ((g k₂ : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) ∈
      Submodule.span (ZMod p)
        {((g k₁ : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} := by
    rw [hspan_eq']
    exact Submodule.mem_span_singleton_self _
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : g k₂ = c • g k₁ := Subtype.coe_injective (by
    simpa only [Submodule.coe_smul] using hc.symm)
  have hrepr := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)
    => g.repr w k₂) hc'
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero] at hrepr
  exact one_ne_zero hrepr

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_count (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Fin (Module.finrank (ZMod p) U - 2) → Fin (Module.finrank (ZMod p) U - 1)}
    (hf_inj : Function.Injective f) {j₂ : Fin (Module.finrank (ZMod p) U - 1)}
    (hj₂_notmem : j₂ ∉ Set.range f) :
    insert j₂ (Finset.univ.image f) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    have h4 := S.four_le_finrank
    omega
  · rw [Finset.mem_image]
    rintro ⟨k, _, hk⟩
    exact hj₂_notmem ⟨k, hk⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_F_b {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (hbmon : ∀ y ∈ movedGroup F, ∃ (σ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)))
      (c : Fin (Module.finrank (ZMod p) U - 1) → ZMod p), (∀ k, c k ≠ 0) ∧
      ∀ k, y (b k) = c k • b (σ k)) :
    ∀ g' ∈ F, ∀ j, ∃ j', (Submodule.span (ZMod p)
      {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)}).map
        (g' : U →ₗ[ZMod p] U) = Submodule.span (ZMod p)
      {((b j' : HardMathSupport.Kantor79.commutatorSpace F) : U)} := by
  intro g' hg' j
  let g'' : HardMathSupport.Kantor79.commutatorSpace F ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace F :=
    restrictHom F (HardMathSupport.Kantor79.commutatorSpace F)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨g', hg'⟩
  have hg'' : g'' ∈ movedGroup F := ⟨⟨g', hg'⟩, rfl⟩
  obtain ⟨σ, c, hc, h⟩ := hbmon g'' hg''
  refine ⟨σ j, ?_⟩
  rw [Submodule.map_span, Set.image_singleton]
  change Submodule.span (ZMod p) {g' ((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)} =
    Submodule.span (ZMod p)
      {((b (σ j) : HardMathSupport.Kantor79.commutatorSpace F) : U)}
  have h1 : g' ((b j : HardMathSupport.Kantor79.commutatorSpace F) : U) =
      (c j : ZMod p) • ((b (σ j) : HardMathSupport.Kantor79.commutatorSpace F) : U) := by
    have h2 := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace F => (w : U)) (h j)
    rw [restrictHom_apply] at h2
    simpa only [Submodule.coe_smul] using h2
  rw [h1, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (hc j))]

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_j2_notmem (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1))
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    {f : Fin (Module.finrank (ZMod p) U - 2) → Fin (Module.finrank (ZMod p) U - 1)}
    (hf_spec : ∀ k, Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
      Submodule.span (ZMod p)
        {((b (f k) : HardMathSupport.Kantor79.commutatorSpace F) : U)})
    {j₂ : Fin (Module.finrank (ZMod p) U - 1)}
    (hMline : centralizerSpace (basisStab H e i) ⊓
      Submodule.span (ZMod p) (Set.range fun k => (b k : U)) =
      Submodule.span (ZMod p)
        {((b j₂ : HardMathSupport.Kantor79.commutatorSpace F) : U)}) :
    j₂ ∉ Set.range f := by
  let M := centralizerSpace (basisStab H e i) ⊓
    Submodule.span (ZMod p) (Set.range fun k => (b k : U))
  have hM_le : M ≤ centralizerSpace (basisStab H e i) := inf_le_left
  rintro ⟨k, hk⟩
  have hline : M = Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} := by
    have hM_eq' : M = Submodule.span (ZMod p)
        {((b j₂ : HardMathSupport.Kantor79.commutatorSpace F) : U)} := hMline
    rw [hM_eq', hf_spec k, hk]
  have hle : Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} ≤
      HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) ⊓
        centralizerSpace (basisStab H e i) := by
    refine le_inf ?_ ?_
    · exact (Submodule.span_singleton_le_iff_mem
        (((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U))
        (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))).mpr (g k).2
    · rw [← hline]
      exact hM_le
  rw [(splitSupport_basisStab hp S i).1.inf_eq_bot] at hle
  have hmem := hle (Submodule.mem_span_singleton_self
    ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U))
  exact (g.ne_zero k) (by simpa using hmem)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_b_lines_mem (_hp : p ≠ 2) (_S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1))
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    {f : Fin (Module.finrank (ZMod p) U - 2) → Fin (Module.finrank (ZMod p) U - 1)}
    (hf_spec : ∀ k, Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
      Submodule.span (ZMod p)
        {((b (f k) : HardMathSupport.Kantor79.commutatorSpace F) : U)})
    {j₂ : Fin (Module.finrank (ZMod p) U - 1)}
    (hMline : centralizerSpace (basisStab H e i) ⊓
      Submodule.span (ZMod p) (Set.range fun k => (b k : U)) =
      Submodule.span (ZMod p)
        {((b j₂ : HardMathSupport.Kantor79.commutatorSpace F) : U)})
    (hcount : insert j₂ (Finset.univ.image f) = Finset.univ)
    (hgline : ∀ k, ∃ j, j ≠ i ∧
      ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
      ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) :
    ∀ j, Submodule.span (ZMod p)
      {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)} ∈
      impFrameAt H e i (centralizerSpace (basisStab H e i) ⊓
        Submodule.span (ZMod p) (Set.range fun k => (b k : U))) := by
  intro j
  by_cases hj : j = j₂
  · rw [hj, impFrameAt]
    left
    exact hMline.symm
  · have hjmem : j ∈ Finset.univ.image f := by
      have hthis : j ∈ insert j₂ (Finset.univ.image f) := by
        rw [hcount]; exact Finset.mem_univ j
      rw [Finset.mem_insert] at hthis
      rcases hthis with h | h
      · exact absurd h hj
      · exact h
    rw [Finset.mem_image] at hjmem
    obtain ⟨k, _, hk⟩ := hjmem
    rw [← hk, ← hf_spec k]
    rw [impFrameAt]
    right
    obtain ⟨l, hl, hlk⟩ := hgline k
    exact ⟨l, hl, by rw [hlk]⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_impFrameAt_b {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (i : Fin (Module.finrank (ZMod p) U - 1))
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    {f : Fin (Module.finrank (ZMod p) U - 2) → Fin (Module.finrank (ZMod p) U - 1)}
    (hf_spec : ∀ k, Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
      Submodule.span (ZMod p)
        {((b (f k) : HardMathSupport.Kantor79.commutatorSpace F) : U)})
    {j₂ : Fin (Module.finrank (ZMod p) U - 1)}
    (hMline : centralizerSpace (basisStab H e i) ⊓
      Submodule.span (ZMod p) (Set.range fun k => (b k : U)) =
      Submodule.span (ZMod p)
        {((b j₂ : HardMathSupport.Kantor79.commutatorSpace F) : U)})
    {psie : Fin (Module.finrank (ZMod p) U - 2) ≃
        {j : Fin (Module.finrank (ZMod p) U - 1) // j ≠ i}}
    (hpsi_val : ∀ k, ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
      ((e (psie k).1 : HardMathSupport.Kantor79.commutatorSpace H) : U)) :
    ∀ X ∈ impFrameAt H e i
      (centralizerSpace (basisStab H e i) ⊓
        Submodule.span (ZMod p) (Set.range fun k => (b k : U))),
      ∃ j, X = Submodule.span (ZMod p)
        {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)} := by
  intro X hX
  rw [impFrameAt] at hX
  rcases hX with hX | ⟨k, hk, hX⟩
  · exact ⟨j₂, by rw [hX]; exact hMline⟩
  · let k' : Fin (Module.finrank (ZMod p) U - 2) := psie.symm ⟨k, hk⟩
    have hk' : ((g k' : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
        ((e k : HardMathSupport.Kantor79.commutatorSpace H) : U) := by
      have h1 : psie k' = ⟨k, hk⟩ := Equiv.apply_symm_apply psie ⟨k, hk⟩
      have h2 : (psie k').1 = k := congrArg Subtype.val h1
      rw [hpsi_val k', h2]
    refine ⟨f k', ?_⟩
    rw [hX, ← hf_spec k', hk']

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_hperm_final {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (i : Fin (Module.finrank (ZMod p) U - 1))
    (hXb : ∀ X ∈ impFrameAt H e i
      (centralizerSpace (basisStab H e i) ⊓
        Submodule.span (ZMod p) (Set.range fun k => (b k : U))),
      ∃ j, X = Submodule.span (ZMod p)
        {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)})
    (hb_lines : ∀ j, Submodule.span (ZMod p)
      {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)} ∈
      impFrameAt H e i (centralizerSpace (basisStab H e i) ⊓
        Submodule.span (ZMod p) (Set.range fun k => (b k : U))))
    (hF_b : ∀ g' ∈ F, ∀ j, ∃ j', (Submodule.span (ZMod p)
      {((b j : HardMathSupport.Kantor79.commutatorSpace F) : U)}).map
        (g' : U →ₗ[ZMod p] U) = Submodule.span (ZMod p)
      {((b j' : HardMathSupport.Kantor79.commutatorSpace F) : U)}) :
    ∀ g' ∈ F, ∀ X ∈ impFrameAt H e i
      (centralizerSpace (basisStab H e i) ⊓
        Submodule.span (ZMod p) (Set.range fun k => (b k : U))),
      X.map (g' : U →ₗ[ZMod p] U) ∈ impFrameAt H e i
        (centralizerSpace (basisStab H e i) ⊓
          Submodule.span (ZMod p) (Set.range fun k => (b k : U))) := by
  intro g' hg' X hX
  obtain ⟨j, hj⟩ := hXb X hX
  obtain ⟨j', hj'⟩ := hF_b g' hg' j
  rw [hj, hj']
  exact hb_lines j'

private lemma zs4j_perm_impFrameAt (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (i : Fin (Module.finrank (ZMod p) U - 1))
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hKF : basisStab H e i ≤ F)
    {b : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F)}
    (hbmon : ∀ y ∈ movedGroup F, ∃ (σ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)))
      (c : Fin (Module.finrank (ZMod p) U - 1) → ZMod p), (∀ k, c k ≠ 0) ∧
      ∀ k, y (b k) = c k • b (σ k))
    {g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))}
    {k₀ k₁ : Fin (Module.finrank (ZMod p) U - 2)} (hk : k₀ ≠ k₁)
    (hgline : ∀ k, ∃ j, j ≠ i ∧
      ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
      ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U))
    (hgmono1 : movedGroup H = gmmn p e j₀ j₁ ζ →
      movedGroup (basisStab H e i) = gmmn p g k₀ k₁ ζ)
    (hgmono2 : movedGroup H = g2mmn p e j₀ j₁ ζ →
      movedGroup (basisStab H e i) = g2mmn p g k₀ k₁ ζ) :
    ∀ g' ∈ F, ∀ X ∈ impFrameAt H e i
      (centralizerSpace (basisStab H e i) ⊓
        Submodule.span (ZMod p) (Set.range fun k => (b k : U))),
      X.map (g' : U →ₗ[ZMod p] U) ∈ impFrameAt H e i
        (centralizerSpace (basisStab H e i) ⊓
          Submodule.span (ZMod p) (Set.range fun k => (b k : U))) := by
  have hb_li := zs4j_linearIndependent_b (F := F) (b := b)
  have hle_b := zs4j_commutatorSpace_le_span_b (F := F) (b := b) i hKF
  have hmonH := zs4j_monomial_on_b (F := F) (b := b) i hKF hbmon
  have hspan_eq := zs4j_span_eq_lines (F := F) (b := b) hp S hM i hb_li hmonH hle_b hk
    hgmono1 hgmono2
  obtain ⟨hlines, j₂, hMline⟩ := hspan_eq
  let f : Fin (Module.finrank (ZMod p) U - 2) → Fin (Module.finrank (ZMod p) U - 1) :=
    fun k => Classical.choose (hlines k)
  have hf_spec : ∀ k, Submodule.span (ZMod p)
      {((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U)} =
      Submodule.span (ZMod p)
        {((b (f k) : HardMathSupport.Kantor79.commutatorSpace F) : U)} :=
    fun k => Classical.choose_spec (hlines k)
  obtain ⟨psie, hpsi_val⟩ := zs4j_psi_bij S i hgline
  have hf_inj := zs4j_f_inj (F := F) (b := b) (g := g) i f hf_spec
  have hj₂_notmem := zs4j_j2_notmem (F := F) (b := b) (g := g) (f := f) hp S i hf_spec hMline
  have hcount := zs4j_count S hf_inj hj₂_notmem
  have hb_lines := zs4j_b_lines_mem (F := F) (b := b) (g := g) (f := f) hp S i hf_spec hMline
    hcount hgline
  exact zs4j_hperm_final i (zs4j_impFrameAt_b i hf_spec hMline hpsi_val) hb_lines
    (zs4j_F_b hbmon)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_reflGen_closure_insert (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U} (har : IsRefl p a) :
    ReflGen p (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))) := by
  let X : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))
  change ReflGen p X
  have hgX : a ∈ X := Subgroup.subset_closure (Set.mem_insert a _)
  have hHX : basisStab H e i ≤ X := fun h hh =>
    Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have hSH : basisStab H e i ≤
      Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} := by
    rw [reflGen_basisStab S i]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htH, htr⟩
    exact Subgroup.subset_closure ⟨hHX htH, htr⟩
  change X = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t}
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun _ hx => hx.1)
  change Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))) ≤ _
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hxH
  · exact Subgroup.subset_closure ⟨hgX, har⟩
  · exact hSH hxH

private lemma zs4j_finrank_centralizerSpace_basisStab (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) :
    Module.finrank (ZMod p) (centralizerSpace (basisStab H e i)) = 2 := by
  have hsum2 := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i))
    (centralizerSpace (basisStab H e i))
  rw [(splitSupport_basisStab hp S i).1.sup_eq_top, finrank_top,
    (splitSupport_basisStab hp S i).1.inf_eq_bot, finrank_bot, add_zero] at hsum2
  rw [(splitSupport_basisStab hp S i).2.1] at hsum2
  have h4 := S.four_le_finrank
  omega

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_basisStab_commutatorSpace_le (_S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hKF : basisStab H e i ≤ F) :
    HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) ≤
      HardMathSupport.Kantor79.commutatorSpace F := by
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
  rintro w ⟨k, hk', v, rfl⟩
  exact Submodule.subset_span ⟨k, hKF hk', v, rfl⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_sup_centralizerSpace_commutatorSpace (hp : p ≠ 2)
    (S : ImpExtStd G H d e j₀ j₁ ζ) (i : Fin (Module.finrank (ZMod p) U - 1))
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hle : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) ≤
      HardMathSupport.Kantor79.commutatorSpace F) :
    centralizerSpace (basisStab H e i) ⊔ HardMathSupport.Kantor79.commutatorSpace F = ⊤ := by
  rw [eq_top_iff, ← (splitSupport_basisStab hp S i).1.sup_eq_top, sup_comm]
  exact sup_le_sup_left hle _

private lemma zs4j_finrank_inf_commutatorSpace (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hKF : basisStab H e i ≤ F)
    (hfinF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) =
      Module.finrank (ZMod p) U - 1) :
    Module.finrank (ZMod p) ↥(centralizerSpace (basisStab H e i) ⊓
      HardMathSupport.Kantor79.commutatorSpace F) = 1 := by
  have hsupU := zs4j_sup_centralizerSpace_commutatorSpace hp S i
    (zs4j_basisStab_commutatorSpace_le S i hKF)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (centralizerSpace (basisStab H e i)) (HardMathSupport.Kantor79.commutatorSpace F)
  rw [hsupU, finrank_top] at hsum
  have hCB := zs4j_finrank_centralizerSpace_basisStab hp S i
  have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
  omega

theorem frame_of_imprimitive (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (i : Fin (Module.finrank (ZMod p) U - 1))
    {a : U ≃ₗ[ZMod p] U} (_ha : a ∈ G) (har : IsRefl p a)
    (hF : SplitSupport (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1))
    (himp : Quasithin.SimsG4.IsImprimitiveOnV
      (movedGroup (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))))) :
    ∃ M : Submodule (ZMod p) U, M ≤ centralizerSpace (basisStab H e i) ∧
      Module.finrank (ZMod p) M = 1 ∧
      ∀ g ∈ Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))),
        ∀ X ∈ impFrameAt H e i M, X.map (g : U →ₗ[ZMod p] U) ∈ impFrameAt H e i M := by
  classical
  let F := Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))
  have hgenF : ReflGen p F := zs4j_reflGen_closure_insert S i har
  have hirrF : AbsIrred p (movedGroup F) := absIrred_movedGroup hgenF hF
  have hgen_mono : movedGroup F = Subgroup.closure {r | r ∈ movedGroup F ∧ GGLinRefl r} :=
    reflGen_movedGroup hgenF
  have hn : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) =
      Module.finrank (ZMod p) U - 1 := hF.2.1
  obtain ⟨b, hbmon⟩ := ggRC_monomial_of_imprimitive hn (movedGroup F) hirrF hgen_mono himp
  obtain ⟨g, k₀, k₁, hk, hgline, hgmono1, hgmono2⟩ := exists_basis_basisStab hp S i
  let M := centralizerSpace (basisStab H e i) ⊓
    Submodule.span (ZMod p) (Set.range fun k => (b k : U))
  have hM_le : M ≤ centralizerSpace (basisStab H e i) := inf_le_left
  have hM_finrank : Module.finrank (ZMod p) M = 1 := by
    have hspan := zs4j_span_range_b (F := F) (b := b)
    have hM_eq : M = centralizerSpace (basisStab H e i) ⊓
        HardMathSupport.Kantor79.commutatorSpace F := by
      rw [← hspan]
    rw [hM_eq]
    exact zs4j_finrank_inf_commutatorSpace hp S i
      (fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem a hh)) hn
  have hperm := zs4j_perm_impFrameAt hp S hM i
    (fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem a hh)) hbmon hk hgline
    hgmono1 hgmono2
  exact ⟨M, hM_le, hM_finrank, hperm⟩


private theorem exists_map_not_mem_aux (_hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (I : ImpExtInputs G H) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (har : IsRefl p a)
    (haH : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c)
    (hcon : ∀ j, ∃ k, (Submodule.span (ZMod p)
        {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
        (a : U →ₗ[ZMod p] U) =
      Submodule.span (ZMod p) {((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)}) :
    False := by
  have hmap_le : (HardMathSupport.Kantor79.commutatorSpace H).map (a : U →ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    have hVH_eq : HardMathSupport.Kantor79.commutatorSpace H =
        Submodule.span (ZMod p)
          (Set.range fun i => ((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)) := by
      have h := congrArg (Submodule.map
        (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace H))) e.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top] at h
      rw [← Set.range_comp] at h
      exact h.symm
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [hVH_eq] at hv
    change a v ∈ HardMathSupport.Kantor79.commutatorSpace H
    refine Submodule.span_induction (p := fun x _ =>
      a x ∈ HardMathSupport.Kantor79.commutatorSpace H) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hcon j
      have haej : a ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) ∈
          Submodule.span (ZMod p)
            {((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)} := by
        rw [← hk]
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
      exact (Submodule.span_singleton_le_iff_mem
        ((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)
        (HardMathSupport.Kantor79.commutatorSpace H)).mpr (e k).2 haej
    · simp
    · intro x y hx hy hax hay
      rw [map_add]
      exact Submodule.add_mem _ hax hay
    · intro c x hx hax
      rw [map_smul]
      exact Submodule.smul_mem _ c hax
  have hmap : (HardMathSupport.Kantor79.commutatorSpace H).map (a : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace H := by
    refine Submodule.eq_of_le_of_finrank_eq hmap_le ?_
    exact LinearEquiv.finrank_map_eq a (HardMathSupport.Kantor79.commutatorSpace H)
  exact haH (ImpExtSetting.mem_mul_centralizer_of_map_eq S.toImpExtSetting I.lemmaOneSeven
    ha har (Or.inl hmap))

theorem exists_map_not_mem (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) (I : ImpExtInputs G H)
    {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (har : IsRefl p a)
    (haH : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c) :
    ∃ j, ∀ k,
      (Submodule.span (ZMod p) {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
        (a : U →ₗ[ZMod p] U) ≠
      Submodule.span (ZMod p) {((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)} := by
  by_contra hcon
  push Not at hcon
  exact exists_map_not_mem_aux hp S I ha har haH hcon

private lemma zs4j_finrank_span_sup_centralizerSpace (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) :
    Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) {((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)} ⊔
        centralizerSpace H) = 2 := by
  have hinf : Submodule.span (ZMod p)
      {((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)} ⊓ centralizerSpace H = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv.1
    have hmem : c • ((e i : HardMathSupport.Kantor79.commutatorSpace H) : U) ∈
        HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.smul_mem _ c (e i).2
    have hmem' : c • ((e i : HardMathSupport.Kantor79.commutatorSpace H) : U) ∈
        HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H := ⟨hmem, hv.2⟩
    rw [S.splitSupport.1.inf_eq_bot] at hmem'
    simpa using hmem'
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod p) {((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)})
    (centralizerSpace H)
  rw [hinf, finrank_bot, add_zero] at hsum
  rw [hsum, finrank_span_singleton (by
    intro h
    exact e.ne_zero i (Subtype.ext h)),
    ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting]

private lemma centralizerSpace_basisStab_eq (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) :
    centralizerSpace (basisStab H e i) =
      Submodule.span (ZMod p) {((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)} ⊔
        centralizerSpace H := by
  have hle : Submodule.span (ZMod p) {((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)} ⊔
      centralizerSpace H ≤ centralizerSpace (basisStab H e i) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, mem_centralizerSpace]
      intro g hg
      exact MulAction.mem_stabilizer_iff.mp hg.2
    · intro v hv
      rw [mem_centralizerSpace] at hv ⊢
      intro g hg
      exact hv g hg.1
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [zs4j_finrank_span_sup_centralizerSpace S i, zs4j_finrank_centralizerSpace_basisStab hp S i]

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_smul_sub_eq_zero (S : ImpExtStd G H d e j₀ j₁ ζ)
    {i₁ i₂ : Fin (Module.finrank (ZMod p) U - 1)} {a b : ZMod p} {v w₁ w₂ : U}
    (hw₁ : w₁ ∈ centralizerSpace H) (hw₂ : w₂ ∈ centralizerSpace H)
    (hxw₁ : a • ((e i₁ : HardMathSupport.Kantor79.commutatorSpace H) : U) + w₁ = v)
    (hxw₂ : b • ((e i₂ : HardMathSupport.Kantor79.commutatorSpace H) : U) + w₂ = v) :
    a • ((e i₁ : HardMathSupport.Kantor79.commutatorSpace H) : U) -
      b • ((e i₂ : HardMathSupport.Kantor79.commutatorSpace H) : U) = 0 := by
  have hmem : a • ((e i₁ : HardMathSupport.Kantor79.commutatorSpace H) : U) -
      b • ((e i₂ : HardMathSupport.Kantor79.commutatorSpace H) : U) ∈
      HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H := by
    refine ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ a (e i₁).2)
        (Submodule.smul_mem _ b (e i₂).2)
    · have h1' : a • ((e i₁ : HardMathSupport.Kantor79.commutatorSpace H) : U) = v - w₁ := by
        rw [← hxw₁]; abel
      have h2' : b • ((e i₂ : HardMathSupport.Kantor79.commutatorSpace H) : U) = v - w₂ := by
        rw [← hxw₂]; abel
      have hsub : a • ((e i₁ : HardMathSupport.Kantor79.commutatorSpace H) : U) -
          b • ((e i₂ : HardMathSupport.Kantor79.commutatorSpace H) : U) = w₂ - w₁ := by
        rw [h1', h2']; abel
      rw [hsub]
      exact Submodule.sub_mem _ hw₂ hw₁
  rw [S.splitSupport.1.inf_eq_bot] at hmem
  simpa using hmem

private lemma centralizerSpace_basisStab_inf_le (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    {i₁ i₂ : Fin (Module.finrank (ZMod p) U - 1)} (hi : i₁ ≠ i₂) :
    centralizerSpace (basisStab H e i₁) ⊓ centralizerSpace (basisStab H e i₂) ≤
      centralizerSpace H := by
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [centralizerSpace_basisStab_eq hp S i₁, centralizerSpace_basisStab_eq hp S i₂] at hv
  have h1 := hv.1
  have h2 := hv.2
  rw [Submodule.mem_sup] at h1 h2
  obtain ⟨x₁, hx₁, w₁, hw₁, hxw₁⟩ := h1
  obtain ⟨x₂, hx₂, w₂, hw₂, hxw₂⟩ := h2
  rw [Submodule.mem_span_singleton] at hx₁ hx₂
  obtain ⟨a, rfl⟩ := hx₁
  obtain ⟨b, rfl⟩ := hx₂
  have hzero := zs4j_smul_sub_eq_zero S hw₁ hw₂ hxw₁ hxw₂
  have hzero' : a • (e i₁ : HardMathSupport.Kantor79.commutatorSpace H) -
      b • (e i₂ : HardMathSupport.Kantor79.commutatorSpace H) = 0 := by
    refine Subtype.ext ?_
    simpa using hzero
  have ha0 : a = 0 := by
    have h2 := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace H => e.repr w i₁) hzero'
    simp only [map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply,
      Finsupp.smul_apply, Finsupp.single_eq_same] at h2
    simpa [hi] using h2
  have hv' : v = w₁ := by
    rw [← hxw₁]
    simp [ha0]
  rw [hv']
  exact hw₁

omit [Module.Finite (ZMod p) U] in
private lemma impFrameAt_centralizerSpace_subset (_S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) :
    impFrameAt H e i (centralizerSpace H) ⊆ impFrame H e := by
  intro X hX
  rw [impFrameAt] at hX
  rcases hX with hX | ⟨k, _hk, hX⟩
  · rw [hX]; exact Set.mem_insert _ _
  · rw [hX, impFrame]; exact Set.mem_insert_of_mem _ (Set.mem_range_self k)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_map_line_eq {a : U ≃ₗ[ZMod p] U} {i j : Fin (Module.finrank (ZMod p) U - 1)}
    (hj : j ≠ i)
    (hja : ∀ k,
      (Submodule.span (ZMod p) {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
        (a : U →ₗ[ZMod p] U) ≠
      Submodule.span (ZMod p) {((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)})
    {M : Submodule (ZMod p) U}
    (ha : ∀ X ∈ impFrameAt H e i M, X.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i M) :
    (Submodule.span (ZMod p)
        {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
      (a : U →ₗ[ZMod p] U) = M := by
  have hmem : (Submodule.span (ZMod p)
        {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
      (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i M :=
    ha _ (by
      rw [impFrameAt]
      exact Set.mem_insert_of_mem _ ⟨j, hj, rfl⟩)
  rw [impFrameAt] at hmem
  rcases hmem with hmem | ⟨k, _hk, hk'⟩
  · exact hmem
  · exact absurd hk' (hja k)

private lemma zs4j_map_line_eq_centralizerSpace (S : ImpExtStd G H d e j₀ j₁ ζ)
    {a : U ≃ₗ[ZMod p] U} {j : Fin (Module.finrank (ZMod p) U - 1)}
    (hle : (Submodule.span (ZMod p)
        {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
      (a : U →ₗ[ZMod p] U) ≤ centralizerSpace H) :
    (Submodule.span (ZMod p)
        {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
      (a : U →ₗ[ZMod p] U) = centralizerSpace H := by
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearEquiv.finrank_map_eq, ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting]
  exact finrank_span_singleton (by
    intro h
    exact e.ne_zero j (Subtype.ext h))

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_map_mem_impFrame_of_centralizerSpace (S : ImpExtStd G H d e j₀ j₁ ζ)
    {a : U ≃ₗ[ZMod p] U} {i₁ i₂ : Fin (Module.finrank (ZMod p) U - 1)} (hi : i₁ ≠ i₂)
    (ha₁ : ∀ X ∈ impFrameAt H e i₁ (centralizerSpace H),
      X.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i₁ (centralizerSpace H))
    (ha₂ : ∀ X ∈ impFrameAt H e i₂ (centralizerSpace H),
      X.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i₂ (centralizerSpace H)) :
    ∀ X ∈ impFrame H e, X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e := by
  intro X hX
  rw [impFrame] at hX ⊢
  rcases hX with hX | ⟨k, hX⟩
  · have hmem : X ∈ impFrameAt H e i₁ (centralizerSpace H) := by
      rw [impFrameAt]
      left
      exact hX
    exact impFrameAt_centralizerSpace_subset S i₁ (ha₁ X hmem)
  · by_cases hk : k = i₁
    · rw [hk] at hX
      have hmem : X ∈ impFrameAt H e i₂ (centralizerSpace H) := by
        rw [impFrameAt]
        exact Set.mem_insert_of_mem _ ⟨i₁, hi, hX.symm⟩
      exact impFrameAt_centralizerSpace_subset S i₂ (ha₂ X hmem)
    · have hmem : X ∈ impFrameAt H e i₁ (centralizerSpace H) := by
        rw [impFrameAt]
        exact Set.mem_insert_of_mem _ ⟨k, hk, hX.symm⟩
      exact impFrameAt_centralizerSpace_subset S i₁ (ha₁ X hmem)

theorem map_mem_impFrame_of_two (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    {a : U ≃ₗ[ZMod p] U} {i₁ i₂ j : Fin (Module.finrank (ZMod p) U - 1)} (hi : i₁ ≠ i₂)
    (hj₁ : j ≠ i₁) (hj₂ : j ≠ i₂)
    (hja : ∀ k,
      (Submodule.span (ZMod p) {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
        (a : U →ₗ[ZMod p] U) ≠
      Submodule.span (ZMod p) {((e k : HardMathSupport.Kantor79.commutatorSpace H) : U)})
    {M₁ M₂ : Submodule (ZMod p) U} (hM₁ : M₁ ≤ centralizerSpace (basisStab H e i₁))
    (hM₂ : M₂ ≤ centralizerSpace (basisStab H e i₂))
    (ha₁ : ∀ X ∈ impFrameAt H e i₁ M₁, X.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i₁ M₁)
    (ha₂ : ∀ X ∈ impFrameAt H e i₂ M₂, X.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i₂ M₂) :
    ∀ X ∈ impFrame H e, X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e := by
  have hLj1 := zs4j_map_line_eq hj₁ hja ha₁
  have hLj2 := zs4j_map_line_eq hj₂ hja ha₂
  have hM12 : M₁ = M₂ := hLj1.symm.trans hLj2
  have hL_eq := zs4j_map_line_eq_centralizerSpace S (a := a) (j := j) (by
    rw [hLj1]
    exact le_trans (le_inf hM₁ (hM12 ▸ hM₂)) (centralizerSpace_basisStab_inf_le hp S hi))
  rw [hLj1.symm.trans hL_eq] at ha₁
  rw [hLj2.symm.trans hL_eq] at ha₂
  exact zs4j_map_mem_impFrame_of_centralizerSpace S hi ha₁ ha₂

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_exists_monomial_action (S : ImpExtStd G H d e j₀ j₁ ζ) {h : U ≃ₗ[ZMod p] U}
    (hh : h ∈ H) (j : Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ σ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)),
      ∃ d : Fin (Module.finrank (ZMod p) U - 1) → (ZMod p)ˣ,
      h ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) =
        (d (σ j) : ZMod p) • ((e (σ j) : HardMathSupport.Kantor79.commutatorSpace H) : U) := by
  let φ := restrictHom H (HardMathSupport.Kantor79.commutatorSpace H)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hφ : φ ⟨h, hh⟩ ∈ movedGroup H := ⟨⟨h, hh⟩, rfl⟩
  rcases S.mono with hmono | hmono
  · have hg : φ ⟨h, hh⟩ ∈ gmmn p e j₀ j₁ ζ := by rwa [← hmono]
    obtain ⟨d, σ, _hd, _hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn e S.ne hg
    refine ⟨σ, d, ?_⟩
    have h1 := congrArg (fun g : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H => g (e j)) hgeq
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis] at h1
    have h2 := congrArg (fun v : HardMathSupport.Kantor79.commutatorSpace H => (v : U)) h1
    simpa [φ, restrictHom_apply, map_smul] using h2
  · have hg : φ ⟨h, hh⟩ ∈ g2mmn p e j₀ j₁ ζ := by rwa [← hmono]
    obtain ⟨d, σ, _hd, _hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn e S.ne hg
    refine ⟨σ, d, ?_⟩
    have h1 := congrArg (fun g : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H => g (e j)) hgeq
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis] at h1
    have h2 := congrArg (fun v : HardMathSupport.Kantor79.commutatorSpace H => (v : U)) h1
    simpa [φ, restrictHom_apply, map_smul] using h2

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_exists_restrict_centralizer {c : U ≃ₗ[ZMod p] U}
    (hc : c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    ∃ T : Module.End (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H),
      (∀ v, ((T v : HardMathSupport.Kantor79.commutatorSpace H) : U) = c (v : U)) ∧
      ∀ g ∈ movedGroup H,
        T ∘ₗ (g : (HardMathSupport.Kantor79.commutatorSpace H) →ₗ[ZMod p]
          (HardMathSupport.Kantor79.commutatorSpace H)) =
        (g : (HardMathSupport.Kantor79.commutatorSpace H) →ₗ[ZMod p]
          (HardMathSupport.Kantor79.commutatorSpace H)) ∘ₗ T := by
  have hmap_c : (HardMathSupport.Kantor79.commutatorSpace H).map (c : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace H :=
    map_commutatorSpace_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer (H : Set (U ≃ₗ[ZMod p] U)) hc)
  let T : Module.End (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) :=
    { toFun := fun v => ⟨c (v : U), by
        have hmem : c (v : U) ∈ (HardMathSupport.Kantor79.commutatorSpace H).map
            (c : U →ₗ[ZMod p] U) := Submodule.mem_map_of_mem v.2
        rwa [hmap_c] at hmem⟩
      map_add' := by intro u v; ext; simp [map_add]
      map_smul' := by intro r v; ext; simp [map_smul] }
  refine ⟨T, fun v => rfl, ?_⟩
  rintro g ⟨x, rfl⟩
  ext v
  have hcomm : c * (x : U ≃ₗ[ZMod p] U) = (x : U ≃ₗ[ZMod p] U) * c :=
    ((Subgroup.mem_centralizer_iff.mp hc) x x.2).symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, restrictHom_apply]
  exact congrArg (fun f : U ≃ₗ[ZMod p] U => f (v : U)) hcomm

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_ne_zero_of_apply_eq_smul {c : U ≃ₗ[ZMod p] U} {v : U} (hv : v ≠ 0)
    {lam : ZMod p} (h : c v = lam • v) : lam ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h
  exact hv (c.injective (h.trans (map_zero c).symm))

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_exists_scalar_centralizer (S : ImpExtStd G H d e j₀ j₁ ζ)
    {c : U ≃ₗ[ZMod p] U} (hc : c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (j : Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ lam : ZMod p, lam ≠ 0 ∧
      c ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) =
        lam • ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) := by
  obtain ⟨T, hT, hTcomm⟩ := zs4j_exists_restrict_centralizer hc
  obtain ⟨lam, hlam⟩ := (absIrred_movedGroup S.reflGen_H S.splitSupport).2 T hTcomm
  have h1 := congrArg (fun f : Module.End (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace H) => f (e j)) hlam
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at h1
  have h2 : c ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) =
      lam • ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) :=
    (hT _).symm.trans
      (congrArg (fun v : HardMathSupport.Kantor79.commutatorSpace H => (v : U)) h1)
  exact ⟨lam, zs4j_ne_zero_of_apply_eq_smul (fun h0 => e.ne_zero j (Subtype.ext h0)) h2, h2⟩

omit [Module.Finite (ZMod p) U] in
private lemma map_mem_impFrame_of_mem_mul_coord (_hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    {a : U ≃ₗ[ZMod p] U}
    (haH : ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c)
    (j : Fin (Module.finrank (ZMod p) U - 1)) :
    (Submodule.span (ZMod p) {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
      (a : U →ₗ[ZMod p] U) ∈ impFrame H e := by
  rcases haH with ⟨h, hh, c, hc, rfl⟩
  obtain ⟨σ, d, hh_action⟩ := zs4j_exists_monomial_action S hh j
  obtain ⟨lam, hlam, hc_action⟩ := zs4j_exists_scalar_centralizer S hc j
  rw [impFrame]
  refine Set.mem_insert_of_mem _ ?_
  rw [Submodule.map_span, Set.image_singleton]
  refine Set.mem_range.mpr ⟨σ j, ?_⟩
  have hmain : ((h * c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) =
      (lam * (d (σ j) : ZMod p)) •
        ((e (σ j) : HardMathSupport.Kantor79.commutatorSpace H) : U) := by
    rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply]
    change (h : U →ₗ[ZMod p] U) (c ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) =
      (lam * (d (σ j) : ZMod p)) • ((e (σ j) : HardMathSupport.Kantor79.commutatorSpace H) : U)
    rw [hc_action, map_smul]
    change lam • h ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) =
      (lam * (d (σ j) : ZMod p)) • ((e (σ j) : HardMathSupport.Kantor79.commutatorSpace H) : U)
    rw [hh_action, smul_smul]
  rw [hmain]
  exact (Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (mul_ne_zero hlam (Units.ne_zero (d (σ j))))) _).symm

theorem map_mem_impFrame_of_mem_mul (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    {a : U ≃ₗ[ZMod p] U}
    (haH : ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c) :
    ∀ X ∈ impFrame H e, X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e := by
  rintro X hX
  rw [impFrame] at hX ⊢
  rcases hX with hX | ⟨j, hX⟩
  · subst hX
    rcases haH with ⟨h, hh, c, hc, rfl⟩
    have hmap : (centralizerSpace H).map ((h * c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        centralizerSpace H := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.map_le_iff_le_comap]
        intro v hv
        rw [Submodule.mem_comap]
        rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply]
        change h (c v) ∈ centralizerSpace H
        have hcv : c v ∈ centralizerSpace H := by
          rw [mem_centralizerSpace] at hv ⊢
          intro g hg
          have hcomm : c * g = g * c :=
            ((Subgroup.mem_centralizer_iff.mp hc) g hg).symm
          calc g (c v) = (g * c) v := (LinearEquiv.mul_apply g c v).symm
            _ = (c * g) v := by rw [hcomm.symm]
            _ = c (g v) := LinearEquiv.mul_apply c g v
            _ = c v := by rw [hv g hg]
        rw [mem_centralizerSpace] at hcv ⊢
        intro g hg
        rw [hcv h hh]
        exact hcv g hg
      · rw [LinearEquiv.finrank_map_eq]
    rw [hmap]
    exact Set.mem_insert _ _
  · subst hX
    exact map_mem_impFrame_of_mem_mul_coord hp S haH j

theorem fix_or_frame (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (I : ImpExtInputs G H)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G)
    (har : IsRefl p a)
    (haH : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c) :
    (∀ j, j ≠ i → a ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U) = e j) ∨
      ∃ M ≤ centralizerSpace (basisStab H e i),
        ∀ X ∈ impFrameAt H e i M, X.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i M := by
  by_cases hai : ∃ h ∈ basisStab H e i,
      ∃ c ∈ Subgroup.centralizer (basisStab H e i : Set (U ≃ₗ[ZMod p] U)), a = h * c
  · exact Or.inl (fix_of_mem_mul_basisStab hp S I i ha har haH hai)
  · refine Or.inr ?_
    let F := Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))
    have hF : SplitSupport F (Module.finrank (ZMod p) U - 1) := by
      rcases lt_or_ge p 5 with hp5 | hp5
      · have hprime : p.Prime := Fact.out
        have hp3 : p = 3 := by
          have h2 := hprime.two_le
          have hne4 : p ≠ 4 := by
            intro h4
            rw [h4] at hprime
            norm_num at hprime
          omega
        exact splitSupport_closure_of_three S hp3 hM I i ha har hai
      · exact splitSupport_closure_of_five_le S hp5 I i ha har hai
    by_cases hFp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup F)
    · obtain ⟨M, hMle, _, hperm⟩ := frame_of_imprimitive hp S hM i ha har hF hFp
      exact ⟨M, hMle, fun X hX =>
        hperm a (Subgroup.subset_closure (Set.mem_insert a _)) X hX⟩
    · rcases primitive_cases hp S hM I i ha har hF hFp with ⟨hn4, hd5, h3⟩ | ⟨hn5, hcF, hcH⟩
      · obtain ⟨f, lam, a₁, a₂, a₃, K, h43⟩ :=
          exists_fourThreeData hp S I hn4 hd5 i ha har haH hF h3
        exact (FourThreeData.false hp h43).elim
      · exact (false_of_card_eq_1152 hp S i ha har hn5 hF hcF hcH).elim

theorem map_mem_impFrame (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (I : ImpExtInputs G H) :
    ∀ a ∈ G, IsRefl p a → ∀ X ∈ impFrame H e, X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e := by
  intro a ha har X hX
  by_cases haH : ∃ h ∈ H,
      ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c
  · exact map_mem_impFrame_of_mem_mul hp S haH X hX
  · obtain ⟨j, hj⟩ := exists_map_not_mem hp S I ha har haH
    have hl : 3 ≤ Module.finrank (ZMod p) U - 1 := by
      have h4 := S.four_le_finrank; omega
    let s : Finset (Fin (Module.finrank (ZMod p) U - 1)) := Finset.univ.erase j
    have hscard : 1 < s.card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i₁, hi₁, i₂, hi₂, hi12⟩ := Finset.one_lt_card.mp hscard
    have hi₁j : i₁ ≠ j := (Finset.mem_erase.mp hi₁).1
    have hi₂j : i₂ ≠ j := (Finset.mem_erase.mp hi₂).1
    have hcase : ∀ i, i ≠ j → ∃ M ≤ centralizerSpace (basisStab H e i),
        ∀ Y ∈ impFrameAt H e i M, Y.map (a : U →ₗ[ZMod p] U) ∈ impFrameAt H e i M := by
      intro i hij
      rcases fix_or_frame hp S hM I i ha har haH with h | h
      · exfalso
        have hmap : (Submodule.span (ZMod p)
            {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}).map
              (a : U →ₗ[ZMod p] U) = Submodule.span (ZMod p)
            {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)} := by
          rw [Submodule.map_span, Set.image_singleton]
          change Submodule.span (ZMod p)
            {a ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)} =
            Submodule.span (ZMod p)
              {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}
          rw [h j hij.symm]
        exact (hj j) hmap
      · exact h
    obtain ⟨M₁, hM₁, ha₁⟩ := hcase i₁ hi₁j
    obtain ⟨M₂, hM₂, ha₂⟩ := hcase i₂ hi₂j
    exact map_mem_impFrame_of_two hp S hi12 hi₁j.symm hi₂j.symm hj hM₁ hM₂ ha₁ ha₂ X hX

private noncomputable def frameFamily (_S : ImpExtStd G H d e j₀ j₁ ζ) :
    Option (Fin (Module.finrank (ZMod p) U - 1)) → Submodule (ZMod p) U :=
  fun o => match o with
    | none => centralizerSpace H
    | some j => Submodule.span (ZMod p)
        {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)}

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_closure_maps_impFrame (_S : ImpExtStd G H d e j₀ j₁ ζ)
    (h : ∀ a ∈ G, IsRefl p a → ∀ X ∈ impFrame H e,
      X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e) :
    ∀ g ∈ Subgroup.closure {t | t ∈ G ∧ IsRefl p t},
      (∀ X ∈ impFrame H e, X.map (g : U →ₗ[ZMod p] U) ∈ impFrame H e) ∧
      (∀ X ∈ impFrame H e, X.map ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∈ impFrame H e) := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    have htG : t ∈ G := ht.1
    have htr : IsRefl p t := ht.2
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htr.1
    refine ⟨h t htG htr, ?_⟩
    rw [htinv]
    exact h t htG htr
  | one =>
    refine ⟨?_, ?_⟩ <;> intro X hX <;> simpa using hX
  | mul x y hx hy ihx ihy =>
    refine ⟨?_, ?_⟩
    · intro X hX
      have h1 : X.map (y : U →ₗ[ZMod p] U) ∈ impFrame H e := ihy.1 X hX
      have h2 : (X.map (y : U →ₗ[ZMod p] U)).map (x : U →ₗ[ZMod p] U) ∈ impFrame H e :=
        ihx.1 _ h1
      have hxy : ((x * y : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
          (x : U →ₗ[ZMod p] U).comp (y : U →ₗ[ZMod p] U) := by
        ext a
        simp
      rw [hxy, Submodule.map_comp]
      exact h2
    · intro X hX
      have h1 : X.map ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∈ impFrame H e :=
        ihx.2 X hX
      have h2 : (X.map ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)).map
          ((y⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∈ impFrame H e := ihy.2 _ h1
      have hxy : ((((x * y : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
          ((y⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
            ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by
        rw [mul_inv_rev]
        ext a
        simp
      rw [hxy, Submodule.map_comp]
      exact h2
  | inv x hx ihx =>
    refine ⟨ihx.2, ?_⟩
    rw [inv_inv]
    exact ihx.1

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_G_maps_impFrame (S : ImpExtStd G H d e j₀ j₁ ζ)
    (h : ∀ a ∈ G, IsRefl p a → ∀ X ∈ impFrame H e,
      X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e) :
    ∀ g ∈ G, ∀ X ∈ impFrame H e, X.map (g : U →ₗ[ZMod p] U) ∈ impFrame H e := by
  intro g hg
  rw [S.reflGen] at hg
  exact (zs4j_closure_maps_impFrame S h g hg).1

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_frameFamily_range (S : ImpExtStd G H d e j₀ j₁ ζ) :
    Set.range (frameFamily S) = impFrame H e := by
  ext X
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Set.mem_insert _ _
    | some j => exact Set.mem_insert_of_mem _ (Set.mem_range_self j)
  · intro hX
    rw [impFrame] at hX
    rcases hX with hX | ⟨j, hj⟩
    · exact ⟨none, by rw [hX]; rfl⟩
    · refine ⟨some j, ?_⟩
      simpa [frameFamily] using hj

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_frameFamily_perm (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hG : ∀ g ∈ G, ∀ X ∈ impFrame H e, X.map (g : U →ₗ[ZMod p] U) ∈ impFrame H e)
    (hrange : Set.range (frameFamily S) = impFrame H e) :
    ∀ g ∈ G, ∀ o, ∃ o', ((frameFamily S) o).map (g : U →ₗ[ZMod p] U) =
      (frameFamily S) o' := by
  intro g hg o
  have hWo : (frameFamily S) o ∈ impFrame H e := by
    rw [← hrange]
    exact Set.mem_range_self o
  have hmem : ((frameFamily S) o).map (g : U →ₗ[ZMod p] U) ∈ impFrame H e :=
    hG g hg ((frameFamily S) o) hWo
  rw [← hrange] at hmem
  rcases hmem with ⟨o', ho'⟩
  exact ⟨o', ho'.symm⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_commutatorSpace_eq_span_e (_S : ImpExtStd G H d e j₀ j₁ ζ) :
    HardMathSupport.Kantor79.commutatorSpace H =
      Submodule.span (ZMod p) (Set.range fun j : Fin (Module.finrank (ZMod p) U - 1) =>
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) := by
  have h := congrArg (Submodule.map
    (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace H))) e.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top] at h
  rw [← Set.range_comp] at h
  exact h.symm

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_linearIndependent_e (_S : ImpExtStd G H d e j₀ j₁ ζ) :
    LinearIndependent (ZMod p)
      (fun j : Fin (Module.finrank (ZMod p) U - 1) =>
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) := by
  have h' := e.linearIndependent.map' (Submodule.subtype
    (HardMathSupport.Kantor79.commutatorSpace H)) (Submodule.ker_subtype _)
  simpa [Function.comp_def] using h'

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_v₀_notin (S : ImpExtStd G H d e j₀ j₁ ζ) {v₀ : U}
    (hv₀mem : v₀ ∈ centralizerSpace H) (hv₀ne : v₀ ≠ 0)
    (hVH_eq : HardMathSupport.Kantor79.commutatorSpace H =
      Submodule.span (ZMod p) (Set.range fun j : Fin (Module.finrank (ZMod p) U - 1) =>
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U))) :
    v₀ ∉ Submodule.span (ZMod p)
      (Set.range fun j : Fin (Module.finrank (ZMod p) U - 1) =>
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) := by
  intro hmem
  rw [← hVH_eq] at hmem
  have hinf : v₀ ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
    ⟨hmem, hv₀mem⟩
  rw [S.splitSupport.1.inf_eq_bot] at hinf
  exact hv₀ne (by simpa using hinf)

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_frameFamily_iSup (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hVH_eq : HardMathSupport.Kantor79.commutatorSpace H =
      Submodule.span (ZMod p) (Set.range fun j : Fin (Module.finrank (ZMod p) U - 1) =>
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U))) :
    (⨆ o, frameFamily S o) = ⊤ := by
  rw [iSup_option]
  have hnone : frameFamily S none = centralizerSpace H := rfl
  have hsome : (⨆ j : Fin (Module.finrank (ZMod p) U - 1), frameFamily S (some j)) =
      HardMathSupport.Kantor79.commutatorSpace H := by
    have heq : (fun j : Fin (Module.finrank (ZMod p) U - 1) => frameFamily S (some j)) =
        fun j => Submodule.span (ZMod p)
          {((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)} := by
      funext j
      rfl
    rw [heq, Submodule.iSup_span, Set.iUnion_singleton_eq_range]
    exact hVH_eq.symm
  rw [hnone, hsome, sup_comm, S.splitSupport.1.sup_eq_top]

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_frameFamily_ne_bot (S : ImpExtStd G H d e j₀ j₁ ζ) {v₀ : U}
    (hv₀span : centralizerSpace H = Submodule.span (ZMod p) {v₀}) (hv₀ne : v₀ ≠ 0) :
    ∀ o, frameFamily S o ≠ ⊥ := by
  let v : Option (Fin (Module.finrank (ZMod p) U - 1)) → U := fun o => match o with
    | none => v₀
    | some j => ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)
  have hWv : ∀ o, frameFamily S o = Submodule.span (ZMod p) {v o} := by
    intro o
    cases o with
    | none => exact hv₀span
    | some j => rfl
  have hv_ne : ∀ o, v o ≠ 0 := by
    intro o
    cases o with
    | none => simpa [v] using hv₀ne
    | some j =>
      intro hzero
      exact e.ne_zero j (Subtype.ext hzero)
  intro o h
  have hvo : v o = 0 := by
    have h' : Submodule.span (ZMod p) {v o} = ⊥ := by rw [← hWv o]; exact h
    rwa [Submodule.span_singleton_eq_bot] at h'
  exact hv_ne o hvo

omit [Module.Finite (ZMod p) U] in
private lemma zs4j_frameFamily_iSupIndep (S : ImpExtStd G H d e j₀ j₁ ζ) {v₀ : U}
    (hv₀span : centralizerSpace H = Submodule.span (ZMod p) {v₀})
    (hv₀mem : v₀ ∈ centralizerSpace H) (hv₀ne : v₀ ≠ 0)
    (hVH_eq : HardMathSupport.Kantor79.commutatorSpace H =
      Submodule.span (ZMod p) (Set.range fun j : Fin (Module.finrank (ZMod p) U - 1) =>
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U))) :
    iSupIndep (frameFamily S) := by
  let v : Option (Fin (Module.finrank (ZMod p) U - 1)) → U := fun o => match o with
    | none => v₀
    | some j => ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)
  have hWv : ∀ o, frameFamily S o = Submodule.span (ZMod p) {v o} := by
    intro o
    cases o with
    | none => exact hv₀span
    | some j => rfl
  have hli_e := zs4j_linearIndependent_e S
  have hv₀_notin := zs4j_v₀_notin S hv₀mem hv₀ne hVH_eq
  have hli : LinearIndependent (ZMod p) v := by
    rw [linearIndependent_option]
    refine ⟨?_, ?_⟩
    · convert hli_e using 1
      ext j
      rfl
    · intro hmem
      exact hv₀_notin (by simpa [v, Function.comp_def] using hmem)
  have hv_ne : ∀ o, v o ≠ 0 := by
    intro o
    cases o with
    | none => simpa [v] using hv₀ne
    | some j =>
      intro hzero
      exact e.ne_zero j (Subtype.ext hzero)
  have hW : frameFamily S = fun o => Submodule.span (ZMod p) {v o} := funext hWv
  rw [hW]
  exact (iSupIndep_iff_linearIndependent_of_ne_zero hv_ne).mpr hli

theorem isImprimitiveOnV_of_map_mem_impFrame (S : ImpExtStd G H d e j₀ j₁ ζ)
    (h : ∀ a ∈ G, IsRefl p a → ∀ X ∈ impFrame H e, X.map (a : U →ₗ[ZMod p] U) ∈ impFrame H e) :
    Quasithin.SimsG4.IsImprimitiveOnV G := by
  classical
  let l := Module.finrank (ZMod p) U - 1
  have hl : 3 ≤ l := by
    have h4 := S.four_le_finrank
    omega
  have hVH : centralizerSpace H ≠ ⊥ := by
    intro hbot
    have h1 := ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting
    rw [hbot, finrank_bot] at h1
    exact Nat.zero_ne_one h1
  obtain ⟨v₀, hv₀mem, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVH
  have hv₀span : centralizerSpace H = Submodule.span (ZMod p) {v₀} :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting) hv₀mem hv₀ne
  have hVH_eq := zs4j_commutatorSpace_eq_span_e S
  let v : Option (Fin l) → U := fun o => match o with
    | none => v₀
    | some j => ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)
  let W : Option (Fin l) → Submodule (ZMod p) U := frameFamily S
  have hWv : ∀ o, W o = Submodule.span (ZMod p) {v o} := by
    intro o
    cases o with
    | none => exact hv₀span
    | some j => rfl
  have hrange : Set.range W = impFrame H e := zs4j_frameFamily_range S
  have hU0 : ∀ o, W o ≠ ⊥ := zs4j_frameFamily_ne_bot S hv₀span hv₀ne
  have hind : iSupIndep W := zs4j_frameFamily_iSupIndep S hv₀span hv₀mem hv₀ne hVH_eq
  have hsup : (⨆ o, W o) = ⊤ := zs4j_frameFamily_iSup S hVH_eq
  have hG := zs4j_G_maps_impFrame S h
  have hperm : ∀ g ∈ G, ∀ o, ∃ o', (W o).map (g : U →ₗ[ZMod p] U) = W o' :=
    zs4j_frameFamily_perm S hG (zs4j_frameFamily_range S)
  have hι : 1 < Nat.card (Option (Fin l)) := by
    rw [Finite.card_option, Nat.card_fin]
    omega
  exact Quasithin.SimsG4.isImprimitiveOnV_of_family hι W hU0 hind hsup hperm

theorem impExtRowM (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) (I : ImpExtInputs G H) :
    ImpExtRowM H e j₀ j₁ ζ := by
  by_contra hM
  exact S.primitive (isImprimitiveOnV_of_map_mem_impFrame S (map_mem_impFrame hp S hM I))

end ImpExtStd

end CFSG.StandardType.ZS

end
