module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtPlaneLeaf
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem swapEquiv_mem_sup_even {t : ℕ} (ht : 3 ≤ t) {a c : Fin t} (hac : a ≠ c) :
    swapEquiv t c a ∈ evenSignedPermGroupOn t (Finset.univ.erase a) ⊔
      evenSignedPermGroupOn t (Finset.univ.erase c) := by
  classical
  obtain ⟨x, hxa, hxc⟩ : ∃ x : Fin t, x ≠ a ∧ x ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin t)) ⊆ {a, c} := fun i _ => by
      by_cases hia : i = a
      · simp [hia]
      · simp [hcon i hia]
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, c} : Finset (Fin t)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have h1 : swapEquiv t c x ∈ evenSignedPermGroupOn t (Finset.univ.erase a) :=
    Subgroup.subset_closure (Or.inl ⟨c, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ c⟩, x,
      Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩, rfl⟩)
  have h2 : swapEquiv t a x ∈ evenSignedPermGroupOn t (Finset.univ.erase c) :=
    Subgroup.subset_closure (Or.inl ⟨a, Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩, x,
      Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ x⟩, rfl⟩)
  have heq : swapEquiv t c a = swapEquiv t c x * swapEquiv t a x * swapEquiv t c x := by
    ext v k
    simp only [swapEquiv, LinearEquiv.mul_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, Function.comp_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
    (Subgroup.mem_sup_right h2)) (Subgroup.mem_sup_left h1)

theorem cartanD_succ {n : ℕ} (hn : 3 ≤ n) (p q : Fin n) :
    CartanMatrix.D (n + 1) p.succ q.succ = CartanMatrix.D n p q := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq, Fin.succ_mk]
  split_ifs <;> omega

private theorem exists_equiv_compl_image_zero {n : ℕ} {ι : Type} (f : Fin (n + 1) ≃ ι) :
    ∃ f' : Fin n ≃ {i // i ≠ f 0}, ∀ p, (f' p : ι) = f p.succ := by
  refine ⟨Equiv.ofBijective (fun p => ⟨f p.succ, ?_⟩) ⟨?_, ?_⟩, fun p => rfl⟩
  · exact fun h => Fin.succ_ne_zero p (f.injective h)
  · intro p q hpq
    exact Fin.succ_injective _ (f.injective (congrArg Subtype.val hpq))
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := f.surjective i
    have hj : j ≠ 0 := fun h => hi (by rw [h])
    obtain ⟨p, rfl⟩ := Fin.exists_succ_eq.mpr hj
    exact ⟨p, rfl⟩

theorem insideZero_inf_centZero {t : ℕ} (S : Finset (Fin t)) : insideZero S ⊓ centZero S = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  rw [Submodule.mem_bot]
  funext i
  by_cases hi : i ∈ S
  · exact (mem_centZero S v).mp h2 i hi
  · exact (mem_insideZero' S v).mp h1 i hi

theorem insideZero_sup_centZero {t : ℕ} (S : Finset (Fin t)) : insideZero S ⊔ centZero S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro v _
  refine Submodule.mem_sup.mpr ⟨fun i => if i ∈ S then v i else 0, ?_,
    fun i => if i ∈ S then 0 else v i, ?_, ?_⟩
  · exact (mem_insideZero' S _).mpr fun i hi => by simp [hi]
  · exact (mem_centZero S _).mpr fun i hi => by simp [hi]
  · funext i
    by_cases hi : i ∈ S <;> simp [hi]

theorem finrank_insideZero {t : ℕ} (S : Finset (Fin t)) : finrank F (insideZero S) = S.card := by
  classical
  let e : insideZero S ≃ₗ[F] (S → F) :=
    { toFun := fun v i => (v : V t) i
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl
      invFun := fun g => ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 0,
        (mem_insideZero' S _).mpr fun i hi => by simp [hi]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi]
        · simp [hi, (mem_insideZero' S _).mp v.2 i hi]
      right_inv := fun g => by
        funext i
        simp [i.2] }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp

theorem extAmbD_A1 (hAmb : AmbientChainEvenSigned) {t : ℕ} (ht : 7 ≤ t) (hodd : Odd t)
    {vx z : V t} {ℓ j k : Code t} {U : Submodule F (V t)} (h : ExtShapeA1 vx ℓ U j z k) :
    ExtAmbDAt (planeEntry (.orthogonal 0) t) vx z ℓ k := by
  obtain ⟨a, c, s, s', hac, hs, hs', hvx, hz, hℓ, hj, hk, hU⟩ := h
  obtain ⟨W, f, hcart, ha, hb, hpa, hpab, hrefl, hker, hroot, hbasis⟩ :=
    hAmb t (by omega) c a hac.symm
  obtain ⟨m, hm⟩ := hodd
  subst hm
  have hspan : Submodule.span F {z} = Submodule.span F {(Pi.single c 1 : V (2 * m + 1))} := by
    rw [hz]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs') _
  refine ⟨W, ?_, ?_, ?_, ?_, hbasis, m, by omega, ?_⟩
  · show W.toLin.parab {i | i ≠ W.a} = PlaneRaw.normalizerOf (.orthogonal 0) (2 * m + 1) k
    rw [hpa, hk, normalizerOf_zero_even]
  · show W.toLin.simpleRefl W.a ∈ PlaneRaw.normalizerOf (.orthogonal 0) (2 * m + 1) ℓ ⊔
      PlaneRaw.normalizerOf (.orthogonal 0) (2 * m + 1) k
    rw [hrefl, hℓ, hk, normalizerOf_zero_even, normalizerOf_zero_even]
    exact swapEquiv_mem_sup_even (by omega) hac
  · intro v
    exact (hker v).trans (Iff.of_eq (congrArg (fun S => v ∈ S) hspan.symm))
  · intro i hia hib
    exact (show W.root i vx = 0 by
      rw [hvx, map_smul]
      simp only [unitVec]
      rw [hroot i hia hib, smul_zero])
  · obtain ⟨f', hf'⟩ := exists_equiv_compl_image_zero f
    have hW0 : W.a = f 0 := by rw [ha]; rfl
    refine ⟨f'.trans (Equiv.subtypeEquivRight fun i => by rw [hW0]), fun p q => ?_⟩
    simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
    rw [hf' p, hf' q, hcart, cartanD_succ (by omega)]

theorem extD5_A1 (hAmb : AmbientChainEvenSigned) {vx z : V 5} {ℓ j k : Code 5}
    {U : Submodule F (V 5)} (h : ExtShapeA1 vx ℓ U j z k) :
    ExtD5At (planeEntry (.orthogonal 0) 5) vx z ℓ j k := by
  obtain ⟨a, c, s, s', hac, hs, hs', hvx, hz, hℓ, hj, hk, hU⟩ := h
  obtain ⟨W, f, hcart, ha, hb, hpa, hpab, hrefl, hker, hroot, hbasis⟩ :=
    hAmb 5 (by omega) c a hac.symm
  have hspan : Submodule.span F {z} = Submodule.span F {(Pi.single c 1 : V 5)} := by
    rw [hz]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs') _
  have hjcard : (Finset.univ \ {a, c} : Finset (Fin 5)).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hac]
  have hlab : PlaneRaw.label (.orthogonal 0) (.zero (Finset.univ \ {a, c}) : Code 5) =
      ⟨.twD, 3, 1⟩ := by
    have hodd : ¬ Even (Finset.univ \ {a, c} : Finset (Fin 5)).card := by
      rw [hjcard]
      decide
    simp [PlaneRaw.label, hodd, hjcard] <;> decide
  refine ⟨W, ?_, ?_, ?_, ?_, hbasis, ⟨f, hcart, ha, Or.inl hb⟩, ?_,
    (⟨.twD, 3, 1⟩ : LargeEvenLabel), Or.inr rfl, ?_, ?_, ?_, ?_⟩
  · show W.toLin.parab {i | i ≠ W.a} = PlaneRaw.normalizerOf (.orthogonal 0) 5 k
    rw [hpa, hk, normalizerOf_zero_even]
  · show W.toLin.simpleRefl W.a ∈ PlaneRaw.normalizerOf (.orthogonal 0) 5 ℓ ⊔ PlaneRaw.normalizerOf (.orthogonal 0) 5 k
    rw [hrefl, hℓ, hk, normalizerOf_zero_even, normalizerOf_zero_even]
    exact swapEquiv_mem_sup_even (by omega) hac
  · intro v
    exact (hker v).trans (Iff.of_eq (congrArg (fun S => v ∈ S) hspan.symm))
  · intro i hia hib
    exact (show W.root i vx = 0 by
      rw [hvx, map_smul]
      simp only [unitVec]
      rw [hroot i hia hib, smul_zero])
  · show W.toLin.parab {i | i ≠ W.a ∧ i ≠ W.b} = PlaneRaw.normalizerOf (.orthogonal 0) 5 j
    rw [hpab, hj, normalizerOf_zero_even, Finset.pair_comm]
  · show GGLabelIso ⟨.twD, 3, 1⟩ (PlaneRaw.label (.orthogonal 0) j)
    rw [hj, hlab]
    exact Or.inl rfl
  · show PlaneRaw.inside (.orthogonal 0) j ⊓ PlaneRaw.cent (.orthogonal 0) j = ⊥
    rw [hj]
    exact insideZero_inf_centZero _
  · show PlaneRaw.inside (.orthogonal 0) j ⊔ PlaneRaw.cent (.orthogonal 0) j = ⊤
    rw [hj]
    exact insideZero_sup_centZero _
  · show finrank F (PlaneRaw.inside (.orthogonal 0) j) = 3
    rw [hj]
    exact (finrank_insideZero _).trans hjcard

end

end CFSG.StandardType.GGQ2Frame
