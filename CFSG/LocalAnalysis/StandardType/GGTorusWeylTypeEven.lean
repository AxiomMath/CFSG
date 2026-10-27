module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrthPlus
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeEvenAux
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGRCTransfer
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB SpCoord Multiplicative

private lemma ggWTEven_toPerm_sgnAut {p k : ℕ} (i : Fin k) :
    MulAut.toPerm (Fin k → Multiplicative (ZMod p)) (sgnAut i) = SpJoin.coordInv k p i := by
  ext v; rfl

private lemma ggWTEven_toPerm_permAut {p k : ℕ} (σ : Equiv.Perm (Fin k)) :
    MulAut.toPerm (Fin k → Multiplicative (ZMod p)) (permAut σ) = SpJoin.coordPerm k p σ := by
  ext v; rfl

private lemma ggWTEven_toPerm_injective {p k : ℕ} :
    Function.Injective (MulAut.toPerm (Fin k → Multiplicative (ZMod p))) := by
  intro a b h
  exact MulEquiv.ext fun v =>
    congrArg (fun e : Equiv.Perm (Fin k → Multiplicative (ZMod p)) => e v) h

private lemma ggWTEven_fin_ne_succ {k : ℕ} {i : Fin k} (hi : i.val + 1 < k) :
    i ≠ ⟨i.val + 1, hi⟩ := by
  intro hh
  have h2 : i.val = i.val + 1 := by
    have := congrArg Fin.val hh
    simpa using this
  omega

private lemma ggWTEven_isRefl_sgnAut {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (i : Fin k) :
    GGIsReflection p (MulAut.congr Θ (sgnAut i)) :=
  ⟨by rw [← map_pow, sgnAut_sq, map_one],
    (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 (sgnAut_sq i))
      (card_fix_sgnAut hp hp2 i)).2⟩

private lemma ggWTEven_isRefl_permAut_swap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) {a b : Fin k} (hab : a ≠ b) :
    GGIsReflection p (MulAut.congr Θ (permAut (Equiv.swap a b))) :=
  ⟨by rw [← map_pow, permAut_swap_sq, map_one],
    (ggIsPseudoReflection_congr Θ
      (pow_sub_one_eq_one_of_sq hp hp2 (permAut_swap_sq a b))
      (card_fix_permAut_swap hp hp2 hab)).2⟩

private theorem ggWTEven_weylReflGroup_B {p : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)))
    (hsgn : ∀ i : Fin k, sgnAut i ∈
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).comap
        (MulAut.congr Θ).toMonoidHom) :
    GGWeylReflectionGroup p (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let V := Fin k → Multiplicative (ZMod p)
  let Φ : MulAut V ≃* MulAut ↥A := MulAut.congr Θ
  let Aut : Subgroup (MulAut ↥A) :=
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  let Gens : Set (MulAut V) :=
    Set.range (fun i : Fin k => sgnAut i) ∪
      Set.range (fun x : {x : Fin k × Fin k // x.1 ≠ x.2} =>
        permAut (Equiv.swap x.1.1 x.1.2))
  set H : Subgroup (MulAut V) := Subgroup.closure Gens with hH
  have hgen_mem : ∀ α ∈ Gens, Φ α ∈ Aut := by
    intro α hα
    rcases hα with ⟨i, rfl⟩ | ⟨⟨⟨a, b⟩, hab⟩, rfl⟩
    · exact Subgroup.mem_comap.mp (hsgn i)
    · obtain ⟨n, hn, hnα⟩ := hP (Equiv.swap a b)
      rw [← hnα]
      exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
        ⟨n, rfl⟩ hn
  have hmapΦ : H.map Φ.toMonoidHom = Aut := by
    apply le_antisymm
    · rw [hH, Subgroup.map_le_iff_le_comap]
      exact (Subgroup.closure_le _).mpr (fun α hα => hgen_mem α hα)
    · intro φ hφ
      obtain ⟨g, hgH, hg, hφg⟩ := eq_ggConjAut_of_mem_ggAutomizer hφ
      obtain ⟨n, rfl⟩ := hgH
      have hsp : IsSignedPerm ⇑(Φ.symm φ) := by
        rw [hφg]; exact hN n hg
      have hmemH : Φ.symm φ ∈ H :=
        mem_of_isSignedPerm
          (fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
          (fun a b hab => Subgroup.subset_closure (Or.inr ⟨⟨(a, b), hab⟩, rfl⟩))
          hsp
      exact Subgroup.mem_map.mpr ⟨Φ.symm φ, hmemH, by simp⟩
  have hmapPerm : H.map (MulAut.toPerm V) = SpJoin.spSignedGroup k p := by
    rw [hH, MonoidHom.map_closure]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨α, hα, rfl⟩
      rcases hα with ⟨i, rfl⟩ | ⟨⟨⟨a, b⟩, hab⟩, rfl⟩
      · rw [ggWTEven_toPerm_sgnAut]; exact SpJoin.coordInv_mem_spSignedGroup i
      · rw [ggWTEven_toPerm_permAut]; exact SpJoin.coordPerm_mem_spSignedGroup (Equiv.swap a b)
    · rw [SpJoin.spSignedGroup]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨i, rfl⟩
      by_cases hi : i.val + 1 < k
      · rw [SpJoin.spReflPerm_of_lt k p i hi]
        refine Subgroup.subset_closure ⟨permAut (Equiv.swap i ⟨i.val + 1, hi⟩), ?_, ?_⟩
        · exact Or.inr ⟨⟨(i, ⟨i.val + 1, hi⟩), ggWTEven_fin_ne_succ hi⟩, rfl⟩
        · rw [ggWTEven_toPerm_permAut]
      · rw [SpJoin.spReflPerm_of_not_lt k p i hi]
        refine Subgroup.subset_closure ⟨sgnAut i, Or.inl ⟨i, rfl⟩, ?_⟩
        rw [ggWTEven_toPerm_sgnAut]
  let isoHSp : H ≃* ↥(SpJoin.spSignedGroup k p) :=
    (Subgroup.equivMapOfInjective H (MulAut.toPerm V) ggWTEven_toPerm_injective).trans
      (MulEquiv.subgroupCongr hmapPerm)
  let isoHAut : H ≃* Aut :=
    (Subgroup.equivMapOfInjective H Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr hmapΦ)
  have isoHSp_apply : ∀ h : H, (↑(isoHSp h) : Equiv.Perm V) = MulAut.toPerm V ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H (MulAut.toPerm V)
        ggWTEven_toPerm_injective).trans (MulEquiv.subgroupCongr hmapPerm) h) : Equiv.Perm V) =
      MulAut.toPerm V ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  have isoHAut_apply : ∀ h : H, (↑(isoHAut h) : MulAut ↥A) = Φ ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H Φ.toMonoidHom Φ.injective).trans
        (MulEquiv.subgroupCongr hmapΦ) h) : MulAut ↥A) = Φ ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  obtain ⟨e, he⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 (k := k) (by omega)
  let f : (CoxeterMatrix.B k).Group ≃* Aut := (e.trans isoHSp.symm).trans isoHAut
  let g : Fin k → MulAut V := fun i =>
    if hi : i.val + 1 < k then permAut (Equiv.swap i ⟨i.val + 1, hi⟩) else sgnAut i
  have hg_toPerm : ∀ i, MulAut.toPerm V (g i) = SpJoin.spReflPerm k p i := by
    intro i
    by_cases hi : i.val + 1 < k
    · rw [show g i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        simp only [g, dif_pos hi], ggWTEven_toPerm_permAut, SpJoin.spReflPerm_of_lt k p i hi]
    · rw [show g i = sgnAut i from by simp only [g, dif_neg hi],
        ggWTEven_toPerm_sgnAut, SpJoin.spReflPerm_of_not_lt k p i hi]
  have hg_mem : ∀ i, g i ∈ H := by
    intro i
    rw [hH]
    refine Subgroup.subset_closure ?_
    by_cases hi : i.val + 1 < k
    · refine Or.inr ⟨⟨(i, ⟨i.val + 1, hi⟩), ?_⟩, ?_⟩
      · exact ggWTEven_fin_ne_succ hi
      · show permAut (Equiv.swap i ⟨i.val + 1, hi⟩) = g i
        simp only [g, dif_pos hi]
    · refine Or.inl ⟨i, ?_⟩
      show sgnAut i = g i
      simp only [g, dif_neg hi]
  have hf_simple : ∀ i, (f ((CoxeterMatrix.B k).simple i) : MulAut ↥A) = Φ (g i) := by
    intro i
    have hei : e ((CoxeterMatrix.B k).simple i) =
        ⟨SpJoin.spReflPerm k p i, SpJoin.spReflPerm_mem_spSignedGroup k p i⟩ :=
      Subtype.ext (he i)
    have hsymm : isoHSp.symm ⟨SpJoin.spReflPerm k p i, SpJoin.spReflPerm_mem_spSignedGroup k p i⟩ =
        ⟨g i, hg_mem i⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [isoHSp_apply]
      exact (hg_toPerm i).symm
    calc (f ((CoxeterMatrix.B k).simple i) : MulAut ↥A)
        = ↑(isoHAut (isoHSp.symm (e ((CoxeterMatrix.B k).simple i)))) := by
          simp only [f, MulEquiv.trans_apply]
      _ = ↑(isoHAut (isoHSp.symm ⟨SpJoin.spReflPerm k p i,
            SpJoin.spReflPerm_mem_spSignedGroup k p i⟩)) := by rw [hei]
      _ = ↑(isoHAut ⟨g i, hg_mem i⟩) := by rw [hsymm]
      _ = Φ (g i) := isoHAut_apply ⟨g i, hg_mem i⟩
  refine ⟨Fin k, CoxeterMatrix.B k, ?_, f, ?_⟩
  · refine Or.inl ⟨k, Equiv.refl (Fin k), by omega, Or.inr (Or.inl ⟨by omega, ?_⟩)⟩
    exact (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm
  · intro i
    rw [hf_simple i]
    by_cases hi : i.val + 1 < k
    · rw [show g i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        simp only [g, dif_pos hi]]
      exact ggWTEven_isRefl_permAut_swap hp hp2 Θ (ggWTEven_fin_ne_succ hi)
    · rw [show g i = sgnAut i from by simp only [g, dif_neg hi]]
      exact ggWTEven_isRefl_sgnAut hp hp2 Θ i

private theorem ggWTEven_weylReflGroup {p : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk4 : 4 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hD : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hST : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j * permAut (Equiv.swap i j)))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    GGWeylReflectionGroup p (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let V := Fin k → Multiplicative (ZMod p)
  let Aut : Subgroup (MulAut ↥A) :=
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  set H : Subgroup (MulAut V) := Aut.comap (MulAut.congr Θ).toMonoidHom with hH
  have hHsp : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    have huW : MulAut.congr Θ u ∈ Aut := Subgroup.mem_comap.mp hu
    obtain ⟨_, ⟨n, rfl⟩, hmn, hmu⟩ := mem_ggAutomizer_iff.mp huW
    have hcu : MulAut.congr Θ u = ggConjAut A hmn := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      exact (hmu b).trans (ggConjAut_apply A hmn b).symm
    have hu' : u = (MulAut.congr Θ).symm (ggConjAut A hmn) := by
      rw [← hcu, MulEquiv.symm_apply_apply]
    rw [hu']
    exact hN n hmn
  have hdH : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
    intro i j hij
    obtain ⟨n, hn, hnD⟩ := hD i j hij
    refine Subgroup.mem_comap.mpr ?_
    change MulAut.congr Θ (sgnAut i * sgnAut j) ∈ Aut
    rw [show MulAut.congr Θ (sgnAut i * sgnAut j) = ggConjAut A hn from hnD.symm]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    obtain ⟨n, hn, hnP⟩ := hP (Equiv.swap a b)
    refine Subgroup.mem_comap.mpr ?_
    change MulAut.congr Θ (permAut (Equiv.swap a b)) ∈ Aut
    rw [show MulAut.congr Θ (permAut (Equiv.swap a b)) = ggConjAut A hn from hnP.symm]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  obtain ⟨i₀⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  by_cases hsgn : sgnAut i₀ ∈ H
  · have hsg : ∀ i : Fin k, sgnAut i ∈ H := by
      intro i
      by_cases hi : i = i₀
      · rw [hi]; exact hsgn
      · have h1 : sgnAut i * sgnAut i₀ ∈ H := hdH i i₀ hi
        have h2 := H.mul_mem h1 hsgn
        rwa [mul_assoc, OrthExcEven.sgnAut_mul_self, mul_one] at h2
    exact ggWTEven_weylReflGroup_B hp hp2 (by omega) Θ hP hN hsg
  ·
    let GensD : Set (MulAut V) :=
      Set.range (fun x : {x : Fin k × Fin k // x.1 ≠ x.2} =>
          sgnAut x.1.1 * sgnAut x.1.2) ∪
        Set.range (fun x : {x : Fin k × Fin k // x.1 ≠ x.2} =>
          permAut (Equiv.swap x.1.1 x.1.2))
    set H0 : Subgroup (MulAut V) := Subgroup.closure GensD with hH0def
    have hdH0 : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H0 :=
      fun i j hij => Subgroup.subset_closure (Or.inl ⟨⟨(i, j), hij⟩, rfl⟩)
    have htH0 : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H0 :=
      fun a b hab => Subgroup.subset_closure (Or.inr ⟨⟨(a, b), hab⟩, rfl⟩)
    have hH0_le_H : H0 ≤ H := by
      rw [hH0def]
      refine (Subgroup.closure_le _).mpr ?_
      rintro α (⟨⟨⟨i, j⟩, hij⟩, rfl⟩ | ⟨⟨⟨a, b⟩, hab⟩, rfl⟩)
      · exact hdH i j hij
      · exact htH a b hab
    have hH_le_H0 : H ≤ H0 := by
      intro u hu
      rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm hdH0 htH0 i₀ (hHsp u hu) with h1 | h1
      · exact h1
      · exfalso
        apply hsgn
        have h2 : u * sgnAut i₀ ∈ H := hH0_le_H h1
        have h3 := H.mul_mem (H.inv_mem hu) h2
        rwa [inv_mul_cancel_left] at h3
    have hH0_eq : H0 = H := le_antisymm hH0_le_H hH_le_H0
    let b : Module.Basis (Fin k) (ZMod p) (Fin k → ZMod p) := Pi.basisFun (ZMod p) (Fin k)
    let ι : Additive ↥A ≃+ (Fin k → ZMod p) :=
      { toFun := fun x i => toAdd ((Θ.symm (Additive.toMul x)) i)
        invFun := fun (v : Fin k → ZMod p) => Additive.ofMul (Θ (fun i => ofAdd (v i)))
        left_inv := by intro x; simp
        right_inv := by intro v; ext i; simp
        map_add' := by intro x y; ext i; simp [map_mul] }
    let ψ : MulAut V →* ((Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) :=
      (ggLin (p := p) ι).comp (MulAut.congr Θ).toMonoidHom
    have hAbar_eq : Aut.map (ggLin (p := p) ι) = H0.map ψ := by
      have hAut : Aut = H.map (MulAut.congr Θ).toMonoidHom :=
        (Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.congr Θ).toMonoidHom)
          (MulAut.congr Θ).surjective Aut).symm
      rw [hAut, hH0_eq, Subgroup.map_map]
    have hι_single : ∀ i : Fin k, ι (Additive.ofMul (Θ (Pi.mulSingle i (ofAdd 1)))) = b i := by
      intro i; ext j
      by_cases hji : j = i
      · rw [hji]; simp [ι, b, Pi.mulSingle_apply, Pi.single_apply]
      · simp [ι, b, Pi.mulSingle_apply, Pi.single_apply, hji]
    have hggLin : ∀ (u : MulAut V) (l : Fin k),
        ggLin (p := p) ι (MulAut.congr Θ u) (b l)
          = fun m => toAdd (u (Pi.mulSingle l (ofAdd 1)) m) := by
      intro u l
      rw [← hι_single l, ggLin_apply_ofMul]
      simp [ι, toMul_ofMul, MulAut.congr_apply]
    have hdbl_mem : ∀ i j : Fin k, i ≠ j →
        ggLin (p := p) ι (MulAut.congr Θ (sgnAut i * sgnAut j)) ∈ ggWTEven_evenLin p k b := by
      intro i j hij
      refine ⟨Equiv.refl (Fin k), fun l => if l = i ∨ l = j then (-1 : ZMod p) else 1,
        ?_, ?_, ?_⟩
      · intro l; by_cases h : l = i ∨ l = j <;> simp [h]
      · exact ggWTEven_prod_pair i j hij
      · intro l
        rw [hggLin]
        funext m
        rw [OrthExcEven.sgnAut_mul_sgnAut_apply, ggWTEven_dinv_apply i j l m hij]
        by_cases hml : m = l
        · rw [hml]; simp [b, Pi.basisFun_apply]
        · simp [b, Pi.basisFun_apply, hml]
    have hswap_mem : ∀ a b' : Fin k, a ≠ b' →
        ggLin (p := p) ι (MulAut.congr Θ (permAut (Equiv.swap a b'))) ∈
          ggWTEven_evenLin p k b := by
      intro a b' hab
      refine ⟨Equiv.swap a b', fun _ => 1, ?_, ?_, ?_⟩
      · intro l; left; rfl
      · simp
      · intro l
        rw [hggLin]
        funext m
        rw [permAut_mulSingle]
        by_cases hm : m = Equiv.swap a b' l
        · rw [hm]; simp [b, Pi.basisFun_apply]
        · simp [b, Pi.basisFun_apply, hm]
    have hAbar_le : Aut.map (ggLin (p := p) ι) ≤ ggWTEven_evenLin p k b := by
      rw [hAbar_eq, hH0def, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨u, hu, rfl⟩
      rcases hu with ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ | ⟨⟨⟨a, b'⟩, hab⟩, rfl⟩
      · exact hdbl_mem i j hij
      · exact hswap_mem a b' hab
    have hEvenLin_le : ggWTEven_evenLin p k b ≤ Aut.map (ggLin (p := p) ι) := by
      intro a ha
      obtain ⟨σ, c, hc, hprod, ha'⟩ := ha
      have hperm : permAut σ ∈ H0 := by
        rw [hH0def]
        exact Subgroup.closure_mono (Set.subset_union_right) (ggWTEven_permAut_mem_closure σ)
      have hdiag : diagAut c (fun i => coord_sign_mul_self (hc i)) ∈ H0 := by
        have heven : Even (Finset.univ.filter (fun i => c i = -1)).card :=
          ggWTEven_even_card_of_prod hp hp2 c hc hprod
        obtain ⟨n, hn⟩ := heven
        refine OrthExcEven.mem_of_diag_even hdH0 n (Finset.univ.filter (fun i => c i = -1))
          (by omega) _ c ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases hc i with h | h
          · exact h
          · exact absurd h hi
        · intro i hi
          simpa using hi
        · intro f i
          simp [diagAut_apply]
      have hu : permAut σ * diagAut c (fun i => coord_sign_mul_self (hc i)) ∈ H0 :=
        H0.mul_mem hperm hdiag
      rw [hAbar_eq]
      refine Subgroup.mem_map.mpr ⟨permAut σ * diagAut c (fun i => coord_sign_mul_self (hc i)),
        hu, ?_⟩
      apply LinearEquiv.ext
      intro v
      have hbl : ∀ l, ψ (permAut σ * diagAut c (fun i => coord_sign_mul_self (hc i))) (b l) =
          a (b l) := by
        intro l
        change ggLin (p := p) ι (MulAut.congr Θ
          (permAut σ * diagAut c (fun i => coord_sign_mul_self (hc i)))) (b l) = a (b l)
        rw [hggLin]
        funext m
        rw [MulAut.mul_apply, diagAut_mulSingle, permAut_mulSingle, ha' l]
        simp only [Pi.mulSingle_apply, Pi.smul_apply, b, Pi.basisFun_apply, Pi.single_apply,
          smul_eq_mul]
        split_ifs <;> simp_all [toAdd_ofAdd, toAdd_one]
      have h' : ((ψ (permAut σ * diagAut c (fun i => coord_sign_mul_self (hc i))) :
          (Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) :
            (Fin k → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p)) =
          ((a : (Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) :
            (Fin k → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p)) := by
        apply Module.Basis.ext
        exact hbl
      exact congrArg (fun f : (Fin k → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p) => f v) h'
    have hEvenLin_eq : Aut.map (ggLin (p := p) ι) = ggWTEven_evenLin p k b :=
      le_antisymm hAbar_le hEvenLin_le
    have hLinWeyl : ZS.LinWeyl p (Aut.map (ggLin (p := p) ι)) :=
      ggRC_linWeyl_of_even_signed hp2 hk4 b (Aut.map (ggLin (p := p) ι))
        (fun a => by rw [hEvenLin_eq]; rfl)
    exact ggRC_weylReflGroup_of_linWeyl ι Aut hLinWeyl

theorem ggTorusWeylTypeW_of_evenSignedPermEltSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {kP : ℕ → Prop} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (hkP : ∀ k, kP k → 4 ≤ k)
    (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGTorusWeylTypeW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨k, Θ, hk, hkp, hW, hD, hP, hST, hN⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hAab hAI h3 hsc
  have hk4 : 4 ≤ k := hkP k hkp
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hWdef
  obtain ⟨ι, M, hM, f, hf⟩ := ggWTEven_weylReflGroup hp hp2 hk4 Θ hW hD hP hST hN
  refine ⟨ι, M, f, hM, ?_, fun i => ?_⟩
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (MulAut (Fin k → Multiplicative (ZMod p))) :=
      Finite.of_injective
        (fun f : MulAut (Fin k → Multiplicative (ZMod p)) =>
          (f : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))))
        (fun f g hfg => MulEquiv.ext (congrFun hfg))
    set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
      W.comap (MulAut.congr Θ).toMonoidHom with hH
    have hmap : Subgroup.map (MulAut.congr Θ).toMonoidHom H = W :=
      Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.congr Θ).toMonoidHom)
        (MulAut.congr Θ).surjective W
    have hcardH : Nat.card H = Nat.card W := by
      rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.congr Θ).toMonoidHom)
        (MulAut.congr Θ).injective]
    have hHsp : ∀ u ∈ H, IsSignedPerm ⇑u := by
      intro u hu
      have huW : MulAut.congr Θ u ∈ W := Subgroup.mem_comap.mp hu
      obtain ⟨_, ⟨n, rfl⟩, hmn, hmu⟩ := mem_ggAutomizer_iff.mp huW
      have hcu : MulAut.congr Θ u = ggConjAut A hmn := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        exact (hmu b).trans (ggConjAut_apply A hmn b).symm
      have hu' : u = (MulAut.congr Θ).symm (ggConjAut A hmn) := by
        rw [← hcu, MulEquiv.symm_apply_apply]
      rw [hu']
      exact hN n hmn
    have hdH : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
      intro i j hij
      obtain ⟨n, hn, hnD⟩ := hD i j hij
      refine Subgroup.mem_comap.mpr ?_
      change MulAut.congr Θ (sgnAut i * sgnAut j) ∈ W
      rw [show MulAut.congr Θ (sgnAut i * sgnAut j) = ggConjAut A hn from hnD.symm]
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
    have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := by
      intro a b hab
      obtain ⟨n, hn, hnP⟩ := hP (Equiv.swap a b)
      refine Subgroup.mem_comap.mpr ?_
      change MulAut.congr Θ (permAut (Equiv.swap a b)) ∈ W
      rw [show MulAut.congr Θ (permAut (Equiv.swap a b)) = ggConjAut A hn from hnP.symm]
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
    have hdvd : 2 ^ (k - 1) * k.factorial ∣ Nat.card H :=
      SignedPermCount.dvd_card_of_isSignedPerm_even hp hp2 hHsp hdH htH
    have hbig : 12 < 2 ^ (k - 1) * k.factorial := by
      have h2 : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hf : Nat.factorial 3 ≤ k.factorial := Nat.factorial_le (by omega)
      have h24 : 24 ≤ 2 ^ (k - 1) * k.factorial := by
        have hm := Nat.mul_le_mul h2 hf
        have hf3 : Nat.factorial 3 = 6 := by decide
        rw [hf3] at hm
        norm_num at hm
        exact hm
      omega
    have hpos : 0 < Nat.card H := by
      haveI : Nonempty ↥H := ⟨1⟩
      exact Nat.card_pos
    have hle : 2 ^ (k - 1) * k.factorial ≤ Nat.card H := Nat.le_of_dvd hpos hdvd
    rw [← hcardH]
    omega
  ·
    rw [ggWTEven_reflSet_eq hW]
    exact ⟨(f (M.simple i)).2, hf i⟩

end CFSG.StandardType

end
