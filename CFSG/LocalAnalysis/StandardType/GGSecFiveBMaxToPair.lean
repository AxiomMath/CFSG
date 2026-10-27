module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrXInnerWeyl
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGCoxeterBReflJoin
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE

public section

namespace CFSG.StandardType

theorem GGSecFiveRestHyp.eq_one_of_fix_pair {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hN : GGNbr p B x D J y K) (b : Bs)
    (hb : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ b = b) : b = 1 := by
  have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hW y K hN
  have hSW : GGScalarsOrWeyl' p B Bs x D J := Or.inr hW
  have hbX : (b : G) ∈ Subgroup.zpowers x :=
    hTBF G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hN hrefl hSW b
      fun φ hφ => hb φ (Subgroup.mem_sup_left hφ)
  exact Subtype.ext <| (ggTBFixNbrXInput_of_innerWeyl hWI) G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1
    hR.2.2.2.1 y K hN hrefl hSW b hbX fun φ hφ => hb φ (Subgroup.mem_sup_right hφ)

private theorem range_subtype_comp {X Y : Type*} [Group X] [Group Y] {H : Subgroup Y}
    (φ : X →* ↥H) (hφ : Function.Surjective φ) : (H.subtype.comp φ).range = H := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, Subgroup.map_top,
    Subgroup.range_subtype]

private theorem ggIsWeylMatrix_B {n : ℕ} (hn : 2 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.B n) :=
  Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inl ⟨hn, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩

private theorem not_g2_reindex_B {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ e : Fin 2 ≃ Fin n, CoxeterMatrix.B n = CoxeterMatrix.G₂.reindex e := by
  rintro ⟨e, he⟩
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hB : (CoxeterMatrix.B n).M ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 6 := by
    simp only [CoxeterMatrix.B, Matrix.of_apply]
    split_ifs <;> omega
  have h := congrArg
    (fun M : CoxeterMatrix (Fin n) => M.M ⟨0, by omega⟩ ⟨1, by omega⟩) he
  rw [CoxeterMatrix.reindex_apply] at h
  have hne : e.symm ⟨0, by omega⟩ ≠ e.symm ⟨1, by omega⟩ := fun h' => h01 (e.symm.injective h')
  have h6 : CoxeterMatrix.G₂.M (e.symm ⟨0, by omega⟩) (e.symm ⟨1, by omega⟩) = 6 := by
    revert hne
    generalize e.symm ⟨0, by omega⟩ = a
    generalize e.symm ⟨1, by omega⟩ = b
    intro hne
    fin_cases a <;> fin_cases b <;>
      simp_all [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
  rw [h6] at h
  exact hB h

theorem map_closure_range_eq_of_simple {W X : Type*} [Group W] [Group X]
    {κ : Type*} (M : CoxeterMatrix κ) (F : W →* X) (s : κ → W) (f : M.Group →* X)
    (hs : ∀ i, F (s i) = f (M.simple i)) :
    Subgroup.map F (Subgroup.closure (Set.range s)) = f.range := by
  rw [MonoidHom.map_closure]
  have himg : F '' Set.range s = Set.range (fun i => f (M.simple i)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hs i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨s i, ⟨i, rfl⟩, hs i⟩
  rw [himg]
  change Subgroup.closure (Set.range (f ∘ M.simple)) = f.range
  rw [← CoxeterMatrix.toCoxeterSystem_simple M, Set.range_comp, ← MonoidHom.map_closure,
    M.toCoxeterSystem.subgroup_closure_range_simple, Subgroup.map_top]

private theorem exists_conj_simple_of_typeB
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hEl : CFSG.Assembly.IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs) {n : ℕ} (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (E : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hE : ∀ i : Fin n, GGIsReflection p
      ((E ((CoxeterMatrix.B n).simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
    {T : Subgroup (MulAut ↥Bs)} (hTA : T ≤ ggAutomizerJoin L Bs 𝒦)
    {κ : Type} {M' : CoxeterMatrix κ} (f : M'.Group ≃* ↥T)
    (hf : ∀ i, GGIsReflection p ((f (M'.simple i) : ↥T) : MulAut ↥Bs)) (a : κ) :
    ∃ (w : (CoxeterMatrix.B n).Group) (i : Fin n),
      E.symm ⟨(f (M'.simple a) : MulAut ↥Bs), hTA (f (M'.simple a)).2⟩ =
        w * (CoxeterMatrix.B n).simple i * w⁻¹ := by
  obtain ⟨i, g, hig⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs
    (Fact.out : p.Prime) hp2 hEl hNT (ggAutomizerJoin L Bs 𝒦) hAind
    (Fin n) (CoxeterMatrix.B n) (ggIsWeylMatrix_B hn) (not_g2_reindex_B hn) E hE
    ⟨(f (M'.simple a) : MulAut ↥Bs), hTA (f (M'.simple a)).2⟩ (hf a)
  refine ⟨g, i, ?_⟩
  simpa using congrArg E.symm hig

private theorem exists_not_le_sign_map_of_typeB
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hne : 𝒦.Nonempty) {n : ℕ} (hn : 2 ≤ n)
    (E : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) :
    ∃ K ∈ 𝒦, ¬ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      Subgroup.map ((ggAutomizerJoin L Bs 𝒦).subtype.comp E.toMonoidHom) (coxeterBSign n).ker := by
  classical
  by_contra hcon
  have hcon' : ∀ K ∈ 𝒦, (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      Subgroup.map ((ggAutomizerJoin L Bs 𝒦).subtype.comp E.toMonoidHom)
        (coxeterBSign n).ker := by
    intro K hK
    by_contra h
    exact hcon ⟨K, hK, h⟩
  set F : (CoxeterMatrix.B n).Group →* MulAut ↥Bs :=
    (ggAutomizerJoin L Bs 𝒦).subtype.comp E.toMonoidHom with hF
  set Ksign : Subgroup (MulAut ↥Bs) := Subgroup.map F (coxeterBSign n).ker
  have hAL : ggAutomizer L Bs ≤ Ksign := by
    obtain ⟨K₀, hK₀⟩ := hne
    exact (le_sup_left : ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs).trans
      (hcon' K₀ hK₀)
  have hAK : (⨆ K ∈ 𝒦, ggAutomizer K Bs) ≤ Ksign :=
    iSup₂_le fun K hK =>
      (le_sup_right : ggAutomizer K Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs).trans
        (hcon' K hK)
  have hA : ggAutomizerJoin L Bs 𝒦 ≤ Ksign := by
    simpa only [ggAutomizerJoin] using sup_le hAL hAK
  have hFrange : F.range = ggAutomizerJoin L Bs 𝒦 :=
    range_subtype_comp E.toMonoidHom E.surjective
  have htop : (⊤ : Subgroup (CoxeterMatrix.B n).Group) ≤ (coxeterBSign n).ker := by
    intro w _
    have hFw : F w ∈ Ksign := hA (hFrange ▸ MonoidHom.mem_range.mpr ⟨w, rfl⟩)
    obtain ⟨w', hw', heq⟩ := Subgroup.mem_map.mp hFw
    have hww : w' = w := E.injective (Subtype.ext heq)
    rwa [hww] at hw'
  have hi : (CoxeterMatrix.B n).simple ⟨n - 1, by omega⟩ ∈ (coxeterBSign n).ker :=
    htop (Subgroup.mem_top _)
  rw [MonoidHom.mem_ker] at hi
  have hsign : coxeterBSign n ((CoxeterMatrix.B n).simple ⟨n - 1, by omega⟩) = -1 := by
    rw [coxeterBSign_simple, Fin.val_mk, if_neg (by omega)]
  rw [hsign] at hi
  exact (by decide : (-1 : ℤˣ) ≠ 1) hi

private theorem GGSecFiveRouteCfg.eq_zero_of_forall_ggLin_fix
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hN : GGNbr p B x D J y K)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {W : Type*} [Group W] (F : W →* MulAut ↥Bs)
    (T : Subgroup (MulAut ↥Bs)) (hT : T = ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    {κ : Type*} {M' : CoxeterMatrix κ} (f : M'.Group ≃* ↥T)
    (s : κ → W) (hsF : ∀ i, F (s i) = (f (M'.simple i) : MulAut ↥Bs))
    (v : V) (hv : ∀ a, ggLin (p := p) ι (F (s a)) v = v) : v = 0 := by
  let b : ↥Bs := Additive.toMul (ι.symm v)
  have hsimple : ∀ i, ((f (M'.simple i) : ↥T) : MulAut ↥Bs) b = b := by
    intro i
    rw [← hsF i, ggLin_fix_iff (p := p) ι (F (s i)) b]
    simpa [b] using hv i
  have hfw : ∀ w : M'.Group, ((f w : ↥T) : MulAut ↥Bs) b = b := by
    intro w
    induction w using M'.toCoxeterSystem.simple_induction_left with
    | one => simp
    | mul_simple_left w i ih =>
        rw [map_mul]
        change ((f (M'.simple i) : ↥T) : MulAut ↥Bs)
          (((f w : ↥T) : MulAut ↥Bs) b) = b
        rw [ih, hsimple i]
  have hb : ∀ φ ∈ T, φ b = b := by
    intro φ hφ
    obtain ⟨w, hw⟩ := f.surjective ⟨φ, hφ⟩
    have hcoe : ((f w : ↥T) : MulAut ↥Bs) = φ := congrArg Subtype.val hw
    exact hcoe ▸ hfw w
  have hb' : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ b = b := by
    intro φ hφ
    rw [← hT] at hφ
    exact hb φ hφ
  have hb1 : b = 1 :=
    GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b hb'
  have hv0 : ι (Additive.ofMul b) = v := by simp [b]
  rw [hb1] at hv0
  simpa using hv0.symm

theorem reflTransGen_ne_comm_of_weyl {W X : Type*} [Group W] [Group X]
    {κ : Type} {M' : CoxeterMatrix κ} (hM' : GGIsWeylMatrix M') (F : W →* X) (s : κ → W)
    (f : M'.Group →* X) (hf : Function.Injective f)
    (hsf : ∀ i, F (s i) = f (M'.simple i)) :
    ∀ a b, Relation.ReflTransGen (fun a b => s a * s b ≠ s b * s a) a b := by
  classical
  have : Finite κ := ggIsWeylMatrix_finite hM'
  have : Fintype κ := Fintype.ofFinite κ
  intro a b
  refine Relation.ReflTransGen.mono ?_ a b (ggRC_weyl_connected hM' a b)
  rintro u v ⟨huv, huv2⟩ hcomm
  apply huv2
  have h1 : F (s u * s v) = F (s v * s u) := by rw [hcomm]
  rw [map_mul, map_mul, hsf u, hsf v, ← map_mul, ← map_mul] at h1
  have h2 : M'.simple u * M'.simple v = M'.simple v * M'.simple u := hf h1
  have hsq : (M'.simple u * M'.simple v) ^ 2 = 1 := by
    rw [pow_two]
    calc (M'.simple u * M'.simple v) * (M'.simple u * M'.simple v)
        = M'.simple u * (M'.simple v * M'.simple u) * M'.simple v := by group
      _ = M'.simple u * (M'.simple u * M'.simple v) * M'.simple v := by rw [← h2]
      _ = (M'.simple u * M'.simple u) * (M'.simple v * M'.simple v) := by group
      _ = 1 := by
        have hu : M'.simple u * M'.simple u = 1 := by
          simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
            M'.toCoxeterSystem.simple_mul_simple_self u
        have hv : M'.simple v * M'.simple v = 1 := by
          simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
            M'.toCoxeterSystem.simple_mul_simple_self v
        rw [hu, hv, mul_one]
  have hdvd : orderOf (M'.simple u * M'.simple v) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hord : orderOf (M'.simple u * M'.simple v) = M'.M u v := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M'.toCoxeterSystem.orderOf_simple_mul_simple u v
  have hle : M'.M u v ≤ 2 := by
    rw [← hord]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < M'.M u v := by
    rw [← hord]
    exact Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hne1 : M'.M u v ≠ 1 := M'.off_diagonal u v huv
  omega

private theorem isReflection_simple_reindex {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type} {n : ℕ} {e' : Fin n ≃ ι}
    {e : ((CoxeterMatrix.B n).reindex e').Group ≃* ↥A}
    (hP : GGCoxeterPres p A ((CoxeterMatrix.B n).reindex e') e)
    (E : (CoxeterMatrix.B n).Group ≃* ↥A)
    (hE : E = ((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e) :
    ∀ i : Fin n, GGIsReflection p
      ((E ((CoxeterMatrix.B n).simple i) : ↥A) : MulAut ↥Bs) := by
  intro i
  have hEi : E ((CoxeterMatrix.B n).simple i) =
      e (((CoxeterMatrix.B n).reindex e').simple (e' i)) := by
    rw [hE, MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
  have h := hP.2 (e' i)
  rwa [← hEi] at h

private theorem not_le_ker_of_map_eq {W X : Type*} [Group W] [Group X] (F : W →* X)
    {S : Subgroup W} {T : Subgroup X} {ker : Subgroup W} (hmap : Subgroup.map F S = T)
    (hT : ¬ T ≤ Subgroup.map F ker) : ¬ S ≤ ker := by
  intro hS
  apply hT
  intro φ hφ
  rw [← hmap] at hφ
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hφ
  exact Subgroup.mem_map.mpr ⟨z, hS hz, rfl⟩

private theorem exists_neighbour_join_data
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {L : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hEl : CFSG.Assembly.IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs) {n : ℕ} (hn : 2 ≤ n)
    (hp2 : p ≠ 2)
    (E : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hE : ∀ i : Fin n, GGIsReflection p
      ((E ((CoxeterMatrix.B n).simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
    (F : (CoxeterMatrix.B n).Group →* MulAut ↥Bs)
    (hF : F = (ggAutomizerJoin L Bs 𝒦).subtype.comp E.toMonoidHom)
    {T : Subgroup (MulAut ↥Bs)} (hTKleA : T ≤ ggAutomizerJoin L Bs 𝒦)
    {κ : Type} {M' : CoxeterMatrix κ} (hM' : GGIsWeylMatrix M')
    (f : M'.Group ≃* ↥T)
    (hf : ∀ i, GGIsReflection p ((f (M'.simple i) : ↥T) : MulAut ↥Bs)) :
    ∃ s : κ → (CoxeterMatrix.B n).Group,
      (∀ i, F (s i) = (f (M'.simple i) : MulAut ↥Bs)) ∧
      (∀ a, ∃ (w : (CoxeterMatrix.B n).Group) (i : Fin n),
        s a = w * (CoxeterMatrix.B n).simple i * w⁻¹) ∧
      (∀ a b, Relation.ReflTransGen (fun a b => s a * s b ≠ s b * s a) a b) ∧
      Subgroup.map F (Subgroup.closure (Set.range s)) = T := by
  let s : κ → (CoxeterMatrix.B n).Group := fun i =>
    E.symm ⟨(f (M'.simple i) : MulAut ↥Bs), hTKleA (f (M'.simple i)).2⟩
  have hsF : ∀ i, F (s i) = (f (M'.simple i) : MulAut ↥Bs) := by
    intro i
    rw [hF]
    simp [s]
  let f' : M'.Group →* MulAut ↥Bs := T.subtype.comp f.toMonoidHom
  have hf'inj : Function.Injective f' := Subtype.val_injective.comp f.injective
  have hf'r : f'.range = T := range_subtype_comp f.toMonoidHom f.surjective
  refine ⟨s, hsF, ?_, ?_, ?_⟩
  · exact fun a => exists_conj_simple_of_typeB hEl hNT hAind hn hp2 E hE hTKleA f hf a
  · exact reflTransGen_ne_comm_of_weyl hM' F s f' hf'inj hsF
  · rw [map_closure_range_eq_of_simple M' F s f' hsF, hf'r]

private theorem neighbour_closure_eq_top
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {y : G} {K : Subgroup G} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hN : GGNbr p B x D J y K)
    {n : ℕ} (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (F : (CoxeterMatrix.B n).Group →* MulAut ↥Bs) (hFinj : Function.Injective F)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (hrefl : ∀ i : Fin n, IsLinRefl (ggLin (p := p) ι (F ((CoxeterMatrix.B n).simple i))))
    {κ : Type} {M' : CoxeterMatrix κ} (f : M'.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (s : κ → (CoxeterMatrix.B n).Group)
    (hsF : ∀ i, F (s i) = (f (M'.simple i) : MulAut ↥Bs))
    (hconj : ∀ a, ∃ (w : (CoxeterMatrix.B n).Group) (i : Fin n),
      s a = w * (CoxeterMatrix.B n).simple i * w⁻¹)
    (hconn : ∀ a b, Relation.ReflTransGen (fun a b => s a * s b ≠ s b * s a) a b)
    (hmapS : Subgroup.map F (Subgroup.closure (Set.range s)) =
      ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hTKnot : ¬ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ Subgroup.map F (coxeterBSign n).ker) :
    Subgroup.closure (Set.range s) = ⊤ := by
  let T : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  have hfix : ∀ v : V, (∀ a, ggLin (p := p) ι (F (s a)) v = v) → v = 0 := by
    intro v hv
    exact hR.eq_zero_of_forall_ggLin_fix hTBF hWI hN ι F T rfl f s hsF v hv
  have hD : ¬ Subgroup.closure (Set.range s) ≤ (coxeterBSign n).ker :=
    not_le_ker_of_map_eq F hmapS hTKnot
  exact coxeterB_closure_eq_top_of_fix_eq_zero hp2 hn ((ggLin (p := p) ι).comp F)
    ((ggLin_injective ι).comp hFinj) hrefl s hconj hconn hD hfix

private theorem automizer_sup_le_automizerJoin {G : Type} [Group G] {Bs L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {K : Subgroup G} (hK : K ∈ 𝒦) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  rw [ggAutomizerJoin]
  exact sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl))

private theorem exists_join_eq_of_neighbour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {y : G} {K : Subgroup G} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hN : GGNbr p B x D J y K)
    (hK : K ∈ 𝒦) {n : ℕ} (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (E : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hE : ∀ i : Fin n, GGIsReflection p
      ((E ((CoxeterMatrix.B n).simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (hTKnot : ¬ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      Subgroup.map ((ggAutomizerJoin L Bs 𝒦).subtype.comp E.toMonoidHom) (coxeterBSign n).ker)
    {κ : Type} {M' : CoxeterMatrix κ} (hM' : GGIsWeylMatrix M')
    (f : M'.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hf : ∀ i, GGIsReflection p
      ((f (M'.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  have hEl : CFSG.Assembly.IsElemAbelian p Bs := hR.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hAind := ggAutomizerJoin_le_ggInduced_top (G := G) (Bs := Bs) L 𝒦
  let A : Subgroup (MulAut ↥Bs) := ggAutomizerJoin L Bs 𝒦
  let T : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  have hTKleA : T ≤ A := automizer_sup_le_automizerJoin hK
  let F : (CoxeterMatrix.B n).Group →* MulAut ↥Bs := A.subtype.comp E.toMonoidHom
  have hFinj : Function.Injective F := Subtype.val_injective.comp E.injective
  have hFrange : F.range = A := range_subtype_comp E.toMonoidHom E.surjective
  obtain ⟨s, hsF, hconj, hconn, hmapS⟩ :=
    exists_neighbour_join_data hEl hNT hAind hn hp2 E hE F rfl hTKleA hM' f hf
  have htop : Subgroup.closure (Set.range s) = ⊤ :=
    neighbour_closure_eq_top hR hTBF hWI hN hn hp2 F hFinj ι
      (fun i => exists_of_ggIsReflection (p := p) ι (hE i)) f s hsF hconj hconn hmapS hTKnot
  calc T = Subgroup.map F (Subgroup.closure (Set.range s)) := hmapS.symm
    _ = Subgroup.map F ⊤ := by rw [htop]
    _ = F.range := Subgroup.map_top F
    _ = A := hFrange

theorem GGSecFiveRouteCfg.exists_join_eq_of_typeB {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixB M) :
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  classical
  by_cases h1 : 𝒦.card ≤ 1
  · exact hR.exists_join_eq_of_card_le_one h1
  obtain ⟨n, e', hn, rfl⟩ := hM
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have : Fact p.Prime := ⟨hp⟩
  let A : Subgroup (MulAut ↥Bs) := ggAutomizerJoin L Bs 𝒦
  let E : (CoxeterMatrix.B n).Group ≃* ↥A :=
    ((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e
  have hEsimple := isReflection_simple_reindex hP E rfl
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) hR.1.1.2.1.2.1
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hne : 𝒦.Nonempty := by
    have hle2 : 𝒦.card ≤ 2 := hR.2.2.2.1.1
    exact Finset.card_pos.mp (by omega)
  obtain ⟨K, hK, hTKnot⟩ := exists_not_le_sign_map_of_typeB hne hn E
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  obtain ⟨κ, M', hM', f, hf⟩ :=
    hR.1.2.2.2.2.1 y K hN (hR.2.1 y K hN) (Or.inr hR.2.1)
  exact ⟨y, K, hN, exists_join_eq_of_neighbour hR hTBF hWI hN hK hn hp2 E hEsimple ι hTKnot
    hM' f hf⟩

end CFSG.StandardType

end
