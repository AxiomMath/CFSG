module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.SeitzReduction.SymplecticPilot TableBSymp SpCoord Multiplicative

theorem ggTBJ_sp_full_torus_automizer {p : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (q : MulAut (Fin 3 → Multiplicative (ZMod p))) (hq : IsSignedPerm q)
    (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* (spTorusSp (m := 3) hζ).range)
    (hκ : ∀ f, (κ f : LargeEvenSpGroup K 3) = spTorusSp hζ (q f)) :
    (ggAutomizer ⊤ (spTorusSp (m := 3) hζ).range).map
      (MulAut.congr κ.symm).toMonoidHom = (ggSpSigned_rho p 3).range := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let T := (spTorusSp (m := 3) hζ).range
  let κ₀ := MonoidHom.ofInjective (spTorusSp_injective (m := 3) hζ hζo)
  have hκ₀ : ∀ f, (κ₀ f : LargeEvenSpGroup K 3) = spTorusSp hζ f := fun _ => rfl
  let H₀ := (ggAutomizer ⊤ T).map (MulAut.congr κ₀.symm).toMonoidHom
  have hcanonical : ∀ v : MulAut (Fin 3 → Multiplicative (ZMod p)), IsSignedPerm v → v ∈ H₀ := by
    intro v hv
    apply mem_of_isSignedPerm (H := H₀) ?_ ?_ hv
    · intro i
      refine (mem_map_congr_ggAutomizer_iff T ⊤ κ₀ (sgnAut i)).mpr
        ⟨spSwapSp i, Subgroup.mem_top _, ?_⟩
      intro f
      rw [hκ₀ f, hκ₀ (sgnAut i f)]
      exact ggTBJSpC_conj_spSwapSp hζ i f
    · intro i j hij
      refine (mem_map_congr_ggAutomizer_iff T ⊤ κ₀ (permAut (Equiv.swap i j))).mpr
        ⟨permSp K (Equiv.swap i j), Subgroup.mem_top _, ?_⟩
      intro f
      rw [hκ₀ f, hκ₀ (permAut (Equiv.swap i j) f)]
      exact ggTBJSpC_conj_permSp hζ (Equiv.swap i j) f
  let φ : Fin 3 → MulAut (Fin 3 → Multiplicative (ZMod p)) := ggSpSigned_spReflAut p 3
  let gen : Fin 3 → ↥(SpJoin.spSignedGroup 3 p) := fun i =>
    ⟨SpJoin.spReflPerm 3 p i, SpJoin.spReflPerm_mem_spSignedGroup 3 p i⟩
  have htop : Subgroup.closure (Set.range gen) = ⊤ :=
    ggSpSigned_closure_range_subtype (SpJoin.spReflPerm 3 p)
      (fun i => SpJoin.spReflPerm_mem_spSignedGroup 3 p i) rfl
  have hρgen : (ggSpSigned_rho p 3).range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (ggSpSigned_rho_spReflPerm p 3 i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨gen i, ⟨i, rfl⟩, ggSpSigned_rho_spReflPerm p 3 i⟩
  have hφsigned : ∀ i, IsSignedPerm (φ i) := by
    intro i
    by_cases hi : i.val + 1 < 3
    · change IsSignedPerm (ggSpSigned_spReflAut p 3 i)
      rw [ggSpSigned_spReflAut, dif_pos hi]
      refine ⟨Equiv.swap i ⟨i.val + 1, hi⟩, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
      intro f j
      simp [permAut_apply]
    · change IsSignedPerm (ggSpSigned_spReflAut p 3 i)
      rw [ggSpSigned_spReflAut, dif_neg hi]
      exact isSignedPerm_sgnAut i
  apply le_antisymm
  · intro u hu
    exact ggSpSigned_isSignedPerm_mem_range (by decide : 1 ≤ 3)
      (ggTBJ_sp_torus_automizer_signed_of_coordinates hp hζo hζ ⊤ q hq κ hκ hu)
  · rw [hρgen, Subgroup.closure_le]
    rintro u ⟨i, rfl⟩
    let v : MulAut (Fin 3 → Multiplicative (ZMod p)) := q * φ i * q⁻¹
    have hv : IsSignedPerm v := (hq.mul (hφsigned i)).mul hq.inv
    obtain ⟨n, hn, hact⟩ :=
      (mem_map_congr_ggAutomizer_iff T ⊤ κ₀ v).mp (hcanonical v hv)
    refine (mem_map_congr_ggAutomizer_iff T ⊤ κ (φ i)).mpr ⟨n, hn, ?_⟩
    intro f
    have h := hact (q f)
    rw [hκ₀ (q f), hκ₀ (v (q f))] at h
    rw [hκ f, hκ (φ i f)]
    have hqinv : (q⁻¹ : MulAut (Fin 3 → Multiplicative (ZMod p))) (q f) = f :=
      q.symm_apply_apply f
    simpa only [v, MulAut.mul_apply, hqinv] using h

theorem ggTBJ_sp_coxeter_of_coordinates {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] {A : Subgroup G} {H : Subgroup (MulAut ↥A)}
    (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* ↥A)
    (hFull : H.map (MulAut.congr κ.symm).toMonoidHom = (ggSpSigned_rho p 3).range) :
    ∃ f : (CoxeterMatrix.B 3).Group ≃* H,
      ∀ i, (f ((CoxeterMatrix.B 3).simple i) : MulAut ↥A) =
        MulAut.congr κ (ggSpSigned_spReflAut p 3 i) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e₀, he₀⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 (by decide : 2 ≤ 3)
  let F : MulAut ↥A ≃* MulAut (Fin 3 → Multiplicative (ZMod p)) := MulAut.congr κ.symm
  let η : H ≃* H.map F.toMonoidHom := H.equivMapOfInjective F.toMonoidHom F.injective
  let Ψ : ↥(SpJoin.spSignedGroup 3 p) ≃* H.map F.toMonoidHom :=
    (MonoidHom.ofInjective (ggSpSigned_rho_injective p 3)).trans
      (MulEquiv.subgroupCongr hFull.symm)
  let f : (CoxeterMatrix.B 3).Group ≃* H := e₀.trans (Ψ.trans η.symm)
  have hΨval (w : ↥(SpJoin.spSignedGroup 3 p)) :
      (Ψ w : MulAut (Fin 3 → Multiplicative (ZMod p))) = ggSpSigned_rho p 3 w := by
    simp only [Ψ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  have hfval (w : (CoxeterMatrix.B 3).Group) :
      F (f w : MulAut ↥A) = ggSpSigned_rho p 3 (e₀ w) := by
    have h := congrArg Subtype.val (η.apply_symm_apply (Ψ (e₀ w)))
    change F (f w : MulAut ↥A) = (Ψ (e₀ w) : MulAut (Fin 3 → Multiplicative (ZMod p))) at h
    exact h.trans (hΨval _)
  have hFback (u : MulAut (Fin 3 → Multiplicative (ZMod p))) : F (MulAut.congr κ u) = u := by
    apply MulEquiv.ext
    intro v
    change κ.symm (κ (u (κ.symm (κ v)))) = u v
    simp
  refine ⟨f, fun i => ?_⟩
  apply F.injective
  rw [hFback, hfval]
  have hi : e₀ ((CoxeterMatrix.B 3).simple i) =
      ⟨SpJoin.spReflPerm 3 p i, SpJoin.spReflPerm_mem_spSignedGroup 3 p i⟩ := Subtype.ext (he₀ i)
  rw [hi]
  exact ggSpSigned_rho_spReflPerm p 3 i

theorem ggTBJ_sp_cover_rank_three_automizers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)  {K : Type}
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L']
    [Finite L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K 3)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p 3 (LargeEvenProj (LargeEvenSpGroup K 3))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K 3)))) L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ κ : (Fin 3 → Multiplicative (ZMod p)) ≃* ↥A,
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).map
        (MulAut.congr κ.symm).toMonoidHom = (ggSpSigned_rho p 3).range ∧
      ((ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map
          (MulAut.congr κ.symm).toMonoidHom =
        Subgroup.closure ({sgnAut (2 : Fin 3), permAut (Equiv.swap (1 : Fin 3) 2)} :
          Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) ∨
        (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map
          (MulAut.congr κ.symm).toMonoidHom =
        Subgroup.closure ({permAut (Equiv.swap (0 : Fin 3) 1),
          permAut (Equiv.swap (1 : Fin 3) 2)} :
          Set (MulAut (Fin 3 → Multiplicative (ZMod p))))) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, ν, Θ, J₀, hζo, hνinj, hνrange, hνtorus, hAmap, hJmap,
      hJ₀, hcount_core, hWeyl⟩ := ggTBJ_sp_inner_model hp hp2 hpq ψ₀ A hA y hy hJ hcount
  let f₀ : Fin 3 → Multiplicative (ZMod p) := Θ.symm ⟨y, hy⟩
  let t : Fin 3 → Kˣ := fun i => zmodPowHom hζ (f₀ i)
  have ht : ∃ i, t i ≠ 1 := by
    by_contra h
    have hti : ∀ i, t i = 1 := by simpa only [not_exists, not_not] using h
    have hf₀ : f₀ = 1 := by
      funext i
      apply ReflSp.zmodPowHom_injective hζ hζo
      simpa [t] using hti i
    have hyone : y = 1 := by
      have h := congrArg (fun f => (Θ f : MulAut L')) hf₀
      simpa [f₀] using h
    exact hy1 hyone
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ Nat.card K := by
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have h3 : 3 ≤ p := by
      have h := hp.two_le
      omega
    have hpos : 0 < Nat.card K - 1 := by omega
    have hle := Nat.le_of_dvd hpos hpq
    omega
  have hJdiag : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({diagSp K 3 t} : Set (LargeEvenSpGroup K 3))) := by
    simpa only [ggTBJSpC_spTorusSp_eq_diagSp, t, f₀] using hJ₀
  obtain ⟨q, κ₀, hq, hκ₀, hpar⟩ :=
    ggTBJ_sp_rank_three_automizer hp hK4 hζo hζ t ht hJdiag hcount_core
  let T := (spTorusSp (m := 3) hζ).range
  let eTA : T ≃* A := (T.equivMapOfInjective ν hνinj).trans (MulEquiv.subgroupCongr hAmap)
  let κ : (Fin 3 → Multiplicative (ZMod p)) ≃* A := κ₀.trans eTA
  have hcoords (Q : Subgroup (LargeEvenSpGroup K 3)) :
      (ggAutomizer (Q.map ν) A).map (MulAut.congr κ.symm).toMonoidHom =
        (ggAutomizer Q T).map (MulAut.congr κ₀.symm).toMonoidHom := by
    rw [F4AutWeyl.ggAutomizer_map_eq hνinj Q T hAmap, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro u
    apply MulEquiv.ext
    intro f
    change κ₀.symm (eTA.symm (eTA (u (eTA.symm (eTA (κ₀ f)))))) = κ₀.symm (u (κ₀ f))
    rw [eTA.symm_apply_apply, eTA.symm_apply_apply]
  have hfull : (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).map
      (MulAut.congr κ.symm).toMonoidHom = (ggSpSigned_rho p 3).range := by
    calc _ = (ggAutomizer ⊤ T).map (MulAut.congr κ₀.symm).toMonoidHom := by
          simpa only [Subgroup.map_top, hνrange] using hcoords ⊤
      _ = _ := ggTBJ_sp_full_torus_automizer hp hζo hζ q hq κ₀ hκ₀
  have hcomp : (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map
      (MulAut.congr κ.symm).toMonoidHom =
        (ggAutomizer J₀ T).map (MulAut.congr κ₀.symm).toMonoidHom := by
    simpa only [hJmap] using hcoords J₀
  refine ⟨κ, hfull, ?_, hWeyl⟩
  rcases hpar with h | h
  · exact Or.inl (hcomp.trans h)
  · exact Or.inr (hcomp.trans h)

theorem ggTBJ_sp_cover_rank_three_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)  {K : Type}
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L']
    [Finite L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K 3)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p 3 (LargeEvenProj (LargeEvenSpGroup K 3))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K 3)))) L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (b : Fin 3) (f : (CoxeterMatrix.B 3).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)),
      (b = 0 ∨ b = 2) ∧
      (∀ i, GGIsReflection p (f ((CoxeterMatrix.B 3).simple i) : MulAut ↥A)) ∧
      ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A =
        Subgroup.closure (Set.range fun j : {j : Fin 3 // j ≠ b} =>
          (f ((CoxeterMatrix.B 3).simple j) : MulAut ↥A)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) := by
  classical
  obtain ⟨κ, hfull, hpar, hWeyl⟩ :=
    ggTBJ_sp_cover_rank_three_automizers hp hp2 hpq ψ₀ A hA y hy hy1 hJ hcount
  obtain ⟨f, hf⟩ := ggTBJ_sp_coxeter_of_coordinates hp hp2 κ hfull
  let φ : Fin 3 → MulAut (Fin 3 → Multiplicative (ZMod p)) := ggSpSigned_spReflAut p 3
  let F : MulAut ↥A ≃* MulAut (Fin 3 → Multiplicative (ZMod p)) := MulAut.congr κ.symm
  have hFφ : ∀ i, F (f ((CoxeterMatrix.B 3).simple i) : MulAut ↥A) = φ i := by
    intro i
    rw [hf i]
    apply MulEquiv.ext
    intro v
    change κ.symm (κ (φ i (κ.symm (κ v)))) = φ i v
    simp
  have hrefl : ∀ i, GGIsReflection p (f ((CoxeterMatrix.B 3).simple i) : MulAut ↥A) := by
    intro i
    rw [hf i]
    by_cases hi : i.val + 1 < 3
    · rw [ggSpSigned_spReflAut, dif_pos hi]
      have hne : i ≠ (⟨i.val + 1, hi⟩ : Fin 3) := by
        intro h
        have h' := congrArg Fin.val h
        simp only [Fin.val_mk] at h'
        omega
      exact ggSpSigned_ggIsReflection_congr hp hp2 κ
        (permAut_swap_sq i ⟨i.val + 1, hi⟩) (card_fix_permAut_swap hp hp2 hne)
    · rw [ggSpSigned_spReflAut, dif_neg hi]
      exact ggSpSigned_ggIsReflection_congr hp hp2 κ (sgnAut_sq i) (card_fix_sgnAut hp hp2 i)
  have hsetC : Set.range (fun j : {j : Fin 3 // j ≠ 0} => φ j) =
      ({sgnAut (2 : Fin 3), permAut (Equiv.swap (1 : Fin 3) 2)} :
        Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) := by
    ext u
    constructor
    · rintro ⟨j, rfl⟩
      have hcases : (j : Fin 3) = 1 ∨ (j : Fin 3) = 2 :=
        (by decide +kernel : ∀ i : Fin 3, i ≠ 0 → i = 1 ∨ i = 2) j j.2
      rcases hcases with h | h <;> simp [φ, ggSpSigned_spReflAut, h]
    · intro hu
      rcases Set.mem_insert_iff.mp hu with hu | hu
      · refine ⟨⟨2, by decide⟩, ?_⟩
        simpa [φ, ggSpSigned_spReflAut] using hu.symm
      · refine ⟨⟨1, by decide⟩, ?_⟩
        simpa [φ, ggSpSigned_spReflAut] using (Set.mem_singleton_iff.mp hu).symm
  have hsetA : Set.range (fun j : {j : Fin 3 // j ≠ 2} => φ j) =
      ({permAut (Equiv.swap (0 : Fin 3) 1), permAut (Equiv.swap (1 : Fin 3) 2)} :
        Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) := by
    ext u
    constructor
    · rintro ⟨j, rfl⟩
      have hcases : (j : Fin 3) = 0 ∨ (j : Fin 3) = 1 :=
        (by decide +kernel : ∀ i : Fin 3, i ≠ 2 → i = 0 ∨ i = 1) j j.2
      rcases hcases with h | h <;> simp [φ, ggSpSigned_spReflAut, h]
    · intro hu
      rcases Set.mem_insert_iff.mp hu with hu | hu
      · refine ⟨⟨0, by decide⟩, ?_⟩
        simpa [φ, ggSpSigned_spReflAut] using hu.symm
      · refine ⟨⟨1, by decide⟩, ?_⟩
        simpa [φ, ggSpSigned_spReflAut] using (Set.mem_singleton_iff.mp hu).symm
  have hJgen (b : Fin 3)
      (hE : (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map F.toMonoidHom =
        Subgroup.closure (Set.range fun j : {j : Fin 3 // j ≠ b} => φ j)) :
      ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A =
        Subgroup.closure (Set.range fun j : {j : Fin 3 // j ≠ b} =>
          (f ((CoxeterMatrix.B 3).simple j) : MulAut ↥A)) := by
    apply Subgroup.map_injective (f := F.toMonoidHom) F.injective
    have himg : F.toMonoidHom '' Set.range (fun j : {j : Fin 3 // j ≠ b} =>
        (f ((CoxeterMatrix.B 3).simple j) : MulAut ↥A)) =
        Set.range (fun j : {j : Fin 3 // j ≠ b} => φ j) := by
      ext u
      constructor
      · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, (hFφ j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨f ((CoxeterMatrix.B 3).simple j), ⟨j, rfl⟩, hFφ j⟩
    rw [MonoidHom.map_closure, himg]
    exact hE
  rcases hpar with hC | hA
  · refine ⟨0, f, Or.inl rfl, hrefl, hJgen 0 ?_, hWeyl⟩
    rw [hsetC]
    exact hC
  · refine ⟨2, f, Or.inr rfl, hrefl, hJgen 2 ?_, hWeyl⟩
    rw [hsetA]
    exact hA

end CFSG.StandardType
