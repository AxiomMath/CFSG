module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteStd
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteA
import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_const_of_mem_centralizer (hK : Nat.card K = 4) {L Bs : Subgroup G}
    {Q : Type} [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {c : Fin 6} {J₁ : Subgroup G}
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {s : ↥Bs} (hsC : (s : G) ∈ Subgroup.centralizer (J₁ : Set G)) :
    ∀ i ∈ Finset.univ.erase c, ∀ j ∈ Finset.univ.erase c,
      βL (Additive.ofMul s) i = βL (Additive.ofMul s) j := by
  intro i hi j hj
  by_contra hne
  have hij : i ≠ j := fun h => hne (by rw [h])
  apply qtwoDB12_pow_val_ne hω hne
  have hPmem : ggPermSU (K := K) (f := 1) (Equiv.swap i j) ∈
      coordBlockSU K 2 1 (Finset.univ.erase c) := by
    refine ggQTwoDUnitSix_coordBlockSU_mono ?_ (qtwoDB12_permSU_mem_coordBlockSU hij)
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  have hPimg : ψ (ggPermSU (K := K) (f := 1) (Equiv.swap i j)) ∈
      NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ := by
    rw [hJ₁]
    exact Subgroup.mem_map_of_mem ψ hPmem
  obtain ⟨n, hnJ, hnf⟩ := NsQuot.mem_img.mp hPimg
  have hsn : (⟨s, hD.BsN s.2⟩ : ↥(Subgroup.normalizer (L : Set G))) * n =
      n * ⟨s, hD.BsN s.2⟩ :=
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp hsC) n hnJ).symm
  obtain ⟨u', hu'mat, hu'ψ⟩ := hind s (hD.BsN s.2)
    (ggPermSU (K := K) (f := 1) (Equiv.swap i j))
  have hψu' : ψ u' = ψ (ggPermSU (K := K) (f := 1) (Equiv.swap i j)) := by
    rw [hu'ψ, ← hnf, ← map_mul, hsn, map_mul, mul_inv_cancel_right]
  have hz : u' * (ggPermSU (K := K) (f := 1) (Equiv.swap i j))⁻¹ ∈
      Subgroup.center (Su K 2 1 6) :=
    hψk (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψu', mul_inv_cancel])
  exact qtwoDB12_diag_eq_of_conj_permSU hK (by norm_num) hu'mat hz

theorem ggQTwoDUnitSix_cent_J (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {x : G} (hxBs : x ∈ Bs)
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) {βL : Additive ↥Bs ≃+ DVec 6}
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1) :
    Bs ⊓ Subgroup.centralizer (J₁ : Set G) = Subgroup.closure {x, (b' : G)} := by
  classical
  have hNL : ∀ n : ↥(Subgroup.normalizer (L : Set G)), ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L :=
    fun n l hl => (Subgroup.mem_normalizer_iff.mp n.2 l).mp hl
  apply le_antisymm
  · intro s hs
    obtain ⟨hsBs, hsC⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨c0, hc0⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [Fintype.card_fin]; norm_num) c
    exact qtwoDB12_mem_closure_of_const (s := ⟨s, hsBs⟩) hxBs hxcoord hc0 hb'
      (ggQTwoDUnitSix_const_of_mem_centralizer hK hD hψk hω hind hJ₁ (s := ⟨s, hsBs⟩) hsC)
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_inf.mpr ⟨hxBs, Subgroup.centralizer_le hJ₁L hxL⟩
    · have hb'd : qTwoChartTwoThree_induces ψ (f ⟨b', hD.BsN b'.2⟩) (qtwoDB39_delDiag ω c) := by
        have hfun : (fun i => ω ^ (βL (Additive.ofMul b') i).val) = qtwoDB39_delDiag ω c := by
          rw [hb']
          exact ggQTwoDUnitSix_single_delDiag ω c
        rw [← hfun]
        exact hind b' (hD.BsN b'.2)
      obtain ⟨θ, -, hθr, hθf⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c)
        (by rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
          Fintype.card_fin]; norm_num) hJ₁L hJ₁Z hJ₁
      have hc := ggQTwoDUnitSix_chart_commute hK hD _ hJ₁L hJ₁Z hJ₁ hθr hθf
        (s := ⟨b', hD.BsN b'.2⟩) (hNL _) hb'd
        (fun i hi => by simp [qtwoDB39_delDiag, (Finset.mem_erase.mp hi).1])
      exact Subgroup.mem_inf.mpr
        ⟨b'.2, Subgroup.mem_centralizer_iff.mpr fun j hj => (hc j hj).symm⟩

theorem ggQTwoDUnitSix_layer_eq (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {x : G}
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L)
    [Group.IsPerfect ↥J₁] (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥(Subgroup.normalizer (L : Set G))} {ω : Kˣ} (hω : orderOf ω = 3)
    (hb' : qTwoChartTwoThree_induces ψ (f b') (qtwoDB39_delDiag ω c)) :
    LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G)) = J₁ ∧
      IsComponentOf J₁ (L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G)) := by
  classical
  have hω1 : ω ≠ 1 := by
    rintro rfl
    simp at hω
  have hNL : ∀ n : ↥(Subgroup.normalizer (L : Set G)), ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L :=
    fun n l hl => (Subgroup.mem_normalizer_iff.mp n.2 l).mp hl
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxL) l hl
  have hCinf : L ⊓ Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G) =
      L ⊓ Subgroup.centralizer ({(b' : G)} : Set G) := by
    have hCpair : Subgroup.centralizer (Subgroup.closure {x, (b' : G)} : Set G) =
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({(b' : G)} : Set G) := by
      rw [Subgroup.centralizer_closure]
      ext g
      simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
        Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    rw [hCpair, ← inf_assoc, inf_eq_left.mpr hLx]
  obtain ⟨θ, hθ, hθr, hθf⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
      Fintype.card_fin]; norm_num) hJ₁L hJ₁Z hJ₁
  have hcomp : IsComponentOf J₁ (L ⊓ Subgroup.centralizer ({(b' : G)} : Set G)) :=
    ggQTwoDUnitSix_J_comp_L hK hD hψr c hJ₁L hJ₁Z hJ₁ hψk hθ hθr hθf (hNL b') hω hb'
  rw [hCinf]
  refine ⟨le_antisymm ?_ (le_sSup hcomp), hcomp⟩
  rw [LargeEvenLayer]
  refine sSup_le fun K' hK' => ?_
  have hK'perf : Group.IsPerfect ↥K' := Group.isPerfect_def.2 hK'.2.2.1
  have hK'L : K' ≤ L := hK'.1.trans inf_le_left
  have hK'N : K' ≤ Subgroup.normalizer (L : Set G) := hK'L.trans hD.LN
  refine hD.le_of_img_le hJ₁L hK'L ?_
  have hperfImg : Group.IsPerfect ↥(NsQuot.img (Subgroup.normalizer (L : Set G)) f K') := by
    have : Group.IsPerfect ↥(K'.subgroupOf (Subgroup.normalizer (L : Set G))) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'N).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hK'N).symm.surjective
    exact Group.IsPerfect.map f
  have himgF : NsQuot.img (Subgroup.normalizer (L : Set G)) f K' ≤
      (CFSG.ClassicalInvolution.Balance.fixedGroup
        (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c))).map ψ := by
    intro q hq
    obtain ⟨u, huK, rfl⟩ := NsQuot.mem_img.mp hq
    obtain ⟨huL, hub⟩ := Subgroup.mem_inf.mp (hK'.1 huK)
    obtain ⟨w, hw⟩ : f u ∈ ψ.range := by
      rw [hψr]
      exact NsQuot.mem_img.mpr ⟨u, huL, rfl⟩
    exact ⟨w, ggQTwoDUnitSix_fixed_of_commute hK hψk hω hb' (l := u)
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hub)) hw, hw⟩
  calc NsQuot.img (Subgroup.normalizer (L : Set G)) f K'
      = ⁅NsQuot.img (Subgroup.normalizer (L : Set G)) f K',
          NsQuot.img (Subgroup.normalizer (L : Set G)) f K'⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅(CFSG.ClassicalInvolution.Balance.fixedGroup
          (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c))).map ψ,
        (CFSG.ClassicalInvolution.Balance.fixedGroup
          (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c))).map ψ⁆ :=
        Subgroup.commutator_mono himgF himgF
    _ = (⁅CFSG.ClassicalInvolution.Balance.fixedGroup
          (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c)),
        CFSG.ClassicalInvolution.Balance.fixedGroup
          (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c))⁆).map ψ :=
        (Subgroup.map_commutator _ _ _).symm
    _ ≤ (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ :=
        Subgroup.map_mono (qtwoDB39_commutator_le hK hω1)
    _ = NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ := hJ₁.symm

omit [Finite G] in
theorem ggQTwoDUnitSix_not_small (hK : Nat.card K = 4) {n : ℕ} (hn : n = 5) {J : Subgroup G}
    {θ : Su K 2 1 n →* G} (hθ : Function.Injective θ) (hθr : θ.range = J) :
    ¬ LargeEvenSmall J := by
  subst hn
  have hcard : Nat.card ↥J = 13685760 := by
    rw [← hθr, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hθ, Subgroup.card_top,
      card_Su_five hK]
  exact not_largeEvenSmall_of_map_big (MonoidHom.id G) J
    (Or.inr (by rw [Subgroup.map_id, hcard]; norm_num))

theorem ggQTwoDUnitSix_stdSub (hK : Nat.card K = 4) {B L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) (hBsE : CFSG.Open.IsElemAbelian 3 Bs)
    (hBBs : B ≤ Bs) {x : G} (hxB : x ∈ B) (hxBs : x ∈ Bs) (hxord : orderOf x = 3)
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) {βL : Additive ↥Bs ≃+ DVec 6}
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    LargeEvenStdSub 3 B x L (Subgroup.closure {x, (b' : G)}) J₁ := by
  have hb'd : qTwoChartTwoThree_induces ψ (f ⟨b', hD.BsN b'.2⟩) (qtwoDB39_delDiag ω c) := by
    have hfun : (fun i => ω ^ (βL (Additive.ofMul b') i).val) = qtwoDB39_delDiag ω c := by
      rw [hb']
      exact ggQTwoDUnitSix_single_delDiag ω c
    rw [← hfun]
    exact hind b' (hD.BsN b'.2)
  have hcore := ggQTwoDUnitSix_layer_eq hK hD hψr hψk hxL hJ₁L hJ₁Z hJ₁
    (b' := ⟨b', hD.BsN b'.2⟩) hω hb'd
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  obtain ⟨θ, hθ, hθr, -⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c) (by omega)
    hJ₁L hJ₁Z hJ₁
  unfold LargeEvenStdSub
  exact ⟨qtwoDB13_stdSubPre_of hBsE hBBs hxB hxBs hxord (by norm_num) hxcoord hb' hb'B hcore.1
    hcore.2 (ggQTwoDUnitSix_cent_J hK hD hψk hxBs hxL hxcoord hω hind hJ₁L hJ₁Z hJ₁ hb'),
    fun _ => ggQTwoDUnitSix_not_small hK h5 hθ hθr⟩

end CFSG.StandardType.QTwo

end
