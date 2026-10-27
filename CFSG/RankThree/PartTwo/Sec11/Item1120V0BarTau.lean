module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1120V0Bar

variable {G : Type} [Group G] [Finite G]

theorem thetaAut_mul (Y : Subgroup G) {m n : G} (hm : m ∈ Subgroup.normalizer (Y : Set G))
    (hn : n ∈ Subgroup.normalizer (Y : Set G)) :
    Sec4.Item426.thetaAut Y (Subgroup.mul_mem _ hm hn) =
      Sec4.Item426.thetaAut Y hm * Sec4.Item426.thetaAut Y hn := by
  exact (congrArg (⇑(Sec4.thetaQuotMulAut Y))
    (map_mul (Sec4.compAction Y) (⟨m, hm⟩ : Subgroup.normalizer (Y : Set G)) ⟨n, hn⟩)).trans
    (map_mul (Sec4.thetaQuotMulAut Y) _ _)

theorem thetaAut_inv (Y : Subgroup G) {n : G} (hn : n ∈ Subgroup.normalizer (Y : Set G)) :
    Sec4.Item426.thetaAut Y (Subgroup.inv_mem _ hn) = (Sec4.Item426.thetaAut Y hn)⁻¹ := by
  exact (congrArg (⇑(Sec4.thetaQuotMulAut Y))
    (map_inv (Sec4.compAction Y) (⟨n, hn⟩ : Subgroup.normalizer (Y : Set G)))).trans
    (map_inv (Sec4.thetaQuotMulAut Y) _)

theorem thetaAut_congr (Y : Subgroup G) {m n : G} (hm : m ∈ Subgroup.normalizer (Y : Set G))
    (hn : n ∈ Subgroup.normalizer (Y : Set G)) (e : m = n) :
    Sec4.Item426.thetaAut Y hm = Sec4.Item426.thetaAut Y hn := by
  subst e
  rfl

theorem thetaAut_zpow (Y : Subgroup G) {n : G} (hn : n ∈ Subgroup.normalizer (Y : Set G))
    (k : ℤ) :
    Sec4.Item426.thetaAut Y (Subgroup.zpow_mem _ hn k) = Sec4.Item426.thetaAut Y hn ^ k := by
  exact (congrArg (⇑(Sec4.thetaQuotMulAut Y))
    (map_zpow (Sec4.compAction Y) (⟨n, hn⟩ : Subgroup.normalizer (Y : Set G)) k)).trans
    (map_zpow (Sec4.thetaQuotMulAut Y) _ k)

theorem thetaAut_of_mem (Y : Subgroup G) {y : G} (hy : y ∈ Y)
    (hyN : y ∈ Subgroup.normalizer (Y : Set G)) :
    Sec4.Item426.thetaAut Y hyN =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨y, hy⟩) := by
  show Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨y, hyN⟩) =
    MulAut.conj ((⟨y, hy⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y)
  ext q
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem thetaAut_eq_one_of_forall_commute (Y : Subgroup G) {n : G}
    (hn : n ∈ Subgroup.normalizer (Y : Set G)) (hc : ∀ z ∈ Y, n * z = z * n) :
    Sec4.Item426.thetaAut Y hn = 1 := by
  show Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨n, hn⟩) = 1
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change n * (l : G) * n⁻¹ = l
  rw [hc l l.2, mul_inv_cancel_right]

theorem inv_mul_mem_thetaQuotCentralizer_of_thetaAut_eq (Y : Subgroup G) {m n : G}
    (hm : m ∈ Subgroup.normalizer (Y : Set G)) (hn : n ∈ Subgroup.normalizer (Y : Set G))
    (h : Sec4.Item426.thetaAut Y hm = Sec4.Item426.thetaAut Y hn) :
    m⁻¹ * n ∈ Sec4.thetaQuotCentralizer Y := by
  have hx : m⁻¹ * n ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn
  have key : Sec4.Item426.thetaAut Y hx = 1 := by
    rw [thetaAut_mul Y (Subgroup.inv_mem _ hm) hn, thetaAut_inv Y hm, h, inv_mul_cancel]
  unfold Sec4.thetaQuotCentralizer
  exact Subgroup.mem_map.mpr ⟨⟨m⁻¹ * n, hx⟩, key, rfl⟩

@[expose] noncomputable def thetaAutHom (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
  (Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)

theorem mem_closure_sup_thetaQuotCentralizer (Y : Subgroup G) {u v b : G}
    (hu : u ∈ Subgroup.normalizer (Y : Set G)) (hv : v ∈ Subgroup.normalizer (Y : Set G))
    (hb : b ∈ Subgroup.normalizer (Y : Set G))
    (hmem : Sec4.Item426.thetaAut Y hb ∈
      Subgroup.closure ({Sec4.Item426.thetaAut Y hu, Sec4.Item426.thetaAut Y hv} :
        Set (MulAut (Y ⧸ aschbacherSolvableCore 3 Y)))) :
    b ∈ Subgroup.closure ({u, v} : Set G) ⊔ Sec4.thetaQuotCentralizer Y := by
  have hmap : (Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩} :
      Set (Subgroup.normalizer (Y : Set G)))).map (thetaAutHom Y) =
      Subgroup.closure ({thetaAutHom Y ⟨u, hu⟩, thetaAutHom Y ⟨v, hv⟩} :
        Set (MulAut (Y ⧸ aschbacherSolvableCore 3 Y))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have hmem' : thetaAutHom Y ⟨b, hb⟩ ∈ (Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩} :
      Set (Subgroup.normalizer (Y : Set G)))).map (thetaAutHom Y) := by
    rw [hmap]
    exact hmem
  obtain ⟨w, hw, hwb⟩ := Subgroup.mem_map.mp hmem'
  have hwG : (w : G) ∈ Subgroup.closure ({u, v} : Set G) := by
    have h := Subgroup.mem_map_of_mem (Subgroup.normalizer (Y : Set G)).subtype hw
    rw [MonoidHom.map_closure, Set.image_pair] at h
    exact h
  have hinv := inv_mul_mem_thetaQuotCentralizer_of_thetaAut_eq Y w.2 hb hwb
  have hprod := Subgroup.mul_mem_sup hwG hinv
  rwa [mul_inv_cancel_left] at hprod

theorem isPGroup_closure_thetaAut (Y : Subgroup G) {u v w : G}
    (hu : u ∈ Subgroup.normalizer (Y : Set G)) (hv : v ∈ Subgroup.normalizer (Y : Set G))
    (hw : w ∈ Subgroup.normalizer (Y : Set G))
    (hP : IsPGroup 3 (Subgroup.closure ({u, v, w} : Set G))) :
    IsPGroup 3 (Subgroup.closure ({Sec4.Item426.thetaAut Y hu, Sec4.Item426.thetaAut Y hv,
      Sec4.Item426.thetaAut Y hw} : Set (MulAut (Y ⧸ aschbacherSolvableCore 3 Y)))) := by
  have hsub : Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩} :
      Set (Subgroup.normalizer (Y : Set G))) ≤
      (Subgroup.closure ({u, v, w} : Set G)).comap (Subgroup.normalizer (Y : Set G)).subtype := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.mem_comap.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact Subgroup.mem_comap.mpr
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · exact Subgroup.mem_comap.mpr
        (Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hP' : IsPGroup 3 (Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩} :
      Set (Subgroup.normalizer (Y : Set G)))) :=
    IsPGroup.to_le
      (hP.comap_of_injective (Subgroup.normalizer (Y : Set G)).subtype Subtype.coe_injective) hsub
  have hmap : (Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩} :
      Set (Subgroup.normalizer (Y : Set G)))).map (thetaAutHom Y) =
      Subgroup.closure ({thetaAutHom Y ⟨u, hu⟩, thetaAutHom Y ⟨v, hv⟩, thetaAutHom Y ⟨w, hw⟩} :
        Set (MulAut (Y ⧸ aschbacherSolvableCore 3 Y))) := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_pair]
  have key := hP'.map (thetaAutHom Y)
  rw [hmap] at key
  exact key

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
