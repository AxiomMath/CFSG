module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalLin
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

theorem exists_mem_inf_eq_sup_of_omegaPlus {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {D : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D) :
    ∃ e ∈ D, e ∈ L ∧ e ≠ 1 ∧ D = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
  classical
  let E : Subgroup G := Bs ⊓ L
  have hxL : x ∉ L := by
    intro hxLin
    have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
    have hxZ : (⟨x, hxLin⟩ : ↥L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxcent l l.2
    obtain ⟨k, hk⟩ := hZ2 ⟨⟨x, hxLin⟩, hxZ⟩
    have hxpow : x ^ 3 = 1 := by
      have hxBs : x ∈ Bs := by
        have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
          rw [hBL]
          exact Subgroup.mem_zpowers x
        exact this.1
      exact hBs.2 x hxBs
    have hx3 : orderOf x = 3 := orderOf_eq_prime hxpow hx1
    have hk' : (⟨x, hxLin⟩ : ↥L) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf (⟨x, hxLin⟩ : ↥L) ∣ 2 ^ k :=
      orderOf_dvd_iff_pow_eq_one.mpr hk'
    have h3x : orderOf (⟨x, hxLin⟩ : ↥L) = 3 := by
      rw [Subgroup.orderOf_mk x hxLin]
      exact hx3
    rw [h3x] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  have hxE : x ∉ E := fun h => hxL h.2
  have hE3 : IsPGroup 3 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro y
    exact ⟨1, by
      apply Subtype.ext
      simpa using hBs.2 (y : G) y.2.1⟩
  have hErelBs : E.relIndex Bs = 3 := by
    have h := Subgroup.relIndex_mul_card (H := E) (K := Bs)
    rw [inf_eq_left.mpr (show E ≤ Bs from inf_le_left), hcardE, hcard] at h
    have hmul : E.relIndex Bs * 3 ^ 4 = 3 * 3 ^ 4 := by
      rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3 ^ 4) hmul
  have hErelD_le : E.relIndex D ≤ 3 := by
    have h := Subgroup.relIndex_le_of_le_right (H := E) (K := D) (L := Bs) hDB (by
      rw [hErelBs]; norm_num)
    rwa [hErelBs] at h
  have hDEne : E ⊓ D ≠ ⊥ := by
    intro hbot
    have hcard' : Nat.card ↥(E ⊓ D) = 1 := by rw [hbot, Subgroup.card_bot]
    have hmul := Subgroup.relIndex_mul_card (H := E) (K := D)
    rw [hcard', mul_one, hDcard] at hmul
    have hle : E.relIndex D ≤ 3 := hErelD_le
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E ⊓ D, e ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton ↥(E ⊓ D) := ⟨fun a b => Subtype.ext (by
      rw [h a a.2, h b b.2])⟩
    apply hDEne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, hy⟩ : ↥(E ⊓ D)) = 1 := Subsingleton.elim _ _
    have : y = 1 := congrArg Subtype.val h1
    simpa using this
  have heD : e ∈ D := he.2
  have heE : e ∈ E := he.1
  have heL : e ∈ L := heE.2
  have heBs : e ∈ Bs := heE.1
  have he3 : e ^ 3 = 1 := hBs.2 e heBs
  have hx3 : x ^ 3 = 1 := by
    have hxBs : x ∈ Bs := by
      have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [hBL]
        exact Subgroup.mem_zpowers x
      exact this.1
    exact hBs.2 x hxBs
  have hxorder : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have heorder : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hnotmem : e ∉ Subgroup.zpowers x := by
    intro hmem
    have heq : Subgroup.zpowers e = Subgroup.zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
      rw [Nat.card_zpowers, Nat.card_zpowers, heorder, hxorder]
    have hxL' : x ∈ L := Subgroup.zpowers_le.mpr heL (heq ▸ Subgroup.mem_zpowers x)
    exact hxL hxL'
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
    · have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
        rw [lt_iff_le_and_ne]
        refine ⟨le_sup_left, ?_⟩
        intro h
        have hesup : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers e :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
        rw [← h] at hesup
        exact hnotmem hesup
      have hcard_gt : 3 < Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) := by
        have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
          rw [Nat.card_zpowers, hxorder]
        have hlecard : Nat.card ↥(Subgroup.zpowers x) ≤
            Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion le_sup_left)
            (Subgroup.inclusion_injective le_sup_left)
        have hne : Nat.card ↥(Subgroup.zpowers x) ≠
            Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) := by
          intro hc
          have hEq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
            apply Subgroup.eq_of_le_of_card_ge le_sup_left
            rw [← hc]
          exact hlt.ne hEq
        omega
      have hcard_dvd : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) ∣ 9 := by
        have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers e ≤ D :=
          sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
        have h := Subgroup.card_dvd_of_le hle
        rwa [hDcard] at h
      have hcard9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) = 9 := by
        have hle9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) ≤ 9 :=
          Nat.le_of_dvd (by norm_num) hcard_dvd
        set c := Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) with hc
        have hcgt : 3 < c := hcard_gt
        have hcle : c ≤ 9 := hle9
        have hcdvd : c ∣ 9 := hcard_dvd
        interval_cases c <;> norm_num at hcdvd
        norm_num
      rw [hcard9, hDcard]
      norm_num
  exact ⟨e, heD, heL, he1, hDgen⟩
theorem exists_lift_mem_inf_centralizer_qMap {Bs L : Subgroup G} {x e : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    {D : Subgroup G} (hDB : D ≤ Bs) (heD : e ∈ D) (heL : e ∈ L)
    (hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers e)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    {r : OrthRest.RPlus K 4}
    (hr : r ∈ Subgroup.centralizer ({qMap (K := K) θ ⟨e, heL⟩} :
      Set (OrthRest.RPlus K 4))) :
    ∃ l : ↥L, (l : G) ∈ L ⊓ Subgroup.centralizer (D : Set G) ∧ qMap (K := K) θ l = r := by
  classical
  have heBs : e ∈ Bs := hDB heD
  have he3 : e ^ 3 = 1 := hBs.2 e heBs
  obtain ⟨l, hl⟩ := qMap_surjective (K := K) θ r
  rw [Subgroup.mem_centralizer_singleton_iff] at hr
  let z : ↥L := l * ⟨e, heL⟩ * l⁻¹ * ⟨e, heL⟩⁻¹
  have hzq : qMap (K := K) θ z = 1 := by
    show qMap (K := K) θ (l * ⟨e, heL⟩ * l⁻¹ * ⟨e, heL⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hl, hr]
    group
  have hzc : z ∈ Subgroup.center L := by
    rw [← qMap_ker (K := K) θ]
    exact hzq
  have hcomm : Commute z (⟨e, heL⟩ : ↥L) :=
    (Subgroup.mem_center_iff.mp hzc ⟨e, heL⟩).symm
  have hconj : l * ⟨e, heL⟩ * l⁻¹ = z * ⟨e, heL⟩ := by
    show l * ⟨e, heL⟩ * l⁻¹ = (l * ⟨e, heL⟩ * l⁻¹ * ⟨e, heL⟩⁻¹) * ⟨e, heL⟩
    group
  have hconj3 : (l * ⟨e, heL⟩ * l⁻¹) ^ 3 = 1 := by
    rw [conj_pow, show (⟨e, heL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using he3),
      mul_one, mul_inv_cancel]
  have hz3 : z ^ 3 = 1 := by
    have h1 : z ^ 3 * (⟨e, heL⟩ : ↥L) ^ 3 = 1 := by
      rw [← hcomm.mul_pow, ← hconj]
      exact hconj3
    rwa [show (⟨e, heL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using he3), mul_one] at h1
  have hz1 : z = 1 := by
    obtain ⟨n, hn⟩ := hZ2 ⟨z, hzc⟩
    have h2 : z ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hdvd2 : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2)
  have hle : (l : G) * e = e * (l : G) := by
    have h1 : l * ⟨e, heL⟩ * l⁻¹ = ⟨e, heL⟩ := by rw [hconj, hz1, one_mul]
    have h2 : (l : G) * e * (l : G)⁻¹ = e := congrArg Subtype.val h1
    calc (l : G) * e = (l : G) * e * (l : G)⁻¹ * (l : G) := by group
      _ = e * (l : G) := by rw [h2]
  refine ⟨l, ?_, hl⟩
  refine Subgroup.mem_inf.mpr ⟨l.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hcentD : D ≤ Subgroup.centralizer ({(l : G)} : Set G) := by
    rw [hDgen]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2)).symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hle.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcentD hd)
theorem map_subgroupOf_inf_centralizer_eq_centralizer_qMap {Bs L : Subgroup G} {x e : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    {D : Subgroup G} (hDB : D ≤ Bs) (heD : e ∈ D) (heL : e ∈ L)
    (hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers e)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L).map (qMap (K := K) θ) =
      Subgroup.centralizer ({qMap (K := K) θ ⟨e, heL⟩} :
        Set (OrthRest.RPlus K 4)) := by
  classical
  ext r
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hlinf : (l : G) ∈ L ⊓ Subgroup.centralizer (D : Set G) := Subgroup.mem_subgroupOf.mp hl
    have hlC : (l : G) ∈ Subgroup.centralizer (D : Set G) := hlinf.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hlC e heD).symm
  · intro hr
    obtain ⟨l, hlK, hlq⟩ := exists_lift_mem_inf_centralizer_qMap hZ2 hBs hLx hDB heD heL hDgen θ hr
    have hlM : l ∈ (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hlK
    exact Subgroup.mem_map.mpr ⟨l, hlM, hlq⟩
theorem isComponentOf_map_of_isPGroup_ker {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hker : IsPGroup 2 (MonoidHom.ker f)) {L K : Subgroup X}
    (h : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map f) (K.map f) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  haveI : Group.IsPerfect L := ⟨hq.1⟩
  haveI : Nontrivial (L ⧸ Subgroup.center L) := hq.2.toNontrivial
  haveI : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  have hqnative : CFSG.IsQuasisimple L :=
    ⟨⟨hq.1⟩, hq.2, by
      have hnc := Group.IsPerfect.not_isMulCommutative (G := L ⧸ Subgroup.center L)
      simpa only [isMulCommutative_iff, not_forall] using hnc⟩
  have hN2 : IsPGroup 2 (f.ker.subgroupOf L) := by
    have h := (hker.to_subgroup ((L ⊓ f.ker).subgroupOf f.ker)).of_equiv
      ((Subgroup.subgroupOfEquivOfLe inf_le_right).trans
        (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
    rwa [Subgroup.inf_subgroupOf_left] at h
  have hNne : f.ker.subgroupOf L ≠ ⊤ := by
    intro htop
    have hL2 : IsPGroup 2 L := by
      have h := hN2
      rw [htop] at h
      exact h.of_equiv Subgroup.topEquiv
    exact (Group.IsPerfect.not_isNilpotent (G := L)) hL2.isNilpotent
  have hnot : ¬ L ≤ f.ker := fun hle => hNne (Subgroup.subgroupOf_eq_top.mpr hle)
  have hmapqs : CFSG.IsQuasisimple (L.map f) :=
    CFSG.LocalCores.isQuasisimple_map hqnative f hnot
  exact ⟨Subgroup.map_mono hLK, CFSG.Open.IsSubnormal.map f hsub,
    ⟨hmapqs.1.commutator_eq_top, hmapqs.2.1⟩⟩
theorem map_centralizer_singleton_mulEquiv {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (y : M) :
    (Subgroup.centralizer (Set.singleton y)).map e.toMonoidHom =
      Subgroup.centralizer (Set.singleton (e y)) := by
  ext z
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ ({e y} : Set N) := hw
    rw [Set.mem_singleton_iff] at hw'
    subst w
    have hmc : m ∈ Subgroup.centralizer ({y} : Set M) := hm
    rw [Subgroup.mem_centralizer_iff] at hmc
    have hm' : y * m = m * y := hmc y (by simp)
    calc e y * e m = e (y * m) := by rw [map_mul]
      _ = e (m * y) := by rw [hm']
      _ = e m * e y := by rw [map_mul]
  · intro hz
    refine Subgroup.mem_map.mpr ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ ({y} : Set M) := hw
    rw [Set.mem_singleton_iff] at hw'
    subst w
    have hzc : z ∈ Subgroup.centralizer ({e y} : Set N) := hz
    rw [Subgroup.mem_centralizer_iff] at hzc
    have hz' : e y * z = z * e y := hzc (e y) (by simp)
    apply e.injective
    calc e (y * e.symm z) = e y * z := by rw [map_mul, e.apply_symm_apply]
      _ = z * e y := hz'
      _ = e (e.symm z * y) := by rw [map_mul, e.apply_symm_apply]
theorem eq_sup_of_mem_inf_of_card {Bs L : Subgroup G} {x e : G} {D : Subgroup G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (heD : e ∈ D) (heL : e ∈ L) (he1 : e ≠ 1) :
    D = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
  classical
  have hxL : x ∉ L := by
    intro hxLin
    have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
    have hxZ : (⟨x, hxLin⟩ : ↥L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxcent l l.2
    obtain ⟨k, hk⟩ := hZ2 ⟨⟨x, hxLin⟩, hxZ⟩
    have hxpow : x ^ 3 = 1 := by
      have hxBs : x ∈ Bs := by
        have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
          rw [hBL]
          exact Subgroup.mem_zpowers x
        exact this.1
      exact hBs.2 x hxBs
    have hx3 : orderOf x = 3 := orderOf_eq_prime hxpow hx1
    have hk' : (⟨x, hxLin⟩ : ↥L) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf (⟨x, hxLin⟩ : ↥L) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk'
    have h3x : orderOf (⟨x, hxLin⟩ : ↥L) = 3 := by
      rw [Subgroup.orderOf_mk x hxLin]
      exact hx3
    rw [h3x] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  have heBs : e ∈ Bs := hDB heD
  have he3 : e ^ 3 = 1 := hBs.2 e heBs
  have hx3 : x ^ 3 = 1 := by
    have hxBs : x ∈ Bs := by
      have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [hBL]
        exact Subgroup.mem_zpowers x
      exact this.1
    exact hBs.2 x hxBs
  have hxorder : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have heorder : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hnotmem : e ∉ Subgroup.zpowers x := by
    intro hmem
    have heq : Subgroup.zpowers e = Subgroup.zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
      rw [Nat.card_zpowers, Nat.card_zpowers, heorder, hxorder]
    have hxL' : x ∈ L := Subgroup.zpowers_le.mpr heL (heq ▸ Subgroup.mem_zpowers x)
    exact hxL hxL'
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
  · have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
      rw [lt_iff_le_and_ne]
      refine ⟨le_sup_left, ?_⟩
      intro h
      have hesup : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers e :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
      rw [← h] at hesup
      exact hnotmem hesup
    have hcard_gt : 3 < Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) := by
      have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, hxorder]
      have hlecard : Nat.card ↥(Subgroup.zpowers x) ≤
          Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion le_sup_left)
          (Subgroup.inclusion_injective le_sup_left)
      have hne : Nat.card ↥(Subgroup.zpowers x) ≠
          Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) := by
        intro hc
        have hEq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
          apply Subgroup.eq_of_le_of_card_ge le_sup_left
          rw [← hc]
        exact hlt.ne hEq
      omega
    have hcard_dvd : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) ∣ 9 := by
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers e ≤ D :=
        sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
      have h := Subgroup.card_dvd_of_le hle
      rwa [hDcard] at h
    have hcard9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) = 9 := by
      have hle9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) ≤ 9 :=
        Nat.le_of_dvd (by norm_num) hcard_dvd
      set c := Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) with hc
      have hcgt : 3 < c := hcard_gt
      have hcle : c ≤ 9 := hle9
      have hcdvd : c ∣ 9 := hcard_dvd
      interval_cases c <;> norm_num at hcdvd
      norm_num
    rw [hcard9, hDcard]
    norm_num
theorem isComponentOf_map_qMap {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    {e : G} (heD : e ∈ D) (heL : e ∈ L) (he1 : e ≠ 1)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    CFSG.Open.IsComponentOf ((J.subgroupOf L).map (qMap (K := K) θ))
      (Subgroup.centralizer ({qMap (K := K) θ ⟨e, heL⟩} :
        Set (OrthRest.RPlus K 4))) := by
  classical
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers e :=
    eq_sup_of_mem_inf_of_card hZ2 hBs hx1 hLx hBL hDB hDcard hxD heD heL he1
  let KD : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G)
  let JL : Subgroup ↥L := J.subgroupOf L
  let M : Subgroup ↥L := KD.subgroupOf L
  have hJopen : CFSG.Open.IsComponentOf J KD := CFSG.Assembly.isComponentOf_iff_open.mp hJ
  have hJL : JL ≤ M := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hJopen.1 (Subgroup.mem_subgroupOf.mp hy))
  have hsubK : CFSG.Open.IsSubnormal JL M := by
    have h := CFSG.Open.IsSubnormal.comap L.subtype hJopen.2.1
    simpa [JL, M, KD] using h
  have hJqM : CFSG.Open.IsQuasisimple (JL.subgroupOf M) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hJL).trans
        (Subgroup.subgroupOfEquivOfLe (hJopen.1.trans inf_le_left)))
      hJopen.2.2
  have hJtop : CFSG.Open.IsComponentOf (JL.subgroupOf M) ⊤ := by
    refine ⟨le_top, ?_, hJqM⟩
    rw [← CFSG.Assembly.isSubnormal_iff_open, CFSG.Assembly.IsSubnormal.top_iff]
    exact (CFSG.Assembly.isSubnormal_iff_open.mpr hsubK).subgroupOf
  have hkerEq : MonoidHom.ker ((qMap (K := K) θ).comp M.subtype) =
      (Subgroup.center L).comap M.subtype := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.comp_apply]
    rw [← qMap_ker (K := K) θ, MonoidHom.mem_ker]
  have hker : IsPGroup 2 (MonoidHom.ker ((qMap (K := K) θ).comp M.subtype)) := by
    rw [hkerEq]
    let f : ↥((Subgroup.center L).comap M.subtype) →* ↥(Subgroup.center L) :=
      MonoidHom.mk' (fun x => (⟨(x : ↥L), x.2⟩ : ↥(Subgroup.center L))) (fun a b => rfl)
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(Subgroup.center L) => (z : ↥L)) hab
    exact IsPGroup.of_injective hZ2 f hinj
  have h := isComponentOf_map_of_isPGroup_ker ((qMap (K := K) θ).comp M.subtype) hker hJtop
  have htopM : M.map (qMap (K := K) θ) =
      Subgroup.centralizer ({qMap (K := K) θ ⟨e, heL⟩} : Set (OrthRest.RPlus K 4)) := by
    simpa [M, KD] using
      map_subgroupOf_inf_centralizer_eq_centralizer_qMap hZ2 hBs hLx hDB heD heL hDgen θ
  have htop : (⊤ : Subgroup ↥M).map ((qMap (K := K) θ).comp M.subtype) =
      Subgroup.centralizer ({qMap (K := K) θ ⟨e, heL⟩} : Set (OrthRest.RPlus K 4)) := by
    rw [← htopM]
    ext r
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨(x : ↥L), x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hJmap : (JL.subgroupOf M).map ((qMap (K := K) θ).comp M.subtype) =
      JL.map (qMap (K := K) θ) := by
    ext r
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(l : ↥L), Subgroup.mem_subgroupOf.mp hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨l, hJL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [hJmap, htop] at h
  exact h
end CFSG.StandardType.E6QTwo
end