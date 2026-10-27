module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.GroupTheory.CyclicDiagonal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveDiagonal
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.GroupTheory.SquarefreeOrder
import CFSG.Quasithin.Background.E6Nineteen
import CFSG.Timmesfeld.Bridge.RootStructR2Incidence
import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.RankThree.PartOne CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem normalizes_conj_of_mem_normalizer_normalizer {T K : Subgroup G} {a : G}
    (haT : a ∈ Subgroup.normalizer (T : Set G))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer (K.map (MulAut.conj a).toMonoidHom : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hta : a⁻¹ * t * a ∈ T :=
    (Subgroup.mem_normalizer_iff''.mp haT t).mp ht
  have hKt : K.map (MulAut.conj (a⁻¹ * t * a)).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTK hta)
  calc
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj t).toMonoidHom
        = K.map (MulAut.conj (t * a)).toMonoidHom := Subgroup.map_conj_map_conj K a t
    _ = K.map (MulAut.conj (a * (a⁻¹ * t * a))).toMonoidHom := by
          rw [show t * a = a * (a⁻¹ * t * a) by group]
    _ = (K.map (MulAut.conj (a⁻¹ * t * a)).toMonoidHom).map
          (MulAut.conj a).toMonoidHom := (Subgroup.map_conj_map_conj K (a⁻¹ * t * a) a).symm
    _ = K.map (MulAut.conj a).toMonoidHom := by rw [hKt]

theorem normalizes_conjugatePower_of_normalizes_one {T L : Subgroup G} {a : G} {r : ℕ}
    (ha : a ^ r = 1) (haT : a ∈ Subgroup.normalizer (T : Set G))
    {j : ℕ} (hj : j < r) (hTj : T ≤ Subgroup.normalizer (conjugatePower a L j : Set G)) :
    ∀ i : Fin r, T ≤ Subgroup.normalizer (conjugatePower a L (i : ℕ) : Set G) := by
  have hperiod : ∀ i : ℕ, conjugatePower a L (i + r) = conjugatePower a L i := by
    intro i
    rw [conjugatePower, conjugatePower, pow_add, ha, mul_one]
  have hshift : ∀ k : ℕ, T ≤ Subgroup.normalizer
      ((conjugatePower a L j).map (MulAut.conj (a ^ k)).toMonoidHom : Set G) := by
    intro k
    induction k with
    | zero => simpa using hTj
    | succ k ih =>
        have hstep := normalizes_conj_of_mem_normalizer_normalizer haT ih
        have hEq : (conjugatePower a L j).map (MulAut.conj (a ^ (k + 1))).toMonoidHom =
            ((conjugatePower a L j).map (MulAut.conj (a ^ k)).toMonoidHom).map
              (MulAut.conj a).toMonoidHom := by
          rw [Subgroup.map_conj_map_conj, pow_succ']
        rw [hEq]
        exact hstep
  intro i
  have hi : (i : ℕ) < r := i.isLt
  by_cases hji : j ≤ (i : ℕ)
  · let k := (i : ℕ) - j
    have hk : k + j = (i : ℕ) := by omega
    have hKi : conjugatePower a L (i : ℕ) =
        (conjugatePower a L j).map (MulAut.conj (a ^ k)).toMonoidHom := by
      rw [← conjugatePower_add a L k j, hk]
    rw [hKi]
    exact hshift k
  · let k := (i : ℕ) + r - j
    have hj' : j < r := hj
    have hk : k + j = (i : ℕ) + r := by omega
    have hKi : conjugatePower a L (i : ℕ) =
        (conjugatePower a L j).map (MulAut.conj (a ^ k)).toMonoidHom := by
      rw [← conjugatePower_add a L k j, hk, hperiod]
    rw [hKi]
    exact hshift k

private theorem mem_normalizer_of_isPGroup_zpowers_of_sylow {M L T : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hT : ∀ K ∈ conjSetOf M L, T ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hxM : x ∈ M) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    ∀ K ∈ conjSetOf M L, x ∈ Subgroup.normalizer (K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2' : IsPGroup 2 ((Subgroup.zpowers x).subgroupOf M) := hx2.comap_subtype
  obtain ⟨Q, hxQ⟩ := hx2'.exists_le_sylow
  let P : Subgroup G := (Q : Subgroup ↥M).map M.subtype
  have hSylP : CFSG.ABGLocalTools.IsSylowOf 2 P M := ⟨Q, rfl⟩
  have hxP : Subgroup.zpowers x ≤ P := by
    intro y hy
    have hyM : y ∈ M := Subgroup.zpowers_le.mpr hxM hy
    exact ⟨⟨y, hyM⟩, hxQ hy, rfl⟩
  obtain ⟨k, hkM, hconj⟩ := hSyl.exists_mem_conj hSylP
  have hxk : k⁻¹ * x * k ∈ T := (hconj x).mp (hxP (Subgroup.mem_zpowers x))
  have hxeq : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
  intro K hK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let K' : Subgroup G := K.map (MulAut.conj k⁻¹).toMonoidHom
  have hK' : K' ∈ conjSetOf M L := by
    obtain ⟨m, hmM, rfl⟩ := hK
    refine ⟨k⁻¹ * m, M.mul_mem (M.inv_mem hkM) hmM, ?_⟩
    dsimp only [K']
    rw [Subgroup.map_conj_map_conj]
  have htK' : k⁻¹ * x * k ∈ Subgroup.normalizer (K' : Set G) := hT K' hK' hxk
  have hK't : K'.map (MulAut.conj (k⁻¹ * x * k)).toMonoidHom = K' :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htK'
  calc
    K.map (MulAut.conj x).toMonoidHom
        = K.map (MulAut.conj (k * (k⁻¹ * x * k) * k⁻¹)).toMonoidHom := by rw [← hxeq]
    _ = (K'.map (MulAut.conj (k⁻¹ * x * k)).toMonoidHom).map
          (MulAut.conj k).toMonoidHom := by
          dsimp only [K']
          rw [Subgroup.map_conj_map_conj, Subgroup.map_conj_map_conj]
    _ = K'.map (MulAut.conj k).toMonoidHom := by rw [hK't]
    _ = K := by
          dsimp only [K']
          rw [Subgroup.map_conj_map_conj, mul_inv_cancel]
          ext x
          simp

private theorem conj_eq_self_of_conj_sq_eq_self {L : Subgroup G} {a : G}
    (h : (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      L.map (MulAut.conj a).toMonoidHom) :
    L.map (MulAut.conj a).toMonoidHom = L := by
  have hleft : ((L.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom =
      L.map (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.map_conj_map_conj, Subgroup.map_conj_map_conj]
    congr 1
    group
  have hright : (L.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj a⁻¹).toMonoidHom = L := by
    rw [Subgroup.map_conj_map_conj]
    rw [show a⁻¹ * a = 1 by group]
    ext y
    simp [Subgroup.mem_map, MulAut.conj_apply]
  have h4 := congrArg (fun H : Subgroup G =>
    H.map (MulAut.conj a⁻¹).toMonoidHom) h
  rw [hleft, hright] at h4
  exact h4

private theorem mem_normalizer_of_inverts_of_mem_normalizer_conjugatePower {L : Subgroup G}
    {a x : G}
    (hx : x * a * x⁻¹ = a⁻¹) (ha : Odd (orderOf a))
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxK : x ∈ Subgroup.normalizer (conjugatePower a L 1 : Set G)) :
    a ∈ Subgroup.normalizer (L : Set G) := by
  let K : Subgroup G := conjugatePower a L 1
  have hKconj : CFSG.conjugate K a = L := by
    calc
      CFSG.conjugate K a = K.map (MulAut.conj a⁻¹).toMonoidHom := rfl
      _ = L.map (MulAut.conj (a⁻¹ * a)).toMonoidHom := by
            dsimp only [K]
            rw [conjugatePower, pow_one, Subgroup.map_conj_map_conj]
      _ = L := by
            rw [inv_mul_cancel]
            ext x
            simp [Subgroup.mem_map, MulAut.conj_apply]
  have hz : x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).inv_mem hxK
  have hz' : x⁻¹ ∈ Subgroup.normalizer
      ((CFSG.conjugate K a : Subgroup G) : Set G) := by
    rw [hKconj]
    exact (Subgroup.normalizer (L : Set G)).inv_mem hxL
  have hd : (x⁻¹)⁻¹ * a * x⁻¹ = a⁻¹ := by simpa using hx
  have haN : a ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.E6.mem_normalizer_of_inverts hz hz' hd ha
  have hKmap : K.map (MulAut.conj a).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
  have hLmap : L.map (MulAut.conj a).toMonoidHom = L :=
    conj_eq_self_of_conj_sq_eq_self (by simpa [K, conjugatePower] using hKmap)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLmap

private theorem exists_order_three_mem_centralizer_of_dvd_card_bar2 {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (haM : a ∈ M) (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haL : a ∉ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (Bar2 L) = ⊥) (h3 : 3 ∣ Nat.card (Bar2 L)) :
    ∃ z : G, z ∈ M ∧ z ∈ Subgroup.centralizer ({a} : Set G) ∧ orderOf z = 3 := by
  classical
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let B : Subgroup (Bar2 M) := barImage M L
  let δ : ↥B →* Bar2 M :=
    orbitDiagonalHom (q ⟨a, haM⟩) B (orderOf a) (mk_pow_orderOf_eq_one haM)
      (conjugatesCommute_barImage hL haM hr haL)
  obtain ⟨D, hDM, hDcent, -, -, hDmap⟩ :=
    exists_diagonal_perfect hL haM hr hr2 haL
  have hDmap' : (D.subgroupOf M).map q = δ.range := by
    simpa [q, B, δ] using hDmap
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv hL
  have hZB : Subgroup.center ↥B = ⊥ := by
    have h := Subgroup.map_center_eq eB
    rw [hZ] at h
    simpa using h.symm
  have hker : δ.ker ≤ Subgroup.center ↥B :=
    orbitDiagonalHom_ker_le_center (q ⟨a, haM⟩) B (orderOf a) (mk_pow_orderOf_eq_one haM)
      (conjugatesCommute_barImage hL haM hr haL) hr.pos
  have hδinj : Function.Injective δ := by
    exact (MonoidHom.ker_eq_bot_iff δ).mp (le_bot_iff.mp (hker.trans (le_of_eq hZB)))
  have hcardB : 3 ∣ Nat.card ↥B := by
    rw [← Nat.card_congr eB.toEquiv]
    exact h3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' 3 hcardB
  have hδyord : orderOf (δ y) = 3 := by
    rw [orderOf_injective δ hδinj y, hyord]
  have hδymem : δ y ∈ (D.subgroupOf M).map q := by
    rw [hDmap']
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  obtain ⟨d, hdD, hdq⟩ := Subgroup.mem_map.mp hδymem
  have h3dvd : 3 ∣ orderOf (d : G) := by
    have hdvd := orderOf_map_dvd q d
    rw [hdq, hδyord] at hdvd
    rwa [Subgroup.orderOf_coe]
  refine ⟨(d : G) ^ (orderOf (d : G) / 3), ?_, ?_, ?_⟩
  · exact hDM (Subgroup.pow_mem D (show (d : G) ∈ D from hdD) _)
  · exact Subgroup.pow_mem (Subgroup.centralizer ({a} : Set G))
      (hDcent (show (d : G) ∈ D from hdD)) _
  · exact orderOf_pow_orderOf_div (orderOf_pos (d : G)).ne' h3dvd

private theorem normalizes_conjSetOf_of_sylow {M T L : Subgroup G} {a : G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (haT : a ∈ Subgroup.normalizer (T : Set G))
    (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haL : a ∉ Subgroup.normalizer (L : Set G))
    (hconj : conjSetOf M L =
      Set.range (fun i : Fin (orderOf a) => conjugatePower a L i)) :
    ∀ K ∈ conjSetOf M L, T ≤ Subgroup.normalizer (K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective
      (fun i : Fin (orderOf a) => conjugatePower a L i) := by
    intro i j hij
    apply Fin.ext
    exact conjugatePower_injOn hr haL
      (Set.mem_Iio.mpr i.isLt) (Set.mem_Iio.mpr j.isLt) hij
  have hcard : (conjSetOf M L).ncard = orderOf a := by
    rw [hconj, Set.ncard_range_of_injective hinj, Nat.card_fin]
  have hodd : Odd (conjSetOf M L).ncard := hcard ▸ hr.odd_of_ne_two hr2
  have hstab : ∀ t ∈ T, ∀ K ∈ conjSetOf M L,
      K.map (MulAut.conj t).toMonoidHom ∈ conjSetOf M L := by
    intro t ht K hK
    obtain ⟨m, hmM, rfl⟩ := hK
    exact ⟨t * m, M.mul_mem (hSyl.le ht) hmM, by
      rw [Subgroup.map_conj_map_conj]⟩
  obtain ⟨K0, hK0, hfix0⟩ :=
    CFSG.Timmesfeld.Bridge.exists_map_conj_eq_of_isPGroup (p := 2) hSyl.isPGroup hstab
      hodd.not_two_dvd_nat
  have hTK0 : T ≤ Subgroup.normalizer (K0 : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix0 t ht)
  have hK0r : K0 ∈ Set.range (fun i : Fin (orderOf a) => conjugatePower a L i) := by
    rwa [← hconj]
  obtain ⟨j, hj⟩ := hK0r
  have hTKj : T ≤ Subgroup.normalizer (conjugatePower a L (j : ℕ) : Set G) := by
    rwa [← hj] at hTK0
  intro K hK
  have hKr : K ∈ Set.range (fun i : Fin (orderOf a) => conjugatePower a L i) := by
    rwa [← hconj]
  obtain ⟨i, hi⟩ := hKr
  rw [← hi]
  exact normalizes_conjugatePower_of_normalizes_one (pow_orderOf_eq_one a) haT
    j.isLt hTKj i

private theorem exists_mem_inverts_of_orderOf_three {D : Data G} {Ch : Choice2011 G}
    (e : Ctx215 D Ch) (h1930 : H1930 D) (hM3 : IsStronglyPEmbedded 3 D.M)
    {z : G} (hzM : z ∈ D.M) (hzC : z ∈ Subgroup.centralizer ({e.a} : Set G))
    (hzord : orderOf z = 3) :
    ∃ m ∈ D.M, ∀ b ∈ Subgroup.zpowers e.a, m * b * m⁻¹ = b⁻¹ := by
  classical
  let X : Subgroup G := Subgroup.zpowers z
  have hXM : X ≤ D.M := Subgroup.zpowers_le.mpr hzM
  have hXne : X ≠ ⊥ := by
    change Subgroup.zpowers z ≠ ⊥
    rw [Subgroup.zpowers_ne_bot]
    intro hz1
    rw [hz1, orderOf_one] at hzord
    omega
  have hXq : IsPGroup 3 ↥X :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one])
  have hXU : X ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded (by norm_num) hM3 hXM hXne hXq
  have hXC : X ≤ Subgroup.centralizer (Subgroup.zpowers e.a : Set G) := by
    have hzC' : z ∈ Subgroup.centralizer (Subgroup.zpowers e.a : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute e.a z :=
        Subgroup.mem_centralizer_iff.mp hzC e.a (Set.mem_singleton e.a)
      exact (hcomm.zpow_left k).eq
    exact Subgroup.zpowers_le.mpr hzC'
  have hXA : X ≤ Subgroup.normalizer (Subgroup.zpowers e.a : Set G) :=
    hXC.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers e.a : Set G))
  have hAne : Subgroup.zpowers e.a ≠ ⊥ := by
    rw [Subgroup.zpowers_ne_bot]
    intro ha1
    exact e.ha_prime.ne_one (by rw [ha1, orderOf_one])
  have hAB : Subgroup.zpowers e.a ≤ e.toCtx21.B := Subgroup.zpowers_le.mpr e.haB
  exact s21_10 D Ch h1930 e.toCtx21 (Subgroup.zpowers e.a) hAne hAB X hXne
    ⟨3, by norm_num, hXq⟩ hXA hXU

private theorem exists_twoElement_inverts {D : Data G} {Ch : Choice2011 G}
    (e : Ctx215 D Ch) (h1930 : H1930 D) (hM3 : IsStronglyPEmbedded 3 D.M)
    (hZ : Subgroup.center (Bar2 e.L) = ⊥) (h3 : 3 ∣ Nat.card (Bar2 e.L)) :
    ∃ x ∈ D.M, IsPGroup 2 (Subgroup.zpowers x) ∧ x * e.a * x⁻¹ = e.a⁻¹ := by
  classical
  have haM : e.a ∈ D.M := e.hBM (e.hle e.haB)
  obtain ⟨z, hzM, hzC, hzord⟩ :=
    exists_order_three_mem_centralizer_of_dvd_card_bar2 e.hL haM e.ha_prime e.ha_ne_two
      e.ha_not_mem hZ h3
  obtain ⟨m, hmM, hmInv⟩ := exists_mem_inverts_of_orderOf_three e h1930 hM3 hzM hzC hzord
  obtain ⟨k, t, hkpow, hkinv⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne.exists_two_element_inverting
      (B := Subgroup.zpowers e.a) (g := m) hmInv
  let x : G := m ^ k
  have hxM : x ∈ D.M := (Subgroup.zpowers_le.mpr hmM) (Subgroup.npow_mem_zpowers m k)
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 ^ t := orderOf_dvd_of_pow_eq_one hkpow
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  exact ⟨x, hxM, hx2, hkinv e.a (Subgroup.mem_zpowers e.a)⟩

theorem Ctx215.false_of_conjSetOf_eq {D : Data G} {Ch : Choice2011 G} (e : Ctx215 D Ch)
    (h1930 : H1930 D) (hM3 : IsStronglyPEmbedded 3 D.M)
    (haT : e.a ∈ Subgroup.normalizer (D.T : Set G))
    (hconj : conjSetOf D.M e.L =
      Set.range (fun i : Fin (orderOf e.a) => conjugatePower e.a e.L i))
    (hZ : Subgroup.center (Bar2 e.L) = ⊥) (h3 : 3 ∣ Nat.card (Bar2 e.L)) : False := by
  classical
  have haM : e.a ∈ D.M := e.hBM (e.hle e.haB)
  have hTall : ∀ K ∈ conjSetOf D.M e.L, D.T ≤ Subgroup.normalizer (K : Set G) :=
    normalizes_conjSetOf_of_sylow D.sylowM haT e.ha_prime e.ha_ne_two e.ha_not_mem hconj
  obtain ⟨x, hxM, hx2, hxinv⟩ := exists_twoElement_inverts e h1930 hM3 hZ h3
  have hxAll : ∀ K ∈ conjSetOf D.M e.L, x ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_isPGroup_zpowers_of_sylow D.sylowM hTall hxM hx2
  have hxL : x ∈ Subgroup.normalizer (e.L : Set G) :=
    hxAll e.L ⟨1, D.M.one_mem, by ext y; simp⟩
  have hxK : x ∈ Subgroup.normalizer (conjugatePower e.a e.L 1 : Set G) :=
    hxAll (conjugatePower e.a e.L 1) ⟨e.a, haM, by rw [conjugatePower, pow_one]⟩
  have haN : e.a ∈ Subgroup.normalizer (e.L : Set G) :=
    mem_normalizer_of_inverts_of_mem_normalizer_conjugatePower hxinv
      (e.ha_prime.odd_of_ne_two e.ha_ne_two) hxL hxK
  exact e.ha_not_mem haN

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
