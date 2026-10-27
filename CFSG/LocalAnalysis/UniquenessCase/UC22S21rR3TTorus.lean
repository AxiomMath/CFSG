module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TSz
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHpCartan
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Blueprint Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def uc22r3tN0 (T M L : Subgroup G) : Subgroup G :=
  conjClosure M L ⊓ normalizer (T : Set G) ⊓ normalizer (L : Set G)

theorem uc22r3tN0_le_conjClosure (T M L : Subgroup G) :
    uc22r3tN0 T M L ≤ conjClosure M L := inf_le_left.trans inf_le_left

theorem uc22r3tN0_le_normalizer_T (T M L : Subgroup G) :
    uc22r3tN0 T M L ≤ normalizer (T : Set G) := inf_le_left.trans inf_le_right

theorem uc22r3tN0_le_normalizer_L (T M L : Subgroup G) :
    uc22r3tN0 T M L ≤ normalizer (L : Set G) := inf_le_right

theorem uc22r3t_theta_ne_one_of_mem {M L : Subgroup G} (hL : L ∈ calC M) {q : ℕ}
    (hSz : IsSz (Bar2 L) q) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : G} (hxL : x ∈ L)
    (hxo : orderOf x = r) (hxn : x ∈ normalizer (L : Set G)) :
    inducedQuotInfAut L x hxn ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : center (BarInf L ⧸ center (BarInf L)) = ⊥ :=
    uc22r3t_center_xbar_eq_bot hL hSz
  have hne : piBarInf L ⟨x, hxL⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← solvableRadical_eq_pCore_of_center_bar2_eq_bot hL.2.2
        (center_eq_bot_of_isSz hL.2.2 hSz), ← piBarInf_ker hL.2.2]
      exact MonoidHom.mem_ker.2 h1
    have h2 : orderOf (⟨⟨x, hxL⟩, hmem⟩ : ↥(CFSG.pCore 2 ↥L)) = r := by
      rw [← Subgroup.orderOf_coe (⟨⟨x, hxL⟩, hmem⟩ : ↥(CFSG.pCore 2 ↥L)),
        ← Subgroup.orderOf_coe (⟨x, hxL⟩ : ↥L)]
      exact hxo
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    have h3 : r ∣ 2 ^ n := by
      rw [← h2, ← hn]
      exact orderOf_dvd_natCard _
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3))
  rw [uc22r3t_theta_eq_conj hxL hxn]
  rintro h1
  apply hne
  have hmem : piBarInf L ⟨x, hxL⟩ ∈ center (BarInf L ⧸ center (BarInf L)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := congrArg (fun f : MulAut (BarInf L ⧸ center (BarInf L)) => f y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc y * piBarInf L ⟨x, hxL⟩ = (piBarInf L ⟨x, hxL⟩ * y * (piBarInf L ⟨x, hxL⟩)⁻¹) *
          piBarInf L ⟨x, hxL⟩ := by rw [h2]
      _ = piBarInf L ⟨x, hxL⟩ * y := by group
  rwa [hcent, Subgroup.mem_bot] at hmem

theorem uc22r3t_exists_swap_mem_T {D : Data G} {L K : Subgroup G}
    (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) (hTL : ¬ D.T ≤ normalizer (L : Set G)) :
    ∃ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom = K ∧
      K.map (MulAut.conj t).toMonoidHom = L := by
  obtain ⟨t, htT, htN⟩ := SetLike.not_le_iff_exists.1 hTL
  have htM : t ∈ D.M := D.sylowM.le htT
  have hLt : L.map (MulAut.conj t).toMonoidHom = K := by
    have hmem : L.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M L := ⟨t, htM, rfl⟩
    rw [hset] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem.resolve_left fun h => htN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
  refine ⟨t, htT, hLt, ?_⟩
  have h2 : L.map (MulAut.conj (t * t)).toMonoidHom ∈ conjSetOf D.M L :=
    ⟨t * t, D.M.mul_mem htM htM, rfl⟩
  rw [hset] at h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
  have hLt2 : L.map (MulAut.conj (t * t)).toMonoidHom = L := by
    rcases h2 with h2 | h2
    · exact h2
    · exfalso
      have h3 : L.map (MulAut.conj (t⁻¹ * (t * t))).toMonoidHom =
          L.map (MulAut.conj (t⁻¹ * t)).toMonoidHom := by
        rw [← uc22p22d_map_conj_map_conj L (t * t) t⁻¹,
          ← uc22p22d_map_conj_map_conj L t t⁻¹, h2, hLt]
      rw [show t⁻¹ * (t * t) = t by group, show t⁻¹ * t = 1 by group] at h3
      have h4 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
        rw [show MulAut.conj (1 : G) = 1 from map_one _]
        exact Subgroup.map_id L
      exact hne (hLt.symm.trans (h3.trans h4))
  calc K.map (MulAut.conj t).toMonoidHom
      = (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := by rw [hLt]
    _ = L.map (MulAut.conj (t * t)).toMonoidHom := uc22p22d_map_conj_map_conj L t t
    _ = L := hLt2


theorem uc22r3t_conj_eq_one_iff {M L : Subgroup G} (hL : L ∈ calC M) {q : ℕ}
    (hSz : IsSz (Bar2 L) q) {u : BarInf L ⧸ center (BarInf L)} :
    MulAut.conj u = 1 ↔ u = 1 := by
  have hcent : center (BarInf L ⧸ center (BarInf L)) = ⊥ :=
    uc22r3t_center_xbar_eq_bot hL hSz
  constructor
  · intro h1
    have hmem : u ∈ center (BarInf L ⧸ center (BarInf L)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun f : MulAut (BarInf L ⧸ center (BarInf L)) => f y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * u = (u * y * u⁻¹) * u := by rw [h2]
        _ = u * y := by group
    rwa [hcent, Subgroup.mem_bot] at hmem
  · rintro rfl
    exact map_one _

theorem uc22r3t_conjClosure_eq_sup {M L K : Subgroup G} (hset : conjSetOf M L = {L, K}) :
    conjClosure M L = L ⊔ K := by
  have hL : L ∈ conjSetOf M L := by rw [hset]; simp
  have hK : K ∈ conjSetOf M L := by rw [hset]; simp
  refine le_antisymm ?_ (sup_le (le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) L hL
    le_rfl) (le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) K hK le_rfl))
  refine iSup₂_le fun A hA => ?_
  rw [hset] at hA
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem uc22r3t_mem_pCore_of_theta_eq_one {M L : Subgroup G} (hL : L ∈ calC M) {q : ℕ}
    (hSz : IsSz (Bar2 L) q) {a : G} (haL : a ∈ L) (han : a ∈ normalizer (L : Set G))
    (hθ : inducedQuotInfAut L a han = 1) : a ∈ pCoreOf 2 L := by
  rw [uc22r3t_theta_eq_conj haL han] at hθ
  have hpi : piBarInf L ⟨a, haL⟩ = 1 := (uc22r3t_conj_eq_one_iff hL hSz).1 hθ
  have hmem : (⟨a, haL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← solvableRadical_eq_pCore_of_center_bar2_eq_bot hL.2.2
      (center_eq_bot_of_isSz hL.2.2 hSz), ← piBarInf_ker hL.2.2]
    exact MonoidHom.mem_ker.2 hpi
  exact Subgroup.mem_map.2 ⟨⟨a, haL⟩, hmem, rfl⟩

theorem uc22r3t_mem_normalizer_inf_of_mem_conjClosure {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {x : G}
    (hx : x ∈ conjClosure M L) :
    x ∈ normalizer (L : Set G) ∧ x ∈ normalizer (K : Set G) := by
  have hLK : L ≤ normalizer (K : Set G) := uc22p22u_calC_normalizes hK hL hne
  have hKL : K ≤ normalizer (L : Set G) := uc22p22u_calC_normalizes hL hK (Ne.symm hne)
  have hxmem : x ∈ (L : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L K hLK,
      ← uc22r3t_conjClosure_eq_sup hset]
    exact hx
  obtain ⟨l, hl, k, hk, rfl⟩ := Set.mem_mul.1 hxmem
  exact ⟨(normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hl) (hKL hk),
    (normalizer (K : Set G)).mul_mem (hLK hl) (Subgroup.le_normalizer hk)⟩

private theorem uc22r3t_theta_eq_one_of_mul_mem {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) {q : ℕ} (hSz : IsSz (Bar2 L) q) {l k : G}
    (hlL : l ∈ L) (hkK : k ∈ K) (hln : l ∈ normalizer (L : Set G))
    (hkn : k ∈ normalizer (L : Set G)) (hmuln : l * k ∈ normalizer (L : Set G))
    (hθ : inducedQuotInfAut L (l * k) hmuln = 1) : l ∈ pCoreOf 2 L := by
  have hθl : inducedQuotInfAut L l hln = 1 := by
    rw [uc22r3t_theta_eq_conj hlL hln]
    have hm := inducedQuotInfAut_mul L hln hkn hmuln
    rw [hm, uc22r3t_theta_eq_conj hlL hln,
      uc22r3t_theta_eq_one_of_mem_ne hL hK (Ne.symm hne) hkK hkn, mul_one] at hθ
    exact hθ
  exact uc22r3t_mem_pCore_of_theta_eq_one hL hSz hlL hln hθl

private theorem uc22r3t_theta_conj_mem_pCore {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) {q : ℕ} (hSz : IsSz (Bar2 L) q) {l k t : G}
    (hlL : l ∈ L) (hkK : k ∈ K) (hLt : L.map (MulAut.conj t).toMonoidHom = K)
    (hKt : K.map (MulAut.conj t).toMonoidHom = L)
    (hyn : t * (l * k) * t⁻¹ ∈ normalizer (L : Set G))
    (hyθ : inducedQuotInfAut L (t * (l * k) * t⁻¹) hyn = 1) :
    t * k * t⁻¹ ∈ pCoreOf 2 L := by
  have hκK : t * l * t⁻¹ ∈ K := by
    rw [← hLt]
    exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hlL
  have hℓL : t * k * t⁻¹ ∈ L := by
    rw [← hKt]
    exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hkK
  have hκN : t * l * t⁻¹ ∈ normalizer (L : Set G) :=
    uc22p22u_calC_normalizes hL hK (Ne.symm hne) hκK
  have hℓN : t * k * t⁻¹ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hℓL
  have hyn' : (t * l * t⁻¹) * (t * k * t⁻¹) ∈ normalizer (L : Set G) := by
    have h : t * (l * k) * t⁻¹ = (t * l * t⁻¹) * (t * k * t⁻¹) := by group
    rw [← h]; exact hyn
  have hcongr : inducedQuotInfAut L (t * (l * k) * t⁻¹) hyn =
      inducedQuotInfAut L ((t * l * t⁻¹) * (t * k * t⁻¹)) hyn' := by
    refine congrArg (inducedQuotInfAutHom L) (Subtype.ext ?_)
    show t * (l * k) * t⁻¹ = (t * l * t⁻¹) * (t * k * t⁻¹)
    group
  have hyθ' : inducedQuotInfAut L ((t * l * t⁻¹) * (t * k * t⁻¹)) hyn' = 1 := by
    rw [← hcongr]; exact hyθ
  have hm := inducedQuotInfAut_mul L hκN hℓN hyn'
  rw [hm, uc22r3t_theta_eq_one_of_mem_ne hL hK (Ne.symm hne) hκK hκN, one_mul] at hyθ'
  exact uc22r3t_mem_pCore_of_theta_eq_one hL hSz hℓL hℓN hyθ'

theorem uc22r3t_theta_conj_ne_one {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {q : ℕ} (hSz : IsSz (Bar2 L) q) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {t x : G} (htM : t ∈ M)
    (hLt : L.map (MulAut.conj t).toMonoidHom = K)
    (hKt : K.map (MulAut.conj t).toMonoidHom = L)
    (hxX : x ∈ conjClosure M L) (hxn : x ∈ normalizer (L : Set G)) (hxo : orderOf x = r)
    (hxθ : inducedQuotInfAut L x hxn = 1)
    (hyn : t * x * t⁻¹ ∈ normalizer (L : Set G))
    (hyθ : inducedQuotInfAut L (t * x * t⁻¹) hyn = 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK : L ≤ normalizer (K : Set G) := uc22p22u_calC_normalizes hK hL hne
  have hxmem : x ∈ (L : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L K hLK,
      ← uc22r3t_conjClosure_eq_sup hset]
    exact hxX
  obtain ⟨l, hlL, k, hkK, rfl⟩ := Set.mem_mul.1 hxmem
  have hln : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hkn : k ∈ normalizer (L : Set G) := uc22p22u_calC_normalizes hL hK (Ne.symm hne) hkK
  have hlO : l ∈ pCoreOf 2 L :=
    uc22r3t_theta_eq_one_of_mul_mem hL hK hne hSz hlL hkK hln hkn hxn hxθ
  have hℓO : t * k * t⁻¹ ∈ pCoreOf 2 L :=
    uc22r3t_theta_conj_mem_pCore hL hK hne hSz hlL hkK hLt hKt hyn hyθ
  have hℓM : t * k * t⁻¹ ∈ pCoreOf 2 M :=
    (uc22ine229_pCoreOf_le_of_isSubnormal hL.1) hℓO
  have hkO : k ∈ pCoreOf 2 M := by
    have h1 := uc22p21c_conj_mem_pCoreOf_self (K := M) (M.inv_mem htM) hℓM
    convert h1 using 1
    group
  have hlM : l ∈ pCoreOf 2 M := (uc22ine229_pCoreOf_le_of_isSubnormal hL.1) hlO
  have hxO : l * k ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem hlM hkO
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (uc22p21c_isPGroup_pCoreOf M)
  have hdvd : r ∣ 2 ^ n := by
    have h1 : orderOf (l * k) ∣ Nat.card ↥(pCoreOf 2 M) :=
      Subgroup.orderOf_dvd_natCard (pCoreOf 2 M) hxO
    rwa [hn, hxo] at h1
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))

theorem uc22r3t_exists_rElt_of_le_normalizer {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (_hK : K ∈ calC D.M) {q : ℕ}
    (hSz : IsSz (Bar2 L) q) {r : ℕ} (hr : r.Prime) (hrq : r ∣ 2 ^ q - 1)
    (hTL : D.T ≤ normalizer (L : Set G)) :
    ∃ y ∈ conjClosure D.M L, ∃ hyL : y ∈ normalizer (L : Set G),
      orderOf y = r ∧ y ∈ normalizer (D.T : Set G) ∧ inducedQuotInfAut L y hyL ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hqodd : Odd q := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have hr2 : r ≠ 2 := uc22ine229_ne_two hqodd hrq
  obtain ⟨x, hxL, hxo, hxT⟩ :=
    uc22ine229_exists_mem_normalizer_of_isSz D.sylowM.isPGroup hTL
      (uc22p2214_isSylowOf_inf D.sylowM hL.1) hSz hqodd dvd_rfl hr hrq
  have hxn : x ∈ normalizer (L : Set G) := Subgroup.le_normalizer hxL
  have hxX : x ∈ conjClosure D.M L :=
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf D.M L) => A) L
      ⟨1, D.M.one_mem, by ext y; simp⟩ le_rfl hxL
  exact ⟨x, hxX, hxn, hxo, hxT, uc22r3t_theta_ne_one_of_mem hL hSz hr hr2 hxL hxo hxn⟩

private theorem uc22r3t_conj_mem_normalizer_of_map_conj {L K : Subgroup G} {t x : G}
    (hKt : K.map (MulAut.conj t).toMonoidHom = L)
    (hxK : x ∈ normalizer (K : Set G)) :
    t * x * t⁻¹ ∈ normalizer (L : Set G) := by
  have hLt'inv : L.map (MulAut.conj t⁻¹).toMonoidHom = K := by
    have h := congrArg (fun A : Subgroup G => A.map (MulAut.conj t⁻¹).toMonoidHom) hKt
    have h1 : t⁻¹ * t = 1 := by group
    rw [uc22p22d_map_conj_map_conj K t t⁻¹, h1] at h
    have hK1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
      rw [show MulAut.conj (1 : G) = 1 from map_one _]
      exact Subgroup.map_id K
    rw [hK1] at h
    exact h.symm
  have hxK' : K.map (MulAut.conj x).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hxK
  have hyeq : ((L.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom).map
      (MulAut.conj t).toMonoidHom = L.map (MulAut.conj (t * x * t⁻¹)).toMonoidHom := by
    rw [uc22p22d_map_conj_map_conj L t⁻¹ x, uc22p22d_map_conj_map_conj L (x * t⁻¹) t]
    congr 2
    group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change L.map (MulAut.conj (t * x * t⁻¹)).toMonoidHom = L
  rw [← hyeq, hLt'inv, hxK', hKt]

theorem uc22r3t_exists_rElt_of_not_le_normalizer {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {q : ℕ} (hSz : IsSz (Bar2 L) q) {r : ℕ}
    (hr : r.Prime) (hrq : r ∣ 2 ^ q - 1) (hTL : ¬ D.T ≤ normalizer (L : Set G)) :
    ∃ y ∈ conjClosure D.M L, ∃ hyL : y ∈ normalizer (L : Set G),
      orderOf y = r ∧ y ∈ normalizer (D.T : Set G) ∧ inducedQuotInfAut L y hyL ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hqodd : Odd q := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have hr2 : r ≠ 2 := uc22ine229_ne_two hqodd hrq
  have hc : (conjSetOf D.M L).ncard ≤ 2 := by
    rw [hset, Set.ncard_pair (Ne.symm hne)]
  obtain ⟨x, hxX, hxo, hxT⟩ :=
    uc22ine229_exists_mem_conjClosure_normalizer_of_isSz D.sylowM hL hc hSz hqodd dvd_rfl hr
      hrq
  obtain ⟨hxn, hxK⟩ := uc22r3t_mem_normalizer_inf_of_mem_conjClosure hL hK hne hset hxX
  by_cases hθ : inducedQuotInfAut L x hxn ≠ 1
  · exact ⟨x, hxX, hxn, hxo, hxT, hθ⟩
  push Not at hθ
  obtain ⟨t, htT, hLt, hKt⟩ := uc22r3t_exists_swap_mem_T hne hset hTL
  have htM : t ∈ D.M := D.sylowM.le htT
  have hNX : D.M ≤ normalizer (conjClosure D.M L : Set G) :=
    (uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) le_rfl Subgroup.le_normalizer hL).2.1
  have hyX : t * x * t⁻¹ ∈ conjClosure D.M L :=
    (Subgroup.mem_normalizer_iff.1 (hNX htM) x).1 hxX
  have hyn : t * x * t⁻¹ ∈ normalizer (L : Set G) :=
    uc22r3t_conj_mem_normalizer_of_map_conj hKt hxK
  have hynT : t * x * t⁻¹ ∈ normalizer (D.T : Set G) :=
    (normalizer (D.T : Set G)).mul_mem
      ((normalizer (D.T : Set G)).mul_mem (Subgroup.le_normalizer htT) hxT)
      ((normalizer (D.T : Set G)).inv_mem (Subgroup.le_normalizer htT))
  have hyo : orderOf (t * x * t⁻¹) = r := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hxo]
  exact ⟨t * x * t⁻¹, hyX, hyn, hyo, hynT, fun hyθ =>
    uc22r3t_theta_conj_ne_one hL hK hne hset hSz hr hr2 htM hLt hKt hxX hxn hxo hθ hyn
      hyθ⟩

theorem uc22r3t_exists_rElt {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {q : ℕ} (hSz : IsSz (Bar2 L) q) {r : ℕ}
    (hr : r.Prime) (hrq : r ∣ 2 ^ q - 1) :
    ∃ y ∈ conjClosure D.M L, ∃ hyL : y ∈ normalizer (L : Set G),
      orderOf y = r ∧ y ∈ normalizer (D.T : Set G) ∧ inducedQuotInfAut L y hyL ≠ 1 := by
  by_cases hTL : D.T ≤ normalizer (L : Set G)
  · exact uc22r3t_exists_rElt_of_le_normalizer hL hK hSz hr hrq hTL
  · exact uc22r3t_exists_rElt_of_not_le_normalizer hL hK hne hset hSz hr hrq hTL

theorem uc22r3t_split {D : Data G} {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {R : Subgroup G} {r : ℕ} (hr : r.Prime) (hR : IsPGroup r R) (hr2 : r ≠ 2)
    (hRM : R ≤ D.M) (hRT : R ≤ normalizer (D.T : Set G)) {b : G}
    (hz : ∃ z ∈ R, b * z ≠ z * b) :
    (∃ z ∈ R ⊓ H₁, b * z ≠ z * b) ∨ (∃ z ∈ R ⊓ H₂, b * z ≠ z * b) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hsolvT : Group.IsSolvable ↥D.T :=
    CFSG.GorensteinWalter.isSolvable_of_isPGroup D.sylowM.isPGroup
  have hsolvR : Group.IsSolvable ↥R := CFSG.GorensteinWalter.isSolvable_of_isPGroup hR
  have hsolv : Group.IsSolvable ↥(R ⊔ D.T) := by
    rw [sup_comm]
    exact CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hRT hsolvT hsolvR
  have hodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
    rw [hn]
    exact (hr.odd_of_ne_two hr2).pow
  have hmul := uc22s21rhp_cartan_eq_mul D hH₁ hH₂ hfX (Y := R ⊔ D.T) (C := R)
    (sup_le hRM D.sylowM.le) le_sup_right hsolv le_sup_left
    (Subgroup.coe_mul_of_left_le_normalizer_right R D.T hRT) hodd
  obtain ⟨z, hzR, hzne⟩ := hz
  change z ∈ (R : Set G) at hzR
  rw [hmul] at hzR
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.1 hzR
  by_cases h1 : b * z₁ = z₁ * b
  · refine Or.inr ⟨z₂, hz₂, fun h2 => hzne ?_⟩
    calc b * (z₁ * z₂) = (b * z₁) * z₂ := by group
      _ = (z₁ * b) * z₂ := by rw [h1]
      _ = z₁ * (b * z₂) := by group
      _ = z₁ * (z₂ * b) := by rw [h2]
      _ = z₁ * z₂ * b := by group
  · exact Or.inl ⟨z₁, hz₁, h1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
