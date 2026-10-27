module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSNF
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLocal
public import CFSG.Quasithin.Vol2.GoldschmidtF431NFKAmalgam

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.NF CFSG.Quasithin.Loc442Q

universe u

section Core

variable {Mb : Type u} [Group Mb] [Finite Mb] [DecidableEq Mb] {G : Type} [Group G] [Finite G]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t v nr na : Mb} {b1 : ↥M1 →* G} {b2 : ↥M2 →* G}
  {M1G M2G : Subgroup G} {V L Q Z X Y : Subgroup Mb} {q n : ℕ}

theorem local_core (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2) (hI : I = {z, t})
    (hrange1 : b1.range = M1G) (hrange2 : b2.range = M2G)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1G), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1G)
    (cz : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (ct : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (NF : NFK T Q Z X Y M1 M2 z v nr na q n) (Zperf : Z ≤ centerOf (perfectCore M1))
    (conj_tv : IsConj t v) (LK : LocK T z t V L) :
    ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) ∧
      Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ M1G ∧
      Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G) ≤ M2G := by
  have hz1 : z ∈ M1 := NF.z_mem₁
  have hzperf : z ∈ centerOf (perfectCore M1) := Zperf NF.z_mem
  have hcent1 : ∀ (w : Mb) (hw : w ∈ Z), w ≠ 1 →
      Subgroup.centralizer ({b1 ⟨w, NF.Z_le_M₁ hw⟩} : Set G) ≤ M1G := by
    intro w hw hw1
    have hwo : orderOf w = 2 := orderOf_eq_prime (by
      have := NF.Z_exp w hw
      rwa [← sq] at this) hw1
    have h := map_mem_centerOf_perfectCore (b := b1) C.inj₁ hrange1 (NF.Z_le_M₁ hw) (Zperf hw)
    exact hyp1 _ h ((orderOf_img C.inj₁ (NF.Z_le_M₁ hw)).trans hwo)
  have hb1 : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ M1G := by
    rw [amalgamMap_of_mem₁ b1 b2 hz1]
    exact hcent1 z NF.z_mem (NF.z_ne)
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ b1.range := hrange1 ▸ hb1
  have hsyl : IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤ := D.lemma_F433 C (Or.inl hb)
  have hcentb : ∀ x ∈ (Z.subgroupOf M1).map b1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ b1.range := by
    rintro _ ⟨⟨w, hw1⟩, hw, rfl⟩ hne
    have hwZ : w ∈ Z := hw
    have hw1' : w ≠ 1 := fun h => hne (by
      subst h
      exact map_one b1)
    exact hrange1 ▸ hcent1 w hwZ hw1'
  have hnfzv := NF.not_isConj_amalgam C hsyl hcentb
  have ht : t ∈ I := by
    rw [hI]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) := by
    intro h
    exact hnfzv (h.trans (D.fusion_forward C (D.mem_T t ht) (NF.Q_le_T NF.v_mem) conj_tv))
  exact ⟨hnf, hb1, hrange2 ▸ cent_t_le_oriented D C hI LK cz ct hb hnf⟩

end Core

section Final

variable {D : Type} [Group D] [Finite D] {G : Type} [Group G] [Finite G] {M1 M2 : Subgroup G}
  (E : LieExt D M1 M2)

structure OrientD (A : LieAmalgamExt D) (P P' : Subgroup D) (N N' : Subgroup (MulAut D))
    (z0 t0 v0 nr0 na0 : D) (Zd Qd Xd Yd : Subgroup D) (q n : ℕ) : Prop where
  cz : Subgroup.centralizer ({z0} : Set D) ≤ P
  ct : Subgroup.centralizer ({t0} : Set D) ≤ P'
  nz : ¬ Subgroup.centralizer ({z0} : Set D) ≤ P'
  nt : ¬ Subgroup.centralizer ({t0} : Set D) ≤ P
  Zperf : Zd ≤ centerOf (perfectCore P)
  nfd : NFD A N N' z0 v0 nr0 na0 Zd Qd Xd Yd q n
  conj_tv : IsConj t0 v0

open scoped Classical in
theorem f431Local_of_dlevel (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ E.K)
    (hodd : ¬ 2 ∣ (iK E.toLieAmalgamExt hgen).range.index) {z0 t0 : D} {V L : Subgroup D}
    (H : TwoClassD E.toLieAmalgamExt z0 t0) (HL : LocD E.toLieAmalgamExt z0 t0 V L)
    (hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
      Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨ Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1)
    (hyp2 : ∀ w ∈ centerOf (perfectCore M2), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M2)
    (hor : (∃ (v0 nr0 na0 : D) (Zd Qd Xd Yd : Subgroup D) (q n : ℕ),
        OrientD E.toLieAmalgamExt E.P1 E.P2 E.N1 E.N2 z0 t0 v0 nr0 na0 Zd Qd Xd Yd q n) ∨
      (∃ (v0 nr0 na0 : D) (Zd Qd Xd Yd : Subgroup D) (q n : ℕ),
        OrientD E.toLieAmalgamExt E.P2 E.P1 E.N2 E.N1 z0 t0 v0 nr0 na0 Zd Qd Xd Yd q n)) :
    ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
  set A := E.toLieAmalgamExt with hA
  have LK := f431LieK_of_twoClassD A hgen hcen hodd H hag
  have LKloc := locK_of_dlevel A hgen hcen hodd HL
  have hinj := iK_injective A hgen hcen
  refine ⟨A.TD.map (iK A hgen), {iK A hgen z0, iK A hgen t0}, iK A hgen z0, LK, ?_⟩
  have hI : ({iK A hgen z0, iK A hgen t0} : Finset ↥A.K) = {iK A hgen z0, iK A hgen t0} := rfl
  have hmemI : ∀ i ∈ ({iK A hgen z0, iK A hgen t0} : Finset ↥A.K),
      i = iK A hgen z0 ∨ i = iK A hgen t0 := by
    intro i hi
    rwa [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hor with ⟨v0, nr0, na0, Zd, Qd, Xd, Yd, q, n, HO⟩ |
    ⟨v0, nr0, na0, Zd, Qd, Xd, Yd, q, n, HO⟩
  · have NF := nfk_of_nfd A hgen hcen HO.nfd
    have Zp : Zd.map (iK A hgen) ≤ centerOf (perfectCore A.Mb1) := by
      rintro _ ⟨w, hw, rfl⟩
      exact iK_mem_centerOf_perfectCore_Mb1 A hgen hcen hodd (HO.Zperf hw)
    obtain ⟨hnf, hb1, hbt⟩ := local_core LK E.comp hI E.range_b1 E.range_b2 hyp1
      (cent_le_Mb1 A hgen hcen HO.cz H.aut_z) (cent_le_Mb2 A hgen hcen HO.ct H.aut_t) NF Zp
      ((iK A hgen).map_isConj HO.conj_tv) LKloc
    refine ⟨hnfI_of_hnf hnf, ?_, ?_⟩
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact hb1
      · exact absurd (cent_le_P1_of_Mb1 A hgen hc) HO.nt
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact absurd (cent_le_P2_of_Mb2 A hgen hc) HO.nz
      · exact hbt
  · have NF := nfk_of_nfd A hgen hcen HO.nfd
    have Zp : Zd.map (iK A hgen) ≤ centerOf (perfectCore A.Mb2) := by
      rintro _ ⟨w, hw, rfl⟩
      exact iK_mem_centerOf_perfectCore_Mb2 A hgen hcen hodd (HO.Zperf hw)
    obtain ⟨hnf, hb1, hbt⟩ := local_core (swapLieK LK) (swapComp E.comp) hI E.range_b2 E.range_b1
      hyp2 (cent_le_Mb2 A hgen hcen HO.cz H.aut_z) (cent_le_Mb1 A hgen hcen HO.ct H.aut_t) NF Zp
      ((iK A hgen).map_isConj HO.conj_tv) LKloc
    rw [amalgamMap_swap E.comp] at hnf hb1 hbt
    refine ⟨hnfI_of_hnf hnf, ?_, ?_⟩
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact absurd (cent_le_P1_of_Mb1 A hgen hc) HO.nz
      · exact hbt
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact hb1
      · exact absurd (cent_le_P2_of_Mb2 A hgen hc) HO.nt

end Final

end CFSG.Quasithin.H13.F431.Lift
