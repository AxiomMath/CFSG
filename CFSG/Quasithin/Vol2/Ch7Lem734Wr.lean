module

public import CFSG.Quasithin.Vol2.Ch7Lem734Mod
public import CFSG.Quasithin.Vol2.Ch10SecABasicL0
public import CFSG.Quasithin.Vol2.Ch10SecAModels
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuL0_eq_oTwoUpper (hfsu : FSU G T L I) : fsuL0 T L = oTwoUpper (fsuL0 T L) := by
  have hperf : ⁅L, L⁆ = L := hfsu.maximal.1.2.1.2.1
  refine le_antisymm (conjClosure_le fun s hs l hl => ?_) (oTwoUpper_le _)
  set Ls := L.map (MulAut.conj s).toMonoidHom with hLs
  have hLsp : ⁅Ls, Ls⁆ = Ls := by rw [hLs, ← Subgroup.map_commutator, hperf]
  have hLsL0 : Ls ≤ fsuL0 T L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_conjClosure hs hx
  have h1 : Ls ≤ oTwoUpper (fsuL0 T L) := by
    rw [eq_oTwoUpper_of_perfect hLsp]
    exact oTwoUpper_mono hLsL0
  exact h1 ⟨l, hl, rfl⟩

theorem hyp318_fsu (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) := by
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨h1, h2, h3⟩ := h3228 G T L I hyp.fsu
  exact { inM := ⟨hU.1.1, le_sup_right.trans hU.1.2⟩
          nonempty := ⟨H, hH⟩
          perfect := fsuL0_eq_oTwoUpper hyp.fsu
          le_M := Subgroup.le_normalizer
          normal := le_rfl
          unique := ⟨⟨hU.1.1, sup_le Subgroup.le_normalizer (le_sup_right.trans hU.1.2)⟩,
            fun M' hM' => hU.2 M' ⟨hM'.1, (sup_le_sup_right (le_fsuL0 T L) T).trans hM'.2⟩⟩
          reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨h1, h2⟩
          centralizer := h3 }

theorem center_facts_fsu (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf (fsuL0 T L ⊔ T) = ⊥ := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hJ := thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN
  rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      (hyp318_fsu h37 h38 h39 h3228 hyp hH) with ⟨hJ', -⟩ | ⟨-, hZ, hZ'⟩
  · exact absurd (le_inf (iSup₂_le fun _ hA => hA.1) hJ) hJ'
  · exact ⟨hZ H hH, hZ'⟩

theorem inf_fsuM_eq_of_ti (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    (hTI : IsTISetUnder (fsuV T I) (fsuM T L)) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  exact inf_eq_inf_normalizer_of_center hTI hNM (fsuV_inf_omegaOneCenter_ne_bot hyp.fsu hV hN)
    (center_facts_fsu hC58 h317 h37 h38 h39 h3228 hyp hH).1

omit [Finite G] in
theorem not_le_normalizer_of_lt (hlt : L < fsuL0 T L) : ¬ T ≤ Subgroup.normalizer (L : Set G) :=
  fun h => hlt.ne (fsuL0_eq_of_le_normalizer h).symm

theorem conjSubgroupsBy_eq (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hfsu : FSU G T L I)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    conjSubgroupsBy (fsuM T L) L = {L, CFSG.conjugate L t} := by
  have hcard := Vol2.Ch10.SecA.ncard_conjSubgroupsBy_fsuM (a37ForSQTKCat_of_sqtk h37)
    (a38ForSQTKCat_of_sqtk h38) hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.faithful hnot
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · rintro K (rfl | rfl)
    · simpa [Vol2.Ch10.SecA.conjugate_one] using
        Vol2.Ch10.SecA.conjugate_mem_conjSubgroupsBy (T := T) (L := K) (fsuM T K).one_mem
    · exact Vol2.Ch10.SecA.conjugate_mem_conjSubgroupsBy (Vol2.Ch10.SecA.le_fsuM T L ht)
  · rw [hcard, Set.ncard_pair (Vol2.Ch10.SecA.ne_conjugate htn)]

theorem conjugate_eq_or_of_mem (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hfsu : FSU G T L I)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate L s = L ∨ CFSG.conjugate L s = CFSG.conjugate L t := by
  have h := Vol2.Ch10.SecA.conjugate_mem_conjSubgroupsBy hs
  rw [conjSubgroupsBy_eq h37 h38 hfsu hnot ht htn] at h
  exact h

omit [Finite G] in
theorem conjugate_conjugate_inv_self (X : Subgroup G) (s : G) :
    CFSG.conjugate (CFSG.conjugate X s) s⁻¹ = X := by
  rw [Vol2.Ch10.SecA.conjugate_conjugate, mul_inv_cancel, Vol2.Ch10.SecA.conjugate_one]

omit [Finite G] in
theorem conjugate_injective {X Y : Subgroup G} {s : G}
    (h : CFSG.conjugate X s = CFSG.conjugate Y s) : X = Y := by
  rw [← conjugate_conjugate_inv_self X s, h, conjugate_conjugate_inv_self]

theorem mem_normalizer_of_odd_wreath (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hfsu : FSU G T L I)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {b : G} (hb : b ∈ fsuM T L)
    (hodd : Odd (orderOf b)) :
    b ∈ Subgroup.normalizer (L : Set G) ∧
      b ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  have hor : ∀ {s : G}, s ∈ fsuM T L →
      CFSG.conjugate L s = L ∨ CFSG.conjugate L s = CFSG.conjugate L t := fun hs =>
    conjugate_eq_or_of_mem h37 h38 hfsu hnot ht htn hs
  have hne : L ≠ CFSG.conjugate L t := Vol2.Ch10.SecA.ne_conjugate htn
  have h2 : ∀ s ∈ fsuM T L, s * s ∈ Subgroup.normalizer (L : Set G) := by
    intro s hs
    rcases hor hs with h1 | h1
    · have := Vol2.Ch10.SecA.conjugate_eq_self_iff.mp h1
      exact Subgroup.mul_mem _ this this
    · rcases hor (Subgroup.mul_mem _ hs hs) with h2 | h2
      · exact Vol2.Ch10.SecA.conjugate_eq_self_iff.mp h2
      · exfalso
        have h3 : CFSG.conjugate (CFSG.conjugate L s) s = CFSG.conjugate L s := by
          rw [Vol2.Ch10.SecA.conjugate_conjugate, h2, h1]
        have h4 : CFSG.conjugate L s = L := by
          have := congrArg (fun X => CFSG.conjugate X s⁻¹) h3
          simpa only [conjugate_conjugate_inv_self] using this
        exact hne (h4.symm.trans h1)
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := by
    obtain ⟨m, hm⟩ := hodd
    have e : b = (b * b) ^ (m + 1) := by
      rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf b + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ (h2 b hb) _
  refine ⟨hbL, Vol2.Ch10.SecA.conjugate_eq_self_iff.mp ?_⟩
  have hLb : CFSG.conjugate L b = L := Vol2.Ch10.SecA.conjugate_eq_self_iff.mpr hbL
  have htM : t ∈ fsuM T L := Vol2.Ch10.SecA.le_fsuM T L ht
  rw [Vol2.Ch10.SecA.conjugate_conjugate]
  rcases hor (Subgroup.mul_mem _ htM hb) with h1 | h1
  · exfalso
    have : CFSG.conjugate (CFSG.conjugate L t) b = CFSG.conjugate L b := by
      rw [Vol2.Ch10.SecA.conjugate_conjugate, h1, hLb]
    exact hne (conjugate_injective this).symm
  · exact h1

theorem pCoreOf_le_centralizer_fsuV (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) :
    pCoreOf 2 L ≤ pCoreOf 2 (fsuL0 T L) ∧
      pCoreOf 2 (fsuL0 T L) ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have hloc := hyp.fsu.maximal.1
  have h1 : pCoreOf 2 L ≤ pCoreOf 2 (fsuL0 T L) :=
    S1549D.pCoreOf_le_pCoreOf_of_normalizes (le_fsuL0 T L)
      (Vol2.Ch10.SecA.fsuL0_le_normalizer hloc)
  have h2 : pCoreOf 2 (fsuL0 T L) ≤ pCoreOf 2 (fsuL0 T L ⊔ T) :=
    S1549D.pCoreOf_le_pCoreOf_of_normalizes le_sup_left
      (sup_le Subgroup.le_normalizer (le_normalizer_conjClosure L T))
  have hQ : pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    (h3228 G T L I hyp.fsu).2.2
  exact ⟨h1, (h2.trans hQ.le).trans inf_le_right⟩

theorem not_le_centralizer_fsuV' (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) :
    ¬ L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hLC
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hL0C : fsuL0 T L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    refine conjClosure_le fun s hs l hl => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : s⁻¹ * v * s ∈ fsuV T I := by
      have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem hs)) v).mp hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (hLC hl) _ hw
    calc v * (s * l * s⁻¹) = s * ((s⁻¹ * v * s) * l) * s⁻¹ := by group
      _ = s * (l * (s⁻¹ * v * s)) * s⁻¹ := by rw [hc]
      _ = s * l * s⁻¹ * v := by group
  apply hyp.fsu.irrPlus.2.1
  rw [← hyp.fsu.irrPlus.2.2.2.1]
  change ⁅I, fsuL0 T L⁆ = ⊥
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro i hi
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hL0C hl) i (le_fsuV I T hi)).symm

theorem fsuL0_eq_sup' (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hfsu : FSU G T L I)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L = L ⊔ CFSG.conjugate L t := by
  refine le_antisymm (conjClosure_le fun s hs l hl => ?_)
    (sup_le (le_fsuL0 T L) (Vol2.Ch10.SecA.conjugate_le_fsuL0 ht))
  have hmem : s * l * s⁻¹ ∈ CFSG.conjugate L s⁻¹ := by
    rw [Vol2.Ch10.SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hl
  rcases conjugate_eq_or_of_mem h37 h38 hfsu hnot ht htn
      (Vol2.Ch10.SecA.le_fsuM T L (T.inv_mem hs)) with h | h
  · rw [h] at hmem
    exact Subgroup.mem_sup_left hmem
  · rw [h] at hmem
    exact Subgroup.mem_sup_right hmem

omit [Finite G] in
theorem conj_mem_centralizer {V : Subgroup G} {t x : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hw : t⁻¹ * v * t ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) v).mp hv
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hx _ hw
  calc v * (t * x * t⁻¹) = t * ((t⁻¹ * v * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * v * t)) * t⁻¹ := by rw [hc]
    _ = t * x * t⁻¹ * v := by group

theorem commutator_mem_pCoreOf_fsuL0 (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    {t : G} (ht : t ∈ T) (hL0 : fsuL0 T L = L ⊔ CFSG.conjugate L t) {b : G}
    (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hbLt : b ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G))
    (hb : ∀ m ∈ fsuL0 T L, b * m * b⁻¹ * m⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G)) :
    ∀ m ∈ fsuL0 T L, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (fsuL0 T L) := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  obtain ⟨hO1, hO2⟩ := pCoreOf_le_centralizer_fsuV h3228 hyp
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (le_fsuL0 T L).trans (le_sup_left.trans hN)
  have hperf : ⁅L, L⁆ = L := hyp.fsu.maximal.1.2.1.2.1
  have hLC := not_le_centralizer_fsuV' h3228 hyp
  set O := pCoreOf 2 (fsuL0 T L) with hO
  have hOn : fsuL0 T L ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have htO : t ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) _
      (le_normalizer_conjClosure L T ht)
  let S : Subgroup G :=
    { carrier := {m | m ∈ fsuL0 T L ∧ b * m * b⁻¹ * m⁻¹ ∈ O}
      mul_mem' := by
        rintro m n ⟨hm, hm'⟩ ⟨hn, hn'⟩
        refine ⟨(fsuL0 T L).mul_mem hm hn, ?_⟩
        have e : b * (m * n) * b⁻¹ * (m * n)⁻¹ =
            (b * m * b⁻¹ * m⁻¹) * (m * (b * n * b⁻¹ * n⁻¹) * m⁻¹) := by group
        rw [e]
        exact O.mul_mem hm' ((Subgroup.mem_normalizer_iff.mp (hOn hm) _).mp hn')
      one_mem' := ⟨(fsuL0 T L).one_mem, by simp⟩
      inv_mem' := by
        rintro m ⟨hm, hm'⟩
        refine ⟨(fsuL0 T L).inv_mem hm, ?_⟩
        have e : b * m⁻¹ * b⁻¹ * m⁻¹⁻¹ = m⁻¹ * (b * m * b⁻¹ * m⁻¹)⁻¹ * m⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hOn ((fsuL0 T L).inv_mem hm)) _).mp
          (O.inv_mem hm') }
  have hLS : L ≤ S := by
    intro l hl
    refine ⟨le_fsuL0 T L hl, hO1 ?_⟩
    have := commutatorElement_mem_pCoreOf_of_centralizer hyp.fsu.quasisimple hperf hLN
      (hO1.trans hO2) hLC hbL (fun l' hl' => by
        rw [commutatorElement_def]
        exact hb l' (le_fsuL0 T L hl')) l hl
    rwa [commutatorElement_def] at this
  have hmc : ∀ y : G, y ∈ CFSG.conjugate L t ↔ t * y * t⁻¹ ∈ L := fun y =>
    Vol2.Ch10.SecA.mem_conjugate_iff
  set b' := t * b * t⁻¹ with hb'
  have hb'L : b' ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hy : t⁻¹ * x * t ∈ CFSG.conjugate L t := by
        rw [hmc]
        simpa [mul_assoc] using hx
      have hz := (Subgroup.mem_normalizer_iff.mp hbLt _).mp hy
      rw [hmc] at hz
      have e : t * (b * (t⁻¹ * x * t) * b⁻¹) * t⁻¹ = b' * x * b'⁻¹ := by rw [hb']; group
      rwa [e] at hz
    · intro hx
      have e : t⁻¹ * (b' * x * b'⁻¹) * t = b * (t⁻¹ * x * t) * b⁻¹ := by rw [hb']; group
      have hy : b * (t⁻¹ * x * t) * b⁻¹ ∈ CFSG.conjugate L t := by
        rw [hmc, ← e]
        simpa [mul_assoc] using hx
      have hz := (Subgroup.mem_normalizer_iff.mp hbLt _).mpr hy
      rw [hmc] at hz
      simpa [mul_assoc] using hz
  have hb'c : ∀ l ∈ L, ⁅b', l⁆ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro l hl
    have hy : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
      rw [hmc]
      simpa [mul_assoc] using hl
    have h1 := hb _ (Vol2.Ch10.SecA.conjugate_le_fsuL0 ht hy)
    have e : ⁅b', l⁆ = t * (b * (t⁻¹ * l * t) * b⁻¹ * (t⁻¹ * l * t)⁻¹) * t⁻¹ := by
      rw [commutatorElement_def, hb']
      group
    rw [e]
    exact conj_mem_centralizer (hTV ht) h1
  have hb'O := commutatorElement_mem_pCoreOf_of_centralizer hyp.fsu.quasisimple hperf hLN
    (hO1.trans hO2) hLC hb'L hb'c
  have hLtS : CFSG.conjugate L t ≤ S := by
    intro l' hl'
    refine ⟨Vol2.Ch10.SecA.conjugate_le_fsuL0 ht hl', ?_⟩
    have hl := (hmc l').mp hl'
    have h1 := hO1 (hb'O _ hl)
    have e : b * l' * b⁻¹ * l'⁻¹ = t⁻¹ * ⁅b', t * l' * t⁻¹⁆ * t := by
      rw [commutatorElement_def, hb']
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htO) _).mp h1
    simpa using this
  intro m hm
  rw [hL0] at hm
  exact (sup_le hLS hLtS hm).2

theorem inf_centralizer_le_of_faithful' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) (hlt : L < fsuL0 T L) {H : Subgroup G}
    (hloc1 : H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G))
    (h2c : ∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (oTwoUpper H ⊓ fsuM T L) ∧
      oTwoUpper H ⊓ fsuM T L ≤ Subgroup.normalizer (P : Set G))
    (hfaith : ∀ B : Subgroup G, B ≤ H ⊓ fsuM T L → Odd (Nat.card B) →
      (∃ k : ℕ, B.relIndex (H ⊓ fsuM T L) = 2 ^ k) → ∀ b ∈ B,
        (∀ m ∈ conjClosure L T, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (conjClosure L T)) → b = 1) :
    H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L) := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hnot := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hnot fun x hx => h x hx
  have hL0 := fsuL0_eq_sup' h37 h38 hyp.fsu hnot ht htn
  have hXV : H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hloc1]
    exact inf_le_right
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hNeq : H ⊓ fsuM T L ⊓ oTwoUpper H = oTwoUpper H ⊓ fsuM T L := by
    rw [inf_comm (H ⊓ fsuM T L), ← inf_assoc, inf_eq_left.mpr (oTwoUpper_le H)]
  have hN2 : E1.IsTwoClosed (H ⊓ fsuM T L ⊓ oTwoUpper H) := by
    obtain ⟨P, hP, hPn⟩ := h2c
    rw [hNeq]
    exact ⟨P, hP, (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hPn⟩
  have hB : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∀ b ∈ B, (∀ l ∈ fsuL0 T L, b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G)) →
        b = 1 := by
    intro B hB b hb hbl
    have hbM : b ∈ fsuM T L := (hB.1 hb).2
    have hodd : Odd (orderOf b) := Odd.of_dvd_nat hB.2.1 (Subgroup.orderOf_dvd_natCard B hb)
    obtain ⟨hbL, hbLt⟩ := mem_normalizer_of_odd_wreath h37 h38 hyp.fsu hnot ht htn hbM hodd
    exact hfaith B hB.1 hB.2.1 hB.2.2 b hb
      (commutator_mem_pCoreOf_fsuL0 h3228 hyp ht hL0 hbL hbLt hbl)
  have hp := Vol2.Ch10.SecD.isPGroup_inf_centralizer (X := H ⊓ fsuM T L)
    (N := H ⊓ fsuM T L ⊓ oTwoUpper H) (L0 := fsuL0 T L) inf_le_left hXV hL0N hN2
    (fun x hx ho => ⟨hx, mem_oTwoUpper_of_odd hx.1 ho⟩)
    (Vol2.Ch10.SecD.exists_relIndex_oTwoUpper_eq_two_pow inf_le_left) hB
  exact QuasithinUnique.le_pCoreOf_of_normalizes inf_le_left
    (Vol2.Ch10.SecD.le_normalizer_inf_centralizer hXV) hp

omit [Finite G] in
theorem card_fsuV_wreath [IsMulCommutative ↥(fsuV T I)] (h : Row711L3Wreath T L I) :
    Nat.card ↥(fsuV T I) = 2 ^ 9 := by
  obtain ⟨-, π, hπ⟩ := h
  rw [Vol2.Ch10.SecA.card_eq_of_realizesVia_tensorPair hπ, Nat.card_zmod, Fintype.card_fin]

theorem fsuV_eq_conjClosure_of_eq (hyp : Hyp7_0_2 G T L I) (hIV : I = fsuV T I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hcen : centerOf (fsuL0 T L ⊔ T) = ⊥) :
    fsuV T I = conjClosure (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (fsuL0 T L) := by
  set W := conjClosure (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (fsuL0 T L) with hWdef
  have hLV : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hWV : W ≤ fsuV T I := conjClosure_le fun l hl x hx =>
    (Subgroup.mem_normalizer_iff.mp (hLV hl) x).mp hx.1
  have hWL : fsuL0 T L ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hW0 : W ≠ ⊥ := by
    intro h
    apply fsuV_inf_centralizer_T_ne_bot hyp.fsu hV hN
    rw [eq_bot_iff, ← h]
    exact le_conjClosure _ _
  have hCV := fsuV_inf_centralizer_eq_bot hyp.fsu hV hN hcen
  have hCI : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    exact inf_le_inf_right _ (le_fsuV I T)
  rcases irr_of_inf_centralizer hyp.fsu hCI W (hIV ▸ hWV) hWL with h | h
  · exact absurd h hW0
  · exact hIV.symm.trans h.symm

theorem local_structure_wreath (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hIV : I = fsuV T I) (hTI : IsTISetUnder (fsuV T I) (fsuM T L)) :
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
      H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
        H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L) := by
  intro H hH hn
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hloc1 := inf_fsuM_eq_of_ti hC58 h317 h37 h38 h39 h3228 hyp hTI hH
  have hcen := (center_facts_fsu hC58 h317 h37 h38 h39 h3228 hyp hH).2
  refine ⟨hloc1, ?_⟩
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨hVX, hred, -⟩ := h3228 G T L I hyp.fsu
  have hcomm := commutator_fsuV_fsuL0 hyp.fsu hN
  rcases h4414 G T (fsuM T L) L (fsuV T I) H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow hU.1.1 (le_sup_right.trans hU.1.2) hyp.fsu.maximal hyp.fsu.faithful
      (le_sup_left.trans hU.1.2) hyp.fsu.quasisimple hVX hred hH
      (by rw [hcomm]; exact fsuV_ne_bot hyp.fsu)
      (fsuV_eq_conjClosure_of_eq hyp hIV hV hN hcen)
      (by rw [hcomm]; exact not_isFFModule_autOn_sup h37 h38 h39 hyp hV hN) hn with
    ⟨h2c, hfaith⟩ | ⟨n, hn1, -, h2⟩ | ⟨-, h3⟩
  · exact inf_centralizer_le_of_faithful' h37 h38 h3228 hyp hrow.1 hloc1 h2c hfaith
  · rw [hcomm] at h2
    exact (not_orth hyp hn1 h2).elim
  · rw [hcomm] at h3
    exfalso
    obtain ⟨hc, h3⟩ := h3
    have h64 := Fano.FanoCoreModule.card h3
    rw [card_fsuV_wreath hrow] at h64
    norm_num at h64

end CFSG.Quasithin.H13
