module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModM

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem LQ_inf_centralizer_le' (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    (L ⊔ pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (V : Set G) ≤ (T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T) := by
  intro x hx
  obtain ⟨hxLQ, hxC⟩ := Subgroup.mem_inf.1 hx
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hx' : x ∈ ((L ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) := hxLQ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLQ] at hx'
  obtain ⟨l, hl, q, hq, rfl⟩ := hx'
  have hqC := Q_le_centralizer h1222 h hq
  have hlC : l ∈ Subgroup.centralizer (V : Set G) := by
    have := Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hqC)
    simpa using this
  have hlO : l ∈ pCoreOf 2 L := by
    rw [← inf_centralizer_eq_of_1222 h1222 h]
    exact Subgroup.mem_inf.2 ⟨hl, hlC⟩
  exact Subgroup.mul_mem _ (le_sup_left (a := T ⊓ L)
    (Subgroup.mem_inf.2 ⟨pCoreOf_L_le_T h hlO, hl⟩)) (le_sup_right (b := pCoreOf 2 (L ⊔ T)) hq)

omit [IsMulCommutative ↥V] in
theorem mem_of_conj_mem (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {K : Subgroup G}
    (hBK : (T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T) ≤ K) (hKLQ : K ≤ L ⊔ pCoreOf 2 (L ⊔ T)) {x : G}
    (hxLQ : x ∈ L ⊔ pCoreOf 2 (L ⊔ T)) (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hxK : conjAct V ⟨x, hx⟩ ∈ autOn K V) : x ∈ K := by
  obtain ⟨k, hk, hkK, hkx⟩ := mem_autOn'.1 hxK
  have hxk : x * k⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hk)
  have h1 : conjAct V ⟨x * k⁻¹, hxk⟩ = 1 := by
    have e : conjAct V ⟨x * k⁻¹, hxk⟩ = conjAct V ⟨x, hx⟩ * (conjAct V ⟨k, hk⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e, hkx, mul_inv_cancel]
  have hC := (conjAct_eq_one' hxk).1 h1
  have hmem : x * k⁻¹ ∈ K := hBK (LQ_inf_centralizer_le' h1222 h
    (Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ hxLQ (Subgroup.inv_mem _ (hKLQ hkK)), hC⟩))
  have := K.mul_mem hmem hkK
  simpa using this

@[expose] def codesOf (C : Coding ↥V) (K : Subgroup G) : Set Mc :=
  {A | ∃ a ∈ autOn K V, C.cB a = A.toB6}

omit [Finite G] in
theorem codesOf_one (C : Coding ↥V) (K : Subgroup G) : Mc.one ∈ codesOf C K :=
  ⟨1, (autOn K V).one_mem, by rw [C.cB_one, toB6_one]⟩

omit [Finite G] in
theorem codesOf_mul (C : Coding ↥V) {K : Subgroup G}
    (hK : ∀ a ∈ autOn K V, C.cB a ∈ gm6) {A B : Mc} (hA : A ∈ codesOf C K)
    (hB : B ∈ codesOf C K) : A.mul B ∈ codesOf C K := by
  obtain ⟨a, ha, hac⟩ := hA
  obtain ⟨b, hb, hbc⟩ := hB
  refine ⟨a * b, (autOn K V).mul_mem ha hb, ?_⟩
  have hAv : A.Valid := by
    obtain ⟨A', hA', hA'e⟩ := List.mem_map.1 (hK a ha)
    have hall := cert_gmList_mem
    rw [hac] at hA'e
    rw [← toB6_injective hA'e]
    exact (hall A' hA').1
  have hBv : B.Valid := by
    obtain ⟨B', hB', hB'e⟩ := List.mem_map.1 (hK b hb)
    have hall := cert_gmList_mem
    rw [hbc] at hB'e
    rw [← toB6_injective hB'e]
    exact (hall B' hB').1
  rw [C.cB_mul, hac, hbc, toB6_mul hAv hBv]

theorem presv_mul_toB6 {l : List ℕ} {A B : Mc} (hA : A.Valid) (hB : B.Valid)
    (hAp : presv l A.toB6 = true) (hBp : presv l B.toB6 = true) :
    presv l (A.mul B).toB6 = true := by
  rw [toB6_mul hA hB]
  exact presv_comp hAp hBp

theorem codes_all_of
    {P : Mc → Prop} (hone : P Mc.one) (hmul : ∀ x y, P x → P y → P (x.mul y))
    (hgm : ∀ x, P x → x ∈ gmList) (hs0 : ∀ s ∈ s0m, P s) {x y : Mc} (hx : P x)
    (hx1 : presv p1c x.toB6 = false) (hy : P y) (hy2 : presv l2c y.toB6 = false) :
    ∀ g ∈ gmList, P g := by
  obtain ⟨rx, sx, hsx, sx', hsx', hrxe, hrxd, hpx1, hpx2⟩ :
      ∃ r, ∃ s ∈ s0m, ∃ s' ∈ s0m, (s.mul x).mul s' = r ∧ r ∈ dreps ∧
        presv p1c r.toB6 = presv p1c x.toB6 ∧ presv l2c r.toB6 = presv l2c x.toB6 := by
    obtain ⟨s, hs, s', hs', h1, h2, h3⟩ := cert_dcov x (hgm x hx)
    exact ⟨_, s, hs, s', hs', rfl, h1, h2, h3⟩
  obtain ⟨ry, sy, hsy, sy', hsy', hrye, hryd, hpy1, hpy2⟩ :
      ∃ r, ∃ s ∈ s0m, ∃ s' ∈ s0m, (s.mul y).mul s' = r ∧ r ∈ dreps ∧
        presv p1c r.toB6 = presv p1c y.toB6 ∧ presv l2c r.toB6 = presv l2c y.toB6 := by
    obtain ⟨s, hs, s', hs', h1, h2, h3⟩ := cert_dcov y (hgm y hy)
    exact ⟨_, s, hs, s', hs', rfl, h1, h2, h3⟩
  have hPrx : P rx := hrxe ▸ hmul _ _ (hmul _ _ (hs0 _ hsx) hx) (hs0 _ hsx')
  have hPry : P ry := hrye ▸ hmul _ _ (hmul _ _ (hs0 _ hsy) hy) (hs0 _ hsy')
  have hrx1 : presv p1c rx.toB6 = false := hpx1.trans hx1
  have hry2 : presv l2c ry.toB6 = false := hpy2.trans hy2
  have hcl : ∀ gens : List Mc, (∀ g ∈ gens, P g) → ∀ g ∈ closureM gens, P g :=
    fun gens hg => mem_closureM hone hmul hg
  intro g hg
  by_cases h2 : presv l2c rx.toB6 = true
  · by_cases h1 : presv p1c ry.toB6 = true
    · refine hcl _ (fun g' hg' => ?_) g
        (mem_of_genAll (cert_gen2 rx hrxd hrx1 h2 ry hryd h1 hry2) g hg)
      rcases List.mem_append.1 hg' with hg' | hg'
      · exact hs0 g' hg'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        · exact hPrx
        · exact hPry
    · have h1' : presv p1c ry.toB6 = false := by simpa using h1
      refine hcl _ (fun g' hg' => ?_) g (mem_of_genAll (cert_gen1 ry hryd h1' hry2) g hg)
      rcases List.mem_append.1 hg' with hg' | hg'
      · exact hs0 g' hg'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rw [hg']
        exact hPry
  · have h2' : presv l2c rx.toB6 = false := by simpa using h2
    refine hcl _ (fun g' hg' => ?_) g (mem_of_genAll (cert_gen1 rx hrxd hrx1 h2') g hg)
    rcases List.mem_append.1 hg' with hg' | hg'
    · exact hs0 g' hg'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rw [hg']
      exact hPrx

theorem gm6_of_gmList {A : Mc} (hA : A.Valid ∧ inGm A = true) :
    A.toB6 ∈ gm6 := by
  have hall := cert_gmList_complete
  obtain ⟨⟨h0, h1, h2⟩, hin⟩ := hA
  exact List.mem_map.2 ⟨A, hall _ (List.mem_range.2 h0) _ (List.mem_range.2 h1) _
    (List.mem_range.2 h2) hin, rfl⟩

theorem lemma12_7_2_zero
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    maxOver (L ⊔ pCoreOf 2 (L ⊔ T)) ((T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T)) = {P1 T L V, P2 T L V} ∧
      P1 T L V ≠ P2 T L V := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hV1 := V1_eq h hC
  have hV2 := V2_eq h hC
  have hLQN := LQ_le_normalizer h1222 h
  have hP1 : ∀ a, a ∈ autOn (P1 T L V) V ↔ C.cB a ∈ gm6 ∧ presv p1c (C.cB a) = true := by
    intro a
    rw [P1, hV1]
    exact mem_autOn_Pof h1222 h hC.1 p1c_lt a
  have hP2 : ∀ a, a ∈ autOn (P2 T L V) V ↔ C.cB a ∈ gm6 ∧ presv l2c (C.cB a) = true := by
    intro a
    rw [P2, hV2]
    exact mem_autOn_Pof h1222 h hC.1 l2c_lt a
  have hB0P : ∀ W : Subgroup G, T ≤ Subgroup.normalizer (W : Set G) →
      (T ⊓ L) ⊔ Q ≤ Pof T L W := fun W hTW =>
    sup_le (le_inf (inf_le_right.trans le_sup_left) (inf_le_left.trans hTW))
      (le_inf le_sup_right ((Q_le_T h).trans hTW))
  have hB1 := hB0P _ (T_le_normalizer_V1 h1222 h)
  have hB2 := hB0P _ (T_le_normalizer_V2 h1222 h)
  have hKgm : ∀ K : Subgroup G, K ≤ L ⊔ Q → ∀ a ∈ autOn K V, C.cB a ∈ gm6 :=
    fun K hK a ha => (hC.1.1 a).1 (by rw [← autOn_LQ h1222 h]; exact A4.autOn_mono hK ha)
  have hcodes_gm : ∀ K : Subgroup G, K ≤ L ⊔ Q → ∀ x ∈ codesOf C K, x ∈ gmList := by
    rintro K hK x ⟨a, ha, hax⟩
    have hm := hKgm K hK a ha
    rw [hax] at hm
    obtain ⟨A, hA, hAe⟩ := List.mem_map.1 hm
    rw [← toB6_injective hAe]
    exact hA
  have hcodes_s0 : ∀ K : Subgroup G, (T ⊓ L) ⊔ Q ≤ K → ∀ s ∈ s0m, s ∈ codesOf C K := by
    intro K hK s hs
    obtain ⟨a, ha, hae⟩ := hC.s0_surj s.toB6 (List.mem_map.2 ⟨s, hs, rfl⟩)
    exact ⟨a, A4.autOn_mono (le_sup_left.trans hK) ha, hae⟩
  have htop : ∀ K : Subgroup G, (T ⊓ L) ⊔ Q ≤ K → K ≤ L ⊔ Q →
      (∀ g ∈ gmList, g ∈ codesOf C K) → K = L ⊔ Q := by
    intro K hBK hKLQ hall
    apply le_antisymm hKLQ
    intro x hx
    have hxN := hLQN hx
    have hmem : C.cB (conjAct V ⟨x, hxN⟩) ∈ gm6 :=
      hKgm (L ⊔ Q) le_rfl _ (conjAct_mem_autOn hx hxN)
    obtain ⟨A, hA, hAe⟩ := List.mem_map.1 hmem
    obtain ⟨a, ha, hae⟩ := hall A hA
    have e : a = conjAct V ⟨x, hxN⟩ := C.cB_injective (hae.trans hAe)
    exact mem_of_conj_mem h1222 h hBK hKLQ hx hxN (e ▸ ha)
  have hall_of : ∀ K : Subgroup G, (T ⊓ L) ⊔ Q ≤ K → K ≤ L ⊔ Q →
      ∀ {x y : Mc}, x ∈ codesOf C K → presv p1c x.toB6 = false → y ∈ codesOf C K →
        presv l2c y.toB6 = false → K = L ⊔ Q := by
    intro K hBK hKLQ x y hx hx1 hy hy2
    exact htop K hBK hKLQ (codes_all_of (P := (· ∈ codesOf C K)) (codesOf_one C K)
      (fun _ _ ha hb => codesOf_mul C (hKgm K hKLQ) ha hb) (hcodes_gm K hKLQ)
      (hcodes_s0 K hBK) hx hx1 hy hy2)
  have hcodeMc : ∀ K : Subgroup G, K ≤ L ⊔ Q → ∀ x ∈ K, ∃ A : Mc, A ∈ codesOf C K ∧
      ∃ hxN : x ∈ Subgroup.normalizer (V : Set G), C.cB (conjAct V ⟨x, hxN⟩) = A.toB6 := by
    intro K hK x hx
    have hxN := hLQN (hK hx)
    obtain ⟨A, -, hAe⟩ := List.mem_map.1 (hKgm K hK _ (conjAct_mem_autOn hx hxN))
    exact ⟨A, ⟨_, conjAct_mem_autOn hx hxN, hAe.symm⟩, hxN, hAe.symm⟩
  obtain ⟨hwAv, hwAin, hwA1, hwA2⟩ := wA_facts
  obtain ⟨hwBv, hwBin, hwB2, hwB1⟩ := wB_facts
  obtain ⟨aA, haA⟩ := hC.1.2 _ (gm6_of_gmList ⟨hwAv, hwAin⟩)
  obtain ⟨aB, haB⟩ := hC.1.2 _ (gm6_of_gmList ⟨hwBv, hwBin⟩)
  have haA1 : aA ∈ autOn (P1 T L V) V := (hP1 aA).2 ⟨haA ▸ gm6_of_gmList ⟨hwAv, hwAin⟩,
    by rw [haA]; exact hwA1⟩
  have haB2 : aB ∈ autOn (P2 T L V) V := (hP2 aB).2 ⟨haB ▸ gm6_of_gmList ⟨hwBv, hwBin⟩,
    by rw [haB]; exact hwB2⟩
  have hlt1 : P1 T L V < L ⊔ Q := by
    refine lt_of_le_of_ne inf_le_left fun e => ?_
    have : aB ∈ autOn (P1 T L V) V := by
      rw [e, autOn_LQ h1222 h]
      exact (hC.1.1 aB).2 (haB ▸ gm6_of_gmList ⟨hwBv, hwBin⟩)
    have := ((hP1 aB).1 this).2
    rw [haB, hwB1] at this
    exact Bool.false_ne_true this
  have hlt2 : P2 T L V < L ⊔ Q := by
    refine lt_of_le_of_ne inf_le_left fun e => ?_
    have : aA ∈ autOn (P2 T L V) V := by
      rw [e, autOn_LQ h1222 h]
      exact (hC.1.1 aA).2 (haA ▸ gm6_of_gmList ⟨hwAv, hwAin⟩)
    have := ((hP2 aA).1 this).2
    rw [haA, hwA2] at this
    exact Bool.false_ne_true this
  have hmax1 : IsMaxSubgroupIn (L ⊔ Q) (P1 T L V) := by
    refine ⟨hlt1, fun K hPK hKLQ => ?_⟩
    obtain ⟨x, hxK, hxP⟩ := IsConcreteLE.exists_of_lt hPK
    obtain ⟨A, hAK, hxN, hAe⟩ := hcodeMc K hKLQ x hxK
    have hA1 : presv p1c A.toB6 = false := by
      by_contra hne
      have hne' : presv p1c A.toB6 = true := by simpa using hne
      apply hxP
      exact mem_of_conj_mem h1222 h hB1 inf_le_left (hKLQ hxK) hxN
        ((hP1 _).2 ⟨hAe ▸ hKgm K hKLQ _ (conjAct_mem_autOn hxK hxN), by rw [hAe]; exact hne'⟩)
    exact hall_of K (hB1.trans hPK.le) hKLQ hAK hA1 ⟨aA, A4.autOn_mono hPK.le haA1, haA⟩ hwA2
  have hmax2 : IsMaxSubgroupIn (L ⊔ Q) (P2 T L V) := by
    refine ⟨hlt2, fun K hPK hKLQ => ?_⟩
    obtain ⟨x, hxK, hxP⟩ := IsConcreteLE.exists_of_lt hPK
    obtain ⟨A, hAK, hxN, hAe⟩ := hcodeMc K hKLQ x hxK
    have hA2 : presv l2c A.toB6 = false := by
      by_contra hne
      have hne' : presv l2c A.toB6 = true := by simpa using hne
      apply hxP
      exact mem_of_conj_mem h1222 h hB2 inf_le_left (hKLQ hxK) hxN
        ((hP2 _).2 ⟨hAe ▸ hKgm K hKLQ _ (conjAct_mem_autOn hxK hxN), by rw [hAe]; exact hne'⟩)
    exact hall_of K (hB2.trans hPK.le) hKLQ ⟨aB, A4.autOn_mono hPK.le haB2, haB⟩ hwB1 hAK hA2
  have hne : P1 T L V ≠ P2 T L V := by
    intro e
    have := ((hP2 aA).1 (e ▸ haA1)).2
    rw [haA, hwA2] at this
    exact Bool.false_ne_true this
  refine ⟨?_, hne⟩
  ext N
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hBN⟩
    have hNLQ : N ≤ L ⊔ Q := hN.1.le
    have hsub : ∀ {l : List ℕ} {W : Subgroup G} (hPW : ∀ a, a ∈ autOn (Pof T L W) V ↔
        C.cB a ∈ gm6 ∧ presv l (C.cB a) = true),
        (T ⊓ L) ⊔ Q ≤ Pof T L W →
        (∀ A ∈ codesOf C N, presv l A.toB6 = true) → N ≤ Pof T L W := by
      intro l W hPW hBW hall x hx
      obtain ⟨A, hAN, hxN, hAe⟩ := hcodeMc N hNLQ x hx
      exact mem_of_conj_mem h1222 h hBW inf_le_left (hNLQ hx) hxN
        ((hPW _).2 ⟨hAe ▸ hKgm N hNLQ _ (conjAct_mem_autOn hx hxN), by rw [hAe]; exact hall A hAN⟩)
    have heq : ∀ {P : Subgroup G}, P < L ⊔ Q → N ≤ P → N = P := by
      intro P hPLQ hNP
      by_contra hNe
      exact hPLQ.ne (hN.2 P (lt_of_le_of_ne hNP hNe) hPLQ.le)
    by_cases h1 : ∀ A ∈ codesOf C N, presv p1c A.toB6 = true
    · exact Or.inl (heq hlt1 (hsub hP1 hB1 h1))
    · by_cases h2 : ∀ A ∈ codesOf C N, presv l2c A.toB6 = true
      · exact Or.inr (heq hlt2 (hsub hP2 hB2 h2))
      · push Not at h1 h2
        obtain ⟨x, hx, hx1⟩ := h1
        obtain ⟨y, hy, hy2⟩ := h2
        exact absurd (hall_of N hBN hNLQ hx (by simpa using hx1) hy (by simpa using hy2))
          hN.1.ne
  · rintro (rfl | rfl)
    · exact ⟨hmax1, hB1⟩
    · exact ⟨hmax2, hB2⟩

end CFSG.Quasithin.H13.S127.Mod

end
