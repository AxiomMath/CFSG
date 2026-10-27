module

public import CFSG.Quasithin.EmptyFaithful.S1469QB
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem sylowTwo_eq_of_le {K A B : Subgroup G} (hA : IsSylowTwoOf A K)
    (hB : IsSylowTwoOf B K) (hAB : A ≤ B) : A = B := by
  have h1 := Subgroup.relIndex_mul_relIndex A B K hAB hB.1
  obtain ⟨k, hk⟩ := hB.2.1.index (A.subgroupOf B)
  have hAB1 : A.relIndex B = 2 ^ k := hk
  have hodd : ¬ 2 ∣ A.relIndex K := hA.2.2
  have hk0 : k = 0 := by
    by_contra hne
    apply hodd
    rw [← h1, hAB1]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hne) _
  rw [hk0, pow_zero] at hAB1
  exact le_antisymm hAB (Subgroup.relIndex_eq_one.mp hAB1)

omit [Finite G] in
private theorem exists_two_pow_mem_of_mul {L : Subgroup G} {q y : G}
    (hq : ∀ l ∈ L, q⁻¹ * l * q ∈ L) (hy : y ∈ L) (n : ℕ) :
    ∃ l ∈ L, (q * y) ^ n = q ^ n * l := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l, hl, e⟩ := ih
    refine ⟨q⁻¹ * l * q * y, L.mul_mem (hq l hl) hy, ?_⟩
    rw [pow_succ, e, pow_succ]; group

private theorem conj_mem_block {Kall L : Subgroup G} {c : G} (hsh : IsShort2 L) (hLK : L ≤ Kall)
    (hLn : Kall ≤ Subgroup.normalizer (L : Set G)) (hcK : ∀ x ∈ Kall, c * x * c⁻¹ ∈ Kall)
    (hcQ : ∀ x ∈ Kall, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 Kall) :
    ∀ x ∈ L, c * x * c⁻¹ ∈ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := L.map (MulAut.conj c).toMonoidHom with hM
  have hMmem : ∀ x, x ∈ M ↔ ∃ y ∈ L, c * y * c⁻¹ = x := by
    intro x
    simp [hM, Subgroup.mem_map, MulAut.conj_apply]
  have hMK : M ≤ Kall := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hMmem x).1 hx
    exact hcK y (hLK hy)
  have hshM : IsShort2 M := by
    have := (Lin2.isShort2_conjR_iff L c⁻¹).2 hsh
    rw [Lin2.conjR_def, inv_inv] at this
    exact this
  have hnorm : M ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLn (hMK hx), Subgroup.le_normalizer hx⟩
  have : ((L ⊓ M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hnorm
  have hpg : IsPGroup 2 (↥M ⧸ (L ⊓ M).subgroupOf M) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨y, hy, hxy⟩ := (hMmem x).1 x.2
      have hq := hcQ y (hLK hy)
      have hqK : c * y * c⁻¹ * y⁻¹ ∈ Kall := pCoreOf_le 2 Kall hq
      have hq' : ∀ l ∈ L, (c * y * c⁻¹ * y⁻¹)⁻¹ * l * (c * y * c⁻¹ * y⁻¹) ∈ L := fun l hl => by
        simpa using (Subgroup.mem_normalizer_iff.mp (hLn (Kall.inv_mem hqK)) l).1 hl
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Kall) ⟨c * y * c⁻¹ * y⁻¹, hq⟩
      have hk' : (c * y * c⁻¹ * y⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨l, hl, e⟩ := exists_two_pow_mem_of_mul hq' hy (2 ^ k)
      have hxe : (x : G) = (c * y * c⁻¹ * y⁻¹) * y := by rw [← hxy]; group
      have hLpow : (x : G) ^ 2 ^ k ∈ L := by
        rw [hxe, e, hk', one_mul]; exact hl
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ⟨hLpow, M.pow_mem x.2 _⟩
  have htop := hshM.1 ((L ⊓ M).subgroupOf M) hpg
  intro x hx
  have hmem : c * x * c⁻¹ ∈ M := (hMmem _).2 ⟨x, hx, rfl⟩
  have : (⟨c * x * c⁻¹, hmem⟩ : ↥M) ∈ (L ⊓ M).subgroupOf M := htop ▸ Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.1 this).1

omit [Finite G] in
private theorem mul_comm_of_commutator_eq_bot' {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) {a b : G}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have h1 : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

private theorem isSylowTwoOf_inf_block {I S Kall L : Subgroup G} (hSyl : IsSylowTwoOf S I)
    (hKI : Kall ≤ I) (hKnorm : I ≤ Subgroup.normalizer (Kall : Set G)) (hLK : L ≤ Kall)
    (hLn : Kall ≤ Subgroup.normalizer (L : Set G)) : IsSylowTwoOf (S ⊓ L) L := by
  have hKnormal : (Kall.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).2 hKnorm
  have hLnormal : (L.subgroupOf Kall).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).2 hLn
  have hS1 : IsSylowTwoOf (S ⊓ Kall) Kall :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hSyl hKI hKnormal.isSubnormal
  have := RankOneRecog.isSylowTwoOf_inf_of_subnormal hS1 hLK hLnormal.isSubnormal
  rwa [inf_assoc, inf_eq_right.mpr hLK] at this

private theorem normalizer_inf_sup_of_blocks {I S Kall L L' : Subgroup G} {n : ℕ} (hn : 0 < n)
    (hKeq : Kall = L ⊔ L') (hSyl : IsSylowTwoOf S I) (hcomm : ⁅L, L'⁆ = ⊥) (hKI : Kall ≤ I)
    (hKnorm : I ≤ Subgroup.normalizer (Kall : Set G))
    (hlin : IsLin2Type L n) (hlin' : IsLin2Type L' n)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hP' : IsSylowTwoOf (S ⊓ L') L') :
    ∀ b ∈ L, b ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
      b ∈ Subgroup.normalizer ((S ⊓ Kall : Subgroup G) : Set G) := by
  have hLc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    mul_comm_of_commutator_eq_bot' hcomm ha hb
  have hinf : L ⊓ L' ≤ (S ⊓ L) ⊓ (S ⊓ L') := by
    intro x hx
    have hxP : x ∈ S ⊓ L :=
      mem_of_forall_commute_of_isLin2Type hn hlin hP hx.1 fun a ha => (hLc a ha x hx.2).symm
    have hxP' : x ∈ S ⊓ L' :=
      mem_of_forall_commute_of_isLin2Type hn hlin' hP' hx.2 fun a ha => hLc x hx.1 a ha
    exact ⟨hxP, hxP'⟩
  have hPP' : IsSylowTwoOf ((S ⊓ L) ⊔ (S ⊓ L')) (L ⊔ L') :=
    isSylowTwoOf_sup_of_commuting hLc hP hP' hinf
  have hKnormal : (Kall.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).2 hKnorm
  have hR : IsSylowTwoOf (S ⊓ Kall) Kall :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hSyl hKI hKnormal.isSubnormal
  subst hKeq
  have hRe : (S ⊓ L) ⊔ (S ⊓ L') = S ⊓ (L ⊔ L') :=
    sylowTwo_eq_of_le hPP' hR
      (sup_le (inf_le_inf_left S le_sup_left) (inf_le_inf_left S le_sup_right))
  rw [← hRe]
  intro b hb hbN
  have hbN' : b ∈ Subgroup.normalizer ((S ⊓ L' : Subgroup G) : Set G) :=
    le_normalizer_of_commute (A := S ⊓ L') (B := L) (fun p hp a ha => (hLc a ha p hp.2).symm) hb
  have hbinv : b⁻¹ ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := Subgroup.inv_mem _ hbN
  have hbinv' : b⁻¹ ∈ Subgroup.normalizer ((S ⊓ L' : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hbN'
  refine B6.mem_normalizer_of_conjSub_le ?_ ?_
  · rw [(B6.conjSub b).map_sup, B6.conjSub_eq_self hbN, B6.conjSub_eq_self hbN']
  · rw [(B6.conjSub b⁻¹).map_sup, B6.conjSub_eq_self hbinv, B6.conjSub_eq_self hbinv']

private theorem pCoreOf_inf_le_pCoreOf {I X : Subgroup G} (hXI : X ≤ I) :
    pCoreOf 2 I ⊓ X ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf 2 inf_le_right ?_ ((pCoreOf_isPGroup 2 I).to_le inf_le_left)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_pCoreOf 2 I (hXI hx), Subgroup.le_normalizer hx⟩

private theorem lin2Block_commutes_of_centerIz {I S Iz Kall L : Subgroup G} {n : ℕ} {c : G}
    (hmin : MinParabolic I S Iz) (hKI : Kall ≤ I)
    (hKnorm : I ≤ Subgroup.normalizer (Kall : Set G)) (hLK : L ≤ Kall)
    (hLn : Kall ≤ Subgroup.normalizer (L : Set G)) (hn : 1 < n) (hsh : IsShort2 L)
    (hlin : IsLin2Type L n)
    (hBR : ∀ b ∈ L, b ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
      b ∈ Subgroup.normalizer ((S ⊓ Kall : Subgroup G) : Set G))
    (hcI : c ∈ I) (hcIz : ∀ y ∈ Iz, y * c = c * y) (hcO : c ∈ pCoreOf 2 I) :
    ∀ x ∈ L, c * x = x * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowTwoOf S I := hmin.isSylow
  have hP : IsSylowTwoOf (S ⊓ L) L := isSylowTwoOf_inf_block hSyl hKI hKnorm hLK hLn
  have hnotN : ¬ L ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    obtain ⟨F, _, _, ⟨A⟩⟩ := exists_adapted (by omega : 0 < n) hlin hP
    exact A.not_le_normalizer
  have hBIz : ∀ b ∈ L, b ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) → b ∈ Iz := by
    intro b hb hbN
    have hSY : S ≤ I ⊓ Subgroup.normalizer ((S ⊓ Kall : Subgroup G) : Set G) := by
      refine le_inf hSyl.1 fun s hs => ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hs, hKnorm (hSyl.1 hs)⟩
    have hYI : I ⊓ Subgroup.normalizer ((S ⊓ Kall : Subgroup G) : Set G) < I := by
      refine lt_of_le_of_ne inf_le_left fun hYI => hnotN ?_
      intro l hl
      have hlN : l ∈ Subgroup.normalizer ((S ⊓ Kall : Subgroup G) : Set G) := by
        have : l ∈ I ⊓ Subgroup.normalizer ((S ⊓ Kall : Subgroup G) : Set G) := by
          rw [hYI]; exact hKI (hLK hl)
        exact this.2
      have := Subgroup.inf_normalizer_le_normalizer_inf ⟨hlN, Subgroup.le_normalizer hl⟩
      rwa [inf_assoc, inf_eq_right.mpr hLK] at this
    obtain ⟨N, hN, hYN⟩ := exists_isMaxSubgroupIn hYI
    have hNeq := hmin.eq_of_maximal hN (hSY.trans hYN)
    rw [← hNeq]
    exact hYN ⟨hKI (hLK hb), hBR b hb hbN⟩
  have hcK : ∀ x ∈ Kall, c * x * c⁻¹ ∈ Kall := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hKnorm hcI) x).1 hx
  have hOI : ∀ x ∈ I, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 I := by
    intro x hx
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I hx) c⁻¹).1
      (Subgroup.inv_mem _ hcO)
    have h3 := Subgroup.mul_mem _ hcO h2
    simpa [mul_assoc] using h3
  have hcQ0 : ∀ x ∈ Kall, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 Kall := fun x hx =>
    pCoreOf_inf_le_pCoreOf hKI ⟨hOI x (hKI hx), Kall.mul_mem (hcK x hx) (Kall.inv_mem hx)⟩
  have hcL := conj_mem_block hsh hLK hLn hcK hcQ0
  have hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L := fun x hx =>
    pCoreOf_inf_le_pCoreOf (hLK.trans hKI) ⟨hOI x (hKI (hLK hx)), L.mul_mem (hcL x hx) (L.inv_mem hx)⟩
  exact lin2_commute_of_borel hn hsh hlin hP hcQ
    (fun b hb hbN => (hcIz b (hBIz b hb hbN)).symm)

theorem input1469Lin2_proved : Input1469Lin2 := by
  intro G _ _ I S Iz _ r K _ hchar hmin hK _ _ _ _ hlin
  obtain ⟨i₀, n, hn, h₀⟩ := hlin
  obtain ⟨hr1, hr2, hblk, hcomm, hres, htrans, hinv⟩ := hK
  have hlinj : ∀ j, IsLin2Type (K j) n := fun j => by
    obtain ⟨t, -, htj⟩ := htrans i₀ j
    rw [← htj]
    exact Lin2.IsLin2Type.map_equiv h₀ (MulAut.conj t)
  have hSyl : IsSylowTwoOf S I := hmin.isSylow
  obtain ⟨Kall, hKall⟩ : ∃ Kall : Subgroup G, Kall = ⨆ i, K i := ⟨_, rfl⟩
  have hKI : Kall ≤ I := hKall ▸ iSup_le fun i => (hblk i).1.2.1
  have hSnorm : S ≤ Subgroup.normalizer (Kall : Set G) := by
    intro t ht
    have h1 : ∀ s ∈ S, B6.conjSub s Kall ≤ Kall := by
      intro s hs
      rw [hKall, OrderIso.map_iSup]
      refine iSup_le fun i => ?_
      obtain ⟨j, hj⟩ := hinv s hs i
      rw [hj]
      exact le_iSup K j
    exact B6.mem_normalizer_of_conjSub_le (h1 t ht) (h1 t⁻¹ (S.inv_mem ht))
  have hKnorm : I ≤ Subgroup.normalizer (Kall : Set G) :=
    (hKall ▸ hres).le.trans (sup_le hSnorm Subgroup.le_normalizer)
  have hLn : ∀ j, Kall ≤ Subgroup.normalizer (K j : Set G) := by
    intro j
    rw [hKall]
    refine iSup_le fun i => ?_
    by_cases hij : i = j
    · subst hij; exact Subgroup.le_normalizer
    · exact le_normalizer_of_commute fun a ha b hb =>
        mul_comm_of_commutator_eq_bot' (hcomm j i (Ne.symm hij)) ha hb
  intro c hc
  have hcIz : c ∈ Iz := hc.1
  have hcc : ∀ y ∈ Iz, y * c = c * y := fun y hy => Subgroup.mem_centralizer_iff.mp hc.2 y hy
  have hcI : c ∈ I := hmin.maximal.1.le hcIz
  have hcO : c ∈ pCoreOf 2 I := by
    refine hchar ⟨hcI, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact hcc y (hmin.le (B6.pCoreOf_two_le_of_isSylowTwoOf hSyl hy))
  have hblocks : ∀ j, ∀ x ∈ K j, c * x = x * c := by
    intro j
    have hLK : K j ≤ Kall := hKall ▸ le_iSup K j
    refine lin2Block_commutes_of_centerIz hmin hKI hKnorm hLK (hLn j) hn (hblk j).1.1 (hlinj j) ?_ hcI hcc hcO
    obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
    · have hKeq : Kall = K j := by
        rw [hKall]
        exact le_antisymm (iSup_le fun i => by rw [Subsingleton.elim i j]) (le_iSup K j)
      intro b hb hbN
      rw [hKeq]; exact hbN
    · have hKeq2 : Kall = K 0 ⊔ K 1 := by
        rw [hKall]
        exact le_antisymm (iSup_le fun i => by fin_cases i <;> simp)
          (sup_le (le_iSup K 0) (le_iSup K 1))
      have hP : ∀ i, IsSylowTwoOf (S ⊓ K i) (K i) := fun i =>
        isSylowTwoOf_inf_block hSyl hKI hKnorm (hKall ▸ le_iSup K i) (hLn i)
      fin_cases j
      · exact normalizer_inf_sup_of_blocks (by omega) hKeq2 hSyl (hcomm 0 1 (by decide)) hKI hKnorm
          (hlinj 0) (hlinj 1) (hP 0) (hP 1)
      · refine normalizer_inf_sup_of_blocks (L := K 1) (L' := K 0) (by omega)
          (by rw [hKeq2, sup_comm]) hSyl (hcomm 1 0 (by decide)) hKI hKnorm
          (hlinj 1) (hlinj 0) (hP 1) (hP 0)
  have hcent : I ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hres]
    refine sup_le ?_ (iSup_le fun j x hx => ?_)
    · intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcc s (hmin.le hs)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hblocks j x hx).symm
  refine ⟨hcI, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcent hx)

end CFSG.Quasithin
