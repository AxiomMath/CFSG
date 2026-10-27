module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherAssembly
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGRawAutRest
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtAutAsm_exists_pow_of_cyclic {C : Type*} [Group C] [IsCyclic C]
    {p : ℕ} (hp : p.Prime) {a b : C} (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃ j : ℕ, ¬ p ∣ j ∧ a = b ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have horda : orderOf a = p := orderOf_eq_prime ha ha1
  have hordb : orderOf b = p := orderOf_eq_prime hb hb1
  have hfinA : Finite (Subgroup.zpowers a) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, ha⟩)
  have hfinB : Finite (Subgroup.zpowers b) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hb⟩)
  have heq : Subgroup.zpowers a = Subgroup.zpowers b := by
    haveI := hfinA
    haveI := hfinB
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, horda, hordb]
  have hmem : a ∈ Subgroup.zpowers b := by rw [← heq]; exact Subgroup.mem_zpowers a
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hrem_nonneg : 0 ≤ k % (p : ℤ) := Int.emod_nonneg k (by exact_mod_cast hp.ne_zero)
  let j : ℕ := (k % (p : ℤ)).toNat
  have hj_int : (j : ℤ) = k % (p : ℤ) := by
    dsimp [j]
    exact Int.toNat_of_nonneg hrem_nonneg
  have h1 : b ^ k = b ^ (k % (p : ℤ)) := zpow_eq_zpow_emod' k hb
  have h2 : b ^ (k % (p : ℤ)) = b ^ j := by
    rw [← hj_int]
    simp
  have hbj : b ^ j = a := h2.symm.trans (h1.symm.trans hk)
  have hjnd : ¬ p ∣ j := by
    intro hd
    obtain ⟨m, hm⟩ := hd
    have hzero : b ^ j = 1 := by rw [hm, pow_mul, hb, one_pow]
    exact ha1 (hbj.symm.trans hzero)
  exact ⟨j, hjnd, hbj.symm⟩

theorem ggL45NtAutAsm_isCyclic_quotient {M : Type*} [Group M] {J S : Subgroup M}
    (hN : (J.subgroupOf S).Normal)
    (hgen : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) :
    IsCyclic (S ⧸ J.subgroupOf S) := by
  haveI : (J.subgroupOf S).Normal := hN
  obtain ⟨g, hg, hgen'⟩ := hgen
  refine ⟨⟨(QuotientGroup.mk (⟨g, hg⟩ : S) : S ⧸ J.subgroupOf S), fun x => ?_⟩⟩
  induction x using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨k, hk⟩ := hgen' s s.2
    have h1 : (QuotientGroup.mk ((⟨g, hg⟩ : S) ^ k * s) : S ⧸ J.subgroupOf S) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hg⟩ : S) : S ⧸ J.subgroupOf S) ^ (-k) = _
    rw [zpow_neg]
    exact inv_eq_of_mul_eq_one_right h1

@[expose] def GGL45NtNotD4Three (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)

theorem ggL45NtAutOn_notD4Three :
    GGL45NtAutOn GGL45NtNotD4Three := by
  intro p hp hp2 lab hlab hkg hS
  have hIFall : LargeEvenLabelAll lab (GGRawInnField p) :=
    ggRawInnFieldInput_holds p hp hp2 lab hlab
  have hIDall : LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) :=
    ggInndiagNormalInput_holds lab hlab
  have hCycAll : LargeEvenLabelAll lab (GGRawPCyclic p) :=
    ggRawPCyclicOn_notD4Three_of_round5 ggRawPCyclicOn_rest5 p hp hp2 lab hlab hS
  have hall : LargeEvenLabelAll lab fun R _ I F =>
      GGRawInnField p R I F ∧
        (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) R I F ∧
          GGRawPCyclic p R I F :=
    largeEvenLabelAll_and hIFall (largeEvenLabelAll_and hIDall hCycAll)
  refine LargeEvenLabelAll.mono ?_ hall
  intro R _ I F hRaw
  obtain ⟨hIF, hID, hCyc⟩ := hRaw
  intro hs hna
  obtain ⟨hmul, hinv, hinn, hFnotI⟩ := hIF hs hna
  have hIDn : GGInndiagNormal R I := hID hs hna
  obtain ⟨J', S, hJ'coe, hJ'S, hJ'norm, hgen, hpS⟩ := hCyc hs hna
  have hJ'normal : J'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnI : n ∈ I := by rw [← hJ'coe]; exact hn
    have hmem : g * n * g⁻¹ ∈ ggInndiag R I := hIDn g n hnI
    have hle : ggInndiag R I ≤ J' := by
      refine sup_le ?_ ?_
      · rintro _ ⟨r, rfl⟩
        change MulAut.conj r ∈ (J' : Set (MulAut R))
        rw [hJ'coe]
        exact hinn r
      · rw [Subgroup.closure_le]
        intro x hx
        change x ∈ (J' : Set (MulAut R))
        rw [hJ'coe]
        exact hx
    exact hle hmem
  refine ⟨⟨J', hJ'normal, hJ'coe⟩, ?_⟩
  intro α hαP hαI hαp f hfF hford
  have hαS : α ∈ S := hpS α hαP
  have hfp : f ^ p = 1 := by rw [← hford]; exact pow_orderOf_eq_one f
  have hfS : f ∈ S := hpS f ⟨1, by simpa using hfp⟩
  let K : Subgroup S := J'.subgroupOf S
  haveI : K.Normal := hJ'norm
  let q : S →* S ⧸ K := QuotientGroup.mk' K
  let a : S := ⟨α, hαS⟩
  let b : S := ⟨f, hfS⟩
  have hqa_pow : (q a) ^ p = 1 := by
    have hmem : (a ^ p : S) ∈ K := by
      rw [Subgroup.mem_subgroupOf]
      change ((a ^ p : S) : MulAut R) ∈ (J' : Set (MulAut R))
      rw [hJ'coe]
      simpa [a] using hαp
    have hqap : q (a ^ p) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (a ^ p)).mpr hmem
    simpa using hqap
  have hqb_pow : (q b) ^ p = 1 := by
    have hbp : b ^ p = 1 := by
      apply Subtype.ext
      simp [b, hfp]
    have hqbp : q (b ^ p) = 1 := by rw [hbp, map_one]
    simpa using hqbp
  have hqa_ne : q a ≠ 1 := by
    intro h
    apply hαI
    rw [QuotientGroup.mk'_apply] at h
    have hmem : a ∈ K := (QuotientGroup.eq_one_iff a).mp h
    have hJ'mem : (a : MulAut R) ∈ J' := Subgroup.mem_subgroupOf.mp hmem
    change (a : MulAut R) ∈ (J' : Set (MulAut R)) at hJ'mem
    rw [hJ'coe] at hJ'mem
    simpa [a] using hJ'mem
  have hqb_ne : q b ≠ 1 := by
    intro h
    apply hFnotI f hfF hford
    rw [QuotientGroup.mk'_apply] at h
    have hmem : b ∈ K := (QuotientGroup.eq_one_iff b).mp h
    have hJ'mem : (b : MulAut R) ∈ J' := Subgroup.mem_subgroupOf.mp hmem
    change (b : MulAut R) ∈ (J' : Set (MulAut R)) at hJ'mem
    rw [hJ'coe] at hJ'mem
    simpa [b] using hJ'mem
  haveI : IsCyclic (S ⧸ K) := ggL45NtAutAsm_isCyclic_quotient hJ'norm hgen
  obtain ⟨j, hjnd, hqaeq⟩ :=
    ggL45NtAutAsm_exists_pow_of_cyclic hp hqa_pow hqb_pow hqa_ne hqb_ne
  refine ⟨j, hjnd, ?_⟩
  have hq : (QuotientGroup.mk (a * (b ^ j)⁻¹) : S ⧸ K) = 1 := by
    have hq' : q (a * (b ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hqaeq, mul_inv_cancel]
    simpa [q] using hq'
  have hmemK : (a * (b ^ j)⁻¹) ∈ K := (QuotientGroup.eq_one_iff _).mp hq
  have hJ'mem : ((a * (b ^ j)⁻¹ : S) : MulAut R) ∈ J' := Subgroup.mem_subgroupOf.mp hmemK
  change ((a * (b ^ j)⁻¹ : S) : MulAut R) ∈ (J' : Set (MulAut R)) at hJ'mem
  rw [hJ'coe] at hJ'mem
  simpa [a, b] using hJ'mem

theorem ggL45NtAutOn_clAut :
    GGL45NtAutOn GGL45NtFamClAut :=
  ggL45NtAutOn_notD4Three.antitone fun _ _ h => h.2

theorem ggL45NtAutOn_ex :
    GGL45NtAutOn GGL45NtFamEx := by
  refine ggL45NtAutOn_notD4Three.antitone fun p lab h hD => ?_
  have h1 := h.2.2
  have h2 := hD.1
  simp only [GGL45NtExcLabel] at h1
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at h2 <;> cases h2

end CFSG.StandardType
