module

public import CFSG.Quasithin.Vol2.Ch10SecQ34ND
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem gap10_2_6Nonquasi_of (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1025 : Stmt10_2_5) : Gap10_2_6Nonquasi := by
  intro G _ _ T L I hyp H hH hHM X K hX hKc hXK _ hNQ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hS := isSylowTwoOf_T1_of_inM h331 h37 h38 h1025 hyp hH hHM
  have hH2 : pCoreOf 2 H ≠ ⊥ := (inH_of_inM hH).2
  obtain ⟨t, ht, hXt⟩ : ∃ t ∈ T, X = L ∨ X = CFSG.conjugate L t := by
    rcases hX with h | ⟨t, ht, -, h⟩
    · exact ⟨1, T.one_mem, Or.inl h⟩
    · exact ⟨t, ht, Or.inr h⟩
  obtain ⟨hXc, hXn, -, -⟩ := li_data h37 h38 hyp ht hXt
  have hT1M : T1 T L ≤ fsuM T L := inf_le_left.trans (le_fsuM T L)
  have hXfam := cComp_subset_lFamily hT1M hXc
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKn : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp
      (Vol2Native.lemma_1_2_4_normal hK h37 h38 hH2 hS hXfam hXK.le hKc hXn)
  obtain ⟨hcase, hcommon, -⟩ := Vol2Native.lemma_1_2_1_four_core hK h36 hH2 hKc
  rcases hNQ with ⟨-, h21, -⟩ | ⟨hcomm, ⟨p, hp, hp5, -, hSLp⟩, N, hNn, hNeq, hSL5⟩
  · exact hne h21
  rcases hcase with hc | ⟨p', hp', hp'3, -, he0, hnat⟩ | ⟨-, -, hSL5', -⟩
  ·
    rcases C10P34.le_center_or_comm hc.1 (CFSG.oddCore ↥(modO2Image H K)) with hz | hab
    · apply hcomm
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨o, ho, rfl⟩ k hk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hz ho) ⟨k, hk⟩)
    · obtain ⟨a, b, hab'⟩ := hcommon.2.1.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
      obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
      apply hab'
      have h1 := hab (QuotientGroup.mk a'') (QuotientGroup.mk b'')
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      have h2 : (QuotientGroup.mk (a'' * b'') :
          ↥(modO2Image H K) ⧸ CFSG.fittingSubgroup ↥(modO2Image H K)) =
          QuotientGroup.mk (b'' * a'') := by
        rw [QuotientGroup.eq, hcommon.1]
        exact h1
      simp only [← QuotientGroup.mk_mul]
      rw [h2]
  ·
    have := hNn
    exact C10P34.false_of_natural hK h331 h37 h38 h1011 hyp ht hXt hH hS hKn hXK.le hp' hp'3 he0
      hnat (by rw [hcommon.1]) N hNeq hSL5
  ·
    obtain ⟨e5⟩ := hSL5'
    obtain ⟨ep⟩ := hSLp
    have : Fact p.Prime := ⟨hp⟩
    have h5 := C10P34.eq_five_of_sl2_equiv
      ((e5.symm.trans (QuotientGroup.quotientMulEquivOfEq hcommon.1)).trans ep)
    rw [h5] at hp5
    norm_num at hp5

end CFSG.Quasithin.Vol2.Ch10.SecB
