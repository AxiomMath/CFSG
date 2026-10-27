module

public import CFSG.Quasithin.Vol2.Ch12Sec5Lemmas
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Vol2.Ch12Sec2StatementsPrime
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3OffenderB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 E3

namespace S125

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem mem_R2 {E : Subgroup G} {v : G} (hv : v ∈ reducedAggregate E) :
    v ∈ pCoreOf 2 E ∧ (∀ k ∈ pCoreOf 2 E, k * v = v * k) ∧ v ^ 2 = 1 := by
  obtain ⟨r, hr, rfl⟩ := hv
  obtain ⟨-, -, hRc⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥E) 2
  obtain ⟨h1, h2, h3⟩ := BlueprintB2.mem_centerTorsion_iff.1 (hRc hr)
  have hc : CFSG.inSubgroup (CFSG.pCore 2) E = pCoreOf 2 E := by
    rw [CFSG.inSubgroup, CFSG.Open.pCoreOf]
  refine ⟨?_, fun k hk => ?_, ?_⟩
  · rw [← hc]
    exact ⟨r, h1, rfl⟩
  · rw [← hc] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact congrArg Subtype.val (h2 k' hk')
  · have := congrArg Subtype.val h3
    simpa using this

theorem isElemAbelian_of_hyp1223 (hH : Hyp1223 G T L V) : IsElemAbelian 2 V := by
  have hR := hH.irrPlus.1
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun v hv => (mem_R2 (hR hv)).2.2⟩
  exact ((mem_R2 (hR a.2)).2.1 b (mem_R2 (hR b.2)).1).symm

theorem le_of_hyp1223 (hH : Hyp1223 G T L V) : V ≤ T := by
  have hT := hH.sylow
  have hS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    ⟨le_sup_right, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  exact fun v hv => pCoreOf_two_le_of_isSylowTwoOf hS (mem_R2 (hH.irrPlus.1 hv)).1

theorem not_nParam_le_zero (hH : Hyp1223 G T L V) {H : Subgroup G} (hTH : T ≤ H) :
    ¬ E1.nParam H ≤ 0 := by
  intro h0
  have hodd := E1.odd_of_nParam_le_zero h0
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH.irrPlus.2.1
  have hv2 : orderOf (v : G) = 2 :=
    orderOf_eq_prime ((isElemAbelian_of_hyp1223 hH).2 v v.2) fun h => hv1 (Subtype.ext h)
  have hdvd : orderOf (v : G) ∣ Nat.card H :=
    Subgroup.orderOf_dvd_natCard H (hTH (le_of_hyp1223 hH v.2))
  rw [hv2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem one_lt_nParam_of (h6 : Lemma12_5_6) (h7 : Lemma12_5_7) (h10 : Lemma12_5_10)
    (hH : Hyp125 G T L V) (F : Frame125 T L V) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) : 1 < E1.nParam H := by
  have hVe := isElemAbelian_of_hyp1223 hH.hyp
  have hs : sParam hVe = 3 := ((h6 G T L V hH) hVe).2.2
  have hW := (h7 G T L V hH).2.2
  have hC := (h10 G T L V F hH).2
  have hT := hH.hyp.sylow
  have hS : IsSylowIn 2 T H :=
    ⟨hHs.1.1, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hHs.1.1))⟩
  have h0 := not_nParam_le_zero hH.hyp hHs.1.1
  by_contra hle
  push Not at hle
  have h1 : E1.nParam H = ((1 : ℕ) : ℕ∞) := by
    have hpos : 0 < E1.nParam H := lt_of_not_ge h0
    have h01 := Order.add_one_le_of_lt hpos
    rw [zero_add] at h01
    exact_mod_cast le_antisymm hle h01
  have hgen := e3_19 hVe hS (i := 0) h1 (by rw [hs]; norm_num)
  apply hHs.2.1
  rw [← hgen, zero_add]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hW)

omit [Finite G] in
theorem V1_le (F : Frame125 T L V) : F.V1 ≤ V := Subgroup.map_subtype_le _

omit [Finite G] in
theorem V1_ne_bot (F : Frame125 T L V) : F.V1 ≠ ⊥ := by
  intro h
  have hw : ((F.e.symm (Multiplicative.ofAdd (Pi.single 0 1)) : ↥V) : G) ∈ F.V1 := by
    refine ⟨F.e.symm (Multiplicative.ofAdd (Pi.single 0 1)), fun k hk => ?_, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact Pi.single_eq_of_ne (by simpa using hk) _
  rw [h, Subgroup.mem_bot] at hw
  have h1 : F.e.symm (Multiplicative.ofAdd (Pi.single 0 1)) = 1 := Subtype.ext hw
  have h2 := congrArg F.e h1
  rw [MulEquiv.apply_symm_apply, map_one] at h2
  have h3 := congrArg (fun x : Multiplicative (Fin 10 → ZMod 2) => Multiplicative.toAdd x 0) h2
  simp at h3

end S125

theorem lemma12_5_12_of (h6 : Lemma12_5_6) (h7 : Lemma12_5_7) (h10 : Lemma12_5_10)
    (h2211 : Stmt12_2_11') : Lemma12_5_12 := by
  intro G _ _ T L V F hH H hHs hHV
  have h1 := S125.one_lt_nParam_of h6 h7 h10 hH F hHs
  obtain ⟨hle, h2⟩ := h2211 G T L V H F.V1 hH.hyp hHs (S125.V1_ne_bot F) (S125.V1_le F) hHV
    (Or.inl hH.quot)
  have hn : E1.nParam H = 2 := by
    refine le_antisymm hle ?_
    have := Order.add_one_le_of_lt h1
    rwa [one_add_one_eq_two] at this
  exact ⟨hn, h2 hn⟩

end CFSG.Quasithin.H13
