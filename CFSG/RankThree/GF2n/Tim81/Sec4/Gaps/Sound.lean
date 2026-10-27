module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Check
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Defs
public import CFSG.LargeExtraspecial.S97RYWit
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S97RYCore

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75
  CFSG.CGT.Timmesfeld75.WCCheck CFSG.LargeExtraspecial.S11.PairCheck
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six
open CFSG.RankThree.GF2n.Tim81
open scoped Pointwise

variable {P : GData} {M : Subgroup (Equiv.Perm (Fin P.D.n))} {genG : ℤ → M}

@[expose] noncomputable def gensT (D : Data) (M : Subgroup (Equiv.Perm (Fin D.n))) (J : List Bool)
    (genG : ℤ → M) : List M :=
  1 :: (idxU D J).map (eltG (pcG D genG))

@[expose] noncomputable def gensTc (D : Data) (M : Subgroup (Equiv.Perm (Fin D.n))) (J : List Bool)
    (genG : ℤ → M) (c : List Int) : List M :=
  (gensT D M J genG).map fun x => wG D genG c * x * (wG D genG c)⁻¹

theorem closure_gens_eq_sup {T : Subgroup M} {J : List Bool} {c : List Int}
    (hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU P.D J, eltG (pcG P.D genG) i = x) :
    Subgroup.closure {g | g ∈ gensT P.D M J genG ++ gensTc P.D M J genG c} =
      T ⊔ conjSubgroup (wG P.D genG c) T := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Subgroup.one_mem _
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        exact Subgroup.mem_sup_left ((hmemT _).2 (Or.inr ⟨i, hi, rfl⟩))
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjSubgroup]
      rcases List.mem_cons.1 hy with rfl | hy
      · simp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
        simpa [mul_assoc] using (hmemT _).2 (Or.inr ⟨i, hi, rfl⟩)
  · refine sup_le ?_ ?_
    · intro x hx
      rcases (hmemT x).1 hx with rfl | ⟨i, hi, rfl⟩
      · exact Subgroup.subset_closure (List.mem_append_left _ (List.mem_cons_self ..))
      · exact Subgroup.subset_closure
          (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hi)))
    · intro y hy
      rw [mem_conjSubgroup] at hy
      rcases (hmemT _).1 hy with h1 | ⟨i, hi, hxi⟩
      · have hy1 : y = 1 := by
          have := congrArg (fun z => wG P.D genG c * z * (wG P.D genG c)⁻¹) h1
          simpa [mul_assoc] using this
        rw [hy1]
        exact Subgroup.one_mem _
      · have hyeq : y = wG P.D genG c * eltG (pcG P.D genG) i * (wG P.D genG c)⁻¹ := by
          have := congrArg (fun z => wG P.D genG c * z * (wG P.D genG c)⁻¹) hxi
          simpa [mul_assoc] using this.symm
        rw [hyeq]
        refine Subgroup.subset_closure (List.mem_append_right _ ?_)
        exact List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_map_of_mem hi))

@[expose] def blockSet (n : Nat) [NeZero n] (bs : List (List Nat)) : Finset (Finset (Fin n)) :=
  (bs.map (blockFinset n)).toFinset

private theorem blockFinset_inj_on {n : Nat} [NeZero n] {bs : List (List Nat)}
    (hlen : bs.length = 5)
    (hne : ∀ B ∈ bs, B ≠ [])
    (hdisj : ∀ i < 5, ∀ j < 5, i ≠ j → ∀ x, x ∈ bs.getD i [] → x ∉ bs.getD j [])
    (hlt : ∀ B ∈ bs, ∀ x ∈ B, x < n) :
    ∀ B ∈ bs, ∀ C ∈ bs, blockFinset n B = blockFinset n C → B = C := by
  intro B hB C hC heq
  by_contra hBC
  have hBidx : bs.idxOf B < bs.length := List.idxOf_lt_length_of_mem hB
  have hCidx : bs.idxOf C < bs.length := List.idxOf_lt_length_of_mem hC
  have hBget : bs.getD (bs.idxOf B) [] = B := by
    rw [List.getD_eq_get (l := bs) (d := []) (i := ⟨bs.idxOf B, hBidx⟩),
      List.idxOf_get hBidx]
  have hCget : bs.getD (bs.idxOf C) [] = C := by
    rw [List.getD_eq_get (l := bs) (d := []) (i := ⟨bs.idxOf C, hCidx⟩),
      List.idxOf_get hCidx]
  have hBCidx : bs.idxOf B ≠ bs.idxOf C := by
    intro h
    apply hBC
    rw [← hBget, ← hCget, h]
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne B hB)
  have hxlt : x < n := hlt B hB x hx
  have hxF : Fin.ofNat n x ∈ blockFinset n B := by
    rw [blockFinset]
    exact Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, rfl⟩
  rw [heq] at hxF
  rw [blockFinset] at hxF
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxF
  have hyC : y ∈ C := List.mem_toFinset.mp hy
  have hyn : y < n := hlt C hC y hyC
  have hxy : y = x := by
    have := congrArg Fin.val hyx
    simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hyn] using this
  have hdisj' := hdisj (bs.idxOf B) (by omega) (bs.idxOf C) (by omega) hBCidx x
  rw [hBget, hCget] at hdisj'
  exact hdisj' hx (by rwa [hxy] at hyC)

theorem card_blockSet {n : Nat} [NeZero n] {bs : List (List Nat)}
    (hlen : bs.length = 5) (hnd : bs.Nodup)
    (hne : ∀ B ∈ bs, B ≠ [])
    (hdisj : ∀ i < 5, ∀ j < 5, i ≠ j → ∀ x, x ∈ bs.getD i [] → x ∉ bs.getD j [])
    (hlt : ∀ B ∈ bs, ∀ x ∈ B, x < n) :
    (blockSet n bs).card = 5 := by
  have hmapnd : (bs.map (blockFinset n)).Nodup :=
    hnd.map_on (fun B hB C hC heq => blockFinset_inj_on hlen hne hdisj hlt B hB C hC heq)
  rw [blockSet, List.toFinset_card_of_nodup hmapnd, List.length_map, hlen]

theorem image_inv_mem_of_image_mem {n : Nat} {x : Equiv.Perm (Fin n)}
    {S : Finset (Finset (Fin n))} (h : ∀ B ∈ S, B.image x ∈ S) :
    ∀ B ∈ S, B.image x.symm ∈ S := by
  have hsub : S.image (fun B => B.image x) ⊆ S := by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    exact h B hB
  have hcard : (S.image (fun B => B.image x)).card = S.card :=
    Finset.card_image_of_injective S (Finset.image_injective x.injective)
  have heq : S.image (fun B => B.image x) = S :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro B hB
  have hB' : B ∈ S.image (fun B => B.image x) := heq.symm ▸ hB
  obtain ⟨C, hC, hCB⟩ := Finset.mem_image.mp hB'
  rw [← hCB, Finset.image_image]
  rw [show (⇑(Equiv.symm x) ∘ ⇑x) = id from by funext b; simp, Finset.image_id]
  exact hC

structure MaskFacts (P : GData) (M : Subgroup (Equiv.Perm (Fin P.D.n)))
    (genG : ℤ → M) (T : Subgroup M) (J : List Bool) : Prop where
  hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU P.D J, eltG (pcG P.D genG) i = x
  hcard : Nat.card T = (idxU P.D J).length + 1
  hmemU : ∀ {t : Table} {x : M}, Rep P.D.n t x → t.size = P.D.n →
    (memU P.D J t = true ↔ x ∈ T)
  hcontains : ∀ {i : ℕ}, (idxU P.D J).contains i = true → eltG (pcG P.D genG) i ∈ T

theorem witness_of_notClosed {T : Subgroup M} {J : List Bool}
    (hn : P.D.n < 2 ^ 32) (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
    (hD : MaskFacts P M genG T J) {i j : Nat}
    (hok : gverdictOK P J (.notClosed i j) = true) : False := by
  simp only [gverdictOK, verdictOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨hi, hj⟩, hU⟩ := hok
  have hprod := T.mul_mem (hD.hcontains hi) (hD.hcontains hj)
  have := (hD.hmemU (Rep.compT (rep_el hn hgen i) (rep_el hn hgen j)) (size_compT' _ _)).2 hprod
  rw [hU] at this
  exact absurd this (by decide)

theorem witness_of_bad {T : Subgroup M} {J : List Bool}
    (hn : P.D.n < 2 ^ 32) (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hD : MaskFacts P M genG T J)
    (hT : IsWC T) {t y : Nat} {g : List Int}
    (hok : gverdictOK P J (.bad t y g) = true) : False := by
  simp only [gverdictOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨ht, hy⟩, ht1⟩, hcomm⟩, hU⟩ := hok
  have htT := hD.hcontains ht
  have ht1' : eltG (pcG P.D genG) t ≠ 1 := fun h =>
    ht1 (beq_iff_eq.1 (beq_of_eq (rep_el hn hgen t)
      (by rw [show eltG (pcG P.D genG) t = 1 from h]; exact Rep.idT (G := M) hn)
      (size_el _) size_idT'))
  have hle : conjSubgroup (wG P.D genG g) T ≤
      Subgroup.centralizer ({eltG (pcG P.D genG) t} : Set M) := by
    intro w hw
    rw [mem_conjSubgroup] at hw
    obtain ⟨u, hu, hru⟩ := exists_mem_tabU_of_mem hn hgen hD.hmemT hw
    have hrc := rep_conjW hn hgen hinv g hru
    rw [show wG P.D genG g * ((wG P.D genG g)⁻¹ * w * wG P.D genG g) * (wG P.D genG g)⁻¹ =
      w by group] at hrc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact eq_of_rep ((compT_eq_of_commT (hcomm u hu)) ▸ Rep.compT hrc (rep_el hn hgen t))
      (Rep.compT (rep_el hn hgen t) hrc)
  have hc := (hT.2 _ htT ht1').2 _ hle
  have hyT : wG P.D genG g * eltG (pcG P.D genG) y * (wG P.D genG g)⁻¹ ∈ T := by
    rw [← hc, mem_conjSubgroup]
    simpa [mul_assoc] using hD.hcontains hy
  have := (hD.hmemU (rep_conjW hn hgen hinv g (rep_el hn hgen y)) (size_compT' _ _)).2 hyT
  rw [hU] at this
  exact absurd this (by decide)

theorem exists_alt5_quotient {X S : Type} [Group X] [Finite X] [Fintype S] {a : Nat}
    (φ : X →* Equiv.Perm S) (hcardS : Fintype.card S = 5)
    (hcardX : Nat.card X = 2 ^ a * 60) (hker : Nat.card φ.ker = 2 ^ a) :
    ∃ R : Subgroup X, ∃ _ : R.Normal, Group.IsSolvable ↥R ∧
      Nonempty (X ⧸ R ≃* alternatingGroup (Fin 5)) := by
  have hquot : Nat.card (X ⧸ φ.ker) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [hcardX, hker] at h
    have h' : 2 ^ a * 60 = 2 ^ a * Nat.card (X ⧸ φ.ker) := by
      calc 2 ^ a * 60 = Nat.card (X ⧸ φ.ker) * 2 ^ a := h
        _ = 2 ^ a * Nat.card (X ⧸ φ.ker) := mul_comm _ _
    exact (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h').symm
  have hrange : Nat.card φ.range = 60 := by
    rw [← hquot]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm
  let e : S ≃ Fin 5 := Fintype.equivFinOfCardEq hcardS
  let Psub : Subgroup (Equiv.Perm (Fin 5)) :=
    φ.range.map e.permCongrHom.toMonoidHom
  have hPcard : Nat.card Psub = 60 := by
    rw [show Psub = φ.range.map e.permCongrHom.toMonoidHom from rfl,
      Subgroup.card_map_of_injective e.permCongrHom.injective, hrange]
  have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hidx : Psub.index = 2 := by
    have h := Psub.card_mul_index
    rw [hPcard, hcardPerm] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 60) h
  have hA5le : alternatingGroup (Fin 5) ≤ Psub :=
    Equiv.Perm.alternatingGroup_le_of_index_le_two (by rw [hidx])
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hP_eq : Psub = alternatingGroup (Fin 5) := by
    exact (Subgroup.eq_of_le_of_card_ge hA5le (by rw [hPcard, hA5card])).symm
  let eR : φ.range ≃* Psub :=
    Subgroup.equivMapOfInjective φ.range e.permCongrHom.toMonoidHom
      e.permCongrHom.injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsPGroup 2 φ.ker := IsPGroup.of_card hker
  haveI : Group.IsNilpotent φ.ker := (IsPGroup.of_card hker).isNilpotent
  haveI : Group.IsSolvable φ.ker := inferInstance
  exact ⟨φ.ker, inferInstance, inferInstance,
    ⟨(QuotientGroup.quotientKerEquivRange φ).trans (eR.trans (MulEquiv.subgroupCongr hP_eq))⟩⟩

private theorem witness_of_le (hn : P.D.n < 2 ^ 32)
    (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : BaseFacts P.D)
    (hv : ∀ J ∈ allMasks P.D.cls.length, ∀ T : Subgroup M, MaskFacts P M genG T J → IsWC T →
      4 ≤ Nat.card T → ∃ g : M, SubpairWitnessAt M T g)
    {T : Subgroup M} (hT : IsWC T) (h4 : 4 ≤ Nat.card T) (hTS : T ≤ S0 P.D genG) :
    ∃ g : M, SubpairWitnessAt M T g := by
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    omega
  obtain ⟨J, hJ, hnd, h0, hbd, hmemT⟩ :=
    exists_mask (D := P.D) (M := M) (genG := genG) hn hgen hinv hF hT hT1 hTS
  have hcard := card_of_idx (D := P.D) (M := M) hn hgen hF hnd h0 hbd hmemT
  have hmemU : ∀ {t : Table} {x : M}, Rep P.D.n t x → t.size = P.D.n →
      (memU P.D J t = true ↔ x ∈ T) := fun ht hts => memU_iff_of_mask hn hgen hmemT ht hts
  have hcontains : ∀ {i : ℕ}, (idxU P.D J).contains i = true → eltG (pcG P.D genG) i ∈ T :=
    fun hi => (hmemT _).2 (Or.inr ⟨_, List.elem_iff.1 hi, rfl⟩)
  exact hv J hJ T ⟨hmemT, hcard, hmemU, hcontains⟩ hT h4

theorem subpairWitness_of_masks (hgen : ∀ l, Rep P.D.n (P.D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹)
    (hM : ∃ m : ℕ, Odd m ∧ Nat.card M = 2 ^ P.D.pc.length * m)
    (hn : P.D.n < 2 ^ 32) (hnpos : 0 < P.D.n) (hbase : baseCheck P.D = true)
    (hv : ∀ J ∈ allMasks P.D.cls.length, ∀ T : Subgroup M, MaskFacts P M genG T J → IsWC T →
      4 ≤ Nat.card T → ∃ g : M, SubpairWitnessAt M T g) : SubpairWitness M := by
  intro T hT h4
  have hF := baseFacts_of_check hbase
  obtain ⟨m, hm, hcardM⟩ := hM
  have hp := isPGroup_S0_base hn hgen hinv hF
  have hidx : ¬ 2 ∣ (S0 P.D genG).index := by
    have h := (S0 P.D genG).card_mul_index
    rw [card_S0_base hn hgen hF hinv, hcardM] at h
    have : (S0 P.D genG).index = m := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h
    rw [this]
    exact hm.not_two_dvd_nat
  let P₀ : Sylow 2 M := hp.toSylow hidx
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q P₀
  have hT'S : conjSubgroup c T ≤ S0 P.D genG := by
    intro x hx
    have h1 : x ∈ conjSubgroup c (Q : Subgroup M) := Subgroup.map_mono hTQ hx
    have h2 : x ∈ ((c • Q : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact h1
    rw [hc] at h2
    exact h2
  have hT' : IsWC (conjSubgroup c T) := hT.conj c
  have hcard' : Nat.card (conjSubgroup c T) = Nat.card T := card_conjSubgroup c T
  obtain ⟨g', hg'⟩ := witness_of_le (P := P) hn hgen hinv hF hv hT'
    (hcard' ▸ h4) hT'S
  obtain ⟨g, hg⟩ := SubpairWitnessAt.of_mulEquiv (e := MulAut.conj c) (T := T) hg'
  exact ⟨g, hg⟩

end CFSG.RankThree.GF2n.Tim81.Gaps
