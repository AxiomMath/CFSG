module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsXMod
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.Quasithin.Background.SmithD39TwoSocle
public import CFSG.Quasithin.Background.F918Z3A1Aux
public import CFSG.Quasithin.Background.HM22RowAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin

theorem irreducible_or_card_three_of_irrSpanTrans_index_two
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {A J : Subgroup (MulAut W)} (hJA : J ≤ A)
    (hJn : (J.subgroupOf A).Normal)
    (hindex : (J.subgroupOf A).index = 2)
    (z : MulAut W) (hzJ : z ∈ J) (hz : orderOf z = 3)
    (hfix : ∀ w : W, z w = w → w = 1)
    (hcent : ∀ g ∈ J, g * z = z * g)
    (htrans : IrrSpanTrans A J) :
    IsIrrOn J ⊤ ⊥ ∨ Nat.card J = 3 := by
  classical
  have hfixJ : fixV J = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact hfix w (mem_fixV.1 hw z hzJ)
  have hex : ∃ I : Subgroup W, I ∈ irrSet J ∧ I ≠ ⊥ := by
    by_contra h
    push Not at h
    have hbot : (⨆ I ∈ irrSet J, I) = ⊥ := by
      rw [iSup_eq_bot]
      intro I
      rw [iSup_eq_bot]
      intro hI
      exact h I hI
    have htopbot : (⊤ : Subgroup W) = ⊥ := by rw [← htrans.1, hbot]
    have hcard1 : Nat.card W = 1 := by
      have := congrArg (fun S : Subgroup W => Nat.card ↥S) htopbot
      simpa using this
    rw [hcard] at hcard1
    norm_num at hcard1
  obtain ⟨I, hIset, hIne⟩ := hex
  have hIirrBot : IsIrrOn J I ⊥ := by simpa [hfixJ] using hIset.2
  have hIx : XMod.IsIrr ↥J I := (isIrrOn_bot_iff_isIrr).1 hIirrBot
  have hIinv : XMod.IsInv ↥J I := hIx.1
  have hIstable : StableUnder J I := by
    intro j hj i hi
    exact ((Z3A1.isInv_iff).1 hIinv) j hj i hi
  obtain ⟨tA, htAJ, -⟩ :=
    (Subgroup.index_eq_two_iff_exists_notMem_and' (H := J.subgroupOf A)).1 hindex
  have htA : (tA : MulAut W) ∈ A := tA.2
  have htJ : (tA : MulAut W) ∉ J := fun h => htAJ (Subgroup.mem_subgroupOf.2 h)
  let t : MulAut W := tA
  have hconj : ∀ g ∈ A, ∀ x ∈ J, g * x * g⁻¹ ∈ J := by
    intro g hg x hx
    have hmem := Subgroup.Normal.conj_mem hJn (⟨x, hJA hx⟩ : ↥A)
      (Subgroup.mem_subgroupOf.2 hx) (⟨g, hg⟩ : ↥A)
    simpa using Subgroup.mem_subgroupOf.1 hmem
  have hconjInv : ∀ x ∈ J, t⁻¹ * x * t ∈ J := by
    intro x hx
    have := hconj t⁻¹ (A.inv_mem htA) x hx
    simpa [t] using this
  have hN : XMod.Normalizes ↥J ↥A W := Z3A1.normalizes_of_conj hconj
  have ht2J : t * t ∈ J := by
    have hmem := Subgroup.sq_mem_of_index_two hindex (a := tA)
    simpa [pow_two, t] using (Subgroup.mem_subgroupOf.1 hmem)
  have hmap_self : ∀ {H : Subgroup W}, StableUnder J H → ∀ {j : MulAut W}, j ∈ J →
      H.map j.toMonoidHom = H := by
    intro H hH j hj
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro w hw
      rcases Subgroup.mem_map.1 hw with ⟨v, hv, rfl⟩
      exact hH j hj v hv
    · rw [Subgroup.card_map_of_injective j.injective]
  have hItStable : StableUnder J (I.map t.toMonoidHom) :=
    stableUnder_map_of_normalizes (g := t) hconjInv hIstable
  have hItIrrSet : I.map t.toMonoidHom ∈ irrSet J :=
    map_mem_irrSet (X := J) (g := t) (fun x hx => hconj t htA x hx) hconjInv hIset
  have hIrrOfMem : ∀ H ∈ irrSet J, XMod.IsIrr ↥J H := by
    intro H hH
    exact (isIrrOn_bot_iff_isIrr).1 (by simpa [hfixJ] using hH.2)
  have hItIrr : XMod.IsIrr ↥J (I.map t.toMonoidHom) := hIrrOfMem _ hItIrrSet
  let P : Subgroup W := SmithD39Two.isoComp ↥J I
  let Q : Subgroup W := SmithD39Two.isoComp ↥J (I.map t.toMonoidHom)
  have hPinv : XMod.IsInv ↥J P := SmithD39Two.isInv_isoComp (A := ↥J) I
  have hQinv : XMod.IsInv ↥J Q :=
    SmithD39Two.isInv_isoComp (A := ↥J) (I.map t.toMonoidHom)
  have hType : ∀ H ∈ irrSet J,
      XMod.Iso ↥J H I ∨ XMod.Iso ↥J H (I.map t.toMonoidHom) := by
    intro H hH
    have hHx := hIrrOfMem H hH
    obtain ⟨g, hgA, hsec⟩ := htrans.2 I hIset H hH
    have hsec' : SecIsoOn J (I.map g.toMonoidHom) ⊥ H ⊥ := by
      simpa [hfixJ] using hsec
    have hiso : XMod.Iso ↥J (I.map g.toMonoidHom) H := iso_of_secIsoOn_bot hsec'
    by_cases hgJ : g ∈ J
    · have hIg : I.map g.toMonoidHom = I := hmap_self hIstable hgJ
      have hiso' : XMod.Iso ↥J I H := by rwa [hIg] at hiso
      exact Or.inl (XMod.Iso.symm hIinv hiso')
    · have htgJ : t⁻¹ * g ∈ J := by
        have htinvAJ : tA⁻¹ ∉ J.subgroupOf A := fun h => htAJ ((J.subgroupOf A).inv_mem h)
        have hgAJ : (⟨g, hgA⟩ : ↥A) ∉ J.subgroupOf A :=
          fun h => hgJ (Subgroup.mem_subgroupOf.1 h)
        have hmem : tA⁻¹ * (⟨g, hgA⟩ : ↥A) ∈ J.subgroupOf A := by
          rw [Subgroup.mul_mem_iff_of_index_two hindex]
          simp [htinvAJ, hgAJ]
        simpa [t] using Subgroup.mem_subgroupOf.1 hmem
      have hg_eq : g = t * (t⁻¹ * g) := by group
      have hIg : I.map g.toMonoidHom = I.map t.toMonoidHom := by
        have hcomp : (t * (t⁻¹ * g)).toMonoidHom =
            t.toMonoidHom.comp ((t⁻¹ * g) : MulAut W).toMonoidHom := rfl
        rw [hg_eq, hcomp, ← Subgroup.map_map, hmap_self hIstable htgJ]
      have hiso' : XMod.Iso ↥J (I.map t.toMonoidHom) H := by rwa [hIg] at hiso
      exact Or.inr (XMod.Iso.symm hItIrr.1 hiso')
  have hspan_le : (⨆ H ∈ irrSet J, H) ≤ P ⊔ Q := by
    change (⨆ H ∈ irrSet J, H) ≤
      SmithD39Two.isoComp ↥J I ⊔ SmithD39Two.isoComp ↥J (I.map t.toMonoidHom)
    refine iSup₂_le fun H hH => ?_
    have hHx := hIrrOfMem H hH
    rcases hType H hH with hHI | hHIt
    · have hle : H ≤ SmithD39Two.isoComp ↥J I :=
        SmithD39Two.le_isoComp (A := ↥J) (Q := W) (I := I) (J := H) hHx hHI
      exact hle.trans le_sup_left
    · have hle : H ≤ SmithD39Two.isoComp ↥J (I.map t.toMonoidHom) :=
        SmithD39Two.le_isoComp (A := ↥J) (Q := W) (I := I.map t.toMonoidHom) (J := H)
          hHx hHIt
      exact hle.trans le_sup_right
  have htopPQ : P ⊔ Q = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← htrans.1]
    exact hspan_le
  have hPmap_le_Q : P.map t.toMonoidHom ≤ Q := by
    unfold P Q SmithD39Two.isoComp
    rw [Subgroup.map_iSup]
    refine iSup_le fun H => SmithD39Two.le_isoComp (A := ↥J) (Q := W) ?_ ?_
    · have h := Z391.isIrr_smul (Q := W) hN tA H.2.1
      change XMod.IsIrr ↥J (H.1.map t.toMonoidHom) at h
      exact h
    · have h := XMod.iso_smul (Q := W) hN tA H.2.2
      change XMod.Iso ↥J (H.1.map t.toMonoidHom) (I.map t.toMonoidHom) at h
      exact h
  have hQmap_le_P : Q.map t.toMonoidHom ≤ P := by
    unfold Q P SmithD39Two.isoComp
    rw [Subgroup.map_iSup]
    refine iSup_le fun H => SmithD39Two.le_isoComp (A := ↥J) (Q := W) ?_ ?_
    · have h := Z391.isIrr_smul (Q := W) hN tA H.2.1
      change XMod.IsIrr ↥J (H.1.map t.toMonoidHom) at h
      exact h
    · have h := XMod.iso_smul (Q := W) hN tA H.2.2
      change XMod.Iso ↥J (H.1.map t.toMonoidHom)
        ((I.map t.toMonoidHom).map t.toMonoidHom) at h
      have hcomp : t.toMonoidHom.comp t.toMonoidHom = (t * t).toMonoidHom := rfl
      have hImap : (I.map t.toMonoidHom).map t.toMonoidHom = I := by
        rw [Subgroup.map_map, hcomp, hmap_self hIstable ht2J]
      rwa [hImap] at h
  have hcardPQ : Nat.card P = Nat.card Q := by
    have h1 : Nat.card (P.map t.toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective (K := P) t.injective
    have h2 : Nat.card (P.map t.toMonoidHom) ≤ Nat.card Q :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hPmap_le_Q)
        (Subgroup.inclusion_injective hPmap_le_Q)
    have h3 : Nat.card (Q.map t.toMonoidHom) = Nat.card Q :=
      Subgroup.card_map_of_injective (K := Q) t.injective
    have h4 : Nat.card (Q.map t.toMonoidHom) ≤ Nat.card P :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hQmap_le_P)
        (Subgroup.inclusion_injective hQmap_le_P)
    omega
  have hrkPQ : rk P = rk Q := by
    have hPcard := card_eq_two_pow hW P
    have hQcard := card_eq_two_pow hW Q
    have hpoweq : 2 ^ rk P = 2 ^ rk Q := by
      rw [← hPcard, ← hQcard]
      exact hcardPQ
    exact Nat.pow_right_injective (by norm_num : 1 < 2) hpoweq
  have hdisj : ¬ XMod.Iso ↥J I (I.map t.toMonoidHom) → P ⊓ Q = ⊥ := by
    intro hnot
    by_contra hne
    have hPQinv : XMod.IsInv ↥J (P ⊓ Q) := hPinv.inf hQinv
    obtain ⟨S, hSle, hSirr⟩ := SmithD391.exists_isIrr_le (Λ := J) hPQinv hne
    have hSP : S ≤ P := hSle.trans inf_le_left
    have hSQ : S ≤ Q := hSle.trans inf_le_right
    have hSI : XMod.Iso ↥J S I := by
      have hle : S ≤ SmithD39Two.isoComp ↥J I := hSP
      unfold SmithD39Two.isoComp at hle
      obtain ⟨H, hHiso⟩ := SmithD391.exists_iso_of_le_iSup
        (A := ↥J)
        (S := fun H : {H : Subgroup W // XMod.IsIrr ↥J H ∧ XMod.Iso ↥J H I} =>
          (H : Subgroup W)) (fun H => H.2.1) hSirr hle
      exact XMod.Iso.trans hHiso H.2.2
    have hSIt : XMod.Iso ↥J S (I.map t.toMonoidHom) := by
      have hle : S ≤ SmithD39Two.isoComp ↥J (I.map t.toMonoidHom) := hSQ
      unfold SmithD39Two.isoComp at hle
      obtain ⟨H, hHiso⟩ := SmithD391.exists_iso_of_le_iSup
        (A := ↥J)
        (S := fun H : {H : Subgroup W //
            XMod.IsIrr ↥J H ∧ XMod.Iso ↥J H (I.map t.toMonoidHom)} =>
          (H : Subgroup W)) (fun H => H.2.1) hSirr hle
      exact XMod.Iso.trans hHiso H.2.2
    exact hnot (XMod.Iso.trans (XMod.Iso.symm hSirr.1 hSI) hSIt)
  have hrank_components : P ⊓ Q = ⊥ → rk W = rk P + rk Q := by
    intro hinf
    have h := rk_sup_add_rk_inf (U := P) (W := Q)
    rw [htopPQ, hinf, rk_top, rk_bot] at h
    simpa using h
  have hrkW : rk W = 6 := by
    rw [rk, hcard]
    exact padicValNat.prime_pow 6
  have hz3triple : ∀ w : W, z (z (z w)) = w := by
    have hzpow : z ^ 3 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    intro w
    have := congrArg (fun f : MulAut W => f w) hzpow
    simpa [pow_succ, MulAut.mul_apply] using this
  have hzInv : ∀ {H : Subgroup W}, XMod.IsInv ↥J H → ∀ h ∈ H, z h ∈ H := by
    intro H hH h hh
    exact ((Z3A1.isInv_iff).1 hH) z hzJ h hh
  have hEven : ∀ {H : Subgroup W}, XMod.IsInv ↥J H → 2 ∣ rk H := by
    intro H hH
    obtain ⟨k, hk⟩ := CFSG.Quasithin.H.Mathieu.M22Row.exists_card_eq_four_pow
      (z := z) hW hz3triple hfix H (fun h hh => hzInv hH h hh)
    have hcardH : Nat.card H = 2 ^ rk H := card_eq_two_pow hW H
    have hpoweq : 2 ^ rk H = 2 ^ (2 * k) := by
      rw [← hcardH, hk, show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    have hrkH : rk H = 2 * k := Nat.pow_right_injective (by norm_num : 1 < 2) hpoweq
    exact ⟨k, by rw [hrkH]⟩
  have hiso : XMod.Iso ↥J I (I.map t.toMonoidHom) := by
    by_contra hnot
    have hinf : P ⊓ Q = ⊥ := hdisj hnot
    have hrk := hrank_components hinf
    have hPne : P ≠ ⊥ := by
      intro h
      have hle : I ≤ P := SmithD39Two.le_isoComp (A := ↥J) hIx (XMod.Iso.refl I)
      rw [h] at hle
      exact hIne (le_bot_iff.1 hle)
    have hQne : Q ≠ ⊥ := by
      intro h
      have hle : I.map t.toMonoidHom ≤ Q :=
        SmithD39Two.le_isoComp (A := ↥J) hItIrr (XMod.Iso.refl (I.map t.toMonoidHom))
      rw [h] at hle
      exact (bot_lt_iff_ne_bot.mp hItIrr.2.1) (le_bot_iff.1 hle)
    have h2P : 2 ∣ rk P := hEven hPinv
    obtain ⟨a, ha⟩ := h2P
    omega
  have hPtop : P = ⊤ := by
    have hPleQ : P ≤ Q := by
      unfold P Q SmithD39Two.isoComp
      refine iSup_le fun H => SmithD39Two.le_isoComp (A := ↥J) H.2.1 ?_
      exact XMod.Iso.trans H.2.2 hiso
    have hQleP : Q ≤ P := by
      unfold P Q SmithD39Two.isoComp
      refine iSup_le fun H => SmithD39Two.le_isoComp (A := ↥J) H.2.1 ?_
      exact XMod.Iso.trans H.2.2 (XMod.Iso.symm hIinv hiso)
    rw [sup_eq_left.mpr hQleP] at htopPQ
    exact htopPQ
  obtain ⟨c, hc⟩ := SmithD39Two.exists_rk_eq_mul (A := ↥J) hW hIx
    (XMod.isInv_top) (by rw [← hPtop])
  have hc' : rk W = c * rk I := by
    rw [← rk_top]
    exact hc
  have hIpos : 0 < rk I := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hIne ((rk_eq_zero_iff hW).1 h0)
  have hIdvd : rk I ∣ 6 := ⟨c, by rw [← hrkW, hc', mul_comm]⟩
  have hIle : rk I ≤ 6 := Nat.le_of_dvd (by norm_num) hIdvd
  have hI2 : 2 ∣ rk I := hEven hIinv
  have hIcases : rk I = 2 ∨ rk I = 6 := by
    obtain ⟨q, hq⟩ := hI2
    have hqle : q ≤ 3 := by omega
    have hqpos : 0 < q := by omega
    interval_cases q
    · exact Or.inl (by omega)
    · exfalso
      rw [hq] at hIdvd
      norm_num at hIdvd
    · exact Or.inr (by omega)
  rcases hIcases with hrkI | hrkI
  ·
    right
    have hcardI : Nat.card I = 4 := by
      rw [card_eq_two_pow hW I, hrkI]
      norm_num
    have hHomI : ∀ H ∈ irrSet J, XMod.Iso ↥J H I := by
      intro H hH
      rcases hType H hH with h | h
      · exact h
      · exact XMod.Iso.trans h (XMod.Iso.symm hIinv hiso)
    have hfaith : ∀ j : ↥J, (∀ i : ↥I, (j : MulAut W) i = i) → j = 1 := by
      intro j hj
      have hfixOn : ∀ H ∈ irrSet J, ∀ h : ↥H, (j : MulAut W) h = h := by
        intro H hH h
        obtain ⟨φ, hφ⟩ := hHomI H hH
        have hHx := hIrrOfMem H hH
        have hyh_mem : (j : MulAut W) (h : W) ∈ H :=
          ((Z3A1.isInv_iff).1 hHx.1) j j.2 h h.2
        let h' : ↥H := ⟨(j : MulAut W) (h : W), hyh_mem⟩
        have hconj : (h' : W) = (j : MulAut W) (h : W) := rfl
        have h1 := hφ j h h' hconj
        have h2 : ((φ h' : ↥I) : W) = ((φ h : ↥I) : W) := by
          simpa [Subgroup.smul_def, MulAut.smul_def, hj (φ h)] using h1.symm
        have h3 : h' = h := φ.injective (Subtype.ext h2)
        exact congrArg Subtype.val h3
      have hfixW : ∀ w : W, (j : MulAut W) w = w := by
        intro w
        have hw : w ∈ (⨆ H : {H : Subgroup W // H ∈ irrSet J}, H.1) := by
          rw [← iSup_subtype' (p := fun H : Subgroup W => H ∈ irrSet J)
            (f := fun H _ => H)]
          rw [htrans.1]
          trivial
        refine Subgroup.iSup_induction (C := fun z => (j : MulAut W) z = z)
          (fun H : {H : Subgroup W // H ∈ irrSet J} => H.1) hw ?_ ?_ ?_
        · intro H x hx
          simpa using hfixOn H.1 H.2 ⟨x, hx⟩
        · exact map_one (j : MulAut W)
        · intro x y hx hy
          rw [map_mul (j : MulAut W) x y, hx, hy]
      exact Subtype.ext (MulEquiv.ext hfixW)
    obtain ⟨v, hvI, hvne⟩ : ∃ v : W, v ∈ I ∧ v ≠ 1 := by
      obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hIne
      exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩
    have hzI : ∀ i ∈ I, z i ∈ I := hzInv hIinv
    have hz2I : ∀ i ∈ I, z (z i) ∈ I := fun i hi => hzI _ (hzI i hi)
    have hz_nofix1 : z v ≠ v := fun h => hvne (hfix v h)
    have hz_nofix2 : z (z v) ≠ v := by
      intro h
      have h1 : v = z v := by
        have := congrArg z h
        rwa [hz3triple v] at this
      exact hz_nofix1 h1.symm
    have hzv_ne_one : z v ≠ 1 := fun h => hvne (z.injective (by rw [h, map_one]))
    have hzzv_ne_one : z (z v) ≠ 1 := by
      intro h
      apply hzv_ne_one
      exact z.injective (by simpa using h)
    have hset_subset : ({1, v, z v, z (z v)} : Set W) ⊆ I := by
      intro u hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact I.one_mem
      · exact hvI
      · exact hzI v hvI
      · exact hz2I v hvI
    have h1not : (1 : W) ∉ ({v, z v, z (z v)} : Set W) := by
      intro h
      rcases h with h | h | h
      · exact hvne h.symm
      · exact hzv_ne_one h.symm
      · exact hzzv_ne_one h.symm
    have hvnot : v ∉ ({z v, z (z v)} : Set W) := by
      intro h
      rcases h with h | h
      · exact hz_nofix1 h.symm
      · exact hz_nofix2 h.symm
    have hzvnot : z v ∉ ({z (z v)} : Set W) := by
      intro h
      exact hz_nofix1 (z.injective h).symm
    have hset_card : ({1, v, z v, z (z v)} : Set W).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (s := ({v, z v, z (z v)} : Set W)) h1not,
        Set.ncard_insert_of_notMem (s := ({z v, z (z v)} : Set W)) hvnot,
        Set.ncard_insert_of_notMem (s := ({z (z v)} : Set W)) hzvnot,
        Set.ncard_singleton]
    have hIcard_set : (I : Set W).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hcardI
    have hIset : (I : Set W) = {1, v, z v, z (z v)} := by
      refine (Set.eq_of_subset_of_ncard_le hset_subset ?_ ?_).symm
      · rw [hIcard_set, hset_card]
      · exact Set.toFinite _
    let ev : ↥J → {i : ↥I // i ≠ (1 : ↥I)} := fun j =>
      ⟨⟨j.1 v, hIstable j j.2 v hvI⟩, by
        intro h
        exact hvne (j.1.injective (by simpa using congrArg Subtype.val h))⟩
    have hev_inj : Function.Injective ev := by
      intro a b hab
      have h1 : (a.1 : MulAut W) v = (b.1 : MulAut W) v :=
        congrArg (fun i : {i : ↥I // i ≠ (1 : ↥I)} => ((i : ↥I) : W)) hab
      have hvab : ((b⁻¹ * a : ↥J) : MulAut W) v = v := by
        calc ((b⁻¹ * a : ↥J) : MulAut W) v
            = (b.1 : MulAut W)⁻¹ ((a.1 : MulAut W) v) := rfl
          _ = (b.1 : MulAut W)⁻¹ ((b.1 : MulAut W) v) := by rw [h1]
          _ = v := (b.1 : MulAut W).symm_apply_apply v
      have hcommute : ∀ w : W, ((b⁻¹ * a : ↥J) : MulAut W) (z w) =
          z (((b⁻¹ * a : ↥J) : MulAut W) w) := by
        intro w
        have := congrArg (fun f : MulAut W => f w)
          (hcent ((b⁻¹ * a : ↥J) : MulAut W) (b⁻¹ * a).2)
        simpa [MulAut.mul_apply] using this
      have hfixI : ∀ i : ↥I, ((b⁻¹ * a : ↥J) : MulAut W) i = i := by
        intro i
        have hi : (i : W) ∈ ({1, v, z v, z (z v)} : Set W) := by
          rw [← hIset]
          exact i.2
        rcases hi with h1 | h1 | h1 | h1
        · rw [h1, map_one]
        · rw [h1, hvab]
        · rw [h1, hcommute v, hvab]
        · rw [h1]
          calc ((b⁻¹ * a : ↥J) : MulAut W) (z (z v))
              = z (((b⁻¹ * a : ↥J) : MulAut W) (z v)) := hcommute (z v)
            _ = z (z (((b⁻¹ * a : ↥J) : MulAut W) v)) := by rw [hcommute v]
            _ = z (z v) := by rw [hvab]
      have hba : (b⁻¹ * a : ↥J) = 1 := hfaith _ hfixI
      calc a = b * (b⁻¹ * a) := by group
        _ = b * 1 := by rw [hba]
        _ = b := mul_one b
    have hcardJ_le : Nat.card ↥J ≤ 3 := by
      haveI : Fintype ↥I := Fintype.ofFinite _
      have hle : Nat.card ↥J ≤ Nat.card {i : ↥I // i ≠ (1 : ↥I)} :=
        Nat.card_le_card_of_injective ev hev_inj
      have hcard_ne : Nat.card {i : ↥I // i ≠ (1 : ↥I)} = 3 := by
        have h2 : Fintype.card ↥I = 4 := by
          rw [← Nat.card_eq_fintype_card]
          exact hcardI
        rw [Nat.card_eq_fintype_card]
        change Fintype.card ({i : ↥I | i ≠ (1 : ↥I)} : Set ↥I) = 3
        rw [Set.card_ne_eq, h2]
      omega
    have h3dvd : 3 ∣ Nat.card ↥J := by
      rw [← hz]
      exact Subgroup.orderOf_dvd_natCard J hzJ
    have h3le : 3 ≤ Nat.card ↥J := Nat.le_of_dvd (by norm_num) h3dvd
    omega
  ·
    left
    have hIeqTop : I = ⊤ := by
      refine eq_of_le_of_rk_le hW le_top ?_
      rw [rk_top, hrkW, hrkI]
    rwa [hIeqTop] at hIirrBot

end CFSG.LocalAnalysis.WeakClosure81
