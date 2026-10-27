module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIsoAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private lemma s16t3_no_class_two_iso (r : Fin 3 → Fin 3 → Prop)
    (hrefl : ∀ i, r i i)
    (hsymm : ∀ i j, r i j → r j i)
    (hcard : ∀ i, Nat.card {k : Fin 3 // r k i} = 2) : False := by
  classical
  let T : Fin 3 → Finset (Fin 3) := fun i => Finset.univ.filter (fun k => r k i)
  have hT : ∀ i, (T i).card = 2 := by
    intro i
    have h : (T i).card = Nat.card {k : Fin 3 // r k i} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h, hcard i]
  have h0T : (0 : Fin 3) ∈ T 0 := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrefl 0
  have hErase : ((T 0).erase 0).card = 1 := by
    rw [Finset.card_erase_of_mem h0T, hT 0]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hErase
  have hT0 : T 0 = {0, y} := by
    rw [← Finset.insert_erase h0T, hy]
  have hy0 : y ≠ 0 := by
    have hmem : y ∈ (T 0).erase 0 := by rw [hy]; exact Finset.mem_singleton_self y
    exact (Finset.mem_erase.mp hmem).1
  have hyr : r y 0 := by
    have hmem : y ∈ T 0 := by
      rw [hT0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have hcard_pair : ({0, y} : Finset (Fin 3)).card = 2 := Finset.card_pair (Ne.symm hy0)
  have hTy : T y = {0, y} := by
    have hsub : ({0, y} : Finset (Fin 3)) ⊆ T y := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hsymm y 0 hyr
      · rw [Finset.mem_singleton] at hk
        rw [hk]
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hrefl y
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hT y, hcard_pair])).symm
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({0, y} : Finset (Fin 3)))
    (t := Finset.univ) (by rw [hcard_pair]; simp)
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (by simp)
  have hzy : z ≠ y := by rintro rfl; exact hz (by simp)
  have hzT0 : z ∉ T 0 := by rw [hT0]; exact hz
  have hzTy : z ∉ T y := by rw [hTy]; exact hz
  have hzall : ({0, y, z} : Finset (Fin 3)) = Finset.univ := by
    have hcard3 : ({0, y, z} : Finset (Fin 3)).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨0, y, z, Ne.symm hy0, Ne.symm hz0, Ne.symm hzy, rfl⟩
    apply Finset.eq_of_subset_of_card_le
    · intro k _; exact Finset.mem_univ k
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hcard3.ge
  have hsubz : T z ⊆ {z} := by
    intro k hk
    by_contra hkz
    have hkrz : r k z := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    have hkz' : k ≠ z := fun h => hkz (Finset.mem_singleton.mpr h)
    have hk' : k = 0 ∨ k = y := by
      have hkmem : k ∈ ({0, y, z} : Finset (Fin 3)) := by rw [hzall]; exact Finset.mem_univ k
      rcases Finset.mem_insert.mp hkmem with h0 | hkmem
      · exact Or.inl h0
      rcases Finset.mem_insert.mp hkmem with hy' | hz'
      · exact Or.inr hy'
      · exact absurd (Finset.mem_singleton.mp hz') hkz'
    rcases hk' with hk0 | hky
    · rw [hk0] at hkrz
      exact hzT0 (by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hsymm 0 z hkrz)
    · rw [hky] at hkrz
      exact hzTy (by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hsymm y z hkrz)
  have hcardz : (T z).card ≤ 1 := by
    calc (T z).card ≤ ({z} : Finset (Fin 3)).card := Finset.card_le_card hsubz
      _ = 1 := Finset.card_singleton z
  exact absurd hcardz (by rw [hT z]; norm_num)

private theorem s16t3_iso_summands_of_seven {Γ : Type*} [Group Γ] {Q : Type*}
    [CommGroup Q] [MulDistribMulAction Γ Q] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Λ : Subgroup Γ} {S : Fin 3 → Subgroup Q} (hS : ∀ i, XMod.IsIrr ↥Λ (S i))
    (htop : (⨆ i, S i) = ⊤)
    (hlen : ∀ i, IsotypicOfLength ↥Λ (isoComp ↥Λ (S i)) (S i)
      (Nat.card {k : Fin 3 // XMod.Iso ↥Λ (S k) (S i)}))
    (hE : ∀ i, Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod (hS i).1)) = 2)
    (hconst : ∀ i j, Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S i)} =
      Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S j)})
    (h7 : Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} = 7) :
    ∀ i k, XMod.Iso ↥Λ (S k) (S i) := by
  classical
  let c : Fin 3 → ℕ := fun i => Nat.card {k : Fin 3 // XMod.Iso ↥Λ (S k) (S i)}
  let n : Fin 3 → ℕ :=
    fun i => Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S i)}
  have hn : ∀ i, n i = 2 ^ c i - 1 := fun i =>
    s16t3_card_iso_type hQ (hS i) (hlen i) (hE i)
  have hcpos : ∀ i, 1 ≤ c i := by
    intro i
    haveI : Nonempty {k : Fin 3 // XMod.Iso ↥Λ (S k) (S i)} :=
      ⟨⟨i, XMod.Iso.refl (S i)⟩⟩
    show 0 < c i
    exact Finite.card_pos
  have hcle : ∀ i, c i ≤ 3 := by
    intro i
    have h : c i ≤ Nat.card (Fin 3) :=
      Finite.card_subtype_le (fun k : Fin 3 => XMod.Iso ↥Λ (S k) (S i))
    have h3 : Nat.card (Fin 3) = 3 := by simp
    omega
  have hcconst : ∀ i, c i = c 0 := by
    intro i
    have h1 : 2 ^ c i - 1 = 2 ^ c 0 - 1 := by
      rw [← hn i, ← hn 0]
      exact hconst i 0
    have h2 : 1 ≤ 2 ^ c i := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ c 0 := Nat.one_le_two_pow
    have h4 : (2 ^ c i - 1) + 1 = (2 ^ c 0 - 1) + 1 := by rw [h1]
    rw [Nat.sub_add_cancel h2, Nat.sub_add_cancel h3] at h4
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h4
  have hex : ∀ Y : Subgroup Q, XMod.IsIrr ↥Λ Y → ∃ i, XMod.Iso ↥Λ Y (S i) := by
    intro Y hY
    exact CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup (A := ↥Λ) (S := S) hS hY
      (by rw [htop]; exact le_top)
  have hc0 : c 0 = 1 ∨ c 0 = 2 ∨ c 0 = 3 := by
    have h1 := hcpos 0
    have h3 := hcle 0
    omega
  rcases hc0 with h1 | h2 | h3
  · exfalso
    have hci : ∀ i, c i = 1 := fun i => by rw [hcconst i, h1]
    have hni : ∀ i, n i = 1 := by
      intro i
      rw [hn i, hci i]
      norm_num
    have huniq : ∀ i k, XMod.Iso ↥Λ (S k) (S i) → k = i := by
      intro i k hk
      have hcard : Nat.card {k' : Fin 3 // XMod.Iso ↥Λ (S k') (S i)} = 1 := hci i
      haveI : Subsingleton {k' : Fin 3 // XMod.Iso ↥Λ (S k') (S i)} :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      have hEq : (⟨k, hk⟩ : {k' : Fin 3 // XMod.Iso ↥Λ (S k') (S i)}) =
          ⟨i, XMod.Iso.refl (S i)⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val hEq
    have huniqJ : ∀ i J, XMod.IsIrr ↥Λ J → XMod.Iso ↥Λ J (S i) → J = S i := by
      intro i J hJ hJi
      have hcard : Nat.card
          {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' (S i)} = 1 := hni i
      haveI : Subsingleton
          {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' (S i)} :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      have hEq : (⟨J, hJ, hJi⟩ :
            {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' (S i)}) =
          ⟨S i, hS i, XMod.Iso.refl (S i)⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val hEq
    let e : {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} ≃ Fin 3 :=
      { toFun := fun Y => Classical.choose (hex Y.1 Y.2)
        invFun := fun i => ⟨S i, hS i⟩
        left_inv := fun Y => by
          have hspec := Classical.choose_spec (hex Y.1 Y.2)
          exact Subtype.ext
            (huniqJ (Classical.choose (hex Y.1 Y.2)) Y.1 Y.2 hspec).symm
        right_inv := fun i => by
          have hspec := Classical.choose_spec (hex (S i) (hS i))
          exact huniq i (Classical.choose (hex (S i) (hS i)))
            (XMod.Iso.symm (hS i).1 hspec) }
    have h3' : Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} = 3 := by
      rw [Nat.card_congr e]
      simp
    omega
  · exfalso
    have hci : ∀ i, c i = 2 := fun i => by rw [hcconst i, h2]
    exact s16t3_no_class_two_iso (fun i j => XMod.Iso ↥Λ (S i) (S j))
      (fun i => XMod.Iso.refl (S i))
      (fun i j h => XMod.Iso.symm (hS i).1 h)
      (fun i => hci i)
  · have hci : ∀ i, c i = 3 := fun i => by rw [hcconst i, h3]
    have hcard0 : Nat.card {k : Fin 3 // XMod.Iso ↥Λ (S k) (S 0)} = 3 := hci 0
    have hiso0 : ∀ k, XMod.Iso ↥Λ (S k) (S 0) := by
      intro k
      by_contra hk
      have hlt := Finite.card_subtype_lt
        (p := fun k : Fin 3 => XMod.Iso ↥Λ (S k) (S 0)) hk
      have h3' : Nat.card (Fin 3) = 3 := by simp
      omega
    intro i k
    exact (hiso0 k).trans (XMod.Iso.symm (hS i).1 (hiso0 i))

theorem s16t3_iso_all_irr_of_seven (helem : ∀ w : W, w * w = 1)
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (hsum : SumOfNatShape L (⊤ : Subgroup W) (fixV L) 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    (h7 : Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} = 7) :
    ∀ Y Y' : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)),
      XMod.IsIrr ↥L Y → XMod.IsIrr ↥L Y' → XMod.Iso ↥L Y Y' := by
  have hQ : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, pow_two, helem w, QuotientGroup.mk_one]
  obtain ⟨I, hnat, hS, hind, htop⟩ := s16t3_quot_summands hq hsum
  have hS' : ∀ i, XMod.IsIrr ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) (I i)) :=
    fun i => (s16t3_isIrr_top_iff (A := ↥L) _).2 (hS i)
  have htop' : (⨆ i, tilde L (⊤ : Subgroup W) (I i)) = ⊤ := htop
  have hlen' : ∀ i, IsotypicOfLength ↥(⊤ : Subgroup ↥L)
      (isoComp ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) (I i)))
      (tilde L (⊤ : Subgroup W) (I i))
      (Nat.card {k : Fin 3 // XMod.Iso ↥(⊤ : Subgroup ↥L)
        (tilde L (⊤ : Subgroup W) (I k)) (tilde L (⊤ : Subgroup W) (I i))}) :=
    fun i => s16t3_isotypicOfLength_isoComp hS' hind htop' (hS' i)
  have hE' : ∀ i, Nat.card (Module.End ↥(XMod.opRing ↥(⊤ : Subgroup ↥L)
      (W ⧸ modFix L (⊤ : Subgroup W))) ↥(XMod.toSubmod (hS' i).1)) = 2 :=
    fun i => s16t3_card_end_eq_two_of_endUnits (hS' i)
      (s16t3_endUnitsTrivial_tilde hq (hnat i))
  have hconst' : ∀ i j, Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
        XMod.IsIrr ↥(⊤ : Subgroup ↥L) J ∧ XMod.Iso ↥(⊤ : Subgroup ↥L) J
          (tilde L (⊤ : Subgroup W) (I i))} =
      Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
        XMod.IsIrr ↥(⊤ : Subgroup ↥L) J ∧ XMod.Iso ↥(⊤ : Subgroup ↥L) J
          (tilde L (⊤ : Subgroup W) (I j))} := by
    intro i j
    rw [s16t3_card_iso_top (A := ↥L), s16t3_card_iso_top (A := ↥L)]
    exact s16t3_card_iso_eq_of_trans hq htrans (hS i) (hS j)
  have h7' : Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) Y} = 7 := by
    rw [s16t3_card_irr_top (A := ↥L)]
    exact h7
  have hsummands := s16t3_iso_summands_of_seven hQ hS' htop' hlen' hE' hconst' h7'
  intro Y Y' hY hY'
  have hYt : XMod.IsIrr ↥(⊤ : Subgroup ↥L) Y := (s16t3_isIrr_top_iff (A := ↥L) Y).2 hY
  have hYt' : XMod.IsIrr ↥(⊤ : Subgroup ↥L) Y' := (s16t3_isIrr_top_iff (A := ↥L) Y').2 hY'
  obtain ⟨i, hi⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
    (S := fun i => tilde L (⊤ : Subgroup W) (I i)) hS' hYt (by rw [htop']; exact le_top)
  obtain ⟨j, hj⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
    (S := fun i => tilde L (⊤ : Subgroup W) (I i)) hS' hYt' (by rw [htop']; exact le_top)
  have hisoij : XMod.Iso ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) (I i))
      (tilde L (⊤ : Subgroup W) (I j)) :=
    XMod.Iso.symm (hS' j).1 (hsummands i j)
  have hiL : XMod.Iso ↥L Y (tilde L (⊤ : Subgroup W) (I i)) :=
    (s16t3_iso_top_iff (A := ↥L) Y (tilde L (⊤ : Subgroup W) (I i))).1 hi
  have hijL : XMod.Iso ↥L (tilde L (⊤ : Subgroup W) (I i))
      (tilde L (⊤ : Subgroup W) (I j)) :=
    (s16t3_iso_top_iff (A := ↥L) _ _).1 hisoij
  have hjL : XMod.Iso ↥L (tilde L (⊤ : Subgroup W) (I j)) Y' :=
    XMod.Iso.symm hY'.1
      ((s16t3_iso_top_iff (A := ↥L) Y' (tilde L (⊤ : Subgroup W) (I j))).1 hj)
  exact hiL.trans (hijL.trans hjL)

theorem s16t3_exists_mulEquiv_of_tilde_iso (hW : ∀ w : W, w * w = 1)
    {J J' : Subgroup W}
    (hcard : Nat.card ↥(J ⊓ fixV L) = Nat.card ↥(J' ⊓ fixV L))
    (hiso : XMod.Iso ↥L (tilde L (⊤ : Subgroup W) J) (tilde L (⊤ : Subgroup W) J')) :
    ∃ φ : ↥J ≃* ↥J', (∀ u : ↥J, (φ u : W) ∈ fixV L ↔ (u : W) ∈ fixV L) ∧
      ∀ l ∈ L, ∀ u : ↥J, ∀ hu : l (u : W) ∈ J,
        ((φ ⟨l (u : W), hu⟩ : ↥J') : W) * (l ((φ u : ↥J') : W))⁻¹ ∈ fixV L := by
  classical
  obtain ⟨θ, hθ⟩ := hiso
  let fJ : ↥J →* ↥(tilde L (⊤ : Subgroup W) J) :=
    { toFun := fun u => ⟨QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) (u : W),
        Subgroup.mem_map_of_mem _ u.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let fJ' : ↥J' →* ↥(tilde L (⊤ : Subgroup W) J') :=
    { toFun := fun u => ⟨QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) (u : W),
        Subgroup.mem_map_of_mem _ u.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hkerJ : fJ.ker = (J ⊓ fixV L).subgroupOf J := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h
      rw [QuotientGroup.eq_one_iff, CFSG.Quasithin.SmithD391.modFix_top_eq] at h1
      exact ⟨u.2, h1⟩
    · rintro ⟨-, hZ⟩
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, CFSG.Quasithin.SmithD391.modFix_top_eq]
      exact hZ
  have hkerJ' : fJ'.ker = (J' ⊓ fixV L).subgroupOf J' := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h
      rw [QuotientGroup.eq_one_iff, CFSG.Quasithin.SmithD391.modFix_top_eq] at h1
      exact ⟨u.2, h1⟩
    · rintro ⟨-, hZ⟩
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, CFSG.Quasithin.SmithD391.modFix_top_eq]
      exact hZ
  have hsurjJ : Function.Surjective fJ := by
    intro y
    obtain ⟨w, hwJ, hw⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨w, hwJ⟩, Subtype.ext hw⟩
  have hsurjJ' : Function.Surjective fJ' := by
    intro y
    obtain ⟨w, hwJ, hw⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨w, hwJ⟩, Subtype.ext hw⟩
  let eJ : ↥J ⧸ (J ⊓ fixV L).subgroupOf J ≃* ↥(tilde L (⊤ : Subgroup W) J) :=
    (QuotientGroup.quotientMulEquivOfEq hkerJ).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective fJ hsurjJ)
  let eJ' : ↥J' ⧸ (J' ⊓ fixV L).subgroupOf J' ≃* ↥(tilde L (⊤ : Subgroup W) J') :=
    (QuotientGroup.quotientMulEquivOfEq hkerJ').symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective fJ' hsurjJ')
  have heJ : ∀ u : ↥J, eJ (QuotientGroup.mk' ((J ⊓ fixV L).subgroupOf J) u) = fJ u := by
    intro u
    simp only [eJ, MulEquiv.trans_apply]
    have h1 : (QuotientGroup.quotientMulEquivOfEq hkerJ).symm
        (QuotientGroup.mk' ((J ⊓ fixV L).subgroupOf J) u) = QuotientGroup.mk' fJ.ker u := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [h1]
    exact QuotientGroup.kerLift_mk fJ u
  have heJ' : ∀ u : ↥J', eJ' (QuotientGroup.mk' ((J' ⊓ fixV L).subgroupOf J') u) = fJ' u := by
    intro u
    simp only [eJ', MulEquiv.trans_apply]
    have h1 : (QuotientGroup.quotientMulEquivOfEq hkerJ').symm
        (QuotientGroup.mk' ((J' ⊓ fixV L).subgroupOf J') u) = QuotientGroup.mk' fJ'.ker u := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [h1]
    exact QuotientGroup.kerLift_mk fJ' u
  let ψ : ↥J ⧸ (J ⊓ fixV L).subgroupOf J ≃* ↥J' ⧸ (J' ⊓ fixV L).subgroupOf J' :=
    eJ.trans (θ.trans eJ'.symm)
  have hψ : ∀ u : ↥J, eJ' (ψ (QuotientGroup.mk' ((J ⊓ fixV L).subgroupOf J) u)) =
      θ (fJ u) := by
    intro u
    simp only [ψ, MulEquiv.trans_apply, heJ u, MulEquiv.apply_symm_apply]
  have hcard' : Nat.card ↥((J ⊓ fixV L).subgroupOf J) =
      Nat.card ↥((J' ⊓ fixV L).subgroupOf J') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcard
  have hJJ : ∀ j : ↥J, j * j = 1 := fun j => Subtype.ext (hW (j : W))
  have hJJ' : ∀ j : ↥J', j * j = 1 := fun j => Subtype.ext (hW (j : W))
  haveI : ((J ⊓ fixV L).subgroupOf J).Normal := Subgroup.normal_of_isMulCommutative _
  haveI : ((J' ⊓ fixV L).subgroupOf J').Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨φ, hφmem, hφquot⟩ :=
    s16t3_exists_mulEquiv_of_quotientEquiv (Y := (J ⊓ fixV L).subgroupOf J)
      (Y' := (J' ⊓ fixV L).subgroupOf J') hJJ hJJ' hcard' ψ
  refine ⟨φ, ?_, ?_⟩
  · intro u
    have h := hφmem u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf] at h
    exact ⟨fun hf => (h.mp ⟨(φ u).2, hf⟩).2, fun hf => (h.mpr ⟨u.2, hf⟩).2⟩
  · intro l hl u hu
    have hθu : fJ' (φ u) = θ (fJ u) := by
      rw [← heJ' (φ u), hφquot u, hψ u]
    have hθlu : fJ' (φ ⟨l (u : W), hu⟩) = θ (fJ ⟨l (u : W), hu⟩) := by
      rw [← heJ' (φ ⟨l (u : W), hu⟩), hφquot ⟨l (u : W), hu⟩, hψ ⟨l (u : W), hu⟩]
    have hact : (⟨l, hl⟩ : ↥L) • (fJ u : W ⧸ modFix L (⊤ : Subgroup W)) =
        (fJ ⟨l (u : W), hu⟩ : W ⧸ modFix L (⊤ : Subgroup W)) := by
      show (⟨l, hl⟩ : ↥L) • (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) =
        QuotientGroup.mk (l (u : W))
      rw [XMod.smul_quotMk]
      rfl
    have hkey := hθ ⟨l, hl⟩ (fJ u) (fJ ⟨l (u : W), hu⟩) hact
    have hkey' : (⟨l, hl⟩ : ↥L) •
          ((fJ' (φ u) : ↥(tilde L (⊤ : Subgroup W) J')) : W ⧸ modFix L (⊤ : Subgroup W)) =
        ((fJ' (φ ⟨l (u : W), hu⟩) : ↥(tilde L (⊤ : Subgroup W) J')) :
          W ⧸ modFix L (⊤ : Subgroup W)) := by
      rw [hθu, hθlu]
      exact hkey
    have hleft : (⟨l, hl⟩ : ↥L) •
          ((fJ' (φ u) : ↥(tilde L (⊤ : Subgroup W) J')) : W ⧸ modFix L (⊤ : Subgroup W)) =
        QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) (l ((φ u : ↥J') : W)) := by
      show (⟨l, hl⟩ : ↥L) •
          (QuotientGroup.mk ((φ u : ↥J') : W) : W ⧸ modFix L (⊤ : Subgroup W)) = _
      rw [XMod.smul_quotMk]
      rfl
    have hright : ((fJ' (φ ⟨l (u : W), hu⟩) : ↥(tilde L (⊤ : Subgroup W) J')) :
          W ⧸ modFix L (⊤ : Subgroup W)) =
        QuotientGroup.mk' (modFix L (⊤ : Subgroup W))
          ((φ ⟨l (u : W), hu⟩ : ↥J') : W) := rfl
    have hmk : QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) (l ((φ u : ↥J') : W)) =
        QuotientGroup.mk' (modFix L (⊤ : Subgroup W))
          ((φ ⟨l (u : W), hu⟩ : ↥J') : W) := by
      rw [← hleft, hkey', hright]
    have hone : QuotientGroup.mk' (modFix L (⊤ : Subgroup W))
        (((φ ⟨l (u : W), hu⟩ : ↥J') : W) * (l ((φ u : ↥J') : W))⁻¹) = 1 := by
      rw [map_mul, map_inv, hmk, mul_inv_cancel]
    rw [← CFSG.Quasithin.SmithD391.modFix_top_eq L, ← QuotientGroup.eq_one_iff]
    exact hone

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
