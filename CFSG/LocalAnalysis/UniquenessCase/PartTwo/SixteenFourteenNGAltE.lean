module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGAltPair
public import CFSG.GF2Type.Smith1979W3.CaseD.Jordan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Open

variable {n : ℕ}

private theorem s1614_ae_sq_eq_one (v : PermMod n) : v * v = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  show Multiplicative.toAdd v i + Multiplicative.toAdd v i = 0
  exact CharTwo.add_self_eq_zero _

private theorem s1614_ae_pow_two_eq_one (v : PermMod n) : v ^ 2 = 1 := by
  rw [pow_two]
  exact s1614_ae_sq_eq_one v

private theorem s1614_ae_altPair_toAdd_self {i j : Fin n} (hij : i ≠ j) :
    Multiplicative.toAdd (s1614_altPair n i j) i = 1 := by
  simp [s1614_altPair, hij]

private theorem s1614_ae_altPair_toAdd_other {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    Multiplicative.toAdd (s1614_altPair n i j) k = 0 := by
  simp [s1614_altPair, hki, hkj]

private theorem s1614_ae_altPair_ne_one {i j : Fin n} (hij : i ≠ j) :
    s1614_altPair n i j ≠ 1 := by
  intro h
  have h' := congrArg (fun v : PermMod n => Multiplicative.toAdd v i) h
  rw [s1614_ae_altPair_toAdd_self hij] at h'
  have hz : (1 : ZMod 2) = 0 := by simpa using h'
  exact one_ne_zero hz

private theorem s1614_ae_altPair_symm (n : ℕ) (i j : Fin n) :
    s1614_altPair n i j = s1614_altPair n j i := by
  apply Multiplicative.toAdd.injective
  funext k
  simp [s1614_altPair, add_comm]

private theorem s1614_ae_altPair_toAdd_self_right {i j : Fin n} (hij : i ≠ j) :
    Multiplicative.toAdd (s1614_altPair n i j) j = 1 := by
  rw [s1614_ae_altPair_symm n i j]
  exact s1614_ae_altPair_toAdd_self (Ne.symm hij)

private theorem s1614_ae_altPair_ne {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    s1614_altPair n a b ≠ s1614_altPair n a c := by
  intro h
  have h' := congrArg (fun v : PermMod n => Multiplicative.toAdd v b) h
  rw [s1614_ae_altPair_toAdd_self_right hab,
    s1614_ae_altPair_toAdd_other (Ne.symm hab) hbc] at h'
  have hz : (1 : ZMod 2) = 0 := h'
  exact one_ne_zero hz

@[expose] def s1614_altKlein (n : ℕ) (a b c : Fin n) : Subgroup (PermMod n) :=
  Subgroup.closure {s1614_altPair n a b, s1614_altPair n a c}

private theorem s1614_ae_altPair_bc_mem (n : ℕ) (a b c : Fin n) :
    s1614_altPair n b c ∈ s1614_altKlein n a b c := by
  rw [s1614_altKlein]
  have h : (s1614_altPair n a b)⁻¹ * s1614_altPair n a c = s1614_altPair n b c := by
    rw [← s1614_altPair_mul (n := n) a b c]
    exact inv_mul_cancel_left _ _
  rw [← h]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))

private theorem s1614_ae_zpow_eq_one_or_self {G : Type*} [Group G] [Finite G]
    [DecidableEq G] {v z : G} (hv : v ^ 2 = 1) (hz : z ∈ Subgroup.zpowers v) :
    z = 1 ∨ z = v := by
  by_cases h1 : v = 1
  · left
    rw [h1] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← hk]; simp
  · have ho : orderOf v = 2 := orderOf_eq_prime (p := 2) hv h1
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, hiz⟩ := hz
    interval_cases i
    · left; rw [← hiz]; simp
    · right; rw [← hiz]; simp

private theorem s1614_ae_zpowers_inf_eq_bot {G : Type*} [Group G] [Finite G]
    [DecidableEq G] {x y : G}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : x ≠ y) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hzx, hzy⟩ := Subgroup.mem_inf.1 hz
  obtain h1 | h1 := s1614_ae_zpow_eq_one_or_self hx hzx
  · exact h1
  · obtain h2 | h2 := s1614_ae_zpow_eq_one_or_self hy hzy
    · exact h2
    · exact absurd (h1.symm.trans h2) hxy

theorem s1614_altKlein_card {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Nat.card ↥(s1614_altKlein n a b c) = 4 := by
  let U : Subgroup (PermMod n) := Subgroup.zpowers (s1614_altPair n a b)
  let W : Subgroup (PermMod n) := Subgroup.zpowers (s1614_altPair n a c)
  have hK : s1614_altKlein n a b c = U ⊔ W := by
    rw [s1614_altKlein]
    rw [show ({s1614_altPair n a b, s1614_altPair n a c} : Set (PermMod n)) =
        {s1614_altPair n a b} ∪ {s1614_altPair n a c} by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  have hx1 : s1614_altPair n a b ≠ 1 := s1614_ae_altPair_ne_one hab
  have hy1 : s1614_altPair n a c ≠ 1 := s1614_ae_altPair_ne_one hac
  have hxy : s1614_altPair n a b ≠ s1614_altPair n a c := s1614_ae_altPair_ne hab hbc
  have hx2 : (s1614_altPair n a b) ^ 2 = 1 := s1614_ae_pow_two_eq_one _
  have hy2 : (s1614_altPair n a c) ^ 2 = 1 := s1614_ae_pow_two_eq_one _
  have hxcard : Nat.card ↥U = 2 := by
    change Nat.card ↥(Subgroup.zpowers (s1614_altPair n a b)) = 2
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) hx2 hx1]
  have hycard : Nat.card ↥W = 2 := by
    change Nat.card ↥(Subgroup.zpowers (s1614_altPair n a c)) = 2
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) hy2 hy1]
  have hinf_eq : U ⊓ W = ⊥ := by
    change Subgroup.zpowers (s1614_altPair n a b) ⊓
      Subgroup.zpowers (s1614_altPair n a c) = ⊥
    exact s1614_ae_zpowers_inf_eq_bot hx2 hy2 hxy
  have hinfcard : Nat.card ↥(U ⊓ W) = 1 := by
    have hc := congrArg (fun H : Subgroup (PermMod n) => Nat.card ↥H) hinf_eq
    simpa [Subgroup.card_bot] using hc
  have hmain := card_sup_mul_card_inf U W
  have hcard : Nat.card ↥(U ⊔ W) = 4 := by
    calc Nat.card ↥(U ⊔ W) = Nat.card ↥(U ⊔ W) * 1 := (mul_one _).symm
      _ = Nat.card ↥(U ⊔ W) * Nat.card ↥(U ⊓ W) := by rw [hinfcard]
      _ = Nat.card ↥U * Nat.card ↥W := hmain
      _ = 2 * 2 := by rw [hxcard, hycard]
      _ = 4 := by norm_num
  rw [hK]
  exact hcard

theorem s1614_altKlein_inf_ker (hn : 6 ≤ n) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    s1614_altKlein n a b c ⊓ (Subgroup.zpowers (allOnes n) ⊓ coreMod n) = ⊥ := by
  have hlt : ({a, b, c} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_three (by omega)
  obtain ⟨d, -, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hda : d ≠ a := fun h => hdnot (by rw [h]; simp)
  have hdb : d ≠ b := fun h => hdnot (by rw [h]; simp)
  have hdc : d ≠ c := fun h => hdnot (by rw [h]; simp)
  let S : Subgroup (PermMod n) :=
    { carrier := {v | Multiplicative.toAdd v d = 0}
      one_mem' := by simp
      mul_mem' := by
        intro v w hv hw
        have hv' : Multiplicative.toAdd v d = 0 := hv
        have hw' : Multiplicative.toAdd w d = 0 := hw
        show Multiplicative.toAdd v d + Multiplicative.toAdd w d = 0
        rw [hv', hw', add_zero]
      inv_mem' := by
        intro v hv
        have hv' : Multiplicative.toAdd v d = 0 := hv
        have hinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (s1614_ae_sq_eq_one v)
        show Multiplicative.toAdd v⁻¹ d = 0
        rw [hinv]
        exact hv' }
  have hxS : Multiplicative.toAdd (s1614_altPair n a b) d = 0 :=
    s1614_ae_altPair_toAdd_other hda hdb
  have hyS : Multiplicative.toAdd (s1614_altPair n a c) d = 0 :=
    s1614_ae_altPair_toAdd_other hda hdc
  have hallOnesS : allOnes n ∉ S := by
    intro h
    change Multiplicative.toAdd (allOnes n) d = 0 at h
    have h1 : Multiplicative.toAdd (allOnes n) d = 1 := by simp [allOnes]
    rw [h1] at h
    exact one_ne_zero h
  have hKle : s1614_altKlein n a b c ≤ S := by
    rw [s1614_altKlein, Subgroup.closure_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hxS
    · exact hyS
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hzK, hzZc⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨hzZ, _⟩ := Subgroup.mem_inf.1 hzZc
  obtain h | h := s1614_ae_zpow_eq_one_or_self (s1614_ae_pow_two_eq_one (allOnes n)) hzZ
  · exact h
  · exfalso
    exact hallOnesS (hKle (h ▸ hzK))

theorem s1614_alt_exists_E (hn : 6 ≤ n) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∃ E : Subgroup ↥(alternatingGroup (Fin n)), IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, ∀ x ∈ s1614_altKlein n a b c,
        permAct n (e : Equiv.Perm (Fin n)) x ∈ s1614_altKlein n a b c := by
  have hlt3 : ({a, b, c} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_three (by omega)
  obtain ⟨d, -, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt3
  have hlt4 : ({a, b, c, d} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨e, -, henot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt4
  have hlt5 : ({a, b, c, d, e} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_five (by omega)
  obtain ⟨f, -, hfnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt5
  have hda : d ≠ a := fun h => hdnot (by rw [h]; simp)
  have hdb : d ≠ b := fun h => hdnot (by rw [h]; simp)
  have hdc : d ≠ c := fun h => hdnot (by rw [h]; simp)
  have hea : e ≠ a := fun h => henot (by rw [h]; simp)
  have heb : e ≠ b := fun h => henot (by rw [h]; simp)
  have hec : e ≠ c := fun h => henot (by rw [h]; simp)
  have hed : e ≠ d := fun h => henot (by rw [h]; simp)
  have hfa : f ≠ a := fun h => hfnot (by rw [h]; simp)
  have hfb : f ≠ b := fun h => hfnot (by rw [h]; simp)
  have hfc : f ≠ c := fun h => hfnot (by rw [h]; simp)
  have hfd : f ≠ d := fun h => hfnot (by rw [h]; simp)
  have hfe : f ≠ e := fun h => hfnot (by rw [h]; simp)
  have had : a ≠ d := hda.symm
  have hae : a ≠ e := hea.symm
  have haf : a ≠ f := hfa.symm
  have hbd : b ≠ d := hdb.symm
  have hbe : b ≠ e := heb.symm
  have hbf : b ≠ f := hfb.symm
  have hcd : c ≠ d := hdc.symm
  have hce : c ≠ e := hec.symm
  have hcf : c ≠ f := hfc.symm
  have hde : d ≠ e := hed.symm
  have hdf : d ≠ f := hfd.symm
  have hef : e ≠ f := hfe.symm
  let σ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c
  let τ : Equiv.Perm (Fin n) := Equiv.swap d e * Equiv.swap d f
  have hσ3 : σ.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hτ3 : τ.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hde hdf hef
  have hσ3pow : σ ^ 3 = 1 := by
    simpa [hσ3.orderOf] using pow_orderOf_eq_one σ
  have hτ3pow : τ ^ 3 = 1 := by
    simpa [hτ3.orderOf] using pow_orderOf_eq_one τ
  have hσa : σ a = c := by
    change Equiv.swap a b (Equiv.swap a c a) = c
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)
  have hσb : σ b = a := by
    change Equiv.swap a b (Equiv.swap a c b) = a
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc]
    exact Equiv.swap_apply_right a b
  have hσc : σ c = b := by
    change Equiv.swap a b (Equiv.swap a c c) = b
    rw [Equiv.swap_apply_right]
    exact Equiv.swap_apply_left a b
  have hτa : τ a = a := by
    change Equiv.swap d e (Equiv.swap d f a) = a
    rw [Equiv.swap_apply_of_ne_of_ne had haf]
    exact Equiv.swap_apply_of_ne_of_ne had hae
  have hτb : τ b = b := by
    change Equiv.swap d e (Equiv.swap d f b) = b
    rw [Equiv.swap_apply_of_ne_of_ne hbd hbf]
    exact Equiv.swap_apply_of_ne_of_ne hbd hbe
  have hτc : τ c = c := by
    change Equiv.swap d e (Equiv.swap d f c) = c
    rw [Equiv.swap_apply_of_ne_of_ne hcd hcf]
    exact Equiv.swap_apply_of_ne_of_ne hcd hce
  have hdisj : σ.Disjoint τ := by
    intro x
    by_cases hx : x = a ∨ x = b ∨ x = c
    · right
      rcases hx with rfl | rfl | rfl
      · exact hτa
      · exact hτb
      · exact hτc
    · left
      simp only [not_or] at hx
      obtain ⟨hxa, hxb, hxc⟩ := hx
      change Equiv.swap a b (Equiv.swap a c x) = x
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxc]
      exact Equiv.swap_apply_of_ne_of_ne hxa hxb
  have hσA : σ ∈ alternatingGroup (Fin n) := hσ3.mem_alternatingGroup
  have hτA : τ ∈ alternatingGroup (Fin n) := hτ3.mem_alternatingGroup
  let E : Subgroup ↥(alternatingGroup (Fin n)) :=
    Subgroup.closure ({⟨σ, hσA⟩, ⟨τ, hτA⟩} : Set ↥(alternatingGroup (Fin n)))
  have hmap : E.map (alternatingGroup (Fin n)).subtype =
      Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin n))) := by
    change (Subgroup.closure
        ({⟨σ, hσA⟩, ⟨τ, hτA⟩} : Set ↥(alternatingGroup (Fin n)))).map
          (alternatingGroup (Fin n)).subtype = _
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨z, hz, hzg⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · left; exact hzg.symm
      · right; exact hzg.symm
    · rintro (rfl | rfl)
      · exact ⟨⟨σ, hσA⟩, by simp, rfl⟩
      · exact ⟨⟨τ, hτA⟩, by simp, rfl⟩
  have hEcard : Nat.card ↥E = 9 := by
    have h1 := Subgroup.card_map_of_injective (K := E)
      (f := (alternatingGroup (Fin n)).subtype)
      (alternatingGroup (Fin n)).subtype_injective
    have h9 : Nat.card ↥(Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin n)))) = 9 :=
      CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles hσ3 hτ3 hdisj
    rw [hmap] at h1
    rw [h9] at h1
    exact h1.symm
  have hEdef : E =
      Subgroup.closure ({⟨σ, hσA⟩, ⟨τ, hτA⟩} : Set ↥(alternatingGroup (Fin n))) := rfl
  have hEcomm : IsMulCommutative E := by
    rw [hEdef]
    apply Subgroup.isMulCommutative_closure
    intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · rw [commute_iff_eq]; apply Subtype.ext; exact hdisj.commute.eq
    · rw [commute_iff_eq]; apply Subtype.ext; exact hdisj.commute.eq.symm
    · exact absurd rfl huv
  have hEpow : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    rw [hEdef] at hx
    refine Subgroup.closure_induction
      (p := fun z _ => z ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · apply Subtype.ext; simpa using hσ3pow
      · apply Subtype.ext; simpa using hτ3pow
    · simp
    · intro p q hp hq ihp ihq
      have hc : Commute p q := by
        rw [commute_iff_eq]
        simpa using congrArg Subtype.val (hEcomm.is_comm.comm (⟨p, hp⟩ : E) (⟨q, hq⟩ : E))
      rw [hc.mul_pow 3, ihp, ihq, one_mul]
    · intro p hp ihp
      rw [inv_pow, ihp, inv_one]
  have hEab : IsElemAbelian 3 E := ⟨hEcomm, hEpow⟩
  let Stab : Submonoid (Equiv.Perm (Fin n)) :=
    { carrier := {g | ∀ x ∈ s1614_altKlein n a b c,
        permAct n g x ∈ s1614_altKlein n a b c}
      one_mem' := by intro x hx; simpa using hx
      mul_mem' := by
        intro g h hg hh x hx
        rw [map_mul]
        show permAct n g (permAct n h x) ∈ s1614_altKlein n a b c
        exact hg _ (hh x hx) }
  have hσStab : σ ∈ Stab := by
    intro x hx
    have hle : s1614_altKlein n a b c ≤
        (s1614_altKlein n a b c).comap (permAct n σ).toMonoidHom := by
      rw [s1614_altKlein, Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · change permAct n σ (s1614_altPair n a b) ∈
          Subgroup.closure ({s1614_altPair n a b, s1614_altPair n a c} : Set (PermMod n))
        rw [s1614_permAct_altPair, hσa, hσb]
        rw [s1614_ae_altPair_symm n c a]
        exact Subgroup.subset_closure (by simp)
      · change permAct n σ (s1614_altPair n a c) ∈
          Subgroup.closure ({s1614_altPair n a b, s1614_altPair n a c} : Set (PermMod n))
        rw [s1614_permAct_altPair, hσa, hσc]
        rw [s1614_ae_altPair_symm n c b]
        exact s1614_ae_altPair_bc_mem n a b c
    exact hle hx
  have hτStab : τ ∈ Stab := by
    intro x hx
    have hle : s1614_altKlein n a b c ≤
        (s1614_altKlein n a b c).comap (permAct n τ).toMonoidHom := by
      rw [s1614_altKlein, Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · change permAct n τ (s1614_altPair n a b) ∈
          Subgroup.closure ({s1614_altPair n a b, s1614_altPair n a c} : Set (PermMod n))
        rw [s1614_permAct_altPair, hτa, hτb]
        exact Subgroup.subset_closure (by simp)
      · change permAct n τ (s1614_altPair n a c) ∈
          Subgroup.closure ({s1614_altPair n a b, s1614_altPair n a c} : Set (PermMod n))
        rw [s1614_permAct_altPair, hτa, hτc]
        exact Subgroup.subset_closure (by simp)
    exact hle hx
  have hStab_le : Submonoid.closure ({σ, τ} : Set (Equiv.Perm (Fin n))) ≤ Stab := by
    rw [Submonoid.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hσStab
    · exact hτStab
  refine ⟨E, hEab, ?_, ?_⟩
  · omega
  · intro e he x hx
    have heJ : (e : Equiv.Perm (Fin n)) ∈
        Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin n))) := by
      rw [← hmap]
      exact ⟨e, he, rfl⟩
    have hsub : (e : Equiv.Perm (Fin n)) ∈
        (Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin n)))).toSubmonoid := heJ
    rw [Subgroup.closure_toSubmonoid_of_finite] at hsub
    exact hStab_le hsub x hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
