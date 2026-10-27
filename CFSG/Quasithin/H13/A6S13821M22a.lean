module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions
public import CFSG.Quasithin.H13.L32AC47e

public section

namespace CFSG.Quasithin.H13.A6.HatM22

open CFSG.ComponentClassification.WittDesign MulAction
open scoped Pointwise

@[expose] def hexadSet : SubMulAction M22 (Finset (Fin 22)) where
  carrier := (hexads : Set (Finset (Fin 22)))
  smul_mem' g _ hB := smul_mem_hexads g hB

theorem exists_hexad_le_stabilizer {S : Subgroup M22}
    (hS : IsPGroup 2 S) : ∃ B ∈ hexads, S ≤ stabilizer M22 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card hexadSet = 77 := by
    rw [← card_hexads]
    exact Nat.card_eq_finsetCard hexads
  obtain ⟨B, hB⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card hexadSet
    (by rw [hcard]; norm_num)
  refine ⟨B.1, B.2, fun s hs => ?_⟩
  rw [mem_stabilizer_iff]
  exact congrArg Subtype.val (hB ⟨s, hs⟩)

theorem not_dvd_card_inf_stabilizer
    {B B' : Finset (Fin 22)}
    (hB : B ∈ hexads) (hB' : B' ∈ hexads) (hne : B ≠ B') :
    ¬ 128 ∣ Nat.card ↥(stabilizer M22 B ⊓ stabilizer M22 B') := by
  set A := stabilizer M22 B with hA
  have horb : orbit A B' =
      ((hexads.filter fun C => (B ∩ C).card = (B ∩ B').card : Finset _) :
        Set (Finset (Fin 22))) := by
    ext C
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩
      have hC : (g : M22) • B' ∈ hexads := smul_mem_hexads _ hB'
      refine ⟨hC, ?_⟩
      exact ((exists_stabilizer_smul_hexad_eq_iff hB hB' hC).1 ⟨g, rfl⟩).symm
    · rintro ⟨hC, hcard⟩
      obtain ⟨g, hg⟩ := (exists_stabilizer_smul_hexad_eq_iff hB hB' hC).2 hcard.symm
      exact ⟨g, hg⟩
  have hcardO : Nat.card (orbit A B') = 16 ∨ Nat.card (orbit A B') = 60 := by
    rw [horb, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    obtain ⟨h16, h60⟩ := hexads_intersections hB
    rcases isSteinerTriple_hexads.card_inter hB hB' hne with h0 | h2
    · left
      have e : (hexads.filter fun C => (B ∩ C).card = 0) = hexads.filter fun C => Disjoint B C :=
        Finset.filter_congr fun C _ => by
          rw [Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]
      rw [← h16, h0, e]
    · right
      rw [← h60, h2]
  have hos := natCard_orbit_mul_card_stabilizer A B'
  rw [card_stabilizer_hexad hB] at hos
  have hst : Nat.card (stabilizer A B') = Nat.card ↥(A ⊓ stabilizer M22 B') := by
    have e : stabilizer A B' = (stabilizer M22 B').subgroupOf A := by
      ext g
      rfl
    rw [e, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hst] at hos
  intro h128
  obtain ⟨m, hm⟩ := h128
  rw [hm] at hos
  rcases hcardO with h | h <;> rw [h] at hos <;> omega

theorem eq_of_le_stabilizer
    {S : Subgroup M22}
    (hS : Nat.card S = 128) {B B' : Finset (Fin 22)} (hB : B ∈ hexads) (hB' : B' ∈ hexads)
    (hSB : S ≤ stabilizer M22 B) (hSB' : S ≤ stabilizer M22 B') : B = B' := by
  by_contra hne
  apply not_dvd_card_inf_stabilizer hB hB' hne
  rw [← hS]
  exact Subgroup.card_dvd_of_le (le_inf hSB hSB')

theorem map_stabilizer_eq
    {S : Subgroup M22} (hS : Nat.card S = 128)
    {B : Finset (Fin 22)} (hB : B ∈ hexads) (hSB : S ≤ stabilizer M22 B) (α : M22 ≃* M22)
    (hα : S.map α.toMonoidHom = S) :
    (stabilizer M22 B).map α.toMonoidHom = stabilizer M22 B := by
  have hidx : ((stabilizer M22 B).map α.toMonoidHom).index = 77 := by
    have e : (stabilizer M22 B).map α.toMonoidHom = (stabilizer M22 B).map (α : M22 →* M22) :=
      rfl
    rw [e, Subgroup.index_map_equiv]
    exact index_stabilizer_hexad hB
  obtain ⟨B'', hB'', heq⟩ := eq_stabilizer_hexad_of_index_77 _ hidx
  have hSB'' : S ≤ stabilizer M22 B'' := by
    rw [← heq, ← hα]
    exact Subgroup.map_mono hSB
  rw [heq, eq_of_le_stabilizer hS hB hB'' hSB hSB'']

theorem not_comm_of_card_eight {X : Subgroup (alternatingGroup (Fin 6))} (hX : Nat.card X = 8) :
    ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : IsPGroup 2 L32A.C.Alt6.D0 :=
    IsPGroup.of_card (n := 3) (by rw [L32A.C.Alt6.card_D0]; rfl)
  have hX2 : IsPGroup 2 X := IsPGroup.of_card (n := 3) (by rw [hX]; rfl)
  have hidx : ∀ Y : Subgroup (alternatingGroup (Fin 6)), Nat.card Y = 8 → ¬ 2 ∣ Y.index := by
    intro Y hY
    have := Y.card_mul_index
    rw [hY, L32A.C.Alt6.card_A6] at this
    rintro ⟨m, hm⟩
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6))
    (hX2.toSylow (hidx X hX)) (hD.toSylow (hidx _ L32A.C.Alt6.card_D0))
  have hmem : ∀ d ∈ L32A.C.Alt6.D0, g⁻¹ * d * g ∈ X := by
    intro d hd
    have h1 : d ∈ ((hD.toSylow (hidx _ L32A.C.Alt6.card_D0) : Sylow 2 _) : Subgroup _) := hd
    rw [← hg] at h1
    simp only [Sylow.smul_def] at h1
    change d ∈ (MulAut.conj g • ((hX2.toSylow (hidx X hX) : Sylow 2 _) :
      Subgroup (alternatingGroup (Fin 6)))) at h1
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
  have hzd : (L32A.C.Alt6.aA * L32A.C.Alt6.toA6 L32A.C.Alt6.d6
      (L32A.C.Alt6.d0_sign _ (by simp [L32A.C.Alt6.d0List])) : alternatingGroup (Fin 6)) ≠
      L32A.C.Alt6.toA6 L32A.C.Alt6.d6 (L32A.C.Alt6.d0_sign _ (by simp [L32A.C.Alt6.d0List])) *
        L32A.C.Alt6.aA := by
    intro h
    have := congrArg Subtype.val h
    revert this
    decide +kernel
  apply hzd
  have hz := hmem _ (show L32A.C.Alt6.aA ∈ L32A.C.Alt6.D0 by
    show L32A.C.Alt6.a6 ∈ L32A.C.Alt6.d0List
    simp [L32A.C.Alt6.d0List])
  have hd := hmem (L32A.C.Alt6.toA6 L32A.C.Alt6.d6
    (L32A.C.Alt6.d0_sign _ (by simp [L32A.C.Alt6.d0List]))) (by
      show L32A.C.Alt6.d6 ∈ L32A.C.Alt6.d0List
      simp [L32A.C.Alt6.d0List])
  have h := hcomm _ hz _ hd
  have e : ∀ a b : alternatingGroup (Fin 6),
      (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) → a * b = b * a := by
    intro a b hab
    have := congrArg (fun x => g * x * g⁻¹) hab
    simpa [mul_assoc] using this
  exact e _ _ h

theorem kernelSubgroup_le
    {S : Subgroup M22}
    (hS : Nat.card S = 128) {B : Finset (Fin 22)} (hB : B ∈ hexads)
    (hSB : S ≤ stabilizer M22 B) : kernelSubgroup B ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : S ≤ Subgroup.normalizer (kernelSubgroup B : Set M22) := by
    intro s hs
    have hsB : s • B = B := mem_stabilizer_iff.mp (hSB hs)
    rw [Subgroup.mem_normalizer_iff]
    intro e
    conv_rhs => rw [← hsB]
    rw [mem_kernelSubgroup_smul, show s⁻¹ * (s * e * s⁻¹) * s = e by group]
  have hE2 : IsPGroup 2 (kernelSubgroup B) :=
    IsPGroup.of_card (n := 4) (by rw [card_kernelSubgroup hB]; rfl)
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [hS]; rfl)
  have hP := hE2.to_sup_of_normal_left' hS2 hEN
  have hle : kernelSubgroup B ⊔ S ≤ stabilizer M22 B := sup_le (kernelSubgroup_le_stabilizer B) hSB
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 2 ^ k ∣ 5760 := by
    rw [← hk, ← card_stabilizer_hexad hB]
    exact Subgroup.card_dvd_of_le hle
  have hk7 : k ≤ 7 := by
    by_contra h
    have h8 : 2 ^ 8 ∣ 5760 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right : S ≤ kernelSubgroup B ⊔ S) (by
    rw [hk, hS]
    calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
      _ = 128 := by norm_num)
  rw [heq]
  exact le_sup_left

theorem apply_comm_of_orbit {S : Subgroup M22} {x : Fin 22}
    (key : ∀ u ∈ S, ∀ v ∈ S, (u : Equiv.Perm (Fin 22)) x = x ∨ (v : Equiv.Perm (Fin 22)) x = x ∨
      (u : Equiv.Perm (Fin 22)) x = (v : Equiv.Perm (Fin 22)) x)
    {s t : M22} (hs : s ∈ S) (ht : t ∈ S) :
    (s : Equiv.Perm (Fin 22)) ((t : Equiv.Perm (Fin 22)) x) =
      (t : Equiv.Perm (Fin 22)) ((s : Equiv.Perm (Fin 22)) x) := by
  have hmul : ∀ (a b : M22) (y : Fin 22), ((a * b : M22) : Equiv.Perm (Fin 22)) y =
      (a : Equiv.Perm (Fin 22)) ((b : Equiv.Perm (Fin 22)) y) := fun _ _ _ => rfl
  by_cases h1 : (s : Equiv.Perm (Fin 22)) x = x
  · by_cases h2 : (t : Equiv.Perm (Fin 22)) x = x
    · rw [h2, h1, h2]
    · rcases key _ (S.mul_mem hs ht) _ ht with h | h | h
      · rw [hmul] at h
        exact absurd ((s : Equiv.Perm (Fin 22)).injective (h.trans h1.symm)) h2
      · exact absurd h h2
      · rw [hmul] at h
        rw [h, h1]
  · by_cases h2 : (t : Equiv.Perm (Fin 22)) x = x
    · rcases key _ (S.mul_mem ht hs) _ hs with h | h | h
      · rw [hmul] at h
        exact absurd ((t : Equiv.Perm (Fin 22)).injective (h.trans h2.symm)) h1
      · exact absurd h h1
      · rw [hmul] at h
        rw [h2, h]
    · have h12 : (s : Equiv.Perm (Fin 22)) x = (t : Equiv.Perm (Fin 22)) x := by
        rcases key _ hs _ ht with h | h | h
        · exact absurd h h1
        · exact absurd h h2
        · exact h
      have hss : (s : Equiv.Perm (Fin 22)) ((s : Equiv.Perm (Fin 22)) x) = x := by
        rcases key _ (S.mul_mem hs hs) _ hs with h | h | h
        · rwa [hmul] at h
        · exact absurd h h1
        · rw [hmul] at h
          exact absurd ((s : Equiv.Perm (Fin 22)).injective h) h1
      have htt : (t : Equiv.Perm (Fin 22)) ((t : Equiv.Perm (Fin 22)) x) = x := by
        rcases key _ (S.mul_mem ht ht) _ ht with h | h | h
        · rwa [hmul] at h
        · exact absurd h h2
        · rw [hmul] at h
          exact absurd ((t : Equiv.Perm (Fin 22)).injective h) h2
      rw [← h12, hss, h12, htt]

theorem exists_three_mem_orbit
    {S : Subgroup M22}
    (hS : Nat.card S = 128) {B : Finset (Fin 22)} (hB : B ∈ hexads)
    (hSB : S ≤ stabilizer M22 B) :
    ∃ x ∈ B, ∃ s ∈ S, ∃ t ∈ S, (s : Equiv.Perm (Fin 22)) x ≠ x ∧
      (t : Equiv.Perm (Fin 22)) x ≠ x ∧
      (s : Equiv.Perm (Fin 22)) x ≠ (t : Equiv.Perm (Fin 22)) x := by
  classical
  by_contra hno
  push Not at hno
  have hE := kernelSubgroup_le hS hB hSB
  set A := stabilizer M22 B with hA
  set S' : Subgroup A := S.subgroupOf A with hS'
  set f := resHexad B with hf
  have hcomm : ∀ a ∈ S'.map f, ∀ b ∈ S'.map f, a * b = b * a := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    refine Equiv.ext fun y => Subtype.ext ?_
    have hsS : (s : M22) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have htS : (t : M22) ∈ S := Subgroup.mem_subgroupOf.mp ht
    have key : ∀ u ∈ S, ∀ v ∈ S, (u : Equiv.Perm (Fin 22)) y = y ∨
        (v : Equiv.Perm (Fin 22)) y = y ∨
        (u : Equiv.Perm (Fin 22)) y = (v : Equiv.Perm (Fin 22)) y := by
      intro u hu v hv
      by_contra h
      push Not at h
      exact h.2.2 (hno y y.2 u hu v hv h.1 h.2.1)
    exact apply_comm_of_orbit key hsS htS
  have hker : f.ker ≤ S' := fun g hg =>
    Subgroup.mem_subgroupOf.mpr (hE (mem_ker_resHexad.mp hg))
  have hcardS' : Nat.card S' = 128 := by
    rw [hS', ← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
  have hcard8 : Nat.card (S'.map f) = 8 := by
    rw [← Subgroup.relIndex_ker]
    have h1 := Subgroup.relIndex_mul_card f.ker S'
    rw [inf_eq_left.mpr hker, card_ker_resHexad hB, hcardS'] at h1
    omega
  have hAlt : S'.map f ≤ alternatingGroup B := by
    rw [← range_resHexad hB]
    exact Subgroup.map_le_range f S'
  obtain ⟨e⟩ : Nonempty (B ≃ Fin 6) := ⟨Fintype.equivFinOfCardEq (card_hexad_type hB)⟩
  set ε := Equiv.altCongrHom e with hε
  set X : Subgroup (alternatingGroup (Fin 6)) :=
    ((S'.map f).subgroupOf (alternatingGroup B)).map ε.toMonoidHom with hX
  have hX8 : Nat.card X = 8 := by
    rw [hX, Subgroup.card_map_of_injective ε.injective, ← hcard8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAlt).toEquiv
  apply not_comm_of_card_eight hX8
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))

theorem le_stabilizer_of_isTwoThree
    {S P : Subgroup M22}
    (hS : Nat.card S = 128) {B : Finset (Fin 22)} (hB : B ∈ hexads)
    (hSB : S ≤ stabilizer M22 B) (hSP : S ≤ P)
    (hP : ∀ p : ℕ, p.Prime → p ∣ Nat.card P → p = 2 ∨ p = 3) : P ≤ stabilizer M22 B := by
  classical
  have hE := kernelSubgroup_le hS hB hSB
  obtain ⟨x, hxB, s, hs, t, ht, hsx, htx, hst⟩ := exists_three_mem_orbit hS hB hSB
  have horb : ∀ p ∈ P, (p : Equiv.Perm (Fin 22)) x ∈ B := by
    intro p hp
    by_contra hy
    set O := orbit P x with hO
    have hsub : ((Finset.univ.filter fun z => z ∉ B) ∪
        {x, (s : Equiv.Perm (Fin 22)) x, (t : Equiv.Perm (Fin 22)) x} : Finset (Fin 22)) ⊆
          O.toFinset := by
      intro z hz
      rw [Set.mem_toFinset]
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨e, ⟨he, hez⟩, -⟩ :=
          kernelSubgroup_regular hB hy (Finset.mem_filter.mp hz).2
        refine ⟨⟨e * p, P.mul_mem (hSP (hE he)) hp⟩, ?_⟩
        show ((e * p : M22) : Equiv.Perm (Fin 22)) x = z
        exact hez
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact mem_orbit_self _
        · exact ⟨⟨s, hSP hs⟩, rfl⟩
        · exact ⟨⟨t, hSP ht⟩, rfl⟩
    have hcard16 : (Finset.univ.filter fun z => z ∉ B).card = 16 := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.filter_mem_eq_inter, Finset.univ_inter, card_of_mem_hexads hB]
      rfl
    have hcard3 : ({x, (s : Equiv.Perm (Fin 22)) x, (t : Equiv.Perm (Fin 22)) x} :
        Finset (Fin 22)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hsx, Ne.symm htx]),
        Finset.card_pair hst]
    have hdisj : Disjoint (Finset.univ.filter fun z => z ∉ B)
        {x, (s : Equiv.Perm (Fin 22)) x, (t : Equiv.Perm (Fin 22)) x} := by
      rw [Finset.disjoint_right]
      intro z hz hz'
      have hzB : z ∈ B := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hxB
        · exact (mem_stabilizer_finset_iff.mp (hSB hs)) _ hxB
        · exact (mem_stabilizer_finset_iff.mp (hSB ht)) _ hxB
      exact (Finset.mem_filter.mp hz').2 hzB
    have h19 : 19 ≤ Nat.card O := by
      rw [Nat.card_eq_card_toFinset]
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hcard16, hcard3] at this
      exact this
    have h22 : Nat.card O ≤ 22 := by
      rw [Nat.card_eq_card_toFinset]
      exact (Finset.card_le_univ _).trans (by simp)
    have hdvd : Nat.card O ∣ Nat.card P := by
      rw [← natCard_orbit_mul_card_stabilizer P x]
      exact Dvd.intro _ rfl
    have hbad : ∀ n : ℕ, 19 ≤ n → n ≤ 22 → ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ q ≠ 2 ∧ q ≠ 3 := by
      intro n h1 h2
      interval_cases n
      · exact ⟨19, by norm_num, dvd_refl _, by norm_num, by norm_num⟩
      · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    obtain ⟨q, hq, hqn, hq2, hq3⟩ := hbad _ h19 h22
    rcases hP q hq (hqn.trans hdvd) with h | h
    · exact hq2 h
    · exact hq3 h
  intro p hp
  set σ : Equiv.Perm (Fin 22) := (p : Equiv.Perm (Fin 22)) with hσ
  set u : Fin 22 := (s : Equiv.Perm (Fin 22)) x with hu
  set v : Fin 22 := (t : Equiv.Perm (Fin 22)) x with hv
  have huB : u ∈ B := (mem_stabilizer_finset_iff.mp (hSB hs)) _ hxB
  have hvB : v ∈ B := (mem_stabilizer_finset_iff.mp (hSB ht)) _ hxB
  have hpB : σ • B ∈ hexads := smul_mem_hexads p hB
  have hT : ({σ x, σ u, σ v} : Finset (Fin 22)).card = 3 := by
    have hinj := σ.injective
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hsx (hinj h).symm, fun h => htx (hinj h).symm⟩),
      Finset.card_pair (fun h => hst (hinj h))]
  obtain ⟨D, -, hD⟩ := isSteinerTriple_hexads.2.2 _ hT
  have hsubB : ({σ x, σ u, σ v} : Finset (Fin 22)) ⊆ B := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact horb p hp
    · exact horb (p * s) (P.mul_mem hp (hSP hs))
    · exact horb (p * t) (P.mul_mem hp (hSP ht))
  have hsubpB : ({σ x, σ u, σ v} : Finset (Fin 22)) ⊆ σ • B := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.smul_mem_smul_finset hxB
    · exact Finset.smul_mem_smul_finset huB
    · exact Finset.smul_mem_smul_finset hvB
  rw [mem_stabilizer_iff, Subgroup.smul_def]
  exact (hD _ ⟨hpB, hsubpB⟩).trans (hD _ ⟨hB, hsubB⟩).symm

end CFSG.Quasithin.H13.A6.HatM22
