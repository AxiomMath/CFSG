module

public import CFSG.Quasithin.Vol2.Ch8Sec2KG
public import CFSG.Quasithin.Background.KG82CoverParab
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCases

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H.L34Cov CFSG.ComponentClassification.PSL3Four
  CFSG.LieType.BorelTits MulAction
open scoped commutatorElement

theorem card_eq_map_mul_ker {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G) :
    Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  have h := Subgroup.card_mul_index (f.domRestrict H).ker
  rw [Subgroup.index_ker] at h
  have h1 : (f.domRestrict H).range = H.map f := by
    ext b
    simp [Subgroup.mem_map]
  have h3 : Nat.card ↥(f.domRestrict H).ker = Nat.card ↥(H ⊓ f.ker) := by
    rw [MonoidHom.ker_domRestrict, ← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, h3] at h
  rw [← h, mul_comm]

theorem exists_of_card_two {G : Type*} [Group G] {Z : Subgroup G} (hZ : Nat.card ↥Z = 2) :
    ∃ z ∈ Z, z ≠ 1 ∧ z * z = 1 ∧ ∀ x ∈ Z, x = 1 ∨ x = z := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).1 hZ
  have : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  refine ⟨y, y.2, fun h => hy (Subtype.ext h), ?_, fun x hx => ?_⟩
  · have h1 : y ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    rw [hZ, sq] at h1
    exact congrArg Subtype.val h1
  · by_cases h1 : x = 1
    · exact Or.inl h1
    · right
      have := huniq ⟨x, hx⟩ (fun h => h1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this

theorem dbl_of_iso {G T : Type*} [Group G] [Group T] {Z : Subgroup G} [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hZz : ∀ x ∈ Z, x = 1 ∨ x = z) (ψ : G ⧸ Z ≃* T) :
    Dbl (ψ.toMonoidHom.comp (QuotientGroup.mk' Z)) z := by
  refine ⟨ψ.surjective.comp (QuotientGroup.mk'_surjective Z), hZc hzZ, hz1, hz2, ?_, ?_⟩
  · simp [(QuotientGroup.eq_one_iff z).2 hzZ]
  · intro x hx
    apply hZz
    have h1 : (QuotientGroup.mk' Z) x = 1 := ψ.injective (by simpa using hx)
    exact (QuotientGroup.eq_one_iff x).1 h1

theorem ker_eq_of_dbl {G T : Type*} [Group G] [Group T] {π : G →* T} {z : G} (h : Dbl π z)
    {Z : Subgroup G} (hZz : ∀ x, x ∈ Z ↔ x = 1 ∨ x = z) : π.ker = Z := by
  ext x
  rw [MonoidHom.mem_ker, hZz]
  constructor
  · exact h.ker x
  · rintro (rfl | rfl)
    · exact map_one π
    · exact h.map

theorem card_map_of_dbl {G T : Type*} [Group G] [Group T] {π : G →* T} {z : G} (h : Dbl π z)
    {Z P : Subgroup G} (hZz : ∀ x, x ∈ Z ↔ x = 1 ∨ x = z) (hZ : Nat.card ↥Z = 2) (hZP : Z ≤ P) :
    Nat.card ↥P = 2 * Nat.card ↥(P.map π) := by
  rw [card_eq_map_mul_ker π P, ker_eq_of_dbl h hZz, inf_eq_right.2 hZP, hZ, mul_comm]

theorem kg82CoverL34_holds :
    KG82CoverL34 := by
  intro K _ _ hq hZ hpsl P hZP hP
  obtain ⟨ψ⟩ := exact_model.2.2.2.1 _ hpsl
  obtain ⟨z, hzZ, hz1, hz2, hZz⟩ := exists_of_card_two hZ
  have hd := dbl_of_iso le_rfl hzZ hz1 hz2 hZz ψ
  have hZz' : ∀ x, x ∈ Subgroup.center K ↔ x = 1 ∨ x = z := fun x =>
    ⟨hZz x, by rintro (rfl | rfl); exacts [Subgroup.one_mem _, hzZ]⟩
  have hzc : z ∈ commutator K := by
    rw [hq.1]
    exact Subgroup.mem_top z
  have hcard : Nat.card ↥(P.map (ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))) =
      960 := by
    have := card_map_of_dbl hd hZz' hZ hZP
    omega
  obtain ⟨⟨E, V, F, hpd⟩, -⟩ := parData_of_card _ hcard
  exact commutator_pCoreOf_eq hd hzc triple_S isConj_S (hZP hzZ) hpd

theorem mem_commutator_of_relIndex_two {G : Type*} [Group G] [Finite G] {z : G}
    (hz : z ∈ Subgroup.center G) (hzc : z ∈ commutator G) (hz2 : z * z = 1)
    {X Y H : Subgroup G} (hYX : Y ≤ X) (hzY : z ∈ Y) (hYH : Y ≤ H) (hrel : Y.relIndex H = 2)
    (hodd : Odd H.index) (hYN : ∀ y ∈ Y, ∃ n ∈ ⁅Y, Y⁆, y = n ∨ y = n * z) : z ∈ ⁅X, X⁆ := by
  by_contra hzX
  set N := ⁅Y, Y⁆ with hN
  have hzN : z ∉ N := fun h => hzX (Subgroup.commutator_mono hYX hYX h)
  have hNY : N ≤ Y := Subgroup.commutator_le_self Y
  have hzH : z ∈ ⁅H, H⁆ := mem_commutator_of_odd_index hz hzc hz2 (hYH hzY) hodd
  have hrelN : N.relIndex Y = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨z, hzY, fun y hy => ?_⟩
    by_cases hyN : y ∈ N
    · right
      refine ⟨hyN, fun h => hzN ?_⟩
      have := N.mul_mem (N.inv_mem hyN) h
      rwa [inv_mul_cancel_left] at this
    · left
      refine ⟨?_, hyN⟩
      obtain ⟨n, hn, rfl | rfl⟩ := hYN y hy
      · exact absurd hn hyN
      · rwa [mul_assoc, hz2, mul_one]
  have hYn : (Y.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hrel
  have hconjY : ∀ h ∈ H, Y.map (MulAut.conj h).toMonoidHom = Y := by
    intro h hh
    have hin : ∀ g ∈ H, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy => by
      have := hYn.conj_mem ⟨y, hYH hy⟩ hy ⟨g, hg⟩
      exact this
    refine le_antisymm ?_ fun y hy => ⟨h⁻¹ * y * h, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hin h hh y hy
    · have := hin h⁻¹ (H.inv_mem hh) y hy
      simpa using this
    · simp [mul_assoc]
  have hNn : (N.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : N.map (MulAut.conj (g : G)).toMonoidHom = N := by
      rw [hN, Subgroup.map_commutator, hconjY g g.2]
    have h2 : (g : G) * n * (g : G)⁻¹ ∈ N := by
      rw [← h1]
      exact ⟨n, hn, rfl⟩
    exact h2
  have h4 : (N.subgroupOf H).index = 4 := by
    have := Subgroup.relIndex_mul_relIndex N Y H hNY hYH
    rw [hrelN, hrel] at this
    exact this.symm
  have hcomm : ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by rw [← Subgroup.index, h4]; norm_num)).is_comm.comm a b
  have hHH : ⁅H, H⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 := hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
    have h2 : (QuotientGroup.mk (⁅(⟨a, ha⟩ : ↥H), ⟨b, hb⟩⁆) : ↥H ⧸ N.subgroupOf H) = 1 := by
      rw [show (QuotientGroup.mk (⁅(⟨a, ha⟩ : ↥H), ⟨b, hb⟩⁆) : ↥H ⧸ N.subgroupOf H) =
          ⁅(QuotientGroup.mk ⟨a, ha⟩ : ↥H ⧸ N.subgroupOf H), QuotientGroup.mk ⟨b, hb⟩⁆ from
          map_commutatorElement (QuotientGroup.mk' (N.subgroupOf H)) _ _,
        commutatorElement_eq_one_iff_mul_comm]
      exact h1
    have h3 := (QuotientGroup.eq_one_iff _).1 h2
    exact h3
  exact hzN (hHH hzH)

@[expose] def pairStab (a b : Fin 22) : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22 where
  carrier := {g | (g • a = a ∧ g • b = b) ∨ (g • a = b ∧ g • b = a)}
  one_mem' := Or.inl ⟨one_smul _ _, one_smul _ _⟩
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, mul_smul] at hg hh ⊢
    rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;> rcases hh with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
    · exact Or.inl ⟨by rw [hh1, hg1], by rw [hh2, hg2]⟩
    · exact Or.inr ⟨by rw [hh1, hg2], by rw [hh2, hg1]⟩
    · exact Or.inr ⟨by rw [hh1, hg1], by rw [hh2, hg2]⟩
    · exact Or.inl ⟨by rw [hh1, hg2], by rw [hh2, hg1]⟩
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
    · exact Or.inl ⟨by rw [inv_smul_eq_iff, hg1], by rw [inv_smul_eq_iff, hg2]⟩
    · exact Or.inr ⟨by rw [inv_smul_eq_iff, hg2], by rw [inv_smul_eq_iff, hg1]⟩

theorem card_ker_of_dbl {G T : Type*} [Group G] [Group T] {π : G →* T} {z : G} (h : Dbl π z) :
    Nat.card ↥π.ker = 2 := by
  have e : (π.ker : Set G) = {1, z} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨h.ker x, by rintro (rfl | rfl); exacts [map_one π, h.map]⟩
  have h1 : Nat.card ↥π.ker = Nat.card ↥(π.ker : Set G) := rfl
  rw [h1, e, Nat.card_coe_set_eq, Set.ncard_pair h.ne_one.symm]

section M22

open CFSG.ComponentClassification.WittDesign

theorem card_twoStab
    {a b : Fin 22} (hab : a ≠ b) :
    Nat.card ↥(stabilizer M22 a ⊓ stabilizer M22 b) = 960 := by
  have horb : orbit ↥(stabilizer M22 a) b = ↑(Finset.univ.erase a) := by
    ext x
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, true_and,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩ hga
      have hg : (g : M22) • a = a := g.2
      have hga' : (g : M22) • b = a := hga
      exact hab (smul_left_cancel (g : M22) (hg.trans hga'.symm))
    · intro hx
      obtain ⟨g, hg, hgx⟩ := exists_mem_stabilizer_smul_eq a (Ne.symm hab) hx
      exact ⟨⟨g, hg⟩, hgx⟩
  have h1 := index_stabilizer ↥(stabilizer M22 a) b
  rw [horb, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Subgroup.relIndex_mul_card (stabilizer M22 b) (stabilizer M22 a)
  have h3 : (stabilizer M22 b).relIndex (stabilizer M22 a) = 21 := h1
  rw [h3, card_stabilizer_point, inf_comm] at h2
  omega

theorem mem_commutator_of_m22
    {K : Type} [Group K] [Finite K] {z : K} (hz : z ∈ Subgroup.center K)
    (hzc : z ∈ commutator K) {πM : K →* ↥M22} (hdM : Dbl πM z) {X : Subgroup K} (hzX : z ∈ X)
    {πX : ↥X →* ↥S} (hdX : Dbl πX ⟨z, hzX⟩) (hXc : Nat.card ↥(X.map πM) = 20160) :
    z ∈ ⁅X, X⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : (X.map πM).index = 22 := by
    have := (X.map πM).card_mul_index
    rw [hXc, card_M22'] at this
    omega
  obtain ⟨a, ha⟩ := eq_stabilizer_of_index_22 _ hidx
  obtain ⟨b, hab⟩ : ∃ b : Fin 22, a ≠ b := by
    by_cases h0 : a = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, h0⟩
  obtain ⟨t, hta, htb⟩ := exists_smul_eq_pair hab (Ne.symm hab)
  set Ys := stabilizer M22 a ⊓ stabilizer M22 b with hYs
  set Js := pairStab a b with hJs
  have hYJ : Ys ≤ Js := fun g hg => Or.inl ⟨hg.1, hg.2⟩
  have htJ : t ∈ Js := Or.inr ⟨hta, htb⟩
  have hrelS : Ys.relIndex Js = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, htJ, fun g hg => ?_⟩
    rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
    · right
      refine ⟨⟨hg1, hg2⟩, fun h => hab ?_⟩
      have h1 : (g * t) • a = a := h.1
      rw [mul_smul, hta, hg2] at h1
      exact h1.symm
    · left
      refine ⟨⟨?_, ?_⟩, fun h => hab ?_⟩
      · show (g * t) • a = a
        rw [mul_smul, hta, hg2]
      · show (g * t) • b = b
        rw [mul_smul, htb, hg1]
      · have h1 : g • a = a := h.1
        exact h1.symm.trans hg1
  have hcardY : Nat.card ↥Ys = 960 := card_twoStab hab
  have hcardJ : Nat.card ↥Js = 1920 := by
    have := Subgroup.relIndex_mul_card Ys Js
    rw [hrelS, inf_eq_left.2 hYJ, hcardY] at this
    norm_num at this
    exact this.symm
  have hoddJ : Odd Js.index := by
    have := Js.card_mul_index
    rw [hcardJ, card_M22'] at this
    rw [show Js.index = 231 by omega]
    decide
  set Y := Ys.comap πM with hY
  set H := Js.comap πM with hH
  have hYX : Y ≤ X := fun y hy => by
    have h1 : πM y ∈ X.map πM := by
      rw [ha]
      exact hy.1
    exact hdM.mem_of_map_mem hzX h1
  have hkerY : πM.ker ≤ Y := fun x hx => by
    show πM x ∈ Ys
    rw [MonoidHom.mem_ker.1 hx]
    exact Ys.one_mem
  have hzY : z ∈ Y := hkerY hdM.map
  have hrel : Y.relIndex H = 2 := by
    rw [hY, hH, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hdM.surj]
    exact hrelS
  have hodd : Odd H.index := by
    rw [hH, Subgroup.index_comap_of_surjective _ hdM.surj]
    exact hoddJ
  have hYN : ∀ y ∈ Y, ∃ n ∈ ⁅Y, Y⁆, y = n ∨ y = n * z := by
    set Y' := Y.subgroupOf X with hY'
    have hcY : Nat.card ↥Y = 1920 := by
      rw [card_eq_map_mul_ker πM Y, inf_eq_right.2 hkerY, card_ker_of_dbl hdM, hY,
        Subgroup.map_comap_eq_self_of_surjective hdM.surj, hcardY]
    have hkerY' : πX.ker ≤ Y' := fun x hx => by
      rcases hdX.ker x hx with rfl | rfl
      · exact Y'.one_mem
      · exact hzY
    have hcY' : Nat.card ↥(Y'.map πX) = 960 := by
      have h1 := card_eq_map_mul_ker πX Y'
      rw [inf_eq_right.2 hkerY', card_ker_of_dbl hdX,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv, hcY] at h1
      omega
    have hperf := (parData_of_card _ hcY').2
    intro y hy
    have h1 : πX ⟨y, hYX hy⟩ ∈ (⁅Y', Y'⁆).map πX := by
      rw [Subgroup.map_commutator, hperf]
      exact ⟨⟨y, hYX hy⟩, hy, rfl⟩
    obtain ⟨n, hn, hny⟩ := h1
    have hnY : (n : K) ∈ ⁅Y, Y⁆ := by
      have : (n : K) ∈ (⁅Y', Y'⁆).map X.subtype := ⟨n, hn, rfl⟩
      rwa [Subgroup.map_commutator, hY', Subgroup.map_subgroupOf_eq_of_le hYX] at this
    refine ⟨n, hnY, ?_⟩
    rcases hdX.eq_or_eq_mul hny with h2 | h2
    · exact Or.inl (congrArg Subtype.val h2)
    · exact Or.inr (congrArg Subtype.val h2)
  exact mem_commutator_of_relIndex_two hz hzc hdM.sq hYX hzY (Subgroup.comap_mono hYJ) hrel
    hodd hYN

end M22

theorem map_pCoreOf_subgroupOf {G : Type*} [Group G] {X P : Subgroup G} (hPX : P ≤ X) :
    (pCoreOf 2 (P.subgroupOf X)).map X.subtype = pCoreOf 2 P := by
  have e := map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hPX)
  rw [pCoreOf, pCoreOf, Subgroup.map_map, ← e, Subgroup.map_map]
  rfl

theorem kg82CoverM22_holds :
    KG82CoverM22 := by
  intro K _ _ hq hZ hm22 X hZX hpsl P hZP hPX hP
  obtain ⟨z, hzZ, hz1, hz2, hZz⟩ := exists_of_card_two hZ
  obtain ⟨eM⟩ := hm22
  obtain ⟨ψX⟩ := exact_model.2.2.2.1 _ hpsl
  have hdM := dbl_of_iso le_rfl hzZ hz1 hz2 hZz eM
  have hzX : z ∈ X := hZX hzZ
  set z' : ↥X := ⟨z, hzX⟩ with hz'
  set Z' := (Subgroup.center K).subgroupOf X with hZ'
  have hZ'c : Z' ≤ Subgroup.center ↥X := fun x hx => Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (Subgroup.mem_center_iff.1 (show (x : K) ∈ Subgroup.center K from hx) y)
  have hZz' : ∀ x, x ∈ Z' ↔ x = 1 ∨ x = z' := fun x => by
    constructor
    · intro hx
      rcases hZz x hx with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Z'.one_mem
      · exact hzZ
  have hdX := dbl_of_iso hZ'c ((hZz' z').2 (Or.inr rfl)) (fun h => hz1 (congrArg Subtype.val h))
    (Subtype.ext hz2) (fun x hx => (hZz' x).1 hx) ψX
  have hcZ' : Nat.card ↥Z' = 2 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv, hZ]
  have hcX : Nat.card ↥X = 40320 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z', Nat.card_congr ψX.toEquiv, card_S,
      hcZ']
  have hZz'' : ∀ x, x ∈ Subgroup.center K ↔ x = 1 ∨ x = z := fun x =>
    ⟨hZz x, by rintro (rfl | rfl); exacts [Subgroup.one_mem _, hzZ]⟩
  have hXc : Nat.card ↥(X.map (eM.toMonoidHom.comp (QuotientGroup.mk' _))) = 20160 := by
    have := card_map_of_dbl hdM hZz'' hZ hZX
    omega
  have hzc : z ∈ commutator K := by
    rw [hq.1]
    exact Subgroup.mem_top z
  have hzXX := mem_commutator_of_m22 hzZ hzc hdM hzX hdX hXc
  have hzc' : z' ∈ commutator ↥X := by
    have : z ∈ (commutator ↥X).map X.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hzXX
    obtain ⟨y, hy, hyz⟩ := this
    have hy' : y = z' := Subtype.ext hyz
    rwa [← hy']
  have hzP' : z' ∈ P.subgroupOf X := hZP hzZ
  have hcP' : Nat.card ↥((P.subgroupOf X).map (ψX.toMonoidHom.comp (QuotientGroup.mk' Z'))) =
      960 := by
    have h1 := card_map_of_dbl hdX hZz' hcZ' (P := P.subgroupOf X) (fun x hx => by
      rw [Subgroup.mem_subgroupOf]
      exact hZP hx)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hP] at h1
    omega
  obtain ⟨⟨E, V, F, hpd⟩, -⟩ := parData_of_card _ hcP'
  have hmain := commutator_pCoreOf_eq hdX hzc' triple_S isConj_S hzP' hpd
  have hPmap : (P.subgroupOf X).map X.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPX
  calc ⁅pCoreOf 2 P, P⁆ = (⁅pCoreOf 2 (P.subgroupOf X), P.subgroupOf X⁆).map X.subtype := by
        rw [Subgroup.map_commutator, map_pCoreOf_subgroupOf hPX, hPmap]
    _ = pCoreOf 2 P := by rw [hmain, map_pCoreOf_subgroupOf hPX]

end CFSG.Quasithin.H13
