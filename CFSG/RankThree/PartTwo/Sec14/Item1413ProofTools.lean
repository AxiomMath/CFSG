module

public import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413

variable {G : Type} [Group G] [Finite G]

theorem sec14Std_at {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {c' : G}
    {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    Sec14Std G A c' L' :=
  { toSec13Data := { h.toSec13Data with zpowers_mem_omegaA := hc', mem_lA := hL' }
    hypS_or_hypT := h.hypS_or_hypT
    chosen136 := h.chosen136 }

theorem transOn_centralizer_of_not_mem_gammaA (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h143 : Item143 A (lB A))
    (hJ : ∀ L₀ ∈ lA A c,
      IsEmpty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {e : G} (heA : e ∈ A) (he1 : e ≠ 1) (hΓ : Subgroup.zpowers e ∉ gammaA A (lB A)) :
    TransOn A (lB A) (xA A) (Subgroup.centralizer ({e} : Set G)) := by
  have hA : IsE27 A := h.isE27
  by_cases hΩ : Subgroup.zpowers e ∈ omegaA A
  · have hT : TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
      by_contra hT
      exact hΓ ⟨hΩ, hT⟩
    exact (transOn_normalizer_iff hA heA).mp hT
  set K := delta A (lB A) (Subgroup.centralizer ({e} : Set G)) with hKdef
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  obtain ⟨Q, -, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups K A (piCompl 3))) (a := ⊥)
    ⟨bot_le, (isPiSubgroup_piCompl_iff Nat.prime_three ⊥).mpr (by simp),
      by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top⟩
  obtain ⟨hQ𝓠, hcase⟩ := h143 e heA he1 hΩ Q hQ
  rcases hcase with hK | ⟨b, d, Lb, hb, hLb, hJb, hdA, hd1, hdc, -, -⟩
  ·
    have hXCe : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.centralizer ({e} : Set G) :=
      (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA))
    have hN : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) : Set G) :=
      hXCe.trans (le_normalizer_pPrimeCoreOf 3 _)
    have hK3 : ¬ 3 ∣ Nat.card K := by
      intro h3
      rw [hKdef, hK, sup_comm] at h3
      have hdvd := h3.trans (card_sup_dvd_card_mul hN)
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h1
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h1
    have hKmem : K ∈ invariantPiSubgroups K A (piCompl 3) :=
      ⟨le_rfl, (isPiSubgroup_piCompl_iff Nat.prime_three K).mpr hK3, hAK⟩
    have hQK : Q = K := hQ.eq_of_le hKmem hQ.prop.1
    have hKQ : K ∈ scriptQ A (lB A) := hQK ▸ hQ𝓠.1
    exact transOn_of_delta (transOn_of_mem_scriptQ hA hbot hKQ)
  ·
    obtain ⟨Le, hLe, ⟨φ⟩⟩ := exists_hj_of_hj_point h134 h48 h415 h hb hLb hJb hdA hd1 hdc
      h.toSec13Data.zpowers_mem_omegaA
    exact ((hJ Le hLe).false φ).elim

theorem mem_gammaA_of_meet (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h143 : Item143 A (lB A))
    (hfail : Fail1411 A (lB A))
    (hJ : ∀ L₀ ∈ lA A c,
      IsEmpty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hSa : S ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥)
    (hTa : T ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥) :
    Subgroup.zpowers a ∈ gammaA A (lB A) := by
  by_contra hΓ
  exact not_transOn_centralizer_of_meet h h146 hbot hfail.2 hS hT hST haA hSa hTa
    (transOn_centralizer_of_not_mem_gammaA h134 h48 h415 h hbot h143 hJ haA ha1 hΓ)

theorem xA_le_normalizer_of_mem_lA {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (h3 : 3 ∣ Nat.card La) : xA A ≤ Subgroup.normalizer (La : Set G) := by
  intro x hx
  have haA : a ∈ A := (zpowers_mem_omegaA_iff.mp ha).1
  have hxa : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA) (pPrimeCoreOf_le 3 _ hx)
  refine mem_normalizer_of_map_conj_eq
    ((h.chosen136.2 a ha La hLa).2 _ (Sec6.map_conj_mem_thetaComponentsAt hxa hLa.1) ?_)
  rwa [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem map_conj_mem_scriptQPiStar_of_xA {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (h3 : 3 ∣ Nat.card La) {U : Subgroup G} (hU : U ∈ scriptQPiStar A (lB A) La (piOf 2))
    {x : G} (hx : x ∈ xA A) :
    U.map (MulAut.conj x).toMonoidHom ∈ scriptQPiStar A (lB A) La (piOf 2) := by
  have hXL := xA_le_normalizer_of_mem_lA h ha hLa h3
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hnat := isNaturalFamily_lB A
  refine maximal_map_conj (W := xA A) (fun V hV y hy => ?_) hU hx
  refine ⟨⟨rank3II_14_4_5 hnat (hXA hy) hV.1.1, ?_⟩, ?_⟩
  · rw [← Late.map_conj_eq_of_mem_normalizer (hXL hy)]
    exact Subgroup.map_mono hV.1.2
  · intro q hq
    exact hV.2 q (by rwa [Subgroup.card_map_of_injective (MulAut.conj y).injective] at hq)

omit [Finite G] in
theorem inf_centralizer_map_conj_of_mem_xA {A U : Subgroup G} {x : G} (hx : x ∈ xA A) :
    A ⊓ Subgroup.centralizer ((U.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
      A ⊓ Subgroup.centralizer (U : Set G) := by
  have hxA : ∀ a ∈ A, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp (pPrimeCoreOf_le 3 _ hx) a ha
  ext a
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.coe_map,
    MulEquiv.coe_toMonoidHom, Set.mem_image, SetLike.mem_coe, MulAut.conj_apply,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine and_congr_right fun ha => ⟨fun h u hu => ?_, fun h u hu => ?_⟩
  · have h1 := h u hu
    have hax := hxA a ha
    calc u * a = x⁻¹ * (x * u * x⁻¹ * a) * x := by
          rw [show x * u * x⁻¹ * a = x * u * (x⁻¹ * a) by group,
            show x⁻¹ * a = a * x⁻¹ by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hax, mul_assoc, mul_inv_cancel, mul_one]]
          group
      _ = x⁻¹ * (a * (x * u * x⁻¹)) * x := by rw [h1]
      _ = a * u := by
          rw [show x⁻¹ * (a * (x * u * x⁻¹)) * x = x⁻¹ * a * x * u by group,
            show x⁻¹ * a = a * x⁻¹ by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hax, mul_assoc, mul_inv_cancel, mul_one]]
          group
  · have h1 := h u hu
    have hax := hxA a ha
    have hxinv : x⁻¹ * a = a * x⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hax, mul_assoc, mul_inv_cancel, mul_one]
    calc x * u * x⁻¹ * a = x * (u * a) * x⁻¹ := by
          rw [mul_assoc (x * u), hxinv]; group
      _ = x * (a * u) * x⁻¹ := by rw [h1]
      _ = a * (x * u * x⁻¹) := by
          rw [show x * (a * u) * x⁻¹ = x * a * (u * x⁻¹) by group, ← hax]; group

theorem xA_le_normalizer_of_injective {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (h3 : 3 ∣ Nat.card La)
    (hinj : ∀ R₁ ∈ scriptQPiStar A (lB A) La (piOf 2), ∀ R₂ ∈ scriptQPiStar A (lB A) La (piOf 2),
      A ⊓ Subgroup.centralizer (R₁ : Set G) = A ⊓ Subgroup.centralizer (R₂ : Set G) → R₁ = R₂)
    {U : Subgroup G} (hU : U ∈ scriptQPiStar A (lB A) La (piOf 2)) :
    xA A ≤ Subgroup.normalizer (U : Set G) := fun _ hx =>
  mem_normalizer_of_map_conj_eq (hinj _ (map_conj_mem_scriptQPiStar_of_xA h ha hLa h3 hU hx) U hU
    (inf_centralizer_map_conj_of_mem_xA hx))

theorem map_conj_eq_of_zpowers_eq_map {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {b w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) {Lb : Subgroup G} (hLb : Lb ∈ lA A b)
    (h3 : 3 ∣ Nat.card Lb)
    (hcb : Subgroup.zpowers c = (Subgroup.zpowers b).map (MulAut.conj w).toMonoidHom) :
    Lb.map (MulAut.conj w).toMonoidHom = L := by
  have hD := h.toSec13Data
  have h1 : Lb.map (MulAut.conj w).toMonoidHom ∈ lA A (w * b * w⁻¹) :=
    (map_conj_mem_lA_iff hw).mpr hLb
  have h2 : Subgroup.zpowers (w * b * w⁻¹) = Subgroup.zpowers c := by
    rw [hcb, MonoidHom.map_zpowers]
    rfl
  rw [lA_eq_of_zpowers_eq h2] at h1
  refine (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).2 _ h1.1 ?_
  rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective]

theorem isEmpty_mulEquiv_of_card_ne {X Y : Type*} [Group X] [Group Y]
    (h : Nat.card X ≠ Nat.card Y) : IsEmpty (X ≃* Y) :=
  ⟨fun e => h (Nat.card_congr e.toEquiv)⟩

omit [Finite G] in
theorem three_dvd_card_of_mulEquiv {L : Subgroup G} {X : Type*} [Group X]
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* X) (h3 : 3 ∣ Nat.card X) : 3 ∣ Nat.card L := by
  have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
  rw [Nat.card_congr φ.toEquiv] at h1
  exact h3.trans h1

theorem center_eq_bot_of_isSimpleGroup' {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : Subgroup.center Q = ⊥ := by
  rcases (inferInstance : (Subgroup.center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

theorem not_mem_of_mulEquiv_simple {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    {X : Type*} [Group X] [IsSimpleGroup X] (hX : ¬ (Nat.card X).Prime)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* X) : c ∉ L :=
  Sec13.not_mem_of_center_eq_bot hD
    (Sec13.center_eq_bot_of_mulEquiv φ (center_eq_bot_of_isSimpleGroup' hX))

section NF

variable {L : Subgroup G} {c b d : G}

theorem three_dvd_of_pow_mem (hc : orderOf c = 3) (hcL : c ∉ L) {m : ℕ} (hm : c ^ m ∈ L) :
    3 ∣ m := by
  have h := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc hcL
  have hmem : c ^ m ∈ L ⊓ Subgroup.zpowers c :=
    ⟨hm, Subgroup.pow_mem _ (Subgroup.mem_zpowers c) m⟩
  rw [h, Subgroup.mem_bot] at hmem
  rw [← hc]
  exact orderOf_dvd_of_pow_eq_one hmem

omit [Finite G] in
theorem three_dvd_of_pow_mul_pow_eq_one (hb3 : b ^ 3 = 1) (hd : orderOf d = 3)
    (hbd : b ∉ Subgroup.zpowers d) {i j : ℕ} (h : b ^ i * d ^ j = 1) : 3 ∣ i ∧ 3 ∣ j := by
  have hi : 3 ∣ i := by
    by_contra hi
    have hbi : b ^ i ∈ Subgroup.zpowers d := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j)
    apply hbd
    have hmod : b ^ i = b ^ (i % 3) := by
      conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hb3, one_pow, mul_one]
    rcases (by omega : i % 3 = 1 ∨ i % 3 = 2) with h1 | h2
    · rwa [hmod, h1, pow_one] at hbi
    · have hsq : (b ^ i) ^ 2 = b := by
        rw [hmod, h2, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hb3, one_mul, pow_one]
      rw [← hsq]
      exact Subgroup.pow_mem _ hbi 2
  refine ⟨hi, ?_⟩
  obtain ⟨k, rfl⟩ := hi
  rw [pow_mul, hb3, one_pow, one_mul] at h
  rw [← hd]
  exact orderOf_dvd_of_pow_eq_one h

@[expose] def nf (c b d : G) (i j k : ℕ) : G := c ^ i * b ^ j * d ^ k

omit [Finite G] in
theorem nf_mul (hcb : Commute c b) (hcd : Commute c d) (hbd : Commute b d) (i j k i' j' k' : ℕ) :
    nf c b d i j k * nf c b d i' j' k' = nf c b d (i + i') (j + j') (k + k') := by
  have h1 : d ^ k * c ^ i' = c ^ i' * d ^ k := ((hcd.pow_pow i' k).eq).symm
  have h2 : b ^ j * c ^ i' = c ^ i' * b ^ j := ((hcb.pow_pow i' j).eq).symm
  have h3 : d ^ k * b ^ j' = b ^ j' * d ^ k := ((hbd.pow_pow j' k).eq).symm
  unfold nf
  rw [pow_add, pow_add, pow_add]
  calc c ^ i * b ^ j * d ^ k * (c ^ i' * b ^ j' * d ^ k')
      = c ^ i * (b ^ j * (d ^ k * c ^ i')) * b ^ j' * d ^ k' := by simp only [mul_assoc]
    _ = c ^ i * (b ^ j * (c ^ i' * d ^ k)) * b ^ j' * d ^ k' := by rw [h1]
    _ = c ^ i * ((b ^ j * c ^ i') * d ^ k) * b ^ j' * d ^ k' := by simp only [mul_assoc]
    _ = c ^ i * ((c ^ i' * b ^ j) * d ^ k) * b ^ j' * d ^ k' := by rw [h2]
    _ = c ^ i * c ^ i' * b ^ j * (d ^ k * b ^ j') * d ^ k' := by simp only [mul_assoc]
    _ = c ^ i * c ^ i' * b ^ j * (b ^ j' * d ^ k) * d ^ k' := by rw [h3]
    _ = c ^ i * c ^ i' * (b ^ j * b ^ j') * (d ^ k * d ^ k') := by simp only [mul_assoc]

omit [Finite G] in
theorem nf_pow (hcb : Commute c b) (hcd : Commute c d) (hbd : Commute b d) (i j k n : ℕ) :
    nf c b d i j k ^ n = nf c b d (i * n) (j * n) (k * n) := by
  induction n with
  | zero => simp [nf]
  | succ n ih =>
    rw [pow_succ, ih, nf_mul hcb hcd hbd]
    ring_nf

theorem nf_eq_mod (hcb : Commute c b) (hcd : Commute c d) (hbd : Commute b d) (hc : orderOf c = 3)
    (hcL : c ∉ L) (hbL : b ∈ L) (hdL : d ∈ L) (hb3 : b ^ 3 = 1) (hd : orderOf d = 3)
    (hbdz : b ∉ Subgroup.zpowers d) {i j k i' j' k' : ℕ}
    (h : nf c b d i j k = nf c b d i' j' k') :
    i % 3 = i' % 3 ∧ j % 3 = j' % 3 ∧ k % 3 = k' % 3 := by
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hd3 : d ^ 3 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have h1 : nf c b d (i + 2 * i') (j + 2 * j') (k + 2 * k') = 1 := by
    rw [← nf_mul hcb hcd hbd, h, nf_mul hcb hcd hbd]
    unfold nf
    rw [show i' + 2 * i' = 3 * i' by ring, show j' + 2 * j' = 3 * j' by ring,
      show k' + 2 * k' = 3 * k' by ring, pow_mul, pow_mul, pow_mul, hc3, hb3, hd3]
    simp
  unfold nf at h1
  have h1' : c ^ (i + 2 * i') * (b ^ (j + 2 * j') * d ^ (k + 2 * k')) = 1 := by
    rw [← mul_assoc]
    exact h1
  have hcm : c ^ (i + 2 * i') ∈ L := by
    rw [eq_inv_of_mul_eq_one_left h1']
    exact inv_mem (mul_mem (Subgroup.pow_mem _ hbL _) (Subgroup.pow_mem _ hdL _))
  have hci := three_dvd_of_pow_mem hc hcL hcm
  obtain ⟨r, hr⟩ := hci
  rw [hr, pow_mul, hc3, one_pow, one_mul] at h1
  obtain ⟨hj, hk⟩ := three_dvd_of_pow_mul_pow_eq_one hb3 hd hbdz h1
  omega

end NF

end Proof1413

end CFSG.RankThree.PartTwo.Sec14
