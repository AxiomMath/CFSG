module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_commutator_le_left {H K : Subgroup G} (h : ⁅H, K⁆ ≤ H) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ H, k * x * k⁻¹ ∈ H := by
    intro k hk x hx
    have h1 : ⁅x⁻¹, k⁆ ∈ H := h (Subgroup.commutator_mem_commutator (H.inv_mem hx) hk)
    have e : k * x * k⁻¹ = x * ⁅x⁻¹, k⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact H.mul_mem hx h1
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key k hk x
  · intro hx
    have := key k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this

variable [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem exists_commutator_eq (h : Hyp611Nat G T M L V n) {a : G} (ha : a ∈ ch6S T L V)
    (haV : a ∉ Subgroup.centralizer (V : Set G)) {z : G} (hz : z ∈ ch6ZS T L V) :
    ∃ x ∈ V, ⁅x, a⁆ = z := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨B, hB, hBeq⟩ := h.exists_stab_of_mem_S hv hle ha
  have haN : a ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer ha.1
  set m : Subgroup.normalizer (V : Set G) := ⟨a, h.toHyp611.T_le_normalizer ha.1⟩ with hm
  obtain ⟨w, hw⟩ : ∃ w, (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact haV (h.data.mem_centralizer_of_conj_eq m fun w => by rw [hBeq, hcon])
  obtain ⟨c', hc'⟩ := sub_mem_line_of_mem_sl2Stab hv hB w
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    apply hw
    rw [zero_smul, sub_eq_zero] at hc'
    exact hc'
  obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hz.1⟩).mp hz
  set t : h.data.K := -(c / c') with ht
  set x : ↥V := h.data.E.symm (Multiplicative.ofAdd (t • w)) with hx
  have hEx : Multiplicative.toAdd (h.data.E x) = t • w := by simp [hx]
  refine ⟨x, x.2, ?_⟩
  have hy : a * (x : G)⁻¹ * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp haN _).mp (V.inv_mem x.2)
  have hmem : (x : G) * (a * (x : G)⁻¹ * a⁻¹) ∈ V := V.mul_mem x.2 hy
  have hcomm : ⁅(x : G), a⁆ = (x : G) * (a * (x : G)⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hcomm]
  have hE : h.data.E ⟨(x : G) * (a * (x : G)⁻¹ * a⁻¹), hmem⟩ =
      h.data.E x * h.data.E ⟨a * (x : G)⁻¹ * a⁻¹, hy⟩ := by
    rw [← map_mul]
    rfl
  have hEt : Multiplicative.toAdd (h.data.E ⟨a * (x : G)⁻¹ * a⁻¹, hy⟩) =
      (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec
        (Multiplicative.toAdd (h.data.E ⟨(x : G)⁻¹, V.inv_mem x.2⟩)) := by
    rw [← hBeq, h.data.conj_apply]
    congr 2
  have hEinv : Multiplicative.toAdd (h.data.E ⟨(x : G)⁻¹, V.inv_mem x.2⟩) =
      -Multiplicative.toAdd (h.data.E x) := by
    rw [show (⟨(x : G)⁻¹, V.inv_mem x.2⟩ : ↥V) = x⁻¹ from rfl, map_inv]
    rfl
  have hfinal : Multiplicative.toAdd (h.data.E ⟨(x : G) * (a * (x : G)⁻¹ * a⁻¹), hmem⟩) =
      Multiplicative.toAdd (h.data.E ⟨z, hz.1⟩) := by
    rw [hE, toAdd_mul, hEt, hEinv, Matrix.mulVec_neg, hEx, hc, Matrix.mulVec_smul]
    have hBw : (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w = w + c' • v := by
      rw [← hc']
      abel
    rw [hBw]
    have e2 : t • w + -(t • (w + c' • v)) = -((t * c') • v) := by
      rw [smul_add, smul_smul]
      abel
    have e3 : t * c' = -c := by
      rw [ht]
      field_simp
    rw [e2, e3, neg_smul, neg_neg]
  exact congrArg Subtype.val (h.data.E.injective (Multiplicative.toAdd.injective hfinal))

theorem centralizer_eq_ZS (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A)
    (hAC : Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n ≤ Nat.card A)
    (hVC : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = 2 ^ n) :
    A ≤ ch6S T L V ∧ V ⊓ Subgroup.centralizer (A : Set G) = ch6ZS T L V := by
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have hAS : A ≤ ch6S T L V := by
    refine h.le_S_of_card hAT hA ?_
    rw [hVcard, hVC]
    calc 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
        (Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n) * 2 ^ n := by ring
      _ ≤ Nat.card A * 2 ^ n := Nat.mul_le_mul_right _ hAC
  refine ⟨hAS, ?_⟩
  have hle : ch6ZS T L V ≤ V ⊓ Subgroup.centralizer (A : Set G) := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hAS ha).2 z hz).symm⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hVC, h.card_ZS])).symm

end Hyp611Nat

theorem stmt6_1_11 (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) : Stmt6_1_11 := by
  intro G _ _ T M L V n h g hgT hne hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.toHyp611.isElemAbelian
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have hpos : 0 < 2 ^ n := by positivity
  set A := conjSubgroup V g with hAdef
  have hAe : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hV g
  have hAcard : Nat.card A = 2 ^ n * 2 ^ n := by rw [hAdef, E3.card_conjSubgroup, hVcard]
  have hAN : A ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_commutator_le_left (hle.trans inf_le_left)
  have hVNA : V ≤ Subgroup.normalizer (A : Set G) := by
    refine le_normalizer_of_commutator_le_left ?_
    rw [Subgroup.commutator_comm]
    exact hle.trans inf_le_right
  have hAC : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have h3 := (h6110 G T M L V n h).2.2
  have hcardAC : Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n = 2 ^ n * 2 ^ n := by
    have hm := h3 g hAN hAC
    have hrel : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 2 ^ n := by
      have hdvd : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ∣ 2 ^ (n + n) := by
        rw [pow_add, ← hAcard]
        exact Subgroup.relIndex_dvd_card _ _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      unfold mQuot at hm
      rw [hj, padicValNat.prime_pow] at hm
      rw [hj, hm]
    have := card_mul_relIndex_of_le (inf_le_left : A ⊓ Subgroup.centralizer (V : Set G) ≤ A)
    rw [hrel, hAcard] at this
    exact this
  set B := conjSubgroup V g⁻¹ with hBdef
  have hBA : conjSubgroup A g⁻¹ = V := by
    rw [hAdef, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := by
    have := E3.conjSubgroup_mono_left g⁻¹ hVNA
    rwa [E3.conjSubgroup_normalizer, hBA] at this
  have hBC : ¬ B ≤ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hAC
    have := E3.conjSubgroup_mono_left g hc
    rw [hBdef, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      E3.conjSubgroup_centralizer] at this
    rw [Subgroup.le_centralizer_iff]
    exact this
  have hBcard : Nat.card B = 2 ^ n * 2 ^ n := by rw [hBdef, E3.card_conjSubgroup, hVcard]
  have hcardBC : Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n = 2 ^ n * 2 ^ n := by
    have hm := h3 g⁻¹ hBN hBC
    have hrel : (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B = 2 ^ n := by
      have hdvd : (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B ∣ 2 ^ (n + n) := by
        rw [pow_add, ← hBcard]
        exact Subgroup.relIndex_dvd_card _ _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      unfold mQuot at hm
      rw [hj, padicValNat.prime_pow] at hm
      rw [hj, hm]
    have := card_mul_relIndex_of_le (inf_le_left : B ⊓ Subgroup.centralizer (V : Set G) ≤ B)
    rw [hrel, hBcard] at this
    exact this
  have hVCB : conjSubgroup (A ⊓ Subgroup.centralizer (V : Set G)) g⁻¹ =
      V ⊓ Subgroup.centralizer (B : Set G) := by
    rw [E3.conjSubgroup_inf, hBA, E3.conjSubgroup_centralizer]
  have hVCA : conjSubgroup (B ⊓ Subgroup.centralizer (V : Set G)) g =
      V ⊓ Subgroup.centralizer (A : Set G) := by
    rw [E3.conjSubgroup_inf, hBdef, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      E3.conjSubgroup_centralizer]
  have hcardVCA : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = 2 ^ n := by
    rw [← hVCA, E3.card_conjSubgroup]
    exact Nat.eq_of_mul_eq_mul_right hpos hcardBC
  have hcardVCB : Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) = 2 ^ n := by
    rw [← hVCB, E3.card_conjSubgroup]
    exact Nat.eq_of_mul_eq_mul_right hpos hcardAC
  obtain ⟨hAS, hCVA⟩ := h.centralizer_eq_ZS hgT hAe (by rw [hcardAC, hAcard]) hcardVCA
  have hcomm : ⁅V, A⁆ = ch6ZS T L V := by
    apply le_antisymm ((Subgroup.commutator_mono le_rfl hAS).trans h.commutator_V_S_le)
    intro z hz
    obtain ⟨a, haA, haV⟩ := Set.not_subset.mp hAC
    obtain ⟨x, hxV, hxz⟩ := h.exists_commutator_eq (hAS haA) haV hz
    rw [← hxz]
    exact Subgroup.commutator_mem_commutator hxV haA
  have hinter : ch6ZS T L V = V ⊓ A := by
    apply le_antisymm (hcomm ▸ hle)
    rw [← hCVA]
    exact inf_le_inf_left V fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      B2F.isElemAbelian_comm hAe ha hx
  refine ⟨hcomm.symm, hinter, ?_⟩
  have hCAV : A ⊓ Subgroup.centralizer (V : Set G) = ch6ZS T L V := by
    have hle' : ch6ZS T L V ≤ A ⊓ Subgroup.centralizer (V : Set G) := by
      intro z hz
      have hzA : z ∈ A := (hinter.le hz).2
      exact ⟨hzA, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        B2F.isElemAbelian_comm hV hv hz.1⟩
    refine (Subgroup.eq_of_le_of_card_ge hle' ?_).symm
    rw [h.card_ZS]
    have := Nat.eq_of_mul_eq_mul_right hpos hcardAC
    rw [this]
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      h.toHyp611.T_le_normalizer le_top
  have hBe : IsElemAbelian 2 B := E3.isElemAbelian_conjSubgroup hV g⁻¹
  obtain ⟨y, hyN, hyT⟩ := exists_conj_le_of_isSylowTwoOf hTsyl hBN
    (B2F.isPGroup_of_isElemAbelian hBe)
  set B' := cjSub y B with hB'def
  have hB'e : IsElemAbelian 2 B' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · have ha := mem_cjSub.mp a.2
      have hb := mem_cjSub.mp b.2
      have hab := B2F.isElemAbelian_comm hBe ha hb
      calc (a : G) * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [hab]
        _ = b * a := by group
    · have h2 := hBe.2 _ (mem_cjSub.mp ha)
      rw [pow_two] at h2 ⊢
      calc a * a = y * ((y⁻¹ * a * y) * (y⁻¹ * a * y)) * y⁻¹ := by group
        _ = 1 := by rw [h2]; group
  have hB'card : Nat.card B' = 2 ^ n * 2 ^ n := by
    rw [hB'def, ← hBcard]
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hcardB'C : Nat.card ↥(B' ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 ^ n := by
    have hinj : Nat.card ↥(B' ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) := by
      refine Nat.card_le_card_of_injective (fun x => ⟨y⁻¹ * x * y, mem_cjSub.mp x.2.1, ?_⟩) ?_
      · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        have hw' : y * w * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
        have hc := Subgroup.mem_centralizer_iff.mp x.2.2 _ hw'
        calc w * (y⁻¹ * x * y) = y⁻¹ * ((y * w * y⁻¹) * x) * y := by group
          _ = y⁻¹ * (x * (y * w * y⁻¹)) * y := by rw [hc]
          _ = y⁻¹ * x * y * w := by group
      · intro x x' hxx'
        apply Subtype.ext
        have h1 := congrArg Subtype.val hxx'
        simp only at h1
        have h2 := congrArg (fun z => y * z * y⁻¹) h1
        simpa [mul_assoc] using h2
    rw [Nat.eq_of_mul_eq_mul_right hpos hcardBC] at hinj
    exact hinj
  have hcardVCB' : 2 ^ n ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (B' : Set G)) := by
    rw [← hcardVCB]
    refine Nat.card_le_card_of_injective (fun x => ⟨y * x * y⁻¹,
      (Subgroup.mem_normalizer_iff.mp hyN _).mp x.2.1, ?_⟩) ?_
    · refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      have hb' := mem_cjSub.mp hb
      have hc := Subgroup.mem_centralizer_iff.mp x.2.2 _ hb'
      calc b * (y * x * y⁻¹) = y * ((y⁻¹ * b * y) * x) * y⁻¹ := by group
        _ = y * (x * (y⁻¹ * b * y)) * y⁻¹ := by rw [hc]
        _ = y * x * y⁻¹ * b := by group
    · intro x x' hxx'
      apply Subtype.ext
      have h1 := congrArg Subtype.val hxx'
      simp only at h1
      have h2 := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using h2
  have hB'C : ¬ B' ≤ Subgroup.centralizer (V : Set G) := by
    intro hc
    have : Nat.card B' ≤ 2 ^ n := by
      rw [← inf_eq_left.mpr hc]
      exact hcardB'C
    rw [hB'card] at this
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    nlinarith
  obtain ⟨b₀, hb₀B', hb₀V⟩ := Set.not_subset.mp hB'C
  have hcardVCB'le : Nat.card ↥(V ⊓ Subgroup.centralizer (B' : Set G)) ≤ 2 ^ n :=
    le_trans (Subgroup.card_le_of_le (inf_le_inf_left V
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb₀B'))))
      (h.data.card_fixed_le_two_pow ⟨b₀, h.toHyp611.T_le_normalizer (hyT hb₀B')⟩
        (h.T_le_normalizer_L (hyT hb₀B')) hb₀V)
  obtain ⟨-, hCVB'⟩ := h.centralizer_eq_ZS hyT hB'e
    (by
      calc Nat.card ↥(B' ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n ≤ 2 ^ n * 2 ^ n :=
          Nat.mul_le_mul_right _ hcardB'C
        _ = Nat.card B' := hB'card.symm)
    (le_antisymm hcardVCB'le hcardVCB')
  have hiff : ∀ x : G, g⁻¹ * x * g ∈ ch6ZS T L V ↔ y * x * y⁻¹ ∈ ch6ZS T L V := by
    intro x
    have e1 : x ∈ V ⊓ Subgroup.centralizer (B : Set G) ↔ g⁻¹ * x * g ∈ ch6ZS T L V := by
      rw [← hVCB, mem_conjSubgroup_iff, inv_inv, hCAV]
    have e2 : x ∈ V ⊓ Subgroup.centralizer (B : Set G) ↔ y * x * y⁻¹ ∈ ch6ZS T L V := by
      rw [← hCVB']
      constructor
      · rintro ⟨hxV, hxC⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hyN _).mp hxV,
          Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
        have hb' := mem_cjSub.mp hb
        have hc := Subgroup.mem_centralizer_iff.mp hxC _ hb'
        calc b * (y * x * y⁻¹) = y * ((y⁻¹ * b * y) * x) * y⁻¹ := by group
          _ = y * (x * (y⁻¹ * b * y)) * y⁻¹ := by rw [hc]
          _ = y * x * y⁻¹ * b := by group
      · rintro ⟨hxV, hxC⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hyN _).mpr hxV,
          Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
        have hb' : y * b * y⁻¹ ∈ B' := mem_cjSub.mpr (by simpa [mul_assoc] using hb)
        have hc := Subgroup.mem_centralizer_iff.mp hxC _ hb'
        have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
        calc b * x = y⁻¹ * ((y * b * y⁻¹) * (y * x * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * x * y⁻¹) * (y * b * y⁻¹)) * y := by rw [hc]
          _ = x * b := by group
    exact e1.symm.trans e2
  have hk : y * g ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    rw [← Subgroup.inv_mem_iff, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have := (hiff (y⁻¹ * z * y)).mpr (by simpa [mul_assoc] using hz)
      simpa [mul_assoc] using this
    · intro hz
      have := (hiff (y⁻¹ * z * y)).mp (by simpa [mul_assoc] using hz)
      simpa [mul_assoc] using this
  have hVk : conjSubgroup V (y * g) = A := by
    rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hyN]
  have hS := h.isSylowIn_S
  have hfrat := exists_mul_of_sylow (Subgroup.centralizer_le_normalizer _)
    (F7.normalizer_le_normalizer_centralizer _) hS.le hS.isPGroup hS.not_dvd_relIndex
  obtain ⟨m, hm, c, hc, hmc⟩ := hfrat (y * g) hk
  have hmM : m ∈ M := h.normalizer_S_le h432 hm.2
  have hmV : m ∈ Subgroup.normalizer (V : Set G) :=
    (h.normalizer_le h.ZS_ne_bot h.ZS_le ⟨hmM, hm.1⟩).2
  refine ⟨c, hc, ?_⟩
  rw [← hVk, hmc, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hmV]

end CFSG.Quasithin.H13
