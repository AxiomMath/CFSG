module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.GroupTheory.SuzukiTwoGroupsCoprime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.Quasithin.St84

open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem card_eq_relIndex_of_isComplement {X Z : Subgroup G} [Finite ↥X] [Finite ↥Z]
    (hXZ : X ⊓ Z = ⊥) (hZX : Z ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card ↥X = Z.relIndex (X ⊔ Z) := by
  have hdisj : Disjoint X Z := disjoint_iff.mpr hXZ
  have hsup : Nat.card ↥(X ⊔ Z) = Nat.card ↥X * Nat.card ↥Z :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X Z hZX hdisj
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf (X ⊔ Z))
  have hZcard : Nat.card ↥(Z.subgroupOf (X ⊔ Z)) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Z ≤ X ⊔ Z)).toEquiv
  rw [hZcard] at hsplit
  have hrel : Z.relIndex (X ⊔ Z) = Nat.card (↥(X ⊔ Z) ⧸ Z.subgroupOf (X ⊔ Z)) := rfl
  rw [hrel]
  exact Nat.mul_right_cancel Nat.card_pos (hsup.symm.trans hsplit)

private theorem le_sylow_of_normal {Q A L : Subgroup G} [Finite ↥L] (hA : IsSylowTwoOf A L)
    (hQL : Q ≤ L) (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q) :
    Q ≤ A := by
  have hAQn : A ≤ Subgroup.normalizer (Q : Set G) := hA.1.trans hQn
  have hAQ2 : IsPGroup 2 ↥(A ⊔ Q) :=
    IsPGroup.to_sup_of_normal_right' hA.2.1 hQ2 hAQn
  have hAQle : A ⊔ Q ≤ L := sup_le hA.1 hQL
  have hodd : ¬ 2 ∣ A.relIndex (A ⊔ Q) := by
    intro h2
    apply hA.2.2
    change 2 ∣ A.relIndex L
    rw [← Subgroup.relIndex_mul_relIndex A (A ⊔ Q) L le_sup_left hAQle]
    exact dvd_mul_of_dvd_left h2 _
  haveI hfinA : Finite ↥A :=
    Finite.of_injective (Subgroup.inclusion hA.1) (Subgroup.inclusion_injective hA.1)
  haveI hfinAQ : Finite ↥(A ⊔ Q) :=
    Finite.of_injective (Subgroup.inclusion hAQle) (Subgroup.inclusion_injective hAQle)
  haveI hfinSub : Finite ↥(A.subgroupOf (A ⊔ Q)) :=
    Finite.of_injective (Subgroup.inclusion (le_top : A.subgroupOf (A ⊔ Q) ≤ ⊤))
      (Subgroup.inclusion_injective le_top)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAQ2
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hA.2.1
  have hcard : A.relIndex (A ⊔ Q) = 2 ^ k / 2 ^ m := by
    rw [show A.relIndex (A ⊔ Q) = (A.subgroupOf (A ⊔ Q)).index from rfl,
        Subgroup.index_eq_card_div, hk]
    congr 1
    rw [← hm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ Q)).toEquiv
  have hmk : m ≤ k := by
    have hdvd : 2 ^ m ∣ 2 ^ k := by
      rw [← hm, ← hk]
      exact Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ Q)
    exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num : 1 < 2)).mp hdvd
  have hq : A.relIndex (A ⊔ Q) = 2 ^ (k - m) := by
    have hnum : 2 ^ k = 2 ^ (k - m) * 2 ^ m := by
      conv_lhs => rw [show k = (k - m) + m by omega, pow_add]
    rw [hcard, hnum, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ m)]
  by_contra hQA
  have hlt : m < k := by
    rcases Nat.lt_or_ge m k with h | h
    · exact h
    · exfalso
      apply hQA
      have hcardle : Nat.card ↥(A ⊔ Q) ≤ Nat.card ↥A := by
        rw [hk, hm]
        exact Nat.pow_le_pow_right (by norm_num : 0 < 2) h
      have heq : A = A ⊔ Q :=
        Subgroup.eq_of_le_of_card_ge (H := A) (K := A ⊔ Q) le_sup_left hcardle
      have hle : Q ≤ A ⊔ Q := le_sup_right
      rwa [← heq] at hle
  exact hodd (by rw [hq]; exact dvd_pow_self 2 (by omega : k - m ≠ 0))

private theorem isSylowTwoOf_inf_of_complement {L L' Q A : Subgroup G} [Finite ↥L]
    (hL : L = L' ⊔ Q) (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hA : IsSylowTwoOf A L)
    (hQ2 : IsPGroup 2 Q) : IsSylowTwoOf (A ⊓ L') L' := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hQL : Q ≤ L := by rw [hL]; exact le_sup_right
  have hQA : Q ≤ A := le_sylow_of_normal hA hQL hQn hQ2
  have hL'Qn : L' ≤ Subgroup.normalizer (Q : Set G) := hL'L.trans hQn
  haveI hQsubN : (Q.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQn
  let mkL : ↥L →* (↥L ⧸ Q.subgroupOf L) := QuotientGroup.mk' (Q.subgroupOf L)
  let inc : ↥L' →* ↥L := Subgroup.inclusion hL'L
  let g : ↥L' →* (↥L ⧸ Q.subgroupOf L) := mkL.comp inc
  have hgker : g.ker = (L' ⊓ Q).subgroupOf L' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : ((inc x : ↥L) : G) ∈ Q := by
        have heq : (QuotientGroup.mk' (Q.subgroupOf L)) (inc x) = 1 := by
          simpa [g, mkL] using hx
        exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (inc x)).mp heq)
      exact ⟨x.2, hx'⟩
    · rintro ⟨-, hxQ⟩
      have hgx : g x = mkL (inc x) := rfl
      rw [hgx]
      exact (QuotientGroup.eq_one_iff (inc x)).mpr
        (Subgroup.mem_subgroupOf.mpr hxQ)
  have hker_le : g.ker ≤ A.subgroupOf L' := by
    rw [hgker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hQA hx.2
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf L) y
    have hxmem : (x : G) ∈ L' ⊔ Q := by rw [← hL]; exact x.2
    obtain ⟨l, hl, q, hq, hxeq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hL'Qn).mp hxmem
    refine ⟨⟨l, hl⟩, ?_⟩
    show mkL (inc ⟨l, hl⟩) = mkL x
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((inc ⟨l, hl⟩ : ↥L) : G) = l := rfl
    have h2 : ((x : ↥L) : G) = l * q := hxeq
    have hcoe : (((inc ⟨l, hl⟩ / x : ↥L)) : G) = l * q⁻¹ * l⁻¹ := by
      simp [h1, h2, div_eq_mul_inv, mul_assoc]
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp (hQn (hL'L hl)) (q⁻¹)).mp (Q.inv_mem hq)
  have hmapA' : ((A.subgroupOf L').map g) = (A.subgroupOf L).map mkL := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨inc x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ A ⊓ (L' ⊔ Q) := by rw [← hL]; exact ⟨hx, x.2⟩
      have hmod : A ⊓ (L' ⊔ Q) = (A ⊓ L') ⊔ Q :=
        (Subgroup.inf_sup_assoc_of_le hL'Qn hQA).symm
      have hx'' : (x : G) ∈ (A ⊓ L') ⊔ Q := by rwa [hmod] at hx'
      have hA'Qn : A ⊓ L' ≤ Subgroup.normalizer (Q : Set G) :=
        (inf_le_left.trans hA.1).trans hQn
      obtain ⟨a, ha, q, hq, hxaq⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hA'Qn).mp hx''
      obtain ⟨haA, haL⟩ := Subgroup.mem_inf.mp ha
      refine ⟨⟨a, haL⟩, haA, ?_⟩
      show mkL (inc ⟨a, haL⟩) = mkL x
      refine (QuotientGroup.eq_iff_div_mem).mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((inc ⟨a, haL⟩ : ↥L) : G) = a := rfl
      have h2 : ((x : ↥L) : G) = a * q := hxaq
      have hcoe : (((inc ⟨a, haL⟩ / x : ↥L)) : G) = a * q⁻¹ * a⁻¹ := by
        simp [h1, h2, div_eq_mul_inv, mul_assoc]
      rw [hcoe]
      exact (Subgroup.mem_normalizer_iff.mp (hQn (hL'L haL)) (q⁻¹)).mp (Q.inv_mem hq)
  have hcard1 : ((A.subgroupOf L).map mkL).index = (A.subgroupOf L).index :=
    Subgroup.index_map_eq (A.subgroupOf L) (QuotientGroup.mk'_surjective (Q.subgroupOf L)) (by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_mono L hQA)
  have hcard2 : ((A.subgroupOf L').map g).index = (A.subgroupOf L').index :=
    Subgroup.index_map_eq (A.subgroupOf L') hgsurj hker_le
  have hsubeq : (A ⊓ L').subgroupOf L' = A.subgroupOf L' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hidx : (A ⊓ L').relIndex L' = A.relIndex L := by
    rw [show (A ⊓ L').relIndex L' = ((A ⊓ L').subgroupOf L').index from rfl, hsubeq,
        ← hcard2, hmapA', hcard1]
    rfl
  refine ⟨inf_le_right, hA.2.1.to_le inf_le_left, ?_⟩
  change ¬ 2 ∣ (A ⊓ L').relIndex L'
  rw [hidx]
  exact hA.2.2

private theorem index_of_complement {L L' E Z W Q : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z) :
    (⊥ : Subgroup G).relIndex W = 2 ^ (2 * n) := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hWL' : W ≤ L' := (hW ▸ (le_sup_left : W ≤ W ⊔ Z)).trans h.E_le
  have hZL' : Z ≤ L' := h.Z_le.trans h.E_le
  haveI : Finite ↥L' :=
    Finite.of_injective (Subgroup.inclusion hL'L) (Subgroup.inclusion_injective hL'L)
  haveI : Finite ↥W :=
    Finite.of_injective (Subgroup.inclusion hWL') (Subgroup.inclusion_injective hWL')
  haveI : Finite ↥Z :=
    Finite.of_injective (Subgroup.inclusion hZL') (Subgroup.inclusion_injective hZL')
  rw [Subgroup.relIndex_bot_left]
  have hZC : Z ≤ Subgroup.centralizer (W : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hZ z hz w (hWL' hw)).symm
  have hZW := hZC.trans (Subgroup.centralizer_le_normalizer (W : Set G))
  have hcard := card_eq_relIndex_of_isComplement hWZ hZW
  rw [hW] at hcard
  rw [hcard, h.index]

private theorem sylow_eq_inf_sup {L L' Q A : Subgroup G} [Finite ↥L]
    (hL : L = L' ⊔ Q) (hQn : L ≤ Subgroup.normalizer (Q : Set G))
    (hA : IsSylowTwoOf A L) (hQ2 : IsPGroup 2 Q) :
    A = (A ⊓ L') ⊔ Q := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hQL : Q ≤ L := by rw [hL]; exact le_sup_right
  have hQA : Q ≤ A := le_sylow_of_normal hA hQL hQn hQ2
  have hL'Qn : L' ≤ Subgroup.normalizer (Q : Set G) := hL'L.trans hQn
  have h := Subgroup.inf_sup_assoc_of_le (H := L') (K := A) (N := Q) hL'Qn hQA
  rw [← hL, inf_eq_left.mpr hA.1] at h
  exact h.symm

private theorem commutator_mem_of_le_normalizer {W L A : Subgroup G}
    (hWL : W ≤ L) (hAL : A ≤ L) (hWn : L ≤ Subgroup.normalizer (W : Set G)) :
    ∀ w ∈ W, ∀ a ∈ A, ⁅w, a⁆ ∈ W := by
  intro w hw a ha
  have hainv : a⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normalizer (W : Set G)).inv_mem (hWn (hAL ha))
  have h1 : a⁻¹ * w * a ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp hainv w).mp hw
    simpa using h
  have h2 : a⁻¹ * ⁅w, a⁆ * a ∈ W := by
    have heq : a⁻¹ * ⁅w, a⁆ * a = (a⁻¹ * w * a) * w⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact W.mul_mem h1 (W.inv_mem hw)
  have h3 : a * (a⁻¹ * ⁅w, a⁆ * a) * a⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hWn (hAL ha)) _).mp h2
  have h4 : a * (a⁻¹ * ⁅w, a⁆ * a) * a⁻¹ = ⁅w, a⁆ := by group
  rwa [h4] at h3

private theorem relCent_eq_inf {L L' E Z W Q A : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q) (hQ2 : IsPGroup 2 Q)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hEQ : E ≤ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q)
    (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z)
    (hA : IsSylowTwoOf A L) :
    relCent W ⊥ A = W ⊓ relCent E Z (A ⊓ L') := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hEL' : E ≤ L' := h.E_le
  have hWE : W ≤ E := by rw [← hW]; exact le_sup_left
  have hWL : W ≤ L := hWE.trans (hEL'.trans hL'L)
  have hEZn : E ≤ Subgroup.normalizer (Z : Set G) :=
    hEL'.trans (fun x hx => (h.normal hx).2)
  have hWN : W ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hNW := commutator_mem_of_le_normalizer hWL hA.1 hWn
  have hAeq : A = (A ⊓ L') ⊔ Q := sylow_eq_inf_sup hL hQn hA hQ2
  have hA'Qn : A ⊓ L' ≤ Subgroup.normalizer (Q : Set G) :=
    ((inf_le_right : A ⊓ L' ≤ L')).trans (hL'L.trans hQn)
  ext x
  constructor
  · intro hx
    obtain ⟨hxW, hxcomm⟩ := (mem_relCent hWN).mp hx
    refine Subgroup.mem_inf.mpr ⟨hxW, (mem_relCent hEZn).mpr ⟨hWE hxW, ?_⟩⟩
    intro a' ha'
    have hxbot : ⁅x, a'⁆ ∈ (⊥ : Subgroup G) :=
      hxcomm a' ((inf_le_left : A ⊓ L' ≤ A) ha')
    rw [Subgroup.mem_bot] at hxbot
    rw [hxbot]
    exact Z.one_mem
  · intro hx
    obtain ⟨hxW, hxX⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨-, hxcomm⟩ := (mem_relCent hEZn).mp hxX
    refine (mem_relCent hWN).mpr ⟨hxW, fun a ha => ?_⟩
    have ha_mem : a ∈ (A ⊓ L') ⊔ Q := by
      rw [← hAeq]
      exact ha
    obtain ⟨a', ha'_mem, q, hq, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hA'Qn).mp ha_mem
    have hcommq : ⁅x, q⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hQW q hq x hxW).symm
    have hxa : ⁅x, a' * q⁆ = ⁅x, a'⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hcommq, mul_one, mul_inv_cancel_right]
    rw [hxa]
    have hxa'W : ⁅x, a'⁆ ∈ W := hNW x hxW a' ((inf_le_left : A ⊓ L' ≤ A) ha'_mem)
    have hxa'Z : ⁅x, a'⁆ ∈ Z := hxcomm a' ha'_mem
    have hmem : ⁅x, a'⁆ ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨hxa'W, hxa'Z⟩
    rw [hWZ] at hmem
    exact hmem

private theorem relCent_eq_sup {L L' E Z W Q A' : Subgroup G} {n : ℕ}
    (h : NatQuot L' E Z n) (hEQ : E ≤ Q) (hW : W ⊔ Z = E)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q)
    (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z)
    (hA' : A' ≤ L') :
    relCent E Z A' = (W ⊓ relCent E Z A') ⊔ Z := by
  have hEZn : E ≤ Subgroup.normalizer (Z : Set G) :=
    h.E_le.trans (fun x hx => (h.normal hx).2)
  have hZWn : Z ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro z hz w hw
    have hzQ : z ∈ Q := hEQ (h.Z_le hz)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hQW z hzQ w hw)]
    exact W.one_mem
  have hZX : Z ≤ relCent E Z A' := by
    intro z hz
    rw [mem_relCent hEZn]
    refine ⟨h.Z_le hz, fun a ha => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZ z hz a (hA' ha))]
    exact Z.one_mem
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, -⟩ := (mem_relCent hEZn).mp hx
    have hxE' : x ∈ Z ⊔ W := by rw [sup_comm, hW]; exact hxE
    obtain ⟨z, hz, w, hw, hxzw⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZWn).mp hxE'
    have hzX : z ∈ relCent E Z A' := hZX hz
    have hwX : w ∈ relCent E Z A' := by
      have hw_eq : w = z⁻¹ * x := by rw [hxzw]; group
      rw [hw_eq]
      exact (relCent E Z A').mul_mem ((relCent E Z A').inv_mem hzX) hx
    rw [hxzw, sup_comm]
    exact Subgroup.mul_mem_sup hz (Subgroup.mem_inf.mpr ⟨hw, hwX⟩)
  · exact sup_le inf_le_right hZX

private theorem line_of_complement {L L' E Z W Q A : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q) (hQ2 : IsPGroup 2 Q)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hEQ : E ≤ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q)
    (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z)
    (hA : IsSylowTwoOf A L) :
    (⊥ : Subgroup G).relIndex (relCent W ⊥ A) = 2 ^ n := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hEL' : E ≤ L' := h.E_le
  have hZL' : Z ≤ L' := h.Z_le.trans hEL'
  have hWE : W ≤ E := by rw [← hW]; exact le_sup_left
  have hWL : W ≤ L := hWE.trans (hEL'.trans hL'L)
  have hEZn : E ≤ Subgroup.normalizer (Z : Set G) :=
    hEL'.trans (fun x hx => (h.normal hx).2)
  have hA' : IsSylowTwoOf (A ⊓ L') L' := isSylowTwoOf_inf_of_complement hL hQn hA hQ2
  have hrel : relCent W ⊥ A = W ⊓ relCent E Z (A ⊓ L') :=
    relCent_eq_inf h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA
  have hsup : relCent E Z (A ⊓ L') = (W ⊓ relCent E Z (A ⊓ L')) ⊔ Z :=
    relCent_eq_sup (L := L) (Q := Q) h hEQ hW hQW hZ (inf_le_right : A ⊓ L' ≤ L')
  have hline : Z.relIndex (relCent E Z (A ⊓ L')) = 2 ^ n := h.line (A ⊓ L') hA'
  have hXleE : relCent E Z (A ⊓ L') ≤ E := fun x hx => ((mem_relCent hEZn).mp hx).1
  haveI hfinL' : Finite ↥L' :=
    Finite.of_injective (Subgroup.inclusion hL'L) (Subgroup.inclusion_injective hL'L)
  haveI hfinZ : Finite ↥Z :=
    Finite.of_injective (Subgroup.inclusion (hZL'.trans hL'L))
      (Subgroup.inclusion_injective (hZL'.trans hL'L))
  haveI hfinW : Finite ↥W :=
    Finite.of_injective (Subgroup.inclusion hWL) (Subgroup.inclusion_injective hWL)
  haveI hfinX : Finite ↥(relCent E Z (A ⊓ L')) :=
    Finite.of_injective (Subgroup.inclusion (hXleE.trans (hEL'.trans hL'L)))
      (Subgroup.inclusion_injective (hXleE.trans (hEL'.trans hL'L)))
  haveI hfinA0 : Finite ↥(W ⊓ relCent E Z (A ⊓ L')) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans hWL))
      (Subgroup.inclusion_injective (inf_le_left.trans hWL))
  have hAZ : Z ⊓ (W ⊓ relCent E Z (A ⊓ L')) = ⊥ := by
    rw [inf_comm]
    apply le_bot_iff.mp
    exact (le_inf ((inf_le_left : (W ⊓ relCent E Z (A ⊓ L')) ⊓ Z ≤
      W ⊓ relCent E Z (A ⊓ L')).trans inf_le_left) inf_le_right).trans hWZ.le
  have hAn : W ⊓ relCent E Z (A ⊓ L') ≤ Subgroup.normalizer (Z : Set G) :=
    (inf_le_left.trans (hWE.trans hEL')).trans (fun x hx => (h.normal hx).2)
  have hcardsup : Nat.card ↥Z =
      (W ⊓ relCent E Z (A ⊓ L')).relIndex (Z ⊔ (W ⊓ relCent E Z (A ⊓ L'))) :=
    card_eq_relIndex_of_isComplement (X := Z) (Z := W ⊓ relCent E Z (A ⊓ L')) hAZ hAn
  have hZX : Z ≤ relCent E Z (A ⊓ L') := by
    intro z hz
    rw [mem_relCent hEZn]
    refine ⟨h.Z_le hz, fun a ha => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (hZ z hz a ((inf_le_right : A ⊓ L' ≤ L') ha))]
    exact Z.one_mem
  have hsupZ : Z ⊔ (W ⊓ relCent E Z (A ⊓ L')) = relCent E Z (A ⊓ L') := by
    rw [sup_comm]
    exact hsup.symm
  have hcardsup' : Nat.card ↥Z = (W ⊓ relCent E Z (A ⊓ L')).relIndex
      (relCent E Z (A ⊓ L')) := by
    have h := hcardsup
    rw [hsupZ] at h
    exact h
  have hcardX : Nat.card ↥(relCent E Z (A ⊓ L')) =
      Nat.card ↥Z * Nat.card ↥(W ⊓ relCent E Z (A ⊓ L')) := by
    have h1 := Subgroup.relIndex_mul_card (H := W ⊓ relCent E Z (A ⊓ L'))
      (K := relCent E Z (A ⊓ L'))
    rw [inf_eq_left.mpr (inf_le_right : W ⊓ relCent E Z (A ⊓ L') ≤
      relCent E Z (A ⊓ L')), ← hcardsup'] at h1
    exact h1.symm
  have hcardZ : 2 ^ n * Nat.card ↥Z = Nat.card ↥(relCent E Z (A ⊓ L')) := by
    have h1 := Subgroup.relIndex_mul_card (H := Z) (K := relCent E Z (A ⊓ L'))
    rw [inf_eq_left.mpr hZX, hline] at h1
    exact h1
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hfinal : Nat.card ↥(W ⊓ relCent E Z (A ⊓ L')) = 2 ^ n := by
    apply Nat.mul_left_cancel hZpos
    rw [← hcardX, mul_comm (Nat.card ↥Z) (2 ^ n)]
    exact hcardZ.symm
  rw [hrel, Subgroup.relIndex_bot_left, hfinal]

private theorem commutator_eq_relCent {L L' E Z W Q A : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q) (hQ2 : IsPGroup 2 Q)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hEQ : E ≤ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q)
    (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z)
    (hA : IsSylowTwoOf A L) :
    ⁅W, A⁆ ⊔ ⊥ = relCent W ⊥ A := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hEL' : E ≤ L' := h.E_le
  have hWE : W ≤ E := by rw [← hW]; exact le_sup_left
  have hWL : W ≤ L := hWE.trans (hEL'.trans hL'L)
  have hEZn : E ≤ Subgroup.normalizer (Z : Set G) :=
    hEL'.trans (fun x hx => (h.normal hx).2)
  have hZWn : Z ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro z hz w hw
    have hzQ : z ∈ Q := hEQ (h.Z_le hz)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hQW z hzQ w hw)]
    exact W.one_mem
  have hNW := commutator_mem_of_le_normalizer hWL hA.1 hWn
  have hA' : IsSylowTwoOf (A ⊓ L') L' := isSylowTwoOf_inf_of_complement hL hQn hA hQ2
  have hA'Qn : A ⊓ L' ≤ Subgroup.normalizer (Q : Set G) :=
    ((inf_le_right : A ⊓ L' ≤ L')).trans (hL'L.trans hQn)
  have hEA' : ⁅E, A ⊓ L'⁆ = ⁅W, A ⊓ L'⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro e he a ha
      have he' : e ∈ Z ⊔ W := by rw [sup_comm, hW]; exact he
      obtain ⟨z, hz, w, hw, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZWn).mp he'
      have hza : z * a = a * z := hZ z hz a ((inf_le_right : A ⊓ L' ≤ L') ha)
      have h1 : ⁅z * w, a⁆ = z * ⁅w, a⁆ * z⁻¹ := by
        rw [commutatorElement_mul_left_eq_conj_mul,
          Commute.commutator_eq ((commute_iff_eq z a).mpr hza), mul_one]
      rw [h1]
      have h2 : z * ⁅w, a⁆ * z⁻¹ = ⁅z * w * z⁻¹, a⁆ := by
        rw [conjugate_commutatorElement, show z * a * z⁻¹ = a by rw [hza]; group]
      rw [h2]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hZWn hz) w).mp hw) ha
    · exact Subgroup.commutator_mono_left hWE
  have hWA : ⁅W, A⁆ = ⁅W, A ⊓ L'⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro w hw a ha
      have ha_mem : a ∈ (A ⊓ L') ⊔ Q := by
        rw [← sylow_eq_inf_sup hL hQn hA hQ2]
        exact ha
      obtain ⟨a', ha'_mem, q, hq, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hA'Qn).mp ha_mem
      have hcommq : ⁅w, q⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hQW q hq w hw).symm
      have hcomm : ⁅w, a' * q⁆ = ⁅w, a'⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj, hcommq, mul_one, mul_inv_cancel_right]
      rw [hcomm]
      exact Subgroup.commutator_mem_commutator hw ha'_mem
    · exact Subgroup.commutator_mono_right inf_le_left
  have hKleW : ⁅W, A ⊓ L'⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro w hw a ha
    exact hNW w hw a ((inf_le_left : A ⊓ L' ≤ A) ha)
  have hKL' : ⁅W, A ⊓ L'⁆ ≤ L' :=
    Subgroup.commutator_le_of_le (hWE.trans hEL') (inf_le_right : A ⊓ L' ≤ L')
  have hKZ : ⁅W, A ⊓ L'⁆ ≤ Subgroup.normalizer (Z : Set G) :=
    hKL'.trans (fun x hx => (h.normal hx).2)
  have hXeq : relCent E Z (A ⊓ L') = ⁅W, A ⊓ L'⁆ ⊔ Z := by
    rw [← hEA']
    exact (h.comm_eq (A ⊓ L') hA').symm
  have hinter : W ⊓ relCent E Z (A ⊓ L') = ⁅W, A ⊓ L'⁆ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxW, hxX⟩ := Subgroup.mem_inf.mp hx
      rw [hXeq] at hxX
      obtain ⟨k, hk, z, hz, hxkz⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hKZ).mp hxX
      have hkW : k ∈ W := hKleW hk
      have hzW : z ∈ W := by
        have hz_eq : z = k⁻¹ * x := by rw [hxkz]; group
        rw [hz_eq]
        exact W.mul_mem (W.inv_mem hkW) hxW
      have hzbot : z ∈ (⊥ : Subgroup G) := by
        have hmem : z ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨hzW, hz⟩
        rwa [hWZ] at hmem
      rw [hxkz, Subgroup.mem_bot.mp hzbot, mul_one]
      exact hk
    · rw [hXeq]
      exact le_inf hKleW le_sup_left
  have hrel := relCent_eq_inf h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA
  rw [hWA, sup_bot_eq, hrel, hinter]

private theorem lines_inf_of_complement {L L' E Z W Q A B : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q) (hQ2 : IsPGroup 2 Q)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hEQ : E ≤ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q)
    (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z)
    (hA : IsSylowTwoOf A L) (hB : IsSylowTwoOf B L)
    (hnot : ¬ A ≤ B ⊔ W) :
    relCent W ⊥ A ⊓ relCent W ⊥ B = ⊥ ∧
      relCent W ⊥ A ⊔ relCent W ⊥ B = W := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hQL : Q ≤ L := by rw [hL]; exact le_sup_right
  have hEL' : E ≤ L' := h.E_le
  have hWE : W ≤ E := by rw [← hW]; exact le_sup_left
  have hWL : W ≤ L := hWE.trans (hEL'.trans hL'L)
  have hA' : IsSylowTwoOf (A ⊓ L') L' := isSylowTwoOf_inf_of_complement hL hQn hA hQ2
  have hB' : IsSylowTwoOf (B ⊓ L') L' := isSylowTwoOf_inf_of_complement hL hQn hB hQ2
  have hQB : Q ≤ B := le_sylow_of_normal hB hQL hQn hQ2
  have hAeq : A = (A ⊓ L') ⊔ Q := sylow_eq_inf_sup hL hQn hA hQ2
  have hnot' : ¬ (A ⊓ L') ≤ (B ⊓ L') ⊔ E := by
    intro hle
    apply hnot
    have hAleB : A ⊓ L' ≤ B := hle.trans (sup_le inf_le_left (hEQ.trans hQB))
    rw [hAeq]
    exact sup_le (hAleB.trans le_sup_left) (hQB.trans le_sup_left)
  obtain ⟨hinf, hsup⟩ := h.lines_inf (A ⊓ L') (B ⊓ L') hA' hB' hnot'
  have hrelA := relCent_eq_inf h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA
  have hrelB := relCent_eq_inf h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hB
  have hinter : relCent W ⊥ A ⊓ relCent W ⊥ B = ⊥ := by
    rw [hrelA, hrelB]
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxW1, hxX1⟩ := Subgroup.mem_inf.mp hx1
    obtain ⟨-, hxX2⟩ := Subgroup.mem_inf.mp hx2
    have hxX : x ∈ relCent E Z (A ⊓ L') ⊓ relCent E Z (B ⊓ L') :=
      Subgroup.mem_inf.mpr ⟨hxX1, hxX2⟩
    rw [hinf] at hxX
    have hmem : x ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨hxW1, hxX⟩
    rwa [hWZ] at hmem
  refine ⟨hinter, ?_⟩
  have hcardA : Nat.card ↥(relCent W ⊥ A) = 2 ^ n := by
    have hline := line_of_complement h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA
    rwa [Subgroup.relIndex_bot_left] at hline
  have hcardB : Nat.card ↥(relCent W ⊥ B) = 2 ^ n := by
    have hline := line_of_complement h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hB
    rwa [Subgroup.relIndex_bot_left] at hline
  have hcardW : Nat.card ↥W = 2 ^ (2 * n) := by
    have hindex := index_of_complement h hL hW hWZ hZ
    rwa [Subgroup.relIndex_bot_left] at hindex
  have hcardYA : Nat.card ↥(W ⊓ relCent E Z (A ⊓ L')) = 2 ^ n := by
    rw [← hrelA]
    exact hcardA
  have hcardYB : Nat.card ↥(W ⊓ relCent E Z (B ⊓ L')) = 2 ^ n := by
    rw [← hrelB]
    exact hcardB
  have hcommW : ∀ a ∈ W ⊓ relCent E Z (A ⊓ L'),
      ∀ b ∈ W ⊓ relCent E Z (B ⊓ L'), a * b = b * a := by
    intro a ha b hb
    have haW : a ∈ W := (Subgroup.mem_inf.mp ha).1
    have hbW : b ∈ W := (Subgroup.mem_inf.mp hb).1
    exact hQW a (hEQ (hWE haW)) b hbW
  have hAn : W ⊓ relCent E Z (B ⊓ L') ≤
      Subgroup.normalizer ((W ⊓ relCent E Z (A ⊓ L')) : Set G) := by
    have hcent : W ⊓ relCent E Z (B ⊓ L') ≤
        Subgroup.centralizer ((W ⊓ relCent E Z (A ⊓ L')) : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcommW a ha b hb
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hYinf : W ⊓ relCent E Z (A ⊓ L') ⊓ (W ⊓ relCent E Z (B ⊓ L')) = ⊥ := by
    rw [← hrelA, ← hrelB]
    exact hinter
  have hcardSup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (W ⊓ relCent E Z (A ⊓ L')) (W ⊓ relCent E Z (B ⊓ L')) hAn
    (disjoint_iff.mpr hYinf)
  have hcardSupY : Nat.card ↥((W ⊓ relCent E Z (A ⊓ L')) ⊔
      (W ⊓ relCent E Z (B ⊓ L'))) = 2 ^ (2 * n) := by
    rw [hcardSup, hcardYA, hcardYB, ← pow_add, two_mul]
  haveI hfinW : Finite ↥W :=
    Finite.of_injective (Subgroup.inclusion hWL) (Subgroup.inclusion_injective hWL)
  have hleW : (W ⊓ relCent E Z (A ⊓ L')) ⊔ (W ⊓ relCent E Z (B ⊓ L')) ≤ W :=
    sup_le inf_le_left inf_le_left
  have hcardle : Nat.card ↥W ≤ Nat.card ↥((W ⊓ relCent E Z (A ⊓ L')) ⊔
      (W ⊓ relCent E Z (B ⊓ L'))) := by
    rw [hcardW, hcardSupY]
  have hsupW : (W ⊓ relCent E Z (A ⊓ L')) ⊔ (W ⊓ relCent E Z (B ⊓ L')) = W :=
    Subgroup.eq_of_le_of_card_ge hleW hcardle
  rw [hrelA, hrelB]
  exact hsupW

private theorem fpf_of_complement {L L' E Z W Q : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q) (hQ2 : IsPGroup 2 Q)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hEQ : E ≤ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q) :
    ∀ g ∈ L, Odd (orderOf g) → g ∉ W →
      ∀ (e : G), e ∈ W → ⁅e, g⁆ ∈ (⊥ : Subgroup G) → e ∈ (⊥ : Subgroup G) := by
  intro g hgL hodd hgW e heW hcomm
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hQL : Q ≤ L := by rw [hL]; exact le_sup_right
  have hL'Qn : L' ≤ Subgroup.normalizer (Q : Set G) := hL'L.trans hQn
  have hWE : W ≤ E := by rw [← hW]; exact le_sup_left
  have hgQ : g ∉ Q := by
    intro hgQ
    have h1 : g = 1 := by
      have hodd' : Odd (orderOf (⟨g, hgQ⟩ : ↥Q)) := by
        rw [Subgroup.orderOf_mk]
        exact hodd
      have h := CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd hQ2 hodd'
        (pow_orderOf_eq_one (⟨g, hgQ⟩ : ↥Q))
      exact Subtype.ext_iff.mp h
    exact hgW (by rw [h1]; exact W.one_mem)
  obtain ⟨l, hlL', q, hq, hg_eq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hL'Qn).mp
      (by rw [← hL]; exact hgL)
  have hlL : l ∈ L := hL'L hlL'
  have hqL : q ∈ L := hQL hq
  let NQ : Subgroup ↥L := Q.subgroupOf L
  haveI hNQ : NQ.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQn
  let π : ↥L →* (↥L ⧸ NQ) := QuotientGroup.mk' NQ
  let lL : ↥L := ⟨l, hlL⟩
  let gL : ↥L := ⟨g, hgL⟩
  let qL : ↥L := ⟨q, hqL⟩
  have hgL_eq : gL = lL * qL := Subtype.ext hg_eq
  have hqN : qL ∈ NQ := Subgroup.mem_subgroupOf.mpr hq
  have hπq : π qL = 1 := (QuotientGroup.eq_one_iff (N := NQ) qL).mpr hqN
  have hπl : π lL = π gL := by
    rw [hgL_eq, map_mul, hπq, mul_one]
  have hk_ne : orderOf l ≠ 0 := by
    have hfin : IsOfFinOrder lL := isOfFinOrder_of_finite lL
    have hpos := hfin.orderOf_pos
    rw [Subgroup.orderOf_mk l hlL] at hpos
    exact hpos.ne'
  set s : ℕ := (orderOf l).factorization 2 with hs
  set m : ℕ := ordCompl[2] (orderOf l) with hm
  have hkm : 2 ^ s * m = orderOf l := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (orderOf l) 2
    simpa [s, m] using h
  have hm_odd : Odd m := by
    have hcop : Nat.Coprime 2 m := by
      rw [hm]
      exact Nat.coprime_ordCompl Nat.prime_two hk_ne
    exact Nat.coprime_two_left.mp hcop
  have hpowdvd : 2 ^ s ∣ orderOf l := by
    rw [← hkm]
    exact dvd_mul_right (2 ^ s) m
  have hord : orderOf (l ^ 2 ^ s) = m := by
    rw [orderOf_pow_of_dvd (x := l) (n := 2 ^ s) (by positivity) hpowdvd, ← hkm,
      Nat.mul_div_cancel_left m (by positivity)]
  have hodd2s : Odd (orderOf (l ^ 2 ^ s)) := by
    rw [hord]
    exact hm_odd
  have hNpos : 0 < orderOf g := by
    have hfin : IsOfFinOrder gL := isOfFinOrder_of_finite gL
    have hpos := hfin.orderOf_pos
    rwa [Subgroup.orderOf_mk g hgL] at hpos
  have hNne1 : orderOf g ≠ 1 := by
    intro h1
    exact hgW (by rw [orderOf_eq_one_iff.mp h1]; exact W.one_mem)
  have hN1 : 1 < orderOf g := by omega
  have hcopN : Nat.Coprime (2 ^ s) (orderOf g) :=
    Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hodd)
  obtain ⟨β, -, hβ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopN hN1
  have hl3_odd : Odd (orderOf (l ^ (2 ^ s * β))) := by
    have h2 : l ^ (2 ^ s * β) = (l ^ 2 ^ s) ^ β := by rw [pow_mul]
    rw [h2]
    exact hodd2s.of_dvd_nat (orderOf_pow_dvd (x := l ^ 2 ^ s) β)
  have hdvd : orderOf (π lL) ∣ orderOf g := by
    rw [hπl]
    have hmap := orderOf_map_dvd π gL
    rwa [Subgroup.orderOf_mk g hgL] at hmap
  have hcN : 2 ^ s * β ≡ 1 [MOD orderOf g] := by
    rw [Nat.ModEq, hβ, Nat.mod_eq_of_lt hN1]
  have hcmod : 2 ^ s * β ≡ 1 [MOD orderOf (π lL)] :=
    Nat.ModEq.of_dvd hdvd hcN
  have hpow : (π lL) ^ (2 ^ s * β) = π lL := by
    have h := (pow_eq_pow_iff_modEq (x := π lL) (n := 2 ^ s * β) (m := 1)).mpr hcmod
    simpa using h
  have hl3L' : l ^ (2 ^ s * β) ∈ L' := L'.pow_mem hlL' _
  have hl3L : l ^ (2 ^ s * β) ∈ L := hL'L hl3L'
  have hπl3 : π (⟨l ^ (2 ^ s * β), hl3L⟩ : ↥L) = π lL := by
    have h1 : (⟨l ^ (2 ^ s * β), hl3L⟩ : ↥L) = lL ^ (2 ^ s * β) := Subtype.ext rfl
    rw [h1, map_pow, hpow]
  obtain ⟨zL, hzN, hlLz⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := NQ)).mp hπl3.symm
  let z : G := zL
  have hzQ : z ∈ Q := Subgroup.mem_subgroupOf.mp hzN
  have hl3_eq : l ^ (2 ^ s * β) = l * z := by
    have h := congrArg Subtype.val hlLz
    simp only [Subgroup.coe_mul, Subgroup.coe_mk] at h
    exact h.symm
  have hl3_notE : l ^ (2 ^ s * β) ∉ E := by
    intro hl3E
    have hl3Q : l ^ (2 ^ s * β) ∈ Q := hEQ hl3E
    have hl3one : l ^ (2 ^ s * β) = 1 := by
      have hodd' : Odd (orderOf (⟨l ^ (2 ^ s * β), hl3Q⟩ : ↥Q)) := by
        rw [Subgroup.orderOf_mk]
        exact hl3_odd
      have h := CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd hQ2 hodd'
        (pow_orderOf_eq_one (⟨l ^ (2 ^ s * β), hl3Q⟩ : ↥Q))
      exact Subtype.ext_iff.mp h
    have hlQ : l ∈ Q := by
      have hl_eq : l = l ^ (2 ^ s * β) * z⁻¹ := by rw [hl3_eq]; group
      rw [hl_eq]
      exact Q.mul_mem (by rw [hl3one]; exact Q.one_mem) (Q.inv_mem hzQ)
    exact hgQ (by rw [hg_eq]; exact Q.mul_mem hlQ hq)
  have heg : e * g = g * e :=
    commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hcomm)
  have heq : e * q = q * e := (hQW q hq e heW).symm
  have hel : e * l = l * e := by
    have hcl : Commute e g := (commute_iff_eq e g).mpr heg
    have hcq : Commute e q := (commute_iff_eq e q).mpr heq
    have hl_eq : l = g * q⁻¹ := by rw [hg_eq]; group
    rw [hl_eq]
    exact (hcl.mul_right hcq.inv_right).eq
  have hel3 : e * (l ^ (2 ^ s * β)) = l ^ (2 ^ s * β) * e := by
    have hcl : Commute e l := (commute_iff_eq e l).mpr hel
    have hcz : Commute e z := (commute_iff_eq e z).mpr (hQW z hzQ e heW).symm
    rw [hl3_eq]
    exact (hcl.mul_right hcz).eq
  have hcommZ : ⁅e, l ^ (2 ^ s * β)⁆ ∈ Z := by
    rw [Commute.commutator_eq ((commute_iff_eq e (l ^ (2 ^ s * β))).mpr hel3)]
    exact Z.one_mem
  have heE : e ∈ E := hWE heW
  have heZ : e ∈ Z :=
    h.fpf (l ^ (2 ^ s * β)) hl3L' hl3_odd hl3_notE e heE hcommZ
  have hmem : e ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨heW, heZ⟩
  rwa [hWZ] at hmem

private theorem irred_of_complement {L L' E Z W Q : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥)
    (A : Subgroup G) (hAW : A ≤ W) (hAn : L ≤ Subgroup.normalizer (A : Set G)) :
    A = ⊥ ∨ A = W := by
  have hL'L : L' ≤ L := by rw [hL]; exact le_sup_left
  have hWE : W ≤ E := by rw [← hW]; exact le_sup_left
  have hAZ : Z ≤ A ⊔ Z := le_sup_right
  have hALE : A ⊔ Z ≤ E := sup_le (hAW.trans hWE) h.Z_le
  have hL'n : L' ≤ Subgroup.normalizer ((A ⊔ Z : Subgroup G) : Set G) :=
    CFSG.Quasithin.F1.le_normalizer_sup (hL'L.trans hAn) (fun x hx => (h.normal hx).2)
  rcases h.irred (A ⊔ Z) hAZ hALE hL'n with hAZeq | hAZeq
  · left
    have hAZ_le : A ≤ Z := hAZeq ▸ le_sup_left
    apply le_bot_iff.mp
    intro x hx
    have hxW : x ∈ W := hAW hx
    have hxZ : x ∈ Z := hAZ_le hx
    have hmem : x ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨hxW, hxZ⟩
    rwa [hWZ] at hmem
  · right
    have hZA : Z ≤ Subgroup.normalizer (A : Set G) :=
      h.Z_le.trans (h.E_le.trans (hL'L.trans hAn))
    have hded := Subgroup.inf_sup_assoc_of_le (H := Z) (K := W) (N := A) hZA hAW
    have hZAeq : Z ⊔ A = E := by rw [sup_comm]; exact hAZeq
    rw [hWZ, bot_sup_eq, hZAeq, inf_eq_left.mpr hWE] at hded
    exact hded

theorem NatQuot.of_complement {L L' E Z W Q : Subgroup G} {n : ℕ} [Finite ↥L]
    (h : NatQuot L' E Z n) (hL : L = L' ⊔ Q) (hQ2 : IsPGroup 2 Q)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hEQ : E ≤ Q)
    (hW : W ⊔ Z = E) (hWZ : W ⊓ Z = ⊥) (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q) (hZ : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z) :
    NatQuot L W ⊥ n where
  Z_le := bot_le
  E_le := (by rw [← hW]; exact le_sup_left : W ≤ E).trans
    (h.E_le.trans (by rw [hL]; exact le_sup_left))
  normal := by
    refine le_inf hWn ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  index := index_of_complement h hL hW hWZ hZ
  line := fun A hA => line_of_complement h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA
  comm_eq := fun A hA => commutator_eq_relCent h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA
  lines_inf := fun A B hA hB hnot =>
    lines_inf_of_complement h hL hQ2 hQn hEQ hW hWZ hWn hQW hZ hA hB hnot
  fpf := fpf_of_complement h hL hQ2 hQn hEQ hW hWZ hQW
  irred := fun A _ hAW hAn => irred_of_complement h hL hW hWZ A hAW hAn

end CFSG.Quasithin.St84
