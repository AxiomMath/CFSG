module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lem96
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

section Helpers

private theorem hessImg_not27 {L X : Subgroup G} (hL9 : (Nat.card L).factorization 3 = 2)
    (hXL : X ≤ L) : ¬ 27 ∣ Nat.card X := by
  intro h27
  have hLne : Nat.card L ≠ 0 := Finite.card_pos.ne'
  have h3 : 3 ^ 3 ∣ Nat.card L := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
    exact h27.trans (Subgroup.card_dvd_of_le hXL)
  have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hLne).mp h3
  omega

private theorem hessImg_card_img {A J S : Subgroup G} [(ker148 A J).Normal]
    (hS : S ≤ J ⊔ A) (hS3 : IsPGroup 3 ↥S) : Nat.card (img148 A J S) = Nat.card S := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (ker148 A J)).comp (S.subgroupOf (J ⊔ A)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have ht' : QuotientGroup.mk' (ker148 A J) (t : ↥(J ⊔ A)) = 1 := ht
    have h1 : ((t : ↥(J ⊔ A)) : G) ∈ CFSG.GH74.GLS.pPrimeCoreOf 3 J :=
      mk'_ker148_eq_one_iff.mp ht'
    have h2 : ((t : ↥(J ⊔ A)) : G) ∈ S := Subgroup.mem_subgroupOf.mp t.2
    have h3 : ((t : ↥(J ⊔ A)) : G) ∈ S ⊓ CFSG.GH74.GLS.pPrimeCoreOf 3 J :=
      Subgroup.mem_inf.mpr ⟨h2, h1⟩
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.inf_pPrimeCoreOf_eq_bot Nat.prime_three hS3] at h3
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp h3))
  have hmap : img148 A J S = (⊤ : Subgroup ↥(S.subgroupOf (J ⊔ A))).map
      ((QuotientGroup.mk' (ker148 A J)).comp (S.subgroupOf (J ⊔ A)).subtype) := by
    ext z
    simp only [img148, Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨x, hx, hxz⟩
      exact ⟨⟨x, hx⟩, hxz⟩
    · rintro ⟨t, htz⟩
      exact ⟨t, t.2, htz⟩
  rw [hmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv

private theorem hessImg_sylow {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : Nat.card P = 9) (h27 : ¬ 27 ∣ Nat.card X) : ∃ S : Sylow 3 X, S.toSubgroup = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (show Nat.card P = 3 ^ 2 by norm_num [hP])
  refine ⟨⟨P, hP3, fun {Q} hQ hPQ => ?_⟩, rfl⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hdQ : Nat.card Q ∣ Nat.card X := Subgroup.card_subgroup_dvd_card Q
  have hPQd : Nat.card P ∣ Nat.card Q := Subgroup.card_dvd_of_le hPQ
  rw [hk, hP] at hPQd
  rw [hk] at hdQ
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have hk3' : 3 ≤ k := by omega
    apply h27
    have h33 : 3 ^ 3 ∣ Nat.card X := (pow_dvd_pow 3 hk3').trans hdQ
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact h33
  have hk1 : 2 ≤ k := by
    by_contra hk1
    have hk1' : k < 2 := by omega
    interval_cases k <;> norm_num at hPQd
  have hkeq : k = 2 := by omega
  refine (Subgroup.eq_of_le_of_card_ge hPQ ?_).symm
  rw [hk, hkeq, hP] <;> norm_num

private theorem hessImg_conj {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hS : Nat.card S = 9) (hB : Nat.card B = 9) (h27 : ¬ 27 ∣ Nat.card X) :
    ∃ g : X, ∀ x : X, x ∈ B ↔ g * x * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (Sylow 3 X) :=
    Finite.of_injective (fun P : Sylow 3 X => (P : Set X)) SetLike.coe_injective
  obtain ⟨P1, hP1⟩ := hessImg_sylow hS h27
  obtain ⟨P2, hP2⟩ := hessImg_sylow hB h27
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P1 P2
  have h1 : ((g • P1 : Sylow 3 X) : Subgroup X) = (P2 : Subgroup X) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, hP1, hP2] at h1
  refine ⟨g⁻¹, fun x => ?_⟩
  rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]

private theorem hessImg_normalizer {Q : Type} [Group Q] {Ka Sa : Subgroup Q}
    (hle : Sa ≤ Ka) {m : Q} (hm : m ∈ Ka)
    (h : ∀ y : ↥Ka, y ∈ Sa.subgroupOf Ka ↔
      (⟨m, hm⟩ : ↥Ka) * y * (⟨m, hm⟩ : ↥Ka)⁻¹ ∈ Sa.subgroupOf Ka) :
    ∀ y : Q, y ∈ Sa ↔ m * y * m⁻¹ ∈ Sa := by
  intro y
  by_cases hy : y ∈ Ka
  · simpa [Subgroup.mem_subgroupOf] using h ⟨y, hy⟩
  · constructor
    · intro hy'
      exact absurd (hle hy') hy
    · intro hmy
      exfalso
      apply hy
      have hmy' : m * y * m⁻¹ ∈ Ka := hle hmy
      have e : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [e]
      exact Ka.mul_mem (Ka.mul_mem (Ka.inv_mem hm) hmy') hm

private theorem hessImg_isElemAbelian {Q : Type} [Group Q] {E : Subgroup Q}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (he : ∀ x ∈ E, x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 E := by
  have hcomm : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  exact (⟨hcomm, he⟩ : IsMulCommutative ↥E ∧ ∀ x ∈ E, x ^ 3 = 1)

private theorem hessImg_final {Q : Type} [Group Q] {M T : Subgroup Q} (hTM : T ≤ M)
    (hcT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (heT : ∀ x ∈ T, x ^ 3 = 1)
    (hT9 : Nat.card T = 9)
    (htr : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ w ∈ M,
      (∀ z : Q, z ∈ T ↔ w * z * w⁻¹ ∈ T) ∧ w * x * w⁻¹ = y) :
    ∃ E : Subgroup ↥M, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set ↥M), w * y₀ * w⁻¹ = y₁) ∧
      E.map M.subtype = T := by
  refine ⟨T.subgroupOf M,
    hessImg_isElemAbelian
      (fun x hx y hy => Subtype.ext (hcT _ (Subgroup.mem_subgroupOf.mp hx) _
        (Subgroup.mem_subgroupOf.mp hy)))
      (fun x hx => Subtype.ext ?_), ?_, ?_, ?_⟩
  · simpa using heT _ (Subgroup.mem_subgroupOf.mp hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT9]
  · intro y₀ hy₀ hy₀1 y₁ hy₁ hy₁1
    obtain ⟨w, hwM, hwT, hwy⟩ := htr y₀.1 (Subgroup.mem_subgroupOf.mp hy₀)
      (fun h => hy₀1 (Subtype.ext h)) y₁.1 (Subgroup.mem_subgroupOf.mp hy₁)
      (fun h => hy₁1 (Subtype.ext h))
    refine ⟨⟨w, hwM⟩, ?_, Subtype.ext ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hwT h.1
    · simpa using hwy
  · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTM]

end Helpers

section Pieces

variable {A L J K : Subgroup G} [(ker148 A J).Normal]

theorem leaf2_hessian_img {n : ℕ} (hK : K ≤ L ⊓ J) (hB : A ⊓ L ≤ J)
    (hKn : Sec4.IsoLThreePi ↥(img148 A J K) 2 n) (hn3 : ¬ 3 ∣ n)
    (hL9 : (Nat.card L).factorization 3 = 2) (hA9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) :
    ∃ E : Subgroup ↥(img148 A J J), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set ↥(img148 A J J)), w * y₀ * w⁻¹ = y₁) ∧
      E.map (img148 A J J).subtype = img148 A J (A ⊓ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAcomm, hAexp⟩ : IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ 3 = 1 := hAe
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hn3 (dvd_zero 3))
  have hKL : K ≤ L := hK.trans inf_le_left
  have hKJ : K ≤ J := hK.trans inf_le_right
  have hKU : K ≤ J ⊔ A := hKJ.trans le_sup_left
  have hDL : L ⊓ J ≤ L := inf_le_left
  have hBU : A ⊓ L ≤ J ⊔ A := inf_le_left.trans le_sup_right
  have hBD : A ⊓ L ≤ L ⊓ J := le_inf inf_le_right hB
  have hKM : img148 A J K ≤ img148 A J J := img148_mono hKJ
  have hTM : img148 A J (A ⊓ L) ≤ img148 A J J := img148_mono hB
  have hK27 : ¬ 27 ∣ Nat.card K := hessImg_not27 hL9 hKL
  have h9img : 9 ∣ Nat.card ↥(img148 A J K) :=
    Proof155w2.nine_dvd_card_of_isLThreePi ⟨2, n, ⟨Nat.prime_two⟩, hn1, hKn⟩
  have h9K : 9 ∣ Nat.card K := h9img.trans (Main148.card_img148_dvd hKU)
  have himg27 : ¬ 27 ∣ Nat.card ↥(img148 A J K) :=
    fun h => hK27 (h.trans (Main148.card_img148_dvd hKU))
  obtain ⟨S0, hS0K, hS0card⟩ : ∃ S0 : Subgroup G, S0 ≤ K ∧ Nat.card S0 = 9 := by
    have hdvdK : 3 ^ 2 ∣ Nat.card K := by norm_num; exact h9K
    obtain ⟨S1, hS1⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvdK
    exact ⟨S1.map K.subtype, Subgroup.map_subtype_le S1,
      by rw [Subgroup.card_map_of_injective K.subtype_injective, hS1] <;> norm_num⟩
  have hS0U : S0 ≤ J ⊔ A := hS0K.trans hKU
  have hS0D : S0 ≤ L ⊓ J := hS0K.trans hK
  have hS0P : IsPGroup 3 ↥S0 := IsPGroup.of_card (n := 2) (hS0card.trans (by norm_num))
  have hSD : Nat.card (S0.subgroupOf (L ⊓ J)) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0D).toEquiv).trans hS0card
  have hBD9 : Nat.card ((A ⊓ L).subgroupOf (L ⊓ J)) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBD).toEquiv).trans hA9
  obtain ⟨g, hg⟩ := hessImg_conj hSD hBD9 (hessImg_not27 hL9 hDL)
  obtain ⟨d, hdD, hd⟩ : ∃ d : G, d ∈ L ⊓ J ∧ ∀ x : G, x ∈ A ⊓ L ↔ d * x * d⁻¹ ∈ S0 := by
    refine ⟨(g : G), g.2, fun x => ?_⟩
    by_cases hx : x ∈ L ⊓ J
    · simpa [Subgroup.mem_subgroupOf] using hg ⟨x, hx⟩
    · constructor
      · intro hxB
        exact absurd (hBD hxB) hx
      · intro hdx
        exfalso
        apply hx
        have h1 : (g : G) * x * (g : G)⁻¹ ∈ L ⊓ J := hS0D hdx
        have e : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) := by group
        rw [e]
        exact (L ⊓ J).mul_mem ((L ⊓ J).mul_mem ((L ⊓ J).inv_mem g.2) h1) g.2
  have hdJ : d ∈ J := hdD.2
  have hdU : d ∈ J ⊔ A := (le_sup_left : J ≤ J ⊔ A) hdJ
  obtain ⟨g0, hg0⟩ : ∃ g0 : ↥(J ⊔ A) ⧸ ker148 A J,
      g0 = QuotientGroup.mk' (ker148 A J) ⟨d, hdU⟩ := ⟨_, rfl⟩
  have hg0M : g0 ∈ img148 A J J := mem_img148_iff.mpr ⟨d, hdU, hdJ, hg0.symm⟩
  have hT : ∀ z : ↥(J ⊔ A) ⧸ ker148 A J,
      z ∈ img148 A J (A ⊓ L) ↔ g0 * z * g0⁻¹ ∈ img148 A J S0 := by
    intro z
    constructor
    · intro hz
      obtain ⟨b, hbU, hbB, hbz⟩ := mem_img148_iff.mp hz
      have hdbU : d * b * d⁻¹ ∈ J ⊔ A :=
        (J ⊔ A).mul_mem ((J ⊔ A).mul_mem hdU hbU) ((J ⊔ A).inv_mem hdU)
      refine mem_img148_iff.mpr ⟨d * b * d⁻¹, hdbU, (hd b).mp hbB, ?_⟩
      have e1 : (⟨d * b * d⁻¹, hdbU⟩ : ↥(J ⊔ A)) = ⟨d, hdU⟩ * ⟨b, hbU⟩ * ⟨d, hdU⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv, hbz, hg0]
    · intro hz
      obtain ⟨s, hsU, hsS, hsz⟩ := mem_img148_iff.mp hz
      have hbU : d⁻¹ * s * d ∈ J ⊔ A :=
        (J ⊔ A).mul_mem ((J ⊔ A).mul_mem ((J ⊔ A).inv_mem hdU) hsU) hdU
      have hbB : d⁻¹ * s * d ∈ A ⊓ L := by
        refine (hd _).mpr ?_
        rw [show d * (d⁻¹ * s * d) * d⁻¹ = s by group]
        exact hsS
      refine mem_img148_iff.mpr ⟨d⁻¹ * s * d, hbU, hbB, ?_⟩
      have e2 : (⟨d⁻¹ * s * d, hbU⟩ : ↥(J ⊔ A)) = ⟨d, hdU⟩⁻¹ * ⟨s, hsU⟩ * ⟨d, hdU⟩ := rfl
      rw [e2, map_mul, map_mul, map_inv, ← hg0, hsz]
      group
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hcT : ∀ x ∈ img148 A J (A ⊓ L), ∀ y ∈ img148 A J (A ⊓ L), x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, haU, haB, rfl⟩ := mem_img148_iff.mp hx
    obtain ⟨c, hcU, hcB, rfl⟩ := mem_img148_iff.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc a haB.1 c hcB.1)
  have heT : ∀ x ∈ img148 A J (A ⊓ L), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨b, hbU, hbB, rfl⟩ := mem_img148_iff.mp hx
    rw [← map_pow]
    have h3 : (⟨b, hbU⟩ : ↥(J ⊔ A)) ^ 3 = 1 := Subtype.ext (hAexp b hbB.1)
    rw [h3, map_one]
  have hB3 : IsPGroup 3 ↥(A ⊓ L) := IsPGroup.of_card (n := 2) (hA9.trans (by norm_num))
  have hT9 : Nat.card ↥(img148 A J (A ⊓ L)) = 9 :=
    (hessImg_card_img hBU hB3).trans hA9
  have hSα_le : img148 A J S0 ≤ img148 A J K := img148_mono hS0K
  have hSα_card : Nat.card ↥(img148 A J S0) = 9 :=
    (hessImg_card_img hS0U hS0P).trans hS0card
  have hPX : Nat.card ↥((img148 A J S0).subgroupOf (img148 A J K)) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSα_le).toEquiv).trans hSα_card
  obtain ⟨SX, hSX⟩ := hessImg_sylow hPX himg27
  have hmod : n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  have hstep : ∀ k : ℕ, 2 ^ (k + 6) % 9 = 2 ^ k % 9 := by
    intro k
    rw [pow_add, Nat.mul_mod]
    norm_num
  have hper : ∀ q r : ℕ, 2 ^ (6 * q + r) % 9 = 2 ^ r % 9 := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show 6 * (q + 1) + r = (6 * q + r) + 6 by ring, hstep, ih]
  have h2n : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6]
    exact hper (n / 6) (n % 6)
  have h91 : 2 ^ n % 9 ≠ 1 := by
    rw [h2n]
    rcases hmod with h | h | h | h <;> rw [h] <;> norm_num
  have h98 : 2 ^ n % 9 ≠ 8 := by
    rw [h2n]
    rcases hmod with h | h | h | h <;> rw [h] <;> norm_num
  have htrX := CFSG.RankThree.PartTwo.Sec19.Item19ResProof.transitive_sylow hn1 hKn h91 h98 SX
  have htrQ : ∀ z ∈ img148 A J S0, z ≠ 1 → ∀ z' ∈ img148 A J S0, z' ≠ 1 →
      ∃ m ∈ img148 A J K, (∀ y, y ∈ img148 A J S0 ↔ m * y * m⁻¹ ∈ img148 A J S0) ∧
        m * z * m⁻¹ = z' := by
    intro z hz hz1 z' hz' hz'1
    have hzK : z ∈ img148 A J K := hSα_le hz
    have hz'K : z' ∈ img148 A J K := hSα_le hz'
    have hx : (⟨z, hzK⟩ : ↥(img148 A J K)) ∈ SX.toSubgroup := by
      rw [hSX]
      exact Subgroup.mem_subgroupOf.mpr hz
    have hy : (⟨z', hz'K⟩ : ↥(img148 A J K)) ∈ SX.toSubgroup := by
      rw [hSX]
      exact Subgroup.mem_subgroupOf.mpr hz'
    have hx1 : (⟨z, hzK⟩ : ↥(img148 A J K)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have hy1 : (⟨z', hz'K⟩ : ↥(img148 A J K)) ≠ 1 := fun h => hz'1 (congrArg Subtype.val h)
    obtain ⟨m, hm, hmrel⟩ := htrX _ hx hx1 _ hy hy1
    rw [hSX] at hm
    have hm' : ∀ y : ↥(img148 A J K), y ∈ (img148 A J S0).subgroupOf (img148 A J K) ↔
        (⟨(m : ↥(J ⊔ A) ⧸ ker148 A J), m.2⟩ : ↥(img148 A J K)) * y *
          (⟨(m : ↥(J ⊔ A) ⧸ ker148 A J), m.2⟩ : ↥(img148 A J K))⁻¹ ∈
            (img148 A J S0).subgroupOf (img148 A J K) :=
      fun y => Subgroup.mem_normalizer_iff.mp hm y
    refine ⟨(m : ↥(J ⊔ A) ⧸ ker148 A J), m.2,
      hessImg_normalizer hSα_le m.2 hm', ?_⟩
    have := congrArg Subtype.val hmrel
    simpa using this
  have htr : ∀ x ∈ img148 A J (A ⊓ L), x ≠ 1 → ∀ y ∈ img148 A J (A ⊓ L), y ≠ 1 →
      ∃ w ∈ img148 A J J, (∀ z, z ∈ img148 A J (A ⊓ L) ↔ w * z * w⁻¹ ∈ img148 A J (A ⊓ L)) ∧
        w * x * w⁻¹ = y := by
    intro x hx hx1 y hy hy1
    have hx' : g0 * x * g0⁻¹ ∈ img148 A J S0 := (hT x).mp hx
    have hy' : g0 * y * g0⁻¹ ∈ img148 A J S0 := (hT y).mp hy
    have hx'1 : g0 * x * g0⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have e : x = g0⁻¹ * (g0 * x * g0⁻¹) * g0 := by group
      rw [e, h]
      group
    have hy'1 : g0 * y * g0⁻¹ ≠ 1 := by
      intro h
      apply hy1
      have e : y = g0⁻¹ * (g0 * y * g0⁻¹) * g0 := by group
      rw [e, h]
      group
    obtain ⟨m, hmK, hmnorm, hmrel⟩ := htrQ _ hx' hx'1 _ hy' hy'1
    refine ⟨g0⁻¹ * m * g0, ?_, ?_, ?_⟩
    · exact (img148 A J J).mul_mem
        ((img148 A J J).mul_mem ((img148 A J J).inv_mem hg0M) (hKM hmK)) hg0M
    · intro z
      have hw := hT (g0⁻¹ * m * g0 * z * (g0⁻¹ * m * g0)⁻¹)
      have e3 : g0 * (g0⁻¹ * m * g0 * z * (g0⁻¹ * m * g0)⁻¹) * g0⁻¹
          = m * (g0 * z * g0⁻¹) * m⁻¹ := by
        group
      rw [hw, e3, hT z]
      exact hmnorm _
    · have e4 : g0⁻¹ * m * g0 * x * (g0⁻¹ * m * g0)⁻¹
          = g0⁻¹ * (m * (g0 * x * g0⁻¹) * m⁻¹) * g0 := by
        group
      rw [e4, hmrel]
      group
  exact hessImg_final hTM hcT heT hT9 htr

end Pieces

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
