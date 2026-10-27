module

public import CFSG.RankThree.GF2n.Parrott.Lemma15Equality
public import CFSG.RankThree.GF2n.Parrott.EqualityBranchModuleV
import CFSG.SignalizerFunctorTheorem.MinimalAction.AbelianCase

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

section Abelianization

variable {G : Type} [Group G] [Finite G]

theorem mem_commutator_self_of_mem_commutator_of_centralizes {p : ℕ} [Fact p.Prime]
    {P A : Subgroup G} (hP : IsPGroup p P) (hA : Nat.Coprime p (Nat.card A))
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) {r : G} (hr : r ∈ ⁅P, A⁆)
    (hcent : ∀ a ∈ A, a * r = r * a) : r ∈ ⁅P, P⁆ := by
  have hPA : ⁅P, A⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hAP
  let ρ : A →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP)
  let ab : MulAut P →* AddMonoid.End (Additive (Abelianization P)) :=
    { toFun := fun α => MonoidHom.toAdditive (Abelianization.map α.toMonoidHom)
      map_one' := by
        show MonoidHom.toAdditive (Abelianization.map (MonoidHom.id P)) =
          (1 : AddMonoid.End (Additive (Abelianization P)))
        rw [Abelianization.map_id]
        rfl
      map_mul' := fun α β => by
        show MonoidHom.toAdditive (Abelianization.map (α.toMonoidHom.comp β.toMonoidHom)) = _
        rw [← Abelianization.map_comp]
        rfl }
  let φ : A →* AddMonoid.End (Additive (Abelianization P)) := ab.comp ρ
  have hφ : ∀ (a : A) (g : P), φ a (Additive.ofMul (Abelianization.of g)) =
      Additive.ofMul (Abelianization.of (ρ a g)) := fun _ _ => rfl
  have hρ : ∀ (a : A) (g : P), ((ρ a g : P) : G) = (a : G) * g * (a : G)⁻¹ := fun _ _ => rfl
  have hV : ∃ k : ℕ, Nat.card (Additive (Abelianization P)) = p ^ k := by
    have hab : IsPGroup p (Abelianization P) :=
      hP.of_surjective Abelianization.of fun y => QuotientGroup.induction_on y fun g => ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := hab.exists_card_eq
    exact ⟨k, (Nat.card_congr Additive.toMul).trans hk⟩
  let W : AddSubgroup (Additive (Abelianization P)) :=
    AddSubgroup.closure {u | ∃ a ∈ (⊤ : Subgroup A), ∃ v, u = φ a v - v}
  have hgen : ∀ (a : A) (v : Additive (Abelianization P)), φ a v - v ∈ W := fun a v =>
    AddSubgroup.subset_closure ⟨a, Subgroup.mem_top a, v, rfl⟩
  let S₀ : Subgroup P := (AddSubgroup.toSubgroup' W).comap Abelianization.of
  have hS₀ : ∀ g : P, g ∈ S₀ ↔ Additive.ofMul (Abelianization.of g) ∈ W := fun g => Iff.rfl
  have hle : ⁅P, A⁆ ≤ S₀.map P.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg a ha
    have hga : ⁅g, a⁆ ∈ P := hPA (Subgroup.commutator_mem_commutator hg ha)
    refine ⟨⟨⁅g, a⁆, hga⟩, (hS₀ _).mpr ?_, rfl⟩
    have hdecomp : (⟨⁅g, a⁆, hga⟩ : P) = ⟨g, hg⟩ * (ρ ⟨a, ha⟩ ⟨g, hg⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ, commutatorElement_def]
      group
    rw [hdecomp, map_mul, map_inv, ofMul_mul, ofMul_inv, ← hφ]
    have h1 := neg_mem (hgen ⟨a, ha⟩ (Additive.ofMul (Abelianization.of ⟨g, hg⟩)))
    have h2 : Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P)) +
        -(φ ⟨a, ha⟩ (Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P)))) =
        -(φ ⟨a, ha⟩ (Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P))) -
          Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P))) := by abel
    rw [h2]
    exact h1
  have hrP : r ∈ P := hPA hr
  have hw : Additive.ofMul (Abelianization.of (⟨r, hrP⟩ : P)) ∈ W := by
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp (hle hr)
    have hy' : y = ⟨r, hrP⟩ := Subtype.ext hyr
    rw [hy'] at hy
    exact (hS₀ _).mp hy
  have hρr : ∀ a : A, ρ a ⟨r, hrP⟩ = ⟨r, hrP⟩ := fun a => by
    apply Subtype.ext
    rw [hρ]
    exact mul_inv_eq_of_eq_mul (hcent a a.2)
  have hfix : ∀ a ∈ (⊤ : Subgroup A), φ a (Additive.ofMul (Abelianization.of (⟨r, hrP⟩ : P))) =
      Additive.ofMul (Abelianization.of (⟨r, hrP⟩ : P)) := fun a _ => by
    rw [hφ, hρr]
  have hQ : Nat.Coprime p (Nat.card (⊤ : Subgroup A)) := by rwa [Subgroup.card_top]
  have h0 := CFSG.SignalizerFunctorTheorem.MinimalAction.eq_zero_of_mem_commutator_of_fixed hV φ
    hQ hw hfix
  have h1 : Abelianization.of (⟨r, hrP⟩ : P) = 1 := by simpa using h0
  have h2 : (⟨r, hrP⟩ : P) ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    exact h1
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h2, rfl⟩

end Abelianization

section KeyStep

variable {G : Type} [Group G] [Finite G] {z : G}

theorem commutator_le_J_of_le_H {B : Subgroup G} (hBH : B ≤ H z) : ⁅B, J z⁆ ≤ J z := by
  rw [Subgroup.commutator_le]
  intro b hb j hj
  rw [commutatorElement_def]
  exact (J z).mul_mem (conj_mem_J_of_mem_H (hBH hb) hj) ((J z).inv_mem hj)

theorem commute_of_mem_commutator_J_of_conj_mem_centerIn {B : Subgroup G} (hBH : B ≤ H z)
    (hBZ : ∀ b ∈ B, ∀ c ∈ centerIn (J z), b * c = c * b)
    (hEB : ⁅⁅B, J z⁆, B⁆ = ⁅B, J z⁆) {x : G} (hxB : x ∈ Subgroup.centralizer (B : Set G))
    (hx : ∀ e ∈ ⁅B, J z⁆, x * e * x⁻¹ * e⁻¹ ∈ centerIn (J z)) :
    ∀ e ∈ ⁅B, J z⁆, x * e = e * x := by
  have hEJ : ⁅B, J z⁆ ≤ J z := commutator_le_J_of_le_H hBH
  have hle : ⁅⁅B, J z⁆, B⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro e he b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have heJ : e ∈ J z := hEJ he
    have hkJ : ⁅e, b⁆ ∈ J z := by
      have e2 : ⁅e, b⁆ = e * (b * e⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
      rw [e2]
      exact (J z).mul_mem heJ (conj_mem_J_of_mem_H (hBH hb) ((J z).inv_mem heJ))
    obtain ⟨c, hcZ, hc⟩ : ∃ c ∈ centerIn (J z), c = x * e * x⁻¹ * e⁻¹ := ⟨_, hx e he, rfl⟩
    have hxe : x * e * x⁻¹ = c * e := by rw [hc]; group
    have hxbx : x * b * x⁻¹ = b := by
      rw [← Subgroup.mem_centralizer_iff.mp hxB b hb]
      group
    have hbc : b * c⁻¹ * b⁻¹ = c⁻¹ := by
      rw [show b * c⁻¹ * b⁻¹ = (b * c * b⁻¹)⁻¹ by group, hBZ b hb c hcZ]
      group
    have hck : c * ⁅e, b⁆ * c⁻¹ = ⁅e, b⁆ := by
      rw [← Subgroup.mem_centralizer_iff.mp hcZ.2 _ hkJ]
      group
    have key : x * ⁅e, b⁆ * x⁻¹ = ⁅e, b⁆ := by
      have h1 : x * ⁅e, b⁆ * x⁻¹ =
          x * e * x⁻¹ * (x * b * x⁻¹) * (x * e * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      have h2 : c * e * b * (c * e)⁻¹ * b⁻¹ = c * ⁅e, b⁆ * (b * c⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [h1, hxe, hxbx, h2, hbc, hck]
    calc ⁅e, b⁆ * x = x * ⁅e, b⁆ * x⁻¹ * x := by rw [key]
      _ = x * ⁅e, b⁆ := by group
  intro e he
  rw [← hEB] at he
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle he)).symm

end KeyStep

section Main

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem commutator_J_isExtraspecial2_of_card_eq_five (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {B : Subgroup G} (hBH : B ≤ H z) (hB5 : Nat.card B = 5) :
    ⁅B, J z⁆ ≤ J z ∧ IsExtraspecial2 ⁅B, J z⁆ ∧ Nat.card (⁅B, J z⁆ : Subgroup G) = 2 ^ 5 ∧
      ∀ w : G, cosetJ (z := z) (uH D * vH D) w → w ∈ Subgroup.centralizer (B : Set G) →
        ∀ e ∈ ⁅B, J z⁆, w * e = e * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz2 : orderOf z = 2 := h.1
  have hJ' : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm', -, -⟩ := h
    simpa [J, H] using hcomm'
  have hEJ : ⁅B, J z⁆ ≤ J z := commutator_le_J_of_le_H hBH
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hBN : B ≤ Subgroup.normalizer (J z : Set G) := hBH.trans hHN
  obtain ⟨⟨b, hbB⟩, hbord⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hB5] : 5 ∣ Nat.card B)
  rw [Subgroup.orderOf_mk] at hbord
  have hBb : B = Subgroup.zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
      (by rw [hB5, Nat.card_zpowers, hbord])).symm
  set bH : ↥(H z) := ⟨b, hBH hbB⟩ with hbHdef
  have hbH5 : orderOf bH = 5 := by rw [hbHdef, Subgroup.orderOf_mk, hbord]
  have hZb : conjZ z bH = 1 :=
    conjZ_eq_one_of_mem_Q (z := z) D h bH (qH_mem_QP45_of_orderOf_eq_five (z := z) D hbH5)
  have hBZ : ∀ b' ∈ B, ∀ c ∈ centerIn (J z), b' * c = c * b' := by
    intro b' hb' c hc
    rw [hBb] at hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    exact ((sigma_commute_of_mem_centerIn_of (z := z) hZb hc).zpow_left k).eq
  have hBp : IsPGroup 5 B := IsPGroup.of_card (n := 1) (by rw [hB5, pow_one])
  have hJ5 : ¬ 5 ∣ Nat.card (J z) := by rw [card_J h]; norm_num
  have hfact :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      5 (by norm_num) B (J z) hBp hJ5 hBN
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent
    5 (by norm_num) B (J z) hBp hJ5 hBN
  have hEc : ⁅J z, B⁆ = ⁅B, J z⁆ := Subgroup.commutator_comm (J z) B
  rw [hEc] at hfact hidem
  have hkey := fun (x : G) (hxB : x ∈ Subgroup.centralizer (B : Set G)) hx =>
    commute_of_mem_commutator_J_of_conj_mem_centerIn hBH hBZ hidem (x := x) hxB hx
  have hCJ : ∀ x ∈ J z, x ∈ Subgroup.centralizer (B : Set G) →
      ∀ e ∈ ⁅B, J z⁆, x * e = e * x := by
    intro x hxJ hxB
    refine hkey x hxB fun e he => ?_
    have hxe := commutator_mem_centerIn h ⟨x, hxJ⟩ ⟨e, hEJ he⟩
    rwa [commutatorElement_def] at hxe
  have hZE : ∀ c ∈ ⁅B, J z⁆, (∀ e ∈ ⁅B, J z⁆, c * e = e * c) → c ∈ centerIn (J z) := by
    intro c hc hcE
    have hJc : J z ≤ Subgroup.centralizer ({c} : Set G) := by
      refine hfact.le.trans (sup_le ?_ ?_)
      · intro e he
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcE e he).symm
      · rintro x ⟨hxJ, hxB⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hCJ x hxJ hxB c hc)
    exact ⟨hEJ hc, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hJc hy)⟩
  have hEZ : ∀ c ∈ ⁅B, J z⁆, c ∈ centerIn (J z) → c ∈ Subgroup.zpowers z := by
    intro c hc hcZ
    rw [← hEc] at hc
    have hcJ := mem_commutator_self_of_mem_commutator_of_centralizes (isPGroup_J h)
      (by rw [hB5]; norm_num) hBN hc fun b' hb' => hBZ b' hb' c hcZ
    rwa [hJ'] at hcJ
  have hBmap : (Subgroup.zpowers bH).map (H z).subtype = B := by
    rw [MonoidHom.map_zpowers, hBb]
    rfl
  have hπE : commutatorV h bH = (⁅B, J z⁆.subgroupOf (J z)).map (QuotientV.pi z) := by
    change ((⁅(Subgroup.zpowers bH).map (H z).subtype, J z⁆).subgroupOf (J z)).map
      (QuotientV.pi z) = _
    rw [hBmap]
  have hcardV : Nat.card (commutatorV h bH) = 16 :=
    card_commutatorV_of_orderOf_eq_five (z := z) D h hσ₂ hq₂ hcomm hEq hbH5
  have hmemV : ∀ e (he : e ∈ ⁅B, J z⁆), QuotientV.pi z ⟨e, hEJ he⟩ ∈ commutatorV h bH := by
    intro e he
    rw [hπE]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he)
  have hnab : ⁅⁅B, J z⁆, ⁅B, J z⁆⁆ ≠ ⊥ := by
    intro hbot
    have hle : commutatorV h bH ≤ ⊥ := by
      rw [hπE]
      rintro _ ⟨⟨e, heJ⟩, he, rfl⟩
      have he' : e ∈ ⁅B, J z⁆ := Subgroup.mem_subgroupOf.mp he
      have heZ : e ∈ centerIn (J z) := hZE e he' fun e' he'' => by
        have hc := Subgroup.commutator_mem_commutator he' he''
        rwa [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientV.pi_ker]
      exact Subgroup.mem_subgroupOf.mpr heZ
    have hcard := Subgroup.card_le_of_le hle
    rw [hcardV, Subgroup.card_bot] at hcard
    omega
  have hzc : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hE' : ⁅⁅B, J z⁆, ⁅B, J z⁆⁆ = Subgroup.zpowers z := by
    have hle : ⁅⁅B, J z⁆, ⁅B, J z⁆⁆ ≤ Subgroup.zpowers z :=
      hJ' ▸ Subgroup.commutator_mono hEJ hEJ
    apply Subgroup.eq_of_le_of_card_ge hle
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnab
    omega
  have hzE : z ∈ ⁅B, J z⁆ := Subgroup.commutator_le_self _ (hE' ▸ Subgroup.mem_zpowers z)
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hEZeq : ⁅B, J z⁆ ⊓ centerIn (J z) = Subgroup.zpowers z :=
    le_antisymm (fun c hc => hEZ c hc.1 hc.2)
      (le_inf (Subgroup.zpowers_le.mpr hzE) (Subgroup.zpowers_le.mpr hzZ))
  have hZEeq : (Subgroup.center (⁅B, J z⁆ : Subgroup G)).map (⁅B, J z⁆ : Subgroup G).subtype =
      Subgroup.zpowers z := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hcE : ∀ e ∈ ⁅B, J z⁆, (c : G) * e = e * c := fun e he =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨e, he⟩)).symm
      rw [← hEZeq]
      exact ⟨c.2, hZE c c.2 hcE⟩
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (J_le_H (hEJ g.2))
  have hcardE : Nat.card (⁅B, J z⁆ : Subgroup G) = 2 ^ 5 := by
    have h1 := Subgroup.relIndex_mul_card (QuotientV.pi z).ker (⁅B, J z⁆.subgroupOf (J z))
    rw [Subgroup.relIndex_ker, ← hπE, hcardV] at h1
    have hker : (QuotientV.pi z).ker ⊓ ⁅B, J z⁆.subgroupOf (J z) =
        (⁅B, J z⁆ ⊓ centerIn (J z)).subgroupOf (J z) := by
      rw [QuotientV.pi_ker]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      tauto
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hEJ)).toEquiv,
      hEZeq, hzc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv] at h1
    omega
  have hwE : ∀ w : G, cosetJ (z := z) (uH D * vH D) w → w ∈ Subgroup.centralizer (B : Set G) →
      ∀ e ∈ ⁅B, J z⁆, w * e = e * w := by
    intro w hw hwB
    obtain ⟨j, hj, hwj⟩ := hw
    have hwH : w ∈ H z := by
      rw [hwj]
      exact (H z).mul_mem (uH D * vH D).2 (J_le_H hj)
    have hqw : qH D ⟨w, hwH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ := by
      have e1 : (⟨w, hwH⟩ : ↥(H z)) = (uH D * vH D) * ⟨j, J_le_H hj⟩ := Subtype.ext hwj
      have hjq : qH D ⟨j, J_le_H hj⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
      rw [e1, map_mul, hjq, mul_one, map_mul, qH_uH, qH_vH]
    have hg2 : qH D ⟨w, hwH⟩ * qH D ⟨w, hwH⟩ = 1 := by
      have huu : (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨u, u_mem_A⟩ = 1 := Subtype.ext u_sq
      have hvv : (⟨v, v_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ = 1 := Subtype.ext v_sq
      have huv : Commute (⟨u, u_mem_A⟩ : QA45.originalSubgroup) ⟨v, v_mem_A⟩ :=
        Subtype.ext u_commute_v
      rw [hqw, Commute.mul_mul_mul_comm huv.symm, huu, hvv, one_mul]
    have hgb : qH D ⟨w, hwH⟩ * qH D bH = qH D bH * qH D ⟨w, hwH⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwB b hbB).symm
    have hfixV := conjV_eq_self_of_mem_commutatorV_of_orderOf_eq_five (z := z) D h hσ₂ hq₂
      hcomm hEq hbH5 hg2 hgb
    refine hkey w hwB fun e he => ?_
    have hfe := hfixV _ (hmemV e he)
    rwa [conjV_pi_eq_iff] at hfe
  exact ⟨hEJ, ⟨(isPGroup_J h).to_le hEJ, hE'.trans hZEeq.symm, by rw [hE', hzc]⟩, hcardE, hwE⟩

theorem exists_order_five_subgroup_extraspecial_conj_mem_uvJ (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    ∃ B : Subgroup G, B ≤ H z ∧ Nat.card B = 5 ∧
      (∀ b ∈ B, cosetJ (z := z) (uH D * vH D) (b * ((uH D * vH D : ↥(H z)) : G) * b⁻¹)) ∧
      ∃ E : Subgroup G, E ≤ J z ∧ IsExtraspecial2 E ∧ Nat.card E = 2 ^ 5 ∧
        ∀ w : G, cosetJ (z := z) (uH D * vH D) w → w ∈ Subgroup.centralizer (B : Set G) →
          ∀ e ∈ E, w * e = e * w := by
  obtain ⟨B, hBH, hB5, hBuv⟩ := exists_order_five_subgroup_conj_mem_uvJ (z := z) D h
  obtain ⟨hEJ, hE, hEcard, hwE⟩ :=
    commutator_J_isExtraspecial2_of_card_eq_five (z := z) D h hσ₂ hq₂ hcomm hEq hBH hB5
  exact ⟨B, hBH, hB5, hBuv, ⁅B, J z⁆, hEJ, hE, hEcard, hwE⟩

end Main

end CFSG.RankThree.GF2n.Parrott
