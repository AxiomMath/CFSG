module

public import CFSG.Quasithin.Recognition.Kleidman.F204.NatA
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOff
public import CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.FixedPointCount
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFixed

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom
open CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

section Generic

theorem centralizes_of_fixes_four {V : Subgroup G} (hV4 : Nat.card V = 4) {d : G}
    (hd : d ∈ Subgroup.normalizer (V : Set G)) (hd3 : d ^ 3 = 1) {a : G} (ha : a ∈ V)
    (ha1 : a ≠ 1) (hda : d * a = a * d) : ∀ v ∈ V, d * v = v * d := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  set F : Subgroup V := (Subgroup.centralizer ({d} : Set G)).subgroupOf V with hFdef
  have hmem : ∀ x : V, x ∈ F ↔ d * (x : G) = (x : G) * d := by
    intro x
    simp [hFdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  have hFix : ∀ x : V, conjPerm hd x = x ↔ d * (x : G) = (x : G) * d := by
    intro x
    have e := conjPerm_pow_apply hd 1 x
    rw [pow_one, pow_one] at e
    rw [Subtype.ext_iff, e, mul_inv_eq_iff_eq_mul]
  have hcardF : Nat.card (FixedSet (conjPerm hd)) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hFix, hmem])
  have hσ3 : (conjPerm hd) ^ 3 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [conjPerm_pow_apply, hd3]
    simp
  have hmod := natCard_fixed_modEq_three _ hσ3
  rw [hV4, hcardF] at hmod
  have hdvd : Nat.card F ∣ 4 := by
    have := Subgroup.card_subgroup_dvd_card F
    rwa [hV4] at this
  have hne1 : Nat.card F ≠ 1 := by
    intro h1
    have hbot : F = ⊥ := Subgroup.eq_bot_of_card_eq F h1
    have haF : (⟨a, ha⟩ : V) ∈ F := (hmem _).mpr hda
    rw [hbot, Subgroup.mem_bot] at haF
    exact ha1 (congrArg Subtype.val haF)
  have hF4 : Nat.card F = 4 := by
    have h3 : Nat.card F % 3 = 1 := by
      unfold Nat.ModEq at hmod
      omega
    have hcle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    generalize hc : Nat.card F = c at h3 hdvd hne1 hcle ⊢
    interval_cases c <;> first | rfl | omega
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hF4, hV4])
  intro v hv
  have hvF : (⟨v, hv⟩ : V) ∈ F := by rw [htop]; exact Subgroup.mem_top _
  exact (hmem _).mp hvF

variable {H M : Subgroup G}

theorem eq_one_of_mem_Qv_of_pow_three {δ : Geo H M} {t : G} (ht : t ∈ Qv δ) (ht3 : t ^ 3 = 1) :
    t = 1 := by
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (stab δ)) ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨hk', ht3⟩
  rwa [hg, pow_one] at this

@[expose] def ThreeCent (δ : Geo H M) : Prop :=
  ∀ t ∈ stab δ, t ^ 3 = 1 → t ∈ Subgroup.centralizer (Zv δ : Set G)

omit [Finite G] in
theorem ThreeCent.smul (g : ↥(H ⊔ M)) {δ : Geo H M} (h : ThreeCent δ) : ThreeCent (g • δ) := by
  intro t ht ht3
  rw [stab_smul, mem_conjSub] at ht
  have e : ((g : G)⁻¹ * t * (g : G)) ^ 3 = (g : G)⁻¹ * t ^ 3 * (g : G) := by
    have := conj_pow (a := (g : G)⁻¹) (b := t) (i := 3)
    rwa [inv_inv] at this
  have h' := h _ ht (by rw [e, ht3]; group)
  rw [Zv_smul, conjSub_centralizer, mem_conjSub]
  exact h'

omit [Finite G] in
theorem ThreeCent.of_vtype_eq {δ δ' : Geo H M} (hv : vtype δ = vtype δ') (h : ThreeCent δ) :
    ThreeCent δ' := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq hv
  exact h.smul g

end Generic

variable {L1 L2 S D X : Subgroup G}

theorem threeCent_of_mem_centralizer (F : Frame L1 L2 S D X)
    {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) {ρ : G} (hρ : ρ ∈ stab δ)
    (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1) (hρC : ρ ∈ Subgroup.centralizer (Zv δ : Set G)) :
    ThreeCent δ := by
  have hA := Amal.of_frame F
  obtain ⟨E, hEδ, hE3, -, hball⟩ := ballStab_one_false F hδ
  have hEn : E ≤ Subgroup.normalizer (Qv δ : Set G) :=
    hEδ.trans (le_normalizer_pCoreOf 2 (stab δ))
  have hQC : Qv δ ≤ Subgroup.centralizer (Zv δ : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv δ hy).2 q hq).symm
  have hQE : ∀ t ∈ stab δ, t ^ 3 = 1 → ∃ q ∈ Qv δ, ∃ e ∈ E, t = q * e := by
    intro t ht ht3
    have htb : t ∈ ballStab 1 δ := by
      rw [mem_ballStab]
      intro ε hε
      rcases (dist_le_one_iff rfl).mp hε with rfl | hadj
      · exact ht
      · exact three_mem_stab_nbr F hδ hadj ht ht3
    rw [hball] at htb
    exact (F1.mem_sup_iff_exists_mul_of_normalizes hEn).mp htb
  obtain ⟨q₀, hq₀, e₀, he₀, rfl⟩ := hQE _ hρ hρ3
  have he₀C : e₀ ∈ Subgroup.centralizer (Zv δ : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQC hq₀)) hρC
    rwa [inv_mul_cancel_left] at this
  have he₀1 : e₀ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hρ3 hρ1
    exact hρ1 (eq_one_of_mem_Qv_of_pow_three hq₀ hρ3)
  have he₀3 : e₀ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥E) (x := ⟨e₀, he₀⟩)
    rw [hE3] at this
    simpa using congrArg Subtype.val this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf e₀ = 3 := orderOf_eq_prime he₀3 he₀1
  have hzp : Subgroup.zpowers e₀ = E :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he₀)
      (by rw [hE3, Nat.card_zpowers, hord])
  have hEC : E ≤ Subgroup.centralizer (Zv δ : Set G) := by
    rw [← hzp]; exact Subgroup.zpowers_le.mpr he₀C
  intro t ht ht3
  obtain ⟨q, hq, e, he, rfl⟩ := hQE t ht ht3
  exact Subgroup.mul_mem _ (hQC hq) (hEC he)

section T1

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
include F hT1

theorem inf_centralizer_three_eq_bot {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hN : NatA x) {ρ : G} (hρ : ρ ∈ stab x) (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1) :
    Zv x ⊓ Subgroup.centralizer {ρ} = ⊥ := by
  have hA := Amal.of_frame F
  obtain ⟨⟨δ, hδx, hρδ⟩, ⟨δ', hδ'x, hρδ'⟩, hne, -⟩ :=
    Nat.card_eq_two_iff.mp (card_fixed_nbrs_three F hx hρ hρ3 hρ1)
  have hne' : δ ≠ δ' := fun h => hne (Subtype.ext h)
  have hvf : ∀ μ ∈ nbrs x, vtype μ = false := by
    intro μ hμ
    have := vtype_ne_of_adj (show (graph _ _ _).Adj x μ from hμ)
    rw [hx] at this
    cases h : vtype μ <;> simp_all
  have hδf := hvf δ hδx
  have hδ'f := hvf δ' hδ'x
  have hsup := Zv_sup_Zv_eq F hT1 hx hN hδx hδ'x hne'
  have hinf := Zv_inf_Zv_eq_bot F hT1 hx hN hδx hδ'x hne'
  have hcent : ThreeCent δ → False := by
    intro h3
    have h3' : ThreeCent δ' := h3.of_vtype_eq (by rw [hδf, hδ'f])
    have hCδ := h3 ρ hρδ hρ3
    have hCδ' := h3' ρ hρδ' hρ3
    have hle : Zv δ ⊔ Zv δ' ≤ Subgroup.centralizer {ρ} := by
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hCδ z hz
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hCδ' z hz
    rw [hsup] at hle
    obtain ⟨φ, hφ, hker⟩ := exists_phi_stab F hx
    have hQC : Qv x ≤ Subgroup.centralizer (Zv x : Set G) := fun q hq =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hy).2 q hq).symm
    have hkerC : ∀ l : ↥(stab x), φ l = 1 → (l : G) ∈ Subgroup.centralizer (Zv x : Set G) := by
      intro l hl
      have hlk : l ∈ φ.ker := hl
      rw [hker, Subgroup.mem_subgroupOf] at hlk
      exact hQC hlk
    have hCL : ∀ v ∈ Zv x, (∀ l : ↥(stab x), v * (l : G) = (l : G) * v) → v = 1 := by
      intro v hv hvl
      have hmem : v ∈ Zv x ⊓ Subgroup.centralizer (stab x : Set G) :=
        ⟨hv, Subgroup.mem_centralizer_iff.mpr fun g hg => (hvl ⟨g, hg⟩).symm⟩
      rw [H1 F hT1 hx] at hmem
      exact hmem
    have hV1 : ∃ v ∈ Zv x, v ≠ 1 := by
      obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hA.Zv_ne_bot x)
      exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩
    have hφρ : φ ⟨ρ, hρ⟩ = 1 :=
      (centralises_iff_phi_eq_one (hA.stab_le_normalizer_Zv x) φ hφ hkerC hCL hV1 ⟨ρ, hρ⟩).mp
        fun v hv => Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
    have hρk : (⟨ρ, hρ⟩ : ↥(stab x)) ∈ φ.ker := hφρ
    rw [hker, Subgroup.mem_subgroupOf] at hρk
    exact hρ1 (eq_one_of_mem_Qv_of_pow_three hρk hρ3)
  rw [eq_bot_iff]
  rintro v ⟨hvx, hvρ⟩
  rw [Subgroup.mem_bot]
  by_contra hv1
  have hcomm : ∀ y ∈ Zv x, ∀ z ∈ Zv x, y * z = z * y := fun y hy z hz =>
    (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hz).2 y (hA.Zv_le_Qv x hy))
  have hδle : Zv δ ≤ Zv x := hsup ▸ le_sup_left
  have hδ'le : Zv δ' ≤ Zv x := hsup ▸ le_sup_right
  have hnorm : Zv δ' ≤ Subgroup.normalizer (Zv δ : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm b (hδ'le hb) y (hδle hy), mul_inv_cancel_right]
      exact hy
    · intro hy
      have hw := hcomm b (hδ'le hb) (b * y * b⁻¹) (hδle hy)
      have e : y = b * y * b⁻¹ := by
        calc y = b⁻¹ * ((b * y * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * y * b⁻¹)) := by rw [hw]
          _ = b * y * b⁻¹ := by group
      rw [e]; exact hy
  rw [← hsup] at hvx
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hvx
  have hρa : ρ * a * ρ⁻¹ ∈ Zv δ :=
    (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv δ hρδ) a).mp ha
  have hρb : ρ * b * ρ⁻¹ ∈ Zv δ' :=
    (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv δ' hρδ') b).mp hb
  have hvρ' : (a * b) * ρ = ρ * (a * b) := Subgroup.mem_centralizer_singleton_iff.mp hvρ
  have hsplit : (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) = a * b := by
    calc (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) = ρ * (a * b) * ρ⁻¹ := by group
      _ = (a * b) * ρ * ρ⁻¹ := by rw [hvρ']
      _ = a * b := by group
  have hab : a⁻¹ * (ρ * a * ρ⁻¹) = b * (ρ * b * ρ⁻¹)⁻¹ := by
    calc a⁻¹ * (ρ * a * ρ⁻¹)
        = a⁻¹ * ((ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹)) * (ρ * b * ρ⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * b) * (ρ * b * ρ⁻¹)⁻¹ := by rw [hsplit]
      _ = b * (ρ * b * ρ⁻¹)⁻¹ := by group
  have h1 : a⁻¹ * (ρ * a * ρ⁻¹) ∈ Zv δ ⊓ Zv δ' :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hρa,
      by rw [hab]; exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hρb)⟩
  rw [hinf, Subgroup.mem_bot] at h1
  have h2 : b * (ρ * b * ρ⁻¹)⁻¹ = 1 := by rw [← hab]; exact h1
  have hfa : ρ * a = a * ρ := by
    have e : ρ * a * ρ⁻¹ = a := by
      calc ρ * a * ρ⁻¹ = a * (a⁻¹ * (ρ * a * ρ⁻¹)) := by group
        _ = a := by rw [h1, mul_one]
    calc ρ * a = ρ * a * ρ⁻¹ * ρ := by group
      _ = a * ρ := by rw [e]
  have hfb : ρ * b = b * ρ := by
    have e : ρ * b * ρ⁻¹ = b := by
      calc ρ * b * ρ⁻¹ = (b * (ρ * b * ρ⁻¹)⁻¹)⁻¹ * b := by group
        _ = b := by rw [h2, inv_one, one_mul]
    calc ρ * b = ρ * b * ρ⁻¹ * ρ := by group
      _ = b * ρ := by rw [e]
  have hab1 : a ≠ 1 ∨ b ≠ 1 := by
    by_contra h
    push Not at h
    exact hv1 (by rw [h.1, h.2, mul_one])
  rcases hab1 with ha1 | hb1
  · have hCa := centralizes_of_fixes_four (card_Zv_nbr F hT1 hx hN hδx)
      (hA.stab_le_normalizer_Zv δ hρδ) hρ3 ha ha1 hfa
    exact hcent (threeCent_of_mem_centralizer F hδf hρδ hρ3 hρ1
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (hCa z hz).symm))
  · have hCb := centralizes_of_fixes_four (card_Zv_nbr F hT1 hx hN hδ'x)
      (hA.stab_le_normalizer_Zv δ' hρδ') hρ3 hb hb1 hfb
    exact hcent ((threeCent_of_mem_centralizer F hδ'f hρδ' hρ3 hρ1
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (hCb z hz).symm)).of_vtype_eq
        (by rw [hδ'f, hδf]))

end T1

end CFSG.Quasithin.Kleidman.F204
