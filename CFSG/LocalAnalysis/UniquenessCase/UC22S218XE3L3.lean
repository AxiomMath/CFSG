module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218CenL
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3Ex
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3Cov
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LieType.OutStructureAGeneral
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GAbs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj proj_eq_one_iff
  proj_eq_proj_iff scalars)
open CFSG.Quasithin.H13.KG4413 (dg3 coe_dg3 dL3)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

section Cartan

variable {K : Type} [Field K]

private theorem dg3_scalar_nine {t : Kˣ × Kˣ} (h : dg3 t ∈ scalars 3 K) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ t = (c, c) := by
  obtain ⟨c, hc, hA⟩ := h
  refine ⟨c, hc, Prod.ext (Units.ext ?_) (Units.ext ?_)⟩
  · simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 0) 0
  · simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 1) 1

private theorem dg3_mem_scalars_nine {c : Kˣ} (hc : c ^ 3 = 1) : dg3 (c, c) ∈ scalars 3 K := by
  refine ⟨c, hc, ?_⟩
  have hinv : ((c * c)⁻¹ : Kˣ) = c := inv_eq_of_mul_eq_one_right (by rw [mul_assoc, ← pow_three, hc])
  rw [coe_dg3, Matrix.scalar_apply, hinv]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem dL3_comm_nine {a b : projectiveSL 3 K} (ha : a ∈ dL3 K) (hb : b ∈ dL3 K) :
    a * b = b * a := by
  obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hb
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm s t]

theorem uc22s218_l3_exists_elemAbelian_nine [Finite K] (h9 : 9 ∣ Nat.card K - 1) :
    ∃ Q : Subgroup (projectiveSL 3 K), Q ≤ dL3 K ∧ IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have h9' : 9 ∣ orderOf g := by rw [hg, Nat.card_units]; exact h9
  have hηo : orderOf (g ^ (orderOf g / 9)) = 9 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h9'
  set η := g ^ (orderOf g / 9) with hη
  have hωo : orderOf (η ^ 3) = 3 := by
    rw [orderOf_pow' η (by norm_num), hηo]
    norm_num
  have hω3 : (η ^ 3) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (η ^ 3)
    rwa [hωo] at h
  have hω1 : η ^ 3 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωo
    norm_num at hωo
  set x : projectiveSL 3 K := proj 3 K (dg3 (η, η)) with hx
  set y : projectiveSL 3 K := proj 3 K (dg3 (η ^ 3, 1)) with hy
  have hxD : x ∈ dL3 K := ⟨dg3 (η, η), ⟨(η, η), rfl⟩, rfl⟩
  have hyD : y ∈ dL3 K := ⟨dg3 (η ^ 3, 1), ⟨(η ^ 3, 1), rfl⟩, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow, ← map_pow, proj_eq_one_iff]
    exact dg3_mem_scalars_nine hω3
  have hx1 : x ≠ 1 := by
    intro h
    obtain ⟨c, hc, hcη⟩ := dg3_scalar_nine (proj_eq_one_iff.1 h)
    have hη3 : η ^ 3 = 1 := by
      rw [show η = c from congrArg Prod.fst hcη]
      exact hc
    exact hω1 hη3
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← map_pow, ← map_pow,
      show ((η ^ 3, 1) : Kˣ × Kˣ) ^ 3 = 1 from Prod.ext hω3 (one_pow 3), map_one, map_one]
  have hyx : y ∉ zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [hx, hy, ← map_zpow, ← map_zpow, proj_eq_proj_iff, ← map_inv, ← map_mul] at hk
    obtain ⟨c, -, hc⟩ := dg3_scalar_nine hk
    have h1 := congrArg Prod.fst hc
    have h2 := congrArg Prod.snd hc
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Prod.pow_fst,
      Prod.pow_snd, mul_one] at h1 h2
    rw [← h2] at h1
    exact hω1 (mul_left_cancel (h1.trans (mul_one _).symm))
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 fun h => hyx (h ▸ one_mem _)
  obtain ⟨hQe, hQc⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
    (X := zpowers x) (by rw [Nat.card_zpowers, hxo]) hyo hyx
    fun a ha => dL3_comm_nine ((zpowers_le.2 hxD) ha) hyD
  exact ⟨zpowers x ⊔ zpowers y, sup_le (zpowers_le.2 hxD) (zpowers_le.2 hyD), hQe, hQc⟩

end Cartan

section Model

theorem uc22s218_l3_torus_nine {Y : Type} [Group Y] {n : ℕ} (hY : IsL3 Y n) (h9 : 9 ∣ 2 ^ n - 1)
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hrn : r ∣ 2 ^ n - 1) :
    ∃ E Q : Subgroup Y, IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ IsElemAbelian 3 Q ∧
      Nat.card Q = 3 ^ 2 ∧ ∀ x ∈ Q, ∀ e ∈ E, x * e = e * x := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  obtain ⟨A, hAD, hAe, hAc⟩ := uc22s218_l3_exists_elemAbelian hr hr3 (by rw [hK]; exact hrn)
  obtain ⟨Q, hQD, hQe, hQc⟩ := uc22s218_l3_exists_elemAbelian_nine (K := K) (by rw [hK]; exact h9)
  refine ⟨A.map e.symm.toMonoidHom, Q.map e.symm.toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map hAe _, ?_, CFSG.SectionRank.isElemAbelian_map hQe _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hAc]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hQc]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, dL3_comm_nine (hQD hx) (hAD ha)]

theorem uc22s218_l3_pRank_le_one {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hpK1 : ¬ p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  rw [CFSG.LieType.OutStructure.pRank_projectiveSL_formula hp hp2 (by norm_num) hpK
    (fun h => hpK1 (h.trans (Nat.gcd_dvd_right _ _))), if_neg hpK1]
  have h1 : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    intro h
    apply hpK1
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    rw [← ZMod.natCast_eq_zero_iff]
    have h2 : ((Nat.card K - 1 : ℕ) : ZMod p) + 1 = 1 := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hK1, h]
    exact add_eq_right.1 h2
  rcases Nat.lt_or_ge (orderOf ((Nat.card K : ℕ) : ZMod p)) 2 with h | h
  · have h0 : orderOf ((Nat.card K : ℕ) : ZMod p) = 0 := by omega
    rw [h0, Nat.div_zero]
    exact zero_le_one
  · exact (Nat.div_le_div_left h (by norm_num)).trans (by norm_num)

end Model

section Pair

variable {G : Type} [Group G] [Finite G]

theorem uc22s218_card_center_bar2_dvd_three {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hX : IsL3 (BarInf L) n) (hn : 2 < n) :
    Nat.card (center (Bar2 L)) ∣ 3 ∧ (3 ∣ Nat.card (center (Bar2 L)) → 3 ∣ 2 ^ n - 1) := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hX' : IsL3 (Bar2 L ⧸ center (Bar2 L)) n := LieModel.of_mulEquiv e hX
  obtain ⟨F, _, _, _, α, hF, hα, hαc⟩ := uc22pwI3_exists_cover hq hn hX'
  have hZ : center (Bar2 L) = (center (Matrix.SpecialLinearGroup (Fin 3) F)).map α := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect
      (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)) α hα hαc,
      Subgroup.map_comap_eq_self_of_surjective hα]
  have hdvd : Nat.card (center (Bar2 L)) ∣
      Nat.card (center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    rw [hZ]
    exact Subgroup.card_map_dvd _ α
  have hμ : Nat.card (center (Matrix.SpecialLinearGroup (Fin 3) F)) =
      Nat.card (rootsOfUnity 3 F) := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
    congr 2
  have hμ3 : Nat.card (rootsOfUnity 3 F) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    exact Subtype.ext ((mem_rootsOfUnity 3 _).mp g.2)
  refine ⟨hdvd.trans (hμ ▸ hμ3), fun h3 => ?_⟩
  have h := (h3.trans hdvd).trans (hμ ▸ Subgroup.card_subgroup_dvd_card (rootsOfUnity 3 F))
  rwa [Nat.card_units, hF] at h

theorem exists_mem_kernel_of_pRank_lt {L M : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (K : Subgroup ↥L) [K.Characteristic] {p : ℕ} (hp : p.Prime)
    (hlt : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥L ⧸ K))) < CFSG.Open.pRank p M) :
    ∃ (x : G) (hx : x ∈ M), x ≠ 1 ∧ x ^ p = 1 ∧
      uc22s218_rhoK L K ⟨x, le_normalizer_of_normal_subgroupOf hLM hx⟩ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨A, hAM, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hlt
  let ρA : ↥A →* MulAut (↥L ⧸ K) := (uc22s218_rhoK L K).comp (Subgroup.inclusion (hAM.trans hML))
  have : IsMulCommutative ↥A := hAel.1
  have hnotinj : ¬ Function.Injective ρA := fun hinj => by
    have h4 := CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
      (fun a => Subtype.ext (hAel.2 _ a.2)) hAc ρA hinj (H := ⊤) le_top
    omega
  obtain ⟨a, ha1, hρa⟩ : ∃ a : ↥A, a ≠ 1 ∧ ρA a = 1 := by
    by_contra h
    exact hnotinj ((injective_iff_map_eq_one ρA).2 fun a ha =>
      by_contra fun h' => h ⟨a, h', ha⟩)
  exact ⟨(a : G), hAM a.2, fun h => ha1 (Subtype.ext h), hAel.2 _ a.2, hρa⟩

omit [Finite G] in
private theorem pair_map_subtype {L : Subgroup G} {p r : ℕ} {E Q : Subgroup ↥L}
    (hE : IsElemAbelian r E) (hEc : Nat.card E = r ^ 2) (hQ : IsElemAbelian p Q)
    (hQc : Nat.card Q = p ^ 2) (hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ L ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  refine ⟨E.map L.subtype, Q.map L.subtype, Subgroup.map_subtype_le E, hE.map _, ?_,
    Subgroup.map_subtype_le Q, hQ.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hQc]
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hpow q hq
    refine ⟨k, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have h := congrArg (fun z : ↥L => (z : G)) (hk e he)
    simpa using h

theorem exists_pair_L3_three {L M : Subgroup G} (hL : L ∈ calC M) [(L.subgroupOf M).Normal]
    {n : ℕ} (hX : IsL3 (BarInf L) n) (hn : ¬ IsPowTwo n) (h3M : 3 ≤ CFSG.Open.pRank 3 M)
    (h3 : 3 ∣ 2 ^ n - 1) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ M := hL.1.le
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hr3 : r ≠ 3 := fun h => uc22s218_l3_not_three_dvd hs (h ▸ hrs)
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hn0 : 1 ≤ n := (LieModel.admissible hX).2.1
  have hn1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
  have hn2 : n ≠ 2 := fun h => hn ⟨1, by simp [h]⟩
  have h2n : 2 ∣ n := by
    by_contra h
    exact uc22s218_l3_not_three_dvd (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)) h3
  obtain ⟨hZ3, -⟩ := uc22s218_card_center_bar2_dvd_three hL hX (by omega)
  have hrZ : ¬ r ∣ Nat.card (center (Bar2 L)) := fun h =>
    hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (h.trans hZ3))
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hr hr2 hrZ
  have hpow1 : ∀ {Y : Type} [Group Y] {E₀ Q₀ : Subgroup Y},
      (∀ x ∈ Q₀, ∀ e ∈ E₀, x * e = e * x) →
        ∀ x ∈ Q₀, ∃ k : ℕ, ∀ e ∈ E₀, x * e * x⁻¹ = e ^ k := fun hc x hx =>
    ⟨1, fun e he => by rw [pow_one, mul_inv_eq_iff_eq_mul]; exact hc x hx e he⟩
  by_cases hZ : 3 ∣ Nat.card (center (Bar2 L))
  ·
    have : (CFSG.pCore 2 ↥L).Characteristic := CFSG.pCore_characteristic
    have hK2 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      intro ℓ hℓ hℓ2 hdvd
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk] at hdvd
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hdvd))
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
    have hX' : IsL3 (Bar2 L ⧸ center (Bar2 L)) n := LieModel.of_mulEquiv e hX
    obtain ⟨F, _, _, _, α, hF, hα, hαc⟩ := uc22pwI3_exists_cover hq (by omega) hX'
    obtain ⟨E₀, y, hE₀, hE₀c, hyo, hyE, hyZ⟩ := uc22s218_l3_cover_pair_data α hα hαc hr hr3
      (by rw [hF]; exact hrn) (by rw [hF]; exact h3)
    obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center (Bar2 L))) 3 hZ
    have hzo' : orderOf (z : Bar2 L) = 3 := by rw [Subgroup.orderOf_coe, hzo]
    have hzZ : zpowers (z : Bar2 L) ≤ center (Bar2 L) := zpowers_le.2 z.2
    have hyz : y ∉ zpowers (z : Bar2 L) := fun h => by
      obtain ⟨w, hw⟩ := hyZ
      exact hw ((Subgroup.mem_center_iff.1 (hzZ h) w))
    obtain ⟨hQe, hQc⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
      (X := zpowers (z : Bar2 L)) (by rw [Nat.card_zpowers, hzo']) hyo hyz
      fun a ha => (Subgroup.mem_center_iff.1 (hzZ ha) y).symm
    have hQE : ∀ x ∈ zpowers (z : Bar2 L) ⊔ zpowers y, ∀ e ∈ E₀, x * e = e * x := by
      have hle : zpowers (z : Bar2 L) ⊔ zpowers y ≤ centralizer (E₀ : Set (Bar2 L)) :=
        sup_le (hzZ.trans (Subgroup.center_le_centralizer _))
          (zpowers_le.2 (mem_centralizer_iff.2 fun e he => (hyE e he).symm))
      exact fun x hx e he => (mem_centralizer_iff.1 (hle hx) e he).symm
    obtain ⟨E₁, Q₁, hE₁, hE₁c, hQ₁, hQ₁c, hpow₁⟩ := exists_pair_lift (CFSG.pCore 2 ↥L)
      Nat.prime_three hr (Ne.symm hr3) (hK2 3 Nat.prime_three (by norm_num)) (hK2 r hr hr2) hE₀
      hE₀c hQe hQc (hpow1 hQE)
    obtain ⟨E, Q, hEL, hEe, hEc, hQL, hQe', hQc', hpow⟩ :=
      pair_map_subtype hE₁ hE₁c hQ₁ hQ₁c hpow₁
    exact ⟨E, Q, hEL, hEe, hEc, hQL.trans hLM, hQe', hQc', hpow⟩
  have h3K : ¬ 3 ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 Nat.prime_three (by norm_num) hZ
  by_cases h9 : 9 ∣ 2 ^ n - 1
  ·
    obtain ⟨E₀, Q₀, hE₀, hE₀c, hQ₀, hQ₀c, hQE⟩ := uc22s218_l3_torus_nine hX h9 hr hr3 hrn
    obtain ⟨E₁, Q₁, hE₁, hE₁c, hQ₁, hQ₁c, hpow₁⟩ := exists_pair_lift (CFSG.solvableRadical ↥L)
      Nat.prime_three hr (Ne.symm hr3) h3K hrK hE₀ hE₀c hQ₀ hQ₀c (hpow1 hQE)
    obtain ⟨E, Q, hEL, hEe, hEc, hQL, hQe', hQc', hpow⟩ :=
      pair_map_subtype hE₁ hE₁c hQ₁ hQ₁c hpow₁
    exact ⟨E, Q, hEL, hEe, hEc, hQL.trans hLM, hQe', hQc', hpow⟩
  have h3n : ¬ 3 ∣ n := fun h => h9 ((show 9 ∣ 2 ^ 6 - 1 by norm_num).trans
    (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2n h)))
  have haut := uc22s218_l3_pRank_mulAut_le_two hX h2n h3n
  obtain ⟨x, hxM, hx1, hxp, hρ⟩ :=
    exists_mem_kernel_of_pRank_lt hLM (CFSG.solvableRadical ↥L) Nat.prime_three (by omega)
  obtain ⟨T, hTc, hTE, y, hyT, hyo⟩ := uc22s218_l3_torus_order_three hX h3
  obtain ⟨E₀, hE₀T, hE₀, hE₀c⟩ := hTE r hr hrn hr3
  refine uc22s218_exists_pair_of_kernel_elem hLM (CFSG.solvableRadical ↥L) Nat.prime_three hr
    (Ne.symm hr3) h3K hrK hxM hx1 hxp hρ hE₀ hE₀c hyo (fun e he => hTc y hyT e (hE₀T he)) ?_
  by_contra hcen
  have hy1 := uc22s218_l3_center_eq_one hX y fun x =>
    (by_contra fun h => hcen ⟨x, h⟩ : x * y = y * x).symm
  rw [hy1, orderOf_one] at hyo
  exact absurd hyo (by norm_num)

end Pair

section Main

variable {G : Type} [Group G] [Finite G]

theorem uc22s218x_false_L3 (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsL3 (BarInf L) n)
    (hn : ¬ IsPowTwo n) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hF := torusFacts218_L3 hX
  have hn0 : 1 ≤ n := (LieModel.admissible hX).2.1
  have hn1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
  have hn2 : n ≠ 2 := fun h => hn ⟨1, by simp [h]⟩
  obtain ⟨hZ3, hZ3'⟩ := uc22s218_card_center_bar2_dvd_three hL hX (by omega)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center (Bar2 L)) →
      ¬ (ℓ ∣ 2 ^ n - 1 ∧ ℓ ≠ 3) ∧ ¬ ¬ ℓ ∣ 2 ^ n - 1 := by
    intro ℓ hℓ hdvd
    have hℓ3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hdvd.trans hZ3)
    subst hℓ3
    exact ⟨fun h => h.2 rfl, fun h => h (hZ3' hdvd)⟩
  have : (L.subgroupOf D.M).Normal := normal_of_facts D Ch hSg h211 hH c hL hF hZ hn
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hpσ
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpσ
  obtain ⟨s, hs, hs1, hsn⟩ := PartTwo.s13_exists_odd_divisor hn
  have hCL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded q D.M :=
    fun q hq hq2 hqs => not_stronglyEmbedded_of_facts D Ch h211 hH c hLM hML hF hs hsn hq hq2 hqs
  have hps : ¬ p ∣ 2 ^ s - 1 := fun h => hCL p hp hp2 h hsp
  have hs3 : 3 ≤ s := by
    obtain ⟨k, rfl⟩ := hs
    omega
  have h8 : 8 ≤ 2 ^ s :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ s - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrs
  have hrσ : r ∉ D.sig := fun hrσ => hCL r hr hr2 hrs (UC6S846.sp_of_mem_sig hSg hns hrσ)
  have hpr : p ≠ r := by
    rintro rfl
    exact hps hrs
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hr hr2 fun h => (hZ r hr h).1 (hF.tor_of_dvd hs hsn hr hrs)
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hTp : p ∣ 2 ^ n - 1 ∧ p ≠ 3
    · have hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L) :=
        not_dvd_card_solvableRadical hL.2.2 hp hp2 fun h => (hZ p hp h).1 hTp
      obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        exists_pair_of_tor hF hs hsn hr hrs hp hTp hpr hpK hrK
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    by_cases hOp : ¬ p ∣ 2 ^ n - 1
    · have hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L) :=
        not_dvd_card_solvableRadical hL.2.2 hp hp2 fun h => (hZ p hp h).2 hOp
      have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
        have h1 := uc22s218_l3_pRank_le_one hX hp hp2 hOp
        rw [← pRank_eq_pRank_barInf hp hpK] at h1
        omega
      exact exists_pair_of_out hLM hF hs hsn hp hp2 hOp hpK hr hr2 hrs hrK hpr hrank
    have hp1 : p ∣ 2 ^ n - 1 := not_not.1 hOp
    have hp3 : p = 3 := by
      by_contra h
      exact hTp ⟨hp1, h⟩
    subst hp3
    exact exists_pair_L3_three hL hX hn h3 hp1 hs hsn hr hrs
  exact hCL r hr hr2 hrs (stronglyEmbedded_of_torus_of_facts D hSg h614 hL hML hF hs hsn hp
    (h76 p hpσ hsp) hr hr2 hrs hrK hrσ hEL hEel hEc hQM hQel hQc hpow)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
