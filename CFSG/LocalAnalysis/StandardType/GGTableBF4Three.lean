module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4ThreeWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBF4

theorem geomSum_mod (q k m : ℕ) :
    (∑ i ∈ Finset.range k, q ^ i) % m = (∑ i ∈ Finset.range k, (q % m) ^ i % m) % m := by
  rw [Finset.sum_nat_mod]
  exact congrArg (· % m) (Finset.sum_congr rfl fun i _ => Nat.pow_mod q i m)

theorem exists_nine_mul_geomSums {q : ℕ} (hq : 1 ≤ q) (h3 : 3 ∣ q - 1) :
    ∃ M : ℕ, q ^ 24 * ((∑ i ∈ Finset.range 12, q ^ i) * (∑ i ∈ Finset.range 8, q ^ i) *
      (∑ i ∈ Finset.range 6, q ^ i) * (∑ i ∈ Finset.range 2, q ^ i)) = 9 * M ∧ ¬ 3 ∣ M := by
  have hr : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
  have h12 : (∑ i ∈ Finset.range 12, q ^ i) % 9 = 3 := by
    rw [geomSum_mod]
    rcases hr with h | h | h <;> rw [h] <;> decide
  have h6 : (∑ i ∈ Finset.range 6, q ^ i) % 9 = 6 := by
    rw [geomSum_mod]
    rcases hr with h | h | h <;> rw [h] <;> decide
  have h8 : (∑ i ∈ Finset.range 8, q ^ i) % 3 = 2 := by
    rw [geomSum_mod]
    have : q % 3 = 1 := by omega
    rw [this]
    decide
  have h2 : (∑ i ∈ Finset.range 2, q ^ i) % 3 = 2 := by
    rw [geomSum_mod]
    have : q % 3 = 1 := by omega
    rw [this]
    decide
  set G12 := ∑ i ∈ Finset.range 12, q ^ i
  set G8 := ∑ i ∈ Finset.range 8, q ^ i
  set G6 := ∑ i ∈ Finset.range 6, q ^ i
  set G2 := ∑ i ∈ Finset.range 2, q ^ i
  refine ⟨q ^ 24 * ((3 * (G12 / 9) + 1) * G8 * (3 * (G6 / 9) + 2) * G2), ?_, ?_⟩
  · have e12 : G12 = 3 * (3 * (G12 / 9) + 1) := by omega
    have e6 : G6 = 3 * (3 * (G6 / 9) + 2) := by omega
    conv_lhs => rw [e12, e6]
    ring
  · have hp := Nat.prime_three
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := hp.dvd_of_dvd_pow h
      omega
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h <;> omega
        · omega
      · omega

section X


variable (K : Type) [Field K]

@[expose] noncomputable def weylX₀ : Subgroup (monomialSubgroup .F4 K) :=
  weylS.comap (weylQuotientHom .F4 K)

@[expose] noncomputable def weylX : Subgroup (adjointGroup .F4 K) :=
  ((weylX₀ K).map (monomialSubgroup .F4 K).subtype).subgroupOf (adjointGroup .F4 K)

variable {K}

theorem weylQuotientHom_surjective_ker :
    Function.Surjective (weylQuotientHom .F4 K) ∧
      (weylQuotientHom .F4 K).ker = (torusGroup .F4 K).subgroupOf (monomialSubgroup .F4 K) := by
  obtain ⟨-, ⟨ρ, hsurj, hmaps, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient .F4 K
  have hρ : weylQuotientHom .F4 K = ρ := MonoidHom.ext fun g => weylQuotientHom_eq (hmaps g)
  rw [hρ]
  exact ⟨hsurj, hker⟩

theorem mem_weylX {g : adjointGroup .F4 K} :
    g ∈ weylX K ↔ ∃ hg : (g : ModGL .F4 K) ∈ monomialSubgroup .F4 K,
      weylQuotientHom .F4 K ⟨g, hg⟩ ∈ weylS := by
  rw [weylX, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm, hmg⟩
    have hg : (g : ModGL .F4 K) ∈ monomialSubgroup .F4 K := hmg ▸ m.2
    refine ⟨hg, ?_⟩
    have : m = ⟨g, hg⟩ := Subtype.ext hmg
    rw [← this]
    exact hm
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem card_weylX₀ [Finite K] : Nat.card (weylX₀ K) = 9 * (Nat.card K - 1) ^ 4 := by
  obtain ⟨hsurj, hker⟩ := weylQuotientHom_surjective_ker (K := K)
  set ρ := weylQuotientHom .F4 K with hρdef
  set f : weylX₀ K →* WeylGroup .F4 := ρ.comp (weylX₀ K).subtype with hf
  have hrange : f.range = weylS := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hw
      obtain ⟨m, rfl⟩ := hsurj w
      exact ⟨⟨m, hw⟩, rfl⟩
  have hkerle : ρ.ker ≤ weylX₀ K := fun m hm => by
    show ρ m ∈ weylS
    rw [MonoidHom.mem_ker.mp hm]
    exact one_mem _
  have hfker : f.ker = ρ.ker.subgroupOf (weylX₀ K) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have h1 := TableB.card_range_mul_card_ker f
  rw [hrange, card_weylS, hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv,
    hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show torusGroup .F4 K ≤ monomialSubgroup .F4 K from le_sup_left)).toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_F4] at h1
  exact h1.symm

theorem card_weylX [Finite K] : Nat.card (weylX K) = 9 * (Nat.card K - 1) ^ 4 := by
  have hle : (weylX₀ K).map (monomialSubgroup .F4 K).subtype ≤ adjointGroup .F4 K :=
    (Subgroup.map_subtype_le _).trans monomialSubgroup_le_adjointGroup'
  rw [weylX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Subgroup.card_map_of_injective (monomialSubgroup .F4 K).subtype_injective, card_weylX₀]


theorem not_three_dvd_index_weylX [Finite K] (h3 : 3 ∣ Nat.card K - 1) : ¬ 3 ∣ (weylX K).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨M, hM, hM3⟩ := exists_nine_mul_geomSums hq h3
  have hcard := Subgroup.card_mul_index (weylX K)
  rw [card_weylX, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, ordF4_eq_mul hq, hM]
    at hcard
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < 9 * (Nat.card K - 1) ^ 4 := Nat.mul_pos (by norm_num) (pow_pos (by omega) 4)
  have h2 : (weylX K).index = M := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hcard]
    ring
  rw [h2]
  exact hM3

end X

theorem exists_conj_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hidx : ¬ p ∣ X.index) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ X := by
  have := Fact.mk hp
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p X))
  have hPp : IsPGroup p ((P : Subgroup X).map X.subtype) := P.isPGroup'.map _
  have hPidx : ¬ p ∣ ((P : Subgroup X).map X.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact P.not_dvd_index h
    · exact hidx h
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hPp.toSylow hPidx)
  refine ⟨g, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hmem : (MulAut.conj g).toMonoidHom e ∈ ((g • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    convert hEQ he using 1
    simp only [MulAut.smul_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  rw [hg] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  rw [← hz]
  exact z.2

theorem card_le_card_filter_of_forall {α β : Type*} [Fintype β] [DecidableEq β] {s : Set α}
    (P : β → Prop) [DecidablePred P] (f : β → α) (h : ∀ a ∈ s, ∃ b, f b = a ∧ P b) :
    Nat.card s ≤ (Finset.univ.filter P).card := by
  classical
  choose g hg using h
  have hinj : Function.Injective (fun a : s => (⟨g a a.2, (hg a a.2).2⟩ : {b // P b})) := by
    intro a a' haa'
    have h1 := congrArg (fun b : {b // P b} => f b.1) haa'
    simp only at h1
    rw [(hg a a.2).1, (hg a' a'.2).1] at h1
    exact Subtype.ext h1
  calc Nat.card s ≤ Nat.card {b // P b} := Nat.card_le_card_of_injective _ hinj
    _ = (Finset.univ.filter P).card := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

section Count

variable {K : Type} [Field K]

theorem range_chevTorus_eq_torusPow [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (chevTorus .F4 ζ hζ).range = torusPow K 3 := by
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod 3) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  have hle : (chevTorus .F4 ζ hζ).range ≤ torusPow K 3 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(torusCoordHom .F4 K (chevTorusExp .F4 ζ hζ x)).2, ?_⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_torusPow Nat.prime_three h3,
    ← Nat.card_congr (MonoidHom.ofInjective (chevTorus_injective hζo hζ hdet)).toEquiv,
    card_multiplicative_fin_zmod]
  rfl

end Count

section Main

variable {K : Type} [Field K]

theorem eq_torusPow_of_le_weylX [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) (hEX : E ≤ weylX K)
    (hcard : 3 ^ 4 ≤ Nat.card E) : E = torusPow K 3 := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod 3) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  have hφinj := chevTorus_injective hζo hζ hdet
  have hφrange := range_chevTorus_eq_torusPow h3 hζo hζ
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (K := K)
  have hEM : ∀ e : E, ((e : adjointGroup .F4 K) : ModGL .F4 K) ∈ monomialSubgroup .F4 K :=
    fun e => (mem_weylX.mp (hEX e.2)).1
  let ι : E →* monomialSubgroup .F4 K :=
    ((adjointGroup .F4 K).subtype.comp E.subtype).codRestrict _ hEM
  let ψ : E →* WeylGroup .F4 := (weylQuotientHom .F4 K).comp ι
  have hψS : ∀ e : E, ψ e ∈ weylS := fun e => (mem_weylX.mp (hEX e.2)).2
  have hkerH : ∀ e : E, ψ e = 1 →
      ((e : adjointGroup .F4 K) : ModGL .F4 K) ∈ torusGroup .F4 K := by
    intro e he
    have h1 : ι e ∈ (weylQuotientHom .F4 K).ker := he
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hkerV : ∀ e : E, ψ e = 1 → (e : adjointGroup .F4 K) ∈ torusPow K 3 := fun e he =>
    ⟨hkerH e he, hE.2 _ e.2⟩
  have hfix : ∀ (e₀ : E) (ω : List (Fin Tag.F4.rank)), ψ e₀ = (coxeterSystem .F4).wordProd ω →
      ∀ e : E, ψ e = 1 → ∃ x : Fin Tag.F4.rank → ZMod 3,
        chevTorus .F4 ζ hζ (.ofAdd x) = (e : adjointGroup .F4 K) ∧ torusWordF4 ω x = x := by
    intro e₀ ω hω e he
    obtain ⟨x, hx⟩ : (e : adjointGroup .F4 K) ∈ (chevTorus .F4 ζ hζ).range :=
      hφrange ▸ hkerV e he
    refine ⟨Multiplicative.toAdd x, by rw [ofAdd_toAdd]; exact hx, ?_⟩
    set n := nWordF4 K ω with hn
    have hm := coe_nWordF4_mem_monomialSubgroup (K := K) ω
    have hρ : weylQuotientHom .F4 K (ι e₀ * (⟨_, hm⟩ : monomialSubgroup .F4 K)⁻¹) = 1 := by
      rw [map_mul, map_inv, weylQuotientHom_nWordF4]
      change ψ e₀ * _ = 1
      rw [hω, mul_inv_cancel]
    have hh : (((e₀ : adjointGroup .F4 K) * n⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈
        torusGroup .F4 K := by
      have h1 : ι e₀ * (⟨_, hm⟩ : monomialSubgroup .F4 K)⁻¹ ∈ (weylQuotientHom .F4 K).ker := hρ
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hc0 : (e₀ : adjointGroup .F4 K) * e = e * e₀ := TableB.IsElemAbelian.comm hE e₀.2 e.2
    have hch : ((e₀ : adjointGroup .F4 K) * n⁻¹) * e = e * ((e₀ : adjointGroup .F4 K) * n⁻¹) :=
      Subtype.ext (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
        (torusGroup_le_diagonalGroup (hkerH e he)))
    have hne : n * (e : adjointGroup .F4 K) * n⁻¹ = e := by
      set h := (e₀ : adjointGroup .F4 K) * n⁻¹ with hhdef
      have hn' : n = h⁻¹ * e₀ := by
        rw [hhdef]
        group
      have hc0' : (e₀ : adjointGroup .F4 K) * e * (e₀ : adjointGroup .F4 K)⁻¹ = e := by
        rw [hc0]
        group
      have hch' : h⁻¹ * (e : adjointGroup .F4 K) * h = e := by
        rw [mul_assoc, ← hch]
        group
      rw [hn', mul_inv_rev, inv_inv]
      calc h⁻¹ * (e₀ : adjointGroup .F4 K) * e * ((e₀ : adjointGroup .F4 K)⁻¹ * h) =
          h⁻¹ * ((e₀ : adjointGroup .F4 K) * e * (e₀ : adjointGroup .F4 K)⁻¹) * h := by group
        _ = h⁻¹ * e * h := by rw [hc0']
        _ = e := hch'
    have hconj := nWordF4_conj_chevTorus hζ ω (Multiplicative.toAdd x)
    rw [ofAdd_toAdd, hx, hne] at hconj
    exact congrArg Multiplicative.toAdd (hφinj (hconj.symm.trans hx.symm))
  have hkercard : ∀ (P : (Fin Tag.F4.rank → ZMod 3) → Prop) [DecidablePred P],
      (∀ e : E, ψ e = 1 → ∃ x, chevTorus .F4 ζ hζ (.ofAdd x) = (e : adjointGroup .F4 K) ∧ P x) →
      Nat.card ψ.ker ≤ (Finset.univ.filter P).card := by
    intro P _ hP
    have h1 : Nat.card ψ.ker = Nat.card ((ψ.ker.map E.subtype : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) :=
      (Subgroup.card_map_of_injective E.subtype_injective).symm
    rw [h1]
    refine card_le_card_filter_of_forall P (fun x => chevTorus .F4 ζ hζ (.ofAdd x)) ?_
    rintro _ ⟨e, he, rfl⟩
    exact hP e he
  have hcardE := TableB.card_range_mul_card_ker ψ
  by_cases hr : ψ.range = ⊥
  · have hEle : E ≤ torusPow K 3 := fun e he => by
      have h1 : ψ ⟨e, he⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hr, Subgroup.mem_bot] at h1
      exact hkerV ⟨e, he⟩ h1
    exact Subgroup.eq_of_le_of_card_ge hEle (by rw [card_torusPow Nat.prime_three h3]; exact hcard)
  · exfalso
    have hrS : ψ.range ≤ weylS := by
      rintro _ ⟨e, rfl⟩
      exact hψS e
    have hr9 : Nat.card ψ.range ∣ 9 := card_weylS ▸ Subgroup.card_dvd_of_le hrS
    have hr1 : Nat.card ψ.range ≠ 1 := fun h => hr (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ ψ.range, w ≠ 1 := by
      by_contra hcon
      apply hr
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      by_contra hw1
      exact hcon ⟨w, hw, hw1⟩
    obtain ⟨e₀, rfl⟩ := hw
    obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_of_mem_weylS (hψS e₀)
    have hω : ψ e₀ = (coxeterSystem .F4).wordProd (wordAB a b) := by rw [wordProd_wordAB, hab]
    have hab0 : ((⟨a, ha⟩ : Fin 3), (⟨b, hb⟩ : Fin 3)) ≠ (0, 0) := by
      intro h
      have h1 : a = 0 := congrArg Fin.val (congrArg Prod.fst h)
      have h2 : b = 0 := congrArg Fin.val (congrArg Prod.snd h)
      apply hw1
      rw [hab, h1, h2, pow_zero, pow_zero, mul_one]
    have hk9 : Nat.card ψ.ker ≤ 9 :=
      (hkercard _ fun e he => hfix e₀ (wordAB a b) hω e he).trans
        (card_fix_torusWordF4_le ⟨a, ha⟩ ⟨b, hb⟩ hab0)
    have hcases : Nat.card ψ.range = 3 ∨ Nat.card ψ.range = 9 := by
      have h1 : Nat.card ψ.range ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hr9, by norm_num⟩
      have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [h9] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      omega
    rcases hcases with h | h
    · rw [h] at hcardE
      omega
    · have hrS' : ψ.range = weylS :=
        Subgroup.eq_of_le_of_card_ge hrS (by rw [h, card_weylS])
      obtain ⟨e₁, he₁⟩ : weylW1 ∈ ψ.range := hrS' ▸ weylW1_mem_weylS
      obtain ⟨e₂, he₂⟩ : weylW2 ∈ ψ.range := hrS' ▸ weylW2_mem_weylS
      have hk3 : Nat.card ψ.ker ≤ 3 := by
        refine (hkercard (fun x => torusWordF4 word1 x = x ∧ torusWordF4 word2 x = x)
          fun e he => ?_).trans card_fix_word1_word2_le
        obtain ⟨x, hx, hx1⟩ := hfix e₁ word1 he₁ e he
        obtain ⟨y, hy, hy2⟩ := hfix e₂ word2 he₂ e he
        have hxy : x = y := congrArg Multiplicative.toAdd (hφinj (hx.trans hy.symm))
        exact ⟨x, hx, hx1, hxy ▸ hy2⟩
      rw [h] at hcardE
      omega


theorem ggF4ToralRankInput_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    GGF4ToralRankInput K 3 := by
  intro E hE hcard
  have : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  obtain ⟨g, hg⟩ := exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_weylX h3) (TableB.isPGroup_of_isElemAbelian hE)
  refine ⟨g, eq_torusPow_of_le_weylX h3 (TableB.isElemAbelian_map hE _) hg ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hcard

end Main

end TableBF4

theorem ggF4ThreeRankInput_holds :
    GGF4ThreeRankInput :=
  fun _ _ _ _ h3 => TableBF4.ggF4ToralRankInput_three h3

end CFSG.StandardType
