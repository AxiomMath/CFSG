module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.RankThree.CentralCover.SteinbergBNEvenCommutingSL2SplitPrime
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.CentralCover
open scoped MatrixGroups

section ToQuot

variable {H : Type} {C : Type*} [Group H] [Group C]

theorem map_mem_commutator (Ψ : C →* H) (hC : commutator C = ⊤) (c : C) :
    Ψ c ∈ commutator H := by
  have hc : c ∈ commutator C := hC ▸ Subgroup.mem_top c
  rw [commutator_def] at hc ⊢
  have h : Ψ c ∈ Subgroup.map Ψ ⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆ := ⟨c, hc, rfl⟩
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono le_top le_top h

@[expose] noncomputable def toQuot (Ψ : C →* H) (hC : commutator C = ⊤) :
    C →* TauCeti.DerivedCentralQuotient H :=
  (QuotientGroup.mk' (Subgroup.center ↥(commutator H))).comp
    (Ψ.codRestrict (commutator H) (map_mem_commutator Ψ hC))

theorem toQuot_eq_one_iff (Ψ : C →* H) (hC : commutator C = ⊤) (c : C) :
    toQuot Ψ hC c = 1 ↔ ∀ y ∈ commutator H, Ψ c * y = y * Ψ c := by
  rw [toQuot, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro h y hy
    exact (congrArg Subtype.val (h ⟨y, hy⟩)).symm
  · intro h z
    exact Subtype.ext (h z z.2).symm

variable {Ψ : C →* H}

theorem mem_center_of_toQuot_eq_one (hΨ : Function.Injective Ψ) (hC : commutator C = ⊤) {c : C}
    (h : toQuot Ψ hC c = 1) : c ∈ Subgroup.center C := by
  rw [Subgroup.mem_center_iff]
  intro c'
  apply hΨ
  rw [map_mul, map_mul]
  exact ((toQuot_eq_one_iff Ψ hC c).1 h (Ψ c') (map_mem_commutator Ψ hC c')).symm

theorem toQuot_injective (hΨ : Function.Injective Ψ) (hC : commutator C = ⊤)
    (hZ : Subgroup.center C = ⊥) : Function.Injective (toQuot Ψ hC) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  have := mem_center_of_toQuot_eq_one hΨ hC (MonoidHom.mem_ker.1 hc)
  rwa [hZ] at this

theorem toQuot_comp_injective (hΨ : Function.Injective Ψ) (hC : commutator C = ⊤) {S : Type*}
    [Group S] (ρ : S →* C) (hρ : ∀ A, ρ A ∈ Subgroup.center C → A = 1) :
    Function.Injective ((toQuot Ψ hC).comp ρ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  exact hρ A (mem_center_of_toQuot_eq_one hΨ hC (MonoidHom.mem_ker.1 hA))

theorem toQuot_injOn (hΨ : Function.Injective Ψ) (hC : commutator C = ⊤) {E : Subgroup C}
    (hEZ : E ⊓ Subgroup.center C = ⊥) : Set.InjOn (toQuot Ψ hC) E := by
  intro a ha b hb hab
  have h1 : toQuot Ψ hC (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  have h2 : a⁻¹ * b ∈ E ⊓ Subgroup.center C :=
    ⟨E.mul_mem (E.inv_mem ha) hb, mem_center_of_toQuot_eq_one hΨ hC h1⟩
  rw [hEZ, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

theorem le_localRank_of_toQuot [Finite (TauCeti.DerivedCentralQuotient H)]
    (hΨ : Function.Injective Ψ) (hC : commutator C = ⊤) {p k : ℕ} (hp : p.Prime)
    {E P : Subgroup C} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEZ : E ⊓ Subgroup.center C = ⊥) (hP2 : IsPGroup 2 P) (hPZ : ¬ P ≤ Subgroup.center C)
    (hEP : E ≤ Subgroup.normalizer (P : Set C)) :
    k ≤ localRank p (TauCeti.DerivedCentralQuotient H) := by
  set θ := toQuot Ψ hC
  refine le_localRank_of_le_normalizer hp (P := P.map θ) (E := E.map θ) ?_ (hP2.map θ) ?_ ?_
    ((Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map θ))
  · intro hbot
    apply hPZ
    intro x hx
    have h1 : θ x = 1 := by
      have : θ x ∈ P.map θ := ⟨x, hx, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    exact mem_center_of_toQuot_eq_one hΨ hC h1
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      change (a : TauCeti.DerivedCentralQuotient H) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg θ (congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · rw [← hc]
    exact Nat.card_image_of_injOn (toQuot_injOn hΨ hC hEZ)

end ToQuot

section SL2

variable {G : Type} [Group G] [Finite G]

theorem eq_zero_of_sl2Upper_commute_weyl {K : Type*} [Field K] {c : K}
    (h : sl2Upper c * sl2Weyl K = sl2Weyl K * sl2Upper c) : c = 0 := by
  have h00 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Weyl, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00
  simpa using h00

theorem sum_le_localRank_of_commuting_SL2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (i₀ : ι) {K : ι → Type*} [∀ i, Field (K i)] [∀ i, Fintype (K i)]
    (f : ι → ℕ) (hK : ∀ i, Fintype.card (K i) = p ^ f i) (φ : ∀ i, SL(2, K i) →* G)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ (A : SL(2, K i)) (B : SL(2, K j)), φ i A * φ j B = φ j B * φ i A) :
    ∑ i, f i ≤ localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ∀ i, CharP (K i) p := fun i => charP_of_card_eq_prime_pow (hK i)
  set x : ∀ i, Multiplicative (K i) →* G := fun i => (φ i).comp (sl2UpperHom (K i)) with hx
  have hxinj : ∀ i, Function.Injective (x i) := fun i => (hφ i).comp sl2UpperHom_injective
  have hxc : Pairwise fun i j => ∀ (a : Multiplicative (K i)) (b : Multiplicative (K j)),
      Commute (x i a) (x j b) := fun i j hij a b => hcomm i j hij _ _
  have hcen : ∀ i j, i ≠ j → (x j).range ≤ Subgroup.centralizer (φ i).range := by
    rintro i j hij _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact hcomm i j hij A _
  have hind : iSupIndep fun i => (x i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    obtain ⟨hyi, hyj⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨c, rfl⟩ := hyi
    have hyc : x i c ∈ Subgroup.centralizer (φ i).range :=
      (iSup₂_le fun j hj => hcen i j (Ne.symm hj)) hyj
    have h1 := Subgroup.mem_centralizer_iff.1 hyc (φ i (sl2Weyl (K i))) ⟨_, rfl⟩
    rw [hx, MonoidHom.comp_apply, ← map_mul, ← map_mul] at h1
    have h2 := eq_zero_of_sl2Upper_commute_weyl ((hφ i) h1).symm
    rw [Subgroup.mem_bot, hx, MonoidHom.comp_apply, sl2UpperHom_apply, h2, sl2Upper_zero,
      map_one]
  set Φ := MonoidHom.noncommPiCoprod x hxc
  have hΦ : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep x hind hxinj
  set E := Φ.range
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha⟩ := a.2
      obtain ⟨b', hb⟩ := b.2
      change (a : G) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := by
        funext i
        change Multiplicative.ofAdd (p • Multiplicative.toAdd (a i)) = Multiplicative.ofAdd 0
        rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rw [this, map_one]
  have hcard : Nat.card E = p ^ ∑ i, f i := by
    change Nat.card Φ.range = _
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_pi,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, hK i]
  have ht : orderOf (φ i₀ (sl2Diag (-1))) = 2 := by
    rw [orderOf_injective (φ i₀) (hφ i₀)]
    exact orderOf_sl2Diag_neg_one (by rw [ringChar.eq (K i₀) p]; exact hp2)
  have hEt : ∀ y ∈ E, y * φ i₀ (sl2Diag (-1)) = φ i₀ (sl2Diag (-1)) * y := by
    have hle : E ≤ Subgroup.centralizer {φ i₀ (sl2Diag (-1))} := by
      change Φ.range ≤ _
      rw [MonoidHom.noncommPiCoprod_range]
      refine iSup_le fun i => ?_
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hi : i = i₀
      · subst hi
        rw [hx, MonoidHom.comp_apply, ← map_mul, ← map_mul,
          (sl2Diag_neg_one_commute (sl2UpperHom (K i) c)).eq]
      · exact (hcomm i₀ i (Ne.symm hi) (sl2Diag (-1)) (sl2UpperHom (K i) c)).symm
    exact fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
  exact le_localRank_of_commute_involution hp ht hE hcard hEt

theorem le_localRank_of_commuting_SL2_even {K : Type*} [Field K] [Fintype K]
    (hK : ringChar K = 2) {r m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ Fintype.card K - 1)
    (hm : 1 ≤ m) (φ : Fin m → SL(2, K) →* G) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    m ≤ localRank r G := by
  obtain ⟨-, -, -, -, A, -, -, -, h⟩ :=
    even_commuting_SL2_actual_central_cover_split_prime_local_rank (⊤ : Subgroup G) hK hr hr2
      hrq hm (⊤ : Subgroup G).subtype (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
      (by rw [Subgroup.ker_subtype]; exact bot_le) φ hφ hcomm
  exact h

@[expose] def sl2Three (K : Type*) [Field K] : SL(2, K) := sl2Weyl K * sl2Upper 1

theorem sl2Three_pow_three (K : Type*) [Field K] : sl2Three K ^ 3 = 1 := by
  ext i j
  rw [pow_succ, pow_two, sl2Three]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Weyl,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Three_not_commute (K : Type*) [Field K] :
    sl2Three K * sl2Upper 1 ≠ sl2Upper 1 * sl2Three K := by
  intro h
  have h00 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [sl2Three, Matrix.mul_apply, Fin.sum_univ_two, coe_sl2Upper, coe_sl2Weyl] at h00

theorem card_le_localRank_three_of_commuting_SL2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (φ : ι → SL(2, K) →* G) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) {u : G}
    (hu : orderOf u = 2) (hφu : ∀ i A, φ i A * u = u * φ i A) :
    Fintype.card ι ≤ localRank 3 G := by
  refine CFSG.RankThree.Theta.card_le_localRank_three (fun i => (φ i).range) ?_
    (fun i => φ i (sl2Three K)) (fun i => ⟨_, rfl⟩) (fun i h => ?_) (fun i => ?_) hu
    (fun i => Subgroup.mem_centralizer_singleton_iff.2 (hφu i _))
  · rintro i j hij _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact hcomm i j hij A B
  · have h1 := Subgroup.mem_centralizer_iff.1 h (φ i (sl2Upper 1)) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact sl2Three_not_commute K ((hφ i) h1).symm
  · rw [← map_pow, sl2Three_pow_three, map_one]
    exact Subgroup.one_mem _

theorem card_le_localRank_three_of_le_normalizer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Subgroup G) (hK : ∀ i j, i ≠ j → K j ≤ Subgroup.centralizer (K i : Set G))
    (y : ι → G) (hyK : ∀ i, y i ∈ K i) (hy : ∀ i, y i ∉ Subgroup.centralizer (K i : Set G))
    (hy3 : ∀ i, y i ^ 3 ∈ Subgroup.centralizer (K i : Set G)) {P : Subgroup G} (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hyP : ∀ i, y i ∈ Subgroup.normalizer (P : Set G)) :
    Fintype.card ι ≤ localRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair : (Set.range y).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    exact Subgroup.mem_centralizer_iff.1 (hK i j hij' (hyK j)) (y i) (hyK i)
  set Y := Subgroup.closure (Set.range y)
  have hYc : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ a b : Y, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm }
  let y' : ι → Y := fun i => ⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range y') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range y)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  have hbound := CFSG.RankThree.Theta.three_pow_card_le_card_ker_pow y' hgen
    (fun i => (Subgroup.centralizer (K i : Set G)).subgroupOf Y)
    (fun i j hij => Subgroup.mem_subgroupOf.2 (hK i j hij (hyK j)))
    (fun i h => hy i (Subgroup.mem_subgroupOf.1 h)) (fun i => Subgroup.mem_subgroupOf.2 (hy3 i))
  set Ω : Subgroup G := (powMonoidHom 3 : Y →* Y).ker.map Y.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card (powMonoidHom 3 : Y →* Y).ker :=
    Subgroup.card_map_of_injective Y.subtype_injective
  have hΩY : Ω ≤ Y := Subgroup.map_subtype_le _
  have hΩc : IsMulCommutative Ω := ⟨⟨fun a b => Subtype.ext
    (show (a : G) * b = b * a from congrArg Subtype.val (hcomm ⟨a, hΩY a.2⟩ ⟨b, hΩY b.2⟩))⟩⟩
  have hΩq : ∀ w ∈ Ω, w ^ 3 = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
  have hΩp : IsPGroup 3 Ω := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hΩq _ w.2, Subgroup.coe_one])⟩
  obtain ⟨r, hr⟩ := hΩp.exists_card_eq
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := (Subgroup.closure_le _).2 (by
    rintro _ ⟨i, rfl⟩
    exact hyP i)
  have hr' := le_localRank_of_le_normalizer Nat.prime_three hP hP2 ⟨hΩc, hΩq⟩ hr
    (hΩY.trans hYP)
  have h3r : 3 ^ Fintype.card ι ≤ 3 ^ r := by
    rw [← hr, hΩcard]
    exact hbound
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3r
  omega

end SL2

theorem four_le_twoLocalOddRank_of_localRank {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : 4 ≤ localRank p G) : 4 ≤ CFSG.twoLocalOddRank G := by
  have hpG : p ∣ Nat.card G := by
    have h1 : localRank p G ≤ Assembly.pRank p (⊤ : Subgroup G) :=
      CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp G
    have h2 := CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp
      (⊤ : Subgroup G)
    rw [Subgroup.card_top] at h2
    exact (dvd_pow_self p (by omega : Assembly.pRank p (⊤ : Subgroup G) ≠ 0)).trans h2
  exact h.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hp hp2 hpG)

section Four

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K]

theorem four_le_twoLocalOddRank_of_four_commuting_SL2 (hK2 : Fintype.card K ≠ 2)
    (φ : Fin 4 → SL(2, K) →* G) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    4 ≤ CFSG.twoLocalOddRank G := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  by_cases h2 : ringChar K = 2
  · rw [h2] at hn
    have hn2 : 2 ≤ (n : ℕ) := by
      by_contra hlt
      have h1 : (n : ℕ) = 1 := by omega
      rw [h1, pow_one] at hn
      exact hK2 hn
    have h4 : 4 ≤ Fintype.card K := hn ▸ le_trans (by norm_num) (Nat.pow_le_pow_right
      (by norm_num) hn2)
    have hK2' : 2 ∣ Fintype.card K := hn ▸ dvd_pow_self 2 (by omega)
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show Fintype.card K - 1 ≠ 1 by omega)
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    exact four_le_twoLocalOddRank_of_localRank hr hr2
      (le_localRank_of_commuting_SL2_even h2 hr hr2 hrd (by norm_num) φ hφ hcomm)
  · have hsum := sum_le_localRank_of_commuting_SL2 hp h2 (0 : Fin 4) (K := fun _ => K)
      (fun _ => (n : ℕ)) (fun _ => hn) φ hφ hcomm
    have h4 : 4 ≤ ∑ _i : Fin 4, (n : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    exact four_le_twoLocalOddRank_of_localRank hp h2 (h4.trans hsum)

theorem four_le_twoLocalOddRank_of_two_commuting_SL2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (hK : Fintype.card K = p ^ f) (φ : Fin 2 → SL(2, K) →* G)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    4 ≤ CFSG.twoLocalOddRank G := by
  have hsum := sum_le_localRank_of_commuting_SL2 hp hp2 (0 : Fin 2) (K := fun _ => K)
    (fun _ => f) (fun _ => hK) φ hφ hcomm
  have h4 : 4 ≤ ∑ _i : Fin 2, f := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  exact four_le_twoLocalOddRank_of_localRank hp hp2 (h4.trans hsum)

omit [Fintype K] in
theorem orderOf_sl2Upper_one (h2 : ringChar K = 2) : orderOf (sl2Upper (1 : K)) = 2 := by
  have : CharP K 2 := ringChar.of_eq h2
  apply orderOf_eq_prime
  · have h0 : ((2 : ℕ) : K) * 1 = 0 := by
      rw [mul_one, Nat.cast_ofNat]
      exact CharTwo.two_eq_zero
    rw [sl2Upper_pow, h0, sl2Upper_zero]
  · intro h
    exact one_ne_zero (sl2Upper_injective (h.trans sl2Upper_zero.symm))

omit [Fintype K] in
theorem four_le_twoLocalOddRank_of_five_commuting_SL2 (h2 : ringChar K = 2)
    (φ : Fin 5 → SL(2, K) →* G) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    4 ≤ CFSG.twoLocalOddRank G := by
  have hu : orderOf (φ 4 (sl2Upper 1)) = 2 := by
    rw [orderOf_injective (φ 4) (hφ 4)]
    exact orderOf_sl2Upper_one h2
  have h4 := card_le_localRank_three_of_commuting_SL2 (ι := Fin 4)
    (fun i => φ (Fin.castSucc i)) (fun i => hφ _)
    (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B) hu
    (fun i A => hcomm _ _ (Fin.castSucc_ne_last i) A _)
  rw [Fintype.card_fin] at h4
  exact four_le_twoLocalOddRank_of_localRank Nat.prime_three (by norm_num) h4

end Four

end CFSG.RankThree.PartTwo.Census.Exceptional
