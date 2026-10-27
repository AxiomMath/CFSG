module

import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (hxa : x ^ a ∈ H) (hxb : x ^ b = 1) : x ∈ H := by
  have hcop : Nat.Coprime a (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxb) hab
  rcases (orderOf x).lt_or_ge 2 with hlt | hge
  · have h1 : orderOf x = 1 := by
      have := orderOf_pos x
      omega
    rw [orderOf_eq_one_iff.mp h1]
    exact one_mem _
  · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hge
    have hx : x = (x ^ a) ^ u := by
      rw [← pow_mul, ← pow_mod_orderOf, hu, pow_one]
    rw [hx]
    exact pow_mem hxa u

theorem mem_of_mul_pow_eq_one {N : Subgroup G} {n w : G} (hn : n ∈ N)
    (hw : w ∈ Subgroup.normalizer (N : Set G)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : (n * w) ^ a = 1) (hb : w ^ b = 1) : w ∈ N := by
  have hpow : ∀ j : ℕ, ∃ n' ∈ N, (n * w) ^ j = n' * w ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', hj⟩ := ih
      refine ⟨n' * (w ^ j * n * (w ^ j)⁻¹),
        mul_mem hn' ((Subgroup.mem_normalizer_iff.mp (pow_mem hw j) n).mp hn), ?_⟩
      rw [pow_succ, hj, pow_succ]
      group
  obtain ⟨n', hn', h⟩ := hpow a
  rw [ha] at h
  have hwa : w ^ a ∈ N := by
    rw [eq_inv_of_mul_eq_one_right h.symm]
    exact inv_mem hn'
  exact mem_of_pow_mem_of_coprime hab hwa hb

theorem le_of_le_sup_commutator {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (h : T ≤ N ⊔ ⁅T, T⁆) : T ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥T) := ⟨hT⟩
  set H : Subgroup ↥T := N.subgroupOf T with hH
  have hmap : (H ⊔ _root_.commutator ↥T).map T.subtype = N ⊔ ⁅T, T⁆ := by
    rw [Subgroup.map_sup, hH, Subgroup.map_subgroupOf_eq_of_le hNT, _root_.commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htop : H ⊔ _root_.commutator ↥T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ (H ⊔ _root_.commutator ↥T).map T.subtype := hmap ▸ h x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  have htop' : H ⊔ frattini ↥T = ⊤ :=
    eq_top_iff.mpr (htop.symm.le.trans
      (sup_le_sup_left (CFSG.commutator_le_frattini_of_isPGroup (p := 2)) _))
  have hHtop : H = ⊤ := CFSG.lemma_1_7_a (p := 2) H htop'
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥T) ∈ H := hHtop ▸ Subgroup.mem_top _
  exact hmem

theorem inf_centralizer_le_commutator {T : Subgroup G} {c : G} (hT : IsPGroup 2 T)
    (hc3 : c ^ 3 = 1) (hcT : c ∈ Subgroup.normalizer (T : Set G))
    (hTc : T = ⁅T, Subgroup.zpowers c⁆) :
    T ⊓ Subgroup.centralizer ({c} : Set G) ≤ ⁅T, T⁆ := by
  set τ : MulAut ↥T := T.normalizerMonoidHom ⟨c, hcT⟩ with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have : (⟨c, hcT⟩ : Subgroup.normalizer (T : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  set σ : Abelianization ↥T →* Abelianization ↥T := Abelianization.map τ.toMonoidHom with hσ
  set ψ : Abelianization ↥T →* Abelianization ↥T := MonoidHom.id _ * σ * σ.comp σ with hψdef
  have hσπ : ∀ x : ↥T, σ (Abelianization.of x) = Abelianization.of (τ x) := fun x =>
    Abelianization.map_of _ _
  have hψπ : ∀ x : ↥T, ψ (Abelianization.of x) =
      Abelianization.of x * Abelianization.of (τ x) * Abelianization.of (τ (τ x)) := by
    intro x
    simp only [hψdef, MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.comp_apply, hσπ]
  have hτττ : ∀ x : ↥T, τ (τ (τ x)) = x := by
    intro x
    have := congrArg (fun α : MulAut ↥T => α x) hτ3
    simpa [pow_succ, MulAut.mul_apply] using this
  let Fix : Subgroup (MulAut ↥T) :=
    { carrier := {α | ∀ x, ψ (Abelianization.of (α x)) = ψ (Abelianization.of x)}
      mul_mem' := fun {α β} hα hβ x => by
        change ψ (Abelianization.of (α (β x))) = _
        rw [hα, hβ]
      one_mem' := fun x => rfl
      inv_mem' := fun {α} hα x => by
        have := hα (α⁻¹ x)
        rw [MulAut.apply_inv_self] at this
        exact this.symm }
  have hτFix : τ ∈ Fix := by
    intro x
    rw [hψπ, hψπ, hτττ]
    ac_rfl
  have hker : ⁅T, Subgroup.zpowers c⁆ ≤
      ((ψ.comp Abelianization.of).ker).map T.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hyT : c ^ k ∈ Subgroup.normalizer (T : Set G) := zpow_mem hcT k
    have hmem : c ^ k * x * (c ^ k)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hyT x).mp hx
    have hτk : (τ ^ k) ⟨x, hx⟩ = ⟨c ^ k * x * (c ^ k)⁻¹, hmem⟩ := by
      apply Subtype.ext
      rw [hτ, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    refine ⟨⟨x, hx⟩ * ((τ ^ k) ⟨x, hx⟩)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_inv, map_mul,
        map_inv, zpow_mem hτFix k ⟨x, hx⟩, mul_inv_cancel]
    · rw [hτk, map_mul, map_inv]
      change x * (c ^ k * x * (c ^ k)⁻¹)⁻¹ = ⁅x, c ^ k⁆
      rw [commutatorElement_def]
      group
  rintro t ⟨ht, htc⟩
  have hτt : τ ⟨t, ht⟩ = ⟨t, ht⟩ := by
    apply Subtype.ext
    rw [hτ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    change c * t * c⁻¹ = t
    rw [(Subgroup.mem_centralizer_singleton_iff.mp htc).symm]
    group
  obtain ⟨s, hs, hst⟩ := hker (hTc.le ht)
  obtain rfl : s = ⟨t, ht⟩ := Subtype.ext hst
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, hψπ, hτt, hτt] at hs
  have h3 : (⟨t, ht⟩ : ↥T) ^ 3 ∈ _root_.commutator ↥T := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_pow, pow_three, ← mul_assoc]
    exact hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hT ⟨t, ht⟩
  have htT : (⟨t, ht⟩ : ↥T) ∈ _root_.commutator ↥T :=
    mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right m (by norm_num)) h3 hm
  have hmap : (_root_.commutator ↥T).map T.subtype = ⁅T, T⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hmap]
  exact ⟨⟨t, ht⟩, htT, rfl⟩

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three {c : G} (hc3 : c ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers c) := fun g => ⟨1, Subtype.ext (by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hc3, one_zpow, Subgroup.coe_one])⟩

theorem not_three_dvd_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h3
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rw [hn] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem commutator_le_iSup_commutator {B V : Subgroup G} {c : G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : 3 ^ 2 ≤ Nat.card B) (hc3 : c ^ 3 = 1)
    (hcB : ∀ b ∈ B, b * c = c * b) (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) (hV : IsPGroup 2 V) :
    ⁅V, Subgroup.zpowers c⁆ ≤ ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
      ⁅V ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ := by
  set T := ⁅V, Subgroup.zpowers c⁆ with hT
  set N := ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
    ⁅V ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ with hN
  have hc3' := isPGroup_zpowers_of_pow_three hc3
  have hcZ : Subgroup.zpowers c ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hcV
  have hTV : T ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hcZ
  have hT2 : IsPGroup 2 T := hV.to_le hTV
  have hcT : c ∈ Subgroup.normalizer (T : Set G) := by
    have h := Subgroup.normalizer_commutator_ge_left (Subgroup.zpowers c) V
    rw [Subgroup.commutator_comm] at h
    exact h (Subgroup.mem_zpowers c)
  have hTc : T = ⁅T, Subgroup.zpowers c⁆ :=
    (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
      (Subgroup.zpowers c) V hc3' (not_three_dvd_of_isPGroup_two hV) hcZ).symm
  have hNT : N ≤ T := iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
    Subgroup.commutator_mono inf_le_left le_rfl
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    have hbc : b ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcB b hb)
    refine mem_normalizer_of_map_conj_eq ?_
    rw [hT, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hBV hb),
      Late.map_conj_eq_of_mem_normalizer (centralizer_singleton_le_normalizer_zpowers c hbc)]
  have hTle : T ≤ N ⊔ ⁅T, T⁆ := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB hB9 hBT
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_of_isPGroup_two hT2))
      fun b hb hb1 => ?_
    set R := T ⊓ Subgroup.centralizer ({b} : Set G) with hR
    have hcb : c ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcB b hb).symm
    have hcR : Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) :=
      Late.le_normalizer_inf (Subgroup.zpowers_le.mpr hcT)
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hcb))
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three (Subgroup.zpowers c) R hc3'
      (not_three_dvd_of_isPGroup_two (hT2.to_le inf_le_left)) hcR]
    refine sup_le ?_ ?_
    · exact (Subgroup.commutator_mono (inf_le_inf_right _ hTV) le_rfl).trans
        (le_sup_of_le_left (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))))
    · refine le_sup_of_le_right (le_trans ?_ (inf_centralizer_le_commutator hT2 hc3 hcT hTc))
      intro x hx
      exact ⟨hx.1.1, Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)) hx.2⟩
  exact le_of_le_sup_commutator hT2 hNT hTle

theorem le_sup_commutator_of_cover {Y L V : Subgroup G} {c : G}
    (hY3 : Y = oPrimeResidualOf 3 Y) (hcov : Y ≤ L ⊔ V) (hV : IsPGroup 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hc3 : c ^ 3 = 1) (hcV : c ∈ Subgroup.normalizer (V : Set G))
    (hCL : V ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Y ≤ L ⊔ ⁅V, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := ⁅V, Subgroup.zpowers c⁆ with hT
  set C := V ⊓ Subgroup.centralizer ({c} : Set G) with hC
  set N := L ⊔ T with hN
  have hc3' := isPGroup_zpowers_of_pow_three hc3
  have hcZ : Subgroup.zpowers c ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hcV
  have hLT : L ≤ Subgroup.normalizer (T : Set G) := by
    intro l hl
    refine mem_normalizer_of_map_conj_eq ?_
    rw [hT, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hLV hl),
      Late.map_conj_eq_of_mem_normalizer (centralizer_singleton_le_normalizer_zpowers c (hLc hl))]
  have hVT : V ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.normalizer_commutator_ge_left V (Subgroup.zpowers c)
  have hCN : C ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_sup hCL (inf_le_left.trans hVT)
  have hVfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three (Subgroup.zpowers c) V hc3' (not_three_dvd_of_isPGroup_two hV) hcZ
  have hCC : V ⊓ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) ≤ C :=
    inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  have hYNC : Y ≤ N ⊔ C := by
    calc Y ≤ L ⊔ V := hcov
      _ ≤ L ⊔ (T ⊔ C) := sup_le_sup_left (hVfac.le.trans (sup_le_sup_left hCC _)) _
      _ = N ⊔ C := by rw [hN, sup_assoc]
  refine hY3.le.trans ?_
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro x ⟨hxY, k, hk⟩
  have hx : x ∈ ((N ⊔ C : Subgroup G) : Set G) := hYNC hxY
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N C hCN] at hx
  obtain ⟨n, hn, w, hw, rfl⟩ := hx
  obtain ⟨m, hm⟩ := hV ⟨w, hw.1⟩
  have hm' : w ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  exact mul_mem hn (mem_of_mul_pow_eq_one hn (hCN hw)
    (Nat.Coprime.pow k m (by norm_num)) hk hm')

end CFSG.RankThree.PartTwo.Sec17.Proof171
