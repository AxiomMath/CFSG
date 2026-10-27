module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProof2124

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item2125Unique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ K₁ ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K₁ →
        ∀ K₂ ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K₂ → K₁ = K₂

@[expose] def Item2125Generic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ e ∈ A, e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d →
        e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d →
        ∃ Le ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card Le ∧ Nonempty (lBar Le ≃* lBar L) ∧
          d ∈ Le ∧ Sec4.InducesTypeOn Le d 1 ∧ Sec4.InducesTypeOn Le c 2

namespace Item2119EndProof

section Transport

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjEquiv (g : G) (L : Subgroup G) :
    L ≃* L.map (MulAut.conj g).toMonoidHom :=
  L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

omit [Finite G] in
theorem coe_conjEquiv (g : G) (L : Subgroup G) (l : L) :
    ((conjEquiv g L l : L.map (MulAut.conj g).toMonoidHom) : G) = g * l * g⁻¹ :=
  rfl

@[expose] noncomputable def lBarMapConj (g : G) (L : Subgroup G) :
    lBar L ≃* lBar (L.map (MulAut.conj g).toMonoidHom) :=
  QuotientGroup.congr _ _ (conjEquiv g L)
    (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three (conjEquiv g L))

theorem lBarMapConj_mk (g : G) (L : Subgroup G) (l : L) :
    lBarMapConj g L (l : lBar L) = ((conjEquiv g L l : L.map (MulAut.conj g).toMonoidHom) :
      lBar (L.map (MulAut.conj g).toMonoidHom)) :=
  rfl

omit [Finite G] in
theorem conj_mem_normalizer_map {L : Subgroup G} {x : G} (g : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  rw [show g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.mp hx _)

theorem inducesTypeOn_map_conj {L : Subgroup G} {x : G} {k : ℕ} (g : G)
    (h : Sec4.InducesTypeOn L x k) :
    Sec4.InducesTypeOn (L.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) k := by
  obtain ⟨hx, π, p, f, K, hF, hK, hq, e, y, hy, hty, hact⟩ := h
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hx' := conj_mem_normalizer_map g hx
  have hkey : ∀ w : lBar L, Sec4.thetaQuotMulAut L' (L'.normalizerMonoidHom ⟨g * x * g⁻¹, hx'⟩)
      (lBarMapConj g L w) =
        lBarMapConj g L (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) w) := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H l =>
      rw [Sec4.thetaQuotMulAut_mk, lBarMapConj_mk, lBarMapConj_mk, Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, coe_conjEquiv, coe_conjEquiv,
        Sec4.normalizerMonoidHom_apply_coe]
      group
  refine ⟨hx', π, p, f, K, hF, hK, hq, (lBarMapConj g L).symm.trans e, y, hy, hty, fun z => ?_⟩
  obtain ⟨w, rfl⟩ := (lBarMapConj g L).surjective z
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hkey, MulEquiv.symm_apply_apply]
  exact hact w

omit [Finite G] in
theorem thetaComponentsAt_eq_of_zpowers_eq {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    thetaComponentsAt 3 x = thetaComponentsAt 3 y := by
  have hc : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
    have hx : Subgroup.centralizer ({x} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hy : Subgroup.centralizer ({y} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hx, hy, h]
  rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn, hc]

omit [Finite G] in
theorem zpowers_mul_pow_eq {x δ : G} (hx3 : x ^ 3 = 1) (hδ3 : δ ^ 3 = 1) (hxδ : x * δ = δ * x)
    {i j : ℕ} (hi : i < 3) (hi0 : i ≠ 0) :
    Subgroup.zpowers (x * δ ^ ((i * j) % 3)) = Subgroup.zpowers (x ^ i * δ ^ j) := by
  have hc : ∀ (u v : ℕ), Commute (x ^ u) (δ ^ v) := fun u v =>
    Commute.pow_pow (show Commute x δ from hxδ) u v
  have hi' : i = 1 ∨ i = 2 := by omega
  have e1 : (x * δ ^ ((i * j) % 3)) ^ i = x ^ i * δ ^ j := by
    rw [(by simpa using hc 1 ((i * j) % 3) : Commute x (δ ^ ((i * j) % 3))).mul_pow, ← pow_mul,
      Item21LateProof.pow_eq_pow_mod_three hδ3 ((i * j) % 3 * i),
      Item21LateProof.pow_eq_pow_mod_three hδ3 j]
    congr 2
    rcases hi' with rfl | rfl <;> omega
  have e2 : (x ^ i * δ ^ j) ^ i = x * δ ^ ((i * j) % 3) := by
    rw [(hc i j).mul_pow, ← pow_mul, ← pow_mul,
      Item21LateProof.pow_eq_pow_mod_three hx3 (i * i),
      Item21LateProof.pow_eq_pow_mod_three hδ3 (j * i)]
    rcases hi' with rfl | rfl
    · simp
    · rw [show 2 * 2 % 3 = 1 by norm_num, pow_one, Nat.mul_comm j 2]
  apply le_antisymm
  · rw [Subgroup.zpowers_le, ← e2]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i
  · rw [Subgroup.zpowers_le, ← e1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i

end Transport

end Item2119EndProof

open Item2119EndProof

theorem item2125_of
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hU : Item2125Unique) (hGen : Item2125Generic) : Item2125 := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 e he hed
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23' := h23
  obtain ⟨⟨eXL⟩, hdX, hdTX, hcTX⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, -, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, -, hw'd', hw'A, hw'move⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfgX
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hw'a : w' * a * w'⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hw'X), mul_inv_cancel_right]
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU' d ⟨hdA, hdX⟩ hd1 hdTX)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact not_mem_sup_of_config2119End hE
  have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1 hcd
  obtain ⟨k₁, hk₁, hk₁e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hwA a haA)
  have hwa : w * a * w⁻¹ = a * d ^ k₁ := by
    rw [← hk₁e]
    group
  have hk₁0 : k₁ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hwa
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hwa hwd hwc y hyA)
  obtain ⟨k₂, hk₂, hk₂e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hw'A c hcA)
  have hw'c : w' * c * w'⁻¹ = c * d ^ k₂ := by
    rw [← hk₂e]
    group
  have hk₂0 : k₂ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw'c
    obtain ⟨y, hyA, hy⟩ := hw'move
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hw'a hw'd hw'c y hyA)
  have h3dvd : ∀ {K : Subgroup G} {x : G}, x ∈ K → x ≠ 1 → x ^ 3 = 1 → 3 ∣ Nat.card K := by
    intro K x hx hx1 hx3
    have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : K)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hx3 hx1] at h1
  have hL3 : 3 ∣ Nat.card L := h3dvd hdL hd1 hd3
  have hX3 : 3 ∣ Nat.card X := h3dvd hdX hd1 hd3
  have hconjL : ∀ v : G, v * d * v⁻¹ = d → d ∈ L.map (MulAut.conj v).toMonoidHom := by
    intro v hv
    refine ⟨d, hdL, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hv
  have hconjX : ∀ v : G, v * d * v⁻¹ = d → d ∈ X.map (MulAut.conj v).toMonoidHom := by
    intro v hv
    refine ⟨d, hdX, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hv
  by_cases hecd : e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
  ·
    obtain ⟨i, hi, j, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm c hcA d hdA) (h3 c hcA) hd3 hecd
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    obtain ⟨m, hm⟩ := exists_pow_conj_eq hd3 hw'd hk₂ hk₂0 hw'c ((i * j) % 3)
      (Nat.mod_lt _ (by norm_num))
    have hgd : w' ^ m * d * (w' ^ m)⁻¹ = d := conj_pow_eq_of_conj_eq hw'd m
    have hzp : Subgroup.zpowers ((MulAut.conj (w' ^ m)) c) = Subgroup.zpowers (c ^ i * d ^ j) := by
      rw [MulAut.conj_apply, hm]
      exact zpowers_mul_pow_eq (h3 c hcA) hd3 (hcomm c hcA d hdA) hi hi0
    have hmem : L.map (MulAut.conj (w' ^ m)).toMonoidHom ∈ thetaComponentsAt 3 (c ^ i * d ^ j) := by
      rw [← thetaComponentsAt_eq_of_zpowers_eq hzp]
      exact map_mem_thetaComponentsAt (MulAut.conj (w' ^ m)) hLc
    have hcard : 3 ∣ Nat.card (L.map (MulAut.conj (w' ^ m)).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (w' ^ m)).injective]
      exact hL3
    refine ⟨L.map (MulAut.conj (w' ^ m)).toMonoidHom, hmem, hcard, fun K hK hK3 =>
      hU G A E U c L d U₀ a X hE h23' h24 _ he hed K hK hK3 _ hmem hcard,
      ⟨(lBarMapConj (w' ^ m) L).symm⟩, hconjL _ hgd, ?_, fun h => absurd hecd h⟩
    have h1 := inducesTypeOn_map_conj (w' ^ m) hE.type_d
    rwa [hgd] at h1
  by_cases head : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d
  ·
    obtain ⟨i, hi, j, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm a haA d hdA) (h3 a haA) hd3 head
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    obtain ⟨m, hm⟩ := exists_pow_conj_eq hd3 hwd hk₁ hk₁0 hwa ((i * j) % 3)
      (Nat.mod_lt _ (by norm_num))
    have hhd : w ^ m * d * (w ^ m)⁻¹ = d := conj_pow_eq_of_conj_eq hwd m
    have hhc : w ^ m * c * (w ^ m)⁻¹ = c := conj_pow_eq_of_conj_eq hwc m
    have hzp : Subgroup.zpowers ((MulAut.conj (w ^ m)) a) = Subgroup.zpowers (a ^ i * d ^ j) := by
      rw [MulAut.conj_apply, hm]
      exact zpowers_mul_pow_eq (h3 a haA) hd3 (hcomm a haA d hdA) hi hi0
    have hmem : X.map (MulAut.conj (w ^ m)).toMonoidHom ∈ thetaComponentsAt 3 (a ^ i * d ^ j) := by
      rw [← thetaComponentsAt_eq_of_zpowers_eq hzp]
      exact map_mem_thetaComponentsAt (MulAut.conj (w ^ m)) hXa
    have hcard : 3 ∣ Nat.card (X.map (MulAut.conj (w ^ m)).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (w ^ m)).injective]
      exact hX3
    refine ⟨X.map (MulAut.conj (w ^ m)).toMonoidHom, hmem, hcard, fun K hK hK3 =>
      hU G A E U c L d U₀ a X hE h23' h24 _ he hed K hK hK3 _ hmem hcard,
      ⟨(lBarMapConj (w ^ m) X).symm.trans eXL⟩, hconjX _ hhd, ?_, fun _ => ?_⟩
    · have h1 := inducesTypeOn_map_conj (w ^ m) hdTX
      rwa [hhd] at h1
    · have h1 := inducesTypeOn_map_conj (w ^ m) hcTX
      rwa [hhc] at h1
  obtain ⟨Le, hLe, hLe3, ⟨eLe⟩, hdLe, hdTLe, hcTLe⟩ :=
    hGen G A E U c L d U₀ a X hE h23' h24 e he hecd head
  exact ⟨Le, hLe, hLe3, fun K hK hK3 => hU G A E U c L d U₀ a X hE h23' h24 e he hed K hK hK3 Le
    hLe hLe3, ⟨eLe⟩, hdLe, hdTLe, fun _ => hcTLe⟩

end CFSG.RankThree.PartTwo.Sec21
