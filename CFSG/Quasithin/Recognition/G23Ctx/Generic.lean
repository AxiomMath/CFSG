module

public import CFSG.Open.QuasithinDefs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open
open scoped MatrixGroups Pointwise

variable {G : Type*} [Group G]

theorem fpf_inverts [Finite G] {N : Subgroup G} {t : G} (ht : t * t = 1)
    (hN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hfix : ∀ n ∈ N, t * n * t⁻¹ = n → n = 1) :
    ∀ n ∈ N, t * n * t⁻¹ = n⁻¹ := by
  have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hB : ∀ y : G, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    rw [h2]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht, one_mul, mul_one]
  let f : N → N := fun n => ⟨(n : G)⁻¹ * (t * (n : G) * t⁻¹), N.mul_mem (N.inv_mem n.2) (hN (n : G) n.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : (a : G)⁻¹ * (t * (a : G) * t⁻¹) = (b : G)⁻¹ * (t * (b : G) * t⁻¹) :=
      congrArg Subtype.val hab
    have hBa : t * (a : G) * t⁻¹ = (a : G) * (b : G)⁻¹ * (t * (b : G) * t⁻¹) := by
      calc t * (a : G) * t⁻¹ = (a : G) * ((a : G)⁻¹ * (t * (a : G) * t⁻¹)) := by group
        _ = (a : G) * ((b : G)⁻¹ * (t * (b : G) * t⁻¹)) := by rw [hab']
        _ = (a : G) * (b : G)⁻¹ * (t * (b : G) * t⁻¹) := by group
    have hconj : t * ((b : G) * (a : G)⁻¹) * t⁻¹ = (b : G) * (a : G)⁻¹ := by
      calc t * ((b : G) * (a : G)⁻¹) * t⁻¹
          = (t * (b : G) * t⁻¹) * (t * (a : G)⁻¹ * t⁻¹) := by group
        _ = (t * (b : G) * t⁻¹) * (t * (a : G) * t⁻¹)⁻¹ := by group
        _ = (t * (b : G) * t⁻¹) * ((a : G) * (b : G)⁻¹ * (t * (b : G) * t⁻¹))⁻¹ := by
          rw [hBa]
        _ = (b : G) * (a : G)⁻¹ := by group
    have hd : (b : G) * (a : G)⁻¹ = 1 :=
      hfix _ (N.mul_mem b.2 (N.inv_mem a.2)) hconj
    exact Subtype.ext (mul_inv_eq_one.mp hd).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  intro n hn
  obtain ⟨x, hx⟩ := hsurj ⟨n, hn⟩
  have hx' : (x : G)⁻¹ * (t * (x : G) * t⁻¹) = n := congrArg Subtype.val hx
  calc t * n * t⁻¹ = t * ((x : G)⁻¹ * (t * (x : G) * t⁻¹)) * t⁻¹ := by rw [hx']
    _ = (t * (x : G)⁻¹ * t⁻¹) * (t * (t * (x : G) * t⁻¹) * t⁻¹) := by group
    _ = (t * (x : G) * t⁻¹)⁻¹ * (x : G) := by rw [hB (x : G)]; group
    _ = ((x : G)⁻¹ * (t * (x : G) * t⁻¹))⁻¹ := by group
    _ = n⁻¹ := by rw [hx']

theorem exists_mem_center_of_normalizes [Finite G] {T P : Subgroup G} (hT : IsPGroup 2 T)
    (hP : P ≠ ⊥) (hPT : P ≤ T) (hn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P) :
    ∃ p ∈ P, p ≠ 1 ∧ ∀ t ∈ T, t * p = p * t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : IsPGroup 2 P := hT.to_le hPT
  let _ : MulAction T P :=
    { smul := fun g o => ⟨(g : G) * o * (g : G)⁻¹, hn g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (by
        change ((1 : T) : G) * (o : G) * ((1 : T) : G)⁻¹ = o
        rw [Subgroup.coe_one, one_mul, inv_one, mul_one])
      mul_smul := fun a b o => Subtype.ext (by
        change ((a * b : T) : G) * (o : G) * ((a * b : T) : G)⁻¹ =
          (a : G) * ((b : G) * o * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have h1 : (1 : P) ∈ MulAction.fixedPoints T P := fun g => Subtype.ext (by
    change (g : G) * 1 * (g : G)⁻¹ = 1
    group)
  have hdvd : 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hO.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hP (Subgroup.card_eq_one.mp hk)
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨b, hb, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point P hdvd h1
  refine ⟨(b : G), b.2, fun h => hne (Subtype.ext h.symm), fun g hg => ?_⟩
  have e : g * (b : G) * g⁻¹ = (b : G) := congrArg Subtype.val (hb ⟨g, hg⟩)
  calc g * (b : G) = g * (b : G) * g⁻¹ * g := by group
    _ = (b : G) * g := by rw [e]

theorem exists_involution_of_even [Finite G] {N : Subgroup G} (h : ¬ Odd (Nat.card N)) :
    ∃ t ∈ N, t ≠ 1 ∧ t * t = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card N := by
    rcases Nat.even_or_odd (Nat.card N) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : x * x = 1 := by
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hx, pow_two] at h1
    exact h1
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · intro h1
    have hx1 : x = 1 := Subtype.ext h1
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · have := congrArg Subtype.val hx2
    simpa using this

theorem exists_conj_mem_sylow [Finite G] {T : Subgroup G} (hT : quasithinIsSylowTwo T) {t : G}
    (ht : t * t = 1) : ∃ g : G, g * t * g⁻¹ ∈ T := by
  obtain ⟨hT1, hT2⟩ : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 G) :=
    Finite.of_injective (fun Q : Sylow 2 G => (Q : Set G)) SetLike.coe_injective
  have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
  have htZ : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact hord)
  obtain ⟨Q, hQ⟩ := htZ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hT1.toSylow hT2)
  refine ⟨g, ?_⟩
  have hmem : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t)
  have h1 := Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) (Q : Subgroup G) hmem
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

theorem finite_sylow_two [Finite G] : Finite (Sylow 2 G) :=
  Finite.of_injective (fun P : Sylow 2 G => (P : Set G)) SetLike.coe_injective

theorem sylow_subgroupOf {H T : Subgroup G} (hTH : T ≤ H) (hT : quasithinIsSylowTwo T) :
    quasithinIsSylowTwo (T.subgroupOf H) := by
  unfold quasithinIsSylowTwo at hT ⊢
  refine ⟨hT.1.of_injective (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTH).injective, ?_⟩
  have hdvd : (T.subgroupOf H).index ∣ T.index := Dvd.intro _ (Subgroup.relIndex_mul_index hTH)
  exact fun hd => hT.2 (dvd_trans hd hdvd)

theorem sylow_of_card_eq [Finite G] {S T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hS : IsPGroup 2 S) (hcard : Nat.card S = Nat.card T) : quasithinIsSylowTwo S := by
  have hT' : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hT
  have h1 : Nat.card S * S.index = Nat.card G := Subgroup.card_mul_index (H := S)
  have h2 : Nat.card T * T.index = Nat.card G := Subgroup.card_mul_index (H := T)
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hidx : S.index = T.index := by
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  unfold quasithinIsSylowTwo
  refine ⟨hS, ?_⟩
  rw [hidx]
  exact hT'.2

theorem exists_conj_eq_of_card [Finite G] {S T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hS : IsPGroup 2 S) (hcard : Nat.card S = Nat.card T) :
    ∃ g : G, ∀ x : G, x ∈ T ↔ g⁻¹ * x * g ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 G) := finite_sylow_two
  have hS' : IsPGroup 2 S ∧ ¬ 2 ∣ S.index := sylow_of_card_eq hT hS hcard
  have hT' : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hT
  obtain ⟨PS, hPS⟩ : ∃ P : Sylow 2 G, (P : Subgroup G) = S := ⟨hS.toSylow hS'.2, rfl⟩
  obtain ⟨PT, hPT⟩ : ∃ P : Sylow 2 G, (P : Subgroup G) = T := ⟨hT'.1.toSylow hT'.2, rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS PT
  refine ⟨g, fun x => ?_⟩
  have hTset : (PT : Set G) = MulAut.conj g • (PS : Set G) := by
    rw [← Sylow.coe_smul, hg]
  have key : x ∈ MulAut.conj g • (PS : Set G) ↔ g⁻¹ * x * g ∈ (PS : Set G) := by
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hx : x = g * y * g⁻¹ := hyx.symm
      rw [hx]
      have hy' : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [hy']
      exact hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
  rw [← hPT, ← hPS]
  show x ∈ (PT : Set G) ↔ g⁻¹ * x * g ∈ (PS : Set G)
  rw [hTset]
  exact key

theorem sylow_of_normalizer_le [Finite G] {H T : Subgroup G} (hTH : T ≤ H)
    (hT : quasithinIsSylowTwo (T.subgroupOf H)) (hN : Subgroup.normalizer (T : Set G) ≤ H) :
    quasithinIsSylowTwo T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf H) ∧ ¬ 2 ∣ (T.subgroupOf H).index := hT
  have hT2 : IsPGroup 2 T :=
    hT'.1.of_injective (Subgroup.subgroupOfEquivOfLe hTH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTH).symm.injective
  obtain ⟨P, hTP⟩ := IsPGroup.exists_le_sylow hT2
  have hTeq : T = (P : Subgroup G) := by
    by_contra hne
    have hlt : T.subgroupOf (P : Subgroup G) < ⊤ := by
      refine lt_top_iff_ne_top.mpr (fun htop => hne ?_)
      exact le_antisymm hTP (Subgroup.subgroupOf_eq_top.mp htop)
    have hnc : NormalizerCondition (P : Subgroup G) := by
      haveI := P.isPGroup'.isNilpotent
      exact Group.normalizerCondition_of_isNilpotent
    obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt (hnc _ hlt)
    have hxP : (x : G) ∈ (P : Subgroup G) := x.2
    have hxT' : (x : G) ∉ T := fun h => hxT (Subgroup.mem_subgroupOf.mpr h)
    have hxiff := Subgroup.mem_normalizer_iff.mp hxN
    have hxN' : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr (fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
      · have hnP : n ∈ (P : Subgroup G) := hTP hn
        exact Subgroup.mem_subgroupOf.mp ((hxiff ⟨n, hnP⟩).mp (Subgroup.mem_subgroupOf.mpr hn))
      · have h2 : (x : G)⁻¹ * ((x : G) * n * (x : G)⁻¹) * (x : G) ∈ (P : Subgroup G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxP) (hTP hn)) hxP
        have h3 : (x : G)⁻¹ * ((x : G) * n * (x : G)⁻¹) * (x : G) = n := by group
        rw [h3] at h2
        exact Subgroup.mem_subgroupOf.mp ((hxiff ⟨n, h2⟩).mpr (Subgroup.mem_subgroupOf.mpr hn))
    have hxH : (x : G) ∈ H := hN hxN'
    set W : Subgroup G := T ⊔ Subgroup.zpowers (x : G) with hWdef
    have hTW : T ≤ W := le_sup_left
    have hxW : (x : G) ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hWP : W ≤ (P : Subgroup G) := sup_le hTP (Subgroup.zpowers_le.mpr hxP)
    have hWH : W ≤ H := sup_le hTH (Subgroup.zpowers_le.mpr hxH)
    have hW2 : IsPGroup 2 W := P.isPGroup'.to_le hWP
    have hW2' : IsPGroup 2 (W.subgroupOf H) :=
      hW2.of_injective (Subgroup.subgroupOfEquivOfLe hWH).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hWH).injective
    have hle : T.subgroupOf H ≤ W.subgroupOf H := Subgroup.subgroupOf_mono H hTW
    have hmax : W.subgroupOf H = T.subgroupOf H :=
      (hT'.1.toSylow hT'.2).is_maximal' hW2' hle
    have hxTsub : (⟨x, hxH⟩ : H) ∈ T.subgroupOf H := by
      rw [← hmax]
      exact Subgroup.mem_subgroupOf.mpr hxW
    exact hxT' (Subgroup.mem_subgroupOf.mp hxTsub)
  unfold quasithinIsSylowTwo
  refine ⟨hT2, ?_⟩
  rw [hTeq]
  exact Sylow.not_dvd_index P

theorem frattini_sylow [Finite G] {N T : Subgroup G} (hN : N.Normal) (hT : quasithinIsSylowTwo T)
    (hTN : T ≤ N) : ∀ g : G, ∃ n ∈ N, ∃ x ∈ Subgroup.normalizer (T : Set G), g = n * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hT
  obtain ⟨P, hPT⟩ : ∃ P : Sylow 2 G, (P : Subgroup G) = T := ⟨hT'.1.toSylow hT'.2, rfl⟩
  haveI : Finite (Sylow 2 N) := finite_sylow_two
  have hPN : (P : Subgroup G) ≤ N := by
    rw [hPT]
    exact hTN
  have hsup : Subgroup.normalizer (P : Set G) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top' P hPN
  have hnorm : Subgroup.normalizer (P : Set G) = Subgroup.normalizer (T : Set G) :=
    congrArg (fun K : Subgroup G => Subgroup.normalizer (K : Set G)) hPT
  intro g
  have hg : g ∈ N ⊔ Subgroup.normalizer (P : Set G) := by
    rw [sup_comm, hsup]
    exact Subgroup.mem_top g
  have hg' : g ∈ (N : Set G) * (Subgroup.normalizer (P : Set G) : Set G) := by
    rw [← Subgroup.normal_mul]
    exact hg
  obtain ⟨n, hn, x, hx, hnx⟩ := Set.mem_mul.mp hg'
  refine ⟨n, hn, x, ?_, hnx.symm⟩
  rw [← hnorm]
  exact hx

theorem le_of_surj_simple {M V N : Subgroup G} {S : Type*} [Group S] [IsSimpleGroup S]
    (θ : ↥M →* S) (hθ : Function.Surjective θ) (hker : θ.ker = V.subgroupOf M)
    (hN : N.Normal) (hVN : V ≤ N) {u : G} (huM : u ∈ M) (huN : u ∈ N) (huV : u ∉ V) :
    M ≤ N := by
  have hmemker : ∀ x : M, θ x = 1 ↔ (x : G) ∈ V := by
    intro x
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  haveI : (N.subgroupOf M).Normal := inferInstance
  haveI hKn : ((N.subgroupOf M).map θ).Normal := Subgroup.Normal.map this θ hθ
  rcases Subgroup.Normal.eq_bot_or_eq_top ((N.subgroupOf M).map θ) with hbot | htop
  · exfalso
    have hu' : (⟨u, huM⟩ : M) ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr huN
    have hmem : θ ⟨u, huM⟩ ∈ (N.subgroupOf M).map θ := Subgroup.mem_map_of_mem θ hu'
    rw [hbot, Subgroup.mem_bot] at hmem
    exact huV ((hmemker ⟨u, huM⟩).mp hmem)
  · intro m hm
    have hmK : θ ⟨m, hm⟩ ∈ (N.subgroupOf M).map θ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n', hn', hθn⟩ := Subgroup.mem_map.mp hmK
    have hθ1 : θ (n'⁻¹ * (⟨m, hm⟩ : M)) = 1 := by
      rw [map_mul, map_inv, hθn, inv_mul_cancel]
    have hV' : (n' : G)⁻¹ * m ∈ V := (hmemker _).mp hθ1
    have hnN : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have hprod := N.mul_mem hnN (hVN hV')
    simpa using hprod

theorem isSimpleGroup_sl3 : IsSimpleGroup SL(3, ZMod 2) := by
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
    have hr1 : r = 1 := key r hr
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  exact (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)).mp hPSL

end CFSG.Quasithin.G23Type.Ctx
