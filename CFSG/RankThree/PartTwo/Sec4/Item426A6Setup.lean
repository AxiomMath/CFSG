module

import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

abbrev fixSub {X : Type*} [Group X] (α : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X)

theorem mem_fixSub {X : Type*} [Group X] {α : MulAut X} {x : X} : x ∈ fixSub α ↔ α x = x :=
  Iff.rfl

theorem fixSub_one {X : Type*} [Group X] : fixSub (1 : MulAut X) = ⊤ :=
  eq_top_iff.mpr fun _ _ => rfl

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_perfect_le {L K : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hK : Group.IsPerfect K) (hK1 : K ≠ ⊥) (hKL : K ≤ L) {c : G}
    (hKc : K ≤ Subgroup.centralizer ({c} : Set G)) :
    c ∈ Subgroup.normalizer (L : Set G) := by
  have hL' : L.map (MulAut.conj c).toMonoidHom ∈ thetaComponents 3 G :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj c) hL
  have hKL' : K ≤ L.map (MulAut.conj c).toMonoidHom := by
    intro k hk
    refine ⟨k, hKL hk, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hKc hk)
    change c * k * c⁻¹ = k
    rw [← h, mul_inv_cancel_right]
  have heq : L = L.map (MulAut.conj c).toMonoidHom :=
    theta_component_eq_of_perfect_le Nat.prime_three hL hL' hK1 hK hKL hKL'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hm : c * h * c⁻¹ ∈ L.map (MulAut.conj c).toMonoidHom := ⟨h, hh, rfl⟩
    rwa [← heq] at hm
  · intro hh
    rw [heq] at hh
    obtain ⟨h', hh', he⟩ := hh
    have he' : c * h' * c⁻¹ = c * h * c⁻¹ := he
    have : h' = h := by
      have := congrArg (fun x => c⁻¹ * x * c) he'
      simpa [mul_assoc] using this
    rwa [← this]

noncomputable abbrev thetaAut (L : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  thetaQuotMulAut L (compAction L ⟨x, hx⟩)

theorem thetaAut_mk (L : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    thetaAut L hx (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((compAction L ⟨x, hx⟩ l : L) : L ⧸ aschbacherSolvableCore 3 L) :=
  rfl

omit [Finite G] in
theorem coe_compAction_apply (L : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (l : L) : ((compAction L ⟨x, hx⟩ l : L) : G) = x * l * x⁻¹ :=
  rfl

theorem thetaAut_pow_eq_one (L : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hxm : x ^ m = 1) : thetaAut L hx ^ m = 1 := by
  have h : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ m = 1 :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hxm)
  rw [thetaAut, ← map_pow, ← map_pow, h, map_one, map_one]

theorem fixSub_thetaAut_eq_map (L : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) (hc3 : c ^ 3 = 1) :
    fixSub (thetaAut L hc) = ((Subgroup.centralizer ({c} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  apply le_antisymm
  · intro q hq
    have hle : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.zpowers_le).mpr hc
    let act : Subgroup.zpowers c →* MulAut L := (compAction L).comp (Subgroup.inclusion hle)
    have hA : IsPGroup 3 (Subgroup.zpowers c) := by
      intro g
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      rw [pow_one, SubgroupClass.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hc3, one_zpow]
      rfl
    have hNinv : ∀ a : Subgroup.zpowers c, ∀ n ∈ N, act a n ∈ N := fun a n hn => by
      have h := map_aschbacherSolvableCore (act a)
      rw [← hN] at h
      rw [← h]
      exact ⟨n, hn, rfl⟩
    have hcop : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
    have hfix := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA act N hNinv hcop
    have hgen : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction act N hNinv
        ⟨c, Subgroup.mem_zpowers c⟩ = thetaAut L hc := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H x => rfl
    have hq' : q ∈ {q : L ⧸ N | ∀ a : Subgroup.zpowers c,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction act N hNinv a q = q} := by
      intro a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have ha : a = ⟨c, Subgroup.mem_zpowers c⟩ ^ k := Subtype.ext (by simp [hk])
      rw [ha, map_zpow, hgen]
      have hmem : thetaAut L hc ∈ MulAction.stabilizer (MulAut (L ⧸ N)) q := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hq
      have := Subgroup.zpow_mem _ hmem k
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    rw [hfix] at hq'
    obtain ⟨l, hl, rfl⟩ := hq'
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have h' : c * (l : G) * c⁻¹ = l := congrArg Subtype.val (hl ⟨c, Subgroup.mem_zpowers c⟩)
    calc (l : G) * c = (c * l * c⁻¹) * c := by rw [h']
      _ = c * l := by group
  · rintro _ ⟨l, hl, rfl⟩
    rw [mem_fixSub]
    change thetaAut L hc (l : L ⧸ N) = (l : L ⧸ N)
    rw [thetaAut_mk]
    congr 1
    apply Subtype.ext
    rw [coe_compAction_apply]
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hl)
    rw [← h, mul_inv_cancel_right]

omit [Finite G] in
theorem ker_facts_of_injective {Y Q W : Type*} [Group Y] [Group Q] [Group W] (f : Y →* Q)
    (g : Y →* W) (hg : Function.Injective g) (N : Subgroup W) (hfg : ∀ y, f y = 1 → g y ∈ N)
    (hNs : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N) :
    Group.IsSolvable f.ker ∧ ¬ 3 ∣ Nat.card f.ker := by
  let φ : f.ker →* N := (g.comp f.ker.subtype).codRestrict N fun y => hfg y y.2
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext (hg (congrArg Subtype.val hab))
  refine ⟨?_, fun h3 => hN3 (h3.trans (Subgroup.card_dvd_of_injective φ hφ))⟩
  have := hNs
  exact Group.isSolvable_of_isSolvable_injective hφ

omit [Finite G] in
theorem nonempty_quotTheta_equiv_of_surjective {Y Z : Type*} [Group Y] [Group Z] [Finite Y]
    (f : Y →* Z) (hf : Function.Surjective f) (hks : Group.IsSolvable f.ker)
    (hk3 : ¬ 3 ∣ Nat.card f.ker) :
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* Z ⧸ aschbacherSolvableCore 3 Z) := by
  have : Finite Z := Finite.of_surjective f hf
  obtain ⟨hKle, hθmap, -⟩ :=
    solvable_prime_complement_core_quotient_centralizers Nat.prime_three f.ker hks hk3
  let e : Y ⧸ f.ker ≃* Z := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hθZ : aschbacherSolvableCore 3 Z = (aschbacherSolvableCore 3 Y).map f := by
    rw [← aschbacherSolvableCore_map_mulEquiv Nat.prime_three e, ← hθmap, Subgroup.map_map]
    rfl
  let ψ : Y →* Z ⧸ aschbacherSolvableCore 3 Z := (QuotientGroup.mk' _).comp f
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hf
  have hψker : ψ.ker = aschbacherSolvableCore 3 Y := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hθZ]
    constructor
    · rintro ⟨t, ht, hty⟩
      have h1 : t⁻¹ * y ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hty, inv_mul_cancel]
      have h2 := Subgroup.mul_mem _ ht (hKle h1)
      rwa [mul_inv_cancel_left] at h2
    · intro hy
      exact ⟨y, hy, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem map_mem_thetaComponentsIn_fixSub (L : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) (hc3 : c ^ 3 = 1) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G))) :
    (K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∈
      thetaComponentsIn (fixSub (thetaAut L hc)) := by
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  set M := L ⊓ Subgroup.centralizer ({c} : Set G) with hM
  set F := fixSub (thetaAut L hc) with hF
  have hFeq := fixSub_thetaAut_eq_map L hc hc3
  rw [← hF] at hFeq
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  let ι : M →* L := Subgroup.inclusion (inf_le_left : M ≤ L)
  have hιF : ∀ m : M, π (ι m) ∈ F := fun m => by
    rw [hFeq]
    refine Subgroup.mem_map_of_mem π ?_
    rw [Subgroup.mem_subgroupOf]
    exact m.2.2
  let f : M →* F := (π.comp ι).codRestrict F hιF
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    rw [hFeq] at hq
    obtain ⟨l, hl, rfl⟩ := hq
    exact ⟨⟨l, l.2, Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  obtain ⟨hks, hk3⟩ := ker_facts_of_injective f ι (Subgroup.inclusion_injective _) N
    (fun m hm => by
      have h2 : π (ι m) = 1 := congrArg Subtype.val hm
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2) hθs hθ3
  refine ⟨K₀.map f, CFSG.RankThree.PartOne.EmbeddingTransport.map_mem_thetaComponents_of_surjective
    Nat.prime_three f hf hks hk3 hK₀, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hk' : ι k ∈ (K₀.map M.subtype).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨k, hk, rfl⟩
    exact Subgroup.mem_map_of_mem π hk'
  · rintro ⟨l, hl, rfl⟩
    have hl' : l ∈ (K₀.map M.subtype).subgroupOf L := hl
    rw [Subgroup.mem_subgroupOf] at hl'
    obtain ⟨k, hk, hkl⟩ := hl'
    refine ⟨f k, ⟨k, hk, rfl⟩, ?_⟩
    change π (ι k) = π l
    congr 1
    exact Subtype.ext hkl

theorem nonempty_quotTheta_map_equiv (L : Subgroup G) {K : Subgroup G} (hKL : K ≤ L) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
      ((K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) ⧸
        aschbacherSolvableCore 3
          ((K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) := by
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  set P := (K.subgroupOf L).map π with hP
  let ι : K →* L := Subgroup.inclusion hKL
  have hιP : ∀ k : K, π (ι k) ∈ P := fun k =>
    Subgroup.mem_map_of_mem π (by rw [Subgroup.mem_subgroupOf]; exact k.2)
  let f : K →* P := (π.comp ι).codRestrict P hιP
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨l, hl, rfl⟩ := hq
    have hl' : l ∈ K.subgroupOf L := hl
    exact ⟨⟨l, Subgroup.mem_subgroupOf.mp hl'⟩, rfl⟩
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  obtain ⟨hks, hk3⟩ := ker_facts_of_injective f ι (Subgroup.inclusion_injective _) N
    (fun m hm => by
      have h2 : π (ι m) = 1 := congrArg Subtype.val hm
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2) hθs hθ3
  exact nonempty_quotTheta_equiv_of_surjective f hf hks hk3

omit [Finite G] in
theorem eq_sup_of_map_eq_top (L : Subgroup G) {K : Subgroup G} (hKL : K ≤ L)
    (h : (K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) = ⊤) :
    L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  have h1 : K.subgroupOf L ⊔ aschbacherSolvableCore 3 L = ⊤ := by
    have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) h
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
  have h3 := congrArg (Subgroup.map L.subtype) h1
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h3
  exact h3.symm

omit [Finite G] in
theorem card_sylow_three_of_card_eq {T : Type*} [Group T] [Finite T] (hT : Nat.card T = 1080)
    (S : Sylow 3 T) : Nat.card (S : Subgroup T) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hmul := Subgroup.card_mul_index (S : Subgroup T)
  have hidx := S.not_dvd_index
  rw [hk, hT] at hmul
  have hk6 : k ≤ 6 := by
    by_contra h
    have h7 : 3 ^ 7 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < (S : Subgroup T).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    nlinarith
  rw [hk]
  interval_cases k <;> omega

theorem exists_commutator_mem {K : Subgroup G}
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (hA6 : IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥) :
    ∃ a ∈ K, ∃ b ∈ K,
      a * b * a⁻¹ * b⁻¹ ∈ inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ∧
      a * b * a⁻¹ * b⁻¹ ≠ 1 ∧ (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := K ⊓ Subgroup.centralizer (K : Set G) with hY
  set Z := inSubgroup (CFSG.pCore 3) Y with hZ
  set θK := aschbacherSolvableCore 3 K with hθK
  set ρ := QuotientGroup.mk' θK with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective θK
  have hZK : Z ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2.1
  set ZK := Z.subgroupOf K with hZKdef
  have hZ3 : IsPGroup 3 ZK := by
    intro z
    have hz : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp z.2
    obtain ⟨y, hy, hyz⟩ := hz
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := Y)) ⟨y, hy⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : ((y : Y) : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun u : CFSG.pCore 3 Y => ((u : Y) : G)) hk
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hyz]
    exact h1
  have hZcent : ZK ≤ Subgroup.center K := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hz' : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨y, -, hyz⟩ := hz'
    have hyC : ((y : Y) : G) ∈ Subgroup.centralizer (K : Set G) := y.2.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hyz]
    exact (Subgroup.mem_centralizer_iff.mp hyC g g.2)
  have hZn : ZK.Normal := Subgroup.normal_of_le_center hZcent
  have hZT : ZK.map ρ ≤ Subgroup.center (K ⧸ θK) :=
    (Subgroup.map_mono hZcent).trans (Subgroup.map_center_le_center hρs)
  have hinjZ : Set.InjOn ρ (ZK : Set K) := injOn_mk_of_isPGroup Nat.prime_three hZ3
  have hcardZT : Nat.card (ZK.map ρ) = Nat.card ZK := by
    change Nat.card ((ZK.map ρ : Set (K ⧸ θK))) = Nat.card (ZK : Set K)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinjZ]
  have hZK1 : ZK ≠ ⊥ := by
    intro h
    apply hZne
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hZK hx
    have hx' : (⟨x, hxK⟩ : K) ∈ ZK := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  have hc3 : Nat.card (Subgroup.center (K ⧸ θK)) = 3 := hA6.1
  have hZTeq : ZK.map ρ = Subgroup.center (K ⧸ θK) := by
    refine Subgroup.eq_of_le_of_card_ge hZT ?_
    rw [hc3, hcardZT]
    have hdvd : Nat.card ZK ∣ 3 := by
      rw [← hc3, ← hcardZT]
      exact Subgroup.card_dvd_of_le hZT
    have hne1 : Nat.card ZK ≠ 1 := fun h1 => hZK1 (Subgroup.eq_bot_of_card_eq _ h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · omega
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 K))
  set PT := P.mapSurjective hρs with hPT
  have hPTeq : (PT : Subgroup (K ⧸ θK)) = (P : Subgroup K).map ρ := Sylow.coe_mapSurjective hρs P
  have hcardT : Nat.card (K ⧸ θK) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six hA6.isExtOf
  have hPT27 : Nat.card (PT : Subgroup (K ⧸ θK)) = 27 := card_sylow_three_of_card_eq hcardT PT
  have hZP : Subgroup.center (K ⧸ θK) ≤ (PT : Subgroup (K ⧸ θK)) := by
    have hcp : IsPGroup 3 (Subgroup.center (K ⧸ θK)) :=
      IsPGroup.of_card (n := 1) (by rw [hc3, pow_one])
    have : (Subgroup.center (K ⧸ θK)).Normal := inferInstance
    exact hcp.le_sylow_of_normal PT
  set C := (Subgroup.center (K ⧸ θK)).subgroupOf (PT : Subgroup (K ⧸ θK)) with hC
  have hCcard : Nat.card C = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv).trans hc3
  have hQcard : Nat.card ((PT : Subgroup (K ⧸ θK)) ⧸ C) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    rw [hPT27, hCcard] at h
    omega
  have hQab : IsMulCommutative ((PT : Subgroup (K ⧸ θK)) ⧸ C) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard
  have hcommC : ∀ s t : (PT : Subgroup (K ⧸ θK)), s * t * s⁻¹ * t⁻¹ ∈ C := by
    intro s t
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      (isMulCommutative_iff.mp hQab (s : _ ⧸ C) (t : _ ⧸ C))]
    group
  obtain ⟨z₀, hz₀Z, hz₀1, hz₀3⟩ := KFacts.K412.exists_ne_one_of_card_eq_three hc3
  have hperf : commutator (K ⧸ θK) = ⊤ := hq.1.commutator_eq_top
  have hnab := KFacts.K412.not_isMulCommutative_sylow hperf hz₀Z hz₀1 hz₀3 PT
  obtain ⟨s, t, hst⟩ : ∃ s t : (PT : Subgroup (K ⧸ θK)), s * t ≠ t * s := by
    by_contra h
    exact hnab (isMulCommutative_iff.mpr fun x y => by
      by_contra hxy
      exact h ⟨x, y, hxy⟩)
  have hs : (s : K ⧸ θK) ∈ (P : Subgroup K).map ρ := hPTeq ▸ s.2
  have ht : (t : K ⧸ θK) ∈ (P : Subgroup K).map ρ := hPTeq ▸ t.2
  obtain ⟨a, haP, has⟩ := hs
  obtain ⟨b, hbP, hbt⟩ := ht
  set w := a * b * a⁻¹ * b⁻¹ with hw
  have hwP : w ∈ (P : Subgroup K) :=
    mul_mem (mul_mem (mul_mem haP hbP) (inv_mem haP)) (inv_mem hbP)
  have hρw : ρ w = (s : K ⧸ θK) * t * (s : K ⧸ θK)⁻¹ * (t : K ⧸ θK)⁻¹ := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, has, hbt]
  have hρwZ : ρ w ∈ Subgroup.center (K ⧸ θK) := by
    rw [hρw]
    have h := hcommC s t
    rw [hC, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hρw1 : ρ w ≠ 1 := by
    rw [hρw]
    intro h
    apply hst
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (s : K ⧸ θK) * t = ((s : K ⧸ θK) * t * (s : K ⧸ θK)⁻¹ * (t : K ⧸ θK)⁻¹) * (t * s) := by
          group
      _ = t * s := by rw [h, one_mul]
  have hZKP : ZK ≤ (P : Subgroup K) := hZ3.le_sylow_of_normal P
  have hinjP : Set.InjOn ρ ((P : Subgroup K) : Set K) :=
    injOn_mk_of_isPGroup Nat.prime_three P.isPGroup'
  rw [← hZTeq] at hρwZ
  obtain ⟨u, huZ, hu⟩ := hρwZ
  have hwu : u = w := hinjP (hZKP huZ) hwP hu
  have hwZ : w ∈ ZK := hwu ▸ huZ
  have hw3 : w ^ 3 = 1 := by
    apply hinjP (pow_mem hwP 3) (one_mem _)
    rw [map_pow, map_one]
    have h := pow_card_eq_one' (x := (⟨ρ w, hZT ⟨u, huZ, hu.trans rfl⟩⟩ :
      Subgroup.center (K ⧸ θK)))
    rw [hc3] at h
    exact congrArg Subtype.val h
  refine ⟨a, a.2, b, b.2, ?_, ?_, ?_⟩
  · have h := Subgroup.mem_subgroupOf.mp hwZ
    simpa [hw] using h
  · intro h
    apply hρw1
    have : w = 1 := Subtype.ext (by simpa [hw] using h)
    rw [this, map_one]
  · have h := congrArg Subtype.val hw3
    simpa [hw] using h

omit [Finite G] in
theorem isTripleCover_of_mulEquiv {X X' Y : Type*} [Group X] [Group X'] [Group Y]
    (e : X ≃* X') (h : IsTripleCover X Y) : IsTripleCover X' Y := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map (e : X →* X') = Subgroup.center X' := Subgroup.map_center_eq e
  refine ⟨by rw [← hc, Subgroup.card_map_of_injective e.injective, hcard], ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e hc).symm.trans φ

omit [Finite G] in
noncomputable def quotThetaEquiv {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    A ⧸ aschbacherSolvableCore 3 A ≃* B ⧸ aschbacherSolvableCore 3 B :=
  QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)

omit [Finite G] in
theorem isQuasisimple_of_mem_thetaComponentsIn {H K : Subgroup G} [Finite H]
    (hK : K ∈ thetaComponentsIn H) : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  have : Finite K₀ := inferInstance
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (quotThetaEquiv (K₀.equivMapOfInjective H.subtype H.subtype_injective)) hK₀.2.2

theorem eq_top_of_isPerfect_of_isSubnormal {X : Type*} [Group X] [Finite X]
    (hX : IsQuasisimple X) {P : Subgroup X} (hP : Group.IsPerfect P) (hPs : P.IsSubnormal)
    (hP1 : P ≠ ⊥) : P = ⊤ := by
  have hcomp : IsComponent (⊤ : Subgroup X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hX,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hPs with h | h
  · exact top_le_iff.mp h
  · exfalso
    apply hP1
    have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer (P : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hcen : P ≤ Subgroup.center X := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) x hx).symm
    have hab : ∀ a b : P, a * b = b * a := fun a b =>
      Subtype.ext ((Subgroup.mem_center_iff.mp (hcen a.2)) b).symm
    have htop : commutator P = ⊤ := hP.commutator_eq_top
    have hbot : commutator P = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact hab b a
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ commutator P := htop ▸ Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

structure Config426 (X : Type) [Group X] [Finite X] (α : MulAut X) (P : Subgroup X) : Prop where
  quasisimple : IsQuasisimple X
  pow_three : α ^ 3 = 1
  mem : P ∈ thetaComponentsIn (fixSub α)
  tripleCover : IsTripleCover (P ⧸ aschbacherSolvableCore 3 P) (alternatingGroup (Fin 6))
  comm : ∃ a ∈ P, ∃ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 ∧
    (a * b * a⁻¹ * b⁻¹) ^ 3 = 1

namespace Config426

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem fixed (h : Config426 X α P) {x : X} (hx : x ∈ P) : α x = x :=
  le_of_mem_thetaComponentsIn h.mem hx

theorem isPerfect (h : Config426 X α P) : Group.IsPerfect P :=
  isPerfect_of_mem_thetaComponentsIn h.mem

theorem ne_bot (h : Config426 X α P) : P ≠ ⊥ := by
  obtain ⟨a, ha, b, hb, -, h1, -⟩ := h.comm
  intro hP
  apply h1
  rw [hP, Subgroup.mem_bot] at ha hb
  rw [ha, hb]
  group

theorem three_dvd_card_center (h : Config426 X α P) : 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨a, -, b, -, hz, h1, h3⟩ := h.comm
  have hord : orderOf (⟨_, hz⟩ : Subgroup.center X) = 3 := by
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h' => h1 (congrArg Subtype.val h'))
    simpa using h3
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem eq_top_of_eq_one (h : Config426 X α P) (hα : α = 1) : P = ⊤ := by
  have hmem := h.mem
  rw [hα, fixSub_one] at hmem
  obtain ⟨P₀, hP₀, rfl⟩ := hmem
  have hs : (P₀.map (⊤ : Subgroup X).subtype).IsSubnormal :=
    hP₀.2.1.map (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  exact eq_top_of_isPerfect_of_isSubnormal h.quasisimple h.isPerfect hs h.ne_bot

end Config426

theorem config426_of {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) {c : G}
    (hc3 : orderOf c = 3) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)))
    (hA6 : IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥)
    (hZc : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.center G) :
    3 ∣ Nat.card (Subgroup.center G) ∧ K ≤ L ∧
    ∃ hcN : c ∈ Subgroup.normalizer (L : Set G),
      Config426 (L ⧸ aschbacherSolvableCore 3 L) (thetaAut L hcN)
        ((K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hKle := le_of_mem_thetaComponentsIn hK
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKle.trans inf_le_right
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := isQuasisimple_of_mem_thetaComponentsIn hK
  obtain ⟨a, haK, b, hbK, hwZ, hw1, hw3⟩ := exists_commutator_mem hKq hA6 hZne
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at haK hbK
    apply hw1
    rw [haK, hbK]
    group
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_perfect_le hL hKp hK1 hKL hKc
  have hwc : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G := hZc hwZ
  set w := a * b * a⁻¹ * b⁻¹ with hw
  have h3G : 3 ∣ Nat.card (Subgroup.center G) := by
    have hord : orderOf (⟨w, hwc⟩ : Subgroup.center G) = 3 := by
      refine orderOf_eq_prime (Subtype.ext ?_) (fun h' => hw1 (congrArg Subtype.val h'))
      simpa using hw3
    rw [← hord]
    exact orderOf_dvd_natCard _
  refine ⟨h3G, hKL, hcN, hL.2.2, thetaAut_pow_eq_one L hcN hc3',
    map_mem_thetaComponentsIn_fixSub L hcN hc3' hK, ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_quotTheta_map_equiv L hKL
    exact isTripleCover_of_mulEquiv e hA6
  · set N := aschbacherSolvableCore 3 L with hN
    set π := QuotientGroup.mk' N with hπ
    have hwL : w ∈ L := mul_mem (mul_mem (mul_mem (hKL haK) (hKL hbK)) (inv_mem (hKL haK)))
      (inv_mem (hKL hbK))
    have hwZL : (⟨w, hwL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hwc g)
    have hcomm : π ⟨a, hKL haK⟩ * π ⟨b, hKL hbK⟩ * (π ⟨a, hKL haK⟩)⁻¹ * (π ⟨b, hKL hbK⟩)⁻¹ =
        π ⟨w, hwL⟩ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    refine ⟨π ⟨a, hKL haK⟩, Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr haK),
      π ⟨b, hKL hbK⟩, Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbK), ?_, ?_, ?_⟩
    · rw [hcomm]
      exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
        (Subgroup.mem_map_of_mem π hwZL)
    · rw [hcomm, hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      intro hmem
      have hord : orderOf (⟨⟨w, hwL⟩, hmem⟩ : N) ∣ 3 := by
        refine orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext ?_))
        simpa using hw3
      have hord2 : orderOf (⟨⟨w, hwL⟩, hmem⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      have hθ3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
      · rw [orderOf_eq_one_iff] at h1
        exact hw1 (congrArg (fun u : N => ((u : L) : G)) h1)
      · exact hθ3 (h3 ▸ hord2)
    · rw [hcomm, ← map_pow]
      have : (⟨w, hwL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
      rw [this, map_one]

end CFSG.RankThree.PartTwo.Sec4.Item426
