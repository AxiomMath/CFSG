module

public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoPartCommutatorsOdd
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open Subgroup
open scoped Pointwise commutatorElement

section Generic

variable {C : Type*} [Group C]

theorem mulAut_conj_conj_inv (η : MulAut C) (x : C) :
    η * MulAut.conj x * η⁻¹ = MulAut.conj (η x) :=
  MulEquiv.ext fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem apply_eq_of_commute_conj (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    {η : MulAut C} {x : C} (h : η * MulAut.conj x = MulAut.conj x * η) : η x = x := by
  apply hinj
  rw [← mulAut_conj_conj_inv, h, mul_inv_cancel_right]

theorem apply_mem_centralizer_of_apply_eq {η : MulAut C} {x : C} (hη : η x = x) {y : C}
    (hy : y ∈ centralizer ({x} : Set C)) : η y ∈ centralizer ({x} : Set C) := by
  rw [mem_centralizer_singleton_iff] at hy ⊢
  rw [← hη, ← map_mul, ← map_mul, hy]

theorem apply_mem_commutator_centralizer_of_apply_eq {η : MulAut C} {x : C} (hη : η x = x)
    {r : C} (hr : r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆) :
    η r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ := by
  have hY : (centralizer ({x} : Set C)).map η.toMonoidHom = centralizer ({x} : Set C) := by
    rw [CFSG.RankThree.PartOne.map_centralizer_singleton_mulEquiv, hη]
  have h1 : η r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆.map η.toMonoidHom :=
    ⟨r, hr, rfl⟩
  rwa [Subgroup.map_commutator, hY] at h1

theorem apply_mem_centralizer_derived_of_apply_eq {η : MulAut C} {x : C} (hη : η x = x)
    {z : C} (hz : z ∈ centralizer ({x} : Set C) ⊓
      centralizer ((⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C) :
        Set C)) :
    η z ∈ centralizer ({x} : Set C) ⊓
      centralizer ((⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C) :
        Set C) := by
  obtain ⟨hzY, hzR⟩ := Subgroup.mem_inf.1 hz
  refine Subgroup.mem_inf.2 ⟨apply_mem_centralizer_of_apply_eq hη hzY,
    Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
  have hη' : η⁻¹ x = x := by
    nth_rewrite 1 [← hη]
    exact MulAut.inv_apply_self _ _ _
  have h1 := Subgroup.mem_centralizer_iff.1 hzR _
    (apply_mem_commutator_centralizer_of_apply_eq hη' hr)
  have h2 := congrArg η h1
  rwa [map_mul, map_mul, MulAut.apply_inv_self] at h2

variable [Finite C]

theorem aschbacherSolvableCore_fixes_quasisimple
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ} (hp : p.Prime)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C)
    {R : Subgroup C} (hRx : R ≤ centralizer ({x} : Set C))
    (hRinv : ∀ η : MulAut C, η x = x → ∀ r ∈ R, η r ∈ R) (hRq : CFSG.IsQuasisimple R) :
    ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R, (s : MulAut C) r = r := by
  classical
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ with hb
  set M : Subgroup B := centralizer ({b} : Set B) with hM
  have hfix : ∀ m ∈ M, (m : MulAut C) x = x := fun m hm =>
    apply_eq_of_commute_conj hinj (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  set β : C →* B := (MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩ with hβ
  have hβinj : Function.Injective β := fun c d h => hinj (congrArg Subtype.val h)
  have hRM : R.map β ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    change MulAut.conj r * MulAut.conj x = MulAut.conj x * MulAut.conj r
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 (hRx hr))]
  set N : Subgroup M := (R.map β).subgroupOf M with hN
  have hNnormal : N.Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨r, hr, hrn⟩ := hn
    refine ⟨(m : MulAut C) r, hRinv _ (hfix m m.2) r hr, Subtype.ext ?_⟩
    change MulAut.conj ((m : MulAut C) r) = (m : MulAut C) * ((n : B) : MulAut C) * (m : MulAut C)⁻¹
    rw [← mulAut_conj_conj_inv,
      show MulAut.conj r = ((n : B) : MulAut C) from congrArg Subtype.val hrn]
  have e : R ≃* N := (Subgroup.equivMapOfInjective R β hβinj).trans
    (Subgroup.subgroupOfEquivOfLe hRM).symm
  have hNcomp : IsComponent N :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hRq, hNnormal.isSubnormal⟩
  obtain ⟨hsolv, -⟩ := solvable_prime_complement_core_characterization (H := M) hp
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (aschbacherSolvableCore_normal p M).isSubnormal).1 N hNcomp
  intro s hs r hr
  obtain ⟨s', hs', rfl⟩ := hs
  have hn : (⟨β r, hRM ⟨r, hr, rfl⟩⟩ : M) ∈ N := ⟨r, hr, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hn) s' hs'
  have h2 := congrArg (fun m : M => ((m : B) : MulAut C)) h1
  exact apply_eq_of_commute_conj hinj h2

theorem odd_card_commutator_of_invariant
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C) {X : Subgroup C}
    (hXx : X ≤ centralizer ({x} : Set C)) (hXinv : ∀ η : MulAut C, η x = x → ∀ z ∈ X, η z ∈ X)
    {N : Type*} [CommGroup N] [IsCyclic N] (φ : X →* (Fin Tag.G2.rank → N))
    (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A S : Subgroup B}
    (hA : IsPGroup p A) (hAM : A ≤ centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B))
    (hSM : S ≤ centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B))
    (hSA : ⁅S, A⁆ ≤ (X.map (MulAut.conj : C →* MulAut C)).comap B.subtype) :
    Odd (Nat.card (⁅S, A⁆ : Subgroup B)) := by
  classical
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ with hb
  set M : Subgroup B := centralizer ({b} : Set B) with hM
  have hfix : ∀ m ∈ M, (m : MulAut C) x = x := fun m hm =>
    apply_eq_of_commute_conj hinj (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  set β : C →* B := (MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩ with hβ
  have hβinj : Function.Injective β := fun c d h => hinj (congrArg Subtype.val h)
  have hXM : X.map β ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    change MulAut.conj z * MulAut.conj x = MulAut.conj x * MulAut.conj z
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 (hXx hz))]
  set Q : Subgroup M := (X.map β).subgroupOf M with hQ
  have hQnormal : Q.Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨z, hz, hzn⟩ := hn
    refine ⟨(m : MulAut C) z, hXinv _ (hfix m m.2) z hz, Subtype.ext ?_⟩
    change MulAut.conj ((m : MulAut C) z) =
      (m : MulAut C) * ((n : B) : MulAut C) * (m : MulAut C)⁻¹
    rw [← mulAut_conj_conj_inv,
      show MulAut.conj z = ((n : B) : MulAut C) from congrArg Subtype.val hzn]
  have : Q.Normal := hQnormal
  let eQ : X ≃* Q := (Subgroup.equivMapOfInjective X β hβinj).trans
    (Subgroup.subgroupOfEquivOfLe hXM).symm
  set ψ : Q →* (Fin Tag.G2.rank → N) := φ.comp eQ.symm.toMonoidHom with hψ
  have hψ : Function.Injective ψ := hφ.comp eQ.symm.injective
  have hQab : ∀ u ∈ Q, ∀ v ∈ Q, u * v = v * u := by
    intro u hu v hv
    have h := hψ.eq_iff.1 (show ψ (⟨u, hu⟩ * ⟨v, hv⟩) = ψ (⟨v, hv⟩ * ⟨u, hu⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hgen : ∃ T : Sylow 2 Q, ∃ u v : Q, closure ({u, v} : Set Q) = (T : Subgroup Q) := by
    obtain ⟨T⟩ : Nonempty (Sylow 2 Q) := inferInstance
    obtain ⟨-, u, v, huv⟩ := comm_and_two_generated_of_injective
      (ψ.comp (T : Subgroup Q).subtype) (hψ.comp (T : Subgroup Q).subtype_injective)
    refine ⟨T, u, v, ?_⟩
    have h := congrArg (Subgroup.map (T : Subgroup Q).subtype) huv
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hA' : IsPGroup p (A.subgroupOf M) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  have hmap : ⁅S.subgroupOf M, A.subgroupOf M⁆.map M.subtype = ⁅S, A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hSM, inf_of_le_left hAM]
  have hSA' : ⁅S.subgroupOf M, A.subgroupOf M⁆ ≤ Q := by
    intro w hw
    have h1 : (w : B) ∈ ⁅S, A⁆ := hmap ▸ Subgroup.mem_map_of_mem M.subtype hw
    obtain ⟨z, hz, hzw⟩ := hSA h1
    exact ⟨z, hz, Subtype.ext hzw⟩
  have hodd := CFSG.RankThree.GroupTheory.SteinbergBM.abelian_two_generator_two_part_commutators_odd
    hQab hgen hp hp3 hA' hSA'
  rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective]
  exact hodd

end Generic

section G2

variable {K : Type} [Field K]

theorem map_subtype_centralizer_singleton {G : Type*} [Group G] (H : Subgroup G) (y : H) :
    (centralizer ({y} : Set H)).map H.subtype = H ⊓ centralizer ({(y : G)} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hw))⟩
  · rintro ⟨hzH, hz⟩
    exact ⟨⟨z, hzH⟩, mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 hz)), rfl⟩

theorem map_centralizer_eq_toralCentralizer {x g : adjointGroup .G2 K}
    {a : Fin Tag.G2.rank → Kˣ}
    (hxa : ((g * x * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 a) :
    (centralizer ({x} : Set (adjointGroup .G2 K))).map
        ((adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom) =
      toralCentralizer .G2 K a := by
  rw [← Subgroup.map_map, map_conj_centralizer_singleton_eq, map_subtype_centralizer_singleton,
    hxa]
  rfl

theorem exists_injective_of_toralCentralizer_eq_torusGroup {x g : adjointGroup .G2 K}
    {a : Fin Tag.G2.rank → Kˣ}
    (hxa : ((g * x * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 a)
    (hMH : toralCentralizer .G2 K a = torusGroup .G2 K) :
    ∃ φ : centralizer ({x} : Set (adjointGroup .G2 K)) →* (Fin Tag.G2.rank → Kˣ),
      Function.Injective φ := by
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hmap := map_centralizer_eq_toralCentralizer hxa
  rw [hMH] at hmap
  set F := (adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hmem : ∀ y : centralizer ({x} : Set (adjointGroup .G2 K)),
      (F.comp (centralizer ({x} : Set (adjointGroup .G2 K))).subtype) y ∈ torusGroup .G2 K :=
    fun y => hmap ▸ ⟨y, y.2, rfl⟩
  refine ⟨e.symm.toMonoidHom.comp
    ((F.comp (centralizer ({x} : Set (adjointGroup .G2 K))).subtype).codRestrict _ hmem), ?_⟩
  refine e.symm.injective.comp fun y z h => Subtype.ext (hF ?_)
  exact congrArg (fun w : torusGroup .G2 K => (w : ModGL .G2 K)) h

theorem derived_centralizer_data {x g : adjointGroup .G2 K} {a : Fin Tag.G2.rank → Kˣ}
    (hxa : ((g * x * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 a)
    {Q : Subgroup (ModGL .G2 K)}
    (hcomm : ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ = Q)
    (hQq : CFSG.IsQuasisimple Q)
    (hZ : toralCentralizer .G2 K a ⊓ centralizer (Q : Set (ModGL .G2 K)) =
      (center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype)
    (hZH : (center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
      torusGroup .G2 K) :
    (⁅centralizer ({x} : Set (adjointGroup .G2 K)), centralizer ({x} : Set (adjointGroup .G2 K))⁆ :
        Subgroup (adjointGroup .G2 K)).map
        ((adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom) = Q ∧
      CFSG.IsQuasisimple (⁅centralizer ({x} : Set (adjointGroup .G2 K)),
        centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ∧
      ∃ φ : (centralizer ({x} : Set (adjointGroup .G2 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .G2 K)),
            centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) :
              Set (adjointGroup .G2 K)) : Subgroup (adjointGroup .G2 K)) →*
            (Fin Tag.G2.rank → Kˣ),
        Function.Injective φ := by
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hmap := map_centralizer_eq_toralCentralizer hxa
  set Y := centralizer ({x} : Set (adjointGroup .G2 K)) with hY
  set F := (adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hRmap : (⁅Y, Y⁆ : Subgroup (adjointGroup .G2 K)).map F = Q := by
    rw [Subgroup.map_commutator, hmap, hcomm]
  have eR : (⁅Y, Y⁆ : Subgroup (adjointGroup .G2 K)) ≃* Q :=
    (Subgroup.equivMapOfInjective _ F hF).trans (MulEquiv.subgroupCongr hRmap)
  refine ⟨hRmap, CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hQq, ?_⟩
  set X := Y ⊓ centralizer ((⁅Y, Y⁆ : Subgroup (adjointGroup .G2 K)) :
    Set (adjointGroup .G2 K)) with hX
  have hmem : ∀ z : X, (F.comp X.subtype) z ∈ torusGroup .G2 K := by
    rintro ⟨z, hzY, hzR⟩
    refine hZH (hZ ▸ Subgroup.mem_inf.2 ⟨hmap ▸ ⟨z, hzY, rfl⟩,
      Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩)
    rw [← hRmap] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    change F r * F z = F z * F r
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hzR r hr]
  refine ⟨e.symm.toMonoidHom.comp ((F.comp X.subtype).codRestrict _ hmem), ?_⟩
  refine e.symm.injective.comp fun y z h => Subtype.ext (hF ?_)
  exact congrArg (fun w : torusGroup .G2 K => (w : ModGL .G2 K)) h

end G2

theorem commutatorElement_apply_of_fixed {C : Type*} [Group C] {s e : MulAut C} {r : C}
    (h1 : s r = r) (h2 : s (e⁻¹ r) = e⁻¹ r) : ⁅s, e⁆ r = r := by
  have h2' : s⁻¹ (e⁻¹ r) = e⁻¹ r := by
    conv_lhs => rw [← h2]
    exact MulAut.inv_apply_self _ _ _
  rw [commutatorElement_def, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, h2',
    MulAut.apply_inv_self, h1]

theorem odd_card_commutator_split_inner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (t : B) (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (adjointGroup .G2 K)) ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ :
      Subgroup B)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  set R := (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range with hR
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2 (Or.inr ⟨rfl, hℓ3⟩)
  obtain ⟨φ₀, -, -, hφgen, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ₀, hφgen⟩
  obtain ⟨hconjH, -, -, -, -⟩ := odd_G2_split_prime_toral_Sylow_and_centralizers K hKodd hp hp3 hpq
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  obtain ⟨x, hx⟩ := htinn
  have htx : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  subst htx
  have htp : orderOf (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B) = p := orderOf_eq_prime (hEpow _ htE) ht1
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, ← htp, Subgroup.orderOf_mk]
  have hPx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one])
  obtain ⟨g, hg⟩ := hconjH _ hPx
  have hgx : g * x * g⁻¹ ∈ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
    hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgx
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [← ha, orderOf_injective _ (adjointGroup .G2 K).subtype_injective,
      show g * x * g⁻¹ = (MulAut.conj g).toMonoidHom x from rfl,
      orderOf_injective _ (MulAut.conj g).injective x, hxp]
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ with hb
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B)) with hS
  have hSM : S ≤ centralizer ({b} : Set B) := Subgroup.map_subtype_le _
  have hEM : E ≤ centralizer ({b} : Set B) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
      (hE.is_comm.comm (⟨b, htE⟩ : E) ⟨e, he⟩)).symm
  have hfixM : ∀ m ∈ centralizer ({b} : Set B), (m : MulAut (adjointGroup .G2 K)) x = x :=
    fun m hm => apply_eq_of_commute_conj hinj
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  have hgenY : ∀ s ∈ S, ∀ e ∈ E, ∃ c ∈ centralizer ({x} : Set (adjointGroup .G2 K)),
      MulAut.conj c = ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) := by
    intro s hs e he
    have hct : ⁅s, e⁆ ∈ centralizer ({b} : Set B) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hSM hs) (hEM he)) (inv_mem (hSM hs))) (inv_mem (hEM he))
    have hΘ : ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) ∈ R := by
      rw [hR, ← hΘker, MonoidHom.mem_ker, show ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) =
        ⁅(s : MulAut (adjointGroup .G2 K)), (e : MulAut (adjointGroup .G2 K))⁆ from
          map_commutatorElement B.subtype s e, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact IsMulCommutative.is_comm.comm _ _
    obtain ⟨c, hc⟩ := hΘ
    refine ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), hc⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hct)
    simp only [Subgroup.coe_mul] at h1
    rw [map_mul, map_mul, hc]
    exact h1
  rcases toral_centralizer_cases_G2 K hKodd hp hp3 hpq a hao with ⟨⟨-, hMH, -⟩, -⟩ |
    ⟨⟨α, -, -, -, -, -, hQq, hcomm, hZ, hZH, -⟩, -⟩
  ·
    obtain ⟨φ, hφ⟩ := exists_injective_of_toralCentralizer_eq_torusGroup ha hMH
    refine odd_card_commutator_of_invariant hinj hB x le_rfl
      (fun η hη z hz => apply_mem_centralizer_of_apply_eq hη hz) φ hφ hp hp3
      (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    exact ⟨c, hc, hce⟩
  ·
    obtain ⟨-, hRq, φ, hφ⟩ := derived_centralizer_data ha hcomm hQq hZ hZH
    have hRY : (⁅centralizer ({x} : Set (adjointGroup .G2 K)),
        centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
        centralizer ({x} : Set (adjointGroup .G2 K)) :=
      Subgroup.commutator_le.2 fun u hu v hv => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    have hfixR := aschbacherSolvableCore_fixes_quasisimple hinj hp hB x hRY
      (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hRq
    refine odd_card_commutator_of_invariant hinj hB x inf_le_left
      (fun η hη z hz => apply_mem_centralizer_derived_of_apply_eq hη hz) φ hφ hp hp3
      (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    refine ⟨c, Subgroup.mem_inf.2 ⟨hc, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hce⟩
    have he' : ((e : B) : MulAut (adjointGroup .G2 K))⁻¹ x = x := by
      nth_rewrite 1 [← hfixM e (hEM he)]
      exact MulAut.inv_apply_self _ _ _
    have h1 : (MulAut.conj c) r = r := by
      rw [hce, show ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) =
        ⁅(s : MulAut (adjointGroup .G2 K)), (e : MulAut (adjointGroup .G2 K))⁆ from
          map_commutatorElement B.subtype s e]
      exact commutatorElement_apply_of_fixed (hfixR s hs r hr)
        (hfixR s hs _ (apply_mem_commutator_centralizer_of_apply_eq he' hr))
    rw [MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

section Intersection

variable {K : Type} [Field K]

theorem derived_centralizer_root_data [Finite K] (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) {u g : adjointGroup .G2 K}
    {c : Fin Tag.G2.rank → Kˣ}
    (hu : ((g * u * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 c)
    (hcp : c ^ p = 1) (hc1 : c ≠ 1) (i : Fin Tag.G2.rank) (hci : c i = 1) :
    (⁅centralizer ({u} : Set (adjointGroup .G2 K)), centralizer ({u} : Set (adjointGroup .G2 K))⁆ :
        Subgroup (adjointGroup .G2 K)).map
        ((adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom) =
      rootSubgroup .G2 K (Pi.single i 1) ⊔ rootSubgroup .G2 K (-Pi.single i 1) ∧
    CFSG.IsQuasisimple (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hao : orderOf (rootDiagUnit .G2 c) = p := by rw [orderOf_rootDiagUnit, hco]
  have hiker : (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ∈ rootCharKernel c :=
    ⟨isRoot_single .G2 i, by rw [rootChar_pi_single, hci]⟩
  rcases toral_centralizer_cases_G2 K hK hp hp3 hpq c hao with ⟨⟨hker, -, -⟩, -⟩ |
    ⟨⟨α, -, hkerα, -, -, -, hQq, hcomm, hZ, hZH, -⟩, -⟩
  · rw [hker] at hiker
    exact absurd hiker (Set.notMem_empty _)
  obtain ⟨hRmap, hRq, -⟩ := derived_centralizer_data hu hcomm hQq hZ hZH
  refine ⟨hRmap.trans ?_, hRq⟩
  rw [hkerα] at hiker
  rcases hiker with h | h
  · rw [h]
  · rw [show α = -Pi.single i 1 by rw [h, neg_neg], neg_neg, sup_comm]

theorem rootSubgroup_simple_sup_eq_adjointGroup :
    (rootSubgroup .G2 K (Pi.single g2ia 1) ⊔ rootSubgroup .G2 K (-Pi.single g2ia 1)) ⊔
      (rootSubgroup .G2 K (Pi.single g2ir 1) ⊔ rootSubgroup .G2 K (-Pi.single g2ir 1)) =
      adjointGroup .G2 K := by
  have hx : ∀ i : Fin Tag.G2.rank, ∀ c : K, xUnit .G2 K i c ∈
      (rootSubgroup .G2 K (Pi.single g2ia 1) ⊔ rootSubgroup .G2 K (-Pi.single g2ia 1)) ⊔
        (rootSubgroup .G2 K (Pi.single g2ir 1) ⊔ rootSubgroup .G2 K (-Pi.single g2ir 1)) := by
    intro i c
    rcases fin_G2_cases i with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_closure
        ⟨c, pinnedX_single .G2 K g2ia c⟩))
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.subset_closure
        ⟨c, pinnedX_single .G2 K g2ir c⟩))
  have hy : ∀ i : Fin Tag.G2.rank, ∀ c : K, yUnit .G2 K i c ∈
      (rootSubgroup .G2 K (Pi.single g2ia 1) ⊔ rootSubgroup .G2 K (-Pi.single g2ia 1)) ⊔
        (rootSubgroup .G2 K (Pi.single g2ir 1) ⊔ rootSubgroup .G2 K (-Pi.single g2ir 1)) := by
    intro i c
    rcases fin_G2_cases i with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure
        ⟨c, pinnedX_neg_single .G2 K g2ia c⟩))
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.subset_closure
        ⟨c, pinnedX_neg_single .G2 K g2ir c⟩))
  refine le_antisymm (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)) ?_
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_adjointGroup _ c
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_adjointGroup _ c
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_adjointGroup _ c
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_adjointGroup _ c
  · rw [adjointGroup, Subgroup.closure_le]
    rintro z ⟨i, c, h | h⟩
    · rw [show z = xUnit .G2 K i c from Units.ext h]
      exact hx i c
    · rw [show z = yUnit .G2 K i c from Units.ext h]
      exact hy i c

theorem thetaT_eq_bot_split {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    thetaT p E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  set R := (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range with hR
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hNF := conj_normalForm_of_pointwise
    (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)).1
  obtain ⟨hconjH, -, -, -, -⟩ := odd_G2_split_prime_toral_Sylow_and_centralizers K hKodd hp hp3 hpq
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  by_cases hEinn : E.map B.subtype ≤ R
  swap
  ·
    obtain ⟨b, hbE, hbinn⟩ : ∃ b ∈ E, (b : MulAut (adjointGroup .G2 K)) ∉ R := by
      by_contra h
      push Not at h
      exact hEinn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
    have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
    have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF b
    have hcore := (odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK
      hNF hp B hB b hbinn hbp x σ hxσ).2.2.2
    refine eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 ?_)))
    rw [inSubgroup, hcore, Subgroup.map_bot]
  set P : Subgroup (adjointGroup .G2 K) := (E.map B.subtype).comap MulAut.conj with hPdef
  have hPmap : P.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hEinn
  have eP : E ≃* P := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
    ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective P _ hinj).symm)
  have hPcard : Nat.card P = p ^ 2 := by rw [← Nat.card_congr eP.toEquiv, hEcard]
  have hPp : IsPGroup p P := (IsElementaryAbelian.isPGroup p E).of_equiv eP
  have hPpow : ∀ u ∈ P, u ^ p = 1 := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    apply hinj
    rw [map_pow, ← hee, map_one]
    exact congrArg Subtype.val (hEpow e he)
  obtain ⟨g, hg⟩ := hconjH P hPp
  set F := (adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hPH : P.map F = torusTorsion K p := by
    have : NeZero p := ⟨hp.ne_zero⟩
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      rw [mem_torusTorsion_iff]
      refine ⟨hg ⟨u, hu, rfl⟩, ?_⟩
      rw [← map_pow, hPpow u hu, map_one]
    · rw [natCard_torusTorsion hpq, Subgroup.card_map_of_injective hF, hPcard]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpq)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have key : ∀ i : Fin Tag.G2.rank, ∃ u ∈ P, u ≠ 1 ∧
      (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
          centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)).map F =
        rootSubgroup .G2 K (Pi.single i 1) ⊔ rootSubgroup .G2 K (-Pi.single i 1) ∧
      CFSG.IsQuasisimple (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
        centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      rcases fin_G2_cases i with rfl | rfl
      · exact ⟨g2ir, by decide⟩
      · exact ⟨g2ia, by decide⟩
    set c : Fin Tag.G2.rank → Kˣ := fun k => if k = i then 1 else ζ with hc
    have hcp : c ^ p = 1 := funext fun k => by
      by_cases hk : k = i <;> simp [hc, hk, hζp]
    have hc1 : c ≠ 1 := fun h => hζ1 (by simpa [hc, hji] using congrFun h j)
    have hci : c i = 1 := by simp [hc]
    have hdc : rootDiagUnit .G2 c ∈ P.map F := by
      rw [hPH]
      exact (rootDiagUnit_mem_torusTorsion_iff p c).2 hcp
    obtain ⟨u, hu, hdu⟩ := hdc
    have hu1 : u ≠ 1 := fun h => hc1 (rootDiagUnit_injective (by
      rw [← hdu, h, map_one, rootDiagUnit_one]))
    obtain ⟨hRmap, hRq⟩ := derived_centralizer_root_data hKodd hp hp3 hpq hdu hcp hc1 i hci
    exact ⟨u, hu, hu1, hRmap, hRq⟩
  obtain ⟨u₁, hu₁, hu₁1, hR₁, hq₁⟩ := key g2ia
  obtain ⟨u₂, hu₂, hu₂1, hR₂, hq₂⟩ := key g2ir
  have htop : (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
        centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ⊔
      ⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
        centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ = ⊤ := by
    apply Subgroup.map_injective hF
    rw [Subgroup.map_sup, hR₁, hR₂, rootSubgroup_simple_sup_eq_adjointGroup]
    ext z
    refine ⟨fun hz => ⟨g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g, Subgroup.mem_top _, ?_⟩, ?_⟩
    · change ((g * (g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g) * g⁻¹ : adjointGroup .G2 K) :
        ModGL .G2 K) = z
      rw [show g * (g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g) * g⁻¹ =
        (⟨z, hz⟩ : adjointGroup .G2 K) by group]
    · rintro ⟨y, -, rfl⟩
      exact ((MulAut.conj g) y).2
  have hbE : ∀ u ∈ P, (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ∈ E := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    rwa [show (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) = e from Subtype.ext hee.symm]
  have hb1 : ∀ u : adjointGroup .G2 K, u ≠ 1 → (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ≠ 1 :=
    fun u hu h => hu (hinj (congrArg Subtype.val h))
  have hRY : ∀ u : adjointGroup .G2 K, (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
      centralizer ({u} : Set (adjointGroup .G2 K)) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  have hmem : ∀ a ∈ E, a ≠ 1 → s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set B)) := by
    simp only [thetaT, Subgroup.mem_iInf] at hs
    exact hs
  have hs₁ := hmem _ (hbE u₁ hu₁) (hb1 u₁ hu₁1)
  have hs₂ := hmem _ (hbE u₂ hu₂) (hb1 u₂ hu₂1)
  have hle : (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
        centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ⊔
      ⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
        centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ ≤
      MonoidHom.eqLocus (s : MulAut (adjointGroup .G2 K)).toMonoidHom (MonoidHom.id _) :=
    sup_le (fun r hr => hfix₁ s hs₁ r hr) (fun r hr => hfix₂ s hs₂ r hr)
  rw [htop] at hle
  rw [Subgroup.mem_bot]
  exact Subtype.ext (MulEquiv.ext fun y => hle (Subgroup.mem_top y))

end Intersection

theorem odd_G2_split_cross_prime_inner_actor_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (adjointGroup .G2 K)) ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    thetaT p E = ⊥ ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ :
      Subgroup B)) ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔
      thetaT p E)) := by
  have hIB := thetaT_eq_bot_split hℓ hℓ2 hℓ3 hf K hK hp hp3 hpq B hB E hE hEcard
  have hodd := odd_card_commutator_split_inner hℓ hℓ2 hℓ3 hf K hK hp hp3 hpq B hB E hE t htE ht1
    htinn
  refine ⟨hIB, hodd, ?_, ?_⟩
  · rw [hIB, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · rw [hIB, sup_bot_eq]
    exact hodd

end CFSG.RankThree.Chevalley
