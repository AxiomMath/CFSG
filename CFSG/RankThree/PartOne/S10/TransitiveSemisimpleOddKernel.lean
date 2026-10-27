module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
import CFSG.RankThree.Coprime.EvenCenterSectionCover

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Coprime
open scoped IsMulCommutative commutatorElement

namespace TransitiveSemisimple

theorem exists_coordSubgroup_le_of_normal {I : Type} [DecidableEq I] (S : I → Type)
    [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)] (hnonab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (J : Subgroup (∀ i, S i)) [J.Normal] (hJ : J ≠ ⊥) : ∃ i, coordSubgroup S i ≤ J := by
  obtain ⟨⟨j, hjJ⟩, hj1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJ
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ 1 := Function.ne_iff.mp fun h => hj1 (Subtype.ext h)
  have hcenter : center (S i) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hnonab i)).2
  obtain ⟨s, hs⟩ : ∃ s : S i, ⁅s, j i⁆ ≠ 1 := by
    by_contra h
    refine hi ?_
    have hmem : j i ∈ center (S i) := Subgroup.mem_center_iff.mpr fun s =>
      commutatorElement_eq_one_iff_mul_comm.mp (not_not.mp (not_exists.mp h s))
    rwa [hcenter, Subgroup.mem_bot] at hmem
  have hmem : Pi.mulSingle i ⁅s, j i⁆ ∈ J := by
    have h1 := Subgroup.Normal.conj_mem ‹J.Normal› j hjJ (Pi.mulSingle i s)
    have h2 := J.mul_mem h1 (J.inv_mem hjJ)
    convert h2 using 1
    funext k
    by_cases hk : k = i
    · subst hk
      simp [commutatorElement_def]
    · simp [Pi.mulSingle_eq_of_ne hk]
  have hT : J.comap (MonoidHom.mulSingle S i) ≠ ⊥ := by
    intro h
    have : ⁅s, j i⁆ ∈ J.comap (MonoidHom.mulSingle S i) := hmem
    rw [h, Subgroup.mem_bot] at this
    exact hs this
  have hTtop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (J.comap (MonoidHom.mulSingle S i))).resolve_left hT
  refine ⟨i, ?_⟩
  rintro _ ⟨u, rfl⟩
  have : u ∈ J.comap (MonoidHom.mulSingle S i) := by
    rw [hTtop]
    exact mem_top u
  exact this

theorem invariant_normal_le_or_sup_eq_top {K : Type*} [Group K] {A : Type*} [Group A]
    [MulDistribMulAction A K] (C : Subgroup K) [C.Normal] (hCinv : ∀ a : A, ∀ c ∈ C, a • c ∈ C)
    {I : Type} [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, Group (S i)]
    [∀ i, IsSimpleGroup (S i)] (hnonab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (φ : K ⧸ C ≃* (∀ i, S i))
    (htrans : ∀ i j : I, ∃ a : A, ∀ k : K,
      φ (k : K ⧸ C) ∈ coordSubgroup S i ↔ φ ((a • k : K) : K ⧸ C) ∈ coordSubgroup S j)
    (N : Subgroup K) [N.Normal] (hN : ∀ a : A, ∀ k ∈ N, a • k ∈ N) :
    N ≤ C ∨ N ⊔ C = ⊤ := by
  let π : K →* ∀ i, S i := φ.toMonoidHom.comp (QuotientGroup.mk' C)
  have hπ : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective C)
  have hker : ∀ k, π k = 1 ↔ k ∈ C := fun k => by
    change φ (k : K ⧸ C) = 1 ↔ k ∈ C
    rw [← map_one φ, φ.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hJn : (N.map π).Normal := Subgroup.Normal.map ‹N.Normal› π hπ
  by_cases hJbot : N.map π = ⊥
  · left
    intro n hn
    have : π n ∈ N.map π := ⟨n, hn, rfl⟩
    rw [hJbot, Subgroup.mem_bot] at this
    exact (hker n).mp this
  · right
    obtain ⟨i, hi⟩ := exists_coordSubgroup_le_of_normal S hnonab (N.map π) hJbot
    have hN'inv : ∀ a : A, ∀ k ∈ N ⊔ C, a • k ∈ N ⊔ C := by
      intro a
      have hle : N ⊔ C ≤ (N ⊔ C).comap (MulDistribMulAction.toMonoidHom K a) :=
        sup_le (fun k hk => Subgroup.mem_sup_left (hN a k hk))
          (fun k hk => Subgroup.mem_sup_right (hCinv a k hk))
      exact fun k hk => hle hk
    have hbase : ∀ k : K, π k ∈ coordSubgroup S i → k ∈ N ⊔ C := by
      intro k hk
      obtain ⟨n, hn, hnk⟩ := hi hk
      have hc : n⁻¹ * k ∈ C := (hker _).mp (by rw [map_mul, map_inv, hnk, inv_mul_cancel])
      have := Subgroup.mul_mem_sup hn hc
      rwa [mul_inv_cancel_left] at this
    have hall : ∀ j, ∀ k : K, π k ∈ coordSubgroup S j → k ∈ N ⊔ C := by
      intro j k hk
      obtain ⟨a, ha⟩ := htrans i j
      have h1 : π (a⁻¹ • k) ∈ coordSubgroup S i := by
        refine (ha (a⁻¹ • k)).mpr ?_
        rw [smul_inv_smul]
        exact hk
      have := hN'inv a _ (hbase _ h1)
      rwa [smul_inv_smul] at this
    rw [eq_top_iff]
    intro k _
    have hk : π k ∈ (N ⊔ C).map π := by
      refine Subgroup.pi_mem_of_mulSingle_mem _ fun j => ?_
      obtain ⟨k', hk'⟩ := hπ (Pi.mulSingle j (π k j))
      exact ⟨k', hall j k' ⟨π k j, hk'.symm⟩, hk'⟩
    obtain ⟨n, hn, hnk⟩ := hk
    have hc : n⁻¹ * k ∈ C := (hker _).mp (by rw [map_mul, map_inv, hnk, inv_mul_cancel])
    have := (N ⊔ C).mul_mem hn (Subgroup.mem_sup_right hc)
    rwa [mul_inv_cancel_left] at this

theorem natCard_pi_univ_subgroup {I : Type} [Fintype I] {S : I → Type} [∀ i, Group (S i)]
    (H : ∀ i, Subgroup (S i)) : Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i) := by
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypePiEquivPi)
  simp [Subgroup.mem_pi]

theorem exists_isElementaryAbelian_two_pi {I : Type} [Fintype I] [DecidableEq I] (S : I → Type)
    [∀ i, Group (S i)] [∀ i, Finite (S i)] (heven : ∀ i, Even (Nat.card (S i))) {n : ℕ}
    (hn : n ≤ Fintype.card I) :
    ∃ B : Subgroup (∀ i, S i), IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ i, ∃ t : S i, orderOf t = 2 := fun i =>
    exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp (heven i))
  choose t ht using hinv
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I)) (n := n)
    (by rw [Finset.card_univ]; exact hn)
  let H : ∀ i, Subgroup (S i) := fun i => if i ∈ T then zpowers (t i) else ⊥
  have hH : ∀ i, H i ≤ zpowers (t i) := fun i => by
    by_cases hi : i ∈ T <;> simp [H, hi]
  have ht2 : ∀ i, t i ^ 2 = 1 := fun i => by rw [← ht i]; exact pow_orderOf_eq_one (t i)
  have hmem : ∀ x : Subgroup.pi Set.univ H, ∀ i, ∃ k : ℤ, t i ^ k = (x : ∀ i, S i) i := fun x i =>
    mem_zpowers_iff.mp (hH i ((Subgroup.mem_pi _).mp x.2 i (Set.mem_univ i)))
  refine ⟨Subgroup.pi Set.univ H, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · refine Subtype.ext (funext fun i => ?_)
      obtain ⟨k, hk⟩ := hmem x i
      obtain ⟨l, hl⟩ := hmem y i
      change (x : ∀ i, S i) i * (y : ∀ i, S i) i = (y : ∀ i, S i) i * (x : ∀ i, S i) i
      rw [← hk, ← hl]
      exact (Commute.zpow_zpow_self (t i) k l).eq
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      refine Subtype.ext (funext fun i => ?_)
      obtain ⟨k, hk⟩ := hmem x i
      change (x : ∀ i, S i) i ^ 2 = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2 i, one_zpow]
  · rw [natCard_pi_univ_subgroup]
    have hcard : ∀ i, Nat.card (H i) = if i ∈ T then 2 else 1 := fun i => by
      by_cases hi : i ∈ T <;> simp [H, hi, Nat.card_zpowers, ht i]
    rw [Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_ite_mem Finset.univ T (fun _ => 2),
      Finset.univ_inter, Finset.prod_const, hT]

theorem le_center_of_invariant_dichotomy {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {A : Type*} [Group A] [MulDistribMulAction A K] (m : ℕ)
    (he : CFSG.Assembly.evenRank K ≤ m) (C : Subgroup K) [C.Normal]
    (hCsolv : Group.IsSolvable C) (hCodd : Odd (Nat.card C))
    (hdich : ∀ N : Subgroup K, N.Normal → (∀ a : A, ∀ k ∈ N, a • k ∈ N) → N ≤ C ∨ N ⊔ C = ⊤)
    (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 2 ^ (m + 2))
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (R : Subgroup K) [R.Normal]
    (hRinv : ∀ a : A, ∀ k ∈ R, a • k ∈ R) (hR : IsPGroup r R) : R ≤ center K := by
  classical
  rcases subsingleton_or_nontrivial R with hRs | hRnt
  · intro x hx
    have hx1 : x = 1 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : R) 1)
    rw [hx1]
    exact one_mem _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hr2 hR
  set D' : Subgroup K := D.map R.subtype with hD'
  have hD'n : D'.Normal := inferInstance
  have hDinv : ∀ a : A, ∀ x ∈ D', a • x ∈ D' := by
    intro a x hx
    let e : R ≃* R :=
      { toFun := fun r => ⟨a • (r : K), hRinv a r r.2⟩
        invFun := fun r => ⟨a⁻¹ • (r : K), hRinv a⁻¹ r r.2⟩
        left_inv := fun r => Subtype.ext (inv_smul_smul a (r : K))
        right_inv := fun r => Subtype.ext (smul_inv_smul a (r : K))
        map_mul' := fun r s => Subtype.ext (smul_mul' a (r : K) (s : K)) }
    obtain ⟨d, hd, rfl⟩ := hx
    have hcomap := Subgroup.characteristic_iff_comap_eq.mp hDchar e
    have hdc : d ∈ D.comap e.toMonoidHom := by
      rw [hcomap]
      exact hd
    exact ⟨e d, hdc, rfl⟩
  set K₀ := centralizer (D' : Set K) with hK₀
  have hK₀n : K₀.Normal := inferInstance
  have hK₀inv : ∀ a : A, ∀ k ∈ K₀, a • k ∈ K₀ := by
    intro a k hk
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := mem_centralizer_iff.mp hk (a⁻¹ • d) (hDinv a⁻¹ d hd)
    have h2 := congrArg (fun x => a • x) h1
    simp only [smul_mul', smul_inv_smul] at h2
    exact h2
  rcases hdich K₀ hK₀n hK₀inv with hK₀C | hsup
  ·
    exfalso
    obtain ⟨V, hV, hVcard, hVC⟩ := exists_elementary_two_lift C hCodd U hU hUcard
    have := hV
    have hD'p : IsPGroup r D' := hR.to_le (Subgroup.map_subtype_le D)
    have hD'exp : Monoid.exponent D' ∣ r := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hxx, ← map_pow, hDexp x' hx', map_one, Subgroup.coe_one]
    have hD'cl : (⊤ : Subgroup D').lowerCentralSeries 2 = ⊥ := by
      apply lowerCentralSeries_two_eq_bot
      intro x y z
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp y.2
      obtain ⟨z', hz', hzz⟩ := Subgroup.mem_map.mp z.2
      have hc : ⁅x', y'⁆ ∈ centralizer (D : Set R) :=
        (hDcomm (Subgroup.commutator_mem_commutator hx' (mem_top y'))).2
      have hcz : z' * ⁅x', y'⁆ = ⁅x', y'⁆ * z' := mem_centralizer_iff.mp hc z' hz'
      have h1 := congrArg R.subtype hcz
      simp only [map_mul, commutatorElement_def, map_inv] at h1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
      rw [← hxx, ← hyy, ← hzz]
      exact h1.symm
    let act : MulDistribMulAction V D' :=
      MulDistribMulAction.compHom D' ((MulAut.conjNormal (H := D')).comp V.subtype)
    have hsmul : ∀ (v : V) (d : D'), ((v • d : D') : K) = (v : K) * d * (v : K)⁻¹ :=
      fun v d => MulAut.conjNormal_apply (v : K) d
    have hfaith : FaithfulSMul V D' := by
      refine ⟨fun {v₁ v₂} h => ?_⟩
      have hfix : ∀ d : D', (v₂⁻¹ * v₁) • d = d := by
        intro d
        rw [mul_smul, h d, ← mul_smul, inv_mul_cancel, one_smul]
      have hK₀mem : ((v₂⁻¹ * v₁ : V) : K) ∈ K₀ := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg Subtype.val (hfix ⟨x, hx⟩)
        rw [hsmul] at h1
        calc x * ((v₂⁻¹ * v₁ : V) : K) =
            ((v₂⁻¹ * v₁ : V) : K) * x * ((v₂⁻¹ * v₁ : V) : K)⁻¹ * ((v₂⁻¹ * v₁ : V) : K) := by
              rw [h1]
          _ = ((v₂⁻¹ * v₁ : V) : K) * x := by group
      have h1 := Subgroup.disjoint_def.mp hVC (v₂⁻¹ * v₁).2 (hK₀C hK₀mem)
      have h2 : v₂⁻¹ * v₁ = 1 := Subtype.ext h1
      exact (inv_mul_eq_one.mp h2).symm
    have hm : ∀ a : V, a ≠ 1 →
        pRank r (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D') ≤ m := by
      intro a ha
      set F := CFSG.fixedPointSubgroup (Subgroup.zpowers a) D' with hF
      let ι : F →* K := D'.subtype.comp F.subtype
      have hι : Function.Injective ι := D'.subtype_injective.comp F.subtype_injective
      set N := normalizer ((zpowers (a : K) : Subgroup K) : Set K) with hN
      have hιN : (⊤ : Subgroup F).map ι ≤ N := by
        rintro _ ⟨f, -, rfl⟩
        have hf : a • (f : D') = f := f.2 ⟨a, mem_zpowers a⟩
        have hf' : (a : K) * ι f * (a : K)⁻¹ = ι f := by
          have h1 := congrArg Subtype.val hf
          rw [hsmul] at h1
          exact h1
        have hc : ι f ∈ centralizer ((zpowers (a : K) : Subgroup K) : Set K) := by
          rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_iff]
          rintro _ rfl
          calc (a : K) * ι f = (a : K) * ι f * (a : K)⁻¹ * a := by group
            _ = ι f * a := by rw [hf']
        exact centralizer_le_normalizer _ hc
      have ha1 : (a : K) ≠ 1 := fun h => ha (Subtype.ext h)
      have hloc : CFSG.Open.IsTwoLocal N := by
        refine ⟨zpowers (a : K), ?_, ?_, rfl⟩
        · intro h
          apply ha1
          have hmem : (a : K) ∈ zpowers (a : K) := mem_zpowers _
          rwa [h, Subgroup.mem_bot] at hmem
        · have ha2 : (a : K) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a : K) a.2
          exact IsPGroup.of_card (n := 1)
            (by rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1, pow_one])
      calc pRank r F = CFSG.Open.pRank r (⊤ : Subgroup F) :=
            CFSG.SectionRank.pRank_eq_open_pRank_top r F
        _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup F).map ι) :=
            CFSG.SectionRank.pRank_le_map hr.out.one_lt ι hι ⊤
        _ ≤ CFSG.Open.pRank r N := CFSG.SectionRank.pRank_mono hr.out.one_lt hιN
        _ ≤ CFSG.Open.evenRank K :=
            CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr.out hr2 N hloc
        _ = CFSG.Assembly.evenRank K := rfl
        _ ≤ m := he
    have h := class_two_involution_fixed_rank_bound (A := V) (hr.out.odd_of_ne_two hr2) hD'p
      hD'exp hD'cl (m + 2) m hVcard hm
    omega
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' K₀).comp C.subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective K₀ q
      have hk : k ∈ K₀ ⊔ C := by
        rw [hsup]
        exact mem_top k
      obtain ⟨k₀, hk₀, c, hc, rfl⟩ := mem_sup_of_normal_left.mp hk
      refine ⟨⟨c, hc⟩, ?_⟩
      change QuotientGroup.mk' K₀ c = QuotientGroup.mk' K₀ (k₀ * c)
      have hk₀1 : QuotientGroup.mk' K₀ k₀ = 1 := (QuotientGroup.eq_one_iff k₀).mpr hk₀
      rw [map_mul, hk₀1, one_mul]
    have hKK₀ : ∀ k : K, k ∈ K₀ := by
      have : Group.IsSolvable (K ⧸ K₀) := Group.isSolvable_of_surjective hsurj
      have hsolv : Group.IsSolvable (QuotientGroup.mk' K₀).range := by
        rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective K₀)]
        infer_instance
      intro k
      exact (QuotientGroup.eq_one_iff k).mp (eq_one_of_isSolvable_range _ hsolv k)
    let g : K →* MulAut R := MulAut.conjNormal
    have hrange : g.range ≤ fixingSubgroup (MulAut R) (D : Set R) := by
      rintro _ ⟨k, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      change k * (d : K) * k⁻¹ = d
      have h1 := mem_centralizer_iff.mp (hKK₀ k) (d : K) ⟨d, hd, rfl⟩
      rw [← h1, mul_inv_cancel_right]
    have hgp : IsPGroup r g.range := hDfix.to_le hrange
    have hgs : Group.IsSolvable g.range := by
      have := hgp.isNilpotent
      infer_instance
    intro x hx
    rw [mem_center_iff]
    intro k
    have h1 := congrArg (fun φ : MulAut R => ((φ ⟨x, hx⟩ : R) : K))
      (eq_one_of_isSolvable_range g hgs k)
    simp only [g, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [h1]

end TransitiveSemisimple

open TransitiveSemisimple

theorem transitive_semisimple_odd_kernel_centralization :
    TransitiveSemisimpleOddKernelCentralization := by
  intro m K _ _ hK he A _ _ C _ hCinv hCnil hCodd I _ _ hI S _ _ _ hnonab heven φ htrans
  classical
  have := hK
  have hCsolv : Group.IsSolvable C := by
    have := hCnil
    infer_instance
  have hdich : ∀ N : Subgroup K, N.Normal → (∀ a : A, ∀ k ∈ N, a • k ∈ N) →
      N ≤ C ∨ N ⊔ C = ⊤ := fun N hNn hN =>
    invariant_normal_le_or_sup_eq_top C hCinv S hnonab φ htrans N hN
  obtain ⟨B, hB, hBcard⟩ := exists_isElementaryAbelian_two_pi S heven hI
  obtain ⟨hU, hUcard⟩ := isElementaryAbelian_map_mulEquiv φ.symm hB
  have hC : C = (⨆ p ∈ (Nat.card C).primeFactors,
      ((default : Sylow p C) : Subgroup C)).map C.subtype := by
    rw [Sylow.iSup_sylow_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hC, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun p hp => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hCodd)
      (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have : (pCore p K).Normal := pCore_normal
  have hRinv : ∀ a : A, ∀ k ∈ pCore p K, a • k ∈ pCore p K := by
    intro a k hk
    have h := Subgroup.characteristic_iff_comap_eq.mp (pCore_characteristic (p := p) (G := K))
      (MulDistribMulAction.toMulEquiv K a)
    have hk' : k ∈ (pCore p K).comap (MulDistribMulAction.toMulEquiv K a).toMonoidHom := by
      rw [h]
      exact hk
    exact hk'
  exact (Sylow.map_le_pCore inferInstance hCnil p default).trans
    (le_center_of_invariant_dichotomy m he C hCsolv hCodd hdich _ hU (hUcard.trans hBcard) hp2
      (pCore p K) hRinv pCore_isPGroup)

end CFSG.RankThree.PartOne
