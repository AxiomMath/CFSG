module

public import CFSG.Walter.W67.CentralExt
public import CFSG.Quasithin.Recognition.St84.EdgeStabB
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open scoped commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem not_two_dvd_relIndex_of_isSylowTwoOf {P Y X : Subgroup G}
    (hP : IsSylowTwoOf P X) (hPY : P ≤ Y) (hYX : Y ≤ X) : ¬ 2 ∣ Y.relIndex X := by
  intro h
  apply hP.2.2
  change 2 ∣ P.relIndex X
  rw [← Subgroup.relIndex_mul_relIndex P Y X hPY hYX]
  exact dvd_mul_of_dvd_right h _

theorem inf_commutator_sup_le_of_central {M R Z U P : Subgroup G} [Finite ↥M]
    (hRM : R ≤ M) (hRn : M ≤ Subgroup.normalizer (R : Set G))
    (hZM : Z ≤ M) (hZ2 : IsPGroup 2 Z) (hZc : ∀ z ∈ Z, ∀ m ∈ M, ⁅z, m⁆ ∈ R)
    (hUM : U ≤ M) (hUab : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ R)
    (hP : IsSylowTwoOf P M) (hPUZ : P ≤ U ⊔ Z) :
    Z ⊓ (⁅M, M⁆ ⊔ R) ≤ R := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥M := R.subgroupOf M
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hRn
  letI : N.Normal := hNn
  let E := ↥M ⧸ N
  let π : ↥M →* E := QuotientGroup.mk' N
  haveI : Finite E := inferInstance
  let PM : Subgroup ↥M := P.subgroupOf M
  have hPM2 : IsPGroup 2 PM := hP.2.1.comap_subtype
  let Pbar : Subgroup E := PM.map π
  have hPbar2 : IsPGroup 2 Pbar := hPM2.map π
  have hPbar_index_dvd : Pbar.index ∣ PM.index := by
    rw [show Pbar = PM.map π from rfl, Subgroup.index_map]
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N), Subgroup.index_top, mul_one]
    exact Subgroup.index_dvd_of_le le_sup_left
  have hPbar_odd : ¬ 2 ∣ Pbar.index := by
    intro h
    apply hP.2.2
    change 2 ∣ PM.index
    exact h.trans hPbar_index_dvd
  let ZM : Subgroup ↥M := Z.subgroupOf M
  let Zbar : Subgroup E := ZM.map π
  have hZbar2 : IsPGroup 2 Zbar := hZ2.comap_subtype.map π
  have hZbar_center : Zbar ≤ Subgroup.center E := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨zm, hzm, rfl⟩ := Subgroup.mem_map.mp hz
    have hzZ : (zm : G) ∈ Z := Subgroup.mem_subgroupOf.mp hzm
    obtain ⟨xm, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hcomm : ⁅(zm : G), (xm : G)⁆ ∈ R := hZc (zm : G) hzZ (xm : G) xm.2
    have hcommM : ⁅zm, xm⁆ ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      change M.subtype ⁅zm, xm⁆ ∈ R
      rw [map_commutatorElement]
      exact hcomm
    have hcommE : ⁅π zm, π xm⁆ = 1 := by
      rw [← map_commutatorElement]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hcommM
    exact (commutatorElement_eq_one_iff_commute.mp hcommE).eq.symm
  let UM : Subgroup ↥M := U.subgroupOf M
  let Ubar : Subgroup E := UM.map π
  have hUbar_comm : ∀ a ∈ Ubar, ∀ b ∈ Ubar, a * b = b * a := by
    intro a ha b hb
    obtain ⟨am, ham, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨bm, hbm, rfl⟩ := Subgroup.mem_map.mp hb
    have haU : (am : G) ∈ U := Subgroup.mem_subgroupOf.mp ham
    have hbU : (bm : G) ∈ U := Subgroup.mem_subgroupOf.mp hbm
    have hcomm : ⁅(am : G), (bm : G)⁆ ∈ R := hUab (am : G) haU (bm : G) hbU
    have hcommM : ⁅am, bm⁆ ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      change M.subtype ⁅am, bm⁆ ∈ R
      rw [map_commutatorElement]
      exact hcomm
    have hcommE : ⁅π am, π bm⁆ = 1 := by
      rw [← map_commutatorElement]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hcommM
    exact (commutatorElement_eq_one_iff_commute.mp hcommE).eq
  have hPbar_le : Pbar ≤ Ubar ⊔ Zbar := by
    have hsub : PM ≤ (U ⊔ Z).subgroupOf M := fun q hq =>
      Subgroup.mem_subgroupOf.mpr (hPUZ (Subgroup.mem_subgroupOf.mp hq))
    have hle : PM.map π ≤ ((U ⊔ Z).subgroupOf M).map π := Subgroup.map_mono hsub
    rwa [Subgroup.subgroupOf_sup hUM hZM, Subgroup.map_sup] at hle
  haveI : Zbar.Normal := Subgroup.normal_of_le_center hZbar_center
  have hPbar_comm : IsMulCommutative Pbar := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    change (a : E) * (b : E) = (b : E) * (a : E)
    obtain ⟨u, huU, z, hzZ, huz⟩ := Subgroup.mem_sup_of_normal_right.mp (hPbar_le a.2)
    obtain ⟨u', hu'U, z', hz'Z, hu'z'⟩ := Subgroup.mem_sup_of_normal_right.mp (hPbar_le b.2)
    rw [← huz, ← hu'z']
    have hzu : z * u' = u' * z :=
      (Subgroup.mem_center_iff.mp (hZbar_center hzZ) u').symm
    have hz'u : z' * u = u * z' :=
      (Subgroup.mem_center_iff.mp (hZbar_center hz'Z) u).symm
    have huu : u * u' = u' * u := hUbar_comm u huU u' hu'U
    have hzz : z * z' = z' * z :=
      Subgroup.mem_center_iff.mp (hZbar_center hz'Z) z
    calc
      (u * z) * (u' * z') = u * (z * u') * z' := by group
      _ = u * (u' * z) * z' := by rw [hzu]
      _ = (u * u') * (z * z') := by group
      _ = (u' * u) * (z' * z) := by rw [huu, hzz]
      _ = u' * (u * z') * z := by group
      _ = u' * (z' * u) * z := by rw [hz'u]
      _ = (u' * z') * (u * z) := by group
  let S : Sylow 2 E := hPbar2.toSylow hPbar_odd
  have hScomm : IsMulCommutative (S : Subgroup E) := by
    change IsMulCommutative Pbar
    exact hPbar_comm
  have hW := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup S hScomm hZbar_center hZbar2
  intro x hx
  obtain ⟨hxZ, hxD⟩ := Subgroup.mem_inf.mp hx
  have hxM : x ∈ M := hZM hxZ
  let xm : ↥M := ⟨x, hxM⟩
  have hxZbar : π xm ∈ Zbar :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxZ)
  have hxsub : xm ∈ ((⁅M, M⁆ ⊔ R).subgroupOf M) :=
    Subgroup.mem_subgroupOf.mpr hxD
  rw [Subgroup.subgroupOf_sup (Subgroup.commutator_le_self M) hRM] at hxsub
  obtain ⟨cm, hcm_sub, rm, hrm_sub, hxm_eq⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hxsub
  have hcm_comm : cm ∈ commutator ↥M := by
    have hc_map : (cm : G) ∈ (commutator ↥M).map M.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact Subgroup.mem_subgroupOf.mp hcm_sub
    obtain ⟨cm', hcm', hcm'c⟩ := Subgroup.mem_map.mp hc_map
    have hcm'_eq : cm' = cm := Subtype.ext hcm'c
    rwa [hcm'_eq] at hcm'
  have hcmE : π cm ∈ commutator E := by
    have hmap : (commutator ↥M).map π = commutator E := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)]
    rw [← hmap]
    exact Subgroup.mem_map_of_mem π hcm_comm
  have hrm1 : π rm = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hrm_sub
  have hxpi : π xm = π cm := by
    rw [← hxm_eq, map_mul, hrm1, mul_one]
  have hxE : π xm ∈ commutator E := by
    rw [hxpi]
    exact hcmE
  have hx_inf : π xm ∈ Zbar ⊓ commutator E := Subgroup.mem_inf.mpr ⟨hxZbar, hxE⟩
  rw [hW] at hx_inf
  have hx_one : π xm = 1 := Subgroup.mem_bot.mp hx_inf
  have hxN : xm ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx_one
    exact hx_one
  exact Subgroup.mem_subgroupOf.mp hxN


theorem exists_commutator_mul_of_fixedPointFree {U R : Subgroup G} [Finite ↥U] {k : G}
    (hRU : R ≤ U) (hRn : U ≤ Subgroup.normalizer (R : Set G))
    (hkU : k ∈ Subgroup.normalizer (U : Set G)) (hkR : k ∈ Subgroup.normalizer (R : Set G))
    (hfree : ∀ r ∈ U, ⁅k, r⁆ ∈ R → r ∈ R) :
    ∀ u ∈ U, ∃ v ∈ U, ∃ w ∈ R, u = ⁅k, v⁆ * w := by
  classical
  let N : Subgroup ↥U := R.subgroupOf U
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRU).mpr hRn
  letI : N.Normal := hNn
  let f : ↥U → ↥U := fun v =>
    ⟨⁅k, (v : G)⁆, by
      have hv : (v : G) ∈ U := v.2
      have hconj : k * (v : G) * k⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hkU (v : G)).mp hv
      have hcomm : ⁅k, (v : G)⁆ = (k * (v : G) * k⁻¹) * (v : G)⁻¹ := by
        rw [commutatorElement_def]
      rw [hcomm]
      exact U.mul_mem hconj (U.inv_mem hv)⟩
  have hf_rel : ∀ a b : ↥U, (QuotientGroup.leftRel N) a b →
      (QuotientGroup.leftRel N) (f a) (f b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have habR : ((a⁻¹ * b : ↥U) : G) ∈ R := Subgroup.mem_subgroupOf.mp hab
    apply Subgroup.mem_subgroupOf.mpr
    have hid : (((f a)⁻¹ * f b : ↥U) : G) =
        (a : G) * ⁅k, ((a⁻¹ * b : ↥U) : G)⁆ * (a : G)⁻¹ := by
      change (⁅k, (a : G)⁆)⁻¹ * ⁅k, (b : G)⁆ =
        (a : G) * ⁅k, ((a⁻¹ * b : ↥U) : G)⁆ * (a : G)⁻¹
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [commutatorElement_def]
      group
    rw [hid]
    have hrR : ⁅k, ((a⁻¹ * b : ↥U) : G)⁆ ∈ R := by
      have hkcomm : ⁅Subgroup.zpowers k, R⁆ ≤ R :=
        (Subgroup.le_normalizer_iff_commutator_le_right (H := Subgroup.zpowers k) (K := R)).mp
          (Subgroup.zpowers_le.mpr hkR)
      exact hkcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers k) habR)
    exact (Subgroup.mem_normalizer_iff.mp (hRn a.2) _).mp hrR
  let φ : ↥U ⧸ N → ↥U ⧸ N := Quotient.map' f hf_rel
  have hφ_inj : Function.Injective φ := by
    intro qa qb hq
    induction qa using Quotient.inductionOn' with
    | _ a =>
    induction qb using Quotient.inductionOn' with
    | _ b =>
    have hrel : (QuotientGroup.leftRel N) (f a) (f b) := Quotient.exact hq
    rw [QuotientGroup.leftRel_apply] at hrel
    have hrelR : (((f a)⁻¹ * f b : ↥U) : G) ∈ R := Subgroup.mem_subgroupOf.mp hrel
    have hid : (((f a)⁻¹ * f b : ↥U) : G) =
        (a : G) * ⁅k, ((a⁻¹ * b : ↥U) : G)⁆ * (a : G)⁻¹ := by
      change (⁅k, (a : G)⁆)⁻¹ * ⁅k, (b : G)⁆ =
        (a : G) * ⁅k, ((a⁻¹ * b : ↥U) : G)⁆ * (a : G)⁻¹
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [commutatorElement_def]
      group
    rw [hid] at hrelR
    have hrR : ⁅k, ((a⁻¹ * b : ↥U) : G)⁆ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hRn a.2) _).mpr hrelR
    have hrR' : ((a⁻¹ * b : ↥U) : G) ∈ R := hfree _ (a⁻¹ * b).2 hrR
    exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hrR')
  have hφ_surj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ_inj
  intro u hu
  let uu : ↥U := ⟨u, hu⟩
  obtain ⟨v, hv⟩ := hφ_surj (uu : ↥U ⧸ N)
  induction v using Quotient.inductionOn' with
  | _ v =>
    have hv' : (f v : ↥U ⧸ N) = (uu : ↥U ⧸ N) := hv
    have hdiv : ((f v) / uu : ↥U) ∈ N := QuotientGroup.eq_iff_div_mem.mp hv'
    have hdivR : (((f v) / uu : ↥U) : G) ∈ R := Subgroup.mem_subgroupOf.mp hdiv
    let w : ↥U := (f v)⁻¹ * ((f v) / uu)⁻¹ * f v
    have hwR : (w : G) ∈ R := by
      have hdinvR : (((f v) / uu : ↥U)⁻¹ : G) ∈ R := R.inv_mem hdivR
      have hmem : (((f v)⁻¹ : ↥U) : G) ∈ U := U.inv_mem (f v).2
      have hconj := (Subgroup.mem_normalizer_iff.mp (hRn hmem)
        (((f v) / uu : ↥U)⁻¹ : G)).mp hdinvR
      simpa [w] using hconj
    have huu_eq : uu = f v * w := by
      simp only [w]
      rw [div_eq_mul_inv]
      group
    refine ⟨(v : G), v.2, (w : G), hwR, ?_⟩
    have hcoe := congrArg (fun x : ↥U => (x : G)) huu_eq
    simpa [f] using hcoe


theorem psl2_one_commutator_eq_one {f : ℕ} (hf : f = 1)
    {y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hy : y ∈ commutator _) (h2 : ∃ a : ℕ, y ^ 2 ^ a = 1) : y = 1 := by
  subst hf
  let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)
  change y ∈ commutator PSL at hy
  obtain ⟨e⟩ := CFSG.Quasithin.isL2Quot_one_iff_perm3.mp
    (show IsL2Quot 1 PSL from ⟨MulEquiv.refl _⟩)
  have hy' : e y ∈ commutator (Equiv.Perm (Fin 3)) := by
    have hmem : e y ∈ (commutator PSL).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hy
    rwa [show (commutator PSL).map e.toMonoidHom = commutator (Equiv.Perm (Fin 3)) by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]] at hmem
  have hle : commutator (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) :=
    alternatingGroup.commutator_perm_le
  have hcardA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hord3 : orderOf (e y) ∣ 3 := by
    have hmemA : e y ∈ alternatingGroup (Fin 3) := hle hy'
    have h := orderOf_dvd_natCard (x := (⟨e y, hmemA⟩ : alternatingGroup (Fin 3)))
    rw [← Subgroup.orderOf_coe] at h
    rwa [hcardA] at h
  obtain ⟨a, ha⟩ := h2
  have hord2 : orderOf (e y) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ha, map_one]
  have hcop : Nat.Coprime 3 (2 ^ a) :=
    Nat.Coprime.pow_right a (by norm_num)
  have hone : orderOf (e y) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord3 hord2
  have hey : e y = 1 := orderOf_eq_one_iff.mp hone
  exact e.injective (by rw [hey, map_one])


theorem Hyp30.exists_odd_transitive (h : Hyp30 Γ G) {v : V}
    (hn : nOf Γ v = 1 ∨ nOf Γ v = 2) :
    ∃ x ∈ MulAction.stabilizer G v, Odd (orderOf x) ∧
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → ∃ k : ℤ, x ^ k • a = b := by
  classical
  let L : Subgroup G := oTwoPrime (MulAction.stabilizer G v)
  have hN : IsLocL2 Γ G v (nOf Γ v) L := h.isLocL2_oTwoPrime v
  have hLle : L ≤ MulAction.stabilizer G v := oTwoPrime_le _
  let p : ℕ := 2 ^ nOf Γ v + 1
  have hp3or5 : p = 3 ∨ p = 5 := by
    rcases hn with hn | hn <;> simp [p, hn]
  have hp : p.Prime := by
    rcases hp3or5 with h3 | h5
    · rw [h3]; decide
    · rw [h5]; decide
  have hpodd : Odd p := by
    rcases hp3or5 with h3 | h5
    · rw [h3]; decide
    · rw [h5]; decide
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := h.exists_adj v
  have horbit : MulAction.orbit ↥L a = Γ.neighborSet v := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro w ⟨g, rfl⟩
      have hgL : (g : G) ∈ L := g.2
      have hgv : (g : G) • v = v := MulAction.mem_stabilizer_iff.mp (hLle hgL)
      rw [SimpleGraph.mem_neighborSet]
      have := (h.adj_smul (g : G) v a).2 ha
      simpa [hgv, Subgroup.smul_def] using this
    · intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      obtain ⟨g, hgL, hga⟩ := hN.trans a w ha hw
      exact ⟨⟨g, hgL⟩, hga⟩
  have hstab : (MulAction.stabilizer G a).relIndex L = (MulAction.orbit ↥L a).ncard := by
    rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  have hrel : (MulAction.stabilizer G a).relIndex L = p := by
    rw [hstab, horbit]
    simpa [p, Nat.card_coe_set_eq] using (h.valency v).2
  have hdvd : p ∣ Nat.card L := by
    rw [← hrel, ← Subgroup.relIndex_mul_card (H := MulAction.stabilizer G a) (K := L)]
    exact dvd_mul_right _ _
  haveI : Finite ↥L := finite_of_le_stabilizer h hLle
  obtain ⟨xL, hxordL⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let x : G := (xL : G)
  have hxL' : x ∈ L := xL.2
  have hxord : orderOf x = p := by
    change orderOf (xL : G) = p
    rw [Subgroup.orderOf_coe, hxordL]
  have hx_moves : ∃ a, Γ.Adj v a ∧ x • a ≠ a := by
    by_contra hc
    push Not at hc
    have hxQ : x ∈ pCoreOf 2 (MulAction.stabilizer G v) := by
      rw [← inf_kernelOnNeighbors_eq_pCoreOf h hN]
      exact Subgroup.mem_inf.mpr ⟨hxL', mem_kernelOnNeighbors.mpr ⟨hLle hxL', hc⟩⟩
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      (pCoreOf_isPGroup' (MulAction.stabilizer G v)).to_le (Subgroup.zpowers_le.mpr hxQ)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hx2) ⟨x, Subgroup.mem_zpowers x⟩
    rw [← Subgroup.orderOf_coe] at hk
    have hk' : p = 2 ^ k := by rw [← hxord, hk]
    have h2dvd : 2 ∣ p := by
      cases k with
      | zero => rw [pow_zero] at hk'; omega
      | succ k => rw [pow_succ] at hk'; exact ⟨2 ^ k, by rw [hk']; ring⟩
    exact hpodd.not_two_dvd_nat h2dvd
  obtain ⟨a₀, ha₀, hxa₀⟩ := hx_moves
  let O : Set V := MulAction.orbit ↥(Subgroup.zpowers x) a₀
  have hOsub : O ⊆ Γ.neighborSet v := by
    rintro w ⟨g, rfl⟩
    have hgL : (g : G) ∈ L := Subgroup.zpowers_le.mpr hxL' g.2
    have hgv : (g : G) • v = v := MulAction.mem_stabilizer_iff.mp (hLle hgL)
    rw [SimpleGraph.mem_neighborSet]
    have := (h.adj_smul (g : G) v a₀).2 ha₀
    simpa [hgv, Subgroup.smul_def] using this
  have hstabO : (MulAction.stabilizer G a₀).relIndex (Subgroup.zpowers x) = O.ncard := by
    rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  have hdvdO : O.ncard ∣ p := by
    rw [← hstabO, ← hxord, ← Nat.card_zpowers, ← Subgroup.relIndex_mul_card
      (H := MulAction.stabilizer G a₀) (K := Subgroup.zpowers x)]
    exact dvd_mul_right _ _
  have hOge2 : 2 ≤ O.ncard := by
    have haO : a₀ ∈ O := ⟨1, by simp⟩
    have hxaO : x • a₀ ∈ O := ⟨⟨x, Subgroup.mem_zpowers x⟩, rfl⟩
    have hne : a₀ ≠ x • a₀ := Ne.symm hxa₀
    have hpair : ({a₀, x • a₀} : Set V).ncard = 2 := Set.ncard_pair hne
    rw [← hpair]
    exact Set.ncard_le_ncard (s := ({a₀, x • a₀} : Set V)) (t := O) (by
      intro y hy
      rcases hy with rfl | rfl
      · exact haO
      · exact hxaO) ((h.finite_neighborSet v).subset hOsub)
  have hOncard : O.ncard = p := by
    rcases hp.eq_one_or_self_of_dvd O.ncard hdvdO with h1 | hp'
    · omega
    · exact hp'
  have hneighbor_ncard : (Γ.neighborSet v).ncard = p := by
    simpa [p, Nat.card_coe_set_eq] using (h.valency v).2
  have hOeq : O = Γ.neighborSet v := by
    refine Set.eq_of_subset_of_ncard_le hOsub ?_ (h.finite_neighborSet v)
    rw [hneighbor_ncard, hOncard]
  refine ⟨x, hLle hxL', ?_, ?_⟩
  · rw [hxord]
    exact hpodd
  · intro a' b ha' hb'
    have ha'O : a' ∈ O := by rw [hOeq]; exact ha'
    have hbO : b ∈ O := by rw [hOeq]; exact hb'
    obtain ⟨g, hga⟩ := ha'O
    obtain ⟨g', hgb⟩ := hbO
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g'.2
    have hga' : (g : G) • a₀ = a' := by simpa [Subgroup.smul_def] using hga
    have hgb' : (g' : G) • a₀ = b := by simpa [Subgroup.smul_def] using hgb
    have ha'_eq : a' = x ^ j • a₀ := by
      rw [← hga', ← hj]
    have hb_eq : b = x ^ k • a₀ := by
      rw [← hgb', ← hk]
    refine ⟨k - j, ?_⟩
    calc
      x ^ (k - j) • a' = x ^ (k - j) • (x ^ j • a₀) := by rw [ha'_eq]
      _ = (x ^ (k - j) * x ^ j) • a₀ := by rw [mul_smul]
      _ = x ^ ((k - j) + j) • a₀ := by rw [zpow_add]
      _ = x ^ k • a₀ := by rw [sub_add_cancel]
      _ = b := hb_eq.symm


end CFSG.Quasithin.St84
