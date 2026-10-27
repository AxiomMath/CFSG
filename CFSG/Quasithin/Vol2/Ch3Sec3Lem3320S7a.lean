module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S6c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem mem_perfectCore_of_pow_three {I : Subgroup G}
    (hsimp : IsSimpleGroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))
    (hne : perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) ≠ ⊥) {x : G} (hx : x ∈ I)
    (hx3 : x ^ 3 = 1) : x ∈ perfectCore I := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  have hP : (perfectCore (⊤ : Subgroup ↥I)).map I.subtype = perfectCore I := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQ : (perfectCore (⊤ : Subgroup ↥I)).map π =
      perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hnorm : ∀ {Q : Type} [Group Q], (perfectCore (⊤ : Subgroup Q)).Normal := by
    intro Q _
    refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
    exact (Subgroup.normalizer_eq_top (H := (⊤ : Subgroup Q))).ge.trans
      (normalizer_le_normalizer_perfectCore ⊤)
  have hn' : (perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))).Normal := hnorm
  have htop : perfectCore (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  set N := perfectCore (⊤ : Subgroup ↥I) with hN
  have hNn : N.Normal := hnorm
  have hmem : π ⟨x, hx⟩ ∈ N.map π := by
    rw [hQ, htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkx⟩ := hmem
  have hn : k⁻¹ * ⟨x, hx⟩ ∈ CFSG.pPrimeCore 3 ↥I := QuotientGroup.eq.mp hkx
  set ψ := QuotientGroup.mk' N with hψ
  have hk1 : ψ k = 1 := by
    rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have h1 : ψ ⟨x, hx⟩ = ψ (k⁻¹ * ⟨x, hx⟩) := by
    rw [map_mul, map_inv, hk1, inv_one, one_mul]
  have h3 : orderOf (ψ ⟨x, hx⟩) ∣ 3 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥I) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hcop : Nat.Coprime 3 (orderOf (ψ ⟨x, hx⟩)) := by
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right ((orderOf_map_dvd ψ _).trans
      (Subgroup.orderOf_dvd_natCard _ hn)) CFSG.pPrimeCore_coprime_card
  have h4 : orderOf (ψ ⟨x, hx⟩) = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm h3
  have hxN : (⟨x, hx⟩ : ↥I) ∈ N := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h4)
  rw [← hP]
  exact ⟨_, hxN, rfl⟩

def negOneSL2 (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨-1, by simp [Matrix.det_neg]⟩

theorem negOneSL2_mem_center (F : Type) [Field F] :
    negOneSL2 F ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Subgroup.mem_center_iff]
  intro A
  apply Subtype.ext
  show (A : Matrix (Fin 2) (Fin 2) F) * (-1) = (-1) * (A : Matrix (Fin 2) (Fin 2) F)
  rw [mul_neg_one, neg_one_mul]

theorem negOneSL2_sq (F : Type) [Field F] : negOneSL2 F * negOneSL2 F = 1 := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) F) * (-1) = 1
  rw [neg_one_mul, neg_neg]

theorem negOneSL2_ne_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : negOneSL2 F ≠ 1 := by
  intro h
  have h1 := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [negOneSL2] at h1
  apply h2
  linear_combination -h1

theorem false_of_sl2 {Q : Type} [Group Q] [Finite Q] {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (hS : ∀ S : Subgroup Q, S.Normal → Group.IsSolvable ↥S → ∀ s ∈ S, s * s = 1 → s = 1)
    (ψ : Q →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) (hψ : Function.Surjective ψ)
    (hk : Group.IsSolvable ↥ψ.ker) : False := by
  set S := (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))).comap ψ with hSdef
  have hSn : S.Normal := Subgroup.Normal.comap inferInstance ψ
  have hSs : Group.IsSolvable ↥S := by
    let f : ↥ψ.ker →* ↥S := Subgroup.inclusion (fun x hx => by
      rw [hSdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact Subgroup.one_mem _)
    let g : ↥S →* ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))) :=
      (ψ.comp S.subtype).codRestrict _ fun s => s.2
    refine Group.isSolvable_of_ker_le_range f g fun s hs => ?_
    have h1 : ψ s = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hs)
    exact ⟨⟨s, h1⟩, rfl⟩
  obtain ⟨u, hu⟩ := hψ (negOneSL2 (ZMod r))
  have huS : u ∈ S := by
    rw [hSdef, Subgroup.mem_comap, hu]
    exact negOneSL2_mem_center _
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hr ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hord : orderOf (ψ u) = 2 := by
    rw [hu]
    exact orderOf_eq_prime (by rw [sq]; exact negOneSL2_sq _) (negOneSL2_ne_one h2)
  have h2u : 2 ∣ orderOf u := hord ▸ orderOf_map_dvd ψ u
  obtain ⟨m, hm⟩ := h2u
  have hm0 : 0 < m := by
    have := orderOf_pos u
    omega
  have hv : u ^ m * u ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hm, pow_orderOf_eq_one]
  have hv1 : u ^ m ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one hm0 h
    omega
  exact hv1 (hS S hSn hSs _ (S.pow_mem huS m) hv)

theorem eq_bot_of_isSolvable {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) (N : Subgroup Q) [N.Normal] (hN : Group.IsSolvable ↥N) :
    N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    rw [h] at hN
    have hQ : Group.IsSolvable Q :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).toMonoidHom) Subgroup.topEquiv.surjective
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hQ) a b)

theorem commutatorElement_mul_central {Q : Type*} [Group Q] {a b z w : Q}
    (hz : ∀ g : Q, g * z = z * g) (hw : ∀ g : Q, g * w = w * g) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : a * z * (b * w) = a * b * w * z := by
    rw [mul_assoc a z, ← hz (b * w)]
    group
  have h2 : w * a⁻¹ = a⁻¹ * w := (hw a⁻¹).symm
  simp only [commutatorElement_def]
  rw [h1]
  calc a * b * w * z * (a * z)⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]; group

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem X_le_perfectCore {g : G}
    (hsimp : IsSimpleGroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))
    (hne : perfectCore (⊤ : Subgroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g))) ≠ ⊥) :
    X ≤ perfectCore (gZero X T g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxX, hx3, -, hgen⟩ := H.exists_x
  have hXI : X ≤ gZero X T g := le_sup_left.trans le_sup_left
  have hxK : x ∈ perfectCore (gZero X T g) :=
    mem_perfectCore_of_pow_three hsimp hne (hXI hxX) hx3
  refine le_of_le_sup_pgroup H.hXX (S := X ⊓ pCoreOf 2 (X ⊔ T)) ?_ ?_ ?_
  · intro s hs
    exact normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer (hXI hs.1))
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)).to_le inf_le_right
  · intro x' hx'
    obtain ⟨j, hj⟩ := hgen x' hx'
    have e : x' = (x' * (x ^ j)⁻¹) * x ^ j := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup ⟨X.mul_mem hx' (X.inv_mem (X.pow_mem hxX j)), hj⟩
      (Subgroup.pow_mem _ hxK j)

theorem eq_of_X_le (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) (hXK : X ≤ K) :
    conjClosure X D = K := by
  have hYK : conjClosure X D ≤ K := conjClosure_le fun d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hBK (Subgroup.mem_sup_right hd)) x).mp (hXK hx)
  have hsub : IsSubnormal (perfectCore (conjClosure X D)) (X ⊔ T ⊔ D) :=
    A3.subnormal_of_normal ((perfectCore_le _).trans Y_le_B)
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (H.hBY.trans (normalizer_le_normalizer_perfectCore _)))
  have hne : perfectCore (conjClosure X D) ≠ ⊥ := by
    intro h
    have hs : Group.IsSolvable ↥(conjClosure X D) :=
      (isSolvable_iff_perfectCore_eq_bot _).mpr h
    have hsK : Group.IsSolvable ↥(star (X ⊔ T ⊔ D) B₀ K) := by
      rw [H.star_eq_star_Y hB hK hBK hKB₀]
      exact isSolvable_star Y_le_B hs
    obtain ⟨hsimp, a, b, hab⟩ := H.isSimpleGroup_star hB (H.le_commutator_sup hA hB) hK hBK hKB₀
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsK) a b)
  have hle : perfectCore (conjClosure X D) ≤ K := (perfectCore_le _).trans hYK
  have heq : perfectCore (conjClosure X D) = K := by
    by_contra hne'
    exact hK.2.2.2 _ (lt_of_le_of_ne hle hne') hne (perfectCore_perfect _) hsub
  exact le_antisymm hYK (heq ▸ perfectCore_le _)

theorem mem_pPrimeCore_of_mem (hB : IsB₀ X T D B₀) {I : Subgroup G} (hIB : I ≤ X ⊔ T ⊔ D)
    (hsimp : IsSimpleGroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))
    (hnab : ∃ a b : ↥I ⧸ CFSG.pPrimeCore 3 ↥I, a * b ≠ b * a) {x : G} (hx : x ∈ I)
    (hxB : x ∈ B₀) : (⟨x, hx⟩ : ↥I) ∈ CFSG.pPrimeCore 3 ↥I := by
  have hn : (B₀.subgroupOf I).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hIB.trans hB.nor)
  have hs : Group.IsSolvable ↥(B₀.subgroupOf I) := by
    have := H.isSolvable_B₀ hB
    let ι : ↥(B₀.subgroupOf I) →* ↥B₀ :=
      (I.subtype.comp (B₀.subgroupOf I).subtype).codRestrict B₀ fun y => y.2
    refine Group.isSolvable_of_isSolvable_injective (f := ι) fun a b hab => ?_
    have h1 : ((ι a : ↥B₀) : G) = ((ι b : ↥B₀) : G) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hn' : ((B₀.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective _)
  have h1 := eq_bot_of_isSolvable hnab _
    (Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)).subgroupMap_surjective (B₀.subgroupOf I)))
  have h2 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) ⟨x, hx⟩ = 1 := by
    have h3 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))
      (show (⟨x, hx⟩ : ↥I) ∈ B₀.subgroupOf I from hxB)
    rw [h1, Subgroup.mem_bot] at h3
    exact h3
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2

theorem mem_pCoreOf_of_pow (hB : IsB₀ X T D B₀) {n : G} (hn : n ∈ B₀) {k : ℕ}
    (hk : n ^ 2 ^ k = 1) : n ∈ pCoreOf 2 (X ⊔ T ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal B₀ (X ⊔ T ⊔ D) :=
    A3.subnormal_of_normal hB.le (Subgroup.normal_subgroupOf_of_le_normalizer hB.nor)
  have hsyl := A312.isSylowTwoOf_inf_of_subnormal hsub H.isSylowTwoOf_B
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  rw [← hT₀]
  have hTB : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((T ⊓ B₀ : Subgroup G) : Set G) := by
    rw [hT₀]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hnorm : ((T ⊓ B₀).subgroupOf B₀).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hB.le.trans hTB)
  have hmo : Odd ((T ⊓ B₀).subgroupOf B₀).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hsyl.2.2)
  have h1 : n ^ ((T ⊓ B₀).subgroupOf B₀).index ∈ T ⊓ B₀ := by
    have := Subgroup.pow_index_mem ((T ⊓ B₀).subgroupOf B₀) (⟨n, hn⟩ : ↥B₀)
    exact this
  exact Lem3328.mem_of_pow_odd hmo h1 (by rw [hk]; exact Subgroup.one_mem _)

theorem rho_eq_one_of_isSolvable (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀)
    {ρ : (↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) →* (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))}
    (hρ : ∀ h : ↥(X ⊔ T ⊔ D), ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) h) =
      QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) h)
    (S : Subgroup ↥(modO2Image (X ⊔ T ⊔ D) (conjClosure X D))) [S.Normal]
    (hS : Group.IsSolvable ↥S) {s : ↥(modO2Image (X ⊔ T ⊔ D) (conjClosure X D))} (hs : s ∈ S) :
    ρ (s : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) = 1 := by
  have hρY := map_modO2Image (L := conjClosure X D) hρ
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB (H.le_commutator_sup hA hB) hY H.hBY hYB₀
  set S' := (S.map (modO2Image (X ⊔ T ⊔ D) (conjClosure X D)).subtype).map ρ with hS'
  have hS'le : S' ≤ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
    rw [← hρY]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  set N' := S'.subgroupOf (star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn y => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨s', ⟨s₀, hs₀, rfl⟩, hsn⟩ := hn
    have hy : (y : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ∈
        (modO2Image (X ⊔ T ⊔ D) (conjClosure X D)).map ρ := by
      rw [hρY]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨(modO2Image (X ⊔ T ⊔ D) (conjClosure X D)).subtype (⟨z, hz⟩ * s₀ * ⟨z, hz⟩⁻¹),
      Subgroup.mem_map_of_mem _ (‹S.Normal›.conj_mem s₀ hs₀ ⟨z, hz⟩), ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at hsn ⊢
    rw [hsn]
    show ρ z * _ * (ρ z)⁻¹ = _
    rw [hzy]
  have hN's : Group.IsSolvable ↥N' := by
    have h1 : Group.IsSolvable ↥(S.map (modO2Image (X ⊔ T ⊔ D) (conjClosure X D)).subtype) :=
      Group.isSolvable_of_surjective
        ((modO2Image (X ⊔ T ⊔ D) (conjClosure X D)).subtype.subgroupMap_surjective S)
    have h2 : Group.IsSolvable ↥S' := Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hS'le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hS'le).injective
  have hbot := eq_bot_of_isSolvable hnab N' hN's
  have hmem : ρ (s : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) ∈ S' :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs)
  have hmem' : (⟨_, hS'le hmem⟩ : ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) ∈ N' := hmem
  rw [hbot, Subgroup.mem_bot] at hmem'
  exact congrArg Subtype.val hmem'

omit [Finite G] H in
theorem exists_of_rho_eq_one [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    {ρ : (↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) →* (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))}
    (hρ : ∀ h : ↥(X ⊔ T ⊔ D), ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) h) =
      QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) h)
    {q : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)}
    (hq : q ∈ modO2Image (X ⊔ T ⊔ D) (conjClosure X D)) (h1 : ρ q = 1) :
    ∃ (n : G) (hn : n ∈ X ⊔ T ⊔ D), n ∈ conjClosure X D ∧ n ∈ B₀ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) ⟨n, hn⟩ = q := by
  obtain ⟨y, hy, rfl⟩ := hq
  refine ⟨y, y.2, Subgroup.mem_subgroupOf.mp hy, ?_, rfl⟩
  rw [hρ] at h1
  exact (mk_eq_one_iff y.2).mp h1

theorem mk_eq_one_of_sq (hB : IsB₀ X T D B₀) {n : G} (hn : n ∈ X ⊔ T ⊔ D) (hnB : n ∈ B₀)
    (h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) ⟨n, hn⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) ⟨n, hn⟩ = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) ⟨n, hn⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Lem3328.mem_pCore_iff] at h2
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T ⊔ D)) ⟨_, h2⟩
  have hk' : n ^ 2 ^ (k + 1) = 1 := by
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one] at this
    rw [pow_succ', pow_mul, sq]
    exact this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Lem3328.mem_pCore_iff]
  exact H.mem_pCoreOf_of_pow hB hnB hk'

theorem inf_B₀_le_pCoreOf (h36 : Vol2Native.A36ForSQTKCat) (hA : AS_A_1_31)
    (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D)) (hYB₀ : ¬ conjClosure X D ≤ B₀)
    {I : Subgroup G} (hIY : perfectCore I ≤ conjClosure X D)
    (hstar : star (X ⊔ T ⊔ D) B₀ (perfectCore I) = star (X ⊔ T ⊔ D) B₀ (conjClosure X D))
    (hO3 : ∀ x (hx : x ∈ I), x ∈ B₀ → (⟨x, hx⟩ : ↥I) ∈ CFSG.pPrimeCore 3 ↥I) :
    conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D) := by
  have := H.h.simple
  have hKc : LocalSQTK G := (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1
  have hconc := Vol2Native.lemma_1_2_1_four hKc h36 H.hB.2 hY
  have hYB : conjClosure X D ≤ X ⊔ T ⊔ D := Y_le_B
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  obtain ⟨ρ, hρ⟩ := exists_rho (H := X ⊔ T ⊔ D) (N := B₀) ((le_of_eq hT₀.symm).trans inf_le_right)
  have hρY := map_modO2Image (L := conjClosure X D) hρ
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB (H.le_commutator_sup hA hB) hY H.hBY hYB₀
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) with hπ₂
  set Yb := modO2Image (X ⊔ T ⊔ D) (conjClosure X D) with hYb
  have hS : ∀ S : Subgroup ↥Yb, S.Normal → Group.IsSolvable ↥S → ∀ s ∈ S, s * s = 1 → s = 1 := by
    intro S hSn hSs s hs hs2
    have h1 := H.rho_eq_one_of_isSolvable hA hB hY hYB₀ hρ S hSs hs
    obtain ⟨n, hn, -, hnB, hns⟩ := exists_of_rho_eq_one hρ s.2 h1
    have h2 : π₂ ⟨n, hn⟩ * π₂ ⟨n, hn⟩ = 1 := by
      rw [hns]
      exact congrArg Subtype.val hs2
    have h3 := H.mk_eq_one_of_sq hB hn hnB h2
    exact Subtype.ext (hns ▸ h3)
  set Nb := ((conjClosure X D ⊓ B₀).subgroupOf (X ⊔ T ⊔ D)).map π₂ with hNb
  have hNbY : Nb ≤ Yb := Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  set N' := Nb.subgroupOf Yb with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn y => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨m, hm, hmn⟩ := hn
    obtain ⟨y', hy', hyy⟩ := y.2
    have hm' : (m : G) ∈ conjClosure X D ⊓ B₀ := hm
    have hy'' : (y' : G) ∈ conjClosure X D := hy'
    refine ⟨y' * m * y'⁻¹, ?_, ?_⟩
    · show ((y' * m * y'⁻¹ : ↥(X ⊔ T ⊔ D)) : G) ∈ conjClosure X D ⊓ B₀
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine ⟨?_, ?_⟩
      · exact (conjClosure X D).mul_mem ((conjClosure X D).mul_mem hy'' hm'.1)
          ((conjClosure X D).inv_mem hy'')
      · exact (Subgroup.mem_normalizer_iff.mp (hB.nor y'.2) m).mp hm'.2
    · have hyy' : π₂ y' = (y : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)) := hyy
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hmn]
      rw [hyy']
  have hN's : Group.IsSolvable ↥N' := by
    have hs₀ := H.isSolvable_B₀ hB
    have h1 : Group.IsSolvable ↥((conjClosure X D ⊓ B₀).subgroupOf (X ⊔ T ⊔ D)) := by
      let ι : ↥((conjClosure X D ⊓ B₀).subgroupOf (X ⊔ T ⊔ D)) →* ↥B₀ :=
        ((X ⊔ T ⊔ D).subtype.comp (Subgroup.subtype _)).codRestrict B₀ fun y => y.2.2
      refine Group.isSolvable_of_isSolvable_injective (f := ι) fun a b hab => ?_
      have h1 : ((ι a : ↥B₀) : G) = ((ι b : ↥B₀) : G) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have h2 : Group.IsSolvable ↥Nb := Group.isSolvable_of_surjective (π₂.subgroupMap_surjective _)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNbY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNbY).injective
  suffices hN : Nb = ⊥ by
    intro n hn
    have h1 : π₂ ⟨n, hYB hn.1⟩ ∈ Nb := Subgroup.mem_map_of_mem _ hn
    rw [hN, Subgroup.mem_bot, hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Lem3328.mem_pCore_iff] at h1
    exact h1
  have hNb : N' = ⊥ → Nb = ⊥ := by
    intro h1
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hNbY hq⟩ : ↥Yb) ∈ N' := hq
    rw [h1, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  rcases hconc with ⟨-, hsY, -⟩ | ⟨⟨hqY, -⟩, hZ3, -⟩ | h3 | h4
  ·
    have hnabY : ∃ a b : ↥Yb, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      obtain ⟨u, v, huv⟩ := hnab
      have hu : (u : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ∈ Yb.map ρ := by
        rw [hρY]
        exact u.2
      have hv : (v : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ∈ Yb.map ρ := by
        rw [hρY]
        exact v.2
      obtain ⟨a, ha, hau⟩ := hu
      obtain ⟨b, hb, hbv⟩ := hv
      apply huv
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hau, ← hbv, ← map_mul, ← map_mul]
      exact congrArg (fun w : ↥Yb => ρ (w : ↥(X ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(X ⊔ T ⊔ D)))
        (hc ⟨a, ha⟩ ⟨b, hb⟩)
    exact hNb (@eq_bot_of_isSolvable _ _ hsY hnabY N' hN'n hN's)
  ·
    exfalso
    have hZ : N' ≤ Subgroup.center ↥Yb := by
      have hn' : (N'.map (QuotientGroup.mk' (Subgroup.center ↥Yb))).Normal :=
        hN'n.map _ (QuotientGroup.mk'_surjective _)
      have := hqY.2.1
      have h1 := eq_bot_of_isSolvable hqY.2.2 _
        (Group.isSolvable_of_surjective ((QuotientGroup.mk' _).subgroupMap_surjective N'))
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
      exact h1
    have hdec : ∀ q ∈ Yb, ∃ (k : G) (hk : k ∈ X ⊔ T ⊔ D), k ∈ perfectCore I ∧
        ∃ m ∈ Nb, π₂ ⟨k, hk⟩ * m = q := by
      intro q hq
      obtain ⟨y, hy, rfl⟩ := hq
      have hy' : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) y ∈
          star (X ⊔ T ⊔ D) B₀ (perfectCore I) := by
        rw [hstar]
        exact Subgroup.mem_map_of_mem _ hy
      obtain ⟨k, hkB, hk, hky⟩ := mem_star_iff.mp hy'
      refine ⟨k, hkB, hk, π₂ (⟨k, hkB⟩⁻¹ * y), Subgroup.mem_map_of_mem _ ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        refine ⟨(conjClosure X D).mul_mem ((conjClosure X D).inv_mem (hIY hk))
          (Subgroup.mem_subgroupOf.mp hy), ?_⟩
        exact (QuotientGroup.eq (s := B₀.subgroupOf (X ⊔ T ⊔ D))).mp hky
      · rw [← map_mul, mul_inv_cancel_left]
    set Kb := ((perfectCore I).subgroupOf (X ⊔ T ⊔ D)).map π₂ with hKb
    have hKbY : ∀ (k : G) (hk : k ∈ X ⊔ T ⊔ D), k ∈ perfectCore I → π₂ ⟨k, hk⟩ ∈ Yb :=
      fun k hk hkI => Subgroup.mem_map_of_mem _ (show (⟨k, hk⟩ : ↥(X ⊔ T ⊔ D)) ∈
        (conjClosure X D).subgroupOf (X ⊔ T ⊔ D) from hIY hkI)
    have hc : commutator ↥Yb ≤ Kb.subgroupOf Yb := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨k₁, hk₁B, hk₁, m₁, hm₁, he₁⟩ := hdec a a.2
      obtain ⟨k₂, hk₂B, hk₂, m₂, hm₂, he₂⟩ := hdec b b.2
      have ha : a = ⟨_, hKbY k₁ hk₁B hk₁⟩ * ⟨m₁, hNbY hm₁⟩ := Subtype.ext he₁.symm
      have hb : b = ⟨_, hKbY k₂ hk₂B hk₂⟩ * ⟨m₂, hNbY hm₂⟩ := Subtype.ext he₂.symm
      have hz₁ : ∀ g : ↥Yb, g * ⟨m₁, hNbY hm₁⟩ = ⟨m₁, hNbY hm₁⟩ * g := fun g =>
        (Subgroup.mem_center_iff.mp (hZ (show (⟨m₁, hNbY hm₁⟩ : ↥Yb) ∈ N' from hm₁)) g)
      have hz₂ : ∀ g : ↥Yb, g * ⟨m₂, hNbY hm₂⟩ = ⟨m₂, hNbY hm₂⟩ * g := fun g =>
        (Subgroup.mem_center_iff.mp (hZ (show (⟨m₂, hNbY hm₂⟩ : ↥Yb) ∈ N' from hm₂)) g)
      rw [ha, hb, commutatorElement_mul_central hz₁ hz₂, Subgroup.mem_subgroupOf,
        commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 : π₂ ⟨k₁, hk₁B⟩ ∈ Kb := Subgroup.mem_map_of_mem _ hk₁
      have h2 : π₂ ⟨k₂, hk₂B⟩ ∈ Kb := Subgroup.mem_map_of_mem _ hk₂
      exact Kb.mul_mem (Kb.mul_mem (Kb.mul_mem h1 h2) (Kb.inv_mem h1)) (Kb.inv_mem h2)
    have hle : Yb ≤ Kb := by
      intro q hq
      have hq' : (⟨q, hq⟩ : ↥Yb) ∈ commutator ↥Yb := by
        rw [hqY.1.commutator_eq_top]
        exact Subgroup.mem_top _
      exact hc hq'
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Yb)) 3
      (by rw [hZ3])
    obtain ⟨k, hk, hkz⟩ := hle (z : ↥Yb).2
    have hzS := H.rho_eq_one_of_isSolvable hA hB hY hYB₀ hρ (Subgroup.center ↥Yb)
      inferInstance z.2
    obtain ⟨n, hn, -, hnB, hnz⟩ := exists_of_rho_eq_one hρ (z : ↥Yb).2 hzS
    have hkB₀ : (k : G) ∈ B₀ := by
      have h1 : π₂ k = π₂ ⟨n, hn⟩ := by rw [hkz, hnz]
      have h2 := QuotientGroup.eq.mp h1
      rw [Lem3328.mem_pCore_iff] at h2
      have h3 : (k : G)⁻¹ * n ∈ B₀ := ((le_of_eq hT₀.symm).trans inf_le_right) h2
      have := B₀.mul_mem hnB (B₀.inv_mem h3)
      simpa using this
    have hkI : (k : G) ∈ I := perfectCore_le I (Subgroup.mem_subgroupOf.mp hk)
    have hcop : Nat.Coprime 3 (orderOf (⟨k, hkI⟩ : ↥I)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ (hO3 _ hkI hkB₀))
        CFSG.pPrimeCore_coprime_card
    have h3 : 3 ∣ orderOf (⟨k, hkI⟩ : ↥I) := by
      have h4 : orderOf (π₂ k) = 3 := by
        rw [hkz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
      have h5 := orderOf_map_dvd π₂ k
      rw [h4, ← Subgroup.orderOf_coe] at h5
      rw [Subgroup.orderOf_mk]
      exact h5
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  ·
    exfalso
    obtain ⟨r, hr, hr3, -, ⟨eF⟩, e, ψ, hψ, hker, -⟩ := h3
    have : Fact r.Prime := ⟨hr⟩
    refine false_of_sl2 (by omega) hS ψ hψ ?_
    rw [hker]
    exact Group.isSolvable_of_isSolvable_injective (f := eF.toMonoidHom) eF.injective
  ·
    exfalso
    obtain ⟨-, hnil, ⟨e⟩, -⟩ := h4
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine false_of_sl2 (r := 5) (by norm_num) hS
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥Yb)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_
    have hk : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥Yb))).ker =
        CFSG.fittingSubgroup ↥Yb := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hk]
    infer_instance

theorem pCoreOf_YT_eq (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) :
    pCoreOf 2 (conjClosure X D ⊔ T) = (conjClosure X D ⊔ T) ⊓ B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYB : conjClosure X D ≤ X ⊔ T ⊔ D := Y_le_B
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hYTB : conjClosure X D ⊔ T ≤ X ⊔ T ⊔ D := sup_le hYB hTB
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB (H.le_commutator_sup hA hB) hY H.hBY hYB₀
  rw [htop] at hsimp hnab
  have hsB : IsSimpleGroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) :=
    (Subgroup.topEquiv :
      ↥(⊤ : Subgroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))) ≃* _).symm.isSimpleGroup
  have hnabB : ∃ a b : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_) ?_
  ·
    have hPB : pCoreOf 2 (conjClosure X D ⊔ T) ≤ X ⊔ T ⊔ D :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hYTB
    rw [← star_eq_bot_iff hPB]
    have hn : (star (X ⊔ T ⊔ D) B₀ (pCoreOf 2 (conjClosure X D ⊔ T))).Normal := by
      refine ⟨fun n hn q => ?_⟩
      have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
        rw [htop]
        exact Subgroup.mem_top q
      obtain ⟨y, hyB, hy, rfl⟩ := mem_star_iff.mp hq
      have hyN := mk_mem_normalizer_star (B := X ⊔ T ⊔ D) (N := B₀) hyB
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure X D ⊔ T)
          (Subgroup.mem_sup_left hy))
      exact (Subgroup.mem_normalizer_iff.mp hyN n).mp hn
    have hp : IsPGroup 2 ↥(star (X ⊔ T ⊔ D) B₀ (pCoreOf 2 (conjClosure X D ⊔ T))) := by
      have h1 : IsPGroup 2 ↥((pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T ⊔ D)) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
          (Subgroup.subgroupOfEquivOfLe hPB).symm
      exact h1.map _
    have := hp.isNilpotent
    exact eq_bot_of_isSolvable hnabB _ inferInstance
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · intro u hu
      exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hu) (hB.nor (hYTB hu))
    · rintro ⟨u, huYT, huB⟩
      have hTY : T ≤ Subgroup.normalizer (conjClosure X D : Set G) := hTB.trans H.hBY
      obtain ⟨y, hy, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTY).mp huYT
      obtain ⟨a, ha⟩ := H.h.sylow.1 ⟨t, ht⟩
      have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      obtain ⟨y', hy', e⟩ := S3320.pow_mul_mem hy (hTY ht) (2 ^ a)
      rw [ha', mul_one] at e
      have h1 : (y * t) ^ 2 ^ a ∈ conjClosure X D ⊓ B₀ := ⟨e ▸ hy', B₀.pow_mem huB _⟩
      obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T ⊔ D)) ⟨_, hle h1⟩
      refine ⟨a + b, Subtype.ext ?_⟩
      have := congrArg Subtype.val hb
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this

theorem isPSL_YT (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D)) (hYB₀ : ¬ conjClosure X D ≤ B₀)
    (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D)) {p : ℕ}
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) :
    IsPSL 2 p 1 (↥(conjClosure X D ⊔ T) ⧸ CFSG.pCore 2 ↥(conjClosure X D ⊔ T)) := by
  have hYTB : conjClosure X D ⊔ T ≤ X ⊔ T ⊔ D := sup_le Y_le_B (le_sup_right.trans le_sup_left)
  have hP := H.pCoreOf_YT_eq hA hB hY hYB₀ htop hle
  let φ : ↥(conjClosure X D ⊔ T) →* ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D) :=
    (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))).comp (Subgroup.inclusion hYTB)
  have hφs : Function.Surjective φ := by
    intro q
    have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
      rw [htop]
      exact Subgroup.mem_top q
    obtain ⟨y, hyB, hy, rfl⟩ := mem_star_iff.mp hq
    exact ⟨⟨y, Subgroup.mem_sup_left hy⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 ↥(conjClosure X D ⊔ T) := by
    ext u
    rw [MonoidHom.mem_ker, Lem3328.mem_pCore_iff, hP]
    show QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨u, hYTB u.2⟩ = 1 ↔ _
    rw [mk_eq_one_iff]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  let e : (↥(conjClosure X D ⊔ T) ⧸ CFSG.pCore 2 ↥(conjClosure X D ⊔ T)) ≃*
      ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).trans
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm))
  exact isL2_of_mulEquiv e hL

theorem exists_data (hF : F6.TheoremF618Cat) (hIF : F6.InspF618Rest)
    (hIW : InspWalter3320) (hA21 : AsA21SQTKSection) (h36 : Vol2Native.A36ForSQTKCat)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hA : AS_A_1_31) (h312 : Vol2Native.A312ForSQTKCat)
    (hI : InspA312F618)
    (hA6 : ∀ (Q : Type) [Group Q] [Finite Q], (IsAlt 6 Q ∨ F6.IsL2 3 2 Q) → AutOddNormCent Q)
    (hA7 : ∀ (Q : Type) [Group Q] [Finite Q], IsAlt 7 Q → AutOddNormCent Q)
    (hM12 : ∀ (Q : Type) [Group Q] [Finite Q], F6.IsM12 Q → AutOddNormCent Q)
    (hL2Sq : ∀ p : ℕ, p.Prime → 3 < p → ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 2 p 2 Q →
      AutOddNormCent Q)
    (hL2p : FactAutOddL2pPlus) (hL3 : FactAutL3Eps) (hL2o : FactAutL2pOuter)
    (hL2s : FactL2pSylowFour) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    ∃ g ∈ D, g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) ∧
      (F6.IsF618CaseFour (plus (gZero X T g) (X ⊔ T))
          (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
        F6.IsF618CaseFour (plus (gZero X T g) (conjByElt g (X ⊔ T)))
          (plus (gZero X T g) (X ⊔ T))) ∧
      IsSimpleGroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)) ∧
      (∃ a b : ↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g), a * b ≠ b * a) ∧
      X ≤ perfectCore (gZero X T g) ∧ perfectCore (gZero X T g) ≤ conjClosure X D ∧
      star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = ⊤ ∧
      conjClosure X D ∈ cComp (X ⊔ T ⊔ D) ∧ ¬ conjClosure X D ≤ B₀ ∧
      star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤ ∧
      conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D) ∧
      pCoreOf 2 (conjClosure X D ⊔ T) = (conjClosure X D ⊔ T) ⊓ B₀ ∧
      ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
        F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) := by
  obtain ⟨g, hg, hgR, hcase, K, hK, hK₀K, hBK, hKB₀, htop, p, hp, hp24, hL⟩ :=
    H.exists_caseFour hF hIF hIW hA21 h37 h38 h39 hA h312 hI hA6 hA7 hM12 hL2Sq hL2p hL3 hL2o
      hL2s hB
  have hgX := H.not_mem_normalizer_X hg hgR
  have hsimp : IsSimpleGroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)) := by
    rcases hcase with h | h
    · obtain ⟨⟨p', -, -, hL'⟩, -⟩ := h
      exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p' 1 hL').2
    · obtain ⟨⟨p', -, -, hL'⟩, -⟩ := h
      exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p' 1 hL').2
  have hrest : F6.IsF618CaseRestCat (plus (gZero X T g) (X ⊔ T))
        (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
      F6.IsF618CaseRestCat (plus (gZero X T g) (conjByElt g (X ⊔ T)))
        (plus (gZero X T g) (X ⊔ T)) := by
    rcases hcase with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl h))
  have hq : CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup
      (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))) := by
    rcases hrest with h | h
    · exact (hIF _ _ _).1 h
    · exact (hIF _ _ _).1 h
  have hne : perfectCore (⊤ : Subgroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g))) ≠
      ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    have h1 : ∀ x : ↥(perfectCore (⊤ : Subgroup
        (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))), x = 1 := fun x =>
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp h _ x.2)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [h1 a', h1 b']
  have hnab : ∃ a b : ↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a', b', fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h
  have hXK₀ := H.X_le_perfectCore hsimp hne
  have hYK := H.eq_of_X_le hA hB hK hBK hKB₀ (hXK₀.trans hK₀K)
  have hK₀ := perfectCore_mem_cComp hq (H.isGoldschmidtTripleIn hg hgX).isSolvable_pPrimeCore
  have hstar := H.star_perfectCore_eq hIF h312 hI hA hB hg hgR hrest hK₀ hK hK₀K hBK hKB₀
  subst hYK
  have hO3 : ∀ x (hx : x ∈ gZero X T g), x ∈ B₀ →
      (⟨x, hx⟩ : ↥(gZero X T g)) ∈ CFSG.pPrimeCore 3 ↥(gZero X T g) := fun x hx hxB =>
    H.mem_pPrimeCore_of_mem hB (gZero_le hg) hsimp hnab hx hxB
  have hle := H.inf_B₀_le_pCoreOf h36 hA hB hK hKB₀ hK₀K hstar hO3
  exact ⟨g, hg, hgR, hcase, hsimp, hnab, hXK₀, hK₀K, hstar.trans htop, hK, hKB₀, htop, hle,
    H.pCoreOf_YT_eq hA hB hK hKB₀ htop hle, p, hp, hp24, hL⟩

end Hyp3320

end S3320

end CFSG.Quasithin.H13
