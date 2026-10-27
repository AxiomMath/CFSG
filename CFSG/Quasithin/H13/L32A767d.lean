module

public import CFSG.Quasithin.H13.L32A768c
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem center_sl24_eq_bot : Subgroup.center SL(2, F4) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hA', f4_sq_eq_one r hr]
  simp [Matrix.one_apply]

theorem card_mulAut_sl24 : Nat.card (MulAut SL(2, F4)) = 120 := by
  have := isSimpleGroup_sl24
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty card_sl24
  have e5 : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (SteinbergCB.conjPerm 5) ⟨SteinbergCB.conjPerm_injective (by norm_num),
      SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e5.toEquiv, Nat.card_perm,
    Nat.card_fin]
  rfl

omit [Finite G] in
@[expose] def conjOn (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) : ↥X →* ↥X where
  toFun x := ⟨g * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem coe_conjOn (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥X) :
    ((conjOn X g x : ↥X) : G) = g * x * (g : G)⁻¹ := rfl

section Ind

variable {K : Subgroup G} {Q : Type} [Group Q] (π : ↥K →* Q) (hπs : Function.Surjective π)
  (hπk : π.ker = (pCoreOf 2 K).subgroupOf K)

omit [Finite G] in
include hπk in
theorem ker_le_ker_conjOn (g : ↥(Subgroup.normalizer (K : Set G))) :
    π.ker ≤ (π.comp (conjOn K g)).ker := by
  intro x hx
  rw [hπk, Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf,
    coe_conjOn]
  exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K g.2) x).mp hx

@[expose] noncomputable def indAut (g : ↥(Subgroup.normalizer (K : Set G))) : Q →* Q :=
  π.liftOfSurjective hπs ⟨π.comp (conjOn K g), ker_le_ker_conjOn π hπk g⟩

omit [Finite G] in
theorem indAut_apply (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    indAut π hπs hπk g (π k) = π (conjOn K g k) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k

omit [Finite G] in
theorem indAut_mul (g h : ↥(Subgroup.normalizer (K : Set G))) (A : Q) :
    indAut π hπs hπk (g * h) A = indAut π hπs hπk g (indAut π hπs hπk h A) := by
  obtain ⟨k, rfl⟩ := hπs A
  rw [indAut_apply, indAut_apply, indAut_apply]
  congr 1
  exact Subtype.ext (by simp only [coe_conjOn, Subgroup.coe_mul]; group)

omit [Finite G] in
theorem indAut_one (A : Q) : indAut π hπs hπk 1 A = A := by
  obtain ⟨k, rfl⟩ := hπs A
  rw [indAut_apply]
  congr 1
  exact Subtype.ext (by simp [coe_conjOn])

@[expose] noncomputable def autHom : ↥(Subgroup.normalizer (K : Set G)) →* MulAut Q where
  toFun g :=
    { toFun := indAut π hπs hπk g
      invFun := indAut π hπs hπk g⁻¹
      left_inv := fun A => by rw [← indAut_mul, inv_mul_cancel, indAut_one]
      right_inv := fun A => by rw [← indAut_mul, mul_inv_cancel, indAut_one]
      map_mul' := map_mul _ }
  map_one' := MulEquiv.ext fun A => indAut_one π hπs hπk A
  map_mul' g h := MulEquiv.ext fun A => indAut_mul π hπs hπk g h A

omit [Finite G] in
theorem autHom_apply (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    autHom π hπs hπk g (π k) = π (conjOn K g k) :=
  indAut_apply π hπs hπk g k

omit [Finite G] in
theorem autHom_eq_one_iff (g : ↥(Subgroup.normalizer (K : Set G))) :
    autHom π hπs hπk g = 1 ↔ ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  constructor
  · intro h1 k hk
    have e := autHom_apply π hπs hπk g ⟨k, hk⟩
    rw [h1, MulAut.one_apply] at e
    have hker : conjOn K g ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← e, mul_inv_cancel]
    rw [hπk, Subgroup.mem_subgroupOf] at hker
    simpa [coe_conjOn] using hker
  · intro h1
    refine MulEquiv.ext fun A => ?_
    obtain ⟨k, rfl⟩ := hπs A
    rw [autHom_apply, MulAut.one_apply]
    have hker : conjOn K g k * k⁻¹ ∈ π.ker := by
      rw [hπk, Subgroup.mem_subgroupOf]
      simpa [coe_conjOn] using h1 k k.2
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
    exact hker

end Ind

abbrev mK (T V : Subgroup G) : Subgroup G := Subgroup.normalizer (kz T V : Set G)

@[expose] def dK (T V : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ mK T V ∧ ∀ k ∈ kz T V, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 (kz T V)}
  mul_mem' := by
    rintro a b ⟨ha, hak⟩ ⟨hb, hbk⟩
    refine ⟨mul_mem ha hb, fun k hk => ?_⟩
    have hbk' : b * k * b⁻¹ ∈ kz T V := (Subgroup.mem_normalizer_iff.mp hb k).mp hk
    rw [show a * b * k * (a * b)⁻¹ * k⁻¹ =
      (a * (b * k * b⁻¹) * a⁻¹ * (b * k * b⁻¹)⁻¹) * (b * k * b⁻¹ * k⁻¹) by group]
    exact mul_mem (hak _ hbk') (hbk k hk)
  one_mem' := ⟨one_mem _, fun k _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hak⟩
    refine ⟨inv_mem ha, fun k hk => ?_⟩
    have hk' : a⁻¹ * k * a ∈ kz T V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) k).mp hk
      simpa using this
    have h1 := inv_mem (hak _ hk')
    rwa [show (a * (a⁻¹ * k * a) * a⁻¹ * (a⁻¹ * k * a)⁻¹)⁻¹ = a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ by group]
      at h1

omit [Finite G] in
theorem mem_dK {T V : Subgroup G} {g : G} :
    g ∈ dK T V ↔ g ∈ mK T V ∧ ∀ k ∈ kz T V, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 (kz T V) := Iff.rfl

omit [Finite G] in
theorem mK_le_normalizer_dK : mK T V ≤ Subgroup.normalizer (dK T V : Set G) := by
  have key : ∀ g ∈ mK T V, ∀ d ∈ dK T V, g * d * g⁻¹ ∈ dK T V := by
    rintro g hg d ⟨hd, hdk⟩
    refine ⟨mul_mem (mul_mem hg hd) (inv_mem hg), fun k hk => ?_⟩
    have hO := normalizer_le_normalizer_pCoreOf 2 (kz T V) hg
    have hk' : g⁻¹ * k * g ∈ kz T V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hO _).mp (hdk _ hk')
    rwa [show g * (d * (g⁻¹ * k * g) * d⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ =
      g * d * g⁻¹ * k * (g * d * g⁻¹)⁻¹ * k⁻¹ by group] at h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key g hg d, fun hd => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hd
  rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group] at this

omit [Finite G] in
theorem kz_le_mK : kz T V ≤ mK T V := Subgroup.le_normalizer

theorem mem_pCoreOf_of_mem_dK (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {x : G} (hx : x ∈ kz T V) (hxD : x ∈ dK T V) : x ∈ pCoreOf 2 (kz T V) := by
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 h hMod h63
  have hcen : π ⟨x, hx⟩ ∈ Subgroup.center SL(2, F4) := by
    rw [Subgroup.mem_center_iff]
    intro A
    obtain ⟨k, rfl⟩ := hπs A
    have hker : (⟨x, hx⟩ * k * (⟨x, hx⟩ : ↥(kz T V))⁻¹ * k⁻¹ : ↥(kz T V)) ∈ π.ker := by
      rw [hπk, Subgroup.mem_subgroupOf]
      exact hxD.2 k k.2
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at hker
    exact hker.symm
  rw [center_sl24_eq_bot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hπk,
    Subgroup.mem_subgroupOf] at hcen
  exact hcen

theorem inf_dK_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    hz T V ⊓ dK T V ≤ pCoreOf 2 (hz T V) := by
  have hTH := T_le_hz h h63
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) := hTH.trans (le_normalizer_oTwoUpper _)
  have hHK : hz T V ≤ mK T V := le_normalizer_oTwoUpper _
  have hN : hz T V ≤ Subgroup.normalizer ((hz T V ⊓ dK T V : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer hg) (mK_le_normalizer_dK (hHK hg))
  have hp : IsPGroup 2 ↥(hz T V ⊓ dK T V) := by
    rintro ⟨c, hc⟩
    obtain ⟨hcH, hcD⟩ := Subgroup.mem_inf.mp hc
    have hcH' := hcH
    rw [(h63 G T L V h).2.2.1, sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTK] at hcH'
    obtain ⟨t, ht, k, hk, rfl⟩ := hcH'
    obtain ⟨n, hn⟩ := h.fsu.sylow.1 ⟨t, ht⟩
    have ht2 : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k', hk', e⟩ := pow_mul_mem_of_le_normalizer (hTK ht) hk (2 ^ n)
    rw [ht2, one_mul] at e
    have hk'D : k' ∈ dK T V := e ▸ pow_mem hcD _
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (kz T V))
      ⟨k', mem_pCoreOf_of_mem_dK h hMod h63 hk' hk'D⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : k' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, e, hm']
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hN hp

theorem exists_inv_mul_mem_dK (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {g : G} (hg : g ∈ mK T V) : ∃ x ∈ hz T V, x⁻¹ * g ∈ dK T V := by
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 h hMod h63
  have hHK : hz T V ≤ mK T V := le_normalizer_oTwoUpper _
  set Φ := autHom π hπs hπk
  set ι : ↥(hz T V) →* ↥(mK T V) := Subgroup.inclusion hHK
  have hker : ∀ x : ↥(hz T V), x ∈ (Φ.comp ι).ker → (x : G) ∈ pCoreOf 2 (hz T V) := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, autHom_eq_one_iff] at hx
    exact inf_dK_le h hMod h63 (Subgroup.mem_inf.mpr ⟨x.2, hHK x.2, hx⟩)
  obtain ⟨-, -, -, -, ⟨φ5, hφ5s, hφ5k⟩, -⟩ := h63 G T L V h
  have hH : Nat.card ↥(hz T V) = Nat.card ↥(pCoreOf 2 (hz T V)) * 120 := by
    have e1 := Subgroup.card_ker_mul_card_range φ5
    rw [MonoidHom.range_eq_top.mpr hφ5s, Subgroup.card_top, Nat.card_perm, Nat.card_fin, hφ5k]
      at e1
    rw [← e1, pCoreOf, Subgroup.card_map_of_injective (hz T V).subtype_injective]
    rfl
  have hk : Nat.card ↥(Φ.comp ι).ker ≤ Nat.card ↥(pCoreOf 2 (hz T V)) := by
    rw [← Subgroup.card_map_of_injective (hz T V).subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hker x hx
  have hrange : (Φ.comp ι).range = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [card_mulAut_sl24]
    have e2 := Subgroup.card_ker_mul_card_range (Φ.comp ι)
    have hQpos : 0 < Nat.card ↥(pCoreOf 2 (hz T V)) := Nat.card_pos
    rw [hH] at e2
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(Φ.comp ι).ker * Nat.card ↥(Φ.comp ι).range <
        Nat.card ↥(pCoreOf 2 (hz T V)) * 120 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hk) (Nat.mul_lt_mul_of_pos_left hlt hQpos)
    omega
  obtain ⟨x, hx⟩ := (Φ.comp ι).mem_range.mp (hrange ▸ Subgroup.mem_top (Φ ⟨g, hg⟩))
  refine ⟨x, x.2, ?_⟩
  have h1 : Φ ((ι x)⁻¹ * ⟨g, hg⟩) = 1 := by
    rw [map_mul, map_inv, ← MonoidHom.comp_apply, hx, inv_mul_cancel]
  rw [autHom_eq_one_iff] at h1
  exact ⟨mul_mem (inv_mem (hHK x.2)) hg, h1⟩

theorem exists_odd_mem_dK (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hN : ¬ mK T V ≤ hz T V) : ∃ d ∈ dK T V, d ≠ 1 ∧ Odd (orderOf d) := by
  by_contra hno
  push Not at hno
  apply hN
  have hTH := T_le_hz h h63
  have hTM : T ≤ mK T V := hTH.trans (le_normalizer_oTwoUpper _)
  have hp : IsPGroup 2 ↥(dK T V) := by
    refine IsPGroup.of_card_dvd_pow (n := Nat.card ↥(dK T V))
      (Nat.dvd_pow_self_iff Nat.card_pos.ne' two_ne_zero |>.mpr fun q hq => ?_)
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
    by_cases hq2 : q = 2
    · rw [hq2]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_refl 2, two_ne_zero⟩
    exfalso
    have hodd : Odd (orderOf (x : G)) := by
      rw [Subgroup.orderOf_coe, hx]
      exact hqp.odd_of_ne_two hq2
    have h1 := hno x x.2
    by_cases hx1 : (x : G) = 1
    · rw [hx1, orderOf_one] at hodd
      have : orderOf x = 1 := by
        rw [← Subgroup.orderOf_coe, hx1, orderOf_one]
      rw [this] at hx
      exact hqp.one_lt.ne hx
    · exact h1 hx1 hodd
  have hDO : dK T V ≤ pCoreOf 2 (mK T V) :=
    le_pCoreOf_of_le_normalizer 2 (fun d hd => hd.1) mK_le_normalizer_dK hp
  have hDT : dK T V ≤ T :=
    hDO.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h hTM))
  intro g hg
  obtain ⟨x, hx, hxg⟩ := exists_inv_mul_mem_dK h hMod h63 hg
  rw [show g = x * (x⁻¹ * g) by group]
  exact mul_mem hx (hTH (hDT hxg))

theorem not_mem_hz_of_mem_dK (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {d : G} (hd : d ∈ dK T V) (hd1 : d ≠ 1) (hodd : Odd (orderOf d)) : d ∉ hz T V := by
  intro hdH
  have hdQ := inf_dK_le h hMod h63 (Subgroup.mem_inf.mpr ⟨hdH, hd⟩)
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨d, hdQ⟩
  have hd2 : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf d ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hd2
  have hcop : Nat.Coprime (orderOf d) (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h1 : orderOf d = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  exact hd1 (orderOf_eq_one_iff.mp h1)

end CFSG.Quasithin.H13.L32A
