module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace Lem22

variable {G : Type} [Group G]

theorem inf_le_commutator {U V : Subgroup G} [IsMulCommutative ↥V]
    (hUV : U ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (htr : autOn U V = transvAxis ((U ⊓ V).subgroupOf V)) (hidx : (U ⊓ V).relIndex V = 2)
    {v : G} (hvV : v ∈ V) (hvU : v ∉ U) : U ⊓ V ≤ ⁅U, V⁆ := by
  classical
  rintro c ⟨hcU, hcV⟩
  set c' : ↥V := ⟨c, hcV⟩ with hc'
  have hc'2 : c' * c' = 1 := Subtype.ext (by
    show c * c = 1
    rw [← pow_two, hV2 c hcV])
  have hmulU : ∀ x y : ↥V, (x : G) ∉ U → (y : G) ∉ U → ((x * y : ↥V) : G) ∈ U := by
    intro x y hx hy
    have h1 : x * y ∈ (U ⊓ V).subgroupOf V := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (fun h0 => hx (Subgroup.mem_subgroupOf.mp h0).1)
        fun h0 => hy (Subgroup.mem_subgroupOf.mp h0).1
    exact (Subgroup.mem_subgroupOf.mp h1).1
  have hfU : ∀ x : ↥V, ((x * c' : ↥V) : G) ∈ U ↔ (x : G) ∈ U := fun x => by
    constructor
    · intro h
      have := U.mul_mem h (U.inv_mem hcU)
      simpa [hc'] using this
    · intro h
      exact U.mul_mem h hcU
  let f : ↥V → ↥V := fun x => if (x : G) ∈ U then x else x * c'
  have hfin : ∀ x : ↥V, (x : G) ∈ U → f x = x := fun x hx => by simp [f, hx]
  have hfout : ∀ x : ↥V, (x : G) ∉ U → f x = x * c' := fun x hx => by simp [f, hx]
  have hff : ∀ x, f (f x) = x := by
    intro x
    by_cases hx : (x : G) ∈ U
    · rw [hfin x hx, hfin x hx]
    · have h1 : ¬ ((x * c' : ↥V) : G) ∈ U := fun h => hx ((hfU x).mp h)
      rw [hfout x hx, hfout _ h1, mul_assoc, hc'2, mul_one]
  have hfmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : (x : G) ∈ U <;> by_cases hy : (y : G) ∈ U
    · rw [hfin _ (U.mul_mem hx hy), hfin x hx, hfin y hy]
    · have h1 : ¬ ((x * y : ↥V) : G) ∈ U := fun h => hy (by
        have := U.mul_mem (U.inv_mem hx) h
        simpa using this)
      rw [hfout _ h1, hfin x hx, hfout y hy, mul_assoc]
    · have h1 : ¬ ((x * y : ↥V) : G) ∈ U := fun h => hx (by
        have := U.mul_mem h (U.inv_mem hy)
        simpa using this)
      rw [hfout _ h1, hfout x hx, hfin y hy, mul_assoc, mul_comm y c', ← mul_assoc]
    · rw [hfin _ (hmulU x y hx hy), hfout x hx, hfout y hy]
      calc x * y = x * y * (c' * c') := by rw [hc'2, mul_one]
        _ = x * c' * (y * c') := mul_mul_mul_comm x y c' c'
  let τ : MulAut ↥V :=
    { toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      map_mul' := hfmul }
  have hτ : τ ∈ transvAxis ((U ⊓ V).subgroupOf V) := by
    refine ⟨fun a ha => hfin a (Subgroup.mem_subgroupOf.mp ha).1, fun x => ?_⟩
    show f x * x⁻¹ ∈ (U ⊓ V).subgroupOf V
    by_cases hx : (x : G) ∈ U
    · rw [hfin x hx, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [hfout x hx, mul_comm x c', mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_subgroupOf.mpr ⟨hcU, hcV⟩
  rw [← htr] at hτ
  obtain ⟨⟨u, huU⟩, hu⟩ := (A4.mem_autOn_iff hUV).mp hτ
  have huv : u * v * u⁻¹ = v * c := by
    have h1 := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hvV⟩ : ↥V) : G)) hu
    simp only [A4.actionOn_apply_coe] at h1
    rw [h1]
    show ((f ⟨v, hvV⟩ : ↥V) : G) = v * c
    rw [hfout _ hvU]
    rfl
  have e : c = ⁅v⁻¹, u⁆ := by
    calc c = v⁻¹ * (v * c) := by group
      _ = v⁻¹ * (u * v * u⁻¹) := by rw [huv]
      _ = ⁅v⁻¹, u⁆ := by rw [commutatorElement_def]; group
  rw [e, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (V.inv_mem hvV) huU

theorem comm_mem_of_inv {K : Type*} [Group K] {U₀ Q : Subgroup K} [U₀.Normal] {v h : K} {p : ℕ}
    (hpodd : Odd p) (hhp : h ^ p = 1) (hvh : v * h * v⁻¹ = h⁻¹)
    (hvQ : ∀ q ∈ Q, v * q * v⁻¹ * q⁻¹ ∈ U₀) (hhQ : ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) :
    ∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ U₀ := by
  set φ := QuotientGroup.mk' U₀ with hφ
  have hφ1 : ∀ y : K, φ y = 1 ↔ y ∈ U₀ := fun y => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcv : ∀ q ∈ Q, φ v * φ q = φ q * φ v := by
    intro q hq
    have h1 := (hφ1 _).mpr (hvQ q hq)
    simp only [map_mul, map_inv] at h1
    calc φ v * φ q = (φ v * φ q * (φ v)⁻¹ * (φ q)⁻¹) * φ q * φ v := by group
      _ = φ q * φ v := by rw [h1, one_mul]
  have hvh' : φ v * φ h * (φ v)⁻¹ = (φ h)⁻¹ := by
    have := congrArg φ hvh
    simpa only [map_mul, map_inv] using this
  have hsq : ∀ q ∈ Q, φ h * φ h * φ q = φ q * (φ h * φ h) := by
    intro q hq
    have hhq := hhQ q hq
    have e1 : (φ v)⁻¹ * φ q * φ v = φ q := by
      calc (φ v)⁻¹ * φ q * φ v = (φ v)⁻¹ * (φ q * φ v) := by group
        _ = (φ v)⁻¹ * (φ v * φ q) := by rw [hcv q hq]
        _ = φ q := by group
    have e2 : φ v * (φ h * φ q * (φ h)⁻¹) * (φ v)⁻¹ = φ h * φ q * (φ h)⁻¹ := by
      have h1 := hcv _ hhq
      simp only [map_mul, map_inv] at h1
      calc φ v * (φ h * φ q * (φ h)⁻¹) * (φ v)⁻¹ =
          (φ v * (φ h * φ q * (φ h)⁻¹)) * (φ v)⁻¹ := by group
        _ = ((φ h * φ q * (φ h)⁻¹) * φ v) * (φ v)⁻¹ := by rw [h1]
        _ = φ h * φ q * (φ h)⁻¹ := by group
    have e3 : (φ h)⁻¹ * φ q * φ h = φ h * φ q * (φ h)⁻¹ := by
      calc (φ h)⁻¹ * φ q * φ h = (φ h)⁻¹ * φ q * ((φ h)⁻¹)⁻¹ := by rw [inv_inv]
        _ = (φ v * φ h * (φ v)⁻¹) * φ q * (φ v * φ h * (φ v)⁻¹)⁻¹ := by rw [hvh']
        _ = φ v * (φ h * ((φ v)⁻¹ * φ q * φ v) * (φ h)⁻¹) * (φ v)⁻¹ := by group
        _ = φ v * (φ h * φ q * (φ h)⁻¹) * (φ v)⁻¹ := by rw [e1]
        _ = φ h * φ q * (φ h)⁻¹ := e2
    calc φ h * φ h * φ q = φ h * (φ h * φ q * (φ h)⁻¹) * φ h := by group
      _ = φ h * ((φ h)⁻¹ * φ q * φ h) * φ h := by rw [e3]
      _ = φ q * (φ h * φ h) := by group
  intro q hq
  rw [← hφ1]
  simp only [map_mul, map_inv]
  obtain ⟨k, hk⟩ := hpodd
  have hh : φ h = (φ h * φ h) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    calc φ h = φ h ^ (p + 1) := by rw [pow_succ, ← map_pow, hhp, map_one, one_mul]
      _ = φ h ^ (2 * (k + 1)) := by rw [hk]; ring_nf
  have hc : Commute (φ h * φ h) (φ q) := hsq q hq
  have hc' : Commute (φ h) (φ q) := by
    rw [hh]
    exact hc.pow_left _
  calc φ h * φ q * (φ h)⁻¹ * (φ q)⁻¹ = (φ q * φ h) * (φ h)⁻¹ * (φ q)⁻¹ := by rw [hc'.eq]
    _ = 1 := by group

theorem eq_commutator_zpowers [Finite G] {U : Subgroup G} {h : G}
    (hhU : h ∈ Subgroup.normalizer (U : Set G)) (hC : ∀ y ∈ U, h * y * h⁻¹ = y → y = 1) :
    U = ⁅U, Subgroup.zpowers h⁆ := by
  have hmemU : ∀ y ∈ U, ⁅y, h⁆ ∈ U := by
    intro y hy
    have h1 : h * y⁻¹ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hhU y⁻¹).mp (U.inv_mem hy)
    have e : ⁅y, h⁆ = y * (h * y⁻¹ * h⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact U.mul_mem hy h1
  refine le_antisymm ?_ ?_
  · let f : ↥U → ↥U := fun y => ⟨⁅(y : G), h⁆, hmemU y y.2⟩
    have hinj : Function.Injective f := by
      intro y₁ y₂ hy
      have h1 : ⁅(y₁ : G), h⁆ = ⁅(y₂ : G), h⁆ := congrArg Subtype.val hy
      rw [commutatorElement_def, commutatorElement_def] at h1
      have h2 : (y₂ : G)⁻¹ * y₁ = h * ((y₂ : G)⁻¹ * y₁) * h⁻¹ := by
        calc (y₂ : G)⁻¹ * y₁ =
            (y₂ : G)⁻¹ * (y₁ * h * (y₁ : G)⁻¹ * h⁻¹) * (h * y₁ * h⁻¹) := by group
          _ = (y₂ : G)⁻¹ * (y₂ * h * (y₂ : G)⁻¹ * h⁻¹) * (h * y₁ * h⁻¹) := by rw [h1]
          _ = h * ((y₂ : G)⁻¹ * y₁) * h⁻¹ := by group
      have h3 := hC _ (U.mul_mem (U.inv_mem y₂.2) y₁.2) h2.symm
      exact Subtype.ext (inv_mul_eq_one.mp h3).symm
    intro y hy
    obtain ⟨y', hy'⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨y, hy⟩
    have : ⁅(y' : G), h⁆ = y := congrArg Subtype.val hy'
    rw [← this]
    exact Subgroup.commutator_mem_commutator y'.2 (Subgroup.mem_zpowers h)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hk : h ^ k ∈ Subgroup.normalizer (U : Set G) := Subgroup.zpow_mem _ hhU k
    have h1 : h ^ k * a⁻¹ * (h ^ k)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hk a⁻¹).mp (U.inv_mem ha)
    have e : ⁅a, h ^ k⁆ = a * (h ^ k * a⁻¹ * (h ^ k)⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact U.mul_mem ha h1

variable [Finite G]

theorem data_of_card_eq_prime (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    {T L V H P U I : Subgroup G} {h v : G} {p : ℕ} (hyp : Hyp1223 G T L V)
    (hpre : Pre12_2_21 T L V H P U I h p) (hUO : U ≤ pCoreOf 2 H) (hcard : Nat.card P = p)
    (hvV : v ∈ V) (hvU : v ∉ U) (hvh : v * h * v⁻¹ = h⁻¹) (hhI : h ∈ I)
    (hCU : ∀ y ∈ U, h * y * h⁻¹ = y → y = 1) :
    Data12_2_22 V H P U (conjClosure U P) v p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hΦ, hhP, hhM, hI, hUI, hUdec, -, hUe, -,
    -, hidx, hcV, htr⟩ := hpre
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hPz, hord⟩ := Lem21.eq_zpowers_of_card_eq_prime hp hcard hhP hh1
  have hhp : h ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one h
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hOH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hIU : I ≤ Subgroup.normalizer (U : Set G) :=
    hUI ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
  have hVI : V ≤ I := hI ▸ le_sup_left
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hIU hhI
  have hhH : h ∈ H := hPH hhP
  have hvH : v ∈ H := hTH (hVT hvV)
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := by
    rw [hPz]
    exact (Subgroup.zpowers_le).mpr hhU
  have hconj : ∀ {X : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (X : Set G) →
      ∀ y ∈ X, g * y * g⁻¹ ∈ X := fun hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hW : conjClosure U P = U :=
    le_antisymm (conjClosure_le fun x hx y hy => hconj (hPU hx) y hy) (le_conjClosure U P)
  have hUcomm : U = ⁅U, P⁆ := by
    rw [hPz]
    exact eq_commutator_zpowers hhU hCU
  have hUV : U ⊓ V = pCoreOf 2 H ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hTUV : T ≤ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := by
    rw [hUV]
    exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO (hTH ht), hTV ht⟩
  have hconjUV : ∀ g ∈ H, ∀ y ∈ U ⊓ V, g * y * g⁻¹ ∈ U := by
    intro g hg y hy
    obtain ⟨x, hx, t, ht, rfl⟩ :=
      Lem22.exists_mul_of_mem h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hHPT hg
    have h1 : t * y * t⁻¹ ∈ U ⊓ V := hconj (hTUV ht) y hy
    have e : x * t * y * (x * t)⁻¹ = x * (t * y * t⁻¹) * x⁻¹ := by group
    rw [e]
    exact hconj (hPU hx) _ h1.1
  have hconjU : ∀ g ∈ H, ∀ y ∈ U, g * y * g⁻¹ ∈ U := by
    intro g hg y hy
    have hmap : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      conv_lhs => rw [hUdec]
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact hconjUV g hg w hw
      · rintro _ ⟨w, ⟨hwU, hwV⟩, rfl⟩
        have hw' : h * w * h⁻¹ ∈ U ⊓ V :=
          ⟨hconj hhU w hwU, Lem21Post.mem_conjugate_iff.mp hwV⟩
        have e : (MulAut.conj g).toMonoidHom w = (g * h⁻¹) * (h * w * h⁻¹) * (g * h⁻¹)⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact hconjUV _ (H.mul_mem hg (H.inv_mem hhH)) _ hw'
    exact hmap ⟨y, hy, rfl⟩
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    Sec121Swap.mem_normalizer_of_conj_mem fun y hy => hconjU g hg y hy
  have hUH : U ≤ H := hUO.trans hOH
  have hUn : (U.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hHU
  have hOh : ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ * q⁻¹ ∈ U := by
    intro q hq
    have h1 := comm_mem_of_inv (K := ↥H) (U₀ := U.subgroupOf H) (Q := (pCoreOf 2 H).subgroupOf H)
      (v := ⟨v, hvH⟩) (h := ⟨h, hhH⟩) hpodd (Subtype.ext (by simpa using hhp))
      (Subtype.ext (by simpa using hvh)) (fun r hr => by
        have hrO : (r : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hr
        rw [Subgroup.mem_subgroupOf]
        show v * (r : G) * v⁻¹ * (r : G)⁻¹ ∈ U
        have h2 : v * (r : G) * v⁻¹ * (r : G)⁻¹ ∈ pCoreOf 2 H ⊓ V := by
          refine ⟨Subgroup.mul_mem _ (hconj (hHO hvH) _ hrO) (Subgroup.inv_mem _ hrO), ?_⟩
          have e : v * (r : G) * v⁻¹ * (r : G)⁻¹ = v * ((r : G) * v⁻¹ * (r : G)⁻¹) := by group
          rw [e]
          exact V.mul_mem hvV (hconj (hTV (hQT hrO)) _ (V.inv_mem hvV))
        rw [← hUV] at h2
        exact h2.1)
      (fun r hr => by
        rw [Subgroup.mem_subgroupOf] at hr ⊢
        exact hconj (hHO hhH) _ hr) ⟨q, hOH hq⟩ (Subgroup.mem_subgroupOf.mpr hq)
    exact Subgroup.mem_subgroupOf.mp h1
  have hON : pCoreOf 2 H ≤ Subgroup.normalizer ((P ⊔ U : Subgroup G) : Set G) := by
    intro q hq
    have hqH := hOH hq
    have hqh : q * h * q⁻¹ ∈ P ⊔ U := by
      have e : q * h * q⁻¹ = (h * q * h⁻¹ * q⁻¹)⁻¹ * h := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (U.inv_mem (hOh q hq)))
        (Subgroup.mem_sup_left hhP)
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    have hmap : (P ⊔ U).map (MulAut.conj q).toMonoidHom ≤ P ⊔ U := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        rw [hPz] at hw
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ hqh k
      · rintro _ ⟨w, hw, rfl⟩
        exact Subgroup.mem_sup_right (hconjU q hqH w hw)
    exact hmap ⟨y, hy, rfl⟩
  have hO2le : oTwoUpper H ≤ P ⊔ U := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, hk⟩ := Lem22.exists_pow_mem_sup h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hx
    have hsup : P ⊔ pCoreOf 2 H = (P ⊔ U) ⊔ pCoreOf 2 H :=
      le_antisymm (sup_le_sup_right le_sup_left _) (sup_le (sup_le le_sup_left
        (hUO.trans le_sup_right)) le_sup_right)
    rw [hsup, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left (P ⊔ U) (pCoreOf 2 H) hON] at hk
    obtain ⟨b, hb, q, hq, hbq⟩ := hk
    have hbq' : b * q = x ^ 2 ^ k := hbq
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨q, hq⟩
    have hm' : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨b', hb', hpow⟩ := A4.exists_pow_mul_eq hb (hON hq) (2 ^ m)
    refine ⟨k + m, ?_⟩
    rw [pow_add, pow_mul, ← hbq', hpow, hm', mul_one]
    exact hb'
  have hle2 : P ⊔ U ≤ oTwoUpper H := by
    refine sup_le (Lem22.le_oTwoUpper hp hp2 hPp hPH) ?_
    calc U = ⁅U, P⁆ := hUcomm
      _ ≤ oTwoUpper H := by
        rw [Subgroup.commutator_le]
        intro u hu x hx
        have hxo : Odd (orderOf x) := by
          rw [hPz] at hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          have hkp : (h ^ k) ^ p = 1 := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hhp, one_zpow]
          exact hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hkp)
        have hxH := hPH hx
        have hux : Odd (orderOf (u * x * u⁻¹)) := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact hxo
        rw [commutatorElement_def]
        refine Subgroup.mul_mem _ (mem_oTwoUpper_of_odd ?_ hux)
          (mem_oTwoUpper_of_odd (H.inv_mem hxH) (by rw [orderOf_inv]; exact hxo))
        exact H.mul_mem (H.mul_mem (hUH hu) hxH) (H.inv_mem (hUH hu))
  have hPM : P ⊓ Subgroup.normalizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨hPx, -⟩ := Lem21.eq_zpowers_of_card_eq_prime hp hcard hx.1 hx1
    exact hhM ((Subgroup.zpowers_le.mpr hx.2) (hPx ▸ hhP))
  have hUNV : U ≤ Subgroup.normalizer (V : Set G) := (hUO.trans hQT).trans hTV
  refine ⟨hvV, hvU, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl hcard⟩
  · rw [hPz]
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hvh]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers h)) k
  · rw [hW]
    exact hUcomm
  · rw [hW]
    exact hUO
  · rw [hW]
    exact hUe
  · rw [hW]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro u hu x hx
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact V.mul_mem (hconj (hUNV hu) x hx) (V.inv_mem hx)
      · have e : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact U.mul_mem hu (hconj (hIU (hVI hx)) _ (U.inv_mem hu))
    · rw [inf_comm]
      exact inf_le_commutator hUNV hV2 htr hidx hvV hvU
  · rw [hW, inf_comm]
    exact hidx
  · rw [hW]
    exact le_antisymm hO2le hle2
  · rw [← hΦ, hPM]
    exact bot_le

end Lem22

end CFSG.Quasithin.H13
