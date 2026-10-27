module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Setup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

theorem pCoreOf_autOn_vOf_eq_bot (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hsolv : Group.IsSolvable X) (hVne : vOf T X ≠ ⊥) :
    pCoreOf 2 (autOn (X ⊔ T) (vOf T X)) = ⊥ := by
  obtain ⟨-, -, -, p, hp, hp2, hpow, -, -⟩ := id hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set V := vOf T X with hVdef
  set N := Subgroup.normalizer (V : Set G) with hN
  have hXTV : X ⊔ T ≤ N := sup_le_normalizer_vOf hX
  have hXVN : X ≤ N := le_sup_left.trans hXTV
  have hTVN : T ≤ N := le_sup_right.trans hXTV
  set Xb := autOn (X ⊔ T) V with hXb
  set Xs := autOn X V with hXs
  set Ts := autOn T V with hTs
  set Q := pCoreOf 2 Xb with hQ
  have hQXb : Q ≤ Xb := pCoreOf_le 2 Xb
  have hXbQ : Xb ≤ Subgroup.normalizer (Q : Set (MulAut V)) := le_normalizer_pCoreOf 2 Xb
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 Xb
  have hconj : ∀ g h : N, conjAct V g * conjAct V h * (conjAct V g)⁻¹ =
      conjAct V (g * h * g⁻¹) := fun g h => by simp
  have hXsp : ∀ y ∈ Xs, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    refine A4.conjAct_eq_one_iff.mpr ?_
    have hxp := pCoreOf_le_centralizer_vOf hX (hpow x (Subgroup.mem_subgroupOf.mp hx))
    simpa using hxp
  have hXsP : IsPGroup p Xs := fun y => ⟨1, Subtype.ext (by simpa using hXsp y y.2)⟩
  have hXbN : Xb ≤ Subgroup.normalizer (Xs : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * x * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_of_isXi hX
      (Subgroup.mem_subgroupOf.mp hg)) x).mp (Subgroup.mem_subgroupOf.mp hx)
  have hTs2 : IsPGroup 2 Ts := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨k, hk⟩ := hT.1 ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp [← map_pow, hk']
  have hTsXb : Ts ≤ Xb := A4.autOn_mono le_sup_right
  have hXsXb : Xs ≤ Xb := A4.autOn_mono le_sup_left
  have hQTs : IsPGroup 2 (Q ⊔ Ts : Subgroup (MulAut V)) :=
    IsPGroup.to_sup_of_normal_left' hQ2 hTs2 (hTsXb.trans hXbQ)
  have hQXs : Q ⊓ Xs = ⊥ := (IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) Q Xs hQ2 hXsP).eq_bot
  have hR := inf_centralizer_vOf_le hX hsolv hVne
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  obtain ⟨g, hg, rfl⟩ := hQXb hq
  have hg' : (g : G) ∈ ((X ⊔ T : Subgroup G) : Set G) := Subgroup.mem_subgroupOf.mp hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hX.2.1] at hg'
  obtain ⟨x, hx, t, ht, hgxt⟩ := hg'
  have hgxt' : g = ⟨x, hXVN hx⟩ * ⟨t, hTVN ht⟩ := Subtype.ext hgxt.symm
  set xh := conjAct V ⟨x, hXVN hx⟩ with hxh
  set th := conjAct V ⟨t, hTVN ht⟩ with hth
  have hqe : conjAct V g = xh * th := by rw [hgxt', map_mul]
  have hxhXs : xh ∈ Xs := ⟨⟨x, hXVN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hxhQ : xh ∈ Q ⊔ Ts := by
    have e : xh = conjAct V g * th⁻¹ := by rw [hqe]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right
      (Subgroup.inv_mem _ ⟨⟨t, hTVN ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩))
  obtain ⟨k, hk⟩ := hQTs ⟨xh, hxhQ⟩
  have hk' : xh ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hxh1 : xh = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one (hXsp xh hxhXs)))
  have hqt : conjAct V g = th := by rw [hqe, hxh1, one_mul]
  have hcent : ∀ y ∈ Xs, th * y * th⁻¹ * y⁻¹ = 1 := by
    intro y hy
    have h1 : th * y * th⁻¹ * y⁻¹ ∈ Q := by
      have hthQ : th ∈ Q := hqt ▸ hq
      have hyQ : y * th⁻¹ * y⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hXbQ (hXsXb hy)) th⁻¹).mp (Q.inv_mem hthQ)
      have e : th * y * th⁻¹ * y⁻¹ = th * (y * th⁻¹ * y⁻¹) := by group
      rw [e]
      exact Q.mul_mem hthQ hyQ
    have h2 : th * y * th⁻¹ * y⁻¹ ∈ Xs := by
      have hthy : th * y * th⁻¹ ∈ Xs :=
        (Subgroup.mem_normalizer_iff.mp (hXbN (hqt ▸ hQXb hq)) y).mp hy
      exact Xs.mul_mem hthy (Xs.inv_mem hy)
    have h3 : th * y * th⁻¹ * y⁻¹ ∈ Q ⊓ Xs := ⟨h1, h2⟩
    rwa [hQXs, Subgroup.mem_bot] at h3
  have htR : t ∈ pCoreOf 2 (X ⊔ T) := by
    refine xi_mem_pCoreOf_sup hT hX hp hp2 hpow ht fun x' hx' => hR ⟨?_, ?_⟩
    · exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hX.2.1 ht) x').mp hx') (X.inv_mem hx')
    · have h1 := hcent (conjAct V ⟨x', hXVN hx'⟩)
        ⟨⟨x', hXVN hx'⟩, Subgroup.mem_subgroupOf.mpr hx', rfl⟩
      rw [hth, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul] at h1
      have h2 := A4.conjAct_eq_one_iff.mp h1
      simpa using h2
  rw [hqt, hth]
  exact A4.conjAct_eq_one_iff.mpr (pCoreOf_sup_le_centralizer_vOf T X htR)

theorem isTwoReducedIn_vOf (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hsolv : Group.IsSolvable X) (hVne : vOf T X ≠ ⊥) : IsTwoReducedIn (X ⊔ T) (vOf T X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(vOf_le hX).trans le_sup_left, sup_le_normalizer_vOf hX, isElemAbelian_vOf T X, ?_⟩
  intro D hD hDn hD2
  set V := vOf T X with hVdef
  have hXTV : X ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_vOf hX
  have hO := pCoreOf_autOn_vOf_eq_bot hT hX hsolv hVne
  set Xb := autOn (X ⊔ T) V with hXb
  set Db := autOn D V with hDb
  have hconj : ∀ g h : Subgroup.normalizer (V : Set G), conjAct V g * conjAct V h *
      (conjAct V g)⁻¹ = conjAct V (g * h * g⁻¹) := fun g h => by simp
  have hDbXb : Db ≤ Xb := A4.autOn_mono hD
  have hXbDb : Xb ≤ Subgroup.normalizer (Db : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨d, hd, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * d * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hDn (Subgroup.mem_subgroupOf.mp hg)) d).mp
      (Subgroup.mem_subgroupOf.mp hd)
  have hDb2 : IsPGroup 2 Db := by
    rintro ⟨_, d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hD2 d (Subgroup.mem_subgroupOf.mp hd)
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    exact A4.conjAct_eq_one_iff.mpr (by simpa using hk)
  have hle : Db ≤ pCoreOf 2 Xb := le_pCoreOf_of_le_normalizer 2 hDbXb hXbDb hDb2
  rw [hO] at hle
  intro d hd
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := hXTV (hD hd)
  have h1 := hle ⟨⟨d, hdN⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  rw [Subgroup.mem_bot] at h1
  exact A4.conjAct_eq_one_iff.mp h1

theorem inf_centralizer_vOf_eq (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hsolv : Group.IsSolvable X) (hVne : vOf T X ≠ ⊥) :
    T ⊓ Subgroup.centralizer (vOf T X : Set G) =
      pCoreOf 2 ((X ⊔ T) ⊓ Subgroup.centralizer (vOf T X : Set G)) := by
  obtain ⟨-, -, -, p, hp, hp2, hpow, -, -⟩ := id hX
  set V := vOf T X with hVdef
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  have hXTV : X ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_vOf hX
  have hR := inf_centralizer_vOf_le hX hsolv hVne
  have hTR : T ⊓ Subgroup.centralizer (V : Set G) ≤ R := by
    rintro t ⟨ht, htV⟩
    refine xi_mem_pCoreOf_sup hT hX hp hp2 hpow ht fun x hx => hR ⟨?_, ?_⟩
    · exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hX.2.1 ht) x).mp hx) (X.inv_mem hx)
    · have h1 : x * t⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer
          (hXTV (le_sup_left (b := T) hx))) t⁻¹).mp (Subgroup.inv_mem _ htV)
      have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ htV h1
  have hRT : R ≤ T :=
    pCoreOf_le_of_quasithinIsSylowTwo hT (le_sup_right.trans Subgroup.le_normalizer)
  have hRV : R ≤ Subgroup.centralizer (V : Set G) := pCoreOf_sup_le_centralizer_vOf T X
  have hTV : T ⊓ Subgroup.centralizer (V : Set G) = R := le_antisymm hTR (le_inf hRT hRV)
  set K := (X ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hK
  have hKn : X ⊔ T ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    A4.mem_normalizer_inf (Subgroup.le_normalizer hg) (A4.mem_normalizer_centralizer (hXTV hg))
  have hRK : R ≤ K := le_inf (pCoreOf_le 2 _) hRV
  rw [hTV]
  exact le_antisymm
    (le_pCoreOf_of_le_normalizer 2 hRK (inf_le_left.trans (le_normalizer_pCoreOf 2 (X ⊔ T)))
      (pCoreOf_isPGroup 2 _))
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans inf_le_left)
      (hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K))

theorem qhatInt_vOf_le_two {G : Type} [Group G] [Finite G] {T X : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h4 : Stmt1542Four G T) (hX : IsXi T X)
    (hM : IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G))) (hsolv : Group.IsSolvable X) :
    qhatInt (X ⊔ T) (vOf T X) (isElemAbelian_vOf T X) ≤ 2 := by
  have hVne := vOf_ne_bot hyp hX hM
  exact h4 (X ⊔ T) _ (vOf T X) ⟨le_sup_right, hX.2.2.1⟩ hM hVne
    (isTwoReducedIn_vOf hyp.sylow hX hsolv hVne) (inf_centralizer_vOf_eq hyp.sylow hX hsolv hVne)
    (vOf_le_pCoreOf_normalizer hX)

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
