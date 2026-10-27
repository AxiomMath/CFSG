module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Defs
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gold14610

variable {G : Type} [Group G] [Finite G] {I K : Subgroup G}

@[expose] def toD (hKI : K ≤ I) : ↥K →* (↥I ⧸ CFSG.pPrimeCore 3 ↥I) :=
  (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)).comp (Subgroup.inclusion hKI)

omit [Finite G] in
theorem toD_eq_one_iff (hKI : K ≤ I) (k : ↥K) :
    toD hKI k = 1 ↔ (⟨(k : G), hKI k.2⟩ : ↥I) ∈ CFSG.pPrimeCore 3 ↥I := by
  simp only [toD, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Iff.rfl

@[expose] def toImg (hKI : K ≤ I) : ↥K →* ↥(imgMod3 I K) :=
  (toD hKI).codRestrict (imgMod3 I K) fun k =>
    ⟨Subgroup.inclusion hKI k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩

omit [Finite G] in
theorem toImg_surjective (hKI : K ≤ I) : Function.Surjective (toImg hKI) := by
  rintro ⟨u, a, ha, rfl⟩
  exact ⟨⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩, rfl⟩

omit [Finite G] in
theorem mem_ker_toImg (hKI : K ≤ I) (k : ↥K) :
    k ∈ (toImg hKI).ker ↔ (⟨(k : G), hKI k.2⟩ : ↥I) ∈ CFSG.pPrimeCore 3 ↥I := by
  rw [← toD_eq_one_iff hKI, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

omit [Finite G] in
theorem mem_pCore_two_iff {X : Subgroup G} (x : ↥X) :
    x ∈ CFSG.pCore 2 ↥X ↔ (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff x).symm

theorem inf_pCoreOf_le_pCoreOf (hKI : K ≤ I) : K ⊓ pCoreOf 2 I ≤ pCoreOf 2 K := by
  have hp : IsPGroup 2 (pCoreOf 2 I) := pCoreOf_isPGroup 2 I
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => ?_) (hp.to_le inf_le_right)
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 I (hKI hx)⟩

theorem pCore_le_ker_toD (hKI : K ≤ I) (hK : IsSubnormal K I) :
    CFSG.pCore 2 ↥K ≤ (toD hKI).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, toD_eq_one_iff]
  have h1 : (x : G) ∈ pCoreOf 2 K := (mem_pCore_two_iff x).mp hx
  have h2 : (x : G) ∈ pCoreOf 2 I := A4.pCoreOf_le_of_subnormal 2 hK h1
  obtain ⟨y, hy, hyx⟩ := h2
  have : y = ⟨x, hKI x.2⟩ := Subtype.ext hyx
  exact F6.pCore_le_pPrimeCore (this ▸ hy)

theorem pCore_le_ker_toImg (hKI : K ≤ I) (hK : IsSubnormal K I) :
    CFSG.pCore 2 ↥K ≤ (toImg hKI).ker := by
  intro x hx
  have := pCore_le_ker_toD hKI hK hx
  rw [MonoidHom.mem_ker] at this ⊢
  exact Subtype.ext this

omit [Finite G] in
theorem exists_odd_pow_mem_pCore_I
    (hsyl : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I))
    {a : ↥I} (ha : a ∈ CFSG.pPrimeCore 3 ↥I) : ∃ m : ℕ, Odd m ∧ a ^ m ∈ Open.pCore 2 ↥I := by
  obtain ⟨-, -, hodd⟩ := hsyl
  set N := CFSG.pPrimeCore 3 ↥I
  set Q := Open.pCore 2 ↥I
  have hQn : (Q.subgroupOf N).Normal := (CFSG.LieType.BorelTits.pCore_normal 2).subgroupOf N
  refine ⟨(Q.subgroupOf N).index, Nat.not_even_iff_odd.mp fun he => hodd (even_iff_two_dvd.mp he),
    ?_⟩
  have h1 : (QuotientGroup.mk (⟨a, ha⟩ : ↥N) : ↥N ⧸ Q.subgroupOf N) ^ (Q.subgroupOf N).index =
      1 := by
    rw [Subgroup.index_eq_card]
    exact pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem exists_odd_pow_mem_pCore_K (hKI : K ≤ I)
    (hsyl : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I)) {k : ↥K}
    (hk : toD hKI k = 1) : ∃ m : ℕ, Odd m ∧ k ^ m ∈ CFSG.pCore 2 ↥K := by
  obtain ⟨m, hm, hmQ⟩ := exists_odd_pow_mem_pCore_I hsyl ((toD_eq_one_iff hKI k).mp hk)
  refine ⟨m, hm, ?_⟩
  rw [mem_pCore_two_iff]
  have h1 : (k : G) ^ m ∈ pCoreOf 2 I := ⟨_, hmQ, rfl⟩
  exact inf_pCoreOf_le_pCoreOf hKI ⟨(k ^ m).2, h1⟩

end Gold14610

end CFSG.Quasithin
