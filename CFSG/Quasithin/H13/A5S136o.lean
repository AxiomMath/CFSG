module

public import CFSG.Quasithin.H13.A5S136m
public import CFSG.Quasithin.H13.A5S136oa
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin
open CFSG.Quasithin.A5Model
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem conj_mem_centralizer {K : Subgroup G} {t x : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ Subgroup.centralizer (K : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro k hk
  have hk' : t⁻¹ * k * t ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) k).mp hk
    simpa using this
  have h1 := hx _ hk'
  calc k * (t * x * t⁻¹) = t * ((t⁻¹ * k * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * k * t)) * t⁻¹ := by rw [h1]
    _ = t * x * t⁻¹ * k := by group

theorem sq_mem_centralizer_of_inner {K : Subgroup G} {z l : G} (hz : z ^ 2 = 1)
    (hl : ∀ x ∈ K, z⁻¹ * x * z = l⁻¹ * x * l) (hlK : l ∈ K) :
    l ^ 2 ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := hl x hx
  have hx' : l⁻¹ * x * l ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hlK) hx) hlK
  have h2 := hl _ hx'
  have h3 : (l ^ 2)⁻¹ * x * l ^ 2 = x := by
    calc (l ^ 2)⁻¹ * x * l ^ 2 = l⁻¹ * (l⁻¹ * x * l) * l := by rw [pow_two]; group
      _ = z⁻¹ * (z⁻¹ * x * z) * z := by rw [h1, h2]
      _ = (z ^ 2)⁻¹ * x * z ^ 2 := by rw [pow_two]; group
      _ = x := by rw [hz]; group
  calc x * l ^ 2 = l ^ 2 * ((l ^ 2)⁻¹ * x * l ^ 2) := by group
    _ = l ^ 2 * x := by rw [h3]

theorem not_mem_centralizer_of_inner {K : Subgroup G} {z l : G}
    (hl : ∀ x ∈ K, z⁻¹ * x * z = l⁻¹ * x * l)
    (hzK : ¬ K ≤ Subgroup.centralizer ({z} : Set G)) : l ∉ Subgroup.centralizer (K : Set G) := by
  intro hlC
  apply hzK
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hl x hx
  have h2 : l⁻¹ * x * l = x := by
    have := (Subgroup.mem_centralizer_iff.mp hlC) x hx
    calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
      _ = l⁻¹ * (l * x) := by rw [this]
      _ = x := by group
  rw [h2] at h1
  calc x * z = z * (z⁻¹ * x * z) := by group
    _ = z * x := by rw [h1]

theorem le_centralizer_of_mem {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (K : Set G)) : K ≤ Subgroup.centralizer ({g} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hg) k hk

theorem false_of_isSylowTwoOf_le_centralizer {K Q : Subgroup G} (hQ : IsSylowTwoOf Q K)
    (hQZ : Q ≤ Subgroup.centralizer (K : Set G)) {l : G} (hl : l ∈ K)
    (hl2 : l ^ 2 ∈ Subgroup.centralizer (K : Set G))
    (hlZ : l ∉ Subgroup.centralizer (K : Set G)) : False := by
  set Z := K ⊓ Subgroup.centralizer (K : Set G) with hZ
  have hQZ' : Q ≤ Z := le_inf hQ.1 hQZ
  have hZK : Z ≤ K := inf_le_left
  have hodd : ¬ 2 ∣ (Z.subgroupOf K).index := by
    intro h
    apply hQ.2.2
    have e := Subgroup.relIndex_mul_relIndex Q Z K hQZ' hZK
    show 2 ∣ Q.relIndex K
    rw [← e]
    exact h.mul_left _
  have hn : (Z.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * n * (g : G)⁻¹ = n := by
      have := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2) g g.2
      rw [this]
      group
    have e : ((g * n * g⁻¹ : ↥K) : G) = (g : G) * n * (g : G)⁻¹ := rfl
    rw [e, hc]
    exact hn
  let q : ↥K ⧸ Z.subgroupOf K := QuotientGroup.mk ⟨l, hl⟩
  have hq2 : q ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨K.pow_mem hl 2, hl2⟩
  have hq1 : q ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact fun h => hlZ (Subgroup.mem_inf.mp h).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf q = 2 := orderOf_eq_prime hq2 hq1
  have hd : 2 ∣ Nat.card (↥K ⧸ Z.subgroupOf K) := h2 ▸ orderOf_dvd_natCard q
  exact hodd hd

end General

@[expose] def Conf1366 {G : Type} [Group G] (K X Q : Subgroup G) (a z l : G) : Prop :=
  K ≤ X ∧ X ≤ Subgroup.normalizer (K : Set G) ∧ IsSylowTwoOf Q X ∧ a ∈ Q ∧ z ∈ Q ∧
    a ^ 2 = 1 ∧ z ^ 2 = 1 ∧
    (∀ t ∈ Q, a * t * a⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) ∧
    (∀ t ∈ Q, z * t * z⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) ∧
    a ∉ Subgroup.centralizer (K : Set G) ∧ z ∉ Subgroup.centralizer (K : Set G) ∧
    a * z⁻¹ ∉ Subgroup.centralizer (K : Set G) ∧ InducesInner z K ∧
    l ∈ Subgroup.normalizer (K : Set G) ∧ Odd (orderOf l) ∧
    l * a * l⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set G) ∧
    l * z * l⁻¹ * z⁻¹ ∉ Subgroup.centralizer (K : Set G)

@[expose] def FactConfL33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K X Q : Subgroup G) (a z l : G), CFSG.IsQuasisimple ↥K →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 3 3 1 → ¬ Conf1366 K X Q a z l

@[expose] def FactConfL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K X Q : Subgroup G) (a z l : G) (p : ℕ),
    CFSG.IsQuasisimple ↥K → IsFermatOrMersennePrime p →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1 → ¬ Conf1366 K X Q a z l

@[expose] def FactConfSpor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K X Q : Subgroup G) (a z l : G)
    (s : TauCeti.SporadicName), CFSG.IsQuasisimple ↥K → IsLemma115SporadicName s →
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.Carrier s) → ¬ Conf1366 K X Q a z l

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem charTwo_centralizer_a : CharTwo (Subgroup.centralizer ({S.a} : Set G)) := by
  obtain ⟨g, -, hg⟩ := S.exists_conj_a
  refine charTwo_centralizer_of_conj_mem S.h13.qtke S.h13.sylow S.orderOf_a (g := g⁻¹) ?_
  have e : g⁻¹ * S.a * g⁻¹⁻¹ = S.z := by rw [← hg]; group
  rw [e]
  refine Subgroup.mem_inf.mpr ⟨S.V_le_T S.z_mem_V, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have := S.conj_z_of_mem_T ht
  calc t * S.z = t * S.z * t⁻¹ * t := by group
    _ = S.z * t := by rw [this]

theorem charTwo_Gv_a : CharTwo (Subgroup.centralizer ({S.a} : Set G) ⊓
    Subgroup.centralizer ({S.v12} : Set G)) := by
  have hva : S.v12 ∈ Subgroup.centralizer ({S.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨S.v12, S.v12_mem_V⟩
        ⟨S.a, S.a_mem_V⟩))
  have h := CharTwo.inf_centralizer S.charTwo_centralizer_a
    (X := Subgroup.zpowers S.v12) (Subgroup.zpowers_le.mpr hva)
    (S.isPGroup_V.to_le (Subgroup.zpowers_le.mpr S.v12_mem_V))
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem not_le_centralizer_a {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G))) :
    ¬ K ≤ Subgroup.centralizer ({S.a} : Set G) := fun hKa =>
  not_le_of_isComponentIn_of_charTwo S.charTwo_Gv_a inf_le_right hK (le_inf hKa hK.1)

theorem a_mem_normalizer {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hsyl : IsSylowTwoOf S.Tv (Subgroup.centralizer ({S.v12} : Set G)))
    {l : G} (hl : l ∈ K) (hl2 : l ^ 2 ∈ Subgroup.centralizer (K : Set G))
    (hlZ : l ∉ Subgroup.centralizer (K : Set G)) :
    S.a ∈ Subgroup.normalizer (K : Set G) := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  by_contra hN
  have hKc : CFSG.Assembly.IsComponentOf K Gv :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.1).2 hK.2
  have hKac := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hKc S.a
  have hav : S.a * S.v12 * S.a⁻¹ = S.v12 := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp S.a_mem_Gv]
    group
  have hGa : Gv.map (MulAut.conj S.a).toMonoidHom = Gv := by
    rw [hGv, CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hav]
  rw [hGa] at hKac
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hKc hKac with h | h
  · apply hN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : S.a * x * S.a⁻¹ ∈ K.map (MulAut.conj S.a).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [← h] at h1
    · intro hx
      rw [h] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hyx : y = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxy
        exact mul_left_cancel (mul_right_cancel hxy)
      rwa [← hyx]
  · have hcomm : K.map (MulAut.conj S.a).toMonoidHom ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h)
    have hQ := CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hsyl hK.1 hK.2.2
    refine false_of_isSylowTwoOf_le_centralizer hQ ?_ hl hl2 hlZ
    intro x hx
    obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv hxT)
    have h1 : S.a * x * S.a⁻¹ = S.v12 ^ k * x := by
      rw [hk]
      group
    have h2 : S.a * x * S.a⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      hcomm ⟨x, hxK, by simp [MulAut.conj_apply]⟩
    rw [h1, Subgroup.mem_centralizer_iff] at h2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc : Commute y (S.v12 ^ k) :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hy)) k
    calc y * x = (S.v12 ^ k)⁻¹ * (y * (S.v12 ^ k * x)) := by
          rw [← mul_assoc y, hc.eq]
          group
      _ = (S.v12 ^ k)⁻¹ * ((S.v12 ^ k * x) * y) := by rw [h2 y hy]
      _ = x * y := by group

theorem z_mem_centralizer_of_comm {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hLvN : S.Lv ≤ Subgroup.normalizer (K : Set G))
    (h : ∀ l ∈ S.Lv, l * S.z * l⁻¹ * S.z⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    S.z ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨l0, hl0, hσ⟩ := S.exists_Lv_c234
  have hLvGv : S.Lv ≤ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact (oTwoUpper_le _).trans inf_le_right
  have hc : (l0 : G) * S.v12 = S.v12 * l0 :=
    Subgroup.mem_centralizer_singleton_iff.mp (hLvGv hl0)
  set w0 := S.z * S.v12⁻¹ with hw0
  have hw0V : w0 ∈ V := V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V)
  have hpsiw0 : S.frame.ψ ⟨w0, hw0V⟩ = W4 * E12⁻¹ := by
    have e : (⟨w0, hw0V⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ * (⟨S.v12, S.v12_mem_V⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_z, S.psi_v12]
  have hx : ⁅w0, (l0 : G)⁆ ∈ Subgroup.centralizer (K : Set G) := by
    have e : ⁅w0, (l0 : G)⁆ = ((l0 : G) * S.z * (l0 : G)⁻¹ * S.z⁻¹)⁻¹ := by
      rw [commutatorElement_def, hw0]
      calc S.z * S.v12⁻¹ * l0 * (S.z * S.v12⁻¹)⁻¹ * (l0 : G)⁻¹ =
            S.z * (S.v12⁻¹ * ((l0 : G) * S.v12)) * S.z⁻¹ * (l0 : G)⁻¹ := by group
        _ = S.z * (S.v12⁻¹ * (S.v12 * l0)) * S.z⁻¹ * (l0 : G)⁻¹ := by rw [hc]
        _ = ((l0 : G) * S.z * (l0 : G)⁻¹ * S.z⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (h _ hl0)
  obtain ⟨hxV, hψx⟩ := S.psi_commutator ⟨w0, hw0V⟩ l0
  rw [hpsiw0] at hψx
  have hconj := S.psi_conj l0 ⟨_, hxV⟩
  rw [hψx] at hconj
  have hpact : pact (S.frame.ρ l0) (W4 * E12⁻¹ * (pact (S.frame.ρ l0) (W4 * E12⁻¹))⁻¹) =
      W4 * E12⁻¹ := by
    rcases hσ with h1 | h1 <;> rw [h1]
    · exact pact_comm_W4E12.1
    · exact pact_comm_W4E12.2
  rw [hpact, ← hpsiw0] at hconj
  have hw : (l0 : G) * ⁅w0, (l0 : G)⁆ * (l0 : G)⁻¹ = w0 :=
    congrArg Subtype.val (S.frame.ψ.injective hconj)
  have hw0C : w0 ∈ Subgroup.centralizer (K : Set G) := by
    have := conj_mem_centralizer (hLvN hl0) hx
    rwa [hw] at this
  have hvC : S.v12 ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKG hk)
  have hz : S.z = w0 * S.v12 := by rw [hw0]; group
  rw [hz]
  exact Subgroup.mul_mem _ hw0C hvC

theorem mul_inv_not_mem_centralizer {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hLvN : S.Lv ≤ Subgroup.normalizer (K : Set G))
    (hzK : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G)) :
    S.a * S.z⁻¹ ∉ Subgroup.centralizer (K : Set G) := by
  intro haz
  refine hzK (le_centralizer_of_mem (S.z_mem_centralizer_of_comm hKG hLvN fun l hl => ?_))
  have hla := S.Lv_comm_a hl
  have hc := conj_mem_centralizer (hLvN hl) haz
  have e : l * S.z * l⁻¹ * S.z⁻¹ = (l * (S.a * S.z⁻¹) * l⁻¹)⁻¹ * (S.a * S.z⁻¹) := by
    calc l * S.z * l⁻¹ * S.z⁻¹ = l * S.z * l⁻¹ * (l * S.a * l⁻¹)⁻¹ * (S.a * S.z⁻¹) := by
          rw [hla]
          group
      _ = (l * (S.a * S.z⁻¹) * l⁻¹)⁻¹ * (S.a * S.z⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) haz

theorem exists_Lv_odd {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hLvN : S.Lv ≤ Subgroup.normalizer (K : Set G))
    (hzK : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G)) :
    ∃ y ∈ S.Lv, Odd (orderOf y) ∧ y * S.z * y⁻¹ * S.z⁻¹ ∉ Subgroup.centralizer (K : Set G) := by
  by_contra hne
  push Not at hne
  refine hzK (le_centralizer_of_mem (S.z_mem_centralizer_of_comm hKG hLvN fun l hl => ?_))
  have hl' : l ∈ Subgroup.closure
      {y | y ∈ L ⊓ Subgroup.centralizer ({S.v12} : Set G) ∧ ∃ m : ℕ, Odd m ∧ y ^ m = 1} := hl
  have key : l ∈ Subgroup.normalizer (K : Set G) ∧
      l * S.z * l⁻¹ * S.z⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    clear hl
    induction hl' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hy1, m, hm, hym⟩ := hy
      have hyLv : y ∈ S.Lv := Subgroup.subset_closure ⟨hy1, m, hm, hym⟩
      exact ⟨hLvN hyLv, hne y hyLv (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym))⟩
    | one => exact ⟨Subgroup.one_mem _, by simp⟩
    | mul g h _ _ ihg ihh =>
      refine ⟨Subgroup.mul_mem _ ihg.1 ihh.1, ?_⟩
      have e : g * h * S.z * (g * h)⁻¹ * S.z⁻¹ =
          g * (h * S.z * h⁻¹ * S.z⁻¹) * g⁻¹ * (g * S.z * g⁻¹ * S.z⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (conj_mem_centralizer ihg.1 ihh.2) ihg.2
    | inv g _ ihg =>
      refine ⟨Subgroup.inv_mem _ ihg.1, ?_⟩
      have e : g⁻¹ * S.z * g⁻¹⁻¹ * S.z⁻¹ = g⁻¹ * (g * S.z * g⁻¹ * S.z⁻¹)⁻¹ * g⁻¹⁻¹ := by group
      rw [e]
      exact conj_mem_centralizer (Subgroup.inv_mem _ ihg.1) (Subgroup.inv_mem _ ihg.2)
  exact key.2

theorem isSylowTwoOf_Tv_inf (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G))) :
    IsSylowTwoOf (S.Tv ⊓ (Subgroup.centralizer ({S.v12} : Set G) ⊓
      Subgroup.normalizer (K : Set G)))
      (Subgroup.centralizer ({S.v12} : Set G) ⊓ Subgroup.normalizer (K : Set G)) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hsyl : IsSylowTwoOf S.Tv Gv :=
    S.isSylowTwoOf_centralizer h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
  have hO2 := (S.lemma115Hyp_Gv h1222 h517).pCore_ne_bot
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  refine A4.isSylowTwoOf_inf_normal hsyl inf_le_left ?_
  rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hKc with hn | ⟨h2, -⟩
  · have hGN : Gv ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hn
    rw [inf_eq_left.mpr hGN]
    exact Subgroup.le_normalizer
  · rw [ncard_conjSubgroupsBy_eq_index] at h2
    have hn : ((Subgroup.normalizer (K : Set G)).subgroupOf Gv).Normal :=
      Subgroup.normal_of_index_eq_two h2
    have he : (Gv ⊓ Subgroup.normalizer (K : Set G)).subgroupOf Gv =
        (Subgroup.normalizer (K : Set G)).subgroupOf Gv := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← he] at hn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

theorem exists_conf1366 (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hinner : InducesInner S.z K) :
    ∃ (X Q : Subgroup G) (y : G), Conf1366 K X Q S.a S.z y := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hHyp := S.lemma115Hyp_Gv h1222 h517
  obtain ⟨hzN, -, hzM, -⟩ := hHyp.component_action hK
  have hzK : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G) := hzM
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hLvN := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hKc
  have hsyl : IsSylowTwoOf S.Tv Gv :=
    S.isSylowTwoOf_centralizer h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
  obtain ⟨l, hlK, hl⟩ := hinner
  have hlZ := not_mem_centralizer_of_inner hl hzK
  have hl2 := sq_mem_centralizer_of_inner S.z_sq hl hlK
  have haN := S.a_mem_normalizer hK hsyl hlK hl2 hlZ
  obtain ⟨y, hyLv, hyodd, hyz⟩ := S.exists_Lv_odd hKG hLvN hzK
  have hzTv : S.z ∈ S.Tv := (S.lemma115Hyp_Gv h1222 h517).z_mem
  have hzGv : S.z ∈ Gv := hsyl.1 hzTv
  have hTvT : S.Tv ≤ T := inf_le_left
  have hvC : ∀ k : ℤ, S.v12 ^ k ∈ Subgroup.centralizer (K : Set G) := by
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hKG hx)) k).eq
  refine ⟨Gv ⊓ Subgroup.normalizer (K : Set G), S.Tv ⊓ (Gv ⊓ Subgroup.normalizer (K : Set G)), y,
    le_inf hKG Subgroup.le_normalizer, inf_le_right,
    S.isSylowTwoOf_Tv_inf h1222 h517 h37 h38 hK, ⟨S.a_mem_Tv, S.a_mem_Gv, haN⟩,
    ⟨hzTv, hzGv, hzN⟩, S.a_sq, S.z_sq, fun t ht => ?_, fun t ht => ?_, fun haC => ?_,
    fun hzC => hzK (le_centralizer_of_mem hzC), S.mul_inv_not_mem_centralizer hKG hLvN hzK,
    ⟨l, hlK, hl⟩, hLvN hyLv, hyodd, ?_, hyz⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv (Subgroup.mem_inf.mp ht).1)
    rw [← hk]
    exact hvC k
  · have := S.conj_z_of_mem_T (hTvT (Subgroup.mem_inf.mp ht).1)
    have e : S.z * t * S.z⁻¹ * t⁻¹ = 1 := by
      calc S.z * t * S.z⁻¹ * t⁻¹ = S.z * (t * S.z * t⁻¹)⁻¹ := by group
        _ = 1 := by rw [this]; group
    rw [e]
    exact Subgroup.one_mem _
  · exact S.not_le_centralizer_a hK (le_centralizer_of_mem haC)
  · rw [S.Lv_comm_a hyLv, mul_inv_cancel]
    exact Subgroup.one_mem _

end Setting

theorem elim1366EF_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hL33 : FactConfL33)
    (hL2 : FactConfL2) (hSp : FactConfSpor) : Elim1366EF := by
  intro G _ _ T L V S hab K hK hcase
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hK.1
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have hinner : InducesInner S.z K := by
    rcases hcase with ⟨-, h⟩ | ⟨-, ⟨l, hl, hlx, -⟩⟩
    · exact h
    · exact ⟨l, hl, hlx⟩
  obtain ⟨X, Q, y, hconf⟩ := S.exists_conf1366 h1222 h517 h37 h38 hK hinner
  rcases hcase with ⟨h33 | ⟨p, hp, hp2⟩, -⟩ | ⟨⟨s, hs, he⟩, -⟩
  · exact hL33 G K X Q S.a S.z y hqs h33 hconf
  · exact hL2 G K X Q S.a S.z y p hqs hp hp2 hconf
  · exact hSp G K X Q S.a S.z y s hqs hs he hconf

end CFSG.Quasithin.H13.A5
