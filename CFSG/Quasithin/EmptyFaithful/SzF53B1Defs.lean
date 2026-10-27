module

public import CFSG.Quasithin.EmptyFaithful.SzF53Defs
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B1

section Pure

variable {G : Type*} [Group G]

theorem sup_eq_of_relIndex_two {Q X W : Subgroup G} (hQX : Q ≤ X) (h2 : Q.relIndex X = 2)
    (hWX : W ≤ X) (hWQ : ¬ W ≤ Q) : Q ⊔ W = X := by
  have hle2 : Q ⊔ W ≤ X := sup_le hQX hWX
  have hmul := Subgroup.relIndex_mul_relIndex Q (Q ⊔ W) X le_sup_left hle2
  rw [h2] at hmul
  have hne : Q.relIndex (Q ⊔ W) ≠ 1 := by
    intro h1'
    exact hWQ (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1'))
  have hdvd : Q.relIndex (Q ⊔ W) ∣ 2 := ⟨_, hmul.symm⟩
  have h2' : Q.relIndex (Q ⊔ W) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
  rw [h2'] at hmul
  have : (Q ⊔ W).relIndex X = 1 := by omega
  exact le_antisymm hle2 (Subgroup.relIndex_eq_one.mp this)

theorem commutator_sq_mem_of_relIndex_two {Q X : Subgroup G} (h2 : Q.relIndex X = 2)
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) : a * b * a⁻¹ * b⁻¹ ∈ Q ∧ a ^ 2 ∈ Q := by
  have hn : (Q.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two h2
  have hcard : Nat.card (↥X ⧸ Q.subgroupOf X) = 2 := by
    rw [← Subgroup.index_eq_card]; exact h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥X ⧸ Q.subgroupOf X) := isCyclic_of_prime_card hcard
  constructor
  · have h1 : (QuotientGroup.mk (⟨a, ha⟩ : ↥X) : ↥X ⧸ Q.subgroupOf X) *
        QuotientGroup.mk (⟨b, hb⟩ : ↥X) = QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩ :=
      IsMulCommutative.is_comm.comm _ _
    have h3 : ((⟨a, ha⟩ : ↥X) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥X)⁻¹ * (⟨b, hb⟩ : ↥X)⁻¹) ∈
        Q.subgroupOf X := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1]
      group
    exact h3
  · have h1 : (QuotientGroup.mk (⟨a, ha⟩ : ↥X) : ↥X ⧸ Q.subgroupOf X) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥X ⧸ Q.subgroupOf X) (x := QuotientGroup.mk ⟨a, ha⟩)
      rwa [hcard] at this
    have h3 : (⟨a, ha⟩ : ↥X) ^ 2 ∈ Q.subgroupOf X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact h1
    exact h3

theorem commutator_mem_of_central_index_two {X Q A : Subgroup G}
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) (hQA : Q ≤ A)
    (h2 : A.relIndex X = 2) (hc : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ Q) :
    ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ Q := by
  have hn : (Q.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQn
  let π : ↥X →* ↥X ⧸ Q.subgroupOf X := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Q.subgroupOf X := QuotientGroup.ker_mk' _
  have hcen : (A.subgroupOf X).map π ≤ Subgroup.center (↥X ⧸ Q.subgroupOf X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := hπ z
    have ha' : (a : G) ∈ A := ha
    have h1 := hc (a : G)⁻¹ (A.inv_mem ha') (x : G)⁻¹ (X.inv_mem x.2)
    rw [← map_mul, ← map_mul]
    show (QuotientGroup.mk (x * a) : ↥X ⧸ Q.subgroupOf X) = QuotientGroup.mk (a * x)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using h1
  have hidx : ((A.subgroupOf X).map π).index = 2 := by
    rw [Subgroup.index_map_eq _ hπ (by rw [hker]; exact Subgroup.subgroupOf_mono X hQA)]
    exact h2
  have hdvd : (Subgroup.center (↥X ⧸ Q.subgroupOf X)).index ∣ 2 := by
    rw [← hidx]
    exact Subgroup.index_dvd_of_le hcen
  have hcyc : IsCyclic ((↥X ⧸ Q.subgroupOf X) ⧸ Subgroup.center (↥X ⧸ Q.subgroupOf X)) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · have hc1 : Nat.card ((↥X ⧸ Q.subgroupOf X) ⧸
          Subgroup.center (↥X ⧸ Q.subgroupOf X)) = 1 := by
        rw [← Subgroup.index_eq_card]; exact h
      have : Subsingleton ((↥X ⧸ Q.subgroupOf X) ⧸ Subgroup.center (↥X ⧸ Q.subgroupOf X)) :=
        (Nat.card_eq_one_iff_unique.mp hc1).1
      exact isCyclic_of_subsingleton
    · have hc2 : Nat.card ((↥X ⧸ Q.subgroupOf X) ⧸
          Subgroup.center (↥X ⧸ Q.subgroupOf X)) = 2 := by
        rw [← Subgroup.index_eq_card]; exact h
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card hc2
  have hcomm : IsMulCommutative (↥X ⧸ Q.subgroupOf X) :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center (↥X ⧸ Q.subgroupOf X)))
      (by rw [QuotientGroup.ker_mk'])
  intro x hx y hy
  have h1 : π ⟨x, hx⟩ * π ⟨y, hy⟩ = π ⟨y, hy⟩ * π ⟨x, hx⟩ := IsMulCommutative.is_comm.comm _ _
  have h3 : ((⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥X)⁻¹ * (⟨y, hy⟩ : ↥X)⁻¹) ∈
      Q.subgroupOf X := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h1]
    group
  exact h3

theorem le_normalizer_of_commutator_le {K X : Subgroup G} (h : ⁅K, X⁆ ≤ K) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ g ∈ X, ∀ y ∈ K, g * y * g⁻¹ ∈ K := by
    intro g hg y hy
    have h1 : ⁅g, y⁆ ∈ K := by
      apply h
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hg hy
    have e : g * y * g⁻¹ = ⁅g, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem h1 hy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ (X.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem commutator_sup_le {A B C R : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (R : Set G)) (hC : C ≤ Subgroup.normalizer (R : Set G))
    (hAB : ⁅A, B⁆ ≤ R) (hAC : ⁅A, C⁆ ≤ R) : ⁅A, B ⊔ C⁆ ≤ R := by
  let N : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (R : Set G) ∧ ∀ a ∈ A, ⁅a, g⁆ ∈ R}
      one_mem' := ⟨(Subgroup.normalizer (R : Set G)).one_mem, fun a _ => by simp⟩
      mul_mem' := by
        rintro g g' ⟨hg, hgR⟩ ⟨hg', hgR'⟩
        refine ⟨(Subgroup.normalizer (R : Set G)).mul_mem hg hg', fun a ha => ?_⟩
        have e : ⁅a, g * g'⁆ = ⁅a, g⁆ * (g * ⁅a, g'⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R.mul_mem (hgR a ha) ((Subgroup.mem_normalizer_iff.mp hg _).mp (hgR' a ha))
      inv_mem' := by
        rintro g ⟨hg, hgR⟩
        refine ⟨(Subgroup.normalizer (R : Set G)).inv_mem hg, fun a ha => ?_⟩
        have e : ⁅a, g⁻¹⁆ = g⁻¹ * (⁅a, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hg) _).mp
          (R.inv_mem (hgR a ha)) }
  have hBN : B ≤ N := fun g hg => ⟨hB hg, fun a ha => Subgroup.commutator_le.mp hAB a ha g hg⟩
  have hCN : C ≤ N := fun g hg => ⟨hC hg, fun a ha => Subgroup.commutator_le.mp hAC a ha g hg⟩
  have hBC : B ⊔ C ≤ N := sup_le hBN hCN
  rw [Subgroup.commutator_le]
  intro a ha g hg
  exact (hBC hg).2 a ha

private def x5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

private theorem x5_four : x5 ^ 4 = 1 := by decide

private theorem cent_x5 : ∀ a : Equiv.Perm (Fin 5), a * x5 = x5 * a →
    a = 1 ∨ a = x5 ∨ a = x5 ^ 2 ∨ a = x5 ^ 3 := by decide +kernel

private theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

theorem exists_noncommuting_of_card_eight {P : Subgroup (Equiv.Perm (Fin 5))}
    (hP : Nat.card P = 8) : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by simpa using hP)
  have hidx : P.index = 15 := by
    have := P.card_mul_index
    rw [hP, card_perm_five] at this
    omega
  let SP : Sylow 2 (Equiv.Perm (Fin 5)) := hpg.toSylow (by rw [hidx]; decide)
  have hxpg : IsPGroup 2 (Subgroup.zpowers x5) := by
    have hod : orderOf x5 ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one x5_four
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hod
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  obtain ⟨S', hS'⟩ := hxpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) S' SP
  have hmem : g * x5 * g⁻¹ ∈ P := by
    have hxS : x5 ∈ (S' : Subgroup (Equiv.Perm (Fin 5))) := hS' (Subgroup.mem_zpowers x5)
    have h3 : g * x5 * g⁻¹ ∈ ((g • S' : Sylow 2 (Equiv.Perm (Fin 5))) :
        Subgroup (Equiv.Perm (Fin 5))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.conj_inv_apply, mul_assoc] using hxS
    rw [hg] at h3
    exact h3
  have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.zpowers x5 := by
    rintro _ ⟨a, ha, rfl⟩
    have hc : g⁻¹ * a * g * x5 = x5 * (g⁻¹ * a * g) := by
      have := hcon a ha _ hmem
      calc g⁻¹ * a * g * x5 = g⁻¹ * (a * (g * x5 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x5 * g⁻¹) * a) * g := by rw [this]
        _ = x5 * (g⁻¹ * a * g) := by group
    have hc' : (MulAut.conj g⁻¹ a) = g⁻¹ * a * g := by simp
    rw [MulEquiv.coe_toMonoidHom, hc']
    rcases cent_x5 _ hc with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hcard : Nat.card (P.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  have h4 : Nat.card (Subgroup.zpowers x5) ≤ 4 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one x5_four)
  have := Subgroup.card_le_of_le hle
  omega

end Pure

section Conj

variable {G : Type*} [Group G]

structure ZaFacts (H S Z : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 Z
  card_eq : Nat.card Z = 16
  normal : H ≤ Subgroup.normalizer (Z : Set G)
  irred : ∀ N : Subgroup G, N ≤ Z → H ≤ Subgroup.normalizer (N : Set G) → N = ⊥ ∨ N = Z
  card_fix : Nat.card ↥(Z ⊓ Subgroup.centralizer (S : Set G)) = 2
  card_comm : Nat.card ↥⁅Z, S⁆ = 8
  unique2 : ∀ Y : Subgroup G, Y ≤ S →
    S ≤ Subgroup.normalizer ((pCoreOf 2 H ⊔ Y : Subgroup G) : Set G) →
    (pCoreOf 2 H).relIndex (pCoreOf 2 H ⊔ Y) = 2 →
    Nat.card ↥⁅Z, Y⁆ = 4 ∧ ∀ U : Subgroup G, U ≤ Z →
      S ≤ Subgroup.normalizer (U : Set G) → Nat.card U = 4 → U = ⁅Z, Y⁆

theorem ZaFacts.conj {H S Z : Subgroup G} (h : ZaFacts H S Z) (x : G) :
    ZaFacts (conjSub x H) (conjSub x S) (conjSub x Z) where
  elemAbelian := F7.isElemAbelian_conjSub h.elemAbelian
  card_eq := by rw [card_conjSub]; exact h.card_eq
  normal := conjSub_le_normalizer h.normal
  irred := by
    intro N hNZ hHN
    have h1 : conjSub x⁻¹ N ≤ Z := by
      have := conjSub_mono x⁻¹ hNZ
      rwa [conjSub_conjSub_inv] at this
    have h2 : H ≤ Subgroup.normalizer ((conjSub x⁻¹ N : Subgroup G) : Set G) := by
      have := conjSub_le_normalizer (g := x⁻¹) hHN
      rwa [conjSub_conjSub_inv] at this
    rcases h.irred _ h1 h2 with h3 | h3
    · left
      exact (conjSub_eq_bot_iff x⁻¹).mp h3
    · right
      have := congrArg (conjSub x) h3
      rwa [conjSub_inv_conjSub] at this
  card_fix := by
    rw [conjSub_centralizer, ← conjSub_inf, card_conjSub]
    exact h.card_fix
  card_comm := by
    rw [conjSub_commutator, card_conjSub]
    exact h.card_comm
  unique2 := by
    intro Y hYS hSN hrel
    rw [pCoreOf_conjSub] at hSN hrel
    have hYS' : conjSub x⁻¹ Y ≤ S := by
      have := conjSub_mono x⁻¹ hYS
      rwa [conjSub_conjSub_inv] at this
    have hSN' : S ≤ Subgroup.normalizer ((pCoreOf 2 H ⊔ conjSub x⁻¹ Y : Subgroup G) : Set G) := by
      have := conjSub_le_normalizer (g := x⁻¹) hSN
      rwa [conjSub_conjSub_inv, conjSub_sup, conjSub_conjSub_inv] at this
    have hrel' : (pCoreOf 2 H).relIndex (pCoreOf 2 H ⊔ conjSub x⁻¹ Y) = 2 := by
      have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
        (conjSub x (pCoreOf 2 H)) (conjSub x (pCoreOf 2 H) ⊔ Y) (MulEquiv.injective _)
      have e1 : (conjSub x (pCoreOf 2 H)).map (MulAut.conj x⁻¹).toMonoidHom = pCoreOf 2 H :=
        conjSub_conjSub_inv x _
      have e2 : (conjSub x (pCoreOf 2 H) ⊔ Y).map (MulAut.conj x⁻¹).toMonoidHom =
          pCoreOf 2 H ⊔ conjSub x⁻¹ Y := by
        rw [Subgroup.map_sup]
        exact congrArg (· ⊔ conjSub x⁻¹ Y) e1
      rw [e1, e2] at this
      rw [this]
      exact hrel
    obtain ⟨h4, hU⟩ := h.unique2 _ hYS' hSN' hrel'
    have hY : conjSub x (conjSub x⁻¹ Y) = Y := conjSub_inv_conjSub x Y
    refine ⟨?_, fun U hUZ hSU hU4 => ?_⟩
    · have e : ⁅conjSub x Z, Y⁆ = conjSub x ⁅Z, conjSub x⁻¹ Y⁆ := by
        rw [← conjSub_commutator, hY]
      rw [e, card_conjSub]
      exact h4
    · have hU1 : conjSub x⁻¹ U ≤ Z := by
        have := conjSub_mono x⁻¹ hUZ
        rwa [conjSub_conjSub_inv] at this
      have hSU1 : S ≤ Subgroup.normalizer ((conjSub x⁻¹ U : Subgroup G) : Set G) := by
        have := conjSub_le_normalizer (g := x⁻¹) hSU
        rwa [conjSub_conjSub_inv] at this
      have hU41 : Nat.card ↥(conjSub x⁻¹ U) = 4 := by rw [card_conjSub]; exact hU4
      have h5 := hU _ hU1 hSU1 hU41
      have e : U = conjSub x (conjSub x⁻¹ U) := (conjSub_inv_conjSub x U).symm
      rw [e, h5, ← conjSub_commutator, hY]

theorem isChiefSeriesFrom_mono_left {H E U N : Subgroup G} {n : ℕ} (hEU : E ≤ U)
    (h : IsChiefSeriesFrom H E N n) : IsChiefSeriesFrom H U N n := by
  have key : ∀ {L N' : Subgroup G}, IsChiefStep H E L N' → IsChiefStep H U L N' := by
    intro L N' hs
    obtain ⟨hN, hL, hlt, hmax⟩ := hs
    refine ⟨⟨hN.1.trans hEU, hN.2⟩, ⟨hL.1.trans hEU, hL.2⟩, hlt, fun K hK hLK hKN => ?_⟩
    exact hmax K ⟨hKN.trans hN.1, hK.2⟩ hLK hKN
  induction h with
  | bot => exact .bot
  | central hs hc _ ih => exact .central (key hs) hc ih
  | noncentral hs hc _ ih => exact .noncentral (key hs) hc ih

end Conj

section Basic

variable {G : Type*} [Group G]

theorem relIndex_pCoreOf_eq_card {X : Subgroup G} {K : Type*} [Group K] (e : OTwoQuot X ≃* K) :
    (pCoreOf 2 X).relIndex X = Nat.card K := by
  have h3 : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  show ((pCoreOf 2 X).subgroupOf X).index = _
  rw [h3, Subgroup.index_eq_card]
  exact Nat.card_congr e.toEquiv

theorem pCoreOf_subgroupOf (X : Subgroup G) :
    (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X := by
  unfold pCoreOf Subgroup.subgroupOf
  exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _

theorem relIndex_eq_two_pow [Finite G] {S Q : Subgroup G} (hS : IsPGroup 2 S) :
    ∃ n : ℕ, Q.relIndex S = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.index hS (Q.subgroupOf S)

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

theorem omegaOneCenter_le (S : Subgroup G) :
    quasithinOmegaOneCenter S ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

theorem exists_involution_of_normal [Finite G] {S D : Subgroup G} (hS2 : IsPGroup 2 S)
    (hDS : D ≤ S) (hSD : S ≤ Subgroup.normalizer (D : Set G)) (hD : D ≠ ⊥) :
    ∃ z ∈ D, z ∈ Subgroup.centralizer (S : Set G) ∧ z ^ 2 = 1 ∧ z ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥S := hS2.isNilpotent
  have hDn : (D.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSD
  have hD' : D.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hD
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hbot.eq_bot_of_le hDS
  have hC : D.subgroupOf S ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hD'
  have hCp : IsPGroup 2 (D.subgroupOf S ⊓ Subgroup.center ↥S : Subgroup ↥S) :=
    hS2.to_subgroup _
  obtain ⟨n, hn⟩ := hCp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card ↥(D.subgroupOf S ⊓ Subgroup.center ↥S) = 1 := by simpa using hn
    have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hC
    omega
  have hdvd2 : 2 ∣ Nat.card ↥(D.subgroupOf S ⊓ Subgroup.center ↥S) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(D.subgroupOf S ⊓ Subgroup.center ↥S))
    2 hdvd2
  have hyD : ((y : ↥S) : G) ∈ D := y.2.1
  have hyC : ((y : ↥S) : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp y.2.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hz2 : ((y : ↥S) : G) ^ 2 = 1 := by
    have := congrArg (fun t : ↥(D.subgroupOf S ⊓ Subgroup.center ↥S) => ((t : ↥S) : G)) hy2
    simpa using this
  have hz1 : ((y : ↥S) : G) ≠ 1 := by
    intro h1
    have : y = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    rw [this, orderOf_one] at hy
    omega
  exact ⟨_, hyD, hyC, hz2, hz1⟩

theorem omegaOneCenter_ne_bot [Finite G] {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    quasithinOmegaOneCenter S ≠ ⊥ := by
  obtain ⟨z, hzS, hzC, hz2, hz1⟩ := exists_involution_of_normal hS2 le_rfl
    (fun _ hg => Subgroup.le_normalizer hg) hSne
  intro hbot
  have hmem : z ∈ quasithinOmegaOneCenter S := Subgroup.subset_closure ⟨⟨hzS, hzC⟩, hz2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

end Basic

section Hyp

variable {G : Type} [Group G] [Finite G]

structure B1Hyp (H M S : Subgroup G) : Prop where
  amalgam : F53Amalgam H M S
  b_one : ¬ VZ S H ≤ pCoreOf 2 M
  zb_central : VZ S M ≤ Subgroup.centralizer (M : Set G)
  zfacts : ZaFacts H S (VZ S H)

namespace B1Hyp

variable {H M S : Subgroup G}

theorem sylow_H (h : B1Hyp H M S) : IsSylowTwoOf S H := h.amalgam.amalgam.sylow₁

theorem sylow_M (h : B1Hyp H M S) : IsSylowTwoOf S M := h.amalgam.amalgam.sylow₂

theorem S_le_H (h : B1Hyp H M S) : S ≤ H := h.sylow_H.1

theorem S_le_M (h : B1Hyp H M S) : S ≤ M := h.sylow_M.1

theorem Qa_le_S (h : B1Hyp H M S) : pCoreOf 2 H ≤ S := isSylowTwoOf_pCoreOf_le h.sylow_H

theorem Qb_le_S (h : B1Hyp H M S) : pCoreOf 2 M ≤ S := isSylowTwoOf_pCoreOf_le h.sylow_M

theorem relIndex_Qa_H (h : B1Hyp H M S) : (pCoreOf 2 H).relIndex H = 120 := by
  obtain ⟨e⟩ := h.amalgam.quot_left
  rw [relIndex_pCoreOf_eq_card e]
  rw [Nat.card_perm]
  simp [Nat.factorial]

theorem relIndex_Qb_M (h : B1Hyp H M S) : (pCoreOf 2 M).relIndex M = 6 := by
  obtain ⟨e⟩ := h.amalgam.quot_right
  rw [relIndex_pCoreOf_eq_card e, card_perm_three]

theorem relIndex_Qa_S_and_S_H (h : B1Hyp H M S) :
    (pCoreOf 2 H).relIndex S = 8 ∧ S.relIndex H = 15 := by
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) S H h.Qa_le_S h.S_le_H
  rw [h.relIndex_Qa_H] at hmul
  obtain ⟨n, hn⟩ := relIndex_eq_two_pow (Q := pCoreOf 2 H) h.sylow_H.2.1
  have hodd : ¬ 2 ∣ S.relIndex H := F7.isSylowTwoOf_odd_relIndex h.sylow_H
  rw [hn] at hmul ⊢
  have hn3 : n ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 hlt
    have h2 : 2 ^ 4 ∣ 120 := h1.trans ⟨S.relIndex H, hmul.symm⟩
    omega
  interval_cases n <;> omega

theorem relIndex_Qb_S_and_S_M (h : B1Hyp H M S) :
    (pCoreOf 2 M).relIndex S = 2 ∧ S.relIndex M = 3 := by
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 M) S M h.Qb_le_S h.S_le_M
  rw [h.relIndex_Qb_M] at hmul
  obtain ⟨n, hn⟩ := relIndex_eq_two_pow (Q := pCoreOf 2 M) h.sylow_M.2.1
  have hodd : ¬ 2 ∣ S.relIndex M := F7.isSylowTwoOf_odd_relIndex h.sylow_M
  rw [hn] at hmul ⊢
  have hn3 : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hlt
    have h2 : 2 ^ 2 ∣ 6 := h1.trans ⟨S.relIndex M, hmul.symm⟩
    omega
  interval_cases n <;> omega

theorem relIndex_Qa_S (h : B1Hyp H M S) : (pCoreOf 2 H).relIndex S = 8 :=
  h.relIndex_Qa_S_and_S_H.1

theorem relIndex_Qb_S (h : B1Hyp H M S) : (pCoreOf 2 M).relIndex S = 2 :=
  h.relIndex_Qb_S_and_S_M.1

theorem relIndex_S_M (h : B1Hyp H M S) : S.relIndex M = 3 :=
  h.relIndex_Qb_S_and_S_M.2

theorem Za_le_centerOf (h : B1Hyp H M S) : VZ S H ≤ centerOf (pCoreOf 2 H) :=
  (conjClosure_le_centerOf_pCoreOf_of_sylowIn h.S_le_H h.sylow_H.2.1
    (F7.isSylowTwoOf_odd_relIndex h.sylow_H) h.amalgam.amalgam.charTwo (le_refl _)).1

theorem Za_le_Qa (h : B1Hyp H M S) : VZ S H ≤ pCoreOf 2 H := fun _ hz => (h.Za_le_centerOf hz).1

theorem Za_le_centralizer_Qa (h : B1Hyp H M S) :
    VZ S H ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := fun _ hz => (h.Za_le_centerOf hz).2

theorem Za_le_S (h : B1Hyp H M S) : VZ S H ≤ S := h.Za_le_Qa.trans h.Qa_le_S

theorem H_le_normalizer_Za (_h : B1Hyp H M S) :
    H ≤ Subgroup.normalizer (VZ S H : Set G) := le_normalizer_conjClosure _ _

theorem M_le_normalizer_Zb (_h : B1Hyp H M S) :
    M ≤ Subgroup.normalizer (VZ S M : Set G) := le_normalizer_conjClosure _ _

theorem H_le_normalizer_Qa (_h : B1Hyp H M S) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H

theorem M_le_normalizer_Qb (_h : B1Hyp H M S) :
    M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M

theorem Zb_eq (h : B1Hyp H M S) : VZ S M = quasithinOmegaOneCenter S := by
  apply le_antisymm
  · refine conjClosure_le fun m hm z hz => ?_
    have hzV : z ∈ VZ S M := le_conjClosure _ _ hz
    have hc := Subgroup.mem_centralizer_iff.mp (h.zb_central hzV) m hm
    have : m * z * m⁻¹ = z := by rw [hc]; group
    rw [this]
    exact hz
  · exact le_conjClosure _ _

theorem Zb_le_Za (h : B1Hyp H M S) : VZ S M ≤ VZ S H := by
  rw [h.Zb_eq]
  exact le_conjClosure _ _

theorem S_ne_bot (h : B1Hyp H M S) : S ≠ ⊥ := by
  intro hS
  have h2 := h.relIndex_Qb_S
  have : S ≤ pCoreOf 2 M := hS ▸ bot_le
  have := Subgroup.relIndex_eq_one.mpr this
  omega

theorem Zb_ne_bot (h : B1Hyp H M S) : VZ S M ≠ ⊥ := by
  rw [h.Zb_eq]
  exact omegaOneCenter_ne_bot h.sylow_M.2.1 h.S_ne_bot

theorem Zb_eq_inf_centralizer (h : B1Hyp H M S) :
    VZ S M = VZ S H ⊓ Subgroup.centralizer (S : Set G) := by
  have hle : VZ S M ≤ VZ S H ⊓ Subgroup.centralizer (S : Set G) := by
    refine le_inf h.Zb_le_Za ?_
    rw [h.Zb_eq]
    exact (omegaOneCenter_le S).trans inf_le_right
  have hcard : Nat.card (VZ S M) = 2 := by
    have h1 : Nat.card (VZ S M) ≤ 2 := by
      have := Subgroup.card_le_of_le hle
      rwa [h.zfacts.card_fix] at this
    have h2 : 1 < Nat.card (VZ S M) := (Subgroup.one_lt_card_iff_ne_bot _).mpr h.Zb_ne_bot
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.zfacts.card_fix])

theorem card_Zb (h : B1Hyp H M S) : Nat.card (VZ S M) = 2 := by
  rw [h.Zb_eq_inf_centralizer]
  exact h.zfacts.card_fix

theorem exists_x (h : B1Hyp H M S) : ∃ x ∈ M, x ∉ H := by
  by_contra hcon
  push Not at hcon
  have hMS : M ≤ S := fun m hm => h.amalgam.inf_eq ▸ ⟨hcon m hm, hm⟩
  have := Subgroup.relIndex_eq_one.mpr hMS
  have h3 := h.relIndex_S_M
  omega

theorem not_mem_S (h : B1Hyp H M S) {x : G} (hxH : x ∉ H) : x ∉ S := fun hx => hxH (h.S_le_H hx)

theorem normalizer_S (h : B1Hyp H M S) : ∀ x ∈ M, conjSub x S = S → x ∈ S := by
  intro x hxM hx
  have hSM := h.S_le_M
  have hxN : x ∈ Subgroup.normalizer (S : Set G) := mem_normalizer_of_conjSub_eq hx
  have h2 := h.relIndex_Qb_S
  have h3 := h.relIndex_S_M
  have hle : S ≤ M ⊓ Subgroup.normalizer (S : Set G) := le_inf hSM Subgroup.le_normalizer
  have hmul := Subgroup.relIndex_mul_relIndex S (M ⊓ Subgroup.normalizer (S : Set G)) M hle
    inf_le_left
  rw [h3] at hmul
  have hdvd : (M ⊓ Subgroup.normalizer (S : Set G)).relIndex M ∣ 3 := ⟨_, by rw [← hmul]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exfalso
    have hMN : M ≤ Subgroup.normalizer (S : Set G) := fun m hm => by
      have := Subgroup.relIndex_eq_one.mp h1 hm
      exact this.2
    have hSQ : S ≤ pCoreOf 2 M := le_pCoreOf_of_le_normalizer 2 hSM hMN h.sylow_M.2.1
    have := Subgroup.relIndex_eq_one.mpr hSQ
    omega
  · rw [h1] at hmul
    have h1' : S.relIndex (M ⊓ Subgroup.normalizer (S : Set G)) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1' ⟨hxM, hxN⟩

theorem sup_conj_S (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxS : x ∉ S) :
    S ⊔ conjSub x S = M := by
  have hSM := h.S_le_M
  have hxM : conjSub x S ≤ M := by
    have := conjSub_mono x hSM
    rwa [F7.conjSub_eq_of_mem hx] at this
  have hnot : ¬ conjSub x S ≤ S := by
    intro hle
    have heq : conjSub x S = S :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
    exact hxS (h.normalizer_S x hx heq)
  have hle2 : S ⊔ conjSub x S ≤ M := sup_le hSM hxM
  have hmul := Subgroup.relIndex_mul_relIndex S (S ⊔ conjSub x S) M le_sup_left hle2
  rw [h.relIndex_S_M] at hmul
  have hne : S.relIndex (S ⊔ conjSub x S) ≠ 1 := fun h1 =>
    hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1))
  have hdvd : S.relIndex (S ⊔ conjSub x S) ∣ 3 := ⟨_, hmul.symm⟩
  have h3 : S.relIndex (S ⊔ conjSub x S) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  rw [h3] at hmul
  have : (S ⊔ conjSub x S).relIndex M = 1 := by omega
  exact le_antisymm hle2 (Subgroup.relIndex_eq_one.mp this)

theorem exists_commutator_not_mem_Qa (h : B1Hyp H M S) :
    ∃ a ∈ S, ∃ b ∈ S, a * b * a⁻¹ * b⁻¹ ∉ pCoreOf 2 H := by
  obtain ⟨ι⟩ := h.amalgam.quot_left
  let f : ↥S →* Equiv.Perm (Fin 5) :=
    ι.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)).comp
      (Subgroup.inclusion h.S_le_H))
  have hker : f.ker = (pCoreOf 2 H).subgroupOf S := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ι (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) (Subgroup.inclusion h.S_le_H a)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have := pCoreOf_subgroupOf H
    constructor
    · intro hh
      have h2 : Subgroup.inclusion h.S_le_H a ∈ (pCoreOf 2 H).subgroupOf H := by
        rw [this]; exact hh
      exact h2
    · intro hh
      rw [← this]
      exact hh
  have hcard : Nat.card f.range = 8 := by
    rw [← Subgroup.index_ker, hker]
    exact h.relIndex_Qa_S
  obtain ⟨a, ha, b, hb, hne⟩ := exists_noncommuting_of_card_eight hcard
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  refine ⟨a', a'.2, b', b'.2, fun hmem => hne ?_⟩
  have h1 : (a' * b' * a'⁻¹ * b'⁻¹ : ↥S) ∈ f.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hmem
  rw [MonoidHom.mem_ker] at h1
  simp only [map_mul, map_inv] at h1
  have h2 : f a' * f b' * (f a')⁻¹ = f b' := mul_inv_eq_one.mp h1
  calc f a' * f b' = f a' * f b' * (f a')⁻¹ * f a' := by group
    _ = f b' * f a' := by rw [h2]

end B1Hyp

end Hyp

end F53B1

end CFSG.Quasithin
