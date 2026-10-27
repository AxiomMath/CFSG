module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.GroupTheory.PCore.Transport
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.ASInputs

namespace C113

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pCore_eq_open_core (p : ℕ) (K : Type*) [Group K] :
    CFSG.pCore p K = CFSG.Open.pCore p K := (CFSG.Open.pCore_eq_pCore p K).symm

theorem pCoreOf_subgroupOf (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L

theorem L_le_normalizer_blockQ (L : Subgroup G) :
    L ≤ Subgroup.normalizer ((blockQ L : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L

theorem blockQ_le (L : Subgroup G) : blockQ L ≤ L := by
  rw [blockQ, pCoreOf]
  exact Subgroup.map_subtype_le _

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hH, Subgroup.mem_normalizer_iff_map_conj_eq.mp hK]

theorem L_le_normalizer_blockU (L : Subgroup G) :
    L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_commutator (L_le_normalizer_blockQ L hx) (Subgroup.le_normalizer hx)

theorem blockU_le_blockQ (L : Subgroup G) : blockU L ≤ blockQ L := by
  rw [blockU, Subgroup.commutator_le]
  intro p hp l hl
  have h1 : l * p⁻¹ * l⁻¹ ∈ blockQ L :=
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockQ L hl) p⁻¹).mp
      (Subgroup.inv_mem _ hp)
  rw [commutatorElement_def]
  have h2 := Subgroup.mul_mem _ hp h1
  simpa [mul_assoc] using h2

theorem commutator_mem_blockU {L : Subgroup G} {p l : G} (hp : p ∈ blockQ L) (hl : l ∈ L) :
    p * l * p⁻¹ * l⁻¹ ∈ blockU L := by
  have := Subgroup.commutator_mem_commutator hp hl
  rwa [commutatorElement_def] at this

theorem mem_normalizer_of_map_le [Finite G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge h
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_pow_eq_one_of_mem_blockQ [Finite G] {L : Subgroup G} {p : G}
    (hp : p ∈ blockQ L) : ∃ c : ℕ, p ^ 2 ^ c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨p, hp⟩
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

theorem pCoreOf_eq_blockU_of_card_three [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) : pCoreOf 2 L = blockU L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := pCoreOf 2 L with hP
  set U := blockU L with hU
  have hPL : P ≤ L := blockQ_le L
  have hUP : U ≤ P := blockU_le_blockQ L
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hcyc : IsCyclic (↥L ⧸ CFSG.pCore 2 ↥L) := isCyclic_of_prime_card h3
  obtain ⟨gb, hgb⟩ := IsCyclic.exists_generator (α := ↥L ⧸ CFSG.pCore 2 ↥L)
  have hgbord : orderOf gb = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgb, h3]
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) gb
  obtain ⟨b, r, hr, hbr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₀).ne'
  set g : ↥L := g₀ ^ 2 ^ b with hg
  have hgodd : Odd (orderOf g) := by
    rw [hg, orderOf_pow' g₀ (pow_ne_zero _ two_ne_zero), hbr, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left r (Nat.two_pow_pos b)]
    exact hr
  have hgen : ∀ x : ↥L ⧸ CFSG.pCore 2 ↥L, x ∈ Subgroup.zpowers (π g) := by
    have hord : orderOf (π g) = 3 := by
      rw [hg, map_pow, hπ, hg₀, Nat.Coprime.orderOf_pow, hgbord]
      rw [hgbord]
      exact Nat.Coprime.pow_right b (by norm_num)
    intro x
    have hcard : Nat.card ↥(Subgroup.zpowers (π g)) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [Nat.card_zpowers, hord, h3]
    rw [Subgroup.eq_top_of_card_eq _ hcard]
    exact Subgroup.mem_top x
  have hdecomp : ∀ l : ↥L, ∃ i : ℤ, (g⁻¹ ^ i * l : ↥L) ∈ CFSG.pCore 2 ↥L := by
    intro l
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen (π l))
    refine ⟨i, ?_⟩
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_zpow, map_inv, ← hπ,
      ← hi]
    group
  set N : Subgroup G := Subgroup.zpowers (g : G) ⊔ U with hN
  have hNL : N ≤ L := sup_le ((Subgroup.zpowers_le).mpr g.2) (hUP.trans hPL)
  have hgU : (g : G) ∈ Subgroup.normalizer (U : Set G) := L_le_normalizer_blockU L g.2
  have hPN : ∀ p ∈ P, p ∈ Subgroup.normalizer (N : Set G) := by
    intro p hp
    have hpL : p ∈ L := hPL hp
    apply mem_normalizer_of_map_le
    rw [hN, Subgroup.map_sup]
    have hUmap : U.map (MulAut.conj p).toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hpL) u).mp hu
    refine sup_le ?_ (hUmap.trans le_sup_right)
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    have hc := commutator_mem_blockU hp g.2
    have e : (MulAut.conj p).toMonoidHom (g : G) = (p * g * p⁻¹ * (g : G)⁻¹) * g := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hdecomp' : ∀ l : ↥L, ∃ i : ℤ, ((g : G)⁻¹ ^ i * l) ∈ P := by
    intro l
    obtain ⟨i, hi⟩ := hdecomp l
    refine ⟨i, ?_⟩
    have : ((g⁻¹ ^ i * l : ↥L) : G) ∈ P := by
      rw [hP, ← Subgroup.mem_subgroupOf, pCoreOf_subgroupOf]
      exact hi
    simpa using this
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
    intro l hl
    obtain ⟨i, hi⟩ := hdecomp' ⟨l, hl⟩
    have e : l = (g : G) ^ i * ((g : G)⁻¹ ^ i * l) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.mem_sup_left
      (Subgroup.zpow_mem_zpowers _ i))) (hPN _ hi)
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have h2 : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨i, hi⟩ := hdecomp' l
    obtain ⟨c, hc⟩ := exists_pow_eq_one_of_mem_blockQ (L := L) hi
    refine ⟨c, ?_⟩
    have hgi : (g⁻¹ ^ i : ↥L) ∈ N.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      have : ((g⁻¹ ^ i : ↥L) : G) = ((g : G) ^ i)⁻¹ := by simp
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ i))
    have e : (QuotientGroup.mk l : ↥L ⧸ N.subgroupOf L) =
        QuotientGroup.mk (g⁻¹ ^ i * l) := by
      rw [QuotientGroup.eq]
      have h1 := hNn.conj_mem _ hgi l⁻¹
      rw [inv_inv] at h1
      simpa [mul_assoc] using h1
    have hp1 : (g⁻¹ ^ i * l : ↥L) ^ 2 ^ c = 1 := by
      apply Subtype.ext
      simpa using hc
    rw [e, ← QuotientGroup.mk_pow, hp1, QuotientGroup.mk_one]
  have htop : N.subgroupOf L = ⊤ := hL.1 (N.subgroupOf L) h2
  have hLN' : L ≤ N := by
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ N.subgroupOf L := by
      rw [htop]
      exact Subgroup.mem_top _
    exact this
  apply le_antisymm _ hUP
  intro x hx
  have hxN : x ∈ ((N : Subgroup G) : Set G) := hLN' (hPL hx)
  have hzU : Subgroup.zpowers (g : G) ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le).mpr hgU
  rw [hN, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzU] at hxN
  obtain ⟨a, ha, u, hu, rfl⟩ := hxN
  have haP : a ∈ P := by
    have : a = a * u * u⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hUP hu))
  obtain ⟨c, hc⟩ := exists_pow_eq_one_of_mem_blockQ (L := L) haP
  have hd1 : orderOf a ∣ 2 ^ c := orderOf_dvd_of_pow_eq_one hc
  have hd2 : orderOf a ∣ orderOf (g : G) := orderOf_dvd_of_mem_zpowers ha
  rw [Subgroup.orderOf_coe] at hd2
  have hcop : Nat.Coprime (2 ^ c) (orderOf g) :=
    Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr hgodd)
  have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  subst ha1
  simpa using hu

theorem commutator_eq_top_of_isShort2 [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : commutator ↥L = ⊤ := by
  have hperf := Group.isPerfect_def.mp hq.1
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π
      (QuotientGroup.mk'_surjective _), ← commutator_def, hperf]
  refine hL.1 (commutator ↥L) fun x => ?_
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have hl : π l ∈ (commutator ↥L).map π := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hnl⟩ := hl
  have hp : n⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hnl,
      inv_mul_cancel]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup ⟨_, hp⟩
  refine ⟨c, ?_⟩
  have e : (QuotientGroup.mk l : ↥L ⧸ commutator ↥L) = QuotientGroup.mk (n⁻¹ * l) := by
    rw [QuotientGroup.eq]
    have : l⁻¹ * (n⁻¹ * l) = l⁻¹ * n⁻¹ * l⁻¹⁻¹ := by group
    rw [this]
    exact (inferInstance : (commutator ↥L).Normal).conj_mem _ (Subgroup.inv_mem _ hn) l⁻¹
  have hc' : (n⁻¹ * l) ^ 2 ^ c = 1 := by
    simpa using congrArg Subtype.val hc
  rw [e, ← QuotientGroup.mk_pow, hc', QuotientGroup.mk_one]

theorem exists_hopf_surjective [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ (_ : ((blockU L).subgroupOf (pCoreOf 2 L)).Normal)
      (f : CFSG.Open.griessHopfMultiplier (↥L ⧸ CFSG.pCore 2 ↥L) →*
        ↥(pCoreOf 2 L) ⧸ (blockU L).subgroupOf (pCoreOf 2 L)), Function.Surjective f := by
  classical
  have hPL : pCoreOf 2 L ≤ L := blockQ_le L
  have hUP : blockU L ≤ pCoreOf 2 L := blockU_le_blockQ L
  have hU' : ((blockU L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hUP.trans hPL)).mpr (L_le_normalizer_blockU L)
  have hU'' : ((blockU L).subgroupOf (pCoreOf 2 L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mpr
      (hPL.trans (L_le_normalizer_blockU L))
  refine ⟨hU'', ?_⟩
  set U' := (blockU L).subgroupOf L with hU'def
  set U'' := (blockU L).subgroupOf (pCoreOf 2 L) with hU''def
  have hU'P : U' ≤ (CFSG.pCore 2 ↥L).comap (MonoidHom.id ↥L) := by
    intro x hx
    rw [Subgroup.comap_id, ← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
    exact hUP hx
  let q : ↥L ⧸ U' →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    QuotientGroup.map U' (CFSG.pCore 2 ↥L) (MonoidHom.id ↥L) hU'P
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hqmk : ∀ l : ↥L, q (QuotientGroup.mk l) = QuotientGroup.mk l := fun _ => rfl
  have hperf : Group.IsPerfect (↥L ⧸ U') := by
    rw [Group.isPerfect_def, commutator_def, ← Subgroup.map_top_of_surjective
      (QuotientGroup.mk' U') (QuotientGroup.mk'_surjective _), ← Subgroup.map_commutator,
      ← commutator_def, commutator_eq_top_of_isShort2 hL hq]
  have hker : q.ker ≤ Subgroup.center (↥L ⧸ U') := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hlP : (l : G) ∈ pCoreOf 2 L := by
      rw [MonoidHom.mem_ker, hqmk, QuotientGroup.eq_one_iff] at hx
      rw [← Subgroup.mem_subgroupOf, pCoreOf_subgroupOf]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hc := commutator_mem_blockU (L := L) hlP m.2
    have hc' : (l : G)⁻¹ * (m : G)⁻¹ * l * m ∈ blockU L := by
      have h1 : (l : G)⁻¹ ∈ pCoreOf 2 L := Subgroup.inv_mem _ hlP
      have h2 := commutator_mem_blockU (L := L) h1 (Subgroup.inv_mem _ m.2)
      simpa using h2
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hc'
  let ι : ↥(pCoreOf 2 L) →* ↥L := Subgroup.inclusion hPL
  have hιU : U'' ≤ U'.comap ι := fun x hx => hx
  let ψ : ↥(pCoreOf 2 L) ⧸ U'' →* ↥L ⧸ U' := QuotientGroup.map U'' U' ι hιU
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  have hψrange : ψ.range = q.ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MonoidHom.mem_ker]
      show q (QuotientGroup.mk (ι p)) = 1
      rw [hqmk, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
      exact p.2
    · intro hx
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      have hlP : (l : G) ∈ pCoreOf 2 L := by
        rw [MonoidHom.mem_ker, hqmk, QuotientGroup.eq_one_iff] at hx
        rw [← Subgroup.mem_subgroupOf, pCoreOf_subgroupOf]
        exact hx
      exact ⟨QuotientGroup.mk ⟨l, hlP⟩, rfl⟩
  let e : ↥(pCoreOf 2 L) ⧸ U'' ≃* ↥q.ker :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)
  refine ⟨e.symm.toMonoidHom.comp ((CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hqs hker).comp
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toMonoidHom), ?_⟩
  exact e.symm.surjective.comp ((CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs
    hker).comp (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).surjective)

section Action

variable {L T : Subgroup G}

@[expose] def dlt (g u : G) : G := g * u * g⁻¹ * u⁻¹

theorem dlt_def (g u : G) : dlt g u = g * u * g⁻¹ * u⁻¹ := rfl

theorem blockU_comm (hL : IsShort2 L) {u v : G} (hu : u ∈ blockU L) (hv : v ∈ blockU L) :
    u * v = v * u := by
  have hv' : v ∈ Subgroup.centralizer ((blockQ L : Subgroup G) : Set G) := (hL.2.2.1.1 hv).2
  exact (Subgroup.mem_centralizer_iff.mp hv' u (blockU_le_blockQ L hu))

theorem blockU_sq (hL : IsShort2 L) {u : G} (hu : u ∈ blockU L) : u * u = 1 := by
  have := hL.2.2.1.2 u hu
  rwa [pow_two] at this

theorem dlt_mul (hL : IsShort2 L) {g u v : G}
    (hg : g ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G))
    (hu : u ∈ blockU L) (hv : v ∈ blockU L) : dlt g (u * v) = dlt g u * dlt g v := by
  have hgu : g * u * g⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have hgv : g * v * g⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  have hc1 := blockU_comm hL hgv (Subgroup.inv_mem _ hu)
  have hc2 := blockU_comm hL (Subgroup.inv_mem _ hu) (Subgroup.inv_mem _ hv)
  simp only [dlt_def]
  calc g * (u * v) * g⁻¹ * (u * v)⁻¹ = (g * u * g⁻¹) * ((g * v * g⁻¹) * v⁻¹ * u⁻¹) := by group
    _ = (g * u * g⁻¹) * ((g * v * g⁻¹) * (u⁻¹ * v⁻¹)) := by
        rw [mul_assoc (g * v * g⁻¹), hc2.symm]
    _ = (g * u * g⁻¹) * (u⁻¹ * (g * v * g⁻¹) * v⁻¹) := by
        rw [← mul_assoc (g * v * g⁻¹), hc1, mul_assoc]
    _ = g * u * g⁻¹ * u⁻¹ * (g * v * g⁻¹ * v⁻¹) := by group

theorem dlt_mem {g : G} (hg : ∀ u ∈ blockU L, g * u * g⁻¹ ∈ blockU L) {u : G}
    (hu : u ∈ blockU L) :
    dlt g u ∈ blockU L :=
  Subgroup.mul_mem _ (hg u hu) (Subgroup.inv_mem _ hu)

theorem dlt_sq (hL : IsShort2 L) {g u : G}
    (hg : g ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G)) (hu : u ∈ blockU L) :
    dlt (g * g) u = dlt g (dlt g u) := by
  have hgU : ∀ v ∈ blockU L, g * v * g⁻¹ ∈ blockU L := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  have hd := dlt_mem hgU hu
  have e1 : g * u * g⁻¹ = dlt g u * u := by simp [dlt_def]
  have e2 : dlt (g * g) u = (g * (dlt g u * u) * g⁻¹) * u⁻¹ := by
    rw [← e1]
    simp only [dlt_def]
    group
  rw [e2]
  have e3 : g * (dlt g u * u) * g⁻¹ = dlt g (dlt g u) * dlt g u * (dlt g u * u) := by
    have h1 : g * (dlt g u * u) * g⁻¹ = dlt g (dlt g u * u) * (dlt g u * u) := by
      simp only [dlt_def]
      group
    rw [h1, dlt_mul hL hg hd hu]
  rw [e3]
  have hsq := blockU_sq hL hd
  calc dlt g (dlt g u) * dlt g u * (dlt g u * u) * u⁻¹ =
      dlt g (dlt g u) * (dlt g u * dlt g u) := by group
    _ = dlt g (dlt g u) := by rw [hsq, mul_one]

theorem dlt_pow_two_pow (hL : IsShort2 L) {g : G}
    (hg : g ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G)) (j : ℕ) :
    ∀ u ∈ blockU L, dlt (g ^ 2 ^ j) u = (dlt g)^[2 ^ j] u := by
  induction j with
  | zero =>
    intro u hu
    simp
  | succ j ih =>
    intro u hu
    have hgj : g ^ 2 ^ j ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
      Subgroup.pow_mem _ hg _
    have hgU : ∀ v ∈ blockU L, g * v * g⁻¹ ∈ blockU L := fun v hv =>
      (Subgroup.mem_normalizer_iff.mp hg v).mp hv
    have hiter : ∀ (k : ℕ) (v : G), v ∈ blockU L → (dlt g)^[k] v ∈ blockU L := by
      intro k
      induction k with
      | zero => intro v hv; simpa using hv
      | succ k ihk =>
        intro v hv
        rw [Function.iterate_succ_apply']
        exact dlt_mem hgU (ihk v hv)
    rw [pow_succ, pow_mul, sq, dlt_sq hL hgj hu, ih u hu,
      ih _ (hiter _ u hu), ← Function.iterate_add_apply]
    congr 1
    ring

end Action

section Stability

variable {L : Subgroup G}

theorem forall_mem_of_pow (hno : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    {X Y : Subgroup G} (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hpow : ∀ l ∈ L, ∃ k : ℕ, ∀ x ∈ X, l ^ 2 ^ k * x * (l ^ 2 ^ k)⁻¹ * x⁻¹ ∈ Y) :
    ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ * x⁻¹ ∈ Y := by
  let N : Subgroup ↥L :=
    { carrier := {a | ∀ x ∈ X, (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ Y}
      mul_mem' := fun {a b} ha hb x hx => by
        have h1 := hb x hx
        have h2 := ha x hx
        have h3 : (a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hLY a.2) _).mp h1
        have e : ((a * b : ↥L) : G) * x * ((a * b : ↥L) : G)⁻¹ * x⁻¹ =
            ((a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹) *
              ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e]
        exact Subgroup.mul_mem _ h3 h2
      one_mem' := fun x _ => by simp
      inv_mem' := fun {a} ha x hx => by
        have hx' : (a : G)⁻¹ * x * (a : G) ∈ X := by
          have := (Subgroup.mem_normalizer_iff.mp (hLX (Subgroup.inv_mem _ a.2)) x).mp hx
          simpa using this
        have h1 := ha _ hx'
        have e : ((a⁻¹ : ↥L) : G) * x * ((a⁻¹ : ↥L) : G)⁻¹ * x⁻¹ =
            ((a : G) * ((a : G)⁻¹ * x * (a : G)) * (a : G)⁻¹ *
              ((a : G)⁻¹ * x * (a : G))⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        rw [e]
        exact Subgroup.inv_mem _ h1 }
  have hNn : N.Normal := by
    refine ⟨fun a ha b x hx => ?_⟩
    have hx' : (b : G)⁻¹ * x * (b : G) ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hLX (Subgroup.inv_mem _ b.2)) x).mp hx
      simpa using this
    have h1 := ha _ hx'
    have h2 : (b : G) * ((a : G) * ((b : G)⁻¹ * x * (b : G)) * (a : G)⁻¹ *
        ((b : G)⁻¹ * x * (b : G))⁻¹) * (b : G)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hLY b.2) _).mp h1
    have e : ((b * a * b⁻¹ : ↥L) : G) * x * ((b * a * b⁻¹ : ↥L) : G)⁻¹ * x⁻¹ =
        (b : G) * ((a : G) * ((b : G)⁻¹ * x * (b : G)) * (a : G)⁻¹ *
          ((b : G)⁻¹ * x * (b : G))⁻¹) * (b : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show _ ∈ Y
    rw [e]
    exact h2
  have h2 : IsPGroup 2 (↥L ⧸ N) := by
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := hpow l l.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    intro x hx
    simpa using hk x hx
  have htop := hno N h2
  intro l hl x hx
  have : (⟨l, hl⟩ : ↥L) ∈ N := by
    rw [htop]
    exact Subgroup.mem_top _
  exact this x hx

end Stability

section QAction

variable {L T : Subgroup G}

theorem mem_normalizer_inf' {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH x, hK x]

theorem mem_normalizer_centralizer' {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) h).mp hh
      simpa using this
    have := hx _ hh'
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * h := by group
  · intro hx h hh
    have hh' : g * h * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
    have := hx _ hh'
    calc h * x = g⁻¹ * ((g * h * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * h * g⁻¹)) * g := by rw [this]
      _ = x * h := by group

theorem commutator_blockU_le (L : Subgroup G) : ⁅blockU L, L⁆ ≤ blockU L := by
  rw [Subgroup.commutator_le]
  intro u hu l hl
  have h1 : l * u⁻¹ * l⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hl) u⁻¹).mp (Subgroup.inv_mem _ hu)
  rw [commutatorElement_def]
  have h2 := Subgroup.mul_mem _ hu h1
  simpa [mul_assoc] using h2

theorem blockU_eq_commutator [Finite G] (hL : IsShort2 L) : blockU L = ⁅blockU L, L⁆ := by
  have hLU₂ : L ≤ Subgroup.normalizer ((⁅blockU L, L⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (L_le_normalizer_blockU L hx) (Subgroup.le_normalizer hx)
  have key := forall_mem_of_pow hL.1 (L_le_normalizer_blockQ L) hLU₂ (fun l hl => ⟨1, ?_⟩)
  · apply le_antisymm _ (commutator_blockU_le L)
    show ⁅blockQ L, L⁆ ≤ ⁅blockU L, L⁆
    rw [Subgroup.commutator_le]
    intro p hp l hl
    have h := Subgroup.inv_mem _ (key l hl p hp)
    rw [commutatorElement_def]
    simpa [mul_assoc] using h
  · intro p hp
    set d := l * p * l⁻¹ * p⁻¹ with hd
    have hdU : d ∈ blockU L := by
      have := Subgroup.inv_mem _ (commutator_mem_blockU hp hl)
      rw [hd]
      simpa [mul_assoc] using this
    have hd2 : d * d = 1 := blockU_sq hL hdU
    have hc : l * d * l⁻¹ * d⁻¹ ∈ ⁅blockU L, L⁆ := by
      have := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hdU hl)
      rw [commutatorElement_def] at this
      simpa [mul_assoc] using this
    have e : l ^ 2 ^ 1 * p * (l ^ 2 ^ 1)⁻¹ * p⁻¹ = (l * d * l⁻¹ * d⁻¹) * (d * d) := by
      rw [hd, pow_one, sq]
      group
    rw [e, hd2, mul_one]
    exact hc

theorem sup_le_normalizer_L (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le (fun _ hx => Subgroup.le_normalizer hx) hTL

theorem sup_le_normalizer_blockQ (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer ((blockQ L : Subgroup G) : Set G) :=
  (sup_le_normalizer_L hTL).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem sup_le_normalizer_blockU (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_commutator (sup_le_normalizer_blockQ hTL hx) (sup_le_normalizer_L hTL hx)

theorem Q_le_sup (L T : Subgroup G) : pCoreOf 2 (L ⊔ T) ≤ L ⊔ T := by
  rw [pCoreOf]
  exact Subgroup.map_subtype_le _

theorem commutator_Q_mem_blockQ [Finite G] (hTL : T ≤ Subgroup.normalizer (L : Set G)) {q l : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hl : l ∈ L) : q * l * q⁻¹ * l⁻¹ ∈ blockQ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqN : q ∈ Subgroup.normalizer (L : Set G) := sup_le_normalizer_L hTL (Q_le_sup L T hq)
  have hQN : L ⊔ T ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have h1 : q * l * q⁻¹ * l⁻¹ ∈ L :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hqN l).mp hl) (Subgroup.inv_mem _ hl)
  have h2 : q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
    have h3 : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hQN (Subgroup.mem_sup_left hl)) q⁻¹).mp
        (Subgroup.inv_mem _ hq)
    have h4 := Subgroup.mul_mem _ hq h3
    simpa [mul_assoc] using h4
  have hle : pCoreOf 2 (L ⊔ T) ⊓ L ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro x hx
    exact mem_normalizer_inf' (hQN (Subgroup.mem_sup_left hx)) (Subgroup.le_normalizer hx)
  exact hle ⟨h2, h1⟩

end QAction

section QCent

variable {L T : Subgroup G}

theorem Q_le_normalizer_blockU (hTL : T ≤ Subgroup.normalizer (L : Set G)) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) : q ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
  sup_le_normalizer_blockU hTL (Q_le_sup L T hq)

theorem Q_le_normalizer_blockZ (hTL : T ≤ Subgroup.normalizer (L : Set G)) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) : q ∈ Subgroup.normalizer ((blockZ L : Subgroup G) : Set G) :=
  mem_normalizer_inf' (Q_le_normalizer_blockU hTL hq)
    (mem_normalizer_centralizer' (sup_le_normalizer_L hTL (Q_le_sup L T hq)))

theorem dlt_conj [Finite G] (hL : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {q l y : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hl : l ∈ L) (hy : y ∈ blockU L) :
    dlt q (l * y * l⁻¹) = l * dlt q y * l⁻¹ := by
  set v := q * l * q⁻¹ * l⁻¹ with hv
  have hvP : v ∈ blockQ L := commutator_Q_mem_blockQ hTL hq hl
  have hqy : q * y * q⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (Q_le_normalizer_blockU hTL hq) y).mp hy
  set w := l * (q * y * q⁻¹) * l⁻¹ with hw
  have hwU : w ∈ blockU L := (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hl) _).mp hqy
  have hvw : v * w = w * v :=
    Subgroup.mem_centralizer_iff.mp (hL.2.2.1.1 hwU).2 v hvP
  calc dlt q (l * y * l⁻¹) = v * w * v⁻¹ * (l * y * l⁻¹)⁻¹ := by
        rw [hv, hw, dlt_def]
        group
    _ = w * (l * y * l⁻¹)⁻¹ := by rw [hvw]; group
    _ = l * dlt q y * l⁻¹ := by rw [hw, dlt_def]; group

theorem dlt_mem_blockZ [Finite G] (hL : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {q u : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hu : u ∈ blockU L) : dlt q u ∈ blockZ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqU := Q_le_normalizer_blockU hTL hq
  have hqZ := Q_le_normalizer_blockZ hTL hq
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hdltU : ∀ v ∈ blockU L, dlt q v ∈ blockU L := fun v hv =>
    dlt_mem (fun w hw => (Subgroup.mem_normalizer_iff.mp hqU w).mp hw) hv
  have hdinv : ∀ v ∈ blockU L, dlt q v⁻¹ = (dlt q v)⁻¹ := by
    intro v hv
    have h1 := dlt_mul hL hqU hv (Subgroup.inv_mem _ hv)
    rw [mul_inv_cancel, show dlt q 1 = 1 by simp [dlt_def]] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  let X : Subgroup G :=
    { carrier := {v | v ∈ blockU L ∧ dlt q v ∈ blockZ L}
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        rw [dlt_mul hL hqU ha.1 hb.1]
        exact Subgroup.mul_mem _ ha.2 hb.2⟩
      one_mem' := ⟨Subgroup.one_mem _, by simp [dlt_def]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
        rw [hdinv a ha.1]
        exact Subgroup.inv_mem _ ha.2⟩ }
  have hZX : blockZ L ≤ X := by
    intro z hz
    refine ⟨hZU hz, Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hqZ z).mp hz)
      (Subgroup.inv_mem _ hz)⟩
  have hXU : X ≤ blockU L := fun v hv => hv.1
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    intro l hl
    apply mem_normalizer_of_map_le
    rintro _ ⟨v, hv, rfl⟩
    have hlv : l * v * l⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hl) v).mp hv.1
    refine ⟨hlv, ?_⟩
    show dlt q (l * v * l⁻¹) ∈ blockZ L
    rw [dlt_conj hL hTL hq hl hv.1]
    have hc : l * dlt q v = dlt q v * l :=
      (Subgroup.mem_centralizer_iff.mp hv.2.2 l hl)
    rw [hc, mul_inv_cancel_right]
    exact hv.2
  rcases hL.2.2.2.2.2 X hZX hXU hLX with hXZ | hXU'
  · exfalso
    obtain ⟨u₀, hu₀U, hu₀Z⟩ := Set.exists_of_ssubset hL.2.2.2.2.1
    have hiter : ∀ j : ℕ, (dlt q)^[j] u₀ ∈ blockU L ∧ (dlt q)^[j] u₀ ∉ blockZ L := by
      intro j
      induction j with
      | zero => exact ⟨hu₀U, hu₀Z⟩
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        refine ⟨hdltU _ ih.1, fun h => ih.2 ?_⟩
        have : (dlt q)^[j] u₀ ∈ X := ⟨ih.1, h⟩
        rwa [hXZ] at this
    obtain ⟨c, hc⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨q, hq⟩
    have hqc : q ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have h1 := dlt_pow_two_pow hL hqU c u₀ hu₀U
    rw [hqc, show dlt 1 u₀ = 1 by simp [dlt_def]] at h1
    exact (hiter (2 ^ c)).2 (h1 ▸ Subgroup.one_mem _)
  · have : u ∈ X := by rw [hXU']; exact hu
    exact this.2

theorem Q_centralizes_blockU [Finite G] (hL : IsShort2 L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {q u : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hu : u ∈ blockU L) : q * u = u * q := by
  have hqU := Q_le_normalizer_blockU hTL hq
  have key : blockU L ≤ Subgroup.centralizer ({q} : Set G) := by
    rw [blockU_eq_commutator hL, Subgroup.commutator_le]
    intro v hv l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlv : l * v⁻¹ * l⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hl) v⁻¹).mp
        (Subgroup.inv_mem _ hv)
    have hd : dlt q ⁅v, l⁆ = 1 := by
      have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e, dlt_mul hL hqU hv hlv, dlt_conj hL hTL hq hl (Subgroup.inv_mem _ hv)]
      have hz := dlt_mem_blockZ hL hTL hq (Subgroup.inv_mem _ hv)
      have hc : l * dlt q v⁻¹ = dlt q v⁻¹ * l := Subgroup.mem_centralizer_iff.mp hz.2 l hl
      rw [hc, mul_inv_cancel_right, ← dlt_mul hL hqU hv (Subgroup.inv_mem _ hv), mul_inv_cancel]
      simp [dlt_def]
    rw [dlt_def] at hd
    have := congrArg (· * (⁅v, l⁆ * q)) hd
    simp only [mul_assoc, inv_mul_cancel_left, one_mul] at this
    simpa [mul_assoc] using this.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (key hu)).symm

end QCent

section QL

variable [Finite G] {L T : Subgroup G}

theorem comm_mem_blockU (hL : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∀ l ∈ L, ∀ x ∈ pCoreOf 2 (L ⊔ T), l * x * l⁻¹ * x⁻¹ ∈ blockU L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLQ : L ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  refine forall_mem_of_pow hL.1 hLQ (L_le_normalizer_blockU L) fun l hl => ⟨b, fun x hx => ?_⟩
  set d := l * x * l⁻¹ * x⁻¹ with hd
  have hdP : d ∈ blockQ L := by
    have := Subgroup.inv_mem _ (commutator_Q_mem_blockQ hTL hx hl)
    rw [hd]
    simpa [mul_assoc] using this
  set e := l * d * l⁻¹ * d⁻¹ with he
  have heU : e ∈ blockU L := by
    have := Subgroup.inv_mem _ (commutator_mem_blockU hdP hl)
    rw [he]
    simpa [mul_assoc] using this
  have hed : Commute e d :=
    (Subgroup.mem_centralizer_iff.mp (hL.2.2.1.1 heU).2 d hdP).symm
  have hlx : l * x * l⁻¹ = d * x := by rw [hd]; group
  have hld : l * d * l⁻¹ = e * d := by rw [he]; group
  have hk : ∀ k : ℕ, ∃ u ∈ blockU L, l ^ k * x * (l ^ k)⁻¹ = u * d ^ k * x := by
    intro k
    induction k with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, huk⟩ := ih
      have hlu : l * u * l⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hl) u).mp hu
      refine ⟨l * u * l⁻¹ * e ^ k, Subgroup.mul_mem _ hlu (Subgroup.pow_mem _ heU k), ?_⟩
      have h1 : l ^ (k + 1) * x * (l ^ (k + 1))⁻¹ = l * (l ^ k * x * (l ^ k)⁻¹) * l⁻¹ := by
        group
      have h2 : l * (u * d ^ k * x) * l⁻¹ = (l * u * l⁻¹) * (l * d * l⁻¹) ^ k *
          (l * x * l⁻¹) := by
        rw [conj_pow]
        group
      rw [h1, huk, h2, hlx, hld, hed.mul_pow]
      group
  obtain ⟨u, hu, huk⟩ := hk (2 ^ b)
  have hdpow : d ^ 2 ^ b = 1 := by
    have h := pow_card_eq_one' (G := ↥(pCoreOf 2 L)) (x := ⟨d, hdP⟩)
    rw [hb] at h
    simpa using congrArg Subtype.val h
  rw [huk, hdpow, mul_one, mul_inv_cancel_right]
  exact hu

theorem commutator_Q_Q_le_centralizer (hL : IsShort2 L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ⁅pCoreOf 2 (L ⊔ T), pCoreOf 2 (L ⊔ T)⁆ ≤ Subgroup.centralizer (L : Set G) := by
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQL : ⁅Q, L⁆ ≤ blockU L := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have := Subgroup.inv_mem _ (comm_mem_blockU hL hTL l hl x hx)
    rw [commutatorElement_def]
    simpa [mul_assoc] using this
  have hUQ : ⁅blockU L, Q⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu q hq
    rw [Subgroup.mem_bot, commutatorElement_def, ← Q_centralizes_blockU hL hTL hq hu]
    group
  have h1 : ⁅⁅Q, L⁆, Q⁆ = ⊥ := eq_bot_iff.mpr ((Subgroup.commutator_mono hQL le_rfl).trans hUQ.le)
  have h2 : ⁅⁅L, Q⁆, Q⁆ = ⊥ := by rw [Subgroup.commutator_comm L Q]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h3

theorem comm_Q_blockQ_mem_blockZ (hL : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {q p : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hp : p ∈ blockQ L) :
    p * q * p⁻¹ * q⁻¹ ∈ blockZ L := by
  have hpQ : p ∈ pCoreOf 2 (L ⊔ T) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((blockQ_le L).trans le_sup_left) (sup_le_normalizer_blockQ hTL)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hp
  refine ⟨comm_mem_blockU hL hTL p (blockQ_le L hp) q hq, ?_⟩
  have h := commutator_Q_Q_le_centralizer hL hTL
    (Subgroup.commutator_mem_commutator hpQ hq)
  rwa [commutatorElement_def] at h

end QL

theorem centralizes_of_comm_mem_blockZ [Finite G] {L : Subgroup G} (hL : IsShort2 L) {x : G}
    (hcomm : ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ blockZ L) : ∀ l ∈ L, l * x = x * l := by
  have hZ : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z = z * l := fun z hz l hl =>
    (Subgroup.mem_centralizer_iff.mp hz.2 l hl)
  have hZsq : ∀ z ∈ blockZ L, z * z = 1 := fun z hz => blockU_sq hL hz.1
  let N : Subgroup ↥L := (Subgroup.centralizer ({x} : Set G)).subgroupOf L
  have hmemN : ∀ a : ↥L, a ∈ N ↔ (a : G) * x = x * a := by
    intro a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  have hNn : N.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [hmemN] at ha ⊢
    obtain ⟨z, hz⟩ : ∃ z, z = (b : G)⁻¹ * x * (b : G)⁻¹⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hzZ : z ∈ blockZ L := hz ▸ hcomm _ (Subgroup.inv_mem _ b.2)
    have hbx : (b : G)⁻¹ * x * b = z * x := by rw [hz]; group
    have hza : (a : G) * z = z * a := hZ z hzZ a a.2
    have h1 : (a : G) * ((b : G)⁻¹ * x * b) = ((b : G)⁻¹ * x * b) * a := by
      rw [hbx]
      calc (a : G) * (z * x) = z * ((a : G) * x) := by rw [← mul_assoc, hza, mul_assoc]
        _ = z * (x * a) := by rw [ha]
        _ = z * x * a := by rw [mul_assoc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (b : G) * a * (b : G)⁻¹ * x = b * ((a : G) * ((b : G)⁻¹ * x * b)) * (b : G)⁻¹ := by
          group
      _ = b * (((b : G)⁻¹ * x * b) * a) * (b : G)⁻¹ := by rw [h1]
      _ = x * (b * a * (b : G)⁻¹) := by group
  have h2 : IsPGroup 2 (↥L ⧸ N) := by
    intro w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨1, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmemN]
    obtain ⟨z, hz⟩ : ∃ z, z = (l : G) * x * (l : G)⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hzZ : z ∈ blockZ L := hz ▸ hcomm l l.2
    have hlx : (l : G) * x * (l : G)⁻¹ = z * x := by rw [hz]; group
    have hlz : (l : G) * z * (l : G)⁻¹ = z := by
      rw [hZ z hzZ l l.2, mul_inv_cancel_right]
    have h3 : (l : G) ^ 2 * x * ((l : G) ^ 2)⁻¹ = x := by
      calc (l : G) ^ 2 * x * ((l : G) ^ 2)⁻¹ = l * ((l : G) * x * (l : G)⁻¹) * (l : G)⁻¹ := by
            rw [sq]
            group
        _ = l * (z * x) * (l : G)⁻¹ := by rw [hlx]
        _ = ((l : G) * z * (l : G)⁻¹) * ((l : G) * x * (l : G)⁻¹) := by group
        _ = z * (z * x) := by rw [hlz, hlx]
        _ = x := by rw [← mul_assoc, hZsq z hzZ, one_mul]
    have h4 := congrArg (· * (l : G) ^ 2) h3
    simp only [inv_mul_cancel_right] at h4
    simpa using h4
  have htop := hL.1 N h2
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ N := by
    rw [htop]
    exact Subgroup.mem_top _
  exact (hmemN _).mp this

section Cocycle

variable [Finite G] {L T : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def cocyc (hL : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥(blockU L) →* Multiplicative W) {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (l : ↥L) : W :=
  Multiplicative.toAdd (β ⟨l * q * (l : G)⁻¹ * q⁻¹, comm_mem_blockU hL hTL l l.2 q hq⟩)

variable (hL : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
  {ρ : Representation (ZMod 2) (↥L ⧸ CFSG.pCore 2 ↥L) W} {β : ↥(blockU L) →* Multiplicative W}
include hL hTL

theorem cocyc_mul_left (hβa : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ρ (QuotientGroup.mk ℓ : ↥L ⧸ CFSG.pCore 2 ↥L) (Multiplicative.toAdd (β u)))
    {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (l₁ l₂ : ↥L) :
    cocyc hL hTL β hq (l₁ * l₂) = cocyc hL hTL β hq l₁ +
      ρ (QuotientGroup.mk l₁ : ↥L ⧸ CFSG.pCore 2 ↥L) (cocyc hL hTL β hq l₂) := by
  have h2 := comm_mem_blockU hL hTL l₂ l₂.2 q hq
  have h1 := comm_mem_blockU hL hTL l₁ l₁.2 q hq
  have h3 : (l₁ : G) * (l₂ * q * (l₂ : G)⁻¹ * q⁻¹) * (l₁ : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L l₁.2) _).mp h2
  have e : (⟨((l₁ * l₂ : ↥L) : G) * q * ((l₁ * l₂ : ↥L) : G)⁻¹ * q⁻¹,
      comm_mem_blockU hL hTL _ (l₁ * l₂).2 q hq⟩ : ↥(blockU L)) =
      ⟨(l₁ : G) * (l₂ * q * (l₂ : G)⁻¹ * q⁻¹) * (l₁ : G)⁻¹, h3⟩ *
        ⟨l₁ * q * (l₁ : G)⁻¹ * q⁻¹, h1⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  have h4 := hβa l₁ ⟨_, h2⟩ ⟨(l₁ : G) * (l₂ * q * (l₂ : G)⁻¹ * q⁻¹) * (l₁ : G)⁻¹, h3⟩ rfl
  simp only [cocyc]
  rw [e, map_mul, toAdd_mul, h4, add_comm]

omit [Module (ZMod 2) W] in
theorem cocyc_eq_zero_of_mem (hβk : β.ker = (blockZ L).subgroupOf (blockU L)) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) {o : ↥L} (ho : o ∈ CFSG.pCore 2 ↥L) :
    cocyc hL hTL β hq o = 0 := by
  have hoP : (o : G) ∈ blockQ L := by
    rw [blockQ, ← Subgroup.mem_subgroupOf, pCoreOf_subgroupOf]
    exact ho
  have hZ := comm_Q_blockQ_mem_blockZ hL hTL hq hoP
  have hker : (⟨o * q * (o : G)⁻¹ * q⁻¹, comm_mem_blockU hL hTL o o.2 q hq⟩ :
      ↥(blockU L)) ∈ β.ker := by
    rw [hβk, Subgroup.mem_subgroupOf]
    exact hZ
  simp only [cocyc]
  rw [MonoidHom.mem_ker] at hker
  rw [hker, toAdd_one]

omit [Module (ZMod 2) W] in
theorem cocyc_mul {q₁ q₂ : G} (hq₁ : q₁ ∈ pCoreOf 2 (L ⊔ T)) (hq₂ : q₂ ∈ pCoreOf 2 (L ⊔ T))
    (l : ↥L) :
    cocyc hL hTL β (Subgroup.mul_mem _ hq₁ hq₂) l =
      cocyc hL hTL β hq₁ l + cocyc hL hTL β hq₂ l := by
  have h1 := comm_mem_blockU hL hTL l l.2 q₁ hq₁
  have h2 := comm_mem_blockU hL hTL l l.2 q₂ hq₂
  have hc : q₁ * (l * q₂ * (l : G)⁻¹ * q₂⁻¹) = (l * q₂ * (l : G)⁻¹ * q₂⁻¹) * q₁ :=
    Q_centralizes_blockU hL hTL hq₁ h2
  have e : (⟨l * (q₁ * q₂) * (l : G)⁻¹ * (q₁ * q₂)⁻¹,
      comm_mem_blockU hL hTL l l.2 _ (Subgroup.mul_mem _ hq₁ hq₂)⟩ : ↥(blockU L)) =
      ⟨l * q₁ * (l : G)⁻¹ * q₁⁻¹, h1⟩ * ⟨l * q₂ * (l : G)⁻¹ * q₂⁻¹, h2⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (l : G) * (q₁ * q₂) * (l : G)⁻¹ * (q₁ * q₂)⁻¹ =
        (l * q₁ * (l : G)⁻¹ * q₁⁻¹) * (q₁ * (l * q₂ * (l : G)⁻¹ * q₂⁻¹)) * q₁⁻¹ := by group
      _ = (l * q₁ * (l : G)⁻¹ * q₁⁻¹) * (l * q₂ * (l : G)⁻¹ * q₂⁻¹) := by rw [hc]; group
  simp only [cocyc]
  rw [e, map_mul, toAdd_mul]

theorem cocyc_of_mem_blockU (hβa : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ρ (QuotientGroup.mk ℓ : ↥L ⧸ CFSG.pCore 2 ↥L) (Multiplicative.toAdd (β u)))
    {u : G} (hu : u ∈ blockU L) (huQ : u ∈ pCoreOf 2 (L ⊔ T)) (l : ↥L) :
    cocyc hL hTL β huQ l = ρ (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L)
      (Multiplicative.toAdd (β ⟨u, hu⟩)) - Multiplicative.toAdd (β ⟨u, hu⟩) := by
  have hlu : (l : G) * u * (l : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L l.2) u).mp hu
  have e : (⟨l * u * (l : G)⁻¹ * u⁻¹, comm_mem_blockU hL hTL l l.2 u huQ⟩ : ↥(blockU L)) =
      ⟨l * u * (l : G)⁻¹, hlu⟩ * (⟨u, hu⟩ : ↥(blockU L))⁻¹ := rfl
  have h1 := hβa l ⟨u, hu⟩ ⟨_, hlu⟩ rfl
  simp only [cocyc]
  rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, h1, sub_eq_add_neg]

end Cocycle

theorem relIndex_le_two_pow_finrank_H1 [Finite G] {L T : Subgroup G}
    (hT : IsSylowTwoOf T (L ⊔ T)) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hL : IsShort2 L)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (↥L ⧸ CFSG.pCore 2 ↥L) W)
    (β : ↥(blockU L) →* Multiplicative W) (hβs : Function.Surjective β)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβa : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ρ (QuotientGroup.mk ℓ : ↥L ⧸ CFSG.pCore 2 ↥L) (Multiplicative.toAdd (β u))) :
    (blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G))).relIndex (pCoreOf 2 (L ⊔ T)) ≤
      2 ^ Module.finrank (ZMod 2) (JonesParshall.H1 ρ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hwd : ∀ (q : ↥Q) (a b : ↥L), a⁻¹ * b ∈ CFSG.pCore 2 ↥L →
      cocyc hL hTL β q.2 a = cocyc hL hTL β q.2 b := by
    intro q a b hab
    have h := cocyc_mul_left hL hTL hβa q.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, cocyc_eq_zero_of_mem hL hTL hβk q.2 hab, map_zero, add_zero] at h
    exact h.symm
  let F : ↥Q → (↥L ⧸ CFSG.pCore 2 ↥L) → W := fun q =>
    Quotient.lift (cocyc hL hTL β q.2) fun a b hab =>
      hwd q a b ((QuotientGroup.leftRel_apply).mp hab)
  have hF : ∀ (q : ↥Q) (l : ↥L), F q (QuotientGroup.mk l) = cocyc hL hTL β q.2 l :=
    fun _ _ => rfl
  have hFZ : ∀ q : ↥Q, F q ∈ JonesParshall.Z1 ρ := by
    intro q x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, hF, hF, hF]
    exact cocyc_mul_left hL hTL hβa q.2 a b
  have hFmul : ∀ q₁ q₂ : ↥Q, F (q₁ * q₂) = F q₁ + F q₂ := by
    intro q₁ q₂
    funext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Pi.add_apply, hF, hF, hF]
    exact cocyc_mul hL hTL q₁.2 q₂.2 l
  have hF1 : F 1 = 0 := by
    have h := hFmul 1 1
    rw [mul_one] at h
    have h2 : F 1 + F 1 = F 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  let Φ : ↥Q →* Multiplicative (JonesParshall.H1 ρ) :=
    { toFun := fun q => Multiplicative.ofAdd (Submodule.Quotient.mk ⟨F q, hFZ q⟩)
      map_one' := by
        rw [← ofAdd_zero]
        congr 1
        rw [Submodule.Quotient.mk_eq_zero]
        show (⟨F 1, hFZ 1⟩ : ↥(JonesParshall.Z1 ρ)) ∈ _
        simp only [hF1]
        exact Submodule.zero_mem _
      map_mul' := fun q₁ q₂ => by
        rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
        congr 2
        exact Subtype.ext (hFmul q₁ q₂) }
  have hU2 : blockU L ≤ Q := by
    have hPQ : blockQ L ≤ Q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((blockQ_le L).trans le_sup_left) (sup_le_normalizer_blockQ hTL)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact (blockU_le_blockQ L).trans hPQ
  have hQT : Q ≤ T := by
    refine A4.le_of_normal_of_isSylowTwoOf hT (Q_le_sup L T) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Q_le_sup L T)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hker : Φ.ker ≤ (blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G))).subgroupOf Q := by
    intro q hq
    have h1 : (Submodule.Quotient.mk ⟨F q, hFZ q⟩ : JonesParshall.H1 ρ) = 0 := by
      have := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hq)
      rw [toAdd_one] at this
      exact this
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨w, hw⟩ := h1
    obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd w)
    have hu₀w : Multiplicative.toAdd (β u₀) = w := by rw [hu₀, toAdd_ofAdd]
    set x : G := (u₀ : G)⁻¹ * q with hx
    have hu₀Q : ((u₀ : G))⁻¹ ∈ Q := Subgroup.inv_mem _ (hU2 u₀.2)
    have hxQ : x ∈ Q := Subgroup.mul_mem _ hu₀Q q.2
    have hcx : ∀ l : ↥L, cocyc hL hTL β hxQ l = 0 := by
      intro l
      have h2 := cocyc_mul (β := β) hL hTL hu₀Q q.2 l
      have h3 := cocyc_of_mem_blockU hL hTL hβa (Subgroup.inv_mem _ u₀.2) hu₀Q l
      have h4 : cocyc hL hTL β q.2 l = ρ (QuotientGroup.mk l) w - w := by
        have := congrFun hw (QuotientGroup.mk l)
        rw [← hF]
        exact this.symm
      have h5 : Multiplicative.toAdd (β ⟨(u₀ : G)⁻¹, Subgroup.inv_mem _ u₀.2⟩) = -w := by
        rw [show (⟨(u₀ : G)⁻¹, Subgroup.inv_mem _ u₀.2⟩ : ↥(blockU L)) = u₀⁻¹ from rfl,
          map_inv, toAdd_inv, hu₀w]
      rw [h2, h3, h4, h5, map_neg]
      abel
    have hxZ : ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ blockZ L := by
      intro l hl
      have h6 := hcx ⟨l, hl⟩
      simp only [cocyc] at h6
      have h7 : β ⟨l * x * l⁻¹ * x⁻¹, comm_mem_blockU hL hTL l hl x hxQ⟩ = 1 :=
        Multiplicative.toAdd.injective (by rw [h6, toAdd_one])
      have h8 : (⟨l * x * l⁻¹ * x⁻¹, comm_mem_blockU hL hTL l hl x hxQ⟩ : ↥(blockU L)) ∈
          β.ker := h7
      rw [hβk, Subgroup.mem_subgroupOf] at h8
      exact h8
    have hxC := centralizes_of_comm_mem_blockZ hL hxZ
    have hxT : x ∈ T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hQT hxQ, Subgroup.mem_centralizer_iff.mpr fun l hl => (hxC l hl)⟩
    rw [Subgroup.mem_subgroupOf]
    have e : (q : G) = u₀ * x := by rw [hx]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left u₀.2) (Subgroup.mem_sup_right hxT)
  have hWfin : Finite W := by
    have : Finite (Multiplicative W) := Finite.of_surjective β hβs
    exact Finite.of_equiv _ Multiplicative.toAdd
  have hZfin : Finite ↥(JonesParshall.Z1 ρ) := inferInstance
  have hHfin : Finite (JonesParshall.H1 ρ) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hH1 : Nat.card (JonesParshall.H1 ρ) = 2 ^ Module.finrank (ZMod 2) (JonesParshall.H1 ρ) := by
    have : Fintype (JonesParshall.H1 ρ) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  calc (blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G))).relIndex Q
      = ((blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G))).subgroupOf Q).index := rfl
    _ ≤ Φ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card Φ.range := Subgroup.index_ker Φ
    _ ≤ Nat.card (Multiplicative (JonesParshall.H1 ρ)) := Subgroup.card_le_card_group _
    _ = 2 ^ Module.finrank (ZMod 2) (JonesParshall.H1 ρ) := hH1

end C113

theorem as_C_1_13_b_holds : AS_C_1_13_b := by
  intro G _ _ L T hT hTL hL
  exact ⟨fun W _ _ ρ β hβs hβk hβa =>
      C113.relIndex_le_two_pow_finrank_H1 hT hTL hL W ρ β hβs hβk hβa,
    fun hq => C113.exists_hopf_surjective hL hq,
    fun h3 => C113.pCoreOf_eq_blockU_of_card_three hL h3⟩

end CFSG.Quasithin.ASInputs
