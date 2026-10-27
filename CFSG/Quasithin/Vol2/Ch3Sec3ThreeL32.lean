module

public import CFSG.Quasithin.Background.AutOnElemAb
public import CFSG.Quasithin.Vol2.Ch3Sec3CZL32
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3325
public import CFSG.Quasithin.Background.B4L3Three
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

namespace ThreeL32

theorem b2_sq : CZL32.b2 * CZL32.b2 = 1 := by decide +kernel

theorem b2_ne_one : CZL32.b2 ≠ 1 := by decide +kernel

theorem b2_e2 : L3.act CZL32.b2 CZL32.e2 ≠ CZL32.e2 := by decide +kernel

theorem card_fix_b2 :
    (Finset.univ.filter fun v : L3.Vec => L3.act CZL32.b2 v = v).card = 4 := by
  decide +kernel

variable {G : Type} [Group G]

theorem blockU_le_pCoreOf {L : Subgroup G} (hshort : IsShort2 L) : blockU L ≤ pCoreOf 2 L :=
  fun _ hu => (hshort.2.2.1.1 hu).1

theorem pCoreOf_le_qL {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ qL L T :=
  CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTL))

variable [Finite G] {T M L D : Subgroup G}

theorem qL_le (h : Hyp331 G T M L D) : qL L T ≤ T :=
  pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf

theorem eq_one_of_mem_centralizer (h : Hyp331 G T M L D) (hTC : tC L T = ⊥) {x : G}
    (hx : x ∈ qL L T) (hxL : x ∈ Subgroup.centralizer (L : Set G)) : x = 1 := by
  have h1 : x ∈ tC L T := ⟨qL_le h hx, hxL⟩
  rw [hTC] at h1
  exact h1

theorem blockZ_eq_bot (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hshort : IsShort2 L) (hTC : tC L T = ⊥) : blockZ L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  exact eq_one_of_mem_centralizer h hTC (pCoreOf_le_qL hTL (blockU_le_pCoreOf hshort hz.1)) hz.2

theorem isElemAbelian_qL
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D) (hshort : IsShort2 L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T = ⊥) :
    IsElemAbelian 2 (qL L T) := by
  have hFQ := h.frattini_qL_le_tC h38 h39 hshort hTL
  rw [hTC] at hFQ
  have hF : frattini ↥(qL L T) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (qL L T).subtype_injective).mp (le_bot_iff.mp hFQ)
  exact isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF

omit [Finite G] in
theorem comm_of_isElemAbelian {Q : Subgroup G} (hQe : IsElemAbelian 2 Q) {a b : G} (ha : a ∈ Q)
    (hb : b ∈ Q) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hQe ha hb

omit [Finite G] in
theorem card_blockU (hLn : IsLnBlock L 3) (hZ : blockZ L = ⊥) : Nat.card (blockU L) = 8 := by
  obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := hLn
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  exact L3Data.card_vec

omit [Finite G] in
theorem mem_fixV_zpowers {V : Type*} [CommGroup V] {a : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem mem_qL_of_centralizer (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hshort : IsShort2 L) {g : G} (hg : g ∈ L ⊔ T)
    (hgc : g ∈ Subgroup.centralizer (qL L T : Set G)) : g ∈ qL L T := by
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have heq := C1.inf_centralizer_blockU_eq hshort le_sup_left hLTN
    (fun g hg => C1.exists_pow_mem_of_mem_sup hT2 hTL hg)
  have hUQ : blockU L ≤ qL L T := (blockU_le_pCoreOf hshort).trans (pCoreOf_le_qL hTL)
  have h1 : g ∈ (L ⊔ T) ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨hg, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUQ) hgc⟩
  rw [heq] at h1
  exact h1

theorem card_qL_le
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥) :
    Nat.card (qL L T) ≤ 2 * Nat.card (blockU L) := by
  obtain ⟨hshort, α, hαs, hαk, β, hβs, hβk, hβe⟩ := id hLn
  have hQe := isElemAbelian_qL h38 h39 h hshort hTL hTC
  have hZ := blockZ_eq_bot h hTL hshort hTC
  have hOQ : pCoreOf 2 L ≤ qL L T := pCoreOf_le_qL hTL
  have hUQ : blockU L ≤ qL L T := (blockU_le_pCoreOf hshort).trans hOQ
  have hQU := Hyp331.commutator_qL_le_blockU hshort hTL
  have hLQ : L ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  obtain ⟨s, hs⟩ := hαs (specialLinearGroupEquivStatedSL 3 (ZMod 2) CZL32.b2)
  have hρs : CZL32.rho3 β hβs hβk ⟨s, Subgroup.le_normalizer s.2⟩ = CZL32.b2 := by
    apply Subtype.ext
    rw [CZL32.rho3_of_mem β hβs hβk hβe s, hs]
    rfl
  have hs2 : (s : G) * s ∈ pCoreOf 2 L := by
    have h1 : s * s ∈ CFSG.pCore 2 ↥L := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, hs, ← map_mul, b2_sq, map_one]
    exact (mem_pCore_iff _).mp h1
  have hs1 : (s : G) ∉ pCoreOf 2 L := by
    intro h1
    have h2 : s ∈ α.ker := by
      rw [hαk]
      exact (mem_pCore_iff s).mpr h1
    rw [MonoidHom.mem_ker, hs] at h2
    exact b2_ne_one ((specialLinearGroupEquivStatedSL 3 (ZMod 2)).injective
      (h2.trans (map_one _).symm))
  have hsQ : ∀ c ∈ qL L T, (s : G) * c⁻¹ * (s : G)⁻¹ ∈ qL L T := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp (hLQ s.2) _).mp ((qL L T).inv_mem hc)
  have hcU : ∀ c ∈ qL L T, ⁅c, (s : G)⁆ ∈ blockU L :=
    fun c hc => hQU (Subgroup.commutator_mem_commutator hc s.2)
  let φ : ↥(qL L T) →* ↥(blockU L) := MonoidHom.mk' (fun c => ⟨⁅(c : G), (s : G)⁆, hcU c c.2⟩)
    (fun a b => Subtype.ext (by
      show ⁅((a * b : ↥(qL L T)) : G), (s : G)⁆ = ⁅(a : G), (s : G)⁆ * ⁅(b : G), (s : G)⁆
      have hc := comm_of_isElemAbelian hQe ((qL L T).mul_mem b.2 (hsQ b b.2)) (hsQ a a.2)
      have e1 : ((a : G) * b) * s * ((a : G) * b)⁻¹ * (s : G)⁻¹ =
          a * ((b * (s * (b : G)⁻¹ * (s : G)⁻¹)) * (s * (a : G)⁻¹ * (s : G)⁻¹)) := by group
      have e2 : (a : G) * s * (a : G)⁻¹ * (s : G)⁻¹ * (b * s * (b : G)⁻¹ * (s : G)⁻¹) =
          a * ((s * (a : G)⁻¹ * (s : G)⁻¹) * (b * (s * (b : G)⁻¹ * (s : G)⁻¹))) := by group
      rw [Subgroup.coe_mul, commutatorElement_def, commutatorElement_def, commutatorElement_def,
        e1, e2, hc]))
  have hφ : ∀ c : ↥(qL L T), ((φ c : ↥(blockU L)) : G) = ⁅(c : G), (s : G)⁆ := fun _ => rfl
  have hker : ∀ c : ↥(qL L T), φ c = 1 → (c : G) ∈ blockU L := by
    intro c hc
    have h1 : ⁅(c : G), (s : G)⁆ = 1 := by rw [← hφ c, hc]; rfl
    obtain ⟨u, hu, hcent⟩ := exists_mem_blockU_of_cocycle hLn
      (fun q hq ℓ hℓ => hQU (Subgroup.commutator_mem_commutator hq hℓ))
      (fun a ha b hb => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (comm_of_isElemAbelian hQe ha hb)]
        exact Subgroup.one_mem _)
      hOQ c.2 s.2 (by rw [pow_two]; exact hs2) hs1 (by rw [h1]; exact Subgroup.one_mem _)
    have h2 : u⁻¹ * c = 1 := eq_one_of_mem_centralizer h hTC
      ((qL L T).mul_mem ((qL L T).inv_mem (hUQ hu)) c.2) hcent
    rw [← (inv_mul_eq_one.mp h2)]
    exact hu
  have hfix : ∀ c : ↥(qL L T), L3.act CZL32.b2 (Multiplicative.toAdd (β (φ c))) =
      Multiplicative.toAdd (β (φ c)) := by
    intro c
    have hs2c : (s : G) * s * (c : G)⁻¹ = (c : G)⁻¹ * (s * s) :=
      comm_of_isElemAbelian hQe (hOQ hs2) ((qL L T).inv_mem c.2)
    have hw2 : ⁅(c : G), (s : G)⁆ * ⁅(c : G), (s : G)⁆ = 1 := by
      have := hshort.2.2.1.2 _ (hcU c c.2)
      rwa [pow_two] at this
    have hw : ((φ c : ↥(blockU L)) : G) =
        (s : G) * ((φ c : ↥(blockU L)) : G) * (s : G)⁻¹ := by
      rw [hφ]
      have e1 : (s : G) * ⁅(c : G), (s : G)⁆ * (s : G)⁻¹ =
          ((s : G) * c * (s : G)⁻¹) * ((s * s) * (c : G)⁻¹ * (s * s : G)⁻¹) := by
        rw [commutatorElement_def]
        group
      have e2 : (s : G) * s * (c : G)⁻¹ * ((s : G) * s)⁻¹ = (c : G)⁻¹ := by
        rw [hs2c]
        group
      have e3 : ⁅(c : G), (s : G)⁆ = (⁅(c : G), (s : G)⁆)⁻¹ :=
        (eq_inv_of_mul_eq_one_left hw2)
      rw [e1, e2, e3, commutatorElement_def]
      group
    have e := CZL32.rho3_equiv β hβs hβk ⟨s, Subgroup.le_normalizer s.2⟩ (φ c) (φ c) hw
    rw [hρs] at e
    exact e.symm
  have hrange : Nat.card φ.range ≤ 4 := by
    let f : ↥φ.range → ↥(Finset.univ.filter fun v : L3.Vec => L3.act CZL32.b2 v = v) :=
      fun x => ⟨Multiplicative.toAdd (β x), by
        obtain ⟨c, hc⟩ := x.2
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hc]
        exact hfix c⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply hβinj
      exact Multiplicative.toAdd.injective (congrArg Subtype.val hxy)
    have h4 : Nat.card ↥(Finset.univ.filter fun v : L3.Vec => L3.act CZL32.b2 v = v) = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_fix_b2]
    exact (Nat.card_le_card_of_injective f hf).trans h4.le
  obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd CZL32.e2)
  have hφu₀ : φ ⟨u₀, hUQ u₀.2⟩ ≠ 1 := by
    intro h1
    have h2 : ⁅(u₀ : G), (s : G)⁆ = 1 := by
      have := congrArg Subtype.val h1
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at h2
    have h3 : (u₀ : G) = s * u₀ * (s : G)⁻¹ := by
      rw [← h2]
      group
    have e := CZL32.rho3_equiv β hβs hβk ⟨s, Subgroup.le_normalizer s.2⟩ u₀ u₀ h3
    rw [hρs, hu₀] at e
    exact b2_e2 e.symm
  set k := φ.ker with hk
  set U' := (blockU L).subgroupOf (qL L T) with hU'
  have hkU' : k ≤ U' := fun c hc => Subgroup.mem_subgroupOf.mpr (hker c hc)
  have hQcard : Nat.card ↥(qL L T) = Nat.card φ.range * Nat.card k := by
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h2
  have hU'card : Nat.card U' = Nat.card (blockU L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv
  have hlt : Nat.card k < Nat.card U' := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hkU')
    intro he
    have hkeq := Subgroup.eq_of_le_of_card_ge hkU' he.ge
    have hmem : (⟨u₀, hUQ u₀.2⟩ : ↥(qL L T)) ∈ U' := Subgroup.mem_subgroupOf.mpr u₀.2
    rw [← hkeq] at hmem
    exact hφu₀ hmem
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hkU'
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have h1 : Nat.card k * m ≤ Nat.card k * 1 := Nat.mul_le_mul_left _ (by omega)
    rw [← hm, mul_one] at h1
    omega
  rw [hQcard, ← hU'card, hm]
  have hkpos : 0 < Nat.card k := Nat.card_pos
  nlinarith

theorem card_qL
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥)
    (hVQ : vPlus L T ≠ qL L T) : Nat.card (qL L T) = 16 := by
  have hshort := hLn.1
  have hZ := blockZ_eq_bot h hTL hshort hTC
  have hU8 := card_blockU hLn hZ
  have hle := card_qL_le h38 h39 h hTL hLn hTC
  have hUQ : blockU L ≤ qL L T := (blockU_le_pCoreOf hshort).trans (pCoreOf_le_qL hTL)
  have hVle : vPlus L T ≤ qL L T := (Hyp331.vPlus_reduced h.toSetup331).1.trans inf_le_left
  have hUV := h.blockU_le_vPlus h38 h39 hshort hTL
  have hne : Nat.card (blockU L) ≠ Nat.card (qL L T) := by
    intro he
    apply hVQ
    have hUeq : blockU L = qL L T := Subgroup.eq_of_le_of_card_ge hUQ he.ge
    exact le_antisymm hVle (hUeq ▸ hUV)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hUQ
  have hpos : 0 < Nat.card (qL L T) := Nat.card_pos
  rw [hU8] at hm hne hle
  rw [hm] at hle hne hpos ⊢
  have hm2 : m ≤ 2 := by omega
  interval_cases m <;> omega

theorem exists_mem_conj
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥)
    {t : G} (ht : t ∈ L ⊔ T) : ∃ ℓ ∈ L, ∀ q ∈ qL L T, t * q * t⁻¹ = ℓ * q * ℓ⁻¹ := by
  obtain ⟨hshort, α, hαs, hαk, β, hβs, hβk, hβe⟩ := id hLn
  have hQe := isElemAbelian_qL h38 h39 h hshort hTL hTC
  have hZ := blockZ_eq_bot h hTL hshort hTC
  have hOQ : pCoreOf 2 L ≤ qL L T := pCoreOf_le_qL hTL
  have hUQ : blockU L ≤ qL L T := (blockU_le_pCoreOf hshort).trans hOQ
  have hQU := Hyp331.commutator_qL_le_blockU hshort hTL
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  set U' := (blockU L).subgroupOf (qL L T) with hU'
  have hidx : U'.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index U'
    have h2 := card_qL_le h38 h39 h hTL hLn hTC
    have h3 : Nat.card U' = Nat.card (blockU L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv
    rw [h3] at h1
    have hpos : 0 < Nat.card (blockU L) := Nat.card_pos
    nlinarith
  obtain ⟨ℓ, hℓ, hρℓ⟩ := CZL32.rho3_surj β hβs hβk hαs hβe
    (CZL32.rho3 β hβs hβk ⟨t, hLTN ht⟩)
  refine ⟨ℓ, hℓ, fun q hq => ?_⟩
  have hxLT : ℓ⁻¹ * t ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hℓ)) ht
  set x := ℓ⁻¹ * t with hx
  have hρx : CZL32.rho3 β hβs hβk ⟨x, hLTN hxLT⟩ = 1 := by
    have e : (⟨x, hLTN hxLT⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨ℓ, Subgroup.le_normalizer hℓ⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
          ⟨t, hLTN ht⟩ := rfl
    rw [e, map_mul, map_inv, hρℓ, inv_mul_cancel]
  have hxU : ∀ u ∈ blockU L, x * u * x⁻¹ = u := by
    intro u hu
    have e := CZL32.rho3_equiv β hβs hβk ⟨x, hLTN hxLT⟩ ⟨u, hu⟩
      ⟨x * u * x⁻¹, Mod32.conj_mem_blockU (hLTN hxLT) ⟨u, hu⟩⟩ rfl
    rw [hρx, L3.act_one] at e
    exact congrArg Subtype.val (hβinj (Multiplicative.toAdd.injective e))
  have hxL : ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
    intro y hy
    have hxyx : x * y * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hLTN hxLT) y).mp hy
    have hz : x * y * x⁻¹ * y⁻¹ ∈ L := L.mul_mem hxyx (L.inv_mem hy)
    have h1 : CZL32.rho3 β hβs hβk ⟨_, Subgroup.le_normalizer hz⟩ = 1 := by
      have e : (⟨x * y * x⁻¹ * y⁻¹, Subgroup.le_normalizer hz⟩ :
          ↥(Subgroup.normalizer (L : Set G))) =
          ⟨x, hLTN hxLT⟩ * ⟨y, Subgroup.le_normalizer hy⟩ * (⟨x, hLTN hxLT⟩ :
            ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
            (⟨y, Subgroup.le_normalizer hy⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hρx, one_mul, inv_one, mul_one,
        mul_inv_cancel]
    exact (mem_pCore_iff ⟨_, hz⟩).mp (CZL32.rho3_ker β hβs hβk hαk hβe ⟨_, hz⟩ h1)
  have hxQ : x * q * x⁻¹ * q⁻¹ ∈ blockU L := by
    by_cases hqU : q ∈ blockU L
    · rw [hxU q hqU, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hidx2 : U'.index = 2 := by
        rcases Nat.lt_or_ge U'.index 2 with h1 | h1
        · exfalso
          have h0 : U'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
          have h2 : U'.index = 1 := by omega
          rw [Subgroup.index_eq_one] at h2
          apply hqU
          have : (⟨q, hq⟩ : ↥(qL L T)) ∈ U' := h2 ▸ Subgroup.mem_top _
          exact Subgroup.mem_subgroupOf.mp this
        · omega
      have hxq : x * q * x⁻¹ ∈ qL L T :=
        (Subgroup.mem_normalizer_iff.mp (hLTQ hxLT) q).mp hq
      have hxqU : x * q * x⁻¹ ∉ blockU L := by
        intro h1
        apply hqU
        have h2 := Mod32.conj_mem_blockU (Subgroup.inv_mem _ (hLTN hxLT)) ⟨_, h1⟩
        have e : x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q := by group
        rw [e] at h2
        exact h2
      have key := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := ⟨_, hxq⟩)
        (b := ⟨q⁻¹, (qL L T).inv_mem hq⟩)).mpr (by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          exact ⟨fun h1 => absurd h1 hxqU, fun h1 => absurd ((blockU L).inv_mem_iff.mp h1) hqU⟩)
      rw [Subgroup.mem_subgroupOf] at key
      exact key
  have hNy : ∀ y ∈ L, y * (x * q * x⁻¹ * q⁻¹) * y⁻¹ = x * q * x⁻¹ * q⁻¹ := by
    intro y hy
    have hwQ : x * y * x⁻¹ * y⁻¹ ∈ qL L T := hOQ (hxL y hy)
    have hr : y * (x * q * x⁻¹) * y⁻¹ ∈ qL L T := by
      have h1 : x * q * x⁻¹ ∈ qL L T := (Subgroup.mem_normalizer_iff.mp (hLTQ hxLT) q).mp hq
      exact (Subgroup.mem_normalizer_iff.mp (hLTQ (Subgroup.mem_sup_left hy)) _).mp h1
    have hwr := comm_of_isElemAbelian hQe hwQ hr
    have hcU : q⁻¹ * y * q * y⁻¹ ∈ blockU L := by
      have := hQU (Subgroup.commutator_mem_commutator ((qL L T).inv_mem hq) hy)
      rwa [commutatorElement_def, inv_inv] at this
    have hxc := hxU _ hcU
    have e1 : y * (x * q * x⁻¹ * q⁻¹) * y⁻¹ =
        (y * (x * q * x⁻¹) * y⁻¹) * (y * q⁻¹ * y⁻¹) := by group
    have e2 : y * (x * q * x⁻¹) * y⁻¹ = (x * y * x⁻¹ * y⁻¹) * (y * (x * q * x⁻¹) * y⁻¹) *
        (x * y * x⁻¹ * y⁻¹)⁻¹ := by
      rw [hwr]
      group
    have e3 : (x * y * x⁻¹ * y⁻¹) * (y * (x * q * x⁻¹) * y⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ *
        (y * q⁻¹ * y⁻¹) = x * q * x⁻¹ * (x * (q⁻¹ * y * q * y⁻¹) * x⁻¹) *
          (q⁻¹ * y * q * y⁻¹)⁻¹ * q⁻¹ := by group
    rw [e1, e2, e3, hxc]
    group
  have hN1 : x * q * x⁻¹ * q⁻¹ = 1 := eq_one_of_mem_centralizer h hTC (hUQ hxQ)
    (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      calc y * (x * q * x⁻¹ * q⁻¹) = (y * (x * q * x⁻¹ * q⁻¹) * y⁻¹) * y := by group
        _ = x * q * x⁻¹ * q⁻¹ * y := by rw [hNy y hy])
  have key : x * q * x⁻¹ = q := mul_inv_eq_one.mp hN1
  calc t * q * t⁻¹ = ℓ * (x * q * x⁻¹) * ℓ⁻¹ := by rw [hx]; group
    _ = ℓ * q * ℓ⁻¹ := by rw [key]

theorem l3Coord
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥)
    [IsMulCommutative ↥(qL L T)] :
    L3Coord (autOn L (qL L T)) ((blockU L).subgroupOf (qL L T)) ⊥ := by
  obtain ⟨hshort, α, hαs, hαk, β, hβs, hβk, hβe⟩ := id hLn
  have hQe := isElemAbelian_qL h38 h39 h hshort hTL hTC
  have hZ := blockZ_eq_bot h hTL hshort hTC
  have hOQ : pCoreOf 2 L ≤ qL L T := pCoreOf_le_qL hTL
  have hUQ : blockU L ≤ qL L T := (blockU_le_pCoreOf hshort).trans hOQ
  have hLQ : L ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  let φ : ↥L →* ↥(autOn L (qL L T)) := InternalSec.autOnHom hLQ
  have hker : α.ker ≤ φ.ker := by
    intro ℓ hℓ
    rw [InternalSec.mem_ker_autOnHom]
    rw [hαk] at hℓ
    have h1 : (ℓ : G) ∈ qL L T := hOQ ((mem_pCore_iff ℓ).mp hℓ)
    exact Subgroup.mem_centralizer_iff.mpr fun q hq => comm_of_isElemAbelian hQe hq h1
  let ψ : ↥L ⧸ α.ker →* ↥(autOn L (qL L T)) := QuotientGroup.lift α.ker φ hker
  let e₁ : ↥L ⧸ α.ker ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    QuotientGroup.quotientKerEquivOfSurjective α hαs
  let e₂ := specialLinearGroupEquivStatedSL 3 (ZMod 2)
  let π : L3.Γ →* ↥(autOn L (qL L T)) := ψ.comp (e₁.symm.toMonoidHom.comp e₂.toMonoidHom)
  have hπ : ∀ ℓ : ↥L, π (e₂.symm (α ℓ)) = φ ℓ := by
    intro ℓ
    have h1 : e₁.symm (α ℓ) = QuotientGroup.mk ℓ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show ψ (e₁.symm (e₂ (e₂.symm (α ℓ)))) = φ ℓ
    rw [MulEquiv.apply_symm_apply, h1]
    rfl
  have hφ : ∀ (ℓ : ↥L) (q : ↥(qL L T)),
      ((((φ ℓ : ↥(autOn L (qL L T))) : MulAut ↥(qL L T)) q : ↥(qL L T)) : G) =
        ℓ * q * (ℓ : G)⁻¹ := fun ℓ q => Setup.rho_apply_coe hLQ ℓ q
  let eU := Subgroup.subgroupOfEquivOfLe hUQ
  let β' : ↥((blockU L).subgroupOf (qL L T)) →* Multiplicative L3.Vec :=
    β.comp eU.toMonoidHom
  have hβ' : ∀ u, β' u = β (eU u) := fun _ => rfl
  have heU : ∀ u : ↥((blockU L).subgroupOf (qL L T)), ((eU u : ↥(blockU L)) : G) = u :=
    fun _ => rfl
  have hπs : Function.Surjective π := by
    intro g
    obtain ⟨ℓ, rfl⟩ := InternalSec.autOnHom_surjective hLQ g
    exact ⟨_, hπ ℓ⟩
  have hβs' : Function.Surjective β' := by
    intro y
    obtain ⟨u, hu⟩ := hβs y
    refine ⟨eU.symm u, ?_⟩
    rw [hβ', MulEquiv.apply_symm_apply, hu]
  have hkerβ : ∀ u : ↥((blockU L).subgroupOf (qL L T)), β' u = 1 ↔
      ((u : ↥(qL L T))) ∈ (⊥ : Subgroup ↥(qL L T)) := by
    intro u
    rw [Subgroup.mem_bot, hβ']
    constructor
    · intro h1
      have h2 : eU u ∈ β.ker := h1
      rw [hβk, hZ, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h2
      have h3 : u = 1 := eU.injective (h2.trans (map_one eU).symm)
      rw [h3]
      rfl
    · intro h1
      have h3 : u = 1 := Subtype.ext h1
      rw [h3, map_one, map_one]
  have hinvU : ∀ g ∈ autOn L (qL L T), ∀ u ∈ (blockU L).subgroupOf (qL L T),
      g u ∈ (blockU L).subgroupOf (qL L T) := by
    intro g hg u hu
    obtain ⟨n, hnL, rfl⟩ := Setup.mem_autOn_iff.mp hg
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    rw [Setup.coe_conjAct_apply]
    exact Mod32.conj_mem_blockU (Subgroup.le_normalizer hnL) ⟨_, hu⟩
  have hinvZ : ∀ g ∈ autOn L (qL L T), ∀ z ∈ (⊥ : Subgroup ↥(qL L T)),
      g z ∈ (⊥ : Subgroup ↥(qL L T)) := by
    intro g _ z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hequi : ∀ (γ : L3.Γ) (u : ↥((blockU L).subgroupOf (qL L T)))
      (hu : ((π γ : ↥(autOn L (qL L T))) : MulAut ↥(qL L T)) (u : ↥(qL L T)) ∈
        (blockU L).subgroupOf (qL L T)),
      β' ⟨((π γ : ↥(autOn L (qL L T))) : MulAut ↥(qL L T)) (u : ↥(qL L T)), hu⟩ =
        Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    obtain ⟨ℓ, hℓ⟩ := hαs (e₂ γ)
    have hγ : γ = e₂.symm (α ℓ) := by rw [hℓ, MulEquiv.symm_apply_apply]
    have hπγ : π γ = φ ℓ := by rw [hγ, hπ]
    have e1 : ((eU ⟨((π γ : ↥(autOn L (qL L T))) : MulAut ↥(qL L T)) u, hu⟩ :
        ↥(blockU L)) : G) = ℓ * ((eU u : ↥(blockU L)) : G) * (ℓ : G)⁻¹ := by
      rw [heU, heU]
      show ((((π γ : ↥(autOn L (qL L T))) : MulAut ↥(qL L T)) u : ↥(qL L T)) : G) = _
      rw [hπγ, hφ]
    have e2 := hβe ℓ (eU u) (eU ⟨_, hu⟩) e1
    apply Multiplicative.toAdd.injective
    rw [hβ', hβ', e2]
    show _ = L3.act γ _
    rw [hγ]
    show _ = Matrix.mulVec ((e₂.symm (α ℓ) : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) _
    congr 1
    have h3 := specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) (e₂.symm (α ℓ))
    rw [MulEquiv.apply_symm_apply] at h3
    exact h3
  exact ⟨⟨π, β', hπs, hβs', hkerβ, bot_le, hinvU, hinvZ, hequi⟩⟩

theorem isIndecomp (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥) [IsMulCommutative ↥(qL L T)] :
    IsIndecompModule (autOn L (qL L T)) := by
  have hshort := hLn.1
  have hZ := blockZ_eq_bot h hTL hshort hTC
  have hOQ : pCoreOf 2 L ≤ qL L T := pCoreOf_le_qL hTL
  have hQU := Hyp331.commutator_qL_le_blockU hshort hTL
  have hLQ : L ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hU8 := card_blockU hLn hZ
  have key : ∀ X : Subgroup ↥(qL L T), (∀ g ∈ autOn L (qL L T), ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ blockU L ≤ X.map (qL L T).subtype := by
    intro X hX
    set XG := X.map (qL L T).subtype with hXG
    have hXL : ∀ ℓ ∈ L, ∀ x ∈ XG, ℓ * x * ℓ⁻¹ ∈ XG := by
      intro ℓ hℓ x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hg : conjAct (qL L T) ⟨ℓ, hLQ hℓ⟩ ∈ autOn L (qL L T) :=
        Setup.mem_autOn_iff.mpr ⟨_, hℓ, rfl⟩
      exact ⟨_, hX _ hg y hy, Setup.coe_conjAct_apply _ y⟩
    have hLX : L ≤ Subgroup.normalizer (XG : Set G) := fun ℓ hℓ =>
      Subgroup.mem_normalizer_iff.mpr fun x => ⟨hXL ℓ hℓ x, fun hx => by
        have := hXL ℓ⁻¹ (L.inv_mem hℓ) _ hx
        simpa [mul_assoc] using this⟩
    set W := ⁅XG, L⁆ with hW
    have hWU : W ≤ blockU L :=
      (Subgroup.commutator_mono (Subgroup.map_subtype_le X) le_rfl).trans hQU
    have hWX : W ≤ XG := by
      rw [hW, Subgroup.commutator_le]
      intro x hx ℓ hℓ
      have := XG.mul_mem hx (hXL ℓ hℓ _ (XG.inv_mem hx))
      simpa [commutatorElement_def, mul_assoc] using this
    have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun ℓ hℓ =>
      mem_normalizer_commutator (hLX hℓ) (Subgroup.le_normalizer hℓ)
    rcases hshort.2.2.2.2.2 W (by rw [hZ]; exact bot_le) hWU hLW with hW0 | hW1
    · left
      rw [hZ] at hW0
      rw [eq_bot_iff]
      intro x hx
      have hxL : (x : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro ℓ hℓ
        have h1 : ⁅(x : G), ℓ⁆ ∈ W := Subgroup.commutator_mem_commutator ⟨x, hx, rfl⟩ hℓ
        rw [hW0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      rw [Subgroup.mem_bot]
      exact Subtype.ext (eq_one_of_mem_centralizer h hTC x.2 hxL)
    · right
      rw [← hW1]
      exact hWX
  intro X Y hX hY hXY _
  rcases key X hX with hX0 | hXU
  · exact Or.inl hX0
  rcases key Y hY with hY0 | hYU
  · exact Or.inr hY0
  exfalso
  have h1 : blockU L ≤ (X ⊓ Y).map (qL L T).subtype := by
    rw [Subgroup.map_inf_eq _ _ _ (qL L T).subtype_injective]
    exact le_inf hXU hYU
  rw [hXY, Subgroup.map_bot, le_bot_iff] at h1
  rw [h1, Subgroup.card_bot] at hU8
  norm_num at hU8

theorem card_eq_card_autOn (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hshort : IsShort2 L) (hQe : IsElemAbelian 2 (qL L T)) {B : Subgroup G} (hB : B ≤ L ⊔ T) :
    Nat.card B = Nat.card (autOn B (qL L T)) * Nat.card ↥(B ⊓ qL L T) := by
  have hBN : B ≤ Subgroup.normalizer (qL L T : Set G) :=
    hB.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (InternalSec.autOnHom hBN).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (InternalSec.autOnHom_surjective hBN)).toEquiv] at h1
  have hk : (InternalSec.autOnHom hBN).ker = (B ⊓ qL L T).subgroupOf B := by
    ext b
    rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf]
    constructor
    · intro hb
      exact ⟨b.2, mem_qL_of_centralizer h hTL hshort (hB b.2) hb⟩
    · intro hb
      exact Subgroup.mem_centralizer_iff.mpr fun q hq => comm_of_isElemAbelian hQe hq hb.2
  rw [h1, hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

omit [Finite G] in
theorem map_fixV_autOn [IsMulCommutative ↥(qL L T)] {B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (qL L T : Set G)) :
    (fixV (autOn B (qL L T))).map (qL L T).subtype =
      qL L T ⊓ Subgroup.centralizer (B : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have h1 := hv (conjAct (qL L T) ⟨b, hBN hb⟩) (Setup.mem_autOn_iff.mpr ⟨_, hb, rfl⟩)
    have h2 : b * (v : G) * b⁻¹ = v := by
      have := congrArg Subtype.val h1
      rwa [Setup.coe_conjAct_apply] at this
    calc b * (v : G) = (b * v * b⁻¹) * b := by group
      _ = v * b := by rw [h2]
  · rintro ⟨hxQ, hxC⟩
    refine ⟨⟨x, hxQ⟩, fun g hg => ?_, rfl⟩
    obtain ⟨n, hnB, rfl⟩ := Setup.mem_autOn_iff.mp hg
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    have := Subgroup.mem_centralizer_iff.mp hxC n hnB
    show (n : G) * x * (n : G)⁻¹ = x
    rw [this]
    group

omit [Finite G] in
theorem map_fixV_zpowers [IsMulCommutative ↥(qL L T)] {b : G}
    (hb : b ∈ Subgroup.normalizer (qL L T : Set G)) :
    (fixV (Subgroup.zpowers (conjAct (qL L T) ⟨b, hb⟩))).map (qL L T).subtype =
      qL L T ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers] at hv
    have h2 : b * (v : G) * b⁻¹ = v := by
      have := congrArg Subtype.val hv
      rwa [Setup.coe_conjAct_apply] at this
    refine ⟨v.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (v : G) * b = (b * v * b⁻¹) * b := by rw [h2]
      _ = b * v := by group
  · rintro ⟨hxQ, hxC⟩
    refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers]
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    have := Subgroup.mem_centralizer_singleton_iff.mp hxC
    show b * x * b⁻¹ = x
    rw [← this]
    group

omit [Finite G] in
theorem isElemAbelian2_autOn [IsMulCommutative ↥(qL L T)] {B : Subgroup G}
    (hBe : IsElemAbelian 2 B) : IsElemAbelian2 (autOn B (qL L T)) :=
  CFSG.Quasithin.AutOn.isElemAbelian2_autOn hBe

omit [Finite G] in
theorem autOn_mono {B B' : Subgroup G} (hBB' : B ≤ B') : autOn B (qL L T) ≤ autOn B' (qL L T) :=
  fun g hg => by
    obtain ⟨n, hn, rfl⟩ := Setup.mem_autOn_iff.mp hg
    exact Setup.mem_autOn_iff.mpr ⟨n, hBB' hn, rfl⟩

theorem autOn_le_autOn
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥) :
    autOn T (qL L T) ≤ autOn L (qL L T) := by
  have hLQ : L ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  intro g hg
  obtain ⟨n, hnT, rfl⟩ := Setup.mem_autOn_iff.mp hg
  obtain ⟨ℓ, hℓ, hconj⟩ := exists_mem_conj h38 h39 h hTL hLn hTC (Subgroup.mem_sup_right hnT)
  refine Setup.mem_autOn_iff.mpr ⟨⟨ℓ, hLQ hℓ⟩, hℓ, MulEquiv.ext fun q => Subtype.ext ?_⟩
  rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
  exact (hconj q q.2).symm

theorem insp3_3_25Three_l32
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) (hTC : tC L T = ⊥)
    (hVQ : vPlus L T ≠ qL L T) :
    ¬ IsG2Block L ∧
    (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(qL L T)) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian T B → ¬ B ≤ qL L T →
      ∃ b ∈ B, qL L T ⊓ Subgroup.centralizer (B : Set G) =
        qL L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    ∀ B B' : Subgroup G, IsMaxElemAbelian T B → IsMaxElemAbelian T B' →
      ¬ B ≤ qL L T → ¬ B' ≤ qL L T → B ⊔ qL L T = B' ⊔ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshort := hLn.1
  have hQe := isElemAbelian_qL h38 h39 h hshort hTL hTC
  have : IsMulCommutative ↥(qL L T) := hQe.1
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hQT : qL L T ≤ T := qL_le h
  have hQ16 := card_qL h38 h39 h hTL hLn hTC hVQ
  have hTQ : T ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨D'⟩ := l3Coord h38 h39 h hTL hLn hTC
  have hind := isIndecomp h hTL hLn hTC
  have hV2 : ∀ v : ↥(qL L T), v ^ 2 = 1 := fun v => Subtype.ext (hQe.2 v v.2)
  have H := offHyp_three D' hV2 hQ16 rfl hind
  have hTL' := autOn_le_autOn h38 h39 h hTL hLn hTC
  have hdata : ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B →
      autOn B (qL L T) ≤ autOn L (qL L T) ∧ IsElemAbelian2 (autOn B (qL L T)) ∧
        Nat.card B ≤ Nat.card (autOn B (qL L T)) * Nat.card (fixV (autOn B (qL L T))) := by
    intro B hBT hBe
    have hBN : B ≤ Subgroup.normalizer (qL L T : Set G) := hBT.trans hTQ
    refine ⟨(autOn_mono hBT).trans hTL', isElemAbelian2_autOn hBe, ?_⟩
    rw [card_eq_card_autOn h hTL hshort hQe (hBT.trans le_sup_right)]
    apply Nat.mul_le_mul_left
    have hle : B ⊓ qL L T ≤ qL L T ⊓ Subgroup.centralizer (B : Set G) := fun x hx =>
      ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun b hb => comm_of_isElemAbelian hBe hb hx.1⟩
    rw [← map_fixV_autOn hBN] at hle
    calc Nat.card ↥(B ⊓ qL L T) ≤
          Nat.card ((fixV (autOn B (qL L T))).map (qL L T).subtype) :=
        Subgroup.card_le_of_le hle
      _ = Nat.card (fixV (autOn B (qL L T))) :=
        Subgroup.card_map_of_injective (qL L T).subtype_injective
  have hbQ : ∀ b ∈ T, ∀ hb : b ∈ Subgroup.normalizer (qL L T : Set G),
      conjAct (qL L T) ⟨b, hb⟩ = 1 → b ∈ qL L T := fun b hbT hb h1 =>
    mem_qL_of_centralizer h hTL hshort (Subgroup.mem_sup_right hbT)
      (mem_centralizer_of_conjAct_eq_one _ h1)
  have himg : ∀ B : Subgroup G, IsMaxElemAbelian T B → ¬ B ≤ qL L T →
      Nat.card (autOn B (qL L T)) = 4 ∧ ∀ x ∈ autOn B (qL L T), x ≠ 1 →
        fixV (autOn B (qL L T)) = fixV (Subgroup.zpowers x) := by
    intro B hB hBQ
    obtain ⟨hBL, hBel, hcard⟩ := hdata B hB.1 hB.2.1
    have h16 : 16 ≤ Nat.card B := hQ16 ▸ hB.2.2 _ hQT hQe
    obtain ⟨b, hbB, hbQ'⟩ := Set.not_subset.mp hBQ
    have hbN : b ∈ Subgroup.normalizer (qL L T : Set G) := hTQ (hB.1 hbB)
    have haB : conjAct (qL L T) ⟨b, hbN⟩ ∈ autOn B (qL L T) :=
      Setup.mem_autOn_iff.mpr ⟨_, hbB, rfl⟩
    have ha1 : conjAct (qL L T) ⟨b, hbN⟩ ≠ 1 := fun h1 => hbQ' (hbQ b (hB.1 hbB) hbN h1)
    have hE4 := H.E4 _ hBL hBel
    have hfix := H.card_fixV_le hBL hBel haB ha1
    have h4 : Nat.card (autOn B (qL L T)) = 4 := by nlinarith
    have hfix4 : 4 ≤ Nat.card (fixV (autOn B (qL L T))) := by nlinarith
    exact ⟨h4, fun x hx hx1 => H.fixV_eq_of_card hBL hBel hx hx1 hfix4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨-, -, hidx⟩
    obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := hLn
    have h1 : ((blockZ L).subgroupOf (blockU L)).index = 8 := by
      rw [← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top]
      exact L3Data.card_vec
    rw [h1] at hidx
    norm_num at hidx
  ·
    intro B hBT hBe
    obtain ⟨hBL, hBel, hcard⟩ := hdata B hBT hBe
    by_cases hB1 : autOn B (qL L T) = ⊥
    · have hBQ : B ≤ qL L T := fun b hb => hbQ b (hBT hb) (hTQ (hBT hb)) (by
        have : conjAct (qL L T) ⟨b, hTQ (hBT hb)⟩ ∈ autOn B (qL L T) :=
          Setup.mem_autOn_iff.mpr ⟨_, hb, rfl⟩
        rw [hB1] at this
        exact this)
      exact Subgroup.card_le_of_le hBQ
    · obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
      have ha1' : a ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
      have h1 := H.E4 _ hBL hBel
      have h2 := H.card_fixV_le hBL hBel ha ha1'
      rw [hQ16]
      calc Nat.card B ≤ _ := hcard
        _ ≤ 4 * 4 := Nat.mul_le_mul h1 h2
        _ = 16 := rfl
  ·
    intro B hB hBQ
    obtain ⟨-, hfx⟩ := himg B hB hBQ
    obtain ⟨b, hbB, hbQ'⟩ := Set.not_subset.mp hBQ
    have hbN : b ∈ Subgroup.normalizer (qL L T : Set G) := hTQ (hB.1 hbB)
    have haB : conjAct (qL L T) ⟨b, hbN⟩ ∈ autOn B (qL L T) :=
      Setup.mem_autOn_iff.mpr ⟨_, hbB, rfl⟩
    have ha1 : conjAct (qL L T) ⟨b, hbN⟩ ≠ 1 := fun h1 => hbQ' (hbQ b (hB.1 hbB) hbN h1)
    refine ⟨b, hbB, ?_⟩
    rw [← map_fixV_autOn (hB.1.trans hTQ), hfx _ haB ha1, map_fixV_zpowers hbN]
  ·
    intro B B' hB hB' hBQ hB'Q
    obtain ⟨h4, hfx⟩ := himg B hB hBQ
    obtain ⟨h4', hfx'⟩ := himg B' hB' hB'Q
    obtain ⟨hBL, hBel, -⟩ := hdata B hB.1 hB.2.1
    obtain ⟨hB'L, hB'el, -⟩ := hdata B' hB'.1 hB'.2.1
    set X := autOn B (qL L T) with hX
    set X' := autOn B' (qL L T) with hX'
    set Tb := autOn T (qL L T) with hTb
    have hXT : X ≤ Tb := autOn_mono hB.1
    have hX'T : X' ≤ Tb := autOn_mono hB'.1
    have hp : IsPGroup 2 ↥Tb := hT2.of_surjective (InternalSec.autOnHom hTQ)
      (InternalSec.autOnHom_surjective hTQ)
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hTpos : 0 < Nat.card Tb := by rw [hk]; exact pow_pos (by norm_num) k
    have hT8 : Nat.card Tb ≤ 8 := by
      have hdvd : 2 ^ k ∣ 2 ^ 3 * 21 := by
        rw [← hk, show (2 : ℕ) ^ 3 * 21 = 168 from rfl, ← D'.card_G]
        exact Subgroup.card_dvd_of_le hTL'
      have h8 : 2 ^ k ∣ 2 ^ 3 :=
        (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right hdvd
      rw [hk]
      exact Nat.le_of_dvd (by norm_num) h8
    have hint : 2 ≤ Nat.card ↥(X' ⊓ X) := by
      have r1 := Subgroup.relIndex_mul_card (H := X') (K := X)
      have r2 := Subgroup.relIndex_mul_card (H := X') (K := Tb)
      rw [inf_of_le_left hX'T, h4'] at r2
      have hne : X'.relIndex Tb ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at r2
        omega
      have r3 : X'.relIndex X ≤ X'.relIndex Tb := Subgroup.relIndex_le_of_le_right hXT hne
      rw [h4] at r1
      have hr : X'.relIndex Tb ≤ 2 := by omega
      have hr' : X'.relIndex X ≤ 2 := r3.trans hr
      interval_cases hri : X'.relIndex X <;> omega
    obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := X' ⊓ X)).mp (fun hbot => by
      rw [hbot, Subgroup.card_bot] at hint
      omega)
    have hc1' : c ≠ 1 := fun h1 => hc1 (Subtype.ext h1)
    have hcX' : c ∈ X' := hc.1
    have hcX : c ∈ X := hc.2
    obtain ⟨E, -, hE4, -, hE⟩ := H.El c (hBL hcX) hc1' (hBel.2 c hcX)
    have hXE : ∀ Y : Subgroup (MulAut ↥(qL L T)), Y ≤ autOn L (qL L T) → IsElemAbelian2 Y →
        Nat.card Y = 4 → c ∈ Y → (∀ x ∈ Y, x ≠ 1 → fixV Y = fixV (Subgroup.zpowers x)) →
        Y = E := by
      intro Y hYL hYel hY4 hcY hYfx
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => (hE x).mpr ⟨hYL hx, ?_⟩)
        (by rw [hY4, hE4])
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr ⟨hYel.2 x hx, (hYfx x hx hx1).symm.trans (hYfx c hcY hc1')⟩
    have hXX : X = X' := (hXE X hBL hBel h4 hcX hfx).trans
      (hXE X' hB'L hB'el h4' hcX' hfx').symm
    have key : ∀ B₁ B₂ : Subgroup G, B₁ ≤ T → B₂ ≤ T →
        autOn B₁ (qL L T) = autOn B₂ (qL L T) → B₁ ⊔ qL L T ≤ B₂ ⊔ qL L T := by
      intro B₁ B₂ h1 h2 he
      rw [sup_le_iff]
      refine ⟨fun b hb => ?_, le_sup_right⟩
      have hbN : b ∈ Subgroup.normalizer (qL L T : Set G) := hTQ (h1 hb)
      have hmem : conjAct (qL L T) ⟨b, hbN⟩ ∈ autOn B₂ (qL L T) :=
        he ▸ Setup.mem_autOn_iff.mpr ⟨_, hb, rfl⟩
      obtain ⟨n, hn, hnb⟩ := Setup.mem_autOn_iff.mp hmem
      have hnT : (n : G) ∈ T := h2 hn
      have hq : (n : G)⁻¹ * b ∈ qL L T := by
        refine hbQ _ (T.mul_mem (T.inv_mem hnT) (h1 hb)) (Subgroup.mul_mem _
          (Subgroup.inv_mem _ n.2) hbN) ?_
        have e : (⟨(n : G)⁻¹ * b, Subgroup.mul_mem _ (Subgroup.inv_mem _ n.2) hbN⟩ :
            ↥(Subgroup.normalizer (qL L T : Set G))) = n⁻¹ * ⟨b, hbN⟩ := rfl
        rw [e, map_mul, map_inv, hnb, inv_mul_cancel]
      have e : b = n * ((n : G)⁻¹ * b) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hn hq
    exact le_antisymm (key B B' hB.1 hB'.1 hXX) (key B' B hB'.1 hB.1 hXX.symm)

@[expose] def Insp3_3_25ThreeRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → IsG2Block L → tC L T = ⊥ → vPlus L T ≠ qL L T →
    (∃ _ : IsMulCommutative ↥(vPlus L T), IsFFModule (V := ↥(vPlus L T))
      (autOn (L ⊔ T) (vPlus L T))) → False

theorem insp3_3_25Three_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Insp3_3_25ThreeRest) :
    Insp3_3_25Three := by
  intro G _ _ T M L D h hTL hb hTC hVQ hFF
  rcases hb with hG | hLn
  · exact (hR G T M L D h hTL hG hTC hVQ hFF).elim
  · exact insp3_3_25Three_l32 h38 h39 h hTL hLn hTC hVQ

end ThreeL32

end CFSG.Quasithin.H13
