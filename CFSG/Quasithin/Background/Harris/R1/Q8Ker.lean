module

public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Quasithin.Background.Harris.R1.PermHom
public import CFSG.Quasithin.Background.Harris.R1.QbetaOut
public import CFSG.Quasithin.Background.Harris.R1.Split

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem normal_eq_pCore_or_top (hs : IsSimpleGroup (OTwoQuot K1)) {X : Subgroup G} (hXK : X ≤ K1)
    (hXn : ∀ k ∈ K1, ∀ x ∈ X, k * x * k⁻¹ ∈ X) (hQX : pCoreOf 2 K1 ≤ X) :
    X = pCoreOf 2 K1 ∨ K1 ≤ X := by
  let X' : Subgroup ↥K1 := X.subgroupOf K1
  have hX'n : X'.Normal := ⟨fun x hx k => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hXn k k.2 x hx⟩
  let φ : ↥K1 →* OTwoQuot K1 := QuotientGroup.mk' _
  have hY : (X'.map φ).Normal := hX'n.map φ (QuotientGroup.mk'_surjective _)
  haveI := hY
  rcases hs.eq_bot_or_eq_top_of_normal (X'.map φ) with h | h
  · left
    refine le_antisymm (fun x hx => ?_) hQX
    have h1 : φ ⟨x, hXK hx⟩ ∈ X'.map φ := ⟨⟨x, hXK hx⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply] at h1
    exact (SplitAux.mem_pCoreOf_iff_mem_pCore ⟨x, hXK hx⟩).mpr (QuotientGroup.eq_one_iff _ |>.mp h1)
  · right
    intro k hk
    have h1 : φ ⟨k, hk⟩ ∈ X'.map φ := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxk⟩ := h1
    have h2 : (x⁻¹ * ⟨k, hk⟩ : ↥K1) ∈ CFSG.Open.pCore 2 ↥K1 := by
      apply QuotientGroup.eq.mp
      exact hxk
    have h3 : ((x⁻¹ * ⟨k, hk⟩ : ↥K1) : G) ∈ pCoreOf 2 K1 :=
      (SplitAux.mem_pCoreOf_iff_mem_pCore _).mpr h2
    have h4 : (x : G) ∈ X := hx
    have e : k = (x : G) * ((x⁻¹ * ⟨k, hk⟩ : ↥K1) : G) := by simp
    rw [e]
    exact X.mul_mem h4 (hQX h3)

theorem hker_of_simple [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω) (hodd : Odd (Fintype.card Ω))
    (h1 : 1 < Fintype.card Ω) (hs : IsSimpleGroup (OTwoQuot K1)) :
    ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1 := by
  classical
  let X : Subgroup G := C.D.act.ker.map K1.subtype
  have hXK : X ≤ K1 := Subgroup.map_subtype_le _
  have hmemX : ∀ k : ↥K1, (k : G) ∈ X ↔ C.D.act k = 1 := by
    intro k
    constructor
    · rintro ⟨x, hx, hxk⟩
      have : x = k := Subtype.ext hxk
      subst this
      exact hx
    · intro h
      exact ⟨k, h, rfl⟩
  have hXn : ∀ k ∈ K1, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
    intro k hk x hx
    have hxK : x ∈ K1 := hXK hx
    have h2 := (hmemX ⟨x, hxK⟩).mp hx
    have e : k * x * k⁻¹ = ((⟨k, hk⟩ * ⟨x, hxK⟩ * ⟨k, hk⟩⁻¹ : ↥K1) : G) := rfl
    rw [e, hmemX, map_mul, map_mul, h2]
    simp
  have hQX : pCoreOf 2 K1 ≤ X := by
    intro q hq
    have hqK : q ∈ K1 := pCoreOf_le 2 K1 hq
    rw [show q = ((⟨q, hqK⟩ : ↥K1) : G) from rfl, hmemX]
    have h2 : permHom C ⟨q, Subgroup.mem_sup_left hqK⟩ = 1 :=
      (permHom_eq_one_iff C _).mpr (pCoreK1_le_kerM C hodd hq)
    rw [← permHom_K1 C ⟨q, hqK⟩]
    exact h2
  intro k hk
  rcases normal_eq_pCore_or_top hs hXK hXn hQX with h | h
  · rw [← h]
    exact (hmemX k).mpr hk
  · exfalso
    have hall : ∀ k : ↥K1, C.D.act k = 1 := fun k => (hmemX k).mp (h k.2)
    obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card h1 C.D.pt
    obtain ⟨k', hk'⟩ := C.D.trans ω
    rw [hall k'] at hk'
    exact hω hk'.symm

theorem exists_order_seven [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω) (hc9 : Fintype.card Ω = 9)
    (hL : IsL2Quot 3 (OTwoQuot K1)) :
    ∃ t : G, t ∈ K1 ∧ t ∈ borelOf K1 S ∧ orderOf t = 7 := by
  classical
  obtain ⟨e⟩ := hL
  have h504 : Nat.card (OTwoQuot K1) = 504 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by norm_num)]
    norm_num
  letI : MulAction ↥K1 Ω := MulAction.compHom Ω C.D.act
  have : MulAction.IsPretransitive ↥K1 Ω := ⟨fun x y => by
    refine ⟨C.D.kf y * (C.D.kf x)⁻¹, ?_⟩
    show C.D.act (C.D.kf y * (C.D.kf x)⁻¹) x = y
    have h1 : C.D.act (C.D.kf x)⁻¹ x = C.D.pt := by
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact (C.D.kf_spec x).symm
    rw [map_mul, Equiv.Perm.mul_apply, h1, C.D.kf_spec]⟩
  have hidx : (MulAction.stabilizer ↥K1 C.D.pt).index = 9 := by
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, hc9]
  have hK : Nat.card ↥K1 = 504 * Nat.card (CFSG.Open.pCore 2 ↥K1) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K1)
    rw [this]
    exact congrArg (· * _) h504
  have h2 : 9 * Nat.card (MulAction.stabilizer ↥K1 C.D.pt) = Nat.card ↥K1 := by
    rw [← hidx]
    exact Subgroup.index_mul_card _
  have h7 : 7 ∣ Nat.card (MulAction.stabilizer ↥K1 C.D.pt) := by
    have : 7 ∣ 9 * Nat.card (MulAction.stabilizer ↥K1 C.D.pt) := by
      rw [h2, hK]
      exact Dvd.dvd.mul_right (by norm_num) _
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hxs : C.D.act (x : ↥K1) C.D.pt = C.D.pt := MulAction.mem_stabilizer_iff.mp x.2
  refine ⟨((x : ↥K1) : G), (x : ↥K1).2, (C.D.stab _).mp hxs, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

end CFSG.Quasithin.Background.Harris.R1
