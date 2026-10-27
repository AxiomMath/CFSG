module

public import CFSG.Quasithin.H13.U3S1347Z4
public import CFSG.Quasithin.H13.U3S1347Z5

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem autOn_structure_of {H W : Subgroup G} (hred : IsTwoReducedIn H W)
    (hcent : H ⊓ centralizer (W : Set G) = pCoreOf 2 H)
    (hext : F6.IsExtensionWith (↥H ⧸ Open.pCore 2 ↥H)
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) fun N => IsPOnePlusTwo 3 ↥N) :
    ∃ K : Subgroup (MulAut ↥W), K ≤ autOn H W ∧
      (∀ β ∈ autOn H W, ∀ κ ∈ K, β * κ * β⁻¹ ∈ K) ∧ IsPOnePlusTwo 3 ↥K := by
  have hP : H ≤ normalizer (W : Set G) := hred.2.1
  obtain ⟨φ, -, hker⟩ := hext
  have hle : Open.pCore 2 ↥H ≤ (Setup.rho W H hP).ker := by
    intro g hg
    rw [MonoidHom.mem_ker, Setup.rho_eq_one_iff]
    exact pCoreOf_le_centralizer_of_reduced' hred ⟨g, hg, rfl⟩
  set ρ' := QuotientGroup.lift (Open.pCore 2 ↥H) (Setup.rho W H hP) hle with hρ'
  have hρ'mk : ∀ g : ↥H, ρ' (g : ↥H ⧸ Open.pCore 2 ↥H) = Setup.rho W H hP g := fun g =>
    QuotientGroup.lift_mk _ hle g
  have hinj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective d
    rw [hρ'mk, Setup.rho_eq_one_iff] at hd
    have hg : (g : G) ∈ pCoreOf 2 H := by
      rw [← hcent]
      exact ⟨g.2, hd⟩
    obtain ⟨g', hg', hgg'⟩ := hg
    have : g' = g := Subtype.ext hgg'
    rw [QuotientGroup.eq_one_iff, ← this]
    exact hg'
  have hmemX : ∀ d, ρ' d ∈ autOn H W := by
    intro d
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective d
    rw [hρ'mk]
    exact (Setup.mem_autOn_self_iff hP).2 ⟨g, rfl⟩
  refine ⟨φ.ker.map ρ', ?_, ?_, A36B.isPOnePlusTwo_of_mulEquiv
    (Subgroup.equivMapOfInjective φ.ker ρ' hinj) hker⟩
  · rintro _ ⟨d, -, rfl⟩
    exact hmemX d
  · intro β hβ κ hκ
    obtain ⟨g, rfl⟩ := (Setup.mem_autOn_self_iff hP).1 hβ
    obtain ⟨d, hd, rfl⟩ := hκ
    refine ⟨(g : ↥H ⧸ Open.pCore 2 ↥H) * d * (g : ↥H ⧸ Open.pCore 2 ↥H)⁻¹, ?_, ?_⟩
    · exact (MonoidHom.normal_ker φ).conj_mem d hd _
    · rw [map_mul, map_mul, map_inv, hρ'mk]

theorem card_VZ_of (S : A6.Setting134 G T L V) {H : Subgroup G} (hTH : T ≤ H)
    (hred : IsTwoReducedIn H (VZ T H)) (hVT : VZ T H ≤ T)
    (hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 H))
    [IsMulCommutative ↥(VZ T H)] {z : MulAut ↥(VZ T H)}
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzn : ∀ β ∈ autOn H (VZ T H), β * z * β⁻¹ = z ∨ β * z * β⁻¹ = z⁻¹)
    (h6k : ∃ k : ℕ, Nat.card ↥(commAutU3 z).range = 2 ^ (6 * k)) :
    Nat.card ↥(VZ T H) = 2 ^ 6 ∧ fixAutU3 z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : H ≤ normalizer (VZ T H : Set G) := hred.2.1
  have hVc : ∀ a ∈ VZ T H, ∀ b ∈ VZ T H, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ a ∈ VZ T H, a * a = 1 := fun a ha => by
    rw [← sq]
    exact hred.2.2.1.2 a ha
  have hW2 : ∀ w : ↥(VZ T H), w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have hmemX : ∀ g : ↥H, Setup.rho (VZ T H) H hP g ∈ autOn H (VZ T H) := fun g =>
    (Setup.mem_autOn_self_iff hP).2 ⟨g, rfl⟩
  have hinv : ∀ w : ↥(VZ T H), w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← sq, hW2])
  have hXU : ∀ β ∈ autOn H (VZ T H), ∀ u ∈ (commAutU3 z).range, β u ∈ (commAutU3 z).range := by
    intro β hβ u hu
    obtain ⟨v, rfl⟩ := hu
    rcases hzn β hβ with e | e
    · have e' : β * z = z * β := by
        calc β * z = (β * z * β⁻¹) * β := by group
          _ = z * β := by rw [e]
      refine ⟨β v, ?_⟩
      rw [commAutU3_apply, commAutU3_apply, map_mul, map_inv, ← MulAut.mul_apply _ β z, e',
        MulAut.mul_apply]
    · have e' : β * z = z⁻¹ * β := by
        calc β * z = (β * z * β⁻¹) * β := by group
          _ = z⁻¹ * β := by rw [e]
      have hzz : z (z⁻¹ (β v)) = β v := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      refine ⟨z⁻¹ (β v), ?_⟩
      rw [commAutU3_apply, commAutU3_apply, hzz, map_mul, map_inv, ← MulAut.mul_apply _ β z, e',
        MulAut.mul_apply, hinv, hinv, mul_comm]
  set U := (commAutU3 z).range.map (VZ T H).subtype with hUdef
  have hUV : U ≤ VZ T H := map_subtype_le _
  have hNU : H ≤ normalizer (U : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Setup.rho (VZ T H) H hP ⟨g, hg⟩ u, hXU _ (hmemX _) u hu, ?_⟩
      exact Setup.rho_apply_coe hP ⟨g, hg⟩ u
    · rintro ⟨u, hu, hux⟩
      refine ⟨Setup.rho (VZ T H) H hP ⟨g⁻¹, inv_mem hg⟩ u, hXU _ (hmemX _) u hu, ?_⟩
      show g⁻¹ * (u : G) * g⁻¹⁻¹ = x
      have hux' : (u : G) = g * x * g⁻¹ := hux
      rw [hux']
      group
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hVc a (hUV ha) b (hUV hb)
  have hU2 : ∀ a ∈ U, a * a = 1 := fun a ha => hV2 a (hUV ha)
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hTH
  have hO₀T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  obtain ⟨T₁, hQT₁, hT₁T, h21, h22⟩ := exists_chain_two hO₀T (pCoreOf_isPGroup 2 _) hT4
  have hc1 := card_inf_centralizer_le_sq hUc hU2 hQT₁ h21 ((hT₁T.trans hTH).trans hNU)
  have hc2 := card_inf_centralizer_le_sq hUc hU2 hT₁T h22 (hTH.trans hNU)
  rw [inf_eq_left.2 (hUV.trans (le_centralizer_iff.1 (pCoreOf_le_centralizer_of_reduced' hred)))]
    at hc1
  have hU4 : Nat.card ↥U ≤ Nat.card ↥(U ⊓ centralizer (T : Set G)) ^ 4 := by
    calc Nat.card ↥U ≤ _ := hc1
      _ ≤ (Nat.card ↥(U ⊓ centralizer (T : Set G)) ^ 2) ^ 2 := Nat.pow_le_pow_left hc2 2
      _ = _ := by rw [← pow_mul]
  have hCZ : U ⊓ centralizer (T : Set G) ≤ quasithinOmegaOneCenter T :=
    fun x hx => subset_closure ⟨⟨hVT (hUV (mem_inf.1 hx).1), (mem_inf.1 hx).2⟩,
      hred.2.2.1.2 x (hUV (mem_inf.1 hx).1)⟩
  obtain ⟨k, hk⟩ := h6k
  have hUk : Nat.card ↥U = 2 ^ (6 * k) := by
    rw [hUdef, card_map_of_injective (VZ T H).subtype_injective, hk]
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this, mul_zero, pow_zero] at hk
    apply hz1
    refine MulEquiv.ext fun v => ?_
    have h1 : commAutU3 z v = 1 := by
      have := (card_eq_one.1 hk)
      rw [eq_bot_iff] at this
      exact this ⟨v, rfl⟩
    rw [commAutU3_apply, mul_inv_eq_one] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.card ↥(U ⊓ centralizer (T : Set G)) := ⟨_, rfl⟩
  have hc4 : c ∣ 4 := by
    rw [hc, ← hZ4]
    exact card_dvd_of_le hCZ
  have hc64 : 2 ^ 6 ≤ c ^ 4 := by
    have h1 : 2 ^ 6 ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hc]
    exact h1.trans (hUk.symm.le.trans hU4)
  have hc4' : c = 4 := by
    have hcle : c ≤ 4 := Nat.le_of_dvd (by norm_num) hc4
    interval_cases c
    · norm_num at hc64
    · norm_num at hc64
    · norm_num at hc64
    · norm_num at hc4
    · rfl
  have hZU : quasithinOmegaOneCenter T ≤ U := by
    have he : U ⊓ centralizer (T : Set G) = quasithinOmegaOneCenter T :=
      eq_of_le_of_card_ge hCZ (by rw [hZ4, ← hc, hc4'])
    rw [← he]
    exact inf_le_left
  have hVU : VZ T H ≤ U := conjClosure_le fun g hg s hs =>
    (mem_normalizer_iff.1 (hNU hg) s).1 (hZU hs)
  have hUtop : (commAutU3 z).range = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, hu, huw⟩ := hVU w.2
    have : u = w := Subtype.ext huw
    rw [← this]
    exact hu
  refine ⟨?_, ?_⟩
  ·
    have hVeq : Nat.card ↥(VZ T H) = 2 ^ (6 * k) := by
      rw [← hUk, le_antisymm hUV hVU]
    have h8 : 2 ^ (6 * k) ≤ 2 ^ 8 := by
      have := hU4
      rw [hUk, ← hc, hc4'] at this
      calc 2 ^ (6 * k) ≤ 4 ^ 4 := this
        _ = 2 ^ 8 := by norm_num
    have hk' : 6 * k ≤ 8 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h8
    have : k = 1 := by omega
    rw [hVeq, this]
  ·
    rw [eq_bot_iff]
    intro w hw
    rw [mem_bot]
    exact eq_one_of_mem_range_commAutU3 hW2 hz3 (hUtop ▸ mem_top w) hw

theorem le_centralizer_of_E4_of (S : A6.Setting134 G T L V) {H W : Subgroup G} (hTH : T ≤ H)
    (hred : IsTwoReducedIn H W) (hVT : W ≤ T)
    (hTC : T ⊓ centralizer (W : Set G) = pCoreOf 2 H)
    (hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 H)) (hV64 : Nat.card ↥W = 2 ^ 6)
    {z : MulAut ↥W} (hz3 : z ^ 3 = 1) (hzfix : fixAutU3 z = ⊥)
    (hzn : ∀ β ∈ autOn H W, β * z * β⁻¹ = z ∨ β * z * β⁻¹ = z⁻¹) :
    ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : H ≤ normalizer (W : Set G) := hred.2.1
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hTH
  have hCZ : W ⊓ centralizer (T : Set G) ≤ quasithinOmegaOneCenter T :=
    fun x hx => subset_closure ⟨⟨hVT (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩,
      hred.2.2.1.2 x (mem_inf.1 hx).1⟩
  have hS4 : Nat.card ↥(autOn T W) = 4 := by
    rw [card_autOn_eq_relIndex (hTH.trans hP), hTC]
    have h1 := relIndex_mul_card (pCoreOf 2 H) T
    rw [inf_eq_left.2 (pCoreOf_two_le_of_isSylowTwoOf hsyl₀), hT4] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  intro A hA
  by_contra hAC
  have hAH : A ≤ H := hA.1.trans hTH
  have hineq := card_le_relIndex_mul_card hred.2.2.1 hVT hA
  rw [← card_autOn_eq_relIndex (hAH.trans hP), hV64] at hineq
  have hAS : autOn A W ≤ autOn T W := fun φ hφ => by
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    exact Setup.mem_autOn_iff.2 ⟨g, hA.1 hg, rfl⟩
  have hdvd : Nat.card ↥(autOn A W) ∣ 4 := by
    rw [← hS4]
    exact card_dvd_of_le hAS
  have hρA : ∀ a (ha : a ∈ A), Setup.rho W H hP ⟨a, hAH ha⟩ ∈ autOn A W := fun a ha =>
    (Setup.mem_autOn_iff_rho hP hAH).2 ⟨⟨a, hAH ha⟩, ha, rfl⟩
  obtain ⟨a, ha, haC⟩ := IsConcreteLE.not_le_iff_exists.1 hAC
  have hα1 : Setup.rho W H hP ⟨a, hAH ha⟩ ≠ 1 := fun h1 =>
    haC ((Setup.rho_eq_one_iff hP _).1 h1)
  have hA1 : Nat.card ↥(autOn A W) ≠ 1 := fun h1 => by
    have := hρA a ha
    rw [card_eq_one.1 h1, mem_bot] at this
    exact hα1 this
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card ↥(autOn A W) ∣ 2 ^ 2
    from hdvd) with ⟨e, he, hce⟩
  interval_cases e
  · exact hA1 (by rw [hce, pow_zero])
  ·
    rw [pow_one] at hce
    set α := Setup.rho W H hP ⟨a, hAH ha⟩ with hαdef
    have hα2 : α ^ 2 = 1 := sq_eq_one_of_card_le_two hce.le (hρA a ha)
    have hαX : α ∈ autOn H W := (Setup.mem_autOn_self_iff hP).2 ⟨_, rfl⟩
    have h16 := card_fixAutU3_le_sixteen hW2 hV64 hz3 hzfix hα1 hα2 (hzn α hαX)
    have hle : W ⊓ centralizer (A : Set G) ≤ (fixAutU3 α).map W.subtype := by
      intro v hv
      obtain ⟨hvV, hvA⟩ := mem_inf.1 hv
      refine ⟨⟨v, hvV⟩, ?_, rfl⟩
      show α ⟨v, hvV⟩ = ⟨v, hvV⟩
      apply Subtype.ext
      rw [hαdef, Setup.rho_apply_coe]
      show a * v * a⁻¹ = v
      rw [(mem_centralizer_iff.1 hvA) a ha, mul_inv_cancel_right]
    have h1 : Nat.card ↥(W ⊓ centralizer (A : Set G)) ≤ 16 := by
      refine (card_le_of_le hle).trans ?_
      rw [card_map_of_injective W.subtype_injective]
      exact h16
    rw [hce] at hineq
    have : 2 ^ 6 ≤ 2 * 16 := hineq.trans (Nat.mul_le_mul_left _ h1)
    norm_num at this
  ·
    have hAeq : autOn A W = autOn T W :=
      eq_of_le_of_card_ge hAS (by rw [hS4, hce]; norm_num)
    have hle : W ⊓ centralizer (A : Set G) ≤ W ⊓ centralizer (T : Set G) := by
      intro v hv
      obtain ⟨hvV, hvA⟩ := mem_inf.1 hv
      refine mem_inf.2 ⟨hvV, mem_centralizer_iff.2 fun t ht => ?_⟩
      have htA : Setup.rho W H hP ⟨t, hTH ht⟩ ∈ autOn A W := by
        rw [hAeq]
        exact (Setup.mem_autOn_iff_rho hP hTH).2 ⟨⟨t, hTH ht⟩, ht, rfl⟩
      obtain ⟨b, hbA, hbt⟩ := (Setup.mem_autOn_iff_rho hP hAH).1 htA
      have h1 : (b : G) * v * (b : G)⁻¹ = t * v * t⁻¹ := by
        have := congrArg (fun φ : MulAut ↥W => ((φ ⟨v, hvV⟩ : ↥W) : G)) hbt
        simpa only [Setup.rho_apply_coe] using this
      have h2 := (mem_centralizer_iff.1 hvA) (b : G) hbA
      have h3 : t * v * t⁻¹ = v := by
        rw [← h1, h2, mul_inv_cancel_right]
      calc t * v = (t * v * t⁻¹) * t := by group
        _ = v * t := by rw [h3]
    have h1 := (card_le_of_le (hle.trans hCZ)).trans hZ4.le
    rw [hce] at hineq
    have : 2 ^ 6 ≤ 2 ^ 2 * 4 := hineq.trans (Nat.mul_le_mul_left _ h1)
    norm_num at this

theorem thompsonJ_le_of_E4 (S : A6.Setting134 G T L V) {H : Subgroup G} (hTH : T ≤ H)
    (hred : IsTwoReducedIn H (VZ T H)) (hVT : VZ T H ≤ T)
    (hcent : H ⊓ centralizer (VZ T H : Set G) = pCoreOf 2 H)
    (hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 H))
    (hext : F6.IsExtensionWith (↥H ⧸ Open.pCore 2 ↥H)
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) fun N => IsPOnePlusTwo 3 ↥N) :
    thompsonJ T ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKX, hKn, hK⟩ := autOn_structure_of hred hcent hext
  obtain ⟨x, y, hz1, hzc, hexp, hzn⟩ := s1347_exists_z hKn hK
  have : IsMulCommutative ↥(VZ T H) := hred.2.2.1.1
  have hW2 : ∀ w : ↥(VZ T H), w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have h6k := card_range_commAutU3 hW2 hzc hexp
  set z : MulAut ↥(VZ T H) := ((⁅x, y⁆ : ↥K) : MulAut ↥(VZ T H)) with hzdef
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hz3 : z ^ 3 = 1 := by
    have := congrArg Subtype.val (hexp ⁅x, y⁆)
    simpa using this
  obtain ⟨hV64, hzfix⟩ := card_VZ_of S hTH hred hVT hZ4 hT4 hz1' hz3 hzn h6k
  have hTC : T ⊓ centralizer (VZ T H : Set G) = pCoreOf 2 H := by
    rw [← hcent]
    refine le_antisymm (inf_le_inf_right _ hTH) (le_inf ?_ inf_le_right)
    rw [hcent]
    exact pCoreOf_two_le_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hTH)
  have hmod := le_centralizer_of_E4_of S hTH hred hVT hTC hZ4 hT4 hV64 hz3 hzfix hzn
  rw [← hTC]
  exact iSup₂_le fun A hA => le_inf hA.1 (hmod A hA)

end CFSG.Quasithin.H13.U3
