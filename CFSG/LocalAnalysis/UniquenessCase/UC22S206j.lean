module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.UniquenessCase.UC6C634b
import CFSG.LocalAnalysis.UniquenessCase.UCKUnfaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Matrix IsMulCommutative
open CFSG.RankThree.FFModules (fixSub)

section D

variable {H : Type} [Group H]

theorem uc22s206j_commutator_ne_bot {Q : Subgroup H} {R : Subgroup ↥Q} {p d : ℕ} (hp : p.Prime)
    (e : ↥R ⧸ frattini ↥R ≃* Multiplicative (Fin d → ZMod p))
    (φ : H →* GL (Fin d) (ZMod p))
    (hφ : ∀ (g : H) (x y : ↥R), ((y : ↥Q) : H) = g * ((x : ↥Q) : H) * g⁻¹ →
      (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
          Multiplicative.toAdd (e (x : ↥R ⧸ frattini ↥R)) =
        Multiplicative.toAdd (e (y : ↥R ⧸ frattini ↥R)))
    {g h : H} (hhg : h * g * h⁻¹ = g ^ 2)
    (h6 : 6 ≤ Module.finrank (ZMod p) (LinearMap.range
      ((Matrix.mulVecLin ((φ g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1))) :
    ⁅zpowers h, R.map Q.subtype⁆ ≠ ⊥ := by
  intro hbot
  have hfix : ∀ v : Fin d → ZMod p,
      ((φ h : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ v = v := by
    intro v
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd v)
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    have hc := commutator_mem_commutator (mem_zpowers h) (mem_map_of_mem Q.subtype r.2)
    rw [hbot, mem_bot, commutatorElement_def, mul_inv_eq_one] at hc
    have h1 := hφ h r r hc.symm
    rwa [hq, toAdd_ofAdd] at h1
  have hφh : φ h = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    exact hfix v
  have hφg : φ g = 1 := by
    have h1 := congrArg φ hhg
    rw [map_mul, map_mul, map_inv, hφh, one_mul, inv_one, mul_one, map_pow, sq] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (φ g)).symm)
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  rw [LinearMap.range_eq_bot.mpr ?_, finrank_bot] at h6
  · omega
  · rw [hφg, Units.val_one, Matrix.mulVecLin_one]
    exact sub_self _

end D

theorem uc22s206j_inf_centralizer_ne_bot {Mg : Type} [Group Mg] [Finite Mg]
    (hchar : centralizer (CFSG.pCore 2 Mg : Set Mg) ≤ CFSG.pCore 2 Mg)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : Mg} (hx3 : orderOf x = 3)
    {D : Subgroup (Mg ⧸ CFSG.pCore 2 Mg)} (hD : IsPGroup p D)
    (hxD : QuotientGroup.mk' (CFSG.pCore 2 Mg) x ∈ normalizer (D : Set (Mg ⧸ CFSG.pCore 2 Mg)))
    (hDx : ⁅zpowers (QuotientGroup.mk' (CFSG.pCore 2 Mg) x), D⁆ ≠ ⊥) :
    CFSG.pCore 2 Mg ⊓ centralizer (zpowers x : Set Mg) ≠ ⊥ := by
  intro hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 Mg) := CFSG.pCore_isPGroup
  haveI : IsElementaryAbelian 2 (↥(CFSG.pCore 2 Mg) ⧸ frattini ↥(CFSG.pCore 2 Mg)) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hQ2).2.2.2.1
  have hker : CFSG.pCore 2 Mg ≤ (UC6.frattiniRep (CFSG.pCore 2 Mg)).ker := fun q hq =>
    MonoidHom.mem_ker.mpr (UC6.frattiniRep_eq_one_of_mem_uc6 (CFSG.pCore 2 Mg) hq)
  have hkerle : (UC6.frattiniRep (CFSG.pCore 2 Mg)).ker ≤ CFSG.pCore 2 Mg := by
    refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker _) ?_
    refine IsPGroup.iff_orderOf.2 fun g => ?_
    obtain ⟨c, hc⟩ := UC6.exists_two_pow_orderOf_of_rep_eq_one_uc6 (CFSG.pCore 2 Mg) hQ2 hchar
      (x := (g : Mg)) (MonoidHom.mem_ker.mp g.2)
    exact ⟨c, by rw [← Subgroup.orderOf_coe, hc]⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Representation (ZMod 2) (Mg ⧸ CFSG.pCore 2 Mg)
      (Additive (↥(CFSG.pCore 2 Mg) ⧸ frattini ↥(CFSG.pCore 2 Mg))),
      ∀ g : Mg, ρ (QuotientGroup.mk' (CFSG.pCore 2 Mg) g) =
        UC6.frattiniRep (CFSG.pCore 2 Mg) g :=
    ⟨QuotientGroup.lift (CFSG.pCore 2 Mg) (UC6.frattiniRep (CFSG.pCore 2 Mg)) hker,
      fun _ => rfl⟩
  have hfaith : ∀ t : Mg ⧸ CFSG.pCore 2 Mg, ρ t = 1 → t = 1 := by
    intro t ht
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Mg) t
    rw [hρ] at ht
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hkerle (MonoidHom.mem_ker.mpr ht)
  have hx3' : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Mg) x) = 3 := by
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Mg) x) ∣ 3 := by
      rw [← hx3]
      exact orderOf_map_dvd _ x
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exfalso
      have hxQ : x ∈ CFSG.pCore 2 Mg := by
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 Mg), MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp h1
      obtain ⟨n, hn⟩ := hQ2.exists_card_eq
      have h3 : 3 ∣ 2 ^ n := by
        have h' := orderOf_dvd_natCard (⟨x, hxQ⟩ : ↥(CFSG.pCore 2 Mg))
        rwa [Subgroup.orderOf_mk, hx3, hn] at h'
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)) (by decide)
    · exact h1
  have hX3 : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx3, pow_one])
  have hfix0 := UC6.fixSub_frattini_eq_bot_uc6 (CFSG.pCore 2 Mg) hQ2 (p := 3) (by norm_num)
    (zpowers x) hX3 hbot
  have hfix : UCK.fixV ρ (zpowers (QuotientGroup.mk' (CFSG.pCore 2 Mg) x)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : v ∈ fixSub (UC6.frattiniRep (CFSG.pCore 2 Mg)) (zpowers x) := by
      intro a ha
      rw [← hρ]
      refine hv _ ?_
      rw [← MonoidHom.map_zpowers]
      exact mem_map_of_mem _ ha
    rw [hfix0] at hv'
    exact hv'
  have hXD : zpowers (QuotientGroup.mk' (CFSG.pCore 2 Mg) x) ≤
      normalizer (D : Set (Mg ⧸ CFSG.pCore 2 Mg)) := zpowers_le.mpr hxD
  have hD3 : ¬ 3 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hXp : IsPGroup 3 (zpowers (QuotientGroup.mk' (CFSG.pCore 2 Mg) x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3', pow_one])
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three _ D hXp hD3 hXD
  have hQD : ⁅D, zpowers (QuotientGroup.mk' (CFSG.pCore 2 Mg) x)⁆ ≤ D :=
    le_normalizer_iff_commutator_le_left.mp hXD
  have hQne : ⁅D, zpowers (QuotientGroup.mk' (CFSG.pCore 2 Mg) x)⁆ ≠ ⊥ := by
    rw [commutator_comm]
    exact hDx
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  obtain ⟨h2, -⟩ := UCK.k42_unfaithful ρ (q := p) (r := 3) hp Nat.prime_three hp2 (by norm_num)
    hp3 (by rw [Nat.card_zpowers, hx3']) hfix (hD.to_le hQD)
    ⟨t, t.2, fun h => ht1 (Subtype.ext (hfaith _ h))⟩ (normalizer_commutator_ge_right _ _)
    ((commutator_comm _ _).trans hidem)
  exact hp2 h2

theorem uc22s206j_pCoreOf_inf_centralizer_ne_bot {G : Type} [Group G] [Finite G]
    {M K : Subgroup G} (hKM : K ≤ M)
    (hchar : M ⊓ centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {R : Subgroup ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))} [R.Characteristic] {d : ℕ}
    (e : ↥R ⧸ frattini ↥R ≃* Multiplicative (Fin d → ZMod p))
    (φ : (↥M ⧸ CFSG.pCore 2 ↥M) →* GL (Fin d) (ZMod p))
    (hφ : ∀ (g : ↥M ⧸ CFSG.pCore 2 ↥M) (x y : ↥R),
      ((y : ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))) : ↥M ⧸ CFSG.pCore 2 ↥M) =
          g * ((x : ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))) : ↥M ⧸ CFSG.pCore 2 ↥M) * g⁻¹ →
        (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
            Multiplicative.toAdd (e (x : ↥R ⧸ frattini ↥R)) =
          Multiplicative.toAdd (e (y : ↥R ⧸ frattini ↥R)))
    {x y : ↥K} (hx3 : orderOf x = 3) (hxy : x * y * x⁻¹ = y ^ 2)
    (h6 : 6 ≤ Module.finrank (ZMod p) (LinearMap.range
      ((Matrix.mulVecLin
        (((φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM))) y :
          GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1))) :
    CFSG.Open.pCoreOf 2 M ⊓ centralizer (zpowers (x : G) : Set G) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcharM : centralizer (CFSG.pCore 2 ↥M : Set ↥M) ≤ CFSG.pCore 2 ↥M := by
    intro m hm
    have hmG : (m : G) ∈ M ⊓ centralizer (CFSG.Open.pCoreOf 2 M : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨m.2, mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hm q hq)
    obtain ⟨q, hq, hqm⟩ := hchar hmG
    rwa [show q = m from Subtype.ext hqm] at hq
  have hxM3 : orderOf (Subgroup.inclusion hKM x) = 3 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective hKM) x, hx3]
  have hQp : IsPGroup p ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) := CFSG.pCore_isPGroup
  have hD : IsPGroup p ↥(R.map (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)).subtype) :=
    (hQp.to_subgroup R).map _
  have hxD : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hKM x) ∈
      normalizer ((R.map (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)).subtype :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top _
  have hDx := uc22s206j_commutator_ne_bot hp e φ hφ
    (g := QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hKM y))
    (h := QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hKM x)) (by
      have h1 := congrArg
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)) hxy
      rwa [map_mul, map_mul, map_inv, map_pow] at h1) h6
  have hne := uc22s206j_inf_centralizer_ne_bot hcharM hp hp2 hp3 hxM3 hD hxD hDx
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨((z : ↥M) : G), Subgroup.mem_inf.mpr
    ⟨⟨z, (Subgroup.mem_inf.mp z.2).1, rfl⟩, mem_centralizer_iff.mpr fun s hs => ?_⟩⟩, ?_⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
    have hc := congrArg Subtype.val (mem_centralizer_iff.mp (Subgroup.mem_inf.mp z.2).2
      (Subgroup.inclusion hKM x ^ k) (zpow_mem_zpowers _ k))
    simpa using hc
  · intro h1
    have h2 : ((z : ↥M) : G) = 1 := congrArg Subtype.val h1
    exact hz1 (Subtype.ext (Subtype.ext h2))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
