module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup

public section

namespace CFSG.RankThree.PartTwo.Sec18

namespace Item189QProof

open CFSG.OrderReductions.ElementaryRepresentation
open CFSG.PreuniquenessRankFour.Helpers

noncomputable scoped instance frattiniQuotientAction {G : Type} [Group G] (P : Subgroup G) :
    MulDistribMulAction (Subgroup.normalizer (P : Set G)) (↥P ⧸ frattini ↥P) :=
  characteristic_quotient_mulDistribMulAction (frattini ↥P)

theorem smul_mk_frattini {G : Type} [Group G] (P : Subgroup G)
    (x : Subgroup.normalizer (P : Set G)) (y : ↥P) :
    x • (QuotientGroup.mk y : ↥P ⧸ frattini ↥P) = QuotientGroup.mk (x • y) := by
  letI : MulAction.QuotientAction (Subgroup.normalizer (P : Set G)) (frattini ↥P) :=
    characteristic_subgroup_quotientAction (frattini ↥P)
  exact MulAction.Quotient.smul_mk (frattini ↥P) x y

theorem frattini_quotient_mul_comm {G : Type} [Group G] [Finite G] (P : Subgroup G)
    (hP : IsPGroup 2 P) (a b : ↥P ⧸ frattini ↥P) : a * b = b * a := by
  let : CommGroup (↥P ⧸ frattini ↥P) := frattiniQuotientCommGroup 2 hP
  exact mul_comm a b

theorem smul_eq_self_of_mem {G : Type} [Group G] [Finite G] (P : Subgroup G)
    (hP : IsPGroup 2 P) (x : Subgroup.normalizer (P : Set G)) (hx : (x : G) ∈ P)
    (q : ↥P ⧸ frattini ↥P) : x • q = q := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [smul_mk_frattini]
  have hconj : x • y = (⟨(x : G), hx⟩ : ↥P) * y * (⟨(x : G), hx⟩ : ↥P)⁻¹ := Subtype.ext rfl
  rw [hconj, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    frattini_quotient_mul_comm P hP (QuotientGroup.mk ⟨(x : G), hx⟩) (QuotientGroup.mk y),
    mul_inv_cancel_right]

theorem three_not_dvd_card_frattini {G : Type} [Group G] [Finite G] (P : Subgroup G)
    (hP : IsPGroup 2 P) : ¬ 3 ∣ Nat.card (frattini ↥P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_subgroup (frattini ↥P))
  rw [hn]
  intro h
  have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  norm_num at h2

theorem isPGroup_three_zpowers {M : Type} [Group M] {g : M} (hg : g ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := by
  intro s
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp s.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hg, one_zpow]

theorem exists_quot_smul_ne {G : Type} [Group G] [Finite G] (P : Subgroup G)
    (hP : IsPGroup 2 P) (dN : Subgroup.normalizer (P : Set G)) (hd3 : dN ^ 3 = 1)
    (hdnt : ∃ x ∈ P, (dN : G) * x * (dN : G)⁻¹ ≠ x) :
    ∃ q : ↥P ⧸ frattini ↥P, dN • q ≠ q := by
  by_contra hall
  push Not at hall
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := Subgroup.zpowers dN
  letI : MulDistribMulAction H ↥P := MulDistribMulAction.compHom ↥P H.subtype
  have hstab : ∀ q : ↥P ⧸ frattini ↥P,
      H ≤ MulAction.stabilizer (Subgroup.normalizer (P : Set G)) q :=
    fun q => Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (hall q))
  have htriv : ∀ (s : H) (e : ↥P),
      QuotientGroup.mk' (frattini ↥P) (s • e) = QuotientGroup.mk' (frattini ↥P) e := by
    intro s e
    have hs : (s : Subgroup.normalizer (P : Set G)) • (QuotientGroup.mk e : ↥P ⧸ frattini ↥P) =
        QuotientGroup.mk e :=
      MulAction.mem_stabilizer_iff.mp (hstab _ s.2)
    rw [smul_mk_frattini] at hs
    exact hs
  obtain ⟨x, hx, hne⟩ := hdnt
  have hact := coprime_pGroup_action_trivial_of_frattini_trivial 3 (isPGroup_three_zpowers hd3)
    (three_not_dvd_card_frattini P hP) htriv
  have h1 := congrArg Subtype.val (hact ⟨dN, Subgroup.mem_zpowers dN⟩ ⟨x, hx⟩)
  exact hne h1

theorem lift_fixed_of_cube_one {G : Type} [Group G] [Finite G] (P : Subgroup G)
    (hP : IsPGroup 2 P) (c : Subgroup.normalizer (P : Set G)) (hc3 : c ^ 3 = 1)
    (q : ↥P ⧸ frattini ↥P) (hq : c • q = q) :
    ∃ x : ↥P, (QuotientGroup.mk x : ↥P ⧸ frattini ↥P) = q ∧ c • x = x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := Subgroup.zpowers c
  letI : MulDistribMulAction H ↥P := MulDistribMulAction.compHom ↥P H.subtype
  letI : MulAction H (↥P ⧸ frattini ↥P) := MulAction.compHom (↥P ⧸ frattini ↥P) H.subtype
  have hstab : H ≤ MulAction.stabilizer (Subgroup.normalizer (P : Set G)) q :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hq)
  have hfixed : ∀ s : H, s • q = q := fun s => MulAction.mem_stabilizer_iff.mp (hstab s.2)
  have hequiv : ∀ (s : H) (e : ↥P),
      QuotientGroup.mk' (frattini ↥P) (s • e) = s • QuotientGroup.mk' (frattini ↥P) e := by
    intro s e
    show QuotientGroup.mk ((s : Subgroup.normalizer (P : Set G)) • e) =
      (s : Subgroup.normalizer (P : Set G)) • (QuotientGroup.mk e : ↥P ⧸ frattini ↥P)
    rw [smul_mk_frattini]
  have hcop : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (frattini ↥P)).ker := by
    rw [QuotientGroup.ker_mk']
    exact three_not_dvd_card_frattini P hP
  obtain ⟨x, hx, hxfix⟩ := fixedPoint_lifts_of_prime_coprime_kernel 3
    (isPGroup_three_zpowers hc3) (QuotientGroup.mk' (frattini ↥P))
    (QuotientGroup.mk'_surjective (frattini ↥P)) hequiv hcop q hfixed
  exact ⟨x, hx, hxfix ⟨c, Subgroup.mem_zpowers c⟩⟩

theorem exists_rep_fpf_of_kernel {G : Type} [Group G] [Finite G]
    {P K : Subgroup G} (hP : IsPGroup 2 P) (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hOK : CFSG.Open.pCoreOf 2 K ≤ P) {c d : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hdP : d ∈ Subgroup.normalizer (P : Set G))
    (hdnt : ∃ x ∈ P, d * x * d⁻¹ ≠ x)
    (hdK : ∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ P)
    (hcd : ∀ x ∈ P, c * x * c⁻¹ = x → d * x * d⁻¹ = x) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (_ : Nontrivial V) (ρ : Representation (ZMod 2) (↥K ⧸ CFSG.pCore 2 ↥K) V),
      ∀ k : ↥K, (k : G) = c → ∀ v : V,
        ρ (k : ↥K ⧸ CFSG.pCore 2 ↥K) v = v → v = 0 := by
  let : CommGroup (↥P ⧸ frattini ↥P) := frattiniQuotientCommGroup 2 hP
  let : Module (ZMod 2) (Additive (↥P ⧸ frattini ↥P)) := frattiniQuotientModule 2 hP
  let ρN : Representation (ZMod 2) (Subgroup.normalizer (P : Set G))
      (Additive (↥P ⧸ frattini ↥P)) :=
    linearRepresentation 2
      (MulDistribMulAction.toMulAut (Subgroup.normalizer (P : Set G)) (↥P ⧸ frattini ↥P))
  have hρN : ∀ (x : Subgroup.normalizer (P : Set G)) (v : Additive (↥P ⧸ frattini ↥P)),
      ρN x v = Additive.ofMul (x • Additive.toMul v) := fun _ _ => rfl
  have hPtriv : ∀ x : Subgroup.normalizer (P : Set G), (x : G) ∈ P → ρN x = 1 := by
    intro x hx
    ext v
    rw [hρN, smul_eq_self_of_mem P hP x hx, Module.End.one_apply]
    rfl
  let ρ0 : ↥K →* Module.End (ZMod 2) (Additive (↥P ⧸ frattini ↥P)) :=
    MonoidHom.comp ρN (Subgroup.inclusion hKP)
  have hker : CFSG.pCore 2 ↥K ≤ ρ0.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have hnP : (n : G) ∈ P := hOK (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
    exact hPtriv (Subgroup.inclusion hKP n) hnP
  let ρQ : (↥K ⧸ CFSG.pCore 2 ↥K) →* Module.End (ZMod 2) (Additive (↥P ⧸ frattini ↥P)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) ρ0 hker
  have hρQ : ∀ k : ↥K, ρQ (k : ↥K ⧸ CFSG.pCore 2 ↥K) = ρ0 k := fun _ => rfl
  obtain ⟨dN, hdN⟩ : ∃ dN : Subgroup.normalizer (P : Set G), (dN : G) = d := ⟨⟨d, hdP⟩, rfl⟩
  have hdN3 : dN ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hdN]; exact hd3)
  have hdnt' : ∃ x ∈ P, (dN : G) * x * (dN : G)⁻¹ ≠ x := by
    rw [hdN]
    exact hdnt
  have hcomm : ∀ k : ↥K, ρN dN * ρ0 k = ρ0 k * ρN dN := by
    intro k
    have hp : (dN : G) * (k : G) * (dN : G)⁻¹ * (k : G)⁻¹ ∈ P := by
      rw [hdN]
      exact hdK (k : G) k.2
    have hPN := hPtriv ⟨(dN : G) * (k : G) * (dN : G)⁻¹ * (k : G)⁻¹,
      Subgroup.le_normalizer (H := P) hp⟩ hp
    have hrel : dN * Subgroup.inclusion hKP k =
        (⟨(dN : G) * (k : G) * (dN : G)⁻¹ * (k : G)⁻¹, Subgroup.le_normalizer (H := P) hp⟩ :
          Subgroup.normalizer (P : Set G)) * Subgroup.inclusion hKP k * dN :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]; group)
    show ρN dN * ρN (Subgroup.inclusion hKP k) = ρN (Subgroup.inclusion hKP k) * ρN dN
    rw [← map_mul, hrel, map_mul, map_mul, hPN, one_mul]
  have hTcomm : ∀ g : ↥K ⧸ CFSG.pCore 2 ↥K,
      ρQ g * (ρN dN - 1) = (ρN dN - 1) * ρQ g := by
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hρQ k, mul_sub, sub_mul, mul_one, one_mul, hcomm k]
  let W : Subrepresentation ρQ :=
    { toSubmodule := LinearMap.range (ρN dN - 1)
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
        exact LinearMap.mem_range.mpr ⟨ρQ g w, LinearMap.congr_fun (hTcomm g).symm w⟩ }
  obtain ⟨q, hq⟩ := exists_quot_smul_ne P hP dN hdN3 hdnt'
  have hw0 : (ρN dN - 1) (Additive.ofMul q) ≠ 0 := by
    intro h0
    apply hq
    have h1 : ρN dN (Additive.ofMul q) = Additive.ofMul q := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
      exact h0
    rw [hρN] at h1
    exact Additive.ofMul.injective h1
  haveI : Nontrivial W.toSubmodule :=
    ⟨⟨⟨(ρN dN - 1) (Additive.ofMul q), LinearMap.mem_range_self _ _⟩, 0,
      fun h => hw0 (congrArg Subtype.val h)⟩⟩
  haveI : Finite W.toSubmodule := inferInstance
  refine ⟨W.toSubmodule, inferInstance, inferInstance, inferInstance, inferInstance,
    W.toRepresentation, ?_⟩
  intro k hk v hv
  have hv1 : ρQ (k : ↥K ⧸ CFSG.pCore 2 ↥K) v.1 = v.1 :=
    Subrepresentation.toRepresentation_apply_coe.mp hv
  rw [hρQ k] at hv1
  have hfix : Subgroup.inclusion hKP k • Additive.toMul v.1 = Additive.toMul v.1 := by
    have h2 : Additive.ofMul (Subgroup.inclusion hKP k • Additive.toMul v.1) =
        Additive.ofMul (Additive.toMul v.1) := by
      rw [← hρN]
      exact hv1
    exact Additive.ofMul.injective h2
  have hk3 : Subgroup.inclusion hKP k ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_inclusion, hk]
    exact hc3
  obtain ⟨x, hxq, hxc⟩ := lift_fixed_of_cube_one P hP (Subgroup.inclusion hKP k) hk3 _ hfix
  have hcx : c * (x : G) * c⁻¹ = (x : G) := by
    have h := congrArg Subtype.val hxc
    rw [← hk]
    exact h
  have hdx : dN • x = x := by
    apply Subtype.ext
    show (dN : G) * (x : G) * (dN : G)⁻¹ = (x : G)
    rw [hdN]
    exact hcd (x : G) x.2 hcx
  have hδv : ρN dN v.1 = v.1 := by
    rw [hρN]
    have h2 : dN • Additive.toMul v.1 = Additive.toMul v.1 := by
      rw [← hxq, smul_mk_frattini, hdx]
    rw [h2]
    rfl
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp v.2
  have hδ3 : ρN dN ^ 3 = 1 := by
    rw [← map_pow, hdN3, map_one]
  have hkey : (ρN dN ^ 2 + ρN dN + 1) * (ρN dN - 1) = 0 := by
    rw [show (ρN dN ^ 2 + ρN dN + 1) * (ρN dN - 1) = ρN dN ^ 3 - 1 by noncomm_ring, hδ3,
      sub_self]
  have hsum : (ρN dN ^ 2 + ρN dN + 1 :
      Module.End (ZMod 2) (Additive (↥P ⧸ frattini ↥P))) v.1 = 0 := by
    rw [← hw, ← Module.End.mul_apply, hkey]
    rfl
  have hsum' : (ρN dN ^ 2 + ρN dN + 1 :
      Module.End (ZMod 2) (Additive (↥P ⧸ frattini ↥P))) v.1 = v.1 + v.1 + v.1 := by
    simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, hδv]
  have htwo : ∀ y : Additive (↥P ⧸ frattini ↥P), y + y = 0 := fun y => by
    rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 by decide, zero_smul]
  have hcore : v.1 = 0 := by
    rw [hsum'] at hsum
    rw [htwo v.1, zero_add] at hsum
    exact hsum
  exact Subtype.ext hcore

end Item189QProof

end CFSG.RankThree.PartTwo.Sec18

end
