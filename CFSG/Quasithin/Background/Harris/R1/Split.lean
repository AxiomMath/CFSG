module

public import CFSG.Quasithin.Background.Harris.R1.AbelIndex
public import CFSG.Quasithin.Recognition.F112J2Act
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.Harris.R1.Defs

public section

namespace CFSG.Quasithin.Background.Harris.R1.SplitAux

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.A5Model CFSG.Quasithin.Background.Harris.R1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_iff_mem_pCore {K : Subgroup G} (z : ↥K) :
    (z : G) ∈ pCoreOf 2 K ↔ z ∈ CFSG.Open.pCore 2 ↥K := CFSG.mem_openPCoreOf_iff_open z

omit [Finite G] in
theorem mk_central {K1 H : Subgroup G} (hN : H ≤ Subgroup.normalizer (K1 : Set G))
    {x : G} (hxH : x ∈ H) (hφ : conjOTwoQuot K1 H hN ⟨x, hxH⟩ = 1) (hxK : x ∈ K1) :
    ∀ y : OTwoQuot K1,
      y * (QuotientGroup.mk ⟨x, hxK⟩ : OTwoQuot K1) = (QuotientGroup.mk ⟨x, hxK⟩ : OTwoQuot K1) * y := by
  have hφ' : conjOTwoQuot K1 H hN ⟨x⁻¹, H.inv_mem hxH⟩ = 1 := by
    have : (⟨x⁻¹, H.inv_mem hxH⟩ : ↥H) = (⟨x, hxH⟩ : ↥H)⁻¹ := rfl
    rw [this, map_inv, hφ, inv_one]
  intro y
  induction y using QuotientGroup.induction_on with
  | H k =>
    have hc : x⁻¹ * (k : G)⁻¹ * x⁻¹⁻¹ * (k : G)⁻¹⁻¹ ∈ pCoreOf 2 K1 :=
      commutator_mem_of_conjOTwoQuot_eq_one hN hφ' (K1.inv_mem k.2)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply (mem_pCoreOf_iff_mem_pCore _).mp
    have e : ((k : G) * x)⁻¹ * (x * k) = x⁻¹ * (k : G)⁻¹ * x⁻¹⁻¹ * (k : G)⁻¹⁻¹ := by group
    simpa [e, mul_assoc] using hc

omit [Finite G] in
theorem mem_pCoreOf_of_iso_A5 {K1 H : Subgroup G} (hN : H ≤ Subgroup.normalizer (K1 : Set G))
    (e : OTwoQuot K1 ≃* A5) {x : G} (hxH : x ∈ H) (hφ : conjOTwoQuot K1 H hN ⟨x, hxH⟩ = 1)
    (hxK : x ∈ K1) : x ∈ pCoreOf 2 K1 := by
  have hcen : e (QuotientGroup.mk ⟨x, hxK⟩ : OTwoQuot K1) ∈ Subgroup.center A5 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, mk_central hN hxH hφ hxK y]
  have hbot : Subgroup.center A5 = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hcen
  exact (mem_pCoreOf_iff_mem_pCore (⟨x, hxK⟩ : ↥K1)).mpr ((QuotientGroup.eq_one_iff _).mp hcen)

omit [Finite G] in
theorem mem_sup_mul {K1 S : Subgroup G} (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G}
    (hx : x ∈ K1 ⊔ S) : ∃ k ∈ K1, ∃ s ∈ S, x = k * s := by
  have hconj : ∀ s ∈ S, ∀ k ∈ K1, s * k * s⁻¹ ∈ K1 := fun s hs k hk =>
    (Subgroup.mem_normalizer_iff.mp (hN ((show S ≤ K1 ⊔ S from le_sup_right) hs)) k).mp hk
  let M : Subgroup G :=
    { carrier := {x | ∃ k ∈ K1, ∃ s ∈ S, x = k * s}
      one_mem' := ⟨1, K1.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k1, hk1, s1, hs1, rfl⟩ ⟨k2, hk2, s2, hs2, rfl⟩
        exact ⟨k1 * (s1 * k2 * s1⁻¹), K1.mul_mem hk1 (hconj s1 hs1 k2 hk2), s1 * s2,
          S.mul_mem hs1 hs2, by group⟩
      inv_mem' := by
        rintro _ ⟨k, hk, s, hs, rfl⟩
        exact ⟨s⁻¹ * k⁻¹ * s, by simpa [mul_assoc] using hconj s⁻¹ (S.inv_mem hs) k⁻¹ (K1.inv_mem hk),
          s⁻¹, S.inv_mem hs, by group⟩ }
  have hle : K1 ⊔ S ≤ M :=
    sup_le (fun k hk => ⟨k, hk, 1, S.one_mem, by simp⟩)
      (fun s hs => ⟨1, K1.one_mem, s, hs, by simp⟩)
  exact hle hx

omit [Finite G] in
theorem exists_pow_two_mem {K1 S : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G} (hx : x ∈ K1 ⊔ S) :
    ∃ a : ℕ, x ^ 2 ^ a ∈ K1 := by
  have hconj : ∀ s ∈ S, ∀ k ∈ K1, s * k * s⁻¹ ∈ K1 := fun s hs k hk =>
    (Subgroup.mem_normalizer_iff.mp (hN ((show S ≤ K1 ⊔ S from le_sup_right) hs)) k).mp hk
  have : (K1.subgroupOf (K1 ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hN
  let ψ : ↥S →* (↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion (show S ≤ K1 ⊔ S from le_sup_right))
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, s, hs, hys⟩ := mem_sup_mul hN y.2
    refine ⟨⟨s, hs⟩, ?_⟩
    refine (QuotientGroup.eq).mpr ?_
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (s⁻¹ : G) * (y : G) ∈ K1
    rw [hys]
    simpa [mul_assoc] using hconj s⁻¹ (S.inv_mem hs) k hk
  have hQ := hS2.of_surjective ψ hψ
  obtain ⟨a, ha⟩ := hQ (QuotientGroup.mk (⟨x, hx⟩ : ↥(K1 ⊔ S)))
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
  simpa using ha

theorem ker_two_power {K1 S : Subgroup G} (e : OTwoQuot K1 ≃* A5) (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G} (hx : x ∈ K1 ⊔ S)
    (hφ : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x, hx⟩ = 1) :
    ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_pow_two_mem hS2 hN hx
  have hmem : x ^ 2 ^ a ∈ K1 ⊔ S := (K1 ⊔ S).pow_mem hx _
  have hφ' : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x ^ 2 ^ a, hmem⟩ = 1 := by
    have : (⟨x ^ 2 ^ a, hmem⟩ : ↥(K1 ⊔ S)) = (⟨x, hx⟩ : ↥(K1 ⊔ S)) ^ 2 ^ a := rfl
    rw [this, map_pow, hφ, one_pow]
  have hx' : x ^ 2 ^ a ∈ pCoreOf 2 K1 := mem_pCoreOf_of_iso_A5 hN e hmem hφ' ha
  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K1 ⟨x ^ 2 ^ a, hx'⟩
  have hb' : (x ^ 2 ^ a) ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  refine ⟨a + b, ?_⟩
  rw [pow_add, pow_mul, hb']

omit [Finite G] in
theorem ker_le_pCore_of {K1 S : Subgroup G} {M : Type*} [Group M] (φ : ↥(K1 ⊔ S) →* M)
    (hD2 : ∀ g : ↥(K1 ⊔ S), φ g = 1 → ∃ n : ℕ, (g : G) ^ 2 ^ n = 1)
    {x : G} (hx : x ∈ K1 ⊔ S) (hφ : φ ⟨x, hx⟩ = 1) : x ∈ pCoreOf 2 (K1 ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup G := φ.ker.map (K1 ⊔ S).subtype
  have hDle : D ≤ K1 ⊔ S := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hconj : ∀ g ∈ K1 ⊔ S, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    rintro g hg _ ⟨c, hc, rfl⟩
    exact ⟨⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹, φ.normal_ker.conj_mem c hc ⟨g, hg⟩, by simp⟩
  have hnorm : K1 ⊔ S ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun h => hconj g hg d h, fun h => ?_⟩
    have := hconj g⁻¹ ((K1 ⊔ S).inv_mem hg) _ h
    simpa [mul_assoc] using this
  have hD2' : IsPGroup 2 ↥D := by
    rintro ⟨d, hd⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨n, hn⟩ := hD2 g (MonoidHom.mem_ker.mp hg)
    refine ⟨n, ?_⟩
    ext
    simpa using hn
  have hxD : x ∈ D := ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr hφ, rfl⟩
  exact le_pCoreOf_of_le_normalizer hDle hnorm hD2' hxD

theorem ker_le_pCore {K1 S : Subgroup G} (e : OTwoQuot K1 ≃* A5) (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G} (hx : x ∈ K1 ⊔ S)
    (hφ : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x, hx⟩ = 1) : x ∈ pCoreOf 2 (K1 ⊔ S) :=
  ker_le_pCore_of (conjOTwoQuot K1 (K1 ⊔ S) hN)
    (fun g hg => ker_two_power e hS2 hN g.2 hg) hx hφ

omit [Finite G] in
theorem P_le_ker {K1 S : Subgroup G} (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G}
    (hx : x ∈ pCoreOf 2 K1) :
    conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x, (show K1 ≤ K1 ⊔ S from le_sup_left) (pCoreOf_le 2 K1 hx)⟩ = 1 := by
  apply MulEquiv.ext
  intro q
  rw [MulAut.one_apply]
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [conjOTwoQuot_apply_mk, QuotientGroup.eq]
    apply (mem_pCoreOf_iff_mem_pCore _).mp
    have h1 : k⁻¹ * x * (k⁻¹)⁻¹ ∈ pCoreOf 2 K1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K1 (K1.inv_mem k.2)) x).mp hx
    have h2 : x * (k⁻¹ * x * (k⁻¹)⁻¹)⁻¹ ∈ pCoreOf 2 K1 :=
      (pCoreOf 2 K1).mul_mem hx ((pCoreOf 2 K1).inv_mem h1)
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem ker_iff_P {K1 S : Subgroup G} (e : OTwoQuot K1 ≃* A5) (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G))
    (hO : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1) (g : ↥(K1 ⊔ S)) :
    conjOTwoQuot K1 (K1 ⊔ S) hN g = 1 ↔ (g : G) ∈ pCoreOf 2 K1 := by
  constructor
  · intro hg
    have h := ker_le_pCore e hS2 hN g.2 hg
    rwa [hO] at h
  · intro hg
    exact P_le_ker hN hg

theorem pCore_eq_ker {K1 S : Subgroup G} (e : OTwoQuot K1 ≃* A5) (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G))
    (hO : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1) :
    CFSG.Open.pCore 2 ↥(K1 ⊔ S) = (conjOTwoQuot K1 (K1 ⊔ S) hN).ker := by
  ext g
  rw [MonoidHom.mem_ker, ← mem_pCoreOf_iff_mem_pCore g, hO]
  exact (ker_iff_P e hS2 hN hO g).symm

theorem ker_eq_subgroupOf {K1 S : Subgroup G} (e : OTwoQuot K1 ≃* A5) (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G))
    (hO : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1) :
    (conjOTwoQuot K1 (K1 ⊔ S) hN).ker = (pCoreOf 2 K1).subgroupOf (K1 ⊔ S) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ker_iff_P e hS2 hN hO g

noncomputable def mulAutTransport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    MulAut X ≃* MulAut Y where
  toFun σ := e.symm.trans (σ.trans e)
  invFun τ := e.trans (τ.trans e.symm)
  left_inv σ := MulEquiv.ext fun x => by simp
  right_inv τ := MulEquiv.ext fun y => by simp
  map_mul' σ τ := MulEquiv.ext fun y => by simp [MulAut.mul_apply]

noncomputable def a5AutEquiv : MulAut A5 ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective _ (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num))).symm

noncomputable def thetaEquiv (K1 : Subgroup G) (e : OTwoQuot K1 ≃* A5) :
    MulAut (OTwoQuot K1) ≃* Equiv.Perm (Fin 5) :=
  (mulAutTransport e).trans a5AutEquiv

omit [Finite G] in
theorem card_mulAut_OTwoQuot (K1 : Subgroup G) (e : OTwoQuot K1 ≃* A5) :
    Nat.card (MulAut (OTwoQuot K1)) = 120 := by
  rw [Nat.card_congr (thetaEquiv K1 e).toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  norm_num [Nat.factorial]

omit [Finite G] in
theorem relIndex_pCoreOf_K1 (K1 : Subgroup G) (e : OTwoQuot K1 ≃* A5) :
    (pCoreOf 2 K1).relIndex K1 = 60 := by
  have hP : (pCoreOf 2 K1).subgroupOf K1 = CFSG.Open.pCore 2 ↥K1 := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    exact mem_pCoreOf_iff_mem_pCore z
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm,
      Fintype.card_fin] at h2
    have h120 : Nat.factorial 5 = 120 := by decide
    rw [h120] at h2
    omega
  rw [Subgroup.relIndex, hP, Subgroup.index_eq_card]
  show Nat.card (OTwoQuot K1) = 60
  rw [Nat.card_congr e.toEquiv]
  exact h60

end CFSG.Quasithin.Background.Harris.R1.SplitAux

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.A5Model SplitAux

theorem r1aSplit_holds : ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G),
    R1SettingLegacyBare K1 L2 S Zs → IsL2Quot 2 (OTwoQuot K1) → pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1 →
    S ≤ K1 ∨ Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) := by
  intro G _ _ K1 L2 S Zs h hL24 hO
  by_cases hSK : S ≤ K1
  · exact Or.inl hSK
  refine Or.inr ?_
  have hS2 : IsPGroup 2 ↥S := h.hyp.h1.pgroup
  have hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
    sup_le Subgroup.le_normalizer h.hyp.h1.normalizes
  obtain ⟨e1⟩ := hL24
  obtain ⟨e2⟩ := F112J2.nonempty_psl_four_equiv_alt5
  let e : OTwoQuot K1 ≃* A5 := e1.trans e2
  have hfin : Finite (MulAut (OTwoQuot K1)) :=
    Finite.of_equiv _ (thetaEquiv K1 e).symm.toEquiv
  let φ := conjOTwoQuot K1 (K1 ⊔ S) hN
  have hcardMA : Nat.card (MulAut (OTwoQuot K1)) = 120 := card_mulAut_OTwoQuot K1 e
  have hidx : Nat.card φ.range = 60 * K1.relIndex (K1 ⊔ S) := by
    rw [← Subgroup.index_ker, ker_eq_subgroupOf e hS2 hN hO]
    have hrel := Subgroup.relIndex_mul_relIndex (hHK := pCoreOf_le 2 K1)
      (hKL := (le_sup_left : K1 ≤ K1 ⊔ S))
    rw [relIndex_pCoreOf_K1 K1 e] at hrel
    exact hrel.symm
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have hle : Nat.card φ.range ≤ 120 := by
    rw [← hcardMA]
    exact Subgroup.card_le_card_group _
  have hr1 : K1.relIndex (K1 ⊔ S) ≠ 1 := fun h1 =>
    hSK ((show S ≤ K1 ⊔ S from le_sup_right).trans (Subgroup.relIndex_eq_one.mp h1))
  have hr2 : K1.relIndex (K1 ⊔ S) = 2 := by omega
  have hcard : Nat.card φ.range = Nat.card (MulAut (OTwoQuot K1)) := by
    rw [hcardMA, hidx, hr2]
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact hcard
  have hker := pCore_eq_ker e hS2 hN hO
  let isoTop : φ.range ≃* MulAut (OTwoQuot K1) :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (isoTop.trans (thetaEquiv K1 e)))⟩

end CFSG.Quasithin.Background.Harris.R1

end
