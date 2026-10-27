module

public import CFSG.Quasithin.Vol2.KGFact1297Red
public import CFSG.Quasithin.Vol2.KGFact1295Par

public section

namespace CFSG.Quasithin.H13.KG1295

open CFSG.Open CFSG.Quasithin.H13.KG1296
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_sylow_image [Finite G] {X K S : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X) :
    ∃ T : Sylow 2 (↥K ⧸ CFSG.pCore 2 ↥K), (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) =
      (S.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hSodd⟩ := hS
  let S₀ : Sylow 2 ↥X := hS2.comap_subtype.toSylow hSodd
  have : (K.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hXN g.2) n).1 hn⟩
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S₀ (N := K.subgroupOf X)
  let e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  let ψ : ↥(K.subgroupOf X) →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp e.toMonoidHom
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp e.surjective
  refine ⟨P.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ ((S₀ : Subgroup ↥X) ⊓ K.subgroupOf X).subgroupOf (K.subgroupOf X) := by
      rw [← hP]
      exact hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx'
    exact ⟨e x, hx'.1, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨e.symm k, ?_, ?_⟩
    · have : e.symm k ∈ ((S₀ : Subgroup ↥X) ⊓ K.subgroupOf X).subgroupOf (K.subgroupOf X) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨hk, (e.symm k).2⟩
      rw [← hP] at this
      exact this
    · show QuotientGroup.mk' (CFSG.pCore 2 ↥K) (e (e.symm k)) = _
      rw [MulEquiv.apply_symm_apply]

theorem exists_psi_of_inner [Finite G] {X K S : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKS : K ⊔ S = X)
    (hinn : ∀ s : ↥X, (s : G) ∈ S →
      ∃ z, (actBar K).comp (Subgroup.inclusion hXN) s = MulAut.conj z)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    ∃ ψ : ↥X →* (↥K ⧸ CFSG.pCore 2 ↥K),
      (∀ k (hk : k ∈ K), ψ ⟨k, hKX hk⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩) ∧
      (∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ centralizerMod (pCoreOf 2 K) X K) ∧
      ∀ x : ↥X, MulAut.conj (ψ x) = (actBar K).comp (Subgroup.inclusion hXN) x := by
  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (actBar K).comp (Subgroup.inclusion hXN)
    with hφ
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hconj : Function.Injective
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw := congrArg (fun f : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => f w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at hw
      calc w * z = (z * w * z⁻¹) * z := by rw [hw]
        _ = z * w := by group
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hφK : ∀ k (hk : k ∈ K), φ ⟨k, hKX hk⟩ = MulAut.conj (π ⟨k, hk⟩) := fun k hk =>
    actBar_of_mem _ hk
  have hSX : S ≤ X := hKS ▸ le_sup_right
  have hrange : φ.range ≤
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range := by
    have htop : K.subgroupOf X ⊔ S.subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKX hSX, hKS, Subgroup.subgroupOf_self]
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨⟨k, hkX⟩, hk, rfl⟩
      exact ⟨π ⟨k, hk⟩, (hφK k hk).symm⟩
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨z, hz⟩ := hinn s hs
      exact ⟨z, hz.symm⟩
  set e := MonoidHom.ofInjective hconj with he
  set ψ : ↥X →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    e.symm.toMonoidHom.comp (φ.codRestrict _ fun x => hrange ⟨x, rfl⟩) with hψ
  have hconjψ : ∀ x, MulAut.conj (ψ x) = φ x := by
    intro x
    have h : ((e (ψ x) : ↥(MonoidHom.range _)) : MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) =
        MulAut.conj (ψ x) := MonoidHom.ofInjective_apply hconj
    rw [← h]
    show ((e (e.symm ⟨φ x, _⟩) : ↥(MonoidHom.range _)) : MulAut _) = φ x
    rw [MulEquiv.apply_symm_apply]
  refine ⟨ψ, fun k hk => hconj ?_, fun x => ?_, hconjψ⟩
  · rw [hconjψ, hφK]
  · rw [← hconj.eq_iff, map_one, hconjψ, hφ, MonoidHom.comp_apply]
    exact (mem_centralizerMod_iff hXN x.2).symm

section Lift

variable {X : Subgroup G} {M : Type} [Group M] (ρ : ↥X →* M)

theorem img_mem_oTwoUpper {P : Subgroup G} (hPX : P ≤ X) {y : G} (hy : y ∈ oTwoUpper P) :
    ρ ⟨y, hPX (oTwoUpper_le P hy)⟩ ∈ oTwoUpper ((P.subgroupOf X).map ρ) := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine mem_oTwoUpper_of_odd ⟨⟨x, hPX hx.1⟩, hx.1, rfl⟩ (Odd.of_dvd_nat hx.2 ?_)
    rw [← Subgroup.orderOf_mk x (hPX hx.1)]
    exact orderOf_map_dvd ρ _
  | one =>
    have e : (⟨1, hPX (oTwoUpper_le P (Subgroup.one_mem _))⟩ : ↥X) = 1 := rfl
    rw [e, map_one]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, hPX (oTwoUpper_le P (Subgroup.mul_mem _ hx hy))⟩ : ↥X) =
        ⟨x, hPX (oTwoUpper_le P hx)⟩ * ⟨y, hPX (oTwoUpper_le P hy)⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
    have e : (⟨x⁻¹, hPX (oTwoUpper_le P (Subgroup.inv_mem _ hx))⟩ : ↥X) =
        (⟨x, hPX (oTwoUpper_le P hx)⟩ : ↥X)⁻¹ := rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ ih

variable [Finite G]

theorem exists_of_parOut [Finite M] {S B : Subgroup G} (hρ : Function.Surjective ρ)
    (hker2 : IsPGroup 2 ρ.ker) (hkerS : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ S) (hSX : S ≤ X)
    (hBX : B ≤ X) (hSB : S ≤ Subgroup.normalizer (B : Set G)) (hBO : oTwoUpper B = B)
    {P₀ : Subgroup M} (h : ParOut ((S.subgroupOf X).map ρ) ((B.subgroupOf X).map ρ) P₀) :
    ∃ P : Subgroup G, S ≤ P ∧ P ≤ X ∧ (∀ Y : Subgroup G, S ≤ Y → Y ≤ P → Y = S ∨ Y = P) ∧
      (∃ y ∈ P, orderOf y = 3) ∧ P ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅B, oTwoUpper P⁆ ≤ pCoreOf 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTP, hmax, ⟨y₀, hy₀P, hy₀⟩, hN, hcomm⟩ := h
  set Bh := (B.subgroupOf X).map ρ with hBh
  set P : Subgroup G := (P₀.comap ρ).map X.subtype with hPdef
  have hPX : P ≤ X := Subgroup.map_subtype_le _
  have hmemP : ∀ x (hx : x ∈ X), x ∈ P ↔ ρ ⟨x, hx⟩ ∈ P₀ := by
    intro x hx
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact hx'
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hPimg : (P.subgroupOf X).map ρ = P₀ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmemP x x.2).1 hx
    · intro hz
      obtain ⟨x, rfl⟩ := hρ z
      exact ⟨x, (hmemP x x.2).2 hz, rfl⟩
  have hSP : S ≤ P := fun s hs => (hmemP s (hSX hs)).2 (hTP ⟨⟨s, hSX hs⟩, hs, rfl⟩)
  have hpow_ker : ∀ x : ↥X, ρ x = 1 → ∃ a : ℕ, x ^ 2 ^ a = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := hker2 ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  have hPN : P ≤ Subgroup.normalizer (B : Set G) := by
    refine le_normalizer_of_forall fun p hp b hb => ?_
    have hpX := hPX hp
    have hρp : ρ ⟨p, hpX⟩ ∈ P₀ := (hmemP p hpX).1 hp
    have hle : B.map (MulAut.conj p).toMonoidHom ≤ B := by
      have hO : oTwoUpper (B.map (MulAut.conj p).toMonoidHom) =
          B.map (MulAut.conj p).toMonoidHom := by
        rw [oTwoUpper_map, hBO]
      rw [← hO]
      refine oTwoUpper_le_of_pow_mem fun x hx => ?_
      obtain ⟨b', hb', rfl⟩ := hx
      have hb'X := hBX hb'
      have hxX : p * b' * p⁻¹ ∈ X := X.mul_mem (X.mul_mem hpX hb'X) (X.inv_mem hpX)
      show ∃ k : ℕ, (p * b' * p⁻¹) ^ 2 ^ k ∈ B
      have hρx : ρ ⟨p * b' * p⁻¹, hxX⟩ ∈ Bh := by
        have e : (⟨p * b' * p⁻¹, hxX⟩ : ↥X) = ⟨p, hpX⟩ * ⟨b', hb'X⟩ * (⟨p, hpX⟩ : ↥X)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 (hN hρp) _).1 ⟨⟨b', hb'X⟩, hb', rfl⟩
      obtain ⟨b'', hb'', hρb⟩ := hρx
      set d : ↥X := b''⁻¹ * ⟨p * b' * p⁻¹, hxX⟩ with hd
      have hd1 : ρ d = 1 := by rw [hd, map_mul, map_inv, hρb, inv_mul_cancel]
      obtain ⟨a, ha⟩ := hpow_ker d hd1
      obtain ⟨b₀, hb₀, e⟩ := CFSG.Quasithin.A4.exists_pow_mul_eq (H := B) (x := (b'' : G))
        (r := (d : G)) hb'' (hSB (hkerS d hd1)) (2 ^ a)
      have e2 : (b'' : G) * (d : G) = p * b' * p⁻¹ := by
        rw [hd]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      have ha' : (d : G) ^ 2 ^ a = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      refine ⟨a, ?_⟩
      rw [← e2, e, ha', mul_one]
      exact hb₀
    exact hle ⟨b, hb, rfl⟩
  refine ⟨P, hSP, hPX, fun Y hSY hYP => ?_, ?_, hPN, ?_⟩
  ·
    have hYX : Y ≤ X := hYP.trans hPX
    have h1 : (S.subgroupOf X).map ρ ≤ (Y.subgroupOf X).map ρ :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono X hSY)
    have h2 : (Y.subgroupOf X).map ρ ≤ P₀ := by
      rw [← hPimg]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hYP)
    rcases hmax _ h1 h2 with h | h
    · left
      exact le_antisymm (KG1297.le_of_img_le ρ hYX hkerS h.le) hSY
    · right
      refine le_antisymm hYP (KG1297.le_of_img_le ρ hPX (fun x hx => hSY (hkerS x hx)) ?_)
      rw [hPimg, h]
  ·
    have h3 : 3 ∣ Nat.card P := by
      have h1 : 3 ∣ Nat.card P₀ := by
        rw [← hy₀, ← Subgroup.orderOf_mk y₀ hy₀P]
        exact orderOf_dvd_natCard _
      have h2 : Nat.card P₀ ∣ Nat.card (P₀.comap ρ) := by
        conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective hρ P₀]
        exact Subgroup.card_map_dvd _ _
      have h3 : Nat.card P = Nat.card (P₀.comap ρ) :=
        Subgroup.card_map_of_injective X.subtype_injective
      rw [h3]
      exact h1.trans h2
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3
    exact ⟨y, y.2, by rw [Subgroup.orderOf_coe, hy]⟩
  ·
    refine Subgroup.commutator_le.2 fun b hb y hy => ?_
    have hyP := oTwoUpper_le P hy
    have hyX := hPX hyP
    have hbX := hBX hb
    set N : Subgroup G := B ⊓ ((pCoreOf 2 Bh).comap ρ).map X.subtype with hNdef
    have hNB : N ≤ B := inf_le_left
    have hBN : B ≤ Subgroup.normalizer (N : Set G) := by
      refine le_normalizer_of_forall fun a ha z hz => ?_
      obtain ⟨hzB, ⟨z', hz', rfl⟩⟩ := hz
      have haX := hBX ha
      refine ⟨B.mul_mem (B.mul_mem ha hzB) (B.inv_mem ha),
        ⟨⟨a, haX⟩ * z' * (⟨a, haX⟩ : ↥X)⁻¹, ?_, rfl⟩⟩
      show ρ (⟨a, haX⟩ * z' * (⟨a, haX⟩ : ↥X)⁻¹) ∈ pCoreOf 2 Bh
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Bh
        ⟨⟨a, haX⟩, ha, rfl⟩) _).1 hz'
    have hN2 : IsPGroup 2 N := by
      rintro ⟨_, hzB, ⟨z', hz', rfl⟩⟩
      obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Bh ⟨_, hz'⟩
      have h1 : ρ (z' ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val ha
      obtain ⟨c, hc⟩ := hpow_ker _ h1
      refine ⟨a + c, Subtype.ext ?_⟩
      have := congrArg Subtype.val hc
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNB hBN hN2 ?_
    have hcB : ⁅b, y⁆ ∈ B := by
      rw [commutatorElement_def]
      have := (Subgroup.mem_normalizer_iff.1 (hPN hyP) b⁻¹).1 (B.inv_mem hb)
      rw [mul_assoc, mul_assoc, ← mul_assoc y]
      exact B.mul_mem hb this
    have hcX : ⁅b, y⁆ ∈ X := hBX hcB
    refine ⟨hcB, ⟨⟨⁅b, y⁆, hcX⟩, ?_, rfl⟩⟩
    have e : (⟨⁅b, y⁆, hcX⟩ : ↥X) = ⁅(⟨b, hbX⟩ : ↥X), ⟨y, hyX⟩⁆ := rfl
    show ρ ⟨⁅b, y⁆, hcX⟩ ∈ pCoreOf 2 Bh
    rw [e, map_commutatorElement]
    refine hcomm (Subgroup.commutator_mem_commutator ⟨⟨b, hbX⟩, hb, rfl⟩ ?_)
    have := img_mem_oTwoUpper ρ hPX hy
    rwa [hPimg] at this

end Lift

end CFSG.Quasithin.H13.KG1295
