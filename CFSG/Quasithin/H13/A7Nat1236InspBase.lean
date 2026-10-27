module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.H13.A7Coordinates

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin
open scoped Pointwise

theorem nat_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem isSimpleGroup_alt_six : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)

theorem card_alt_six_dvd {Y : Type*} [Group Y] [Finite Y] {f : Y →* alternatingGroup (Fin 6)}
    (hf : Function.Surjective f) : 360 ∣ Nat.card Y := by
  rw [← nat_card_alt_six]
  exact Subgroup.card_dvd_of_surjective hf

theorem le_ker_of_isPGroup_normal {Y : Type*} [Group Y] [Finite Y]
    {f : Y →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) {N : Subgroup Y}
    (hN : N.Normal) (hN2 : IsPGroup 2 N) : N ≤ f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := isSimpleGroup_alt_six
  rw [← Subgroup.map_eq_bot_iff]
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ (hN.map f hf) with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup 2 (N.map f) := hN2.map f
    rw [h] at h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [card_top, nat_card_alt_six] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem false_of_surj_alt_six_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hcard : Nat.card S ≠ 360) {g : S →* alternatingGroup (Fin 6)} (hg : Function.Surjective g) :
    False := by
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker with h | h
    · exact h
    · exfalso
      have h1 : ∀ a : alternatingGroup (Fin 6), a = 1 := fun a => by
        obtain ⟨x, rfl⟩ := hg a
        exact (MonoidHom.mem_ker).1 (h ▸ mem_top x)
      have h2 : Nat.card (alternatingGroup (Fin 6)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, inferInstance⟩
      rw [nat_card_alt_six] at h2
      norm_num at h2
  apply hcard
  rw [← nat_card_alt_six]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hg⟩)

theorem false_of_surj_alt_six_of_twoKer {B S : Type*} [Group B] [Finite B] [Group S] [Finite S]
    [IsSimpleGroup S] (hcard : Nat.card S ≠ 360) {h : B →* S} (hh : Function.Surjective h)
    (hker : IsPGroup 2 h.ker) {g : B →* alternatingGroup (Fin 6)}
    (hg : Function.Surjective g) : False := by
  have hle : h.ker ≤ g.ker := le_ker_of_isPGroup_normal hg h.normal_ker hker
  let g' : S →* alternatingGroup (Fin 6) :=
    (QuotientGroup.lift h.ker g hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective h hh).symm.toMonoidHom
  have hg' : Function.Surjective g' := by
    intro a
    obtain ⟨x, rfl⟩ := hg a
    refine ⟨h x, ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective h hh).symm (h x) =
        (QuotientGroup.mk x : B ⧸ h.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift h.ker g hle
      ((QuotientGroup.quotientKerEquivOfSurjective h hh).symm (h x)) = g x
    rw [h1]
    rfl
  exact false_of_surj_alt_six_of_simple hcard hg'

theorem commutator_alt_six : commutator (alternatingGroup (Fin 6)) = ⊤ :=
  commutator_alternatingGroup_eq_top (by rw [Nat.card_fin]; norm_num)

theorem not_isPGroup_of_surj_alt_six {Y : Type*} [Group Y] {f : Y →* alternatingGroup (Fin 6)}
    (hf : Function.Surjective f) : ¬ IsPGroup 2 Y := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : IsPGroup 2 (alternatingGroup (Fin 6)) := h2.of_surjective f hf
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2'
  rw [nat_card_alt_six] at hk
  have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem exists_surj_of_ker_le {W Z Q : Type*} [Group W] [Group Z] [Group Q] (ρ : W →* Z)
    {θ : W →* Q} (hθ : Function.Surjective θ) (h : ∀ w, ρ w = 1 → θ w = 1) :
    ∃ f : ↥ρ.range →* Q, Function.Surjective f := by
  have hker : ρ.ker ≤ θ.ker := fun w hw => (MonoidHom.mem_ker).2 (h w ((MonoidHom.mem_ker).1 hw))
  refine ⟨(QuotientGroup.lift ρ.ker θ hker).comp
    (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom, fun q => ?_⟩
  obtain ⟨w, rfl⟩ := hθ q
  refine ⟨⟨ρ w, w, rfl⟩, ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ w, w, rfl⟩ =
      (QuotientGroup.mk w : W ⧸ ρ.ker) := by
    apply (QuotientGroup.quotientKerEquivRange ρ).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  show QuotientGroup.lift ρ.ker θ hker
    ((QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ w, w, rfl⟩) = θ w
  rw [h1]
  rfl

theorem exists_theta {G : Type*} [Group G] (X : Subgroup G)
    (e : (↥X ⧸ CFSG.pCore 2 ↥X) ⧸ center (↥X ⧸ CFSG.pCore 2 ↥X) ≃* alternatingGroup (Fin 6)) :
    ∃ θ : ↥X →* alternatingGroup (Fin 6), Function.Surjective θ ∧
      ∀ c : ↥X, (∀ x : ↥X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥X) → θ c = 1 := by
  refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (center (↥X ⧸ CFSG.pCore 2 ↥X))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X))),
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)),
    fun c hc => ?_⟩
  have hz : (QuotientGroup.mk c : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ center (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h2 : (QuotientGroup.mk (c * x * c⁻¹ * x⁻¹) : ↥X ⧸ CFSG.pCore 2 ↥X) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hc x)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    calc (QuotientGroup.mk x : ↥X ⧸ CFSG.pCore 2 ↥X) * QuotientGroup.mk c
        = ((QuotientGroup.mk c * QuotientGroup.mk x * (QuotientGroup.mk c)⁻¹ *
            (QuotientGroup.mk x)⁻¹)⁻¹ * (QuotientGroup.mk c * QuotientGroup.mk x)) := by group
      _ = QuotientGroup.mk c * QuotientGroup.mk x := by rw [h2, inv_one, one_mul]
  change e (QuotientGroup.mk' _ (QuotientGroup.mk' _ c)) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hz,
    map_one]

theorem commutator_mem_pCore_of_mem {G : Type*} [Group G] {X : Subgroup G} {c : ↥X}
    (hc : c ∈ CFSG.pCore 2 ↥X) (x : ↥X) : c * x * c⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥X := by
  have : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have h1 : x * c⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥X := this.conj_mem _ (inv_mem hc) x
  have h2 := mul_mem hc h1
  rwa [← mul_assoc, ← mul_assoc] at h2

theorem mem_pCore_of_coe_mem {G : Type*} [Group G] {X : Subgroup G} {x : ↥X}
    (hx : (x : G) ∈ pCoreOf 2 X) : x ∈ CFSG.pCore 2 ↥X := (CFSG.mem_openPCoreOf_iff x).mp hx

theorem coe_mem_pCoreOf {G : Type*} [Group G] {X : Subgroup G} {x : ↥X}
    (hx : x ∈ CFSG.pCore 2 ↥X) : (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff x).mpr hx

theorem isSylowTwoOf_map_subgroupOf {G Q : Type*} [Group G] [Group Q] {S H : Subgroup G}
    (hS : QuasithinUnique.IsSylowTwoOf S H) (ρ : ↥H →* Q) (hρ : Function.Surjective ρ) :
    QuasithinUnique.IsSylowTwoOf ((S.subgroupOf H).map ρ) ⊤ := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨le_top, hS2.map ρ, fun hd => hS.2.2 ?_⟩
  have hd' : 2 ∣ ((S.subgroupOf H).map ρ).relIndex ⊤ := hd
  rw [Subgroup.relIndex_top_right] at hd'
  exact hd'.trans (Subgroup.index_map_dvd _ hρ)

theorem map_le_normalizer_range {G S : Type*} [Group G] [Group S] {K X T₀ : Subgroup G}
    (hXK : X ≤ K) (hT₀X : T₀ ≤ normalizer (X : Set G)) (κ : ↥K →* S) :
    (T₀.subgroupOf K).map κ ≤ normalizer ((κ.comp (Subgroup.inclusion hXK)).range : Set S) := by
  have key : ∀ s : ↥K, (s : G) ∈ T₀ → ∀ y ∈ (κ.comp (Subgroup.inclusion hXK)).range,
      κ s * y * (κ s)⁻¹ ∈ (κ.comp (Subgroup.inclusion hXK)).range := by
    rintro s hs _ ⟨x, rfl⟩
    have hx : (s : G) * x * (s : G)⁻¹ ∈ X := (mem_normalizer_iff.1 (hT₀X hs) x).1 x.2
    refine ⟨⟨_, hx⟩, ?_⟩
    show κ (Subgroup.inclusion hXK ⟨_, hx⟩) = κ s * κ (Subgroup.inclusion hXK x) * (κ s)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key t ht y, fun hy => ?_⟩
  have h1 := key t⁻¹ (T₀.inv_mem ht) _ hy
  have h2 : κ t⁻¹ * (κ t * y * (κ t)⁻¹) * (κ t⁻¹)⁻¹ = y := by
    rw [map_inv]
    group
  rwa [h2] at h1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_mem_oTwoZIn {K : Subgroup G} {z k : G} (hz : z ∈ oTwoZIn K)
    (hk : k ∈ K) : z * k * z⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  unfold oTwoZIn preimageModTwoCore at hz
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
  have hc := mem_center_iff.1 (Subgroup.mem_comap.1 hy) (QuotientGroup.mk ⟨k, hk⟩)
  have h1 : y * ⟨k, hk⟩ * y⁻¹ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥K) y * QuotientGroup.mk ⟨k, hk⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y)⁻¹ * (QuotientGroup.mk ⟨k, hk⟩)⁻¹ = 1
    rw [← hc]
    group
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨_, h1, rfl⟩

omit [Finite G] in
theorem oTwoZIn_le_self (K : Subgroup G) : oTwoZIn K ≤ K := by
  intro z hz
  unfold oTwoZIn preimageModTwoCore at hz
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hz
  exact y.2

theorem pCoreOf_le_pCoreOf_sup {K R : Subgroup G} (hRK : R ≤ normalizer (K : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    ((sup_le le_normalizer hRK).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

omit [Finite G] in
theorem commutator_mem_of_mem_sup {P Z X : Subgroup G} (hZP : Z ≤ normalizer (P : Set G))
    (hXP : X ≤ normalizer (P : Set G)) (hZ : ∀ z ∈ Z, ∀ x ∈ X, z * x * z⁻¹ * x⁻¹ ∈ P)
    {c : G} (hc : c ∈ P ⊔ Z) {x : G} (hx : x ∈ X) : c * x * c⁻¹ * x⁻¹ ∈ P := by
  let S : Subgroup G :=
    { carrier := {g | g ∈ normalizer (P : Set G) ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ P}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := fun {g h} hg hh => by
        refine ⟨mul_mem hg.1 hh.1, fun x hx => ?_⟩
        have h1 := (mem_normalizer_iff.1 hg.1 _).1 (hh.2 x hx)
        have h2 := P.mul_mem h1 (hg.2 x hx)
        have : g * h * x * (g * h)⁻¹ * x⁻¹ =
            g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by group
        rw [this]
        exact h2
      inv_mem' := fun {g} hg => by
        refine ⟨inv_mem hg.1, fun x hx => ?_⟩
        have h1 := (mem_normalizer_iff.1 (inv_mem hg.1) _).1 (P.inv_mem (hg.2 x hx))
        have : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [this]
        exact h1 }
  have hPS : P ≤ S := fun p hp => ⟨le_normalizer hp, fun x hx => by
    have h1 := (mem_normalizer_iff.1 (hXP hx) _).1 (P.inv_mem hp)
    have := P.mul_mem hp h1
    simpa [mul_assoc] using this⟩
  have hZS : Z ≤ S := fun z hz => ⟨hZP hz, fun x hx => hZ z hz x hx⟩
  exact ((sup_le hPS hZS) hc).2 x hx

theorem comm_mem_pCoreOf_of_mem_centralizer_C27 {K R V X : Subgroup G}
    (hRK : R ≤ normalizer (K : Set G))
    (hC : (K ⊔ R) ⊓ centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) (hXK : X ≤ K)
    {c : G} (hcX : c ∈ X) (hcV : c ∈ centralizer (V : Set G)) {x : G} (hxX : x ∈ X) :
    c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (K ⊔ R) with hPdef
  have hKRN : K ⊔ R ≤ normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hKK : K ≤ K ⊔ R := le_sup_left
  have hOK : pCoreOf 2 K ≤ P := pCoreOf_le_pCoreOf_sup hRK
  have hZP : oTwoZIn K ≤ normalizer (P : Set G) := fun z hz => hKRN (hKK (oTwoZIn_le_self K hz))
  have hcP : c * x * c⁻¹ * x⁻¹ ∈ P :=
    commutator_mem_of_mem_sup hZP ((hXK.trans hKK).trans hKRN)
      (fun z hz x hx => hOK (commutator_mem_pCoreOf_of_mem_oTwoZIn hz (hXK hx)))
      (hC ⟨hKK (hXK hcX), hcV⟩) hxX
  have hXN : X ≤ normalizer ((P ⊓ X : Subgroup G) : Set G) := fun y hy =>
    A4.mem_normalizer_inf (hKRN (hKK (hXK hy))) (le_normalizer hy)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hXN
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_left)
    ⟨hcP, X.mul_mem (X.mul_mem (X.mul_mem hcX hxX) (X.inv_mem hcX)) (X.inv_mem hxX)⟩

theorem theta_eq_one_of_mem_centralizer {K R V X : Subgroup G}
    (hRK : R ≤ normalizer (K : Set G))
    (hC : (K ⊔ R) ⊓ centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) (hXK : X ≤ K)
    {θ : ↥X →* alternatingGroup (Fin 6)}
    (hθ : ∀ c : ↥X, (∀ x : ↥X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥X) → θ c = 1) {c : ↥X}
    (hcV : (c : G) ∈ centralizer (V : Set G)) : θ c = 1 :=
  hθ c fun x => mem_pCore_of_coe_mem
    (comm_mem_pCoreOf_of_mem_centralizer_C27 hRK hC hXK c.2 hcV x.2)

theorem exists_surj_autOn_alt_six {K R V X : Subgroup G} (hRK : R ≤ normalizer (K : Set G))
    (hC : (K ⊔ R) ⊓ centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hXK : X ≤ K) (hXV : X ≤ normalizer (V : Set G))
    (e : (↥X ⧸ CFSG.pCore 2 ↥X) ⧸ center (↥X ⧸ CFSG.pCore 2 ↥X) ≃* alternatingGroup (Fin 6)) :
    ∃ f : ↥(autOn X V) →* alternatingGroup (Fin 6), Function.Surjective f := by
  obtain ⟨θ, hθs, hθc⟩ := exists_theta X e
  obtain ⟨f, hf⟩ := exists_surj_of_ker_le (A4.actionOn V X hXV) hθs fun c hc =>
    theta_eq_one_of_mem_centralizer hRK hC hXK hθc ((A4.actionOn_eq_one_iff hXV c).1 hc)
  have hrange : (A4.actionOn V X hXV).range = autOn X V := by
    ext a
    rw [MonoidHom.mem_range, A4.mem_autOn_iff hXV]
  exact ⟨f.comp (MulEquiv.subgroupCongr hrange.symm).toMonoidHom,
    hf.comp (MulEquiv.subgroupCongr hrange.symm).surjective⟩

theorem false_of_surj_alt_six_of_le_normalizer {W : Type*} [Group W] [Finite W]
    {Ks S Y : Subgroup W} (hS : QuasithinUnique.IsSylowTwoOf S Ks) (hYK : Y ≤ Ks)
    (hYS : Y ≤ normalizer (S : Set W)) {f : ↥Y →* alternatingGroup (Fin 6)}
    (hf : Function.Surjective f) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hYP, hP⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le (inf_le_right : S ⊓ Y ≤ Y)
    ((hS.2.1).to_le inf_le_left)
  have hPS : P ≤ S := by
    have hPSn : P ≤ normalizer (S : Set W) := hP.1.trans hYS
    have h2 : IsPGroup 2 ↥(P ⊔ S) := IsPGroup.to_sup_of_normal_right' hP.2.1 hS.2.1 hPSn
    have := hS.eq_of_le le_sup_right (sup_le (hP.1.trans hYK) hS.1) h2
    rw [← this]
    exact le_sup_left
  have hPeq : P = S ⊓ Y := le_antisymm (le_inf hPS hP.1) hYP
  have hN : ((S ⊓ Y).subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).2 fun y hy =>
      A4.mem_normalizer_inf (hYS hy) (le_normalizer hy)
  have hN2 : IsPGroup 2 ((S ⊓ Y).subgroupOf Y) :=
    ((hS.2.1).to_le inf_le_left).comap_of_injective _ Y.subtype_injective
  have hle := le_ker_of_isPGroup_normal hf hN hN2
  have hdvd : f.ker.index ∣ ((S ⊓ Y).subgroupOf Y).index := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hf, card_top, nat_card_alt_six] at hdvd
  have hodd := hP.2.2
  rw [hPeq] at hodd
  exact hodd (dvd_trans (by norm_num) hdvd)

theorem apply_eq_self_of_pow_five {α : Type*} [DecidableEq α] {f : Perm α} (h5 : f ^ 5 = 1)
    {s : Finset α} (hs : s.card < 5) (hfs : ∀ x ∈ s, f x ∈ s) : ∀ x ∈ s, f x = x := by
  intro x hx
  have hper : Function.IsPeriodicPt f 5 x := by
    change f^[5] x = x
    rw [Equiv.Perm.iterate_eq_pow, h5]
    rfl
  have hdvd := hper.minimalPeriod_dvd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h1 | h1
  · exact Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1
  · exfalso
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
    rw [h1] at hinj
    have hall : ∀ n : ℕ, f^[n] x ∈ s := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hfs _ ih
    have hsub : (Finset.range 5).image (fun n => f^[n] x) ⊆ s := by
      intro y hy
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hy
      exact hall n
    have hcard : ((Finset.range 5).image (fun n => f^[n] x)).card = 5 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      exact hinj (by simpa using ha) (by simpa using hb) hab
    have := Finset.card_le_card hsub
    omega

theorem perm_eq_one_of_pow_five_of_mem_stabilizer {σ : Perm (Fin 7)} (h5 : σ ^ 5 = 1)
    {P : Finset (Finset (Fin 7))} (hσ : σ ∈ MulAction.stabilizer (Perm (Fin 7)) P)
    (hcov : P.biUnion id = Finset.univ) (hP : P.card < 5) (hB : ∀ B ∈ P, B.card < 5) :
    σ = 1 := by
  classical
  have hσP : σ • P = P := hσ
  have hblock : ∀ B ∈ P, σ • B = B := by
    have h5' : (MulAction.toPerm σ : Perm (Finset (Fin 7))) ^ 5 = 1 := by
      have h6 : (MulAction.toPerm σ : Perm (Finset (Fin 7))) =
          MulAction.toPermHom (Perm (Fin 7)) (Finset (Fin 7)) σ := rfl
      rw [h6, ← map_pow, h5, map_one]
    refine apply_eq_self_of_pow_five h5' hP fun B hB => ?_
    change σ • B ∈ P
    rw [← hσP]
    exact Finset.smul_mem_smul_finset hB
  ext x
  have hx : x ∈ P.biUnion id := hcov ▸ Finset.mem_univ x
  obtain ⟨B, hB', hxB⟩ := Finset.mem_biUnion.1 hx
  have hfix := apply_eq_self_of_pow_five h5 (hB B hB') (fun y hy => by
    rw [← hblock B hB']
    exact Finset.smul_mem_smul_finset hy) x hxB
  rw [hfix]
  rfl

end CFSG.Quasithin.H13.A7
