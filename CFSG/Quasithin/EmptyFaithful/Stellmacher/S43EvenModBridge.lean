module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModS18
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.Quasithin.F53Mod CFSG.Quasithin.F7 CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] {X P Z L N : Subgroup G}

theorem EvenMod.conj_comm_eq_inv (q y : G) :
    q * y * q⁻¹ * y⁻¹ = ⁅y, q⁆⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem EvenMod.commutator_le_iff {Q : Subgroup G} :
    ⁅N, Q⁆ ≤ L ↔ ∀ q ∈ Q, ∀ y ∈ N, q * y * q⁻¹ * y⁻¹ ∈ L := by
  rw [Subgroup.commutator_le]
  constructor
  · intro h q hq y hy
    rw [EvenMod.conj_comm_eq_inv]
    exact L.inv_mem (h y hy q hq)
  · intro h y hy q hq
    have := L.inv_mem (h q hq y hy)
    rwa [EvenMod.conj_comm_eq_inv, inv_inv] at this

theorem ker_le_cSecIn (D : Dict5 X P Z) (hsec : IsSec X L N) (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L) :
    D.ψ.ker ≤ (cSecIn X L N).subgroupOf X := by
  intro x hx
  rw [MonoidHom.mem_ker, D.ker_iff] at hx
  rw [Subgroup.mem_subgroupOf, mem_cSecIn_iff hsec.normL]
  exact ⟨x.2, fun y hy => EvenMod.commutator_le_iff.mp hQ _ hx y hy⟩

variable [Finite G]

noncomputable abbrev secMod (D : Dict5 X P Z) (hsec : IsSec X L N)
    (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L) : Model 5 :=
  secModule hsec D.ψ D.surj (ker_le_cSecIn D hsec hQ)

noncomputable abbrev secProj (D : Dict5 X P Z) (hsec : IsSec X L N)
    (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L) : ↥N →* (secMod D hsec hQ).W :=
  hsec.proj

variable (D : Dict5 X P Z) (hsec : IsSec X L N) (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L)

theorem secProj_surjective : Function.Surjective (secProj D hsec hQ) :=
  hsec.proj_surjective

theorem secProj_eq_iff (y y' : ↥N) :
    secProj D hsec hQ y = secProj D hsec hQ y' ↔ (y : G)⁻¹ * (y' : G) ∈ L :=
  hsec.proj_eq_proj_iff y y'

theorem secProj_eq_one_iff (y : ↥N) : secProj D hsec hQ y = 1 ↔ (y : G) ∈ L :=
  hsec.proj_eq_one_iff y

theorem ker_secProj : (secProj D hsec hQ).ker = L.subgroupOf N := by
  ext y
  rw [MonoidHom.mem_ker, secProj_eq_one_iff, Subgroup.mem_subgroupOf]

theorem secMod_act (x : ↥X) (y : ↥N) :
    (secMod D hsec hQ).act (D.ψ x) (secProj D hsec hQ y) =
      secProj D hsec hQ (hsec.conjN x y) :=
  secModule_act_proj hsec D.ψ D.surj _ x y

theorem secMod_fix_iff (x : ↥X) (y : ↥N) :
    (secMod D hsec hQ).act (D.ψ x) (secProj D hsec hQ y) = secProj D hsec hQ y ↔
      (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ L := by
  rw [secMod_act, ← mul_inv_eq_one, ← map_inv, ← map_mul, secProj_eq_one_iff]
  simp [IsSec.conjN]

theorem mem_fixW_secMod_iff {K : Subgroup G} (hK : K ≤ X) (y : ↥N) :
    secProj D hsec hQ y ∈ fixW (secMod D hsec hQ) (D.bar K) ↔ (y : G) ∈ fixSecIn K L N := by
  have := hsec.normal_subgroupOf
  rw [X1512.mem_fixSecIn hsec.le, mem_fixW]
  constructor
  · intro h
    refine ⟨y.2, fun a ha => ?_⟩
    exact (secMod_fix_iff D hsec hQ ⟨a, hK ha⟩ y).mp (h _ ⟨⟨a, hK ha⟩, ha, rfl⟩)
  · rintro ⟨-, h⟩ σ ⟨a, ha, rfl⟩
    exact (secMod_fix_iff D hsec hQ a y).mpr (h a ha)

theorem secData_secMod [(L.subgroupOf N).Normal] :
    SecData (secMod D hsec hQ) X L N D.ψ (MonoidHom.id hsec.W) where
  surj := Function.surjective_id
  inj := Function.injective_id
  equiv := fun k u x hux => by
    refine ⟨hsec.conj_mem_N k x, ?_⟩
    have h1 : u = hsec.proj x := hux
    subst h1
    exact secMod_act D hsec hQ k x

theorem card_secMod : Nat.card (secMod D hsec hQ).W = L.relIndex N :=
  natCard_secModule hsec D.ψ D.surj _

theorem index_fixW_secMod {K : Subgroup G} (hK : K ≤ X) :
    (fixW (secMod D hsec hQ) (D.bar K)).index = (fixSecIn K L N).relIndex N := by
  have := hsec.normal_subgroupOf
  exact ((secData_secMod D hsec hQ).relIndex_fixSecIn hsec.le hK).symm

theorem idx_secMod {x : G} (hx : x ∈ X) :
    idx (secMod D hsec hQ) (D.ψ ⟨x, hx⟩) = secIdx (Subgroup.zpowers x) L N := by
  have := hsec.normal_subgroupOf
  exact ((secData_secMod D hsec hQ).secIdx_eq_idx hsec.le hx).symm

theorem isTransvec_one_iff {x : G} (hx : x ∈ X) :
    IsTransvec 1 x L N ↔ idx (secMod D hsec hQ) (D.ψ ⟨x, hx⟩) = 2 := by
  rw [idx_secMod]
  unfold IsTransvec
  rw [pow_one]
  omega

theorem mem_commW_secMod_iff {K : Subgroup G} (hK : K ≤ X) (y : ↥N) :
    secProj D hsec hQ y ∈ commW (secMod D hsec hQ) (D.bar K) ⊤ ↔ (y : G) ∈ ⁅N, K⁆ ⊔ L := by
  have := hsec.normal_subgroupOf
  have h := (secData_secMod D hsec hQ).map_commW hsec.le hK
  constructor
  · intro hy
    have h1 : hsec.proj y ∈
        ((commSec K L N).subgroupOf N).map (QuotientGroup.mk' (L.subgroupOf N)) := by
      rw [← h]
      exact ⟨_, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := h1
    have h2 : (z : G)⁻¹ * y ∈ L := (hsec.proj_eq_proj_iff z y).mp hzy
    have e : (y : G) = z * ((z : G)⁻¹ * y) := by group
    rw [e]
    exact (commSec K L N).mul_mem hz (le_sup_right (a := ⁅N, K⁆) h2)
  · intro hy
    have h1 : hsec.proj y ∈
        ((commSec K L N).subgroupOf N).map (QuotientGroup.mk' (L.subgroupOf N)) :=
      ⟨y, hy, rfl⟩
    rw [← h] at h1
    obtain ⟨u, hu, hue⟩ := h1
    have hue' : u = secProj D hsec hQ y := hue
    rw [← hue']
    exact hu

theorem card_commW_secMod {K : Subgroup G} (hK : K ≤ X) :
    Nat.card (commW (secMod D hsec hQ) (D.bar K) ⊤) = L.relIndex (⁅N, K⁆ ⊔ L) := by
  have := hsec.normal_subgroupOf
  exact ((secData_secMod D hsec hQ).card_commSec hsec.le hK).symm

omit [Finite G] in
theorem EvenMod.cSecIn_le (F L N : Subgroup G) : cSecIn F L N ≤ F :=
  (Subgroup.closure_le F).mpr fun _ hx => hx.1

theorem secMod_faithful_iff : (secMod D hsec hQ).Faithful ↔ cSecIn X L N ≤ pCoreOf 2 X := by
  rw [secModule_faithful_iff, D.ker_eq]
  constructor
  · intro h x hx
    exact h (show (⟨x, EvenMod.cSecIn_le X L N hx⟩ : ↥X) ∈ (cSecIn X L N).subgroupOf X from hx)
  · intro h x hx
    exact h hx

theorem secMod_faithful_of_not_le (h : ¬ oTwoRes X ≤ cSecIn X L N) :
    (secMod D hsec hQ).Faithful := by
  refine EvenMod.faithful_of_fixW_alt_ne_top _ fun htop => h fun l hl => ?_
  have hlX : l ∈ X := oTwoRes_le X hl
  rw [mem_cSecIn_iff hsec.normL]
  refine ⟨hlX, fun y hy => ?_⟩
  have hA : D.ψ ⟨l, hlX⟩ ∈ alternatingGroup (Fin 5) := map_oTwoRes_le_alt D.ψ ⟨⟨l, hlX⟩, hl, rfl⟩
  have hfix : secProj D hsec hQ ⟨y, hy⟩ ∈ fixW (secMod D hsec hQ) (alternatingGroup (Fin 5)) :=
    htop ▸ Subgroup.mem_top _
  exact (secMod_fix_iff D hsec hQ ⟨l, hlX⟩ ⟨y, hy⟩).mp (hfix _ hA)

omit [Finite G] in
include hsec hQ in
theorem pCoreOf_le_cSecIn : pCoreOf 2 X ≤ cSecIn X L N := fun q hq => by
  rw [mem_cSecIn_iff hsec.normL]
  exact ⟨pCoreOf_le 2 X hq, fun y hy => EvenMod.commutator_le_iff.mp hQ q hq y hy⟩

noncomputable abbrev secSub (U : Subgroup G) : Subgroup (secMod D hsec hQ).W :=
  (U.subgroupOf N).map (secProj D hsec hQ)

theorem mem_secSub_iff {U : Subgroup G} (hLU : L ≤ U) (y : ↥N) :
    secProj D hsec hQ y ∈ secSub D hsec hQ U ↔ (y : G) ∈ U := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h1 : (z : G)⁻¹ * y ∈ L := (secProj_eq_iff D hsec hQ z y).mp hzy
    have e : (y : G) = z * ((z : G)⁻¹ * y) := by group
    rw [e]
    exact U.mul_mem hz (hLU h1)
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem isInvSub_secSub {U : Subgroup G} (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    IsInvSub (secMod D hsec hQ) ⊤ (secSub D hsec hQ U) := by
  intro σ _ w hw
  obtain ⟨x, rfl⟩ := D.surj σ
  obtain ⟨y, hy, rfl⟩ := hw
  rw [secMod_act]
  refine ⟨hsec.conjN x y, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hXU x.2) _).mp hy

theorem secSub_mono {U U' : Subgroup G} (h : U ≤ U') :
    secSub D hsec hQ U ≤ secSub D hsec hQ U' := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

theorem secSub_le_secSub_iff {U U' : Subgroup G} (hUN : U ≤ N) (hLU' : L ≤ U') :
    secSub D hsec hQ U ≤ secSub D hsec hQ U' ↔ U ≤ U' := by
  refine ⟨fun h u hu => ?_, secSub_mono D hsec hQ⟩
  have h1 := h ⟨⟨u, hUN hu⟩, hu, rfl⟩
  exact (mem_secSub_iff D hsec hQ hLU' ⟨u, hUN hu⟩).mp h1

theorem secSub_inf {U U' : Subgroup G} (hLU : L ≤ U) (hLU' : L ≤ U') :
    secSub D hsec hQ (U ⊓ U') = secSub D hsec hQ U ⊓ secSub D hsec hQ U' := by
  ext w
  obtain ⟨y, rfl⟩ := secProj_surjective D hsec hQ w
  rw [Subgroup.mem_inf, mem_secSub_iff D hsec hQ (le_inf hLU hLU'), mem_secSub_iff D hsec hQ hLU,
    mem_secSub_iff D hsec hQ hLU', Subgroup.mem_inf]

theorem secSub_eq_bot_iff {U : Subgroup G} (hUN : U ≤ N) : secSub D hsec hQ U = ⊥ ↔ U ≤ L := by
  constructor
  · intro h u hu
    have h1 : secProj D hsec hQ ⟨u, hUN hu⟩ ∈ secSub D hsec hQ U := ⟨⟨u, hUN hu⟩, hu, rfl⟩
    rw [h, Subgroup.mem_bot, secProj_eq_one_iff] at h1
    exact h1
  · intro h
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_bot.mpr ((secProj_eq_one_iff D hsec hQ y).mpr (h hy))

theorem secSub_eq_top_iff {U : Subgroup G} (hLU : L ≤ U) : secSub D hsec hQ U = ⊤ ↔ N ≤ U := by
  constructor
  · intro h y hy
    have h1 : secProj D hsec hQ ⟨y, hy⟩ ∈ secSub D hsec hQ U := by rw [h]; trivial
    exact (mem_secSub_iff D hsec hQ hLU ⟨y, hy⟩).mp h1
  · intro h
    rw [eq_top_iff]
    intro w _
    obtain ⟨y, rfl⟩ := secProj_surjective D hsec hQ w
    exact (mem_secSub_iff D hsec hQ hLU y).mpr (h y.2)

theorem card_secSub {U : Subgroup G} (hUN : U ≤ N) :
    Nat.card (secSub D hsec hQ U) = L.relIndex U := by
  rw [← Subgroup.relIndex_ker, ker_secProj, Subgroup.relIndex_subgroupOf hUN]

theorem secSub_fixSecIn {K : Subgroup G} (hK : K ≤ X) :
    secSub D hsec hQ (fixSecIn K L N) = fixW (secMod D hsec hQ) (D.bar K) := by
  have := hsec.normal_subgroupOf
  have hL : L ≤ fixSecIn K L N := fun l hl => (X1512.mem_fixSecIn hsec.le).mpr
    ⟨hsec.le hl, fun a ha => L.mul_mem (hsec.conj_mem_L (hK ha) hl) (L.inv_mem hl)⟩
  ext w
  obtain ⟨y, rfl⟩ := secProj_surjective D hsec hQ w
  rw [mem_secSub_iff D hsec hQ hL, mem_fixW_secMod_iff D hsec hQ hK]

theorem secSub_commSec {K : Subgroup G} (hK : K ≤ X) :
    secSub D hsec hQ (⁅N, K⁆ ⊔ L) = commW (secMod D hsec hQ) (D.bar K) ⊤ := by
  ext w
  obtain ⟨y, rfl⟩ := secProj_surjective D hsec hQ w
  rw [mem_secSub_iff D hsec hQ le_sup_right, mem_commW_secMod_iff D hsec hQ hK]

omit [Finite G] in
theorem EvenMod.bar_self : D.bar X = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨x, rfl⟩ := D.surj σ
  exact ⟨x, x.2, rfl⟩

theorem secSub_fixSecIn_self :
    secSub D hsec hQ (fixSecIn X L N) = fixW (secMod D hsec hQ) ⊤ := by
  rw [secSub_fixSecIn D hsec hQ le_rfl, EvenMod.bar_self]

theorem secSub_commSec_self :
    secSub D hsec hQ (⁅N, X⁆ ⊔ L) = commW (secMod D hsec hQ) ⊤ ⊤ := by
  rw [secSub_commSec D hsec hQ le_rfl, EvenMod.bar_self]

theorem EvenMod.bar_oTwoRes : D.bar (oTwoRes X) = alternatingGroup (Fin 5) :=
  map_oTwoRes_eq_alt D.surj

theorem secSub_fixSecIn_oTwoRes :
    secSub D hsec hQ (fixSecIn (oTwoRes X) L N) =
      fixW (secMod D hsec hQ) (alternatingGroup (Fin 5)) := by
  rw [secSub_fixSecIn D hsec hQ (oTwoRes_le X), EvenMod.bar_oTwoRes]

theorem secSub_commSec_oTwoRes :
    secSub D hsec hQ (⁅N, oTwoRes X⁆ ⊔ L) =
      commW (secMod D hsec hQ) (alternatingGroup (Fin 5)) ⊤ := by
  rw [secSub_commSec D hsec hQ (oTwoRes_le X), EvenMod.bar_oTwoRes]

omit [Finite G] in
theorem EvenMod.isSec_of_le (hsec : IsSec X L N) {F : Subgroup G} (hLF : L ≤ F) (hFN : F ≤ N)
    (hXF : X ≤ Subgroup.normalizer (F : Set G)) : IsSec X L F where
  le := hLF
  normN := hXF
  normL := hsec.normL
  comm := fun x hx y hy => hsec.comm x (hFN hx) y (hFN hy)
  sq := fun x hx => hsec.sq x (hFN hx)

omit [Finite G] in
theorem EvenMod.isSec_of_ge (hsec : IsSec X L N) {K : Subgroup G} (hLK : L ≤ K) (hKN : K ≤ N)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) : IsSec X K N where
  le := hKN
  normN := hsec.normN
  normL := hXK
  comm := fun x hx y hy => hLK (hsec.comm x hx y hy)
  sq := fun x hx => hLK (hsec.sq x hx)

theorem restrict_secSub_iso {F : Subgroup G} (hLF : L ≤ F) (hFN : F ≤ N)
    (hXF : X ≤ Subgroup.normalizer (F : Set G)) :
    Nonempty ((secMod D (EvenMod.isSec_of_le hsec hLF hFN hXF)
      ((Subgroup.commutator_mono hFN le_rfl).trans hQ)).Iso
        ((secMod D hsec hQ).restrict (secSub D hsec hQ F) (isInvSub_secSub D hsec hQ hXF))) := by
  set hsecF := EvenMod.isSec_of_le hsec hLF hFN hXF with hsecFdef
  set hQF : ⁅F, pCoreOf 2 X⁆ ≤ L := (Subgroup.commutator_mono hFN le_rfl).trans hQ
  have := hsec.normal_subgroupOf
  have := hsecF.normal_subgroupOf
  let g : (secMod D hsecF hQF).W →* (secMod D hsec hQ).W :=
    QuotientGroup.map (L.subgroupOf F) (L.subgroupOf N) (Subgroup.inclusion hFN) (fun _ hx => hx)
  have hg : ∀ y : ↥F, g (secProj D hsecF hQF y) = secProj D hsec hQ (Subgroup.inclusion hFN y) :=
    fun y => rfl
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨y, rfl⟩ := secProj_surjective D hsecF hQF u
    rw [hg, secProj_eq_one_iff] at hu
    exact (secProj_eq_one_iff D hsecF hQF y).mpr hu
  have hrange : g.range = secSub D hsec hQ F := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨y, rfl⟩ := secProj_surjective D hsecF hQF u
      rw [hg]
      exact ⟨_, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨secProj D hsecF hQF ⟨y, hy⟩, rfl⟩
  refine ⟨⟨(MonoidHom.ofInjective hginj).trans (MulEquiv.subgroupCongr hrange), fun σ u => ?_⟩⟩
  obtain ⟨x, rfl⟩ := D.surj σ
  obtain ⟨y, rfl⟩ := secProj_surjective D hsecF hQF u
  apply Subtype.ext
  show g ((secMod D hsecF hQF).act (D.ψ x) (secProj D hsecF hQF y)) =
    (secMod D hsec hQ).act (D.ψ x) (g (secProj D hsecF hQF y))
  rw [secMod_act, hg, hg, secMod_act]
  rfl

theorem isModelSec_of_iso_secMod {M : Model 5} (e : M.Iso (secMod D hsec hQ))
    (hc : cSecIn X L N ≤ pCoreOf 2 X) : IsModelSec M X L N := by
  have hker : D.ψ.ker = (cSecIn X L N).subgroupOf X := by
    rw [D.ker_eq]
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => pCoreOf_le_cSecIn hsec hQ h, fun h => hc h⟩
  exact isModelSec_of_iso hsec D.ψ D.surj hker e

theorem le_normalizer_of_isInvSub_secSub {U : Subgroup G} (hLU : L ≤ U) (hUN : U ≤ N)
    (hU : IsInvSub (secMod D hsec hQ) ⊤ (secSub D hsec hQ U)) :
    X ≤ Subgroup.normalizer (U : Set G) := by
  refine X1512.le_normalizer_of_forall fun g hg u hu => ?_
  have h1 := hU (D.ψ ⟨g, hg⟩) (Subgroup.mem_top _) _ ⟨⟨u, hUN hu⟩, hu, rfl⟩
  rw [secMod_act] at h1
  exact (mem_secSub_iff D hsec hQ hLU _).mp h1

omit [Finite G] in
theorem EvenMod.le_fixSecIn (hsec : IsSec X L N) {K : Subgroup G} (hK : K ≤ X) :
    L ≤ fixSecIn K L N := by
  have := hsec.normal_subgroupOf
  exact fun l hl => (X1512.mem_fixSecIn hsec.le).mpr
    ⟨hsec.le hl, fun a ha => L.mul_mem (hsec.conj_mem_L (hK ha) hl) (L.inv_mem hl)⟩

omit [Finite G] in
theorem EvenMod.fixSecIn_le (K L N : Subgroup G) : fixSecIn K L N ≤ N :=
  (Subgroup.closure_le N).mpr fun _ hx => hx.1

omit [Finite G] in
theorem EvenMod.commSec_le (hsec : IsSec X L N) {K : Subgroup G} (hK : K ≤ X) :
    ⁅N, K⁆ ⊔ L ≤ N := by
  refine sup_le ?_ hsec.le
  rw [Subgroup.commutator_le]
  intro y hy k hk
  have h1 : k * y⁻¹ * k⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hsec.normN (hK hk)) _).mp
    (N.inv_mem hy)
  have e : ⁅y, k⁆ = y * (k * y⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact N.mul_mem hy h1

theorem EvenMod.orth_faithful : orth.Faithful := by
  rw [Model.Faithful, ← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  by_contra h1
  have h2 : idx orth σ = 1 := by
    unfold idx
    rw [Subgroup.index_eq_one, eq_top_iff]
    intro w _
    rw [mem_fixW_zpowers, hσ]
    rfl
  have h3 := idx_orth σ
  rw [h2] at h3
  split_ifs at h3 with hh <;> first | omega | exact h1 hh

theorem EvenMod.faithful_of_iso {M M' : Model 5} (e : M.Iso M') (h : M.Faithful) : M'.Faithful := by
  rw [Model.Faithful, ← MonoidHom.ker_eq_bot_iff, eq_bot_iff] at h ⊢
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  refine h ?_
  rw [MonoidHom.mem_ker]
  ext w
  apply e.toMulEquiv.injective
  rw [e.map_act, hσ]
  rfl

end CFSG.Quasithin.F53.Stellmacher.S43.Even
