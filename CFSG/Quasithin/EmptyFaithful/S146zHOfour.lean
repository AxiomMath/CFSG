module

public import CFSG.Quasithin.EmptyFaithful.S146zHFaith
public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.Quasithin.EmptyFaithful.S146F10
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F15
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146F20
public import CFSG.Quasithin.EmptyFaithful.S146zHDih

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Aux

variable {G : Type} [Group G]

theorem card_tildeOf_eq_relIndex {Z X : Subgroup G} (hZX : Z ≤ X)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card (tildeOf Z X) = Z.relIndex X := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z) (H := X)
    le_rfl hZX hXN
  have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  exact h1

end Aux

section Ofour

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.isOFourPlusOn (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ 3)
    (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (hr : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2) : IsOFourPlusOn T M H := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) := isPGroup_of_isElemAbelian hUab
  have huK_le : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have huKN : uK T M H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    huK_le.trans hUZ
  have hHuK : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hcard12 : Nat.card (uHi T M H H₁) = Nat.card (uHi T M H H₂) := by
    rw [← h.conjSub_uHi hred]
    exact (CosetGeom.card_conjSub t _).symm
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := Nat.card_pos
  have hrel₁ : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) = 4 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hi₁), hr]; norm_num
  have hrel₂ : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) = 4 := by
    have e1 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁)
    have e2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₂)
    rw [inf_eq_left.mpr (Z_le_uHi T M H H₁)] at e1
    rw [inf_eq_left.mpr (Z_le_uHi T M H H₂)] at e2
    rw [hcard12, ← e2, hrel₁] at e1
    exact Nat.eq_of_mul_eq_mul_right hZpos (by omega)
  have huKel : IsElemAbelian 2 (uK T M H) := by
    rw [isElemAbelian_iff]
    exact ⟨fun a ha b hb => isElemAbelian_comm hUab (huK_le ha) (huK_le hb),
      fun a ha => isElemAbelian_pow_eq_one hUab (huK_le ha)⟩
  have hVel : IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uK T M H)) :=
    isElemAbelian_secImg huKel
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := tildeOf Z (uK T M H) with hVdef
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVel
  have hsup_le : ∀ X : Subgroup G, X ≤ uK T M H ⊔ Z → tildeOf Z X ≤ V := by
    intro X hX
    refine (secImg_mono hX).trans ?_
    rw [hVdef]
    exact (tildeOf_sup_self huKN).le
  have hZ1 : Z ≤ uHi T M H H₁ := Z_le_uHi T M H H₁
  have hZ2 : Z ≤ uHi T M H H₂ := Z_le_uHi T M H H₂
  have hVi₁ : tildeOf Z (uHi T M H H₁) ≤ V := hsup_le _ (le_sup_left.trans h.dir_sup.le)
  have hVi₂ : tildeOf Z (uHi T M H H₂) ≤ V := hsup_le _ (le_sup_right.trans h.dir_sup.le)
  have hinf : (tildeOf Z (uHi T M H H₁)).subgroupOf V ⊓ (tildeOf Z (uHi T M H H₂)).subgroupOf V = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw1 := Subgroup.mem_subgroupOf.mp hw.1
    have hw2 := Subgroup.mem_subgroupOf.mp hw.2
    obtain ⟨x₁, hx₁, hx₁w⟩ := mem_secImg.mp hw1
    obtain ⟨x₂, hx₂, hx₂w⟩ := mem_secImg.mp hw2
    have h12 : (x₁ : G)⁻¹ * x₂ ∈ Z := secMk_eq_secMk_iff.mp (hx₁w.trans hx₂w.symm)
    have hx₂1 : (x₂ : G) ∈ uHi T M H H₁ := by
      have e : (x₂ : G) = (x₁ : G) * ((x₁ : G)⁻¹ * x₂) := by group
      rw [e]; exact (uHi T M H H₁).mul_mem hx₁ (hZ1 h12)
    have hx₂Z : (x₂ : G) ∈ Z := by
      have : (x₂ : G) ∈ uHi T M H H₁ ⊓ uHi T M H H₂ := ⟨hx₂1, hx₂⟩
      rwa [h.dir_inf] at this
    have : (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z) = 1 := by
      rw [← hx₂w]; exact secMk_eq_one_iff.mpr hx₂Z
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hsup : (tildeOf Z (uHi T M H H₁)).subgroupOf V ⊔ (tildeOf Z (uHi T M H H₂)).subgroupOf V = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, hu, huw⟩ := mem_secImg.mp w.2
    have huU : (u : G) ∈ uHi T M H H₁ ⊔ uHi T M H H₂ := by
      rw [h.dir_sup]; exact Subgroup.mem_sup_left hu
    have hN12 : uHi T M H H₁ ≤ Subgroup.normalizer (uHi T M H H₂ : Set G) :=
      le_normalizer_of_forall_commute fun x hx y hy => isElemAbelian_comm hUab (hi₁ hx) (hi₂ hy)
    have hmul : (↑(uHi T M H H₁ ⊔ uHi T M H H₂) : Set G) = ↑(uHi T M H H₁) * ↑(uHi T M H H₂) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN12
    have huU' : (u : G) ∈ (↑(uHi T M H H₁ ⊔ uHi T M H H₂) : Set G) := huU
    rw [hmul] at huU'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp huU'
    let aN : ↥(Subgroup.normalizer (Z : Set G)) := ⟨a, hUZ (hi₁ ha)⟩
    let bN : ↥(Subgroup.normalizer (Z : Set G)) := ⟨b, hUZ (hi₂ hb)⟩
    have huab : u = aN * bN := Subtype.ext hab.symm
    have hwa : secMk (Subgroup.normalizer (Z : Set G)) Z aN ∈ V := hVi₁ (secMk_mem_secImg ha)
    have hwb : secMk (Subgroup.normalizer (Z : Set G)) Z bN ∈ V := hVi₂ (secMk_mem_secImg hb)
    have hweq : w = ⟨secMk (Subgroup.normalizer (Z : Set G)) Z aN, hwa⟩ *
        ⟨secMk (Subgroup.normalizer (Z : Set G)) Z bN, hwb⟩ :=
      Subtype.ext (by rw [← huw, huab, map_mul]; rfl)
    rw [hweq]
    exact Subgroup.mul_mem_sup (by rw [Subgroup.mem_subgroupOf]; exact secMk_mem_secImg ha)
      (by rw [Subgroup.mem_subgroupOf]; exact secMk_mem_secImg hb)
  have hVsq : ∀ w : ↥V, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hVel w.2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA₁card : Nat.card ((tildeOf Z (uHi T M H H₁)).subgroupOf V) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVi₁).toEquiv,
      card_tildeOf_eq_relIndex hZ1 (hi₁.trans hUZ), hrel₁]
    norm_num
  have hA₂card : Nat.card ((tildeOf Z (uHi T M H H₂)).subgroupOf V) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVi₂).toEquiv,
      card_tildeOf_eq_relIndex hZ2 (hi₂.trans hUZ), hrel₂]
    norm_num
  obtain ⟨φ₁⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥((tildeOf Z (uHi T M H H₁)).subgroupOf V)) (fun a b => mul_comm a b)
    (fun a => Subtype.ext (hVsq a.1)) hA₁card
  obtain ⟨φ₂⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥((tildeOf Z (uHi T M H H₂)).subgroupOf V)) (fun a b => mul_comm a b)
    (fun a => Subtype.ext (hVsq a.1)) hA₂card
  have hcard16 : Nat.card ↥V = 16 := S1417.card_eq_sixteen hinf hsup φ₁ φ₂
  have hle : autOn (tildeOf Z H) V ≤ orthogonalGroupOf (S1417.quadOf hinf hsup φ₁ φ₂) := by
    intro g hg
    obtain ⟨s, hsS, rfl⟩ := mem_autOn_iff.mp hg
    obtain ⟨xN, hxH, hxs⟩ := mem_secImg.mp hsS
    have hperm := h.perm_uHi S hred hxH
    have hact : ∀ w : ↥V, ((conjAct V s w : ↥V) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
        secMk (Subgroup.normalizer (Z : Set G)) Z xN * (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z) *
          (secMk (Subgroup.normalizer (Z : Set G)) Z xN)⁻¹ := by
      intro w
      rw [conjAct_apply_coe', hxs]
    have hstep : ∀ X Y : Subgroup G, conjSub (xN : G) X = Y → ∀ w : ↥V,
        (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈ tildeOf Z X →
          ((conjAct V s w : ↥V) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈ tildeOf Z Y := by
      intro X Y hXY w hw
      obtain ⟨y, hy, hyw⟩ := mem_secImg.mp hw
      rw [hact, ← hyw, ← map_inv, ← map_mul, ← map_mul]
      refine secMk_mem_secImg (X := Y) ?_
      rw [← hXY]
      exact mul_mem_conjSub hy
    show ∀ v : ↥V, S1417.quadOf hinf hsup φ₁ φ₂ (conjAct V s v) = S1417.quadOf hinf hsup φ₁ φ₂ v
    intro w
    rcases hperm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact S1417.quadOf_apply_of_stab hinf hsup φ₁ φ₂ (g := conjAct V s)
        (fun u hu => by
          rw [Subgroup.mem_subgroupOf] at hu ⊢
          exact hstep _ _ h1 u hu)
        (fun u hu => by
          rw [Subgroup.mem_subgroupOf] at hu ⊢
          exact hstep _ _ h2 u hu) w
    · exact S1417.quadOf_apply_of_swap hinf hsup φ₁ φ₂ (g := conjAct V s)
        (fun u hu => by
          rw [Subgroup.mem_subgroupOf] at hu ⊢
          exact hstep _ _ h1 u hu)
        (fun u hu => by
          rw [Subgroup.mem_subgroupOf] at hu ⊢
          exact hstep _ _ h2 u hu) w
  have hcardAut : Nat.card (autOn (tildeOf Z H) V) = 72 := by
    have h1 : Nat.card (autOn (tildeOf Z H) V) = (centralizerMod Z H (uK T M H)).relIndex H :=
      card_autOn_secImg (K := Z) (E := uK T M H) (X := H) hHN huKN hHuK
    rw [h1, S.centralizerMod_uK_eq hH]
    exact h.relIndex_pCoreOf_eq_72 S hred
  obtain ⟨L₁, L₂, t', hOS, -, -⟩ := S153.exists_ofourStruct hinf hsup φ₁ φ₂
  have hcardO : Nat.card (orthogonalGroupOf (S1417.quadOf hinf hsup φ₁ φ₂)) = 72 := hOS.card_X
  refine ⟨⟨hcard16, S1417.quadOf hinf hsup φ₁ φ₂, S1417.quadOf_isQuadratic hinf hsup φ₁ φ₂,
    S1417.quadOf_nondeg hinf hsup φ₁ φ₂, S1417.quadOf_plus hinf hsup φ₁ φ₂, ?_⟩,
    S.centralizerMod_uK_eq hH⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardO, hcardAut])

end Ofour

end CFSG.Quasithin
