module

public import CFSG.Quasithin.EmptyFaithful.S146zUG1Core
public import CFSG.Quasithin.EmptyFaithful.S153MMod
public import CFSG.Quasithin.Background.F918P4

public section

namespace CFSG.Quasithin.S146zU.UG1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

attribute [local instance] commGroupOfFact

section Sub

variable {G : Type} [Group G]

@[expose] def cmodSub (V₁ U B : Subgroup G) (hU : U ≤ Subgroup.normalizer (V₁ : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ U ∧ ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ V₁}
  mul_mem' := by
    rintro x y ⟨hxU, hx⟩ ⟨hyU, hy⟩
    refine ⟨U.mul_mem hxU hyU, fun b hb => ?_⟩
    have e : x * y * b * (x * y)⁻¹ * b⁻¹ =
        x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group
    rw [e]
    exact V₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hU hxU) _).mp (hy b hb)) (hx b hb)
  one_mem' := ⟨U.one_mem, fun b _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxU, hx⟩
    refine ⟨U.inv_mem hxU, fun b hb => ?_⟩
    have e : x⁻¹ * b * x⁻¹⁻¹ * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hU (U.inv_mem hxU)) _).mp (V₁.inv_mem (hx b hb))

end Sub

section Vec

variable {G : Type} [Group G] {V₁ H IH : Subgroup G}

theorem actH_mul_inv_modMk [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (a : ↥H) {u : G} (hu : u ∈ IH)
    (hw : (a : G) * u * (a : G)⁻¹ * u⁻¹ ∈ IH) :
    actH hV₁ hIH a (modMk hIHN u hu) * (modMk hIHN u hu)⁻¹ =
      modMk hIHN ((a : G) * u * (a : G)⁻¹ * u⁻¹) hw := by
  have hau : (a : G) * u * (a : G)⁻¹ ∈ IH := (Subgroup.mem_normalizer_iff.mp (hIH a.2) u).mp hu
  rw [actH_modMk hV₁ hIHN hIH a hu, ← modMk_inv hIHN hu, ← modMk_mul hIHN hau (IH.inv_mem hu)]

end Vec

section Gen

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem dmod_of_split [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hclaim : tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆)
    {Ka Kb : Subgroup G} (hKa : ⁅Ka, Ka⁆ = Ka) (hKaH : Ka ≤ H) (hKaK : Ka ≤ conjClosure K T)
    (hKbH : Kb ≤ H) (hsplit : commV (autIH V₁ I H Ka) ≤ fixV (autIH V₁ I H Kb))
    (a b : ↥H) (ha : (a : G) ∈ Ka) (hb : (b : G) ∈ Kb)
    (y : ↥(tildeOf V₁ (conjClosure Vp H))) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹ := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) :=
    ⟨h.toHypF98.toHypF91.isElemAbelian_tilde⟩
  have hV₁ := h.H_le_normalizer_V₁
  have hUN := le_normalizer_conjClosure Vp H
  have hI₀N := le_normalizer_conjClosure I H
  have hUV₁ := h.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hI₀U : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  let ι : ↥(tildeOf V₁ (conjClosure I H)) →* ↥(tildeOf V₁ (conjClosure Vp H)) :=
    Subgroup.inclusion (secImg_mono hI₀U)
  let σE : ↥Ka →* MulAut ↥(tildeOf V₁ (conjClosure I H)) :=
    (actH hV₁ hI₀N).comp (Subgroup.inclusion hKaH)
  let σY : ↥Ka →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
    (actH hV₁ hUN).comp (Subgroup.inclusion hKaH)
  have : Group.IsPerfect ↥Ka := Subgroup.isPerfect_iff.mpr hKa
  have hιg : ∀ (g : ↥H) (e : ↥(tildeOf V₁ (conjClosure I H))),
      ι (actH hV₁ hI₀N g e) = actH hV₁ hUN g (ι e) := by
    intro g e
    apply Subtype.ext
    show ((actH hV₁ hI₀N g e : ↥(tildeOf V₁ (conjClosure I H))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      ((actH hV₁ hUN g (ι e) : ↥(tildeOf V₁ (conjClosure Vp H))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)
    rw [actH_apply_coe, actH_apply_coe]
    rfl
  have hrange : ∀ (p : ↥Ka) (y : ↥(tildeOf V₁ (conjClosure Vp H))),
      σY p y * y⁻¹ ∈ ι.range := by
    intro p y
    obtain ⟨a', haU, hay⟩ := exists_mk_of_mem_tilde y
    have hy : y = modMk hUV₁ (a' : G) haU := Subtype.ext hay.symm
    have hpH : (p : G) ∈ H := hKaH p.2
    have hw : (p : G) * (a' : G) * (p : G)⁻¹ * (a' : G)⁻¹ ∈ conjClosure Vp H :=
      (conjClosure Vp H).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hUN hpH) (a' : G)).mp haU)
        ((conjClosure Vp H).inv_mem haU)
    have hcomm : (p : G) * (a' : G) * (p : G)⁻¹ * (a' : G)⁻¹ ∈
        ⁅conjClosure Vp H, conjClosure K T⁆ := by
      have hm := Subgroup.commutator_mem_commutator haU (hKaK p.2)
      have e : ((p : G) * (a' : G) * (p : G)⁻¹ * (a' : G)⁻¹) =
          (⁅(a' : G), (p : G)⁆)⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.inv_mem _ hm
    have hmem : secMk (Subgroup.normalizer (V₁ : Set G)) V₁
        ⟨(p : G) * (a' : G) * (p : G)⁻¹ * (a' : G)⁻¹, hUV₁ hw⟩ ∈
          tildeOf V₁ (conjClosure I H) := by
      rw [hclaim]
      exact secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) hcomm
    refine ⟨⟨_, hmem⟩, ?_⟩
    have h1 := actH_mul_inv_modMk hV₁ hUV₁ hUN (Subgroup.inclusion hKaH p) haU hw
    rw [hy]
    exact h1.symm
  have hAσ : ∀ p : ↥Ka, σE p ∈ autIH V₁ I H Ka := fun p => by
    rw [autIH_eq_map h hKaH]
    exact ⟨Subgroup.inclusion hKaH p, Subgroup.mem_subgroupOf.mpr p.2, rfl⟩
  have hA : ∀ (p : ↥Ka) (e : ↥(tildeOf V₁ (conjClosure I H))),
      σE p e * e⁻¹ ∈ commV (autIH V₁ I H Ka) := fun p e =>
    Subgroup.subset_closure ⟨σE p, hAσ p, e, rfl⟩
  have hbmem : actH hV₁ hI₀N b ∈ autIH V₁ I H Kb := by
    rw [autIH_eq_map h hKbH]
    exact ⟨b, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hAα : ∀ x ∈ commV (autIH V₁ I H Ka), actH hV₁ hI₀N b x = x := fun x hx =>
    hsplit hx _ hbmem
  exact fix_of_isPerfect σE σY ι (fun p e => hιg _ e) hrange hA (α := actH hV₁ hI₀N b)
    (β := actH hV₁ hUN b) (fun e => hιg b e) hAα ⟨a, ha⟩ y

theorem commutator_commutator_le_of_dmod (h : HypF918 T V L V₁ Vp H K) {Ka Kb : Subgroup G}
    (hKaH : Ka ≤ H) (hKbH : Kb ≤ H)
    (hD : ∀ (a b : ↥H), (a : G) ∈ Ka → (b : G) ∈ Kb → ∀ y : ↥(tildeOf V₁ (conjClosure Vp H)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹) =
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹) :
    ⁅⁅conjClosure Vp H, Ka⁆, Kb⁆ ≤ V₁ := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) :=
    ⟨h.toHypF98.toHypF91.isElemAbelian_tilde⟩
  have hV₁ := h.H_le_normalizer_V₁
  have hUN := le_normalizer_conjClosure Vp H
  have hUV₁ := h.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hsub : ⁅conjClosure Vp H, Ka⁆ ≤ cmodSub V₁ (conjClosure Vp H) Kb hUV₁ := by
    rw [Subgroup.commutator_le]
    intro u hu a ha
    have haH : a ∈ H := hKaH ha
    have hau : a * u * a⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hUN haH) u).mp hu
    have hw : a * u * a⁻¹ * u⁻¹ ∈ conjClosure Vp H :=
      (conjClosure Vp H).mul_mem hau ((conjClosure Vp H).inv_mem hu)
    have hcomm_eq : ⁅u, a⁆ = (a * u * a⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [hcomm_eq]
    refine ⟨(conjClosure Vp H).inv_mem hw, fun b hb => ?_⟩
    have hbH : b ∈ H := hKbH hb
    have hbw : b * (a * u * a⁻¹ * u⁻¹) * b⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hUN hbH) _).mp hw
    have hD' := hD ⟨a, haH⟩ ⟨b, hbH⟩ ha hb (modMk hUV₁ u hu)
    rw [actH_mul_inv_modMk hV₁ hUV₁ hUN ⟨a, haH⟩ hu hw,
      actH_modMk hV₁ hUV₁ hUN ⟨b, hbH⟩ hw] at hD'
    have hc := (S153M.modMk_conj_eq_iff hUV₁ hw hbw).mp hD'
    have e : (a * u * a⁻¹ * u⁻¹)⁻¹ * b * (a * u * a⁻¹ * u⁻¹)⁻¹⁻¹ * b⁻¹ =
        (a * u * a⁻¹ * u⁻¹)⁻¹ * (b * (a * u * a⁻¹ * u⁻¹) * b⁻¹ * (a * u * a⁻¹ * u⁻¹)⁻¹) *
          (a * u * a⁻¹ * u⁻¹)⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hUV₁ ((conjClosure Vp H).inv_mem hw)) _).mp hc
  rw [Subgroup.commutator_le]
  intro x hx b hb
  exact (hsub hx).2 b hb

theorem dmod_swap (h : HypF918 T V L V₁ Vp H K) {Ka Kb : Subgroup G}
    (hcomm : ∀ (a b : ↥H), (a : G) ∈ Ka → (b : G) ∈ Kb →
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a *
          actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b =
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b *
          actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a)
    (hD : ∀ (a b : ↥H), (a : G) ∈ Ka → (b : G) ∈ Kb → ∀ y : ↥(tildeOf V₁ (conjClosure Vp H)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹) =
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹)
    (b a : ↥H) (hb : (b : G) ∈ Kb) (ha : (a : G) ∈ Ka)
    (y : ↥(tildeOf V₁ (conjClosure Vp H))) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b y * y⁻¹) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b y * y⁻¹ := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) :=
    ⟨h.toHypF98.toHypF91.isElemAbelian_tilde⟩
  exact fix_swap (hcomm a b ha hb).symm (hD a b ha hb) y

end Gen

end CFSG.Quasithin.S146zU.UG1
