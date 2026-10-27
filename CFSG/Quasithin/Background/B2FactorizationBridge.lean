module

public import CFSG.Quasithin.Background.B2Thompson
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

open CFSG.Open

universe u

variable {G : Type u} [Group G]

@[expose] def IntMod (V : Subgroup G) (_hV : IsElemAbelian 2 V) : Type u := V

namespace IntMod

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

instance instCommGroup : CommGroup (IntMod V hV) := commGroupOfElemAbelian hV

instance instFinite [Finite G] : Finite (IntMod V hV) := inferInstanceAs (Finite V)

@[expose] def mk (v : V) : IntMod V hV := v

variable {hV}

@[expose] def val (v : IntMod V hV) : G := Subtype.val v

theorem val_mem (v : IntMod V hV) : v.val ∈ V := Subtype.property v

theorem val_injective : Function.Injective (val (hV := hV)) := fun _ _ h => Subtype.ext h

@[simp] theorem val_mul (a b : IntMod V hV) : (a * b).val = a.val * b.val := rfl

@[simp] theorem val_one : (1 : IntMod V hV).val = 1 := rfl

@[simp] theorem val_inv (a : IntMod V hV) : (a⁻¹).val = (a.val)⁻¹ := rfl

theorem sq_eq_one (v : IntMod V hV) : v ^ 2 = 1 :=
  val_injective (by simpa [pow_two] using hV.2 v.val v.val_mem)

theorem val_comm (a b : IntMod V hV) : a.val * b.val = b.val * a.val := by
  have := hV.1
  exact setLike_mul_comm a.val_mem b.val_mem

theorem exists_eq_mk (v : V) : ∃ w : IntMod V hV, w.val = v := ⟨mk hV v, rfl⟩

end IntMod

section Action

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def convI : Subgroup.normalizer (V : Set G) →* MulAut (IntMod V hV) :=
  conjAct V

theorem convI_apply_val (g : Subgroup.normalizer (V : Set G)) (v : IntMod V hV) :
    (convI hV g v).val = g * v.val * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

@[expose] noncomputable def autI (K : Subgroup G) : Subgroup (MulAut (IntMod V hV)) :=
  (K.subgroupOf (Subgroup.normalizer (V : Set G))).map (convI hV)

theorem autI_eq_autOn (K : Subgroup G) : autI hV K = autOn K V := rfl

theorem mem_autI {K : Subgroup G} {φ : MulAut (IntMod V hV)} :
    φ ∈ autI hV K ↔ ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ K ∧ convI hV g = φ := by
  unfold autI
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem convI_mem_autI {K : Subgroup G} {g : G} (hg : g ∈ K)
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) : convI hV ⟨g, hgN⟩ ∈ autI hV K :=
  (mem_autI hV).2 ⟨⟨g, hgN⟩, hg, rfl⟩

theorem autI_mono {K K' : Subgroup G} (h : K ≤ K') : autI hV K ≤ autI hV K' := by
  intro φ hφ
  obtain ⟨g, hg, e⟩ := (mem_autI hV).1 hφ
  exact (mem_autI hV).2 ⟨g, h hg, e⟩

theorem convI_eq_one_iff (g : Subgroup.normalizer (V : Set G)) :
    convI hV g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := congrArg (fun φ : MulAut (IntMod V hV) => (φ (IntMod.mk hV ⟨v, hv⟩)).val) h
    have h2 : (g : G) * v * (g : G)⁻¹ = v := by
      have := h1
      simp only [convI_apply_val, MulAut.one_apply] at this
      exact this
    calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [h2]
      _ = g * v := by group
  · intro h
    ext v
    refine IntMod.val_injective ?_
    rw [convI_apply_val, MulAut.one_apply]
    have h2 := Subgroup.mem_centralizer_iff.mp h v.val v.val_mem
    rw [← h2, mul_inv_cancel_right]

theorem autI_eq_bot_iff {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    autI hV K = ⊥ ↔ K ≤ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h k hk
    have hmem : convI hV ⟨k, hK hk⟩ ∈ autI hV K := convI_mem_autI hV hk (hK hk)
    rw [h, Subgroup.mem_bot] at hmem
    exact (convI_eq_one_iff hV ⟨k, hK hk⟩).1 hmem
  · intro h
    refine eq_bot_iff.2 fun φ hφ => ?_
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact (Subgroup.mem_bot).2 ((convI_eq_one_iff hV g).2 (h hg))

theorem autI_bot : autI hV (⊥ : Subgroup G) = ⊥ :=
  (autI_eq_bot_iff hV bot_le).2 bot_le

theorem autI_eq_bot_of_le_centralizer {K : Subgroup G}
    (h : K ≤ Subgroup.centralizer (V : Set G)) : autI hV K = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  exact (Subgroup.mem_bot).2 ((convI_eq_one_iff hV g).2 (h hg))

@[expose] noncomputable def convHom (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    K →* MulAut (IntMod V hV) :=
  (convI hV).comp (Subgroup.inclusion hK)

theorem convHom_apply {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) (k : K) :
    convHom hV K hK k = convI hV ⟨k, hK k.2⟩ := rfl

theorem range_convHom (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    (convHom hV K hK).range = autI hV K := by
  unfold convHom autI
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem ker_convHom (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    (convHom hV K hK).ker = (K ⊓ Subgroup.centralizer (V : Set G)).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩

theorem autI_eq_map_convHom {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hKA : K ≤ A) : autI hV K = (K.subgroupOf A).map (convHom hV A hA) := by
  ext φ
  rw [mem_autI, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hKA hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hA a.2⟩, Subgroup.mem_subgroupOf.1 ha, rfl⟩

theorem card_autI_eq {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autI hV A) = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A :=
  card_autOn_eq_relIndex hA

theorem card_autI_mul_card_inf {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) = Nat.card A := by
  have h := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
  rw [inf_eq_left.2 (inf_le_left : A ⊓ Subgroup.centralizer (V : Set G) ≤ A)] at h
  rw [card_autI_eq hV hA]
  exact h

theorem mem_fixV_autI {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (v : IntMod V hV) : v ∈ fixV (autI hV A) ↔ v.val ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (convI hV ⟨a, hA ha⟩) (convI_mem_autI hV ha (hA ha))
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    calc a * v.val = (a * v.val * a⁻¹) * a := by group
      _ = v.val * a := by rw [h2]
  · intro h x hx
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hx
    refine IntMod.val_injective ?_
    rw [convI_apply_val]
    have h2 := h g hg
    rw [h2, mul_inv_cancel_right]

theorem card_fixV_autI {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (fixV (autI hV A)) = Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
  card_fixV_autOn_eq hV hA

theorem isElemAbelian2_autI {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) : IsElemAbelian2 (autI hV A) :=
  isElemAbelian2_autOn hV hA hAN

theorem isA2_autI {H A : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) (hAH : A ≤ H)
    (hA : IsElemAbelian 2 A) (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    IsA2 (autI hV H) (autI hV A) :=
  ⟨autI_mono hV hAH, (autI_eq_bot_iff hV (hAH.trans hH)).not.2 hA1,
    isElemAbelian2_autI hV hA (hAH.trans hH)⟩

@[expose] noncomputable def preI (A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G))
    (B : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  (B.comap (convHom hV A hA)).map A.subtype

theorem mem_preI {A : Subgroup G} {hA : A ≤ Subgroup.normalizer (V : Set G)}
    {B : Subgroup (MulAut (IntMod V hV))} {g : G} :
    g ∈ preI hV A hA B ↔ ∃ hg : g ∈ A, convHom hV A hA ⟨g, hg⟩ ∈ B := by
  unfold preI
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem preI_le {A : Subgroup G} {hA : A ≤ Subgroup.normalizer (V : Set G)}
    {B : Subgroup (MulAut (IntMod V hV))} : preI hV A hA B ≤ A :=
  fun _ hg => (mem_preI hV |>.1 hg).1

theorem inf_centralizer_le_preI {A : Subgroup G} {hA : A ≤ Subgroup.normalizer (V : Set G)}
    {B : Subgroup (MulAut (IntMod V hV))} :
    A ⊓ Subgroup.centralizer (V : Set G) ≤ preI hV A hA B := by
  intro g hg
  refine (mem_preI hV).2 ⟨hg.1, ?_⟩
  have h1 : convHom hV A hA ⟨g, hg.1⟩ = 1 := (convI_eq_one_iff hV ⟨g, hA hg.1⟩).2 hg.2
  rw [h1]
  exact B.one_mem

theorem autI_preI {A : Subgroup G} {hA : A ≤ Subgroup.normalizer (V : Set G)}
    {B : Subgroup (MulAut (IntMod V hV))} (hB : B ≤ autI hV A) :
    autI hV (preI hV A hA B) = B := by
  rw [autI_eq_map_convHom hV hA (K := preI hV A hA B) (preI_le hV)]
  have h1 : (preI hV A hA B).subgroupOf A = B.comap (convHom hV A hA) := by
    unfold preI
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  rw [h1, Subgroup.map_comap_eq, range_convHom]
  exact inf_eq_right.2 hB

theorem card_preI {A : Subgroup G} {hA : A ≤ Subgroup.normalizer (V : Set G)}
    {B : Subgroup (MulAut (IntMod V hV))} (hB : B ≤ autI hV A) :
    Nat.card (preI hV A hA B) = Nat.card B * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
  have h1 := card_autI_mul_card_inf hV ((preI_le hV).trans hA : preI hV A hA B ≤ _)
  rw [autI_preI hV hB] at h1
  have h2 : preI hV A hA B ⊓ Subgroup.centralizer (V : Set G) =
      A ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (inf_le_inf_right _ (preI_le hV)) (le_inf (inf_centralizer_le_preI hV) inf_le_right)
  rw [h2] at h1
  exact h1.symm

@[expose] def cjSub (g : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_cjSub {g x : G} {A : Subgroup G} : x ∈ cjSub g A ↔ g⁻¹ * x * g ∈ A := by
  unfold cjSub
  rw [Subgroup.mem_map_equiv]
  simp

theorem cjSub_mono {g : G} {A B : Subgroup G} (h : A ≤ B) : cjSub g A ≤ cjSub g B :=
  Subgroup.map_mono h

theorem cjSub_cjSub_inv (g : G) (A : Subgroup G) : cjSub g (cjSub g⁻¹ A) = A := by
  ext x
  simp [mem_cjSub, mul_assoc]

theorem cjSub_inv_cjSub (g : G) (A : Subgroup G) : cjSub g⁻¹ (cjSub g A) = A := by
  ext x
  simp [mem_cjSub, mul_assoc]

theorem card_cjSub (g : G) (A : Subgroup G) : Nat.card (cjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cjSub_le {g : G} {H A : Subgroup G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hA : A ≤ H) : cjSub g A ≤ H := by
  intro x hx
  have h1 := hA (mem_cjSub.1 hx)
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg _).1 h1
  simpa [mul_assoc] using h2

theorem isElemAbelian_cjSub {g : G} {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (cjSub g A) := by
  have := hA.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have hx := mem_cjSub.1 x.2
    have hy := mem_cjSub.1 y.2
    apply Subtype.ext
    have h := setLike_mul_comm hx hy
    have h2 := congrArg (fun t => g * t * g⁻¹) h
    simpa [mul_assoc] using h2
  · have h := hA.2 _ (mem_cjSub.1 hx)
    have h2 : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by simp [pow_two, mul_assoc]
    rw [h2] at h
    have h3 : x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by simp [mul_assoc]
    rw [h3, h]
    simp

theorem not_cjSub_le_centralizer {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {A : Subgroup G} (hA : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    ¬ cjSub g A ≤ Subgroup.centralizer (V : Set G) := by
  intro h
  apply hA
  intro a ha
  have h1 : g * a * g⁻¹ ∈ cjSub g A := by
    rw [mem_cjSub]
    simpa [mul_assoc] using ha
  have h2 := h h1
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have hw : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hg v).1 hv
  have h3 := Subgroup.mem_centralizer_iff.1 h2 _ hw
  have h4 : g * (v * a) * g⁻¹ = g * (a * v) * g⁻¹ := by
    calc g * (v * a) * g⁻¹ = g * v * g⁻¹ * (g * a * g⁻¹) := by group
      _ = g * a * g⁻¹ * (g * v * g⁻¹) := h3
      _ = g * (a * v) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h4)

theorem isMaxElemAbelian_cjSub {g : G} {H A : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hA : IsMaxElemAbelian H A) :
    IsMaxElemAbelian H (cjSub g A) := by
  refine ⟨cjSub_le hg hA.1, isElemAbelian_cjSub hA.2.1, fun B hBH hB => ?_⟩
  have hB' : cjSub g⁻¹ B ≤ H := cjSub_le (inv_mem hg) hBH
  have h1 := hA.2.2 _ hB' (isElemAbelian_cjSub hB)
  rw [card_cjSub] at h1
  rw [card_cjSub]
  exact h1

theorem autI_cjSub {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (A : Subgroup G) :
    (autI hV A).map (MulAut.conj (convI hV ⟨g, hg⟩)).toMonoidHom = autI hV (cjSub g A) := by
  ext ψ
  rw [Subgroup.mem_map, mem_autI]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
    refine ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, mem_cjSub]
      simpa [mul_assoc] using ha
    · simp [map_mul, map_inv]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨convI hV (⟨g, hg⟩⁻¹ * x * ⟨g, hg⟩), (mem_autI hV).2 ⟨_, ?_, rfl⟩, ?_⟩
    · have := mem_cjSub.1 hx
      simpa [mul_assoc] using this
    · simp [map_mul, map_inv, mul_assoc]

theorem autI_sup {K K' : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hK' : K' ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (K ⊔ K') = autI hV K ⊔ autI hV K' := by
  unfold autI
  rw [Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

theorem autI_iSup {ι : Sort*} (K : ι → Subgroup G)
    (hK : ∀ i, K i ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (⨆ i, K i) = ⨆ i, autI hV (K i) := by
  unfold autI
  have h : (⨆ i, K i).subgroupOf (Subgroup.normalizer (V : Set G)) =
      ⨆ i, (K i).subgroupOf (Subgroup.normalizer (V : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hK), Subgroup.map_iSup]
    exact (iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hK i)).symm)
  rw [h, Subgroup.map_iSup]

theorem autI_iSup₂ {P : Subgroup G → Prop}
    (hP : ∀ A, P A → A ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (⨆ (A : Subgroup G) (_ : P A), A) = ⨆ (A : Subgroup G) (_ : P A), autI hV A := by
  rw [autI_iSup hV _ (fun A => iSup_le fun hA => hP A hA)]
  exact iSup_congr fun A => autI_iSup hV (fun _ : P A => A) (fun hA => hP A hA)

end Action

namespace B2F

section Commuting

variable {A B : Subgroup G}

private theorem comm_of_mem_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x y : G}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : x * y = y * x := by
  have h1 : ∀ z ∈ Subgroup.closure S, ∀ b ∈ S, z * b = b * z := by
    intro z hz b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hS a ha h hb).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hz)) b rfl).symm
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact h1 h hy a ha
  exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y rfl).symm

private theorem pow_two_eq_one_of_mem_closure {S : Set G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (h2 : ∀ a ∈ S, a ^ 2 = 1) {x : G}
    (hx : x ∈ Subgroup.closure S) : x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (comm_of_mem_closure hS hx hy) 2, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem isElemAbelian_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (h2 : ∀ a ∈ S, a ^ 2 = 1) : IsElemAbelian 2 (Subgroup.closure S) :=
  ⟨⟨⟨fun x y => Subtype.ext (comm_of_mem_closure hS x.2 y.2)⟩⟩,
    fun _ hx => pow_two_eq_one_of_mem_closure hS h2 hx⟩

theorem isElemAbelian_sup_of_commute (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian 2 (A ⊔ B) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hA hB h

theorem relIndex_sup_eq_of_le_normalizer' {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem card_sup_mul_card_inf_of_commute (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha b hb
  have h1 := relIndex_sup_eq_of_le_normalizer' hBN
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A B
  have h4 : A ⊓ (B ⊔ A) = A := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

end Commuting

theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have h := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * s := by group
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

theorem le_normalizer_inf {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hg) x,
    Subgroup.mem_normalizer_iff.mp (hB hg) x]

theorem le_normalizer_centralizer {S V : Subgroup G}
    (h : S ≤ Subgroup.normalizer (V : Set G)) :
    S ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
  h.trans (normalizer_le_normalizer_centralizer V)

theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) : IsPGroup 2 E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

theorem isElemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem isElemAbelian_mono {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem eq_sup_of_forall_exists_mul {H N C : Subgroup G} (hN : N ≤ H) (hC : C ≤ H)
    (h : ∀ x ∈ H, ∃ n ∈ N, ∃ c ∈ C, x = n * c) : H = N ⊔ C := by
  refine le_antisymm (fun x hx => ?_) (sup_le hN hC)
  obtain ⟨n, hn, c, hc, rfl⟩ := h x hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hc)

theorem mem_normalizer_iff_cjSub_eq {g : G} {K : Subgroup G} :
    g ∈ Subgroup.normalizer (K : Set G) ↔ cjSub g K = K := by
  constructor
  · intro hg
    ext x
    rw [mem_cjSub]
    exact (Subgroup.mem_normalizer_iff''.1 hg x).symm
  · intro h
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    rw [← mem_cjSub, h]

theorem le_normalizer_sup {S A B : Subgroup G} (hA : S ≤ Subgroup.normalizer (A : Set G))
    (hB : S ≤ Subgroup.normalizer (B : Set G)) : S ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  have hA' := mem_normalizer_iff_cjSub_eq.1 (hA hg)
  have hB' := mem_normalizer_iff_cjSub_eq.1 (hB hg)
  rw [mem_normalizer_iff_cjSub_eq]
  have h : cjSub g (A ⊔ B) = cjSub g A ⊔ cjSub g B := Subgroup.map_sup _ _ _
  rw [h, hA', hB']

theorem le_centralizer_self {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun v hv => by
    have := hV.1
    exact setLike_mul_comm hv hx

end B2F

end CFSG.Quasithin
