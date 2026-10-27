module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Act
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsHat

public section

namespace CFSG.Quasithin.A312M23

open CFSG.Quasithin.A312Words
open scoped commutatorElement

variable {Γ α : Type} [Group Γ] [MulAction Γ α] {m : ℕ}

@[expose] noncomputable def rhoFn (Y : Subgroup Γ) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) (g : Γ) : Equiv.Perm (Fin m) := by
  classical exact if h : g ∈ Y then actHom Y pt hpt hY ⟨g, h⟩ else 1

theorem rhoFn_of_mem {Y : Subgroup Γ} {pt : Fin m → α} {hpt : Function.Injective pt}
    {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {g : Γ} (h : g ∈ Y) :
    rhoFn Y pt hpt hY g = actHom Y pt hpt hY ⟨g, h⟩ := by
  simp [rhoFn, h]

theorem rhoFn_mul {Y : Subgroup Γ} {pt : Fin m → α} {hpt : Function.Injective pt}
    {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {g h : Γ} (hg : g ∈ Y) (hh : h ∈ Y) :
    rhoFn Y pt hpt hY (g * h) = rhoFn Y pt hpt hY g * rhoFn Y pt hpt hY h := by
  rw [rhoFn_of_mem (Y.mul_mem hg hh), rhoFn_of_mem hg, rhoFn_of_mem hh, ← map_mul]
  rfl

theorem rhoFn_one {Y : Subgroup Γ} {pt : Fin m → α} {hpt : Function.Injective pt}
    {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} : rhoFn Y pt hpt hY 1 = 1 := by
  rw [rhoFn_of_mem Y.one_mem]
  exact map_one _

theorem rhoFn_inv {Y : Subgroup Γ} {pt : Fin m → α} {hpt : Function.Injective pt}
    {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {g : Γ} (hg : g ∈ Y) :
    rhoFn Y pt hpt hY g⁻¹ = (rhoFn Y pt hpt hY g)⁻¹ := by
  rw [rhoFn_of_mem (Y.inv_mem hg), rhoFn_of_mem hg, ← map_inv]
  rfl

theorem rhoFn_spec {Y : Subgroup Γ} {pt : Fin m → α} {hpt : Function.Injective pt}
    {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {g : Γ} (hg : g ∈ Y) (i : Fin m) :
    g • pt i = pt (rhoFn Y pt hpt hY g i) := by
  rw [rhoFn_of_mem hg]
  exact (actHom_spec Y pt hpt hY ⟨g, hg⟩ i).symm

@[expose] noncomputable def actOn (Y A : Subgroup Γ) (hAY : A ≤ Y) (pt : Fin m → α)
    (hpt : Function.Injective pt) (hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) :
    ↥A →* Equiv.Perm (Fin m) :=
  (actHom Y pt hpt hY).comp (Subgroup.inclusion hAY)

theorem actOn_apply {Y A : Subgroup Γ} (hAY : A ≤ Y) {pt : Fin m → α}
    {hpt : Function.Injective pt} {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} (a : ↥A) :
    actOn Y A hAY pt hpt hY a = rhoFn Y pt hpt hY (a : Γ) := by
  rw [rhoFn_of_mem (hAY a.2)]
  rfl

theorem actOn_range {Y : Subgroup Γ} {ol : List Γ} (hol : ∀ g ∈ ol, g ∈ Y) (pt : Fin m → α)
    (hpt : Function.Injective pt) (hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) :
    (actOn Y (Subgroup.closure {x | x ∈ ol}) ((Subgroup.closure_le Y).mpr fun g hg => hol g hg)
        pt hpt hY).range = Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hY)} := by
  have hAY : Subgroup.closure {x | x ∈ ol} ≤ Y := (Subgroup.closure_le Y).mpr fun g hg => hol g hg
  have hall : ∀ x ∈ Subgroup.closure {x | x ∈ ol},
      rhoFn Y pt hpt hY x ∈ Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hY)} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (List.mem_map.mpr ⟨x, hx, rfl⟩)
    | one => rw [rhoFn_one]; exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      rw [rhoFn_mul (hAY hx) (hAY hy)]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      rw [rhoFn_inv (hAY hx)]
      exact Subgroup.inv_mem _ ihx
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    rw [actOn_apply hAY]
    exact hall a.1 a.2
  · rw [Subgroup.closure_le]
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact ⟨⟨x, Subgroup.subset_closure hx⟩, by rw [actOn_apply hAY]⟩

theorem closure_fix {vl : List Γ} {pt : Fin m → α} (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) :
    ∀ v ∈ Subgroup.closure {x | x ∈ vl}, ∀ i, v • pt i = pt i := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact hvfix x hx
  | one => intro i; exact one_smul _ _
  | mul x y _ _ ihx ihy => intro i; rw [mul_smul, ihy, ihx]
  | inv x _ ihx => intro i; exact inv_smul_eq_iff.mpr (ihx i).symm

theorem actOn_ker_ge {Y V A : Subgroup Γ} (hAY : A ≤ Y) {pt : Fin m → α}
    {hpt : Function.Injective pt} {hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j}
    (hfix : ∀ v ∈ V, ∀ i, v • pt i = pt i) :
    V.subgroupOf A ≤ (actOn Y A hAY pt hpt hY).ker := by
  intro w hw
  rw [MonoidHom.mem_ker]
  show actHom Y pt hpt hY ⟨(w : Γ), hAY w.2⟩ = 1
  rw [actHom_eq_one_iff]
  exact hfix _ (Subgroup.mem_subgroupOf.mp hw)

variable [Finite Γ]

theorem ext_core_ge {Y : Subgroup Γ} {ol : List Γ} (hol : ∀ g ∈ ol, g ∈ Y) (pt : Fin m → α)
    (hpt : Function.Injective pt) (hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) (vl : List Γ)
    (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {x | x ∈ ol})
    (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) :
    Nat.card (Subgroup.closure {x | x ∈ vl}) *
        Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hY)}) ≤
      Nat.card (Subgroup.closure {x | x ∈ ol}) := by
  have hAY : Subgroup.closure {x | x ∈ ol} ≤ Y := (Subgroup.closure_le Y).mpr fun g hg => hol g hg
  have hVA : Subgroup.closure {x | x ∈ vl} ≤ Subgroup.closure {x | x ∈ ol} :=
    (Subgroup.closure_le _).mpr fun v hv => hvol v hv
  have hker := actOn_ker_ge (hpt := hpt) (hY := hY) hAY (closure_fix hvfix)
  have hrange := actOn_range hol pt hpt hY
  have h1 := Subgroup.card_ker_mul_card_range
    (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY)
  rw [hrange] at h1
  have hV : Nat.card (Subgroup.closure {x | x ∈ vl}) ≤
      Nat.card (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY).ker := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv]
    exact Subgroup.card_le_of_le hker
  rw [← h1]
  exact Nat.mul_le_mul_right _ hV

theorem ext_core {Y : Subgroup Γ} {ol : List Γ} {t : Γ} (hid : IdxTwoData Y ol t)
    (hperf : ⁅Subgroup.closure {x | x ∈ ol}, Subgroup.closure {x | x ∈ ol}⁆ =
      Subgroup.closure {x | x ∈ ol})
    (pt : Fin m → α) (hpt : Function.Injective pt) (hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j)
    (vl : List Γ) (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {x | x ∈ ol})
    (hVnorm : ∀ g ∈ ol ++ [t], ∀ v ∈ Subgroup.closure {x | x ∈ vl},
      g⁻¹ * v * g ∈ Subgroup.closure {x | x ∈ vl})
    (hvc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) (hvsq : ∀ a ∈ vl, a * a = 1)
    (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) {r : ℕ}
    (hE : Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hY)}) = r)
    (hcard : Nat.card (Subgroup.closure {x | x ∈ ol}) =
      Nat.card (Subgroup.closure {x | x ∈ vl}) * r) :
    ∃ (V' : Subgroup ↥(Subgroup.closure {x | x ∈ ol})) (_ : V'.Normal)
      (π : ↥(Subgroup.closure {x | x ∈ ol}) →* Equiv.Perm (Fin m)),
        (∀ x ∈ V', ∀ y ∈ V', x * y = y * x) ∧ (∀ x ∈ V', x * x = 1) ∧
        Nat.card V' = Nat.card (Subgroup.closure {x | x ∈ vl}) ∧ π.ker = V' ∧
        (∀ a, π a = rhoFn Y pt hpt hY (a : Γ)) ∧
        π.range = Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hY)} ∧
        Nat.card π.range = r ∧ ∀ a, Equiv.Perm.sign (π a) = 1 := by
  classical
  have hol : ∀ g ∈ ol, g ∈ Y := fun g hg => hid.mem g hg
  have hAY : Subgroup.closure {x | x ∈ ol} ≤ Y := (Subgroup.closure_le Y).mpr hol
  have hVA : Subgroup.closure {x | x ∈ vl} ≤ Subgroup.closure {x | x ∈ ol} :=
    (Subgroup.closure_le _).mpr fun v hv => hvol v hv
  have hrange := actOn_range hol pt hpt hY
  have hVconj := idxTwo_conj_mem hid hVnorm
  have hVn : ((Subgroup.closure {x | x ∈ vl}).subgroupOf
      (Subgroup.closure {x | x ∈ ol})).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVA]
    intro w a hw ha
    simpa using hVconj a⁻¹ (Y.inv_mem (hAY ha)) w hw
  have hker_ge := actOn_ker_ge (hpt := hpt) (hY := hY) hAY (closure_fix hvfix)
  have hr : 0 < r := hE ▸ Nat.card_pos
  have hrr : Nat.card (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY).range = r := by
    rw [← hE]
    exact Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv
  have hkc : Nat.card (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY).ker =
      Nat.card (Subgroup.closure {x | x ∈ vl}) := by
    have h1 := Subgroup.card_ker_mul_card_range
      (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY)
    rw [hrr, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hr h1
  have hVc' : Nat.card ((Subgroup.closure {x | x ∈ vl}).subgroupOf
      (Subgroup.closure {x | x ∈ ol})) = Nat.card (Subgroup.closure {x | x ∈ vl}) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv
  have hkereq : (Subgroup.closure {x | x ∈ vl}).subgroupOf (Subgroup.closure {x | x ∈ ol}) =
      (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY).ker :=
    Subgroup.eq_of_le_of_card_ge hker_ge (by rw [hkc, hVc'])
  have hAperf : commutator ↥(Subgroup.closure {x | x ∈ ol}) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  have hsign : ∀ a, Equiv.Perm.sign
      (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY a) = 1 := by
    intro a
    have hk : commutator ↥(Subgroup.closure {x | x ∈ ol}) ≤
        (Equiv.Perm.sign.comp (actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY)).ker :=
      Abelianization.commutator_subset_ker _
    rw [hAperf] at hk
    exact MonoidHom.mem_ker.mp (hk (Subgroup.mem_top a))
  refine ⟨_, hVn, actOn Y (Subgroup.closure {x | x ∈ ol}) hAY pt hpt hY,
    fun x hx y hy => Subtype.ext (closure_comm_of_gens hvc x.1 hx y.1 hy),
    fun x hx => Subtype.ext (closure_sq_of_gens hvc hvsq x.1 hx), hVc', hkereq.symm,
    fun a => actOn_apply hAY a, hrange, hrr, hsign⟩

end CFSG.Quasithin.A312M23
