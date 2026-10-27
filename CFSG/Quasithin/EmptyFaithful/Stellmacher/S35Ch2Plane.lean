module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Mbl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Std S35.Fin S35.Ch S35.II
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def UC (δ : Geo H M) : Prop := ⁅Vn δ, stab δ⁆ ⊓ Cb δ ≤ Zv δ

omit [Finite G] in
theorem comm_le_Vn {δ : Geo H M} {X A : Subgroup G} (hX : X ≤ Vn δ) (hA : A ≤ stab δ) :
    ⁅X, A⁆ ≤ Vn δ := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have h1 := conj_mem_Vn (hA ha) ((Vn δ).inv_mem (hX hx))
  have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact (Vn δ).mul_mem (hX hx) h1

omit [Finite G] in
theorem conj_mem_comm {X A : Subgroup G} (hXA : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {a : G}
    (ha : a ∈ A) {u : G} (hu : u ∈ ⁅X, A⁆) : a * u * a⁻¹ ∈ ⁅X, A⁆ := by
  have h : ⁅X, A⁆ ≤ ⁅X, A⁆.comap (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx b hb
    have e : a * ⁅x, b⁆ * a⁻¹ = ⁅a * x * a⁻¹, a * b * a⁻¹⁆ := by
      simp [commutatorElement_def]; group
    show a * ⁅x, b⁆ * a⁻¹ ∈ ⁅X, A⁆
    rw [e]
    exact Subgroup.commutator_mem_commutator (hXA a ha x hx)
      (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha))
  exact h hu

theorem Plane2_le_Vn (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) (l : Geo H M) :
    Plane2 δ l ≤ Vn δ :=
  sup_le (comm_le_Vn (comm_le_Vn le_rfl inf_le_left) inf_le_left) (S34.Zv_le_Vn hS.glob hδ)

omit [Finite G] in
theorem Zv_le_Plane2 (δ l : Geo H M) : Zv δ ≤ Plane2 δ l := le_sup_right

theorem inf_le_normalizer_Plane2 (hS : Sit H M S) (δ l : Geo H M) :
    stab δ ⊓ stab l ≤ Subgroup.normalizer ((Plane2 δ l : Subgroup G) : Set G) := by
  have h1 : ∀ a ∈ stab δ ⊓ stab l, ∀ x ∈ Vn δ, a * x * a⁻¹ ∈ Vn δ :=
    fun a ha x hx => conj_mem_Vn ha.1 hx
  have h2 : ∀ a ∈ stab δ ⊓ stab l, ∀ x ∈ ⁅Vn δ, stab δ ⊓ stab l⁆, a * x * a⁻¹ ∈
      ⁅Vn δ, stab δ ⊓ stab l⁆ := fun a ha x hx => conj_mem_comm h1 ha hx
  have h3 : stab δ ⊓ stab l ≤ Subgroup.normalizer
      ((⁅⁅Vn δ, stab δ ⊓ stab l⁆, stab δ ⊓ stab l⁆ : Subgroup G) : Set G) :=
    fun a ha => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact ⟨fun hx => conj_mem_comm h2 ha hx, fun hx => by
        have := conj_mem_comm h2 ((stab δ ⊓ stab l).inv_mem ha) hx
        simpa [mul_assoc] using this⟩
  have h4 : stab δ ⊓ stab l ≤ Subgroup.normalizer (Zv δ : Set G) :=
    inf_le_left.trans (stab_le_normalizer_Zv hS.glob.amalg δ)
  exact fun a ha => normalizer_inf_le_sup ⟨h3 ha, h4 ha⟩

omit [Finite G] in
theorem Plane2_le_comm_sup (δ l : Geo H M) : Plane2 δ l ≤ ⁅Vn δ, stab δ⁆ ⊔ Zv δ := by
  refine sup_le ?_ le_sup_right
  refine le_sup_of_le_left ?_
  refine (Subgroup.commutator_mono (comm_le_Vn le_rfl inf_le_left) le_rfl).trans ?_
  exact Subgroup.commutator_mono le_rfl inf_le_left

theorem UC.sup_inf_le (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) (hU : UC δ) :
    (⁅Vn δ, stab δ⁆ ⊔ Zv δ) ⊓ Cb δ ≤ Zv δ := by
  have hle : ⁅Vn δ, stab δ⁆ ≤ Subgroup.normalizer (Zv δ : Set G) := by
    refine Chart2.le_normalizer_of_forall' fun y hy z hz => ?_
    have hyS : y ∈ stab δ :=
      Qv_le_stab' δ (Vn_le_Qv_self hS δ (comm_le_Vn (X := Vn δ) le_rfl le_rfl hy))
    have := (hS.glob.central δ hδ hz).2 y hyS
    rw [this]
    simpa using hz
  rintro x ⟨hx, hxC⟩
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right ⁅Vn δ, stab δ⁆ (Zv δ) hle
  have hx' : x ∈ (↑(⁅Vn δ, stab δ⁆ ⊔ Zv δ) : Set G) := hx
  rw [hmul] at hx'
  obtain ⟨a, ha, z, hz, rfl⟩ := hx'
  have hzC : z ∈ Cb δ := S34.Zv_le_Cb hS.glob hδ hz
  have haC : a ∈ Cb δ := by
    have := (Cb δ).mul_mem hxC ((Cb δ).inv_mem hzC)
    simpa using this
  exact (Zv δ).mul_mem (hU ⟨ha, haC⟩) hz

theorem UC.Plane2_inf_le (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) (hU : UC δ)
    (l : Geo H M) : Plane2 δ l ⊓ Cb δ ≤ Zv δ :=
  fun _ hx => hU.sup_inf_le hS hδ ⟨Plane2_le_comm_sup δ l hx.1, hx.2⟩

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

include c

omit [Finite G] in
theorem img_comm {U A : Subgroup G} (hUV : U ≤ Vn δ) (hA : A ≤ stab δ) :
    c.img (⁅U, A⁆ ⊔ Cb δ) = commW orth (c.bar A) (c.img U) := by
  have hcV : ⁅U, A⁆ ≤ Vn δ := comm_le_Vn hUV hA
  apply le_antisymm
  · set K : Subgroup G := ((commW orth (c.bar A) (c.img U)).comap c.π).map (Vn δ).subtype
      with hK
    have hmemK : ∀ x : ↥(Vn δ), (x : G) ∈ K ↔ c.π x ∈ commW orth (c.bar A) (c.img U) := by
      intro x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro h
        exact ⟨x, h, rfl⟩
    have hle : ⁅U, A⁆ ⊔ Cb δ ≤ K := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx a ha
        have hcx : ⁅x, a⁆ ∈ Vn δ := hcV (Subgroup.commutator_mem_commutator hx ha)
        have e : (⟨⁅x, a⁆, hcx⟩ : ↥(Vn δ)) = (conjV ⟨a, hA ha⟩ ⟨x, hUV hx⟩ * ⟨x, hUV hx⟩⁻¹)⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def, mul_assoc]
        refine (hmemK ⟨_, hcx⟩).mpr ?_
        rw [e, map_inv, map_mul, map_inv, c.π_conj]
        refine Subgroup.inv_mem _ (Subgroup.subset_closure ⟨c.θ ⟨a, hA ha⟩, ?_, c.π ⟨x, hUV hx⟩,
          (c.mem_img_iff').mpr ⟨⟨x, hUV hx⟩, hx, rfl⟩, rfl⟩)
        exact c.mem_bar_of_mem ha (hA ha)
      · intro z hz
        refine (hmemK ⟨z, c.le hz⟩).mpr ?_
        rw [(c.π_eq_one _).mpr hz]
        exact Subgroup.one_mem _
    intro w hw
    obtain ⟨x, hxU, rfl⟩ := (c.mem_img_iff').mp hw
    exact (hmemK x).mp (hle hxU)
  · unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, u, hu, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
    obtain ⟨v, hvU, rfl⟩ := (c.mem_img_iff').mp hu
    refine (c.mem_img_iff').mpr ⟨conjV a v * v⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_sup_left ?_
      have e : ((conjV a v * v⁻¹ : ↥(Vn δ)) : G) = (⁅(v : G), (a : G)⁆)⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (⁅U, A⁆).inv_mem (Subgroup.commutator_mem_commutator hvU ha)
    · rw [map_mul, map_inv, c.π_conj]

theorem img_Plane2 (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.img (Plane2 δ l) = commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤ := by
  have hD := c.card_Dl hS hl
  have hDle : stab δ ⊓ stab l ≤ stab δ := inf_le_left
  have hU1 : ⁅Vn δ, stab δ ⊓ stab l⁆ ≤ Vn δ := comm_le_Vn le_rfl hDle
  have h1 : c.img (⁅Vn δ, stab δ ⊓ stab l⁆) = commW orth (c.Dl l) ⊤ := by
    rw [← c.img_sup_Cb hU1]
    have := c.img_comm (le_refl (Vn δ)) hDle
    rw [c.img_Vn] at this
    exact this
  have h2 : Plane2 δ l ⊔ Cb δ = ⁅⁅Vn δ, stab δ ⊓ stab l⁆, stab δ ⊓ stab l⁆ ⊔ Cb δ := by
    unfold Plane2
    rw [sup_assoc, sup_eq_right.mpr (S34.Zv_le_Cb hS.glob hδ)]
  rw [← c.img_sup_Cb (Plane2_le_Vn hS hδ l), h2, c.img_comm hU1 hDle, h1]
  exact commW_two_eq hD (isCentInv_zc hD)

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
