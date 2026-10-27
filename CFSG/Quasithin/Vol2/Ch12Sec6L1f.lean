module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem26A8Sh
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Vol2.Ch12Sec6FF
public import CFSG.Quasithin.Vol2.Ch12Sec6Pm
public import CFSG.Quasithin.Vol2.Ch12Sec6T2A6
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

namespace S126L1f

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique S126 S126P Equiv
open scoped IsMulCommutative commutatorElement

theorem sum_corr : ∀ x : Fin 8 → ZMod 2, x 0 = 0 →
    ∑ i, (if i = 0 then 0 else x i + ∑ j, x j) = 0 := by
  decide +kernel

theorem exists_cob (c : ↥(alternatingGroup (Fin 8)) → D8)
    (hc : ∀ σ τ, c (σ * τ) = dAct σ (c τ) * c σ) :
    ∃ d : D8, ∀ σ : ↥(alternatingGroup (Fin 8)), (σ : Perm (Fin 8)) 0 = 0 →
      c σ = dAct σ d * d⁻¹ := by
  classical
  let α := {i : Fin 8 // i ≠ 0}
  have hmem : ∀ τ : Perm α, τ ∈ alternatingGroup α →
      Perm.ofSubtype τ ∈ alternatingGroup (Fin 8) := fun τ hτ => by
    rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
    exact hτ
  let ι : ↥(alternatingGroup α) → ↥(alternatingGroup (Fin 8)) :=
    fun τ => ⟨Perm.ofSubtype (τ : Perm α), hmem τ τ.2⟩
  have hι_mul : ∀ τ₁ τ₂, ι (τ₁ * τ₂) = ι τ₁ * ι τ₂ := fun τ₁ τ₂ =>
    Subtype.ext (map_mul Perm.ofSubtype (τ₁ : Perm α) τ₂)
  have hι0 : ∀ τ, ((ι τ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) 0 = 0 := fun τ =>
    Perm.ofSubtype_apply_of_not_mem (τ : Perm α) (by simp)
  have hιinv : ∀ (τ : ↥(alternatingGroup α)) (y : α),
      ((ι τ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))⁻¹ y.1 = ((τ⁻¹ • y : α) : Fin 8) := by
    intro τ y
    show (Perm.ofSubtype (τ : Perm α))⁻¹ y.1 = (((τ : Perm α)⁻¹ y : α) : Fin 8)
    rw [← map_inv, Perm.ofSubtype_apply_coe]
  let c' : ↥(alternatingGroup α) → α → ZMod 2 := fun τ y =>
    Multiplicative.toAdd (S126F.iota (c (ι τ))) y.1
  have hc' : ∀ g h y, c' (g * h) y = c' g y + c' h (g⁻¹ • y) := by
    intro g h y
    have e0 : ((ι g : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))⁻¹ 0 = 0 := by
      rw [Perm.inv_eq_iff_eq, hι0]
    show Multiplicative.toAdd (S126F.iota (c (ι (g * h)))) y.1 =
      Multiplicative.toAdd (S126F.iota (c (ι g))) y.1 +
        Multiplicative.toAdd (S126F.iota (c (ι h))) (g⁻¹ • y : α).1
    rw [hι_mul, hc, map_mul, toAdd_mul, Pi.add_apply, S126F.iota_dAct, hιinv, e0,
      S126F.iota_zero, add_zero, add_comm]
  have h3 : 3 ≤ Nat.card α := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨e, he⟩ := Lem26A8.exists_coboundary_alternatingGroup h3 c' hc'
  let x : Fin 8 → ZMod 2 := fun i => if h : i = 0 then 0 else e ⟨i, h⟩
  let x' : Fin 8 → ZMod 2 := fun i => if i = 0 then 0 else x i + ∑ j, x j
  have hx0 : x 0 = 0 := by simp [x]
  have hx'0 : x' 0 = 0 := by simp [x']
  have hsum : Multiplicative.ofAdd x' ∈ coreMod 8 := sum_corr x hx0
  let d : D8 := QuotientGroup.mk ⟨Multiplicative.ofAdd x', hsum⟩
  have hd : ∀ i, Multiplicative.toAdd (S126F.iota d) i = x' i := by
    intro i
    rw [S126F.iota_mk, S126F.nrm_apply]
    show x' i + x' 0 = x' i
    rw [hx'0, add_zero]
  refine ⟨d, fun σ hσ0 => ?_⟩
  have hp : ∀ i, (fun j : Fin 8 => j ≠ 0) ((σ : Perm (Fin 8)) i) ↔ (fun j : Fin 8 => j ≠ 0) i := by
    intro i
    simp only
    constructor
    · intro h hi
      exact h (by rw [hi, hσ0])
    · intro h hi
      exact h ((σ : Perm (Fin 8)).injective (hi.trans hσ0.symm))
  let τ₀ : Perm α := (σ : Perm (Fin 8)).subtypePerm hp
  have hτσ : Perm.ofSubtype τ₀ = (σ : Perm (Fin 8)) :=
    Perm.ofSubtype_subtypePerm hp fun i hi h0 => hi (by rw [h0, hσ0])
  have hτ₀ : τ₀ ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hτσ]
    exact σ.2
  have hιτ : ι ⟨τ₀, hτ₀⟩ = σ := Subtype.ext hτσ
  apply S126F.iota_inj
  apply Multiplicative.toAdd.injective
  funext i
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, S126F.iota_dAct,
    hd, hd, hd]
  by_cases hi : i = 0
  · subst hi
    rw [S126F.iota_zero, Perm.inv_eq_iff_eq.2 hσ0.symm, hx'0]
    simp
  · have hσi : (σ : Perm (Fin 8))⁻¹ i ≠ 0 := fun h => hi (by
      rw [Perm.inv_eq_iff_eq] at h
      rw [h, hσ0])
    have h1 := he ⟨τ₀, hτ₀⟩ ⟨i, hi⟩
    have h2 : c' ⟨τ₀, hτ₀⟩ ⟨i, hi⟩ = Multiplicative.toAdd (S126F.iota (c σ)) i := by
      show Multiplicative.toAdd (S126F.iota (c (ι ⟨τ₀, hτ₀⟩))) i = _
      rw [hιτ]
    have h3' : ((⟨τ₀, hτ₀⟩ : ↥(alternatingGroup α))⁻¹ • (⟨i, hi⟩ : α) : α) =
        ⟨(σ : Perm (Fin 8))⁻¹ i, hσi⟩ := by
      apply Subtype.ext
      rw [← hιinv, hιτ]
    have hσ0' : (σ : Perm (Fin 8))⁻¹ 0 = 0 := Perm.inv_eq_iff_eq.2 hσ0.symm
    have ex : ∀ (j : Fin 8) (hj : j ≠ 0), x' j = e ⟨j, hj⟩ + ∑ k, x k := fun j hj => by
      show (if j = 0 then 0 else x j + ∑ k, x k) = _
      rw [ite_eq_right hj]
      congr 1
      show (if h : j = 0 then 0 else e ⟨j, h⟩) = _
      rw [dite_eq_right hj]
    rw [← h2, h1, h3', hσ0', hx'0, ex _ hσi, ex _ hi]
    have key : ∀ a b t : ZMod 2, a + b = a + t + 0 + -(b + t) := by decide
    exact key _ _ _

theorem fix_vec : ∀ x : Fin 8 → ZMod 2, x 0 = 0 → ∑ i, x i = 0 →
    (∀ i, x ((S126T2.cy 2 3 4)⁻¹ i) = x i) → (∀ i, x ((S126T2.cy 3 4 5)⁻¹ i) = x i) →
    (∀ i, x ((S126T2.cy 4 5 6)⁻¹ i) = x i) → (∀ i, x ((S126T2.cy 5 6 7)⁻¹ i) = x i) →
    x = 0 ∨ x = fun i => B5FinS8.pv 0 1 i + B5FinS8.pv 0 1 0 := by
  decide +kernel

theorem d01_ne_one : (QuotientGroup.mk (pe 0 1) : D8) ≠ 1 := by
  intro h
  have h1 := congrArg (fun y : D8 => Multiplicative.toAdd (S126F.iota y) 2) h
  simp only [S126F.iota_mk, S126F.nrm_apply, map_one, toAdd_one, Pi.zero_apply] at h1
  exact absurd h1 (by decide)

theorem fix_cases {y : D8} (h₁ : dAct (S126T2.cy 2 3 4) y = y)
    (h₂ : dAct (S126T2.cy 3 4 5) y = y) (h₃ : dAct (S126T2.cy 4 5 6) y = y)
    (h₄ : dAct (S126T2.cy 5 6 7) y = y) : y = 1 ∨ y = QuotientGroup.mk (pe 0 1) := by
  have key : ∀ {σ : Perm (Fin 8)}, σ⁻¹ 0 = 0 → dAct σ y = y →
      ∀ i, Multiplicative.toAdd (S126F.iota y) (σ⁻¹ i) =
        Multiplicative.toAdd (S126F.iota y) i := by
    intro σ hσ h i
    have := S126F.cond_of_fix h i
    rwa [hσ, S126F.iota_zero, add_zero] at this
  rcases fix_vec _ (S126F.iota_zero y) (S126F.iota_sum y) (key (by decide) h₁)
      (key (by decide) h₂) (key (by decide) h₃) (key (by decide) h₄) with h | h
  · left
    apply S126F.iota_inj
    rw [map_one]
    exact Multiplicative.toAdd.injective (h.trans toAdd_one.symm)
  · right
    apply S126F.iota_inj
    apply Multiplicative.toAdd.injective
    rw [h, S126F.iota_mk]
    funext i
    rw [S126F.nrm_apply]
    rfl

theorem exists_k (i : Fin 8) (hi : i ≠ 0) :
    ∃ k : ↥(alternatingGroup (Fin 8)), (k : Perm (Fin 8)) 0 = 0 ∧ (k : Perm (Fin 8)) 1 = i := by
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨⟨swap 1 2 * swap 3 4, Perm.mem_alternatingGroup.2 (by decide)⟩, by decide, by decide⟩
  · exact ⟨⟨swap 1 3 * swap 2 4, Perm.mem_alternatingGroup.2 (by decide)⟩, by decide, by decide⟩
  · exact ⟨⟨swap 1 4 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩, by decide, by decide⟩
  · exact ⟨⟨swap 1 5 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩, by decide, by decide⟩
  · exact ⟨⟨swap 1 6 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩, by decide, by decide⟩
  · exact ⟨⟨swap 1 7 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩, by decide, by decide⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem mem_centralizer_of_comm_mem {L Z : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hZ : Z ≤ Subgroup.centralizer (L : Set G)) (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {x : G}
    (hx : ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ Z) : x ∈ Subgroup.centralizer (L : Set G) := by
  let φ : ↥L →* ↥Z :=
    { toFun := fun l => ⟨(l : G) * x * (l : G)⁻¹ * x⁻¹, hx l l.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a * b : ↥L) : G) * x * ((a * b : ↥L) : G)⁻¹ * x⁻¹ =
          ((a : G) * x * (a : G)⁻¹ * x⁻¹) * ((b : G) * x * (b : G)⁻¹ * x⁻¹)
        have hb := hx b b.2
        have hab : (a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) =
            ((b : G) * x * (b : G)⁻¹ * x⁻¹) * a :=
          Subgroup.mem_centralizer_iff.1 (hZ hb) a a.2
        have hc := hZc _ (hx a a.2) _ hb
        calc ((a * b : ↥L) : G) * x * ((a * b : ↥L) : G)⁻¹ * x⁻¹ =
            (a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹ *
              ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
          _ = ((b : G) * x * (b : G)⁻¹ * x⁻¹) * ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
              rw [hab]
              group
          _ = _ := hc.symm }
  have hker : ∀ l (hl : l ∈ L), φ ⟨l, hl⟩ = 1 := by
    have hle : ⁅L, L⁆ ≤ φ.ker.map L.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆, (?_ : _ ∈ φ.ker), rfl⟩
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hZc _ (φ ⟨a, ha⟩).2 _ (φ ⟨b, hb⟩).2)
    intro l hl
    rw [hLp] at hle
    obtain ⟨l', hl', he⟩ := hle hl
    have : l' = ⟨l, hl⟩ := Subtype.ext he
    rw [← this]
    exact hl'
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 : l * x * l⁻¹ * x⁻¹ = 1 := congrArg Subtype.val (hker l hl)
  calc l * x = (l * x * l⁻¹ * x⁻¹) * (x * l) := by group
    _ = x * l := by rw [h2, one_mul]

theorem relIndex_le_two (F : Frame126 T L V) (hH : Hyp126 G T L V) {W : Subgroup G}
    [IsMulCommutative ↥W] (hVW : V ≤ W) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hCW : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (W : Set G))
    (hWL : ⁅W, L⁆ ≤ V) :
    (V ⊔ (W ⊓ Subgroup.centralizer (L : Set G))).relIndex W ≤ 2 := by
  classical
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hLp : ⁅L, L⁆ = L := hyp.maximal.1.2.1.2.1
  have hlift : ∀ σ : ↥(alternatingGroup (Fin 8)), ∃ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ L ∧ conjAct V g = ((F.π σ : ↥(autOn L V)) : MulAut ↥V) :=
    fun σ => Setup.mem_autOn_iff.1 (F.π σ).2
  choose lf hlfL hlfπ using hlift
  have hact : ∀ σ, ActsAs F (lf σ : G) σ := fun σ => actsAs_of_pi F (lf σ).2 σ (hlfπ σ)
  have hcomm : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ * w⁻¹ ∈ V := by
    intro l hl w hw
    have h1 := V.inv_mem (hWL (Subgroup.commutator_mem_commutator hw hl))
    rw [commutatorElement_def] at h1
    convert h1 using 1
    group
  have hsame : ∀ g g' : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L → (g' : G) ∈ L →
      conjAct V g = conjAct V g' → ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ = g' * w * (g' : G)⁻¹ := by
    intro g g' hg hg' he w hw
    have hm : (g : G)⁻¹ * g' ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨L.mul_mem (L.inv_mem hg) hg', ?_⟩
      have h1 : conjAct V (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      show (g : G)⁻¹ * g' ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h1
      simp only [Setup.coe_conjAct_apply, MulAut.one_apply] at h2
      have h3 : ((g : G)⁻¹ * g') * v * ((g : G)⁻¹ * g')⁻¹ = v := by simpa using h2
      calc v * ((g : G)⁻¹ * g') = ((g : G)⁻¹ * g') * v * ((g : G)⁻¹ * g')⁻¹ * ((g : G)⁻¹ * g') := by
            rw [h3]
        _ = ((g : G)⁻¹ * g') * v := by group
    have hc := Subgroup.mem_centralizer_iff.1 (hCW hm) w hw
    calc (g : G) * w * (g : G)⁻¹ = g * (w * ((g : G)⁻¹ * g')) * ((g : G)⁻¹ * g')⁻¹ * (g : G)⁻¹ := by
          group
      _ = g * (((g : G)⁻¹ * g') * w) * ((g : G)⁻¹ * g')⁻¹ * (g : G)⁻¹ := by rw [hc]
      _ = g' * w * (g' : G)⁻¹ := by group
  let coc : ↥W → ↥(alternatingGroup (Fin 8)) → D8 := fun w σ =>
    F.β ⟨(lf σ : G) * w * (lf σ : G)⁻¹ * (w : G)⁻¹, hcomm _ (hlfL σ) _ w.2⟩
  have hcoc : ∀ (σ : ↥(alternatingGroup (Fin 8))) (g : ↥(Subgroup.normalizer (V : Set G)))
      (hg : (g : G) ∈ L), conjAct V g = ((F.π σ : ↥(autOn L V)) : MulAut ↥V) → ∀ w : ↥W,
      coc w σ = F.β ⟨(g : G) * w * (g : G)⁻¹ * (w : G)⁻¹, hcomm _ hg _ w.2⟩ := by
    intro σ g hg he w
    show F.β _ = F.β _
    congr 1
    apply Subtype.ext
    show (lf σ : G) * w * (lf σ : G)⁻¹ * (w : G)⁻¹ = g * w * (g : G)⁻¹ * (w : G)⁻¹
    rw [hsame (lf σ) g (hlfL σ) hg ((hlfπ σ).trans he.symm) w w.2]
  have hcoc_mul : ∀ (w : ↥W) (σ τ : ↥(alternatingGroup (Fin 8))),
      coc w (σ * τ) = dAct σ (coc w τ) * coc w σ := by
    intro w σ τ
    have he : conjAct V (lf σ * lf τ) = ((F.π (σ * τ) : ↥(autOn L V)) : MulAut ↥V) := by
      rw [map_mul, hlfπ, hlfπ, map_mul, Subgroup.coe_mul]
    rw [hcoc (σ * τ) (lf σ * lf τ) (L.mul_mem (hlfL σ) (hlfL τ)) he w]
    have hy := hcomm _ (hlfL τ) _ w.2
    have hconjy : (lf σ : G) * ((lf τ : G) * w * (lf τ : G)⁻¹ * (w : G)⁻¹) * (lf σ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV (hlfL σ)) _).1 hy
    have hsplit : (⟨((lf σ * lf τ : ↥(Subgroup.normalizer (V : Set G))) : G) * w *
        ((lf σ * lf τ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ * (w : G)⁻¹,
        hcomm _ (L.mul_mem (hlfL σ) (hlfL τ)) _ w.2⟩ : ↥V) =
        ⟨_, hconjy⟩ * ⟨(lf σ : G) * w * (lf σ : G)⁻¹ * (w : G)⁻¹, hcomm _ (hlfL σ) _ w.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [hsplit, map_mul, hact σ ⟨_, hy⟩ ⟨_, hconjy⟩ rfl]
  have hcoc_w : ∀ (w₁ w₂ : ↥W) σ, coc (w₁ * w₂) σ = coc w₁ σ * coc w₂ σ := by
    intro w₁ w₂ σ
    show F.β _ = F.β _ * F.β _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    have hk := hLW (hlfL σ)
    have hw1 : (lf σ : G) * w₁ * (lf σ : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hk _).1 w₁.2
    have hw2 : (lf σ : G) * w₂ * (lf σ : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hk _).1 w₂.2
    have key : ∀ a b c d : ↥W, a * b * (c * d)⁻¹ = (a * c⁻¹) * (b * d⁻¹) := fun a b c d => by
      rw [mul_inv, mul_mul_mul_comm]
    have h1 := congrArg Subtype.val (key ⟨_, hw1⟩ ⟨_, hw2⟩ w₁ w₂)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    simp only [Subgroup.coe_mul]
    calc (lf σ : G) * ((w₁ : G) * w₂) * (lf σ : G)⁻¹ * ((w₁ : G) * w₂)⁻¹ =
        (lf σ : G) * w₁ * (lf σ : G)⁻¹ * ((lf σ : G) * w₂ * (lf σ : G)⁻¹) *
          ((w₁ : G) * w₂)⁻¹ := by group
      _ = _ := h1
  have hcoc_V : ∀ (v : ↥V) σ, coc ⟨v, hVW v.2⟩ σ = dAct σ (F.β v) * (F.β v)⁻¹ := by
    intro v σ
    have hv' : (lf σ : G) * v * (lf σ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV (hlfL σ)) v).1 v.2
    have hsplit : (⟨(lf σ : G) * v * (lf σ : G)⁻¹ * (v : G)⁻¹,
        hcomm _ (hlfL σ) _ (hVW v.2)⟩ : ↥V) = ⟨_, hv'⟩ * v⁻¹ := Subtype.ext (by simp)
    show F.β _ = _
    rw [hsplit, map_mul, map_inv, hact σ v ⟨_, hv'⟩ rfl]
  let cocHom : ↥(alternatingGroup (Fin 8)) → (↥W →* D8) := fun σ =>
    { toFun := fun w => coc w σ
      map_one' := by
        show F.β ⟨(lf σ : G) * ((1 : ↥W) : G) * (lf σ : G)⁻¹ * ((1 : ↥W) : G)⁻¹,
          hcomm _ (hlfL σ) _ (1 : ↥W).2⟩ = 1
        have h1 : (⟨(lf σ : G) * ((1 : ↥W) : G) * (lf σ : G)⁻¹ * ((1 : ↥W) : G)⁻¹,
            hcomm _ (hlfL σ) _ (1 : ↥W).2⟩ : ↥V) = 1 := Subtype.ext (by simp)
        rw [h1, map_one]
      map_mul' := fun w₁ w₂ => hcoc_w w₁ w₂ σ }
  have hcocHom : ∀ σ w, cocHom σ w = coc w σ := fun _ _ => rfl
  let X : Subgroup ↥W :=
    ⨅ (σ : ↥(alternatingGroup (Fin 8))) (_ : (σ : Perm (Fin 8)) 0 = 0), (cocHom σ).ker
  have hX : ∀ x : ↥W, x ∈ X → ∀ σ : ↥(alternatingGroup (Fin 8)), (σ : Perm (Fin 8)) 0 = 0 →
      coc x σ = 1 := by
    intro x hx σ hσ
    have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx σ) hσ
    rwa [MonoidHom.mem_ker, hcocHom] at h1
  have hWX : ∀ w : ↥W, ∃ v : ↥V, w * (⟨v, hVW v.2⟩ : ↥W)⁻¹ ∈ X := by
    intro w
    obtain ⟨d, hd⟩ := exists_cob (fun σ => coc w σ) (fun σ τ => hcoc_mul w σ τ)
    obtain ⟨v, hv⟩ := F.β_surj d
    refine ⟨v, ?_⟩
    rw [Subgroup.mem_iInf]
    intro σ
    rw [Subgroup.mem_iInf]
    intro hσ
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcocHom, hcocHom, hd σ hσ, hcoc_V v σ, hv,
      mul_inv_cancel]
  have hh : swap (0 : Fin 8) 1 * swap 2 3 ∈ alternatingGroup (Fin 8) :=
    Perm.mem_alternatingGroup.2 (by decide)
  let h₀ : ↥(alternatingGroup (Fin 8)) := ⟨swap 0 1 * swap 2 3, hh⟩
  have hh₀ : (h₀ : Perm (Fin 8)) 0 = 1 := by
    show (swap (0 : Fin 8) 1 * swap 2 3 : Perm (Fin 8)) 0 = 1
    decide
  have hfixh : ∀ x : ↥W, x ∈ X → ∀ s : ↥(alternatingGroup (Fin 8)),
      (s : Perm (Fin 8)) 0 = 0 → (s : Perm (Fin 8)) 1 = 1 → dAct s (coc x h₀) = coc x h₀ := by
    intro x hx s hs0 hs1
    have hm0 : ((h₀⁻¹ * s * h₀ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) 0 = 0 := by
      show (h₀ : Perm (Fin 8))⁻¹ ((s : Perm (Fin 8)) ((h₀ : Perm (Fin 8)) 0)) = 0
      rw [hh₀, hs1, Perm.inv_eq_iff_eq, hh₀]
    have e2 : s * h₀ = h₀ * (h₀⁻¹ * s * h₀) := by group
    have h1 := hcoc_mul x s h₀
    have h2 := hcoc_mul x h₀ (h₀⁻¹ * s * h₀)
    rw [hX x hx s hs0, mul_one] at h1
    rw [hX x hx _ hm0, map_one, one_mul, ← e2] at h2
    rw [← h1, h2]
  have hall : ∀ x : ↥W, x ∈ X → coc x h₀ = 1 → ∀ σ, coc x σ = 1 := by
    intro x hx hxh σ
    by_cases hσ0 : (σ : Perm (Fin 8)) 0 = 0
    · exact hX x hx σ hσ0
    · obtain ⟨k, hk0, hk1⟩ := exists_k ((σ : Perm (Fin 8)) 0) hσ0
      have hm0 : (((k * h₀)⁻¹ * σ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) 0 = 0 := by
        show ((k : Perm (Fin 8)) * (h₀ : Perm (Fin 8)))⁻¹ ((σ : Perm (Fin 8)) 0) = 0
        rw [Perm.inv_eq_iff_eq, Perm.mul_apply, hh₀, hk1]
      have e : σ = k * (h₀ * ((k * h₀)⁻¹ * σ)) := by group
      rw [e, hcoc_mul, hcoc_mul, hX x hx _ hm0, map_one, one_mul, hxh, map_one,
        hX x hx k hk0, one_mul]
  have hcent : ∀ x : ↥W, x ∈ X → coc x h₀ = 1 →
      (x : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro x hx hxh
    have h0 := hall x hx hxh
    refine mem_centralizer_of_comm_mem hLp inf_le_right (fun a ha b hb =>
      congrArg Subtype.val (mul_comm (⟨a, ha.1⟩ : ↥V) ⟨b, hb.1⟩)) fun l hl => ?_
    have hlV := hLV hl
    have ha : conjAct V ⟨l, hlV⟩ ∈ autOn L V := Setup.mem_autOn_iff.2 ⟨⟨l, hlV⟩, hl, rfl⟩
    obtain ⟨σ, hσ⟩ := F.π_surj ⟨_, ha⟩
    have he : conjAct V ⟨l, hlV⟩ = ((F.π σ : ↥(autOn L V)) : MulAut ↥V) := by rw [hσ]
    have h1 := hcoc σ ⟨l, hlV⟩ hl he x
    rw [h0 σ] at h1
    exact ⟨hcomm l hl x x.2, (F.β_ker _).1 h1.symm⟩
  set N' : Subgroup ↥W := V.subgroupOf W ⊔ (Subgroup.centralizer (L : Set G)).subgroupOf W
    with hN'
  have hrel : (V ⊔ (W ⊓ Subgroup.centralizer (L : Set G))).relIndex W = N'.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_sup hVW inf_le_left,
      Subgroup.inf_subgroupOf_left]
  rw [hrel]
  have htop : X ⊔ N' = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, hv⟩ := hWX w
    have e : w = (w * (⟨v, hVW v.2⟩ : ↥W)⁻¹) * ⟨v, hVW v.2⟩ := by group
    rw [e]
    exact Subgroup.mul_mem_sup hv (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 v.2))
  have h1 : N'.index = N'.relIndex X := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  rw [h1]
  let Ψ : ↥X →* D8 := (cocHom h₀).comp X.subtype
  have hΨ : ∀ x : ↥X, Ψ x = coc x h₀ := fun _ => rfl
  have hker : Ψ.ker ≤ N'.subgroupOf X := by
    intro x hx
    rw [MonoidHom.mem_ker, hΨ] at hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 (hcent x x.2 hx))
  have hval : ∀ r ∈ Ψ.range, r = 1 ∨ r = QuotientGroup.mk (pe 0 1) := by
    rintro _ ⟨x, rfl⟩
    rw [hΨ]
    have hs : ∀ {a b d : Fin 8}, a ≠ b → a ≠ d → a ∈ S126T2.six → b ∈ S126T2.six →
        d ∈ S126T2.six → S126T2.cy a b d ∈ alternatingGroup (Fin 8) :=
      fun h1 h2 h3 h4 h5 => (S126T2.mem_A6s.1 (S126T2.cy_mem h1 h2 h3 h4 h5)).2.2
    exact fix_cases
      (hfixh x x.2 ⟨S126T2.cy 2 3 4, hs (by decide) (by decide) (by decide) (by decide)
        (by decide)⟩ (by show S126T2.cy 2 3 4 0 = 0; decide)
        (by show S126T2.cy 2 3 4 1 = 1; decide))
      (hfixh x x.2 ⟨S126T2.cy 3 4 5, hs (by decide) (by decide) (by decide) (by decide)
        (by decide)⟩ (by show S126T2.cy 3 4 5 0 = 0; decide)
        (by show S126T2.cy 3 4 5 1 = 1; decide))
      (hfixh x x.2 ⟨S126T2.cy 4 5 6, hs (by decide) (by decide) (by decide) (by decide)
        (by decide)⟩ (by show S126T2.cy 4 5 6 0 = 0; decide)
        (by show S126T2.cy 4 5 6 1 = 1; decide))
      (hfixh x x.2 ⟨S126T2.cy 5 6 7, hs (by decide) (by decide) (by decide) (by decide)
        (by decide)⟩ (by show S126T2.cy 5 6 7 0 = 0; decide)
        (by show S126T2.cy 5 6 7 1 = 1; decide))
  have hrange : Nat.card ↥Ψ.range ≤ 2 := by
    have hinj : Function.Injective (fun r : ↥Ψ.range => decide ((r : D8) = 1)) := by
      intro r r' hrr
      apply Subtype.ext
      simp only at hrr
      rcases hval r r.2 with h1 | h1 <;> rcases hval r' r'.2 with h2 | h2
      · rw [h1, h2]
      · exfalso
        rw [h1, h2] at hrr
        have h3 : decide ((QuotientGroup.mk (pe 0 1) : D8) = 1) = true := by
          rw [← hrr]
          exact decide_eq_true rfl
        exact d01_ne_one (of_decide_eq_true h3)
      · exfalso
        rw [h1, h2] at hrr
        have h3 : decide ((QuotientGroup.mk (pe 0 1) : D8) = 1) = true := by
          rw [hrr]
          exact decide_eq_true rfl
        exact d01_ne_one (of_decide_eq_true h3)
      · rw [h1, h2]
    calc Nat.card ↥Ψ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  calc N'.relIndex X = (N'.subgroupOf X).index := rfl
    _ ≤ Ψ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card ↥Ψ.range := Subgroup.index_ker Ψ
    _ ≤ 2 := hrange

end S126L1f

end CFSG.Quasithin.H13
