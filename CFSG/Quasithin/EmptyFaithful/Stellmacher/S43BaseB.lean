module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43

variable {α : Geo H M}

theorem exists_sit29 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ l : Geo H M}
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ∃ a₂ a₃ : Geo H M, S29.Sit29 H M S l a₂ a₃ δ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have hs' := hs.of_vtype_false hlv
  exact S29.exists_sit29' hA (hss28At_of_hss26A hA h26) h26 hs.b1 (nbrs_symm hl) hlv hs'.bα
    (hs.Zv_le_centerOf hA h26 hδ) (Or.inl hs'.orth)

end Sit43

theorem Yv_eq_of_sit29 {α a₂ a₃ δ : Geo H M} (hs : S29.Sit29 H M S α a₂ a₃ δ) :
    Yv δ = Zv α ⊓ Zv a₂ := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (iInf₂_le (f := fun (l : Geo H M) (_ : l ∈ nbrs δ) => Zv l) α hs.n₁)
    · exact (iInf₂_le (f := fun (l : Geo H M) (_ : l ∈ nbrs δ) => Zv l) a₂ hs.n₂)
  · refine le_iInf₂ fun w hw => ?_
    rcases hs.nbrs_eq w hw with h | h | h
    · rw [h]; exact inf_le_left
    · rw [h]; exact inf_le_right
    · rw [h, hs.R_eq₂]; exact inf_le_right

omit [Finite G] in
theorem commutator_sup_eq_of_centralizes {Z C T : Subgroup G}
    (hC : ∀ c ∈ C, ∀ z ∈ Z, c * z = z * c) (hT : T ≤ Subgroup.normalizer (C : Set G))
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) :
    ⁅Z, C ⊔ T⁆ = ⁅Z, T⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro z hz x hx
    obtain ⟨c, hc, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hT).mp hx
    have hzt : ⁅z, t⁆ ∈ Z := by
      have h1 : t * z⁻¹ * t⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hTZ ht) z⁻¹).mp (Z.inv_mem hz)
      have : ⁅z, t⁆ = z * (t * z⁻¹ * t⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Z.mul_mem hz h1
    have h1 : ⁅z, c * t⁆ = ⁅z, t⁆ := by
      have hcz : c * z = z * c := hC c hc z hz
      have hct : c * ⁅z, t⁆ = ⁅z, t⁆ * c := hC c hc _ hzt
      simp only [commutatorElement_def, mul_inv_rev] at hct ⊢
      calc z * (c * t) * z⁻¹ * (t⁻¹ * c⁻¹) = c * (z * t * z⁻¹ * t⁻¹) * c⁻¹ := by
            have : c * z = z * c := hcz
            calc z * (c * t) * z⁻¹ * (t⁻¹ * c⁻¹) = (z * c) * t * z⁻¹ * t⁻¹ * c⁻¹ := by group
              _ = (c * z) * t * z⁻¹ * t⁻¹ * c⁻¹ := by rw [this]
              _ = c * (z * t * z⁻¹ * t⁻¹) * c⁻¹ := by group
        _ = (z * t * z⁻¹ * t⁻¹ * c) * c⁻¹ := by rw [hct]
        _ = z * t * z⁻¹ * t⁻¹ := by group
    rw [h1]
    exact Subgroup.commutator_mem_commutator hz ht
  · exact Subgroup.commutator_mono le_rfl le_sup_right

omit [Finite G] in
theorem Yv_le_Zv {δ l : Geo H M} (hl : l ∈ nbrs δ) : Yv δ ≤ Zv l :=
  iInf₂_le (f := fun (l : Geo H M) (_ : l ∈ nbrs δ) => Zv l) l hl

omit [Finite G] in
theorem commutator_iSup_le {ι : Type*} {A : ι → Subgroup G} {Q X Y : Subgroup G}
    (hX : ∀ i, A i ≤ X) (hY : X ≤ Subgroup.normalizer (Y : Set G))
    (h : ∀ i, ⁅A i, Q⁆ ≤ Y) : ⁅⨆ i, A i, Q⁆ ≤ Y := by
  let N : Subgroup G :=
    { carrier := {v | v ∈ X ∧ ∀ q ∈ Q, ⁅v, q⁆ ∈ Y}
      one_mem' := ⟨X.one_mem, fun q _ => by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
        refine ⟨X.mul_mem hv hw, fun q hq => ?_⟩
        have e : ⁅v * w, q⁆ = v * ⁅w, q⁆ * v⁻¹ * ⁅v, q⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY hv) _).mp (hw' q hq)) (hv' q hq)
      inv_mem' := by
        rintro v ⟨hv, hv'⟩
        refine ⟨X.inv_mem hv, fun q hq => ?_⟩
        have e : ⁅v⁻¹, q⁆ = v⁻¹ * ⁅v, q⁆⁻¹ * v⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hY (X.inv_mem hv)) _).mp (Y.inv_mem (hv' q hq)) }
  have hle : ⨆ i, A i ≤ N := iSup_le fun i v hv =>
    ⟨hX i hv, fun q hq => h i (Subgroup.commutator_mem_commutator hv hq)⟩
  rw [Subgroup.commutator_le]
  intro v hv q hq
  exact (hle hv).2 q hq

omit [Finite G] in
theorem normalizer_inf_centralizer {X Y : Subgroup G} (hn : X ≤ Subgroup.normalizer (Y : Set G)) :
    X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ X, ∀ x ∈ X ⊓ Subgroup.centralizer (Y : Set G),
      g * x * g⁻¹ ∈ X ⊓ Subgroup.centralizer (Y : Set G) := by
    intro g hg x hx
    refine ⟨X.mul_mem (X.mul_mem hg hx.1) (X.inv_mem hg), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : g⁻¹ * y * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hn (X.inv_mem hg)) y).mp hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * y := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact key g hg x hx
  · intro hx
    have := key g⁻¹ (X.inv_mem hg) _ hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem relIndex_centralizer_dvd_six {X Y : Subgroup G}
    (hn : X ≤ Subgroup.normalizer (Y : Set G)) (hY : Nat.card Y = 4) :
    (X ⊓ Subgroup.centralizer (Y : Set G)).relIndex X ∣ 6 := by
  classical
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  let T : Type := {y : ↥Y // y ≠ 1}
  have hmem : ∀ x : ↥X, ∀ y : ↥Y, (x : G) * y * (x : G)⁻¹ ∈ Y := fun x y =>
    (Subgroup.mem_normalizer_iff.mp (hn x.2) y).mp y.2
  let f : ↥X → T → T := fun x y =>
    ⟨⟨(x : G) * (y.1 : G) * (x : G)⁻¹, hmem x y.1⟩, fun h => y.2 (by
      have h1 : (x : G) * (y.1 : G) * (x : G)⁻¹ = 1 := congrArg Subtype.val h
      have : (y.1 : G) = 1 := by
        have h2 := congrArg (fun z => (x : G)⁻¹ * z * (x : G)) h1
        simpa [mul_assoc] using h2
      exact Subtype.ext this)⟩
  have hf1 : ∀ y, f 1 y = y := fun y => Subtype.ext (Subtype.ext (by simp [f]))
  have hfm : ∀ a b y, f (a * b) y = f a (f b y) := fun a b y =>
    Subtype.ext (Subtype.ext (by simp [f, mul_assoc]))
  let φ : ↥X →* Equiv.Perm T :=
    { toFun := fun x =>
        { toFun := f x
          invFun := f x⁻¹
          left_inv := fun y => by rw [← hfm, inv_mul_cancel, hf1]
          right_inv := fun y => by rw [← hfm, mul_inv_cancel, hf1] }
      map_one' := Equiv.ext hf1
      map_mul' := fun a b => Equiv.ext (hfm a b) }
  have hker : φ.ker = (X ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, fun y hy => ?_⟩
      by_cases hy1 : (⟨y, hy⟩ : ↥Y) = 1
      · have : y = 1 := congrArg Subtype.val hy1
        subst this
        simp
      · have := congrArg (fun p : Equiv.Perm T => (p ⟨⟨y, hy⟩, hy1⟩ : T).1.1) h
        simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, f, Equiv.Perm.coe_one,
          id_eq] at this
        have h2 : (x : G) * y * (x : G)⁻¹ = y := this
        calc y * (x : G) = ((x : G) * y * (x : G)⁻¹) * x := by rw [h2]
          _ = x * y := by group
    · rintro ⟨-, h⟩
      refine Equiv.ext fun y => Subtype.ext (Subtype.ext ?_)
      have h2 := h y.1.1 y.1.2
      show (x : G) * y.1.1 * (x : G)⁻¹ = y.1.1
      calc (x : G) * y.1.1 * (x : G)⁻¹ = (y.1.1 * (x : G)) * (x : G)⁻¹ := by rw [h2]
        _ = y.1.1 := by group
  have hT : Nat.card T = 3 := by
    have := Fintype.ofFinite Y
    have : Fintype T := Fintype.ofFinite T
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hY]
  have hdvd := Subgroup.card_subgroup_dvd_card φ.range
  rw [Nat.card_perm, hT] at hdvd
  unfold Subgroup.relIndex
  rw [← hker, Subgroup.index_ker]
  simpa [Nat.factorial] using hdvd

namespace Sit43

variable {α : Geo H M}

theorem inf_Zv_eq_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ x y : Geo H M}
    (hδ : vtype δ = true) (hx : x ∈ nbrs δ) (hy : y ∈ nbrs δ) (hxy : x ≠ y) :
    Zv x ⊓ Zv y = Yv δ := by
  obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ hx
  rw [Yv_eq_of_sit29 h29]
  exact h29.inf_eq_R hx hy hxy

theorem card_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ : Geo H M}
    (hδ : vtype δ = true) : Nat.card (Yv δ) = 4 := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ hl
  rw [Yv_eq_of_sit29 h29]
  exact h29.card_R_eq

theorem stab_le_normalizer_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ : Geo H M} (hδ : vtype δ = true) : stab δ ≤ Subgroup.normalizer (Yv δ : Set G) := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ hl
  rw [Yv_eq_of_sit29 h29]
  exact h29.R_normal

theorem Yv_eq_comm_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    Yv δ = ⁅⁅Zv l, stab l ⊓ stab δ⁆, stab l ⊓ stab δ⁆ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have hS := sylow_stab_inf_left hA (nbrs_symm hl)
  refine eq_comm_comm_of_inv (quot_stab_five hA hlv) hS (hs.of_vtype_false hlv).orth _
    (Yv_le_Zv hl) ?_ (hs.card_Yv hA h26 hδ)
  intro g hg
  exact (inf_le_right.trans (hs.stab_le_normalizer_Yv hA h26 hδ)) hg

theorem comm_Qv_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ⁅Zv l, Qv δ⁆ = ⁅Zv l, stab l ⊓ stab δ⁆ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have h8 := hs.sup_Qv_edge hA h26 hlv (nbrs_symm hl)
  rw [← h8]
  have h1 := commutator_sup_eq_of_centralizes (Z := Zv l) (C := Qv l) (T := Qv δ)
    (fun c hc z hz => ((Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l hc) z hz)).symm)
    ((Qv_le_stab_of_mem_nbrs hA hl).trans (le_normalizer_pCoreOf 2 (stab l)))
    ((Qv_le_stab_of_mem_nbrs hA hl).trans (stab_le_normalizer_Zv hA l))
  rw [h1]

theorem card_comm_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    Nat.card ↥⁅Zv l, Qv δ⁆ = 8 := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  rw [hs.comm_Qv_eq hA h26 hδ hl]
  exact card_comm_S (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth

theorem Qv_le_centralizer_Yv (hA : F53Amalgam H M S) {δ l : Geo H M} (hl : l ∈ nbrs δ) :
    Qv l ≤ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) :=
  le_inf (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hl))
    ((Qv_le_centralizer_Zv hA l).trans (Subgroup.centralizer_le (Yv_le_Zv hl)))

theorem centralizer_sup_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)) ⊔ Qv δ = stab δ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  set K := stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) with hK
  have hKn : stab δ ≤ Subgroup.normalizer (K : Set G) :=
    normalizer_inf_centralizer (hs.stab_le_normalizer_Yv hA h26 hδ)
  have hKQ : ¬ K ≤ pCoreOf 2 (stab δ) := fun h =>
    not_Qv_le_Qv_nbr hA h26 hs (δ := l) (l := δ) hlv (nbrs_symm hl)
      ((Qv_le_centralizer_Yv hA hl).trans h)
  have hup := sup_sylow_eq_of_normal_not_le (Or.inl rfl) (quot_stab_three hA hδ)
    (sylow_stab_inf_left hA hl) inf_le_left hKn hKQ
  apply le_antisymm (sup_le inf_le_left (pCoreOf_le 2 _))
  intro x hx
  have h1 := hup hx
  have h2 : K ⊔ (stab δ ⊓ stab l) ≤ K ⊔ Qv δ := by
    refine sup_le le_sup_left ?_
    rw [inf_comm, ← hs.sup_Qv_edge hA h26 hlv (nbrs_symm hl)]
    exact sup_le (le_sup_of_le_left (Qv_le_centralizer_Yv hA hl)) le_sup_right
  exact h2 h1

theorem not_Qv_le_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ¬ Qv δ ≤ Subgroup.centralizer (Yv δ : Set G) := by
  intro h
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have hE : stab l ⊓ stab δ ≤ Subgroup.centralizer (Yv δ : Set G) := by
    rw [← hs.sup_Qv_edge hA h26 hlv (nbrs_symm hl)]
    exact sup_le ((Qv_le_centralizer_Yv hA hl).trans inf_le_right) h
  have h6 := relIndex_centralizer_Y (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth
  rw [← hs.Yv_eq_comm_comm hA h26 hδ hl, inf_eq_left.mpr hE, Subgroup.relIndex_self] at h6
  omega

theorem relIndex_centralizer_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).relIndex (stab δ) = 2 ∧
      (Qst δ).relIndex (Qv δ) = 2 := by
  set K := stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) with hK
  have hn := hs.stab_le_normalizer_Yv hA h26 hδ
  have hKn : stab δ ≤ Subgroup.normalizer (K : Set G) := normalizer_inf_centralizer hn
  have h1 : K.relIndex (Qv δ ⊔ K) = K.relIndex (Qv δ) :=
    relIndex_sup_of_le_normalizer ((pCoreOf_le 2 _).trans hKn)
  rw [sup_comm, hs.centralizer_sup_Qv hA h26 hδ hl] at h1
  have hQst : Qst δ = K ⊓ Qv δ := by
    ext x
    simp only [Qst, hK, Subgroup.mem_inf]
    constructor
    · rintro ⟨hq, hc⟩
      exact ⟨⟨pCoreOf_le 2 _ hq, hc⟩, hq⟩
    · rintro ⟨⟨-, hc⟩, hq⟩
      exact ⟨hq, hc⟩
  have h2 : (Qst δ).relIndex (Qv δ) = K.relIndex (stab δ) := by
    rw [h1, hQst, Subgroup.inf_relIndex_right]
  have h3 := relIndex_centralizer_dvd_six hn (hs.card_Yv hA h26 hδ)
  obtain ⟨n, hn2⟩ := (pCoreOf_isPGroup (r := 2) (stab δ)).exists_card_eq
  have h4 : (Qst δ).relIndex (Qv δ) ∣ 2 ^ n := by
    have := Subgroup.relIndex_dvd_card (Qst δ) (Qv δ)
    exact hn2 ▸ this
  obtain ⟨i, hi, hi2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  have h5 : (Qst δ).relIndex (Qv δ) ≠ 1 := by
    intro h
    exact hs.not_Qv_le_centralizer hA h26 hδ hl
      (fun x hx => (Subgroup.relIndex_eq_one.mp h hx).2)
  rw [← h2] at h3
  have hi1 : i = 1 := by
    rcases i with _ | _ | i
    · exact absurd (by simpa using hi2) h5
    · rfl
    · exfalso
      rw [hi2] at h3
      have : 4 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega : 2 ≤ i + 2)).trans h3
      omega
  rw [hi1] at hi2
  exact ⟨h2 ▸ hi2, hi2⟩

omit [Finite G] in
theorem Qst_eq_inf (δ : Geo H M) :
    Qst δ = (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)) ⊓ Qv δ := by
  ext x
  simp only [Qst, Subgroup.mem_inf]
  constructor
  · rintro ⟨hq, hc⟩
    exact ⟨⟨pCoreOf_le 2 _ hq, hc⟩, hq⟩
  · rintro ⟨⟨-, hc⟩, hq⟩
    exact ⟨hq, hc⟩

theorem Qv_inf_Qv_le_Qst (hA : F53Amalgam H M S) {δ l : Geo H M} (hl : l ∈ nbrs δ) :
    Qv l ⊓ Qv δ ≤ Qst δ := fun _ hx =>
  ⟨hx.2, (Qv_le_centralizer_Yv hA hl hx.1).2⟩

theorem commutator_Qv_centralizer_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) {δ : Geo H M} (hδ : vtype δ = true) :
    ⁅Qv δ, stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)⁆ ≤ Qst δ := by
  have hKn := normalizer_inf_centralizer (hs.stab_le_normalizer_Yv hA h26 hδ)
  have hQn : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) := le_normalizer_pCoreOf 2 _
  rw [Qst_eq_inf, Subgroup.commutator_le]
  intro q hq k hk
  have hqs : q ∈ stab δ := pCoreOf_le 2 _ hq
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : q * k * q⁻¹ ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hKn hqs) k).mp hk
    have : ⁅q, k⁆ = (q * k * q⁻¹) * k⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hk)
  · have h1 : k * q⁻¹ * k⁻¹ ∈ Qv δ :=
      (Subgroup.mem_normalizer_iff.mp (hQn hk.1) q⁻¹).mp ((Qv δ).inv_mem hq)
    have : ⁅q, k⁆ = q * (k * q⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact (Qv δ).mul_mem hq h1

theorem Qv_sup_Qst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    Qv l ⊔ Qst δ = (stab l ⊓ stab δ) ⊓ Subgroup.centralizer (Yv δ : Set G) := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have h8 := hs.sup_Qv_edge hA h26 hlv (nbrs_symm hl)
  have hQlC := Qv_le_centralizer_Yv hA hl
  have hQδl : Qv δ ≤ stab l := Qv_le_stab_of_mem_nbrs hA hl
  apply le_antisymm
  · refine sup_le (le_inf (le_inf (pCoreOf_le 2 _) (hQlC.trans inf_le_left))
      (hQlC.trans inf_le_right))
      (le_inf (le_inf (((inf_le_left : Qst δ ≤ Qv δ).trans hQδl)) ?_) inf_le_right)
    exact (inf_le_left : Qst δ ≤ Qv δ).trans (pCoreOf_le 2 _)
  · rintro x ⟨hxE, hxC⟩
    rw [← h8] at hxE
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (hQδl.trans (le_normalizer_pCoreOf 2 (stab l)))).mp hxE
    have hbC : b ∈ Subgroup.centralizer (Yv δ : Set G) := by
      have h1 : a⁻¹ * (a * b) ∈ Subgroup.centralizer (Yv δ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQlC ha).2) hxC
      simpa using h1
    exact Subgroup.mul_mem_sup ha ⟨hb, hbC⟩

theorem relIndex_edge_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ((stab l ⊓ stab δ) ⊓ Subgroup.centralizer (Yv δ : Set G)).relIndex (stab l ⊓ stab δ) = 2 := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have h6 := relIndex_centralizer_Y (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth
  rwa [← hs.Yv_eq_comm_comm hA h26 hδ hl] at h6

theorem comm_Zv_Qst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ⁅Zv l, Qst δ⁆ = Yv δ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have hQδl : Qv δ ≤ stab l := Qv_le_stab_of_mem_nbrs hA hl
  have hQstl : Qst δ ≤ stab l := (inf_le_left : Qst δ ≤ Qv δ).trans hQδl
  have h1 := commutator_sup_eq_of_centralizes (Z := Zv l) (C := Qv l) (T := Qst δ)
    (fun c hc z hz => ((Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l hc) z hz)).symm)
    (hQstl.trans (le_normalizer_pCoreOf 2 (stab l))) (hQstl.trans (stab_le_normalizer_Zv hA l))
  rw [← h1, hs.Qv_sup_Qst hA h26 hδ hl]
  have hY := hs.Yv_eq_comm_comm hA h26 hδ hl
  rw [hY]
  exact comm_centralizer_Y (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth

theorem comm_Vn_Qst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ⁅Vn δ, Qst δ⁆ = Yv δ := by
  apply le_antisymm
  · unfold Vn
    rw [iSup_subtype']
    refine commutator_iSup_le (X := stab δ) (fun i => ?_)
      (hs.stab_le_normalizer_Yv hA h26 hδ) (fun i => ?_)
    · exact (Zv_le_Qv hA i.1).trans (Qv_le_stab_of_mem_nbrs hA (nbrs_symm i.2))
    · exact (hs.comm_Zv_Qst hA h26 hδ i.2).le
  · rw [← hs.comm_Zv_Qst hA h26 hδ hl]
    exact Subgroup.commutator_mono
      (le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs δ) => Zv m) l hl le_rfl) le_rfl

theorem le_Yv_of_normalizes (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {U : Subgroup G} (hU : U ≤ Zv l)
    {g : G} (hg : g ∈ stab δ) (hmov : (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l ≠ l)
    (hgU : conjSub g U = U) : U ≤ Yv δ := by
  have hgl : (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l ∈ nbrs δ := by
    have := (smul_mem_nbrs_iff (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) (l := δ) (δ := l)).mpr hl
    rwa [smul_eq_of_mem_stab (show ((⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) : G) ∈ stab δ from hg)] at this
  have h1 : U ≤ Zv ((⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l) := by
    rw [← S29.Sit29.Zv_conj (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) l, ← hgU]
    exact conjSub_mono g hU
  rw [← hs.inf_Zv_eq_Yv hA h26 hδ hl hgl (Ne.symm hmov)]
  exact le_inf hU h1

theorem four_le_relIndex (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {U : Subgroup G} (hU : U ≤ Zv l)
    (hUY : U ≤ Yv δ) : 4 ≤ U.relIndex (Zv l) := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have h1 := Subgroup.relIndex_mul_card U (Zv l)
  rw [inf_eq_left.mpr hU, hs.card_Zv_false hlv] at h1
  have hc : Nat.card U ≤ 4 := hs.card_Yv hA h26 hδ ▸ Subgroup.card_le_of_le hUY
  have hpos : 0 < Nat.card U := Nat.card_pos
  interval_cases hcU : Nat.card U <;> omega

theorem S14 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l₁ l₂ : Geo H M} (hδ : vtype δ = true) (h1 : l₁ ∈ nbrs δ) (h2 : l₂ ∈ nbrs δ)
    (h12 : l₁ ≠ l₂) {y : G} (hy1 : y ∈ stab l₁) (hyδ : y ∈ stab δ) (hyQ : y ∉ Qv δ)
    {U : Subgroup G} (hU : U ≤ Zv l₂) (hyU : conjSub y U = U) : U ≤ Yv δ := by
  obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ h1
  have hsw := h29.smul_swap (⟨y, stab_le δ hyδ⟩ : ↥(H ⊔ M)) hy1 hyδ hyQ
  refine hs.le_Yv_of_normalizes hA h26 hδ h2 hU hyδ ?_ hyU
  rcases h29.nbrs_eq l₂ h2 with h | h | h
  · exact absurd h.symm h12
  · rw [h, hsw.1]; exact h29.ne₂₃.symm
  · rw [h, hsw.2]; exact h29.ne₂₃

theorem comm_Yv_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) : ⁅Yv δ, Qv δ⁆ = Zv δ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have hS := sylow_stab_inf_left hA (nbrs_symm hl)
  have hq := quot_stab_five hA hlv
  have hZ := (hs.of_vtype_false hlv).orth
  have h8 := hs.sup_Qv_edge hA h26 hlv (nbrs_symm hl)
  have hY := hs.Yv_eq_comm_comm hA h26 hδ hl
  have h1 := commutator_sup_eq_of_centralizes (Z := Yv δ) (C := Qv l) (T := Qv δ)
    (fun c hc z hz => ((Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l hc) z
      (Yv_le_Zv hl hz))).symm)
    ((Qv_le_stab_of_mem_nbrs hA hl).trans (le_normalizer_pCoreOf 2 (stab l)))
    ((pCoreOf_le 2 (stab δ)).trans (hs.stab_le_normalizer_Yv hA h26 hδ))
  rw [h8] at h1
  rw [← h1, hY, comm_comm_comm_S hq hS hZ]
  exact hs.Zv_inf_centralizer hA h26 hδ hl

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
