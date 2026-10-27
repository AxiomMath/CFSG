module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34D
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.SecModDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1
open scoped commutatorElement

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Vn_comm (hG : Glob H M S) (δ : Geo H M) {a b : G} (ha : a ∈ Vn δ) (hb : b ∈ Vn δ) :
    a * b = b * a := by
  have h := isElemAbelian_Vn hG.amalg hG.three_le δ
  exact congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem Vn_sq (hG : Glob H M S) (δ : Geo H M) {a : G} (ha : a ∈ Vn δ) : a * a = 1 := by
  rw [← pow_two]
  exact (isElemAbelian_Vn hG.amalg hG.three_le δ).2 a ha

omit [Finite G] in
theorem stab_le_normalizer_Cb (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Cb δ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp
    (normalizer_le_normalizer_centralizer _ (le_normalizer_oTwoRes _ hg)) x
  constructor
  · intro hx
    exact ⟨h1.mp hx.1, h2.mp hx.2⟩
  · intro hx
    exact ⟨h1.mpr hx.1, h2.mpr hx.2⟩

theorem comm_mem_Cb (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) {q x : G}
    (hq : q ∈ Qv δ) (hx : x ∈ Vn δ) : q * x * q⁻¹ * x⁻¹ ∈ Cb δ := by
  have h1 : ⁅x, q⁆ ∈ ⁅Vn δ, Qv δ⁆ := Subgroup.commutator_mem_commutator hx hq
  have h2 := EmptyFaithful.Stellmacher.OrdinaryProofs.commutator_Vn_Qv_le hG.amalg hδ
    (hG.central δ hδ) h1
  have h3 := Zv_le_Cb hG hδ h2
  have h4 := (Cb δ).inv_mem h3
  have : q * x * q⁻¹ * x⁻¹ = ⁅x, q⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [this]

theorem mem_Cb_of_comm (hG : Glob H M S) (δ : Geo H M) {x : G} (hx : x ∈ Vn δ)
    (h : ∀ a ∈ stab δ, a * x * a⁻¹ * x⁻¹ ∈ Cb δ) : x ∈ Cb δ := by
  refine ⟨hx, ?_⟩
  have hle : oTwoRes (stab δ) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro l ⟨hl, m, hm, hlm⟩
    have hl' : l ∈ oTwoRes (stab δ) := Subgroup.subset_closure ⟨hl, m, hm, hlm⟩
    have hy : l * x * l⁻¹ * x⁻¹ ∈ Cb δ := h l hl
    have hyV : l * x * l⁻¹ * x⁻¹ ∈ Vn δ := Cb_le_Vn δ hy
    have hly : l * (l * x * l⁻¹ * x⁻¹) = (l * x * l⁻¹ * x⁻¹) * l :=
      Subgroup.mem_centralizer_iff.mp hy.2 l hl'
    set y := l * x * l⁻¹ * x⁻¹ with hydef
    have hlx : l * x * l⁻¹ = y * x := by rw [hydef]; group
    have hly' : l * y * l⁻¹ = y := by
      rw [hly]; group
    have key : ∀ k : ℕ, l ^ k * x * (l ^ k)⁻¹ = y ^ k * x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc l ^ (k + 1) * x * (l ^ (k + 1))⁻¹
            = l * (l ^ k * x * (l ^ k)⁻¹) * l⁻¹ := by rw [pow_succ']; group
          _ = l * (y ^ k * x) * l⁻¹ := by rw [ih]
          _ = (l * y * l⁻¹) ^ k * (l * x * l⁻¹) := by
              rw [conj_pow]; group
          _ = y ^ (k + 1) * x := by rw [hly', hlx, pow_succ]; group
    have h1 := key m
    rw [hlm] at h1
    have h2 : y ^ m = 1 := by
      have : y ^ m * x = 1 * x := by rw [← h1]; group
      simpa using this
    obtain ⟨j, rfl⟩ := hm
    have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact Vn_sq hG δ hyV
    have : y = 1 := by
      have e : y ^ (2 * j + 1) = (y ^ 2) ^ j * y := by rw [pow_succ, pow_mul]
      rw [e, hy2, one_pow, one_mul] at h2
      exact h2
    rw [this] at hlx
    show l ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : l * x = x * l := by
      have := hlx
      simp only [one_mul] at this
      calc l * x = (l * x * l⁻¹) * l := by group
        _ = x * l := by rw [this]
    exact this
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hl)

theorem fixSecIn_Cb (hG : Glob H M S) (δ : Geo H M) :
    fixSecIn (stab δ) (Cb δ) (Vn δ) = Cb δ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hxa⟩
    exact mem_Cb_of_comm hG δ hx hxa
  · intro x hx
    refine Subgroup.subset_closure ⟨Cb_le_Vn δ hx, fun a ha => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Cb δ ha) x).mp hx
    exact (Cb δ).mul_mem h1 ((Cb δ).inv_mem hx)

theorem isSec (hG : Glob H M S) (δ : Geo H M) : IsSec (stab δ) (Cb δ) (Vn δ) where
  le := Cb_le_Vn δ
  normN := stab_le_normalizer_Vn δ
  normL := stab_le_normalizer_Cb δ
  comm x hx y hy := by
    rw [Vn_comm hG δ hx hy]
    simp
  sq x hx := by
    have h := Vn_sq hG δ hx
    rw [pow_two, h]
    exact (Cb δ).one_mem

theorem pCoreOf_stab_le_cSecIn (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    pCoreOf 2 (stab δ) ≤ cSecIn (stab δ) (Cb δ) (Vn δ) := by
  intro q hq
  exact Subgroup.subset_closure ⟨pCoreOf_le 2 _ hq, fun x hx => comm_mem_Cb hG hδ hq hx⟩

omit [Finite G] in
theorem Zv_le_Vn_nbr {δ μ : Geo H M} (hμ : μ ∈ nbrs δ) : Zv μ ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμ le_rfl

theorem Cb_ne_Vn (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) : Cb δ ≠ Vn δ := by
  intro heq
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hμ' : μ ∈ nbrs δ := hμ
  have hvμ : vtype μ = true := by
    have h := vtype_ne_of_adj hμ
    rw [hδ] at h
    generalize vtype μ = b at h ⊢
    cases b <;> simp_all
  have h1 := Cb_inf_Zv_eq hG hδ hμ'
  rw [heq, inf_eq_right.mpr (Zv_le_Vn_nbr hμ')] at h1
  have hc := EmptyFaithful.Stellmacher.OrdinaryProofs.card_Zv_eq_sq hG.amalg hvμ hμ.symm
    (hG.central δ hδ)
  rw [h1] at hc
  have hpos : 0 < Nat.card (Zv δ) := Nat.card_pos
  have hone : Nat.card (Zv δ) = 1 := by
    have : Nat.card (Zv δ) * 1 = Nat.card (Zv δ) * Nat.card (Zv δ) := by
      rw [mul_one, ← pow_two]; exact hc
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  exact Zv_ne_bot hG.amalg δ (Subgroup.card_eq_one.mp hone)

theorem Zv_nbr_le_fixSecIn (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) : Zv μ ≤ fixSecIn (stab δ ⊓ stab μ) (Cb δ) (Vn δ) := by
  intro z hz
  refine Subgroup.subset_closure ⟨Zv_le_Vn_nbr hμ hz, fun t ht => ?_⟩
  by_cases htQ : t ∈ Qv μ
  · have h := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hG.amalg μ hz).2 t htQ
    have e : t * z * t⁻¹ * z⁻¹ = 1 := by rw [h]; group
    rw [e]
    exact (Cb δ).one_mem
  · exact Zv_le_Cb hG hδ (EmptyFaithful.Stellmacher.OrdinaryProofs.comm_Zv_into hG.amalg
      hδ hμ (hG.central δ hδ) ⟨ht.2, ht.1⟩ htQ z hz)

theorem gen_Vn (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ)
    (U : Subgroup G) (hUV : U ≤ Vn δ) (hn : stab δ ≤ Subgroup.normalizer (U : Set G))
    (hfix : fixSecIn (stab δ ⊓ stab μ) (Cb δ) (Vn δ) ≤ U) : U = Vn δ := by
  refine le_antisymm hUV (iSup₂_le fun κ hκ => ?_)
  obtain ⟨g, hg, hgμ⟩ := stab_transitive_on_nbrs hμ hκ
  intro z hz
  have h1 : z ∈ Zv (g • μ) := by rw [hgμ]; exact hz
  rw [Zv_smul, mem_conjSub] at h1
  have h2 := (Subgroup.mem_normalizer_iff.mp (hn hg) _).mp (hfix (Zv_nbr_le_fixSecIn hG hδ hμ h1))
  simpa [mul_assoc] using h2

theorem secFacts (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    IsSec (stab δ) (Cb δ) (Vn δ) ∧ pCoreOf 2 (stab δ) ≤ cSecIn (stab δ) (Cb δ) (Vn δ) ∧
      fixSecIn (stab δ) (Cb δ) (Vn δ) = Cb δ ∧ Cb δ ≠ Vn δ :=
  ⟨isSec hG δ, pCoreOf_stab_le_cSecIn hG hδ, fixSecIn_Cb hG δ, Cb_ne_Vn hG hδ⟩

theorem good_of_overInv (hG : Glob H M S) (hirr : IrrSecSec) {δ : Geo H M}
    (hδ : vtype δ = false) {g : G} (_hg : g ∈ stab δ) (ho : OverInv δ g) (h8 : rk δ g ≤ 8) :
    Good δ := by
  unfold OverInv OverIn at ho
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hμ' : μ ∈ nbrs δ := hμ
  have hT := sylow_stab_inf_left hG.amalg hμ'
  have := hirr G (stab δ) (Vn δ) (Cb δ) (stab δ ⊓ stab μ) (quot_stab_five hG.amalg hδ)
    (isSec hG δ) (Cb_ne_Vn hG hδ) (pCoreOf_stab_le_cSecIn hG hδ) (fixSecIn_Cb hG δ) hT
    (fun U _ hUV hn hfix => gen_Vn hG hδ hμ' U hUV hn hfix) g ho.1 ho.2.1 ho.2.2 h8
  exact this.symm

theorem good_of_transv (hG : Glob H M S) (h15 : Hss15Sec) {δ : Geo H M}
    (hδ : vtype δ = false) {g : G} (hg : g ∈ stab δ) (h2 : rk δ g = 2) : Good δ :=
  Or.inr (h15 G (stab δ) (Vn δ) (Cb δ) (quot_stab_five hG.amalg hδ) (isSec hG δ)
    (pCoreOf_stab_le_cSecIn hG hδ) (fixSecIn_Cb hG δ) g hg h2)

end S34

end F53.Stellmacher

end CFSG.Quasithin
