module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3NGeo
public import CFSG.Quasithin.EmptyFaithful.SzF53B1Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Alg
public import CFSG.Quasithin.EmptyFaithful.SzF53B3A5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53B3

namespace O1

variable {G : Type} [Group G]

theorem b6 [Finite G] {H M S : Subgroup G} (hB : B3Base H M S) {μ x y : Geo H M}
    (hμ : vtype μ = true) (hxy : x ≠ y) (hx : (graph (H ⊔ M) H M).Adj μ x)
    (hy : (graph (H ⊔ M) H M).Adj μ y) :
    Vn x ⊓ Vn y = Zv μ ∨ Zv μ ≤ ⁅Vn x ⊓ Vn y, Qv μ⁆ := by
  by_cases hle : Zv μ ≤ ⁅Vn x ⊓ Vn y, Qv μ⁆
  · exact Or.inr hle
  left
  have hA := hB.amalgam
  have hxn : x ∈ nbrs μ := hx
  have hyn : y ∈ nbrs μ := hy
  have hxf : vtype x = false := vtype_nbr_of_true hxn hμ
  have hyf : vtype y = false := vtype_nbr_of_true hyn hμ
  have hμx : μ ∈ nbrs x := hx.symm
  have hμy : μ ∈ nbrs y := hy.symm
  have hcen : centerOf (stab μ) = ⊥ := centerOf_eq_bot_of_Zv_central hA hμx (hB.central x hxf)
  have hcz : ∀ z ∈ stab μ, (∀ g ∈ stab μ, g * z * g⁻¹ = z) → z = 1 := by
    intro z hz hc
    have : z ∈ centerOf (stab μ) := by
      refine ⟨hz, ?_⟩
      show z ∈ Subgroup.centralizer (stab μ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [hc g hg]
    rw [hcen] at this
    exact Subgroup.mem_bot.mp this
  set R := Vn x ⊓ Vn y with hR
  set R0 := ⁅R, Qv μ⁆ with hR0
  have hRn : stab μ ≤ Subgroup.normalizer (R : Set G) := vn_inf_normal_of hB hxy.symm hμ hxn hyn
  have hQn : stab μ ≤ Subgroup.normalizer (Qv μ : Set G) := N37.stab_le_normalizer_Qv μ
  have hR0n : stab μ ≤ Subgroup.normalizer (R0 : Set G) := le_normalizer_commutator hRn hQn
  have hQμs : Qv μ ≤ stab μ := N37.Qv_le_stab_self μ
  have hVxQμ : Vn x ≤ Qv μ := vn_le_qv_of_dist hB (N37.dist_le_one_of_adj hx.symm)
  have hVyQμ : Vn y ≤ Qv μ := vn_le_qv_of_dist hB (N37.dist_le_one_of_adj hy.symm)
  have hRQ : R ≤ Qv μ := inf_le_left.trans hVxQμ
  have hQxμ : Qv x ≤ stab μ := Qv_le_stab_of_mem_nbrs hA hμx
  have hQyμ : Qv y ≤ stab μ := Qv_le_stab_of_mem_nbrs hA hμy
  have hR0R : R0 ≤ R := by
    have := commutator_le_inf_of_normalizes (A := R) (B := Qv μ)
      ((hRQ.trans hQμs).trans hQn) (hQμs.trans hRn)
    exact this.trans inf_le_left
  have hZμR : Zv μ ≤ R := le_inf (N37.Zv_le_Vn_of_adj hx.symm) (N37.Zv_le_Vn_of_adj hy.symm)
  have hZR0 : Zv μ ⊓ ⁅R, Qv μ⁆ = ⊥ := by
    have hUn : stab μ ≤ Subgroup.normalizer ((Zv μ ⊓ R0 : Subgroup G) : Set G) :=
      F7.le_normalizer_inf (stab_le_normalizer_Zv hA μ) hR0n
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : Zv μ ⊓ R0 ≤ Zv μ)
    rw [card_zv_true hB hμ] at hdvd
    have hpos : 0 < Nat.card (Zv μ ⊓ R0 : Subgroup G) := Nat.card_pos
    have hle4 : Nat.card (Zv μ ⊓ R0 : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : Nat.card (Zv μ ⊓ R0 : Subgroup G) = 1 ∨ Nat.card (Zv μ ⊓ R0 : Subgroup G) = 2 ∨
        Nat.card (Zv μ ⊓ R0 : Subgroup G) = 4 := by
      interval_cases h : Nat.card (Zv μ ⊓ R0 : Subgroup G)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · omega
      · exact Or.inr (Or.inr rfl)
    rcases hcases with h1 | h2 | h4
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      obtain ⟨z, hzU, hz1, hzu⟩ := exists_gen_of_card_two h2
      have hzs : z ∈ stab μ := (hQμs ((Zv_le_Qv hA μ) hzU.1))
      refine hz1 (hcz z hzs fun g hg => ?_)
      have hgz : g * z * g⁻¹ ∈ Zv μ ⊓ R0 := (Subgroup.mem_normalizer_iff.mp (hUn hg) z).mp hzU
      rcases hzu _ hgz with h | h
      · exfalso
        apply hz1
        have := congrArg (fun w => g⁻¹ * w * g) h
        simpa [mul_assoc] using this
      · exact h
    · exfalso
      apply hle
      have : Zv μ ⊓ R0 = Zv μ :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left : Zv μ ⊓ R0 ≤ Zv μ)
          (by rw [h4, card_zv_true hB hμ])
      rw [← this]
      exact inf_le_right
  have hstep2 : ∀ w : Geo H M, w ∈ nbrs μ → R ≤ Vn w → ⁅R0, Qv w⁆ = ⊥ := by
    intro w hw hRw
    have hwf : vtype w = false := vtype_nbr_of_true hw hμ
    have hwμ : (graph (H ⊔ M) H M).Adj w μ := (show (graph (H ⊔ M) H M).Adj μ w from hw).symm
    have hμw : μ ∈ nbrs w := hwμ
    have hVwQ : Vn w ≤ Qv w :=
      vn_le_qv_of_dist hB (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)
    have hR0Q : R0 ≤ Qv w := (hR0R.trans hRw).trans hVwQ
    have h1 : ⁅R0, Qv w⁆ ≤ R0 := by
      refine (commutator_le_inf_of_normalizes (A := R0) (B := Qv w)
        (hR0Q.trans ((N37.Qv_le_stab_self w).trans (N37.stab_le_normalizer_Qv w)))
        ((Qv_le_stab_of_mem_nbrs hA hμw).trans hR0n)).trans inf_le_left
    have h2 : ⁅R0, Qv w⁆ ≤ Zv μ :=
      ((Subgroup.commutator_mono (hR0R.trans hRw) le_rfl).trans
        (comm_vn_qv_le hB hwf)).trans (zv_le_zv_of_adj hB hwf hwμ)
    exact le_bot_iff.mp ((le_inf h2 h1).trans hZR0.le)
  have hR0x := hstep2 x hxn inf_le_left
  have hR0y := hstep2 y hyn inf_le_right
  have hR0bot : R0 = ⊥ := by
    by_contra hne
    have hP : IsPGroup 2 (Qv μ) := pCoreOf_isPGroup 2 (stab μ)
    obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (inf_centralizer_ne_bot_of_normalized hP (hR0R.trans hRQ) (hQμs.trans hR0n) hne)
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    have hrQ : ∀ q ∈ Qv μ, q * r = r * q := Subgroup.mem_centralizer_iff.mp hr.2
    have hrx : ∀ q ∈ Qv x, q * r = r * q := fun q hq => by
      have h1 : ⁅r, q⁆ ∈ ⁅R0, Qv x⁆ := Subgroup.commutator_mem_commutator hr.1 hq
      rw [hR0x, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hry : ∀ q ∈ Qv y, q * r = r * q := fun q hq => by
      have h1 : ⁅r, q⁆ ∈ ⁅R0, Qv y⁆ := Subgroup.commutator_mem_commutator hr.1 hq
      rw [hR0y, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hCle : stab μ ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [stab_eq_sup_Qv hB hμ hxy hxn hyn]
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hrQ q hq)
      · intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hrx q hq)
      · intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hrQ q hq)
      · intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hry q hq)
    refine hr1' (hcz r (hQμs (hR0R.trans hRQ |> fun h => h hr.1)) fun g hg => ?_)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hCle hg)
    rw [this]
    group
  have hcQR : ∀ r ∈ R, ∀ q ∈ Qv μ, q * r = r * q := fun r hr q hq => by
    have h1 : ⁅r, q⁆ ∈ R0 := Subgroup.commutator_mem_commutator hr hq
    rw [hR0bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have h6 : (Qv μ).relIndex (stab μ) = 6 := by
    obtain ⟨e⟩ := quot_stab_three hA hμ
    have := F53B1.relIndex_pCoreOf_eq_card e
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  have hS2 : ∀ w ∈ nbrs μ, (Qv μ).relIndex (stab μ ⊓ stab w) = 2 := by
    intro w hw
    have h3 : (stab μ ⊓ stab w).relIndex (stab μ) = 3 := index_inf_stab_true hA hμ hw
    have hQS : Qv μ ≤ stab μ ⊓ stab w := le_inf hQμs (Qv_le_stab_of_mem_nbrs hA hw)
    have hmul := Subgroup.relIndex_mul_relIndex (Qv μ) (stab μ ⊓ stab w) (stab μ) hQS inf_le_left
    rw [h3, h6] at hmul
    omega
  have hex : ∀ w ∈ nbrs μ, ∃ s ∈ Qv w, s ∉ Qv μ := by
    intro w hw
    by_contra hcon
    push Not at hcon
    apply not_inf_stab_le_Qv hA hμ hw
    rw [← hB.prod μ w (show (graph (H ⊔ M) H M).Adj μ w from hw) hμ]
    exact sup_le le_rfl hcon
  have hbound : ∀ w ∈ nbrs μ, R ≤ Vn w → ∃ s ∈ Qv w,
      (R ⊓ Subgroup.centralizer ({s} : Set G)).relIndex R ≤ 2 ∧
      ∀ r ∈ R, s * r = r * s → ∀ g ∈ Qv μ ⊔ Qv w, g * r = r * g := by
    intro w hw hRw
    have hwf : vtype w = false := vtype_nbr_of_true hw hμ
    obtain ⟨s, hsw, hsμ⟩ := hex w hw
    have hVwQ : Vn w ≤ Qv w :=
      vn_le_qv_of_dist hB (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)
    refine ⟨s, hsw, ?_, ?_⟩
    · have := relIndex_inf_centralizer_le (R := R) (Z := Zv w) (s := s)
        (fun a ha b hb => mul_comm_of_elemAbelian (isElemAbelian_Zv hA w) ha hb)
        (fun r hr z hz => by
          have h1 := conj_eq_of_central hB hwf
            ((N37.Qv_le_stab_self w) (hVwQ (hRw hr))) hz
          calc r * z = (r * z * r⁻¹) * r := by group
            _ = z * r := by rw [h1])
        (fun r hr => by
          have h1 : ⁅r, s⁆ ∈ ⁅Vn w, Qv w⁆ := Subgroup.commutator_mem_commutator (hRw hr) hsw
          have := comm_vn_qv_le hB hwf h1
          simpa [commutatorElement_def] using this)
      rw [hB.card_two w hwf] at this
      exact this
    · intro r hr hsr g hg
      have hSw : stab μ ⊓ stab w = Qv μ ⊔ Qv w :=
        (hB.prod μ w (show (graph (H ⊔ M) H M).Adj μ w from hw) hμ).symm
      have hQw : ∀ q ∈ Qv w, q * r = r * q := by
        intro q hq
        have hqS : q ∈ stab μ ⊓ stab w := hSw ▸ Subgroup.mem_sup_right hq
        have hsS : s ∈ stab μ ⊓ stab w := hSw ▸ Subgroup.mem_sup_right hsw
        by_cases hqμ : q ∈ Qv μ
        · exact hcQR r hr q hqμ
        · have hqs : q * s⁻¹ ∈ Qv μ :=
            mul_inv_mem_of_relIndex_two (hS2 w hw) hqS hsS hqμ hsμ
          have h1 := hcQR r hr _ hqs
          calc q * r = (q * s⁻¹) * (s * r) := by group
            _ = (q * s⁻¹) * (r * s) := by rw [hsr]
            _ = ((q * s⁻¹) * r) * s := by group
            _ = (r * (q * s⁻¹)) * s := by rw [h1]
            _ = r * q := by group
      have hCle : Qv μ ⊔ Qv w ≤ Subgroup.centralizer ({r} : Set G) := sup_le
        (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hcQR r hr q hq))
        (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hQw q hq))
      exact Subgroup.mem_centralizer_singleton_iff.mp (hCle hg)
  obtain ⟨sx, hsx, hAx, hcx⟩ := hbound x hxn inf_le_left
  obtain ⟨sy, hsy, hAy, hcy⟩ := hbound y hyn inf_le_right
  have hinf : (R ⊓ Subgroup.centralizer ({sx} : Set G)) ⊓
      (R ⊓ Subgroup.centralizer ({sy} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    have hrR : r ∈ R := hr.1.1
    have hrx : sx * r = r * sx := (Subgroup.mem_centralizer_singleton_iff.mp hr.1.2).symm
    have hry : sy * r = r * sy := (Subgroup.mem_centralizer_singleton_iff.mp hr.2.2).symm
    have hall : stab μ ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [stab_eq_sup_Qv hB hμ hxy hxn hyn]
      exact sup_le
        (fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hcx r hrR hrx g hg))
        (fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hcy r hrR hry g hg))
    refine hcz r (hQμs (hRQ hrR)) fun g hg => ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp (hall hg)
    rw [this]
    group
  have hcard : Nat.card R ≤ 4 := by
    have h := Subgroup.relIndex_inf_le (H := R ⊓ Subgroup.centralizer ({sx} : Set G))
      (K := R ⊓ Subgroup.centralizer ({sy} : Set G)) (L := R)
    rw [hinf, Subgroup.relIndex_bot_left] at h
    exact h.trans (Nat.mul_le_mul hAx hAy)
  exact (Subgroup.eq_of_le_of_card_ge hZμR (by rw [card_zv_true hB hμ]; exact hcard)).symm

end O1

end F53B3

end CFSG.Quasithin
