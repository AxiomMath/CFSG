module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] {H M S : Subgroup G}

namespace C18

theorem comm_mem_of_odd {Z E N : Subgroup G} {l : G} {m : ℕ} (hm : Odd m) (hlm : l ^ m = 1)
    (hlZ : l ∈ Subgroup.normalizer (Z : Set G)) (hEN : E ≤ N) (hsq : ∀ n ∈ N, n ^ 2 ∈ Z)
    (hNE : ∀ n ∈ N, l * n * l⁻¹ * n⁻¹ ∈ E) (hEZ : ∀ e ∈ E, l * e * l⁻¹ * e⁻¹ ∈ Z) :
    ∀ n ∈ N, l * n * l⁻¹ * n⁻¹ ∈ Z := by
  intro n hn
  have hc := hNE n hn
  have hz := hEZ _ hc
  have hc2 := hsq _ (hEN hc)
  have h2 : l ^ 2 ∈ fixer Z n := by
    rw [pow_two]
    refine (mem_fixer_iff).mpr ⟨Subgroup.mul_mem _ hlZ hlZ, ?_⟩
    have e : l * l * n * (l * l)⁻¹ * n⁻¹ = (l * (l * n * l⁻¹ * n⁻¹) * l⁻¹ *
        (l * n * l⁻¹ * n⁻¹)⁻¹) * ((l * n * l⁻¹ * n⁻¹) * (l * n * l⁻¹ * n⁻¹)) := by
      group
    rw [e, ← pow_two]
    exact Z.mul_mem hz hc2
  obtain ⟨k, hk⟩ := hm
  have hl : l = (l ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = m + 1 by omega, pow_succ, hlm, one_mul]
  have hmem : l ∈ fixer Z n := by
    rw [hl]
    exact Subgroup.pow_mem _ h2 _
  exact ((mem_fixer_iff).mp hmem).2

theorem oTwoRes_comm_mem {X Z E N : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hEN : E ≤ N) (hsq : ∀ n ∈ N, n ^ 2 ∈ Z)
    (hNE : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ E)
    (hEZ : ∀ l ∈ oTwoRes X, ∀ e ∈ E, l * e * l⁻¹ * e⁻¹ ∈ Z) :
    ∀ l ∈ oTwoRes X, ∀ n ∈ N, l * n * l⁻¹ * n⁻¹ ∈ Z := by
  obtain ⟨C, hC, -, -⟩ := exists_centralizer_quotient hXZ hXN
  have hLC : oTwoRes X ≤ C := by
    refine (Subgroup.closure_le C).mpr ?_
    rintro x ⟨hxX, m, hm, hxm⟩
    have hxL : x ∈ oTwoRes X := Subgroup.subset_closure ⟨hxX, m, hm, hxm⟩
    have h1 := comm_mem_of_odd hm hxm (hXZ hxX) hEN hsq (hNE x hxX) (hEZ x hxL)
    refine (hC x).mpr ⟨hxX, fun n hn => ?_⟩
    have e : ⁅n, x⁆ = (x * n * x⁻¹ * n⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Z.inv_mem (h1 n hn)
  intro l hl n hn
  have h1 := ((hC l).mp (hLC hl)).2 n hn
  have e : l * n * l⁻¹ * n⁻¹ = ⁅n, l⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact Z.inv_mem h1

variable [Finite G] {α β : Geo H M}

theorem stab_le_normalizer_of_Lres (hA : F53Amalgam H M S) (hβ : β ∈ nbrs α) {U : Subgroup G}
    (hLU : ∀ l ∈ Lres α, ∀ u ∈ U, l * u * l⁻¹ ∈ U)
    (hTU : ∀ t ∈ stab α ⊓ stab β, ∀ u ∈ U, t * u * t⁻¹ ∈ U) :
    stab α ≤ Subgroup.normalizer (U : Set G) := by
  have hT := sylow_stab_inf_left hA hβ
  refine Sit43.le_normalizer_of_conj_mem fun y hy u hu => ?_
  have hTL : stab α ⊓ stab β ≤ Subgroup.normalizer (Lres α : Set G) :=
    inf_le_left.trans (le_normalizer_oTwoRes (stab α))
  obtain ⟨a, ha, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTL).mp
    (le_oTwoRes_sup_of_isSylowTwoOf hT hy)
  have : y * u * y⁻¹ = a * (t * u * t⁻¹) * a⁻¹ := by rw [e]; group
  rw [this]
  exact hLU a ha _ (hTU t ht u hu)

theorem not_forall_Lres_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) :
    ¬ ∀ l ∈ Lres α, ∀ w ∈ Wn α, l * w * l⁻¹ * w⁻¹ ∈ Zv α := by
  intro hL
  have hVW : Vn β ≤ Wn α := hs.Vn_le_Wn hA h26 hβ
  have hLV : ∀ l ∈ Lres α, ∀ v ∈ Vn β, l * v * l⁻¹ ∈ Vn β := by
    intro l hl v hv
    have e : l * v * l⁻¹ = (l * v * l⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact (Vn β).mul_mem (Sit43.Zv_le_Vn hβ (hL l hl v (hVW hv))) hv
  have hTV : ∀ t ∈ stab α ⊓ stab β, ∀ v ∈ Vn β, t * v * t⁻¹ ∈ Vn β := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β ht.2) v).mp hv
  have hαV := stab_le_normalizer_of_Lres hA hβ hLV hTV
  have hU : Vn β ≤ stab α ⊓ stab β := le_inf
    ((hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hβ).trans (pCoreOf_le 2 _))
    ((hs.Vn_le_Qv hβ).trans (pCoreOf_le 2 _))
  have hbot := eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj α β from hβ) hU hαV
    (stab_le_normalizer_Vn β)
  exact Zv_ne_bot hA α (le_bot_iff.mp (hbot ▸ Sit43.Zv_le_Vn hβ))

theorem Vn_sup_eq_of_Lres (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {K : Subgroup G} (hKW : K ≤ Wn α)
    (hK : stab α ≤ Subgroup.normalizer (K : Set G))
    (hL : ∀ l ∈ Lres α, ∀ w ∈ Wn α, l * w * l⁻¹ * w⁻¹ ∈ K) : Vn β ⊔ K = Wn α := by
  have hVW : Vn β ≤ Wn α := hs.Vn_le_Wn hA h26 hβ
  have hUW : Vn β ⊔ K ≤ Wn α := sup_le hVW hKW
  refine le_antisymm hUW ?_
  have hLU : ∀ l ∈ Lres α, ∀ u ∈ Vn β ⊔ K, l * u * l⁻¹ ∈ Vn β ⊔ K := by
    intro l hl u hu
    have e : l * u * l⁻¹ = (l * u * l⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact (Vn β ⊔ K).mul_mem ((le_sup_right : K ≤ Vn β ⊔ K) (hL l hl u (hUW hu))) hu
  have hTn : stab α ⊓ stab β ≤ Subgroup.normalizer ((Vn β ⊔ K : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (inf_le_right.trans (stab_le_normalizer_Vn β)) (inf_le_left.trans hK)
  have hTU : ∀ t ∈ stab α ⊓ stab β, ∀ u ∈ Vn β ⊔ K, t * u * t⁻¹ ∈ Vn β ⊔ K := fun t ht u hu =>
    (Subgroup.mem_normalizer_iff.mp (hTn ht) u).mp hu
  have hαU := stab_le_normalizer_of_Lres hA hβ hLU hTU
  rw [hs.Wn_eq_iSup_conj hA h26 hs.vα hβ]
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hαU hg) y).mp ((le_sup_left : Vn β ≤ Vn β ⊔ K) hy)

theorem exists_Estar (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) :
    ∃ E : Subgroup G, E ≤ Wn α ∧ Zv α ≤ E ∧ stab α ≤ Subgroup.normalizer (E : Set G) ∧
      (∀ l ∈ Lres α, ∀ e ∈ E, l * e * l⁻¹ * e⁻¹ ∈ Zv α) ∧
      ∀ w ∈ Wn α, (∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E) → w ∈ E := by
  have hW := hs.w17Hyp hA h26 hb
  have hZn := stab_le_normalizer_Zv hA α
  have hZ0 : ∀ l ∈ Lres α, ∀ e ∈ Zv α, l * e * l⁻¹ * e⁻¹ ∈ Zv α := fun l hl e he =>
    (Zv α).mul_mem ((Subgroup.mem_normalizer_iff.mp (hZn (oTwoRes_le _ hl)) e).mp he)
      ((Zv α).inv_mem he)
  obtain ⟨E, hE⟩ := (Set.toFinite {E : Subgroup G | E ≤ Wn α ∧ Zv α ≤ E ∧
      stab α ≤ Subgroup.normalizer (E : Set G) ∧
      ∀ l ∈ Lres α, ∀ e ∈ E, l * e * l⁻¹ * e⁻¹ ∈ Zv α}).exists_maximal
    ⟨Zv α, hs.Zv_le_Wn hA h26, le_rfl, hZn, hZ0⟩
  obtain ⟨hEW, hZE, hEn, hEL⟩ := hE.1
  refine ⟨E, hEW, hZE, hEn, hEL, fun w hw hwE => ?_⟩
  have hE'W : E ⊔ Subgroup.zpowers w ≤ Wn α := sup_le hEW (Subgroup.zpowers_le.mpr hw)
  have hE'n : stab α ≤ Subgroup.normalizer ((E ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := by
    refine Sit43.le_normalizer_of_conj_mem fun g hg y hy => ?_
    have hmap : (E ⊔ Subgroup.zpowers w).map (MulAut.conj g).toMonoidHom ≤
        E ⊔ Subgroup.zpowers w := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ ?_
      · rintro _ ⟨e, he, rfl⟩
        exact (le_sup_left : E ≤ E ⊔ Subgroup.zpowers w)
          ((Subgroup.mem_normalizer_iff.mp (hEn hg) e).mp he)
      · rw [Subgroup.zpowers_le]
        have e : (MulAut.conj g).toMonoidHom w = (g * w * g⁻¹ * w⁻¹) * w := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
        rw [e]
        exact (E ⊔ Subgroup.zpowers w).mul_mem
          ((le_sup_left : E ≤ E ⊔ Subgroup.zpowers w) (hwE g hg))
          ((le_sup_right : Subgroup.zpowers w ≤ E ⊔ Subgroup.zpowers w)
            (Subgroup.mem_zpowers w))
    exact hmap ⟨y, hy, rfl⟩
  have hE'E : E ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (E : Set G) :=
    (hE'W.trans hW.Wn_le_stab).trans hEn
  have hfix : E ⊔ Subgroup.zpowers w ≤ fixSecIn (stab α) E (E ⊔ Subgroup.zpowers w) := by
    refine sup_le (fun e he => ?_) ?_
    · refine (mem_fixSecIn_iff hE'E).mpr ⟨(le_sup_left : E ≤ E ⊔ Subgroup.zpowers w) he,
        fun a ha => ?_⟩
      exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEn ha) e).mp he) (E.inv_mem he)
    · rw [Subgroup.zpowers_le]
      exact (mem_fixSecIn_iff hE'E).mpr
        ⟨(le_sup_right : Subgroup.zpowers w ≤ E ⊔ Subgroup.zpowers w) (Subgroup.mem_zpowers w),
          hwE⟩
  have hE'L : ∀ l ∈ Lres α, ∀ n ∈ E ⊔ Subgroup.zpowers w, l * n * l⁻¹ * n⁻¹ ∈ Zv α :=
    oTwoRes_comm_mem hZn hE'n le_sup_left (fun n hn => hW.sq_mem n (hE'W hn))
      (fun a ha n hn => ((mem_fixSecIn_iff hE'E).mp (hfix hn)).2 a ha) hEL
  have hle := hE.2 ⟨hE'W, hZE.trans le_sup_left, hE'n, hE'L⟩
    (le_sup_left : E ≤ E ⊔ Subgroup.zpowers w)
  exact hle ((le_sup_right : Subgroup.zpowers w ≤ E ⊔ Subgroup.zpowers w)
    (Subgroup.mem_zpowers w))

omit [Finite G] in
theorem isNormalIn_Wn (α : Geo H M) : IsNormalIn (stab α) (Wn α) (Wn α) :=
  ⟨le_rfl, fun _ hg x hx => (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hg) x).mp hx⟩

omit [Finite G] in
theorem isNormalIn_of_le {E : Subgroup G} (hEW : E ≤ Wn α)
    (hEn : stab α ≤ Subgroup.normalizer (E : Set G)) : IsNormalIn (stab α) (Wn α) E :=
  ⟨hEW, fun _ hg x hx => (Subgroup.mem_normalizer_iff.mp (hEn hg) x).mp hx⟩

theorem exists_chiefStep {E : Subgroup G} (hEW : E < Wn α)
    (hEn : stab α ≤ Subgroup.normalizer (E : Set G)) :
    ∃ F : Subgroup G, IsChiefStep (stab α) (Wn α) E F := by
  obtain ⟨F, hF⟩ := (Set.toFinite {F : Subgroup G | IsNormalIn (stab α) (Wn α) F ∧
    E < F}).exists_minimal ⟨Wn α, isNormalIn_Wn α, hEW⟩
  refine ⟨F, hF.1.1, isNormalIn_of_le hEW.le hEn, hF.1.2, fun K hK hEK hKF => ?_⟩
  by_cases hKE : K = E
  · exact Or.inl hKE
  · exact Or.inr (le_antisymm hKF (hF.2 ⟨hK, lt_of_le_of_ne hEK (Ne.symm hKE)⟩ hKF))

theorem Lres_comm_mem (hA : F53Amalgam H M S) (hs : Sit43 α) (hβ : β ∈ nbrs α)
    {F : Subgroup G} (hFn : stab α ≤ Subgroup.normalizer (F : Set G)) {x : G}
    (hx : x ∈ stab α) (hxQ : x ∉ Qv α) (hxF : ∀ w ∈ Wn α, x * w * x⁻¹ * w⁻¹ ∈ F) :
    ∀ l ∈ Lres α, ∀ w ∈ Wn α, l * w * l⁻¹ * w⁻¹ ∈ F := by
  obtain ⟨C, hC, hCX, hCn⟩ := exists_centralizer_quotient (X := stab α) (N := Wn α) (Z := F)
    hFn (stab_le_normalizer_Wn α)
  have hxC : x ∈ C := (hC x).mpr ⟨hx, fun w hw => by
    have e : ⁅w, x⁆ = (x * w * x⁻¹ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact F.inv_mem (hxF w hw)⟩
  have hCQ : ¬ C ≤ pCoreOf 2 (stab α) := fun h => hxQ (h hxC)
  have hT := sylow_stab_inf_left hA hβ
  have hup := sup_sylow_eq_of_normal_not_le (Or.inr rfl) (quot_stab_five hA hs.vα) hT hCX hCn hCQ
  have hTn : stab α ⊓ stab β ≤ Subgroup.normalizer (C : Set G) := inf_le_left.trans hCn
  have hL : Lres α ≤ C := oTwoRes_le_of_cover (X := stab α) (C := C) (Q := stab α ⊓ stab β) hCn
    hT.2.1 hT.1 (fun y hy => by
      obtain ⟨c, hc, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTn).mp (hup hy)
      exact ⟨c, hc, t, ht, e⟩)
  intro l hl w hw
  have h1 := F.inv_mem (((hC l).mp (hL hl)).2 w hw)
  have e : ⁅w, l⁆⁻¹ = l * w * l⁻¹ * w⁻¹ := by simp only [commutatorElement_def]; group
  rwa [e] at h1

theorem card_Vn_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) {x : G} (hx : x ∈ stab α) (hxQ : x ∉ Qv α)
    (hxt : IsTransvec 1 x (Zv α) (Wn α)) (hβ : β ∈ nbrs α) : Nat.card (Vn β) = 2 ^ 6 := by
  have hW := hs.w17Hyp hA h26 hb
  have hZn := stab_le_normalizer_Zv hA α
  have hWn := stab_le_normalizer_Wn α
  obtain ⟨E, hEW, hZE, hEn, hEL, hC⟩ := exists_Estar hA h26 hs hb
  have hEW' : E < Wn α := by
    refine lt_of_le_of_ne hEW fun h => not_forall_Lres_comm hA h26 hs (by omega) hβ ?_
    intro l hl w hw
    exact hEL l hl w (h ▸ hw)
  obtain ⟨F, hstep⟩ := exists_chiefStep hEW' hEn
  have hFW : F ≤ Wn α := hstep.1.1
  have hEF : E < F := hstep.2.2.1
  have hFn : stab α ≤ Subgroup.normalizer (F : Set G) :=
    Sit43.le_normalizer_of_conj_mem hstep.1.2
  have hnc : ¬ IsCentralStep (stab α) E F := fun hc =>
    (lt_irrefl F) (lt_of_le_of_lt (fun y hy => hC y (hFW hy) fun g hg => hc g hg y hy) hEF)
  have hcs : cSecIn (stab α) E F = Qv α := by
    rcases chief_central_or_nat_or_orth (quot_stab_five hA hs.vα) hW.Wn_le_Qv hstep with
      h | ⟨h, -⟩
    · exact absurd h hnc
    · exact h
  have hWst : Wn α ≤ stab α := hW.Wn_le_stab
  have hWZ : Wn α ≤ Subgroup.normalizer (Zv α : Set G) := hWst.trans hZn
  have hWE : Wn α ≤ Subgroup.normalizer (E : Set G) := hWst.trans hEn
  have hWF : Wn α ≤ Subgroup.normalizer (F : Set G) := hWst.trans hFn
  have h1 := secIdx_mul_le (x := x) hZE hEW hWZ hWE (hZn hx) (hEn hx)
  have h2 := secIdx_mul_le (x := x) hEF.le hFW hWE hWF (hEn hx) (hFn hx)
  have hEFne : secIdx (Subgroup.zpowers x) E F ≠ 1 := by
    intro h
    have h' := (secIdx_eq_one_iff (hFW.trans hWE) (hEn hx)).mp h
    apply hxQ
    rw [← hcs]
    exact (mem_cSecIn_iff hEn).mpr ⟨hx, h'⟩
  have hp1 := secIdx_pos (Subgroup.zpowers x) (Zv α) E
  have hp2 := secIdx_pos (Subgroup.zpowers x) E F
  have hp3 := secIdx_pos (Subgroup.zpowers x) F (Wn α)
  have hle2 : secIdx (Subgroup.zpowers x) (Zv α) (Wn α) ≤ 2 := hxt.2
  have hFW1 : secIdx (Subgroup.zpowers x) F (Wn α) = 1 := by
    have h3 : secIdx (Subgroup.zpowers x) E F * secIdx (Subgroup.zpowers x) F (Wn α) ≤ 2 :=
      h2.trans ((Nat.le_mul_of_pos_left _ hp1).trans (h1.trans hle2))
    by_contra hne
    have h4 : 2 ≤ secIdx (Subgroup.zpowers x) E F := by omega
    have h5 : 2 ≤ secIdx (Subgroup.zpowers x) F (Wn α) := by omega
    nlinarith
  have hxF := (secIdx_eq_one_iff hWF (hFn hx)).mp hFW1
  have hL := Lres_comm_mem hA hs hβ hFn hx hxQ hxF
  have hVF := Vn_sup_eq_of_Lres hA h26 hs hβ hFW hFn hL
  obtain ⟨-, -, hidx, -⟩ := hs.S17' hA h26 hb hβ hEn hFn hZE hEF hFW hstep hnc hC hVF
  have hEL' : ⁅E, Lres α⁆ ≤ Zv α := by
    rw [Subgroup.commutator_le]
    intro e he l hl
    have e1 : ⁅e, l⁆ = (l * e * l⁻¹ * e⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e1]
    exact (Zv α).inv_mem (hEL l hl e he)
  have hVE := hs.S13' hA h26 hEn hZE hEL' hβ
  have hVEn : Vn β ≤ Subgroup.normalizer (E : Set G) := (hs.Vn_le_Wn hA h26 hβ).trans hWE
  have hrel : (Zv α).relIndex (Vn β) ≤ 4 := by
    rw [← hVE, inf_comm, Subgroup.inf_relIndex_right, ← relIndex_sup_eq_of_le_normalizer hVEn]
    exact hidx
  have hcard := Subgroup.relIndex_mul_card (Zv α) (Vn β)
  rw [inf_eq_left.mpr (Sit43.Zv_le_Vn hβ), hs.card_Zv_false hs.vα] at hcard
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  rcases hs.card_Vn_cases hA h26 (by omega) hβv with h | h | h
  · exact h
  · rw [h] at hcard; omega
  · rw [h] at hcard; omega

end C18

theorem claim18a [Finite G] (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 4 ≤ bMin H M) (h17 : Claim17 α) {β : Geo H M} (hβ : β ∈ nbrs α) :
    Nat.card (Vn β) = 2 ^ 6 ∧ ⁅Wn α, Qv α⁆ ≤ Zv α := by
  obtain ⟨x, hx, hxQ, hxt⟩ := h17
  have h4 := C18.card_Vn_eq hA h26 hs hb hx hxQ hxt hβ
  exact ⟨h4, hs.comm_Wn_Qv_le hA h26 (by omega) hs.vα hβ h4⟩

end CFSG.Quasithin.F53.Stellmacher.S43.Even
