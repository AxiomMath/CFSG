module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s1614e3_ieor_of_card {p n : ℕ} [hp : Fact p.Prime] {W : Type} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1)
    (hcard : Nat.card W = p ^ n) : IsElemAbelianOfRank p n W := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod p) (Additive W) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod p) (Additive W) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive W) _ _ _ hF
  have hfin : Module.finrank (ZMod p) (Additive W) =
      Module.finrank (ZMod p) (Fin n → ZMod p) := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective hp.out.two_le (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod p) (Additive W) (Fin n → ZMod p) _ _ _ hFr _ _ _ _ hF _
      hfin).toAddEquiv⟩

theorem s1614e3_lemmaP_split (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) {p : ℕ}
    (hp : p ∈ D.sig) (hpr : CFSG.Open.pRank p (Mbar D.M ⊥ V hV) ≤ 2) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      IsElemAbelianOfRank p 2 ↥(barSub ⊥ V hV E) ∧
      Nat.card ↥(E ⊓ centralizer (V : Set G)) = p := by
  classical
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hpf : PairFacts D.M ⊥ V := h.pairFacts
  have hMn : D.M ≤ normalizer (V : Set G) := hpf.le_normalizer
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hMn hpf.le_normalizer₀
  have hpp : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hk3 : 3 ≤ CFSG.Open.pRank p D.M := hx.three_le p hp
  obtain ⟨E₀, hE₀el, hE₀card⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank hpp hk3
  let E : Subgroup G := E₀.map D.M.subtype
  have hEM : E ≤ D.M := Subgroup.map_subtype_le E₀
  have hEel : IsElemAbelian p E := hE₀el.map D.M.subtype
  have hEcard : Nat.card E = p ^ 3 := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective, hE₀card]
  have hEst : E ≤ stabTil ⊥ V := hEM.trans hMst
  have hc4 : Nat.card (⊥ : Subgroup G) ≤ 4 := by simp
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  obtain ⟨-, -, -, hY'⟩ := exists_rank_data h115 (Hyp125.hyp11 h127 h) hc4 hp
  have hYker : ∀ Y' : Subgroup ↥D.M, IsElemAbelian p Y' → Y' ≤ (barHom ⊥ V hV hMst).ker →
      Nat.card Y' ≤ p := fun Y' hYel hYk =>
    hY' Y' hYel (by rwa [ker_barHom ⊥ V hV hMn hMst] at hYk)
  have hΛM : barSub ⊥ V hV E ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  have hΛel : IsElemAbelian p (barSub ⊥ V hV E) :=
    (hEel.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  have hE₀E : preBarSub E ⊥ V hV ⊥ ≤ E := inf_le_left
  have hE₀M : preBarSub E ⊥ V hV ⊥ ≤ D.M := hE₀E.trans hEM
  have hC₀card : Nat.card (preBarSub E ⊥ V hV ⊥) ≤ p := by
    have hel : IsElemAbelian p ((preBarSub E ⊥ V hV ⊥).subgroupOf D.M) :=
      (hEel.mono hE₀E).subgroupOf D.M
    have hker : (preBarSub E ⊥ V hV ⊥).subgroupOf D.M ≤ (barHom ⊥ V hV hMst).ker := by
      intro x hx'
      obtain ⟨-, hst, hx1⟩ := (mem_preBarSub E ⊥ V hV ⊥).1 (Subgroup.mem_subgroupOf.1 hx')
      rw [MonoidHom.mem_ker]
      have : barHom ⊥ V hV hMst x = actTil ⊥ V hV ⟨(x : G), hst⟩ := rfl
      rw [this]
      exact Subgroup.mem_bot.1 hx1
    have h3 := hYker _ hel hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀M).toEquiv] at h3
  have hid := s16c7_card_mul_card_preBarSub hV hEst (Q := ⊥) bot_le
  rw [Subgroup.card_bot, mul_one] at hid
  obtain ⟨j, hj⟩ := hΛel.isPGroup.exists_card_eq
  have hjrank : j ≤ CFSG.Open.pRank p (Mbar D.M ⊥ V hV) :=
    CFSG.SectionRank.le_pRank hpp.one_lt hΛM hΛel hj
  have hj2 : j = 2 := by
    have hle1 : p ^ 3 ≤ p ^ (j + 1) := by
      calc p ^ 3 = Nat.card E := hEcard.symm
        _ = Nat.card (preBarSub E ⊥ V hV ⊥) * Nat.card (barSub ⊥ V hV E) := hid
        _ = Nat.card (preBarSub E ⊥ V hV ⊥) * p ^ j := by rw [hj]
        _ ≤ p * p ^ j := Nat.mul_le_mul_right _ hC₀card
        _ = p ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
    have h2j : 2 ≤ j := by
      have := (Nat.pow_le_pow_iff_right hpp.one_lt).1 hle1
      omega
    omega
  have hĒcard : Nat.card (barSub ⊥ V hV E) = p ^ 2 := by
    rw [hj, hj2]
  have hΛrank : IsElemAbelianOfRank p 2 ↥(barSub ⊥ V hV E) :=
    s1614e3_ieor_of_card (fun a b => Subtype.ext (hΛel.comm a.2 b.2))
      (fun a => Subtype.ext (hΛel.2 a a.2)) hĒcard
  have hC₀eq : Nat.card (preBarSub E ⊥ V hV ⊥) = p := by
    have h1 : Nat.card (preBarSub E ⊥ V hV ⊥) * p ^ 2 = p * p ^ 2 := by
      rw [← hĒcard, ← hid, hEcard, hĒcard, pow_succ']
    have h2 : 0 < p ^ 2 := pow_pos hpp.pos 2
    exact Nat.eq_of_mul_eq_mul_right h2 h1
  refine ⟨E, hEM, hEel, hEcard, hΛrank, ?_⟩
  have hpre : preBarSub E ⊥ V hV ⊥ = E ⊓ centralizer (V : Set G) := by
    ext g
    rw [mem_preBarSub, Subgroup.mem_inf]
    constructor
    · rintro ⟨hgE, hgs, hg1⟩
      refine ⟨hgE, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h2 := (actTil_eq_one_iff ⊥ V hV ⟨g, hgs⟩).1 (Subgroup.mem_bot.1 hg1) v hv
      rw [Subgroup.mem_bot] at h2
      calc v * g = (g * v * g⁻¹ * v⁻¹) * (v * g) := by rw [h2, one_mul]
        _ = g * v := by group
    · rintro ⟨hgE, hgC⟩
      refine ⟨hgE, hMst (hEM hgE), ?_⟩
      rw [Subgroup.mem_bot, actTil_eq_one_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      have h2 := Subgroup.mem_centralizer_iff.1 hgC v hv
      rw [← h2]
      group
  rwa [← hpre]

private theorem s1614e3_imgTil_bot_work (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
  ext q
  rw [mem_imgTil]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : x.val = 1 := Subgroup.mem_bot.1 hx
    have hx1' : x = 1 := IntMod.val_injective hx1
    rw [hx1', map_one]
    exact Subgroup.mem_bot.2 rfl
  · intro hq
    rw [Subgroup.mem_bot] at hq
    subst hq
    exact ⟨1, Subgroup.mem_bot.2 rfl, map_one _⟩

theorem s1614e3_false_of_lemmaP (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV)
    {U : Subgroup G} (hU : Min1614 D V U) {p : ℕ} (hp : p ∈ D.sig)
    (hpr : CFSG.Open.pRank p (Mbar D.M ⊥ V hV) ≤ 2)
    (hnorm : ∀ E : Subgroup (MulAut (Vtil ⊥ V hV)), E ≤ Mbar D.M ⊥ V hV →
      IsElemAbelianOfRank p 2 ↥E → ∃ e ∈ E, e ≠ 1 ∧
        ∃ Z : Subgroup (Vtil ⊥ V hV), Z ≠ ⊥ ∧ Z ≤ imgTil ⊥ V hV U ∧
          Z.map e.toMonoidHom = Z) : False := by
  classical
  obtain ⟨E, hEM, hEel, hEcard, hΛrank, hCcard⟩ :=
    s1614e3_lemmaP_split D hx h61 h127 hV hc hp hpr
  have hĒM : barSub ⊥ V hV E ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  obtain ⟨ē, hēĒ, hē1, Z, hZne, hZU, hZmap⟩ := hnorm (barSub ⊥ V hV E) hĒM hΛrank
  obtain ⟨g, hgE, hactil⟩ := (mem_barSub ⊥ V hV E ē).1 hēĒ
  let e : G := (g : G)
  let C : Subgroup G := E ⊓ centralizer (V : Set G)
  let X : Subgroup G := Subgroup.zpowers e ⊔ C
  let R : Subgroup G := preTil ⊥ V hV Z
  have hgeN : e ∈ normalizer (V : Set G) := stabTil_le_normalizer ⊥ V g.2
  have hRV : R ≤ V := preTil_le ⊥ V hV Z
  have hR2 : IsPGroup 2 R := (hV.mono hRV).isPGroup
  have hRne : R ≠ ⊥ := by
    intro hR0
    apply hZne
    have hpre : preTil ⊥ V hV Z = ⊥ := hR0
    calc Z = imgTil ⊥ V hV (preTil ⊥ V hV Z) := (imgTil_preTil ⊥ V hV Z).symm
      _ = imgTil ⊥ V hV ⊥ := by rw [hpre]
      _ = ⊥ := s1614e3_imgTil_bot_work V hV
  have hRU : R ≤ U := by
    intro r hr
    have hrV : r ∈ V := hRV hr
    have hZr : mkTil ⊥ V hV (IntMod.mk hV ⟨r, hrV⟩) ∈ Z :=
      (mem_preTil_iff_of_mem ⊥ V hV Z hrV).1 hr
    have himg : mkTil ⊥ V hV (IntMod.mk hV ⟨r, hrV⟩) ∈ imgTil ⊥ V hV U := hZU hZr
    obtain ⟨x, hxU, hxr⟩ := (mem_imgTil ⊥ V hV U _).1 himg
    have hxr' : x.val = r := by
      have h2 := (mkTil_eq_iff ⊥ V hV x (IntMod.mk hV ⟨r, hrV⟩)).1 hxr
      rw [Subgroup.mem_bot] at h2
      calc x.val = x.val * (IntMod.mk hV ⟨r, hrV⟩).val⁻¹ *
              (IntMod.mk hV ⟨r, hrV⟩).val := by group
        _ = 1 * (IntMod.mk hV ⟨r, hrV⟩).val := by rw [h2]
        _ = (IntMod.mk hV ⟨r, hrV⟩).val := one_mul _
        _ = r := rfl
    rwa [hxr'] at hxU
  have heC : e ∉ C := by
    intro he
    have hcent : e ∈ centralizer (V : Set G) := he.2
    have h1 : actTil ⊥ V hV g = 1 := by
      rw [actTil_eq_one_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      change e * v * e⁻¹ * v⁻¹ = 1
      have h2 : v * e = e * v := Subgroup.mem_centralizer_iff.1 hcent v hv
      rw [← h2]
      group
    rw [hactil] at h1
    exact hē1 h1
  have hCXle : C ≤ X := le_sup_right
  have hCXne : C ≠ X := by
    intro h
    apply heC
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hCXlt : C < X := lt_of_le_of_ne hCXle hCXne
  have hXE : X ≤ E := sup_le (Subgroup.zpowers_le.2 hgE) inf_le_left
  have hXM : X ≤ D.M := hXE.trans hEM
  have hXel : IsElemAbelian p X := hEel.mono hXE
  have hXp : IsPGroup p X := hXel.isPGroup
  have hXc : ¬ IsCyclic X := by
    intro hcyc
    have hpp : p.Prime := (D.sig_prime p hp).1
    haveI : Fintype ↥X := Fintype.ofFinite _
    haveI : IsCyclic ↥X := hcyc
    have hle : Nat.card ↥X ≤ p := by
      have h := IsCyclic.card_pow_eq_one_le (α := ↥X) hpp.pos
      have hall : (Finset.univ.filter fun a : ↥X => a ^ p = 1) = Finset.univ := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact Subtype.ext (hXel.2 a a.2)
      rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card] at h
      exact h
    have hplt : p < Nat.card X := by
      have h1 := Subgroup.card_lt_of_lt hCXlt
      rwa [hCcard] at h1
    omega
  have hkey : ∀ r (hrV : r ∈ V) (herV : e * r * e⁻¹ ∈ V),
      mkTil ⊥ V hV (IntMod.mk hV ⟨e * r * e⁻¹, herV⟩)
        = ē (mkTil ⊥ V hV (IntMod.mk hV ⟨r, hrV⟩)) := by
    intro r hrV herV
    have h1 : actStab ⊥ V hV g (IntMod.mk hV ⟨r, hrV⟩) =
        IntMod.mk hV ⟨e * r * e⁻¹, herV⟩ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl
    calc mkTil ⊥ V hV (IntMod.mk hV ⟨e * r * e⁻¹, herV⟩)
        = mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV ⟨r, hrV⟩)) := by rw [h1]
      _ = actTil ⊥ V hV g (mkTil ⊥ V hV (IntMod.mk hV ⟨r, hrV⟩)) :=
            (actTil_mk ⊥ V hV g _).symm
      _ = ē (mkTil ⊥ V hV (IntMod.mk hV ⟨r, hrV⟩)) := by rw [hactil]
  have hZiff : ∀ z : Vtil ⊥ V hV, z ∈ Z ↔ ē z ∈ Z := by
    intro z
    constructor
    · intro hz
      have hmem : ē z ∈ Z.map ē.toMonoidHom := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
      rwa [hZmap] at hmem
    · intro hz
      have hmem : ē z ∈ Z.map ē.toMonoidHom := by rw [hZmap]; exact hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hmem
      rwa [ē.injective hyz] at hy
  have heN : e ∈ normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have hrV : r ∈ V := hRV hr
      have herV : e * r * e⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hgeN r).1 hrV
      have hZr : mkTil ⊥ V hV (IntMod.mk hV ⟨r, hrV⟩) ∈ Z :=
        (mem_preTil_iff_of_mem ⊥ V hV Z hrV).1 hr
      rw [mem_preTil_iff_of_mem ⊥ V hV Z herV, hkey r hrV herV]
      exact (hZiff _).1 hZr
    · intro hr'
      have herV : e * r * e⁻¹ ∈ V := hRV hr'
      have hrV : r ∈ V := (Subgroup.mem_normalizer_iff.1 hgeN r).2 herV
      have hZr' : mkTil ⊥ V hV (IntMod.mk hV ⟨e * r * e⁻¹, herV⟩) ∈ Z :=
        (mem_preTil_iff_of_mem ⊥ V hV Z herV).1 hr'
      rw [hkey r hrV herV] at hZr'
      rw [mem_preTil_iff_of_mem ⊥ V hV Z hrV]
      exact (hZiff _).2 hZr'
  have hXN : X ≤ normalizer (R : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact heN
    · intro c hc
      exact Subgroup.centralizer_le_normalizer (R : Set G)
        (Subgroup.centralizer_le hRV hc.2)
  have hH : CFSG.Open.IsTwoLocal (normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  have hNM : normalizer (R : Set G) ≤ D.M :=
    le_of_noncyclic_of_isTwoLocal D h61 hp hXM hXp hXc hH hXN
  exact hU.2.1 (le_trans (Subgroup.centralizer_le hRU)
    (le_trans (Subgroup.centralizer_le_normalizer (R : Set G)) hNM))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
