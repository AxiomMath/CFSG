module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Cond
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private theorem s16h_mixed_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

private theorem s16h_mixed_card_preTil_bot {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil ⊥ V hV)) :
    Nat.card ↥(preTil ⊥ V hV S) = Nat.card ↥S := by
  unfold preTil
  rw [Subgroup.card_map_of_injective (f := valHom V hV)
    (K := S.comap (mkTil ⊥ V hV)) (fun x y h => IntMod.val_injective h)]
  rw [← Subgroup.card_map_of_injective (f := mkTil ⊥ V hV)
    (K := S.comap (mkTil ⊥ V hV)) (s16h_mixed_mkTil_bot_injective hV),
    Subgroup.map_comap_eq_self_of_surjective (mkTil_surjective ⊥ V hV) S]

private theorem s16h_mixed_comm_of_mem_cElt_bot {M : Subgroup G} {v m : G}
    (hm : m ∈ F11.CElt M ⊥ v) : m * v = v * m := by
  have h1 : m * v * m⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 hm.2.2
  refine mul_inv_eq_one.mp ?_
  rw [mul_inv_rev]
  simpa only [mul_assoc] using h1

private theorem s16h_mixed_eq_of_ne_one_of_card_le_two {H : Subgroup G}
    (hcard : Nat.card ↥H ≤ 2) {z w : G} (hz : z ∈ H) (hz1 : z ≠ 1) (hw : w ∈ H)
    (hw1 : w ≠ 1) : w = z := by
  by_contra hne
  have hinj : Function.Injective (fun i : Fin 3 =>
      (![⟨1, H.one_mem⟩, ⟨z, hz⟩, ⟨w, hw⟩] : Fin 3 → ↥H) i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
  have h3 : 3 ≤ Nat.card ↥H :=
    calc 3 = Nat.card (Fin 3) := by simp
      _ ≤ Nat.card ↥H := Nat.card_le_card_of_injective _ hinj
  omega

private theorem s16h_mixed_map_conj_le_centralizer {B A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (B : Set G)) (hA : A ≤ Subgroup.centralizer (B : Set G)) :
    A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (B : Set G) := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hp
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro b hb
  have hgb : g * b = b * g := (hg b hb).symm
  have hab : b * a = a * b := (Subgroup.mem_centralizer_iff.1 (hA ha)) b hb
  have h1 : g⁻¹ * b * g = b := by
    calc g⁻¹ * b * g = g⁻¹ * (b * g) := by group
      _ = g⁻¹ * (g * b) := by rw [← hgb]
      _ = b := by group
  have h2 : b * g⁻¹ = g⁻¹ * b := by
    apply mul_left_cancel (a := g)
    calc g * (b * g⁻¹) = (g * b) * g⁻¹ := by group
      _ = (b * g) * g⁻¹ := by rw [hgb]
      _ = b := by group
      _ = g * (g⁻¹ * b) := by group
  calc b * (g * a * g⁻¹) = g * (g⁻¹ * b * g) * a * g⁻¹ := by group
    _ = g * b * a * g⁻¹ := by rw [h1]
    _ = g * (b * a) * g⁻¹ := by group
    _ = g * (a * b) * g⁻¹ := by rw [hab]
    _ = g * a * (b * g⁻¹) := by group
    _ = g * a * (g⁻¹ * b) := by rw [h2]
    _ = (g * a * g⁻¹) * b := by group

private theorem s16h_mixed_card_map_mul_card_inf_ker_cond {H N : Type*} [Group H] [Group N]
    (f : H →* N) (E : Subgroup H) :
    Nat.card ↥(E.map f) * Nat.card ↥(E ⊓ f.ker) = Nat.card ↥E := by
  have h1 : Nat.card ↥(f.ker.subgroupOf E) * Nat.card ↥(E.map f) = Nat.card ↥E := by
    have h := Subgroup.card_ker_mul_card_range (f.domRestrict E)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
    exact h
  have h2 : Nat.card ↥(f.ker.subgroupOf E) = Nat.card ↥(E ⊓ f.ker) := by
    rw [← Subgroup.inf_subgroupOf_left (H := f.ker) (K := E)]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ f.ker ≤ E)).toEquiv
  rw [h2, mul_comm] at h1
  exact h1

private theorem s16h_mixed_card_inf_preBarSub_eq {M V₀ V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hEM : E ≤ M) (hEs : E ≤ stabTil V₀ V) (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) :
    Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar) =
      Nat.card ↥(barSub V₀ V hV E ⊓ Xbar) *
        Nat.card ↥((E.subgroupOf (stabTil V₀ V)) ⊓ (actTil V₀ V hV).ker) := by
  have h1 := s16h_mixed_card_map_mul_card_inf_ker_cond (actTil V₀ V hV)
    ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV))
  rw [Subgroup.map_inf_comap] at h1
  have hker : ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)) ⊓
      (actTil V₀ V hV).ker = (E.subgroupOf (stabTil V₀ V)) ⊓ (actTil V₀ V hV).ker := by
    rw [inf_assoc, inf_eq_right.2 (Subgroup.ker_le_comap (actTil V₀ V hV) Xbar)]
  rw [hker] at h1
  have hpre : E ⊓ preBarSub M V₀ V hV Xbar
      = ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)).map
          (stabTil V₀ V).subtype := by
    unfold preBarSub
    rw [← inf_assoc, inf_eq_left.2 hEM]
    rw [Subgroup.map_inf _ _ (stabTil V₀ V).subtype (Subgroup.subtype_injective _)]
    rw [Subgroup.map_subgroupOf_eq_of_le hEs]
  have hcard4 : Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar)
      = Nat.card ↥((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)) := by
    rw [hpre, Subgroup.card_map_of_injective (f := (stabTil V₀ V).subtype)
      (K := (E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV))
      (Subgroup.subtype_injective _)]
  rw [hcard4]
  exact h1.symm

private theorem s16h_mixed_conj_mem_centSub {W : Type*} [CommGroup W] {U : Subgroup W}
    {g φ : MulAut W} (hg : ∀ u ∈ U, g u ∈ U) (hg' : ∀ u ∈ U, g⁻¹ u ∈ U)
    (hφ : φ ∈ centSub U) : g * φ * g⁻¹ ∈ centSub U := by
  intro u hu
  rw [MulAut.mul_apply, MulAut.mul_apply, hφ (g⁻¹ u) (hg' u hu)]
  exact g.apply_symm_apply u

private theorem s16h_mixed_E_fixes_Z₂ {M Z₁ Z₂ : Subgroup G}
    (hperm : ∀ m ∈ M, (Z₁.map (MulAut.conj m).toMonoidHom = Z₁ ∧
        Z₂.map (MulAut.conj m).toMonoidHom = Z₂) ∨
      (Z₁.map (MulAut.conj m).toMonoidHom = Z₂ ∧
        Z₂.map (MulAut.conj m).toMonoidHom = Z₁))
    {E : Subgroup G} (hEM : E ≤ M) {q : ℕ} (hE : IsElemAbelian q E) (hqodd : Odd q) :
    ∀ e ∈ E, Z₂.map (MulAut.conj e).toMonoidHom = Z₂ := by
  intro e he
  have hconj_le : Set.ncard {Y : Subgroup G |
      ∃ φ ∈ M, Y = Z₁.map (MulAut.conj φ).toMonoidHom} ≤ 2 := by
    have hsub : {Y : Subgroup G | ∃ φ ∈ M, Y = Z₁.map (MulAut.conj φ).toMonoidHom} ⊆
        {Z₁, Z₂} := by
      rintro Y ⟨φ, hφ, rfl⟩
      rcases hperm φ hφ with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Set.mem_insert_iff.2 (Or.inl h1)
      · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 h1))
    calc Set.ncard _ ≤ ({Z₁, Z₂} : Set (Subgroup G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          rcases eq_or_ne Z₁ Z₂ with h | h
          · rw [h]; simp
          · simp [Set.ncard_pair h]
  have hnorm : e ∈ normalizer (Z₁ : Set G) :=
    s15GapFour_mem_normalizer_of_odd M Z₁ hconj_le (hEM he) hqodd (hE.2 e he)
  have hZ₁e : Z₁.map (MulAut.conj e).toMonoidHom = Z₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hnorm
  rcases hperm e (hEM he) with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · have hZ₂eq : Z₂ = Z₁ := by rw [← h1, hZ₁e]
    rw [h2, hZ₂eq]

private theorem s16h_mixed_exists_P (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {q : ℕ} (hq : q ∈ D.sig) (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hFix : s16h_H5Fix (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
      (barSub ⊥ V h.hyp151.isElemAbelian L) q)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian q E)
    (hEcard : Nat.card ↥E = q ^ 3)
    (hcardEq : Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
      (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) = q)
    {Z : Subgroup G} (hEZ : E ≤ Subgroup.centralizer (Z : Set G))
    (hLZ : L ≤ Subgroup.centralizer (Z : Set G))
    {u z : G} (hu : u ∈ wSub ⊥ V h.hyp151.isElemAbelian L) (hu1 : u ≠ 1) (hz : z ∈ Z) :
    ∃ P : Subgroup G, IsElemAbelian q P ∧ q ^ 2 ≤ Nat.card ↥P ∧
      P ≤ D.M ⊓ Subgroup.centralizer ({u * z} : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hpp := D.sig_prime q hq
  haveI : Fact q.Prime := ⟨hpp.1⟩
  have huV : u ∈ V := preTil_le ⊥ V hV _ hu
  let Ū : Subgroup (Vtil ⊥ V hV) := wTil ⊥ V hV L
  let X : Subgroup G := preBarSub D.M ⊥ V hV (centSub Ū)
  have hcardEq' : Nat.card ↥(E ⊓ X) = q := hcardEq
  have hne_bot : E ⊓ X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardEq'
    exact hpp.1.ne_one hcardEq'.symm
  obtain ⟨a₀, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne_bot
  let a : G := (a₀ : G)
  have haE : a ∈ E := (Subgroup.mem_inf.1 a₀.2).1
  have haX : a ∈ X := (Subgroup.mem_inf.1 a₀.2).2
  have ha1 : a ≠ 1 := fun hh => ha₀1 (Subtype.ext hh)
  have hEs : E ≤ stabTil ⊥ V := hEM.trans hMs
  let K : Subgroup (↥(stabTil ⊥ V)) :=
    (E.subgroupOf (stabTil ⊥ V)) ⊓ (actTil ⊥ V hV).ker
  have hKer1 : Nat.card ↥(barSub ⊥ V hV E) * Nat.card ↥K = Nat.card ↥E := by
    have hh := s16h_mixed_card_map_mul_card_inf_ker_cond (actTil ⊥ V hV)
      (E.subgroupOf (stabTil ⊥ V))
    have hcardE : Nat.card ↥(E.subgroupOf (stabTil ⊥ V)) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEs).toEquiv
    rw [hcardE] at hh
    exact hh
  have hKer2 : Nat.card ↥(E ⊓ X) =
      Nat.card ↥(barSub ⊥ V hV E ⊓ centSub Ū) * Nat.card ↥K :=
    s16h_mixed_card_inf_preBarSub_eq hV hEM hEs (centSub Ū)
  have hEq : q ^ 2 * Nat.card ↥(barSub ⊥ V hV E ⊓ centSub Ū) =
      Nat.card ↥(barSub ⊥ V hV E) := by
    apply Nat.mul_right_cancel (card_subgroup_pos K)
    calc (q ^ 2 * Nat.card ↥(barSub ⊥ V hV E ⊓ centSub Ū)) * Nat.card ↥K
        = q ^ 2 * (Nat.card ↥(barSub ⊥ V hV E ⊓ centSub Ū) * Nat.card ↥K) := by ring
      _ = q ^ 2 * Nat.card ↥(E ⊓ X) := by rw [← hKer2]
      _ = q ^ 2 * q := by rw [hcardEq']
      _ = q ^ 3 := by ring
      _ = Nat.card ↥E := hEcard.symm
      _ = Nat.card ↥(barSub ⊥ V hV E) * Nat.card ↥K := hKer1.symm
  have hĒM : barSub ⊥ V hV E ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  have hĒab : IsElemAbelian q (barSub ⊥ V hV E) := s16h_barSub_isElemAbelian hV hE
  have hEn : barSub ⊥ V hV E ≤ normalizer (barSub ⊥ V hV L :
      Set (MulAut (Vtil ⊥ V hV))) :=
    s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs.le
      (hpp.1.odd_of_ne_two hpp.2) hEM hE
  let util : Vtil ⊥ V hV := mkTil ⊥ V hV (IntMod.mk hV ⟨u, huV⟩)
  have hutil : util ∈ Ū := (mem_preTil_iff_of_mem ⊥ V hV Ū huV).1 hu
  have hutil1 : util ≠ 1 := by
    intro hh
    apply hu1
    have h2 : (IntMod.mk hV ⟨u, huV⟩ : IntMod V hV) ∈ modNull ⊥ V hV :=
      (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) _).1 hh
    exact Subgroup.mem_bot.1 ((mem_modNull ⊥ V hV _).1 h2)
  obtain ⟨g, hgL, bbar, hbbarE, hbbarC, hfix⟩ :=
    hFix (barSub ⊥ V hV E) (le_inf hĒM hEn) hĒab (le_of_eq hEq) util hutil hutil1
  obtain ⟨ĝ, hĝL, hĝeq⟩ := (mem_barSub ⊥ V hV L g).1 hgL
  obtain ⟨bhat, hbhatE, hbhateq⟩ := (mem_barSub ⊥ V hV E bbar).1 hbbarE
  have hbX : (bhat : G) ∉ X := by
    intro hbX
    obtain ⟨-, hh, hh'⟩ := (mem_preBarSub D.M ⊥ V hV (centSub Ū)).1 hbX
    have hcast : actTil ⊥ V hV ⟨(bhat : G), hh⟩ = bbar := by
      rw [show (⟨(bhat : G), hh⟩ : ↥(stabTil ⊥ V)) = bhat from Subtype.ext rfl, hbhateq]
    exact hbbarC (hcast ▸ hh')
  have hstabg : ∀ v ∈ Ū, g v ∈ Ū :=
    commSub_top_stable151b (X := barSub ⊥ V hV L) (g := g)
      (fun x hx => (barSub ⊥ V hV L).mul_mem
        ((barSub ⊥ V hV L).mul_mem hgL hx) ((barSub ⊥ V hV L).inv_mem hgL))
  have hstabgi : ∀ v ∈ Ū, g⁻¹ v ∈ Ū :=
    commSub_top_stable151b (X := barSub ⊥ V hV L) (g := g⁻¹)
      (fun x hx => (barSub ⊥ V hV L).mul_mem
        ((barSub ⊥ V hV L).mul_mem ((barSub ⊥ V hV L).inv_mem hgL) hx)
        ((barSub ⊥ V hV L).inv_mem ((barSub ⊥ V hV L).inv_mem hgL)))
  have hstabg' : ∀ v ∈ Ū, actTil ⊥ V hV ĝ v ∈ Ū := by rw [hĝeq]; exact hstabg
  have hstabgi' : ∀ v ∈ Ū, (actTil ⊥ V hV ĝ)⁻¹ v ∈ Ū := by rw [hĝeq]; exact hstabgi
  obtain ⟨haM, haStab, haC⟩ := (mem_preBarSub D.M ⊥ V hV (centSub Ū)).1 haX
  let x' : G := (ĝ : G) * a * (ĝ : G)⁻¹
  let x'' : G := (ĝ : G) * (bhat : G) * (ĝ : G)⁻¹
  have hx'CE : x' ∈ F11.CElt D.M ⊥ u := by
    have hx'stab : x' ∈ stabTil ⊥ V :=
      (stabTil ⊥ V).mul_mem ((stabTil ⊥ V).mul_mem ĝ.2 haStab)
        ((stabTil ⊥ V).inv_mem ĝ.2)
    have hx'M : x' ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (h.hyp151.le hĝL) haM)
        (D.M.inv_mem (h.hyp151.le hĝL))
    have hx'C : actTil ⊥ V hV ⟨x', hx'stab⟩ ∈ centSub Ū := by
      have heq : (⟨x', hx'stab⟩ : ↥(stabTil ⊥ V)) = ĝ * ⟨a, haStab⟩ * ĝ⁻¹ :=
        Subtype.ext (by simp [x'])
      rw [heq]
      simp only [map_mul, map_inv]
      exact s16h_mixed_conj_mem_centSub hstabg' hstabgi' haC
    exact s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hu
      ((mem_preBarSub D.M ⊥ V hV (centSub Ū)).2 ⟨hx'M, hx'stab, hx'C⟩)
  have hx''CE : x'' ∈ F11.CElt D.M ⊥ u := by
    have hx''stab : x'' ∈ stabTil ⊥ V :=
      (stabTil ⊥ V).mul_mem ((stabTil ⊥ V).mul_mem ĝ.2 bhat.2)
        ((stabTil ⊥ V).inv_mem ĝ.2)
    have hx''M : x'' ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (h.hyp151.le hĝL) (hEM hbhatE))
        (D.M.inv_mem (h.hyp151.le hĝL))
    have hact : actTil ⊥ V hV ⟨x'', hx''stab⟩ = g * bbar * g⁻¹ := by
      have heq : (⟨x'', hx''stab⟩ : ↥(stabTil ⊥ V)) = ĝ * bhat * ĝ⁻¹ :=
        Subtype.ext (by simp [x''])
      rw [heq]
      simp only [map_mul, map_inv]
      rw [hĝeq, hbhateq]
    refine ⟨hx''M, stabTil_le_normalizer₀ ⊥ V hx''stab, ?_⟩
    have h1 : actTil ⊥ V hV ⟨x'', hx''stab⟩ util = util := by rw [hact]; exact hfix
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  let H : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers (bhat : G)
  have hb_not_a : (bhat : G) ∉ Subgroup.zpowers a := fun hb =>
    hbX (Subgroup.zpowers_le.2 haX hb)
  have hbhat1 : (bhat : G) ≠ 1 := fun h1 => hb_not_a (h1.symm ▸ Subgroup.one_mem _)
  have hHab_card := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_mem_isElemAbelian hE haE hbhatE
    (orderOf_eq_prime (hE.2 a haE) ha1)
    (orderOf_eq_prime (hE.2 (bhat : G) hbhatE) hbhat1) hb_not_a
  have hHab : IsElemAbelian q H := hHab_card.1
  have hHge : q ^ 2 ≤ Nat.card ↥H := le_of_eq hHab_card.2.symm
  let P : Subgroup G := conjSubgroup H ((ĝ : G)⁻¹)
  have hPab : IsElemAbelian q P :=
    hHab.map (MulAut.conj ((ĝ : G)⁻¹)⁻¹).toMonoidHom
  have hPge : q ^ 2 ≤ Nat.card ↥P := by
    have hh := Subgroup.card_map_of_injective
      (f := (MulAut.conj ((ĝ : G)⁻¹)⁻¹).toMonoidHom) (K := H) (MulAut.conj _).injective
    exact hh.symm ▸ hHge
  have hPle : P ≤ F11.CElt D.M ⊥ u := by
    show H.map (MulAut.conj ((ĝ : G)⁻¹)⁻¹).toMonoidHom ≤ F11.CElt D.M ⊥ u
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      show MulAut.conj ((ĝ : G)⁻¹)⁻¹ a ∈ F11.CElt D.M ⊥ u
      rw [inv_inv, MulAut.conj_apply]
      exact hx'CE
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      show MulAut.conj ((ĝ : G)⁻¹)⁻¹ (bhat : G) ∈ F11.CElt D.M ⊥ u
      rw [inv_inv, MulAut.conj_apply]
      exact hx''CE
  have hHcentZ : H ≤ Subgroup.centralizer (Z : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hEZ haE
    · rw [Subgroup.zpowers_le]; exact hEZ hbhatE
  have hĝcentZ : (ĝ : G) ∈ Subgroup.centralizer (Z : Set G) := hLZ hĝL
  have hPcentZ : P ≤ Subgroup.centralizer (Z : Set G) := by
    have hh := s16h_mixed_map_conj_le_centralizer (B := Z) (A := H) (g := (ĝ : G))
      hĝcentZ hHcentZ
    simpa [P, conjSubgroup, inv_inv] using hh
  refine ⟨P, hPab, hPge, ?_⟩
  intro p hp
  refine ⟨(hPle hp).1, ?_⟩
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hpu : p * u = u * p := s16h_mixed_comm_of_mem_cElt_bot (hPle hp)
  have hpz : z * p = p * z := (Subgroup.mem_centralizer_iff.1 (hPcentZ hp)) z hz
  calc (u * z) * p = u * (z * p) := by group
    _ = u * (p * z) := by rw [hpz]
    _ = (u * p) * z := by group
    _ = (p * u) * z := by rw [hpu]
    _ = p * (u * z) := by group

theorem s16h_uniqueMax_of_fix_two_mixed (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {q : ℕ} (hq : q ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M)
    (hBB : s16h_BlockBound (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
      (barSub ⊥ V h.hyp151.isElemAbelian L) q 2)
    (hFix : s16h_H5Fix (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
      (barSub ⊥ V h.hyp151.isElemAbelian L) q)
    (hZ2 : Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hpp := D.sig_prime q hq
  haveI : Fact q.Prime := ⟨hpp.1⟩
  have hqodd : Odd q := hpp.1.odd_of_ne_two hpp.2
  have hq2le : 2 ≤ q := hpp.1.two_le
  obtain ⟨x, hxM, hxn⟩ :=
    s16c34_exists_not_mem_nBar D h.hyp151 (by omega : 1 < s15 D.M ⊥ V hV L)
  let Z₁ : Subgroup G := wSub ⊥ V hV L ⊓ centralizer (L : Set G)
  let Z₂ : Subgroup G := Z₁.map (MulAut.conj x).toMonoidHom
  have hv1 := s16h_v1Sub_eq_sup_of_s_two D h hs hxM hxn
  have hperm := hv1.2
  have hv1eq : v1Sub D.M ⊥ V hV L = Z₁ ⊔ Z₂ := hv1.1
  have hZ₂v1 : Z₂ ≤ v1Sub D.M ⊥ V hV L := by rw [hv1eq]; exact le_sup_right
  have hZ₁le : Z₁ ≤ wSub ⊥ V hV L := inf_le_left
  have hsupw : wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L = wSub ⊥ V hV L ⊔ Z₂ := by
    rw [hv1eq, ← sup_assoc, sup_eq_left.2 hZ₁le]
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h3)
  let Ū : Subgroup (Vtil ⊥ V hV) := wTil ⊥ V hV L
  let X : Subgroup G := preBarSub D.M ⊥ V hV (centSub Ū)
  have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs.le hqodd hEM hE
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hE hEn
  have hqle : q ≤ Nat.card ↥(E ⊓ X) := by
    rw [hEcard] at hcard
    have h2 : q ^ 2 * q ≤ q ^ 2 * Nat.card ↥(E ⊓ X) := by
      calc q ^ 2 * q = q ^ 3 := by ring
        _ ≤ _ := hcard
    exact Nat.le_of_mul_le_mul_left h2 (pow_pos hpp.1.pos 2)
  have hZ₂card : Nat.card ↥Z₂ ≤ 2 := by
    have h1 : Nat.card ↥Z₂ = Nat.card ↥Z₁ :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have h2 : Z₁ = preTil ⊥ V hV (commSub ⊤ (lBar ⊥ V hV L) ⊓
        fixV (lBar ⊥ V hV L)) := s16h_wSub_inf_centralizer_eq_preTil D h
    rw [h1, h2, s16h_mixed_card_preTil_bot hV]
    exact hZ2
  have hEfixZ₂ : ∀ e ∈ E, Z₂.map (MulAut.conj e).toMonoidHom = Z₂ :=
    s16h_mixed_E_fixes_Z₂ hperm hEM hE hqodd
  have hEcentZ₂ : ∀ e ∈ E, ∀ z ∈ Z₂, e * z = z * e := by
    intro e he z hz
    have hmem : e * z * e⁻¹ ∈ Z₂ := by
      have hh' : MulAut.conj e z ∈ Z₂ := by
        have hh'' := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hz
        rwa [hEfixZ₂ e he] at hh''
      rwa [MulAut.conj_apply] at hh'
    by_cases hz1 : z = 1
    · subst hz1; simp
    · have hmem1 : e * z * e⁻¹ ≠ 1 := by
        intro h1
        apply hz1
        calc z = e⁻¹ * (e * z * e⁻¹) * e := by group
          _ = e⁻¹ * 1 * e := by rw [h1]
          _ = 1 := by group
      have heq : e * z * e⁻¹ = z :=
        s16h_mixed_eq_of_ne_one_of_card_le_two hZ₂card hz hz1 hmem hmem1
      calc e * z = (e * z * e⁻¹) * e := by group
        _ = z * e := by rw [heq]
  have hLcentZ₂ : ∀ l ∈ L, ∀ z ∈ Z₂, l * z = z * l := by
    intro l hl z hz
    have hLpre : L ≤ preBarSub D.M ⊥ V hV (barSub ⊥ V hV L) :=
      le_preBarSub_barSub hV h.hyp151.le (h.hyp151.le.trans hMs)
    have hce : l ∈ F11.CElt D.M ⊥ z := by
      have hh := s16c34_preBarSub_le_cElt_v1 D h.hyp151 (c := 1) D.M.one_mem (hZ₂v1 hz)
      rw [conjSubgroup_one] at hh
      exact hh (hLpre hl)
    exact s16h_mixed_comm_of_mem_cElt_bot hce
  intro w hw hw1
  rw [hsupw] at hw
  haveI : IsMulCommutative ↥V := hV.1
  have hZ₂V : Z₂ ≤ V := hZ₂v1.trans (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hwV : w ∈ V := (sup_le (preTil_le ⊥ V hV _) hZ₂V) hw
  have hWV : wSub ⊥ V hV L ≤ V := preTil_le ⊥ V hV _
  have hwH : (⟨w, hwV⟩ : ↥V) ∈
      (wSub ⊥ V hV L).subgroupOf V ⊔ Z₂.subgroupOf V := by
    rw [← Subgroup.subgroupOf_sup hWV hZ₂V]
    exact (Subgroup.mem_subgroupOf).2 hw
  obtain ⟨y, hy, z', hz', hyz⟩ := Subgroup.mem_sup.1 hwH
  let u : G := (y : G)
  let z : G := (z' : G)
  have hu : u ∈ wSub ⊥ V hV L := (Subgroup.mem_subgroupOf).1 hy
  have hz : z ∈ Z₂ := (Subgroup.mem_subgroupOf).1 hz'
  have hw_eq : w = u * z := by
    have h2 : (y : G) * (z' : G) = w := congrArg (fun t : ↥V => (t : G)) hyz
    exact h2.symm
  by_cases hbig : q ^ 2 ≤ Nat.card ↥(E ⊓ X)
  · have hnc : ¬ IsCyclic ↥(E ⊓ X) :=
      s16c7_not_isCyclic_of_elemAbelian hpp.1 (hE.mono inf_le_left) hbig
    have hle : E ⊓ X ≤ D.M ⊓ centralizer ({w} : Set G) := by
      intro e he
      have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
      have heX : e ∈ X := (Subgroup.mem_inf.1 he).2
      have heu : e * u = u * e :=
        s16h_mixed_comm_of_mem_cElt_bot
          (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hu heX)
      have hez : e * z = z * e := hEcentZ₂ e heE z hz
      refine ⟨(inf_le_left.trans hEM) he, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      rw [hy, hw_eq]
      calc (u * z) * e = u * (z * e) := by group
        _ = u * (e * z) := by rw [hez]
        _ = (u * e) * z := by group
        _ = (e * u) * z := by rw [heu]
        _ = e * (u * z) := by group
    exact s16c34_uniqueMax_of_noncyclic D h61 hq
      (IsElemAbelian.isPGroup (hE.mono inf_le_left)) hnc hle inf_le_left
  · have hsmall : Nat.card ↥(E ⊓ X) < q ^ 2 := not_le.1 hbig
    by_cases hz1 : z = 1
    · have hwu : w ∈ wSub ⊥ V hV L := by rw [hw_eq, hz1, mul_one]; exact hu
      exact s16h_uniqueMax_of_fix_two D h61 h127 h hs.le hq h3 hBB hFix w hwu hw1
    · by_cases hu1 : u = 1
      · have hEnc : ¬ IsCyclic ↥E :=
          s16c7_not_isCyclic_of_elemAbelian hpp.1 hE (by
            rw [hEcard]
            exact Nat.pow_le_pow_right hpp.1.pos (by omega : 2 ≤ 3))
        have hle : E ≤ D.M ⊓ centralizer ({w} : Set G) := by
          intro e he
          refine ⟨hEM he, ?_⟩
          refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
          rw [Set.mem_singleton_iff] at hy
          rw [hy, hw_eq, hu1, one_mul]
          exact (hEcentZ₂ e he z hz).symm
        exact s16c34_uniqueMax_of_noncyclic D h61 hq (IsElemAbelian.isPGroup hE) hEnc hle
          inf_le_left
      · have hEab' : IsElemAbelian q (E ⊓ X) := hE.mono inf_le_left
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).1 hEab'.isPGroup
        have hn_eq : n = 1 := by
          have h1 : q ≤ q ^ n := by rw [← hn]; exact hqle
          have h2 : q ^ n < q ^ 2 := by rw [← hn]; exact hsmall
          have hnpos : 0 < n := by
            by_contra hc
            have h0 : n = 0 := by omega
            subst h0
            rw [pow_zero] at h1
            omega
          have hnlt : n < 2 := by
            by_contra hc
            have h2n : 2 ≤ n := not_lt.1 hc
            have hle' := Nat.pow_le_pow_right hpp.1.pos h2n
            omega
          omega
        have hcardEq : Nat.card ↥(E ⊓ X) = q := by rw [hn, hn_eq, pow_one]
        have hEZ : E ≤ Subgroup.centralizer (Z₂ : Set G) :=
          fun e he => Subgroup.mem_centralizer_iff.2 fun y hy => (hEcentZ₂ e he y hy).symm
        have hLZ : L ≤ Subgroup.centralizer (Z₂ : Set G) :=
          fun l hl => Subgroup.mem_centralizer_iff.2 fun y hy => (hLcentZ₂ l hl y hy).symm
        obtain ⟨P, hPab, hPge, hPle⟩ :=
          s16h_mixed_exists_P D h hq hs hFix hEM hE hEcard hcardEq hEZ hLZ hu hu1 hz
        rw [hw_eq]
        exact s16c34_uniqueMax_of_noncyclic D h61 hq (IsElemAbelian.isPGroup hPab)
          (s16c7_not_isCyclic_of_elemAbelian hpp.1 hPab hPge) hPle inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
