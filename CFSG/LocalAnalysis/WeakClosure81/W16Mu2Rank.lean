module

public import CFSG.LocalAnalysis.WeakClosure81.W16Setup
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_centralizer_of_comm_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V₀ V B : Subgroup G} (hV : IsPGroup 2 V) (hV₀ : V₀ ≤ V) (hB : IsPGroup p B)
    (hBV₀ : B ≤ normalizer (V₀ : Set G)) {v : G} (hv : v ∈ V)
    (hvB : ∀ b ∈ B, b * v * b⁻¹ * v⁻¹ ∈ V₀) : v ∈ V ⊓ centralizer (B : Set G) ⊔ V₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hV₀2 : IsPGroup 2 V₀ := hV.to_le hV₀
  have hcop : ¬ p ∣ Nat.card V₀ := by
    obtain ⟨n, hn⟩ := hV₀2.exists_card_eq
    rw [hn]
    intro hdvd
    have hp2' : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
    exact hp2 hp2'
  have hk : ∀ a : ↥B, ∀ x : G, (v⁻¹)⁻¹ * x ∈ V₀ →
      (v⁻¹)⁻¹ * ((MulAut.conj.comp B.subtype) a) x ∈ V₀ := by
    intro a x hx
    simp only [MonoidHom.comp_apply, MulAut.conj_apply, inv_inv]
    have hx' : v * x ∈ V₀ := by simpa only [inv_inv] using hx
    have h1 : v * ((a : G) * v⁻¹ * (a : G)⁻¹) ∈ V₀ := by
      have h := V₀.inv_mem (hvB a.1 a.2)
      convert h using 1 <;> group
    have h2 : (a : G) * (v * x) * (a : G)⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 (hBV₀ a.2) (v * x)).mp hx'
    have h3 := V₀.mul_mem h1 h2
    convert h3 using 1 <;> simp only [Subgroup.coe_subtype] <;> group
  obtain ⟨y, hy, hyfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hB
      (MulAut.conj.comp B.subtype) V₀ hcop v⁻¹).2 hk
  have hyV₀ : v * y ∈ V₀ := by simpa using hy
  have hyV : y ∈ V := by
    have h1 : v * y ∈ V := hV₀ hyV₀
    have h2 : v⁻¹ * (v * y) ∈ V := V.mul_mem (V.inv_mem hv) h1
    rwa [inv_mul_cancel_left] at h2
  have hyC : y ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h : b * y * b⁻¹ = y := hyfix ⟨b, hb⟩
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [h]
  have hyinv : y⁻¹ ∈ V ⊓ centralizer (B : Set G) :=
    (V ⊓ centralizer (B : Set G)).inv_mem ⟨hyV, hyC⟩
  have hvy : v = (v * y) * y⁻¹ := by group
  rw [hvy, show V ⊓ centralizer (B : Set G) ⊔ V₀ =
      V₀ ⊔ (V ⊓ centralizer (B : Set G)) from sup_comm _ _]
  exact Subgroup.mul_mem_sup hyV₀ hyinv

theorem comm_mem_of_mQuot_le_one {V₀ Y : Subgroup G} (hY : IsPGroup 2 Y) (hV₀ : V₀ ≤ Y)
    (h1 : E3.mQuot Y V₀ ≤ 1) {e : G} (heY : e ∈ normalizer (Y : Set G))
    (he₀ : e ∈ normalizer (V₀ : Set G)) {y : G} (hy : y ∈ Y) : e * y * e⁻¹ * y⁻¹ ∈ V₀ := by
  by_cases hy₀ : y ∈ V₀
  · have hey₀ : e * y * e⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 he₀ y).mp hy₀
    exact V₀.mul_mem hey₀ (V₀.inv_mem hy₀)
  · have hey₀ : e * y * e⁻¹ ∉ V₀ := by
      intro h
      exact hy₀ ((Subgroup.mem_normalizer_iff.1 he₀ y).mpr h)
    have heyY : e * y * e⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 heY y).mp hy
    have hne : E3.mQuot Y V₀ ≠ 0 := by
      intro h0
      have hVY : V₀ = Y := (E3.mQuot_eq_zero_iff hY hV₀).1 h0
      rw [← hVY] at hy
      exact hy₀ hy
    have h1' : E3.mQuot Y V₀ = 1 := by omega
    have hrel : V₀.relIndex Y = 2 := by
      rw [E3.relIndex_eq_two_pow hY, h1']
      norm_num
    obtain ⟨a, -, hxor⟩ := Subgroup.relIndex_eq_two_iff.1 hrel
    have hya : y * a ∈ V₀ := by
      rcases hxor y hy with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hy₀
    have heya : (e * y * e⁻¹) * a ∈ V₀ := by
      rcases hxor (e * y * e⁻¹) heyY with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hey₀
    have hmem : (e * y * e⁻¹) * a * (y * a)⁻¹ ∈ V₀ :=
      V₀.mul_mem heya (V₀.inv_mem hya)
    convert hmem using 1
    group

private theorem inf_centralizer_le_sup_of_mQuot_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V₀ V E F : Subgroup G} (hV : IsPGroup 2 V) (hV₀ : V₀ ≤ V) (hE : IsElemAbelian p E)
    (hFE : F ≤ E) (hEV : E ≤ normalizer (V : Set G)) (hEV₀ : E ≤ normalizer (V₀ : Set G))
    (h1 : E3.mQuot (V ⊓ centralizer (F : Set G) ⊔ V₀) V₀ ≤ 1) :
    V ⊓ centralizer (F : Set G) ≤ V ⊓ centralizer (E : Set G) ⊔ V₀ := by
  have hEF : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e :=
    fun e he f hf => CFSG.Open.IsElemAbelian.comm hE he (hFE hf)
  have hEF' : ∀ e ∈ E, ∀ f ∈ F, e⁻¹ * f = f * e⁻¹ :=
    fun e he f hf => CFSG.Open.IsElemAbelian.comm hE (E.inv_mem he) (hFE hf)
  have hmapC : ∀ e ∈ E, ∀ c : G, c ∈ centralizer (F : Set G) →
      e * c * e⁻¹ ∈ centralizer (F : Set G) := by
    intro e he c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro f hf
    calc f * (e * c * e⁻¹) = (f * e) * c * e⁻¹ := by group
      _ = (e * f) * c * e⁻¹ := by rw [← hEF e he f hf]
      _ = e * (f * c) * e⁻¹ := by group
      _ = e * (c * f) * e⁻¹ := by rw [hc f hf]
      _ = e * c * (f * e⁻¹) := by group
      _ = e * c * (e⁻¹ * f) := by rw [← hEF' e he f hf]
      _ = (e * c * e⁻¹) * f := by group
  have hEC : E ≤ normalizer (centralizer (F : Set G)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hmapC e he c
    · intro hc
      have h := hmapC e⁻¹ (E.inv_mem he) (e * c * e⁻¹) hc
      convert h using 1
      group
  have hmapV : ∀ e ∈ E, V.map (MulAut.conj e) = V := fun e he =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hEV he)
  have hmapV₀ : ∀ e ∈ E, V₀.map (MulAut.conj e) = V₀ := fun e he =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hEV₀ he)
  have hmapC' : ∀ e ∈ E, (centralizer (F : Set G)).map (MulAut.conj e) =
      centralizer (F : Set G) := fun e he =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hEC he)
  have hEY : E ≤ normalizer (V ⊓ centralizer (F : Set G) ⊔ V₀ : Subgroup G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj e).injective,
      hmapV e he, hmapC' e he, hmapV₀ e he]
  intro v hv
  have hvV : v ∈ V := hv.1
  have hY : IsPGroup 2 (V ⊓ centralizer (F : Set G) ⊔ V₀ : Subgroup G) :=
    hV.to_le (sup_le inf_le_left hV₀)
  refine mem_sup_centralizer_of_comm_mem hp hp2 hV hV₀
    (CFSG.Open.IsElemAbelian.isPGroup hE) hEV₀ hvV ?_
  intro e he
  exact comm_mem_of_mQuot_le_one hY le_sup_right h1 (hEY he) (hEV₀ he)
    (Subgroup.mem_sup_left hv)

theorem exists_hyperplane_two_le_mQuot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V₀ V E : Subgroup G} (hV : IsPGroup 2 V) (hV₀ : V₀ ≤ V) (hE : IsElemAbelian p E)
    (hEp : p ≤ Nat.card E) (hEV : E ≤ normalizer (V : Set G))
    (hEV₀ : E ≤ normalizer (V₀ : Set G)) (h2 : 2 ≤ E3.mQuot V V₀) :
    ∃ F ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E,
      2 ≤ E3.mQuot (V ⊓ centralizer (F : Set G) ⊔ V₀) V₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp' : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  have hcopV : Nat.Coprime p (Nat.card V) := by
    obtain ⟨n, hn⟩ := hV.exists_card_eq
    rw [hn]
    exact Nat.Prime.coprime_pow_of_not_dvd (p := 2) (a := p) (m := n) Nat.prime_two
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm)
  obtain ⟨r, hr⟩ := hEp'.exists_card_eq
  have hp2le : 2 ≤ p := hp.two_le
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, pow_zero] at hr
      omega
    · exact h
  have hdvd : p ^ (r - 1) ∣ Nat.card ↥E := by
    rw [hr]
    exact pow_dvd_pow p (Nat.sub_le r 1)
  obtain ⟨F₀, hF₀card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) p hdvd
  let F : Subgroup G := F₀.map E.subtype
  have hFE : F ≤ E := Subgroup.map_subtype_le F₀
  have hFcard : Nat.card F = p ^ (r - 1) := by
    dsimp only [F]
    rw [Subgroup.card_subtype E F₀, hF₀card]
  have hcardEF : Nat.card E = p * Nat.card F := by
    calc Nat.card E = p ^ r := hr
      _ = p ^ ((r - 1) + 1) := by rw [Nat.sub_add_cancel hr1]
      _ = p * p ^ (r - 1) := by rw [pow_succ']
      _ = p * Nat.card F := by rw [hFcard]
  have hFmem : F ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E :=
    ⟨hFE, hcardEF⟩
  by_contra hcon
  have hno : ∀ F' : Subgroup G,
      F' ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E →
      E3.mQuot (V ⊓ centralizer (F' : Set G) ⊔ V₀) V₀ ≤ 1 := by
    intro F' hF'
    have hlt : ¬ (2 ≤ E3.mQuot (V ⊓ centralizer (F' : Set G) ⊔ V₀) V₀) :=
      fun hge => hcon ⟨F', hF', hge⟩
    omega
  have hle : ∀ F' ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E,
      V ⊓ centralizer (F' : Set G) ≤ V ⊓ centralizer (E : Set G) ⊔ V₀ :=
    fun F' hF' => inf_centralizer_le_sup_of_mQuot_le_one hp hp2 hV hV₀ hE hF'.1
      hEV hEV₀ (hno F' hF')
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
    (G := G) hp hE hEp hEV hcopV
  have hVle : V ≤ V ⊓ centralizer (E : Set G) ⊔ V₀ := by
    calc V = ⨆ F' ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p E,
          V ⊓ centralizer (F' : Set G) := hgen.symm
      _ ≤ V ⊓ centralizer (E : Set G) ⊔ V₀ := iSup₂_le hle
  have hCEF : V ⊓ centralizer (E : Set G) ≤ V ⊓ centralizer (F : Set G) :=
    inf_le_inf_left V (Subgroup.centralizer_le (fun f hf => hFE hf))
  have hVle2 : V ≤ V ⊓ centralizer (F : Set G) ⊔ V₀ :=
    le_trans hVle (sup_le_sup hCEF le_rfl)
  have heq : V ⊓ centralizer (F : Set G) ⊔ V₀ = V :=
    le_antisymm (sup_le inf_le_left hV₀) hVle2
  have h2' : 2 ≤ E3.mQuot (V ⊓ centralizer (F : Set G) ⊔ V₀) V₀ := by
    rw [heq]
    exact h2
  have := hno F hFmem
  omega

theorem exists_two_le_mQuot_sup_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V₀ V E : Subgroup G} (hV : IsPGroup 2 V) (hV₀ : V₀ ≤ V) (hE : IsElemAbelian p E)
    (hE3 : p ^ 3 ≤ Nat.card E) (hEV : E ≤ normalizer (V : Set G))
    (hEV₀ : E ≤ normalizer (V₀ : Set G)) (h2 : 2 ≤ E3.mQuot V V₀) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 2 ∧
      2 ≤ E3.mQuot (V ⊓ centralizer (B : Set G) ⊔ V₀) V₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : p ≤ Nat.card E := by
    calc p = p ^ 1 := by rw [pow_one]
      _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
      _ ≤ Nat.card E := hE3
  obtain ⟨F, hFmem, hF2⟩ :=
    exists_hyperplane_two_le_mQuot hp hp2 hV hV₀ hE hEp hEV hEV₀ h2
  have hFE : F ≤ E := hFmem.1
  have hFp : IsPGroup p F := (CFSG.Open.IsElemAbelian.isPGroup hE).to_le hFE
  have hFcard : p ^ 2 ≤ Nat.card F := by
    have hmul : p * p ^ 2 ≤ p * Nat.card F := by
      have h := hE3
      rw [hFmem.2] at h
      rwa [show p ^ 3 = p * p ^ 2 by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']] at h
    exact Nat.le_of_mul_le_mul_left hmul hp.pos
  obtain ⟨s, hs⟩ := hFp.exists_card_eq
  have hs2 : 2 ≤ s := by
    have hle : p ^ 2 ≤ p ^ s := by rwa [← hs]
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hdvd : p ^ 2 ∣ Nat.card ↥F := by
    rw [hs]
    exact pow_dvd_pow p hs2
  obtain ⟨B₀, hB₀card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥F) p hdvd
  let B : Subgroup G := B₀.map F.subtype
  have hBF : B ≤ F := Subgroup.map_subtype_le B₀
  have hBcard : Nat.card B = p ^ 2 := by
    dsimp only [B]
    rw [Subgroup.card_subtype F B₀, hB₀card]
  refine ⟨B, hBF.trans hFE, hBcard, ?_⟩
  have hCFB : centralizer (F : Set G) ≤ centralizer (B : Set G) :=
    Subgroup.centralizer_le (fun b hb => hBF hb)
  have hmono : V ⊓ centralizer (F : Set G) ⊔ V₀ ≤ V ⊓ centralizer (B : Set G) ⊔ V₀ :=
    sup_le_sup (inf_le_inf_left V hCFB) le_rfl
  have hadd := E3.mQuot_add (V := V ⊓ centralizer (B : Set G) ⊔ V₀) (U := V₀)
    (U' := V ⊓ centralizer (F : Set G) ⊔ V₀) le_sup_right hmono
  omega

theorem mQuot_le_mQuot_of_inf_eq {V₀ V X Y : Subgroup G} (hV : IsPGroup 2 V) (hX : X ≤ V)
    (hY : Y ≤ V) (hXY : X ⊓ Y = V₀) : E3.mQuot X V₀ ≤ E3.mQuot V Y := by
  have hX2 : IsPGroup 2 X := hV.to_le hX
  have hpow : 2 ^ E3.mQuot X V₀ ≤ 2 ^ E3.mQuot V Y := by
    rw [← E3.relIndex_eq_two_pow hX2, ← E3.relIndex_eq_two_pow hV]
    calc V₀.relIndex X = (X ⊓ Y).relIndex X := by rw [hXY]
      _ = Y.relIndex X := Subgroup.inf_relIndex_left X Y
      _ ≤ Y.relIndex V := Subgroup.relIndex_le_of_le_right hX (E3.relIndex_ne_zero' V Y)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow

theorem exists_mem_sup_not_mem_of_mQuot {V₀ V U C : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hU : U ≤ V) (hC : C ≤ V) (h2 : 2 ≤ E3.mQuot (C ⊔ V₀) V₀)
    (h1 : E3.mQuot V (U ⊔ V₀) ≤ 1) : ∃ x ∈ C, x ∈ U ⊔ V₀ ∧ x ∉ V₀ := by
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hV hx hy
  by_contra hcon
  have hno : ∀ x : G, x ∈ C → x ∈ U ⊔ V₀ → x ∈ V₀ := by
    intro x hxC hxU
    by_contra hx0
    exact hcon ⟨x, hxC, hxU, hx0⟩
  have hinf : (C ⊔ V₀) ⊓ (U ⊔ V₀) = V₀ := by
    refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨c, hcC, w, hwV₀, hcw⟩ := exists_mul_of_mem_sup hC hV₀ hcomm hy.1
    have hcU : c ∈ U ⊔ V₀ := by
      have hc : c = y * w⁻¹ := by rw [← hcw]; group
      rw [hc]
      exact Subgroup.mul_mem _ hy.2 (Subgroup.mem_sup_right (V₀.inv_mem hwV₀))
    have hcV₀ : c ∈ V₀ := hno c hcC hcU
    have hy' : y = c * w := hcw.symm
    rw [hy']
    exact V₀.mul_mem hcV₀ hwV₀
  have hle := mQuot_le_mQuot_of_inf_eq hV2 (sup_le hC hV₀) (sup_le hU hV₀) hinf
  omega

theorem centralizer_singleton_le_of_uniqueMax {M B : Subgroup G} (huniq : UniqueMax M B)
    {x : G} (hx1 : x ≠ 1) (hx2 : IsPGroup 2 (zpowers x))
    (hxB : x ∈ centralizer (B : Set G)) : centralizer ({x} : Set G) ≤ M := by
  have hD : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
  have hCN : centralizer ({x} : Set G) ≤ normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer (Subgroup.closure ({x} : Set G) : Set G)
  have hBC : B ≤ centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hxB b hb
  have hNM : normalizer (Subgroup.zpowers x : Set G) ≤ M :=
    normalizer_le_of_uniqueMax huniq hD hx2 (hBC.trans hCN)
  exact hCN.trans hNM

theorem false_of_uniqueMax_of_mQuot_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M V₀ V U E : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) (hU : U ≤ V)
    (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) (hEV : E ≤ normalizer (V : Set G))
    (hEV₀ : E ≤ normalizer (V₀ : Set G))
    (hEu : ∀ B : Subgroup G, B ≤ E → Nat.card B = p ^ 2 → UniqueMax M B)
    (h2 : 2 ≤ E3.mQuot V V₀) (h1 : E3.mQuot V (U ⊔ V₀) ≤ 1)
    (ha : ∀ x ∈ U ⊔ V₀, x ∉ V₀ → ¬ centralizer ({x} : Set G) ≤ M) : False := by
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV
  obtain ⟨B, hBE, hBcard, hB2⟩ :=
    exists_two_le_mQuot_sup_centralizer hp hp2 hV2 hV₀ hE hE3 hEV hEV₀ h2
  obtain ⟨x, hxC, hxU, hx0⟩ := exists_mem_sup_not_mem_of_mQuot hV hV₀ hU inf_le_left hB2 h1
  have hx1 : x ≠ 1 := fun e => hx0 (e ▸ V₀.one_mem)
  have hx2 : IsPGroup 2 (zpowers x) := hV2.to_le ((zpowers_le (G := G)).2 hxC.1)
  exact ha x hxU hx0 (centralizer_singleton_le_of_uniqueMax (hEu B hBE hBcard) hx1 hx2 hxC.2)

end CFSG.LocalAnalysis.WeakClosure81
