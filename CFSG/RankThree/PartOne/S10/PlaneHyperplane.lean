module

public import CFSG.RankThree.PartOne.S10.PlaneFactorCases
import CFSG.RankThree.PartOne.S10.PlaneCoreBounds
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.ThompsonAxB
import CFSG.RankThree.GroupTheory.SteinbergBMClassTwoExtraspecialAction
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly
open scoped commutatorElement

namespace PlaneHyperplane


theorem exists_hyperplane_moving {D Z : Type} [Group D] [Finite D] [Group Z] [Finite Z]
    [IsElementaryAbelian 2 Z] (hD : ¬ 2 ∣ Nat.card D) (φ : Z →* MulAut D)
    (hφ : Function.Injective φ) {z : Z} (hz : z ≠ 1) :
    ∃ Z₀ : Subgroup Z, Z₀.index = 2 ∧ ∃ e : D, (∀ g ∈ Z₀, φ g e = e) ∧ φ z e ≠ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Z := ⟨⟨z, 1, hz⟩⟩
  let _ : MulDistribMulAction Z D := MulDistribMulAction.compHom D φ
  have hgen := SolvableHall.coprime_hyperplane_generation (p := 2) (A := Z) (H := D) hD
  by_contra hcon
  push Not at hcon
  apply hz
  apply hφ
  rw [map_one]
  refine MulEquiv.ext fun d => ?_
  have hle : (⨆ (B : Subgroup Z) (_ : B.index = 2), fixedPointSubgroup B D) ≤
      MonoidHom.eqLocus (φ z).toMonoidHom (MonoidHom.id D) := by
    refine iSup₂_le fun B hB e he => ?_
    exact hcon B hB e fun g hg => he ⟨g, hg⟩
  have hd : d ∈ (⨆ (B : Subgroup Z) (_ : B.index = 2), fixedPointSubgroup B D) := by
    rw [hgen]; exact Subgroup.mem_top d
  exact hle hd

theorem zpow_apply_mem {D : Type*} [Group D] {E : Subgroup D} (σ : MulAut D) {m : ℕ} (hm : 0 < m)
    (hσ : σ ^ m = 1) (hE : ∀ e ∈ E, σ e ∈ E) (k : ℤ) {e : D} (he : e ∈ E) : (σ ^ k) e ∈ E := by
  have hnat : ∀ n : ℕ, ∀ e ∈ E, (σ ^ n) e ∈ E := by
    intro n
    induction n with
    | zero => intro e he; simpa using he
    | succ n ih =>
      intro e he
      rw [pow_succ']
      exact hE _ (ih e he)
  have hord : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hσ
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hσ⟩)
  rw [← zpow_mod_orderOf]
  have h0 : 0 ≤ k % (orderOf σ : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
  rw [hn, zpow_natCast]
  exact hnat n e he

theorem exists_fixed_moved {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Type} [Group D] [Finite D]
    (hD : IsPGroup p D) {E : Subgroup D} (u v : MulAut D) (hu : u ^ 2 = 1) (hv : v ^ p = 1)
    (huv : Commute u v) (huE : ∀ e ∈ E, u e ∈ E) (hvE : ∀ e ∈ E, v e ∈ E)
    (hmove : ∃ e ∈ E, u e ≠ e) : ∃ f ∈ E, v f = f ∧ u f ≠ f := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  have huE' : ∀ g ∈ Subgroup.zpowers u, ∀ e ∈ E, g e ∈ E := by
    rintro _ ⟨k, rfl⟩ e he
    exact zpow_apply_mem u (m := 2) (by norm_num) hu huE k he
  have hvE' : ∀ g ∈ Subgroup.zpowers v, ∀ e ∈ E, g e ∈ E := by
    rintro _ ⟨k, rfl⟩ e he
    exact zpow_apply_mem v hp.pos hv hvE k he
  let α : Subgroup.zpowers u →* MulAut E :=
    PlaneSemidirect.restrictHom (Subgroup.zpowers u).subtype E (fun g e he => huE' g g.2 e he)
  let β' : Subgroup.zpowers v →* MulAut E :=
    PlaneSemidirect.restrictHom (Subgroup.zpowers v).subtype E (fun g e he => hvE' g g.2 e he)
  have hA : ¬ p ∣ Nat.card (Subgroup.zpowers u) := by
    rw [Nat.card_zpowers]
    intro h
    have h2 : p ∣ 2 := h.trans (orderOf_dvd_of_pow_eq_one hu)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hB : IsPGroup p (Subgroup.zpowers v) := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hv) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hall := CFSG.GroupTheory.thompson_A_times_B (p := p) (hD.to_subgroup E) hA hB α β'
    (fun a b => by
      refine MulEquiv.ext fun e => Subtype.ext ?_
      obtain ⟨i, hi⟩ := a.2
      obtain ⟨j, hj⟩ := b.2
      change (a : MulAut D) ((b : MulAut D) (e : D)) = (b : MulAut D) ((a : MulAut D) (e : D))
      rw [← hi, ← hj]
      exact congrArg (fun w : MulAut D => w (e : D)) ((huv.zpow_zpow i j).eq))
    (fun a r hr => by
      refine Subtype.ext ?_
      have hvr : v (r : D) = r := congrArg Subtype.val (hr ⟨v, Subgroup.mem_zpowers v⟩)
      have hur : u (r : D) = r := hcon r r.2 hvr
      obtain ⟨i, hi⟩ := a.2
      change (a : MulAut D) (r : D) = r
      rw [← hi]
      exact PlaneSemidirect.zpow_apply_eq_of_apply_eq (MonoidHom.id (MulAut D)) hur i)
  obtain ⟨e, he, hue⟩ := hmove
  have := congrArg Subtype.val (DFunLike.congr_fun (hall ⟨u, Subgroup.mem_zpowers u⟩) ⟨e, he⟩)
  exact hue this

theorem extraspecial_quotient_contradiction {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {D : Type}
    [Group D] [Finite D] (hDp : IsPGroup p D) (hDexp : ∀ x : D, x ^ p = 1)
    (hDcl : commutator D ≤ Subgroup.center D) {T : Type} [Group T] [Finite T] (ρ : T →* MulAut D)
    {N : Subgroup T} [N.Normal] {n : ℕ} (hn : 2 ≤ n) (hext : IsExtraspecialPGroup 2 (T ⧸ N))
    (hcard : Nat.card (T ⧸ N) = 2 ^ (1 + 2 * n)) {z : T} (hzc : z ∈ Subgroup.center T)
    (hz1 : z ∉ N) {P : Subgroup D} (hPinv : ∀ t : T, ∀ x ∈ P, ρ t x ∈ P)
    (hNtriv : ∀ t ∈ N, ∀ x ∈ P, ρ t x = x) (hzmove : ∃ x ∈ P, ρ z x ≠ x)
    (hPgen : P ≤ Subgroup.closure {w : D | ∃ x ∈ P, w = x⁻¹ * ρ z x})
    (hrank : ∀ t : T, t ∉ N → ∀ E : Subgroup D, IsElementaryAbelian p E → E ≤ P →
      (∀ e ∈ E, ρ t e = e) → ∀ k : ℕ, Nat.card E = p ^ k → k ≤ 3)
    (hPrank : ∀ E : Subgroup D, IsElementaryAbelian p E → E ≤ P → ∀ k : ℕ,
      Nat.card E = p ^ k → k ≤ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNρ : N ≤ (PlaneSemidirect.restrictHom ρ P hPinv).ker := fun t ht =>
    MonoidHom.mem_ker.mpr (MulEquiv.ext fun x => Subtype.ext (hNtriv t ht x x.2))
  let ρbar : T ⧸ N →* MulAut P := QuotientGroup.lift N (PlaneSemidirect.restrictHom ρ P hPinv) hNρ
  have hρbar : ∀ t : T, ρbar (t : T ⧸ N) = PlaneSemidirect.restrictHom ρ P hPinv t := fun t => rfl
  have hzbc : (z : T ⧸ N) ∈ Subgroup.center (T ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H q =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subgroup.mem_center_iff.mp hzc q)
  have hzb1 : (z : T ⧸ N) ≠ 1 := fun h => hz1 ((QuotientGroup.eq_one_iff z).mp h)
  have hcenter : Subgroup.center (T ⧸ N) = Subgroup.zpowers (z : T ⧸ N) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzbc) ?_
    rw [hext.2.2.2, Nat.card_zpowers]
    have h2 : orderOf (z : T ⧸ N) ∣ 2 := by
      have := orderOf_dvd_natCard (⟨_, hzbc⟩ : Subgroup.center (T ⧸ N))
      rwa [hext.2.2.2, Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hzb1
    · exact h.ge
  have hPp : IsPGroup p P := hDp.to_subgroup P
  have hPexp : ∀ x : P, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow]; exact hDexp x)
  have hPcl : commutator P ≤ Subgroup.center P := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_center_iff]
    intro w
    refine Subtype.ext ?_
    have hc : (⁅x, y⁆ : P).1 ∈ commutator D := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact Subgroup.mem_center_iff.mp (hDcl hc) w
  have hρbar_inj : Function.Injective ρbar := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    have hK : ρbar.ker ≠ ⊥ := fun h => hx1 ((Subgroup.mem_bot).mp (h ▸ hx))
    have h2 := (CFSG.SectionRank.Ccomm.normal_inf_center_card hext.1 hK).2
    have hcle : Nat.card (ρbar.ker ⊓ Subgroup.center (T ⧸ N) : Subgroup (T ⧸ N)) ≤
        Nat.card (Subgroup.center (T ⧸ N)) := Subgroup.card_le_of_le inf_le_right
    rw [hext.2.2.2] at hcle
    have heq : ρbar.ker ⊓ Subgroup.center (T ⧸ N) = Subgroup.center (T ⧸ N) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hext.2.2.2]; omega)
    have hzK : (z : T ⧸ N) ∈ ρbar.ker := by
      have : (z : T ⧸ N) ∈ ρbar.ker ⊓ Subgroup.center (T ⧸ N) := by
        rw [heq]
        exact hzbc
      exact this.1
    obtain ⟨y, hy, hyz⟩ := hzmove
    apply hyz
    have := congrArg (fun φ : MulAut P => (φ ⟨y, hy⟩ : P).1) (MonoidHom.mem_ker.mp hzK)
    exact this
  have hfix : ∀ s : T ⧸ N, s ≠ 1 →
      CFSG.pRank p (CFSG.RankThree.PartTwo.fixedSubgroupOf (ρbar s)) ≤ 3 := by
    intro s hs
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective s
    have htN : t ∉ N := fun h => hs ((QuotientGroup.eq_one_iff t).mpr h)
    refine PlaneCore.pRank_le_of_forall hp _ fun E hE hEF k hk => ?_
    have := hE
    refine hrank t htN (E.map P.subtype) (IsElementaryAbelian.map_subtype (H := E))
      (Subgroup.map_subtype_le E) ?_ k
      (by rw [Subgroup.card_map_of_injective P.subtype_injective, hk])
    rintro _ ⟨e, he, rfl⟩
    have := hEF he
    exact congrArg Subtype.val this
  obtain ⟨hn3, -, hmain⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.class_two_extraspecial_action_bound hp2 hPp hPexp
      hPcl hext hcard hcenter ρbar hρbar_inj hfix
  have hclos : Subgroup.closure {y : P | ∃ x : P, ∃ s ∈ Subgroup.center (T ⧸ N),
      y = x⁻¹ * ρbar s x} = ⊤ := by
    set S₀ : Set P := {y : P | ∃ x : P, ∃ s ∈ Subgroup.center (T ⧸ N), y = x⁻¹ * ρbar s x}
      with hS₀
    have h1 : P ≤ (Subgroup.closure S₀).map P.subtype := by
      calc P ≤ Subgroup.closure {w : D | ∃ x ∈ P, w = x⁻¹ * ρ z x} := hPgen
        _ ≤ Subgroup.closure (P.subtype '' S₀) := by
          refine Subgroup.closure_mono ?_
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩⁻¹ * ρbar (z : T ⧸ N) ⟨x, hx⟩, ⟨⟨x, hx⟩, (z : T ⧸ N), hzbc, rfl⟩, rfl⟩
        _ = (Subgroup.closure S₀).map P.subtype := (MonoidHom.map_closure P.subtype S₀).symm
    rw [eq_top_iff]
    intro y _
    obtain ⟨w, hw, hwy⟩ := h1 y.2
    have : w = y := Subtype.ext hwy
    exact this ▸ hw
  obtain ⟨s, hs, hso⟩ := CFSG.RankThree.GroupTheory.SteinbergBM.exists_noncentral_involution hext
    hcard hn hcenter
  obtain ⟨d, hd1, hd2, hd3⟩ := hmain hclos s hs hso
  have hPrank' : ∀ E : Subgroup P, IsElementaryAbelian p E → ∀ k : ℕ, Nat.card E = p ^ k →
      k ≤ 2 := fun E hE k hk => by
    have := hE
    exact hPrank (E.map P.subtype) (IsElementaryAbelian.map_subtype (H := E))
      (Subgroup.map_subtype_le E) k (by rw [Subgroup.card_map_of_injective P.subtype_injective, hk])
  have hle : p ^ (2 * d) ≤ p ^ 2 :=
    hd2 ▸ PlaneCore.card_frattini_quotient_le hp hPp hPexp hPcl hPrank'
  have h2d : 2 * d ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hd2' : 2 ≤ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ d := hd3
  omega

section InvCommutator

variable {p : ℕ} {D : Type*} [Group D]

@[expose] def invCommutator (u : MulAut D) (F : Subgroup D) : Subgroup D :=
  Subgroup.closure {w : D | ∃ x ∈ F, w = x⁻¹ * u x}

theorem mem_invCommutator {u : MulAut D} {F : Subgroup D} {x : D} (hx : x ∈ F) :
    x⁻¹ * u x ∈ invCommutator u F :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem invCommutator_le {u : MulAut D} {F : Subgroup D} (hF : ∀ x ∈ F, u x ∈ F) :
    invCommutator u F ≤ F := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  exact F.mul_mem (F.inv_mem hx) (hF x hx)

theorem apply_inv_mul_apply {u : MulAut D} (hu : u ^ 2 = 1) (x : D) :
    u (x⁻¹ * u x) = (x⁻¹ * u x)⁻¹ := by
  have h2 : u (u x) = x := by
    have := congrArg (fun w : MulAut D => w x) hu
    simpa [pow_two] using this
  rw [map_mul, map_inv, h2]
  group

theorem invCommutator_le_invCommutator_self (hp2 : p ≠ 2) (hp : p.Prime) (hexp : ∀ x : D, x ^ p = 1)
    {u : MulAut D} (hu : u ^ 2 = 1) {F : Subgroup D} :
    invCommutator u F ≤ invCommutator u (invCommutator u F) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  set w := x⁻¹ * u x with hw
  have hwP : w ∈ invCommutator u F := mem_invCommutator hx
  have huw : u w = w⁻¹ := apply_inv_mul_apply hu x
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    exact ⟨m, hm⟩
  have hpow : w = (w⁻¹ * u w) ^ m := by
    have h1 : w ^ (2 * m) * w = 1 := by rw [← pow_succ]; exact hm ▸ hexp w
    have h2 : w⁻¹ * u w = (w ^ 2)⁻¹ := by rw [huw]; group
    rw [h2, inv_pow, ← pow_mul]
    exact eq_inv_of_mul_eq_one_right h1
  have h := (invCommutator u (invCommutator u F)).pow_mem (mem_invCommutator hwP) m
  rwa [← hpow] at h

theorem exists_apply_ne_of_invCommutator (hp2 : p ≠ 2) (hp : p.Prime) (hexp : ∀ x : D, x ^ p = 1)
    {u : MulAut D} (hu : u ^ 2 = 1) {F : Subgroup D} {f : D} (hf : f ∈ F) (hmove : u f ≠ f) :
    ∃ x ∈ invCommutator u F, u x ≠ x := by
  refine ⟨f⁻¹ * u f, mem_invCommutator hf, fun h => hmove ?_⟩
  have h1 := apply_inv_mul_apply hu f
  rw [h] at h1
  have h2 : (f⁻¹ * u f) ^ 2 = 1 := by
    rw [pow_two]
    calc f⁻¹ * u f * (f⁻¹ * u f) = (f⁻¹ * u f) * (f⁻¹ * u f)⁻¹⁻¹ := by rw [inv_inv]
      _ = 1 := by rw [← h1]; exact mul_inv_cancel _
  have h3 : f⁻¹ * u f = 1 := by
    have h4 := pow_gcd_eq_one.mpr ⟨h2, hexp (f⁻¹ * u f)⟩
    rwa [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one, pow_one] at h4
  exact (inv_mul_eq_one.mp h3).symm

theorem invCommutator_invariant {u τ : MulAut D} (huτ : Commute u τ) {F : Subgroup D}
    (hF : ∀ x ∈ F, τ x ∈ F) {x : D} (hx : x ∈ invCommutator u F) : τ x ∈ invCommutator u F := by
  have hle : invCommutator u F ≤ (invCommutator u F).comap τ.toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    change τ (y⁻¹ * u y) ∈ invCommutator u F
    have h : τ (u y) = u (τ y) := (congrArg (fun w : MulAut D => w y) huτ.eq).symm
    have : τ (y⁻¹ * u y) = (τ y)⁻¹ * u (τ y) := by rw [map_mul, map_inv, h]
    rw [this]
    exact mem_invCommutator (hF y hy)
  exact hle hx

end InvCommutator

theorem hyperplane_contradiction {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {B S D : Type} [Group B]
    [Group S] [Group D] [Finite B] [Finite S] [Finite D] [MulDistribMulAction B S]
    (hB : IsElementaryAbelian p B) (hS : IsPGroup 2 S) (hDp : IsPGroup p D)
    (hDexp : ∀ x : D, x ^ p = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D) (hβ : Function.Injective β)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3)
    {S₁ Z₁ : Subgroup S} {n : ℕ} (hsp : PlaneFactorCases.SpecialData (B := B) S₁ Z₁ n)
    {b₁ : B} (hb₁ : b₁ ≠ 1) (hb₁S₁ : ∀ s ∈ S₁, b₁ • s = s) {Z : Subgroup S} (hZ₁ : Z₁ ≤ Z)
    (hZel : IsElementaryAbelian 2 Z) (hZfix : ActionCentralizes B Z)
    (hZcent : ∀ z ∈ Z, ∀ s ∈ S₁, z * s = s * z) (hZ4 : 4 ≤ Nat.card Z) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hZel
  let ρ : S →* MulAut D := β.comp SemidirectProduct.inl
  let σ : B →* MulAut D := β.comp SemidirectProduct.inr
  have hρinj : Function.Injective ρ := hβ.comp SemidirectProduct.inl_injective
  have hcompat : ∀ (b : B) (s : S), σ b * ρ s * (σ b)⁻¹ = ρ (b • s) := by
    intro b s
    have h := SemidirectProduct.inl_aut (φ := MulDistribMulAction.toMulAut B S) b s
    change SemidirectProduct.inl (b • s) = _ at h
    show β (SemidirectProduct.inr b) * β (SemidirectProduct.inl s) *
      (β (SemidirectProduct.inr b))⁻¹ = β (SemidirectProduct.inl (b • s))
    rw [h]
    simp only [map_mul, map_inv]
  obtain ⟨⟨z₁, hz₁Z₁⟩, hz₁1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hsp.ne_bot
  have hz₁1 : z₁ ≠ 1 := fun h => hz₁1' (Subtype.ext h)
  have hz₁Z : z₁ ∈ Z := hZ₁ hz₁Z₁
  have hz₁S₁ : z₁ ∈ S₁ := hsp.le hz₁Z₁
  have hz₁sq : z₁ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) z₁ hz₁Z
  have hDodd : ¬ 2 ∣ Nat.card D := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  obtain ⟨Z₀', hZ₀'idx, e, he₀, hmove⟩ := exists_hyperplane_moving hDodd (ρ.comp Z.subtype)
    (hρinj.comp Z.subtype_injective) (z := ⟨z₁, hz₁Z⟩) (fun h => hz₁1 (congrArg Subtype.val h))
  set Z₀ : Subgroup S := Z₀'.map Z.subtype with hZ₀
  have hZ₀Z : Z₀ ≤ Z := Subgroup.map_subtype_le _
  have hz₁Z₀ : z₁ ∉ Z₀ := by
    rintro ⟨g, hg, hgz⟩
    have hg' : g = ⟨z₁, hz₁Z⟩ := Subtype.ext hgz
    subst hg'
    exact hmove (he₀ _ hg)
  have hZcard : Nat.card Z = 2 * Nat.card Z₀ := by
    have h1 := Subgroup.card_mul_index Z₀'
    rw [hZ₀'idx] at h1
    rw [← h1, hZ₀, Subgroup.card_map_of_injective Z.subtype_injective, mul_comm]
  have hZ₀ne : Z₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    omega
  let E : Subgroup D :=
    { carrier := {d | ∀ u ∈ Z₀, ρ u d = d}
      mul_mem' := fun {a b} ha hb u hu => by rw [map_mul, ha u hu, hb u hu]
      one_mem' := fun u hu => map_one _
      inv_mem' := fun {a} ha u hu => by rw [map_inv, ha u hu] }
  have hmemE : ∀ d : D, d ∈ E ↔ ∀ u ∈ Z₀, ρ u d = d := fun d => Iff.rfl
  have heE : e ∈ E := fun u hu => by
    obtain ⟨g, hg, rfl⟩ := hu
    exact he₀ g hg
  have hρE : ∀ s ∈ S₁, ∀ d ∈ E, ρ s d ∈ E := by
    intro s hs d hd u hu
    have hcomm : u * s = s * u := hZcent u (hZ₀Z hu) s hs
    have h1 : ρ u (ρ s d) = ρ s (ρ u d) := by
      have := congrArg (fun w : S => ρ w d) hcomm
      simpa only [map_mul, MulAut.mul_apply] using this
    rw [h1, hd u hu]
  have hσE : ∀ b : B, ∀ d ∈ E, σ b d ∈ E := by
    intro b d hd u hu
    have hfix : b • u = u := hZfix b u (hZ₀Z hu)
    have h1 : ρ u (σ b d) = σ b (ρ u d) := by
      have h2 := hcompat b u
      rw [hfix] at h2
      have h3 : σ b * ρ u = ρ u * σ b := by
        calc σ b * ρ u = σ b * ρ u * (σ b)⁻¹ * σ b := by group
          _ = ρ u * σ b := by rw [h2]
      have := congrArg (fun w : MulAut D => w d) h3
      exact this.symm
    rw [h1, hd u hu]
  have hu2 : (ρ z₁) ^ 2 = 1 := by rw [← map_pow, hz₁sq, map_one]
  have hb₁p : b₁ ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B) b₁
  have hv : (σ b₁) ^ p = 1 := by rw [← map_pow, hb₁p, map_one]
  have huv : Commute (ρ z₁) (σ b₁) := by
    have h2 := hcompat b₁ z₁
    rw [hb₁S₁ z₁ hz₁S₁] at h2
    show ρ z₁ * σ b₁ = σ b₁ * ρ z₁
    calc ρ z₁ * σ b₁ = σ b₁ * ρ z₁ * (σ b₁)⁻¹ * σ b₁ := by rw [h2]
      _ = σ b₁ * ρ z₁ := by group
  obtain ⟨f, hfE, hfb, hfmove⟩ := exists_fixed_moved hp hp2 hDp (E := E) (ρ z₁) (σ b₁) hu2 hv
    huv (hρE z₁ hz₁S₁) (hσE b₁) ⟨e, heE, hmove⟩
  let F : Subgroup D := E ⊓ CFSG.RankThree.PartTwo.fixedSubgroupOf (σ b₁)
  have hmemF : ∀ d : D, d ∈ F ↔ d ∈ E ∧ σ b₁ d = d := fun d => Iff.rfl
  have hfF : f ∈ F := ⟨hfE, hfb⟩
  have hFz : ∀ x ∈ F, ρ z₁ x ∈ F := by
    intro x hx
    refine ⟨hρE z₁ hz₁S₁ x hx.1, ?_⟩
    have h2 := hcompat b₁ z₁
    rw [hb₁S₁ z₁ hz₁S₁] at h2
    have h3 : σ b₁ (ρ z₁ x) = ρ z₁ (σ b₁ x) := by
      have h4 : σ b₁ * ρ z₁ = ρ z₁ * σ b₁ := by
        calc σ b₁ * ρ z₁ = σ b₁ * ρ z₁ * (σ b₁)⁻¹ * σ b₁ := by group
          _ = ρ z₁ * σ b₁ := by rw [h2]
      exact congrArg (fun w : MulAut D => w x) h4
    have hx2 : σ b₁ x = x := hx.2
    show σ b₁ (ρ z₁ x) = ρ z₁ x
    rw [h3, hx2]
  have hFs : ∀ s ∈ S₁, ∀ x ∈ F, ρ s x ∈ F := by
    intro s hs x hx
    refine ⟨hρE s hs x hx.1, ?_⟩
    have h2 := hcompat b₁ s
    rw [hb₁S₁ s hs] at h2
    have h3 : σ b₁ (ρ s x) = ρ s (σ b₁ x) := by
      have h4 : σ b₁ * ρ s = ρ s * σ b₁ := by
        calc σ b₁ * ρ s = σ b₁ * ρ s * (σ b₁)⁻¹ * σ b₁ := by group
          _ = ρ s * σ b₁ := by rw [h2]
      exact congrArg (fun w : MulAut D => w x) h4
    have hx2 : σ b₁ x = x := hx.2
    show σ b₁ (ρ s x) = ρ s x
    rw [h3, hx2]
  set P : Subgroup D := invCommutator (ρ z₁) F with hP
  have hPF : P ≤ F := invCommutator_le hFz
  have hPE : ∀ x ∈ P, x ∈ E := fun x hx => (hPF hx).1
  have hPinv : ∀ t : S₁, ∀ x ∈ P, (ρ.comp S₁.subtype) t x ∈ P := by
    intro t x hx
    refine invCommutator_invariant (u := ρ z₁) (τ := ρ t) ?_ (hFs t t.2) hx
    show ρ z₁ * ρ t = ρ t * ρ z₁
    rw [← map_mul, ← map_mul, hsp.central z₁ hz₁Z₁ t t.2]
  have hNle : Z₁ ⊓ Z₀ ≤ S₁ := inf_le_left.trans hsp.le
  let N : Subgroup S₁ := (Z₁ ⊓ Z₀).subgroupOf S₁
  have hNcenter : N ≤ Subgroup.center S₁ := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hsp.central (t : S) (Subgroup.mem_subgroupOf.mp ht).1 (g : S) g.2).symm
  have : N.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hNcenter hn) g
    rwa [h, mul_inv_cancel_right]⟩
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsupcard : Nat.card (Z₁ ⊔ Z₀ : Subgroup S) = 2 * Nat.card Z₀ := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le (le_sup_right : Z₀ ≤ Z₁ ⊔ Z₀)
    have hdvd : Nat.card (Z₁ ⊔ Z₀ : Subgroup S) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le (sup_le hZ₁ hZ₀Z)
    rw [hc, hZcard, mul_comm 2] at hdvd
    have hpos : 0 < Nat.card Z₀ := Nat.card_pos
    have hc2 : c ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with h1 | h2
    · exfalso
      rw [h1, mul_one] at hc
      have heq : Z₀ = Z₁ ⊔ Z₀ := Subgroup.eq_of_le_of_card_ge le_sup_right hc.le
      exact hz₁Z₀ (heq ▸ Subgroup.mem_sup_left hz₁Z₁)
    · rw [hc, h2, mul_comm]
  have hZ₁card : Nat.card Z₁ = 2 * Nat.card (Z₁ ⊓ Z₀ : Subgroup S) := by
    have h := PlaneCommuting.card_sup_mul_card_inf (X := Z₁) (Y := Z₀) fun x hx y hy =>
      hZcomm x (hZ₁ hx) y (hZ₀Z hy)
    rw [hsupcard, mul_assoc, mul_comm (Nat.card Z₀)] at h
    have hpos : 0 < Nat.card Z₀ := Nat.card_pos
    have h' : Nat.card Z₁ * Nat.card Z₀ = (2 * Nat.card (Z₁ ⊓ Z₀ : Subgroup S)) * Nat.card Z₀ := by
      rw [← h]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  have hNcard : Nat.card (Subgroup.center S₁) = 2 * Nat.card N := by
    rw [hsp.card_center, hZ₁card]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv).symm
  have hquot := hsp.quotient N hNcenter hNcard
  have hzc : (⟨z₁, hz₁S₁⟩ : S₁) ∈ Subgroup.center S₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hsp.central z₁ hz₁Z₁ (g : S) g.2).symm
  have hz1N : (⟨z₁, hz₁S₁⟩ : S₁) ∉ N := fun h => hz₁Z₀ (Subgroup.mem_subgroupOf.mp h).2
  have hNtriv : ∀ t ∈ N, ∀ x ∈ P, (ρ.comp S₁.subtype) t x = x := by
    intro t ht x hx
    exact hPE x hx (t : S) (Subgroup.mem_subgroupOf.mp ht).2
  have hzmove : ∃ x ∈ P, (ρ.comp S₁.subtype) ⟨z₁, hz₁S₁⟩ x ≠ x :=
    exists_apply_ne_of_invCommutator hp2 hp hDexp hu2 hfF hfmove
  have hPgen : P ≤ Subgroup.closure {w : D | ∃ x ∈ P,
      w = x⁻¹ * (ρ.comp S₁.subtype) ⟨z₁, hz₁S₁⟩ x} :=
    invCommutator_le_invCommutator_self hp2 hp hDexp hu2
  have hrank : ∀ t : S₁, t ∉ N → ∀ E' : Subgroup D, IsElementaryAbelian p E' → E' ≤ P →
      (∀ e ∈ E', (ρ.comp S₁.subtype) t e = e) → ∀ k : ℕ, Nat.card E' = p ^ k → k ≤ 3 := by
    intro t htN E' hE' hE'P hfix k hk
    have hts : (t : S) ≠ 1 := by
      intro h
      apply htN
      have : t = 1 := Subtype.ext h
      rw [this]
      exact N.one_mem
    exact (PlaneSemidirect.le_evenRank_of_fixed β hp hp2 hS hts hE' hfix hk).trans he
  have hPrank : ∀ E' : Subgroup D, IsElementaryAbelian p E' → E' ≤ P → ∀ k : ℕ,
      Nat.card E' = p ^ k → k ≤ 2 := by
    intro E' hE' hE'P k hk
    have h := PlaneSemidirect.succ_le_evenRank_of_fixed β hp hp2 hS hZ₀ne hE'
      (fun u hu e he' => hPE e (hE'P he') u hu) hb₁ hb₁p (fun e he' => (hPF (hE'P he')).2)
      (fun u hu => hZfix b₁ u (hZ₀Z hu)) hk
    have := h.trans he
    omega
  exact extraspecial_quotient_contradiction hp hp3 hDp hDexp hDcl (ρ.comp S₁.subtype) hsp.two_le
    hquot.1 hquot.2 hzc hz1N hPinv hNtriv hzmove hPgen hrank hPrank

end PlaneHyperplane

end CFSG.RankThree.PartOne
