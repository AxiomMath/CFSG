module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.SmithD321Q

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
  CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem eq_one_of_mem_commV_zpowers (hW : ∀ w : W, w ^ 2 = 1) {d : MulAut W} (hd5 : d ^ 5 = 1)
    {r : W} (hr : r ∈ commV (Subgroup.zpowers d)) (hdr : d r = r) : r = 1 := by
  let N : W →* W :=
    { toFun := fun w => w * d w * (d ^ 2) w * (d ^ 3) w * (d ^ 4) w
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        ac_rfl }
  have hN : ∀ w, N w = w * d w * (d ^ 2) w * (d ^ 3) w * (d ^ 4) w := fun _ => rfl
  let K : Subgroup (MulAut W) :=
    { carrier := {g | ∀ w, N (g w) = N w}
      one_mem' := fun w => rfl
      mul_mem' := by
        intro a b ha hb w
        show N (a (b w)) = N w
        rw [ha, hb]
      inv_mem' := by
        intro a ha w
        have h1 := ha (a⁻¹ w)
        rw [MulAut.apply_inv_self] at h1
        exact h1.symm }
  have hdK : d ∈ K := by
    intro w
    show N (d w) = N w
    have e2 : d (d w) = (d ^ 2) w := by rw [pow_two, MulAut.mul_apply]
    have e3 : (d ^ 2) (d w) = (d ^ 3) w := by rw [pow_succ d 2, MulAut.mul_apply]
    have e4 : (d ^ 3) (d w) = (d ^ 4) w := by rw [pow_succ d 3, MulAut.mul_apply]
    have e5 : (d ^ 4) (d w) = w := by
      rw [← MulAut.mul_apply, ← pow_succ, hd5, MulAut.one_apply]
    rw [hN, hN, e2, e3, e4, e5]
    ac_rfl
  have hzK : Subgroup.zpowers d ≤ K := Subgroup.zpowers_le.2 hdK
  have hNr : N r = 1 := by
    have hle : commV (Subgroup.zpowers d) ≤ N.ker := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨g, hg, w, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hzK hg w, mul_inv_cancel]
    exact hle hr
  have hpow : ∀ n : ℕ, (d ^ n) r = r := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hdr, ih]
  have hr5 : N r = r := by
    rw [hN, hdr, hpow 2, hpow 3, hpow 4]
    have h2 := hW r
    calc r * r * r * r * r = r * (r * r) * (r * r) := by simp only [mul_assoc]
      _ = r := by rw [← pow_two, h2, mul_one, mul_one]
  rw [← hr5, hNr]

omit [Finite W] in
theorem mem_stabSub_of_inv {U : Subgroup W} {g : MulAut W} (h : ∀ u ∈ U, g u ∈ U)
    (h' : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U :=
  CFSG.Quasithin.S1417.mem_stabSub_of_forall h h'

theorem isIrrSec_of_order_five (hW : ∀ w : W, w ^ 2 = 1) {R : Subgroup W} (hR : rk ↥R = 4)
    {δ : MulAut ↥R} (hδ5 : δ ^ 5 = 1) (hfix : ∀ r : ↥R, δ r = r → r = 1) :
    XMod.IsIrrSec ↥(Subgroup.zpowers δ) (⊥ : Subgroup ↥R) ⊤ := by
  classical
  have hR2 : ∀ q : ↥R, q ^ 2 = 1 := fun q => Subtype.ext (by simpa using hW (q : W))
  have hcardR : Nat.card ↥(⊤ : Subgroup ↥R) = 2 ^ 4 := by
    rw [Subgroup.card_top, Nat.card_congr (Equiv.refl ↥R)]
    have h1 := card_eq_two_pow hW R
    rw [hR] at h1
    exact h1
  refine ⟨?_, fun J hJ _ _ => ?_⟩
  · refine bot_lt_iff_ne_bot.2 fun h => ?_
    have h1 : Nat.card ↥(⊤ : Subgroup ↥R) = 1 := by rw [h, Subgroup.card_bot]
    rw [hcardR] at h1
    norm_num at h1
  ·
    let f : Function.End ↥J := fun j => ⟨δ j, hJ ⟨δ, Subgroup.mem_zpowers δ⟩ j j.2⟩
    have hf : ∀ n : ℕ, ∀ j : ↥J, ((f ^ n) j : ↥R) = (δ ^ n) j := by
      intro n
      induction n with
      | zero => intro j; rfl
      | succ n ih =>
        intro j
        have e : (f ^ (n + 1)) j = f ((f ^ n) j) := by rw [pow_succ']; rfl
        rw [e, pow_succ', MulAut.mul_apply, ← ih]
    have hf5 : f ^ 5 ^ 1 = 1 := by
      funext j
      apply Subtype.ext
      rw [pow_one, hf, hδ5]
      rfl
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : Fintype ↥J := Fintype.ofFinite _
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf5
    have hfixpts : Nat.card ↑(Function.fixedPoints f) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      have key : ∀ x : ↑(Function.fixedPoints f), x = ⟨1, Subtype.ext (map_one δ)⟩ := by
        rintro ⟨j, hj⟩
        apply Subtype.ext
        have hj' : δ (j : ↥R) = j := congrArg Subtype.val hj
        exact Subtype.ext (hfix (j : ↥R) hj')
      exact ⟨⟨fun a b => by rw [key a, key b]⟩, ⟨⟨1, Subtype.ext (map_one δ)⟩⟩⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hfixpts] at hmod
    have hcardJ : Nat.card ↥J = 2 ^ rk ↥J := card_eq_two_pow hR2 J
    have hdvd : 2 ^ rk ↥J ∣ 2 ^ 4 := by
      rw [← hcardJ, ← hcardR, Subgroup.card_top]
      exact Subgroup.card_subgroup_dvd_card J
    have hk : rk ↥J ≤ 4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    rw [hcardJ] at hmod
    have hcases : rk ↥J = 0 ∨ rk ↥J = 4 := by
      interval_cases h : rk ↥J
      · exact Or.inl rfl
      · exact absurd hmod (by decide)
      · exact absurd hmod (by decide)
      · exact absurd hmod (by decide)
      · exact Or.inr rfl
    rcases hcases with h0 | h4
    · left
      have h1 : Nat.card ↥J = 1 := by rw [card_eq_two_pow hR2 J, h0, pow_zero]
      exact Subgroup.eq_bot_of_card_eq J h1
    · right
      have h1 : Nat.card ↥J = Nat.card ↥(⊤ : Subgroup ↥R) := by
        rw [card_eq_two_pow hR2 J, h4, hcardR]
      exact Subgroup.eq_top_of_card_eq J (h1.trans (by rw [Subgroup.card_top]))

private theorem eq_one_of_mem_isPGroup {M X N : Subgroup (MulAut W)} (hX : IsSimpleGroup ↥X)
    (hXc : X ∈ cComp M) {p : ℕ} [Fact p.Prime]
    (hNn : M ≤ Subgroup.normalizer (N : Set (MulAut W))) (hN : IsPGroup p ↥N) {x : MulAut W}
    (hxX : x ∈ X) (hxN : x ∈ N) : x = 1 := by
  have hXM : X ≤ M := le_of_mem_cComp hXc
  have hnorm : (N.subgroupOf X).Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.1 (hNn (hXM g.2)) _).1 hn⟩
  rcases hX.eq_bot_or_eq_top_of_normal (N.subgroupOf X) with h | h
  · have hmem : (⟨x, hxX⟩ : ↥X) ∈ N.subgroupOf X := hxN
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hXN : X ≤ N := fun y hy => by
      have : (⟨y, hy⟩ : ↥X) ∈ N.subgroupOf X := h ▸ Subgroup.mem_top _
      exact this
    have : Group.IsNilpotent ↥X := (hN.to_le hXN).isNilpotent
    exact not_isSolvable_of_mem_cComp hXc inferInstance

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem commute_of_isPGroup {N : Subgroup (MulAut W)} {p : ℕ} [Fact p.Prime] (hNM : N ≤ M)
    (hNn : M ≤ Subgroup.normalizer (N : Set (MulAut W))) (hN : IsPGroup p ↥N) :
    ∀ x ∈ N, ∀ m ∈ Mp, x * m = m * x := by
  have hconjN : ∀ g ∈ M, ∀ y ∈ N, g * y * g⁻¹ ∈ N := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.1 (hNn hg) y).1 hy
  have hNMp : ∀ y ∈ N, y ∈ Mp → y = 1 := by
    intro y hyN hyMp
    have key : ∀ {X : Subgroup (MulAut W)}, IsSimpleGroup ↥X → X ∈ cComp M →
        (∀ l ∈ X, y * l * y⁻¹ ∈ X) → ∀ l ∈ X, y * l = l * y := by
      intro X hX hXc hXn l hl
      have hXM := le_of_mem_cComp hXc
      have hc1 : y * l * y⁻¹ * l⁻¹ ∈ X := X.mul_mem (hXn l hl) (X.inv_mem hl)
      have hc2 : y * l * y⁻¹ * l⁻¹ ∈ N := by
        have : y * (l * y⁻¹ * l⁻¹) ∈ N := N.mul_mem hyN (hconjN l (hXM hl) _ (N.inv_mem hyN))
        simpa [mul_assoc] using this
      have h1 := eq_one_of_mem_isPGroup hX hXc hNn hN hc1 hc2
      calc y * l = y * l * y⁻¹ * l⁻¹ * l * y := by group
        _ = l * y := by rw [h1]; group
    have hL := key hB.hsimp hB.hD.hyp.comp (fun l hl => hB.conj_mem_L hyMp hl)
    have hLt := key hB.Lt_simp hB.Lt_mem_cComp (fun l hl => hB.conj_mem_Lt hyMp hl)
    refine hB.eq_one_of_mem_Mp hyMp fun m hm => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hm
    rw [← mul_assoc, hL a ha, mul_assoc, hLt b hb, mul_assoc]
  intro x hx m hm
  have hc1 : x * m * x⁻¹ * m⁻¹ ∈ N := by
    have : x * (m * x⁻¹ * m⁻¹) ∈ N :=
      N.mul_mem hx (hconjN m (hB.Mp_le hm) _ (N.inv_mem hx))
    simpa [mul_assoc] using this
  have hc2 : x * m * x⁻¹ * m⁻¹ ∈ Mp := Mp.mul_mem (hB.conj_mem_Mp (hNM hx) hm) (Mp.inv_mem hm)
  have h1 := hNMp _ hc1 hc2
  calc x * m = x * m * x⁻¹ * m⁻¹ * m * x := by group
    _ = m * x := by rw [h1]; group

theorem commutator_pCoreOf_eq_bot {A : Subgroup (MulAut W)} {r : ℚ}
    (hr : qhatOf M = (r : WithTop ℚ)) (hA : A ∈ QhatStar M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ⁅CFSG.Open.pCoreOf p M, A⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hD0
  obtain ⟨h35, h5, -⟩ := D2_13 hB.exp hr hA (p := p) (by omega) rfl hD0
  have hp5' : p = 5 := by rcases h35 with h | h <;> omega
  obtain ⟨-, -, hcard, hcyc, -, hrk⟩ := h5 hp5'
  subst hp5'
  set P := CFSG.Open.pCoreOf 5 M with hPdef
  set D := ⁅P, A⁆ with hDdef
  have hAM : A ≤ M := QhatStar_le hA
  have hPM : P ≤ M := pCoreOf_le 5 M
  have hPn : M ≤ Subgroup.normalizer (P : Set (MulAut W)) := le_normalizer_pCoreOf 5 M
  have hDP : D ≤ P := by
    rw [hDdef, Subgroup.commutator_le]
    intro g hg a ha
    rw [commutatorElement_def]
    have : g * (a * g⁻¹ * a⁻¹) ∈ P :=
      P.mul_mem hg ((Subgroup.mem_normalizer_iff.1 (hPn (hAM ha)) _).1 (P.inv_mem hg))
    simpa [mul_assoc] using this
  have hcomm := hB.commute_of_isPGroup hPM hPn (pCoreOf_isPGroup 5 M)
  obtain ⟨d, hd⟩ := hcyc
  have hord : orderOf d = 5 := by rw [orderOf_eq_card_of_forall_mem_zpowers hd, hcard]
  have hdD : (d : MulAut W) ∈ D := d.2
  have hd5 : (d : MulAut W) ^ 5 = 1 := by
    have := pow_orderOf_eq_one d
    rw [hord] at this
    exact congrArg Subtype.val this
  have hd1 : (d : MulAut W) ≠ 1 := by
    intro h
    have : d = 1 := Subtype.ext h
    rw [this, orderOf_one] at hord
    norm_num at hord
  have hDz : D = Subgroup.zpowers (d : MulAut W) := by
    refine le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.2 hdD)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hd ⟨g, hg⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  set R := commV D with hRdef
  have hRD : ∀ g ∈ D, ∀ r ∈ R, g r ∈ R := by
    intro g hg r hr
    have e : g r = (g r * r⁻¹) * r := by group
    rw [e]
    exact R.mul_mem (Subgroup.subset_closure ⟨g, hg, r, rfl⟩) hr
  have hRMp : ∀ m ∈ Mp, ∀ r ∈ R, m r ∈ R := by
    intro m hm r hr
    have hle : R ≤ R.comap m.toMonoidHom := by
      rw [hRdef, commV, Subgroup.closure_le]
      rintro _ ⟨g, hg, w, rfl⟩
      show m (g w * w⁻¹) ∈ commV D
      have hgm : m * g = g * m := (hcomm g (hDP hg) m hm).symm
      have e : m (g w * w⁻¹) = g (m w) * (m w)⁻¹ := by
        rw [map_mul, map_inv, ← MulAut.mul_apply, hgm, MulAut.mul_apply]
      rw [e]
      exact Subgroup.subset_closure ⟨g, hg, m w, rfl⟩
    exact hle hr
  have hdst : (d : MulAut W) ∈ stabSub R := mem_stabSub_of_inv (hRD _ hdD) (hRD _ (D.inv_mem hdD))
  set δ : MulAut ↥R := resHom R ⟨d, hdst⟩ with hδdef
  have hδ5 : δ ^ 5 = 1 := by
    rw [hδdef, ← map_pow]
    have : (⟨(d : MulAut W), hdst⟩ : ↥(stabSub R)) ^ 5 = 1 := Subtype.ext (by simpa using hd5)
    rw [this, map_one]
  have hδfix : ∀ r : ↥R, δ r = r → r = 1 := by
    intro r hr
    apply Subtype.ext
    have h1 : (d : MulAut W) r = r := congrArg Subtype.val hr
    have hrz : (r : W) ∈ commV (Subgroup.zpowers (d : MulAut W)) := by rw [← hDz]; exact r.2
    exact eq_one_of_mem_commV_zpowers hB.exp hd5 hrz h1
  have hsimple := isIrrSec_of_order_five hB.exp hrk hδ5 hδfix
  have hcyc' : IsCyclic ↥(XMod.eqvAut ↥(Subgroup.zpowers δ) ↥R) :=
    XMod.isCyclic_of_injective_eqvEnd hsimple (XMod.toEqvEnd _ _) XMod.toEqvEnd_injective
  have hmst : ∀ m ∈ Mp, m ∈ stabSub R := fun m hm =>
    mem_stabSub_of_inv (hRMp m hm) (hRMp _ (Mp.inv_mem hm))
  have hmeqv : ∀ m (hm : m ∈ Mp),
      resHom R ⟨m, hmst m hm⟩ ∈ XMod.eqvAut ↥(Subgroup.zpowers δ) ↥R := by
    intro m hm
    have hc : δ ∈ Subgroup.centralizer {resHom R ⟨m, hmst m hm⟩} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      ext r
      show (d : MulAut W) (m r) = m ((d : MulAut W) r)
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm d (hDP hdD) m hm]
    have hz : Subgroup.zpowers δ ≤ Subgroup.centralizer {resHom R ⟨m, hmst m hm⟩} :=
      Subgroup.zpowers_le.2 hc
    intro a q
    have ha := hz a.2
    rw [Subgroup.mem_centralizer_singleton_iff] at ha
    show resHom R ⟨m, hmst m hm⟩ ((a : MulAut ↥R) q) =
      (a : MulAut ↥R) (resHom R ⟨m, hmst m hm⟩ q)
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ha]
  have hmcomm : ∀ m₁ ∈ Mp, ∀ m₂ ∈ Mp, ∀ r ∈ R, m₁ (m₂ r) = m₂ (m₁ r) := by
    intro m₁ hm₁ m₂ hm₂ r hr
    let _ := IsCyclic.commGroup (α := ↥(XMod.eqvAut ↥(Subgroup.zpowers δ) ↥R))
    have h := congrArg Subtype.val (mul_comm
      (⟨_, hmeqv m₁ hm₁⟩ : ↥(XMod.eqvAut ↥(Subgroup.zpowers δ) ↥R)) ⟨_, hmeqv m₂ hm₂⟩)
    have h2 := congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : W)) h
    simpa [MulAut.mul_apply, resHom_apply] using h2
  have hMpcent : Mp ≤ centSub R := by
    rw [← hB.Mp_perfect, Subgroup.commutator_le]
    intro m₁ hm₁ m₂ hm₂
    rw [mem_centSub]
    intro r hr
    have hs : m₂⁻¹ r ∈ R := hRMp _ (Mp.inv_mem hm₂) r hr
    have h1 := hmcomm m₂ hm₂ _ (Mp.inv_mem hm₁) _ hs
    rw [commutatorElement_def]
    simp only [MulAut.mul_apply]
    rw [h1, MulAut.apply_inv_self, MulAut.apply_inv_self]
  have hdfix : ∀ w : W, (d : MulAut W) w * w⁻¹ ∈ fixV Mp := by
    intro w
    refine mem_fixV.2 fun m hm => ?_
    exact (mem_centSub.1 (hMpcent hm)) _ (Subgroup.subset_closure ⟨d, hdD, w, rfl⟩)
  exact hd1 (eq_one_of_fix_quot hB.commV_eq_top (fun l hl => hcomm _ (hDP hdD) l hl) hdfix)

end D321Base

theorem D321Sit.commutator_pCoreOf_eq_bot {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : ⁅CFSG.Open.pCoreOf p M, A⁆ = ⊥ :=
  hS.toD321Base.commutator_pCoreOf_eq_bot hS.hr hS.hAQ hp hp5

section Cover

open CFSG.Open CFSG.QuasithinUnique.Vol2Native

private theorem ker_le_frattini_of_forall_map_eq_top_odd {T Q : Type*} [Group T] [Group Q]
    (ψ : T →* Q) (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup T, H.map ψ = ⊤ → H = ⊤) : ψ.ker ≤ frattini T := by
  refine le_iInf₂ fun H hH => ?_
  have hH' : IsCoatom H := hH
  by_contra hKH
  have hsup : H ⊔ ψ.ker = ⊤ := hH'.2 _ (left_lt_sup.mpr hKH)
  refine hH'.1 (hmin H (eq_top_iff.mpr fun q _ => ?_))
  obtain ⟨t, rfl⟩ := hψ q
  have ht : t ∈ H ⊔ ψ.ker := hsup ▸ Subgroup.mem_top t
  rw [← Subgroup.comap_map_eq] at ht
  exact ht

private theorem isNilpotent_ker_lift_of_le_frattini_odd {T Q : Type*} [Group T] [Finite T]
    [Group Q] (ψ : T →* Q) (P : Subgroup T) [P.Normal] (hP : P ≤ ψ.ker)
    (hψ : ψ.ker ≤ frattini T) : Group.IsNilpotent (QuotientGroup.lift P ψ hP).ker := by
  have : Group.IsNilpotent ↥(frattini T) := frattini_nilpotent
  have : Group.IsNilpotent ψ.ker :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hψ)
  rw [QuotientGroup.ker_lift]
  exact Group.nilpotent_of_surjective ((QuotientGroup.mk' P).subgroupMap ψ.ker)
    (MonoidHom.subgroupMap_surjective _ _)

private theorem odd_card_of_isNilpotent_of_pCore_eq_bot {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] (hO2 : CFSG.pCore 2 G = ⊥) :
    Odd (Nat.card N) := by
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
  obtain ⟨P⟩ : Nonempty (Sylow 2 N) := inferInstance
  have := Sylow.characteristic_of_normal P inferInstance
  have hle : (P : Subgroup N).map N.subtype ≤ CFSG.pCore 2 G :=
    le_sSup ⟨inferInstance, P.isPGroup'.map _⟩
  rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
  exact P.ne_bot_of_dvd_card h hle

theorem exists_sqtk_cover_odd {Q : Type} [Group Q] [Finite Q] (hQ : IsQuotientOfSQTKTC Q)
    (hO2 : CFSG.pCore 2 Q = ⊥) {L : Subgroup Q} (hL : L ∈ cComp (⊤ : Subgroup Q)) :
    ∃ (Shat : Type) (_ : Group Shat) (φ : Shat →* Q), Function.Surjective φ ∧
      SQTKHypCat Shat ∧ Group.IsNilpotent ↥φ.ker ∧ Odd (Nat.card ↥φ.ker) ∧
      ∃ Lhat : Subgroup Shat, Lhat ∈ cComp (⊤ : Subgroup Shat) ∧ Lhat.map φ = L := by
  obtain ⟨S, _, _, hSQT, hK, φ₀, hφ₀⟩ := hQ
  have hS : CFSG.SectionRank.IsSQTKCat S :=
    ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr hSQT, hK⟩
  obtain ⟨S₁, hS₁⟩ := (Set.toFinite {H : Subgroup S | H.map φ₀ = ⊤}).exists_minimal
    ⟨⊤, Subgroup.map_top_of_surjective φ₀ hφ₀⟩
  set ψ : ↥S₁ →* Q := φ₀.comp S₁.subtype with hψdef
  have hψ : Function.Surjective ψ := by
    intro q
    have hq : q ∈ S₁.map φ₀ := by rw [hS₁.prop]; exact Subgroup.mem_top q
    obtain ⟨s, hs, rfl⟩ := hq
    exact ⟨⟨s, hs⟩, rfl⟩
  have hmin : ∀ H : Subgroup ↥S₁, H.map ψ = ⊤ → H = ⊤ := by
    intro H hH
    have h1 : (H.map S₁.subtype).map φ₀ = ⊤ := by rw [Subgroup.map_map]; exact hH
    have h2 : H.map S₁.subtype = S₁ := hS₁.eq_of_le h1 (Subgroup.map_subtype_le H)
    refine Subgroup.map_injective S₁.subtype_injective ?_
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfr : ψ.ker ≤ frattini ↥S₁ := ker_le_frattini_of_forall_map_eq_top_odd ψ hψ hmin
  have hP : CFSG.pCore 2 ↥S₁ ≤ ψ.ker := by
    have h1 : (CFSG.pCore 2 ↥S₁).map ψ ≤ CFSG.pCore 2 Q :=
      le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥S₁)).map ψ hψ, CFSG.pCore_isPGroup.map ψ⟩
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    exact h1
  let φ : (↥S₁ ⧸ CFSG.pCore 2 ↥S₁) →* Q := QuotientGroup.lift (CFSG.pCore 2 ↥S₁) ψ hP
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨s, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk s, rfl⟩
  have hnil : Group.IsNilpotent φ.ker := isNilpotent_ker_lift_of_le_frattini_odd ψ _ hP hfr
  have hhyp : SQTKHypCat (↥S₁ ⧸ CFSG.pCore 2 ↥S₁) :=
    SQTKHypCat.quotient_pCore ↥S₁ (hS.subgroup S₁)
  have := hhyp.finite
  have hodd : Odd (Nat.card φ.ker) := odd_card_of_isNilpotent_of_pCore_eq_bot φ.ker hhyp.o2
  obtain ⟨Lhat, hLhat, hmap⟩ := map_surjOn_cComp_top φ hφ inferInstance hL
  exact ⟨_, inferInstance, φ, hφ, hhyp, hnil, hodd, Lhat, hLhat, hmap⟩

theorem exists_pElement_lift {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H)
    {p : ℕ} (hp : p.Prime) {g : G} {h : H} (hfg : f g = h) (hh : h ^ p = 1) :
    ∃ k : ℕ, ∃ n : ℕ, (g ^ k) ^ (p ^ n) = 1 ∧ f (g ^ k) = h := by
  obtain ⟨a, b, hb, hab⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.one_lt.ne'
  have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb).symm
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨b * c, a, ?_, ?_⟩
  · rw [← pow_mul, show b * c * p ^ a = p ^ a * b * c by ring, pow_mul, ← hab,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, hfg, pow_eq_pow_mod _ hh, hc, pow_one]

theorem le_ker_of_normal_of_ne {S Q : Type*} [Group S] [Group Q] (φ : S →* Q)
    (hker : Group.IsSolvable ↥φ.ker) {Lhat : Subgroup S} (hperf : Group.IsPerfect ↥Lhat)
    (hsimp : IsSimpleGroup ↥(Lhat.map φ)) {N : Subgroup S} (hNL : N ≤ Lhat)
    (hNn : ∀ l ∈ Lhat, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hne : N ≠ Lhat) : N ≤ φ.ker := by
  let N₀ : Subgroup ↥(Lhat.map φ) := (N.map φ).subgroupOf (Lhat.map φ)
  have hN₀ : N₀.Normal := by
    constructor
    intro x hx g
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨l, hl, hlg⟩ := g.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨l * n * l⁻¹, hNn l hl n hn, ?_⟩
    simp only [map_mul, map_inv, hnx, hlg, Subgroup.coe_mul, Subgroup.coe_inv]
  rcases hsimp.eq_bot_or_eq_top_of_normal N₀ with h | h
  · intro n hn
    have hmem : (⟨φ n, ⟨n, hNL hn, rfl⟩⟩ : ↥(Lhat.map φ)) ∈ N₀ :=
      Subgroup.mem_subgroupOf.2 ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    let N' : Subgroup ↥Lhat := N.subgroupOf Lhat
    have hN' : N'.Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (hNn g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
    let K : Subgroup ↥Lhat := φ.ker.subgroupOf Lhat
    have hKs : Group.IsSolvable ↥K := by
      let ι : ↥K →* ↥φ.ker :=
        { toFun := fun k => ⟨((k : ↥Lhat) : S), Subgroup.mem_subgroupOf.1 k.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact Group.isSolvable_of_isSolvable_injective (f := ι) (fun a b hab => by
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext this))
    let π : ↥Lhat →* ↥Lhat ⧸ N' := QuotientGroup.mk' N'
    have hsurj : Function.Surjective (π.comp K.subtype) := by
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N' y
      have hlmem : (⟨φ l, ⟨l, l.2, rfl⟩⟩ : ↥(Lhat.map φ)) ∈ N₀ := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnl⟩ := Subgroup.mem_subgroupOf.1 hlmem
      refine ⟨⟨⟨n⁻¹ * l, Lhat.mul_mem (Lhat.inv_mem (hNL hn)) l.2⟩, ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [hnl, inv_mul_cancel]
      · show (QuotientGroup.mk' N') ⟨n⁻¹ * l, _⟩ = QuotientGroup.mk' N' l
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        rw [Subgroup.mem_subgroupOf]
        have e : ((⟨n⁻¹ * (l : S), Lhat.mul_mem (Lhat.inv_mem (hNL hn)) l.2⟩ : ↥Lhat)⁻¹ * l :
            ↥Lhat) = (l : S)⁻¹ * n * l := by
          simp [mul_assoc]
        rw [e]
        have := hNn _ (Lhat.inv_mem l.2) n hn
        simpa [mul_assoc] using this
    have hsolv : Group.IsSolvable (↥Lhat ⧸ N') := Group.isSolvable_of_surjective hsurj
    have hperf' : Group.IsPerfect (↥Lhat ⧸ N') := inferInstance
    have htriv : Subsingleton (↥Lhat ⧸ N') := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable _ hsolv
    apply hne
    refine le_antisymm hNL fun l hl => ?_
    have h1 := Subsingleton.elim (π ⟨l, hl⟩) 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

theorem eq_one_or_eq_neg_one_of_mul_self {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (A : GL (Fin 2) K) (hA : A * A = 1) (hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1) :
    A = 1 ∨ A = -1 := by
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hM
  have hsq : M * M = 1 := by
    have := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K)) hA
    simpa using this
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have htr : M 0 0 + M 1 1 ≠ 0 := by
    intro h0
    apply h2
    have hd : M 1 1 = -M 0 0 := by linear_combination h0
    rw [hd] at hdet
    linear_combination -e00 - hdet
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right htr
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right htr
  simp only [hb, hc, mul_zero, add_zero, zero_add, sub_zero] at e00 e11 hdet
  have ha0 : M 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e00
    exact one_ne_zero e00.symm
  have had : M 1 1 = M 0 0 := by
    have : (M 1 1 - M 0 0) * M 0 0 = 0 := by linear_combination hdet - e00
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ha0)
  have ha : M 0 0 = 1 ∨ M 0 0 = -1 := by
    have : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases ha with ha | ha
  · left
    apply Units.ext
    show M = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ha, had]
  · right
    apply Units.ext
    show M = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ha, had]

theorem comm_of_mem_inf_ker {S Q : Type*} [Group S] [Finite S] [Group Q]
    (hS : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.pRank q S ≤ 2) (φ : S →* Q)
    (hnil : Group.IsNilpotent ↥φ.ker) (hodd : Odd (Nat.card ↥φ.ker))
    {Lhat : Subgroup S} (hperf : Group.IsPerfect ↥Lhat) (hsimp : IsSimpleGroup ↥(Lhat.map φ)) :
    ∀ k ∈ Lhat ⊓ φ.ker, ∀ l ∈ Lhat, k * l = l * k := by
  classical
  set R := Lhat ⊓ φ.ker with hRdef
  have hRk : R ≤ φ.ker := inf_le_right
  have hsolv : Group.IsSolvable ↥φ.ker := by
    have := hnil
    infer_instance
  have hRn : Lhat ≤ Subgroup.normalizer (R : Set S) := by
    have key : ∀ l ∈ Lhat, ∀ r ∈ R, l * r * l⁻¹ ∈ R := fun l hl r hr =>
      ⟨Lhat.mul_mem (Lhat.mul_mem hl hr.1) (Lhat.inv_mem hl),
        (MonoidHom.normal_ker φ).conj_mem r hr.2 l⟩
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨key l hl r, fun hr => ?_⟩
    have h1 := key l⁻¹ (Lhat.inv_mem hl) _ hr
    simpa [mul_assoc] using h1
  have hRodd : ∀ g ∈ R, Odd (orderOf g) := by
    intro g hg
    have h1 : orderOf (⟨g, hRk hg⟩ : ↥φ.ker) ∣ Nat.card ↥φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hRnil : Group.IsNilpotent ↥R := by
    have := hnil
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRk)
  have key : ∀ q : ℕ, q.Prime → ∀ x ∈ CFSG.Open.pCoreOf q R, ∀ l ∈ Lhat, x * l = l * x := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    set P := CFSG.Open.pCoreOf q R with hPdef
    have hPR : P ≤ R := pCoreOf_le q R
    have hPp : IsPGroup q ↥P := pCoreOf_isPGroup q R
    by_cases hq2 : q = 2
    · intro x hx l hl
      have hx1 : x = 1 := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hPp) ⟨x, hx⟩
        rw [Subgroup.orderOf_mk] at hn
        have hodd' := hRodd x (hPR hx)
        rw [hn, hq2] at hodd'
        rcases n with _ | n
        · rw [pow_zero] at hn
          exact orderOf_eq_one_iff.1 hn
        · exact absurd hodd' (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, n.succ_ne_zero⟩))
      rw [hx1, one_mul, mul_one]
    · have hLn : Lhat ≤ Subgroup.normalizer (P : Set S) :=
        hRn.trans (normalizer_le_normalizer_pCoreOf q R)
      have hrk : CFSG.Open.pRank q (⊤ : Subgroup ↥P) ≤ 2 := by
        have h1 := CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt P.subtype
          P.subtype_injective
        have h2 : CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2 := by
          rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
          exact hS q hq hq2
        exact h1.trans h2
      obtain ⟨θ, hθ⟩ := exists_hom_ker_eq_pCore_aut hq2 hPp hrk
      let c : ↥Lhat →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hLn)
      have hc : ∀ (l : ↥Lhat) (x : ↥P), ((c l x : ↥P) : S) = (l : S) * x * (l : S)⁻¹ :=
        fun _ _ => rfl
      obtain ⟨ρ, hρdef⟩ : ∃ ρ : ↥Lhat →* GL (Fin 2) (ZMod q), ρ = θ.comp c := ⟨_, rfl⟩
      by_cases hρ : ∀ l : ↥Lhat, ρ l = 1
      ·
        have hcr : IsPGroup q ↥c.range := by
          refine (CFSG.LieType.BorelTits.pCore_isPGroup (G := MulAut ↥P) q).to_le ?_
          rintro _ ⟨l, rfl⟩
          rw [← hθ, MonoidHom.mem_ker]
          have := hρ l
          rwa [hρdef] at this
        have : Group.IsPerfect ↥c.range := Group.IsPerfect.range c
        have hsub : Subsingleton ↥c.range := by
          by_contra hnt
          rw [not_subsingleton_iff_nontrivial] at hnt
          exact Group.IsPerfect.not_isNilpotent _ hcr.isNilpotent
        intro x hx l hl
        have h1 : c ⟨l, hl⟩ = 1 :=
          congrArg Subtype.val (Subsingleton.elim (c.rangeRestrict ⟨l, hl⟩) 1)
        have h2 := congrArg (fun α : MulAut ↥P => ((α ⟨x, hx⟩ : ↥P) : S)) h1
        simp only [hc, MulAut.one_apply] at h2
        calc x * l = l * x * l⁻¹ * l := by rw [h2]
          _ = l * x := by group
      · exfalso
        push Not at hρ
        obtain ⟨l₀, hl₀⟩ := hρ
        have hq2' : (2 : ZMod q) ≠ 0 := by
          intro h
          have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
          rw [ZMod.natCast_eq_zero_iff] at h'
          exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')
        have hperfρ : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
        have hntρ : Nontrivial ↥ρ.range :=
          ⟨⟨ρ.rangeRestrict l₀, 1, fun h => hl₀ (congrArg Subtype.val h)⟩⟩
        have heven : Even (Nat.card ↥ρ.range) := by
          by_contra hodd'
          exact Group.IsPerfect.not_isSolvable _
            (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 hodd'))
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 heven)
        obtain ⟨g, hg⟩ := i.2
        have hdet : ∀ l : ↥Lhat,
            ((ρ l : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := by
          intro l
          have h1 : (Matrix.GeneralLinearGroup.det.comp ρ) l = 1 :=
            Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
          have h2 := congrArg Units.val h1
          simpa using h2
        have hgsq : ρ g * ρ g = 1 := by
          rw [hg, ← pow_two]
          have := pow_orderOf_eq_one i
          rw [hi] at this
          exact congrArg Subtype.val this
        have hi1 : (i : GL (Fin 2) (ZMod q)) ≠ 1 := by
          intro h
          have : i = 1 := Subtype.ext h
          rw [this, orderOf_one] at hi
          exact absurd hi (by norm_num)
        rcases eq_one_or_eq_neg_one_of_mul_self hq2' (ρ g) hgsq (hdet g) with h1 | h1
        · exact hi1 (hg ▸ h1)
        ·
          obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup (GL (Fin 2) (ZMod q)), Z = Subgroup.zpowers (-1) :=
            ⟨_, rfl⟩
          have hZc : ∀ z ∈ Z, ∀ y : GL (Fin 2) (ZMod q), y * z = z * y := by
            intro z hz y
            rw [hZdef] at hz
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
            exact ((Commute.neg_one_left y).zpow_left k).eq.symm
          have hm1 : (-1 : GL (Fin 2) (ZMod q)) ∈ Z := by
            rw [hZdef]
            exact Subgroup.mem_zpowers _
          obtain ⟨N₄, hN₄mem⟩ : ∃ N₄ : Subgroup S, ∀ x : S,
              x ∈ N₄ ↔ ∃ y : ↥Lhat, ρ y ∈ Z ∧ (y : S) = x :=
            ⟨(Z.comap ρ).map Lhat.subtype, fun x => by
              simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]⟩
          have hN₄L : N₄ ≤ Lhat := by
            intro x hx
            obtain ⟨y, -, rfl⟩ := (hN₄mem x).1 hx
            exact y.2
          have hN₄n : ∀ l ∈ Lhat, ∀ n ∈ N₄, l * n * l⁻¹ ∈ N₄ := by
            intro l hl n hn
            obtain ⟨y, hy, rfl⟩ := (hN₄mem n).1 hn
            refine (hN₄mem _).2 ⟨⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹, ?_, rfl⟩
            rw [map_mul, map_mul, map_inv, hZc _ hy, mul_inv_cancel_right]
            exact hy
          have hN₄ne : N₄ ≠ Lhat := by
            intro h
            have hcomm : ∀ a b : ↥ρ.range, a * b = b * a := by
              rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
              have ha : (a : S) ∈ N₄ := h ▸ a.2
              obtain ⟨y, hy, hya⟩ := (hN₄mem _).1 ha
              rw [Subtype.ext hya] at hy
              apply Subtype.ext
              exact (hZc _ hy (ρ b)).symm
            have : IsMulCommutative ↥ρ.range := ⟨⟨hcomm⟩⟩
            have hsub : Subsingleton ↥ρ.range :=
              Group.IsPerfect.subsingleton_of_isMulCommutative
            exact (not_nontrivial_iff_subsingleton.2 hsub) hntρ
          have hle : N₄ ≤ φ.ker := le_ker_of_normal_of_ne φ hsolv hperf hsimp hN₄L hN₄n hN₄ne
          have hgN : (g : S) ∈ N₄ := (hN₄mem _).2 ⟨g, by rw [h1]; exact hm1, rfl⟩
          have hgR : (g : S) ∈ R := ⟨g.2, hle hgN⟩
          have hgodd := hRodd _ hgR
          have hpow : ρ g ^ orderOf (g : S) = 1 := by
            rw [Subgroup.orderOf_coe, ← map_pow, pow_orderOf_eq_one, map_one]
          rw [h1, hgodd.neg_one_pow] at hpow
          have h00 := congrArg
            (fun B : GL (Fin 2) (ZMod q) => (B : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) hpow
          simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
          exact hq2' (by linear_combination -h00)
  have hsyl : ∀ q ∈ (Nat.card ↥R).primeFactors,
      ((default : Sylow q ↥R) : Subgroup ↥R).map R.subtype ≤ CFSG.Open.pCoreOf q R := by
    intro q hq
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    refine le_pCoreOf_of_le_normalizer q (Subgroup.map_subtype_le _) ?_
      ((default : Sylow q ↥R).isPGroup'.map R.subtype)
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hnorm : ((default : Sylow q ↥R) : Subgroup ↥R).Normal := inferInstance
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨r, hr⟩ * z * ⟨r, hr⟩⁻¹, hnorm.conj_mem z hz ⟨r, hr⟩, rfl⟩
    · intro hy
      obtain ⟨z, hz, hzy⟩ := hy
      refine ⟨⟨r, hr⟩⁻¹ * z * ⟨r, hr⟩, ?_, ?_⟩
      · have := hnorm.conj_mem z hz ⟨r, hr⟩⁻¹
        rw [inv_inv] at this
        exact this
      · have e : (z : S) = r * y * r⁻¹ := hzy
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [e]
        group
  have hRle : R ≤ ⨆ q ∈ (Nat.card ↥R).primeFactors, CFSG.Open.pCoreOf q R := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥R) ∈
        (⨆ q ∈ (Nat.card ↥R).primeFactors, ((default : Sylow q ↥R) : Subgroup ↥R)) :=
      (Sylow.iSup_sylow_eq_top (G := ↥R)) ▸ Subgroup.mem_top _
    have hmap := Subgroup.mem_map_of_mem R.subtype hx'
    simp only [Subgroup.map_iSup] at hmap
    have hle : (⨆ q ∈ (Nat.card ↥R).primeFactors,
        ((default : Sylow q ↥R) : Subgroup ↥R).map R.subtype) ≤
        ⨆ q ∈ (Nat.card ↥R).primeFactors, CFSG.Open.pCoreOf q R :=
      iSup₂_mono fun q hq => hsyl q hq
    exact hle hmap
  intro k hk l hl
  have hcen : ⨆ q ∈ (Nat.card ↥R).primeFactors, CFSG.Open.pCoreOf q R ≤
      Subgroup.centralizer (Lhat : Set S) :=
    iSup₂_le fun q hq x hx => Subgroup.mem_centralizer_iff.2 fun l hl =>
      (key q (Nat.prime_of_mem_primeFactors hq) x hx l hl).symm
  exact ((Subgroup.mem_centralizer_iff.1 (hcen (hRle hk))) l hl).symm

private theorem commRank_mul_pow_mul {M : Type*} [Monoid M] {A B C : M} (hAB : Commute A B)
    (hAC : Commute A C) (hBC : Commute B C) (i j k i' j' k' : ℕ) :
    A ^ i * B ^ j * C ^ k * (A ^ i' * B ^ j' * C ^ k') =
      A ^ (i + i') * B ^ (j + j') * C ^ (k + k') := by
  have h1 : B ^ j * C ^ k * A ^ i' = A ^ i' * (B ^ j * C ^ k) :=
    ((hAB.pow_pow i' j).symm.mul_left (hAC.pow_pow i' k).symm).eq
  have h2 : C ^ k * B ^ j' = B ^ j' * C ^ k := (hBC.pow_pow j' k).symm.eq
  calc A ^ i * B ^ j * C ^ k * (A ^ i' * B ^ j' * C ^ k')
      = A ^ i * (B ^ j * C ^ k * A ^ i') * B ^ j' * C ^ k' := by simp only [mul_assoc]
    _ = A ^ i * (A ^ i' * (B ^ j * C ^ k)) * B ^ j' * C ^ k' := by rw [h1]
    _ = A ^ i * A ^ i' * B ^ j * (C ^ k * B ^ j') * C ^ k' := by simp only [mul_assoc]
    _ = A ^ i * A ^ i' * B ^ j * (B ^ j' * C ^ k) * C ^ k' := by rw [h2]
    _ = A ^ (i + i') * B ^ (j + j') * C ^ (k + k') := by simp only [pow_add, mul_assoc]

private theorem commRank_eq_of_dvd {p i j : ℕ} (hi : i < p) (hj : j < p)
    (h : p ∣ i + (p - j)) : i = j := by
  rcases lt_or_ge i j with hij | hji
  · have := Nat.eq_zero_of_dvd_of_lt h (by omega)
    omega
  · have h' : p ∣ i - j := by
      have := Nat.dvd_sub h (dvd_refl p)
      rwa [show i + (p - j) - p = i - j by omega] at this
    have := Nat.eq_zero_of_dvd_of_lt h' (by omega)
    omega

private theorem commRank_eq_of_mul_pow_eq {M : Type*} [Monoid M] {p : ℕ} {A B C : M}
    (hAB : Commute A B) (hAC : Commute A C) (hBC : Commute B C) (hA : A ^ p = 1)
    (hB : B ^ p = 1) (hC : C ^ p = 1)
    (hind : ∀ i j k : ℕ, A ^ i * B ^ j * C ^ k = 1 → p ∣ i ∧ p ∣ j ∧ p ∣ k)
    {i j k i' j' k' : ℕ} (hi : i < p) (hj : j < p) (hk : k < p) (hi' : i' < p) (hj' : j' < p)
    (hk' : k' < p) (h : A ^ i * B ^ j * C ^ k = A ^ i' * B ^ j' * C ^ k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have key := hind (i + (p - i')) (j + (p - j')) (k + (p - k')) (by
    rw [← commRank_mul_pow_mul hAB hAC hBC, h, commRank_mul_pow_mul hAB hAC hBC,
      Nat.add_sub_of_le hi'.le, Nat.add_sub_of_le hj'.le, Nat.add_sub_of_le hk'.le, hA, hB, hC,
      mul_one, mul_one])
  exact ⟨commRank_eq_of_dvd hi hi' key.1, commRank_eq_of_dvd hj hj' key.2.1,
    commRank_eq_of_dvd hk hk' key.2.2⟩

private theorem commRank_pow_three_le_card {H : Type*} [Group H] {p : ℕ} {Q : Subgroup H}
    [Finite Q] {A B C : H} (hAQ : A ∈ Q) (hBQ : B ∈ Q) (hCQ : C ∈ Q) (hAB : Commute A B)
    (hAC : Commute A C) (hBC : Commute B C) (hA : A ^ p = 1) (hB : B ^ p = 1) (hC : C ^ p = 1)
    (hind : ∀ i j k : ℕ, A ^ i * B ^ j * C ^ k = 1 → p ∣ i ∧ p ∣ j ∧ p ∣ k) :
    p ^ 3 ≤ Nat.card Q := by
  let F : Fin p × Fin p × Fin p → Q := fun x =>
    ⟨A ^ (x.1 : ℕ) * B ^ (x.2.1 : ℕ) * C ^ (x.2.2 : ℕ),
      Q.mul_mem (Q.mul_mem (Q.pow_mem hAQ _) (Q.pow_mem hBQ _)) (Q.pow_mem hCQ _)⟩
  have hF : Function.Injective F := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    obtain ⟨h1, h2, h3⟩ := commRank_eq_of_mul_pow_eq hAB hAC hBC hA hB hC hind i.2 j.2 k.2
      i'.2 j'.2 k'.2 (congrArg Subtype.val h)
    rw [Fin.ext h1, Fin.ext h2, Fin.ext h3]
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_fin, ← pow_three] at this

private theorem commRank_card_range_le {P H : Type*} [CommGroup P] [Finite P] [Group H] {p : ℕ}
    (g : P →* H) (hg : ∀ y, g y ^ p = 1) :
    Nat.card g.range ≤ Nat.card (powMonoidHom p : P →* P).ker := by
  set φ : P →* P := powMonoidHom p
  have hle : φ.range ≤ g.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hg]
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card P := by
    rw [← Subgroup.index_ker φ, Subgroup.card_mul_index]
  have h2 : Nat.card g.ker * Nat.card g.range = Nat.card P := by
    rw [← Subgroup.index_ker g, Subgroup.card_mul_index]
  have h3 : Nat.card φ.range ≤ Nat.card g.ker := Subgroup.card_le_of_le hle
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := g.ker))
  calc Nat.card g.range * Nat.card g.ker = Nat.card φ.ker * Nat.card φ.range := by
        rw [mul_comm, h2, h1]
    _ ≤ Nat.card φ.ker * Nat.card g.ker := Nat.mul_le_mul_left _ h3

private theorem commRank_le_pRank_of_card {p : ℕ} (hp : 1 < p) {G : Type*} [Group G] [Finite G]
    {E : Subgroup G} (hE : CFSG.IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.pRank p G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

open scoped IsMulCommutative in
private theorem commRank_le_pRank_of_le_card_ker {p : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    [Finite G] {P : Subgroup G} [IsMulCommutative P] {k : ℕ}
    (hk : p ^ k ≤ Nat.card (powMonoidHom p : P →* P).ker) : k ≤ CFSG.pRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  set E : Subgroup G := (powMonoidHom p : P →* P).ker.map P.subtype
  have hEP : E ≤ P := Subgroup.map_subtype_le _
  have hEp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' : y ^ p = 1 := by simpa using hy
    simpa using congrArg Subtype.val hy'
  have hEA : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (setLike_mul_comm (hEP x.2) (hEP y.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hEp x x.2) }
  have hcard : Nat.card E = Nat.card (powMonoidHom p : P →* P).ker :=
    Subgroup.card_map_of_injective P.subtype_injective
  obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq (CFSG.IsElementaryAbelian.isPGroup p E)
  have hkm : k ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hm ▸ hcard ▸ hk)
  exact hkm.trans (commRank_le_pRank_of_card hp.one_lt hEA hm)

open scoped IsMulCommutative in
private theorem commRank_three_le_pRank_of_subgroup {p : ℕ} (hp : p.Prime) {G H : Type*}
    [Group G] [Finite G] [Group H] (f : G →* H) {P : Subgroup G} [IsMulCommutative P]
    (hexp : ∀ y ∈ P, f y ^ p = 1) {a b c : G} (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P)
    (hind : ∀ i j k : ℕ, f a ^ i * f b ^ j * f c ^ k = 1 → p ∣ i ∧ p ∣ j ∧ p ∣ k) :
    3 ≤ CFSG.pRank p G := by
  let g : P →* H := f.comp P.subtype
  have : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have hcomm : ∀ {x y : G}, x ∈ P → y ∈ P → Commute (f x) (f y) := fun hx hy =>
    (show Commute _ _ from setLike_mul_comm hx hy).map f
  have hmem : ∀ {x : G}, x ∈ P → f x ∈ g.range := fun {x} hx => ⟨⟨x, hx⟩, rfl⟩
  have h1 := commRank_card_range_le g (fun y => hexp y y.2)
  have h2 := commRank_pow_three_le_card (hmem haP) (hmem hbP) (hmem hcP) (hcomm haP hbP)
    (hcomm haP hcP) (hcomm hbP hcP) (hexp a haP) (hexp b hbP) (hexp c hcP) hind
  exact commRank_le_pRank_of_le_card_ker hp (h2.trans h1)

theorem three_le_pRank_of_commuting {p : ℕ} (hp : p.Prime) {G H : Type*} [Group G] [Finite G]
    [Group H] (f : G →* H) {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (_ha : ∃ n : ℕ, a ^ p ^ n = 1) (_hb : ∃ n : ℕ, b ^ p ^ n = 1)
    (_hc : ∃ n : ℕ, c ^ p ^ n = 1) (hfa : f a ^ p = 1) (hfb : f b ^ p = 1) (hfc : f c ^ p = 1)
    (hind : ∀ i j k : ℕ, f a ^ i * f b ^ j * f c ^ k = 1 → p ∣ i ∧ p ∣ j ∧ p ∣ k) :
    3 ≤ CFSG.pRank p G := by
  have hpair : ({a, b, c} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hab | exact hac | exact hbc
      | exact Commute.symm hab | exact Commute.symm hac | exact Commute.symm hbc
  have := Subgroup.isMulCommutative_closure hpair
  have hexp : ∀ y ∈ Subgroup.closure ({a, b, c} : Set G), f y ^ p = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [map_mul, ((show Commute x y from setLike_mul_comm hx hy).map f).mul_pow, ihx, ihy,
        one_mul]
    | inv x hx ih => rw [map_inv, inv_pow, ih, inv_one]
  exact commRank_three_le_pRank_of_subgroup hp f hexp (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hind

theorem isQuasisimple_of_comm_ker {S Q : Type*} [Group S] [Group Q] (φ : S →* Q)
    {Lhat : Subgroup S} (hperf : Group.IsPerfect ↥Lhat) (hsimp : IsSimpleGroup ↥(Lhat.map φ))
    (hnab : ∃ a b : ↥(Lhat.map φ), a * b ≠ b * a)
    (hcent : ∀ k ∈ Lhat ⊓ φ.ker, ∀ l ∈ Lhat, k * l = l * k) : CFSG.IsQuasisimple ↥Lhat := by
  let f : ↥Lhat →* ↥(Lhat.map φ) := φ.subgroupMap Lhat
  have hf : Function.Surjective f := φ.subgroupMap_surjective Lhat
  have hker : f.ker ≤ Subgroup.center ↥Lhat := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro l
    have hk' : (k : S) ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hk ⊢
      exact congrArg Subtype.val hk
    exact Subtype.ext (hcent k ⟨k.2, hk'⟩ l l.2).symm
  let e : ↥Lhat ⧸ f.ker ≃* ↥(Lhat.map φ) := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hsimp' : IsSimpleGroup (↥Lhat ⧸ f.ker) := MulEquiv.isSimpleGroup e
  obtain ⟨a, b, hab⟩ := hnab
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient f.ker hker hperf hsimp'
    ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem commutator_mul_mul_of_comm {G : Type*} [Group G] {a b c d : G} (hca : c * a = a * c)
    (hcb : c * b = b * c) (hcd : c * d = d * c) (hda : d * a = a * d) (hdb : d * b = b * d) :
    ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hca' : Commute c a := hca
  have hcb' : Commute c b := hcb
  have hcd' : Commute c d := hcd
  have hda' : Commute d a := hda
  have hdb' : Commute d b := hdb
  have hC : Commute c (a * (d * b) * a⁻¹) :=
    (hca'.mul_right (hcd'.mul_right hcb')).mul_right hca'.inv_right
  have hD : Commute d (a * b * a⁻¹ * b⁻¹) :=
    ((hda'.mul_right hdb').mul_right hda'.inv_right).mul_right hdb'.inv_right
  calc ⁅c * a, d * b⁆ = c * (a * (d * b) * a⁻¹) * c⁻¹ * (d * b)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * (d * b) * a⁻¹ * (d * b)⁻¹ := by rw [hC.eq]; group
    _ = (a * d) * b * a⁻¹ * b⁻¹ * d⁻¹ := by group
    _ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by rw [← hda]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hD.eq]; group
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]

end Cover

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem eq_one_of_pow_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card ↥L)
    {x : MulAut W} (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) (hxp : x ^ p = 1) :
    x = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hx1
  obtain ⟨hxM, hxc⟩ := hx
  have hxcomm : ∀ m ∈ Mp, x * m = m * x := fun m hm =>
    ((Subgroup.mem_centralizer_iff.1 hxc) m hm).symm
  set L₀ : Subgroup ↥M := L.subgroupOf M with hL₀
  set Lt₀ : Subgroup ↥M := (conjAutSub t L).subgroupOf M with hLt₀
  set x₀ : ↥M := ⟨x, hxM⟩ with hx₀
  set t₀ : ↥M := ⟨t, hB.t_mem⟩ with ht₀
  have hO2 : CFSG.pCore 2 ↥M = ⊥ := by
    have h := D31.pCoreOf_eq_bot hB.hD.hyp
    unfold CFSG.Open.pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h
  have hLc : L₀ ∈ cComp (⊤ : Subgroup ↥M) := subgroupOf_mem_cComp hB.hD.hyp.comp
  obtain ⟨Shat, _, φ, hφ, hSQ, hnil, hodd, Lhat, hLhat, hmap⟩ :=
    exists_sqtk_cover_odd hB.hD.hyp.qsqtk hO2 hLc
  have := hSQ.finite
  have hL₀simp : IsSimpleGroup ↥L₀ := by
    have := hB.hsimp
    exact MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hB.L_le)
  have hLt₀simp : IsSimpleGroup ↥Lt₀ := by
    have := hB.Lt_simp
    exact MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hB.Lt_le)
  have hnab : ∀ {X : Subgroup (MulAut W)} (hXc : X ∈ cComp M),
      ∃ a b : ↥(X.subgroupOf M), a * b ≠ b * a := by
    intro X hXc
    by_contra hcon
    push Not at hcon
    have hXM := le_of_mem_cComp hXc
    refine not_isSolvable_of_mem_cComp hXc (Group.isSolvable_of_comm fun a b => ?_)
    have := hcon ⟨⟨a, hXM a.2⟩, a.2⟩ ⟨⟨b, hXM b.2⟩, b.2⟩
    exact Subtype.ext (congrArg (fun y : ↥(X.subgroupOf M) => ((y : ↥M) : MulAut W)) this)
  have hperf : Group.IsPerfect ↥Lhat := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hLhat)
  have hsimpL : IsSimpleGroup ↥(Lhat.map φ) := by rw [hmap]; exact hL₀simp
  have hnabL : ∃ a b : ↥(Lhat.map φ), a * b ≠ b * a := by
    rw [hmap]; exact hnab hB.hD.hyp.comp
  have hcent := comm_of_mem_inf_ker hSQ.sqt φ hnil hodd hperf hsimpL
  have hLq : CFSG.IsQuasisimple ↥Lhat := isQuasisimple_of_comm_ker φ hperf hsimpL hnabL hcent
  obtain ⟨gh, hgh⟩ := hφ t₀
  set Lhat' : Subgroup Shat := Lhat.map (MulAut.conj gh).toMonoidHom with hLhat'
  have hconjc : ∀ (y : Shat) {K : Subgroup Shat}, K ∈ cComp (⊤ : Subgroup Shat) →
      K.map (MulAut.conj y).toMonoidHom ∈ cComp (⊤ : Subgroup Shat) := by
    intro y K hK
    have h1 := cComp_map_mulEquiv (MulAut.conj y) hK
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj y).surjective] at h1
  have hconjq : ∀ (y : Shat) {K : Subgroup Shat}, CFSG.IsQuasisimple ↥K →
      CFSG.IsQuasisimple ↥(K.map (MulAut.conj y).toMonoidHom) := fun y K hK =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective K _ (MulAut.conj y).injective) hK
  have hLhat'c : Lhat' ∈ cComp (⊤ : Subgroup Shat) := hconjc gh hLhat
  have hLq' : CFSG.IsQuasisimple ↥Lhat' := hconjq gh hLq
  have hmap' : Lhat'.map φ = Lt₀ := by
    ext z
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      have hφl : φ l ∈ L₀ := hmap ▸ Subgroup.mem_map_of_mem φ hl
      rw [hLt₀, Subgroup.mem_subgroupOf]
      have e : ((φ ((MulAut.conj gh).toMonoidHom l) : ↥M) : MulAut W) =
          t * ((φ l : ↥M) : MulAut W) * t⁻¹ := by
        simp [MulAut.conj_apply, map_mul, map_inv, hgh, ht₀]
      rw [e]
      exact conj_mem_conjAutSub t (Subgroup.mem_subgroupOf.1 hφl)
    · intro hz
      rw [hLt₀, Subgroup.mem_subgroupOf, mem_conjAutSub] at hz
      have h1 : t₀⁻¹ * z * t₀ ∈ L₀ := Subgroup.mem_subgroupOf.2 hz
      rw [← hmap] at h1
      obtain ⟨l, hl, hlz⟩ := h1
      refine ⟨(MulAut.conj gh).toMonoidHom l, ⟨l, hl, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hgh, hlz]
      group
  have hLne : Lhat ≠ Lhat' := by
    intro h
    apply hB.Lt_ne
    have h1 : L₀ = Lt₀ := by rw [← hmap, ← hmap', h]
    have h2 := congrArg (Subgroup.map M.subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hB.L_le, Subgroup.map_subgroupOf_eq_of_le hB.Lt_le] at h2
    exact h2.symm
  have hcomm' : ⁅Lhat, Lhat'⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hLhat hLhat'c hLq hLq').resolve_left hLne
  have hL₀Mp : ∀ z ∈ L₀, (z : MulAut W) ∈ Mp := fun z hz =>
    hB.L_le_Mp (Subgroup.mem_subgroupOf.1 hz)
  have hLt₀Mp : ∀ z ∈ Lt₀, (z : MulAut W) ∈ Mp := fun z hz =>
    hB.Lt_le_Mp (Subgroup.mem_subgroupOf.1 hz)
  have hx₀c : ∀ z : ↥M, (z : MulAut W) ∈ Mp → x₀ * z = z * x₀ := fun z hz =>
    Subtype.ext (hxcomm _ hz)
  obtain ⟨y₁, hy₁⟩ := hφ x₀
  have hx₀p : x₀ ^ p = 1 := Subtype.ext (by simpa [hx₀] using hxp)
  obtain ⟨kx, nx, hxn, hxk⟩ := exists_pElement_lift φ hp hy₁ hx₀p
  set xh := y₁ ^ kx with hxh
  have hKMp : ∀ {K : Subgroup Shat}, (K.map φ = L₀ ∨ K.map φ = Lt₀) →
      ∀ k ∈ K, ((φ k : ↥M) : MulAut W) ∈ Mp := by
    intro K hKφ k hk
    have h1 : φ k ∈ K.map φ := Subgroup.mem_map_of_mem φ hk
    rcases hKφ with h | h <;> rw [h] at h1
    · exact hL₀Mp _ h1
    · exact hLt₀Mp _ h1
  have hfixK : ∀ {K : Subgroup Shat}, K ∈ cComp (⊤ : Subgroup Shat) → CFSG.IsQuasisimple ↥K →
      (K.map φ = L₀ ∨ K.map φ = Lt₀) → K.map (MulAut.conj xh).toMonoidHom = K := by
    intro K hKc hKq hKφ
    rcases H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple (hconjc xh hKc) hKc
        (hconjq xh hKq) hKq with h | h
    · exact h
    · exfalso
      have hmapeq : (K.map (MulAut.conj xh).toMonoidHom).map φ = K.map φ := by
        ext z
        constructor
        · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          refine ⟨k, hk, ?_⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hxk]
          rw [hx₀c _ (hKMp hKφ k hk)]
          group
        · rintro ⟨k, hk, rfl⟩
          refine ⟨(MulAut.conj xh).toMonoidHom k, ⟨k, hk, rfl⟩, ?_⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hxk]
          rw [hx₀c _ (hKMp hKφ k hk)]
          group
      have h2 : ⁅K.map φ, K.map φ⁆ = ⊥ := by
        have := congrArg (Subgroup.map φ) h
        rwa [Subgroup.map_commutator, hmapeq, Subgroup.map_bot] at this
      have hLtc : Lt₀ ∈ cComp (⊤ : Subgroup ↥M) := subgroupOf_mem_cComp hB.Lt_mem_cComp
      rcases hKφ with hK | hK <;> rw [hK] at h2
      · exact ne_bot_of_mem_cComp hLc ((perfect_of_mem_cComp hLc).symm.trans h2)
      · exact ne_bot_of_mem_cComp hLtc ((perfect_of_mem_cComp hLtc).symm.trans h2)
  have hcentK : ∀ {K : Subgroup Shat}, K.map (MulAut.conj xh).toMonoidHom = K →
      (K.map φ = L₀ ∨ K.map φ = Lt₀) → ⁅K, K⁆ = K →
      (∀ k ∈ K ⊓ φ.ker, ∀ l ∈ K, k * l = l * k) → ∀ l ∈ K, xh * l = l * xh := by
    intro K hKn hKφ hKperf hKc
    have hc : ∀ l ∈ K, xh * l * xh⁻¹ * l⁻¹ ∈ K ⊓ φ.ker := by
      intro l hl
      have h1 : xh * l * xh⁻¹ ∈ K := by
        rw [← hKn]
        exact ⟨l, hl, rfl⟩
      refine ⟨K.mul_mem h1 (K.inv_mem hl), ?_⟩
      show xh * l * xh⁻¹ * l⁻¹ ∈ φ.ker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxk,
        hx₀c _ (hKMp hKφ l hl)]
      group
    have hcomm : ∀ a ∈ K, ∀ b ∈ K, xh * ⁅a, b⁆ = ⁅a, b⁆ * xh := by
      intro a ha b hb
      have hca := hc a ha
      have hcb := hc b hb
      have e1 : xh * ⁅a, b⁆ * xh⁻¹ =
          ⁅(xh * a * xh⁻¹ * a⁻¹) * a, (xh * b * xh⁻¹ * b⁻¹) * b⁆ := by
        simp only [commutatorElement_def]
        group
      have h1 : ⁅(xh * a * xh⁻¹ * a⁻¹) * a, (xh * b * xh⁻¹ * b⁻¹) * b⁆ = ⁅a, b⁆ :=
        commutator_mul_mul_of_comm (hKc _ hca a ha) (hKc _ hca b hb) (hKc _ hca _ hcb.1)
          (hKc _ hcb a ha) (hKc _ hcb b hb)
      calc xh * ⁅a, b⁆ = xh * ⁅a, b⁆ * xh⁻¹ * xh := by group
        _ = ⁅a, b⁆ * xh := by rw [e1, h1]
    have hle : ⁅K, K⁆ ≤ Subgroup.centralizer {xh} := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm a ha b hb).symm
    rw [hKperf] at hle
    intro l hl
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl)).symm
  have hxL : ∀ l ∈ Lhat, xh * l = l * xh :=
    hcentK (hfixK hLhat hLq (Or.inl hmap)) (Or.inl hmap) (perfect_of_mem_cComp hLhat) hcent
  have hperf' : Group.IsPerfect ↥Lhat' := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hLhat'c)
  have hsimpL' : IsSimpleGroup ↥(Lhat'.map φ) := by rw [hmap']; exact hLt₀simp
  have hcent' := comm_of_mem_inf_ker hSQ.sqt φ hnil hodd hperf' hsimpL'
  have hxL' : ∀ l ∈ Lhat', xh * l = l * xh :=
    hcentK (hfixK hLhat'c hLq' (Or.inr hmap')) (Or.inr hmap') (perfect_of_mem_cComp hLhat'c)
      hcent'
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpL
  have hupow : (u : MulAut W) ^ p = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg Subtype.val this
  set u₀ : ↥M := ⟨(u : MulAut W), hB.L_le u.2⟩ with hu₀
  have hu₀p : u₀ ^ p = 1 := Subtype.ext (by simpa [hu₀] using hupow)
  have hu₀' : u₀ ∈ Lhat.map φ := by rw [hmap]; exact Subgroup.mem_subgroupOf.2 u.2
  obtain ⟨v₁, hv₁L, hv₁⟩ := hu₀'
  obtain ⟨ku, nu, hun, huk⟩ := exists_pElement_lift φ hp hv₁ hu₀p
  set uh := v₁ ^ ku with huh
  have huhL : uh ∈ Lhat := Lhat.pow_mem hv₁L ku
  set uh' := gh * uh * gh⁻¹ with huh'
  have huh'L : uh' ∈ Lhat' := ⟨uh, huhL, rfl⟩
  have hφuh' : φ uh' = t₀ * u₀ * t₀⁻¹ := by rw [huh', map_mul, map_mul, map_inv, hgh, huk]
  have hab : xh * uh = uh * xh := hxL uh huhL
  have hac : xh * uh' = uh' * xh := hxL' uh' huh'L
  have hbc : uh * uh' = uh' * uh := by
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm' huhL
    exact ((Subgroup.mem_centralizer_iff.1 h1) uh' huh'L).symm
  have hue' : uh' ^ p ^ nu = 1 := by rw [huh', conj_pow, hun, mul_one, mul_inv_cancel]
  have hu'p : (t₀ * u₀ * t₀⁻¹) ^ p = 1 := by rw [conj_pow, hu₀p, mul_one, mul_inv_cancel]
  have hordx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hordu : orderOf (u : MulAut W) = p := by rw [Subgroup.orderOf_coe, hu]
  have hordu' : orderOf (t * (u : MulAut W) * t⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hordu]
  have hind : ∀ i j k : ℕ, φ xh ^ i * φ uh ^ j * φ uh' ^ k = 1 → p ∣ i ∧ p ∣ j ∧ p ∣ k := by
    intro i j k h
    rw [hxk, huk, hφuh'] at h
    have h' : x ^ i * ((u : MulAut W) ^ j * (t * (u : MulAut W) * t⁻¹) ^ k) = 1 := by
      have := congrArg Subtype.val h
      simpa [hx₀, hu₀, ht₀, mul_assoc] using this
    have hujL : (u : MulAut W) ^ j ∈ L := L.pow_mem u.2 j
    have hukLt : (t * (u : MulAut W) * t⁻¹) ^ k ∈ conjAutSub t L :=
      (conjAutSub t L).pow_mem (conj_mem_conjAutSub t u.2) k
    have hmemMp : (u : MulAut W) ^ j * (t * (u : MulAut W) * t⁻¹) ^ k ∈ Mp :=
      Mp.mul_mem (hB.L_le_Mp hujL) (hB.Lt_le_Mp hukLt)
    have hxi : x ^ i = 1 := by
      have hxiC : x ^ i ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
        (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).pow_mem ⟨hxM, hxc⟩ i
      have hxiMp : x ^ i ∈ Mp := by
        rw [eq_inv_of_mul_eq_one_left h']
        exact Mp.inv_mem hmemMp
      have hmem : x ^ i ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ⊓ Mp := ⟨hxiC, hxiMp⟩
      rw [hB.cent_inf_Mp] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [hxi, one_mul] at h'
    have huj : (u : MulAut W) ^ j = 1 := by
      have h1 : (u : MulAut W) ^ j ∈ conjAutSub t L := by
        rw [eq_inv_of_mul_eq_one_left h']
        exact (conjAutSub t L).inv_mem hukLt
      have hmem : (u : MulAut W) ^ j ∈ L ⊓ conjAutSub t L := ⟨hujL, h1⟩
      rw [hB.hinf] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [huj, one_mul] at h'
    exact ⟨hordx ▸ orderOf_dvd_of_pow_eq_one hxi, hordu ▸ orderOf_dvd_of_pow_eq_one huj,
      hordu' ▸ orderOf_dvd_of_pow_eq_one h'⟩
  have h3 := three_le_pRank_of_commuting hp φ hab hac hbc ⟨nx, hxn⟩ ⟨nu, hun⟩ ⟨nu, hue'⟩
    (by rw [hxk]; exact hx₀p) (by rw [huk]; exact hu₀p) (by rw [hφuh']; exact hu'p) hind
  have h2 := hSQ.sqt p hp hp2
  omega

end D321Base

namespace D321Base

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (hB : D321Base M Mp T L V t)
include hB

theorem eq_one_of_pow_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card ↥L)
    {x : MulAut W} (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) {k : ℕ}
    (hxk : x ^ (p ^ k) = 1) : x = 1 := by
  induction k generalizing x with
  | zero => simpa using hxk
  | succ k ih =>
    have hy : (x ^ (p ^ k)) ^ p = 1 := by rw [← pow_mul, ← pow_succ]; exact hxk
    have hyC : x ^ (p ^ k) ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).pow_mem hx _
    exact ih hx (hB.eq_one_of_pow_prime hp hp2 hpL hyC hy)

theorem mem_Lt_of_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card ↥L)
    {y : MulAut W} (hyM : y ∈ M) (hyL : ∀ l ∈ L, y * l = l * y) {k : ℕ}
    (hyk : y ^ (p ^ k) = 1)
    (hinner : ∃ l' ∈ conjAutSub t L, ∀ m ∈ conjAutSub t L, y * m * y⁻¹ = l' * m * l'⁻¹) :
    y ∈ conjAutSub t L := by
  obtain ⟨l', hl', hconj⟩ := hinner
  set c := l'⁻¹ * y with hc
  have hcLt : ∀ m ∈ conjAutSub t L, c * m = m * c := by
    intro m hm
    have h1 := hconj m hm
    calc c * m = l'⁻¹ * (y * m * y⁻¹) * y := by rw [hc]; group
      _ = l'⁻¹ * (l' * m * l'⁻¹) * y := by rw [h1]
      _ = m * c := by rw [hc]; group
  have hcL : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    have h1 := hyL l hl
    have h2 : l'⁻¹ * l = l * l'⁻¹ := by
      have h3 : l * l' = l' * l := hB.comm l hl l' hl'
      calc l'⁻¹ * l = l'⁻¹ * (l * l') * l'⁻¹ := by group
        _ = l'⁻¹ * (l' * l) * l'⁻¹ := by rw [h3]
        _ = l * l'⁻¹ := by group
    calc c * l = l'⁻¹ * (y * l) := by rw [hc]; group
      _ = l'⁻¹ * (l * y) := by rw [h1]
      _ = (l'⁻¹ * l) * y := by group
      _ = l * c := by rw [h2, hc]; group
  have hcM : c ∈ M := M.mul_mem (M.inv_mem (hB.Lt_le hl')) hyM
  have hcC : c ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
    refine ⟨hcM, Subgroup.mem_centralizer_iff.2 fun m hm => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hm
    rw [mul_assoc, ← hcLt b hb, ← mul_assoc, ← hcL a ha, mul_assoc]
  have hcomm : Commute l' c := (hcLt l' hl').symm
  have hy : y = l' * c := by rw [hc]; group
  have hck : c ^ (p ^ k) = 1 := by
    have h1 : l' ^ (p ^ k) * c ^ (p ^ k) = 1 := by rw [← hcomm.mul_pow, ← hy, hyk]
    have hmemLt : c ^ (p ^ k) ∈ conjAutSub t L := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact (conjAutSub t L).inv_mem ((conjAutSub t L).pow_mem hl' _)
    have hmem : c ^ (p ^ k) ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ⊓ Mp :=
      ⟨(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).pow_mem hcC _, hB.Lt_le_Mp hmemLt⟩
    rw [hB.cent_inf_Mp] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hc1 : c = 1 := hB.eq_one_of_pow_prime_pow hp hp2 hpL hcC hck
  rw [hy, hc1, mul_one]
  exact hl'

end D321Base

end CFSG.Quasithin.SmithD321
