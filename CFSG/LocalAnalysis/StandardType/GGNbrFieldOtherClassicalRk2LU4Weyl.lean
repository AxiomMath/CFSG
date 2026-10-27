module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB NbrInnerRest

@[expose] def GGSCWeylIrredTwoLU4 (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 2 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGWeylIrred E

theorem ggNbrExists_move_of_irredTwoLU4 {p : ℕ} (hp : p.Prime) {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (h2 : p ^ 2 ≤ Nat.card A) {W : Set L'}
    (hW2 : ∀ A' : Subgroup (MulAut L'), A' ≤ A →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A)
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A) (ha₁ : a₀ ≠ 1) :
    ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀ := by
  by_contra hcon
  push Not at hcon
  have hz : Subgroup.zpowers a₀ ≤ A := Subgroup.zpowers_le.mpr ha₀
  have hinv : ∀ n ∈ W, ∀ a ∈ Subgroup.zpowers a₀,
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ Subgroup.zpowers a₀ := by
    intro n hn a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hcon n hn) k
  rcases hW2 (Subgroup.zpowers a₀) hz hinv with hbot | htop
  · exact ha₁ (by simpa using hbot)
  · have hcard : Nat.card A = orderOf a₀ := by rw [← htop, Nat.card_zpowers]
    have hdvd : orderOf a₀ ∣ p := orderOf_dvd_of_pow_eq_one (hA.2 a₀ ha₀)
    have hle : orderOf a₀ ≤ p := Nat.le_of_dvd hp.pos hdvd
    have hlt : p < p ^ 2 := by
      have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)
      simpa using this
    omega

theorem ggSCWeylIrredTwoLU4_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGSCWeylIrredTwoLU4 p R') : GGSCWeylIrredTwoLU4 p R := by
  intro E hE h2 hsc
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp b.2
      show (↑a : R') * ↑b = ↑b * ↑a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha' hb']
    · obtain ⟨x', hx', hx'e⟩ := Subgroup.mem_map.mp hx
      rw [← hx'e, ← map_pow, hE.2 x' hx', map_one]
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) e.injective
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    have hg₀ : e.symm g ∈ E := by
      refine hsc (e.symm g) (fun x hx => ?_) (by rw [← map_pow, hgp, map_one])
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨e.symm g, hg₀, by simp⟩
  have hirr : GGWeylIrred (E.map e.toMonoidHom) :=
    h (E.map e.toMonoidHom) hE' (by rw [hcard]; exact h2) hsc'
  have hthis := ggWeylIrred_map e.symm hirr
  have hEE : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  rwa [hEE] at hthis

theorem ggSCWeylIrredTwoLU4_of_centralQuotient {p : ℕ} (hp : p.Prime) {G R : Type} [Group G]
    [Finite G] [Group R] (q : G →* R) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) (hcp : ¬ p ∣ Nat.card (Subgroup.center G))
    (h : GGSCWeylIrredTwoLU4 p G) : GGSCWeylIrredTwoLU4 p R := by
  intro E hE h2 hsc
  let Et : Subgroup G :=
    { carrier := {g | g ^ p = 1 ∧ q g ∈ E}
      one_mem' := ⟨one_pow p, by rw [map_one]; exact E.one_mem⟩
      mul_mem' := by
        intro x y hx hy
        have hxy : Commute x y :=
          commute_of_lift_pow_eq_one hp hker hcp
            (TableB.IsElemAbelian.comm hE hx.2 hy.2) hy.1
        exact ⟨by rw [hxy.mul_pow, hx.1, hy.1, one_mul],
          by rw [map_mul]; exact E.mul_mem hx.2 hy.2⟩
      inv_mem' := by
        intro x hx
        exact ⟨by rw [inv_pow, hx.1, inv_one], by rw [map_inv]; exact E.inv_mem hx.2⟩ }
  have hEt_ab : IsElemAbelian p Et := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.1⟩
    exact commute_of_lift_pow_eq_one hp hker hcp
      (TableB.IsElemAbelian.comm hE a.2.2 b.2.2) b.2.1
  have hcard : Nat.card Et = Nat.card E := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : Et => (⟨q x, x.2.2⟩ : E)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext
        (eq_of_lift_pow_eq_one hp hker hcp (Subtype.ext_iff.mp hxy) x.2.1 y.2.1)
    · intro e
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e e.2)
      exact ⟨⟨x, hxp, hxq ▸ e.2⟩, Subtype.ext hxq⟩
  have hscEt : ∀ g : G, (∀ e ∈ Et, g * e = e * g) → g ^ p = 1 → g ∈ Et := by
    intro g hg hgp
    refine ⟨hgp, ?_⟩
    refine hsc (q g) (fun e he => ?_) (by rw [← map_pow, hgp, map_one])
    obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
    have hxEt : x ∈ Et := ⟨hxp, hxq ▸ he⟩
    have h1 : q (g * x) = q (x * g) := congrArg q (hg x hxEt)
    rwa [map_mul, map_mul, hxq] at h1
  have hmap : Et.map q = E := by
    refine le_antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hxEt, rfl⟩ := Subgroup.mem_map.mp he
      exact hxEt.2
    · intro e he
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
      exact Subgroup.mem_map.mpr ⟨x, ⟨hxp, hxq ▸ he⟩, hxq⟩
  have hirr : GGWeylIrred Et := h Et hEt_ab (by rw [hcard]; exact h2) hscEt
  intro E' hE'E hN
  let Et' : Subgroup G := Et ⊓ E'.comap q
  have hEt'norm : ∀ n ∈ Subgroup.normalizer (Et : Set G), ∀ x ∈ Et', n * x * n⁻¹ ∈ Et' := by
    intro n hn x hx
    have hnE : n * x * n⁻¹ ∈ Et := (Subgroup.mem_normalizer_iff.mp hn x).mp hx.1
    have hqn : q n ∈ Subgroup.normalizer (E : Set R) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact he : e ∈ Et.map q)
        have h1 : n * y * n⁻¹ ∈ Et := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
        have hqy : q (n * y * n⁻¹) = q n * e * (q n)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hyq]
        rw [← hqy]
        exact h1.2
      · intro he
        obtain ⟨y, hy, hyq⟩ :=
          Subgroup.mem_map.mp (by rw [hmap]; exact he : q n * e * (q n)⁻¹ ∈ Et.map q)
        have h1 : n⁻¹ * y * n ∈ Et := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) y).mp hy
          simpa using this
        have hqy : q (n⁻¹ * y * n) = e := by
          rw [map_mul, map_mul, map_inv, hyq]
          group
        rw [← hqy]
        exact h1.2
    refine ⟨hnE, ?_⟩
    show q (n * x * n⁻¹) ∈ E'
    have hconj : q (n * x * n⁻¹) = q n * q x * (q n)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact hN (q n) hqn (q x) hx.2
  rcases hirr Et' inf_le_left hEt'norm with hbot | htop
  · left
    rw [eq_bot_iff]
    intro e he
    obtain ⟨x, hxEt, hxq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact hE'E he : e ∈ Et.map q)
    have hxEt' : x ∈ Et' := ⟨hxEt, by
      show q x ∈ E'
      rw [hxq]
      exact he⟩
    rw [hbot, Subgroup.mem_bot] at hxEt'
    rw [Subgroup.mem_bot]
    rw [← hxq, hxEt', map_one]
  · right
    refine le_antisymm hE'E ?_
    intro e he
    obtain ⟨x, hxEt, hxq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact he : e ∈ Et.map q)
    have hxEt' : x ∈ Et' := by rw [htop]; exact hxEt
    rw [← hxq]
    exact hxEt'.2

theorem ggTorusNoLineTwo_of_scWeylIrredTwoLU4 {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGSCWeylIrredTwoLU4 p R) : GGTorusNoLineTwo p R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI h2 hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hirr : GGWeylIrred E := h E hEab (by rw [hcardE]; exact h2) hscE
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set R) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2' : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2'
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_⟩
  ·
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  ·
    intro _ a₀ ha₀ ha₁
    refine ggNbrExists_move_of_irredTwoLU4 hp hA h2 (fun A' hA'A hinv => ?_) ha₀ ha₁
    set E' : Subgroup R := A'.comap Λ with hE'
    have hE'E : E' ≤ E := fun e he => hA'A he
    have hinvE : ∀ g ∈ Subgroup.normalizer (E : Set R), ∀ e ∈ E', g * e * g⁻¹ ∈ E' := by
      intro g hg e he
      obtain ⟨n, rfl⟩ := hψ g
      have h1 := hinv n (hnorm_to n hg) (Λ e) he
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
      exact h1
    rcases hirr E' hE'E hinvE with hbot | htop
    · left
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a (hA'A ha)
      have he : e ∈ E' := ha
      rw [hbot, Subgroup.mem_bot] at he
      rw [he, map_one]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hA'A fun a ha => ?_
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have he : e ∈ E' := by
        rw [htop]
        exact ha
      exact he

end CFSG.StandardType

end
