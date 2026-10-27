module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Fld
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Ls
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Aut
import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22s218_conj_injective {S : Type*} [Group S]
    (hZ : ∀ s : S, (∀ t, t * s = s * t) → s = 1) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  refine (injective_iff_map_eq_one _).2 fun s hs => hZ s fun t => ?_
  have h := congrArg (fun φ : MulAut S => φ t) hs
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem uc22s218_isElemAbelian_comap_conj {S : Type*} [Group S]
    (hZ : ∀ s : S, (∀ t, t * s = s * t) → s = 1) {p : ℕ} {V : Subgroup (MulAut S)}
    (hV : IsElemAbelian p V) : IsElemAbelian p (V.comap (MulAut.conj : S →* MulAut S)) := by
  have hinj := uc22s218_conj_injective hZ
  have : IsMulCommutative ↥V := hV.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun t ht => ?_⟩
  · apply Subtype.ext
    apply hinj
    have h : MulAut.conj (a : S) * MulAut.conj (b : S) =
        MulAut.conj (b : S) * MulAut.conj (a : S) :=
      congrArg Subtype.val (mul_comm' (⟨_, a.2⟩ : ↥V) ⟨_, b.2⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h
  · apply hinj
    rw [map_pow, map_one]
    exact hV.2 _ ht

theorem uc22s218_card_comap_conj {S Γ : Type*} [Group S] [Finite S] [Group Γ] [IsCyclic Γ] {p : ℕ}
    (hp : p.Prime) (hZ : ∀ s : S, (∀ t, t * s = s * t) → s = 1) (τ : MulAut S →* Γ)
    (hker : ∀ α, τ α = 1 → ∃ s : S, α = MulAut.conj s) (hinn : ∀ s : S, τ (MulAut.conj s) = 1)
    {V : Subgroup (MulAut S)} (hV : IsElemAbelian p V) (hVc : Nat.card V = p ^ 4)
    (hτ : ∃ f ∈ V, τ f ≠ 1) :
    Nat.card (V.comap (MulAut.conj : S →* MulAut S)) = p ^ 3 := by
  classical
  have hinj := uc22s218_conj_injective hZ
  have hVfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 4 hp.ne_zero)
  let g : ↥V →* Γ := τ.domRestrict V
  have hcard := Subgroup.card_ker_mul_card_range g
  have : Finite g.range := Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hrange : Nat.card g.range ∣ p := by
    have hexp : Monoid.exponent g.range ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨v, hv⟩ := x.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hv, ← map_pow]
        have : v ^ p = 1 := Subtype.ext (hV.2 _ v.2)
        rw [this, map_one]
    rwa [IsCyclic.exponent_eq_card] at hexp
  have hrange1 : Nat.card g.range ≠ 1 := by
    intro h1
    obtain ⟨f, hfV, hτf⟩ := hτ
    have hsub : Subsingleton g.range := (Nat.card_eq_one_iff_unique.1 h1).1
    exact hτf (congrArg Subtype.val (Subsingleton.elim (⟨τ f, ⟨f, hfV⟩, rfl⟩ : g.range) 1))
  have hrp : Nat.card g.range = p := ((Nat.dvd_prime hp).1 hrange).resolve_left hrange1
  have hkerc : Nat.card g.ker = p ^ 3 := by
    rw [hrp, hVc] at hcard
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [hcard, pow_succ])
  rw [← hkerc]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : ↥(V.comap (MulAut.conj : S →* MulAut S)) =>
      (⟨⟨MulAut.conj (t : S), t.2⟩, MonoidHom.mem_ker.2 (hinn t)⟩ : g.ker)) ⟨fun a b hab => ?_,
      fun ⟨⟨α, hαV⟩, hk⟩ => ?_⟩)
  · apply Subtype.ext
    exact hinj (congrArg (fun x : g.ker => (x : ↥V).1) hab)
  · obtain ⟨s, rfl⟩ := hker α (MonoidHom.mem_ker.1 hk)
    exact ⟨⟨s, hαV⟩, rfl⟩

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAutHom hypTorus_comm)

variable {K : Type} [Field K] {n : ℕ}

theorem uc22s218_u4_outer_pair_model (h : UnitaryFieldData 2 n K) [Finite K] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥(unitarySU 2 n K 4)) ≤ 3)
    (hZ : ∀ s : ↥(unitarySU 2 n K 4), (∀ t, t * s = s * t) → s = 1)
    (V : Subgroup (MulAut ↥(unitarySU 2 n K 4))) (hV : IsElemAbelian p V)
    (hVc : Nat.card V = p ^ 4) :
    ∃ (E : Subgroup ↥(unitarySU 2 n K 4)) (Q : Subgroup (MulAut ↥(unitarySU 2 n K 4))),
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ V ∧ IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ α ∈ Q, ∃ k : ℕ, ∀ e ∈ E, α e = e ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨τ, hτfield, hτker, hτinn, hτlang⟩ := uc22s218_u4_aut_structure h
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hinj := uc22s218_conj_injective hZ
  obtain ⟨f₀, hf₀V, hτf₀⟩ : ∃ f ∈ V, τ f ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ MonoidHom.range
        (MulAut.conj : ↥(unitarySU 2 n K 4) →* MulAut ↥(unitarySU 2 n K 4)) := by
      intro α hα
      obtain ⟨s, rfl⟩ := hτker α (hcon α hα)
      exact ⟨s, rfl⟩
    have hW4 : Nat.card (V.comap
        (MulAut.conj : ↥(unitarySU 2 n K 4) →* MulAut ↥(unitarySU 2 n K 4))) = p ^ 4 := by
      rw [← hVc, ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hle]
    have := CFSG.SectionRank.le_pRank hp.one_lt le_top
      (uc22s218_isElemAbelian_comap_conj hZ hV) hW4
    omega
  obtain ⟨hθo, s, hfs⟩ := hτlang hp hp2 f₀ (hV.2 f₀ hf₀V) hτf₀
  generalize τ f₀ = θ at hθo hfs hτf₀
  subst hfs
  have hθ1 : θ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hθo
    exact hp.one_lt.ne hθo
  set c : MulAut ↥(unitarySU 2 n K 4) := MulAut.conj s with hc
  let V' : Subgroup (MulAut ↥(unitarySU 2 n K 4)) := V.map (MulAut.conj c⁻¹).toMonoidHom
  have hV'el : IsElemAbelian p V' := CFSG.SectionRank.isElemAbelian_map hV _
  have hV'c : Nat.card V' = p ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hVc]
  have hσV' : uc22s218_u4_field h θ ∈ V' :=
    ⟨_, hf₀V, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hV'comm : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := fun a ha b hb => by
    have : IsMulCommutative ↥V' := hV'el.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥V') ⟨b, hb⟩)
  have hWel := uc22s218_isElemAbelian_comap_conj hZ hV'el
  have hWc := uc22s218_card_comap_conj hp hZ τ hτker hτinn hV'el hV'c
    ⟨uc22s218_u4_field h θ, hσV', by rw [hτfield]; exact hθ1⟩
  have hWθ : ∀ w ∈ V'.comap
      (MulAut.conj : ↥(unitarySU 2 n K 4) →* MulAut ↥(unitarySU 2 n K 4)),
      uc22s218_u4_field h θ w = w := by
    intro w hw
    apply hinj
    rw [← uc22s218_u4_field_conj, hV'comm _ hσV' _ hw]
    group
  obtain ⟨eT, hTeq, y, hyW, hy1, hyT⟩ := uc22s218_u4_fixed_frame h hp hp2 hpq hθo _ hWel hWc hWθ
  obtain ⟨A, hAT, hAel, hAc⟩ := uc22s218_u4_model_elemAbelian h hr hrn
  obtain ⟨j, hj⟩ := uc22s218_u4_fieldAut_pow h (φ := fieldAutHom h 2 0 θ) ⟨θ, rfl⟩
  let E₀ : Subgroup ↥(unitarySU 2 n K 4) := A.map eT.symm.toMonoidHom
  have hE₀el : IsElemAbelian r E₀ := CFSG.SectionRank.isElemAbelian_map hAel _
  have hE₀c : Nat.card E₀ = r ^ 2 := by
    rw [Subgroup.card_map_of_injective eT.symm.injective, hAc]
  have hσE : ∀ e ∈ E₀, uc22s218_u4_field h θ e = e ^ 2 ^ j := by
    rintro _ ⟨a, ha, rfl⟩
    apply eT.injective
    rw [hTeq, MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.apply_symm_apply, hj a (hAT ha)]
  have hcyE : ∀ e ∈ E₀, MulAut.conj y e = e := by
    rintro _ ⟨a, ha, rfl⟩
    apply eT.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    have := hypTorus_comm h hyT (hAT ha)
    rw [this]
    group
  have hσo : orderOf (uc22s218_u4_field h θ) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hθo, pow_orderOf_eq_one, map_one]
    · intro h1
      apply hθ1
      rw [← hτfield θ, h1, map_one]
  have hcyo : orderOf (MulAut.conj y : MulAut ↥(unitarySU 2 n K 4)) = p := by
    refine orderOf_eq_prime (hV'el.2 _ hyW) fun h1 => hy1 (hinj (h1.trans (map_one _).symm))
  have hcyX : (MulAut.conj y : MulAut ↥(unitarySU 2 n K 4)) ∉
      zpowers (uc22s218_u4_field h θ) := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h2 : θ ^ m = 1 := by
      have := congrArg τ hm
      rwa [map_zpow, hτfield, hτinn] at this
    have h3 : ((orderOf (uc22s218_u4_field h θ) : ℕ) : ℤ) ∣ m := by
      rw [hσo, ← hθo]
      exact orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [orderOf_dvd_iff_zpow_eq_one.1 h3] at hm
    exact hy1 (hinj (hm.symm.trans (map_one _).symm))
  have hcom : Commute (uc22s218_u4_field h θ) (MulAut.conj y) := hV'comm _ hσV' _ hyW
  obtain ⟨hQel, hQc⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := p)
    (X := zpowers (uc22s218_u4_field h θ)) (by rw [Nat.card_zpowers, hσo]) hcyo hcyX
    fun a ha => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact (hcom.zpow_left m).eq
  have hQV' : zpowers (uc22s218_u4_field h θ) ⊔ zpowers (MulAut.conj y) ≤ V' :=
    sup_le (Subgroup.zpowers_le.2 hσV') (Subgroup.zpowers_le.2 hyW)
  have : Finite (MulAut ↥(unitarySU 2 n K 4)) :=
    Finite.of_injective (fun φ : MulAut ↥(unitarySU 2 n K 4) => (φ : _ → _)) DFunLike.coe_injective
  have hσpow : ∀ (i : ℕ), ∀ e ∈ E₀, (uc22s218_u4_field h θ ^ i) e = e ^ (2 ^ j) ^ i := by
    intro i e he
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_pow, hσE e he, ← pow_mul, pow_succ']
  have hcypow : ∀ (i : ℕ), ∀ e ∈ E₀, (MulAut.conj y ^ i : MulAut ↥(unitarySU 2 n K 4)) e = e := by
    intro i e he
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih, hcyE e he]
  have hQpow : ∀ β ∈ zpowers (uc22s218_u4_field h θ) ⊔ zpowers (MulAut.conj y),
      ∃ k : ℕ, ∀ e ∈ E₀, β e = e ^ k := by
    intro β hβ
    refine Subgroup.iSup_induction
      (fun b : Bool => cond b (zpowers (uc22s218_u4_field h θ)) (zpowers (MulAut.conj y)))
      (C := fun β : MulAut ↥(unitarySU 2 n K 4) => ∃ k : ℕ, ∀ e ∈ E₀, β e = e ^ k)
      (by rw [iSup_bool_eq]; exact hβ) ?_ ⟨1, fun e _ => by simp⟩ ?_
    · intro b x hx
      cases b
      · obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hx)
        exact ⟨1, fun e he => by rw [hcypow i e he, pow_one]⟩
      · obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hx)
        exact ⟨(2 ^ j) ^ i, fun e he => hσpow i e he⟩
    · rintro x y ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
      exact ⟨k₁ * k₂, fun e he => by rw [MulAut.mul_apply, hk₂ e he, map_pow, hk₁ e he, ← pow_mul,
        mul_comm]⟩
  refine ⟨E₀.map (c : ↥(unitarySU 2 n K 4) ≃* ↥(unitarySU 2 n K 4)).toMonoidHom,
    (zpowers (uc22s218_u4_field h θ) ⊔ zpowers (MulAut.conj y)).map (MulAut.conj c).toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map hE₀el _, ?_, ?_, CFSG.SectionRank.isElemAbelian_map hQel _,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (c : ↥(unitarySU 2 n K 4) ≃* ↥(unitarySU 2 n K 4)).injective,
      hE₀c]
  · rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨α, hα, rfl⟩ := hQV' hβ
    have : (MulAut.conj c).toMonoidHom ((MulAut.conj c⁻¹).toMonoidHom α) = α := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hα
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hQc]
  · rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨k, hk⟩ := hQpow β hβ
    refine ⟨k, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
    rw [hk e he, map_pow]

theorem uc22s218_outer_pair_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (f : Y ≃* Y')
    {p r : ℕ}
    (H : ∀ V' : Subgroup (MulAut Y'), IsElemAbelian p V' → Nat.card V' = p ^ 4 →
      ∃ (E : Subgroup Y') (Q : Subgroup (MulAut Y')), IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
        Q ≤ V' ∧ IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
        ∀ α ∈ Q, ∃ k : ℕ, ∀ e ∈ E, α e = e ^ k)
    (V : Subgroup (MulAut Y)) (hV : IsElemAbelian p V) (hVc : Nat.card V = p ^ 4) :
    ∃ (E : Subgroup Y) (Q : Subgroup (MulAut Y)), IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      Q ≤ V ∧ IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ α ∈ Q, ∃ k : ℕ, ∀ e ∈ E, α e = e ^ k := by
  obtain ⟨E', Q', hE', hE'c, hQ'V, hQ', hQ'c, hpow⟩ := H (V.map (MulAut.congr f).toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hV _)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr f).injective, hVc])
  refine ⟨E'.map f.symm.toMonoidHom, Q'.map (MulAut.congr f.symm).toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map hE' _,
    by rw [Subgroup.card_map_of_injective f.symm.injective, hE'c], ?_,
    CFSG.SectionRank.isElemAbelian_map hQ' _,
    by rw [Subgroup.card_map_of_injective (MulAut.congr f.symm).injective, hQ'c], ?_⟩
  · rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨α, hα, rfl⟩ := hQ'V hβ
    have : (MulAut.congr f.symm).toMonoidHom ((MulAut.congr f).toMonoidHom α) = α := by
      ext x
      simp [MulAut.congr_apply]
    rw [this]
    exact hα
  · rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨k, hk⟩ := hpow β hβ
    refine ⟨k, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    simp [MulAut.congr_apply, hk e he]

theorem uc22s218_u4_outer_pair {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n) {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1)
    (V : Subgroup (MulAut Y)) (hV : IsElemAbelian p V) (hVc : Nat.card V = p ^ 4) :
    ∃ (E : Subgroup Y) (Q : Subgroup (MulAut Y)), IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      Q ≤ V ∧ IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ α ∈ Q, ∃ k : ℕ, ∀ e ∈ E, α e = e ^ k := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  have := h.finite
  obtain ⟨T, hT⟩ := exists_isGramHypTransport (r := 2) (ε := 0) h (1 : Matrix (Fin 4) (Fin 4) K)
    (by simp) (by simp)
  let eU : ↥(unitarySU 2 n K 4) ≃* ↥(hypSU h 2 0) :=
    (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 4)).trans
      (gramHypEquiv (r := 2) (ε := 0) h (1 : Matrix (Fin 4) (Fin 4) K) hT)
  let f : Y ≃* ↥(unitarySU 2 n K 4) := e.symm.trans eU.symm
  refine uc22s218_outer_pair_of_mulEquiv f (fun V' hV' hV'c => ?_) V hV hVc
  refine uc22s218_u4_outer_pair_model h hp hp2 hpq hr hrn ?_ ?_ V' hV' hV'c
  · obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (⊤ : Subgroup ↥(unitarySU 2 n K 4))
    exact (CFSG.SectionRank.le_pRank hp.one_lt (le_top : E.map f.symm.toMonoidHom ≤ ⊤)
      (CFSG.SectionRank.isElemAbelian_map hE _)
      (by rw [Subgroup.card_map_of_injective f.symm.injective, hEc])).trans
      (uc22s218_u4_pRank_le_three hY hp hp2)
  · exact fun s hs => FieldBorel.center_eq_one
      (FieldBorel.of_mulEquiv (uc22s218_u4_fieldBorel hY) f) s fun x => (hs x).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
