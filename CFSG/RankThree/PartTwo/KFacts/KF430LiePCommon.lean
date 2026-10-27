module

public import CFSG.RankThree.PartTwo.KFacts.KF430LieP

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF430

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

@[expose] def HasMove {L : Type*} [Group L] (V : Subgroup L) : Prop :=
  ∃ n ∈ Subgroup.normalizer (V : Set L),
    (∃ x ∈ V, n ^ 2 * x * (n ^ 2)⁻¹ ≠ x) ∧ (∃ x ∈ V, n ^ 3 * x * (n ^ 3)⁻¹ ≠ x)

@[expose] def E9Move (L : Type*) [Group L] : Prop :=
  ∀ V : Subgroup L, CFSG.Assembly.IsElemAbelian 3 V → Nat.card V = 9 → HasMove V

@[expose] def Concl (L : Type*) [Group L] : Prop :=
  (∀ σ : MulAut L, orderOf σ = 3 → σ ∈ (MulAut.conj : L →* MulAut L).range) ∧
    Subgroup.center L = ⊥ ∧ E9Move L

section Transport

variable {L M : Type*} [Group L] [Group M]

theorem inner_of_mulEquiv (e : L ≃* M)
    (h : ∀ σ : MulAut M, orderOf σ = 3 → σ ∈ (MulAut.conj : M →* MulAut M).range)
    (σ : MulAut L) (hσ : orderOf σ = 3) : σ ∈ (MulAut.conj : L →* MulAut L).range := by
  have hσ' : orderOf (MulAut.congr e σ) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hσ
  obtain ⟨m, hm⟩ := h _ hσ'
  refine ⟨e.symm m, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hm]
  ext y
  simp [MulAut.congr_apply]

theorem center_eq_bot_of_mulEquiv (e : L ≃* M) (h : Subgroup.center M = ⊥) :
    Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.1 hx (e.symm y)
    simpa using congrArg e this
  rw [h, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hx', map_one])

theorem isElemAbelian_map {p : ℕ} (f : L →* M) {V : Subgroup L}
    (hV : CFSG.Assembly.IsElemAbelian p V) : CFSG.Assembly.IsElemAbelian p (V.map f) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hV.2 a ha, map_one]

theorem hasMove_of_injective (f : L →* M) (hf : Function.Injective f) {V : Subgroup L} {n : M}
    (hnf : n ∈ f.range) (hn : ∀ y, y ∈ V.map f ↔ n * y * n⁻¹ ∈ V.map f)
    (h2 : ∃ y ∈ V.map f, n ^ 2 * y * (n ^ 2)⁻¹ ≠ y)
    (h3 : ∃ y ∈ V.map f, n ^ 3 * y * (n ^ 3)⁻¹ ≠ y) : HasMove V := by
  obtain ⟨m, rfl⟩ := hnf
  refine ⟨m, Subgroup.mem_normalizer_iff.2 fun x => ?_, ?_, ?_⟩
  · have := hn (f x)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hf,
      Subgroup.mem_map_iff_mem hf] at this
    exact this
  · obtain ⟨_, ⟨x, hx, rfl⟩, hx2⟩ := h2
    refine ⟨x, hx, fun h => hx2 ?_⟩
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, h]
  · obtain ⟨_, ⟨x, hx, rfl⟩, hx3⟩ := h3
    refine ⟨x, hx, fun h => hx3 ?_⟩
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, h]

theorem HasMove.of_map (e : L ≃* M) {V : Subgroup L} (h : HasMove (V.map e.toMonoidHom)) :
    HasMove V := by
  obtain ⟨n, hn, h2, h3⟩ := h
  refine hasMove_of_injective e.toMonoidHom e.injective ⟨e.symm n, by simp⟩
    (fun y => (Subgroup.mem_normalizer_iff.1 hn y)) h2 h3

theorem E9Move.of_mulEquiv (e : L ≃* M) (h : E9Move M) : E9Move L := fun V hV hV9 =>
  HasMove.of_map e (h (V.map e.toMonoidHom) (isElemAbelian_map e.toMonoidHom hV)
    (by rw [Subgroup.card_map_of_injective e.injective, hV9]))

theorem Concl.of_mulEquiv (e : L ≃* M) (h : Concl M) : Concl L :=
  ⟨inner_of_mulEquiv e h.1, center_eq_bot_of_mulEquiv e h.2.1, E9Move.of_mulEquiv e h.2.2⟩

end Transport

section Std

@[expose] def pairHom {X : Type*} [Group X] (g h : X) (hg : g ^ 3 = 1) (hh : h ^ 3 = 1)
    (hgh : g * h = h * g) : Multiplicative (ZMod 3 × ZMod 3) →* X where
  toFun v := g ^ (Multiplicative.toAdd v).1.val * h ^ (Multiplicative.toAdd v).2.val
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hg, ← pow_eq_pow_mod _ hh, pow_add, pow_add]
    have hc : h ^ (Multiplicative.toAdd v).2.val * g ^ (Multiplicative.toAdd w).1.val =
        g ^ (Multiplicative.toAdd w).1.val * h ^ (Multiplicative.toAdd v).2.val :=
      (Commute.pow_pow (show Commute g h from hgh) _ _).eq.symm
    calc g ^ (Multiplicative.toAdd v).1.val * g ^ (Multiplicative.toAdd w).1.val *
          (h ^ (Multiplicative.toAdd v).2.val * h ^ (Multiplicative.toAdd w).2.val)
        = g ^ (Multiplicative.toAdd v).1.val * (g ^ (Multiplicative.toAdd w).1.val *
          h ^ (Multiplicative.toAdd v).2.val) * h ^ (Multiplicative.toAdd w).2.val := by
          simp only [mul_assoc]
      _ = g ^ (Multiplicative.toAdd v).1.val * (h ^ (Multiplicative.toAdd v).2.val *
          g ^ (Multiplicative.toAdd w).1.val) * h ^ (Multiplicative.toAdd w).2.val := by rw [hc]
      _ = _ := by simp only [mul_assoc]

theorem card_le_nine_of_forall_ne {X : Type*} [Group X] [Finite X]
    (h : ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27)
    (E : Subgroup X) (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have hP : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  by_contra hlt
  push Not at hlt
  have h27 : 3 ^ 3 ≤ Nat.card E := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn] at hlt ⊢
    apply Nat.pow_le_pow_right (by norm_num)
    by_contra hn3
    push Not at hn3
    interval_cases n <;> norm_num at hlt
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hP h27
  have hKe : CFSG.Assembly.IsElemAbelian 3 K := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact hE.1.is_comm.comm (x : E) (y : E)
    · simpa using hE.2 _ (x : E).2
  apply h (K.map E.subtype) (isElemAbelian_map E.subtype hKe)
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  norm_num

theorem zmod3_facts : (∀ a b : ZMod 3, (3 • (a, b) : ZMod 3 × ZMod 3) = 0) ∧
    (1 : ZMod 3).val = 1 ∧ (0 : ZMod 3).val = 0 ∧ (1 : ZMod 3) ≠ 0 ∧ (2 : ZMod 3) ≠ 0 ∧
    (2 : ZMod 3) * 2 = 1 := by
  decide

theorem e9Move_of_std {X : Type*} [Group X] [Finite X]
    (hsyl : ∀ (P : Sylow 3 X) (a b : X), a ∈ (P : Subgroup X) → b ∈ (P : Subgroup X) →
      a * b = b * a)
    (hle : ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {g h σ w : X} (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1) (hgh : g * h = h * g)
    (hinj : ∀ a b : ZMod 3, g ^ a.val * h ^ b.val = 1 → a = 0 ∧ b = 0)
    (hσg : σ * g * σ⁻¹ = h) (hσh : σ * h * σ⁻¹ = g)
    (hwg : w * g * w⁻¹ = g ^ 2) (hwh : w * h * w⁻¹ = h) : E9Move X := by
  obtain ⟨h3, hv1, hv0, h10, h20, h22⟩ := zmod3_facts
  set ψ := pairHom g h hg3 hh3 hgh with hψ
  have hψa : ∀ a b : ZMod 3, ψ (Multiplicative.ofAdd (a, b)) = g ^ a.val * h ^ b.val :=
    fun _ _ => rfl
  have hsplit : ∀ v : Multiplicative (ZMod 3 × ZMod 3),
      ∃ a b : ZMod 3, v = Multiplicative.ofAdd (a, b) :=
    fun v => ⟨(Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2, rfl⟩
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    obtain ⟨a, b, rfl⟩ := hsplit v
    rw [hψa] at hv
    obtain ⟨rfl, rfl⟩ := hinj a b hv
    rfl
  have hTop :
      CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
    obtain ⟨a, b, rfl⟩ := hsplit x
    rw [← ofAdd_nsmul, h3, ofAdd_zero]
  have hE₀ : CFSG.Assembly.IsElemAbelian 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact isElemAbelian_map ψ hTop
  have hE₀9 : Nat.card ψ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 3) ≃ ZMod 3 × ZMod 3),
      Nat.card_prod, Nat.card_zmod]
  have hng : (σ * w) * g * (σ * w)⁻¹ = h ^ 2 := by
    calc (σ * w) * g * (σ * w)⁻¹ = σ * (w * g * w⁻¹) * σ⁻¹ := by group
      _ = (σ * g * σ⁻¹) ^ 2 := by rw [hwg, conj_pow]
      _ = h ^ 2 := by rw [hσg]
  have hnh : (σ * w) * h * (σ * w)⁻¹ = g := by
    calc (σ * w) * h * (σ * w)⁻¹ = σ * (w * h * w⁻¹) * σ⁻¹ := by group
      _ = g := by rw [hwh, hσh]
  have hnψ : ∀ a b : ZMod 3, (σ * w) * ψ (Multiplicative.ofAdd (a, b)) * (σ * w)⁻¹ =
      ψ (Multiplicative.ofAdd (b, 2 * a)) := by
    intro a b
    rw [hψa, hψa]
    have e1 : (σ * w) * (g ^ a.val * h ^ b.val) * (σ * w)⁻¹ =
        ((σ * w) * g * (σ * w)⁻¹) ^ a.val * ((σ * w) * h * (σ * w)⁻¹) ^ b.val := by
      rw [conj_pow, conj_pow]
      group
    rw [e1, hng, hnh, ← pow_mul]
    have e2 : h ^ (2 * a.val) = h ^ (2 * a).val := by
      rw [ZMod.val_mul, pow_eq_pow_mod (2 * a.val) hh3]
      rfl
    rw [e2]
    exact (Commute.pow_pow (show Commute h g from hgh.symm) _ _).eq
  have hnN : σ * w ∈ Subgroup.normalizer (ψ.range : Set X) := by
    have hmem : ∀ k : X, ∀ x ∈ ψ.range, (∀ a b : ZMod 3, k * ψ (Multiplicative.ofAdd (a, b)) *
        k⁻¹ ∈ ψ.range) → k * x * k⁻¹ ∈ ψ.range := by
      rintro k _ ⟨v, rfl⟩ hk
      obtain ⟨a, b, rfl⟩ := hsplit v
      exact hk a b
    have hn : ∀ a b : ZMod 3,
        (σ * w) * ψ (Multiplicative.ofAdd (a, b)) * (σ * w)⁻¹ ∈ ψ.range :=
      fun a b => ⟨_, (hnψ a b).symm⟩
    have hn' : ∀ a b : ZMod 3,
        (σ * w)⁻¹ * ψ (Multiplicative.ofAdd (a, b)) * (σ * w)⁻¹⁻¹ ∈ ψ.range := by
      intro a b
      refine ⟨Multiplicative.ofAdd (2 * b, a), ?_⟩
      have h4 : (2 : ZMod 3) * (2 * b) = b := by
        rw [← mul_assoc, h22, one_mul]
      have := hnψ (2 * b) a
      rw [h4] at this
      rw [inv_inv, ← this]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hmem _ x hx hn, fun hx => ?_⟩
    have := hmem _ _ hx hn'
    simpa [mul_assoc] using this
  have hn2 : (σ * w) ^ 2 * g * ((σ * w) ^ 2)⁻¹ = g ^ 2 := by
    have e : (σ * w) ^ 2 * g * ((σ * w) ^ 2)⁻¹ =
        (σ * w) * ((σ * w) * g * (σ * w)⁻¹) * (σ * w)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, hng, ← conj_pow, hnh]
  have hn3 : (σ * w) ^ 3 * g * ((σ * w) ^ 3)⁻¹ = h := by
    have e : (σ * w) ^ 3 * g * ((σ * w) ^ 3)⁻¹ =
        (σ * w) * ((σ * w) ^ 2 * g * ((σ * w) ^ 2)⁻¹) * (σ * w)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, hn2, ← conj_pow, hng, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hh3,
      one_mul]
  have hgE : g ∈ ψ.range :=
    ⟨Multiplicative.ofAdd (1, 0), by rw [hψa, hv1, hv0, pow_one, pow_zero, mul_one]⟩
  have hg2 : g ^ 2 ≠ g := by
    intro h2
    have h1 : g ^ (1 : ZMod 3).val * h ^ (0 : ZMod 3).val = 1 := by
      have : g = 1 := by
        have := congrArg (· * g⁻¹) h2
        simpa [pow_two] using this
      rw [this, one_pow, one_mul, hv0, pow_zero]
    exact h10 (hinj 1 0 h1).1
  have hhg : h ≠ g := by
    intro hhg
    have h1 : g ^ (2 : ZMod 3).val * h ^ (1 : ZMod 3).val = 1 := by
      rw [hhg]
      change g ^ 2 * g ^ 1 = 1
      rw [← pow_add]
      exact hg3
    exact h20 (hinj 2 1 h1).1
  have hmove₀ : HasMove ψ.range :=
    ⟨σ * w, hnN, ⟨g, hgE, by rw [hn2]; exact hg2⟩, ⟨g, hgE, by rw [hn3]; exact hhg⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro V hV hV9
  have hVp : IsPGroup 3 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hE₀p : IsPGroup 3 ψ.range := fun x => ⟨1, Subtype.ext (by simpa using hE₀.2 x x.2)⟩
  obtain ⟨P, hVP⟩ := hVp.exists_le_sylow
  obtain ⟨P₀, hE₀P₀⟩ := hE₀p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X P₀ P
  have hcP : (P : Subgroup X) = (P₀ : Subgroup X).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    rfl
  set E₁ := ψ.range.map (MulAut.conj c).toMonoidHom with hE₁
  have hE₁P : E₁ ≤ P := hcP ▸ Subgroup.map_mono hE₀P₀
  have hE₁e : CFSG.Assembly.IsElemAbelian 3 E₁ := isElemAbelian_map _ hE₀
  have hE₁9 : Nat.card E₁ = 9 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj c).injective, hE₀9]
  let Ω : Subgroup X :=
    { carrier := {x | x ∈ (P : Subgroup X) ∧ x ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (hsyl P x y hx.1 hy.1) 3), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hΩ : CFSG.Assembly.IsElemAbelian 3 Ω :=
    ⟨⟨⟨fun x y => Subtype.ext (hsyl P x y x.2.1 y.2.1)⟩⟩, fun x hx => hx.2⟩
  have hVΩ : V ≤ Ω := fun x hx => ⟨hVP hx, hV.2 x hx⟩
  have hE₁Ω : E₁ ≤ Ω := fun x hx => ⟨hE₁P hx, hE₁e.2 x hx⟩
  have hVeq : V = Ω := Subgroup.eq_of_le_of_card_ge hVΩ (by rw [hV9]; exact hle Ω hΩ)
  have hE₁eq : E₁ = Ω := Subgroup.eq_of_le_of_card_ge hE₁Ω (by rw [hE₁9]; exact hle Ω hΩ)
  refine HasMove.of_map (MulAut.conj c⁻¹) ?_
  have hid : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id X := by
    ext x
    simp [mul_assoc]
  rw [hVeq, ← hE₁eq, hE₁, Subgroup.map_map, hid, Subgroup.map_id]
  exact hmove₀

theorem e9Move_projImage_of_mats {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {H : Subgroup (GL ι F)} [Finite (CFSG.PGLModel.projImage H)]
    (hsyl : ∀ (Q : Sylow 3 (CFSG.PGLModel.projImage H)) (x y : CFSG.PGLModel.projImage H),
      x ∈ (Q : Subgroup _) → y ∈ (Q : Subgroup _) → x * y = y * x)
    (hle : ∀ E : Subgroup (CFSG.PGLModel.projImage H), CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E ≤ 9)
    {a b s w : GL ι F} (ha : a ∈ H) (hb : b ∈ H) (hs : s ∈ H) (hw : w ∈ H)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hind : ∀ i j : ZMod 3, ∀ c : Fˣ, a ^ i.val * b ^ j.val = Matrix.GeneralLinearGroup.scalar ι c →
      i = 0 ∧ j = 0)
    (hsa : s * a * s⁻¹ = b) (hsb : s * b * s⁻¹ = a) (hwa : w * a * w⁻¹ = a ^ 2)
    (hwb : w * b * w⁻¹ = b) : E9Move (CFSG.PGLModel.projImage H) := by
  set π : H →* CFSG.PGLModel.projImage H :=
    ((Matrix.ProjGenLinGroup.mk : GL ι F →* _).comp H.subtype).codRestrict _
      (fun x => Subgroup.mem_map_of_mem _ x.2) with hπ
  have hπk : ∀ x : H, π x = 1 → ∃ c : Fˣ, (x : GL ι F) = Matrix.GeneralLinearGroup.scalar ι c := by
    intro x hx
    have hx' : x ∈ ((Matrix.ProjGenLinGroup.mk : GL ι F →* _).comp H.subtype).ker :=
      MonoidHom.mem_ker.2 (congrArg Subtype.val hx)
    rw [CFSG.Open.StatedAPI.ker_mk_comp_subtype] at hx'
    obtain ⟨c, hc⟩ := hx'
    exact ⟨c, hc.symm⟩
  set A : H := ⟨a, ha⟩
  set B : H := ⟨b, hb⟩
  set S : H := ⟨s, hs⟩
  set W : H := ⟨w, hw⟩
  refine e9Move_of_std hsyl hle (g := π A) (h := π B) (σ := π S) (w := π W) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, show A ^ 3 = 1 from Subtype.ext ha3, map_one]
  · rw [← map_pow, show B ^ 3 = 1 from Subtype.ext hb3, map_one]
  · rw [← map_mul, ← map_mul, show A * B = B * A from Subtype.ext hab]
  · intro i j hij
    rw [← map_pow, ← map_pow, ← map_mul] at hij
    obtain ⟨c, hc⟩ := hπk _ hij
    exact hind i j c hc
  · rw [← map_inv, ← map_mul, ← map_mul, show S * A * S⁻¹ = B from Subtype.ext hsa]
  · rw [← map_inv, ← map_mul, ← map_mul, show S * B * S⁻¹ = A from Subtype.ext hsb]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, show W * A * W⁻¹ = A ^ 2 from Subtype.ext hwa]
  · rw [← map_inv, ← map_mul, ← map_mul, show W * B * W⁻¹ = B from Subtype.ext hwb]

end Std

@[expose] def KF430LiePG2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (L : Type) [Group L] [Finite L],
    ChevalleyExceptionalModel L .G2 p 1 → Concl L

@[expose] def KF430LiePSp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* projSp 2 (GaloisField p 1)) → Concl L

@[expose] def KF430LiePSU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* projSU 4 p 1) → Concl L

@[expose] def KF430LiePSL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* projSL 4 (GaloisField p 1)) → Concl L

theorem kf430LieP_of_parts (hG2 : KF430LiePG2) (hSp : KF430LiePSp) (hSU : KF430LiePSU)
    (hSL : KF430LiePSL) : KF430LieP := by
  intro p _ hp L _ _ hL
  rcases hL with h | h | ⟨h3, h⟩ | ⟨h3, h⟩
  · exact hG2 p hp L h
  · exact hSp p hp L h
  · exact hSU p hp h3 L h
  · exact hSL p hp h3 L h

end CFSG.RankThree.PartTwo.KFacts.KF430
