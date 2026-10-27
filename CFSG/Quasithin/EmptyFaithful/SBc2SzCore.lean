module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G3a
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped Pointwise

namespace SBc2

theorem fixed_modEq {S : Type*} [Finite S] (f : S → S) (hf : ∀ s, f (f (f s)) = s) :
    Nat.card S ≡ Nat.card {s : S // f s = s} [MOD 3] := by
  classical
  have := Fintype.ofFinite S
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F : Function.End S := f
  have hF : F ^ 3 ^ 1 = 1 := by
    funext s
    simp only [pow_one]
    show f (f (f s)) = s
    exact hf s
  have h := Equiv.Perm.card_fixedPoints_modEq hF
  have e1 : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  have e2 : Nat.card {s : S // f s = s} = Fintype.card ↑(Function.fixedPoints F) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [e1, e2]
  exact h

theorem two_pow_mod_three {e : ℕ} (he : Odd e) : 2 ^ e % 3 = 2 := by
  obtain ⟨k, rfl⟩ := he
  rw [pow_succ, pow_mul]
  have : (2 ^ 2) ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem isSz_equiv {X : Type} [Group X] {e : ℕ} (h : IsSz e X) :
    ∃ a : ℕ, 1 ≤ a ∧ e = 2 * a + 1 ∧ Nonempty (X ≃* Sz a) := by
  obtain ⟨-, a, ha, K, _, _, he, hcard, ⟨φ⟩⟩ := h
  refine ⟨a, ha, he, ⟨?_⟩⟩
  exact φ.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha (he ▸ hcard)))

theorem exists_data {X : Type} [Group X]
    [Finite X] {e : ℕ} (h : IsSz e X) (T : Sylow 2 X) :
    Odd e ∧ IsSimpleGroup X ∧ ∃ D : Subgroup X, BorelSetup T D ∧
      Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ e ∧ Nat.card (T : Subgroup X) = (2 ^ e) ^ 2 ∧
        Nat.card D = 2 ^ e - 1 := by
  have hsimple : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 e h).2
  obtain ⟨a, ha, rfl, ⟨φ⟩⟩ := isSz_equiv h
  have hX : fusionIsBenderGroup X := Or.inr (Or.inr ⟨a, ha, ⟨φ⟩⟩)
  obtain ⟨D, hD⟩ := exists_borelSetup hX T
  exact ⟨⟨a, by ring⟩, hsimple, D, hD, hD.orders_sz ha φ⟩

section Action

variable {X : Type} [Group X]

theorem mem_smul_sylow_iff (α : MulAut X) (Q : Sylow 2 X) (x : X) :
    x ∈ ((α • Q : Sylow 2 X) : Subgroup X) ↔ α⁻¹ x ∈ (Q : Subgroup X) := by
  rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem smul_smul_sylow (α : MulAut X) (g : X) (Q : Sylow 2 X) :
    α • (g • Q) = (α g) • (α • Q) := by
  rw [Sylow.smul_def, Sylow.smul_def, ← mul_smul, ← mul_smul]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem apply_mem_normalizer_of_smul_eq {α : MulAut X} {Q : Sylow 2 X} (h : α • Q = Q) {x : X}
    (hx : x ∈ Subgroup.normalizer (Q : Set X)) : α x ∈ Subgroup.normalizer (Q : Set X) := by
  rw [← Sylow.smul_eq_iff_mem_normalizer] at hx ⊢
  have := smul_smul_sylow α x Q
  rw [h, hx, h] at this
  exact this.symm

theorem apply_mem_of_comm {T : Sylow 2 X} {α : MulAut X}
    (hcomm : ∀ b ∈ Subgroup.normalizer ((T : Subgroup X) : Set X), b⁻¹ * α b ∈ (T : Subgroup X))
    {t : X} (ht : t ∈ (T : Subgroup X)) : α t ∈ (T : Subgroup X) := by
  have h := (T : Subgroup X).mul_mem ht (hcomm t (Subgroup.le_normalizer ht))
  simpa using h

theorem smul_sylow_eq_of_comm {T : Sylow 2 X} {α : MulAut X}
    (hcomm : ∀ b ∈ Subgroup.normalizer ((T : Subgroup X) : Set X), b⁻¹ * α b ∈ (T : Subgroup X)) :
    α • T = T := by
  have hle : ((α • T : Sylow 2 X) : Subgroup X) ≤ (T : Subgroup X) := by
    intro x hx
    rw [mem_smul_sylow_iff] at hx
    simpa using apply_mem_of_comm hcomm hx
  exact Sylow.ext ((α • T).is_maximal' T.isPGroup' hle).symm

end Action

section Core

variable {X : Type} [Group X] [Finite X]

theorem core_fixed [IsSimpleGroup X] {T T' : Sylow 2 X} {D : Subgroup X} (hD : BorelSetup T D) {e : ℕ}
    (he : Odd e) (hZ : Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ e)
    (hT : Nat.card (T : Subgroup X) = (2 ^ e) ^ 2) (hDc : Nat.card D = 2 ^ e - 1) (hT'ne : T' ≠ T)
    (hinf : Subgroup.normalizer ((T : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((T' : Subgroup X) : Set X) = D)
    (α : MulAut X) (hα3 : α * α * α = 1)
    (hcomm : ∀ b ∈ Subgroup.normalizer ((T : Subgroup X) : Set X), b⁻¹ * α b ∈ (T : Subgroup X))
    (hfix : α • T' = T') : α = 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod2 := two_pow_mod_three he
  have hα3' : ∀ x, α (α (α x)) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hα3
    simpa using this
  set Tg : Subgroup X := (T : Subgroup X) with hTg
  set Zs : Subgroup X := sylowCenter Tg with hZs
  have hTN : Tg ≤ Subgroup.normalizer (Tg : Set X) := Subgroup.le_normalizer
  have hαT_mem : ∀ t ∈ Tg, α t ∈ Tg := fun t ht => apply_mem_of_comm hcomm ht
  have hαT : α • T = T := smul_sylow_eq_of_comm hcomm
  have hαT_iff : ∀ x, α x ∈ Tg ↔ x ∈ Tg := by
    intro x
    refine ⟨fun hx => ?_, hαT_mem x⟩
    have : α x ∈ ((α • T : Sylow 2 X) : Subgroup X) := by rw [hαT]; exact hx
    rw [mem_smul_sylow_iff] at this
    simpa using this
  have hαN : ∀ x ∈ Subgroup.normalizer (Tg : Set X), α x ∈ Subgroup.normalizer (Tg : Set X) :=
    fun x hx => apply_mem_normalizer_of_smul_eq hαT hx
  have hαD : ∀ d ∈ D, α d ∈ D := by
    intro d hd
    rw [← hinf] at hd ⊢
    exact ⟨hαN d hd.1, apply_mem_normalizer_of_smul_eq hfix hd.2⟩
  have hcentD : ∀ d ∈ D, α d = d := by
    intro d hd
    have h1 : d⁻¹ * α d ∈ Tg := hcomm d (hD.le hd)
    have h2' : d⁻¹ * α d ∈ D := D.mul_mem (D.inv_mem hd) (hαD d hd)
    have h3 : d⁻¹ * α d ∈ Tg ⊓ D := ⟨h1, h2'⟩
    rw [hD.inf, Subgroup.mem_bot] at h3
    exact (inv_mul_eq_one.mp h3).symm
  have hαZ : ∀ z ∈ Zs, α z ∈ Zs := by
    intro z hz
    rw [hZs, mem_sylowCenter] at hz ⊢
    refine ⟨hαT_mem z hz.1, fun t ht => ?_⟩
    have ht' : α⁻¹ t ∈ Tg := by
      refine (hαT_iff _).mp ?_
      simpa using ht
    have h := congrArg α (hz.2 (α⁻¹ t) ht')
    simpa using h
  have hZfix : ∀ z ∈ Zs, α z = z := by
    have hex : ∃ z ∈ Zs, z ≠ 1 ∧ α z = z := by
      by_contra hno
      push Not at hno
      let f : Zs → Zs := fun z => ⟨α z, hαZ z z.2⟩
      have hf : ∀ s, f (f (f s)) = s := fun s => Subtype.ext (hα3' s)
      have hm := fixed_modEq f hf
      have hcard1 : Nat.card {s : Zs // f s = s} = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, ?_⟩⟩⟩
        · have ha : (a.1 : X) = 1 := by
            by_contra hne
            exact hno a.1 a.1.2 hne (congrArg Subtype.val a.2)
          have hb : (b.1 : X) = 1 := by
            by_contra hne
            exact hno b.1 b.1.2 hne (congrArg Subtype.val b.2)
          exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
        · exact Subtype.ext (map_one α)
      rw [hcard1, hZ, Nat.ModEq] at hm
      omega
    obtain ⟨z, hz, hz1, hαz⟩ := hex
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact map_one α
    · obtain ⟨d, hd, hdw⟩ := hD.trans hz hw hz1 hw1
      rw [← hdw, map_mul, map_mul, map_inv, hcentD d hd, hαz]
  have hcentral : ∀ z ∈ Zs, ∀ t ∈ Tg, t * z = z * t := fun z hz t ht =>
    (mem_sylowCenter.mp hz).2 t ht
  let Y : Subgroup X :=
    { carrier := {t | t ∈ Tg ∧ t⁻¹ * α t ∈ Zs}
      mul_mem' := by
        rintro s t ⟨hs, hsz⟩ ⟨ht, htz⟩
        refine ⟨Tg.mul_mem hs ht, ?_⟩
        have hc : t⁻¹ * (s⁻¹ * α s) = (s⁻¹ * α s) * t⁻¹ := hcentral _ hsz _ (Tg.inv_mem ht)
        have e : (s * t)⁻¹ * α (s * t) = (s⁻¹ * α s) * (t⁻¹ * α t) := by
          calc (s * t)⁻¹ * α (s * t) = (t⁻¹ * (s⁻¹ * α s)) * α t := by simp [mul_assoc]
            _ = ((s⁻¹ * α s) * t⁻¹) * α t := by rw [hc]
            _ = (s⁻¹ * α s) * (t⁻¹ * α t) := by simp [mul_assoc]
        rw [e]
        exact Zs.mul_mem hsz htz
      one_mem' := ⟨Tg.one_mem, by simp⟩
      inv_mem' := by
        rintro t ⟨ht, htz⟩
        refine ⟨Tg.inv_mem ht, ?_⟩
        have hc : t * (t⁻¹ * α t)⁻¹ = (t⁻¹ * α t)⁻¹ * t := hcentral _ (Zs.inv_mem htz) _ ht
        have e : t⁻¹⁻¹ * α t⁻¹ = (t⁻¹ * α t)⁻¹ := by
          calc t⁻¹⁻¹ * α t⁻¹ = t * (α t)⁻¹ := by simp
            _ = t * (t⁻¹ * α t)⁻¹ * t⁻¹ := by simp [mul_assoc]
            _ = (t⁻¹ * α t)⁻¹ * t * t⁻¹ := by rw [hc]
            _ = (t⁻¹ * α t)⁻¹ := by simp
        rw [e]
        exact Zs.inv_mem htz }
  have hZY : Zs ≤ Y := fun z hz =>
    ⟨(mem_sylowCenter.mp hz).1, by rw [hZfix z hz]; simp⟩
  have hYT : Y ≤ Tg := fun t ht => ht.1
  have hDY : D ≤ Subgroup.normalizer (Y : Set X) := by
    intro d hd
    refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨hyT, hyz⟩ := hy
    have hdN : d ∈ Subgroup.normalizer (Tg : Set X) := hD.le hd
    refine ⟨(Subgroup.mem_normalizer_iff.mp hdN y).mp hyT, ?_⟩
    have e : (d * y * d⁻¹)⁻¹ * α (d * y * d⁻¹) = d * (y⁻¹ * α y) * d⁻¹ := by
      rw [map_mul, map_mul, map_inv, hcentD d hd]
      simp [mul_assoc]
    rw [e]
    exact hD.conj_mem_center hd hyz
  have hcase : (Nat.card Tg = Nat.card Zs ^ 2 ∧ Nat.card D = Nat.card Zs - 1) ∨
      (Nat.card Tg = Nat.card Zs ^ 3 ∧ Nat.card D = (Nat.card Zs ^ 2 - 1) / Nat.gcd 3 (Nat.card Zs + 1)) :=
    Or.inl ⟨by rw [hT, hZ], by rw [hDc, hZ]⟩
  have hTfix : ∀ t ∈ Tg, α t = t := by
    rcases hD.eq_or_eq_of_invariant hcase hZY hYT hDY with hYZ | hYT'
    · exfalso
      let f : Tg → Tg := fun t => ⟨α t, hαT_mem t t.2⟩
      have hf : ∀ s, f (f (f s)) = s := fun s => Subtype.ext (hα3' s)
      have hm := fixed_modEq f hf
      have hcardF : Nat.card {s : Tg // f s = s} = Nat.card Zs := by
        refine Nat.card_congr
          { toFun := fun s => ⟨s.1.1, ?_⟩
            invFun := fun z => ⟨⟨z.1, (mem_sylowCenter.mp z.2).1⟩, Subtype.ext (hZfix z.1 z.2)⟩
            left_inv := fun s => rfl
            right_inv := fun z => rfl }
        have hy : (s.1 : X) ∈ Y := ⟨s.1.2, by
          have : α (s.1 : X) = s.1 := congrArg Subtype.val s.2
          rw [this]
          simp⟩
        rw [hYZ] at hy
        exact hy
      rw [hcardF, hT, hZ, Nat.ModEq, Nat.pow_mod, hmod2] at hm
      omega
    · intro t ht
      have htY : t ∈ Y := by rw [hYT']; exact ht
      obtain ⟨-, hz⟩ := htY
      set z := t⁻¹ * α t with hzdef
      have hαt : α t = t * z := by rw [hzdef]; simp
      have hαz : α z = z := hZfix z hz
      have h1 : α (t * z) = t * z * z := by rw [map_mul, hαt, hαz]
      have h3 : α (α (α t)) = t * z ^ 3 := by
        calc α (α (α t)) = α (α (t * z)) := by rw [hαt]
          _ = α (t * z * z) := by rw [h1]
          _ = α (t * z) * α z := by rw [map_mul]
          _ = t * z ^ 3 := by rw [h1, hαz, pow_three]; simp only [mul_assoc]
      rw [hα3' t] at h3
      have hz3 : z ^ 3 = 1 := by
        have : t * z ^ 3 = t * 1 := by rw [← h3]; simp
        exact mul_left_cancel this
      have hz1 : z = 1 :=
        BorelSetup.eq_one_of_pow_odd (T := T) (mem_sylowCenter.mp hz).1 (by decide : Odd 3) hz3
      rw [hz1] at hαt
      simpa using hαt
  have hNfix : ∀ b ∈ Subgroup.normalizer (Tg : Set X), α b = b := by
    intro b hb
    obtain ⟨t, ht, d, hd, rfl⟩ := hD.exists_mul hb
    rw [map_mul, hTfix t ht, hcentD d hd]
  have hall : ∀ Q : Sylow 2 X, α • Q = Q := by
    intro Q
    by_cases hQ : Q = T
    · rw [hQ]
      exact hαT
    · obtain ⟨t, ht, rfl⟩ := hD.exists_smul hT'ne hQ
      rw [smul_smul_sylow, hTfix t ht, hfix]
  have hker : ∀ x : X, α x = x := by
    intro x
    have hg : ∀ Q : Sylow 2 X, (x⁻¹ * α x) • Q = Q := by
      intro Q
      have h1 := smul_smul_sylow α x Q
      rw [hall (x • Q), hall Q] at h1
      rw [mul_smul, ← h1]
      simp
    have hK : (MulAction.toPermHom X (Sylow 2 X)).ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (MulAction.toPermHom X (Sylow 2 X)).ker with hK | hK
      · exact hK
      · exfalso
        apply hD.se.1
        rw [eq_top_iff]
        intro g _
        have : g ∈ (MulAction.toPermHom X (Sylow 2 X)).ker := by rw [hK]; exact Subgroup.mem_top g
        have h := congrArg (fun π : Equiv.Perm (Sylow 2 X) => π T) (MonoidHom.mem_ker.mp this)
        exact Sylow.smul_eq_iff_mem_normalizer.mp (by simpa using h)
    have : x⁻¹ * α x ∈ (MulAction.toPermHom X (Sylow 2 X)).ker := by
      rw [MonoidHom.mem_ker]
      exact Equiv.Perm.ext fun Q => by simpa using hg Q
    rw [hK, Subgroup.mem_bot] at this
    exact (inv_mul_eq_one.mp this).symm
  exact MulEquiv.ext fun x => by simpa using hker x

theorem core_sz {X : Type} [Group X]
    [Finite X] {e : ℕ} (h : IsSz e X) (T : Sylow 2 X) (α : MulAut X) (hα3 : α * α * α = 1)
    (hcomm : ∀ b ∈ Subgroup.normalizer ((T : Subgroup X) : Set X), b⁻¹ * α b ∈ (T : Subgroup X)) :
    α = 1 := by
  obtain ⟨he, hsimple, D, hD, hZ, hT, hDc⟩ := exists_data h T
  have := hsimple
  have hmod2 := two_pow_mod_three he
  obtain ⟨T', hT'ne, hDT'⟩ := hD.exists_fixed
  have hinf := hD.normalizer_inf_eq hT'ne hDT'
  have hαT : α • T = T := smul_sylow_eq_of_comm hcomm
  have hex : ∃ T₁ : Sylow 2 X, α • T₁ = T₁ ∧ T₁ ≠ T := by
    by_contra hno
    push Not at hno
    let f : Sylow 2 X → Sylow 2 X := fun Q => α • Q
    have hf : ∀ Q, f (f (f Q)) = Q := fun Q => by
      show α • (α • (α • Q)) = Q
      rw [← mul_smul, ← mul_smul, hα3, one_smul]
    have hm := fixed_modEq f hf
    have hcard1 : Nat.card {Q : Sylow 2 X // f Q = Q} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨T, hαT⟩⟩⟩
      have ha : a.1 = T := hno a.1 a.2
      have hb : b.1 = T := hno b.1 b.2
      exact Subtype.ext (ha.trans hb.symm)
    have hΩ : Nat.card (Sylow 2 X) = (2 ^ e) ^ 2 + 1 := by rw [hD.card, hT]
    have hsq : (2 ^ e) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hmod2]
    rw [hcard1, hΩ, Nat.ModEq] at hm
    omega
  obtain ⟨T₁, hT₁fix, hT₁ne⟩ := hex
  obtain ⟨t, ht, hT₁t⟩ := hD.exists_smul hT'ne hT₁ne
  set c : MulAut X := MulAut.conj t with hc
  set β : MulAut X := c⁻¹ * α * c with hβ
  have hβ3 : β * β * β = 1 := by
    calc β * β * β = c⁻¹ * (α * α * α) * c := by rw [hβ]; group
      _ = 1 := by rw [hα3]; group
  have hβcomm : ∀ b ∈ Subgroup.normalizer ((T : Subgroup X) : Set X),
      b⁻¹ * β b ∈ (T : Subgroup X) := by
    intro b hb
    have hv : t⁻¹ * α t ∈ (T : Subgroup X) := hcomm t (Subgroup.le_normalizer ht)
    have hu : b⁻¹ * α b ∈ (T : Subgroup X) := hcomm b hb
    have e : β b = t⁻¹ * (α t * α b * (α t)⁻¹) * t := by
      rw [hβ, hc]
      simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    have hβb : β b = (t⁻¹ * α t) * b * (b⁻¹ * α b) * (t⁻¹ * α t)⁻¹ := by
      rw [e]
      group
    rw [hβb]
    have e2 : b⁻¹ * ((t⁻¹ * α t) * b * (b⁻¹ * α b) * (t⁻¹ * α t)⁻¹) =
        (b⁻¹ * (t⁻¹ * α t) * b) * (b⁻¹ * α b) * (t⁻¹ * α t)⁻¹ := by group
    rw [e2]
    have hbinv : b⁻¹ ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) :=
      (Subgroup.normalizer ((T : Subgroup X) : Set X)).inv_mem hb
    have hconj : b⁻¹ * (t⁻¹ * α t) * b ∈ (T : Subgroup X) := by
      have := (Subgroup.mem_normalizer_iff.mp hbinv (t⁻¹ * α t)).mp hv
      simpa [mul_assoc] using this
    exact (T : Subgroup X).mul_mem ((T : Subgroup X).mul_mem hconj hu)
      ((T : Subgroup X).inv_mem hv)
  have hβfix : β • T' = T' := by
    have hcT : c • T' = T₁ := hT₁t
    rw [hβ, mul_smul, mul_smul, hcT, hT₁fix, ← hcT, inv_smul_smul]
  have hβ1 := core_fixed hD he hZ hT hDc hT'ne hinf β hβ3 hβcomm hβfix
  have : α = c * β * c⁻¹ := by rw [hβ]; group
  rw [this, hβ1]
  group

end Core

structure SzBorelFacts (X : Type) [Group X] (T : Subgroup X) : Prop where
  coatom : IsCoatom (Subgroup.normalizer (T : Set X))
  cent : Subgroup.centralizer (T : Set X) ≤ T
  solv : ∀ H : Subgroup X, Group.IsSolvable ↥H → T ≤ H → H ≤ Subgroup.normalizer (T : Set X)
  card3 : ¬ 3 ∣ Nat.card X
  core : ∀ α : MulAut X, α * α * α = 1 →
    (∀ b ∈ Subgroup.normalizer (T : Set X), b⁻¹ * α b ∈ T) → α = 1

theorem not_isSolvable_of_borelSetup {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {T : Sylow 2 X}
    {D : Subgroup X} (hD : BorelSetup T D) : ¬ Group.IsSolvable X := by
  intro hs
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  apply hD.se.1
  rw [eq_top_iff]
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e : g * x * g⁻¹ = x := by rw [hcomm g x]; group
  rw [e]

theorem szBorelFacts_of_isSz {X : Type}
    [Group X] [Finite X] {e : ℕ} (h : IsSz e X) (T : Sylow 2 X) :
    SzBorelFacts X (T : Subgroup X) := by
  obtain ⟨he, hsimple, D, hD, hZ, hT, hDc⟩ := exists_data h T
  have := hsimple
  have hmod2 := two_pow_mod_three he
  refine ⟨hD.isCoatom, hD.cent, ?_, ?_, fun α hα3 hcomm => core_sz h T α hα3 hcomm⟩
  · intro H hH hTH
    refine hD.le_normalizer_of_le hTH fun hHtop => ?_
    apply not_isSolvable_of_borelSetup hD
    rw [hHtop] at hH
    exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom)
      Subgroup.topEquiv.surjective
  · have hc := hD.card_eq
    rw [hT, hDc] at hc
    intro hdvd
    rw [hc] at hdvd
    generalize 2 ^ e = q at hc hmod2 hdvd
    have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hmod2]
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
      · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
        omega
      · omega
    · omega


end SBc2

end CFSG.Quasithin
