module

public import CFSG.Milestones.ASVolI.F431.BF436Final

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def burnsideF4m_F436U5_A : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .U5 2 1 Gp M₁ M₂ →
    ∀ a b t : E, a ∈ M₁ → b ∈ M₁ → t ∈ M₁ → a * a = 1 → b * b = 1 → a * b = b * a →
      t * a * t⁻¹ = b → t * b * t⁻¹ = a * b → t ^ 3 = 1 → a ∈ pCoreOf 2 M₁

@[expose] def burnsideF4m_F436U5_B : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂),
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
      ∀ fb ∈ Tb, hyp.toHypF_4_4g.chart.IsGraphInv fb →
        ∃ r ∈ Tb, (∃ g : E, g * fb * g⁻¹ = r) ∧
          ∃ v t x : E, v ∈ cenIn (Gp ⊓ (M₁ ⊓ M₂)) r ∧ t ∈ cenIn (Gp ⊓ M₂) r ∧
            x ∈ cenIn (Gp ⊓ M₁) r ∧ v * v = 1 ∧ t ^ 3 = 1 ∧
            v * (t * v * t⁻¹) = t * v * t⁻¹ * v ∧
            t * (t * v * t⁻¹) * t⁻¹ = v * (t * v * t⁻¹) ∧
            (v * (x * v * x⁻¹)) ^ 3 = 1 ∧ v * (x * v * x⁻¹) ≠ 1

theorem burnsideF4m_A4_conj {E M : Type} [Group E] [Group M] {M₁ : Subgroup E} (b : ↥M₁ →* M)
    (hb : Function.Injective b) (y : M)
    (hA : ∀ a c t : E, a ∈ M₁ → c ∈ M₁ → t ∈ M₁ → a * a = 1 → c * c = 1 → a * c = c * a →
      t * a * t⁻¹ = c → t * c * t⁻¹ = a * c → t ^ 3 = 1 → a ∈ pCoreOf 2 M₁)
    {a c t : M} (ha : a ∈ conjSub y (subImg b M₁)) (hc : c ∈ conjSub y (subImg b M₁))
    (ht : t ∈ conjSub y (subImg b M₁)) (h1 : a * a = 1) (h2 : c * c = 1) (h3 : a * c = c * a)
    (h4 : t * a * t⁻¹ = c) (h5 : t * c * t⁻¹ = a * c) (h6 : t ^ 3 = 1) :
    a ∈ pCoreOf 2 (conjSub y (subImg b M₁)) := by
  set φ : ↥M₁ →* M := (MulAut.conj y).toMonoidHom.comp b with hφ
  have hφinj : Function.Injective φ := (MulAut.conj y).injective.comp hb
  have hpull : ∀ {w : M}, w ∈ conjSub y (subImg b M₁) → ∃ w₀ : ↥M₁, φ w₀ = w := by
    intro w hw
    rw [mem_conjSub] at hw
    obtain ⟨w₀, hw₀, -, hbw⟩ := mem_subImg.mp hw
    refine ⟨⟨w₀, hw₀⟩, ?_⟩
    simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hbw]
    group
  obtain ⟨a₀, rfl⟩ := hpull ha
  obtain ⟨c₀, rfl⟩ := hpull hc
  obtain ⟨t₀, rfl⟩ := hpull ht
  have e1 : a₀ * a₀ = 1 := hφinj (by rw [map_mul, h1, map_one])
  have e2 : c₀ * c₀ = 1 := hφinj (by rw [map_mul, h2, map_one])
  have e3 : a₀ * c₀ = c₀ * a₀ := hφinj (by rw [map_mul, map_mul, h3])
  have e4 : t₀ * a₀ * t₀⁻¹ = c₀ := hφinj (by rw [map_mul, map_mul, map_inv, h4])
  have e5 : t₀ * c₀ * t₀⁻¹ = a₀ * c₀ := hφinj (by rw [map_mul, map_mul, map_inv, map_mul, h5])
  have e6 : t₀ ^ 3 = 1 := hφinj (by rw [map_pow, h6, map_one])
  have hmem := hA a₀ c₀ t₀ a₀.2 c₀.2 t₀.2 (congrArg Subtype.val e1) (congrArg Subtype.val e2)
    (congrArg Subtype.val e3) (congrArg Subtype.val e4) (congrArg Subtype.val e5)
    (by simpa using congrArg Subtype.val e6)
  rw [pCoreOf_conjSub, subImg_pCoreOf hb le_rfl, mem_conjSub]
  have : y⁻¹ * φ a₀ * y = b a₀ := by
    simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [this]
  exact mem_subImg_of_mem b a₀.2 hmem

section F436U5

set_option linter.unusedSectionVars false


theorem burnsideF4m_F436U5_of (ha : burnsideF4m_F436U5_A) (hb : burnsideF4m_F436U5_B) :
    burnsideF4m_F436U5 := by
  intro f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hf1 chart Tb hTb fb hfbT hgraph hconj
  subst hf1
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrT, ⟨g, hg⟩, v, t, x, hv, ht, hx, hv2, ht3, hvv, htv, hw3, hw1⟩ :=
    hb E Gp M₁ M₂ hyp.amalgam Tb hTb (fb : E) hfbT hgraph
  have hrM : r ∈ M₁ ⊓ M₂ := hTb.1 hrT
  set rr : ↥(M₁ ⊓ M₂) := ⟨r, hrM⟩ with hrr
  obtain ⟨h, hh⟩ := as_F_4_30 .U5 1 E Gp M₁ M₂ hyp.amalgam Tb hTb Y β hyp.faithful {fb} {rr}
    (by rintro u rfl; exact hfbT) (by rintro u rfl; exact hrT) ⟨g, by
      rw [Set.image_singleton, Set.image_singleton, Set.image_singleton, hg]⟩
  rw [Set.image_singleton, Set.image_singleton, Set.image_singleton] at hh
  have hh' : h * bmap β fb * h⁻¹ = bmap β rr := Set.singleton_eq_singleton_iff.1 hh
  have hfr : IsConj (bM β ε fb) (bM β ε rr) := by
    refine isConj_iff.2 ⟨epsG β ε h, ?_⟩
    show epsG β ε h * epsG β ε (bmap β fb) * (epsG β ε h)⁻¹ = epsG β ε (bmap β rr)
    rw [← hh', map_mul, map_mul, map_inv]
  obtain ⟨y, hy⟩ := isConj_iff.1 (hconj.trans hfr)
  set H : Subgroup M := conjSub y (MiOne β ε) with hHdef
  have hCH : Subgroup.centralizer ({bM β ε rr} : Set M) ≤ H := by
    rw [← hy, burnsideF4j_centralizer_conj]
    exact conjSub_mono y hyp.hb
  have hb1 := burnsideF4j_bOne_injective hyp
  have hb2 := burnsideF4j_bTwo_injective hyp
  have hX1 : subImg (burnsideF4d_bOne β ε) (cenIn (Gp ⊓ M₁) r) ≤ H := by
    refine (burnsideF4j_subImg_cenIn_le _ _ hrM.1).trans ?_
    have e : burnsideF4d_bOne β ε ⟨r, hrM.1⟩ = bM β ε rr := (burnsideF4j_bM_eq_bOne β ε rr).symm
    rw [e]
    exact hCH
  have hX2 : subImg (burnsideF4d_bTwo β ε) (cenIn (Gp ⊓ M₂) r) ≤ H := by
    refine (burnsideF4j_subImg_cenIn_le _ _ hrM.2).trans ?_
    have e : burnsideF4d_bTwo β ε ⟨r, hrM.2⟩ = bM β ε rr :=
      (burnsideF4j_bOne_eq_bTwo β ε r hrM.1 hrM.2).symm.trans (burnsideF4j_bM_eq_bOne β ε rr).symm
    rw [e]
    exact hCH
  have hvM₁ : v ∈ M₁ := hv.1.2.1
  have hvM₂ : v ∈ M₂ := hv.1.2.2
  have htM₂ : t ∈ M₂ := ht.1.2
  have hxM₁ : x ∈ M₁ := hx.1.2
  have hv1 : v ∈ cenIn (Gp ⊓ M₁) r := ⟨⟨hv.1.1, hvM₁⟩, hv.2⟩
  set a : M := burnsideF4d_bOne β ε ⟨v, hvM₁⟩ with hadef
  have ha2 : a = burnsideF4d_bTwo β ε ⟨v, hvM₂⟩ := burnsideF4j_bOne_eq_bTwo β ε v hvM₁ hvM₂
  set T : M := burnsideF4d_bTwo β ε ⟨t, htM₂⟩ with hTdef
  set X : M := burnsideF4d_bOne β ε ⟨x, hxM₁⟩ with hXdef
  have haH : a ∈ H := hX1 (mem_subImg_of_mem _ hvM₁ hv1)
  have hTH : T ∈ H := hX2 (mem_subImg_of_mem _ htM₂ ht)
  have hXH : X ∈ H := hX1 (mem_subImg_of_mem _ hxM₁ hx)
  have hbH : T * a * T⁻¹ ∈ H := H.mul_mem (H.mul_mem hTH haH) (H.inv_mem hTH)
  have r1 : a * a = 1 := by
    rw [hadef, ← map_mul]
    have : (⟨v, hvM₁⟩ : ↥M₁) * ⟨v, hvM₁⟩ = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hb' : T * a * T⁻¹ = burnsideF4d_bTwo β ε ⟨t * v * t⁻¹,
      M₂.mul_mem (M₂.mul_mem htM₂ hvM₂) (M₂.inv_mem htM₂)⟩ := by
    rw [ha2, hTdef, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have r2 : (T * a * T⁻¹) * (T * a * T⁻¹) = 1 := by
    calc (T * a * T⁻¹) * (T * a * T⁻¹) = T * (a * a) * T⁻¹ := by group
      _ = 1 := by rw [r1]; group
  have r3 : a * (T * a * T⁻¹) = (T * a * T⁻¹) * a := by
    rw [hb', ha2, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hvv
  have r4 : T * (T * a * T⁻¹) * T⁻¹ = a * (T * a * T⁻¹) := by
    rw [hb', ha2, hTdef, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htv
  have r5 : T ^ 3 = 1 := by
    rw [hTdef, ← map_pow]
    have : (⟨t, htM₂⟩ : ↥M₂) ^ 3 = 1 := Subtype.ext (by simpa using ht3)
    rw [this, map_one]
  have hA := ha E Gp M₁ M₂ hyp.amalgam
  have hMi : MiOne β ε = subImg (burnsideF4d_bOne β ε) M₁ := burnsideF4d_MiOne_eq β ε
  have haP : a ∈ pCoreOf 2 H := by
    rw [hHdef, hMi] at haH hTH hbH ⊢
    exact burnsideF4m_A4_conj _ hb1 y hA haH hbH hTH r1 r2 r3 rfl r4 r5
  have hXa : X * a * X⁻¹ ∈ pCoreOf 2 H := by
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hXH
    exact (Subgroup.mem_normalizer_iff.mp hN a).mp haP
  have hwP : a * (X * a * X⁻¹) ∈ pCoreOf 2 H := Subgroup.mul_mem _ haP hXa
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hwP⟩
  have hk' : (a * (X * a * X⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hw' : a * (X * a * X⁻¹) = burnsideF4d_bOne β ε ⟨v * (x * v * x⁻¹),
      M₁.mul_mem hvM₁ (M₁.mul_mem (M₁.mul_mem hxM₁ hvM₁) (M₁.inv_mem hxM₁))⟩ := by
    rw [hadef, hXdef, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have h3' : (a * (X * a * X⁻¹)) ^ 3 = 1 := by
    rw [hw', ← map_pow]
    have : (⟨v * (x * v * x⁻¹), M₁.mul_mem hvM₁ (M₁.mul_mem (M₁.mul_mem hxM₁ hvM₁)
        (M₁.inv_mem hxM₁))⟩ : ↥M₁) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    rw [this, map_one]
  have hord : orderOf (a * (X * a * X⁻¹)) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3')
  rw [orderOf_eq_one_iff, hw'] at hord
  apply hw1
  have := hb1 (hord.trans (map_one _).symm)
  exact congrArg Subtype.val this

end F436U5

end CFSG.ASVolI
