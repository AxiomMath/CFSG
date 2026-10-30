module

public import CFSG.Quasithin.H13.A5W13616a
public import CFSG.Quasithin.MS93.C134SqCond
public import CFSG.Quasithin.Vol2.Ch11SecA15Z1d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

section Generic

variable {G : Type} [Group G]

theorem card_inf_centralizer_sq_le [Finite G] {A K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (A : Set G))
    (hD : ∀ x ∈ A, x ∈ Subgroup.centralizer (K : Set G) →
      t⁻¹ * x * t ∈ Subgroup.centralizer (K : Set G) → x = 1) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) ^ 2 ≤ Nat.card ↥A := by
  set B := A ⊓ Subgroup.centralizer (K : Set G)
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => (Subgroup.mem_normalizer_iff.mp ht a).mp ha
  let f : ↥B × ↥B → ↥A := fun p =>
    ⟨p.1 * (t * p.2 * t⁻¹), A.mul_mem p.1.2.1 (htA _ p.2.2.1)⟩
  have hf : Function.Injective f := by
    rintro ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ h
    have h' : (b₁ : G) * (t * b₂ * t⁻¹) = c₁ * (t * c₂ * t⁻¹) := congrArg Subtype.val h
    set x : G := (c₁ : G)⁻¹ * b₁
    have hx : x = t * ((c₂ : G) * (b₂ : G)⁻¹) * t⁻¹ := by
      have : (c₁ : G)⁻¹ * b₁ = (t * c₂ * t⁻¹) * (t * b₂ * t⁻¹)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h']; group
      exact this.trans (by group)
    have hxB : x ∈ B := B.mul_mem (B.inv_mem c₁.2) b₁.2
    have hyB : (c₂ : G) * (b₂ : G)⁻¹ ∈ B := B.mul_mem c₂.2 (B.inv_mem b₂.2)
    have htx : t⁻¹ * x * t = (c₂ : G) * (b₂ : G)⁻¹ := by rw [hx]; group
    have hx1 : x = 1 := hD x hxB.1 hxB.2 (htx ▸ hyB.2)
    have h1 : (b₁ : G) = c₁ := by
      have : (c₁ : G)⁻¹ * b₁ = 1 := hx1
      rw [inv_mul_eq_one] at this; exact this.symm
    have h2 : (b₂ : G) = c₂ := by
      have : (c₂ : G) * (b₂ : G)⁻¹ = 1 := by rw [← htx, hx1]; group
      rw [mul_inv_eq_one] at this; exact this.symm
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← sq] at this

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem c134SqCond_Tv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) : MS93.C134SqCond S.Tv K₀ := by
  intro T₁ hT₁ hchar
  have hO := S.pCoreOf_sup_T_eq_bot h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hK₀G hK₀
    hTK hz
  have h2 : (S.Tv.subgroupOf T).index = 2 := S.index_Tv
  have hTvT : S.Tv ≤ T := inf_le_left
  have hTvn : T ≤ Subgroup.normalizer (S.Tv : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTvT).mp (Subgroup.normal_of_index_eq_two h2)
  set A := omegaOneCenterOf T₁ with hAdef
  have hAT₁ : A ≤ T₁ := by
    rw [hAdef, omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
    exact fun x hx => hx.1.1
  have hTA : T ≤ Subgroup.normalizer (A : Set G) :=
    (hTvn.trans (CFSG.QuasithinUnique.normalizer_le_normalizer_of_characteristic hT₁ hchar)).trans
      (CFSG.Quasithin.Vol2.Ch11.SecA.normalizer_le_normalizer_omegaOneCenterOf T₁)
  obtain ⟨t, htT, htv⟩ : ∃ t ∈ T, t ∉ S.Tv := by
    by_contra hc
    push Not at hc
    have : S.Tv.subgroupOf T = ⊤ := by
      rw [eq_top_iff]; rintro ⟨x, hx⟩ -; exact Subgroup.mem_subgroupOf.mpr (hc x hx)
    rw [this, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)
  refine card_inf_centralizer_sq_le (hTA htT) ?_
  intro x hxA hxK htxK
  set C := Subgroup.centralizer (K₀ : Set G)
  have hsC : ∀ s ∈ S.Tv, ∀ y ∈ C, s * y * s⁻¹ ∈ C := by
    intro s hs y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro k hk
    have hk' : s⁻¹ * k * s ∈ K₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTK (S.Tv.inv_mem hs)) k).mp hk
      simpa using this
    have := hy _ hk'
    calc k * (s * y * s⁻¹) = s * ((s⁻¹ * k * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * k * s)) * s⁻¹ := by rw [this]
      _ = s * y * s⁻¹ * k := by group
  let D : Subgroup G :=
    { carrier := {y | y ∈ A ∧ y ∈ C ∧ t⁻¹ * y * t ∈ C}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, C.mul_mem ha.2.1 hb.2.1, by
        have : t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by group
        rw [this]; exact C.mul_mem ha.2.2 hb.2.2⟩
      one_mem' := ⟨A.one_mem, C.one_mem, by simp [C.one_mem]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, C.inv_mem ha.2.1, by
        have : t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by group
        rw [this]; exact C.inv_mem ha.2.2⟩ }
  have hAconj : ∀ g ∈ T, ∀ y ∈ A, g * y * g⁻¹ ∈ A := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hTA hg) y).mp hy
  have hTvconj : ∀ g ∈ T, ∀ s ∈ S.Tv, g * s * g⁻¹ ∈ S.Tv := fun g hg s hs =>
    (Subgroup.mem_normalizer_iff.mp (hTvn hg) s).mp hs
  have hPs : ∀ s ∈ S.Tv, ∀ y ∈ D, s * y * s⁻¹ ∈ D := by
    intro s hs y hy
    refine ⟨hAconj s (hTvT hs) y hy.1, hsC s hs y hy.2.1, ?_⟩
    have hs' : t⁻¹ * s * t ∈ S.Tv := by
      have := hTvconj t⁻¹ (T.inv_mem htT) s hs
      simpa using this
    have := hsC _ hs' _ hy.2.2
    have e : t⁻¹ * (s * y * s⁻¹) * t = (t⁻¹ * s * t) * (t⁻¹ * y * t) * (t⁻¹ * s * t)⁻¹ := by group
    rw [e]; exact this
  have hPt : ∀ y ∈ D, t * y * t⁻¹ ∈ D := by
    intro y hy
    have ht2 : t * t ∈ S.Tv := by
      by_contra h
      have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨t, htT⟩) (b := ⟨t, htT⟩))
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, iff_self, iff_true] at this
      exact h this
    have hy2 := hPs _ ht2 y hy
    refine ⟨hAconj t htT y hy.1, ?_, by simpa [mul_assoc] using hy.2.1⟩
    have e : t * y * t⁻¹ = t⁻¹ * (t * t * y * (t * t)⁻¹) * t := by group
    rw [e]; exact hy2.2.2
  have hPg : ∀ g ∈ T, ∀ y ∈ D, g * y * g⁻¹ ∈ D := by
    intro g hg y hy
    by_cases hgv : g ∈ S.Tv
    · exact hPs g hgv y hy
    · have hgt : g * t⁻¹ ∈ S.Tv := by
        have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨g, hg⟩) (b := ⟨t⁻¹, T.inv_mem htT⟩))
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact this.mpr (iff_of_false hgv (fun h => htv (by simpa using S.Tv.inv_mem h)))
      have := hPs _ hgt _ (hPt y hy)
      have e : g * y * g⁻¹ = g * t⁻¹ * (t * y * t⁻¹) * (g * t⁻¹)⁻¹ := by group
      rw [e]; exact this
  have hDN : K₀ ⊔ T ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le (fun k hk => ?_) (fun g hg => ?_)
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp hy.2.1) k hk).symm
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨hPg g hg y, fun hy => ?_⟩
      have := hPg g⁻¹ (T.inv_mem hg) _ hy
      simpa [mul_assoc] using this
  have hDT : D ≤ T := fun y hy => hTvT (hT₁ (hAT₁ hy.1))
  have hD2 : IsPGroup 2 D := S.isPGroup_T.to_le hDT
  have hle : D ≤ pCoreOf 2 (K₀ ⊔ T) :=
    CFSG.QuasithinUnique.le_pCoreOf_of_normalizes (hDT.trans le_sup_right) hDN hD2
  rw [hO] at hle
  exact (Subgroup.mem_bot.mp (hle ⟨hxA, hxK, htxK⟩))

end Setting

end CFSG.Quasithin.H13.A5
