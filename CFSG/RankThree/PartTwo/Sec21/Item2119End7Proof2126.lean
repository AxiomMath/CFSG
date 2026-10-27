module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof2126
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item2126Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        ∀ n p : ℕ, Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) → p.Prime → 3 < p →
          p ∣ 2 ^ n - 1 →
          ∃ P : Subgroup G, IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
            (∀ e (he : e ∈ A), e ∉ Subgroup.zpowers d →
              ∀ τ ∈ trivOnQuot A (Subgroup.zpowers d), τ ⟨e, he⟩ = ⟨e, he⟩ →
                τ ∈ starOf A (Subgroup.normalizer (P : Set G))) ∧
            ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ g ∈ Subgroup.normalizer (A : Set G),
              g ∈ Subgroup.centralizer (P : Set G) → g * e * g⁻¹ = e → g * d * g⁻¹ = d →
              (∀ x ∈ A, x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.zpowers d) →
                g ∈ Subgroup.centralizer (A : Set G)

namespace Item2119End7Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_order_three {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h24 : Concl2124 A L X d) :
    ∃ (u : G) (hu : u ∈ Subgroup.normalizer (A : Set G)), u * d * u⁻¹ = d ∧
      (∀ x ∈ A, x⁻¹ * (u * x * u⁻¹) ∈ Subgroup.zpowers d) ∧
      A.normalizerMonoidHom ⟨u, hu⟩ ≠ 1 ∧ A.normalizerMonoidHom ⟨u, hu⟩ ^ 3 = 1 := by
  obtain ⟨e₃⟩ := hE.cfg.star
  set π₀ : Equiv.Perm (Fin 3) := finRotate 3 with hπ₀
  have hπ3 : π₀ ^ 3 = 1 := by decide
  have hπ1 : π₀ ≠ 1 := by decide
  set σ : starOf A L := e₃.symm π₀ with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hπ3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hπ1 (by rw [← e₃.apply_symm_apply π₀, ← hσ, h, map_one])
  obtain ⟨⟨u, hu⟩, huL, huσ⟩ := σ.2
  have huσ' : A.normalizerMonoidHom ⟨u, hu⟩ = (σ : MulAut A) := huσ
  have hT : (σ : MulAut A) ∈ trivOnQuot A (Subgroup.zpowers d) := by
    rw [← h24]
    exact Subgroup.mem_sup_right σ.2
  have hdA : d ∈ A := hE.mem_d.1
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hd1 : d ≠ 1 := hE.ne_one_d
  have htriv : ∀ x ∈ A, x⁻¹ * (u * x * u⁻¹) ∈ Subgroup.zpowers d := by
    intro x hx
    have h1 := (mem_trivOnQuot_iff.mp hT) ⟨x, hx⟩
    rw [← huσ'] at h1
    exact h1
  have hud : u * d * u⁻¹ = d := by
    have h1 : u * d * u⁻¹ ∈ Subgroup.zpowers d := by
      have h2 := htriv d hdA
      have h3 := Subgroup.mul_mem _ (Subgroup.mem_zpowers d) h2
      rwa [mul_inv_cancel_left] at h3
    obtain ⟨j, hj, hjd⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 h1
    have hu3 : u ^ 3 * d * (u ^ 3)⁻¹ = d := by
      have h4 : (⟨u, hu⟩ : Subgroup.normalizer (A : Set G)) ^ 3 ∈
          (A.normalizerMonoidHom).ker := by
        rw [MonoidHom.mem_ker, map_pow, huσ']
        exact congrArg Subtype.val hσ3
      have h5 := congrArg (fun φ : MulAut A => ((φ ⟨d, hdA⟩ : A) : G)) (MonoidHom.mem_ker.mp h4)
      simpa using h5
    interval_cases j
    · exfalso
      apply hd1
      rw [pow_zero] at hjd
      calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
        _ = 1 := by rw [hjd]; group
    · rwa [pow_one] at hjd
    · exfalso
      have hinv : u * d * u⁻¹ = d⁻¹ := by
        rw [hjd]
        exact Item21LateProof.sq_eq_inv_of_pow_three hd3
      have hinvz : ∀ z : G, u * z * u⁻¹ = z⁻¹ → u * z⁻¹ * u⁻¹ = z := fun z hz => by
        rw [show u * z⁻¹ * u⁻¹ = (u * z * u⁻¹)⁻¹ by group, hz, inv_inv]
      have e2 : u ^ 2 * d * (u ^ 2)⁻¹ = d := by
        calc u ^ 2 * d * (u ^ 2)⁻¹ = u * (u * d * u⁻¹) * u⁻¹ := by
              rw [pow_two, mul_inv_rev]; group
          _ = d := by rw [hinv, hinvz d hinv]
      have e3 : u ^ 3 * d * (u ^ 3)⁻¹ = d⁻¹ := by
        calc u ^ 3 * d * (u ^ 3)⁻¹ = u * (u ^ 2 * d * (u ^ 2)⁻¹) * u⁻¹ := by
              rw [pow_succ' u 2, mul_inv_rev]; group
          _ = d⁻¹ := by rw [e2, hinv]
      rw [hu3] at e3
      apply hd1
      have h6 : d * d = 1 := by
        calc d * d = d * d⁻¹ := by rw [← e3]
          _ = 1 := mul_inv_cancel d
      calc d = d ^ 3 * (d * d)⁻¹ := by group
        _ = 1 := by rw [hd3, h6, inv_one, one_mul]
  refine ⟨u, hu, hud, htriv, ?_, ?_⟩
  · rw [huσ']
    exact fun h => hσ1 (Subtype.ext h)
  · rw [huσ']
    exact congrArg Subtype.val hσ3

omit [Finite G] in
theorem normalizerMonoidHom_eq_one {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (h : ∀ x ∈ A, g * x * g⁻¹ = x) :
    A.normalizerMonoidHom ⟨g, hg⟩ = 1 := by
  ext x
  exact h x x.2

theorem eq_one_of_comm_of_inv {M : Type*} [Group M] {σ τ : M} (h3 : σ ^ 3 = 1)
    (h1 : σ * τ * σ⁻¹ * τ⁻¹ = 1) (h2 : τ * σ * τ⁻¹ * σ = 1) : σ = 1 := by
  have hστ : σ * τ = τ * σ := by
    calc σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
      _ = τ * σ := by rw [h1, one_mul]
  have hσ2 : σ * σ = 1 := by
    calc σ * σ = τ * σ * τ⁻¹ * σ := by rw [← hστ]; group
      _ = 1 := h2
  calc σ = σ ^ 3 * (σ * σ)⁻¹ := by group
    _ = 1 := by rw [h3, hσ2, inv_one, one_mul]

end Item2119End7Proof

open Item2119End7Proof

theorem item2126P_of_loc (hLoc : Item2126Loc) : Item2126P := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn hp hp3 hpd
  obtain ⟨P, hPe, hP2, ha, hb⟩ := hLoc G A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn hp hp3 hpd
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have h27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hdA : d ∈ A := hE.mem_d.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hd1 : d ≠ 1 := hE.ne_one_d
  set ρ := A.normalizerMonoidHom with hρ
  set T := trivOnQuot A (Subgroup.zpowers d) with hT
  set W₁ : Subgroup G := (T.comap ρ).map (Subgroup.normalizer (A : Set G)).subtype with hW₁
  set W₀ : Subgroup G :=
    (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (P : Set G)) ⊓ W₁ with hW₀
  have hW₀A : W₀ ≤ Subgroup.normalizer (A : Set G) := inf_le_left.trans inf_le_left
  have hW₀P : W₀ ≤ Subgroup.normalizer (P : Set G) := inf_le_left.trans inf_le_right
  have hmemW₁ : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (A : Set G)), ρ ⟨g, hg⟩ ∈ T → g ∈ W₁ :=
    fun g hg hgT => ⟨⟨g, hg⟩, hgT, rfl⟩
  have hW₁T : ∀ g ∈ W₁, ∀ hg : g ∈ Subgroup.normalizer (A : Set G), ρ ⟨g, hg⟩ ∈ T := by
    rintro g ⟨h, hh, rfl⟩ hg
    exact hh
  have hfixT : ∀ τ ∈ T, ∃ e, ∃ he : e ∈ A, e ∉ Subgroup.zpowers d ∧ τ ⟨e, he⟩ = ⟨e, he⟩ := by
    intro τ hτ
    have hτW : τ ∈ wStar A := by
      rw [hT, ← h24] at hτ
      exact sup_le (starOf_le_wStar A X) (starOf_le_wStar A L) hτ
    obtain ⟨⟨u, hu⟩, rfl⟩ := hτW
    have hutriv : ∀ x ∈ A, x⁻¹ * (u * x * u⁻¹) ∈ Subgroup.zpowers d := fun x hx =>
      (mem_trivOnQuot_iff.mp hτ) ⟨x, hx⟩
    obtain ⟨e, he, hed, hue⟩ := Item2119End6Proof.exists_fixed_of_trivOnQuot hAe h27 hdA hu hutriv
    exact ⟨e, he, hed, Subtype.ext hue⟩
  have hTW : T ≤ starOf A W₀ := by
    intro τ hτ
    obtain ⟨e, he, hed, hτe⟩ := hfixT τ hτ
    obtain ⟨⟨h, hhA⟩, hhP, hhτ⟩ := ha e he hed τ hτ hτe
    have hhP' : h ∈ Subgroup.normalizer (P : Set G) := hhP
    refine ⟨⟨h, hhA⟩, Subgroup.mem_subgroupOf.mpr ⟨⟨hhA, hhP'⟩, hmemW₁ h hhA ?_⟩, hhτ⟩
    rw [show ρ ⟨h, hhA⟩ = τ from hhτ]
    exact hτ
  obtain ⟨u, hu, hud, hutriv, huσ1, huσ3⟩ := exists_order_three hE h24
  have huT : ρ ⟨u, hu⟩ ∈ T := mem_trivOnQuot_iff.mpr fun x => hutriv x x.2
  obtain ⟨⟨h, hhA⟩, hhW₀, hhσ⟩ := hTW huT
  have hhW₀' : h ∈ W₀ := Subgroup.mem_subgroupOf.mp hhW₀
  have hhσ' : ρ ⟨h, hhA⟩ = ρ ⟨u, hu⟩ := hhσ
  have hhtriv : ∀ x ∈ A, x⁻¹ * (h * x * h⁻¹) ∈ Subgroup.zpowers d := by
    intro x hx
    have h1 := (mem_trivOnQuot_iff.mp huT) ⟨x, hx⟩
    rw [← hhσ'] at h1
    exact h1
  have hhd : h * d * h⁻¹ = d := by
    have h1 := congrArg (fun φ : MulAut A => ((φ ⟨d, hdA⟩ : A) : G)) hhσ'
    change h * d * h⁻¹ = u * d * u⁻¹ at h1
    rw [h1, hud]
  have hfixd : ∀ g ∈ W₀ ⊓ Subgroup.centralizer (P : Set G), g * d * g⁻¹ = d →
      g ∈ Subgroup.centralizer (A : Set G) := by
    rintro g ⟨hgW, hgC⟩ hgd
    have hgA := hW₀A hgW
    have hgtriv : ∀ x ∈ A, x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.zpowers d := fun x hx =>
      (mem_trivOnQuot_iff.mp (hW₁T g hgW.2 hgA)) ⟨x, hx⟩
    obtain ⟨e, he, hed, hge⟩ :=
      Item2119End6Proof.exists_fixed_of_trivOnQuot hAe h27 hdA hgA hgtriv
    exact hb e he hed g hgA hgC hge hgd hgtriv
  have hWC : W₀ ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (A : Set G) := by
    rintro g ⟨hgW, hgC⟩
    have hgA := hW₀A hgW
    have hgT := hW₁T g hgW.2 hgA
    have hgtriv : ∀ x ∈ A, x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.zpowers d := fun x hx =>
      (mem_trivOnQuot_iff.mp hgT) ⟨x, hx⟩
    have hgdmem : g * d * g⁻¹ ∈ Subgroup.zpowers d := hE.normal_d g hgA
    obtain ⟨j, hj, hjd⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 hgdmem
    interval_cases j
    · exfalso
      apply hd1
      rw [pow_zero] at hjd
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [hjd]; group
    · rw [pow_one] at hjd
      exact hfixd g ⟨hgW, hgC⟩ hjd
    · exfalso
      have hgd : g * d * g⁻¹ = d⁻¹ := by
        rw [hjd]
        exact Item21LateProof.sq_eq_inv_of_pow_three hd3
      set k := h * g * h⁻¹ * g⁻¹ with hk
      have hkW : k ∈ W₀ :=
        W₀.mul_mem (W₀.mul_mem (W₀.mul_mem hhW₀' hgW) (W₀.inv_mem hhW₀')) (W₀.inv_mem hgW)
      have hkC : k ∈ Subgroup.centralizer (P : Set G) := by
        have hhP := hW₀P hhW₀'
        have h1 : h * g * h⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : h⁻¹ * y * h ∈ P := by
            have := (Subgroup.mem_normalizer_iff.mp (inv_mem hhP) y).mp hy
            simpa using this
          have h2 := Subgroup.mem_centralizer_iff.mp hgC _ hy'
          calc y * (h * g * h⁻¹) = h * ((h⁻¹ * y * h) * g) * h⁻¹ := by group
            _ = h * (g * (h⁻¹ * y * h)) * h⁻¹ := by rw [h2]
            _ = h * g * h⁻¹ * y := by group
        exact Subgroup.mul_mem _ h1 (inv_mem hgC)
      have hgd' : g⁻¹ * d * g = d⁻¹ := by
        calc g⁻¹ * d * g = g⁻¹ * (g * d * g⁻¹)⁻¹ * g := by rw [hgd, inv_inv]
          _ = d⁻¹ := by group
      have hhd' : h⁻¹ * d⁻¹ * h = d⁻¹ := by
        calc h⁻¹ * d⁻¹ * h = h⁻¹ * (h * d * h⁻¹)⁻¹ * h := by rw [hhd]
          _ = d⁻¹ := by group
      have hkd : k * d * k⁻¹ = d := by
        calc k * d * k⁻¹ = h * g * (h⁻¹ * (g⁻¹ * d * g) * h) * g⁻¹ * h⁻¹ := by
              rw [hk]; group
          _ = h * (g * d⁻¹ * g⁻¹) * h⁻¹ := by rw [hgd', hhd']; group
          _ = h * (g * d * g⁻¹)⁻¹ * h⁻¹ := by group
          _ = d := by rw [hgd, inv_inv, hhd]
      have hkA := hfixd k ⟨hkW, hkC⟩ hkd
      have hk1 : ρ ⟨k, hW₀A hkW⟩ = 1 := normalizerMonoidHom_eq_one _ fun x hx => by
        rw [(Subgroup.mem_centralizer_iff.mp hkA x hx).symm, mul_inv_cancel_right]
      have hinv := Item2119End4Proof.conj_inv_of_trivOnQuot hcomm hdA hgA hgtriv hgd hhtriv hhd
      have hvN : g * h * g⁻¹ * h ∈ Subgroup.normalizer (A : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA hhA)
          (Subgroup.inv_mem _ hgA)) hhA
      have hv1 : ρ ⟨g * h * g⁻¹ * h, hvN⟩ = 1 := normalizerMonoidHom_eq_one _ hinv
      have e1 : ρ ⟨h, hhA⟩ * ρ ⟨g, hgA⟩ * (ρ ⟨h, hhA⟩)⁻¹ * (ρ ⟨g, hgA⟩)⁻¹ = 1 := by
        have e : (⟨k, hW₀A hkW⟩ : Subgroup.normalizer (A : Set G)) =
            ⟨h, hhA⟩ * ⟨g, hgA⟩ * ⟨h, hhA⟩⁻¹ * ⟨g, hgA⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at hk1
        exact hk1
      have e2 : ρ ⟨g, hgA⟩ * ρ ⟨h, hhA⟩ * (ρ ⟨g, hgA⟩)⁻¹ * ρ ⟨h, hhA⟩ = 1 := by
        have e : (⟨g * h * g⁻¹ * h, hvN⟩ : Subgroup.normalizer (A : Set G)) =
            ⟨g, hgA⟩ * ⟨h, hhA⟩ * ⟨g, hgA⟩⁻¹ * ⟨h, hhA⟩ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv] at hv1
        exact hv1
      have hσ3 : ρ ⟨h, hhA⟩ ^ 3 = 1 := by rw [hhσ']; exact huσ3
      apply huσ1
      rw [← hhσ']
      exact eq_one_of_comm_of_inv hσ3 e1 e2
  exact ⟨P, W₀, hPe, hP2, hW₀A, hW₀P, hWC, hTW⟩

end CFSG.RankThree.PartTwo.Sec21
