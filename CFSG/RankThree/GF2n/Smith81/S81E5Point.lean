module

public import CFSG.RankThree.GF2n.Smith81.S81E5Rad
public import CFSG.RankThree.GF2n.Smith81.S81JGSide
public import CFSG.RankThree.GF2n.Smith81.S81WTacitFree45
public import CFSG.RankThree.GF2n.Smith81.S81E5FormHolds

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model


section Point

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem LB_le_Lgen_of_tacit (h34 : Stroth34Statement) (hc : SmithECfg M Q Z B)
    (hTac : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B')
    {C : Subgroup G} (hC : Ctx M Q Z C) : LB M Q C ≤ Lgen M (LB M Q B) := by
  obtain ⟨n, k, hw, hnk⟩ := hc.e.exists_width
  have hn : 3 ≤ n := by
    have := hnk.ten_le
    omega
  have hno : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') :=
    fun B' hB' => (hTac B' hB').1
  have h15c : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G) := fun B' hB' =>
    (stroth_3_5 h34 hB' hw (by omega) (hTac B' hB').1 (hTac B' hB').2).2.1
  have h25 := smith25_of_117 smith117Statement_holds hc.ctx hw hn hno h15c
  have hmem : C ⊔ Z ∈ {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧
      V = A ⊔ Z} := ⟨C, hC.conj, hC.le, hC.ne, rfl⟩
  rw [h25] at hmem
  obtain ⟨g, hg, hCg⟩ := hmem
  have hcg : Ctx M Q Z (conjSubgroup g B) := hc.ctx.conj_of_mem hg
  have hle : conjSubgroup g B ≤ Z ⊔ C := by
    rw [sup_comm, hCg]
    exact le_sup_left
  obtain ⟨p, hpQ, hp⟩ := hC.exists_conj_of_le_ZB hcg hle
  have hpM : p ∈ M := hc.ctx.hyp.Q_normal.1 hpQ
  have hCeq : C = conjSubgroup (p⁻¹ * g) B := by
    rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hm : p⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hpM) hg
  rw [hCeq, hc.ctx.LB_conj hm]
  exact le_iSup₂_of_le (p⁻¹ * g) hm le_rfl

theorem point_E5 [CharP K 2] (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h5 : InCaseE5 M Q Z B)
    (hg : GlobalModelData M Q Z γ M₀) (ψ : M₀.E ≃ₗ[K] V K)
    (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)) (hrange : φ.range = EAut K)
    (hker : ∀ s : Lgen M (LB M Q B), φ s = 1 ↔ (s : G) ∈ Q)
    (hequiv : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      ψ (M₀.π ((s : G) * x * (s : G)⁻¹)) = φ s (ψ (M₀.π x)))
    {A : Subgroup G} (hAZ : IsZConjugate Z A) (hAQ : A ≤ Q) (hAne : A ≠ Z) :
    ∃ g ∈ EAut K, (fun a : G => ψ (M₀.π a)) '' (A : Set G) =
        (Submodule.span K {g (w0 : V K)} : Set (V K)) ∧
      ∀ u ∈ conjSub g (rootRad7 K), ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A ∧ φ t = u := by
  classical
  have hctx : Ctx M Q Z B := hc.ctx
  have hctxA : Ctx M Q Z A := ⟨hctx.hyp, hAZ, hAQ, hAne⟩
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hM : M ≤ Subgroup.normalizer (Q : Set G) := hctx.hyp.Q_normal.2
  have hw : Width Q Z 28 := by
    obtain ⟨t, -, h⟩ := h5
    simpa [Width] using h.1
  have hTac := eTacitE5_of_genByB hGen G M Q Z B IH hc h5
  obtain ⟨hno, hgen⟩ := hTac A hctxA
  obtain ⟨-, hCQt, hLBcard, -⟩ := stroth_3_5 h34 hctxA hw (by norm_num) hno hgen
  have hLBle : LB M Q A ≤ Lgen M (LB M Q B) := LB_le_Lgen_of_tacit h34 hc hTac hctxA
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  set Lb : Subgroup (V K ≃ₗ[K] V K) :=
    ((LB M Q A).subgroupOf (Lgen M (LB M Q B))).map φ with hLb
  have hLbE : Lb ≤ EAut K := by
    rw [← hrange]
    exact Subgroup.map_le_range φ _
  have hLbsq : ∀ u ∈ Lb, u ^ 2 = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_pow, hker, Subgroup.coe_pow]
    exact hctxA.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hs)
  have hLbcard : Nat.card Lb = Nat.card K ^ 27 := by
    have key : Nat.card (LB M Q A) = Nat.card Q * Nat.card Lb :=
      card_eq_card_mul_card_map_of_ker (S := LB M Q A) φ hker hQLg le_sup_left hLBle
    have hpos : 0 < Nat.card Q := Nat.card_pos
    rw [hg.card]
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← key, hLBcard]
  obtain ⟨g, hgE, hgLb⟩ := exists_eq_conjSub_rootRad7 hLbE hLbsq hLbcard.ge
  have hLbfix : ∀ w : V K, (∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A → φ s w = w) ↔
      w ∈ Submodule.span K {g (w0 : V K)} := by
    intro w
    constructor
    · intro hfix
      have h0 : g⁻¹ w ∈ Submodule.span K {(w0 : V K)} := by
        refine mem_span_w0_of_fix fun u₀ hu₀ => ?_
        have hu : g * u₀ * g⁻¹ ∈ Lb := by
          rw [hgLb]
          exact mem_conjSub.2 ⟨u₀, Subgroup.subset_closure hu₀, rfl⟩
        obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 hu
        have h1 := hfix s (Subgroup.mem_subgroupOf.1 hs)
        rw [hsu, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
        have h2 := congrArg g.symm h1
        rw [LinearEquiv.symm_apply_apply, ← LinearEquiv.coe_inv] at h2
        exact h2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h0
      refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
      rw [← map_smul, hc, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    · intro hw s hs
      have hu : φ s ∈ conjSub g (rootRad7 K) := by
        rw [← hgLb]
        exact Subgroup.mem_map.2 ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
      obtain ⟨u₀, hu₀, hu⟩ := mem_conjSub.1 hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [← hu, map_smul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.symm_apply_apply, rootRad7_apply_w0 hu₀]
  let T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) :=
    { toFun := fun s => ψ.trans ((φ s).trans ψ.symm)
      map_one' := by
        ext v
        simp
      map_mul' := fun s t => by
        ext v
        simp [LinearEquiv.mul_apply] }
  have hT : ∀ s v, ψ (T s v) = φ s (ψ v) := fun s v => by
    simp [T]
  have hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x) := fun s x hx => by
    apply ψ.injective
    rw [hT, hequiv s x hx]
  refine ⟨g, hgE, ?_, ?_⟩
  · ext w
    have hfix := fixed_iff_mem_img (Lg := Lgen M (LB M Q B)) hctxA hctxA.LB_le_M hM hZQ rfl hCQt
      hAQ T hTe hLBle (ψ.symm w)
    have hTψ : ∀ s : Lgen M (LB M Q B), T s (ψ.symm w) = ψ.symm w ↔ φ s w = w := fun s => by
      rw [← ψ.injective.eq_iff, hT, LinearEquiv.apply_symm_apply]
    simp only [hTψ] at hfix
    rw [Set.mem_image, SetLike.mem_coe, ← hLbfix, hfix]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, hxw⟩
      exact ⟨x, hx, by rw [hxw, LinearEquiv.apply_symm_apply]⟩
  · intro u hu
    rw [← hgLb] at hu
    obtain ⟨s, hs, rfl⟩ := hu
    have hsLB : (s : G) ∈ LB M Q A := Subgroup.mem_subgroupOf.1 hs
    have hsup : (s : G) ∈ (QB A ⊓ M) ⊔ Q := by
      rw [sup_comm]
      exact hsLB
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := QB A ⊓ M) (K := Q)
        (fun x hx => hM (Subgroup.mem_inf.1 hx).2) hsup
    have hyLg : y ∈ Lgen M (LB M Q B) := by
      have e : y = (s : G) * z⁻¹ := by
        rw [← hyz]
        group
      rw [e]
      exact mul_mem s.2 (inv_mem (hQLg hz))
    refine ⟨⟨y, hyLg⟩, hy.1, ?_⟩
    have hs_eq : s = ⟨y, hyLg⟩ * ⟨z, hQLg hz⟩ := Subtype.ext hyz.symm
    rw [hs_eq, map_mul, (hker ⟨z, hQLg hz⟩).2 hz, mul_one]

end Point

end CFSG.RankThree.GF2n.Smith81
