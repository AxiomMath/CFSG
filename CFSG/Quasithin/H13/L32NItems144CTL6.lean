module

public import CFSG.Quasithin.H13.L32NItems144CTL5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

theorem inf_center_ne_bot' {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyU : (y : G) ∈ U := hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hyU, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem R_le_conj_T {σ h : G} (hσT : σ ∈ T) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ ≤ T.map (MulAut.conj h).toMonoidHom := by
  have hQn : l32nH T V ≤ Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    le_normalizer_pCoreOf (r := 2) (l32nH T V)
  have hmem : ∀ x : G, h⁻¹ * x * h ∈ T → x ∈ T.map (MulAut.conj h).toMonoidHom :=
    fun x hx => ⟨h⁻¹ * x * h, hx, by simp [mul_assoc]⟩
  refine sup_le (fun q hq => hmem q ?_) (Subgroup.zpowers_le.mpr (hmem σ ?_))
  · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hQn hhH)) q).mp hq
    exact S.QT (by simpa using this)
  · have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hQn hhH)) _).mp
      hσh
    have h2 : h⁻¹ * σ * h = h⁻¹ * (σ * h * σ⁻¹ * h⁻¹) * h⁻¹⁻¹ * σ := by group
    rw [h2]
    exact T.mul_mem (S.QT h1) hσT

omit [Finite G] S in
theorem conj_T_le_normalizer {T L : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (h : G) : T.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.normalizer ((L.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl, ?_⟩
    simp [mul_assoc]
  · rintro ⟨l, hl, hlx⟩
    refine ⟨t⁻¹ * l * t, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hTL ht)) l).mp hl
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hlx ⊢
      calc h * (t⁻¹ * l * t) * h⁻¹ =
          (h * t * h⁻¹)⁻¹ * (h * l * h⁻¹) * (h * t * h⁻¹) := by group
        _ = x := by rw [hlx]; group

theorem R_le_normalizer {σ h : G} (hσT : σ ∈ T) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ ≤
      Subgroup.normalizer ((L.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) :=
  (R_le_conj_T S hσT hhH hσh).trans (conj_T_le_normalizer S.TL h)

theorem conj_TL_le_R {σ h : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    (fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g).map (MulAut.conj h).toMonoidHom ≤
      pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ := by
  have hQn : l32nH T V ≤ Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    le_normalizer_pCoreOf (r := 2) (l32nH T V)
  have hσinv : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  have hconjQ : ∀ q ∈ pCoreOf 2 (l32nH T V), h * q * h⁻¹ ∈ pCoreOf 2 (l32nH T V) := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQn hhH) q).mp hq
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_sup_left (hconjQ u (S.U_le_Q hu))
  · rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases mem_Q_or_of_mem_Wg S hσW hσQ hw with hwQ | hwQ
    · exact Subgroup.mem_sup_left (hconjQ w hwQ)
    · have e1 : σ⁻¹ * h * σ * h⁻¹ = σ * h * σ⁻¹ * h⁻¹ := by rw [hσinv]
      have e : h * w * h⁻¹ = σ * (σ * h * σ⁻¹ * h⁻¹) * (h * (σ⁻¹ * w) * h⁻¹) := by
        rw [← e1]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers σ)) (Subgroup.mem_sup_left hσh))
        (Subgroup.mem_sup_left (hconjQ _ hwQ))

end Setup

end L1444CTL

end CFSG.Quasithin.H13
