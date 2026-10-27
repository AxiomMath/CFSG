module

public import CFSG.Quasithin.Vol2.Ch9Prop941
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210Six

public section

namespace CFSG.Quasithin

theorem burnside_fusion_pointwise {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {W : Subgroup G} (hWT : W ≤ T) (hW : IsWeaklyClosedIn W T) {A : Set G}
    (hA : ∀ w ∈ W, ∀ a ∈ A, w * a = a * w) {g : G}
    (hB : ∀ w ∈ W, ∀ a ∈ A, w * (g⁻¹ * a * g) = (g⁻¹ * a * g) * w) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), ∀ a ∈ A, n⁻¹ * a * n = g⁻¹ * a * g := by
  set N := Subgroup.centralizer (conjSet A g) with hN
  have hWN : W ≤ N := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact (hB w hw a ha).symm
  have hW'N : conjSubgroup W g ≤ N := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hA _ hx a ha
    calc g⁻¹ * a * g * x = g⁻¹ * (a * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * a) * g := by rw [← h1]
      _ = x * (g⁻¹ * a * g) := by group
  have hWp : IsPGroup p W := T.isPGroup'.to_le hWT
  have hW'p : IsPGroup p (conjSubgroup W g) := hWp.map _
  obtain ⟨c, hcN, y, hy1, hy2⟩ := exists_conj_le_sylow_of_isPGroup T hWN hW'N hWp hW'p
  have h1 : conjSubgroup W y = W := hW y hy1
  rw [conjSubgroup_conjSubgroup] at hy2
  have h2 : conjSubgroup W (g * (c * y)) = W := hW _ hy2
  refine ⟨g * c, ?_, fun a ha => ?_⟩
  · rw [← conjSubgroup_eq_iff_mem_normalizer]
    have h3 : conjSubgroup (conjSubgroup W (g * c)) y = W := by
      rw [conjSubgroup_conjSubgroup, mul_assoc]
      exact h2
    have h4 : conjSubgroup W (g * c) =
        conjSubgroup (conjSubgroup (conjSubgroup W (g * c)) y) y⁻¹ := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [h4, h3]
    exact conjSubgroup_eq_iff_mem_normalizer.2
      ((Subgroup.normalizer (W : Set G)).inv_mem (conjSubgroup_eq_iff_mem_normalizer.1 h1))
  · have hc' := Subgroup.mem_centralizer_iff.mp hcN (g⁻¹ * a * g) ⟨a, ha, rfl⟩
    calc (g * c)⁻¹ * a * (g * c) = c⁻¹ * ((g⁻¹ * a * g) * c) := by group
      _ = c⁻¹ * (c * (g⁻¹ * a * g)) := by rw [hc']
      _ = g⁻¹ * a * g := by group

namespace H13.Ch9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem mem_fsuM_of_le_map_conj (h3108 : Stmt3_2_10_eight) {D : Subgroup G}
    (hDV : D ≤ fsuV T I) (hDM : Subgroup.centralizer (D : Set G) ≤ fsuM T L) {g : G}
    (hg : D ≤ (fsuV T I).map (MulAut.conj g).toMonoidHom) : g ∈ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set P : Sylow 2 G := hfsu.sylow.1.toSylow hfsu.sylow.2 with hP
  have hPT : (P : Subgroup G) = T := IsPGroup.toSylow_coe hfsu.sylow.1 hfsu.sylow.2
  have hWT : thompsonJ T ≤ P := hPT ▸ thompsonJ_le_self T
  have hW : IsWeaklyClosedIn (thompsonJ T) P := hPT ▸ Prop3210.thompsonJ_isWeaklyClosedIn
  have hA : ∀ w ∈ thompsonJ T, ∀ a ∈ (D : Set G), w * a = a * w := fun w hw a ha =>
    (Subgroup.mem_centralizer_iff.mp (S.hJ hw) a (hDV ha)).symm
  have hB : ∀ w ∈ thompsonJ T, ∀ a ∈ (D : Set G), w * (g⁻¹ * a * g) = (g⁻¹ * a * g) * w := by
    intro w hw a ha
    obtain ⟨v, hv, hva⟩ := Subgroup.mem_map.mp (hg ha)
    have hv' : g⁻¹ * a * g = v := by
      rw [← hva]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hv']
    exact (Subgroup.mem_centralizer_iff.mp (S.hJ hw) v hv).symm
  obtain ⟨m, hmN, hm⟩ := burnside_fusion_pointwise P hWT hW hA hB
  have hmM : m ∈ fsuM T L :=
    (h3108 G T L I (fsuV T I) hfsu S.isVplus_V S.hJ (thompsonJ T)
      (hfsu.sylow.1.to_le (thompsonJ_le_self T)) le_rfl).2 hmN
  have hk : g * m⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hm a ha
    calc a * (g * m⁻¹) = g * (g⁻¹ * a * g) * m⁻¹ := by group
      _ = g * (m⁻¹ * a * m) * m⁻¹ := by rw [h1]
      _ = g * m⁻¹ * a := by group
  have := (fsuM T L).mul_mem (hDM hk) hmM
  simpa using this

end Setup

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem centralizer_pair_le (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h2 : n = 2) {X₀ X₁ : Matrix (Fin 2) (Fin 2) K}
    (hX₀ : X₀.det ≠ 0) (hX₁ : X₁.det ≠ 0) (hne : ∀ c : K, X₁ ≠ c • X₀) {v u : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1) (hu : u ∈ inV e (Om4Pt.lineM X₁))
    (hu1 : u ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({u} : Set G) ≤ fsuM T L := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  rintro x ⟨hxv, hxu⟩
  have h1 := (hc.prop941 h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h2 hX₀ hv
    hv1).2 hxv
  have h3 := (hc.prop941 h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h2 hX₁ hu
    hu1).2 hxu
  have h4 := Xi.mem_normalizer_sup h1 h3
  rwa [hc.sup_lPt_eq h37c h38c hK4 hX₀ hX₁ hne] at h4

end IsCoord

end Setup

end H13.Ch9

end CFSG.Quasithin
