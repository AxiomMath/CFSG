module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1FFW
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped Matrix

namespace Sec1211Ns

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem normalizer_le_normalizer_centralizer {G : Type} [Group G] [Finite G] (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro m hm
  refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  have hy' : m⁻¹ * y * m ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) y).mp hy
    rwa [inv_inv] at this
  have h1 := Subgroup.mem_centralizer_iff.mp hx _ hy'
  calc y * (m * x * m⁻¹) = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by rw [h1]
    _ = m * x * m⁻¹ * y := by group

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  (S : Setting T L V V₁ V₂ n a₀ c₀)
include S

theorem mem_normalizer₁_of {x : G} (hxM : x ∈ Subgroup.normalizer (L : Set G))
    (hxW : x ∈ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer (V₁ : Set G) := by
  have := S.hVe.1
  by_contra hn
  obtain ⟨h₁, -⟩ := Sec121Swap.swap_of_hyp121 S.hyp hxM hn
  obtain ⟨y, hy, hy0, -⟩ := VecStab.exists_perp_ne S.three_le' S.y₀_ne 0
  have hy' : y ⬝ᵥ S.C₂.E c₀ = 0 := by rw [dotProduct_comm]; exact hy
  have hw := S.inv_mem_W₁ hy'
  have hw1 : S.C₁.inv y ≠ 1 := fun h => hy0 (by rw [← S.C₁.E_inv y, h, S.C₁.E_one])
  have hxw : x * S.C₁.inv y * x⁻¹ = S.C₁.inv y := by
    rw [← Subgroup.mem_centralizer_iff.mp hxW _ (Subgroup.mem_sup_left hw), mul_inv_cancel_right]
  have h3 : S.C₁.inv y ∈ V₁ ⊓ V₂ := ⟨hw.1, hxw ▸ h₁ _ hw.1⟩
  rw [S.hyp.inf, Subgroup.mem_bot] at h3
  exact hw1 h3

theorem mem_centralizer_V_of {x : G} (hxM : x ∈ Subgroup.normalizer (L : Set G))
    (hxv : x ∈ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (hxW : x ∈ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  have hβ := KGH91.isDualPairing S.C₁ S.C₂ S.dual
  have hxX : x ∈ Xv L V₁ (a₀ * c₀) := ⟨⟨hxM, S.mem_normalizer₁_of hxM hxW⟩, hxv⟩
  obtain ⟨hxa, hxc⟩ := S.Xv_fix hxX
  have hfixW : ∀ w ∈ S.W₁ ⊔ S.W₂, x * w * x⁻¹ = w := fun w hw => by
    rw [← Subgroup.mem_centralizer_iff.mp hxW w hw, mul_inv_cancel_right]
  have hfix₁ : ∀ a ∈ V₁, x * a * x⁻¹ = a := by
    intro a ha
    rcases zmod2_cases (KGH91.pairing S.C₁ S.C₂ a c₀) with h0 | h1
    · exact hfixW a (Subgroup.mem_sup_left ⟨ha, h0⟩)
    · have hmem : a₀ * a ∈ S.W₁ := ⟨V₁.mul_mem S.ha₀ ha, by
        show KGH91.pairing S.C₁ S.C₂ (a₀ * a) c₀ = 0
        rw [hβ.1 a₀ S.ha₀ a ha c₀ S.hc₀, S.hns, h1]
        decide⟩
      have h2 := hfixW _ (Subgroup.mem_sup_left hmem)
      have e : x * (a₀ * a) * x⁻¹ = (x * a₀ * x⁻¹) * (x * a * x⁻¹) := by group
      rw [e, hxa] at h2
      exact mul_left_cancel h2
  have hfix₂ : ∀ c ∈ V₂, x * c * x⁻¹ = c := by
    intro c hc
    rcases zmod2_cases (KGH91.pairing S.C₁ S.C₂ a₀ c) with h0 | h1
    · exact hfixW c (Subgroup.mem_sup_right ⟨hc, h0⟩)
    · have hmem : c₀ * c ∈ S.W₂ := ⟨V₂.mul_mem S.hc₀ hc, by
        show KGH91.pairing S.C₁ S.C₂ a₀ (c₀ * c) = 0
        rw [hβ.2.1 a₀ S.ha₀ c₀ S.hc₀ c hc, S.hns, h1]
        decide⟩
      have h2 := hfixW _ (Subgroup.mem_sup_right hmem)
      have e : x * (c₀ * c) * x⁻¹ = (x * c₀ * x⁻¹) * (x * c * x⁻¹) := by group
      rw [e, hxc] at h2
      exact mul_left_cancel h2
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hy
  have h3 : x * (a * c) * x⁻¹ = a * c := by
    calc x * (a * c) * x⁻¹ = (x * a * x⁻¹) * (x * c * x⁻¹) := by group
      _ = a * c := by rw [hfix₁ a ha, hfix₂ c hc]
  calc a * c * x = x * (a * c) * x⁻¹ * x := by rw [h3]
    _ = x * (a * c) := by group

theorem thompsonJ_le (F : Frame S 3) {P : Subgroup G} (hPM : P ≤ Subgroup.normalizer (L : Set G))
    (hPv : P ≤ Subgroup.centralizer ({a₀ * c₀} : Set G)) (hWP : S.W₁ ⊔ S.W₂ ≤ P) :
    thompsonJ P ≤ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) := by
  refine GammaExtra.thompsonJ_le fun A hA => ?_
  by_contra hAW
  have hWe : IsElemAbelian 2 (S.W₁ ⊔ S.W₂) := Sec1216Gen.isElemAbelian_of_le S.hVe S.W_le_V
  have h1 := card_le_relIndex_mul_card hWe hWP hA
  rw [card_W F] at h1
  by_cases hA1 : A ≤ Subgroup.normalizer (V₁ : Set G)
  · have h2 := card_mul_card_le_of_le F
      (fun a ha => ⟨⟨hPM (hA.1 ha), hA1 ha⟩, hPv (hA.1 ha)⟩) hA.2.1 hAW
    omega
  · have h2 := card_mul_card_le_of_swap F (hA.1.trans hPM) (hA.1.trans hPv) hA.2.1 hA1
    omega

theorem exists_sylow (h331 : Stmt3_3_1) (F : Frame S 3) :
    ∃ R : Subgroup G, IsSylowTwoOf R (Subgroup.centralizer ({a₀ * c₀} : Set G)) ∧
      R ≤ Subgroup.normalizer (L : Set G) ∧ T ⊓ Subgroup.centralizer (V : Set G) ≤ R ∧
        S.W₁ ⊔ S.W₂ ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.hVe.1
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  set Mv := M ⊓ H with hMv
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using S.hVe.2 x x.2)⟩
  have hVH : V ≤ H := fun x hx => by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact S.comm hx S.v_mem
  have hCV : Subgroup.centralizer (V : Set G) ≤ H := Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr S.v_mem)
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hQMv : Q ≤ Mv := le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hRM : R ≤ M := hR.1.trans inf_le_left
  have hRH : R ≤ H := hR.1.trans inf_le_right
  have hVMv : V ≤ Mv := le_inf S.hyp.le hVH
  have hVR : V ≤ R := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVMv
    (inf_le_left.trans S.le_normalizer) hV2).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hR)
  have hWR : S.W₁ ⊔ S.W₂ ≤ R := S.W_le_V.trans hVR
  have hJ := S.thompsonJ_le F hRM hRH hWR
  have hTM : IsSylowTwoOf T M := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow S.hTL
  have hQsyl : IsSylowTwoOf (T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)))
      (M ⊓ Subgroup.centralizer (V : Set G)) :=
    A4.isSylowTwoOf_inf_normal hTM inf_le_left fun m hm =>
      Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer hm)
        (normalizer_le_normalizer_centralizer V (S.le_normalizer hm))
  have hQeq : T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) = Q := by
    rw [hQ, ← inf_assoc, inf_eq_left.mpr S.hTL]
  rw [hQeq] at hQsyl
  have hRQ : R ⊓ Subgroup.centralizer (V : Set G) ≤ Q :=
    (A4.isSylowTwoOf_iff_maximal.mp hQsyl).2.2 _ (inf_le_inf_right _ hRM)
      (hR.2.1.to_le inf_le_left) (le_inf hQR inf_le_right)
  have hJQ : thompsonJ R ≤ Q := fun x hx => by
    have hxR : x ∈ R := GammaExtra.thompsonJ_le_self R hx
    exact hRQ ⟨hxR, S.mem_centralizer_V_of (hRM hxR) (hRH hxR) (hJ hx)⟩
  have hJeq : thompsonJ Q = thompsonJ R := GammaExtra.thompsonJ_eq_of_le hJQ hQR
  have huniq := Sec1215.isUniqueM_of_hyp121 h331 S.hyp S.hTL
  have hv1 : a₀ * c₀ ≠ 1 := S.v_ne_one
  have hvQ : a₀ * c₀ ∈ Q := ⟨Sec1215.le_of_hyp121 S.hyp S.hTL S.v_mem,
    Subgroup.mem_centralizer_iff.mpr fun y hy => S.comm hy S.v_mem⟩
  have hJ1 : thompsonJ Q ≠ ⊥ := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian Q
    have hZe : IsElemAbelian 2 (Subgroup.zpowers (a₀ * c₀)) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
        exact ((Commute.refl (a₀ * c₀)).zpow_zpow i j).eq
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          S.hVe.2 _ S.v_mem, _root_.one_zpow]
    have h2 := hA.2.2 _ (by rw [Subgroup.zpowers_le]; exact hvQ) hZe
    rw [Nat.card_zpowers, S.orderOf_v] at h2
    intro h
    have hA1 : A = ⊥ := le_bot_iff.mp (h ▸ GammaExtra.le_thompsonJ hA)
    rw [hA1, Subgroup.card_bot] at h2
    omega
  have hJ2 : IsPGroup 2 (thompsonJ Q) := hQ2.to_le (GammaExtra.thompsonJ_le_self Q)
  obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
    (⟨thompsonJ Q, hJ1, hJ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (thompsonJ Q : Set G)))
  have hM'M : M' = M :=
    huniq.2 M' ⟨hM', (GammaExtra.normalizer_le_normalizer_thompsonJ Q).trans hNM'⟩
  have hNR : Subgroup.normalizer (R : Set G) ≤ M := by
    have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ R
    rw [← hJeq] at h1
    exact h1.trans (hM'M ▸ hNM')
  refine ⟨R, Sec1215.isSylowTwoOf_of_normalizer_le hRH hNR (by rw [inf_comm]; exact hR), hRM,
    hQR, hWR⟩

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
