module

public import CFSG.Quasithin.Vol2.Ch3E213MOS11
public import CFSG.Quasithin.Vol2.Ch3E213MDefs

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.GLS.IVK CFSG.GH74.GLS B6 E2P

section Star

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

omit [Finite G] in
theorem star_sup_eq_top (hHK : H = K ⊔ T) : E2.star M H K ⊔ E2.star M H T = ⊤ := by
  have h : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (le_sup_left.trans hHK.ge),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans hHK.ge), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, ← hHK]
  rw [star_def, star_def, ← Subgroup.map_sup, h, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (starMap_surjective M H)]

theorem asHyp_star (hS : Setting H T M V K) (hC2 : Case2 H T M K)
    (hsimp : IsSimpleGroup ↥(E2.star M H K)) (hZ : Subgroup.center ↥(E2.star M H K) = ⊥)
    (hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a) :
    ASHyp (E2.star M H K) (E2.star M H T) (E2.star M H M) := by
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hS.eq_sup]
    exact sup_le Subgroup.le_normalizer hC2.1
  have hmp := minParabolic_star hS.hyp.minParabolic
  have hn := normal_star (M := M) hKH hHK
  have hsup := star_sup_eq_top (M := M) hS.eq_sup
  exact ⟨hmp, hn, hsimp, hnab, hsup, centralizer_eq_bot hmp (kerIn_star M H) hn hZ hsup⟩

end Star

theorem false_of_oddSingle (h12 : IVK_1_2_general) (h13a : IVK_1_3a) (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L)))
    {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G} (hS : Setting H T M V K)
    (hC2 : Case2 H T M K) {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p) (he : e = 1 ∨ e = 2)
    (hpsl : IsPSL 2 p e ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)))
    (hAut : 8 < E2.autCard (E2.star M H T) (E2.star M H K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := id hpsl
  have he0 : e ≠ 0 := by omega
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le hp3 (Nat.le_self_pow he0 p)
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hsimp : IsSimpleGroup ↥(E2.star M H K) := (e₀.trans (L2.equivPSL F)).isSimpleGroup
  have hinj := conj_injective_of_L2 e₀
  have hZ : Subgroup.center ↥(E2.star M H K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    ext y
    have h := (Subgroup.mem_center_iff.mp hx) y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h, mul_inv_cancel_right]
  have hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a := by
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥(E2.star M H K))
    have hca : MulAut.conj a ≠ 1 := fun h => ha (hinj (by rw [h, map_one]))
    obtain ⟨b, hb⟩ : ∃ b, MulAut.conj a b ≠ b := by
      by_contra hcon
      exact hca (MulEquiv.ext fun b => not_not.mp fun h => hcon ⟨b, h⟩)
    refine ⟨a, b, fun h => hb ?_⟩
    rw [MulAut.conj_apply, h, mul_inv_cancel_right]
  have hX := asHyp_star hS hC2 hsimp hZ hnab
  have hMH : M ≤ H := hS.hyp.minParabolic.maximal.1.le
  have hVT : E2.star M H V ≤ E2.star M H T :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hS.hyp.le_T)
  have hVn := star_le_normalizer (M := M) (H := H) hS.hyp.normal_T
  have hsq : ∀ x ∈ E2.star M H V, x * x = 1 :=
    star_sq fun v hv => by rw [← pow_two]; exact hS.hyp.elem.2 v hv
  have hV4 : 4 ≤ Nat.card (E2.star M H V) := hS.four_le.trans (relIndex_le_card_star hS.hyp)
  have hVM := star_le_pCoreOf hMH hS.hyp.le_pCoreOf
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    star_inf_T hS.hyp.minParabolic.isSylow hS.mem_cComp.2.2.1 hKH
  have hMK' : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓
      Subgroup.centralizer (zOf (E2.star M H T ⊓ E2.star M H K) : Set (E2.StarQuot M H)) := by
    rw [← star_inf_M, hMK, ← hTK]
    rfl
  exact false_of_asHyp h12 h13a h13b hcoat hX hp hp3 he hpsl hMK' hAut hVT hVn hsq hV4 hVM

theorem pkgOddSingle_of (h12 : IVK_1_2_general) (h13a : IVK_1_3a) (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L))) : PkgOddSingle := by
  intro G _ _ H T M V K hS hC2 p e hp hp3 he _ hpsl hMK hAut
  exact (false_of_oddSingle h12 h13a h13b hcoat hS hC2 hp hp3 he hpsl hMK hAut).elim

end CFSG.Quasithin.Ch3E213M.OS
