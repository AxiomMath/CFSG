module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cDef
public import CFSG.LocalAnalysis.StandardType.PhanELocalSel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private lemma plh_inf_eq_bot_iff_not_le {a Y : Submodule K (Fin 4 → K)}
    (ha : finrank K a = 1) : a ⊓ Y = ⊥ ↔ ¬ a ≤ Y := by
  constructor
  · intro h hle
    have hbot : a = ⊥ := by rw [← inf_eq_left.mpr hle]; exact h
    have h0 : finrank K a = 0 := by rw [hbot, finrank_bot]
    omega
  · intro h
    by_contra hne
    have h0 : finrank K ↥(a ⊓ Y) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
    have hle1 : finrank K ↥(a ⊓ Y) ≤ 1 := ha ▸ Submodule.finrank_mono inf_le_left
    have h1 : finrank K ↥(a ⊓ Y) = 1 := by omega
    have heq : a ⊓ Y = a :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, ha])
    exact h (heq ▸ inf_le_right)

private lemma plh_le_sgS_iff (hK : Nat.card K = (2 ^ f) ^ 2)
    (a U : Submodule K (Fin 4 → K)) :
    a ≤ sgS K f 4 U ↔ sgS K f 4 a ≤ U := by
  constructor
  · intro h
    have hmono := sgS_mono (f := f) h
    rwa [sgS_sgS hK U] at hmono
  · intro h
    have hmono := sgS_mono (f := f) h
    rwa [sgS_sgS hK a] at hmono

private lemma plh_finrank_sup_point_of_not_le {L a : Submodule K (Fin 4 → K)}
    (hL : finrank K L = 2) (ha : finrank K a = 1) (h : ¬ a ≤ L) :
    finrank K ↥(L ⊔ a) = 3 := by
  have hinf : L ⊓ a = ⊥ := by
    rw [inf_comm]
    exact (plh_inf_eq_bot_iff_not_le ha).mpr h
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq L a
  rw [hinf, finrank_bot, add_zero, hL, ha] at hsum
  exact hsum

private lemma plh_inf_eq_bot_iff_finrank_sup {P Q : Submodule K (Fin 4 → K)}
    (hP : finrank K P = 2) (hQ : finrank K Q = 2) :
    P ⊓ Q = ⊥ ↔ finrank K ↥(P ⊔ Q) = 4 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
  constructor
  · intro hbot
    rw [hbot, finrank_bot, add_zero, hP, hQ] at h
    exact h
  · intro htop
    have h0 : finrank K ↥(P ⊓ Q) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0

theorem adm4c_iff_of_flag (hK : Nat.card K = (2 ^ f) ^ 2) {a L H : Submodule K (Fin 4 → K)}
    (hf : IsFlag a L H) :
    Adm4c f a L H ↔ ¬ sgS K f 4 a ≤ H ∧ L ⊓ sgS K f 4 L = ⊥ := by
  have hσa1 : finrank K (sgS K f 4 a) = 1 := by rw [finrank_sgS hK]; exact hf.p1
  have h1 : a ⊓ sgS K f 4 H = ⊥ ↔ ¬ sgS K f 4 a ≤ H := by
    rw [plh_inf_eq_bot_iff_not_le hf.p1]
    exact not_congr (plh_le_sgS_iff (f := f) hK a H)
  have h3 : H ⊓ sgS K f 4 a = ⊥ ↔ ¬ sgS K f 4 a ≤ H := by
    rw [inf_comm]
    exact plh_inf_eq_bot_iff_not_le hσa1
  unfold Adm4c
  rw [h1, h3]
  exact ⟨fun ⟨h, hL, _⟩ => ⟨h, hL⟩, fun ⟨h, hL⟩ => ⟨h, hL, h⟩⟩

theorem adm4c_nonreal (hK : Nat.card K = (2 ^ f) ^ 2) {p L H : Submodule K (Fin 4 → K)}
    (h : AdmCh (Adm4c (K := K) f) p L H) : sgS K f 4 p ≠ p := by
  obtain ⟨hf, hadm⟩ := h
  have hnot : ¬ sgS K f 4 p ≤ H := (adm4c_iff_of_flag (f := f) hK hf).mp hadm |>.1
  intro hfix
  exact hnot (by rw [hfix]; exact hf.pL.trans hf.LH)

theorem sgS_realLine (hK : Nat.card K = (2 ^ f) ^ 2) (p : Submodule K (Fin 4 → K)) :
    sgS K f 4 (p ⊔ sgS K f 4 p) = p ⊔ sgS K f 4 p := by
  rw [sgS_sup hK, sgS_sgS hK, sup_comm]

theorem finrank_realLine (hK : Nat.card K = (2 ^ f) ^ 2) {p : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hn : sgS K f 4 p ≠ p) :
    finrank K ↥(p ⊔ sgS K f 4 p) = 2 := by
  have hσp : finrank K (sgS K f 4 p) = 1 := by rw [finrank_sgS hK]; exact hp
  exact finrank_sup_of_ne_pts hp hσp hn.symm

theorem skew_iff (hK : Nat.card K = (2 ^ f) ^ 2) {x t : Submodule K (Fin 4 → K)}
    (hx : finrank K x = 1) (ht : finrank K t = 1) (hnx : sgS K f 4 x ≠ x) (hnt : sgS K f 4 t ≠ t)
    (hxt : x ≠ t) :
    (x ⊔ t) ⊓ sgS K f 4 (x ⊔ t) = ⊥ ↔
      (x ⊔ sgS K f 4 x) ⊓ (t ⊔ sgS K f 4 t) = ⊥ := by
  have hA2 : finrank K ↥(x ⊔ t) = 2 := finrank_sup_of_ne_pts hx ht hxt
  have hσA2 : finrank K ↥(sgS K f 4 (x ⊔ t)) = 2 := by rw [finrank_sgS hK, hA2]
  have hC2 : finrank K ↥(x ⊔ sgS K f 4 x) = 2 := finrank_realLine (f := f) hK hx hnx
  have hD2 : finrank K ↥(t ⊔ sgS K f 4 t) = 2 := finrank_realLine (f := f) hK ht hnt
  have hsup : finrank K ↥((x ⊔ t) ⊔ sgS K f 4 (x ⊔ t)) =
      finrank K ↥((x ⊔ sgS K f 4 x) ⊔ (t ⊔ sgS K f 4 t)) := by
    rw [sgS_sup hK,
      show (x ⊔ t) ⊔ (sgS K f 4 x ⊔ sgS K f 4 t) =
        (x ⊔ sgS K f 4 x) ⊔ (t ⊔ sgS K f 4 t) from by ac_rfl]
  rw [plh_inf_eq_bot_iff_finrank_sup hA2 hσA2,
    plh_inf_eq_bot_iff_finrank_sup hC2 hD2, hsup]

theorem adm4c_adj_iff (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {x y : Submodule K (Fin 4 → K)} (hx : finrank K x = 1) (hy : finrank K y = 1)
    (hnx : sgS K f 4 x ≠ x) (hny : sgS K f 4 y ≠ y) (hxy : x ≠ y) :
    AdmAdj (Adm4c (K := K) f) x y ↔ (x ⊔ y) ⊓ sgS K f 4 (x ⊔ y) = ⊥ := by
  rw [AdmAdj]
  constructor
  · rintro ⟨-, L, H, hxLH, hyLH⟩
    obtain ⟨hxf, hadmx⟩ := hxLH
    obtain ⟨hyf, _⟩ := hyLH
    have hL2 : finrank K L = 2 := hxf.L2
    have hsup_le : x ⊔ y ≤ L := sup_le hxf.pL hyf.pL
    have hL_eq : x ⊔ y = L := by
      refine Submodule.eq_of_le_of_finrank_eq hsup_le ?_
      rw [finrank_sup_of_ne_pts hx hy hxy, hL2]
    have hskew : L ⊓ sgS K f 4 L = ⊥ := hadmx.2.1
    rw [← hL_eq] at hskew
    exact hskew
  · intro hskew
    set L : Submodule K (Fin 4 → K) := x ⊔ y with hL
    have hL2 : finrank K L = 2 := by
      rw [hL]; exact finrank_sup_of_ne_pts hx hy hxy
    have hLskew : L ⊓ sgS K f 4 L = ⊥ := hskew
    have hxL : x ≤ L := by rw [hL]; exact le_sup_left
    have hyL : y ≤ L := by rw [hL]; exact le_sup_right
    have hsxL : ¬ sgS K f 4 x ≤ L := by
      intro h
      have hxσL : x ≤ sgS K f 4 L := by
        have hmono := sgS_mono (f := f) h
        rwa [sgS_sgS hK x] at hmono
      have hxbot : x ≤ (⊥ : Submodule K (Fin 4 → K)) := by
        have hle : x ≤ L ⊓ sgS K f 4 L := le_inf hxL hxσL
        rwa [hLskew] at hle
      have hx0 : x = ⊥ := le_bot_iff.mp hxbot
      rw [hx0, finrank_bot] at hx
      omega
    have hsyL : ¬ sgS K f 4 y ≤ L := by
      intro h
      have hyσL : y ≤ sgS K f 4 L := by
        have hmono := sgS_mono (f := f) h
        rwa [sgS_sgS hK y] at hmono
      have hybot : y ≤ (⊥ : Submodule K (Fin 4 → K)) := by
        have hle : y ≤ L ⊓ sgS K f 4 L := le_inf hyL hyσL
        rwa [hLskew] at hle
      have hy0 : y = ⊥ := le_bot_iff.mp hybot
      rw [hy0, finrank_bot] at hy
      omega
    have hσx1 : finrank K (sgS K f 4 x) = 1 := by rw [finrank_sgS hK]; exact hx
    have hσy1 : finrank K (sgS K f 4 y) = 1 := by rw [finrank_sgS hK]; exact hy
    have hLx3 : finrank K ↥(L ⊔ sgS K f 4 x) = 3 :=
      plh_finrank_sup_point_of_not_le hL2 hσx1 hsxL
    have hLy3 : finrank K ↥(L ⊔ sgS K f 4 y) = 3 :=
      plh_finrank_sup_point_of_not_le hL2 hσy1 hsyL
    have hLne : L ≠ ⊤ := by
      intro htop
      have h4 : finrank K L = 4 := by rw [htop, finrank_top, Module.finrank_fin_fun]
      omega
    have hLxne : L ⊔ sgS K f 4 x ≠ ⊤ := by
      intro htop
      have h4 : finrank K ↥(L ⊔ sgS K f 4 x) = 4 := by
        rw [htop, finrank_top, Module.finrank_fin_fun]
      omega
    have hLyne : L ⊔ sgS K f 4 y ≠ ⊤ := by
      intro htop
      have h4 : finrank K ↥(L ⊔ sgS K f 4 y) = 4 := by
        rw [htop, finrank_top, Module.finrank_fin_fun]
      omega
    obtain ⟨w, hw⟩ := exists_notMem_of_card_lt
      ({L, L ⊔ sgS K f 4 x, L ⊔ sgS K f 4 y} : Finset (Submodule K (Fin 4 → K)))
      (by
        intro T hT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl | rfl
        · exact hLne
        · exact hLxne
        · exact hLyne)
      (by
        have h3 : ({L, L ⊔ sgS K f 4 x, L ⊔ sgS K f 4 y} :
            Finset (Submodule K (Fin 4 → K))).card ≤ 3 := Finset.card_le_three
        have h16 : 16 ≤ Nat.card K := by
          rw [hK, pow_two]; exact Nat.mul_le_mul hq hq
        omega)
    have hwL : w ∉ L := hw L (by simp)
    have hwLx : w ∉ L ⊔ sgS K f 4 x := hw (L ⊔ sgS K f 4 x) (by simp)
    have hwLy : w ∉ L ⊔ sgS K f 4 y := hw (L ⊔ sgS K f 4 y) (by simp)
    have hw0 : w ≠ 0 := fun h0 => hwL (h0 ▸ L.zero_mem)
    have hspan1 : finrank K ↥(Submodule.span K {w}) = 1 := finrank_span_singleton hw0
    have hdisj : L ⊓ Submodule.span K {w} = ⊥ := by
      rw [inf_comm]
      exact (plh_inf_eq_bot_iff_not_le hspan1).mpr (by
        rw [Submodule.span_singleton_le_iff_mem]; exact hwL)
    let H : Submodule K (Fin 4 → K) := L ⊔ Submodule.span K {w}
    have hH3 : finrank K H = 3 := by
      rw [show H = L ⊔ Submodule.span K {w} from rfl,
        finrank_sup_of_disjoint (disjoint_iff.mpr hdisj), hL2, hspan1]
    have hLH : L ≤ H := by
      rw [show H = L ⊔ Submodule.span K {w} from rfl]; exact le_sup_left
    have hwH : w ∈ H := by
      rw [show H = L ⊔ Submodule.span K {w} from rfl]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
    have hsxH : ¬ sgS K f 4 x ≤ H := by
      intro hsx
      have hsup_le : L ⊔ sgS K f 4 x ≤ H := sup_le hLH hsx
      have heq : L ⊔ sgS K f 4 x = H :=
        Submodule.eq_of_le_of_finrank_eq hsup_le (by rw [hLx3, hH3])
      have : w ∈ L ⊔ sgS K f 4 x := by rw [heq]; exact hwH
      exact hwLx this
    have hsyH : ¬ sgS K f 4 y ≤ H := by
      intro hsy
      have hsup_le : L ⊔ sgS K f 4 y ≤ H := sup_le hLH hsy
      have heq : L ⊔ sgS K f 4 y = H :=
        Submodule.eq_of_le_of_finrank_eq hsup_le (by rw [hLy3, hH3])
      have : w ∈ L ⊔ sgS K f 4 y := by rw [heq]; exact hwH
      exact hwLy this
    refine ⟨hxy, L, H, ⟨⟨hx, hL2, hH3, hxL, hLH⟩, ?_⟩,
      ⟨⟨hy, hL2, hH3, hyL, hLH⟩, ?_⟩⟩
    · exact (adm4c_iff_of_flag (f := f) hK ⟨hx, hL2, hH3, hxL, hLH⟩).mpr ⟨hsxH, hLskew⟩
    · exact (adm4c_iff_of_flag (f := f) hK ⟨hy, hL2, hH3, hyL, hLH⟩).mpr ⟨hsyH, hLskew⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
