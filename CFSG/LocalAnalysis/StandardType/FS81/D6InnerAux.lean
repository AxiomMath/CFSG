module

public import CFSG.LocalAnalysis.StandardType.FS81.RootLineRigid
public import CFSG.LocalAnalysis.StandardType.FS81.WtTwo
public import CFSG.LocalAnalysis.StandardType.FS81.OrthInner
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.FS81.AutMat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

theorem wt_le_of_apply_zero {n : ℕ} {e : Coords (n + 1)} (h : e 0 = 0) : wt e ≤ n := by
  rw [wt]
  calc (Finset.univ.filter fun i : Fin (n + 1) => e i ≠ 0).card
      ≤ (Finset.univ.erase (0 : Fin (n + 1))).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi
        exact Finset.mem_erase.mpr ⟨fun h0 => hi.2 (h0 ▸ h), Finset.mem_univ i⟩
    _ = n := by simp

theorem vec_mem_K_imp_zero {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G 7} (hB : Adapted B b₀ K E) (hb₀ord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) (hb₀E : b₀ ∈ E)
    {v : Coords 7} (hv : B.vec v ∈ K) : v 0 = 0 := by
  obtain ⟨-, hb0, hbiK⟩ := hB
  have hrest : (List.ofFn fun i : Fin 6 => B.b i.succ ^ (v i.succ).val).prod ∈ K := by
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.pow_mem K (hbiK i.succ (Fin.succ_ne_zero i)) _
  have hsplit : B.vec v = B.b 0 ^ (v 0).val *
      (List.ofFn fun i : Fin 6 => B.b i.succ ^ (v i.succ).val).prod := by
    unfold Basis3.vec
    rw [List.ofFn_succ, List.prod_cons]
  have hpowK : B.b 0 ^ (v 0).val ∈ K := by
    rw [hsplit] at hv
    exact (Subgroup.mul_mem_cancel_right K hrest).mp hv
  have hzp : B.b 0 ^ (v 0).val ∈ Subgroup.zpowers b₀ := by
    rw [hb0]
    exact Subgroup.pow_mem (Subgroup.zpowers b₀) (Subgroup.mem_zpowers b₀) _
  have hE : B.b 0 ^ (v 0).val ∈ E := by
    rw [hb0]
    exact (Subgroup.zpowers_le.mpr hb₀E) (Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _)
  have hone : B.b 0 ^ (v 0).val = 1 :=
    (Subgroup.disjoint_def.mp hdisj) hzp ⟨hE, hpowK⟩
  have hval : (v 0).val = 0 := by
    have hpow1 : b₀ ^ (v 0).val = 1 := by
      rwa [hb0] at hone
    have hdvd : orderOf b₀ ∣ (v 0).val := orderOf_dvd_iff_pow_eq_one.mpr hpow1
    have hdvd3 : 3 ∣ (v 0).val := by
      rwa [hb₀ord] at hdvd
    exact Nat.eq_zero_of_dvd_of_lt hdvd3 (ZMod.val_lt (v 0))
  exact (ZMod.val_eq_zero (v 0)).mp hval

theorem isConjLine_map_conj {G : Type} [Group G] {x : G} {Z : Subgroup G}
    (h : IsConjLine x Z) (c : G) :
    IsConjLine x (Z.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨c * g, ?_⟩
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (c * g * x * (c * g)⁻¹) =
    Subgroup.zpowers (c * (g * x * g⁻¹) * c⁻¹)
  congr 1
  group

theorem line_map_conj {G : Type} [Group G] {k : ℕ} {B : Basis3 G k} {c : G}
    {M : Matrix (Fin k) (Fin k) (ZMod 3)} (h : B.Acts c M) (v : Coords k) :
    (B.line v).map (MulAut.conj c).toMonoidHom = B.line (M *ᵥ v) := by
  rw [Basis3.line, MonoidHom.map_zpowers, Basis3.line]
  change Subgroup.zpowers (c * B.vec v * c⁻¹) = Subgroup.zpowers (B.vec (M *ᵥ v))
  rw [B.acts_vec h]

theorem card_realized_eq_card_ggInduced {G : Type} [Group G] [Finite G] {k : ℕ}
    (B : Basis3 G k) {F : Subgroup G} (hspan : B.span = F) (H : Subgroup G) :
    Nat.card ↥(B.realized H) = Nat.card ↥(ggInduced H F) := by
  subst hspan
  have himg : B.realized H = B.matOf '' ggInduced H B.span := by
    ext A
    rw [Set.mem_image]
    exact B.mem_realized_iff H A
  rw [himg]
  exact Nat.card_image_of_injective B.matOf_injective _

end CFSG.StandardType.FrameRoute.FS81
