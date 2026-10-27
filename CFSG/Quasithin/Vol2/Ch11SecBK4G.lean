module

public import CFSG.Quasithin.Vol2.Ch11SecBK4F
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBK4C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem rootInv_sl3 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2]
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSL 3 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {T : Subgroup G} (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G))
    (hm : E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) = n) :
    ∃ g ∈ L, V ⊓ Subgroup.centralizer (L : Set G) ≤
        conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g ∧
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G))
        (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g) ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex
        (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g) = 2 ^ (n * 2) ∧
      T ⊓ L ≤ Subgroup.normalizer
        (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g : Set G) := by
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  obtain ⟨T', σ, hσ, hT'⟩ := exists_semilinear_conjV hf
    (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT) (x₀ := ![1, 0, 0])
    (fun h => one_ne_zero (congrFun h 0)) hxV hxL
  have hm' := hm
  rw [mQuot_inf_centralizer hxV] at hm'
  have hC : ∀ w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)), T' (f w) = f w :=
    fun w hw => by rw [← hT', mem_fixV_zpowers.mp hw]
  have hM := card_fun_three hK
  have hlow := two_pow_le_card_fix hV hf hC hM hm'
  obtain ⟨y, hy⟩ : ∃ y, T' y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx1 (mem_centralizer_of_sl3 hLV hVL hf hxV hxL fun v => by rw [hT', h])
  have hup := card_mul_card_fix_le T' σ hσ hy (by
    rw [hM, hK, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcard : Nat.card {z : Fin 3 → K // T' z = z} = 2 ^ (2 * n) := by
    rw [hM, hK, show 3 * n = n + 2 * n by ring, pow_add] at hup
    rw [show 3 * n = n + 2 * n by ring, pow_add] at hlow
    exact le_antisymm (Nat.le_of_mul_le_mul_left hup (by positivity))
      (Nat.le_of_mul_le_mul_left hlow (by positivity))
  have hσ1 : ∀ c, σ c = c := by
    by_contra h
    simp only [not_forall] at h
    obtain ⟨θ, hθ⟩ := h
    have h1 := G2Q8.card_fix_sq_le T' σ hθ hσ
    rw [hcard, hM, ← pow_mul] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    omega
  let P : Submodule K (Fin 3 → K) :=
    { carrier := {z | T' z = z}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun c z hz => by
        simp only [Set.mem_ofPred_eq] at hz ⊢
        rw [hσ, hσ1, hz] }
  have hP : Nat.card P = Nat.card K ^ 2 := by
    rw [hK, ← pow_mul, mul_comm, ← hcard]
    rfl
  have hfull : ∀ w : ↥V, T' (f w) = f w → w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)) :=
    fun w hw => mem_of_rkIdx_add_le hV hf hC hM hcard.le (by omega) hw
  have hU : ∀ v : ↥V, (v : G) ∈ V ⊓ Subgroup.centralizer ({x} : Set G) ↔
      f v ∈ P.toAddSubgroup := by
    intro v
    rw [← Subgroup.mem_subgroupOf, inf_centralizer_subgroupOf hxV]
    exact ⟨hC v, hfull v⟩
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g₀, hg₀⟩ := KGNat.exists_sylow_eq_conj_Usl hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hLV hTL')
  obtain ⟨B, hB⟩ := exists_sl3_plane hP
  obtain ⟨l, hl, hlV, hlA⟩ := SecA.mem_autOn_iff.mp (KGNat.rho3 π (B * g₀⁻¹)).2
  have hW'V : conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) l ≤ V :=
    G2Q8.conjSubgroup_le_of_le inf_le_left hlV
  have hW' : (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) l).subgroupOf V =
      hf.pre (KGNat.gmap g₀ (KGNat.stdPlane K)).toAddSubgroup := by
    ext v
    rw [Subgroup.mem_subgroupOf,
      mem_conjSubgroup_iff_lin hf hU hlV (γ := specialLinearGroupEquivStatedSL 3 K (B * g₀⁻¹))
        hlA v]
    change (KGNat.linModelNat (StatedSL 3 K)).lin _ (f v) ∈ P ↔
      f v ∈ KGNat.gmap g₀ (KGNat.stdPlane K)
    rw [KGNat.linModelNat_lin, KGNat.mem_gmap]
    change ((B * g₀⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f v ∈ P ↔ _
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB]
  have hfl := KGNat.isFlagW_pre hsq hf hg₀ (S := KGNat.stdPlane K)
    (fun a b c z hz => KGNat.uMat_mem_stdPlane a b c hz) KGNat.card_stdPlane
  rw [← hW', hK] at hfl
  exact ⟨l, hl, flag_conclusions hLV hW'V hfl⟩

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
