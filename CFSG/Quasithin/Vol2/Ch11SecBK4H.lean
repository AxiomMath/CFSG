module

public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBK4C
public import CFSG.Quasithin.Vol2.Ch11SecBK4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.Quasithin.Vol2.KGNat (spJ)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem rootInv_sp4 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2]
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {T : Subgroup G} (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G))
    (hx2 : SecA.conjV V x hxV * SecA.conjV V x hxV = 1)
    (hm : E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) = n) :
    ∃ g ∈ L, V ⊓ Subgroup.centralizer (L : Set G) ≤
        conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g ∧
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G))
        (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g) ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex
        (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g) = 2 ^ (n * 3) ∧
      T ⊓ L ≤ Subgroup.normalizer
        (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) g : Set G) := by
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  obtain ⟨T', σ, hσ, hT'⟩ := exists_semilinear_conjV hf
    (fun T hT => KGNat.commutant_statedSp T hT) (x₀ := KGNat.vec4 (1 : K) 0 0 0)
    (fun h => one_ne_zero (congrFun h (.inl 0))) hxV hxL
  have hm' := hm
  rw [mQuot_inf_centralizer hxV] at hm'
  have hC : ∀ w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)), T' (f w) = f w :=
    fun w hw => by rw [← hT', mem_fixV_zpowers.mp hw]
  have hM := card_fun_four hK
  have hlow := two_pow_le_card_fix hV hf hC hM hm'
  obtain ⟨y₀, hy₀⟩ : ∃ y, T' y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx1 (mem_centralizer_of_sp4 hLV hVL hf hxV hxL fun v => by rw [hT', h])
  have hup := card_mul_card_fix_le T' σ hσ hy₀ (by
    rw [hM, hK, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcard : Nat.card {z : Fin 2 ⊕ Fin 2 → K // T' z = z} = 2 ^ (3 * n) := by
    rw [hM, hK, show 4 * n = n + 3 * n by ring, pow_add] at hup
    rw [show 4 * n = n + 3 * n by ring, pow_add] at hlow
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
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := T'
      map_add' := map_add T'
      map_smul' := fun c z => by rw [hσ, hσ1]; rfl }
  have hTLe : ∀ z, TL z = T' z := fun z => rfl
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ z,
      TL (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ z) =
        ((γ' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ TL z := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, G2Q8.conjV_mul_conjV_inv_mem hxL hxV (π γ).2⟩
    refine ⟨γ', fun z => ?_⟩
    obtain ⟨w, rfl⟩ := hf.surj z
    have h1 : SecA.conjV V x hxV (((π γ : ↥(autOn L V)) : MulAut ↥V) w) =
        ((π γ' : ↥(autOn L V)) : MulAut ↥V) (SecA.conjV V x hxV w) := by
      have h2 : ((π γ' : ↥(autOn L V)) : MulAut ↥V) =
          SecA.conjV V x hxV * ((π γ : ↥(autOn L V)) : MulAut ↥V) * (SecA.conjV V x hxV)⁻¹ :=
        congrArg Subtype.val hγ'
      rw [h2, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    have e1 := hf.act γ w
    have e2 := hf.act γ' (SecA.conjV V x hxV w)
    have h3 : T' ((KGNat.linModelNat (StatedSp 2 K)).lin γ (f w)) =
        (KGNat.linModelNat (StatedSp 2 K)).lin γ' (T' (f w)) :=
      calc T' ((KGNat.linModelNat (StatedSp 2 K)).lin γ (f w))
          = T' (f (((π γ : ↥(autOn L V)) : MulAut ↥V) w)) := congrArg _ e1.symm
        _ = f (SecA.conjV V x hxV (((π γ : ↥(autOn L V)) : MulAut ↥V) w)) := (hT' _).symm
        _ = f (((π γ' : ↥(autOn L V)) : MulAut ↥V) (SecA.conjV V x hxV w)) := congrArg f h1
        _ = (KGNat.linModelNat (StatedSp 2 K)).lin γ' (f (SecA.conjV V x hxV w)) := e2
        _ = (KGNat.linModelNat (StatedSp 2 K)).lin γ' (T' (f w)) := by rw [hT']
    simp only [KGNat.linModelNat_lin] at h3
    exact h3
  obtain ⟨c, hc⟩ := KGNat.exists_similitude TL hnorm
  have hTT : ∀ z, TL (TL z) = z := by
    intro z
    obtain ⟨w, rfl⟩ := hf.surj z
    rw [hTLe, hTLe, ← hT', ← hT', ← MulAut.mul_apply, hx2, MulAut.one_apply]
  have hiso : ∀ u v, Matrix.toBilin' (spJ K) (T' u) (T' v) = Matrix.toBilin' (spJ K) u v := by
    intro u v
    rw [← hTLe, ← hTLe, hc, KGNat.similitude_eq_one hTT hc, one_mul]
  set v₀ := T' y₀ - y₀ with hv₀
  have hv₀0 : v₀ ≠ 0 := sub_ne_zero.mpr hy₀
  have hperp : ∀ z, T' z = z → Matrix.toBilin' (spJ K) z v₀ = 0 := by
    intro z hz
    rw [hv₀, map_sub, ← hiso z y₀, hz, sub_self]
  let Sv : Submodule K (Fin 2 ⊕ Fin 2 → K) := LinearMap.ker ((Matrix.toBilin' (spJ K)).flip v₀)
  have hSv : ∀ z, z ∈ Sv ↔ Matrix.toBilin' (spJ K) z v₀ = 0 := fun z => Iff.rfl
  obtain ⟨z₀, hz₀⟩ : ∃ z, Matrix.toBilin' (spJ K) z v₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hv₀0 (KGNat.toBilin'_spJ_nondegenerate.2 v₀ h)
  have hSvcard : Nat.card Sv ≤ 2 ^ (3 * n) := by
    have h1 := card_mul_le_of_mem le_top Submodule.mem_top (x₀ := z₀) (S := Sv)
      (fun h => hz₀ ((hSv z₀).mp h))
    have htop : Nat.card (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) = 2 ^ (4 * n) := by
      rw [← hM]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => Submodule.mem_top)
    rw [htop, hK, show 4 * n = 3 * n + n by ring, pow_add] at h1
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hCSv : ∀ z, T' z = z ↔ Matrix.toBilin' (spJ K) z v₀ = 0 := by
    intro z
    refine ⟨hperp z, fun hz => ?_⟩
    by_contra hz'
    let C' : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
      { carrier := {y | T' y = y}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_add, ha, hb]
        zero_mem' := by simp
        smul_mem' := fun c y hy => by
          simp only [Set.mem_ofPred_eq] at hy ⊢
          rw [hσ, hσ1, hy] }
    have h1 := card_mul_le_of_mem (S := C') (S' := Sv) (fun y hy => (hSv y).mpr (hperp y hy))
      ((hSv z).mpr hz) hz'
    have h2 : Nat.card C' = 2 ^ (3 * n) := hcard
    rw [h2, hK] at h1
    have h3 := h1.trans hSvcard
    rw [← pow_add] at h3
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
    omega
  have hfull : ∀ w : ↥V, T' (f w) = f w → w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)) :=
    fun w hw => mem_of_rkIdx_add_le hV hf hC hM hcard.le (by omega) hw
  have hU : ∀ v : ↥V, (v : G) ∈ V ⊓ Subgroup.centralizer ({x} : Set G) ↔
      f v ∈ Sv.toAddSubgroup := by
    intro v
    rw [← Subgroup.mem_subgroupOf, inf_centralizer_subgroupOf hxV]
    exact ⟨fun h => (hCSv _).mp (hC v h), fun h => hfull v ((hCSv _).mpr h)⟩
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g₀, hg₀⟩ := KGNat.exists_sylow_eq_conj_Usp hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hLV hTL')
  have hge : mat 2 K g₀ *ᵥ KGNat.vec4 1 0 0 0 ≠ 0 := by
    intro h
    have h1 := congrArg (fun z => mat 2 K g₀⁻¹ *ᵥ z) h
    simp only [KGNat.mat_inv_mulVec, Matrix.mulVec_zero] at h1
    exact one_ne_zero (congrFun h1 (.inl 0))
  obtain ⟨γ, hγ⟩ := KGNat.exists_sp4_lin_eq _ v₀ hge hv₀0
  rw [KGNat.linModelNat_lin] at hγ
  change mat 2 K γ *ᵥ (mat 2 K g₀ *ᵥ KGNat.vec4 1 0 0 0) = v₀ at hγ
  obtain ⟨l, hl, hlV, hlA⟩ := SecA.mem_autOn_iff.mp (π γ).2
  have hW'V : conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) l ≤ V :=
    G2Q8.conjSubgroup_le_of_le inf_le_left hlV
  have hW' : (conjSubgroup (V ⊓ Subgroup.centralizer ({x} : Set G)) l).subgroupOf V =
      hf.pre (KGNat.gmapSp g₀ (KGNat.spHyp K)).toAddSubgroup := by
    ext v
    rw [Subgroup.mem_subgroupOf, mem_conjSubgroup_iff_lin hf hU hlV hlA v]
    change Matrix.toBilin' (spJ K) ((KGNat.linModelNat (StatedSp 2 K)).lin γ (f v)) v₀ = 0 ↔
      f v ∈ KGNat.gmapSp g₀ (KGNat.spHyp K)
    rw [KGNat.linModelNat_lin, KGNat.mem_gS3_iff, ← hγ]
    change Matrix.toBilin' (spJ K) (mat 2 K γ *ᵥ f v)
      (mat 2 K γ *ᵥ (mat 2 K g₀ *ᵥ KGNat.vec4 1 0 0 0)) = 0 ↔ _
    rw [KGNat.spB_mat, K7.bil_comm]
  have hfl := KGNat.isFlagW_pre_sp hsq hf hg₀ KGNat.spHyp_stable KGNat.card_spHyp
  rw [← hW', hK] at hfl
  exact ⟨l, hl, flag_conclusions hLV hW'V hfl⟩

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
