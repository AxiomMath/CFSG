module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Mbar
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Rad

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace Cx5Conj

theorem conjugate_conjugate (H : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate H a) b = CFSG.conjugate H (a * b) := by
  show conjSubgroup (conjSubgroup H a) b = conjSubgroup H (a * b)
  exact conjSubgroup_conjSubgroup H a b

theorem conjugate_commutator (H K : Subgroup G) (k : G) :
    CFSG.conjugate ⁅H, K⁆ k = ⁅CFSG.conjugate H k, CFSG.conjugate K k⁆ := by
  unfold CFSG.conjugate
  rw [Subgroup.map_commutator]

theorem conjugate_inf (H K : Subgroup G) (k : G) :
    CFSG.conjugate (H ⊓ K) k = CFSG.conjugate H k ⊓ CFSG.conjugate K k := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjugate_iff_mul_mem]

theorem conjugate_mono {H K : Subgroup G} (h : H ≤ K) (k : G) :
    CFSG.conjugate H k ≤ CFSG.conjugate K k := fun _ hx =>
  mem_conjugate_iff_mul_mem.2 (h (mem_conjugate_iff_mul_mem.1 hx))

theorem conjugate_ne_bot {H : Subgroup G} (hH : H ≠ ⊥) (k : G) : CFSG.conjugate H k ≠ ⊥ := by
  intro h
  apply hH
  rw [eq_bot_iff]
  intro x hx
  have h1 : k⁻¹ * x * k ∈ CFSG.conjugate H k := by
    rw [mem_conjugate_iff_mul_mem, show k * (k⁻¹ * x * k) * k⁻¹ = x by group]
    exact hx
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem card_conjugate_inf_centralizer (H K : Subgroup G) (k : G) :
    Nat.card ↥(CFSG.conjugate H k ⊓ Subgroup.centralizer (CFSG.conjugate K k : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer (K : Set G)) := by
  rw [← conjugate_inf_centralizer, card_conjugate_eq]

theorem isElemAbelian_conjugate {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) :
    IsElemAbelian 2 (CFSG.conjugate V g) := by
  have := hV.1
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · have h1 : g * (a : G) * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) :=
      setLike_mul_comm (mem_conjugate_iff_mul_mem.1 a.2) (mem_conjugate_iff_mul_mem.1 b.2)
    have h2 : g * ((a : G) * b) * g⁻¹ = g * ((b : G) * a) * g⁻¹ := by
      calc g * ((a : G) * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := h1
        _ = g * ((b : G) * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · have h1 := hV.2 _ (mem_conjugate_iff_mul_mem.1 hx)
    have h2 : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [h2] at h1
    calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

end Cx5Conj

theorem card_statedSL_five_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

variable [Finite G] {T L V : Subgroup G} {z : G}

namespace Cx5Facts

theorem exists_conj_le_T (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z) {g : G}
    (hg1 : ⁅V, CFSG.conjugate V g⁆ ≠ ⊥)
    (hg2 : ⁅V, CFSG.conjugate V g⁆ ≤ V ⊓ CFSG.conjugate V g) :
    ∃ g' : G, ⁅V, CFSG.conjugate V g'⁆ ≠ ⊥ ∧
      ⁅V, CFSG.conjugate V g'⁆ ≤ V ⊓ CFSG.conjugate V g' ∧ CFSG.conjugate V g' ≤ T ∧
      Nat.card ↥(CFSG.conjugate V g' ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g' : Set G)) := by
  obtain ⟨g₀, h01, h02, h03⟩ : ∃ g₀ : G, ⁅V, CFSG.conjugate V g₀⁆ ≠ ⊥ ∧
      ⁅V, CFSG.conjugate V g₀⁆ ≤ V ⊓ CFSG.conjugate V g₀ ∧
      Nat.card ↥(CFSG.conjugate V g₀ ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g₀ : Set G)) := by
    by_cases hQ : Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G))
    · exact ⟨g, hg1, hg2, hQ⟩
    refine ⟨g⁻¹, ?_, ?_, ?_⟩
    · have h1 := Cx5Conj.conjugate_ne_bot hg1 g⁻¹
      rwa [Cx5Conj.conjugate_commutator, conjugate_conjugate_inv',
        Subgroup.commutator_comm] at h1
    · have h1 := Cx5Conj.conjugate_mono hg2 g⁻¹
      rwa [Cx5Conj.conjugate_commutator, Cx5Conj.conjugate_inf, conjugate_conjugate_inv',
        Subgroup.commutator_comm, inf_comm] at h1
    · have h1 := Cx5Conj.card_conjugate_inf_centralizer (CFSG.conjugate V g⁻¹) V g
      have h2 := Cx5Conj.card_conjugate_inf_centralizer V (CFSG.conjugate V g⁻¹) g
      rw [conjugate_inv_conjugate'] at h1 h2
      rw [← h1, ← h2]
      omega
  have hU : CFSG.conjugate V g₀ ≤ Subgroup.normalizer (V : Set G) :=
    (le_normalizer_of_commutator_le h02).1
  have hUp : IsPGroup 2 ↥(CFSG.conjugate V g₀) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 10) (by rw [card_conjugate_eq, hf.card])
  obtain ⟨n, hn, hnT⟩ := exists_conj_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo hcx.hyp.sylow hf.T_le) hU hUp
  have hk : CFSG.conjugate (CFSG.conjugate V g₀) n⁻¹ ≤ T := by
    intro x hx
    apply hnT
    rw [mem_cjSub]
    rw [mem_conjugate_iff_mul_mem, inv_inv] at hx
    exact hx
  have hV' : CFSG.conjugate V n⁻¹ = V :=
    conjugate_eq_of_mem_normalizer' ((Subgroup.normalizer (V : Set G)).inv_mem hn)
  have hU' : CFSG.conjugate V (g₀ * n⁻¹) = CFSG.conjugate (CFSG.conjugate V g₀) n⁻¹ :=
    (Cx5Conj.conjugate_conjugate V g₀ n⁻¹).symm
  have hcomm : ⁅V, CFSG.conjugate V (g₀ * n⁻¹)⁆ =
      CFSG.conjugate ⁅V, CFSG.conjugate V g₀⁆ n⁻¹ := by
    rw [Cx5Conj.conjugate_commutator, hV', hU']
  have hinf : V ⊓ CFSG.conjugate V (g₀ * n⁻¹) =
      CFSG.conjugate (V ⊓ CFSG.conjugate V g₀) n⁻¹ := by
    rw [Cx5Conj.conjugate_inf, hV', hU']
  refine ⟨g₀ * n⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hcomm]
    exact Cx5Conj.conjugate_ne_bot h01 n⁻¹
  · rw [hcomm, hinf]
    exact Cx5Conj.conjugate_mono h02 n⁻¹
  · rw [hU']
    exact hk
  · have h1 := Cx5Conj.card_conjugate_inf_centralizer (CFSG.conjugate V g₀) V n⁻¹
    have h2 := Cx5Conj.card_conjugate_inf_centralizer V (CFSG.conjugate V g₀) n⁻¹
    rw [hV', ← hU'] at h1 h2
    rw [h1, h2]
    exact h03

theorem mem_commutator_of_le_T [IsMulCommutative ↥V] (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10) (h1229 : Stmt12_2_9) (hpre : Pre1242)
    (h42 : AsB42) (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hA1 : autOn A V ≠ ⊥)
    (hr : Nat.card ↥V ≤ Nat.card (autOn A V) * Nat.card (fixV (autOn A V))) :
    z ∈ ⁅V, A⁆ := by
  have hyp := hcx.hyp
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hf.T_le
  have hX := hf.mbar_eq h1222 h3228 h12210 h1229 hpre h42 hcx h5
  have hTL : autOn T V ≤ autOn L V := (autOn_mono le_sup_right).trans hX.le
  have hAT' : autOn A V ≤ autOn T V := autOn_mono hAT
  have hA2 : IsA2 (autOn (L ⊔ T) V) (autOn A V) :=
    ⟨autOn_mono (hAT.trans le_sup_right), hA1, isElemAbelian2_autOn' hA⟩
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le hW2 hA2 ((rAV_le_one_iff hW2 hA2).2 hr)
  have hBL : B ≤ autOn L V := hB.1.trans hX.le
  have hc := h42 ↥V hW2 (autOn (L ⊔ T) V) (autOn L V) (hf.b4Hyp h1222 h3228 h12210 hcx h5) B hB
  obtain ⟨-, -, -, -, π, hπ, hrad⟩ := b42Case11_of_card hf.card (hf.card_lbar h5) hc
  have hGam : Nat.card (FFModel.extSq (ZMod 2) 5).Gam = 9999360 := card_statedSL_five_two
  have : Finite (FFModel.extSq (ZMod 2) 5).Gam :=
    Nat.finite_of_card_ne_zero (by rw [hGam]; norm_num)
  have hinj : Function.Injective π :=
    (hπ.1.bijective_of_nat_card_le (le_of_eq (by rw [hGam, hf.card_lbar h5]))).1
  have hTB : ∀ s ∈ autOn T V, ∀ b ∈ B, s * b * s⁻¹ ∈ B := by
    have hTp : IsPGroup 2 ↥((autOn T V).subgroupOf (autOn L V)) :=
      (isPGroup_autOn hyp.sylow.1).comap_subtype
    have hSp : IsPGroup 2 ↥(((autOn T V).subgroupOf (autOn L V)).comap π) :=
      hTp.comap_of_injective π hinj
    have hRS : (B.subgroupOf (autOn L V)).comap π ≤
        ((autOn T V).subgroupOf (autOn L V)).comap π :=
      Subgroup.comap_mono fun x hx =>
        Subgroup.mem_subgroupOf.2 (hAT' (hBA (Subgroup.mem_subgroupOf.1 hx)))
    have hnorm := le_normalizer_of_isEndNodeRadical5 hrad hSp hRS
    intro s hs b hb
    obtain ⟨σ, hσ⟩ : ∃ σ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
        π σ = ⟨s, hTL hs⟩ := hπ.1 _
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
        π ρ = ⟨b, hBL hb⟩ := hπ.1 _
    have hσS : σ ∈ ((autOn T V).subgroupOf (autOn L V)).comap π := by
      show π σ ∈ (autOn T V).subgroupOf (autOn L V)
      rw [hσ]
      exact Subgroup.mem_subgroupOf.2 hs
    have hρR : ρ ∈ (B.subgroupOf (autOn L V)).comap π := by
      show π ρ ∈ B.subgroupOf (autOn L V)
      rw [hρ]
      exact Subgroup.mem_subgroupOf.2 hb
    have h1 := (Subgroup.mem_normalizer_iff.1 (hnorm hσS) ρ).1 hρR
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, hσ, hρ] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hWB : ∀ τ : MulAut ↥V, (∀ b ∈ B, τ * b * τ⁻¹ ∈ B) → ∀ w ∈ commV B, τ w ∈ commV B := by
    intro τ hτ w hw
    induction hw using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, v, rfl⟩ := hc
      have h1 : (τ * x * τ⁻¹) (τ v) * (τ v)⁻¹ ∈ commV B :=
        Subgroup.subset_closure ⟨τ * x * τ⁻¹, hτ x hx, τ v, rfl⟩
      have h2 : τ (x v * v⁻¹) = (τ * x * τ⁻¹) (τ v) * (τ v)⁻¹ := by simp
      rw [h2]
      exact h1
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact (commV B).mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact (commV B).inv_mem hx
  set W : Subgroup G := (commV B).map V.subtype
  have hWV : W ≤ V := Subgroup.map_subtype_le _
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ t ∈ T, ∀ x ∈ W, t * x * t⁻¹ ∈ W := by
      intro t ht x hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hτ : conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn T V :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
      refine ⟨conjAct V ⟨t, hf.T_le ht⟩ w, hWB _ (hTB _ hτ) w hw, ?_⟩
      exact A1b.conjAct_coe V ⟨t, hf.T_le ht⟩ w
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hW1 : W ≠ ⊥ := by
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB.2.1
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v : ↥V, b v ≠ v := by
      by_contra h
      push Not at h
      exact hb1' (MulEquiv.ext fun v => h v)
    intro hW
    apply hv
    have h1 : (b v * v⁻¹ : ↥V) ∈ commV B := Subgroup.subset_closure ⟨b, hbB, v, rfl⟩
    have h2 : ((b v * v⁻¹ : ↥V) : G) ∈ W := ⟨_, h1, rfl⟩
    rw [hW, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.1 (Subtype.ext h2)
  obtain ⟨⟨w, hwW, hwC⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (inf_centralizer_ne_bot_of_isPGroup hyp.sylow.1 (hWV.trans hf.le_T) hTW hW1)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwz : w = z := hf.eq_of_mem_centralizer_T (hWV hwW) hwC hw1'
  rw [← hwz, ← map_commV_autOn hAN]
  refine Subgroup.map_mono (Subgroup.closure_mono ?_) hwW
  rintro _ ⟨g, hg, v, hv⟩
  exact ⟨g, hBA hg, v, hv⟩

end Cx5Facts

end CFSG.Quasithin.H13
