module

public import CFSG.RankThree.GF2n.Tim79a34Local
public import CFSG.RankThree.GF2n.Tim79a34Natural

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

theorem l13_eq_of_natCard_two {K : Type} [Group K] {S : Subgroup K} (hS : Nat.card S = 2)
    {y z : K} (hy : y ∈ S) (hz : z ∈ S) (hy1 : y ≠ 1) (hz1 : z ≠ 1) : y = z := by
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hS
  have h1 : (⟨y, hy⟩ : S) = u := hu _ (fun h => hy1 (congrArg Subtype.val h))
  have h2 : (⟨z, hz⟩ : S) = u := hu _ (fun h => hz1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem l13_natCard_eq_two_mul {K : Type} [Group K] {M C : Subgroup K} (hCM : C ≤ M) {b : K}
    (hbM : b ∈ M) (hbC : b ∉ C) (hdich : ∀ g ∈ M, g ∈ C ∨ b⁻¹ * g ∈ C) :
    Nat.card M = 2 * Nat.card C := by
  have key : ∀ y : K, b⁻¹ * y ∈ C → y ∈ C → False := fun y hy1 hy2 => by
    have h := C.mul_mem hy1 (C.inv_mem hy2)
    rw [mul_inv_cancel_right] at h
    exact hbC (inv_mem_iff.mp h)
  have hidx : (C.subgroupOf M).index = 2 := by
    rw [Subgroup.index_eq_two_iff']
    refine ⟨⟨b⁻¹, M.inv_mem hbM⟩, fun x => ?_⟩
    have hxM : (x : K) ∈ M := x.2
    show Xor (b⁻¹ * (x : K) ∈ C) ((x : K) ∈ C)
    rcases hdich x hxM with h | h
    · exact Or.inr ⟨h, fun h' => key x h' h⟩
    · exact Or.inl ⟨h, fun h' => key x h h'⟩
  have h1 := Subgroup.card_mul_index (H := C.subgroupOf M)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv] at h1
  omega

theorem lemma13_holds (hN : NaturalModuleStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) : Lemma13Statement := by
  intro G _ _ M V Q P H hH hZ hcP v hvV hvW
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨n, Φ, ψ, -, hequiv, ⟨a, T, ha, hT, hTV⟩, hpt⟩ := hN G M V Q P H hH hZ
  have hNat : NatCfg V H hVH Φ ψ := ⟨hequiv, hpt⟩
  have hPP : ⁅P, P⁆ = V ⊓ wOf V H := (h11b G M V Q P H hH hZ hcP).1
  obtain ⟨aG, haGdef⟩ : ∃ x : G, x = ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := ⟨_, rfl⟩
  have haG_V : aG ∈ V := by rw [haGdef]; exact hpt a T ha hT hTV
  have haG_W : aG ∈ wOf V H := by rw [haGdef]; exact (Additive.toMul (ψ a)).2
  have haG1 : aG ≠ 1 := by
    intro h
    apply ha
    apply ψ.injective
    rw [map_zero]
    apply Additive.toMul.injective
    rw [haGdef] at h
    exact Subtype.ext h
  have hWcomm : ∀ x ∈ wOf V H, ∀ y ∈ wOf V H, x * y = y * x :=
    fun x hx y hy => elemAbelian_mul_comm hc.wOf_isElemAbelian hx hy
  have hWsq : ∀ x ∈ wOf V H, x * x = 1 :=
    fun x hx => elemAbelian_mul_self hc.wOf_isElemAbelian hx
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => elemAbelian_mul_comm hc.elemAb hx hy
  have haG2 : aG * aG = 1 := hWsq aG haG_W
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hbarcard : Nat.card ↥(barOf V H V) = 2 := hH.q_two
  have hv1 : v ≠ 1 := fun h => hvW (by rw [h]; exact (wOf V H).one_mem)
  have hVall : ∀ x ∈ V, x ∈ wOf V H → x = 1 ∨ x = aG := by
    intro x hxV hxW
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (l13_eq_of_natCard_two hVWcard (Subgroup.mem_inf.mpr ⟨hxV, hxW⟩)
        (Subgroup.mem_inf.mpr ⟨haG_V, haG_W⟩) h1 haG1)
  have hVcos : ∀ x ∈ V, x ∉ wOf V H → x = v ∨ x = v * aG := by
    intro x hxV hxW
    have hxH : x ∈ H := hVH hxV
    have hvH : v ∈ H := hVH hvV
    have hxS : piBar V H ⟨x, hxH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hxV, rfl⟩
    have hvS : piBar V H ⟨v, hvH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨⟨v, hvH⟩, hvV, rfl⟩
    have hS := l13_eq_of_natCard_two hbarcard hxS hvS
      (fun h => hxW ((piBar_eq_one_iff ⟨x, hxH⟩).mp h))
      (fun h => hvW ((piBar_eq_one_iff ⟨v, hvH⟩).mp h))
    have hq : (⟨x, hxH⟩ : ↥H)⁻¹ * ⟨v, hvH⟩ ∈ (wOf V H).subgroupOf H := QuotientGroup.eq.mp hS
    have hxv : x⁻¹ * v ∈ wOf V H := Subgroup.mem_subgroupOf.mp hq
    have hxvV : x⁻¹ * v ∈ V := V.mul_mem (V.inv_mem hxV) hvV
    rcases hVall (x⁻¹ * v) hxvV hxv with h1 | h1
    · exact Or.inl (inv_mul_eq_one.mp h1)
    · refine Or.inr ?_
      have hvx : v = x * aG := inv_mul_eq_iff_eq_mul.mp h1
      calc x = x * (aG * aG) := by rw [haG2, mul_one]
        _ = x * aG * aG := by rw [mul_assoc]
        _ = v * aG := by rw [← hvx]
  have hfix : ∀ g ∈ M, g * aG * g⁻¹ = aG := by
    intro g hgM
    have hmap : Subgroup.map (MulAut.conj g).toMonoidHom P ≤ P := by
      rintro _ ⟨p, hp, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hgM) p).mp hp
    have hle : Subgroup.map (MulAut.conj g).toMonoidHom ⁅P, P⁆ ≤ ⁅P, P⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    have haGc : aG ∈ ⁅P, P⁆ := by
      rw [hPP]
      exact Subgroup.mem_inf.mpr ⟨haG_V, haG_W⟩
    have hmem : g * aG * g⁻¹ ∈ ⁅P, P⁆ := hle (Subgroup.mem_map_of_mem _ haGc)
    rw [hPP] at hmem
    have hne : g * aG * g⁻¹ ≠ 1 := by
      intro h
      apply haG1
      calc aG = g⁻¹ * (g * aG * g⁻¹) * g := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    exact l13_eq_of_natCard_two hVWcard hmem (Subgroup.mem_inf.mpr ⟨haG_V, haG_W⟩) hne haG1
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Fin n ⊕ Fin n → GaloisField 2 1, CaseM.spForm a b₀ = 1 := by
    obtain ⟨y, hy⟩ := CFSG.Timmesfeld.Transvection.ModelRank.exists_spForm_ne_zero ha
    exact ⟨(CaseM.spForm a y)⁻¹ • y, by
      rw [CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', inv_mul_cancel₀ hy]⟩
  obtain ⟨bG, hbG⟩ : ∃ x : G, x = ((Additive.toMul (ψ b₀) : ↥(wOf V H)) : G) := ⟨_, rfl⟩
  have hbG_W : bG ∈ wOf V H := by rw [hbG]; exact (Additive.toMul (ψ b₀)).2
  have hcv : ⁅v, bG⁆ = aG := by
    have h := (h11c G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV b₀ hb₀).1 v hvV hvW
    rw [hbG, haGdef]
    exact h
  have hbM : bG ∈ M := hc.mem_M_of_commute haG_V haG1 (hWcomm bG hbG_W aG haG_W)
  have h1 : v * bG * v⁻¹ = aG * bG := by
    have h := hcv
    rw [commutatorElement_def] at h
    rw [← h, inv_mul_cancel_right]
  have h2 : v * bG = aG * bG * v := by
    rw [← h1, inv_mul_cancel_right]
  have h3 : bG * v = aG * v * bG := by
    calc bG * v = aG * aG * (bG * v) := by rw [haG2, one_mul]
      _ = aG * (aG * bG * v) := by simp only [mul_assoc]
      _ = aG * (v * bG) := by rw [h2]
      _ = aG * v * bG := by rw [mul_assoc]
  have hbconj : bG⁻¹ * (aG * v) = v * bG⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h3, mul_inv_cancel_right]
  have hbC : bG ∉ Subgroup.centralizer ({v} : Set G) := by
    intro hb
    have hbv : v * bG = bG * v := Subgroup.mem_centralizer_iff.mp hb v (Set.mem_singleton v)
    have h4 : aG * v * bG = v * bG := by rw [← h3, hbv]
    have h5 : aG * v = 1 * v := by
      rw [one_mul]
      exact mul_right_cancel h4
    exact haG1 (mul_right_cancel h5)
  have hdich : ∀ g ∈ M, g ∈ Subgroup.centralizer ({v} : Set G) ∨
      bG⁻¹ * g ∈ Subgroup.centralizer ({v} : Set G) := by
    intro g hgM
    have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hgM
    have hconjV : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgN v).mp hvV
    have hconjW : g * v * g⁻¹ ∉ wOf V H := by
      intro hW
      rcases hVall (g * v * g⁻¹) hconjV hW with h | h
      · apply hv1
        have h2' : g * v = g * 1 := by
          rw [mul_one]
          exact mul_inv_eq_one.mp h
        exact mul_left_cancel h2'
      · apply hvW
        have h2' : g * v * g⁻¹ = g * aG * g⁻¹ := by
          rw [h, hfix g hgM]
        have h3' : v = aG := mul_left_cancel (mul_right_cancel h2')
        rw [h3']
        exact haG_W
    rcases hVcos (g * v * g⁻¹) hconjV hconjW with h | h
    · left
      have hgv : g * v = v * g := mul_inv_eq_iff_eq_mul.mp h
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        exact hgv.symm
    · right
      have hgv : g * v = v * aG * g := mul_inv_eq_iff_eq_mul.mp h
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      have hbv' : bG⁻¹ * (v * aG) = v * bG⁻¹ := by
        rw [hVcomm v hvV aG haG_V]
        exact hbconj
      symm
      calc bG⁻¹ * g * v = bG⁻¹ * (g * v) := mul_assoc _ _ _
        _ = bG⁻¹ * (v * aG * g) := by rw [hgv]
        _ = bG⁻¹ * (v * aG) * g := (mul_assoc _ _ _).symm
        _ = v * bG⁻¹ * g := by rw [hbv']
        _ = v * (bG⁻¹ * g) := mul_assoc _ _ _
  have hC1 : Subgroup.centralizer ({v} : Set G) = M ⊓ Subgroup.centralizer (V : Set G) := by
    ext g
    constructor
    · intro hg
      have hgv : g * v = v * g :=
        (Subgroup.mem_centralizer_iff.mp hg v (Set.mem_singleton v)).symm
      have hgM : g ∈ M := hc.mem_M_of_commute hvV hv1 hgv
      have hgfix : g * aG = aG * g := mul_inv_eq_iff_eq_mul.mp (hfix g hgM)
      refine Subgroup.mem_inf.mpr ⟨hgM, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      by_cases hxW : x ∈ wOf V H
      · rcases hVall x hx hxW with h | h
        · rw [h, one_mul, mul_one]
        · rw [h]
          exact hgfix.symm
      · rcases hVcos x hx hxW with h | h
        · rw [h]
          exact hgv.symm
        · rw [h]
          calc v * aG * g = v * (aG * g) := mul_assoc _ _ _
            _ = v * (g * aG) := by rw [← hgfix]
            _ = v * g * aG := (mul_assoc _ _ _).symm
            _ = g * v * aG := by rw [← hgv]
            _ = g * (v * aG) := mul_assoc _ _ _
    · intro hg
      obtain ⟨-, hgV⟩ := Subgroup.mem_inf.mp hg
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_centralizer_iff.mp hgV v hvV
  have hCM : Subgroup.centralizer ({v} : Set G) ≤ M := by
    rw [hC1]
    exact inf_le_left
  refine ⟨hC1, ?_⟩
  rw [← hC1]
  exact l13_natCard_eq_two_mul hCM hbM hbC hdich

end CFSG.RankThree.GF2n.Tim79a
