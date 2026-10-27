module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelClassGroups
public import CFSG.RankThree.GF2n.Stroth80.FieldModelFunctional

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section Main

variable (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q)

include H hgV hgQ

theorem opposite_mem_class_of_three_le {n : ℕ} (hn : 3 ≤ n)
    (D : MulData V (conjSubgroup g V) Q (GaloisField 2 n)) {τ : G} {a : GaloisField 2 n}
    (hτM : τ ∈ M) (hτH : τ ∈ Q ⊔ conjSubgroup g Q)
    (hτU : τ ∈ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G))
    (hτo : orderOf τ = 2 ^ n - 1) (hao : orderOf a = 2 ^ n - 1)
    (hγ : ∀ v ∈ V, D.γ (τ * v * τ⁻¹) = a * D.γ v)
    (hψ : ∀ u ∈ conjSubgroup g V, D.ψ (τ * u * τ⁻¹) = a⁻¹ * D.ψ u)
    {g₂ : G} (hg₂V : conjSubgroup g₂ V ≠ V) (hg₂Q : conjSubgroup g₂ V ≤ Q) :
    conjSubgroup g₂ V ∈ classOf V Q D.γ := by
  classical
  by_contra hnot
  have hn0 : n ≠ 0 := by omega
  have hh := H.toHyp218 hgV hgQ
  have hτV : τ ∈ Subgroup.normalizer (V : Set G) := hh.M_le_normalizer hτM
  have hτQ : τ ∈ Subgroup.normalizer (Q : Set G) := hh.M_le_normalizer_Q hτM
  have hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q := fun y hy => (mem_iff_conj_inv_of_normalizer hτQ y).mp hy
  have hτ' : ∀ y ∈ Q, τ * y * τ⁻¹ ∈ Q := fun y hy => (mem_iff_conj_of_normalizer hτQ y).mp hy
  have hKcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hpow3 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hao
    omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    omega
  have haN : a ^ (2 ^ n - 1) = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hτN : τ ^ (2 ^ n - 1) = 1 := by rw [← hτo]; exact pow_orderOf_eq_one τ
  have hN0 : 0 < 2 ^ n - 1 := by omega
  obtain ⟨n₂, hn₂, ⟨D₂⟩⟩ := H.exists_mulData hg₂V hg₂Q
  have hnn : n = n₂ :=
    Nat.pow_right_injective (le_refl 2) ((D.natCard_V.trans hKcard).symm.trans hn₂)
  subst hnn
  have hU₂C₂ : conjSubgroup g₂ V ∈ classOf V Q D₂.γ := mem_classOf_self D₂ ⟨g₂, rfl⟩ hg₂Q hg₂V
  have hne : classOf V Q D₂.γ ≠ classOf V Q D.γ := fun h => hnot (h ▸ hU₂C₂)
  obtain ⟨d, hd0, hdN, hdC, hdmin⟩ := exists_period τ hN0 hτN (classOf V Q D₂.γ)
  by_cases hd1 : d = 1
  · subst hd1
    have hstab : transC τ (classOf V Q D₂.γ) = classOf V Q D₂.γ := by simpa using hdC
    have hcompat := gammaCompat_of_stable (by omega : 2 ≤ n) D D₂ hτV hτQ
      (by rw [hKcard, hao]) hγ ⟨g₂, rfl⟩ hg₂Q hg₂V hstab
    exact hnot (by rw [← classOf_congr hcompat]; exact hU₂C₂)
  have hd3 : 3 ≤ d := by
    have h2 : d ≠ 2 := by
      rintro rfl
      have h4 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      have h5 : 0 < 2 ^ n := by positivity
      omega
    omega
  obtain ⟨e, he⟩ := id hdN
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, mul_zero] at he; omega
    · exact h
  have hde : d * e = Nat.card (GaloisField 2 n) - 1 := by rw [hKcard]; exact he.symm
  have C := H.modelCtx D
  obtain ⟨n', -, hn', ⟨N'⟩⟩ := exists_natData H hgV hgQ
  have hnn' : n = n' :=
    Nat.pow_right_injective (le_refl 2) ((D.natCard_V.trans hKcard).symm.trans hn')
  subst hnn'
  have hVbot : V ≠ ⊥ := by
    intro h
    have h4 := H.q4
    rw [h] at h4
    simp at h4
  obtain ⟨⟨v₀, hv₀⟩, hv₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVbot
  have hv₀1 : v₀ ≠ 1 := fun h => hv₀1' (Subtype.ext h)
  obtain ⟨hτ10, htrans⟩ := natData_transfer N' D hτH hτV hγ hv₀ hv₀1
  obtain ⟨p, hpmon, hpdeg, hpa⟩ := exists_nat_poly hn0 a
  have hpb := htrans p hpa
  set Q₀ := classGroup V Q D₂.γ with hQ₀
  set Q₁ := classGroup V Q D.γ with hQ₁
  set Y : Subgroup G := Q ⊓ Subgroup.centralizer (Q₁ : Set G) with hY
  set R : Subgroup G := Q ⊓ Subgroup.centralizer (Q₀ : Set G) with hR
  have hQ₀Q : Q₀ ≤ Q := classGroup_le H.V_le_Q
  have hQeq : Q = Q₀ ⊔ R := Hyp79.eq_classGroup_sup_centralizer H D₂ ⟨g₂, rfl⟩ hg₂Q hg₂V
  have hUQ₁ : conjSubgroup g V ≤ Q₁ := le_classGroup_of_mem (mem_classOf_self D ⟨g, rfl⟩ hgQ hgV)
  have hcomm : ∀ x ∈ Q₀, ∀ z ∈ Q₁, x * z = z * x := commute_classGroup H D hne
  have hQ₁τ : ∀ z ∈ Q₁, τ⁻¹ * z * τ ∈ Q₁ := by
    intro z hz
    have h := conj_mem_classGroup (inv_mem hτV) (inv_mem hτQ) (inv_ne_zero ha0)
      (fun v hv => by rw [inv_inv]; exact gamma_conj_inv hτV ha0 hγ hv) hz
    simpa using h
  have hYτ : ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y := by
    intro y hy
    refine ⟨hτ' y hy.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hy.2 (τ⁻¹ * z * τ) (hQ₁τ z hz)
    calc z * (τ * y * τ⁻¹) = τ * ((τ⁻¹ * z * τ) * y) * τ⁻¹ := by group
      _ = τ * (y * (τ⁻¹ * z * τ)) * τ⁻¹ := by rw [h1]
      _ = τ * y * τ⁻¹ * z := by group
  have hVY : V ≤ Y := fun v hv =>
    ⟨H.V_le_Q hv, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (H.V_central hv (classGroup_le H.V_le_Q hz)).symm⟩
  have hYU : ∀ u ∈ conjSubgroup g V, u ∈ Y → u = 1 := by
    intro u hu huY
    have huV : u ∈ V := classGroup_central_le H D ⟨g, rfl⟩ hgQ hgV (hUQ₁ hu)
      (fun z hz => Subgroup.mem_centralizer_iff.mp huY.2 z hz)
    have hbot : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgV
    have : u ∈ V ⊓ conjSubgroup g V := ⟨huV, hu⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hTN : Top Q a τ hτ ^ (d * e) = 1 := by
    rw [show d * e = 2 ^ n - 1 from he.symm]
    exact Top_pow_eq_one hτ hτN haN
  have hpowV : ∀ i : ℕ, τ ^ i ∈ Subgroup.normalizer (V : Set G) :=
    fun i => (Subgroup.normalizer (V : Set G)).pow_mem hτV i
  have hpowQ : ∀ i : ℕ, τ ^ i ∈ Subgroup.normalizer (Q : Set G) :=
    fun i => (Subgroup.normalizer (Q : Set G)).pow_mem hτQ i
  have hconjQ₀ : ∀ i : ℕ, ∀ x ∈ Q₀, τ ^ i * x * (τ ^ i)⁻¹ ∈
      classGroup V Q (fun v => D₂.γ ((τ ^ i)⁻¹ * v * τ ^ i)) :=
    fun i x hx => conj_mem_classGroup' (hpowV i) (hpowQ i) hx
  have hcl : ∀ i : ℕ, classOf V Q (fun v => D₂.γ ((τ ^ i)⁻¹ * v * τ ^ i)) =
      transC (τ ^ i) (classOf V Q D₂.γ) :=
    fun i => (transC_classOf (hpowV i) (hpowQ i) D₂.γ).symm
  have hperiodQ₀ : ∀ x ∈ Q₀, τ ^ d * x * (τ ^ d)⁻¹ ∈ Q₀ := by
    intro x hx
    have h1 := hconjQ₀ d x hx
    rwa [classGroup_congr (by rw [hcl d, hdC] :
      classOf V Q (fun v => D₂.γ ((τ ^ d)⁻¹ * v * τ ^ d)) = classOf V Q D₂.γ)] at h1
  have horbitR : ∀ i, 1 ≤ i → i < d → ∀ x ∈ Q₀, τ ^ i * x * (τ ^ i)⁻¹ ∈ R := by
    intro i hi1 hid x hx
    have h1 := hconjQ₀ i x hx
    have hne_i : classOf V Q (fun v => D₂.γ ((τ ^ i)⁻¹ * v * τ ^ i)) ≠ classOf V Q D₂.γ := by
      rw [hcl i]; exact hdmin i hi1 hid
    exact ⟨classGroup_le H.V_le_Q h1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (commute_classGroup H D₂ hne_i _ h1 y hy).symm⟩
  have hW : Wsp D.γ Q (Q₀ : Set G) ≠ ⊥ := by
    have hU₂ne : conjSubgroup g₂ V ≠ ⊥ := by
      intro h
      have h1 := card_conjSubgroup g₂ V
      rw [h] at h1
      have h4 := H.q4
      simp at h1
      omega
    obtain ⟨⟨u₂, hu₂⟩, hu₂1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU₂ne
    have hu₂1' : u₂ ≠ 1 := fun h => hu₂1 (Subtype.ext h)
    have hu₂V : u₂ ∉ V := by
      intro hV'
      have hbot : V ⊓ conjSubgroup g₂ V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hg₂V
      have : u₂ ∈ V ⊓ conjSubgroup g₂ V := ⟨hV', hu₂⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hu₂1' this
    exact Wsp_ne_bot C (le_classGroup_of_mem hU₂C₂ hu₂) (hg₂Q hu₂) hu₂V
  have hTW : ∀ w ∈ Wsp D.γ Q (Q₀ : Set G), (Top Q a τ hτ ^ d) w ∈ Wsp D.γ Q (Q₀ : Set G) := by
    intro w hw
    have hle : Wsp D.γ Q (Q₀ : Set G) ≤
        Submodule.comap (Top Q a τ hτ ^ d) (Wsp D.γ Q (Q₀ : Set G)) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨x, hx, rfl⟩
        show (Top Q a τ hτ ^ d) (jf D.γ Q x) ∈ Wsp D.γ Q (Q₀ : Set G)
        rw [Top_pow_jf C hτ hτ' hγ (hQ₀Q hx) d]
        exact Submodule.subset_span ⟨_, hperiodQ₀ x hx, rfl⟩)
    exact hle hw
  have hTU : ∀ i, 1 ≤ i → i < d → ∀ w ∈ Wsp D.γ Q (Q₀ : Set G),
      (Top Q a τ hτ ^ i) w ∈ Wsp D.γ Q (R : Set G) := by
    intro i hi1 hid w hw
    have hle : Wsp D.γ Q (Q₀ : Set G) ≤
        Submodule.comap (Top Q a τ hτ ^ i) (Wsp D.γ Q (R : Set G)) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨x, hx, rfl⟩
        show (Top Q a τ hτ ^ i) (jf D.γ Q x) ∈ Wsp D.γ Q (R : Set G)
        rw [Top_pow_jf C hτ hτ' hγ (hQ₀Q hx) i]
        exact Submodule.subset_span ⟨_, horbitR i hi1 hid x hx, rfl⟩)
    exact hle hw
  have hWU : Disjoint (Wsp D.γ Q (Q₀ : Set G)) (Wsp D.γ Q (R : Set G)) :=
    Wsp_disjoint C hQ₀Q hQeq
  have hgen : ∀ x ∈ Q₀, Polynomial.aeval (Top Q a τ hτ)
      ((X - 1) * p.map (Nat.castRingHom (GaloisField 2 n))) (jf D.γ Q x) = 0 := by
    intro x hx
    have hxQ : x ∈ Q := hQ₀Q hx
    have hxP : x ∈ Q ⊓ Subgroup.centralizer (Wg V g : Set G) := by
      refine ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hle : Wg V g ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun v hv => ?_) (fun u hu => ?_)
        · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
          rw [Set.mem_singleton_iff.mp hz]
          exact (H.V_central hv hxQ).symm
        · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
          rw [Set.mem_singleton_iff.mp hz]
          exact hcomm x hx u (hUQ₁ hu)
      exact (Subgroup.mem_centralizer_iff.mp (hle hw) x rfl).symm
    have hℓL := gt1_concrete H hgV hgQ N' hτH hτ10 p hpb hxP
    have hxY : x ∈ Y :=
      ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun z hz => (hcomm x hx z hz).symm⟩
    have hxs_Y : ∀ i : ℕ, τ ^ i * x * (τ ^ i)⁻¹ ∈ Y := by
      intro i
      induction i with
      | zero => simpa using hxY
      | succ i ih =>
        have := hYτ _ ih
        rwa [show τ * (τ ^ i * x * (τ ^ i)⁻¹) * τ⁻¹ = τ ^ (i + 1) * x * (τ ^ (i + 1))⁻¹ by
          rw [pow_succ']; group] at this
    have hℓY : (((List.range (p.natDegree + 1)).map fun i =>
        (τ ^ i * x * (τ ^ i)⁻¹) ^ p.coeff i).prod) ∈ Y := by
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact Subgroup.pow_mem _ (hxs_Y i) _
    have hcomm' := gt2 H hgV hgQ D hτH hτU ha1 hψ Y hYτ hVY hYU hℓY hℓL
    rw [map_mul, map_sub, aeval_X, map_one, Module.End.mul_apply,
      aeval_Top_jf C hτ hτ' hγ p hxQ]
    exact Top_sub_one_jf C hτ hγ hℓL.1 hcomm'
  have hf : ∀ w ∈ Wsp D.γ Q (Q₀ : Set G), Polynomial.aeval (Top Q a τ hτ)
      ((X - 1) * p.map (Nat.castRingHom (GaloisField 2 n))) w = 0 := by
    intro w hw
    have hle : Wsp D.γ Q (Q₀ : Set G) ≤ LinearMap.ker (Polynomial.aeval (Top Q a τ hτ)
        ((X - 1) * p.map (Nat.castRingHom (GaloisField 2 n)))) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨x, hx, rfl⟩
        exact LinearMap.mem_ker.mpr (hgen x hx))
    exact LinearMap.mem_ker.mp (hle hw)
  obtain ⟨μ, hμ0, hμ⟩ := eigen_coset (Top Q a τ hτ) hd0 he0 hde hTN (Wsp D.γ Q (Q₀ : Set G))
    (Wsp D.γ Q (R : Set G)) hW hTW hTU hWU ((X - 1) * p.map (Nat.castRingHom (GaloisField 2 n)))
    hf
  refine no_coset_of_poly hn hKcard hao p hpmon hpdeg hpa hd3 hdN hμ0 (fun ζ hζ => ?_)
  have := hμ ζ hζ
  rw [eval_mul, eval_sub, eval_X, eval_one, eval_map] at this
  exact this

end Main

end CFSG.RankThree.GF2n.Stroth80.FieldModel
