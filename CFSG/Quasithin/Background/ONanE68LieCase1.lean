module

public import CFSG.Quasithin.Background.ONanE68LieBorel
public import CFSG.Quasithin.Background.ONanE68LieCyc
public import CFSG.Quasithin.Background.ONanE68Small

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Omega

variable {S : Type} [Group S]

theorem omegaCenter_le {P : Subgroup S} : omegaCenter P ≤ P := fun _ hz => (mem_omegaCenter.1 hz).1

theorem conj_mem_omegaCenter {P : Subgroup S} {b : S} (hb : b ∈ Subgroup.normalizer (P : Set S))
    {w : S} (hw : w ∈ omegaCenter P) : b * w * b⁻¹ ∈ omegaCenter P := by
  obtain ⟨hwP, hwc, hw2⟩ := mem_omegaCenter.1 hw
  have hb' := Subgroup.mem_normalizer_iff.1 hb
  have hbinv := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb)
  refine mem_omegaCenter.2 ⟨(hb' w).1 hwP, fun y hy => ?_, ?_⟩
  · have hy' : b⁻¹ * y * b ∈ P := by
      have := (hbinv y).1 hy
      simpa using this
    have := hwc _ hy'
    calc b * w * b⁻¹ * y = b * (w * (b⁻¹ * y * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * y * b) * w) * b⁻¹ := by rw [this]
      _ = y * (b * w * b⁻¹) := by group
  · calc b * w * b⁻¹ * (b * w * b⁻¹) = b * (w * w) * b⁻¹ := by group
      _ = 1 := by rw [hw2]; group

theorem singerHyp_omegaCenter {P : Subgroup S}
    (hquot : ∀ a ∈ Subgroup.normalizer (P : Set S), ∀ b ∈ Subgroup.normalizer (P : Set S),
      a * b * a⁻¹ * b⁻¹ ∈ P) {x : S} (hx : x ∈ Subgroup.normalizer (P : Set S))
    (htrans : ∀ z ∈ omegaCenter P, z ≠ 1 → ∀ w ∈ omegaCenter P, w ≠ 1 →
      ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w) :
    SingerHyp (Subgroup.normalizer (P : Set S)) (omegaCenter P) x where
  mem := hx
  inv := fun _ hb _ hw => conj_mem_omegaCenter hb hw
  comm := fun a ha b hb _ hw => ((mem_omegaCenter.1 hw).2.1 _ (hquot a ha b hb)).symm
  trans := htrans

variable [Finite S]

theorem normalizer_le_normalizer_omegaCenter (P : Subgroup S) :
    Subgroup.normalizer (P : Set S) ≤ Subgroup.normalizer (omegaCenter P : Set S) :=
  fun _ hb => mem_normalizer_of_conj_le fun _ hy => conj_mem_omegaCenter hb hy

end Omega

section Case

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem case1_of_borel (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (hBX : borOf T V L ≤ M) (hXB : L ⊓ M ≤ borOf T V L)
    {n : ℕ} (hn : 2 ≤ n)
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L)
    (hcard : Nat.card (omegaCenter (sylowBar T V L)) = 2 ^ n)
    (hsing : ∃ x ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ z ∈ omegaCenter (sylowBar T V L), z ≠ 1 → ∀ w ∈ omegaCenter (sylowBar T V L), w ≠ 1 →
        ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w)
    (hmodel : (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) ∨
      (1 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 n)) :
    E68Case1 hV T M U L := by
  classical
  have hZ := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hXeq : L ⊓ M = borOf T V L := le_antisymm hXB (le_inf borOf_le_left hBX)
  obtain ⟨-, hres, hXN⟩ := sandwich h hU hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  obtain ⟨θ, hθ, hθZ⟩ := exists_theta hInn hmod h hU hL
  set P := sylowBar T V L with hP
  obtain ⟨x, hxN, htrans⟩ := hsing
  have hS := singerHyp_omegaCenter hquot hxN htrans
  have hBW := normalizer_le_normalizer_omegaCenter P
  have hWle : θ.range ≤ omegaCenter P := by
    rintro _ ⟨a, rfl⟩
    exact hθZ a
  obtain ⟨x₀, hx₀B, hx₀⟩ := exists_mem_borOf_of_mem_normalizer hZ hxN
  have hx₀X : x₀ ∈ L ⊓ M := by rw [hXeq]; exact hx₀B
  have hinvW : ∀ w ∈ θ.range, x * w * x⁻¹ ∈ θ.range := by
    intro w hw
    have := theta_range_invariant hVN θ hθ hZ0 hx₀X.1 (hXN hx₀X) w hw
    rwa [hx₀] at this
  have hne : θ.range ≠ ⊥ :=
    theta_range_ne_bot h.isPGroup_V hVN θ hθ hZ0 hperf (mQuot_ne_zero_of_not_le h hLM)
  have hWeq : θ.range = omegaCenter P := hS.eq_of_invariant hWle hinvW hne
  have hk : Nat.card θ.range = 2 ^ n := by rw [hWeq]; exact hcard
  have hm : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n :=
    mQuot_eq_of_card_range h.isPGroup_V hVN θ hθ hZ0 hperf hk
  have hodd := odd_card_autI hV hXN (hres.trans inf_le_right)
  have hW0 : omegaCenter P ≠ ⊥ := hWeq ▸ hne
  have hXB' : ∀ y ∈ L ⊓ M, ∃ b ∈ Subgroup.normalizer (P : Set (Bar.Qbar L)),
      ∀ w ∈ omegaCenter P, piG L y * w * (piG L y)⁻¹ = b * w * b⁻¹ := fun y hy =>
    ⟨piG L y, piG_mem_normalizer_of_mem_borOf hZ (hXeq ▸ hy), fun _ _ => rfl⟩
  obtain ⟨hcyc, hcard'⟩ := autI_cyclic_of_singerHyp hV hXN inf_le_left hodd hVN θ hθ hZ0 hperf
    hS hBW hWeq hW0 hx₀X hx₀ hXB'
  rw [hcard] at hcard'
  refine ⟨n, hmodel, hZ2, hXeq, hcyc, hcard', hm, hm ▸ E3.mQuot_mono
    (le_inf_centralizer_component hU.1 hL), fun hn1 => ?_⟩
  have h3 : 3 ≤ Nat.card (omegaCenter P) := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hfix : ∀ v ∈ V, (∀ y ∈ L ⊓ M, y * v = v * y) → v ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    intro v hv hfv
    refine ⟨hv, ?_⟩
    have h1 := theta_comm_of_comm hVN θ hθ ⟨x₀, hx₀X.1⟩ ⟨v, hv⟩ (hfv x₀ hx₀X)
    have hxv : x * θ ⟨v, hv⟩ * x⁻¹ = θ ⟨v, hv⟩ := by
      rw [← hx₀, piG_of_mem hx₀X.1, h1]
      group
    have hmem : θ ⟨v, hv⟩ ∈ omegaCenter P := hWle ⟨⟨v, hv⟩, rfl⟩
    exact (theta_eq_one_iff hVN θ hθ hZ0 hperf ⟨v, hv⟩).1 (hS.eq_one_of_fixed h3 hmem hxv)
  have hXU : L ⊓ M ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := inf_le_left.trans (le_centralizer_inf_centralizer V L)
  obtain ⟨hd1, hd2⟩ := decomp_of_fixed hV inf_le_left hXN hXU hodd hfix
  refine ⟨by rw [inf_comm]; exact hd1, by rw [sup_comm]; exact hd2, ?_⟩
  exact mQuot_bot_eq_of_decomp h.isPGroup_V inf_le_left (le_sup_right.trans hd2.le)
    (fun a ha b hb => B2F.isElemAbelian_comm hV ha hb) hd1 hd2 hm

end Case

end E68Proof

end E6

end CFSG.Quasithin
