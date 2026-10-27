module

public import CFSG.Quasithin.Background.E6TwentyThreeF
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourRank1
public import CFSG.Quasithin.Background.E6TwentyThreeD
public import CFSG.Quasithin.Background.E6TwentyThreeE
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.E6.A3Push

open CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sl2_model_one_lt {B : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 5) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧ 1 < m ∧
      ∃ α : ↥B →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥B := by
  rcases h with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    exact ⟨F, hF, hFin, n, hcard, hn, α, hαs, hαk⟩
  · obtain ⟨α, hαs, hαk, -⟩ := h5
    let K := GaloisField 2 2
    have hK : Nat.card K = 4 := by
      have := GaloisField.card 2 2 two_ne_zero
      rw [this]
      norm_num
    obtain ⟨e⟩ := Setup.Family.specialLinear_two_equiv_alternating_five K hK
    let _ : Fintype K := Fintype.ofFinite K
    refine ⟨K, inferInstance, inferInstance, 2, ?_, by norm_num,
      e.symm.toMonoidHom.comp α, e.symm.surjective.comp hαs, ?_⟩
    · rw [← Nat.card_eq_fintype_card, hK]
      norm_num
    · rw [MonoidHom.ker_comp_of_injective α e.symm.toMonoidHom e.symm.injective, hαk]

omit [Finite G] in
theorem sixteen_mul_card_blockZ_le {B : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 5) :
    16 * Nat.card (blockZ B) ≤ Nat.card (blockU B) := by
  classical
  have hZU : blockZ B ≤ blockU B := inf_le_left
  have hcardZ : Nat.card ((blockZ B).subgroupOf (blockU B)) = Nat.card (blockZ B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  rcases h with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨F, hF, hFin, hcard, -, -, -, β, hβs, hβk, -⟩ := hlin
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk,
      hcardZ] at h1
    have h2 : Nat.card (Multiplicative (Fin 2 → F)) = (2 ^ n) ^ 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
        Fintype.card_fin, hcard]
    rw [h1, h2]
    have : 16 ≤ (2 ^ n) ^ 2 := by
      calc 16 = (2 ^ 2) ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hn) 2
    exact Nat.mul_le_mul_right _ this
  · obtain ⟨-, -, -, β, hβs, hβk, -⟩ := h5
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk,
      hcardZ] at h1
    have h2 : Nat.card (Multiplicative (evenWeight 5)) = 16 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      have h : Nat.card (evenWeight 5) = Nat.card {x : Fin 5 → ZMod 2 // ∑ i, x i = 0} := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun x => by simp [evenWeight, AddMonoidHom.mem_ker])
      rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
      decide
    rw [h1, h2]

theorem eq_of_ne_one_of_fpf {E W : Subgroup G} {x : G} (hE4 : Nat.card E = 4)
    (hWE : W ≤ E) (hx3 : x ^ 3 = 1) (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hfpf : ∀ u ∈ E, u ≠ 1 → x * u * x⁻¹ ≠ u) {w : G} (hw : w ∈ W) (hw1 : w ≠ 1) : W = E := by
  classical
  have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
  set w₁ := x * w * x⁻¹ with hw₁
  set w₂ := x * w₁ * x⁻¹ with hw₂
  have hw₁W : w₁ ∈ W := hxW w hw
  have hw₂W : w₂ ∈ W := hxW w₁ hw₁W
  have hne1 : ∀ y : G, y ≠ 1 → x * y * x⁻¹ ≠ 1 := fun y hy h => hy (by
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hw₁1 : w₁ ≠ 1 := hne1 w hw1
  have hw₂1 : w₂ ≠ 1 := hne1 w₁ hw₁1
  have h01 : w₁ ≠ w := fun h => hfpf w (hWE hw) hw1 h
  have h12 : w₂ ≠ w₁ := fun h => hfpf w₁ (hWE hw₁W) hw₁1 h
  have h02 : w₂ ≠ w := by
    intro h
    apply h01
    calc w₁ = x * w₂ * x⁻¹ := by rw [h]
      _ = (x * x * x) * w * (x * x * x)⁻¹ := by rw [hw₂, hw₁]; group
      _ = w := by rw [hx3']; group
  have hsub : (({1, w, w₁, w₂} : Finset G) : Set G) ⊆ (W : Set G) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact hw
    · exact hw₁W
    · exact hw₂W
  have hcard : ({1, w, w₁, w₂} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h12.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01.symm, h02.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hw1, Ne.symm hw₁1, Ne.symm hw₂1⟩
  have h4 : 4 ≤ Nat.card W := by
    have h1 : (({1, w, w₁, w₂} : Finset G) : Set G).ncard = 4 := by
      rw [Set.ncard_coe_finset, hcard]
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite (W : Set G))
    rw [h1] at h2
    rw [← Nat.card_coe_set_eq] at h2
    exact h2
  exact Subgroup.eq_of_le_of_card_ge hWE (by omega)

theorem false_of_moved_sl2_block {K Q B E : Subgroup G} {a x : G}
    (hQ : IsSylowTwoOf Q K) (haZ : ∀ q ∈ Q, a * q = q * a) (hB : IsBlock2 K B)
    (hBt : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 5)
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) (hx3 : x ^ 3 = 1)
    (hxC : ¬ ∀ b ∈ B, x * b * x⁻¹ = b) (haC : ¬ ∀ b ∈ B, a * b = b * a)
    (hRxB : ∀ r ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({a} : Set G)),
      x * r * x⁻¹ * r⁻¹ ∈ blockQ B)
    (hRxE : ∀ r ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({a} : Set G)), x * r * x⁻¹ * r⁻¹ ∈ E)
    (hE4 : Nat.card E ≤ 4)
    (hOB : pCoreOf 2 B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({a} : Set G))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBs : IsShort2 B := hB.1
  have hBK : B ≤ K := hB.2.1
  have hS : IsSylowTwoOf (Q ⊓ B) B :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hQ hBK hB.2.2
  set D : Subgroup G := B ⊓ Subgroup.centralizer ({a} : Set G) with hD
  have hSD : Q ⊓ B ≤ D := fun s hs => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hs).2,
    Subgroup.mem_centralizer_singleton_iff.mpr (haZ s (Subgroup.mem_inf.mp hs).1).symm⟩
  obtain ⟨F, hF, hFin, m, hcard, hm, α, hαs, hαk⟩ := exists_sl2_model_one_lt hBt
  rcases L238.dickson_block hS hSD inf_le_left ⟨F, hF, hFin, m, hcard, by omega, α, hαs, hαk⟩
    with hDB | hDN
  · apply haC
    intro b hb
    have : b ∈ D := by rw [hDB]; exact hb
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp this).2).symm
  have hSO : Q ⊓ B ≤ pCoreOf 2 D := le_pCoreOf_of_le_normalizer 2 hSD hDN hS.isPGroup
  have hDsub : IsSubnormal D (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have h := A4.subnormal_inf_right (IsBlock2.isSubnormal hB)
      (L := K ⊓ Subgroup.centralizer ({a} : Set G)) inf_le_left
    rwa [show B ⊓ (K ⊓ Subgroup.centralizer ({a} : Set G)) = D by
      rw [hD, ← inf_assoc, inf_eq_left.mpr hBK]] at h
  have hSR := hSO.trans (A4.pCoreOf_le_of_subnormal 2 hDsub)
  have hB' : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ blockQ B :=
    conj_mul_inv_mem_pCoreOf_of_sylow hcard hm α hαs hαk hxB hx3 hS
      (fun s hs => hRxB s (hSR hs))
  have hU' := mul_inv_mem_blockZ_of_card hBs hxB hB'
    (fun u hu => hRxE u (hOB ((C1.blockU_le_blockQ hBs) hu))) hE4
    (sixteen_mul_card_blockZ_le hBt)
  exact hxC (centralizes_of_trivial hBs hx3 hB' hU')

theorem false_of_moved_block {K Q L B : Subgroup G} {a x : G}
    (hK : CharTwo K) (hQ : IsSylowTwoOf Q K) (haQ : a ∈ Q) (haZ : ∀ q ∈ Q, a * q = q * a)
    (hLb : IsBlock2 (K ⊓ Subgroup.centralizer ({a} : Set G)) L) (hL3 : IsAltType L 3)
    (hxL : x ∈ L) (hx3 : x ^ 3 = 1) (hxfpf : ∀ u ∈ blockU L, u ≠ 1 → x * u * x⁻¹ ≠ u)
    (hB : IsChi0Block K B) (hxB : x ∈ Subgroup.normalizer (B : Set G))
    (hxC : ¬ ∀ b ∈ B, x * b * x⁻¹ = b) (haC : ¬ ∀ b ∈ B, a * b = b * a) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOQ : pCoreOf 2 K ≤ Q := IsSylowTwoOf.pCoreOf_le hQ
  have hQa : Q ≤ Subgroup.centralizer ({a} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haZ q hq).symm
  have haO : a ∈ pCoreOf 2 K := by
    refine hK (Subgroup.mem_inf.mpr ⟨hQ.1 haQ, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (haZ y (hOQ hy)).symm
  have haB : a ∈ Subgroup.normalizer (B : Set G) := mem_normalizer_of_mem_pCoreOf hB.1 haO
  set Ka : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hKa
  have hKaK : Ka ≤ K := inf_le_left
  have hOKa : pCoreOf 2 K ≤ Ka := le_inf (pCoreOf_le 2 K) (hOQ.trans hQa)
  have hKac : CharTwo Ka := charTwo_of_pCoreOf_le hK hOKa hKaK
  have hOO : pCoreOf 2 K ≤ pCoreOf 2 Ka :=
    le_pCoreOf_of_le_normalizer 2 hOKa (hKaK.trans (le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  have hxKa : x ∈ Ka := hLb.2.1 hxL
  have hxa : x * a = a * x :=
    Subgroup.mem_centralizer_singleton_iff.mp ((inf_le_right : Ka ≤ _) hxKa)
  obtain ⟨hQU, hU4, -, -, -, -, -⟩ := hLb.1.alt3_structure hL3
  have hRx : ∀ r ∈ pCoreOf 2 Ka, x * r * x⁻¹ * r⁻¹ ∈ blockU L := by
    intro r hr
    have h := commutator_mem_blockQ_of_mem_pCoreOf hLb hr hxL
    rw [hQU] at h
    exact h
  have hOB : pCoreOf 2 B ≤ pCoreOf 2 Ka :=
    (A4.pCoreOf_le_of_subnormal 2 (IsBlock2.isSubnormal hB.1)).trans hOO
  have hBs : IsShort2 B := hB.1.1
  obtain ⟨q₀, hq₀, hxq₀⟩ : ∃ q ∈ blockQ B, x * q * x⁻¹ ≠ q := by
    by_contra h
    push Not at h
    exact hxC (centralizes_of_centralizes_blockQ hBs hx3 hxB h)
  have hxQB : x ∈ Subgroup.normalizer (blockQ B : Set G) := C1.mem_normalizer_blockQ hxB
  have hxUL : x ∈ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L hxL
  have hUQB : blockU L ≤ blockQ B := by
    have hW := eq_of_ne_one_of_fpf (E := blockU L) (W := blockU L ⊓ blockQ B) hU4 inf_le_left hx3
      (fun w hw => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hxUL w).mp (Subgroup.mem_inf.mp hw).1,
          (Subgroup.mem_normalizer_iff.mp hxQB w).mp (Subgroup.mem_inf.mp hw).2⟩)
      hxfpf (w := x * q₀ * x⁻¹ * q₀⁻¹)
      (Subgroup.mem_inf.mpr ⟨hRx q₀ (hOB hq₀),
        mul_mem ((Subgroup.mem_normalizer_iff.mp hxQB q₀).mp hq₀) (inv_mem hq₀)⟩)
      (fun h => hxq₀ (by rw [← mul_inv_eq_one]; exact h))
    rw [← hW]
    exact inf_le_right
  have hRxB : ∀ r ∈ pCoreOf 2 Ka, x * r * x⁻¹ * r⁻¹ ∈ blockQ B := fun r hr => hUQB (hRx r hr)
  rcases hB.2 with hlin | h3 | h5
  · exact false_of_moved_sl2_block hQ haZ hB.1 (Or.inl hlin) hxB hx3 hxC haC hRxB hRx
      hU4.le hOB
  · apply hxq₀
    refine centralizes_blockQ_of_alt3 hBs h3 haB (fun q hq => haZ q (hOQ ?_)) haC hxB hx3 hxa
      q₀ hq₀
    exact A4.pCoreOf_le_of_subnormal 2 (IsBlock2.isSubnormal hB.1) hq
  · exact false_of_moved_sl2_block hQ haZ hB.1 (Or.inr h5) hxB hx3 hxC haC hRxB hRx
      hU4.le hOB

theorem exists_fpf_not_centralizing {L B : Subgroup G} (hs : IsShort2 L) (h3 : IsAltType L 3)
    (hLB : ¬ L ≤ Subgroup.centralizer (B : Set G)) :
    ∃ x ∈ L, x ^ 3 = 1 ∧ (∀ u ∈ blockU L, u ≠ 1 → x * u * x⁻¹ ≠ u) ∧
      ¬ ∀ b ∈ B, x * b * x⁻¹ = b := by
  classical
  obtain ⟨hQU, hU4, -, hUcomm, -, -, c, hcL, hc3, hcN, hfpf, hLeq⟩ := hs.alt3_structure h3
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hs).trans (C1.blockQ_le L)
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcU : ∀ u ∈ blockU L, c * u * c⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hcN u).mp hu
  have hcand : ∀ u ∈ blockU L, u * c * u⁻¹ ∈ L ∧ (u * c * u⁻¹) ^ 3 = 1 ∧
      ∀ v ∈ blockU L, v ≠ 1 → (u * c * u⁻¹) * v * (u * c * u⁻¹)⁻¹ ≠ v := by
    intro u hu
    refine ⟨mul_mem (mul_mem (hUL hu) hcL) (inv_mem (hUL hu)), ?_, ?_⟩
    · rw [conj_pow, hc3']; group
    · intro v hv hv1 h
      apply hfpf v hv hv1
      have hcv := hcU v hv
      calc c * v * c⁻¹ = u * (c * v * c⁻¹) * u⁻¹ := by rw [hUcomm u hu _ hcv]; group
        _ = (u * c * u⁻¹) * (u * v * u⁻¹) * (u * c * u⁻¹)⁻¹ := by group
        _ = (u * c * u⁻¹) * v * (u * c * u⁻¹)⁻¹ := by rw [hUcomm u hu v hv]; group
        _ = v := h
  by_contra hall
  push Not at hall
  have hcB : ∀ u ∈ blockU L, u * c * u⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
    intro u hu
    obtain ⟨h1, h2, h3'⟩ := hcand u hu
    have := hall _ h1 h2 h3'
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' := this b hb
    calc b * (u * c * u⁻¹) = ((u * c * u⁻¹) * b * (u * c * u⁻¹)⁻¹) * (u * c * u⁻¹) := by
          rw [hb']
      _ = (u * c * u⁻¹) * b := by group
  let f : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun u => ⟨u * (c * u⁻¹ * c⁻¹), mul_mem u.2 (hcU _ (inv_mem u.2))⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by
        obtain ⟨u, hu⟩ := u
        obtain ⟨v, hv⟩ := v
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have h1 := hUcomm _ (hcU _ (inv_mem hu)) _ (hcU _ (inv_mem hv))
        have h2 := hUcomm _ (hcU _ (inv_mem hv)) u hu
        calc u * v * (c * (u * v)⁻¹ * c⁻¹) = u * v * ((c * v⁻¹ * c⁻¹) * (c * u⁻¹ * c⁻¹)) := by
              group
          _ = u * v * ((c * u⁻¹ * c⁻¹) * (c * v⁻¹ * c⁻¹)) := by rw [h1]
          _ = u * (v * (c * u⁻¹ * c⁻¹)) * (c * v⁻¹ * c⁻¹) := by group
          _ = u * ((c * u⁻¹ * c⁻¹) * v) * (c * v⁻¹ * c⁻¹) := by
              rw [hUcomm v hv _ (hcU _ (inv_mem hu))]
          _ = u * (c * u⁻¹ * c⁻¹) * (v * (c * v⁻¹ * c⁻¹)) := by group }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h : (u : G) * (c * (u : G)⁻¹ * c⁻¹) = 1 := congrArg Subtype.val hu
    by_contra hne
    apply hfpf u u.2 (fun h1 => hne (Subtype.ext h1))
    have h' : c * (u : G)⁻¹ * c⁻¹ = (u : G)⁻¹ := by
      calc c * (u : G)⁻¹ * c⁻¹ = (u : G)⁻¹ * ((u : G) * (c * (u : G)⁻¹ * c⁻¹)) := by group
        _ = (u : G)⁻¹ := by rw [h, mul_one]
    calc c * (u : G) * c⁻¹ = (c * (u : G)⁻¹ * c⁻¹)⁻¹ := by group
      _ = u := by rw [h', inv_inv]
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  have hUB : blockU L ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    obtain ⟨u, hu⟩ := hfsurj ⟨v, hv⟩
    have hv' : v = ((u : G) * c * (u : G)⁻¹) * c⁻¹ := by
      have h := congrArg Subtype.val hu
      change (u : G) * (c * (u : G)⁻¹ * c⁻¹) = v at h
      rw [← h]
      group
    rw [hv']
    have hc1 : c ∈ Subgroup.centralizer (B : Set G) := by
      have := hcB 1 (one_mem _)
      simpa using this
    exact mul_mem (hcB u u.2) (inv_mem hc1)
  apply hLB
  rw [hLeq]
  refine sup_le hUB ?_
  rw [Subgroup.zpowers_le]
  have := hcB 1 (one_mem _)
  simpa using this

theorem isBlock2_of_isBlock2_centralizer
    (hC129 : ASC129Statement G) {K Q M L : Subgroup G} {a : G} (hK : CharTwo K)
    (hSQ : IsSQTKIn K) (hQ : IsSylowTwoOf Q K) (hQM : Q ≤ M) (hcgs : cgsIn K Q ≤ M)
    (haQ : a ∈ Q) (haZ : ∀ q ∈ Q, a * q = q * a)
    (hLb : IsBlock2 (K ⊓ Subgroup.centralizer ({a} : Set G)) L) (hL3 : IsAltType L 3)
    (hLM : ¬ L ≤ M) : IsBlock2 K L := by
  classical
  have hSQ' : IsSQTKTC K := C1GN.isSQTKTC_iff_sqtkGroup.mpr hSQ
  have hFle := inf_centralizer_le_of_chi0Blocks hC129 hK hSQ hQ hQM hcgs
  have hLK : L ≤ K := hLb.2.1.trans inf_le_left
  obtain ⟨B, hB𝔊, hLB⟩ : ∃ B ∈ chi0BlocksOutside K Q M,
      ¬ L ≤ Subgroup.centralizer (B : Set G) := by
    by_contra h
    push Not at h
    apply hLM
    refine le_trans (le_inf hLK ?_) hFle
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun B hB => Subgroup.le_centralizer_iff.mp (h B hB)
  obtain ⟨x, hxL, hx3, hxfpf, hxC⟩ := exists_fpf_not_centralizing hLb.1 hL3 hLB
  have hxK : x ∈ K := hLK hxL
  have hBc := hB𝔊.1
  have hBx := C1Pack.conj_mem_chiBlocksOutside hK hSQ' hQ hQM hBc hxK
  have hBx' := C1Pack.conj_mem_chiBlocksOutside hK hSQ' hQ hQM hBc (inv_mem hxK)
  have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
    rcases C1Pack.chiBlocks_eq_of_three hK hSQ' hBc.1 hBx.1 hBx'.1 with h | h | h
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    · exact inv_mem_iff.mp (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
    · have h' := C1Pack.inv_mul_mem_normalizer_of_map_conj_eq h
      have hx2 : x⁻¹ * x⁻¹ = x := by
        calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * (x * x * x) := by
              rw [mul_assoc x, ← pow_three, hx3, mul_one]
          _ = x := by group
      rwa [hx2] at h'
  have hBK : B ≤ K := hB𝔊.2.1.2.1
  by_cases haB : ∀ b ∈ B, a * b = b * a
  ·
    set Ka : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hKa
    have hOQ : pCoreOf 2 K ≤ Q := IsSylowTwoOf.pCoreOf_le hQ
    have hQa : Q ≤ Subgroup.centralizer ({a} : Set G) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.mpr (haZ q hq).symm
    have hKac : CharTwo Ka :=
      charTwo_of_pCoreOf_le hK (le_inf (pCoreOf_le 2 K) (hOQ.trans hQa)) inf_le_left
    have hBKa : B ≤ Ka := le_inf hBK fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mpr (haB b hb).symm
    have hBb : IsBlock2 Ka B := ⟨hB𝔊.2.1.1, hBKa, (isSubnormal_iff_subgroupOf hBKa).mp
      (A4.subnormal_of_le_of_le (IsBlock2.isSubnormal hB𝔊.2.1) hBKa inf_le_left)⟩
    by_cases hLBeq : L = B
    · rw [hLBeq]; exact hB𝔊.2.1
    · exfalso
      have hcomm := distinctBlocksCommuteStatement Ka L B hKac hLb hBb hLBeq
      apply hxC
      intro b hb
      have := Subgroup.commutator_mem_commutator hxL hb
      rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at this
      calc x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
        _ = b := by rw [this, one_mul]
  · exact (false_of_moved_block hK hQ haQ haZ hLb hL3 hxL hx3 hxfpf hB𝔊.2 hxB hxC haB).elim

end CFSG.Quasithin.E6.A3Push
