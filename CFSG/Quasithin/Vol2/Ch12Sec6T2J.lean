module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2D
public import CFSG.Quasithin.Vol2.Ch12Sec6T2FF
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Perf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem Qv_eq (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    Qv T V = (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  refine le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf ?_ inf_le_right)
  have hT := isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow (le_sup_right : T ≤ L ⊔ T)
  exact hT.le_of_normalizes inf_le_left
    (B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTV))
    (isPGroup_CLT_V h1222 hH)

omit [IsMulCommutative ↥V] in
theorem LT_le_normalizer_Qv (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    L ⊔ T ≤ Subgroup.normalizer (Qv T V : Set G) := by
  rw [Qv_eq h1222 hH]
  exact B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer
    (sup_le hH.hyp.irrPlus.2.2.1 (S126L19b.T_le_normalizer_V h1222 hH)))

omit [Finite G] [IsMulCommutative ↥V] in
theorem Qv_le_Gv {v : G} (hv : v ∈ V) : Qv T V ≤ Gv v := fun q hq => by
  rw [Gv, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.1 hq.2 v hv).symm

omit [IsMulCommutative ↥V] in
theorem Qv_le_Rv (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    Qv T V ≤ Rv T L v :=
  le_pCoreOf_of_le_normalizer 2 (le_inf (inf_le_left.trans le_sup_right) (Qv_le_Gv hv))
    (inf_le_left.trans (LT_le_normalizer_Qv h1222 hH)) (hH.hyp.sylow.1.to_le inf_le_left)

@[expose] def Stab01 (σ : Equiv.Perm (Fin 8)) : Prop := (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)

theorem stab01_inv {σ : Equiv.Perm (Fin 8)} (h : Stab01 σ) :
    (σ 0 = 0 ∧ σ 1 = 1 ∧ σ⁻¹ 0 = 0 ∧ σ⁻¹ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0 ∧ σ⁻¹ 0 = 1 ∧ σ⁻¹ 1 = 0) := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, h1, by rw [Equiv.Perm.inv_eq_iff_eq, h0],
      by rw [Equiv.Perm.inv_eq_iff_eq, h1]⟩
  · exact Or.inr ⟨h0, h1, by rw [Equiv.Perm.inv_eq_iff_eq, h1],
      by rw [Equiv.Perm.inv_eq_iff_eq, h0]⟩

theorem comm_fix01 {σ τ : Equiv.Perm (Fin 8)} (hσ : Stab01 σ) (hτ : Stab01 τ) :
    (σ * τ * σ⁻¹ * τ⁻¹) 0 = 0 ∧ (σ * τ * σ⁻¹ * τ⁻¹) 1 = 1 := by
  simp only [Equiv.Perm.mul_apply]
  rcases stab01_inv hσ with ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩ <;>
    rcases stab01_inv hτ with ⟨b0, b1, b2, b3⟩ | ⟨b0, b1, b2, b3⟩
  · exact ⟨by rw [b2, a2, b0, a0], by rw [b3, a3, b1, a1]⟩
  · exact ⟨by rw [b2, a3, b1, a0], by rw [b3, a2, b0, a1]⟩
  · exact ⟨by rw [b2, a2, b1, a1], by rw [b3, a3, b0, a0]⟩
  · exact ⟨by rw [b2, a3, b0, a1], by rw [b3, a2, b1, a0]⟩

theorem comm_mem_A6s {σ τ : Equiv.Perm (Fin 8)} (hσ : Stab01 σ)
    (hσA : σ ∈ alternatingGroup (Fin 8)) (hτ : Stab01 τ) (hτA : τ ∈ alternatingGroup (Fin 8)) :
    σ * τ * σ⁻¹ * τ⁻¹ ∈ A6s := by
  obtain ⟨h0, h1⟩ := comm_fix01 hσ hτ
  exact mem_A6s.2 ⟨h0, h1, (alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).mul_mem
    ((alternatingGroup (Fin 8)).mul_mem hσA hτA) ((alternatingGroup (Fin 8)).inv_mem hσA))
    ((alternatingGroup (Fin 8)).inv_mem hτA)⟩

theorem psiP_mem_A6s (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {l : ↥L}
    (hl : (l : G) ∈ Lv L v) : psiP F hH l ∈ A6s := by
  set K' : Subgroup (Equiv.Perm (Fin 8)) := ((Lv L v).subgroupOf L).map (psiP F hH) with hK'
  have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  have hperf : ⁅K', K'⁆ = K' := by
    rw [hK', ← Subgroup.map_commutator, perfect_subgroupOf hLp (Lv_le_L L v)]
  have hst : ∀ σ ∈ K', ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) ∧
      σ ∈ alternatingGroup (Fin 8) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨psiP_stab h1222 F hH hv hβ (Lv_le_Gv L v hz), psiP_mem F hH z⟩
  have hle : K' ≤ A6s := by
    rw [← hperf, Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [commutatorElement_def]
    exact comm_mem_A6s (hst σ hσ).1 (hst σ hσ).2 (hst τ hτ).1 (hst τ hτ).2
  exact hle ⟨l, hl, rfl⟩

omit [IsMulCommutative ↥V] in
theorem isPGroup_CL (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
  rintro ⟨x, hxL, hxC⟩
  obtain ⟨k, hk⟩ := S126L19a.isPGroup_ker h1222 hH ⟨⟨x, hxL⟩, hxC⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) =>
    ((z : ↥L) : G)) hk
  simpa using this

omit [IsMulCommutative ↥V] in
theorem Lv_inf_le (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) (v : G) :
    Lv L v ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (Lv L v) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left
    (B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer ((Lv_le_L L v).trans hLV)))
    ((isPGroup_CL h1222 hH).to_le (inf_le_inf_right _ (Lv_le_L L v)))

theorem comm_eq_or_le_D (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {J : Subgroup G}
    (hJ : J ≤ (L ⊔ T) ⊓ Gv v) :
    ⁅Lv L v, J⁆ = Lv L v ∨
      J ≤ centralizerSection ((L ⊔ T) ⊓ Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hHN : (L ⊔ T) ⊓ Gv v ≤ Subgroup.normalizer (Lv L v : Set G) := by
    refine le_trans ?_ (normalizer_le_normalizer_perfectCore (L ⊓ Gv v))
    refine (le_inf (inf_le_left.trans (sup_le Subgroup.le_normalizer hTL)) ?_).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact (inf_le_right : (L ⊔ T) ⊓ Gv v ≤ Gv v).trans Subgroup.le_normalizer
  set N := ⁅Lv L v, J⁆ with hN
  have hNle : N ≤ Lv L v := by
    rw [hN, Subgroup.commutator_le]
    intro l hl j hj
    rw [commutatorElement_def]
    have h1 : j * l⁻¹ * j⁻¹ ∈ Lv L v :=
      (Subgroup.mem_normalizer_iff.1 (hHN (hJ hj)) _).1 ((Lv L v).inv_mem hl)
    have e : l * j * l⁻¹ * j⁻¹ = l * (j * l⁻¹ * j⁻¹) := by group
    rw [e]
    exact (Lv L v).mul_mem hl h1
  have hNn : Lv L v ≤ Subgroup.normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_left _ _
  have hNL : N ≤ L := hNle.trans (Lv_le_L L v)
  set M : Subgroup (Equiv.Perm (Fin 8)) := (N.subgroupOf L).map (psiP F hH) with hM
  have hMA : M ≤ A6s := by
    rintro _ ⟨z, hz, rfl⟩
    exact psiP_mem_A6s h1222 F hH hv hβ (hNle hz)
  have hMn : ∀ a ∈ A6s, ∀ m ∈ M, a * m * a⁻¹ ∈ M := by
    intro a ha m hm
    obtain ⟨l, hl, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a ha
    obtain ⟨z, hz, rfl⟩ := hm
    refine ⟨l * z * l⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show ((l : G) * z * (l : G)⁻¹) ∈ N
    exact (Subgroup.mem_normalizer_iff.1 (hNn hl) z).1 hz
  rcases eq_bot_or_eq_of_normal hMA hMn with hbot | htop
  · right
    have hNC : N ≤ pCoreOf 2 (Lv L v) := by
      intro n hn
      refine Lv_inf_le h1222 hH v ⟨hNle hn, ?_⟩
      have h1 : psiP F hH ⟨n, hNL hn⟩ ∈ M := ⟨⟨n, hNL hn⟩, hn, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : S126L19a.psi F hH ⟨n, hNL hn⟩ = 1 := Subtype.ext h1
      exact (S126L19a.psi_eq_one_iff F hH _).1 h2
    intro j hj
    refine ⟨hJ hj, hHN (hJ hj), normalizer_le_normalizer_pCoreOf 2 _ (hHN (hJ hj)),
      fun l hl => hNC ?_⟩
    have := Subgroup.commutator_mem_commutator hl hj
    rwa [commutatorElement_def] at this
  · left
    refine le_antisymm hNle (le_of_two_mod (perfectCore_perfect _) hNn ?_)
    intro k hk
    have hkM : psiP F hH ⟨k, Lv_le_L L v hk⟩ ∈ M := htop ▸ psiP_mem_A6s h1222 F hH hv hβ hk
    obtain ⟨n, hn, hnk⟩ := hkM
    have hnN : (n : G) ∈ N := hn
    refine ⟨n, hnN, (n : G)⁻¹ * k, by group, hNn ((Lv L v).mul_mem
      ((Lv L v).inv_mem (hNle hnN)) hk), ?_⟩
    have hq1 : S126L19a.psi F hH ((n : ↥L)⁻¹ * ⟨k, Lv_le_L L v hk⟩) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact Subtype.ext hnk
    have hqC := (S126L19a.psi_eq_one_iff F hH _).1 hq1
    obtain ⟨m, hm⟩ := S126L19a.isPGroup_ker h1222 hH ⟨(n : ↥L)⁻¹ * ⟨k, Lv_le_L L v hk⟩, hqC⟩
    refine ⟨m, ?_⟩
    have := congrArg (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) =>
      ((z : ↥L) : G)) hm
    simpa using this

theorem offender_le (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {A : Subgroup G} (hAT : A ≤ T) (hAe : IsElemAbelian 2 A)
    (hNP : ∀ i j : Fin 8, i ≠ j → ∃ a ∈ A, ∃ τ : Equiv.Perm (Fin 8), ActsAs F a τ ∧
      ¬ ((τ i = i ∧ τ j = j) ∨ (τ i = j ∧ τ j = i))) :
    (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card V := by
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hN : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (V : Set G) := fun a => hTV (hAT a.2)
  have hex : ∀ a : ↥A, ∃ σ : Equiv.Perm (Fin 8), ActsAs F a σ := fun a =>
    (actsAs_of_mem_T F (hAT a.2)).imp fun _ h => h.2
  choose φ₀ hφ₀ using hex
  let φ : ↥A →* Equiv.Perm (Fin 8) :=
    { toFun := φ₀
      map_one' := (hφ₀ 1).unique (ActsAs.one F) (Subgroup.one_mem _)
      map_mul' := fun a b => (hφ₀ (a * b)).unique ((hφ₀ a).mul (hφ₀ b) (hN b)) (hN (a * b)) }
  have hker : ∀ a : ↥A, φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro a
    constructor
    · intro h
      have h1 : ActsAs F a 1 := h ▸ hφ₀ a
      exact mem_centralizer_of_actsAs_one F hVL hLV (hTL (hAT a.2)) (hN a) h1
    · intro h
      have h1 : ActsAs F a 1 := by
        intro v w hw
        have hwv : w = v := Subtype.ext (by
          rw [hw, (Subgroup.mem_centralizer_iff.1 h v v.2).symm]
          group)
        rw [hwv, dAct_one]
      exact (hφ₀ a).unique h1 (hN a)
  have hsub : (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A = φ.ker := by
    ext a
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    exact ⟨fun h => (hker a).2 h.2, fun h => ⟨a.2, (hker a).1 h⟩⟩
  have hidx : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = Nat.card φ.range := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
  have hfix : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card F.β.ker * Nat.card (fixD φ.range) := by
    let X : Subgroup ↥V := (V ⊓ Subgroup.centralizer (A : Set G)).subgroupOf V
    have hX : Nat.card X = Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    let ψ : ↥X →* D8 := F.β.comp X.subtype
    have h1 : Nat.card X = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have h2 : Nat.card ψ.ker ≤ Nat.card F.β.ker := by
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥X) : ↥V), x.2⟩) fun x y h => ?_
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have h3 : ψ.range ≤ fixD φ.range := by
      rintro _ ⟨x, rfl⟩ σ ⟨a, rfl⟩
      have hxa : ((x : ↥V) : G) = (a : G) * ((x : ↥V) : G) * (a : G)⁻¹ := by
        have hc := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).2
        rw [Subgroup.mem_centralizer_iff.1 hc a a.2]
        group
      exact (hφ₀ a (x : ↥V) (x : ↥V) hxa).symm
    have h4 := Subgroup.card_le_of_le h3
    rw [← hX, h1, mul_comm]
    exact Nat.mul_le_mul h2 h4
  have hV : Nat.card V = Nat.card F.β.ker * 64 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup F.β.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F.β F.β_surj).toEquiv,
      S126L20.card_D8_eq, mul_comm]
  have hcomm : ∀ σ ∈ φ.range, ∀ τ ∈ φ.range, σ * τ = τ * σ := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((B6.isElemAbelian_iff.1 hAe).1 a a.2 b b.2)
  have hinv : ∀ σ ∈ φ.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext (by simpa [pow_two] using (B6.isElemAbelian_iff.1 hAe).2 a a.2)
  have hNP' : NoPair φ.range := by
    intro i j hij
    obtain ⟨a, ha, τ, hτ, hn⟩ := hNP i j hij
    refine ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    have e : φ ⟨a, ha⟩ = τ := (hφ₀ ⟨a, ha⟩).unique hτ (hN ⟨a, ha⟩)
    rw [e]
    exact hn
  have hff := card_mul_card_fixD_le hcomm hinv hNP'
  rw [hidx, hV]
  calc Nat.card φ.range * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))
      ≤ Nat.card φ.range * (Nat.card F.β.ker * Nat.card (fixD φ.range)) :=
        Nat.mul_le_mul_left _ hfix
    _ = Nat.card F.β.ker * (Nat.card φ.range * Nat.card (fixD φ.range)) := by ring
    _ ≤ Nat.card F.β.ker * 64 := Nat.mul_le_mul_left _ hff

theorem swap_not_comm : Equiv.swap (0 : Fin 8) 1 * cy 0 2 3 ≠ cy 0 2 3 * Equiv.swap 0 1 := by
  decide

theorem cy_mem_A8 : cy (0 : Fin 8) 2 3 ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.2 (sign_cy (by decide) (by decide))

theorem L_eq_comm (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hJ : ¬ thompsonJ T ≤ Qv T V) : L = ⁅L, thompsonJ T⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  set N := ⁅L, thompsonJ T⁆ with hNdef
  have hNL : N ≤ L := by
    rw [hNdef, Subgroup.commutator_le]
    intro l hl j hj
    rw [commutatorElement_def]
    have h1 : j * l⁻¹ * j⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hTL (hJT hj)) _).1 (L.inv_mem hl)
    have e : l * j * l⁻¹ * j⁻¹ = l * (j * l⁻¹ * j⁻¹) := by group
    rw [e]
    exact L.mul_mem hl h1
  have hNn : L ≤ Subgroup.normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_left _ _
  set ψ := S126L19a.psi F hH with hψ
  set M : Subgroup ↥(alternatingGroup (Fin 8)) := (N.subgroupOf L).map ψ with hM
  have hMn : M.Normal := ⟨fun m hm g => by
    obtain ⟨l, rfl⟩ := S126L19a.psi_surjective F hH g
    obtain ⟨z, hz, rfl⟩ := hm
    refine ⟨l * z * l⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show ((l : G) * z * (l : G)⁻¹) ∈ N
    exact (Subgroup.mem_normalizer_iff.1 (hNn l.2) z).1 hz⟩
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  · exfalso
    apply hJ
    intro j hj
    have hjT := hJT hj
    obtain ⟨τ, -, hτ⟩ := actsAs_of_mem_T F hjT
    have hcomm : ∀ σ ∈ alternatingGroup (Fin 8), τ * σ = σ * τ := by
      intro σ hσ
      obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH ⟨σ, hσ⟩
      have hc : (l : G) * j * (l : G)⁻¹ * j⁻¹ ∈ N := by
        have := Subgroup.commutator_mem_commutator l.2 hj
        rwa [commutatorElement_def] at this
      have hcL := hNL hc
      have h1 : ψ ⟨_, hcL⟩ ∈ M := ⟨⟨_, hcL⟩, hc, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have hact1 := (S126L19a.actsAs_psi F hH l).commutator hτ (hLV l.2) (hTV hjT)
      have hact2 := S126L19a.actsAs_psi F hH ⟨_, hcL⟩
      rw [show ((ψ ⟨_, hcL⟩ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) = 1 by
        rw [h1]; rfl] at hact2
      have e := hact1.unique hact2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (hLV l.2) (hTV hjT)) (Subgroup.inv_mem _ (hLV l.2))) (Subgroup.inv_mem _ (hTV hjT)))
      rw [hl] at e
      calc τ * σ = (σ * τ * σ⁻¹ * τ⁻¹)⁻¹ * (σ * τ) := by group
        _ = σ * τ := by rw [e, inv_one, one_mul]
    have hτ1 : τ = 1 := by
      rcases eq_of_comm fun a ha => hcomm a (mem_A6s.1 ha).2.2 with h | h
      · exact h
      · exact absurd (h ▸ hcomm _ cy_mem_A8) swap_not_comm
    rw [hτ1] at hτ
    exact ⟨hjT, mem_centralizer_of_actsAs_one F hVL hLV (hTL hjT) (hTV hjT) hτ⟩
  ·
    have hnorm : (N.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 hNn
    have hCN : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (N : Set G) :=
      inf_le_left.trans hNn
    have hCp := isPGroup_CL h1222 hH
    refine (hH.hyp.faithful.2.1 N hNL hnorm fun x hx => ?_).symm
    have hxM : ψ ⟨x, hx⟩ ∈ M := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := hxM
    have hq1 : ψ ((n : ↥L)⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, hnx, inv_mul_cancel]
    have hqC := (S126L19a.psi_eq_one_iff F hH _).1 hq1
    have hmem : x ∈ N ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) := by
      have e : x = (n : G) * ((n : G)⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hn ⟨L.mul_mem (L.inv_mem n.2) hx, hqC⟩
    exact two_pow_mem_of_mem_sup hCp hCN hmem

end S126T2

end CFSG.Quasithin.H13
