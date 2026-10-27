module

public import CFSG.GH74.BNPair.Cells
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def P (i : Bool) : Subgroup X :=
  pgen D.B D.N D.w₁ D.w₂ i

@[expose] def Q (i : Bool) : Subgroup X :=
  pCoreOf 2 (P D i)

@[expose] def mi (i : Bool) : X :=
  (D.lift (gen D.w₁ D.w₂ i) : X)

@[expose] def Uplus (i : Bool) : Subgroup X :=
  D.UwPlusSub (D.lift (gen D.w₁ D.w₂ i))

theorem P_true : P D true = D.P₁ := rfl

theorem P_false : P D false = D.P₂ := rfl

theorem mem_P_iff {i : Bool} {x : X} :
    x ∈ P D i ↔ x ∈ D.B ∨ x ∈ dc D.B D.N (gen D.w₁ D.w₂ i) :=
  mem_parabolic_single_iff D.rank2.tits (D.rank2.gen_mem i)

theorem B_le_P (i : Bool) : D.B ≤ P D i :=
  fun _ hx => D.rank2.B_le_pgen i hx

theorem mi_mem_dc (i : Bool) : mi D i ∈ dc D.B D.N (gen D.w₁ D.w₂ i) := by
  have := coe_mem_dc (B := D.B) (N := D.N) (D.lift (gen D.w₁ D.w₂ i))
  rwa [D.lift_mk] at this

theorem mi_mem_P (i : Bool) : mi D i ∈ P D i :=
  (mem_P_iff D).2 (Or.inr (mi_mem_dc D i))

theorem mi_sq_mem_B (i : Bool) : mi D i * mi D i ∈ D.B := by
  have h : ((D.lift (gen D.w₁ D.w₂ i) * D.lift (gen D.w₁ D.w₂ i) : D.N) : D.Weyl) = 1 := by
    rw [QuotientGroup.mk_mul, D.lift_mk]
    exact D.isTits.mul_self_gen (D.rank2.gen_mem i)
  simpa [mi] using mk_eq_one_iff.1 h

theorem conj_mem_U {b x : X} (hb : b ∈ D.B) (hx : x ∈ D.U) : b * x * b⁻¹ ∈ D.U := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  have hxu : u * x * u⁻¹ ∈ chainProd D.root (intList 1 n) :=
    D.roots.carrier_eq ▸ D.U.mul_mem (D.U.mul_mem hu hx) (D.U.inv_mem hu)
  have key := chainProd_conj_mem D.root D.U h (intList 1 n) (fun k hk y hy => by
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    exact D.root_le_U hk1 hk2 (D.roots.invariant k ⟨by omega, by omega⟩ h hh y hy)) _ hxu
  have e : h * u * x * (h * u)⁻¹ = h * (u * x * u⁻¹) * h⁻¹ := by group
  rw [e]
  exact key

theorem B_le_normalizer_U : D.B ≤ Subgroup.normalizer (D.U : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_U D hg hx, fun hx => ?_⟩
  have := conj_mem_U D (D.B.inv_mem hg) hx
  simpa [mul_assoc] using this

theorem mem_Uplus_iff {i : Bool} {x : X} :
    x ∈ Uplus D i ↔ x ∈ D.U ∧ mi D i * x * (mi D i)⁻¹ ∈ D.U :=
  Iff.rfl

theorem Uplus_le_U (i : Bool) : Uplus D i ≤ D.U :=
  fun _ hx => ((mem_Uplus_iff D).1 hx).1

theorem Uplus_le_P (i : Bool) : Uplus D i ≤ P D i :=
  (Uplus_le_U D i).trans (D.U_le_B.trans (B_le_P D i))

theorem coe_Uplus_true : (Uplus D true : Set X) = chainProd D.root (intList 2 n) := by
  have := (D.eq30_5_A (i := 1) (by have := D.three_le; omega) (D.lift (gen D.w₁ D.w₂ true))
    (by rw [D.lift_mk, altWord_one]; rfl)).2
  show D.UwPlus _ = _
  rw [this]
  simp

theorem coe_Uplus_false : (Uplus D false : Set X) = chainProd D.root (intList 1 ((n : ℤ) - 1)) := by
  have h := (D.eq30_5_B (i := 1) (by have := D.three_le; omega) (D.lift (gen D.w₁ D.w₂ false))
    (by rw [D.lift_mk, altWord_one]; rfl)).2
  have h2 := D.chainProd_intList_reverse (a := 1) (b := (n : ℤ) - ((1 : ℕ) : ℤ)) le_rfl
    (by omega)
  show D.UwPlus _ = _
  rw [h, ← h2]
  simp

theorem root_le_Uplus_true : D.root n ≤ Uplus D true := by
  have hn := D.three_le
  intro x hx
  rw [← SetLike.mem_coe, coe_Uplus_true]
  exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨by omega, le_rfl⟩) hx

theorem root_le_Uplus_false : D.root 1 ≤ Uplus D false := by
  have hn := D.three_le
  intro x hx
  rw [← SetLike.mem_coe, coe_Uplus_false]
  exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨le_rfl, by omega⟩) hx

theorem B_conj_Uplus {i : Bool} {b x : X} (hb : b ∈ D.B) (hx : x ∈ Uplus D i) :
    b * x * b⁻¹ ∈ Uplus D i := by
  have hn := D.three_le
  cases i
  · obtain ⟨V, hVc, -, -, hVn⟩ := D.roots.subgroup 1 ((n : ℤ) - 1) le_rfl (by omega) (by omega)
    have hcar : (Uplus D false : Set X) = (V : Set X) := (coe_Uplus_false D).trans hVc.symm
    have hxV : x ∈ V := by
      rw [← SetLike.mem_coe, ← hcar]
      exact hx
    have := D.B_normalizes_V₂ hVc (hVn (by omega)) b hb x hxV
    rw [← SetLike.mem_coe, ← hcar] at this
    exact this
  · obtain ⟨V, hVc, -, hVn, -⟩ := D.roots.subgroup 2 (n : ℤ) (by norm_num) (by omega) le_rfl
    have hcar : (Uplus D true : Set X) = (V : Set X) := (coe_Uplus_true D).trans hVc.symm
    have hxV : x ∈ V := by
      rw [← SetLike.mem_coe, ← hcar]
      exact hx
    have := D.B_normalizes_V₁ hVc (hVn (by norm_num)) b hb x hxV
    rw [← SetLike.mem_coe, ← hcar] at this
    exact this

theorem mi_conj_Uplus {i : Bool} {x : X} (hx : x ∈ Uplus D i) :
    mi D i * x * (mi D i)⁻¹ ∈ Uplus D i := by
  rw [mem_Uplus_iff]
  refine ⟨((mem_Uplus_iff D).1 hx).2, ?_⟩
  have e : mi D i * (mi D i * x * (mi D i)⁻¹) * (mi D i)⁻¹ =
      (mi D i * mi D i) * x * (mi D i * mi D i)⁻¹ := by group
  rw [e]
  exact conj_mem_U D (mi_sq_mem_B D i) ((mem_Uplus_iff D).1 hx).1

theorem P_conj_Uplus {i : Bool} {p x : X} (hp : p ∈ P D i) (hx : x ∈ Uplus D i) :
    p * x * p⁻¹ ∈ Uplus D i := by
  rcases (mem_P_iff D).1 hp with hB | hd
  · exact B_conj_Uplus D hB hx
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift (D.lift_mk (gen D.w₁ D.w₂ i))).1 hd
    change b₁ * mi D i * b₂ * x * (b₁ * mi D i * b₂)⁻¹ ∈ Uplus D i
    have e : b₁ * mi D i * b₂ * x * (b₁ * mi D i * b₂)⁻¹ =
        b₁ * (mi D i * (b₂ * x * b₂⁻¹) * (mi D i)⁻¹) * b₁⁻¹ := by group
    rw [e]
    exact B_conj_Uplus D hb₁ (mi_conj_Uplus D (B_conj_Uplus D hb₂ hx))

theorem P_le_normalizer_Uplus (i : Bool) : P D i ≤ Subgroup.normalizer (Uplus D i : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => P_conj_Uplus D hg hx, fun hx => ?_⟩
  have := P_conj_Uplus D ((P D i).inv_mem hg) hx
  simpa [mul_assoc] using this

theorem isPGroup_Uplus (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : IsPGroup 2 (Uplus D i) :=
  hU.2.1.to_le (Uplus_le_U D i)

theorem Q_normal_in_P (i : Bool) :
    ∀ p ∈ P D i, ∀ x ∈ Q D i, p * x * p⁻¹ ∈ Q D i := fun _ hp x hx =>
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (P D i) hp) x).1 hx

section Sylow

variable [Finite X]

theorem Q_le_U (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : Q D i ≤ D.U := by
  have hidx : ¬ 2 ∣ D.U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let S : Sylow 2 X := hU.2.1.toSylow hidx
  have hQp : IsPGroup 2 (Q D i) := pCoreOf_isPGroup 2 (P D i)
  have hnorm : P D i ≤ Subgroup.normalizer (Q D i : Set X) := le_normalizer_pCoreOf 2 (P D i)
  have hUQ : D.U ≤ Subgroup.normalizer (Q D i : Set X) :=
    (D.U_le_B.trans (B_le_P D i)).trans hnorm
  have hsup : IsPGroup 2 (Q D i ⊔ D.U : Subgroup X) := hQp.to_sup_of_normal_left' hU.2.1 hUQ
  have := S.is_maximal' hsup (le_sup_right : D.U ≤ Q D i ⊔ D.U)
  exact le_sup_left.trans this.le

omit [Finite X] in
theorem Uplus_le_Q (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : Uplus D i ≤ Q D i :=
  le_pCoreOf_of_le_normalizer 2 (Uplus_le_P D i) (P_le_normalizer_Uplus D i)
    (isPGroup_Uplus D hU i)

theorem Q_le_Uplus (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : Q D i ≤ Uplus D i := by
  intro x hx
  have hm : mi D i ∈ Subgroup.normalizer (Q D i : Set X) :=
    le_normalizer_pCoreOf 2 (P D i) (mi_mem_P D i)
  exact ⟨Q_le_U D hU i hx, Q_le_U D hU i ((Subgroup.mem_normalizer_iff.1 hm x).1 hx)⟩

theorem pCore_eq (hU : IsSylowTwoOf D.U ⊤) (i : Bool) :
    pCoreOf 2 (P D i) = D.UwPlusSub (D.lift (gen D.w₁ D.w₂ i)) :=
  le_antisymm (Q_le_Uplus D hU i) (Uplus_le_Q D hU i)

theorem pCore_eq_inf_comap (hU : IsSylowTwoOf D.U ⊤) (i : Bool) :
    pCoreOf 2 (P D i) = D.U ⊓ D.U.comap (MulAut.conj (mi D i)).toMonoidHom := by
  rw [pCore_eq D hU i]
  ext x
  simp [mi, MulAut.conj_apply]
  rfl

theorem Q_eq_Uplus (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : Q D i = Uplus D i :=
  pCore_eq D hU i

theorem Q_le_B (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : Q D i ≤ D.B :=
  (Q_le_U D hU i).trans D.U_le_B

end Sylow

section Normalizers

theorem exists_conj_root_neg₁ {m : D.N} (hm : (m : D.Weyl) = D.w₁) {y : X}
    (hy : y ∈ D.root (-1)) : ∃ x ∈ D.root 1, y = (m : X) * x * (m : X)⁻¹ := by
  have h := (D.roots.action₁ (m⁻¹) (D.inv_lift₁ m hm)).1
  rw [← h] at hy
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
  refine ⟨x, hx, ?_⟩
  rw [← hxy]
  simp [MulAut.conj_apply]

theorem exists_conj_root_negn {m : D.N} (hm : (m : D.Weyl) = D.w₂) {y : X}
    (hy : y ∈ D.root (-(n : ℤ))) : ∃ x ∈ D.root n, y = (m : X) * x * (m : X)⁻¹ := by
  have h := (D.roots.action₂ (m⁻¹) (D.inv_lift₂ m hm)).1
  rw [← h] at hy
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
  refine ⟨x, hx, ?_⟩
  rw [← hxy]
  simp [MulAut.conj_apply]

theorem false_of_conj₁ {m : D.N} (hm : (m : D.Weyl) = D.w₁)
    (h : ∀ x ∈ D.root 1, (m : X) * x * (m : X)⁻¹ ∈ D.U) : False := by
  have hn := D.three_le
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (D.roots.ne_bot (-1) ⟨by norm_num, by simp; omega⟩)
  obtain ⟨x, hx, rfl⟩ := exists_conj_root_neg₁ D hm hy
  have hVm : (m : X) * x * (m : X)⁻¹ ∈ D.Vm := D.root_le_V D.coe_Vm (by omega) le_rfl hy
  exact hy1 (Subtype.ext (D.eq_one_of_mem_U_Vm (D.U_le_B (h x hx)) hVm))

theorem false_of_conj₂ {m : D.N} (hm : (m : D.Weyl) = D.w₂)
    (h : ∀ x ∈ D.root n, (m : X) * x * (m : X)⁻¹ ∈ D.U) : False := by
  have hn := D.three_le
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (D.roots.ne_bot (-(n : ℤ)) ⟨by omega, by simp⟩)
  obtain ⟨x, hx, rfl⟩ := exists_conj_root_negn D hm hy
  have hVm : (m : X) * x * (m : X)⁻¹ ∈ D.Vm := D.root_le_V D.coe_Vm le_rfl (by omega) hy
  exact hy1 (Subtype.ext (D.eq_one_of_mem_U_Vm (D.U_le_B (h x hx)) hVm))

theorem mi_true_not_mem_normalizer {Z : Subgroup X} (hZ : Z ≤ D.U) (hX : D.root 1 ≤ Z) :
    mi D true ∉ Subgroup.normalizer (Z : Set X) := by
  intro hm
  refine false_of_conj₁ D (m := D.lift (gen D.w₁ D.w₂ true)) (D.lift_mk _) (fun x hx => ?_)
  exact hZ ((Subgroup.mem_normalizer_iff.1 hm x).1 (hX hx))

theorem mi_false_not_mem_normalizer {Z : Subgroup X} (hZ : Z ≤ D.U) (hX : D.root n ≤ Z) :
    mi D false ∉ Subgroup.normalizer (Z : Set X) := by
  intro hm
  refine false_of_conj₂ D (m := D.lift (gen D.w₁ D.w₂ false)) (D.lift_mk _) (fun x hx => ?_)
  exact hZ ((Subgroup.mem_normalizer_iff.1 hm x).1 (hX hx))

theorem le_P_of_no_lift {M : Subgroup X} (hBM : D.B ≤ M) (i : Bool) (hm : mi D (!i) ∉ M) :
    M ≤ P D i := by
  classical
  obtain ⟨J, hJ, rfl⟩ := D.isTits.exists_parabolic hBM
  have hJS : (J : Set D.Weyl) ⊆ (({D.w₁, D.w₂} : Finset D.Weyl) : Set D.Weyl) := by
    exact_mod_cast hJ
  have hJi : J ⊆ {gen D.w₁ D.w₂ i} := by
    intro x hx
    have hx2 := hJ hx
    have hcases : x = gen D.w₁ D.w₂ i ∨ x = gen D.w₁ D.w₂ (!i) := by
      cases i <;> simp at hx2 ⊢ <;> tauto
    rcases hcases with rfl | rfl
    · exact Finset.mem_singleton_self _
    · exact absurd ((D.isTits.bnCore.mono hJS).mem_parabolic_of_mem_dc
        (Subgroup.subset_closure hx) (mi_mem_dc D (!i))) hm
  have := (D.isTits.parabolic_le_iff hJ (Finset.singleton_subset_iff.2 (D.rank2.gen_mem i))).2 hJi
  simpa [P, pgen] using this

theorem P₁_inf_P₂ : D.P₁ ⊓ D.P₂ = D.B :=
  le_antisymm (fun _ hx => D.rank2.pgen_inter true hx.1 hx.2)
    (le_inf (B_le_P D true) (B_le_P D false))

theorem normalizer_U_eq_B : Subgroup.normalizer (D.U : Set X) = D.B := by
  have hn := D.three_le
  refine le_antisymm ?_ (B_le_normalizer_U D)
  have h1 : Subgroup.normalizer (D.U : Set X) ≤ P D true :=
    le_P_of_no_lift D (B_le_normalizer_U D) true
      (mi_false_not_mem_normalizer D le_rfl (D.root_le_U (by omega) le_rfl))
  have h2 : Subgroup.normalizer (D.U : Set X) ≤ P D false :=
    le_P_of_no_lift D (B_le_normalizer_U D) false
      (mi_true_not_mem_normalizer D le_rfl (D.root_le_U le_rfl (by omega)))
  exact fun _ hx => D.rank2.pgen_inter true (h1 hx) (h2 hx)

theorem normalizer_Uplus (i : Bool) : Subgroup.normalizer (Uplus D i : Set X) = P D i := by
  refine le_antisymm ?_ (P_le_normalizer_Uplus D i)
  apply le_P_of_no_lift D ((B_le_P D i).trans (P_le_normalizer_Uplus D i)) i
  cases i
  · exact mi_true_not_mem_normalizer D (Uplus_le_U D false) (root_le_Uplus_false D)
  · exact mi_false_not_mem_normalizer D (Uplus_le_U D true) (root_le_Uplus_true D)

theorem Uplus_ne_bot (i : Bool) : Uplus D i ≠ ⊥ := by
  have hn := D.three_le
  cases i
  · intro h
    exact D.roots.ne_bot 1 ⟨by norm_num, by simp; omega⟩
      (le_bot_iff.1 (h ▸ root_le_Uplus_false D))
  · intro h
    exact D.roots.ne_bot n ⟨by omega, by simp⟩ (le_bot_iff.1 (h ▸ root_le_Uplus_true D))

end Normalizers

section SylowNormalizers

variable [Finite X]

theorem normalizer_Q (hU : IsSylowTwoOf D.U ⊤) (i : Bool) :
    Subgroup.normalizer (Q D i : Set X) = P D i := by
  rw [Q_eq_Uplus D hU i]
  exact normalizer_Uplus D i

theorem pCoreOf_normalizer_Q (hU : IsSylowTwoOf D.U ⊤) (i : Bool) :
    pCoreOf 2 (Subgroup.normalizer (Q D i : Set X)) = Q D i := by
  rw [normalizer_Q D hU i]
  rfl

theorem Q_ne_bot (hU : IsSylowTwoOf D.U ⊤) (i : Bool) : Q D i ≠ ⊥ := by
  rw [Q_eq_Uplus D hU i]
  exact Uplus_ne_bot D i

end SylowNormalizers

end CFSG.Quasithin.H13.F431.BN
