module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBSec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open TableBExcTwo (reflHom reflHom_mulSingle reflHom_ofAdd reflCoeff reflCoeff_apply
  reflCoeff_single)
open TableBExcTwoTB (nW nW_mem wAct map_conj_nW_rootSL2_range rootSL2_range_neg
  rootSL2_eq_of_order_three S0_inv_eq_sq two_eq_zero_of_card_two zmod3_val_one zmod3_val_two
  zmod3_mul_self_of_ne_zero zmod3_two_ne_zero zmod3_two_mul_eq_zero)

namespace TableBF4TwoTB

section Torus

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def tGen (i : Fin 4) : adjointGroup .F4 K :=
  TableBF4Two.rho K i (uSL 1 * vSL 1)

theorem tGen_pow_three (i : Fin 4) : tGen K i ^ 3 = 1 := by
  rw [tGen, ← map_pow, TableBF4Two.S0_pow_three CharTwo.two_eq_zero, map_one]

theorem tGen_ne_one (i : Fin 4) : tGen K i ≠ 1 := fun h =>
  TableBF4Two.S0_ne_one (K := K) CharTwo.two_eq_zero
    (TableBF4Two.rho_injective i (h.trans (map_one _).symm))

variable (K) in
@[expose] noncomputable def tC (i : Fin 4) :
    Multiplicative (ZMod 3) →* adjointGroup .F4 K :=
  TableBSymp.zmodPowHom (tGen_pow_three (K := K) i)

theorem tC_apply (i : Fin 4) (a : Multiplicative (ZMod 3)) :
    tC K i a = tGen K i ^ (Multiplicative.toAdd a).val := by
  rw [tC, TableBSymp.zmodPowHom_apply]

theorem tC_apply_rho (i : Fin 4) (a : Multiplicative (ZMod 3)) :
    tC K i a = TableBF4Two.rho K i ((uSL 1 * vSL 1) ^ (Multiplicative.toAdd a).val) := by
  rw [tC_apply, tGen, map_pow]

theorem tC_one (i : Fin 4) :
    tC K i (Multiplicative.ofAdd 1) = tGen K i := by
  rw [tC_apply, zmod3_val_one, pow_one]

theorem tC_injective (i : Fin 4) : Function.Injective (tC K i) := by
  have := Fact.mk Nat.prime_three
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [tC_apply] at ha
  have hd := orderOf_dvd_of_pow_eq_one ha
  rw [orderOf_eq_prime (tGen_pow_three (K := K) i) (tGen_ne_one (K := K) i)] at hd
  have hlt := ZMod.val_lt (Multiplicative.toAdd a)
  have h0 : (Multiplicative.toAdd a).val = 0 := by omega
  rw [ZMod.val_eq_zero] at h0
  rw [← ofAdd_toAdd a, h0, ofAdd_zero]

theorem tC_commute :
    Pairwise fun i j : Fin 4 => ∀ a b, Commute (tC K i a) (tC K j b) := by
  intro i j hij a b
  rw [tC_apply_rho, tC_apply_rho]
  exact TableBF4Two.commute_rho hij _ _

variable (K) in
@[expose] noncomputable def tD :
    (Fin 4 → Multiplicative (ZMod 3)) →* adjointGroup .F4 K :=
  MonoidHom.noncommPiCoprod (tC K) tC_commute

theorem tC_iSupIndep : iSupIndep fun i => (tC K i).range := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  have hle : (⨆ (j) (_ : j ≠ i), (tC K j).range) ≤
      Subgroup.centralizer {TableBF4Two.rho K i (uSL 1)} := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, tC_apply_rho]
    exact (TableBF4Two.commute_rho hj _ _).eq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx')
  rw [tC_apply_rho, ← map_mul, ← map_mul] at hc
  have hc' := TableBF4Two.rho_injective _ hc
  by_contra hne
  have hval : (Multiplicative.toAdd a).val ≠ 0 := by
    intro h0
    apply hne
    rw [tC_apply_rho, h0, pow_zero, map_one]
  exact TableBF4Two.S0_pow_mul_uSL_ne CharTwo.two_eq_zero (ZMod.val_lt _) hval hc'

theorem tD_injective : Function.Injective (tD K) :=
  MonoidHom.injective_noncommPiCoprod_of_iSupIndep (tC K) tC_iSupIndep tC_injective

variable (K) in
@[expose] noncomputable def tE :
    Multiplicative (Fin 4 → ZMod 3) →* adjointGroup .F4 K :=
  (tD K).comp (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 3).toMonoidHom

theorem tE_apply (v : Fin 4 → ZMod 3) :
    tE K (Multiplicative.ofAdd v) = tD K fun j => Multiplicative.ofAdd (v j) :=
  rfl

theorem tE_injective : Function.Injective (tE K) := fun _ _ h =>
  (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 3).injective (tD_injective (K := K) h)

theorem tE_range : (tE K).range = (tD K).range := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 3).symm f, ?_⟩
    rw [tE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem tE_single (i : Fin 4) (c : ZMod 3) :
    tE K (Multiplicative.ofAdd (Pi.single i c)) = tC K i (Multiplicative.ofAdd c) := by
  rw [tE_apply, tD]
  have h : (fun j => Multiplicative.ofAdd ((Pi.single i c : Fin 4 → ZMod 3) j)) =
      Pi.mulSingle i (Multiplicative.ofAdd c) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [h, MonoidHom.noncommPiCoprod_mulSingle]

variable (K) in
@[expose] noncomputable def nGen (i : Fin 4) : adjointGroup .F4 K :=
  TableBF4Two.rho K i WSL

theorem nGen_conj_tC (i j : Fin 4) (a : Multiplicative (ZMod 3)) :
    nGen K i * tC K j a * (nGen K i)⁻¹ = tC K j (if j = i then a⁻¹ else a) := by
  split_ifs with hji
  · subst hji
    rw [show tC K j a⁻¹ = (tC K j a)⁻¹ from map_inv _ a, tC_apply_rho, nGen, ← map_inv,
      ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [← conj_pow, TableBF4Two.W_S0_W CharTwo.two_eq_zero, inv_pow]
  · rw [tC_apply_rho, nGen, (TableBF4Two.commute_rho (Ne.symm hji) WSL _).eq,
      mul_inv_cancel_right]

theorem nGen_conj_tD (i : Fin 4)
    (f : Fin 4 → Multiplicative (ZMod 3)) :
    nGen K i * tD K f * (nGen K i)⁻¹ = tD K (reflHom i f) := by
  have h : (MulAut.conj (nGen K i)).toMonoidHom.comp (tD K) =
      (tD K).comp (reflHom i) := MonoidHom.pi_ext fun j a => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tD,
      MonoidHom.noncommPiCoprod_mulSingle, reflHom_mulSingle]
    exact nGen_conj_tC i j a
  have h1 := congrArg (fun φ => φ f) h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1

theorem nGen_conj_tE (i : Fin 4) (v : Fin 4 → ZMod 3) :
    nGen K i * tE K (Multiplicative.ofAdd v) * (nGen K i)⁻¹ =
      tE K (Multiplicative.ofAdd (v - reflCoeff i v • Pi.single i 1)) := by
  rw [tE_apply, tE_apply, nGen_conj_tD, reflHom_ofAdd]

theorem smul_single_one4 (i : Fin 4) (c : ZMod 3) :
    c • (Pi.single i 1 : Fin 4 → ZMod 3) = Pi.single i c := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

theorem piTorus_tE : TableBF4.piTorus (tE K) = tD K := by
  refine MonoidHom.ext fun f => ?_
  rw [TableBF4.piTorus_apply, tE_apply]
  congr 1

theorem tD_section {L' : Type} [Group L'] {ψ : L' →* adjointGroup .F4 K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') :
    ∃ σ : (Fin 4 → Multiplicative (ZMod 3)) →* L', ψ.comp σ = tD K := by
  have hcomm : ∀ x ∈ (TableBF4.piTorus (tE K)).range.comap ψ,
      ∀ y ∈ (TableBF4.piTorus (tE K)).range.comap ψ, x * y = y * x := by
    rw [TableBF4.range_piTorus]
    exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker Nat.prime_three
      (by norm_num) (tE K) reflCoeff reflCoeff_single (nGen K) nGen_conj_tE
  have hinv : ∀ i : Fin 4, ∃ w : adjointGroup .F4 K,
      w * TableBSymp.torusBasis (TableBF4.piTorus (tE K)) i * w⁻¹ =
        (TableBSymp.torusBasis (TableBF4.piTorus (tE K)) i)⁻¹ := by
    intro i
    refine ⟨nGen K i, ?_⟩
    rw [TableBF4.torusBasis_piTorus, nGen_conj_tE, reflCoeff_single, ← map_inv, ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  obtain ⟨σ, hσ⟩ := TableBF4.exists_torus_section_of_comm hψ hker (by decide : Odd 3)
    (TableBF4.piTorus (tE K)) hcomm hinv
  exact ⟨σ, by rw [hσ, piTorus_tE]⟩

end Torus

section Frame

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def nWA4 (w : List (Fin Tag.F4.rank)) : adjointGroup .F4 K :=
  ⟨nW .F4 K w, nW_mem .F4 K w⟩

@[expose] def PermutesFrame (w : List (Fin Tag.F4.rank))
    (π : Fin 4 → Fin 4) : Prop :=
  ∀ a, wAct .F4 w (TableBF4Two.orthRoot a) = TableBF4Two.orthRoot (π a) ∨
    wAct .F4 w (TableBF4Two.orthRoot a) = -TableBF4Two.orthRoot (π a)

theorem conj_nWA_tGen (hK : Nat.card K = 2) {w : List (Fin Tag.F4.rank)}
    {π : Fin 4 → Fin 4} (hπ : PermutesFrame w π) (a : Fin 4) :
    ∃ k : ZMod 3, k ≠ 0 ∧
      nWA4 K w * tGen K a * (nWA4 K w)⁻¹ = tC K (π a) (Multiplicative.ofAdd k) := by
  set g := nWA4 K w with hg
  set x : adjointGroup .F4 K := g * tGen K a * g⁻¹ with hx
  have hcoe : (x : ModGL .F4 K) = nW .F4 K w * (tGen K a : ModGL .F4 K) * (nW .F4 K w)⁻¹ := by
    rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hmem1 : (tGen K a : ModGL .F4 K) ∈ (rootSL2 .F4 K (TableBF4Two.orthRoot a)).range :=
    ⟨uSL 1 * vSL 1, rfl⟩
  have hmem2 : nW .F4 K w * (tGen K a : ModGL .F4 K) * (nW .F4 K w)⁻¹ ∈
      (rootSL2 .F4 K (wAct .F4 w (TableBF4Two.orthRoot a))).range := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (nW .F4 K w)).toMonoidHom hmem1
    rw [map_conj_nW_rootSL2_range .F4 K w (TableBF4Two.isRoot_orthRoot a)] at h
    exact h
  have hkey : (rootSL2 .F4 K (wAct .F4 w (TableBF4Two.orthRoot a))).range =
      (rootSL2 .F4 K (TableBF4Two.orthRoot (π a))).range := by
    rcases hπ a with h | h
    · rw [h]
    · rw [h]
      exact rootSL2_range_neg .F4 K (TableBF4Two.isRoot_orthRoot (π a))
  have hmem : (x : ModGL .F4 K) ∈ (rootSL2 .F4 K (TableBF4Two.orthRoot (π a))).range := by
    rw [hcoe, ← hkey]
    exact hmem2
  have hx3 : x ^ 3 = 1 := by
    rw [hx, conj_pow, tGen_pow_three, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    intro h
    apply tGen_ne_one (K := K) a
    rw [hx] at h
    calc tGen K a = g⁻¹ * (g * tGen K a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have h3 : (x : ModGL .F4 K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  have hx1' : (x : ModGL .F4 K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases rootSL2_eq_of_order_three .F4 K hK (TableBF4Two.isRoot_orthRoot (π a)) hmem h3 hx1' with
    h | h
  · refine ⟨1, one_ne_zero, ?_⟩
    apply Subtype.ext
    rw [h, tC_one]
    rfl
  · refine ⟨2, by decide, ?_⟩
    apply Subtype.ext
    rw [h, S0_inv_eq_sq (two_eq_zero_of_card_two hK), map_pow, tC_apply, zmod3_val_two,
      Subgroup.coe_pow]
    rfl

theorem conj_nWA_tC (hK : Nat.card K = 2) {w : List (Fin Tag.F4.rank)}
    {π : Fin 4 → Fin 4} (hπ : PermutesFrame w π) (a : Fin 4) :
    ∃ k : ZMod 3, k ≠ 0 ∧ ∀ x : Multiplicative (ZMod 3),
      nWA4 K w * tC K a x * (nWA4 K w)⁻¹ =
        tC K (π a) (Multiplicative.ofAdd (Multiplicative.toAdd x * k)) := by
  obtain ⟨k, hk0, hk⟩ := conj_nWA_tGen hK hπ a
  refine ⟨k, hk0, fun x => ?_⟩
  rw [tC_apply, ← conj_pow, hk, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

variable (K) in
def frameWeyl (w₁ w₂ : List (Fin Tag.F4.rank)) : Set (adjointGroup .F4 K) :=
  {x | (∃ i, x = nGen K i) ∨ x = nWA4 K w₁ ∨ x = nWA4 K w₂}

theorem tC_mem_tE (a : Fin 4) (x : Multiplicative (ZMod 3)) :
    tC K a x ∈ (tE K).range :=
  ⟨Multiplicative.ofAdd (Pi.single a (Multiplicative.toAdd x)), by
    rw [tE_single, ofAdd_toAdd]⟩

theorem map_conj_tE_le (g : adjointGroup .F4 K) (π : Fin 4 → Fin 4)
    (h : ∀ (a : Fin 4) (x : Multiplicative (ZMod 3)), ∃ y, g * tC K a x * g⁻¹ =
      tC K (π a) y) :
    (tE K).range.map (MulAut.conj g).toMonoidHom ≤ (tE K).range := by
  rw [tE_range, tD, MonoidHom.noncommPiCoprod_range, Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rintro _ ⟨z, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h a x
  show g * tC K a x * g⁻¹ ∈ _
  rw [hy]
  exact (le_iSup (fun i => (tC K i).range) (π a)) ⟨y, rfl⟩

theorem tGen_mem_of_tC_mem {a : Fin 4}
    {E' : Subgroup (adjointGroup .F4 K)} {k : ZMod 3} (hk : k ≠ 0)
    (h : tC K a (Multiplicative.ofAdd k) ∈ E') : tGen K a ∈ E' := by
  have h1 : tC K a (Multiplicative.ofAdd k) ^ k.val = tGen K a := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val,
      zmod3_mul_self_of_ne_zero k hk]
    exact tC_one a
  rw [← h1]
  exact E'.pow_mem h _

theorem irreducible_frame (hK : Nat.card K = 2) {w₁ w₂ : List (Fin Tag.F4.rank)}
    {π₁ π₂ : Fin 4 → Fin 4} (h₁ : PermutesFrame w₁ π₁)
    (h₂ : PermutesFrame w₂ π₂)
    (htrans : ∀ S : Finset (Fin 4), S.Nonempty → (∀ a ∈ S, π₁ a ∈ S) →
      (∀ a ∈ S, π₂ a ∈ S) → S = Finset.univ)
    (E' : Subgroup (adjointGroup .F4 K)) (hle : E' ≤ (tE K).range)
    (hinv : ∀ x ∈ frameWeyl K w₁ w₂, ∀ e ∈ E', x * e * x⁻¹ ∈ E') :
    E' = ⊥ ∨ E' = (tE K).range := by
  classical
  by_cases hbot : E' = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E', x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  obtain ⟨v, rfl⟩ : ∃ v : Fin 4 → ZMod 3, tE K (Multiplicative.ofAdd v) = x := by
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hle hxE)
    exact ⟨Multiplicative.toAdd g, by rw [ofAdd_toAdd, hg]⟩
  have hi : ∃ i, v i ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hx1
    have hv0 : v = 0 := funext hne
    rw [hv0, ofAdd_zero, map_one]
  obtain ⟨i, hi⟩ := hi
  have hc := hinv (nGen K i) (Or.inl ⟨i, rfl⟩) _ hxE
  rw [nGen_conj_tE] at hc
  have hy : tE K (Multiplicative.ofAdd v) *
      (tE K (Multiplicative.ofAdd (v - reflCoeff i v • Pi.single i 1)))⁻¹ =
      tC K i (Multiplicative.ofAdd (reflCoeff i v)) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, ← tE_single]
    congr 2
    rw [smul_single_one4]
    abel
  have hc' : tC K i (Multiplicative.ofAdd (reflCoeff i v)) ∈ E' := by
    rw [← hy]
    exact E'.mul_mem hxE (E'.inv_mem hc)
  have hcne : reflCoeff i v ≠ 0 := by
    rw [reflCoeff_apply]
    exact mul_ne_zero zmod3_two_ne_zero hi
  have hS1 : tGen K i ∈ E' := tGen_mem_of_tC_mem hcne hc'
  have hcl₁ : ∀ a, tGen K a ∈ E' → tGen K (π₁ a) ∈ E' := by
    intro a ha
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tGen hK h₁ a
    have hm := hinv (nWA4 K w₁) (Or.inr (Or.inl rfl)) _ ha
    rw [hk] at hm
    exact tGen_mem_of_tC_mem hk0 hm
  have hcl₂ : ∀ a, tGen K a ∈ E' → tGen K (π₂ a) ∈ E' := by
    intro a ha
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tGen hK h₂ a
    have hm := hinv (nWA4 K w₂) (Or.inr (Or.inr rfl)) _ ha
    rw [hk] at hm
    exact tGen_mem_of_tC_mem hk0 hm
  have hS : Finset.univ.filter (fun a => tGen K a ∈ E') = Finset.univ := by
    apply htrans
    · exact ⟨i, by simp [hS1]⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact hcl₁ a ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact hcl₂ a ha
  have hall : ∀ a, tGen K a ∈ E' := by
    intro a
    have : a ∈ Finset.univ.filter (fun a => tGen K a ∈ E') := by
      rw [hS]
      exact Finset.mem_univ a
    exact (Finset.mem_filter.mp this).2
  refine le_antisymm hle ?_
  rw [tE_range, tD, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  rw [tC_apply]
  exact E'.pow_mem (hall a) _

theorem schur_frame (hK : Nat.card K = 2) {w₁ w₂ : List (Fin Tag.F4.rank)}
    {π₁ π₂ : Fin 4 → Fin 4} (h₁ : PermutesFrame w₁ π₁)
    (h₂ : PermutesFrame w₂ π₂)
    (htrans : ∀ S : Finset (Fin 4), S.Nonempty → (∀ a ∈ S, π₁ a ∈ S) →
      (∀ a ∈ S, π₂ a ∈ S) → S = Finset.univ)
    (G : adjointGroup .F4 K → adjointGroup .F4 K)
    (hGE : ∀ e ∈ (tE K).range, G e ∈ (tE K).range)
    (hGmul : ∀ e ∈ (tE K).range, ∀ e' ∈ (tE K).range, G (e * e') = G e * G e')
    (hGW : ∀ x ∈ frameWeyl K w₁ w₂, ∀ e ∈ (tE K).range, G (x * e * x⁻¹) = x * G e * x⁻¹) :
    ∃ c : ℕ, ∀ e ∈ (tE K).range, G e = e ^ c := by
  have hsurj : ∀ v : Fin 4 → ZMod 3, ∃ u : Fin 4 → ZMod 3,
      tE K (Multiplicative.ofAdd u) = G (tE K (Multiplicative.ofAdd v)) := by
    intro v
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hGE _ ⟨Multiplicative.ofAdd v, rfl⟩)
    exact ⟨Multiplicative.toAdd g, by rw [ofAdd_toAdd, hg]⟩
  choose fE hfE using hsurj
  have hadd : ∀ v w, fE (v + w) = fE v + fE w := by
    intro v w
    apply Multiplicative.ofAdd.injective
    apply tE_injective (K := K)
    rw [hfE, ofAdd_add v w, map_mul,
      hGmul (tE K (Multiplicative.ofAdd v)) ⟨_, rfl⟩ (tE K (Multiplicative.ofAdd w)) ⟨_, rfl⟩,
      ← hfE v, ← hfE w, ofAdd_add (fE v) (fE w), map_mul]
  let fA : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3) := AddMonoidHom.mk' fE hadd
  set c : Fin 4 → ZMod 3 := fun a => fE (Pi.single a 1) a with hc_def
  have hoff : ∀ a j, j ≠ a → fE (Pi.single a 1) j = 0 := by
    intro a j hja
    have hc0 : reflCoeff j (Pi.single a 1) = 0 := by
      rw [reflCoeff_apply, Pi.single_eq_of_ne hja, mul_zero]
    have hfix : nGen K j * tE K (Multiplicative.ofAdd (Pi.single a 1)) * (nGen K j)⁻¹ =
        tE K (Multiplicative.ofAdd (Pi.single a 1)) := by
      rw [nGen_conj_tE, hc0]
      simp
    have hG := hGW (nGen K j) (Or.inl ⟨j, rfl⟩) (tE K (Multiplicative.ofAdd (Pi.single a 1)))
      ⟨_, rfl⟩
    rw [hfix, ← hfE (Pi.single a 1), nGen_conj_tE] at hG
    have hinj := Multiplicative.ofAdd.injective (tE_injective hG)
    have hj := congrFun hinj j
    simp only [Pi.sub_apply, Pi.smul_apply, reflCoeff_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at hj
    apply zmod3_two_mul_eq_zero
    linear_combination hj
  have hdiag : ∀ a, fE (Pi.single a 1) = Pi.single a (c a) := by
    intro a
    funext j
    by_cases hj : j = a
    · subst hj
      simp [hc_def]
    · rw [hoff a j hj, Pi.single_eq_of_ne hj]
  have hsc : ∀ a (y : ZMod 3), fE (Pi.single a y) = Pi.single a (c a * y) := by
    intro a y
    have hsmul : y • (Pi.single a 1 : Fin 4 → ZMod 3) = y.val • Pi.single a 1 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    have hy2 : fE (Pi.single a y) = y.val • fE (Pi.single a 1) := by
      rw [← smul_single_one4 a y, hsmul]
      exact map_nsmul fA _ _
    rw [hy2, hdiag a]
    funext j
    by_cases hj : j = a
    · subst hj
      simp [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
    · simp [Pi.single_eq_of_ne hj]
  have hfull : ∀ v : Fin 4 → ZMod 3, fE v = fun j => c j * v j := by
    intro v
    have hsum : fE v = ∑ j, fE (Pi.single j (v j)) := by
      have hv : v = ∑ j, Pi.single j (v j) := (Finset.univ_sum_single v).symm
      calc fE v = fA v := rfl
        _ = fA (∑ j, Pi.single j (v j)) := by rw [← hv]
        _ = ∑ j, fA (Pi.single j (v j)) := map_sum fA _ _
        _ = ∑ j, fE (Pi.single j (v j)) := rfl
    funext k
    rw [hsum, Finset.sum_apply]
    simp only [hsc]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      simp [Pi.single_eq_of_ne (Ne.symm hjk)]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hG_tC : ∀ (b : Fin 4) (y : ZMod 3),
      G (tC K b (Multiplicative.ofAdd y)) = tC K b (Multiplicative.ofAdd (c b * y)) := by
    intro b y
    rw [← tE_single, ← hfE, hsc, tE_single]
  have hperm₁ : ∀ a, c (π₁ a) = c a := by
    intro a
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tC hK h₁ a
    have hm := hGW (nWA4 K w₁) (Or.inr (Or.inl rfl)) (tC K a (Multiplicative.ofAdd 1))
      (tC_mem_tE a _)
    rw [hk (Multiplicative.ofAdd 1), hG_tC, hG_tC, hk (Multiplicative.ofAdd (c a * 1))] at hm
    have h := Multiplicative.ofAdd.injective (tC_injective (π₁ a) hm)
    simp only [toAdd_ofAdd, mul_one, one_mul] at h
    exact mul_right_cancel₀ hk0 h
  have hperm₂ : ∀ a, c (π₂ a) = c a := by
    intro a
    obtain ⟨k, hk0, hk⟩ := conj_nWA_tC hK h₂ a
    have hm := hGW (nWA4 K w₂) (Or.inr (Or.inr rfl)) (tC K a (Multiplicative.ofAdd 1))
      (tC_mem_tE a _)
    rw [hk (Multiplicative.ofAdd 1), hG_tC, hG_tC, hk (Multiplicative.ofAdd (c a * 1))] at hm
    have h := Multiplicative.ofAdd.injective (tC_injective (π₂ a) hm)
    simp only [toAdd_ofAdd, mul_one, one_mul] at h
    exact mul_right_cancel₀ hk0 h
  have hconst : ∀ a, c a = c 0 := by
    intro a
    have hS : Finset.univ.filter (fun b => c b = c 0) = Finset.univ := by
      apply htrans
      · exact ⟨0, by simp⟩
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        rw [hperm₁ b, hb]
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        rw [hperm₂ b, hb]
    have : a ∈ Finset.univ.filter (fun b => c b = c 0) := by
      rw [hS]
      exact Finset.mem_univ a
    exact (Finset.mem_filter.mp this).2
  refine ⟨(c 0).val, ?_⟩
  have hv : ∀ v : Fin 4 → ZMod 3,
      G (tE K (Multiplicative.ofAdd v)) = tE K (Multiplicative.ofAdd v) ^ (c 0).val := by
    intro v
    have e1 : (fun j => c j * v j) = (c 0).val • v := by
      funext j
      rw [hconst j, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [← hfE v, hfull v, e1, ← map_pow, ← ofAdd_nsmul]
  rintro _ ⟨g, rfl⟩
  have := hv (Multiplicative.toAdd g)
  rw [ofAdd_toAdd] at this
  exact this

theorem secEltAt_frame (hK : Nat.card K = 2) {w₁ w₂ : List (Fin Tag.F4.rank)}
    {π₁ π₂ : Fin 4 → Fin 4} (h₁ : PermutesFrame w₁ π₁)
    (h₂ : PermutesFrame w₂ π₂)
    (htrans : ∀ S : Finset (Fin 4), S.Nonempty → (∀ a ∈ S, π₁ a ∈ S) →
      (∀ a ∈ S, π₂ a ∈ S) → S = Finset.univ) :
    E6TwoTB.SecEltAt 3 (tE K).range := by
  refine ⟨4, TableBF4.piTorus (tE K), frameWeyl K w₁ w₂,
    TableBF4.range_piTorus _, ?_, ?_, ?_, ?_, ?_⟩
  · intro L' _ ψ hψ hker
    obtain ⟨σ, hσ⟩ := tD_section hψ hker
    exact ⟨σ, by rw [hσ, piTorus_tE]⟩
  · rintro x (⟨i, rfl⟩ | rfl | rfl) e he
    · have hm := map_conj_tE_le (K := K) (nGen K i) id
        (fun a y => ⟨_, nGen_conj_tC i a y⟩)
      exact hm ⟨e, he, rfl⟩
    · have hm := map_conj_tE_le (K := K) (nWA4 K w₁) π₁ (fun a y => by
        obtain ⟨k, -, hk⟩ := conj_nWA_tC hK h₁ a
        exact ⟨_, hk y⟩)
      exact hm ⟨e, he, rfl⟩
    · have hm := map_conj_tE_le (K := K) (nWA4 K w₂) π₂ (fun a y => by
        obtain ⟨k, -, hk⟩ := conj_nWA_tC hK h₂ a
        exact ⟨_, hk y⟩)
      exact hm ⟨e, he, rfl⟩
  · intro E' hle hinv
    exact irreducible_frame hK h₁ h₂ htrans E' hle hinv
  · refine ⟨nGen K 0, Or.inl ⟨0, rfl⟩, tGen K 0,
      ⟨Multiplicative.ofAdd (Pi.single 0 1), by rw [tE_single, tC_one]⟩, ?_⟩
    intro h
    rw [← tC_one 0, nGen_conj_tC, if_pos rfl] at h
    have h2 := tC_injective 0 h
    exact absurd h2 (by decide)
  · intro G hGE hGmul hGW
    exact schur_frame hK h₁ h₂ htrans G hGE hGmul hGW

end Frame

def wordA : List (Fin 4) := [2]

def permA : Fin 4 → Fin 4 := ![1, 0, 2, 3]

def wordB : List (Fin 4) := [0, 1, 2, 3, 1, 2, 0]

def permB : Fin 4 → Fin 4 := ![3, 0, 1, 2]

theorem permA_root : ∀ a : Fin 4, wAct .F4 wordA (TableBF4Two.orthRoot a) =
    TableBF4Two.orthRoot (permA a) ∨
      wAct .F4 wordA (TableBF4Two.orthRoot a) = -TableBF4Two.orthRoot (permA a) := by
  decide +kernel

theorem permB_root : ∀ a : Fin 4, wAct .F4 wordB (TableBF4Two.orthRoot a) =
    TableBF4Two.orthRoot (permB a) ∨
      wAct .F4 wordB (TableBF4Two.orthRoot a) = -TableBF4Two.orthRoot (permB a) := by
  decide +kernel

theorem htrans_F4 : ∀ S : Finset (Fin 4), S.Nonempty → (∀ a ∈ S, permA a ∈ S) →
    (∀ a ∈ S, permB a ∈ S) → S = Finset.univ := by
  decide +kernel

section Frames

theorem permutesFrame_A : PermutesFrame wordA permA := fun a => permA_root a

theorem permutesFrame_B : PermutesFrame wordB permB := fun a => permB_root a

theorem secEltAt_F4 {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) :
    E6TwoTB.SecEltAt 3 (tE K).range :=
  secEltAt_frame hK permutesFrame_A permutesFrame_B htrans_F4

end Frames

end TableBF4TwoTB

end CFSG.StandardType

end
