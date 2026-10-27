module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3A2
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.SzF53B3A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem vtype_nbr_of_true {α β : Geo H M} (h : β ∈ nbrs α) (hα : vtype α = true) :
    vtype β = false := by
  have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj α β from h)
  cases hβ : vtype β
  · rfl
  · exact absurd (hα.trans hβ.symm) this

omit [Finite G] in
theorem exists_gen_of_card_two {K : Subgroup G} (h : Nat.card K = 2) :
    ∃ z ∈ K, z ≠ 1 ∧ ∀ w ∈ K, w = 1 ∨ w = z := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).mp h
  refine ⟨(y : G), y.2, fun h1 => hy (Subtype.ext h1), fun w hw => ?_⟩
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  · refine Or.inr ?_
    have : (⟨w, hw⟩ : ↥K) = y := huniq _ (fun h1 => hw1 (congrArg Subtype.val h1))
    exact congrArg Subtype.val this

theorem Zv_eq_omegaOneCenter_true (hB : B3Base H M S) {α β : Geo H M} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) : Zv β = quasithinOmegaOneCenter (stab α ⊓ stab β) := by
  have := (Zv_eq_omegaOneCenter_inf hB.amalgam
    (show α ∈ nbrs β from (show (graph (H ⊔ M) H M).Adj α β from hβ).symm)
    (hB.central β (vtype_nbr_of_true hβ hα))).1
  rwa [inf_comm] at this

theorem Zv_eq_Vn (hB : B3Base H M S) {α : Geo H M} (hα : vtype α = true) : Zv α = Vn α := by
  have hA := hB.amalgam
  obtain ⟨β, hβ⟩ := exists_adj α
  have hβn : β ∈ nbrs α := hβ
  apply le_antisymm
  · rw [Zv_eq_conjClosure (sylow_stab_inf_left hA hβn)]
    refine conjClosure_le fun h hh z hz => ?_
    have hz' : z ∈ Zv β := by
      rw [Zv_eq_omegaOneCenter_true hB hα hβn]
      exact hz
    have hzV : z ∈ Vn α :=
      le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs α) => Zv μ) β hβn le_rfl hz'
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn α hh) z).mp hzV
  · refine iSup₂_le fun μ hμ => ?_
    exact zv_le_zv_of_adj hB (vtype_nbr_of_true hμ hα) (show (graph (H ⊔ M) H M).Adj μ α from
      (show (graph (H ⊔ M) H M).Adj α μ from hμ).symm)

theorem Zv_ne_of_ne (hB : B3Base H M S) {α β δ : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) (hβ : β ∈ nbrs α) (hδ : δ ∈ nbrs α) : Zv β ≠ Zv δ := by
  intro heq
  have hA := hB.amalgam
  have hαβ : (graph (H ⊔ M) H M).Adj α β := hβ
  have hU : Zv β ≤ stab α ⊓ stab β :=
    le_inf ((Zv_le_Qv hA β).trans (Qv_le_stab_of_mem_nbrs hA (show α ∈ nbrs β from hαβ.symm)))
      ((Zv_le_Qv hA β).trans (pCoreOf_le 2 _))
  have hnβ : stab β ≤ Subgroup.normalizer (Zv β : Set G) := stab_le_normalizer_Zv hA β
  have hnδ : stab δ ≤ Subgroup.normalizer (Zv β : Set G) := heq ▸ stab_le_normalizer_Zv hA δ
  have hnα : stab α ≤ Subgroup.normalizer (Zv β : Set G) := by
    rw [stab_eq_sup_inf hA hα hβδ hβ hδ]
    exact sup_le (inf_le_right.trans hnβ) (inf_le_right.trans hnδ)
  exact Zv_ne_bot hA β (eq_bot_of_normalizes_both hA hαβ hU hnα hnβ)

omit [Finite G] in
theorem card_sup_of_commute_disjoint {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hdisj : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm' : ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) :=
    fun m n => hcomm m.1 m.2 n.1 n.2
  let φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm'
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hdisj
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Finite G] in
theorem mul_eq_of_perm {a b c a' b' c' : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (h1 : a' = a ∨ a' = b ∨ a' = c) (h2 : b' = a ∨ b' = b ∨ b' = c)
    (h3 : c' = a ∨ c' = b ∨ c' = c) (n12 : a' ≠ b') (n13 : a' ≠ c') (n23 : b' ≠ c') :
    a' * b' * c' = a * b * c := by
  have e4 : b * c * a = a * b * c := by
    rw [mul_assoc, ← hac, ← mul_assoc, ← hab]
  have e5 : c * a * b = a * b * c := by
    rw [← hac, mul_assoc, ← hbc, ← mul_assoc]
  have e6 : c * b * a = a * b * c := by
    rw [← hbc, mul_assoc, ← hac, ← mul_assoc, ← hab]
  have e2 : a * c * b = a * b * c := by
    rw [mul_assoc, ← hbc, ← mul_assoc]
  have e3 : b * a * c = a * b * c := by
    rw [← hab]
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    rcases h3 with rfl | rfl | rfl <;>
    first
    | exact absurd rfl n12
    | exact absurd rfl n13
    | exact absurd rfl n23
    | rfl
    | exact e2
    | exact e3
    | exact e4
    | exact e5
    | exact e6

omit [Finite G] in
theorem ne_of_gen_ne {K L : Subgroup G} {a b : G} (hb : b ∈ L) (ha : a ∈ K)
    (hau : ∀ w ∈ K, w = 1 ∨ w = a) (hbu : ∀ w ∈ L, w = 1 ∨ w = b) (hKL : K ≠ L) : a ≠ b := by
  intro h
  apply hKL
  ext x
  constructor
  · intro hx
    rcases hau x hx with rfl | rfl
    · exact one_mem _
    · rw [h]
      exact hb
  · intro hx
    rcases hbu x hx with rfl | rfl
    · exact one_mem _
    · rw [← h]
      exact ha

omit [Finite G] in
theorem mul_comm_of_elemAbelian {K : Subgroup G} (h : IsElemAbelian 2 K) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : x * y = y * x := CFSG.Open.IsElemAbelian.comm h hx hy

theorem card_zv_true (hB : B3Base H M S) {α : Geo H M} (hα : vtype α = true) :
    Nat.card (Zv α) = 4 := by
  have hA := hB.amalgam
  obtain ⟨β, δ, ε, hβδ, hβε, hδε, hn⟩ := exists_three_nbrs hA hα
  have hβn : β ∈ nbrs α := by rw [hn]; simp
  have hδn : δ ∈ nbrs α := by rw [hn]; simp
  have hεn : ε ∈ nbrs α := by rw [hn]; simp
  have hβf := vtype_nbr_of_true hβn hα
  have hδf := vtype_nbr_of_true hδn hα
  have hεf := vtype_nbr_of_true hεn hα
  obtain ⟨a, haZ, ha1, hau⟩ := exists_gen_of_card_two (hB.card_two β hβf)
  obtain ⟨b, hbZ, hb1, hbu⟩ := exists_gen_of_card_two (hB.card_two δ hδf)
  obtain ⟨c, hcZ, hc1, hcu⟩ := exists_gen_of_card_two (hB.card_two ε hεf)
  have hadj : ∀ ν ∈ nbrs α, (graph (H ⊔ M) H M).Adj ν α := fun ν hν =>
    (show (graph (H ⊔ M) H M).Adj α ν from hν).symm
  have haα : a ∈ Zv α := zv_le_zv_of_adj hB hβf (hadj β hβn) haZ
  have hbα : b ∈ Zv α := zv_le_zv_of_adj hB hδf (hadj δ hδn) hbZ
  have hcα : c ∈ Zv α := zv_le_zv_of_adj hB hεf (hadj ε hεn) hcZ
  have hZα := isElemAbelian_Zv hA α
  have hab' : a ≠ b := ne_of_gen_ne hbZ haZ hau hbu (Zv_ne_of_ne hB hα hβδ hβn hδn)
  have hac' : a ≠ c := ne_of_gen_ne hcZ haZ hau hcu (Zv_ne_of_ne hB hα hβε hβn hεn)
  have hbc' : b ≠ c := ne_of_gen_ne hcZ hbZ hbu hcu (Zv_ne_of_ne hB hα hδε hδn hεn)
  have hcl : ∀ ν ∈ nbrs α, ∀ x ∈ Zv ν, x ≠ 1 → x = a ∨ x = b ∨ x = c := by
    intro ν hν x hx hx1
    rw [hn] at hν
    rcases hν with rfl | rfl | rfl
    · exact Or.inl ((hau x hx).resolve_left hx1)
    · exact Or.inr (Or.inl ((hbu x hx).resolve_left hx1))
    · exact Or.inr (Or.inr ((hcu x hx).resolve_left hx1))
  have hconj : ∀ g ∈ stab α, g * (a * b * c) * g⁻¹ = a * b * c := by
    intro g hg
    set g' : ↥(H ⊔ M) := ⟨g, stab_le α hg⟩ with hg'
    have hgα : g' • α = α := smul_eq_of_mem_stab hg
    have hnb : ∀ ν ∈ nbrs α, g' • ν ∈ nbrs α := fun ν hν => by
      have := (smul_adj g').mpr (show (graph (H ⊔ M) H M).Adj α ν from hν)
      rwa [hgα] at this
    have hcj : ∀ ν ∈ nbrs α, ∀ x ∈ Zv ν, x ≠ 1 →
        g * x * g⁻¹ = a ∨ g * x * g⁻¹ = b ∨ g * x * g⁻¹ = c := by
      intro ν hν x hx hx1
      refine hcl (g' • ν) (hnb ν hν) _ ?_ ?_
      · rw [Zv_smul]
        exact mul_mem_conjSub hx
      · intro h1
        apply hx1
        have := congrArg (fun y => g⁻¹ * y * g) h1
        simpa [mul_assoc] using this
    have cinj : ∀ x y : G, g * x * g⁻¹ = g * y * g⁻¹ → x = y := fun x y h =>
      mul_left_cancel (mul_right_cancel h)
    have e : g * (a * b * c) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by group
    rw [e]
    exact mul_eq_of_perm (mul_comm_of_elemAbelian hZα haα hbα) (mul_comm_of_elemAbelian hZα haα hcα)
      (mul_comm_of_elemAbelian hZα hbα hcα) (hcj β hβn a haZ ha1) (hcj δ hδn b hbZ hb1)
      (hcj ε hεn c hcZ hc1) (fun h => hab' (cinj _ _ h)) (fun h => hac' (cinj _ _ h))
      (fun h => hbc' (cinj _ _ h))
  have hPZ : a * b * c ∈ Zv α := (Zv α).mul_mem ((Zv α).mul_mem haα hbα) hcα
  have hPc : a * b * c ∈ centerOf (stab α) := by
    refine ⟨(Zv_le_Qv hA α).trans (pCoreOf_le 2 _) hPZ, ?_⟩
    show a * b * c ∈ Subgroup.centralizer (stab α : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    calc h * (a * b * c) = (h * (a * b * c) * h⁻¹) * h := by group
      _ = (a * b * c) * h := by rw [hconj h hh]
  have hP1 : a * b * c = 1 := by
    have h0 := centerOf_eq_bot_of_Zv_central hA (show α ∈ nbrs β from hadj β hβn)
      (hB.central β hβf)
    rw [h0] at hPc
    exact Subgroup.mem_bot.mp hPc
  have ha2 : a * a = 1 := by rw [← sq]; exact (hZα.2 a haα)
  have hb2 : b * b = 1 := by rw [← sq]; exact (hZα.2 b hbα)
  have hcab : c = a * b := by
    have h1 : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hP1
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
    exact (mul_comm_of_elemAbelian hZα haα hbα).symm
  have hsup : Zv α = Zv β ⊔ Zv δ := by
    apply le_antisymm
    · rw [Zv_eq_Vn hB hα]
      refine iSup₂_le fun ν hν => ?_
      have hν' := hν
      rw [hn] at hν'
      rcases hν' with rfl | rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
      · intro w hw
        rcases hcu w hw with rfl | rfl
        · exact one_mem _
        · rw [hcab]
          exact Subgroup.mul_mem_sup haZ hbZ
    · exact sup_le (zv_le_zv_of_adj hB hβf (hadj β hβn)) (zv_le_zv_of_adj hB hδf (hadj δ hδn))
  have hdisj : Zv β ⊓ Zv δ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hab' (((hau x hx.1).resolve_left hx1).symm.trans ((hbu x hx.2).resolve_left hx1))
  have hcomm : ∀ x ∈ Zv β, ∀ y ∈ Zv δ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_elemAbelian hZα (zv_le_zv_of_adj hB hβf (hadj β hβn) hx)
      (zv_le_zv_of_adj hB hδf (hadj δ hδn) hy)
  rw [hsup, card_sup_of_commute_disjoint hcomm hdisj, hB.card_two β hβf, hB.card_two δ hδf]

end F53B3

end CFSG.Quasithin
