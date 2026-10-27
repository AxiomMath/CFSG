module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BAlt
import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamCl
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Orbit
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L27
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinU42
import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310B
import CFSG.Quasithin.Background.RonanE114L2
import CFSG.GH74.GLS.C3.Layer1.St1P89Tools
import CFSG.Walter.TwoRank
import CFSG.Models.Transport
import CFSG.Models.Blueprint
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def SeitzFourExc (X : Type) [Group X] : Prop :=
  CFSG.Models.LieModel X .PSL 2 5 1 ∨ CFSG.Models.LieModel X .PSL 2 7 1 ∨
    CFSG.Models.LieModel X .PSL 2 3 2 ∨ CFSG.Models.LieModel X .PSp 2 3 1

@[expose] def SeitzFour (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L E : Subgroup G), L.Normal → IsSimpleGroup ↥L →
    (∃ a b : ↥L, a * b ≠ b * a) → P ↥L → centralizer (L : Set G) = ⊥ →
    IsElemAbelian 2 E → Nat.card E = 4 → ¬ (E ≤ L ∧ SeitzFourExc ↥L) →
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)) = L

theorem SeitzFourExc.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SeitzFourExc X) : SeitzFourExc Y := by
  rcases h with h | h | h | h
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr (Or.inl (h.of_mulEquiv e))
  · exact Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))
  · exact Or.inr (Or.inr (Or.inr (h.of_mulEquiv e)))

variable {G : Type} [Group G] [Finite G]

theorem centralizer_subgroupOf_fstar_eq_bot {H A M : Subgroup G} (h : Asc80BSetup H A M) :
    Subgroup.centralizer (((Fstar H).subgroupOf H : Subgroup ↥H) : Set ↥H) = ⊥ := by
  have heq : Subgroup.centralizer (((Fstar H).subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (H ⊓ Subgroup.centralizer (Fstar H : Set G)).subgroupOf H := by
    ext x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hcomm := hx ⟨f, fstar_le_group H hf⟩ (by exact hf)
      exact congrArg (fun t : ↥H => (t : G)) hcomm
    · intro hx y hy
      have hxcent : (x : G) ∈ Subgroup.centralizer (Fstar H : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxcent) (y : G) (Subgroup.mem_subgroupOf.mp hy)
  rw [heq, h.inf_centralizer]
  simp

theorem false_of_seitzFour {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], Nonempty (X ≃* Y) → P X → P Y)
    (hS : SeitzFour P) {H A M : Subgroup G} (h : Asc80BSetup H A M)
    (hs : IsSimpleGroup ↥(Fstar H)) (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a)
    (hPF : P ↥(Fstar H)) {A' : Subgroup G} (hAA' : A ≤ A') (hA'H : A' ≤ H)
    (hA' : IsElemAbelian 2 A') {E : Subgroup G} (hEA' : E ≤ A') (hE : IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) (hexc : ¬ (E ≤ Fstar H ∧ SeitzFourExc ↥(Fstar H))) : False := by
  let L : Subgroup ↥H := (Fstar H).subgroupOf H
  let E' : Subgroup ↥H := E.subgroupOf H
  let eL : ↥L ≃* ↥(Fstar H) := Subgroup.subgroupOfEquivOfLe (fstar_le_group H)
  have hEH : E ≤ H := hEA'.trans hA'H
  have : IsSimpleGroup ↥(Fstar H) := hs
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eL.symm a, eL.symm b, fun hc => hab (by simpa using congrArg eL hc)⟩
  have hE'4 : Nat.card E' = 4 := by
    rw [← hE4]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have hexc' : ¬ (E' ≤ L ∧ SeitzFourExc ↥L) := by
    rintro ⟨hle, hx⟩
    refine hexc ⟨fun x hx' => ?_, hx.of_mulEquiv eL⟩
    exact hle (show (⟨x, hEH hx'⟩ : ↥H) ∈ E' from hx')
  have hgen := hS L E' (normal_subgroupOf_fstar H) hLs hLnab (hP _ _ ⟨eL.symm⟩ hPF)
    (centralizer_subgroupOf_fstar_eq_bot h) (hE.subgroupOf H) hE'4 hexc'
  apply h.not_fstar_le
  intro f hf
  have hfL : (⟨f, fstar_le_group H hf⟩ : ↥H) ∈ L := hf
  rw [← hgen] at hfL
  have hle : (⨆ e ∈ E', ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set ↥H)) ≤ M.subgroupOf H := by
    refine iSup₂_le fun e heE => iSup_le fun he1 => ?_
    intro x hx
    obtain ⟨-, hxc⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf]
    set C : Subgroup G := H ⊓ centralizer ({(e : G)} : Set G)
    have heA' : (e : G) ∈ A' := hEA' heE
    have hAC : A ≤ C := by
      intro y hy
      refine Subgroup.mem_inf.mpr ⟨h.sec5.le_group hy, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hA'.1.is_comm.comm ⟨y, hAA' hy⟩ ⟨e, heA'⟩ |> congrArg Subtype.val)
    have hCH : C < H := by
      refine lt_of_le_of_ne inf_le_left fun hCeq => he1 ?_
      have hmem : (e : G) ∈ H ⊓ centralizer (Fstar H : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨e.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
        have hgC : g ∈ C := hCeq ▸ fstar_le_group H hg
        exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hgC).2)
      rw [h.inf_centralizer, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hCM : C ≤ M := h.le_of_lt C hAC hCH
    apply hCM
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
    exact congrArg Subtype.val hxc
  exact hle hfL

section Rank

variable {X : Type} [Group X] [Finite X]

open CFSG.LocalAnalysis.ComponentInitial

theorem four_le_card_of_maximal {L A : Subgroup X} (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hmax : ∀ B : Subgroup X, A ≤ B → IsElemAbelian 2 B → B = A) : 4 ≤ Nat.card A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hA2g : IsPGroup 2 A := IsElemAbelian.isPGroup hA
  obtain ⟨k, hk⟩ := hA2g.exists_card_eq
  have hk1 : k = 1 := by
    have hpos : k ≠ 0 := by
      rintro rfl
      exact hA1 ((Subgroup.card_eq_one).mp (by simpa using hk))
    rcases k with _ | _ | k
    · exact absurd rfl hpos
    · rfl
    · exfalso; rw [hk] at hlt
      have : 2 ^ 2 ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : (2:ℕ) ^ 2 = 4 := by norm_num
      omega
  rw [hk1, pow_one] at hk
  have hkey : ∀ u ∈ A, ∀ v ∈ A, u ≠ 1 → v ≠ 1 → u = v := by
    intro u hu v hv hu1 hv1
    obtain ⟨x, y, hxy, hU⟩ := Nat.card_eq_two_iff.mp hk
    have hmem : ∀ w : ↥A, w = x ∨ w = y := fun w => by
      have : w ∈ ({x, y} : Set ↥A) := hU ▸ Set.mem_univ w
      simpa using this
    have h1 := hmem 1
    have hu' := hmem ⟨u, hu⟩
    have hv' := hmem ⟨v, hv⟩
    have hne1 : ∀ w : ↥A, (w : X) ≠ 1 → w ≠ 1 := fun w hw h => hw (by rw [h]; rfl)
    have hu1' := hne1 ⟨u, hu⟩ hu1
    have hv1' := hne1 ⟨v, hv⟩ hv1
    have : (⟨u, hu⟩ : ↥A) = ⟨v, hv⟩ := by
      rcases h1 with h1 | h1 <;> rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
        first
        | exact hu'.trans hv'.symm
        | exact absurd (hu'.trans h1.symm) hu1'
        | exact absurd (hv'.trans h1.symm) hv1'
    simpa using congrArg Subtype.val this
  obtain ⟨⟨a, haA⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  have hcomm_mem : ∀ t : X, t ^ 2 = 1 → (∀ x ∈ A, x * t = t * x) → t ∈ A := by
    intro t ht htA
    have hB := isElemAbelian_sup_zpowers (G := X) hA ht htA
    have := hmax _ le_sup_left hB
    exact this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hA_el : ∀ x ∈ A, x = 1 ∨ x = (a : X) := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hkey x hx a haA hx1 ha1)
  have haP2 : (a : X) ^ 2 = 1 := hA.2 a haA
  obtain ⟨P, hAP⟩ := hA2g.exists_le_sylow
  have hinvP : ∀ t ∈ (P : Subgroup X), t ^ 2 = 1 → t ≠ 1 → t = a := by
    have haZ : ∀ y ∈ (P : Subgroup X), y * a = a * y := by
      have : Nontrivial ↥(P : Subgroup X) := by
        exact ⟨⟨⟨a, hAP haA⟩, 1, fun h => ha1 (by simpa using congrArg Subtype.val h)⟩⟩
      have hPg : IsPGroup 2 ↥(P : Subgroup X) := P.isPGroup'
      have := hPg.center_nontrivial
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(P : Subgroup X))) 2
        (by
          obtain ⟨m, hm⟩ := (hPg.to_subgroup (Subgroup.center ↥(P : Subgroup X))).exists_card_eq
          have h1 : 1 < Nat.card ↥(Subgroup.center ↥(P : Subgroup X)) :=
            Finite.one_lt_card_iff_nontrivial.mpr inferInstance
          rw [hm] at h1 ⊢
          have : m ≠ 0 := by rintro rfl; simp at h1
          exact dvd_pow_self 2 this)
      set zz : X := ((z : ↥(P : Subgroup X)) : X)
      have hz2 : zz ^ 2 = 1 := by
        have := pow_orderOf_eq_one z
        rw [hz] at this
        simpa [zz] using congrArg (fun w : ↥(Subgroup.center ↥(P : Subgroup X)) =>
          ((w : ↥(P : Subgroup X)) : X)) this
      have hz1 : zz ≠ 1 := by
        intro h
        have : z = 1 := Subtype.ext (Subtype.ext h)
        rw [this, orderOf_one] at hz
        exact absurd hz (by norm_num)
      have hzc : ∀ y ∈ (P : Subgroup X), y * zz = zz * y := by
        intro y hy
        have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
        exact congrArg Subtype.val this
      have hzA : zz ∈ A := hcomm_mem zz hz2 fun x hx => hzc x (hAP hx)
      have hza : zz = a := hkey zz hzA a haA hz1 ha1
      intro y hy
      rw [← hza]; exact hzc y hy
    intro t ht ht2 ht1
    have htA : t ∈ A := hcomm_mem t ht2 fun x hx => by
      rcases hA_el x hx with rfl | rfl
      · simp
      · exact (haZ t ht).symm
    exact hkey t htA a haA ht1 ha1
  have heven : Even (Nat.card ↥L) := by
    by_contra hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)
  have hrank := CFSG.Walter.two_le_twoRank ↥L hnab heven
  obtain ⟨u, -, v, -, hu, hv, huv, hc⟩ :=
    CFSG.ProperTwoGeneratedCore.Assembly.exists_commuting_involutions_of_two_le_pRank
      (K := (⊤ : Subgroup ↥L)) hrank
  set U : X := (u : X)
  set V : X := (v : X)
  have hU2 : U ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    show (u : X) ^ 2 = 1
    rw [← SubgroupClass.coe_pow, h]; rfl
  have hV2 : V ^ 2 = 1 := by
    have h := pow_orderOf_eq_one v
    rw [hv] at h
    show (v : X) ^ 2 = 1
    rw [← SubgroupClass.coe_pow, h]; rfl
  have hUV : U * V = V * U := congrArg Subtype.val hc.eq
  have hzU : IsElemAbelian 2 (zpowers U) := Open.isElemAbelian_iff_isElementaryAbelian.mpr
    (IsElementaryAbelian.zpowers_of_pow_eq_one hU2)
  have hW : IsElemAbelian 2 (zpowers U ⊔ zpowers V) := by
    refine isElemAbelian_sup_zpowers hzU hV2 ?_
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left hUV k).eq
  obtain ⟨Q, hWQ⟩ := (IsElemAbelian.isPGroup hW).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  have hconj : ∀ w ∈ (Q : Subgroup X), g * w * g⁻¹ ∈ (P : Subgroup X) := by
    intro w hw
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul w (MulAut.conj g) (Q : Subgroup X) hw
  have hUQ : U ∈ (Q : Subgroup X) := hWQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers U))
  have hVQ : V ∈ (Q : Subgroup X) := hWQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers V))
  have hU1 : U ≠ 1 := fun h => by
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu; exact absurd hu (by norm_num)
  have hV1 : V ≠ 1 := fun h => by
    have : v = 1 := Subtype.ext h
    rw [this, orderOf_one] at hv; exact absurd hv (by norm_num)
  have e1 := hinvP _ (hconj U hUQ) (by rw [conj_pow, hU2]; group)
    (fun h => hU1 (by simpa [mul_assoc] using congrArg (fun w => g⁻¹ * w * g) h))
  have e2 := hinvP _ (hconj V hVQ) (by rw [conj_pow, hV2]; group)
    (fun h => hV1 (by simpa [mul_assoc] using congrArg (fun w => g⁻¹ * w * g) h))
  apply huv
  apply Subtype.ext
  have : g * U * g⁻¹ = g * V * g⁻¹ := e1.trans e2.symm
  simpa [U, V] using this

end Rank

theorem false_of_sylow_noUMax {H A M : Subgroup G} (h : Asc80BSetup H A M)
    (hno : ∀ T M' : Subgroup ↥H, IsSylowIn 2 T ⊤ → M' < ⊤ →
      (∀ X : Subgroup ↥H, T ≤ X → X < ⊤ → X ≤ M') → False) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 h.sec5.le_group
    (IsElemAbelian.isPGroup h.sec5.isElemAbelian)
  have hMmax : IsMaxSubgroupIn H M := (isUniqueMaxOver_iff.mp h.maxOver_eq).1
  have hT'syl : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le).symm
    · rw [Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex] using hT.not_dvd_relIndex
  have hMlt : M.subgroupOf H < ⊤ :=
    (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := M.subgroupOf H) (K := ⊤)).mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hMmax.le, Subgroup.map_top,
        Subgroup.range_subtype]
      exact hMmax.1)
  refine hno _ _ hT'syl hMlt fun X hT'X hXlt => ?_
  let X' : Subgroup G := X.map H.subtype
  have hTX' : T ≤ X' := by
    calc T = (T.subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hT.le).symm
      _ ≤ X.map H.subtype := Subgroup.map_mono hT'X
  have hX'lt : X' < H := by
    have h' := (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := X) (K := ⊤)).mpr hXlt
    simpa only [X', Subgroup.map_top, Subgroup.range_subtype] using h'
  have hX'M : X' ≤ M := h.le_of_lt X' (hAT.trans hTX') hX'lt
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  exact hX'M (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem exists_mem_ne_one_ne_of_four_le_card {A : Subgroup G} (h4 : 4 ≤ Nat.card A) (e : G) :
    ∃ b ∈ A, b ≠ 1 ∧ b ≠ e := by
  classical
  by_contra hno
  push Not at hno
  have hsub : (A : Set G) ⊆ {1, e} := fun b hb => by
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · exact Or.inr (hno b hb hb1)
  have h1 : Nat.card A = (A : Set G).ncard := (Nat.card_coe_set_eq _)
  have h2 : (A : Set G).ncard ≤ ({1, e} : Set G).ncard := Set.ncard_le_ncard hsub
  have h3 : ({1, e} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({e} : Set G)
    rw [Set.ncard_singleton] at this
    exact this
  omega

theorem asc80ThmBCase_oddLieType_of_seitzFour
    (hS : SeitzFour fun X _ => CFSG.Models.OddLieType X ∧
      ¬ CFSG.Models.LieModel X .PSL 2 5 1 ∧ ¬ CFSG.Models.LieModel X .PSL 2 3 2) :
    Asc80ThmBCase fun X _ => CFSG.Models.OddLieType X := by
  intro G _ _ H A M hs hnab hP hAH hA hM
  by_cases h5 : CFSG.Models.LieModel ↥(Fstar H) .PSL 2 5 1
  · obtain ⟨e5⟩ := CFSG.Quasithin.H13.Ch8310.a5_of_psl25
      (h5.statedClassicalModel_of_ne_zero (by decide))
    exact asc80ThmBCase_alt H A M hs hnab ⟨5, le_rfl, ⟨e5⟩⟩ hAH hA hM
  by_cases h9 : CFSG.Models.LieModel ↥(Fstar H) .PSL 2 3 2
  · obtain ⟨e6⟩ := CFSG.Quasithin.RonanE114.isAlt6_of_isPSL2_nine
      (h9.statedClassicalModel_of_ne_zero (by decide))
    exact asc80ThmBCase_alt H A M hs hnab ⟨6, by norm_num, ⟨e6⟩⟩ hAH hA hM
  replace hP : CFSG.Models.OddLieType ↥(Fstar H) ∧
      ¬ CFSG.Models.LieModel ↥(Fstar H) .PSL 2 5 1 ∧
      ¬ CFSG.Models.LieModel ↥(Fstar H) .PSL 2 3 2 := ⟨hP, h5, h9⟩
  have h := asc80BSetup hs hnab hAH hA hM
  have hPiso : ∀ (X Y : Type) [Group X] [Group Y], Nonempty (X ≃* Y) →
      (CFSG.Models.OddLieType X ∧ ¬ CFSG.Models.LieModel X .PSL 2 5 1 ∧
        ¬ CFSG.Models.LieModel X .PSL 2 3 2) →
      (CFSG.Models.OddLieType Y ∧ ¬ CFSG.Models.LieModel Y .PSL 2 5 1 ∧
        ¬ CFSG.Models.LieModel Y .PSL 2 3 2) :=
    fun X Y _ _ ⟨e⟩ ⟨hX, hX5, hX9⟩ => ⟨CFSG.Models.OddLieType.of_mulEquiv e hX,
      fun h => hX5 (h.of_mulEquiv e.symm), fun h => hX9 (h.of_mulEquiv e.symm)⟩
  obtain ⟨A', hAA', hA'H, hA', hmax, -⟩ := h.exists_maximal
  have h4 : 4 ≤ Nat.card A' := by
    let L : Subgroup ↥H := (Fstar H).subgroupOf H
    let eL : ↥L ≃* ↥(Fstar H) := Subgroup.subgroupOfEquivOfLe (fstar_le_group H)
    have : IsSimpleGroup ↥(Fstar H) := hs
    have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
    have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨eL.symm a, eL.symm b, fun hc => hab (by simpa using congrArg eL hc)⟩
    have hne : A'.subgroupOf H ≠ ⊥ := by
      obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.ne_bot
      refine (Subgroup.ne_bot_iff_exists_ne_one).mpr
        ⟨⟨⟨a, hAH haA⟩, show a ∈ A' from hAA' haA⟩, fun h1 => ha1 ?_⟩
      have h2 := congrArg Subtype.val (congrArg Subtype.val h1)
      exact Subtype.ext (by simpa using h2)
    have hmax' : ∀ B : Subgroup ↥H, A'.subgroupOf H ≤ B → IsElemAbelian 2 B →
        B = A'.subgroupOf H := by
      intro B hAB hB
      have hA'B : A' ≤ B.map H.subtype := by
        calc A' = (A'.subgroupOf H).map H.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hA'H).symm
          _ ≤ B.map H.subtype := Subgroup.map_mono hAB
      have heq := hmax _ hA'B (Subgroup.map_subtype_le B) (hB.map H.subtype)
      calc B = (B.map H.subtype).comap H.subtype :=
            (Subgroup.comap_map_eq_self_of_injective H.subtype_injective B).symm
        _ = A'.subgroupOf H := by rw [heq]; rfl
    have := four_le_card_of_maximal hLs hLnab (hA'.subgroupOf H) hne hmax'
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'H).toEquiv] at this
  have hfour : ∀ e ∈ A', e ≠ 1 → ∃ E : Subgroup G, e ∈ E ∧ E ≤ A' ∧ IsElemAbelian 2 E ∧
      Nat.card E = 4 := by
    intro e heA' he1
    obtain ⟨b, hbA', hb1, hbe⟩ := exists_mem_ne_one_ne_of_four_le_card h4 e
    have he2 : e ^ 2 = 1 := hA'.2 e heA'
    have hb2 : b ^ 2 = 1 := hA'.2 b hbA'
    have heb : e * b = b * e :=
      congrArg Subtype.val (hA'.1.is_comm.comm ⟨e, heA'⟩ ⟨b, hbA'⟩)
    refine ⟨zpowers e ⊔ zpowers b, Subgroup.mem_sup_left (Subgroup.mem_zpowers e),
      sup_le (Subgroup.zpowers_le.mpr heA') (Subgroup.zpowers_le.mpr hbA'), ?_, ?_⟩
    · refine CFSG.LocalAnalysis.ComponentInitial.isElemAbelian_sup_zpowers
        (Open.isElemAbelian_zpowers he2) hb2 ?_
      rintro _ ⟨k, rfl⟩
      exact (Commute.zpow_left heb k).eq
    · exact CFSG.GH74.GLS.C3.Layer1.P89.card_klein he2 hb2 heb he1 hb1 (Ne.symm hbe)
  by_cases hex : ∃ x ∈ A', x ∉ Fstar H
  ·
    exfalso
    obtain ⟨e, heA', heF⟩ := hex
    have he1 : e ≠ 1 := fun h1 => heF (h1 ▸ (Fstar H).one_mem)
    obtain ⟨E, heE, hEA', hE, hE4⟩ := hfour e heA' he1
    exact false_of_seitzFour hPiso hS h hs hnab hP hAA' hA'H hA' hEA' hE hE4
      (fun hx => heF (hx.1 heE))
  · push Not at hex
    obtain ⟨⟨e, heA'⟩, he1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (fun hbot => h.ne_bot (le_bot_iff.mp (hbot ▸ hAA')))
    have he1 : e ≠ 1 := fun h1 => he1' (Subtype.ext h1)
    obtain ⟨E, -, hEA', hE, hE4⟩ := hfour e heA' he1
    by_cases hexc : E ≤ Fstar H ∧ SeitzFourExc ↥(Fstar H)
    · have hHF : Fstar H = H := by
        refine le_antisymm (fstar_le_group H) ?_
        exact h.eq_sup.le.trans (sup_le le_rfl fun x hx => hex x (hAA' hx))
      let eH : ↥(Fstar H) ≃* ↥H := MulEquiv.subgroupCongr hHF
      rcases hexc.2 with h5' | h7 | h9' | h3
      · exact absurd h5' h5
      ·
        exfalso
        have sc := (h7.of_mulEquiv eH).statedClassicalModel_of_ne_zero (by decide)
        have hB : CFSG.Blueprint.LieModel ↥H .PSL 2 7 1 := Or.inl ⟨by decide, sc⟩
        exact false_of_sylow_noUMax h fun T M' hT hMt hMax =>
          not_hasUniqueMaxOver_of_psl_two_seven hB hT ⟨M', hMt, hMax⟩
      · exact absurd h9' h9
      ·
        exfalso
        let eT : ↥(Fstar H) ≃* ↥(⊤ : Subgroup ↥H) := eH.trans Subgroup.topEquiv.symm
        have sc := (h3.of_mulEquiv eT).statedClassicalModel_of_ne_zero (by decide)
        have sU := CFSG.ComponentClassification.HarrisLit.Hin.statedClassicalModel_PSU_four_two_of_PSp_two_three sc
        have hmU : CFSG.Models.LieModel ↥(⊤ : Subgroup ↥H) .PSU 4 2 1 :=
          ⟨⟨Nat.prime_two, le_rfl, by decide⟩, Or.inl sU⟩
        have : IsSimpleGroup ↥(Fstar H) := hs
        have hTs : IsSimpleGroup ↥(⊤ : Subgroup ↥H) := eT.symm.isSimpleGroup
        have hTnab : ∃ a b : ↥(⊤ : Subgroup ↥H), a * b ≠ b * a := by
          obtain ⟨a, b, hab⟩ := hnab
          exact ⟨eT a, eT b, fun hc => hab (by simpa using congrArg eT.symm hc)⟩
        refine false_of_sylow_noUMax h fun T M' hT hMt hMax => ?_
        obtain ⟨K, _, _, D, nn, Hh, π, ee, hBQ, i, j, hne⟩ :=
          Chev2Orbit.hasBQUneven_psu (Or.inl rfl) hmU
        obtain ⟨π', hU⟩ := Chev2Orbit.exists_umaxBQ (L := (⊤ : Subgroup ↥H)) inferInstance hTs
          hTnab hT hMt hMax hBQ
        exact hne (hU.card_rootGroup_eq i j)
    · exact (false_of_seitzFour hPiso hS h hs hnab hP hAA' hA'H hA' hEA' hE hE4 hexc).elim

end CFSG.LocalAnalysis.WeakClosure81
