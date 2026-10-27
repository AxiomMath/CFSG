module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOff
public import CFSG.Quasithin.Recognition.Kleidman.F204.NatA
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFAll
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem card_map_alt5_of_odd {K : Type} [Group K] [Finite K]
    (φ : K →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    {P : Subgroup K} (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) (hker : φ.ker ≤ P) :
    Nat.card (P.map φ) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : (P.map φ).index = P.index := Subgroup.index_map_eq P hφ hker
  have hP' : IsPGroup 2 (P.map φ) := hP.map φ
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have hmul : Nat.card (P.map φ) * P.index = 60 := by
    rw [← hidx, ← h60]
    exact Subgroup.card_mul_index _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP'
  have hdvd : 2 ^ k ∣ 60 := ⟨P.index, by rw [← hk]; exact hmul.symm⟩
  have hk6 : k < 6 := by
    by_contra h
    push Not at h
    have h64 : 2 ^ 6 ∣ 2 ^ k := Nat.pow_dvd_pow 2 h
    have := h64.trans hdvd
    norm_num at this
  rw [hk] at hmul ⊢
  interval_cases k <;> norm_num at hmul ⊢ <;> omega

section NatA

variable (F : Frame L1 L2 S D X)
include F

theorem card_map_Qv_nbr {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) (hδ : δ ∈ nbrs x)
    {φ : ↥(stab x) →* alternatingGroup (Fin 5)} (hφs : Function.Surjective φ)
    (hφk : φ.ker = (Qv x).subgroupOf (stab x)) :
    Nat.card (((Qv δ).subgroupOf (stab x)).map φ) = 4 := by
  obtain ⟨hsub, hp, hodd⟩ := (sylow_sup_Qv F hx hδ).2.1
  have hQx : Qv x ≤ stab x := le_trans le_sup_left hsub
  have hQδ : Qv δ ≤ stab x := le_trans le_sup_right hsub
  have hPeq : (Qv x ⊔ Qv δ).subgroupOf (stab x) = φ.ker ⊔ (Qv δ).subgroupOf (stab x) := by
    rw [hφk, Subgroup.subgroupOf_sup hQx hQδ]
  have hK : φ.ker.map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp hk)
  have hker : φ.ker ≤ (Qv x ⊔ Qv δ).subgroupOf (stab x) := by
    rw [hPeq]
    exact le_sup_left
  have hp' : IsPGroup 2 ((Qv x ⊔ Qv δ).subgroupOf (stab x)) := hp.comap_subtype
  have hcard := card_map_alt5_of_odd φ hφs hp' hodd hker
  have hmapeq : ((Qv x ⊔ Qv δ).subgroupOf (stab x)).map φ =
      ((Qv δ).subgroupOf (stab x)).map φ := by
    rw [hPeq, Subgroup.map_sup, hK, bot_sup_eq]
  rw [← hmapeq]
  exact hcard

theorem map_Qv_ne {x δ δ' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) (hδ : δ ∈ nbrs x) (hδ' : δ' ∈ nbrs x) (hne : δ ≠ δ')
    {φ : ↥(stab x) →* alternatingGroup (Fin 5)}
    (hφk : φ.ker = (Qv x).subgroupOf (stab x)) :
    ((Qv δ).subgroupOf (stab x)).map φ ≠ ((Qv δ').subgroupOf (stab x)).map φ := by
  intro h
  have hQx : Qv x ≤ stab x := le_trans le_sup_left (sylow_sup_Qv F hx hδ).2.1.1
  have hQδx : Qv δ ≤ stab x := le_trans le_sup_right (sylow_sup_Qv F hx hδ).2.1.1
  have hQδ'x : Qv δ' ≤ stab x := le_trans le_sup_right (sylow_sup_Qv F hx hδ').2.1.1
  have hs' : Qv x ⊔ Qv δ' ≤ stab δ' := (sylow_sup_Qv F hx hδ').1.1
  have hgen : ∀ Y : Geo (P1 L1 L2 S) (P2 L1 L2 S), Qv Y ≤ stab x →
      (Qv Y).subgroupOf (stab x) ⊔ φ.ker = (Qv Y ⊔ Qv x).subgroupOf (stab x) := by
    intro Y hY
    rw [hφk, Subgroup.subgroupOf_sup hY hQx]
  have hcomap : (Qv δ).subgroupOf (stab x) ⊔ φ.ker = (Qv δ').subgroupOf (stab x) ⊔ φ.ker := by
    calc (Qv δ).subgroupOf (stab x) ⊔ φ.ker
        = Subgroup.comap φ (Subgroup.map φ ((Qv δ).subgroupOf (stab x))) := by
          rw [Subgroup.comap_map_eq]
      _ = Subgroup.comap φ (Subgroup.map φ ((Qv δ').subgroupOf (stab x))) := by rw [h]
      _ = (Qv δ').subgroupOf (stab x) ⊔ φ.ker := by rw [Subgroup.comap_map_eq]
  have hcomap2 : (Qv δ ⊔ Qv x).subgroupOf (stab x) = (Qv δ' ⊔ Qv x).subgroupOf (stab x) := by
    rw [← hgen δ hQδx, ← hgen δ' hQδ'x]
    exact hcomap
  have hmap := congrArg (Subgroup.map (stab x).subtype) hcomap2
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (sup_le hQδx hQx), inf_eq_left.mpr (sup_le hQδ'x hQx)] at hmap
  have hle : Qv δ ≤ stab δ' :=
    (le_sup_left.trans hmap.le).trans (sup_le (le_trans le_sup_right hs') (le_trans le_sup_left hs'))
  have hw : ∃ w' ∈ nbrs x, w' ≠ δ ∧ w' ≠ δ' := by
    by_contra hcon
    have hsub : nbrs x ⊆ ({δ, δ'} : Set (Geo (P1 L1 L2 S) (P2 L1 L2 S))) := by
      intro w hw
      by_contra hw2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw2
      exact hcon ⟨w, hw, hw2.1, hw2.2⟩
    have h5 := Amal.card_nbrs_true (Amal.of_frame F) hx
    rw [Nat.card_coe_set_eq] at h5
    have h2 := Set.ncard_pair hne
    have hle2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨w', hw'nb, hw'δ, hw'δ'⟩ := hw
  obtain ⟨q, hq, hqw⟩ := exists_Qv_smul_nbr F hx hδ hδ' hw'nb hne.symm hw'δ
  have hfix2 : q • δ' = δ' := smul_eq_of_mem_stab (hle hq)
  have hw_eq : w' = δ' := by
    rw [← hqw]
    exact hfix2
  exact hw'δ' hw_eq

end NatA

theorem H3_natA_core (F : Frame L1 L2 S D X)
    {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hCLx : Zv x ⊓ Subgroup.centralizer (stab x : Set G) = ⊥)
    {A : Subgroup G} (hAx : A ≤ stab x) (hA : IsPGroup 2 (A.subgroupOf (stab x)))
    (hAnt : ∃ a ∈ A, ∃ v ∈ Zv x, a * v ≠ v * a)
    (hidx : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≤
      (A ⊓ Qv x).relIndex A) :
    NatA x ∧ (A ⊓ Qv x).relIndex A = 4 ∧
      (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) = 4 := by
  have hA' := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hV2 : ∀ a ∈ Zv x, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact (hA'.isElemAbelian_Zv x).2 a ha
  have hLV : stab x ≤ Subgroup.normalizer (Zv x : Set G) := hA'.stab_le_normalizer_Zv x
  have hker : ∀ l : ↥(stab x), φ l = 1 → (l : G) ∈ Subgroup.centralizer (Zv x : Set G) := by
    intro l hl
    have hlk : l ∈ φ.ker := MonoidHom.mem_ker.mpr hl
    rw [hφk] at hlk
    exact Qv_le_centralizer_Zv F x (Subgroup.mem_subgroupOf.mp hlk)
  have hCL : ∀ v ∈ Zv x, (∀ l : ↥(stab x), v * (l : G) = (l : G) * v) → v = 1 := by
    intro v hv hvc
    have hmem : v ∈ Zv x ⊓ Subgroup.centralizer (stab x : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact (hvc ⟨h, hh⟩).symm
    rw [hCLx] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbridge : (A ⊓ Qv x).relIndex A = Nat.card ((A.subgroupOf (stab x)).map φ) := by
    calc (A ⊓ Qv x).relIndex A = (Qv x).relIndex A := by
          rw [inf_comm]; exact Subgroup.inf_relIndex_right (H := Qv x) (K := A)
      _ = ((Qv x).subgroupOf (stab x)).relIndex (A.subgroupOf (stab x)) :=
          (Subgroup.relIndex_subgroupOf hAx).symm
      _ = φ.ker.relIndex (A.subgroupOf (stab x)) := by rw [hφk]
      _ = Nat.card ((A.subgroupOf (stab x)).map φ) := Subgroup.relIndex_ker _ φ
  have hAmap : ((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAx]
  have hAnt' : ∃ a ∈ A.subgroupOf (stab x), ∃ v ∈ Zv x, (a : G) * v ≠ v * (a : G) := by
    obtain ⟨a, haA, v, hv, hne⟩ := hAnt
    exact ⟨⟨a, hAx haA⟩, Subgroup.mem_subgroupOf.mpr haA, v, hv, hne⟩
  have hidx' : (Zv x ⊓ Subgroup.centralizer
      (((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) : Set G)).relIndex (Zv x) ≤
      Nat.card ((A.subgroupOf (stab x)).map φ) := by
    rw [hAmap, ← hbridge]
    exact hidx
  obtain ⟨hV16, hK1, hC, hD⟩ := fa5_ff_all hV2 hLV φ hφs hker hCL hA hAnt' hidx'
  have hr4 : (A ⊓ Qv x).relIndex A = 4 := by
    rw [hbridge]
    exact hK1
  have hCA : Nat.card (Zv x ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = 4 := by
    have h := hC (A.subgroupOf (stab x)) hK1
    rw [hAmap] at h
    exact h
  have hZA : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) = 4 := by
    have h := card_eq_relIndex_mul (V := Zv x) (Z := Subgroup.centralizer (A : Set G))
    rw [hV16, hCA] at h
    omega
  refine ⟨?_, hr4, hZA⟩
  unfold NatA
  refine ⟨hV16, ?_, ?_⟩
  · intro δ hδ
    have hQδ : Qv δ ≤ stab x := le_trans le_sup_right (sylow_sup_Qv F hx hδ).2.1.1
    have e1 : ((Qv δ).subgroupOf (stab x)).map (stab x).subtype = Qv δ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQδ]
    have h := hC ((Qv δ).subgroupOf (stab x)) (card_map_Qv_nbr F hx hδ hφs hφk)
    rw [e1] at h
    exact h
  · intro δ hδ δ' hδ' hne
    have hQδ : Qv δ ≤ stab x := le_trans le_sup_right (sylow_sup_Qv F hx hδ).2.1.1
    have hQδ' : Qv δ' ≤ stab x := le_trans le_sup_right (sylow_sup_Qv F hx hδ').2.1.1
    have e1 : ((Qv δ).subgroupOf (stab x)).map (stab x).subtype = Qv δ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQδ]
    have e2 : ((Qv δ').subgroupOf (stab x)).map (stab x).subtype = Qv δ' := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQδ']
    have h := hD ((Qv δ).subgroupOf (stab x)) ((Qv δ').subgroupOf (stab x))
      (card_map_Qv_nbr F hx hδ hφs hφk) (card_map_Qv_nbr F hx hδ' hφs hφk)
      (map_Qv_ne F hx hδ hδ' hne hφk)
    rw [e1, e2] at h
    exact h

theorem H3_natA (F : Frame L1 L2 S D X)
    (hT1 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false)
    {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    {A : Subgroup G} (hAx : A ≤ stab x) (hA : IsPGroup 2 (A.subgroupOf (stab x)))
    (hAnt : ∃ a ∈ A, ∃ v ∈ Zv x, a * v ≠ v * a)
    (hidx : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≤
      (A ⊓ Qv x).relIndex A) :
    NatA x ∧ (A ⊓ Qv x).relIndex A = 4 ∧
      (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) = 4 :=
  H3_natA_core F hx (H1 F hT1 hx) hAx hA hAnt hidx

end CFSG.Quasithin.Kleidman.F204
