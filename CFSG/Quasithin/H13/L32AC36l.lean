module

public import CFSG.Quasithin.EmptyFaithful.LRed5Quot
public import CFSG.Quasithin.H13.L32AC36g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

theorem exists_pow_mul_eq {Γ : Type*} [Group Γ] {L : Subgroup Γ} {l s : Γ} (hl : l ∈ L)
    (hs : s ∈ Subgroup.normalizer (L : Set Γ)) (n : ℕ) : ∃ l' ∈ L, (l * s) ^ n = l' * s ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    have hs' : s ^ n ∈ Subgroup.normalizer (L : Set Γ) := Subgroup.pow_mem _ hs n
    refine ⟨l' * (s ^ n * l * (s ^ n)⁻¹),
      L.mul_mem hl' ((Subgroup.mem_normalizer_iff.mp hs' l).mp hl), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem centralizer_inf_le {Γ : Type} [Group Γ] [Finite Γ] {X L S : Subgroup Γ}
    (hLX : L ≤ X) (hXN : X ≤ Subgroup.normalizer (L : Set Γ)) (hX : X = L ⊔ S)
    (hS2 : IsPGroup 2 S) (hO2 : pCoreOf 2 X = ⊥) :
    Subgroup.centralizer (L : Set Γ) ⊓ X ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (L : Set Γ) ⊓ X with hC
  have hCX : C ≤ X := inf_le_right
  have hSX : S ≤ X := hX ▸ le_sup_right
  have hXC : X ≤ Subgroup.normalizer (C : Set Γ) := by
    intro g hg
    have key : ∀ g ∈ X, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun l hl => ?_, X.mul_mem (X.mul_mem hg (hCX hc))
        (X.inv_mem hg)⟩
      have hl' : g⁻¹ * l * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (X.inv_mem hg |> hXN) l).mp hl
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hc.1 _ hl'
      calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * l := by group
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key g hg c, fun h => ?_⟩
    have := key g⁻¹ (X.inv_mem hg) _ h
    simpa [mul_assoc] using this
  have hpow : ∀ c ∈ C, ∃ e : ℕ, c ^ 2 ^ e ∈ L := by
    intro c hc
    have hn : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN
    obtain ⟨l, hl, s, hs, rfl⟩ := LRed5.exists_mul_of_mem_sup_of_le_normalizer hn hLX hSX
      (show c ∈ L ⊔ S by rw [← hX]; exact hCX hc)
    obtain ⟨e, he⟩ := hS2 ⟨s, hs⟩
    have he' : s ^ 2 ^ e = 1 := congrArg Subtype.val he
    obtain ⟨l', hl', h'⟩ := exists_pow_mul_eq hl (hXN (hSX hs)) (2 ^ e)
    exact ⟨e, by rw [h', he', mul_one]; exact hl'⟩
  set D := L.subgroupOf C with hD
  have hDc : D ≤ Subgroup.center ↥C := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2.1 _ (Subgroup.mem_subgroupOf.mp hd)).symm
  have : D.Normal := ⟨fun d hd c => by
    have := hDc hd
    rw [Subgroup.mem_center_iff] at this
    rw [show c * d * c⁻¹ = d by rw [this c, mul_inv_cancel_right]]
    exact hd⟩
  have hQ2 : IsPGroup 2 (↥C ⧸ D) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      obtain ⟨e, he⟩ := hpow c c.2
      refine ⟨e, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using he)
  have hnilQ : Group.IsNilpotent (↥C ⧸ D) := hQ2.isNilpotent
  have hnil : Group.IsNilpotent ↥C :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' D)
      (by rw [QuotientGroup.ker_mk']; exact hDc)
  obtain P : Sylow 2 ↥C := Classical.arbitrary _
  have hPn : (P : Subgroup ↥C).Normal := inferInstance
  have hPle : (P : Subgroup ↥C).map C.subtype ≤ pCoreOf 2 C :=
    le_pCoreOf 2 (Subgroup.map_subtype_le _) (by rwa [map_subtype_subgroupOf'])
      (P.isPGroup'.map _)
  have hCO : pCoreOf 2 C ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCX)
      (hXC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
  have hP1 : (P : Subgroup ↥C) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective, eq_bot_iff, ← hO2]
    exact hPle.trans hCO
  have hodd : ¬ 2 ∣ Nat.card ↥C := by
    have h1 := P.not_dvd_index
    rw [hP1, Subgroup.index_bot] at h1
    exact h1
  intro c hc
  obtain ⟨e, he⟩ := hpow c hc
  have hco : (2 ^ e).Coprime (orderOf (⟨c, hc⟩ : ↥C)) := by
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h2 => ?_)
    exact hodd (h2.trans (orderOf_dvd_natCard _))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
  have hm' : (c ^ 2 ^ e) ^ m = c := congrArg Subtype.val hm
  rw [← hm']
  exact L.pow_mem he m

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

section Psi

variable {I : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]

theorem psiI_mem_tildeV (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hV₁I : fsuV1 T V ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G))
    (hVIH : V ≤ conjClosure I H) {h : ↥H} (hh : (h : G) ∈ Subgroup.normalizer (V : Set G))
    {w : ↥(subM (fsuV1 T V) (conjClosure I H) I)}
    (hw : w ∈ (subM (fsuV1 T V) (conjClosure I H) V).subgroupOf
      (subM (fsuV1 T V) (conjClosure I H) I)) :
    psiI hF hIU hV₁I hHI h w ∈ (subM (fsuV1 T V) (conjClosure I H) V).subgroupOf
      (subM (fsuV1 T V) (conjClosure I H) I) := by
  have hIHN : conjClosure I H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ hIU
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  obtain ⟨a, haV, ha⟩ := mem_secImg.mp (show ((w : ↥(tildeOf (fsuV1 T V) (conjClosure I H))) :
    SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈ tildeOf (fsuV1 T V) V from hw)
  have hwa : (w : ↥(tildeOf (fsuV1 T V) (conjClosure I H))) = modMk hIHN a (hVIH haV) :=
    Subtype.ext ha.symm
  rw [Subgroup.mem_subgroupOf, psiI_apply, hwa,
    actH_modMk hF.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) h (hVIH haV)]
  exact (modMk_mem_subM_iff hIHN hV₁V _).mpr ((Subgroup.mem_normalizer_iff.mp hh a).mp haV)

end Psi

end CFSG.Quasithin.H13.L32A.C
