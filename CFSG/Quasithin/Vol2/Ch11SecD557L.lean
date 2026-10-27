module

public import CFSG.Quasithin.Vol2.Ch11SecD557K
public import CFSG.Quasithin.Background.G25Setup
public import CFSG.Quasithin.Vol2.Ch11SecD557F
public import CFSG.Quasithin.Vol2.Ch11SecDFacts6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_frattini {U : Subgroup G} (hU : IsPGroup 2 U) {a : G} (ha : a ∈ U) :
    a ^ 2 ∈ (frattini ↥U).map U.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥U) := ⟨hU⟩
  refine ⟨⟨a, ha⟩ ^ 2, ?_, rfl⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  exact Subgroup.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

omit [Finite G] in
theorem comm_sq_inf_rconj {U V₁ : Subgroup G} {x y : G}
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁) (hsq : ∀ a ∈ U, a ^ 2 ∈ V₁)
    (hxy : rconj V₁ x ⊓ rconj V₁ y = ⊥) :
    (∀ a ∈ rconj U x ⊓ rconj U y, ∀ b ∈ rconj U x ⊓ rconj U y, a * b = b * a) ∧
      ∀ a ∈ rconj U x ⊓ rconj U y, a ^ 2 = 1 := by
  have key : ∀ g : G, ∀ a ∈ rconj U g, ∀ b ∈ rconj U g,
      a * b * a⁻¹ * b⁻¹ ∈ rconj V₁ g ∧ a ^ 2 ∈ rconj V₁ g := by
    intro g a ha b hb
    rw [mem_rconj] at ha hb
    rw [mem_rconj, mem_rconj]
    constructor
    · have h1 := hcomm _ ha _ hb
      convert h1 using 1
      group
    · have h1 := hsq _ ha
      convert h1 using 1
      rw [pow_two, pow_two]
      group
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h1 : a * b * a⁻¹ * b⁻¹ ∈ rconj V₁ x ⊓ rconj V₁ y :=
      ⟨(key x a ha.1 b hb.1).1, (key y a ha.2 b hb.2).1⟩
    rw [hxy, Subgroup.mem_bot] at h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · have h1 : a ^ 2 ∈ rconj V₁ x ⊓ rconj V₁ y :=
      ⟨(key x a ha.1 a ha.1).2, (key y a ha.2 a ha.2).2⟩
    rw [hxy, Subgroup.mem_bot] at h1
    exact h1

variable {T L I : Subgroup G} {n : ℕ}

theorem config_structure (hI16 : ASInputs.AS_I_1_6) (hComm : CommLOneSL3Fact)
    (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hSL3 : KindSL3 L (fsuV T I) n)
    (St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G))) {x y : G}
    (hx : x ∈ L) (hy : y ∈ L) (hV : fsuV T I = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y)
    (hxy : rconj V₁ x ⊓ rconj V₁ y = ⊥)
    (hS : pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        rconj (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) x ⊓
        rconj (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) y)
    (hUcomm : ∀ a ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)),
      ∀ b ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), a * b * a⁻¹ * b⁻¹ ∈ V₁)
    (hUsq : ∀ a ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), a ^ 2 ∈ V₁) :
    let U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))
    let S := pCoreOf 2 (L ⊔ U)
    (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧ (∀ a ∈ S, a ^ 2 = 1) ∧
      S ≤ fsuV T I ⊔ (S ⊓ Subgroup.centralizer (L : Set G)) ∧
      U ≤ (U ⊓ L) ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) ∧
      U ⊓ Subgroup.centralizer (L : Set G) ≤ S := by
  intro U S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hScomm, hSsq⟩ := comm_sq_inf_rconj hUcomm hUsq hxy
  have hSE : S ≤ rconj U x ⊓ rconj U y := fun s hs =>
    ⟨(hS hs).1.2, (hS hs).2⟩
  have hSU : S ≤ U := fun s hs => (hS hs).1.1
  have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb => hScomm a (hSE ha) b (hSE hb)
  have hSs : ∀ a ∈ S, a ^ 2 = 1 := fun a ha => hSsq a (hSE ha)
  have hLU : L ≤ L ⊔ U := le_sup_left
  have hUN : U ≤ Subgroup.normalizer (L : Set G) := fun u hu => St.U_le_normL hu
  have hLUN : L ⊔ U ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hUN
  have hVS : fsuV T I ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_conjClosure _ _).trans le_sup_right) St.LU_le_normV St.isPGroup_V
  have hO2L : pCoreOf 2 L ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLU)
      (fun z hz => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hLUN hz))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hI : U ⊔ rconj U x ⊔ rconj U y = L ⊔ U := St.G25_two_aux hx hy hV
  have h5 := St.hyp.G25_five rfl hx hy hV rfl
  have hLS : ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ * s⁻¹ ∈ fsuV T I := by
    intro l hl s hs
    have h1 : ⁅s, l⁆ ∈ fsuV T I :=
      h5 (Subgroup.commutator_mem_commutator (hS hs) (hI ▸ hLU hl))
    have e : l * s * l⁻¹ * s⁻¹ = ⁅s, l⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hKS : ∀ k ∈ L, k ∈ pCoreOf 2 (L ⊔ T) → ∀ s ∈ S, k * s * k⁻¹ = s := by
    intro k hk hkO s hs
    have hkS : k ∈ S := hO2L (inf_le_pCoreOf_of_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))) ⟨hk, hkO⟩)
    rw [hSc k hkS s hs, mul_inv_cancel_right]
  have hVL : fsuV T I ≤ ⁅fsuV T I, L⁆ := by
    have hset := natSetting11_of h1102 h1141 h hV₁
    rw [← hComm G T L I n V₁ hset hSL3 hV₁] at ⊢
    exact (Subgroup.commutator_mono le_rfl ((perfectCore_le _).trans inf_le_left)).trans
      (by rw [hComm G T L I n V₁ hset hSL3 hV₁])
  have hSV := le_sup_centralizer_of_I16 hI16 h.one_lt St.D hVS hSc hSs hLS hKS hVL
  have hVL' : fsuV T I ≤ L := by
    rw [← hComm G T L I n V₁ (natSetting11_of h1102 h1141 h hV₁) hSL3 hV₁,
      Subgroup.commutator_le]
    intro v hv l hl
    have hvN : v ∈ Subgroup.normalizer (L : Set G) :=
      h.normal (SecA.fsuV_le_T h hv)
    have hlL : l ∈ L := ((perfectCore_le _).trans inf_le_left) hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hvN l).mp hlL) (L.inv_mem hlL)
  refine ⟨hSc, hSs, hSV, fun u hu => ?_, fun c hc => ?_⟩
  ·
    have huI : u ∈ L ⊔ U := (le_sup_right : U ≤ L ⊔ U) hu
    obtain ⟨l, hl⟩ := St.D.surj (St.Phi ⟨u, huI⟩)
    have hPl := St.Phi_of_L l
    have ho : (l : G)⁻¹ * u ∈ S := by
      have h1 : St.Phi (⟨(l : G), hLU l.2⟩⁻¹ * ⟨u, huI⟩) = 1 := by
        rw [map_mul, map_inv, hPl, hl, inv_mul_cancel]
      exact (St.Phi_eq_one_iff_mem_S _).mp h1
    have hlU : (l : G) ∈ U := by
      have e : (l : G) = u * ((l : G)⁻¹ * u)⁻¹ := by group
      rw [e]
      exact U.mul_mem hu (U.inv_mem (hSU ho))
    have e : u = (l : G) * ((l : G)⁻¹ * u) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlU, l.2⟩) ?_
    have hle : fsuV T I ⊔ (S ⊓ Subgroup.centralizer (L : Set G)) ≤
        (U ⊓ L) ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) :=
      sup_le (fun v hv => Subgroup.mem_sup_left ⟨(le_conjClosure _ _) hv, hVL' hv⟩)
        (fun w hw => Subgroup.mem_sup_right ⟨hSU hw.1, hw.2⟩)
    exact hle (hSV ho)
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((inf_le_left : U ⊓ Subgroup.centralizer (L : Set G) ≤ U).trans (le_sup_right : U ≤ L ⊔ U))
      (sup_le (fun l hl => A4.mem_normalizer_of_conj_mem fun z hz => ?_)
        (fun u hu => A4.mem_normalizer_of_conj_mem fun z hz => ?_))
      (St.isPGroup_U.to_le inf_le_left) hc
    · refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff.mp hz.2 l hl, mul_inv_cancel_right]
        exact hz.1
      · rw [Subgroup.mem_centralizer_iff.mp hz.2 l hl, mul_inv_cancel_right]
        exact hz.2
    · refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ ?_) z).mp hz.1, ?_⟩
      · exact (St.U_le_T hu |> fun ht => SecA.IsVi.le_normalizer hV₁ ht)
      · show u * z * u⁻¹ ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hl' : u⁻¹ * l * u ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (hUN (U.inv_mem hu)) l).mp hl
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hl'
        calc l * (u * z * u⁻¹) = u * ((u⁻¹ * l * u) * z) * u⁻¹ := by group
          _ = u * (z * (u⁻¹ * l * u)) * u⁻¹ := by rw [h1]
          _ = u * z * u⁻¹ * l := by group

end CFSG.Quasithin.Vol2.Ch11.SecD
