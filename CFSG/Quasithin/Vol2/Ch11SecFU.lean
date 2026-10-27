module

public import CFSG.Quasithin.Vol2.Ch11SecDNat
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11SecFGroup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_left' {W A : Subgroup G} (hA : A ≤ Subgroup.normalizer (W : Set G)) :
    ⁅W, A⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro w hw a ha
  rw [commutatorElement_def]
  have h1 : a * w⁻¹ * a⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hA ha) w⁻¹).mp (W.inv_mem hw)
  have h2 := W.mul_mem hw h1
  simpa [mul_assoc] using h2

theorem le_commutator_sup_of_isNaturalSection {A W Z : Subgroup G} {N : Subgroup ↥A}
    {F : Type} [Field F] (h : IsNaturalSection A W Z N (StatedSL 2 F)) (hZW : Z ≤ W)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) : W ≤ ⁅W, A⁆ ⊔ Z := by
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := h.1
  have hAC : A ≤ Subgroup.normalizer ((⁅W, A⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (A3.sup_le_normalizer_commutator W A)
  have hAX : A ≤ Subgroup.normalizer (((⁅W, A⁆ ⊔ Z) ⊓ W : Subgroup G) : Set G) := fun a ha =>
    SecD.mem_normalizer_inf (SecD.le_normalizer_sup hAC hAZ ha) (hAW ha)
  rcases SecD.isNaturalSection_irred h (le_inf le_sup_right hZW) inf_le_right hAX with heq | heq
  · exfalso
    have hCZ : ⁅W, A⁆ ≤ Z := by
      rw [← heq]
      exact le_inf le_sup_left (commutator_le_left' hAW)
    obtain ⟨-, α, hα, -, β, hβ, hβker, hequiv⟩ := h
    let E : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hE : (Matrix.SpecialLinearGroup.toGL E : GL (Fin 2) F) ∈ StatedSL 2 F :=
      SecD.mem_statedSL_of_det (by simp)
    obtain ⟨a, ha⟩ := hα ⟨_, hE⟩
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd (Pi.single 1 1))
    have hvW : (a : G) * u * (a : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hAW a.2) u).mp u.2
    have hcomm : ((u : G))⁻¹ * ((a : G) * u * (a : G)⁻¹) ∈ Z := by
      have h1 : ⁅((u : G))⁻¹, (a : G)⁆ ∈ ⁅W, A⁆ :=
        Subgroup.commutator_mem_commutator (W.inv_mem u.2) a.2
      have h2 := hCZ h1
      rw [commutatorElement_def] at h2
      simpa [mul_assoc] using h2
    have hker : (u⁻¹ * ⟨_, hvW⟩ : ↥W) ∈ β.ker := by
      rw [hβker, Subgroup.mem_subgroupOf]
      simpa using hcomm
    have heq' := hequiv a u ⟨_, hvW⟩ rfl
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hker
    rw [← hker, hu, ha] at heq'
    have hM : ((((⟨Matrix.SpecialLinearGroup.toGL E, hE⟩ : ↥(StatedSL 2 F)) : GL (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
    rw [hM, toAdd_ofAdd] at heq'
    have h0 := congrFun heq' 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  · exact (le_of_eq heq.symm).trans inf_le_left

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem inf_centralizer_le_pCoreOf_sup (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pCoreOf 2 L ≤ T :=
    (pCoreOf_le_pCoreOf_of_le_normalizer le_sup_left
      (sup_le Subgroup.le_normalizer h.normal)).trans
      (pCoreOf_le_of_sylow h.fsu.sylow le_sup_right)
  have hLV := SecA.L_le_normalizer_fsuV h
  have hTV := SecA.T_le_normalizer_fsuV T I
  have hnorm : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) := by
    refine sup_le (fun l hl => ?_) (fun t ht => SecD.mem_normalizer_inf (Subgroup.le_normalizer ht)
      (SecA.mem_normalizer_centralizer (hTV ht)))
    refine SecD.mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    · have hc : x⁻¹ * (l * x * l⁻¹) ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
        refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2)
          ((Subgroup.mem_normalizer_iff.mp (SecA.mem_normalizer_centralizer (hLV hl)) x).mp
            hx.2)⟩
        have h1 : x⁻¹ * l * x ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (h.normal (Subgroup.inv_mem _ hx.1)) l).mp hl
          simpa using this
        have h2 := L.mul_mem h1 (L.inv_mem hl)
        simpa [mul_assoc] using h2
      rw [SecA.centralizer_eq_pCoreOf h1102 h] at hc
      have heq : l * x * l⁻¹ = x * (x⁻¹ * (l * x * l⁻¹)) := by group
      rw [heq]
      exact ⟨T.mul_mem hx.1 (hO hc), Subgroup.mul_mem _ hx.2
        ((SecA.centralizer_eq_pCoreOf h1102 h).ge hc).2⟩
    · have hl' := L.inv_mem hl
      have hc : x⁻¹ * (l⁻¹ * x * l⁻¹⁻¹) ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
        refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2)
          ((Subgroup.mem_normalizer_iff.mp (SecA.mem_normalizer_centralizer (hLV hl')) x).mp
            hx.2)⟩
        have h1 : x⁻¹ * l⁻¹ * x ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (h.normal (Subgroup.inv_mem _ hx.1)) l⁻¹).mp hl'
          simpa using this
        have h2 := L.mul_mem h1 (L.inv_mem hl')
        simpa [mul_assoc] using h2
      rw [SecA.centralizer_eq_pCoreOf h1102 h] at hc
      have heq : l⁻¹ * x * l = x * (x⁻¹ * (l⁻¹ * x * l⁻¹⁻¹)) := by group
      rw [heq]
      exact ⟨T.mul_mem hx.1 (hO hc), Subgroup.mul_mem _ hx.2
        ((SecA.centralizer_eq_pCoreOf h1102 h).ge hc).2⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    hnorm (h.fsu.sylow.1.to_le inf_le_left)

theorem commutator_pCoreOf_sup_le (h : Hyp11 G T L I n) :
    ⁅pCoreOf 2 (L ⊔ T), L⁆ ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_sylow h.fsu.sylow le_sup_right
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  refine (commutator_le_inf_of_le_normalizer (hOT.trans h.normal) hLO).trans ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun l hl => SecD.mem_normalizer_inf (hLO hl) (Subgroup.le_normalizer hl))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

end CFSG.Quasithin.Vol2.Ch11.SecF
